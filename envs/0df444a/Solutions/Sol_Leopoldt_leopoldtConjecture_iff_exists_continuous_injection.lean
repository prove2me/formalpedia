-- Prove2me | solution 1 for Leopoldt.leopoldtConjecture_iff_exists_continuous_injection
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-09T15:02:46.024619+00:00
-- url     : https://prove2.me/submissions/4b32fa00-074f-4eaf-ba7d-3d292c92651e

import Definitions.Def_LeopoldtDefect

open NumberField

namespace LeopoldtRankAux

variable (p : ℕ) [Fact p.Prime]

/-- Extend a vector of length `m` by zeros to a vector of length `n ≥ m`. -/
noncomputable def padZero {m n : ℕ} (_h : m ≤ n) : (Fin m → ℤ_[p]) →+ (Fin n → ℤ_[p]) where
  toFun x i := if hi : (i : ℕ) < m then x ⟨i, hi⟩ else 0
  map_zero' := by
    funext i
    by_cases hi : (i : ℕ) < m
    · rw [dif_pos hi]; rfl
    · rw [dif_neg hi]; rfl
  map_add' x y := by
    funext i
    by_cases hi : (i : ℕ) < m
    · simp only [Pi.add_apply, dif_pos hi]
    · simp only [Pi.add_apply, dif_neg hi, add_zero]

theorem padZero_apply {m n : ℕ} (h : m ≤ n) (x : Fin m → ℤ_[p]) (i : Fin n) :
    padZero p h x i = if hi : (i : ℕ) < m then x ⟨i, hi⟩ else 0 := rfl

theorem padZero_injective {m n : ℕ} (h : m ≤ n) : Function.Injective (padZero p h) := by
  intro x y hxy
  funext j
  have hj : ((Fin.castLE h j : Fin n) : ℕ) < m := j.isLt
  have e1 := congrFun hxy (Fin.castLE h j)
  simp only [padZero_apply, dif_pos hj] at e1
  exact e1

theorem padZero_continuous {m n : ℕ} (h : m ≤ n) : Continuous (padZero p h) := by
  refine continuous_pi fun i => ?_
  by_cases hi : (i : ℕ) < m
  · simp only [padZero_apply, dif_pos hi]
    exact continuous_apply _
  · simp only [padZero_apply, dif_neg hi]
    exact continuous_const

variable {G : Type*} [CommGroup G] [TopologicalSpace G]

/-- The set of ranks witnessed by a continuous injection, whose supremum is `zpRankBelow`. -/
def zpRankSet (bound : ℕ) (H : Subgroup G) : Set ℕ :=
  {n : ℕ | n ≤ bound ∧ ∃ f : Multiplicative (Fin n → ℤ_[p]) →* G,
    Function.Injective f ∧ Continuous f ∧ ∀ x, f x ∈ H}

theorem zero_mem_zpRankSet (bound : ℕ) (H : Subgroup G) : (0 : ℕ) ∈ zpRankSet p bound H := by
  refine ⟨Nat.zero_le _, 1, ?_, continuous_const, fun x => H.one_mem⟩
  intro a b _
  have : (Multiplicative.toAdd a) = (Multiplicative.toAdd b) := by
    funext i; exact i.elim0
  simpa using this

theorem zpRankSet_nonempty (bound : ℕ) (H : Subgroup G) : (zpRankSet p bound H).Nonempty :=
  ⟨0, zero_mem_zpRankSet p bound H⟩

theorem zpRankSet_bddAbove (bound : ℕ) (H : Subgroup G) : BddAbove (zpRankSet p bound H) :=
  ⟨bound, fun _ hn => hn.1⟩

theorem zpRankBelow_mem (bound : ℕ) (H : Subgroup G) :
    Leopoldt.zpRankBelow p bound H ∈ zpRankSet p bound H :=
  Nat.sSup_mem (zpRankSet_nonempty p bound H) (zpRankSet_bddAbove p bound H)

/-- If a continuous injection of `ℤ_p^n` exists, so does one of `ℤ_p^m` for every `m ≤ n`. -/
theorem zpRankSet_downward (bound : ℕ) (H : Subgroup G) {m n : ℕ} (hmn : m ≤ n)
    (hn : n ∈ zpRankSet p bound H) : m ∈ zpRankSet p bound H := by
  obtain ⟨hnb, f, hinj, hcont, hmem⟩ := hn
  refine ⟨hmn.trans hnb, f.comp (AddMonoidHom.toMultiplicative (padZero p hmn)), ?_, ?_, ?_⟩
  · refine hinj.comp fun a b hab => ?_
    have h1 : padZero p hmn (Multiplicative.toAdd a) = padZero p hmn (Multiplicative.toAdd b) := hab
    exact Multiplicative.toAdd.injective (padZero_injective p hmn h1)
  · exact hcont.comp (padZero_continuous p hmn)
  · intro x; exact hmem _

theorem le_zpRankBelow_iff (bound : ℕ) (H : Subgroup G) {m : ℕ} :
    m ≤ Leopoldt.zpRankBelow p bound H ↔ m ∈ zpRankSet p bound H :=
  ⟨fun h => zpRankSet_downward p bound H h (zpRankBelow_mem p bound H),
   fun h => le_csSup (zpRankSet_bddAbove p bound H) h⟩

theorem units_rank_le_finrank (K : Type*) [Field K] [NumberField K] :
    Units.rank K ≤ Module.finrank ℚ K := by
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank K
  have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
  unfold NumberField.Units.rank
  omega

end LeopoldtRankAux

open LeopoldtRankAux in
/-- Leopoldt's conjecture, unfolded: the defect vanishes exactly when `ℤ_p^r` (with `r` Dirichlet's
unit rank) admits a continuous injective homomorphism into the `p`-adic closure of the units. -/
theorem solution (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] :
    Leopoldt.LeopoldtConjecture p K ↔
      ∃ f : Multiplicative (Fin (Units.rank K) → ℤ_[p]) →* Leopoldt.SemilocalUnits p K,
        Function.Injective f ∧ Continuous f ∧ ∀ x, f x ∈ Leopoldt.unitClosure p K := by
  rw [Leopoldt.LeopoldtConjecture, Leopoldt.defect, Nat.sub_eq_zero_iff_le, le_zpRankBelow_iff]
  constructor
  · rintro ⟨-, f, hf⟩
    exact ⟨f, hf⟩
  · rintro ⟨f, hf⟩
    exact ⟨units_rank_le_finrank K, f, hf⟩
