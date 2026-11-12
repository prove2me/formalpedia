-- Prove2me | solution 1 for LinMaxLoad.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:49:39.561793+00:00
-- url     : https://prove2.me/submissions/410dea21-7954-4043-879f-9981bd9f06f3

import Mathlib
import Definitions.Def_LinMaxLoad_avgLin
import Definitions.Def_LinMaxLoad_condAvgLin
import Definitions.Def_LinMaxLoad_probLin

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
namespace LinMaxLoad.Dev.Fibre

open Classical

variable {K E : Type*} [Field K] [Fintype K] [AddCommGroup E] [Module K E] [Finite E]

/-- restriction of a linear map to a submodule -/
def res (W : Submodule K E) (l : ℕ) (h : E →ₗ[K] (Fin l → K)) : W →ₗ[K] (Fin l → K) :=
  h.comp W.subtype

/-- (a) restriction is surjective -/
theorem res_surjective (W : Submodule K E) (l : ℕ) :
    Function.Surjective (res (K := K) W l) := by
  intro φ
  obtain ⟨g, hg⟩ := LinearMap.exists_extend φ
  exact ⟨g, hg⟩

theorem res_sub (W : Submodule K E) (l : ℕ) (h h' : E →ₗ[K] (Fin l → K)) :
    res W l (h - h') = res W l h - res W l h' := by
  ext x i
  simp [res]

theorem res_add (W : Submodule K E) (l : ℕ) (h h' : E →ₗ[K] (Fin l → K)) :
    res W l (h + h') = res W l h + res W l h' := by
  ext x i
  simp [res]

/-- (b) all fibres have the same cardinality -/
theorem card_fibre_eq (W : Submodule K E) (l : ℕ) (φ ψ : W →ₗ[K] (Fin l → K)) :
    Nat.card {h : E →ₗ[K] (Fin l → K) // res W l h = φ} =
      Nat.card {h : E →ₗ[K] (Fin l → K) // res W l h = ψ} := by
  obtain ⟨h1, hh1⟩ := res_surjective W l φ
  obtain ⟨h2, hh2⟩ := res_surjective W l ψ
  refine Nat.card_congr
    { toFun := fun h => ⟨h.1 - h1 + h2, ?_⟩
      invFun := fun h => ⟨h.1 - h2 + h1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [res_add, res_sub, hh1, hh2, h.2]; abel
  · rw [res_add, res_sub, hh1, hh2, h.2]; abel
  · intro h; ext x : 2; simp
  · intro h; ext x : 2; simp

/-- (d) cardinality of `Hom(W, l)`. -/
theorem card_hom (W : Type*) [AddCommGroup W] [Module K W] [Finite W] (l : ℕ) :
    Nat.card (W →ₗ[K] (Fin l → K)) =
      Fintype.card K ^ (l * Module.finrank K W) := by
  haveI : FiniteDimensional K W := Module.Finite.of_finite
  let b := Module.finBasis K W
  have e := Nat.card_congr (b.constr (M' := Fin l → K) K).toEquiv
  rw [← e, Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := K),
    Nat.card_eq_fintype_card (α := Fin l), Nat.card_eq_fintype_card (α := Fin (Module.finrank K W))]
  simp [pow_mul]

theorem card_hom_real (W : Type*) [AddCommGroup W] [Module K W] [Finite W] (l : ℕ) :
    (Nat.card (W →ₗ[K] (Fin l → K)) : ℝ) =
      (Fintype.card K : ℝ) ^ (l * Module.finrank K W) := by
  rw [card_hom]; push_cast; rfl

theorem card_hom_pos (W : Type*) [AddCommGroup W] [Module K W] [Finite W] (l : ℕ) :
    0 < Nat.card (W →ₗ[K] (Fin l → K)) := by
  rw [card_hom]; exact pow_pos Fintype.card_pos _

/-- the total count factors through the restriction -/
theorem card_hom_mul (W : Submodule K E) (l : ℕ) :
    Nat.card (E →ₗ[K] (Fin l → K)) =
      Nat.card (W →ₗ[K] (Fin l → K)) *
        Nat.card {h : E →ₗ[K] (Fin l → K) // res W l h = 0} := by
  have e := Nat.card_congr (Equiv.sigmaFiberEquiv (res (K := K) W l)).symm
  letI : Fintype (W →ₗ[K] (Fin l → K)) := Fintype.ofFinite _
  rw [e, Nat.card_sigma]
  have : ∀ φ : W →ₗ[K] (Fin l → K),
      Nat.card {h : E →ₗ[K] (Fin l → K) // res W l h = φ} =
        Nat.card {h : E →ₗ[K] (Fin l → K) // res W l h = 0} := fun φ => card_fibre_eq W l φ 0
  simp only [this]
  rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card (α := W →ₗ[K] (Fin l → K))]
  simp

theorem card_filter (l : ℕ) [Fintype (E →ₗ[K] (Fin l → K))] (P : (E →ₗ[K] (Fin l → K)) → Prop)
    [DecidablePred P] :
    ((Finset.univ.filter P).card : ℕ) = Nat.card {h : E →ₗ[K] (Fin l → K) // P h} := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

end LinMaxLoad.Dev.Fibre
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
namespace LinMaxLoad.Dev.Lemma1

open Classical LinMaxLoad.Dev.Fibre

variable {K E : Type*} [Field K] [Fintype K] [AddCommGroup E] [Module K E] [Finite E]

theorem probLin_eq (l : ℕ) (P : (E →ₗ[K] (Fin l → K)) → Prop) :
    probLin K E l P = (Nat.card {h : E →ₗ[K] (Fin l → K) // P h} : ℝ) /
      (Nat.card (E →ₗ[K] (Fin l → K)) : ℝ) := by
  letI : Fintype (E →ₗ[K] (Fin l → K)) := Fintype.ofFinite _
  unfold probLin avgLin
  rw [Finset.sum_boole, Nat.card_eq_fintype_card (α := E →ₗ[K] (Fin l → K)),
    ← card_filter l P]

theorem agree_of_forall {l k : ℕ} (s : Fin k → E) (h h' : E →ₗ[K] (Fin l → K))
    (hh : ∀ i, h (s i) = h' (s i)) :
    res (Submodule.span K (Set.range s)) l h = res (Submodule.span K (Set.range s)) l h' := by
  have hle : Submodule.span K (Set.range s) ≤ LinearMap.ker (h - h') := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    simp [hh i]
  ext x j
  have := hle x.2
  rw [LinearMap.mem_ker] at this
  have h2 := congrFun this j
  simp only [LinearMap.sub_apply, Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at h2
  simpa [res] using h2

theorem key (l k : ℕ) (s : Fin k → E) (y : Fin k → (Fin l → K)) :
    (Nat.card {h : E →ₗ[K] (Fin l → K) // ∀ i, h (s i) = y i} : ℝ) /
        (Nat.card (E →ₗ[K] (Fin l → K)) : ℝ) ≤
      ((Fintype.card K : ℝ) ^ (l * Module.finrank K (Submodule.span K (Set.range s))))⁻¹ := by
  set W := Submodule.span K (Set.range s)
  have hmul := card_hom_mul W l
  have hW := card_hom_real (K := K) W l
  have hWpos := card_hom_pos (K := K) W l
  have hNpos : 0 < Nat.card {h : E →ₗ[K] (Fin l → K) // res W l h = 0} := by
    obtain ⟨h0, hh0⟩ := res_surjective (K := K) W l 0
    haveI : Finite {h : E →ₗ[K] (Fin l → K) // res W l h = 0} := inferInstance
    exact Nat.card_pos_iff.2 ⟨⟨⟨h0, hh0⟩⟩, inferInstance⟩
  set Nf := Nat.card {h : E →ₗ[K] (Fin l → K) // res W l h = 0}
  have ha : Nat.card {h : E →ₗ[K] (Fin l → K) // ∀ i, h (s i) = y i} ≤ Nf := by
    by_cases hne : Nonempty {h : E →ₗ[K] (Fin l → K) // ∀ i, h (s i) = y i}
    · obtain ⟨⟨h0, hh0⟩⟩ := hne
      calc Nat.card {h : E →ₗ[K] (Fin l → K) // ∀ i, h (s i) = y i}
          ≤ Nat.card {h : E →ₗ[K] (Fin l → K) // res W l h = res W l h0} := by
            refine Nat.card_le_card_of_injective
              (fun h => ⟨h.1, agree_of_forall s h.1 h0 (fun i => by rw [h.2 i, hh0 i])⟩) ?_
            intro a b hab
            have h3 := congrArg Subtype.val hab
            exact Subtype.ext h3
        _ = Nf := card_fibre_eq W l _ 0
    · rw [not_nonempty_iff] at hne
      simp
  rw [hmul]
  push_cast
  rw [hW]
  have hq : (0 : ℝ) < (Fintype.card K : ℝ) ^ (l * Module.finrank K W) := by
    have := Fintype.card_pos (α := K)
    positivity
  have hN : (0 : ℝ) < Nf := by exact_mod_cast hNpos
  rw [div_le_iff₀ (by positivity)]
  have : (Nat.card {h : E →ₗ[K] (Fin l → K) // ∀ i, h (s i) = y i} : ℝ) ≤ Nf := by
    exact_mod_cast ha
  calc (Nat.card {h : E →ₗ[K] (Fin l → K) // ∀ i, h (s i) = y i} : ℝ) ≤ Nf := this
    _ = ((Fintype.card K : ℝ) ^ (l * Module.finrank K W))⁻¹ *
        ((Fintype.card K : ℝ) ^ (l * Module.finrank K W) * Nf) := by field_simp

theorem key_zero (l k : ℕ) (s : Fin k → E) :
    (Nat.card {h : E →ₗ[K] (Fin l → K) // ∀ i, h (s i) = 0} : ℝ) /
        (Nat.card (E →ₗ[K] (Fin l → K)) : ℝ) =
      ((Fintype.card K : ℝ) ^ (l * Module.finrank K (Submodule.span K (Set.range s))))⁻¹ := by
  set W := Submodule.span K (Set.range s)
  have hmul := card_hom_mul W l
  have hW := card_hom_real (K := K) W l
  have hNpos : 0 < Nat.card {h : E →ₗ[K] (Fin l → K) // res W l h = 0} := by
    obtain ⟨h0, hh0⟩ := res_surjective (K := K) W l 0
    exact Nat.card_pos_iff.2 ⟨⟨⟨h0, hh0⟩⟩, inferInstance⟩
  have e : Nat.card {h : E →ₗ[K] (Fin l → K) // ∀ i, h (s i) = 0} =
      Nat.card {h : E →ₗ[K] (Fin l → K) // res W l h = 0} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight ?_)
    intro h
    constructor
    · intro hh
      have := agree_of_forall (l := l) s h 0 (fun i => by simp [hh i])
      rw [this]; ext x j; simp [res]
    · intro hh i
      have := LinearMap.congr_fun hh ⟨s i, Submodule.subset_span ⟨i, rfl⟩⟩
      simpa [res] using this
  rw [e, hmul]
  set Nf := Nat.card {h : E →ₗ[K] (Fin l → K) // res W l h = 0}
  push_cast
  rw [hW]
  have hq : (0 : ℝ) < (Fintype.card K : ℝ) ^ (l * Module.finrank K W) := by
    have := Fintype.card_pos (α := K)
    positivity
  have hN : (0 : ℝ) < Nf := by exact_mod_cast hNpos
  field_simp

end LinMaxLoad.Dev.Lemma1

namespace LinMaxLoad
open LinMaxLoad.Dev.Lemma1 in
theorem chk_lemma_1 {K E : Type*} [Field K] [Fintype K] [AddCommGroup E] [Module K E] [Finite E]
    (ℓ k : ℕ) (s : Fin k → E) (y : Fin k → (Fin ℓ → K)) :
    probLin K E ℓ (fun h => ∀ i, h (s i) = y i) ≤
        ((Fintype.card K : ℝ) ^ (ℓ * Module.finrank K (Submodule.span K (Set.range s))))⁻¹ ∧
      probLin K E ℓ (fun h => ∀ i, h (s i) = 0) =
        ((Fintype.card K : ℝ) ^ (ℓ * Module.finrank K (Submodule.span K (Set.range s))))⁻¹ := by
  rw [probLin_eq, probLin_eq]
  exact ⟨key ℓ k s y, key_zero ℓ k s⟩
end LinMaxLoad
end

theorem solution : type_of% @LinMaxLoad.chk_lemma_1 := @LinMaxLoad.chk_lemma_1
