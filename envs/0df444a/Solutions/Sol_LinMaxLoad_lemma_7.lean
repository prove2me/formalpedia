-- Prove2me | solution 1 for LinMaxLoad.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:49:41.107197+00:00
-- url     : https://prove2.me/submissions/016015e9-c8bd-4b89-9a78-7349cbfdab32

import Mathlib
import Definitions.Def_LinMaxLoad_avgLin
import Definitions.Def_LinMaxLoad_condAvgLin
import Definitions.Def_LinMaxLoad_maxLoad
import Definitions.Def_LinMaxLoad_cosetSum
import Definitions.Def_LinMaxLoad_expLoad
import Theorems.Thm_LinMaxLoad_lemma_7_conditional_bound
import Theorems.Thm_LinMaxLoad_lemma_7_kernel_expectation

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

/-- (c) decomposition of `avgLin` over restrictions. -/
theorem avgLin_decomp (V : Submodule K E) (l : ℕ) [Fintype (V →ₗ[K] (Fin l → K))]
    (X : (E →ₗ[K] (Fin l → K)) → ℝ) :
    avgLin K E l X =
      (1 / (Fintype.card (V →ₗ[K] (Fin l → K)) : ℝ)) *
        ∑ φ : V →ₗ[K] (Fin l → K),
          condAvgLin K E l (fun h => h.comp V.subtype = φ) X := by
  letI : Fintype (E →ₗ[K] (Fin l → K)) := Fintype.ofFinite _
  set N : ℕ := Nat.card {h : E →ₗ[K] (Fin l → K) // res V l h = 0} with hN
  have hmul : Nat.card (E →ₗ[K] (Fin l → K)) = Nat.card (V →ₗ[K] (Fin l → K)) * N :=
    card_hom_mul V l
  have hpos := card_hom_pos (K := K) E l
  have hVpos := card_hom_pos (K := K) V l
  have hVcard : Nat.card (V →ₗ[K] (Fin l → K)) = Fintype.card (V →ₗ[K] (Fin l → K)) :=
    Nat.card_eq_fintype_card
  have hEcard : Nat.card (E →ₗ[K] (Fin l → K)) = Fintype.card (E →ₗ[K] (Fin l → K)) :=
    Nat.card_eq_fintype_card
  have hNpos : 0 < N := Nat.pos_of_ne_zero (by
    intro h
    rw [h, mul_zero] at hmul
    omega)
  have hfib : ∀ φ : V →ₗ[K] (Fin l → K),
      ((Finset.univ.filter (fun h : E →ₗ[K] (Fin l → K) => h.comp V.subtype = φ)).card : ℝ) = N := by
    intro φ
    have h1 : (Finset.univ.filter (fun h : E →ₗ[K] (Fin l → K) => h.comp V.subtype = φ)).card = N :=
      (card_filter (K := K) (E := E) l (fun h => h.comp V.subtype = φ)).trans
        (card_fibre_eq V l φ 0)
    exact_mod_cast h1
  unfold condAvgLin avgLin
  simp only [hfib]
  have hsum : ∑ φ : V →ₗ[K] (Fin l → K),
      ∑ h ∈ Finset.univ.filter (fun h : E →ₗ[K] (Fin l → K) => h.comp V.subtype = φ), X h
      = ∑ h, X h := by
    rw [← Finset.sum_fiberwise (Finset.univ) (fun h : E →ₗ[K] (Fin l → K) => h.comp V.subtype) X]
  rw [← Finset.sum_div, hsum]
  have : (Fintype.card (E →ₗ[K] (Fin l → K)) : ℝ) =
      (Fintype.card (V →ₗ[K] (Fin l → K)) : ℝ) * N := by
    rw [← hEcard, hmul, ← hVcard]; push_cast; rfl
  rw [this]
  have : (0 : ℝ) < Fintype.card (V →ₗ[K] (Fin l → K)) := by rw [← hVcard]; exact_mod_cast hVpos
  have : (0 : ℝ) < N := by exact_mod_cast hNpos
  field_simp

end LinMaxLoad.Dev.Fibre
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
namespace LinMaxLoad.Dev.Lemma7

open Classical

/-- the conditional average of a constant over a nonempty fibre is that constant -/
theorem condAvg_const {K E : Type*} [Field K] [Fintype K] [AddCommGroup E] [Module K E] [Finite E]
    (ℓ : ℕ) (V : Submodule K E) (φ : V →ₗ[K] (Fin ℓ → K)) (c : ℝ) :
    LinMaxLoad.condAvgLin K E ℓ (fun h => h.comp V.subtype = φ) (fun _ => c) = c := by
  unfold LinMaxLoad.condAvgLin
  letI : Fintype (E →ₗ[K] (Fin ℓ → K)) := Fintype.ofFinite _
  obtain ⟨h, hh⟩ := Dev.Fibre.res_surjective (K := K) V ℓ φ
  have hne : (Finset.univ.filter (fun h : E →ₗ[K] (Fin ℓ → K) => h.comp V.subtype = φ)).Nonempty :=
    ⟨h, by simpa [Dev.Fibre.res] using hh⟩
  have hpos : (0 : ℝ) < (Finset.univ.filter
      (fun h : E →ₗ[K] (Fin ℓ → K) => h.comp V.subtype = φ)).card := by
    exact_mod_cast hne.card_pos
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_div_cancel_left₀ c hpos.ne'

end LinMaxLoad.Dev.Lemma7

namespace LinMaxLoad

open Classical in
open LinMaxLoad.Dev.Lemma7 in
theorem chk_lemma_7 {K E : Type*} [Field K] [Fintype K] [AddCommGroup E] [Module K E] [Finite E]
    (ℓ : ℕ) (V : Submodule K E) (hV : Module.finrank K V ≤ ℓ) (T : Finset E) :
    expLoad K E ℓ (cosetSum V T) ≤
      2 * expLoad K (E ⧸ V) (ℓ - Module.finrank K V) (T.image V.mkQ) := by
  letI : Fintype (V →ₗ[K] (Fin ℓ → K)) := Fintype.ofFinite _
  set Eq := expLoad K (E ⧸ V) (ℓ - Module.finrank K V) (T.image V.mkQ) with hEq
  have hEq0 : 0 ≤ Eq := by
    rw [hEq]
    unfold expLoad avgLin
    exact div_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hke := lemma_7_kernel_expectation (K := K) ℓ V
  have hY : avgLin K E ℓ (fun h => (Fintype.card K : ℝ) ^
      Module.finrank K (LinearMap.ker (h.domRestrict V))) ≤ 2 :=
    hke.1.trans_le (hke.2.1.trans_le (hke.2.2.1.trans_le (hke.2.2.2 hV)))
  have hYd := Dev.Fibre.avgLin_decomp (K := K) V ℓ
    (fun h => (Fintype.card K : ℝ) ^ Module.finrank K (LinearMap.ker (h.domRestrict V)))
  have hYc : ∀ φ : V →ₗ[K] (Fin ℓ → K),
      condAvgLin K E ℓ (fun h => h.comp V.subtype = φ)
        (fun h => (Fintype.card K : ℝ) ^ Module.finrank K (LinearMap.ker (h.domRestrict V))) =
      (Fintype.card K : ℝ) ^ Module.finrank K (LinearMap.ker φ) := by
    intro φ
    rw [← condAvg_const ℓ V φ ((Fintype.card K : ℝ) ^ Module.finrank K (LinearMap.ker φ))]
    unfold condAvgLin
    congr 1
    refine Finset.sum_congr rfl fun h hh => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh
    have : h.domRestrict V = φ := hh
    beta_reduce
    rw [this]
  simp only [hYc] at hYd
  have hA : (0 : ℝ) < Fintype.card (V →ₗ[K] (Fin ℓ → K)) := by exact_mod_cast Fintype.card_pos
  have hmain := Dev.Fibre.avgLin_decomp (K := K) V ℓ
    (fun h => (maxLoad (h : E → Fin ℓ → K) (cosetSum V T) : ℝ))
  unfold expLoad
  rw [hmain]
  have hb : ∀ φ : V →ₗ[K] (Fin ℓ → K),
      condAvgLin K E ℓ (fun h => h.comp V.subtype = φ)
        (fun h => (maxLoad (h : E → Fin ℓ → K) (cosetSum V T) : ℝ)) ≤
      (Fintype.card K : ℝ) ^ Module.finrank K (LinearMap.ker φ) * Eq :=
    fun φ => lemma_7_conditional_bound ℓ V hV T φ
  calc (1 / (Fintype.card (V →ₗ[K] (Fin ℓ → K)) : ℝ)) * ∑ φ : V →ₗ[K] (Fin ℓ → K),
        condAvgLin K E ℓ (fun h => h.comp V.subtype = φ)
          (fun h => (maxLoad (h : E → Fin ℓ → K) (cosetSum V T) : ℝ))
      ≤ (1 / (Fintype.card (V →ₗ[K] (Fin ℓ → K)) : ℝ)) * ∑ φ : V →ₗ[K] (Fin ℓ → K),
          (Fintype.card K : ℝ) ^ Module.finrank K (LinearMap.ker φ) * Eq :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun φ _ => hb φ) (by positivity)
    _ = (avgLin K E ℓ (fun h => (Fintype.card K : ℝ) ^
          Module.finrank K (LinearMap.ker (h.domRestrict V)))) * Eq := by
        rw [hYd, ← Finset.sum_mul]; ring
    _ ≤ 2 * Eq := mul_le_mul_of_nonneg_right hY hEq0

end LinMaxLoad
end

theorem solution : type_of% @LinMaxLoad.chk_lemma_7 := @LinMaxLoad.chk_lemma_7
