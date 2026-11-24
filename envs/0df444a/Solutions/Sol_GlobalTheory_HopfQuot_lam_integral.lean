-- Prove2me | solution 1 for GlobalTheory.HopfQuot.lam_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:55:10.870301+00:00
-- url     : https://prove2.me/submissions/615477ef-270d-47b5-b28b-d0b203a64ff7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteFaithfullyFlatKer
import Theorems.Thm_GlobalTheory_HopfQuot_tr_comm
import Theorems.Thm_GlobalTheory_HopfQuot_ev_tmul
import Theorems.Thm_GlobalTheory_HopfQuot_shear_tmul
import Theorems.Thm_GlobalTheory_HopfQuot_shear_surjective
import Theorems.Thm_GlobalTheory_HopfQuot_shear_hit
import Theorems.Thm_GlobalTheory_HopfQuot_lam_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HopfQuot.ev_tmul

set_option autoImplicit false
open GlobalTheory GlobalTheory.HopfQuot
open TensorProduct
variable {R Λ ι : Type*} [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [Fintype ι]
namespace GlobalTheory.HopfQuot
theorem _root_.solution [Module.Finite R Λ] (e : ι → Λ) (c : ι → Λ →ₗ[R] R)
    (h : ∀ m, ∑ i, c i m • e i = m) (f : Λ →ₗ[R] R) (x : Λ) :
    ev Λ (lam e c f) (Coalgebra.comul x) = algebraMap R Λ (lam e c f x) := by
  let e' : ι → Λ ⊗[R] Λ := fun i => 1 ⊗ₜ e i
  let c' : ι → Λ ⊗[R] Λ →ₗ[Λ] Λ := fun i => ev Λ (c i)
  have h' : ∀ m, ∑ i, c' i m • e' i = m := by
    intro m
    induction m with
    | zero => simp
    | add a b ha hb => simp only [map_add, add_smul, Finset.sum_add_distrib, ha, hb]
    | tmul a b =>
      conv_rhs => rw [← h b, tmul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [c', e', TensorProduct.smul_tmul']
  have h1 : ∀ z : Λ ⊗[R] Λ, ev Λ (lam e c f) z =
      tr e' c' ((hit f).baseChange Λ ∘ₗ LinearMap.mulLeft Λ z) := by
    intro z
    induction z with
    | zero => simp [tr]
    | add a b ha hb =>
      rw [map_add, ha, hb]
      simp [tr, add_mul, Finset.sum_add_distrib]
    | tmul a b =>
      simp [lam_apply, tr, c', e', Finset.sum_smul]
  have hb : Function.Bijective (shear R Λ).toLinearMap :=
    OrzechProperty.bijective_of_surjective_endomorphism _ shear_surjective
  let σ := LinearEquiv.ofBijective _ hb
  have h2 : (hit f).baseChange Λ ∘ₗ LinearMap.mulLeft Λ (Coalgebra.comul (R := R) x) =
      σ.toLinearMap ∘ₗ (((hit f).baseChange Λ ∘ₗ LinearMap.mulLeft Λ (1 ⊗ₜ x)) ∘ₗ
        σ.symm.toLinearMap) := by
    refine LinearMap.ext fun z => ?_
    obtain ⟨z, rfl⟩ := σ.surjective z
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.mulLeft_apply]
    change _ = shear R Λ _
    rw [shear_hit, map_mul (shear R Λ), shear_tmul, one_smul]
    rfl
  rw [h1, h2, tr_comm e' c' h', LinearMap.comp_assoc, LinearEquiv.symm_comp,
    LinearMap.comp_id, ← h1, ev_tmul, Algebra.algebraMap_eq_smul_one]
end GlobalTheory.HopfQuot
