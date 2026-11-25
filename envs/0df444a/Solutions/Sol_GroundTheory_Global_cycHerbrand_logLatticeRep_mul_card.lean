-- Prove2me | solution 1 for GroundTheory.Global.cycHerbrand_logLatticeRep_mul_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:59:44.405669+00:00
-- url     : https://prove2.me/submissions/2b04d2fb-48e8-4ce6-97fd-aa6e1dcc0a7e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_UnitsHerbrand
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_UnitsHerbrandValue
import Theorems.Thm_GroundTheory_Global_piScalarRight_baseChange_funPermRep
import Theorems.Thm_GroundTheory_Global_logLatticeProdMap_apply
import Theorems.Thm_GroundTheory_Global_logLatticeProdMap_comm
import Theorems.Thm_GroundTheory_Global_linearIndependent_logLattice_one
import Theorems.Thm_GroundTheory_Global_SemiLocal_tensorHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_coeff_permOfFun
import Theorems.Thm_GroundTheory_Global_cycHerbrand_eq_of_real_equiv
import Theorems.Thm_GroundTheory_Global_cycHerbrand_prod
import Theorems.Thm_GroundTheory_Global_cycHerbrand_trivial_int
import Theorems.Thm_GroundTheory_Global_cycSub_apply
import Theorems.Thm_GroundTheory_Global_finrank_logLattice
import Theorems.Thm_GroundTheory_Global_hasHerbrandQuotient_cycSubOne_of_finite
import Theorems.Thm_GroundTheory_Global_normHom_apply
import Theorems.Thm_GroundTheory_Global_piRep_apply
import Theorems.Thm_GroundTheory_GroupCoh_restrictEnd_apply
import Theorems.Thm_P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.SemiLocal.tensorHomeomorph_apply
attribute [local simp] GroundTheory.Global.coeff_permOfFun
attribute [local simp] GroundTheory.Global.cycSub_apply
attribute [local simp] GroundTheory.Global.normHom_apply
attribute [local simp] GroundTheory.Global.piRep_apply
attribute [local simp] GroundTheory.GroupCoh.restrictEnd_apply
attribute [local simp] P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7



set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField NumberField.Units NumberField.InfinitePlace MulAction Module
open scoped TensorProduct
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
namespace GroundTheory.Global
theorem _root_.solution {σ : L ≃ₐ[K] L} (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    cycHerbrand (logLatticeRep K L) σ * Fintype.card (L ≃ₐ[K] L) =
      cycHerbrand (funPermRep ℤ (L ≃ₐ[K] L) (InfinitePlace L)) σ := by
  classical
  let bM := Module.Free.chooseBasis ℤ (logLattice L)
  let b := bM.prod (Basis.singleton Unit ℤ)
  let B := Algebra.TensorProduct.basis ℝ b
  let E := (logLatticeProdMap (L := L)).liftBaseChange ℝ
  let v := Sum.elim (fun i => (bM i : InfinitePlace L → ℝ))
    (fun _ : Unit => (1 : InfinitePlace L → ℝ))
  have hEB : ∀ j, E (B j) = v j := by
    intro j
    rw [Algebra.TensorProduct.basis_apply, LinearMap.liftBaseChange_tmul, one_smul]
    rcases j with i | u
    · simp [b, v, Basis.prod_apply, logLatticeProdMap_apply]
    · simp [b, v, Basis.prod_apply, logLatticeProdMap_apply]
  have hli : LinearIndependent ℝ v := linearIndependent_logLattice_one bM
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (logLattice L) ⊕ Unit) =
      finrank ℝ (InfinitePlace L → ℝ) := by
    rw [Fintype.card_sum, Fintype.card_unit, Module.finrank_fintype_fun_eq_card,
      ← Module.finrank_eq_card_chooseBasisIndex, finrank_logLattice, rank]
    have : 0 < Fintype.card (InfinitePlace L) := Fintype.card_pos
    omega
  have hspan := hli.span_eq_top_of_card_eq_finrank hcard
  have hsurj : Function.Surjective E := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact ⟨B j, hEB j⟩
  have hdim : finrank ℝ (ℝ ⊗[ℤ] (logLattice L × ℤ)) = finrank ℝ (InfinitePlace L → ℝ) := by
    rw [Module.finrank_eq_card_basis B, hcard]
  have hinj : Function.Injective E :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj
  have hbij : Function.Bijective E := ⟨hinj, hsurj⟩
  let P := TensorProduct.piScalarRight ℤ ℝ ℝ (InfinitePlace L)
  let e : ℝ ⊗[ℤ] (logLattice L × ℤ) ≃ₗ[ℝ] ℝ ⊗[ℤ] (InfinitePlace L → ℤ) :=
    (LinearEquiv.ofBijective E hbij).trans P.symm
  have hE : ∀ (g : L ≃ₐ[K] L) y, E ((((logLatticeRep K L).prod
      (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ)) g).baseChange ℝ y) =
      funPermRep ℝ (L ≃ₐ[K] L) (InfinitePlace L) g (E y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r x =>
      rw [LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul,
        map_smul, logLatticeProdMap_comm]
    | add y z hy hz => rw [map_add, map_add, hy, hz, map_add, map_add]
  have he : ∀ (g : L ≃ₐ[K] L) y, e ((((logLatticeRep K L).prod
      (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ)) g).baseChange ℝ y) =
      (funPermRep ℤ (L ≃ₐ[K] L) (InfinitePlace L) g).baseChange ℝ (e y) := by
    intro g y
    apply P.injective
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rw [piScalarRight_baseChange_funPermRep, LinearEquiv.apply_symm_apply,
      LinearEquiv.ofBijective_apply, LinearEquiv.ofBijective_apply, hE]
  rw [← cycHerbrand_eq_of_real_equiv _ _ σ e he,
    cycHerbrand_prod _ _ σ (hasHerbrandQuotient_cycSubOne_of_finite _ hσ)
      (hasHerbrandQuotient_cycSubOne_of_finite _ hσ), cycHerbrand_trivial_int]
end GroundTheory.Global
