-- Prove2me | solution 1 for GlobalTheory.WeilM.isUnitaryOn_splitOm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:16:43.278588+00:00
-- url     : https://prove2.me/submissions/ca2d4eff-4941-4fbb-a488-5e7739f35dd5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilObjectsInhabited
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsLocallyConstantSplitOm
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space
import Theorems.Thm_GlobalTheory_WeilM_smul_map_mulVec_pi
import Theorems.Thm_GlobalTheory_WeilM_splitOm_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ValuativeRel Filter
open scoped NNReal Topology Kronecker
open GlobalTheory GlobalTheory.WeilM
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
namespace GlobalTheory.WeilM
theorem _root_.solution (χ : (F × F)ˣ →* Circle) (J : Matrix β β (F × F)) (σ : κ ≃ α × β) :
    IsUnitaryOn (sbClass F) (splitOm (distribHaarChar F) χ J σ) := by
  classical
  borelize F
  have := SplitWeil.secondCountable F
  have := SplitWeil.t2Space F
  unfold IsUnitaryOn
  rw [← (BorelSpace.measurable_eq : (MeasurableSpace.pi : MeasurableSpace (κ → F)) = borel _)]
  intro μ hμ h φ hφ
  set t := ugFst J h
  let G : Matrix κ κ F := ((1 : Matrix α α F) ⊗ₖ (t⁻¹).val).submatrix σ σ
  have hG : (((GeneralLinearGroup.det t)⁻¹ ^ Fintype.card α : Fˣ) : F) = G.det := by
    rw [det_submatrix_equiv_self, det_kronecker, det_one, one_pow, one_mul, ← map_inv, Units.val_pow_eq_pow_val]
    rfl
  have hgx : ∀ u, flat σ ((flat σ).symm u * (t⁻¹).valᵀ) = G.mulVec u := by
    intro u
    obtain ⟨X, rfl⟩ := (flat σ).surjective u
    funext k
    show _ = ∑ k', ((1 : Matrix α α F) ⊗ₖ (t⁻¹).val) (σ k) (σ k') * X (σ k').1 (σ k').2
    rw [Fintype.sum_equiv σ _ (fun q => ((1 : Matrix α α F) ⊗ₖ (t⁻¹).val) (σ k) q * X q.1 q.2) fun _ => rfl,
      Fintype.sum_prod_type, LinearEquiv.symm_apply_apply, flat_apply, mul_apply]
    simp [kroneckerMap_apply, one_apply, mul_comm]
  have hs : ‖splitChar (distribHaarChar F) χ (Fintype.card α) (GeneralLinearGroup.det t)‖ₑ ^ 2 =
      distribHaarChar F ((GeneralLinearGroup.det t)⁻¹ ^ Fintype.card α) := by
    rw [enorm_eq_nnnorm, ← ENNReal.coe_pow, ENNReal.coe_inj, ← NNReal.coe_inj]
    have p : (0 : ℝ) ≤ distribHaarChar F (GeneralLinearGroup.det t) := NNReal.coe_nonneg _
    simp only [splitChar, MonoidHom.coe_mk, OneHom.coe_mk, NNReal.coe_pow, coe_nnnorm, norm_mul, Circle.norm_coe, one_mul,
      Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg p _), map_pow, map_inv, NNReal.coe_inv]
    rw [← Real.rpow_natCast, ← Real.rpow_mul p, inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg p]
    congr 1
    push_cast
    ring
  have hm : Measurable fun x => ‖φ x‖ₑ ^ 2 := (hφ.1.continuous.measurable.enorm).pow_const 2
  rw [Measure.isAddLeftInvariant_eq_smul μ (Measure.pi fun _ : κ => (Measure.addHaar : Measure F)),
    lintegral_smul_measure, lintegral_smul_measure]
  congr 1
  conv_rhs => rw [← smul_map_mulVec_pi Measure.addHaar G _ hG, lintegral_smul_measure,
    lintegral_map hm (show Measurable G.mulVec from (continuous_const.matrix_mulVec continuous_id).measurable)]
  simp only [splitOm_apply, enorm_mul, mul_pow]
  rw [lintegral_const_mul' _ _ (by simp [enorm_eq_nnnorm]), hs]
  simp only [← hgx]
  rfl
end GlobalTheory.WeilM
