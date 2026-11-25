-- Prove2me | solution 1 for GlobalTheory.MixedSignature.step_of_right_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:16:54.400464+00:00
-- url     : https://prove2.me/submissions/313e0795-df56-421b-8878-925015f55c8c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralBasisReduction
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianLatticeMaps
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetNeZeroOfIsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FinMuOfFiniteCovolume
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIntMulIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MahlerCompactness
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsStabiliserImageSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_OrthonormalFramesBoundedOfDefinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_IsOrthUpdateMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FrameStepOfRightMulRealUnitaryGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_OrthonormalFramesBoundedOfDefinite
import Theorems.Thm_GlobalTheory_MixedSignature_conj_unitary
import Theorems.Thm_GlobalTheory_FiniteCovolume_embGL_val
import Theorems.Thm_GlobalTheory_FiniteCovolume_hermC_eq_dotProduct
import Theorems.Thm_GlobalTheory_FiniteCovolume_inv_keeps_gram
import Theorems.Thm_GlobalTheory_FlagMahler_finite_bounded
import Theorems.Thm_GlobalTheory_IntegralMultiples_exists_int_smul_mem
import Theorems.Thm_GlobalTheory_LatFin_exists_common_den
import Theorems.Thm_GlobalTheory_LatFin_exists_int_smul_mem
import Theorems.Thm_GlobalTheory_LatFin_finite_bounded
import Theorems.Thm_GlobalTheory_UnitaryFrames_hermC_eq_dot
import Theorems.Thm_GlobalTheory_UnitaryFrames_hermC_mulVec
import Theorems.Thm_GlobalTheory_UnitaryFrames_locallyCompact_GL
import Theorems.Thm_GlobalTheory_UnitaryFrames_secondCountable_GL
import Theorems.Thm_GlobalTheory_UnitaryLift_conj_unitary
import Theorems.Thm_GlobalTheory_UnitaryLift_det_ne_zero_of_diag
import Theorems.Thm_P2M_GlobalTheory_UnitaryFrames_col_mul__08ccc1f94cd1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix ComplexConjugate
open GlobalTheory GlobalTheory.MixedSignature
open GlobalTheory.UnitaryFrames (hermC_eq_dot gram_eq_mul hermC_mulVec col_mul' locallyCompact_GL secondCountable_GL)
open GlobalTheory.FiniteCovolume (inv_keeps_gram embGL embGL_val hermC_eq_dotProduct uStabSubgroup)
open GlobalTheory.UnitaryLift (det_ne_zero_of_diag)
open GlobalTheory.LatFin (exists_common_den exists_int_smul_mem finite_bounded)
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.MixedSignature
theorem _root_.solution :
    (∀ (r : ℕ) (X : Data E r) {G : Matrix (Fin r) (Fin r) E} {p : X.Ψ → ℕ} (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ Uni X G fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ x0, Orth X G p x0 → ∀ (τ0 : X.Ψ) (a s : Matrix (Fin r) (Fin r) ℂ), (a)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p τ0 then (1 : ℂ) else -1) * (a).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p τ0 then (1 : ℂ) else -1) → (s)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p τ0 then (1 : ℂ) else -1) * (s).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p τ0 then (1 : ℂ) else -1) → s * a = a⁻¹ * s → ∃ h k : H, k * h = h⁻¹ * k ∧ ∀ g : H, (X.lmulC (fun τ => (((g * h : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) = (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) (X.lmulC (fun τ => (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) τ0 (mat (X.lmulC (fun τ => (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ))) := by
  intro r X G p H hH x0 hx0 τ0 a s ha hs hsa
  letI : DecidableEq X.Ψ := Classical.decEq _
  have hda := det_ne_zero_of_diag ha
  let A : GL (Fin r) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero a hda
  let S : GL (Fin r) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero s (det_ne_zero_of_diag hs)
  have hAi : ((A⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = a⁻¹ := by
    rw [Matrix.coe_units_inv]; rfl
  have hSA : S * A = A⁻¹ * S := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hAi]
    exact hsa
  have hSA' : S * A⁻¹ = A * S := by
    calc S * A⁻¹ = A * (A⁻¹ * S) * A⁻¹ := by group
      _ = A * S := by rw [← hSA]; group
  have hmem : ∀ b : GL (Fin r) ℂ, (b : Matrix (Fin r) (Fin r) ℂ)ᵀ *
      (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p τ0 then (1 : ℂ) else -1) *
      (b : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) =
      (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p τ0 then (1 : ℂ) else -1) →
      toGL X hx0 * Pi.mulSingle τ0 b * (toGL X hx0)⁻¹ ∈ H := by
    intro b hb
    refine (hH _).2 (conj_unitary X hx0 _ fun τ => ?_)
    by_cases h : τ = τ0
    · subst h
      rw [Pi.mulSingle_eq_same]
      exact hb
    · rw [Pi.mulSingle_eq_of_ne h]
      simp
  refine ⟨(⟨_, hmem A ha⟩ : H)⁻¹, ⟨_, hmem S hs⟩, ?_, fun g => ?_⟩
  · apply Subtype.ext
    have h1 : (Pi.mulSingle τ0 S * (Pi.mulSingle τ0 A)⁻¹ : X.Ψ → GL (Fin r) ℂ) =
        Pi.mulSingle τ0 A * Pi.mulSingle τ0 S := by
      rw [← Pi.mulSingle_inv, ← Pi.mulSingle_mul, ← Pi.mulSingle_mul, hSA']
    simp only [inv_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    calc _ = toGL X hx0 * (Pi.mulSingle τ0 S * (Pi.mulSingle τ0 A)⁻¹) * (toGL X hx0)⁻¹ := by group
      _ = _ := by rw [h1]; group
  · have key : ((g * (⟨_, hmem A ha⟩ : H)⁻¹ : H) : X.Ψ → GL (Fin r) ℂ) * toGL X hx0 =
        (g : X.Ψ → GL (Fin r) ℂ) * toGL X hx0 * Pi.mulSingle τ0 A⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Pi.mulSingle_inv]
      group
    funext τ
    have k1 := congrArg (fun u : X.Ψ → GL (Fin r) ℂ => (u τ : Matrix (Fin r) (Fin r) ℂ)) key
    refine k1.trans ?_
    beta_reduce
    rw [Pi.mul_apply, Pi.mul_apply, Units.val_mul, Units.val_mul]
    by_cases h : τ = τ0
    · subst h
      rw [Pi.mulSingle_eq_same, hAi]
      exact Eq.symm (@Function.update_self X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) _ _ _)
    · rw [Pi.mulSingle_eq_of_ne h, Units.val_one, Matrix.mul_one]
      exact Eq.symm (@Function.update_of_ne X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) _ _ h _ _)
end GlobalTheory.MixedSignature
