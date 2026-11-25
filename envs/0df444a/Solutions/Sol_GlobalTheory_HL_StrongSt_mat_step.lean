-- Prove2me | solution 1 for GlobalTheory.HL.StrongSt.mat_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:40:37.999572+00:00
-- url     : https://prove2.me/submissions/39d53df8-f1f7-4704-ae26-e6a3f4881e6f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PatternUnitriangularStrongApproximationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LocalCommonStabiliserBlockUnitriangularOnFrameStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BlockUnitriangularRationalFromCommonStabiliserStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameMatrixCloseGivesLatticeCloseIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StrongApproxStab
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.StrongSt
namespace GlobalTheory.HL.StrongSt
theorem _root_.solution {K V : Type} [CommRing K] [AddCommGroup V] [Module K V] {m : ℕ} (v : Fin m → V)
    (n g' : V ≃ₗ[K] V) (s t : Matrix (Fin m) (Fin m) K) (hs : IsUnit s.det)
    (hn : ∀ j, n (v j) = ∑ i, s i j • v i) (hg : ∀ j, g' (v j) = ∑ i, t i j • v i) :
    ∀ j, (n⁻¹ * g') (v j) = ∑ i, (s⁻¹ * t) i j • v i := by
  have hw : ∀ i, n.symm (v i) = ∑ k, s⁻¹ k i • v k := by
    intro i
    apply n.injective
    rw [LinearEquiv.apply_symm_apply, map_sum]
    simp_rw [map_smul, hn, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have h1 : s * s⁻¹ = 1 := Matrix.mul_nonsing_inv s hs
    have : ∀ l, ∑ k, s⁻¹ k i * s l k = (s * s⁻¹) l i := by
      intro l; rw [Matrix.mul_apply]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    simp_rw [← Finset.sum_smul, this, h1, Matrix.one_apply, ite_smul, one_smul, zero_smul]
    simp
  intro j
  change n.symm (g' (v j)) = _
  rw [hg, map_sum]
  simp_rw [map_smul, hw, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun k _ => by congr 1; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
end GlobalTheory.HL.StrongSt
