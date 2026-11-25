-- Prove2me | solution 1 for GlobalTheory.HL.RatStab.loc_of_glob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:44:47.911416+00:00
-- url     : https://prove2.me/submissions/098747af-ebf2-4b71-b267-7a160c75d567

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianStabiliserRationalUnitriangularPairs
import Theorems.Thm_GlobalTheory_HL_RatStab_sc_mul_sci
import Theorems.Thm_GlobalTheory_HL_RatStab_bc_sum
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
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.RatStab
open GlobalTheory.HL.FrameStab
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) (p : HeightOneSpectrum (𝓞 F))
namespace GlobalTheory.HL.RatStab
theorem _root_.solution (u : Fin (r + 1) → Fin (k + 2 * r + 1) → (A.loc p).Ep) (v : Fin (r + 1) → G.V)
    (hu : ∀ a, u a = sc G p a • A.bc p (v a)) (s : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (h : G.GLV)
    (h' : (Fin (k + 2 * r + 1) → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin (k + 2 * r + 1) → (A.loc p).Ep))
    (hE : A.Ext p h h') (hv : ∀ j, h (v j) = ∑ i, s i j • v i) (j : Fin (r + 1)) :
    h' (u j) = ∑ i, locM G p s i j • u i := by
  rw [hu j, map_smul, hE, hv j, bc_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hu i, smul_smul, smul_smul]
  congr 1
  simp only [locM, Matrix.of_apply]
  linear_combination (-(sc G p j * (A.loc p).ιE (s i j))) * sc_mul_sci G p i
end GlobalTheory.HL.RatStab
