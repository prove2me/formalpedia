-- Prove2me | solution 1 for GlobalTheory.HL.GoodAlmostAll.G_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:53:27.517655+00:00
-- url     : https://prove2.me/submissions/5be4b7c2-2d98-44ae-8257-b7cda938c1ff

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEquivOfRetractions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SelfDualLatticeUnipotentTranslateStandard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnesses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesStabilizerActsOnTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesComplementUnitaryActsOnTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsGluingHomomorphismDefectGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UnitEntries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntegralOfMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HmUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_GlobalHermitianFramesGoodAlmostAllPlaces
import Theorems.Thm_GlobalTheory_HL_GoodAlmostAll_sc_last
import Theorems.Thm_GlobalTheory_HL_GoodAlmostAll_cj_sc
import Theorems.Thm_P2M_GlobalTheory_HL_GoodAlmostAll_cj___6605cd95568a
import Theorems.Thm_GlobalTheory_HL_GoodAlmostAll_D_scale
import Theorems.Thm_GlobalTheory_HL_GoodAlmostAll_TT_eq
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.GoodAlmostAll
open GlobalTheory.HL.GoodClass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) (p : HeightOneSpectrum (𝓞 F))
namespace GlobalTheory.HL.GoodAlmostAll
theorem _root_.solution : (G.S p).G = (∏ i ∈ Finset.range r, sc G p i) ^ 4 * (A.loc p).ιE G.Gr := by
  have hP : ∏ i ∈ Finset.range (r + 1), sc G p i = ∏ i ∈ Finset.range r, sc G p i := by
    rw [Finset.prod_range_succ, sc_last, mul_one]
  have hcj : (A.L p).cj (∏ i ∈ Finset.range r, sc G p i) = ∏ i ∈ Finset.range r, sc G p i := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun i _ => cj_sc G p i
  unfold Frames.G
  rw [D_scale, D_scale, TT_eq]
  simp only [Fin.val_last, Fin.coe_castSucc, hP, map_mul, map_pow, hcj, cj_ι, GFrames.Gr, map_sub]
  ring
end GlobalTheory.HL.GoodAlmostAll
