-- Prove2me | solution 1 for GlobalTheory.HL.GoodAlmostAll.lead_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:36:35.082055+00:00
-- url     : https://prove2.me/submissions/ff84fa3a-7d27-41b2-b27c-3468c5a2f1a6

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
namespace GlobalTheory.HL.GoodAlmostAll
theorem _root_.solution {R R' : Type} [CommRing R] [CommRing R'] (ι : R' →+* R) {N : ℕ}
    (Z : Matrix (Fin N) (Fin N) R') (Z' : Matrix (Fin N) (Fin N) R) (β : ℕ → R)
    (h : ∀ a b, Z' a b = β b * β a * ι (Z a b)) (l : Fin (N + 1)) :
    lead Z' l = (∏ i ∈ Finset.range l, β i) ^ 2 * ι (lead Z l) := by
  unfold lead
  set e := Fin.castLE (Nat.lt_succ_iff.mp l.2)
  have h1 : Z'.submatrix e e = Matrix.of fun i j => β (e j) *
      (Matrix.of fun i j => β (e i) * ((Z.submatrix e e).map ι) i j) i j := by
    ext i j
    simp only [Matrix.submatrix_apply, h, Matrix.of_apply, Matrix.map_apply]
    ring
  rw [h1, Matrix.det_mul_row, Matrix.det_mul_column, RingHom.map_det, RingHom.mapMatrix_apply]
  have h2 : ∏ i : Fin l, β (e i) = ∏ i ∈ Finset.range l, β i := by
    rw [← Fin.prod_univ_eq_prod_range]
    rfl
  rw [h2]
  ring
end GlobalTheory.HL.GoodAlmostAll
