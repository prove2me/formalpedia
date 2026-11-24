-- Prove2me | solution 1 for GlobalTheory.LocalInv.charRep_ss
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:41:31.201352+00:00
-- url     : https://prove2.me/submissions/89bfabc1-c327-44f5-a971-65fd15627034

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_NoLocalInvariants
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_TemperedRepresentations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_WeightRegularOfExt
import Theorems.Thm_GlobalTheory_LocalInv_charRep_val
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LocalInv
open NumberField IsDedekindDomain Polynomial Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
namespace GlobalTheory.LocalInv
theorem _root_.solution (i : N.Loc) (χ : G H.E N.Om →* (N.O i)ˣ) :
    IsSSRep (mapRep (algebraMap (N.O i) (Kf N i)) (charRep N i χ)) := by
  intro W _
  obtain ⟨W', h⟩ := W.exists_isCompl
  refine ⟨W', fun g v hv => ?_, h⟩
  have : ((mapRep (algebraMap (N.O i) (Kf N i)) (charRep N i χ) g : GL (Fin 1) (Kf N i)) :
      Matrix (Fin 1) (Fin 1) (Kf N i)).mulVec v =
      algebraMap (N.O i) (Kf N i) ((χ g : (N.O i)ˣ) : N.O i) • v := by
    ext a
    obtain rfl : a = 0 := Subsingleton.elim _ _
    simp [mapRep, charRep_val, Matrix.mulVec, dotProduct]
  rw [this]
  exact W'.smul_mem _ hv
end GlobalTheory.LocalInv
