-- Prove2me | solution 1 for GlobalTheory.LocalInv.matK_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:07:22.101824+00:00
-- url     : https://prove2.me/submissions/c99c20b1-f128-4ecf-b5e9-339088c93c37

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_NoLocalInvariants
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_TemperedRepresentations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_WeightRegularOfExt
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
theorem _root_.solution (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (g : G H.E N.Om) :
    matK N i ρ g = algebraMap (N.O i) (Kf N i) ((N.chi i 1 g : (N.O i)ˣ) : N.O i) • matW N i ρ g := by
  ext a b
  simp only [matK, matW, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  rw [← map_mul, ← mul_assoc, Units.mul_inv, one_mul]
end GlobalTheory.LocalInv
