-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.matW_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:12:06.691479+00:00
-- url     : https://prove2.me/submissions/36842794-a77a-485a-8d28-33629ff3f570

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_NoLocalInvariants

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts
open NumberField IsDedekindDomain Polynomial Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
namespace GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts
theorem _root_.solution (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (g h : G H.E N.Om) :
    matW N i ρ (g * h) = matW N i ρ g * matW N i ρ h := by
  unfold matW
  rw [← Matrix.map_mul, smul_mul_smul_comm, map_mul, map_mul, mul_inv, Units.val_mul, Units.val_mul]
end GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts
