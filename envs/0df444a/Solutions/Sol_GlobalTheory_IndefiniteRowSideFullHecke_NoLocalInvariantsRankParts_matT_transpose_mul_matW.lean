-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.matT_transpose_mul_matW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:54:16.240003+00:00
-- url     : https://prove2.me/submissions/428266e1-ee11-4a83-8b23-8eb048b76a33

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_NoLocalInvariants
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_NoLocalInvariantsRankParts_matW_mul
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_NoLocalInvariantsRankParts_matW_one

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
theorem _root_.solution (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i))
    (g : G H.E N.Om) :
    (matT N i ρ g)ᵀ * matW N i ρ g =
      algebraMap (N.O i) (Kf N i) ((eps N i g : (N.O i)ˣ) : N.O i) • (1 : Matrix _ _ (Kf N i)) := by
  unfold matT
  rw [Matrix.transpose_smul, Matrix.transpose_transpose, Matrix.smul_mul, ← matW_mul, inv_mul_cancel,
    matW_one]
end GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts
