-- Prove2me | solution 1 for GlobalTheory.Diag.epsVec_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:14:13.518357+00:00
-- url     : https://prove2.me/submissions/2fa01a2f-840f-412f-b87a-63e516cb0c85

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LeftEqIffLieVecSmul
import Theorems.Thm_GlobalTheory_Diag_epsVec_zero
import Theorems.Thm_GlobalTheory_Diag_epsVec_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR epsScaleR IsTangent IsLieComb IsLieBasis OAct epsPt
  IsLieEigen LieMult)
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)
open TrivSqZeroExt (inl inr)
open GlobalTheory GlobalTheory.Diag
variable {S : Scheme.{0}} {R : Type} [CommRing R] {g : Sp (DualNumber R) ⟶ S}
  {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
namespace GlobalTheory.Diag
theorem _root_.solution {n : ℕ} (c : Fin n → (X →+ R)) :
    epsVec g (∑ i, c i) = (List.ofFn fun i => epsVec g (c i)).prod := by
  induction n with
  | zero => simp [epsVec_zero]
  | succ n ih =>
    rw [Fin.sum_univ_succ, epsVec_add, List.ofFn_succ, List.prod_cons, ih]
end GlobalTheory.Diag
