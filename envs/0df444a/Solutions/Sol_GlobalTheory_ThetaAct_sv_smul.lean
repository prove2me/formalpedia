-- Prove2me | solution 1 for GlobalTheory.ThetaAct.sv_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:38.230827+00:00
-- url     : https://prove2.me/submissions/8f40aebb-d15c-4dd2-8ecf-2202c8e9bb17

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThetaAct
open GlobalTheory.CommPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ} {T : Over S}
namespace GlobalTheory.ThetaAct
theorem _root_.solution (c : Γ(T.left, ⊤)) (v : SecM A L k T) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J}
    (hJ : Good L z J) : sv (c • v) r z J = gs (r ≫ (fst T A).left) z ⊤ c * sv v r z J := by
  have hm := hJ.mem (fun _ : Fin 1 => (snd T A).left) r
  exact (gs_mul r z _ hm _ _).trans (congrArg (· * sv v r z J)
    ((gs_res r z le_top hm _).trans (gs_pull r (fst T A).left z ⊤ trivial c)))
end GlobalTheory.ThetaAct
