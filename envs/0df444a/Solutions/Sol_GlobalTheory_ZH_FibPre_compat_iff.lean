-- Prove2me | solution 1 for GlobalTheory.ZH.FibPre.compat_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:17:53.227569+00:00
-- url     : https://prove2.me/submissions/abb4b49f-6540-4b3a-a247-2d7227008a6f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_EqOfWeightEq
import Theorems.Thm_GlobalTheory_ZH_app_res
import Theorems.Thm_GlobalTheory_FunDescent_app_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.ZH
namespace GlobalTheory.ZH
namespace FibPre
theorem _root_.solution {k : Type} [Field k] (Φ : FibPre k) (t : ∀ l, Γ(Φ.E.B.left, Φ.N₀.U l))
    (i j : Φ.N₀.ι) :
    ((Φ.G.left.presheaf.map (homOfLE (inf_le_left : (Φ.H 1).U i ⊓ (Φ.H 1).U j ≤ (Φ.H 1).U i)).op).hom
        ((Φ.D.q.left.app (Φ.N₀.U i)).hom (t i)) =
      ((Φ.H 1).g i j : Γ(Φ.G.left, (Φ.H 1).U i ⊓ (Φ.H 1).U j)) *
        (Φ.G.left.presheaf.map (homOfLE (inf_le_right : (Φ.H 1).U i ⊓ (Φ.H 1).U j ≤ (Φ.H 1).U j)).op).hom
          ((Φ.D.q.left.app (Φ.N₀.U j)).hom (t j))) ↔
    (Φ.E.B.left.presheaf.map (homOfLE (inf_le_left : Φ.N₀.U i ⊓ Φ.N₀.U j ≤ Φ.N₀.U i)).op).hom (t i) =
      (Φ.N₀.g i j : Γ(Φ.E.B.left, Φ.N₀.U i ⊓ Φ.N₀.U j)) *
        (Φ.E.B.left.presheaf.map (homOfLE (inf_le_right : Φ.N₀.U i ⊓ Φ.N₀.U j ≤ Φ.N₀.U j)).op).hom (t j) := by
  have := Φ.D.q_flat
  have := Φ.D.q_surjective
  rw [← (GlobalTheory.FunDescent.app_injective Φ.D.q.left (Φ.N₀.U i ⊓ Φ.N₀.U j)).eq_iff, map_mul,
    app_res _ _ (Φ.D.q.left.preimage_mono inf_le_left), app_res _ _ (Φ.D.q.left.preimage_mono inf_le_right)]
  have hg : ((Φ.H 1).g i j : Γ(Φ.G.left, (Φ.H 1).U i ⊓ (Φ.H 1).U j)) =
      (Φ.D.q.left.app (Φ.N₀.U i ⊓ Φ.N₀.U j)).hom (Φ.N₀.g i j) :=
    congrArg Units.val (pow_one (pullU Φ.D.q.left (Φ.N₀.U i ⊓ Φ.N₀.U j) (Φ.N₀.g i j)))
  rw [hg]
  exact Iff.rfl
end FibPre
end GlobalTheory.ZH
