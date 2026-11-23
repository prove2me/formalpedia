-- Prove2me | solution 1 for GlobalTheory.ZH.WtLin.weight_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:23:45.979846+00:00
-- url     : https://prove2.me/submissions/ca4b45de-2e46-4d54-a141-038579941b77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CoeffSymmSum
import Theorems.Thm_GlobalTheory_ZH_WtLin_coeff_symm_sum
import Theorems.Thm_GlobalTheory_ZH_WtLin_app_constFn

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
noncomputable section
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.WtLin
namespace GlobalTheory.ZH.WtLin
theorem _root_.solution {k : Type} [Field k] (Φ : FibPre k) {d : ℕ} {J : Type} [Fintype J]
    (F : J → (Φ.H d).Sec) (a : J → k) (α : Φ.E.X) (l : Φ.N₀.ι) :
    Φ.D.weight (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l) α
        (∑ i, constFn Φ.G.hom ((Φ.H d).U l) (a i) * (F i).f l : Γ(Φ.G.left, (Φ.H d).U l)) =
      ∑ i, constFn Φ.E.B.hom _ (a i) * Φ.wt (F i) α l := by
  refine Eq.trans ?_ (coeff_symm_sum _ _ _ (Φ.D.coord (Φ.ch l) _ (Φ.aff l) (Φ.le l))
    (fun i => constFn Φ.E.B.hom _ (a i)) (fun i => (F i).f l) α)
  simp only [app_constFn _ _ _ (Over.w Φ.D.q)]
  rfl
end GlobalTheory.ZH.WtLin
