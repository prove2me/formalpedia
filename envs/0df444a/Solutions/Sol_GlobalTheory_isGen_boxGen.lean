-- Prove2me | solution 1 for GlobalTheory.isGen_boxGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:24:56.596842+00:00
-- url     : https://prove2.me/submissions/d1cf415f-2917-431f-b6a0-2ec9f39506c2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_GeneratorPullback_PullAlong
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LcgLinCombEqProd
import Theorems.Thm_GlobalTheory_lcg_linComb_eq_prod
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_res_res__b0a8af1c3378

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
private lemma res_res_eq {Z : Scheme.{0}} {U V V' W : Z.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (h₃ : V' ≤ U)
    (h₄ : W ≤ V') (x : Γ(Z, U)ˣ) : res h₂ (res h₁ x) = res h₄ (res h₃ x) := by
  rw [ReciprocityTheory.ChartRestriction.G.DVR.res_res', ReciprocityTheory.ChartRestriction.G.DVR.res_res']
end GlobalTheory
end

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X X' Y : Scheme.{0}} (L : LB X) {J K : Type} [Fintype J] [Fintype K]
    (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε)) (ht : ∀ i, (t i).IsGen) :
    (GeneratorPullback.boxGen L F φ ε t).IsGen := by
  intro a b
  have hg : ((LB.LinComb L F (fun _ => 1)).LinComb φ ε).g a b = _ := lcg_linComb_eq_prod L F φ ε a b
  rw [hg]
  show res (U := LB.wchart (LB.LinComb L F (fun _ => 1)) φ a)
      (V := LB.wchart (LB.LinComb L F (fun _ => 1)) φ a ⊓ LB.wchart (LB.LinComb L F (fun _ => 1)) φ b) _
      (∏ i, res (V := LB.wchart (LB.LinComb L F (fun _ => 1)) φ a) _ ((t i).s fun k _ => a k i)) =
    (∏ i, res (boxGen_overlap_le L F φ a b i)
      (LB.lcg (L.pull (F i)) φ ε (fun k _ => a k i) (fun k _ => b k i))) *
      res (U := LB.wchart (LB.LinComb L F (fun _ => 1)) φ b)
        (V := LB.wchart (LB.LinComb L F (fun _ => 1)) φ a ⊓ LB.wchart (LB.LinComb L F (fun _ => 1)) φ b) _
        (∏ i, res (V := LB.wchart (LB.LinComb L F (fun _ => 1)) φ b) _ ((t i).s fun k _ => b k i))
  simp only [map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have e := (congrArg (res (boxGen_overlap_le L F φ a b i))
    ((ht i) (fun k _ => a k i) (fun k _ => b k i))).trans (map_mul _ _ _)
  refine (res_res_eq _ _ _ _ _).trans (e.trans ?_)
  congr 1
  exact res_res_eq _ _ _ _ _
end GlobalTheory
