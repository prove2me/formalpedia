-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.linComb_g_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:40:25.391827+00:00
-- url     : https://prove2.me/submissions/f720d6bf-3ccc-4184-b2bb-00db386cebe6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_SpecialFibreUnits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
namespace GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits
theorem _root_.solution {Y Z : Scheme.{0}} (D : LB Z) (h1 : ∀ a b, D.g a b = 1) {K : Type}
    [Fintype K] (φ : K → (Y ⟶ Z)) (ε : K → ℤ) (i j : K → D.ι) :
    (LB.LinComb D φ ε).g i j = 1 := by
  have key : ∀ (W : Y.Opens) (k : K) (hh : W ≤ φ k ⁻¹ᵁ (D.U (i k) ⊓ D.U (j k))),
      res hh (pullU (φ k) _ (D.g (i k) (j k))) ^ (ε k) = 1 := by
    intro W k hh
    rw [h1, map_one, map_one, one_zpow]
  exact @Finset.prod_eq_one K (Γ(Y, D.wchart φ i ⊓ D.wchart φ j)ˣ) _ _ _ (fun k _ => key _ k _)
end GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits
