-- Prove2me | solution 1 for GlobalTheory.FinrankGrowthBounds.finite_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:08:05.546282+00:00
-- url     : https://prove2.me/submissions/6000396a-fc03-439a-a131-7bb14a61443c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FinrankSectionsLineBundlePowEqPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory GlobalTheory.FinrankGrowthBounds
open Filter Topology
namespace GlobalTheory.FinrankGrowthBounds
theorem _root_.solution {R : Type*} [Field R] {M I : Type*} [AddCommGroup M] [Module R M]
    [Nontrivial M] [Module.Finite R (I → M)] : Finite I := by
  classical
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  have : LinearIndependent R (fun i : I => (Pi.single i m : I → M)) := by
    rw [linearIndependent_iff']
    intro s c hc i hi
    have := congrFun hc i
    rw [Finset.sum_apply, Finset.sum_eq_single i] at this
    · simpa [hm] using this
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb.symm]
    · exact fun x => (x hi).elim
  exact this.finite
end GlobalTheory.FinrankGrowthBounds
