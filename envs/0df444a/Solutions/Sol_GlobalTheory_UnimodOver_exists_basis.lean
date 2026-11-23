-- Prove2me | solution 1 for GlobalTheory.UnimodOver.exists_basis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:23:20.467365+00:00
-- url     : https://prove2.me/submissions/34ab6c17-8f6f-4135-b8b7-4db5edc3c977

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPolarizedSuperlatticeOfRiemannForm

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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.UnimodOver
open Module
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
namespace GlobalTheory.UnimodOver
theorem _root_.solution (Λ : Submodule ℤ V) [DiscreteTopology Λ]
    (hs : Submodule.span ℝ (Λ : Set V) = ⊤) :
    ∃ (n : ℕ) (b : Basis (Fin n) ℝ V), Submodule.span ℤ (Set.range b) = Λ := by
  haveI : IsZLattice ℝ Λ := ⟨hs⟩
  haveI : Module.Free ℤ Λ := ZLattice.module_free ℝ Λ
  let b := (Module.Free.chooseBasis ℤ Λ).reindex (Fintype.equivFin _)
  exact ⟨_, b.ofZLatticeBasis ℝ Λ, b.ofZLatticeBasis_span ℝ Λ⟩
end GlobalTheory.UnimodOver
