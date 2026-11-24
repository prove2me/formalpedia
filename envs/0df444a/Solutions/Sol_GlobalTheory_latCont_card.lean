-- Prove2me | solution 1 for GlobalTheory.latCont_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:14:42.656287+00:00
-- url     : https://prove2.me/submissions/30da2f48-2297-4f05-8d57-71d684da43ff

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LatContMapContinuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {La E J : Type} [AddCommGroup La] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Fintype J] (e : Module.Basis J ℤ La) (p : La →+ E)
    (hd : DiscreteTopology p.range) (hi : Function.Injective p)
    (hs : Submodule.span ℝ (Set.range p) = ⊤) :
    Module.finrank ℝ (J → ℝ) = Module.finrank ℝ E := by
  let L : Submodule ℤ E := AddSubgroup.toIntSubmodule p.range
  have : DiscreteTopology L := hd
  have : IsZLattice ℝ L := ⟨by simpa [L] using hs⟩
  have h1 : Module.finrank ℤ L = Module.finrank ℝ E := ZLattice.rank (K := ℝ) (L := L)
  have hL : LinearMap.range p.toIntLinearMap = L := by
    ext x
    simp [L]
  have h2 : Module.finrank ℤ La = Module.finrank ℤ L := by
    rw [← hL]
    exact (LinearEquiv.ofInjective p.toIntLinearMap hi).finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, ← Module.finrank_eq_card_basis e, h2, h1]
end GlobalTheory
