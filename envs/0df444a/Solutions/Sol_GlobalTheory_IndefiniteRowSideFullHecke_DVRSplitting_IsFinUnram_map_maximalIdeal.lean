-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.DVRSplitting.IsFinUnram.map_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:59:46.669309+00:00
-- url     : https://prove2.me/submissions/7fbb6370-fe22-4863-9223-2b01e9eaad23

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_DVRSplitting

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.DVRSplitting
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
namespace GlobalTheory.IndefiniteRowSideFullHecke.DVRSplitting
namespace IsFinUnram
theorem _root_.solution {V W : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Algebra V W] (h : IsFinUnram V W) :
    IsLocalHom (algebraMap V W) ∧ (maximalIdeal V).map (algebraMap V W) = maximalIdeal W := by
  obtain ⟨hi, hf, hu⟩ := h
  have : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective V W).mpr hi
  have : IsLocalHom (algebraMap V W) := inferInstance
  exact ⟨this, Algebra.FormallyUnramified.map_maximalIdeal⟩
end IsFinUnram
end GlobalTheory.IndefiniteRowSideFullHecke.DVRSplitting
