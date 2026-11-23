-- Prove2me | solution 1 for GlobalTheory.subset_of_isOpen_of_closedPoints
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:57:49.149257+00:00
-- url     : https://prove2.me/submissions/46828482-5c1b-4846-995e-09f2ef7aefa3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
variable {T : Type*} [TopologicalSpace T] [JacobsonSpace T]
namespace GlobalTheory
theorem _root_.solution {U V : Set T} (hU : IsOpen U) (hV : IsOpen V)
    (h : ∀ x, IsClosed ({x} : Set T) → x ∈ U → x ∈ V) : U ⊆ V := by
  intro y hy
  by_contra hyV
  obtain ⟨x, ⟨hxU, hxV⟩, hx⟩ := nonempty_inter_closedPoints (Z := U ∩ Vᶜ) ⟨y, hy, hyV⟩
    (hU.isLocallyClosed.inter hV.isClosed_compl.isLocallyClosed)
  exact hxV (h x hx hxU)
end GlobalTheory
