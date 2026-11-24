-- Prove2me | solution 1 for GlobalTheory.Principalise.nonempty_compl_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:47:46.360357+00:00
-- url     : https://prove2.me/submissions/4cea6528-43b4-440f-ba24-85119bc907be

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory
open GlobalTheory.Principalise
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
namespace GlobalTheory.Principalise
namespace _root_.GlobalTheory.Principalise
theorem _root_.solution {Y : Scheme.{0}} [IsIntegral Y] {I : Y.IdealSheafData} (hI : I ≠ ⊥) :
    (I.support.compl : Set Y).Nonempty := by
  by_contra hne
  apply hI
  rw [← Scheme.IdealSheafData.support_eq_top_iff]
  ext x
  simp only [Set.not_nonempty_iff_eq_empty] at hne
  have : x ∉ (I.support.compl : Set Y) := by simp [hne]
  simpa using this
end _root_.GlobalTheory.Principalise
end GlobalTheory.Principalise
