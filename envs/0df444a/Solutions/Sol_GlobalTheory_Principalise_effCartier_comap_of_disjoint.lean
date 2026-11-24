-- Prove2me | solution 1 for GlobalTheory.Principalise.effCartier_comap_of_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:47:40.405491+00:00
-- url     : https://prove2.me/submissions/088909fe-df3d-4718-b22d-464a3e2d507b

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
theorem _root_.solution {W X : Scheme.{0}} (g : W ⟶ X) (J : X.IdealSheafData)
    (h : ∀ w, g w ∉ J.support) : _root_.ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap g) := by
  have htop : J.comap g = ⊤ := by
    rw [← Scheme.IdealSheafData.support_eq_bot_iff, Scheme.IdealSheafData.support_comap]
    ext w
    simpa using h w
  intro w
  obtain ⟨_, ⟨V, hV, rfl⟩, hwV, -⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ w) isOpen_univ
  refine ⟨⟨V, hV⟩, 1, hwV, one_mem _, ?_⟩
  rw [htop, Ideal.span_singleton_one]
  simp [Scheme.IdealSheafData.ideal_top]
end _root_.GlobalTheory.Principalise
end GlobalTheory.Principalise
