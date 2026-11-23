-- Prove2me | solution 1 for GlobalTheory.reduced_finiteType_iff_testRing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:35:15.947156+00:00
-- url     : https://prove2.me/submissions/47b94a5c-4034-445c-a6d0-3f1b5f1711ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ReducedFiniteTypeIffTestRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [Field K], (∀ (R : Type) [CommRing R] [Algebra K R], Algebra.FiniteType K R → IsReduced R → ∃ p : TRing K, Nonempty (p.R ≃ₐ[K] R)) ∧ ∀ p : TRing K, Algebra.FiniteType K p.R ∧ IsReduced p.R := by
  intro K _
  refine ⟨fun R _ _ hft hred => ?_, fun p => ⟨inferInstance, ?_⟩⟩
  · obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hft
    have hrad : (RingHom.ker f).IsRadical := by
      intro x hx
      obtain ⟨m, hm⟩ := hx
      rw [RingHom.mem_ker, map_pow] at hm
      exact (RingHom.mem_ker).2 (IsReduced.eq_zero _ ⟨m, hm⟩)
    exact ⟨⟨n, RingHom.ker f, hrad⟩, ⟨Ideal.quotientKerAlgEquivOfSurjective hf⟩⟩
  · exact (Ideal.isRadical_iff_quotient_reduced p.I).1 p.3
end GlobalTheory
