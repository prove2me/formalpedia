-- Prove2me | solution 1 for GlobalTheory.SectionRing.isDomain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:38:55.931556+00:00
-- url     : https://prove2.me/submissions/038e1645-cb32-43ff-b6b9-931156e70b5c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MonomialMemReesAlgIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsSectionRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SectionRing
open Polynomial
variable {K A : Type} [Field K] [CommRing A] [Algebra K A]
variable (M : ℕ → Submodule K A) [SetLike.GradedMonoid M]
namespace GlobalTheory.SectionRing
theorem _root_.solution {B : Type} [CommRing B] [IsDomain B] (π : A →+* B)
    (hπ : ∀ n, ∀ a ∈ M n, π a = 0 → a = 0) : IsDomain (polyAlg M) := by
  refine Function.Injective.isDomain ((mapRingHom π).comp (polyAlg M).val.toRingHom) ?_
  rw [injective_iff_map_eq_zero]
  intro r hr
  apply Subtype.ext
  ext n
  have h : (r : A[X]).map π = 0 := hr
  refine hπ n _ (r.2 n) ?_
  rw [← coeff_map, h, coeff_zero]
end GlobalTheory.SectionRing
