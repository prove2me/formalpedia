-- Prove2me | solution 1 for GlobalTheory.SectionRing.mono_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:38:57.543801+00:00
-- url     : https://prove2.me/submissions/d88f0d49-127e-426e-a68a-aa1d140d9a3c

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
theorem _root_.solution (e : ℕ) : Function.Injective (mono M e) := fun a b h =>
  Subtype.ext (monomial_injective e (congrArg Subtype.val h))
end GlobalTheory.SectionRing
