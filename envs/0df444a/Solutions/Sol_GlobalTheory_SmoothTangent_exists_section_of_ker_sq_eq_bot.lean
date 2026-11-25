-- Prove2me | solution 1 for GlobalTheory.SmoothTangent.exists_section_of_ker_sq_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:57:49.188198+00:00
-- url     : https://prove2.me/submissions/eb7d0819-6a18-4bb6-a412-82174359c827

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfDimOfFinrankDerivatio

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
open GlobalTheory GlobalTheory.SmoothTangent
namespace GlobalTheory.SmoothTangent
theorem _root_.solution {k B F : Type*} [CommRing k] [CommRing B] [CommRing F]
    [Algebra k B] [Algebra k F] [Algebra.FormallySmooth k F] (π : B →ₐ[k] F)
    (hπ : Function.Surjective π) (h : RingHom.ker π.toRingHom ^ 2 = ⊥) :
    ∃ g : F →ₐ[k] B, π.comp g = AlgHom.id k F :=
  ⟨_, Algebra.FormallySmooth.comp_liftOfSurjective (AlgHom.id k F) π hπ ⟨2, h⟩⟩
end GlobalTheory.SmoothTangent
