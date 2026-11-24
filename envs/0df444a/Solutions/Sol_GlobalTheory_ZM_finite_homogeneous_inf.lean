-- Prove2me | solution 1 for GlobalTheory.ZM.finite_homogeneous_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:19:16.532705+00:00
-- url     : https://prove2.me/submissions/63b38b18-05c0-4edb-a4ab-99c347337e81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_ExistsArBaseAway
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf

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
noncomputable section
open GlobalTheory GlobalTheory.ZM
variable {o : Type} [CommRing o] {S : Scheme.{0}} {g : ℕ} {J : Type}
namespace GlobalTheory.ZM
theorem _root_.solution {K σ : Type} [Field K] [Finite σ] (I : Ideal (MvPolynomial σ K)) (e : ℕ) :
    Module.Finite K ↥(MvPolynomial.homogeneousSubmodule σ K e ⊓ I.restrictScalars K) := by
  have : Module.Finite K ↥(MvPolynomial.homogeneousSubmodule σ K e) :=
    Module.Finite.iff_fg.2 (MvPolynomial.homogeneousSubmodule_fg (σ := σ) (R := K) e)
  exact Submodule.finiteDimensional_inf_left _ _
end GlobalTheory.ZM
