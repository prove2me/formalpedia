-- Prove2me | solution 1 for GlobalTheory.ZM.dimDeg_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:31:55.275161+00:00
-- url     : https://prove2.me/submissions/64ee9629-3494-40c1-b4f3-60a65628595e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_ExistsArBaseAway
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Theorems.Thm_GlobalTheory_ZM_finite_homogeneous_inf

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
    dimDeg I e = 0 ↔ ∀ F ∈ I, F.IsHomogeneous e → F = 0 := by
  haveI := finite_homogeneous_inf I e
  unfold dimDeg
  rw [Submodule.finrank_eq_zero, Submodule.eq_bot_iff]
  constructor
  · intro h F hF hd
    exact h F ⟨(MvPolynomial.mem_homogeneousSubmodule e F).2 hd, hF⟩
  · rintro h F ⟨hd, hF⟩
    exact h F hF ((MvPolynomial.mem_homogeneousSubmodule e F).1 hd)
end GlobalTheory.ZM
