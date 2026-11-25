-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.SecNorm.specializes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:34:39.460742+00:00
-- url     : https://prove2.me/submissions/78af4ddf-e664-4685-9ec2-0abbc41ea00a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EigLat
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsGenericFlag
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_HodgeIPIffHodgeFormConj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder
variable {X : Scheme.{0}} {Ω : Type} [Field Ω]
variable {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]
variable {z : Spec (CommRingCat.of ℂ) ⟶ X}
variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω} {A : HermLine J} {e₀ : Ω}
  {w : (Σ k, J k) → ℂ} {t : Ω} {ν ν' : ℝ}
namespace GlobalTheory.CompanionTheory.Ar
namespace SecNorm
theorem _root_.solution (h : SecNorm ξ y A e₀ z w t ν) : genPt ξ ⤳ centre z := by
  obtain ⟨c, hc⟩ := h.exists_chart
  obtain ⟨u, hu, -⟩ := h.2.2 c hc
  exact hu.1
end SecNorm
end GlobalTheory.CompanionTheory.Ar
