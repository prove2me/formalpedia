-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.UniformizationClosedSplit.PrimeToLevel.not_mem_M
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:54:43.951043+00:00
-- url     : https://prove2.me/submissions/5e766eab-b1ab-4502-a9d6-8194383f501f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ChartDirectionsIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_UniformizationClosedSplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.UniformizationClosedSplit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
variable {Xo c}
namespace GlobalTheory.IndefiniteRowSideFullHecke.UniformizationClosedSplit
namespace PrimeToLevel
theorem _root_.solution {la : HeightOneSpectrum (𝓞 c.F)} (h : PrimeToLevel c la) :
    ((l.M : ℕ) : 𝓞 c.F) ∉ la.asIdeal := by
  intro hM
  apply h
  obtain ⟨k, hk⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
  rw [hk, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hM
end PrimeToLevel
end GlobalTheory.IndefiniteRowSideFullHecke.UniformizationClosedSplit
