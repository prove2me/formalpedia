-- Prove2me | solution 1 for GlobalTheory.PeriodChart.finrank_of_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:21:16.723835+00:00
-- url     : https://prove2.me/submissions/c6aa51c9-afd1-47d6-a699-0e2e7ddfb4c3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsContraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.PeriodChart
section Abstract
variable {V : Type} [AddCommGroup V] [Module ℂ V]
end Abstract
section Mat
variable {g : ℕ}
variable {M : Type} [AddCommGroup M]
private theorem discrete_range_toIntLinearMap_of_discrete_range (P : M →+ (Fin g → ℂ)) (hd : DiscreteTopology P.range) :
    DiscreteTopology (LinearMap.range P.toIntLinearMap) := by
  have hm : ∀ x : LinearMap.range P.toIntLinearMap, (x : Fin g → ℂ) ∈ P.range := by
    rintro ⟨x, hx⟩
    obtain ⟨a, rfl⟩ := LinearMap.mem_range.mp hx
    exact AddMonoidHom.mem_range.mpr ⟨a, rfl⟩
  exact DiscreteTopology.of_continuous_injective
    (f := fun x => (⟨x, hm x⟩ : P.range)) (continuous_subtype_val.subtype_mk _)
    (fun x y hxy => Subtype.ext (congrArg Subtype.val hxy))
end Mat
section Period
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ}
variable {D : Datum H} {ty : Fin g → (E →+* ℂ)}
end Period
end GlobalTheory.PeriodChart
end

set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodChart
variable {g : ℕ}
variable {M : Type} [AddCommGroup M]
namespace GlobalTheory.PeriodChart
theorem _root_.solution (P : M →+ (Fin g → ℂ)) (hi : Function.Injective P)
    (hd : DiscreteTopology P.range) (hs : Submodule.span ℝ (Set.range P) = ⊤) :
    finrank ℤ M = finrank ℝ (Fin g → ℂ) := by
  have : DiscreteTopology (LinearMap.range P.toIntLinearMap) := discrete_range_toIntLinearMap_of_discrete_range P hd
  have : IsZLattice ℝ (LinearMap.range P.toIntLinearMap) := ⟨by
    rw [LinearMap.coe_range]; exact hs⟩
  rw [(LinearEquiv.ofInjective P.toIntLinearMap hi).finrank_eq]
  exact ZLattice.rank ℝ _
end GlobalTheory.PeriodChart
