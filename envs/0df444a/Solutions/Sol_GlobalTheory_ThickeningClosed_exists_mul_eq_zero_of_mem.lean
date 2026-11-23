-- Prove2me | solution 1 for GlobalTheory.ThickeningClosed.exists_mul_eq_zero_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:35:33.439499+00:00
-- url     : https://prove2.me/submissions/19b73ee1-bb73-47b6-9dd7-b3b572b237e2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasicOpenEqZeroOfMemIInfPowSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoOfIsClosedImmersionOfThickenings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.ThickeningClosed
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ThickeningClosed
namespace _root_.GlobalTheory.ThickeningClosed
theorem _root_.solution {X : Scheme.{0}} (K : X.IdealSheafData)
    (U : X.affineOpens) (q : PrimeSpectrum Γ(X, U))
    (hq : U.2.fromSpec q ∈ _root_.GlobalTheory.ThickeningClosed.zeroLocusOpen K) {a : Γ(X, U)}
    (ha : a ∈ K.ideal U) : ∃ s ∉ q.asIdeal, s * a = 0 := by
  have hq' : ∃ V : X.affineOpens, U.2.fromSpec q ∈ V.1 ∧ K.ideal V = ⊥ := hq
  obtain ⟨V, hyV, hV⟩ := hq'
  have hyU : U.2.fromSpec q ∈ U.1 := by
    have : U.2.fromSpec q ∈ Set.range U.2.fromSpec := ⟨q, rfl⟩
    rwa [U.2.range_fromSpec] at this
  obtain ⟨f, hfV, hyf⟩ := U.2.exists_basicOpen_le (V := V.1) ⟨_, hyV⟩ hyU
  have hW : K.ideal (X.affineBasicOpen f) = ⊥ := by
    rw [← K.map_ideal (U := X.affineBasicOpen f) (V := V) hfV, hV, Ideal.map_bot]
  have hfq : f ∉ q.asIdeal := by
    have : q ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen f := hyf
    rw [U.2.fromSpec_preimage_basicOpen] at this
    exact this
  have ha' := Ideal.mem_map_of_mem (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom ha
  rw [K.map_ideal_basicOpen, hW] at ha'
  have h0 : (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom a = 0 := ha'
  have := U.2.isLocalization_basicOpen f
  obtain ⟨⟨m, n, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f) _ a).mp h0
  exact ⟨f ^ n, fun h ↦ hfq (q.2.mem_of_pow_mem n h), hm⟩
end _root_.GlobalTheory.ThickeningClosed
end GlobalTheory.ThickeningClosed
