-- Prove2me | solution 1 for GlobalTheory.FibreLinInd.mem_basicOpen_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:13.489569+00:00
-- url     : https://prove2.me/submissions/76ef364b-8bb4-407a-a1b7-907bac6dabe6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsOpenSetOfLinearIndependentOnFibres

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.FibreLinInd
variable {K : Type} [Field K] {P G : Scheme.{0}}
namespace GlobalTheory.FibreLinInd
theorem _root_.solution (h : Sp K ⟶ P) (U : P.Opens) (hU : ⊤ ≤ h ⁻¹ᵁ U) (D : Γ(P, U))
    (t : Sp K) : h t ∈ P.basicOpen D ↔ evalHom h U hU D ≠ 0 := by
  have e : (Sp K).basicOpen (h.appLE U ⊤ hU D) = h ⁻¹ᵁ P.basicOpen D := by
    rw [Scheme.basicOpen_appLE, top_inf_eq]
  have hinj : Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.bijective
  change t ∈ h ⁻¹ᵁ P.basicOpen D ↔ _
  rw [← e]
  constructor
  · intro ht h0
    have : h.appLE U ⊤ hU D = 0 := hinj.1 (by rw [map_zero]; exact h0)
    rw [this, Scheme.basicOpen_zero] at ht
    exact ht
  · intro h0
    have : IsUnit (h.appLE U ⊤ hU D) :=
      (MulEquiv.isUnit_map
        (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv).1 (IsUnit.mk0 _ h0)
    rw [Scheme.basicOpen_of_isUnit _ this]
    trivial
end GlobalTheory.FibreLinInd
