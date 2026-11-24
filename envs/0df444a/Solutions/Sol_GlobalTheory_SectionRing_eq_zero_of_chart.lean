-- Prove2me | solution 1 for GlobalTheory.SectionRing.eq_zero_of_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:38:54.550944+00:00
-- url     : https://prove2.me/submissions/4219d439-1de5-4717-851d-1651ce676d76

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
variable {K : Type} [Field K] {X : Scheme.{0}} (p : X ⟶ Sp K) (L : LB X)
namespace GlobalTheory.SectionRing
theorem _root_.solution [IsIntegral X] (j₀ : PUnit → L.ι) [Nonempty (chart L j₀)] (e : ℕ)
    (a : Fam p L) (ha : a ∈ secs p L e) (h : evalFam p L j₀ a = 0) : a = 0 := by
  funext j
  change evalFam p L j a = 0
  by_cases hj : Nonempty (chart L j)
  · obtain ⟨x⟩ := hj
    obtain ⟨y⟩ := ‹Nonempty (chart L j₀)›
    obtain ⟨z, hz⟩ := nonempty_preirreducible_inter (chart L j).isOpen (chart L j₀).isOpen
      ⟨x.1, x.2⟩ ⟨y.1, y.2⟩
    haveI : Nonempty (chart L j ⊓ chart L j₀ : X.Opens) := ⟨⟨z, hz⟩⟩
    apply map_injective_of_isIntegral X
      (homOfLE (inf_le_left : chart L j ⊓ chart L j₀ ≤ chart L j))
    have h2 := ha j j₀
    rw [h, map_zero, MulZeroClass.mul_zero] at h2
    exact h2.trans (map_zero _).symm
  · have hb : chart L j = ⊥ := by
      ext x
      exact ⟨fun hx => (hj ⟨⟨x, hx⟩⟩).elim, fun hx => hx.elim⟩
    haveI : Subsingleton Γ(X, chart L j) := by
      rw [hb]
      infer_instance
    exact Subsingleton.elim _ _
end GlobalTheory.SectionRing
