-- Prove2me | solution 1 for GlobalTheory.SmoothDim.ringKrullDim_eq_of_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:51:58.336355+00:00
-- url     : https://prove2.me/submissions/d8adb5cd-191a-4dda-ac09-2294a8569bc4

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SmoothDim
namespace GlobalTheory.SmoothDim
theorem _root_.solution {A : Type*} [CommRing A] [Nontrivial A] (s : Set A)
    (hs : Ideal.span s = ⊤) (d : WithBot ℕ∞)
    (h : ∀ t ∈ s, Nontrivial (Localization.Away t) → ringKrullDim (Localization.Away t) = d) :
    ringKrullDim A = d := by
  have key : ∀ q : Ideal A, q.IsPrime → ∃ t : A, Disjoint (Submonoid.powers t : Set A) q ∧
      ringKrullDim (Localization.Away t) = d := by
    intro q hq
    obtain ⟨t, hts, htq⟩ : ∃ t ∈ s, t ∉ q := by
      by_contra hc
      push Not at hc
      exact hq.ne_top (top_le_iff.mp (hs ▸ Ideal.span_le.mpr hc))
    have disj : Disjoint (Submonoid.powers t : Set A) (q : Set A) :=
      (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr htq
    have hP := IsLocalization.isPrime_of_isPrime_disjoint (.powers t) (Localization.Away t) _ hq
      disj
    refine ⟨t, disj, h t hts ?_⟩
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact hP.ne_top (Subsingleton.elim _ _)
  apply le_antisymm
  · refine (ringKrullDim_le_iff_height_le d).mpr fun q hq => ?_
    obtain ⟨t, disj, ht⟩ := key q hq
    have hP := IsLocalization.isPrime_of_isPrime_disjoint (.powers t) (Localization.Away t) _ hq
      disj
    rw [← IsLocalization.height_map_of_disjoint (S := Localization.Away t) _ q disj, ← ht]
    exact Ideal.height_le_ringKrullDim_of_isPrime
  · obtain ⟨m, hm⟩ := Ideal.exists_maximal A
    obtain ⟨t, -, ht⟩ := key m hm.isPrime
    rw [← ht]
    refine (ringKrullDim_le_iff_height_le _).mpr fun q hq => ?_
    rw [← IsLocalization.height_under (R := A) (.powers t) q]
    exact Ideal.height_le_ringKrullDim_of_isPrime
end GlobalTheory.SmoothDim
