-- Prove2me | solution 1 for GlobalTheory.henselianLocalRing_valuationSubring_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:58:54.786774+00:00
-- url     : https://prove2.me/submissions/7c1b3e1c-de89-4f3d-ae1e-5c49ff7a8482

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsClassicalLiftOfSmooth

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
open GlobalTheory.ZJ
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K : Type*} [Field K] [IsAlgClosed K]
    (V : ValuationSubring K) : HenselianLocalRing V where
  is_henselian f hf a₀ h₁ _ := by
    classical
    have hg : (f.map (algebraMap V K)).Monic := hf.map _
    have hsplit : (f.map (algebraMap V K)).Splits := IsAlgClosed.splits _

    have hev : ((f.eval a₀ : V) : K) =
        ((f.map (algebraMap V K)).roots.map fun r => (a₀ : K) - r).prod := by
      have h1 : ((f.eval a₀ : V) : K) = (f.map (algebraMap V K)).eval (a₀ : K) := by
        rw [Polynomial.eval_map]
        exact (Polynomial.eval₂_at_apply (algebraMap V K) a₀).symm
      rw [h1]
      exact hsplit.eval_eq_prod_roots_of_monic hg _
    have hlt : V.valuation (((f.map (algebraMap V K)).roots.map fun r => (a₀ : K) - r).prod) < 1 := by
      rw [← hev]
      exact (ValuationSubring.valuation_lt_one_iff V _).mp h₁
    rw [map_multiset_prod, Multiset.map_map] at hlt

    obtain ⟨r, hr, hrlt⟩ : ∃ r ∈ (f.map (algebraMap V K)).roots, V.valuation ((a₀ : K) - r) < 1 := by
      by_contra hcon
      push Not at hcon
      refine absurd hlt (not_lt.mpr (Multiset.one_le_prod_of_one_le ?_))
      simp only [Multiset.mem_map, Function.comp_apply]
      rintro _ ⟨s, hs, rfl⟩
      exact hcon s hs
    have hrV : r ∈ V := by
      rw [← V.valuation_le_one_iff]
      have h2 : r = (a₀ : K) - ((a₀ : K) - r) := by ring
      rw [h2]
      exact (Valuation.map_sub _ _ _).trans (max_le (V.valuation_le_one a₀) hrlt.le)
    refine ⟨⟨r, hrV⟩, ?_, ?_⟩
    · have hroot := (Polynomial.mem_roots hg.ne_zero).mp hr
      show Polynomial.eval _ f = 0
      apply Subtype.ext
      have h3 := Polynomial.eval₂_at_apply (p := f) (algebraMap V K) (⟨r, hrV⟩ : V)
      rw [← Polynomial.eval_map] at h3
      simpa using h3.symm.trans hroot
    · rw [ValuationSubring.valuation_lt_one_iff]
      have h4 : ((((⟨r, hrV⟩ : V) - a₀ : V)) : K) = r - a₀ := rfl
      rw [h4, Valuation.map_sub_swap]
      exact hrlt
end GlobalTheory
