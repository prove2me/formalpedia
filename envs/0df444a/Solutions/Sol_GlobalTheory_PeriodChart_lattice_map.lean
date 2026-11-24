-- Prove2me | solution 1 for GlobalTheory.PeriodChart.lattice_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:21:18.422731+00:00
-- url     : https://prove2.me/submissions/b96e3075-b81b-4198-a43b-f81b11f6df06

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
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodChart
variable {g : ℕ}
variable {M : Type} [AddCommGroup M]
namespace GlobalTheory.PeriodChart
theorem _root_.solution (P P' : M →+ (Fin g → ℂ)) (hi : Function.Injective P)
    (hd : DiscreteTopology P.range) (hs : Submodule.span ℝ (Set.range P) = ⊤)
    (T : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)) (hT : Function.Injective T) (h : ∀ a, P' a = T (P a)) :
    Function.Injective P' ∧ DiscreteTopology P'.range ∧ Submodule.span ℝ (Set.range P') = ⊤ := by
  have hTs : Function.Surjective T := LinearMap.injective_iff_surjective.mp hT
  have hP' : ⇑P' = T ∘ P := funext h
  refine ⟨?_, ?_, ?_⟩
  · rw [hP']; exact hT.comp hi
  · obtain ⟨G, hG⟩ := T.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hT)
    have hGT : ∀ z, G (T z) = z := fun z => by simpa using LinearMap.congr_fun hG z
    have hGc : Continuous G := LinearMap.continuous_of_finiteDimensional G
    have hmem : ∀ x : P'.range, G x ∈ P.range := by
      rintro ⟨x, hx⟩
      obtain ⟨a, rfl⟩ := AddMonoidHom.mem_range.mp hx
      exact AddMonoidHom.mem_range.mpr ⟨a, by show P a = G (P' a); rw [h, hGT]⟩
    have := hd
    refine DiscreteTopology.of_continuous_injective
      (f := fun x : P'.range => (⟨G x, hmem x⟩ : P.range)) ((hGc.comp continuous_subtype_val).subtype_mk _) ?_
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    obtain ⟨a, rfl⟩ := AddMonoidHom.mem_range.mp hx
    obtain ⟨c, rfl⟩ := AddMonoidHom.mem_range.mp hy
    have e1 := congrArg Subtype.val hxy
    simp only [h, hGT] at e1
    apply Subtype.ext
    simp only [h, e1]
  · have hr : Set.range P' = T '' Set.range P := by
      rw [hP', Set.range_comp]
    rw [hr, Submodule.span_image, hs, Submodule.map_top, LinearMap.range_eq_top.mpr hTs]
end GlobalTheory.PeriodChart
