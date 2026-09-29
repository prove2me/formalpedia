-- Prove2me | solution 1 for LanglandsTunnell.Converse.prod_map_GammaR_twistedGammaR_archOfParamR_principal_three_real
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/83505c85-2af4-5f8f-8b01-e3b7e69e7e87

import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_prod_map_GammaR_twistedGammaR_archOfParamR_principal_three_real

set_option autoImplicit false

open NumberField LanglandsTunnell LanglandsTunnell.Converse

namespace Ws14RA9

open Classical

theorem univ_real_eq {K : Type} [Field K] [NumberField K]
    (w₀ w₁ w₂ : NumberField.InfinitePlace K) (h₀ : w₀.IsReal) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal)
    (hall : ∀ w : NumberField.InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂) :
    (Finset.univ : Finset {w : NumberField.InfinitePlace K // w.IsReal}) =
      {⟨w₀, h₀⟩, ⟨w₁, h₁⟩, ⟨w₂, h₂⟩} := by
  ext w
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  rcases hall w.1 with h | h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr (Subtype.ext h))

theorem univ_complex_eq_empty {K : Type} [Field K] [NumberField K]
    (w₀ w₁ w₂ : NumberField.InfinitePlace K) (h₀ : w₀.IsReal) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal)
    (hall : ∀ w : NumberField.InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂) :
    (Finset.univ : Finset {w : NumberField.InfinitePlace K // w.IsComplex}) = ∅ := by
  rw [Finset.univ_eq_empty_iff]
  refine ⟨fun w => ?_⟩
  have hw : w.1.IsReal := by
    rcases hall w.1 with h | h | h
    · rw [h]; exact h₀
    · rw [h]; exact h₁
    · rw [h]; exact h₂
  exact (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr w.2) hw

end Ws14RA9

open Ws14RA9 Classical in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (w₀ w₁ w₂ : NumberField.InfinitePlace K) (h₀ : w₀.IsReal) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal)
    (h01 : w₀ ≠ w₁) (h02 : w₀ ≠ w₂) (h12 : w₁ ≠ w₂)
    (hall : ∀ w : NumberField.InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂)
    (uR : ∀ w : NumberField.InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : NumberField.InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : NumberField.InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : NumberField.InfinitePlace K, w.IsComplex → ℤ)
    (P : RealArchParam) (ν₁ ν₂ : ℂ) (a₁ a₂ : ZMod 2) (hP : P = RealArchParam.principal ν₁ a₁ ν₂ a₂)
    (s : ℂ) :
    (((twistedGammaR K (archOfParamR K P) uR aR).map fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod =
        (Complex.Gammaℝ (s + 1 / 2 + ((ν₁ + uR w₀ h₀) + signShift (a₁ + aR w₀ h₀))) *
        Complex.Gammaℝ (s + 1 / 2 + ((ν₂ + uR w₀ h₀) + signShift (a₂ + aR w₀ h₀)))) *
        ((Complex.Gammaℝ (s + 1 / 2 + ((ν₁ + uR w₁ h₁) + signShift (a₁ + aR w₁ h₁))) *
        Complex.Gammaℝ (s + 1 / 2 + ((ν₂ + uR w₁ h₁) + signShift (a₂ + aR w₁ h₁)))) *
        (Complex.Gammaℝ (s + 1 / 2 + ((ν₁ + uR w₂ h₂) + signShift (a₁ + aR w₂ h₂))) *
        Complex.Gammaℝ (s + 1 / 2 + ((ν₂ + uR w₂ h₂) + signShift (a₂ + aR w₂ h₂)))))) ∧
    (((twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC).map fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod = 1) := by
  subst hP
  have hU := univ_real_eq w₀ w₁ w₂ h₀ h₁ h₂ hall
  have hE := univ_complex_eq_empty w₀ w₁ w₂ h₀ h₁ h₂ hall
  have hn0 : (⟨w₀, h₀⟩ : {w : NumberField.InfinitePlace K // w.IsReal}) ∉ ({⟨w₁, h₁⟩, ⟨w₂, h₂⟩} : Finset _) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, not_or]
    exact ⟨h01, h02⟩
  have hn1 : (⟨w₁, h₁⟩ : {w : NumberField.InfinitePlace K // w.IsReal}) ∉ ({⟨w₂, h₂⟩} : Finset _) := by
    simp only [Finset.mem_singleton, Subtype.mk.injEq]
    exact h12
  constructor
  · rw [twistedGammaR, hU, Finset.sum_insert hn0, Finset.sum_insert hn1, Finset.sum_singleton]
    simp only [archOfParamR, RealArchParam.twist, RealArchParam.gammaR, Multiset.map_add, Multiset.prod_add,
      Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton]
  · rw [twistedGammaC, hU, hE, Finset.sum_insert hn0, Finset.sum_insert hn1, Finset.sum_singleton, Finset.sum_empty]
    simp only [archOfParamR, RealArchParam.twist, RealArchParam.gammaC, add_zero, Multiset.map_zero, Multiset.prod_zero]

#print axioms solution

end S_LanglandsTunnell_Converse_prod_map_GammaR_twistedGammaR_archOfParamR_principal_three_real
end P2MW
export P2MW.S_LanglandsTunnell_Converse_prod_map_GammaR_twistedGammaR_archOfParamR_principal_three_real (solution)
