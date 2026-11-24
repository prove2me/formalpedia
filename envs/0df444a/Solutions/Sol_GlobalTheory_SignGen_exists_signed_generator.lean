-- Prove2me | solution 1 for GlobalTheory.SignGen.exists_signed_generator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:16:03.373203+00:00
-- url     : https://prove2.me/submissions/f11bf2d7-6f76-43cc-902e-0fae609cc8f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_PolarisationModuleIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsImaginaryGeneratorCmType
import Theorems.Thm_GlobalTheory_SignGen_gen_mod
import Theorems.Thm_GlobalTheory_SignGen_nakayama_int
import Theorems.Thm_GlobalTheory_SignGen_signs
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.SignGen
namespace GlobalTheory.SignGen
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (M : Submodule (OF E) E), IsUnit M →
    (∀ ξ ∈ M, IsCMField.complexConj E ξ = -ξ) → ∀ (I : Type) (φ : I → E →+* ℂ), IsCMType φ → ∀ (e₀ : ℤˣ) (l : ℕ), l.Prime →
    ∃ ξ ∈ M, (∀ i, 0 < ((e₀ : ℤ) : ℝ) * (φ i ξ).im) ∧
      ∀ η ∈ M, ∃ n : ℕ, n.Coprime l ∧ ∃ a : OF E, (n : E) * η = algebraMap (OF E) E a * ξ := by
  intro E _ _ _ M hM hconj I φ hφ e₀ l hl
  have hinj : Function.Injective (algebraMap (OF E) E) := by
    intro x y hxy
    have h1 : ((x : maximalRealSubfield E) : E) = ((y : maximalRealSubfield E) : E) := hxy
    exact RingOfIntegers.ext (Subtype.ext h1)
  have hl0 : (l : OF E) ≠ 0 := by exact_mod_cast hl.ne_zero
  obtain ⟨ξ₀, hξ₀M, hgen₀⟩ := gen_mod (OF E) E hinj M hM (l : OF E) hl0
  have hfg : M.FG := Submodule.fg_of_isUnit hM
  have hM0 : M ≠ ⊥ := by
    intro h0
    obtain ⟨N, hN⟩ := hM.exists_right_inv
    rw [h0, Submodule.bot_mul] at hN
    have h1 : (1 : E) ∈ (1 : Submodule (OF E) E) := Submodule.one_le.1 le_rfl
    rw [← hN, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  have hξ₀ : ξ₀ ≠ 0 := by
    intro h0
    apply hM0
    rw [eq_bot_iff]
    intro η hη
    obtain ⟨n, hn, a, ha⟩ := nakayama_int (OF E) E M hfg l ξ₀ hgen₀ η hη
    rw [h0, mul_zero] at ha
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hl.one_lt.ne' (by simpa using hn)
    rw [Submodule.mem_bot]
    exact (mul_eq_zero.1 ha).resolve_left (by exact_mod_cast hn0)
  have him : ∀ i, (φ i ξ₀).im ≠ 0 := by
    intro i h
    have h1 := IsCMField.complexEmbedding_complexConj (K := E) (φ i) ξ₀
    rw [hconj ξ₀ hξ₀M, map_neg] at h1
    have h2 : conj (φ i ξ₀) = φ i ξ₀ := Complex.conj_eq_iff_im.2 h
    rw [h2] at h1
    have h3 : φ i ξ₀ = 0 := by
      have : (2 : ℂ) * φ i ξ₀ = 0 := by linear_combination -h1
      simpa using this
    exact hξ₀ ((map_eq_zero _).1 h3)
  obtain ⟨a, ha⟩ := signs E I φ hφ (fun i => ((e₀ : ℤ) : ℝ) * (φ i ξ₀).im)
  have hreal : ∀ i, (φ i (algebraMap (OF E) E a)).im = 0 := by
    intro i
    have h1 := IsCMField.complexEmbedding_complexConj (K := E) (φ i) (algebraMap (OF E) E a)
    have h2 : IsCMField.complexConj E (algebraMap (OF E) E a) = algebraMap (OF E) E a :=
      IsCMField.complexConj_apply_eq_self (K := E) (a : maximalRealSubfield E)
    rw [h2] at h1
    exact Complex.conj_eq_iff_im.1 h1.symm
  set ξ := algebraMap (OF E) E (1 + (l : OF E) * a) * ξ₀ with hξdef
  have hξM : ξ ∈ M := by
    rw [hξdef, ← Algebra.smul_def]; exact M.smul_mem _ hξ₀M
  refine ⟨ξ, hξM, ?_, ?_⟩
  · intro i
    have he : ((e₀ : ℤ) : ℝ) = 1 ∨ ((e₀ : ℤ) : ℝ) = -1 := by
      rcases Int.units_eq_one_or e₀ with h | h <;> simp [h]
    have hc := ha i
    have hx := hreal i
    have hφξ : φ i ξ = (1 + (l : ℂ) * φ i (algebraMap (OF E) E a)) * φ i ξ₀ := by
      rw [hξdef]; simp [map_mul, map_add, map_one, map_natCast]
    rw [hφξ, Complex.mul_im]
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      Complex.add_im, Complex.one_im, Complex.mul_im, hx, mul_zero, sub_zero, zero_mul, add_zero, zero_add]
    have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
    have hc0 : 0 < |((e₀ : ℤ) : ℝ) * (φ i ξ₀).im| := by
      rcases he with h | h <;> rw [h] <;> simpa using him i
    set x := (φ i (algebraMap (OF E) E a)).re
    set c := ((e₀ : ℤ) : ℝ) * (φ i ξ₀).im
    have hc' : c * (1 + l * x) = c + l * (c * x) := by ring
    have key : 0 < c * (1 + l * x) := by
      rw [hc']
      have : -|c| ≤ c := neg_abs_le c
      nlinarith
    have : ((e₀ : ℤ) : ℝ) * ((1 + l * x) * (φ i ξ₀).im) = c * (1 + l * x) := by ring
    linarith
  · apply nakayama_int (OF E) E M hfg l ξ
    have hsub : Submodule.span (OF E) {ξ₀} ≤ Submodule.span (OF E) {ξ} ⊔ Ideal.span {(l : OF E)} • M := by
      rw [Submodule.span_le, Set.singleton_subset_iff]
      have hm : (l : OF E) • (a • ξ₀) ∈ Ideal.span {(l : OF E)} • M :=
        Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (M.smul_mem a hξ₀M)
      have heq : ξ₀ = ξ + -((l : OF E) • (a • ξ₀)) := by
        rw [hξdef, Algebra.smul_def, Algebra.smul_def]; simp [map_add, map_mul]; ring
      rw [heq]
      exact Submodule.add_mem_sup (Submodule.mem_span_singleton_self ξ) (Submodule.neg_mem _ hm)
    exact hgen₀.trans (sup_le hsub le_sup_right)
end GlobalTheory.SignGen
