-- Prove2me | solution 1 for GlobalTheory.UnitFrame.im_hermForm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:23:17.568081+00:00
-- url     : https://prove2.me/submissions/eda47685-1fc4-4bc3-92a8-4de1a109dc78

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MemIffConjugateNotMem
import Theorems.Thm_GlobalTheory_UnitFrame_trace_eq_sum_re
import Theorems.Thm_GlobalTheory_UnitFrame_im_sum_periods
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.UnitFrame
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField Matrix in
open scoped nonZeroDivisors ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma mem_iff_conjugate_not_mem (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) (τ : E →+* ℂ) :
    τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hrt : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (fun y : 𝓞 E => (y : E)) H.rt_sq
    simpa using this
  have hw : (τ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
    rw [← map_pow, hrt]; simp
  have h0 := H.sqrt_neg_disc_sq
  rw [hΨ, hΨ, ComplexEmbedding.conjugate_coe_eq]
  set w := τ (H.rt : E)
  set m := H.rt0
  have reZero : ∀ z : ℂ, z ^ 2 = -(H.d : ℂ) → z.re = 0 ∧ z.im ^ 2 = H.d := by
    intro z hz
    have e1 := congrArg Complex.re hz
    have e2 := congrArg Complex.im hz
    simp [sq, Complex.mul_re, Complex.mul_im] at e1 e2
    have hre : z.re = 0 := by
      rcases mul_eq_zero.1 (show z.re * z.im = 0 by linarith) with h | h
      · exact h
      · exfalso; rw [h] at e1; nlinarith [sq_nonneg z.re]
    refine ⟨hre, ?_⟩
    rw [hre] at e1; nlinarith
  obtain ⟨hwr, hwi⟩ := reZero w hw
  obtain ⟨hmr, hmi⟩ := reZero m h0
  have hm0 : m.im ≠ 0 := by
    intro h; rw [h] at hmi; linarith
  constructor
  · intro h hc
    rw [h] at hc
    have := congrArg Complex.im hc
    simp at this
    exact hm0 (by linarith)
  · intro hn
    apply Complex.ext
    · rw [hwr, hmr]
    · have : (w.im - m.im) * (w.im + m.im) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · exfalso; apply hn
        apply Complex.ext
        · simp [hwr, hmr]
        · simp; linarith
end GlobalTheory.UnitFrame
end

set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.UnitFrame
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.UnitFrame
namespace _root_.GlobalTheory.UnitFrame
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (hΨ : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) (g : ℕ) (idx : Fin g ≃ Ψ × Fin r) (ty : Fin g → (E →+* ℂ)) (hty : ∀ k, ty k = if ((idx k).2 : ℕ) < D.q then ComplexEmbedding.conjugate (idx k).1.1 else (idx k).1.1), _root_.ReciprocityTheory.ChartRestriction.G.FD.cc ξ = -ξ → (∀ τ ∈ Ψ, 0 < (τ ξ).im) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (φ x) (φ y))) → ∀ (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) (P : D.La →+ (Fin g → ℂ)), (∀ v k, P v k = if ((idx k).2 : ℕ) < D.q then _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (idx k).1.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (idx k).1) (idx k).2) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ v)) else ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (idx k).1)⁻¹ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ v)) (idx k).2) → (∀ τ : Ψ, _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) = Matrix.diagonal fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn D.q (a : ℕ) : ℝ) : ℂ)) → ∀ v w, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Matrix.diagonal fun k => ((2 * ‖(idx k).1.1 ξ‖ : ℝ) : ℂ)) (P v) (P w)).im = D.EF v w := by
  intro E _ _ _ H D r ξ Gm φ Ψ hΨ g idx ty hty hξ hpos hdata x P hP hgram v w
  have hEF := hdata.2.2.2.2
  have hcm := mem_iff_conjugate_not_mem H Ψ hΨ
  have hherm : ∀ (τ : E →+* ℂ) (a b : Fin r → E),
      τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm a b) = _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ a) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ b) := by
    intro τ a b
    simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.herm, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC, _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc, map_sum, map_mul,
      IsCMField.complexEmbedding_complexConj]
  have hre : ∀ τ : Ψ, (τ.1 (ξ * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (φ v) (φ w))).re
      = -‖τ.1 ξ‖ * (_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (φ v)) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (φ w))).im := by
    intro τ
    have hc : conj (τ.1 ξ) = -τ.1 ξ := by
      rw [← IsCMField.complexEmbedding_complexConj, ← map_neg]
      congr 1
    have hr : (τ.1 ξ).re = 0 := by
      have := congrArg Complex.re hc
      simp at this; linarith
    have hn : ‖τ.1 ξ‖ = (τ.1 ξ).im := by
      have hz : τ.1 ξ = ((τ.1 ξ).im : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [hr]
      rw [hz, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos]
      · simp
      · simpa using hpos τ.1 τ.2
    rw [map_mul, hherm, Complex.mul_re, hr, hn]
    ring
  have hL : (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Matrix.diagonal fun k => ((2 * ‖(idx k).1.1 ξ‖ : ℝ) : ℂ)) (P v) (P w)).im
      = ∑ k, 2 * ‖(idx k).1.1 ξ‖ * (P v k * conj (P w k)).im := by
    simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, dotProduct, mulVec_diagonal, Complex.im_sum, Pi.star_apply,
      Complex.star_def]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_left_comm, Complex.im_ofReal_mul]
  rw [hL, ← Rat.cast_intCast, hEF, _root_.GlobalTheory.UnitFrame.trace_eq_sum_re Ψ hcm, ← idx.symm.sum_comp,
    Fintype.sum_prod_type]
  refine Fintype.sum_congr _ _ fun τ => ?_
  simp only [Equiv.apply_symm_apply]
  rw [← Finset.mul_sum, ← Complex.im_sum]
  have hPv : ∀ u, ∀ a : Fin r, P u (idx.symm (τ, a)) = if (a : ℕ) < D.q then
      _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) a) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (φ u))
      else ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (φ u)) a := by
    intro u a; rw [hP]; simp
  simp only [hPv]
  rw [_root_.GlobalTheory.UnitFrame.im_sum_periods D.q τ.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (hgram τ), hre]
  ring
end _root_.GlobalTheory.UnitFrame
end GlobalTheory.UnitFrame
