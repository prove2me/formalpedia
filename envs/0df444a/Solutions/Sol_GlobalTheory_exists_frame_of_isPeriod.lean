-- Prove2me | solution 1 for GlobalTheory.exists_frame_of_isPeriod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:39:30.4798+00:00
-- url     : https://prove2.me/submissions/55b5b271-5e9e-4f16-8dbc-93b48bd41ab2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqIffConjNe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsFrameOfIsPeriod
import Theorems.Thm_GlobalTheory_PeriodOnto_lminor_sign
import Theorems.Thm_GlobalTheory_PeriodOnto_kap_apply
import Theorems.Thm_GlobalTheory_PeriodOnto_blockOf_apply
import Theorems.Thm_GlobalTheory_PeriodOnto_exists_frames
import Theorems.Thm_GlobalTheory_PeriodOnto_exists_row
import Theorems.Thm_GlobalTheory_PeriodOnto_trace_eq_sum_re
import Theorems.Thm_GlobalTheory_PeriodOnto_cmType_host
import Theorems.Thm_GlobalTheory_PeriodOnto_hermC_eq
import Theorems.Thm_P2M_GlobalTheory_PeriodOnto_gram_eq__a7a60263ce08
import Theorems.Thm_GlobalTheory_PeriodOnto_hermC_col

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexOrder ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
open PeriodOnto
namespace GlobalTheory
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (_hΨ : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) (g : ℕ) (idx : Fin g ≃ Ψ × Fin r) (ty : Fin g → (E →+* ℂ)) (_hty : ∀ k, ty k = if ((idx k).2 : ℕ) < D.q then ComplexEmbedding.conjugate (idx k).1.1 else (idx k).1.1), FD.cc ξ = -ξ → (∀ τ ∈ Ψ, 0 < (τ ξ).im) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y))) → r = D.p + D.q → ∀ P : D.La →+ (Fin g → ℂ), IsPeriod D ty P → ∃ x ∈ FD.GG Ψ Gm D.q, (∀ v k, P v k = if ((idx k).2 : ℕ) < D.q then FD.hermC (idx k).1.1 Gm (FD.col (FD.mat x (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 (φ v)) else ((FD.mat x (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 (φ v)) (idx k).2) := by
  intro E _ _ _ H D r ξ Gm φ Ψ hΨ g idx ty hty hξ hξpos ⟨hinj, hsp, hG, _, hEF⟩ _ P
    ⟨hlin, _, _, hspan, Hm, _, hpos, hIm⟩
  have hcc : ∀ (τ : E →+* ℂ) (z : E), τ (FD.cc z) = conj (τ z) := fun τ z =>
    IsCMField.complexEmbedding_complexConj E τ z
  have hex : ∀ k, ∃ c : Fin r → ℂ, ∀ v, P v k = ∑ j, c j * ty k (φ v j) := fun k =>
    exists_row φ hinj hsp (ty k) ((Pi.evalAddMonoidHom (fun _ => ℂ) k).comp P) (fun a x => hlin a x k)
  choose C hC using hex
  have hM : ∀ v (t : Ψ), blockOf idx D.q t (P v) =
      (Matrix.of fun (a : Fin r) j => kap D.q a (C (idx.symm (t, a)) j)) *ᵥ FD.Data.emb t.1 (φ v) := by
    intro v t
    ext a
    rw [blockOf_apply, hC, hty]
    simp only [mulVec, dotProduct, of_apply, FD.Data.emb, kap_apply, Equiv.apply_symm_apply]
    split_ifs <;> simp
  have hGH : ∀ t : Ψ, (Gm.map t.1).IsHermitian := by
    intro t
    ext a b
    rw [conjTranspose_apply, map_apply, map_apply, ← hG b a, hcc]
    rfl
  have hmain : ∀ x y, (hermForm Hm (P x) (P y)).im = ∑ t : Ψ, -2 * (t.1 ξ).im *
      (FD.Data.emb t.1 (φ x) ⬝ᵥ Gm.map t.1 *ᵥ star (FD.Data.emb t.1 (φ y))).im := by
    intro x y
    have h1 : ((D.EF x y : ℤ) : ℝ) = ((Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y)) : ℚ) : ℝ) := by
      rw [← hEF]; simp
    rw [hIm, h1, trace_eq_sum_re Ψ (cmType_host H Ψ hΨ)]
    refine Finset.sum_congr rfl fun t _ => ?_
    have h2 : t.1 (FD.herm Gm (φ x) (φ y)) =
        FD.hermC t.1 Gm (FD.Data.emb t.1 (φ x)) (FD.Data.emb t.1 (φ y)) := by
      simp [FD.hermC, FD.herm, FD.Data.emb, hcc]
    have h3 : (t.1 ξ).re = 0 := by
      have := congrArg (fun z => (t.1 z).re) hξ
      simp only [hcc, map_neg, Complex.conj_re, Complex.neg_re] at this
      linarith
    rw [map_mul, h2, hermC_eq, Complex.mul_re, h3]
    ring
  have hfr := exists_frames idx D.q P hspan (fun t v => FD.Data.emb t.1 (φ v)) _ hM
    (fun t => Gm.map t.1) hGH (fun t => (t.1 ξ).im) (fun t => hξpos t.1 t.2) Hm hpos hmain
  choose x hx0 hx1 hx2 using hfr
  refine ⟨fun t => x t, fun t => ⟨hx0 t, fun i => ?_⟩, fun v k => ?_⟩
  · apply lminor_sign
    rw [gram_eq']
    exact hx1 t
  · obtain ⟨⟨t, a⟩, rfl⟩ := idx.symm.surjective k
    rw [hx2, hermC_col _ _ hG, Equiv.apply_symm_apply]
    rfl
end GlobalTheory
