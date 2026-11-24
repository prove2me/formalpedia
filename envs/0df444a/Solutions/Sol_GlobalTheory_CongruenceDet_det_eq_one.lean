-- Prove2me | solution 1 for GlobalTheory.CongruenceDet.det_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:19:25.17481+00:00
-- url     : https://prove2.me/submissions/2bb9af40-9fcb-4a40-92d2-218166392e53

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIntegralDetSubOne
import Theorems.Thm_GlobalTheory_CongruenceDet_isIntegral_det_sub_one
import Theorems.Thm_GlobalTheory_CongruenceDet_det_mul_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CongruenceDet
open NumberField Matrix
open scoped nonZeroDivisors
namespace GlobalTheory.CongruenceDet
namespace _root_.GlobalTheory.CongruenceDet
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (Gm : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E), Gm.det ≠ 0 → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → 3 ≤ M → _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ γ → (∀ v ∈ Λ, ∃ w ∈ Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v + M • w) → (γ : Matrix (Fin r) (Fin r) E).det = 1 := by
  intro E _ _ _ r M Gm Λ γ hG hfg hspan hM hU hγ
  have hM0 : M ≠ 0 := by omega
  have hUisom : ∀ x y, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x)
      ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm x y := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab at hU
    exact hU.1
  set d := (γ : Matrix (Fin r) (Fin r) E).det with hd
  have hint : IsIntegral ℤ ((d - 1) / M) :=
    isIntegral_trans _ (_root_.GlobalTheory.CongruenceDet.isIntegral_det_sub_one hM0 Λ _ hfg hspan hγ)
  have hconj : d * IsCMField.complexConj E d = 1 :=
    _root_.GlobalTheory.CongruenceDet.det_mul_conj Gm _ hG hUisom
  have hMr : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have habs : ∀ φ : E →+* ℂ, ‖φ ((d - 1) / M)‖ ≤ 2 / 3 := by
    intro φ
    have h1 : ‖φ d‖ = 1 := by
      have := congrArg φ hconj
      rw [map_mul, IsCMField.complexEmbedding_complexConj, Complex.mul_conj, map_one] at this
      have h2 : Complex.normSq (φ d) = 1 := by exact_mod_cast this
      rw [Complex.normSq_eq_norm_sq] at h2
      nlinarith [norm_nonneg (φ d)]
    rw [map_div₀, map_sub, map_one, map_natCast, norm_div, Complex.norm_natCast]
    have h3 : ‖φ d - 1‖ ≤ 2 := (norm_sub_le _ _).trans (by rw [h1, norm_one]; norm_num)
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  by_contra hne
  have hx : (d - 1) / M ≠ 0 := by
    intro h0
    rw [div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · exact hne (sub_eq_zero.1 h0)
    · exact hM0 (by exact_mod_cast h0)
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_norm ℚ hint)
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hx
    rw [map_zero, eq_comm, Algebra.norm_eq_zero_iff] at hn
    exact hn
  have hprod := Algebra.norm_eq_prod_embeddings ℚ ℂ ((d - 1) / M)
  rw [← hn] at hprod
  have hle : ‖∏ σ : E →ₐ[ℚ] ℂ, σ ((d - 1) / M)‖ ≤ (2 / 3 : ℝ) ^ Fintype.card (E →ₐ[ℚ] ℂ) := by
    rw [norm_prod, ← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun σ _ => habs σ.toRingHom)
  have hcard : 0 < Fintype.card (E →ₐ[ℚ] ℂ) :=
    Fintype.card_pos_iff.2 ⟨(IsAlgClosed.lift : E →ₐ[ℚ] ℂ)⟩
  have hlt : (2 / 3 : ℝ) ^ Fintype.card (E →ₐ[ℚ] ℂ) < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) hcard.ne'
  rw [← hprod] at hle
  have hge : (1 : ℝ) ≤ ‖(algebraMap ℚ ℂ) ((algebraMap ℤ ℚ) n)‖ := by
    have hcast : (algebraMap ℚ ℂ) ((algebraMap ℤ ℚ) n) = (n : ℂ) := by simp
    rw [hcast, Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hn0
  linarith
end _root_.GlobalTheory.CongruenceDet
end GlobalTheory.CongruenceDet
