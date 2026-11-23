-- Prove2me | solution 1 for GlobalTheory.PeriodNonempty.sum_type
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:20:54.085413+00:00
-- url     : https://prove2.me/submissions/3d804955-4cef-4e93-ba3a-a3ba9a94978c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul



set_option autoImplicit false
open NumberField Matrix
open scoped TensorProduct ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodNonempty
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.PeriodNonempty
theorem _root_.solution (H : Host E) {p q g : ℕ} {ty : Fin g → (E →+* ℂ)} (hty : IsTypeFn H p q ty) (a : E) :
    ∑ i, ty i a = ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0),
      ((p : ℂ) * τ a + (q : ℂ) * starRingEnd ℂ (τ a)) := by
  classical
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hre : H.rt0.re = 0 := by
    have h1 := congrArg Complex.re H.sqrt_neg_disc_sq
    have h2 := congrArg Complex.im H.sqrt_neg_disc_sq
    simp [sq] at h1 h2
    by_contra h0
    have : H.rt0.im = 0 := by
      have : H.rt0.re * H.rt0.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left h0
    rw [this] at h1
    nlinarith [mul_self_nonneg H.rt0.re]
  have hc : conj H.rt0 = -H.rt0 := by apply Complex.ext <;> simp [hre]
  have h0 : H.rt0 ≠ -H.rt0 := fun h => by
    have h1 : H.rt0 = 0 := by linear_combination h / 2
    have := H.sqrt_neg_disc_sq
    rw [h1] at this
    simp at this
    simp [this] at hd
  have hsq : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := fun τ => by
    apply sq_eq_sq_iff_eq_or_eq_neg.1
    have := congrArg (fun x : 𝓞 E => τ (x : E)) H.rt_sq
    simp at this
    rw [H.sqrt_neg_disc_sq, ← this]
  rw [← Finset.sum_fiberwise Finset.univ ty, Finset.sum_add_distrib,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)]
  have hf : ∀ φ : E →+* ℂ, ∑ i ∈ Finset.univ.filter (fun i => ty i = φ), ty i a =
      (Nat.card {i // ty i = φ} : ℂ) * φ a := fun φ => by
    rw [Finset.sum_congr rfl (g := fun _ => φ a) (fun i hi => by rw [(Finset.mem_filter.1 hi).2]),
      Finset.sum_const, nsmul_eq_mul, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  · refine Finset.sum_congr rfl fun τ hτ => ?_
    rw [hf, (hty τ).1 (Finset.mem_filter.1 hτ).2]
  · refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
    · intro τ hτ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      rw [ComplexEmbedding.conjugate_coe_eq, (hsq τ).resolve_left hτ, map_neg, hc, neg_neg]
    · intro τ hτ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      rw [ComplexEmbedding.conjugate_coe_eq, hτ, hc]
      exact h0.symm
    · intro τ _; ext x; simp
    · intro τ _; ext x; simp
    · intro τ hτ
      rw [hf, (hty τ).2 (Finset.mem_filter.1 hτ).2]
      simp
end GlobalTheory.PeriodNonempty
