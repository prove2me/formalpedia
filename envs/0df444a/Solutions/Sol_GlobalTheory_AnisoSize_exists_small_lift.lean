-- Prove2me | solution 1 for GlobalTheory.AnisoSize.exists_small_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:14:32.629433+00:00
-- url     : https://prove2.me/submissions/225f9bf3-0644-437e-b793-1ab53bac80e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsIntMulIsIntegralOfTrace_d66162b46f1d0309
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroMemFractionalIdealNormSqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_AnisotropicFiniteLengthsOfShortLatticeVector
import Theorems.Thm_GlobalTheory_AnisoSize_mul_le_pow
import Theorems.Thm_GlobalTheory_AnisoSize_add_le_pow
import Theorems.Thm_GlobalTheory_AnisoSize_size_sub_le
import Theorems.Thm_GlobalTheory_AnisoSize_size_sum_le
import Theorems.Thm_GlobalTheory_AnisoSize_size_smul_le
import Theorems.Thm_GlobalTheory_AnisoSize_house_form_le
import Theorems.Thm_GlobalTheory_AnisoSize_house_mul_le_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix Module Submodule
open scoped ContDiff Topology nonZeroDivisors
open GlobalTheory GlobalTheory.AnisoSize
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {V : Type} [AddCommGroup V] [Module E V]
  {h : V →ₗ[E] V →ₗ⋆[E] E} {Λ : Submodule ℤ V} {N : ℤ} {ν : V → ℝ} {B : ℝ}
namespace GlobalTheory.AnisoSize
theorem _root_.solution [FiniteDimensional E V] (H : Sized h Λ N ν B) {C U : ℝ}
    (hC : ∀ c : E, ∃ t : E, IsIntegral ℤ t ∧ house (c - t) ≤ C) (hU : 2 ≤ U) (hB : B ≤ U ^ 1)
    (hn : (finrank E V : ℝ) ≤ U ^ 1) (hCU : C ≤ U ^ 1) {v x₀ w : V} (hv : v ∈ Λ) (hx₀ : x₀ ∈ Λ)
    (hw : w ∈ Λ) (hvU : ν v ≤ U ^ 1) (hx₀U : ν x₀ ≤ U ^ 1) (ha : h x₀ v ≠ 0)
    (haU : house (h x₀ v)⁻¹ ≤ U ^ 1) (hwU : house (h w v) ≤ U ^ 1) :
    ∃ w' ∈ Λ, h w' v = h w v ∧ ν w' ≤ U ^ 7 := by
  obtain ⟨x, hx, hsp, -⟩ := Submodule.exists_fun_fin_finrank_span_eq E {x | x ∈ Λ ∧ ν x ≤ B}
  have hn' : (Fintype.card (Fin (finrank E (span E {x | x ∈ Λ ∧ ν x ≤ B}))) : ℝ) ≤ U ^ 1 := by
    rw [Fintype.card_fin, H.span, finrank_top]; exact hn
  replace hsp := hsp.trans H.span
  set a := h x₀ v with had
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 (show w ∈ span E (Set.range x) from hsp.ge mem_top)
  let p := fun i => a • x i - h (x i) v • x₀
  have hpΛ : ∀ i, p i ∈ Λ := fun i =>
    sub_mem (H.stable _ (H.int _ hx₀ _ hv) _ (hx i).1) (H.stable _ (H.int _ (hx i).1 _ hv) _ hx₀)
  have hpv : ∀ i, h (p i) v = 0 := fun i => by simp [p, ← had, mul_comm]
  have hpU : ∀ i, ν (p i) ≤ U ^ 4 := fun i =>
    (size_sub_le H _ _).trans (add_le_pow hU
      (size_smul_le H hU (house_form_le H hU hx₀U hvU) ((hx i).2.trans hB))
      (size_smul_le H hU (house_form_le H hU ((hx i).2.trans hB) hvU) hx₀U))
  have hsum : w = (h w v * a⁻¹) • x₀ + ∑ i, (c i * a⁻¹) • p i := by
    have h1 : h w v = ∑ i, c i * h (x i) v := by rw [← hc]; simp
    have h2 : ∀ i, (c i * a⁻¹) • p i = c i • x i - (c i * h (x i) v * a⁻¹) • x₀ := fun i => by
      simp only [p, smul_sub, smul_smul]
      rw [mul_assoc, inv_mul_cancel₀ ha, mul_one, mul_right_comm]
    simp only [h2, Finset.sum_sub_distrib, hc, ← Finset.sum_smul, ← Finset.sum_mul, ← h1]
    abel
  choose t ht htC using fun i => hC (c i * a⁻¹)
  refine ⟨w - ∑ i, t i • p i, sub_mem hw (sum_mem fun i _ => H.stable _ (ht i) _ (hpΛ i)),
    by simp [hpv], ?_⟩
  have h3 : w - ∑ i, t i • p i = (h w v * a⁻¹) • x₀ + ∑ i, (c i * a⁻¹ - t i) • p i := by
    simp only [sub_smul, Finset.sum_sub_distrib, ← add_sub_assoc, ← hsum]
  rw [h3]
  have h4 : ν (∑ i, (c i * a⁻¹ - t i) • p i) ≤ U ^ 6 := by
    refine (size_sum_le H _ _).trans ((Finset.sum_le_sum fun i _ =>
      size_smul_le H hU ((htC i).trans hCU) (hpU i)).trans ?_)
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    exact mul_le_pow hU hn' le_rfl (by positivity)
  exact (H.add_le _ _).trans
    (add_le_pow hU (size_smul_le H hU (house_mul_le_pow hU hwU haU) hx₀U) h4)
end GlobalTheory.AnisoSize
