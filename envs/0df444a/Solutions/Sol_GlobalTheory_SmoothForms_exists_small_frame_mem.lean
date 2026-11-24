-- Prove2me | solution 1 for GlobalTheory.SmoothForms.exists_small_frame_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:05:34.869803+00:00
-- url     : https://prove2.me/submissions/ceff7652-a320-4205-8e1a-801852b02fa8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_OrthogonalAnisotropicFrameBoundedCM
import Theorems.Thm_GlobalTheory_SmoothForms_exists_small_anisotropic_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
open GlobalTheory GlobalTheory.SmoothForms
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.SmoothForms
theorem _root_.solution (n : ℕ) : ∃ k : ℕ, ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (Λ : Submodule ℤ V) (N : ℤ) (ν : V → ℝ) (B₀ : ℝ), Sized h Λ N ν B₀ →
    ∀ B : ℝ, 2 ≤ B → ∀ W : Submodule E V, Module.finrank E W = n → (∀ y ∈ W, (∀ x ∈ W, h y x = 0) → y = 0) →
    W ≤ Submodule.span E {x | x ∈ Λ ∧ x ∈ W ∧ ν x ≤ B} →
    ∃ v : Fin n → V, (∀ i, v i ∈ Λ ∧ v i ∈ W) ∧ (∀ i j, i ≠ j → h (v i) (v j) = 0) ∧
      ∀ i, h (v i) (v i) ≠ 0 ∧ ν (v i) ≤ B ^ k := by
  induction n with
  | zero => exact ⟨0, fun V _ _ _ h Λ N ν B₀ H B hB W hn hnd hsp =>
      ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩⟩
  | succ n ih =>
    obtain ⟨k, ih⟩ := ih
    refine ⟨10 * k + 4, fun V _ _ _ h Λ N ν B₀ H B hB W hn hnd hsp => ?_⟩
    have hW : W ≠ ⊥ := by
      rintro rfl
      simp at hn
    have h0 : (0 : ℝ) ≤ B := by linarith
    have hB1 : (1 : ℝ) ≤ B := by linarith
    obtain ⟨v, hv1, hv2, hv3, hv4⟩ := exists_small_anisotropic_mem H hB hW hnd hsp
    let g : W →ₗ[E] E := (h.flip v).domRestrict W
    let W' : Submodule E V := (LinearMap.ker g).map W.subtype
    have hmem : ∀ x, x ∈ W' ↔ x ∈ W ∧ h x v = 0 := fun x => by
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, hy⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨x, h1⟩, h2, rfl⟩
    have hrank : Module.finrank E W' = n := by
      have h1 := g.finrank_range_add_finrank_ker
      have h2 : LinearMap.range g = ⊤ := by
        rw [eq_top_iff]
        intro c _
        refine ⟨(c / h v v) • ⟨v, hv2⟩, ?_⟩
        rw [map_smul]
        change (c / h v v) * h v v = c
        field_simp
      rw [h2, hn, finrank_top, Module.finrank_self] at h1
      rw [Submodule.finrank_map_subtype_eq]
      omega
    let P : V →ₗ[E] V := h v v • LinearMap.id - (h.flip v).smulRight v
    have hP : ∀ x, P x = h v v • x + (-h x v) • v := fun x => by
      simp [P, sub_eq_add_neg]
    have hPW : ∀ x ∈ W, P x ∈ W' := fun x hx => by
      rw [hmem, hP]
      refine ⟨W.add_mem (W.smul_mem _ hx) (W.smul_mem _ hv2), ?_⟩
      simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    have hnd' : ∀ y ∈ W', (∀ x ∈ W', h y x = 0) → y = 0 := fun y hy hy0 => by
      obtain ⟨hy1, hy2⟩ := (hmem y).1 hy
      refine hnd y hy1 fun x hx => ?_
      have h1 := hy0 _ (hPW x hx)
      rw [hP] at h1
      simp only [map_add, map_smulₛₗ, hy2, smul_eq_mul, mul_zero, add_zero, starRingEnd_apply] at h1
      exact (mul_eq_zero.1 h1).resolve_left (star_ne_zero.2 hv3)
    have hsp' : W' ≤ Submodule.span E {x | x ∈ Λ ∧ x ∈ W' ∧ ν x ≤ B ^ 10} := by
      have h1 : Submodule.span E {x | x ∈ Λ ∧ x ∈ W ∧ ν x ≤ B} ≤
          (Submodule.span E {x | x ∈ Λ ∧ x ∈ W' ∧ ν x ≤ B ^ 10}).comap P := by
        refine Submodule.span_le.2 ?_
        rintro x ⟨hx1, hx2, hx3⟩
        refine Submodule.subset_span ⟨?_, hPW x hx2, ?_⟩
        · rw [hP]
          exact Λ.add_mem (H.stable _ (H.int v hv1 v hv1) x hx1) (H.stable _ (H.int x hx1 v hv1).neg v hv1)
        · rw [hP]
          have a1 : house (h v v) ≤ B ^ 4 * B ^ 4 :=
            (H.form_le v v).trans (mul_le_mul hv4 hv4 (H.nonneg _) (by positivity))
          have a2 : house (-h x v) ≤ B * B ^ 4 := by
            have : house (-h x v) = house (h x v) := by simp [house]
            rw [this]
            exact (H.form_le x v).trans (mul_le_mul hx3 hv4 (H.nonneg _) h0)
          have a3 : ν (h v v • x) ≤ B ^ 4 * B ^ 4 * B :=
            (H.smul_le _ _).trans (mul_le_mul a1 hx3 (H.nonneg _) (by positivity))
          have a4 : ν ((-h x v) • v) ≤ B * B ^ 4 * B ^ 4 :=
            (H.smul_le _ _).trans (mul_le_mul a2 hv4 (H.nonneg _) (by positivity))
          have a5 : 2 * B ^ 9 ≤ B * B ^ 9 := mul_le_mul_of_nonneg_right hB (by positivity)
          calc _ ≤ _ := H.add_le _ _
            _ ≤ _ := add_le_add a3 a4
            _ = 2 * B ^ 9 := by ring
            _ ≤ B * B ^ 9 := a5
            _ = B ^ 10 := by ring
      intro x hx
      obtain ⟨hx1, hx2⟩ := (hmem x).1 hx
      have h2 : P x ∈ Submodule.span E {x | x ∈ Λ ∧ x ∈ W' ∧ ν x ≤ B ^ 10} := h1 (hsp hx1)
      rw [hP, hx2, neg_zero, zero_smul, add_zero] at h2
      exact (Submodule.smul_mem_iff _ hv3).1 h2
    obtain ⟨w, hw1, hw2, hw3⟩ := ih V h Λ N ν B₀ H (B ^ 10)
      (hB.trans (le_self_pow₀ hB1 (by norm_num))) W' hrank hnd' hsp'
    have hwv : ∀ i, h (w i) v = 0 := fun i => ((hmem _).1 (hw1 i).2).2
    refine ⟨Fin.cons v w, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ⟨hv1, hv2⟩ (fun i => ?_) i
      exact ⟨(hw1 i).1, ((hmem _).1 (hw1 i).2).1⟩
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · intro hij; exact absurd rfl hij
      · intro _
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [H.symm, hwv, star_zero]
      · intro _
        simpa using hwv i
      · intro hij
        simpa using hw2 i j fun e => hij (by rw [e])
    · intro i
      refine Fin.cases ⟨hv3, hv4.trans (pow_le_pow_right₀ hB1 (by omega))⟩ (fun i => ?_) i
      refine ⟨(hw3 i).1, (hw3 i).2.trans ?_⟩
      rw [← pow_mul]
      exact pow_le_pow_right₀ hB1 (by omega)
end GlobalTheory.SmoothForms
