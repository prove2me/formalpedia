-- Prove2me | solution 1 for GlobalTheory.exists_X_pow_smul_mem_span_of_finite_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:04:20.11687+00:00
-- url     : https://prove2.me/submissions/4dfb78b7-b6d9-4f70-8314-c7e8d1d87bd7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsXPowSmulEqZeroOfEqXSubOneSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsXPowSmulMemSpanOfFiniteQuot
import Theorems.Thm_GlobalTheory_GrSum_map_of
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
import Theorems.Thm_GlobalTheory_X_smul_mem_gr
import Theorems.Thm_GlobalTheory_exists_X_pow_smul_eq_zero_of_eq_X_sub_one_smul
import Theorems.Thm_GlobalTheory_exists_homogeneous_add_X_sub_one_smul
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GrSum.map_of
attribute [local simp] GlobalTheory.Wick.dividedContraction_one
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
noncomputable section
open GlobalTheory
open GradedHilbert Pointwise
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct
open Pointwise
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι), Module.Finite (MvPolynomial ι R) (QuotSMulTop (X i - 1 : MvPolynomial ι R) M) → ∃ T : Finset M, ∀ y : M, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y ∈ Submodule.span (MvPolynomial ι R) (T : Set M) := by
  intro ι _ _ R _ M _ _ _ _ ℳ _ _ i hfin
  classical
  set I : Submodule (MvPolynomial ι R) M :=
    (X i - 1 : MvPolynomial ι R) • (⊤ : Submodule (MvPolynomial ι R) M) with hIdef
  have hI : ∀ w : M, (X i - 1 : MvPolynomial ι R) • w ∈ I := fun w =>
    Submodule.smul_mem_pointwise_smul w _ ⊤ Submodule.mem_top

  have hpow : ∀ (e : ℤ) (h : M), h ∈ ℳ e → ∀ m : ℕ,
      (X i : MvPolynomial ι R) ^ m • h ∈ ℳ (e + m) ∧ h - (X i : MvPolynomial ι R) ^ m • h ∈ I := by
    intro e h he m
    refine ⟨?_, ?_⟩
    · induction m with
      | zero => simpa using he
      | succ m ih =>
        rw [pow_succ', mul_smul, Nat.cast_succ, ← add_assoc]
        exact _root_.GlobalTheory.X_smul_mem_gr ℳ i _ _ ih
    · have h1 : (X i : MvPolynomial ι R) ^ m • h - h = (X i - 1 : MvPolynomial ι R) •
          ((∑ j ∈ Finset.range m, (X i : MvPolynomial ι R) ^ j) • h) := by
        rw [← mul_smul, mul_geom_sum, sub_smul, one_smul]
      rw [← neg_sub, h1]
      exact I.neg_mem (hI _)

  obtain ⟨G, hG⟩ := hfin.fg_top
  have hlift : ∀ q : QuotSMulTop (X i - 1 : MvPolynomial ι R) M,
      ∃ m : M, ∃ d : ℤ, m ∈ ℳ d ∧ Submodule.Quotient.mk m = q := by
    intro q
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨n₀, hn₀⟩ := _root_.GlobalTheory.exists_homogeneous_add_X_sub_one_smul ℳ i m
    obtain ⟨m', hm', w, hw⟩ := hn₀ n₀ le_rfl
    refine ⟨m', n₀, hm', ?_⟩
    rw [Submodule.Quotient.eq, hw, sub_add_cancel_left]
    exact I.neg_mem (hI w)
  choose f d hfd hfq using hlift
  set T : Finset M := G.image f with hTdef
  have hspanT : ∀ y : M, ∃ s ∈ Submodule.span (MvPolynomial ι R) (T : Set M), y - s ∈ I := by
    intro y
    have hsub : (G : Set (QuotSMulTop (X i - 1 : MvPolynomial ι R) M)) ⊆ I.mkQ '' (T : Set M) := by
      intro q hq
      exact ⟨f q, Finset.mem_coe.2 (Finset.mem_image_of_mem f hq), hfq q⟩
    have hy : I.mkQ y ∈ Submodule.span (MvPolynomial ι R) (I.mkQ '' (T : Set M)) :=
      Submodule.span_mono hsub (hG ▸ Submodule.mem_top)
    rw [← Submodule.map_span] at hy
    obtain ⟨s, hs, hsy⟩ := Submodule.mem_map.1 hy
    refine ⟨s, hs, ?_⟩
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hsy
    rw [← neg_sub]
    exact I.neg_mem hsy

  have hPadd : ∀ s t : M,
      (∃ N₀ : ℤ, ∀ n, N₀ ≤ n → ∃ s' ∈ ℳ n, s' ∈ Submodule.span (MvPolynomial ι R) (T : Set M) ∧ s - s' ∈ I) →
      (∃ N₀ : ℤ, ∀ n, N₀ ≤ n → ∃ s' ∈ ℳ n, s' ∈ Submodule.span (MvPolynomial ι R) (T : Set M) ∧ t - s' ∈ I) →
      ∃ N₀ : ℤ, ∀ n, N₀ ≤ n → ∃ s' ∈ ℳ n, s' ∈ Submodule.span (MvPolynomial ι R) (T : Set M) ∧ s + t - s' ∈ I := by
    rintro s t ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    obtain ⟨s', hs', hs'T, hsI⟩ := h₁ n (le_of_max_le_left hn)
    obtain ⟨t', ht', ht'T, htI⟩ := h₂ n (le_of_max_le_right hn)
    refine ⟨s' + t', add_mem hs' ht', add_mem hs'T ht'T, ?_⟩
    rw [add_sub_add_comm]
    exact add_mem hsI htI
  have hPsmul : ∀ (p : MvPolynomial ι R) (s : M),
      (∃ N₀ : ℤ, ∀ n, N₀ ≤ n → ∃ s' ∈ ℳ n, s' ∈ Submodule.span (MvPolynomial ι R) (T : Set M) ∧ s - s' ∈ I) →
      ∃ N₀ : ℤ, ∀ n, N₀ ≤ n → ∃ s' ∈ ℳ n, s' ∈ Submodule.span (MvPolynomial ι R) (T : Set M) ∧ p • s - s' ∈ I := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      rintro s ⟨N₀, h⟩
      refine ⟨N₀, fun n hn => ?_⟩
      obtain ⟨s', hs', hs'T, hsI⟩ := h n hn
      refine ⟨C a • s', ?_, Submodule.smul_mem _ _ hs'T, ?_⟩
      · rw [← MvPolynomial.algebraMap_eq, algebraMap_smul]
        exact (ℳ n).smul_mem a hs'
      · rw [← smul_sub]
        exact I.smul_mem _ hsI
    | add p q hp hq =>
      intro s hs
      rw [add_smul]
      exact hPadd _ _ (hp s hs) (hq s hs)
    | mul_X p j hp =>
      rintro s ⟨N₀, h⟩
      rw [mul_smul]
      refine hp _ ⟨N₀ + 1, fun n hn => ?_⟩
      obtain ⟨s', hs', hs'T, hsI⟩ := h (n - 1) (by linarith)
      refine ⟨(X j : MvPolynomial ι R) • s', ?_, Submodule.smul_mem _ _ hs'T, ?_⟩
      · have hmem := _root_.GlobalTheory.X_smul_mem_gr ℳ j (n - 1) s' hs'
        rwa [sub_add_cancel] at hmem
      · rw [← smul_sub]
        exact I.smul_mem _ hsI
  have hPspan : ∀ s ∈ Submodule.span (MvPolynomial ι R) (T : Set M),
      ∃ N₀ : ℤ, ∀ n, N₀ ≤ n → ∃ s' ∈ ℳ n, s' ∈ Submodule.span (MvPolynomial ι R) (T : Set M) ∧ s - s' ∈ I := by
    intro s hs
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
      refine ⟨d q, fun n hn => ?_⟩
      obtain ⟨m, hm⟩ : ∃ m : ℕ, n = d q + m := ⟨(n - d q).toNat, by omega⟩
      obtain ⟨h1, h2⟩ := hpow (d q) (f q) (hfd q) m
      refine ⟨(X i : MvPolynomial ι R) ^ m • f q, by rw [hm]; exact h1,
        Submodule.smul_mem _ _ (Submodule.subset_span hx), h2⟩
    | zero => exact ⟨0, fun n _ => ⟨0, zero_mem _, zero_mem _, by rw [sub_zero]; exact zero_mem _⟩⟩
    | add x y _ _ hx hy => exact hPadd x y hx hy
    | smul a x _ hx => exact hPsmul a x hx

  have hhom : ∀ (n : ℤ) (y : M), y ∈ ℳ n →
      ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y ∈ Submodule.span (MvPolynomial ι R) (T : Set M) := by
    intro n y hy
    obtain ⟨s, hs, hys⟩ := hspanT y
    obtain ⟨N₀, hN₀⟩ := hPspan s hs
    obtain ⟨s', hs', hs'T, hsI⟩ := hN₀ (max N₀ n) (le_max_left _ _)
    obtain ⟨m, hm⟩ : ∃ m : ℕ, max N₀ n = n + m := ⟨(max N₀ n - n).toNat, by omega⟩
    obtain ⟨hy1, hy2⟩ := hpow n y hy m
    rw [← hm] at hy1
    have hdiffI : (X i : MvPolynomial ι R) ^ m • y - s' ∈ I := by
      have hsplit : (X i : MvPolynomial ι R) ^ m • y - s' =
          -(y - (X i : MvPolynomial ι R) ^ m • y) + (y - s) + (s - s') := by abel
      rw [hsplit]
      exact add_mem (add_mem (I.neg_mem hy2) hys) hsI
    obtain ⟨w, -, hw⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hdiffI
    obtain ⟨k, hk⟩ := _root_.GlobalTheory.exists_X_pow_smul_eq_zero_of_eq_X_sub_one_smul ℳ i
      (sub_mem hy1 hs') hw.symm
    refine ⟨k + m, ?_⟩
    rw [pow_add, mul_smul]
    have hkm : (X i : MvPolynomial ι R) ^ k • ((X i : MvPolynomial ι R) ^ m • y) =
        (X i : MvPolynomial ι R) ^ k • s' := by
      rw [← sub_eq_zero, ← smul_sub]
      exact hk
    rw [hkm]
    exact Submodule.smul_mem _ _ hs'T
  refine ⟨T, fun y => ?_⟩
  induction y using DirectSum.Decomposition.inductionOn ℳ with
  | zero => exact ⟨0, by rw [smul_zero]; exact zero_mem _⟩
  | homogeneous m => exact hhom _ _ m.2
  | add y z hy hz =>
    obtain ⟨k₁, hk₁⟩ := hy
    obtain ⟨k₂, hk₂⟩ := hz
    refine ⟨k₁ + k₂, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [add_comm, pow_add, mul_smul]
      exact Submodule.smul_mem _ _ hk₁
    · rw [pow_add, mul_smul]
      exact Submodule.smul_mem _ _ hk₂
end _root_.GlobalTheory
end GlobalTheory
