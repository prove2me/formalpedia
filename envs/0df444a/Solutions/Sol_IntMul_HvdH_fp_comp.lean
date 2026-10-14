-- Prove2me | solution 1 for IntMul.HvdH.fp_comp
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-12T00:50:04.971579+00:00
-- url     : https://prove2.me/submissions/3ecc6a90-afdf-4a5b-a32f-8e5336d42dc6

import Definitions.Def_IntMul_HvdH_FPApprox

open Complex

namespace IntMul.HvdH.FPPf
open IntMul.HvdH

/-- The identity is its own approximation. -/
theorem fp_id {ι : Type*} (p : ℕ) : FPApprox (ι := ι) p id id 0 := by
  intro U hU
  refine ⟨hU, fun k => ?_⟩
  have hp : (2 : ℂ) ^ p ≠ 0 := pow_ne_zero _ two_ne_zero
  simp only [id]
  rw [mul_div_cancel₀ _ hp, sub_self, norm_zero]

/-- Corollary 2.8: composing approximations adds their errors, provided the second exact map
is `1`-Lipschitz. -/
theorem fp_comp {ι κ μ : Type*} (p : ℕ) {Aa : (ι → ℤ × ℤ) → (κ → ℤ × ℤ)} {A : (ι → ℂ) → (κ → ℂ)}
    {Ba : (κ → ℤ × ℤ) → (μ → ℤ × ℤ)} {B : (κ → ℂ) → (μ → ℂ)} {ε₁ ε₂ : ℝ}
    (hA : FPApprox p Aa A ε₁) (hB : FPApprox p Ba B ε₂) (hBl : SupLip B) :
    FPApprox p (Ba ∘ Aa) (B ∘ A) (ε₁ + ε₂) := by
  intro U hU
  obtain ⟨hV, hAe⟩ := hA U hU
  obtain ⟨hW, hBe⟩ := hB (Aa U) hV
  refine ⟨hW, fun k => ?_⟩
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  set u : ι → ℂ := fun i => gC (U i) / 2 ^ p
  set v : κ → ℂ := fun i => gC (Aa U i) / 2 ^ p
  have hvu : ∀ i, ‖v i - A u i‖ ≤ ε₁ / 2 ^ p := by
    intro i
    have e : v i - A u i = (gC (Aa U i) - 2 ^ p * A u i) / 2 ^ p := by
      simp only [v]; field_simp
    rw [e, norm_div, norm_pow, Complex.norm_two]
    exact div_le_div_of_nonneg_right (hAe i) hp.le
  have hL := hBl v (A u) _ hvu k
  have e : gC (Ba (Aa U) k) - 2 ^ p * B (A u) k =
      (gC (Ba (Aa U) k) - 2 ^ p * B v k) + 2 ^ p * (B v k - B (A u) k) := by ring
  show ‖gC (Ba (Aa U) k) - 2 ^ p * B (A u) k‖ ≤ ε₁ + ε₂
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_pow, Complex.norm_two]
  have h2 : (2 : ℝ) ^ p * ‖B v k - B (A u) k‖ ≤ ε₁ := by
    calc _ ≤ 2 ^ p * (ε₁ / 2 ^ p) := mul_le_mul_of_nonneg_left hL hp.le
      _ = ε₁ := by field_simp
  linarith [hBe k]

theorem lip_comp {ι κ μ : Type*} {A : (ι → ℂ) → (κ → ℂ)} {B : (κ → ℂ) → (μ → ℂ)}
    (hA : SupLip A) (hB : SupLip B) : SupLip (B ∘ A) :=
  fun x y δ h k => hB _ _ δ (hA x y δ h) k

theorem fp_slice {d : ℕ} (p : ℕ) (i : Fin d) {Aa : (ℕ → ℤ × ℤ) → (ℕ → ℤ × ℤ)}
    {A : (ℕ → ℂ) → (ℕ → ℂ)} {ε : ℝ} (hA : FPApprox p Aa A ε) :
    FPApprox p (sliceMapZ i Aa) (sliceMap i A) ε := by
  intro U hU
  have hrow : ∀ j : Fin d → ℕ, InDisc p (fun k => U (Function.update j i k)) := fun j k => hU _
  exact ⟨fun j => (hA _ (hrow j)).1 (j i), fun j => (hA _ (hrow j)).2 (j i)⟩

theorem lip_slice {d : ℕ} (i : Fin d) {A : (ℕ → ℂ) → (ℕ → ℂ)} (hA : SupLip A) :
    SupLip (sliceMap i A) :=
  fun x y δ h j => hA _ _ δ (fun k => h _) (j i)

theorem fp_sliceComp {d : ℕ} (p : ℕ) {Aa : Fin d → (ℕ → ℤ × ℤ) → (ℕ → ℤ × ℤ)}
    {A : Fin d → (ℕ → ℂ) → (ℕ → ℂ)} {ε : Fin d → ℝ}
    (hA : ∀ i, FPApprox p (Aa i) (A i) (ε i)) (hL : ∀ i, SupLip (A i)) :
    ∀ l : List (Fin d), FPApprox p (sliceCompZ Aa l) (sliceComp A l) (l.map ε).sum ∧
      SupLip (sliceComp A l)
  | [] => ⟨by simpa [sliceCompZ, sliceComp] using fp_id p, fun _ _ _ h k => h k⟩
  | i :: l => by
    obtain ⟨h1, h2⟩ := fp_sliceComp p hA hL l
    refine ⟨?_, lip_comp (lip_slice i (hL i)) h2⟩
    have := fp_comp p (fp_slice p i (hA i)) h1 h2
    simpa [sliceCompZ, sliceComp] using this

/-- Lemma 2.11: the fixed-point tensor product of approximations approximates the tensor
product, with error the sum of the errors. -/
theorem fp_tensor {d : ℕ} (p : ℕ) (Aa : Fin d → (ℕ → ℤ × ℤ) → (ℕ → ℤ × ℤ))
    (A : Fin d → (ℕ → ℂ) → (ℕ → ℂ)) (ε : Fin d → ℝ)
    (hA : ∀ i, FPApprox p (Aa i) (A i) (ε i)) (hL : ∀ i, SupLip (A i)) :
    FPApprox p (tensorMapZ Aa) (tensorMap A) (∑ i, ε i) := by
  have h := (fp_sliceComp p hA hL (List.finRange d)).1
  rw [Fin.sum_univ_def]
  exact h

theorem lip_sliceComp {d : ℕ} (A : Fin d → (ℕ → ℂ) → (ℕ → ℂ)) (hL : ∀ i, SupLip (A i)) :
    ∀ l : List (Fin d), SupLip (sliceComp A l)
  | [] => fun _ _ _ h k => h k
  | i :: l => lip_comp (lip_slice i (hL i)) (lip_sliceComp A hL l)

theorem lip_tensor {d : ℕ} (A : Fin d → (ℕ → ℂ) → (ℕ → ℂ)) (hL : ∀ i, SupLip (A i)) :
    SupLip (tensorMap A) :=
  lip_sliceComp A hL (List.finRange d)

end IntMul.HvdH.FPPf

open IntMul.HvdH in
theorem solution {ι κ μ : Type*} (p : ℕ) {Aa : (ι → ℤ × ℤ) → (κ → ℤ × ℤ)} {A : (ι → ℂ) → (κ → ℂ)}
    {Ba : (κ → ℤ × ℤ) → (μ → ℤ × ℤ)} {B : (κ → ℂ) → (μ → ℂ)} {ε₁ ε₂ : ℝ}
    (hA : FPApprox p Aa A ε₁) (hB : FPApprox p Ba B ε₂) (hBl : SupLip B) :
    FPApprox p (Ba ∘ Aa) (B ∘ A) (ε₁ + ε₂) :=
  IntMul.HvdH.FPPf.fp_comp p hA hB hBl
