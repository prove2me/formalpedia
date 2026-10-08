-- Prove2me | solution 1 for LocalRademacher.Classif.g_identity
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T11:43:03.355988+00:00
-- url     : https://prove2.me/submissions/516d8905-b89d-45c7-b525-36e5d4fa39d7

import Mathlib
import Definitions.Def_UnderstandingML_Rademacher
import Definitions.Def_LocalRademacher_Classif_Setting

set_option autoImplicit false

open LocalRademacher.Classif in
lemma e4f9_ell_nonneg (a b : ℝ) : 0 ≤ ell a b := by
  unfold ell; split_ifs <;> norm_num

lemma e4f9_iInf_add {ι : Sort*} [Nonempty ι] (g : ι → ℝ) (c : ℝ)
    (hb : BddBelow (Set.range g)) : (⨅ i, (g i + c)) = (⨅ i, g i) + c :=
  ((OrderIso.addRight c).map_ciInf hb).symm

open LocalRademacher.Classif in
lemma e4f9_key (a s y μ : ℝ) (ha : a = 1 ∨ a = -1) (hs : s = 1 ∨ s = -1)
    (hy : y = 1 ∨ y = -1) (hμ : 0 ≤ μ) :
    ell a s + μ * ell a y =
      |s + μ * y| * ell a (Real.sign (s + μ * y)) - |s + μ * y| / 2 + (1 + μ) / 2 := by
  rcases hs with rfl | rfl <;> rcases hy with rfl | rfl
  · have h1 : (0:ℝ) < 1 + μ * 1 := by linarith
    rw [Real.sign_of_pos h1, abs_of_pos h1]
    rcases ha with rfl | rfl <;> norm_num [ell] <;> ring
  · rcases lt_trichotomy μ 1 with h | rfl | h
    · have h1 : (0:ℝ) < 1 + μ * -1 := by linarith
      rw [Real.sign_of_pos h1, abs_of_pos h1]
      rcases ha with rfl | rfl <;> norm_num [ell] <;> ring
    · have h1 : (1:ℝ) + 1 * -1 = 0 := by norm_num
      rw [h1, Real.sign_zero]
      rcases ha with rfl | rfl <;> norm_num [ell]
    · have h1 : (1:ℝ) + μ * -1 < 0 := by linarith
      rw [Real.sign_of_neg h1, abs_of_neg h1]
      rcases ha with rfl | rfl <;> norm_num [ell] <;> ring
  · rcases lt_trichotomy μ 1 with h | rfl | h
    · have h1 : (-1:ℝ) + μ * 1 < 0 := by linarith
      rw [Real.sign_of_neg h1, abs_of_neg h1]
      rcases ha with rfl | rfl <;> norm_num [ell] <;> ring
    · have h1 : (-1:ℝ) + 1 * 1 = 0 := by norm_num
      rw [h1, Real.sign_zero]
      rcases ha with rfl | rfl <;> norm_num [ell]
    · have h1 : (0:ℝ) < -1 + μ * 1 := by linarith
      rw [Real.sign_of_pos h1, abs_of_pos h1]
      rcases ha with rfl | rfl <;> norm_num [ell] <;> ring
  · have h1 : (-1:ℝ) + μ * -1 < 0 := by linarith
    rw [Real.sign_of_neg h1, abs_of_neg h1]
    rcases ha with rfl | rfl <;> norm_num [ell] <;> ring

open LocalRademacher.Classif in
theorem solution {X : Type*} (n : ℕ) (hn : 0 < n) (xs : Fin n → X) (ys : Fin n → ℝ)
    (hys : ∀ i, ys i = 1 ∨ ys i = -1)
    (F : Set (X → ℝ)) (hF : ∀ f ∈ F, ∀ z, f z = 1 ∨ f z = -1) (hFne : F.Nonempty)
    (σ : Fin n → Bool) (r α μ : ℝ) (hμ : 0 ≤ μ) :
    (⨅ f : F, (empLoss xs (UnderstandingML.signVec σ) f.1
        + μ * (empLoss xs ys f.1 - 2 * r / α ^ 2))) =
      (⨅ f : F, (1 / (n : ℝ)) * ∑ i, (ell (f.1 (xs i)) (UnderstandingML.signVec σ i)
        + μ * ell (f.1 (xs i)) (ys i))) - μ * (2 * r / α ^ 2) ∧
    (⨅ f : F, (1 / (n : ℝ)) * ∑ i, (ell (f.1 (xs i)) (UnderstandingML.signVec σ i)
        + μ * ell (f.1 (xs i)) (ys i))) - μ * (2 * r / α ^ 2) =
      J F xs ys σ μ - (1 / (2 * (n : ℝ))) * ∑ i, |UnderstandingML.signVec σ i + μ * ys i|
        + (1 + μ) / 2 - μ * (2 * r / α ^ 2) := by
  haveI : Nonempty F := hFne.to_subtype
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hsig : ∀ i, UnderstandingML.signVec σ i = 1 ∨ UnderstandingML.signVec σ i = -1 := by
    intro i; unfold UnderstandingML.signVec; split_ifs <;> simp
  set c := 2 * r / α ^ 2 with hc
  set G : F → ℝ := fun f => (1 / (n : ℝ)) * ∑ i, (ell (f.1 (xs i)) (UnderstandingML.signVec σ i)
        + μ * ell (f.1 (xs i)) (ys i)) with hG
  set H : F → ℝ := fun f => (1 / (n : ℝ)) * ∑ i, |UnderstandingML.signVec σ i + μ * ys i| *
    ell ((f : X → ℝ) (xs i)) (Real.sign (UnderstandingML.signVec σ i + μ * ys i)) with hH
  have hGb : BddBelow (Set.range G) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨f, rfl⟩
    simp only [hG]
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg; intro i _
    have := e4f9_ell_nonneg (f.1 (xs i)) (UnderstandingML.signVec σ i)
    have := e4f9_ell_nonneg (f.1 (xs i)) (ys i)
    positivity
  have hHb : BddBelow (Set.range H) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨f, rfl⟩
    simp only [hH]
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg; intro i _
    have := e4f9_ell_nonneg (f.1 (xs i)) (Real.sign (UnderstandingML.signVec σ i + μ * ys i))
    positivity
  constructor
  · have h1 : ∀ f : F, empLoss xs (UnderstandingML.signVec σ) f.1
        + μ * (empLoss xs ys f.1 - c) = G f + (-(μ * c)) := by
      intro f
      simp only [hG, empLoss, Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    simp_rw [h1]
    rw [e4f9_iInf_add G _ hGb]
    ring
  · have h2 : ∀ f : F, G f = H f +
        (-(1 / (2 * (n : ℝ))) * ∑ i, |UnderstandingML.signVec σ i + μ * ys i| + (1 + μ) / 2) := by
      intro f
      simp only [hG, hH]
      have hk : ∀ i, ell (f.1 (xs i)) (UnderstandingML.signVec σ i) + μ * ell (f.1 (xs i)) (ys i)
          = |UnderstandingML.signVec σ i + μ * ys i| *
              ell (f.1 (xs i)) (Real.sign (UnderstandingML.signVec σ i + μ * ys i))
            - |UnderstandingML.signVec σ i + μ * ys i| / 2 + (1 + μ) / 2 := fun i =>
        e4f9_key _ _ _ μ (hF f.1 f.2 _) (hsig i) (hys i) hμ
      simp_rw [hk, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, ← Finset.sum_div, nsmul_eq_mul]
      field_simp
      ring
    have hGH : G = fun f => H f +
        (-(1 / (2 * (n : ℝ))) * ∑ i, |UnderstandingML.signVec σ i + μ * ys i| + (1 + μ) / 2) :=
      funext h2
    rw [hGH, e4f9_iInf_add H _ hHb]
    have hJ : J F xs ys σ μ = ⨅ f, H f := rfl
    rw [hJ]
    ring
