-- Prove2me | solution 1 for LocalRademacher.Classif.lemma_6_4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T01:46:45.642645+00:00
-- url     : https://prove2.me/submissions/f83d3a62-763b-4cb0-9685-1e1eeb53b904

import Mathlib
import Definitions.Def_UnderstandingML_Rademacher
import Definitions.Def_LocalRademacher_Classif_Setting



namespace LocalRademacher.Classif

lemma l64_ell_pm (a b : ℝ) (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    ell a b = (1 - a * b) / 2 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [ell] <;> norm_num

lemma l64_ell_nonneg (a b : ℝ) : 0 ≤ ell a b := by
  unfold ell; split_ifs <;> norm_num

noncomputable def l64_flip {n : ℕ} (ys : Fin n → ℝ) (σ : Fin n → Bool) : Fin n → Bool :=
  fun i => if ys i = 1 then !σ i else σ i

lemma l64_flip_inv {n : ℕ} (ys : Fin n → ℝ) (σ : Fin n → Bool) :
    l64_flip ys (l64_flip ys σ) = σ := by
  funext i; unfold l64_flip; split_ifs <;> simp

lemma l64_signVec_flip {n : ℕ} (ys : Fin n → ℝ) (hys : ∀ i, ys i = 1 ∨ ys i = -1)
    (σ : Fin n → Bool) (i : Fin n) :
    UnderstandingML.signVec (l64_flip ys σ) i = - UnderstandingML.signVec σ i * ys i := by
  rcases hys i with h | h
  · simp only [l64_flip, UnderstandingML.signVec, h]
    cases σ i <;> simp
  · have : ¬ ys i = 1 := by rw [h]; norm_num
    have h1 : ((-1 : ℝ) = 1) ↔ False := by norm_num
    simp only [l64_flip, UnderstandingML.signVec, h, h1]
    cases σ i <;> simp

lemma l64_sum_zero {n : ℕ} (ys : Fin n → ℝ) :
    ∑ τ : Fin n → Bool, ∑ i, UnderstandingML.signVec τ i * ys i = 0 := by
  let e : (Fin n → Bool) ≃ (Fin n → Bool) :=
    Function.Involutive.toPerm (fun τ i => !τ i) (by intro τ; funext i; simp)
  have h : ∑ τ : Fin n → Bool, ∑ i, UnderstandingML.signVec τ i * ys i
      = ∑ τ : Fin n → Bool, ∑ i, UnderstandingML.signVec (e τ) i * ys i :=
    (Equiv.sum_comp e (fun τ => ∑ i, UnderstandingML.signVec τ i * ys i)).symm
  have h2 : ∀ τ : Fin n → Bool, ∑ i, UnderstandingML.signVec (e τ) i * ys i
      = - ∑ i, UnderstandingML.signVec τ i * ys i := by
    intro τ
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have he : e τ i = !τ i := rfl
    simp only [he, UnderstandingML.signVec]
    cases τ i <;> simp
  simp only [h2, Finset.sum_neg_distrib] at h
  linarith

theorem l64_core {X : Type*} (n : ℕ) (hn : 0 < n) (xs : Fin n → X) (ys : Fin n → ℝ)
    (hys : ∀ i, ys i = 1 ∨ ys i = -1)
    (F : Set (X → ℝ)) (hF : ∀ f ∈ F, ∀ z, f z = 1 ∨ f z = -1)
    (b : ℝ) (hfeas : ∃ f ∈ F, empLoss xs ys f ≤ b) :
    UnderstandingML.rademacher (lossVecs F xs ys b) =
      1 / 2 - (1 / 2 ^ n : ℝ) * ∑ σ : Fin n → Bool,
        ⨅ f : {f : X → ℝ // f ∈ F ∧ empLoss xs ys f ≤ b},
          empLoss xs (UnderstandingML.signVec σ) f.1 := by
  classical
  set S := {f : X → ℝ // f ∈ F ∧ empLoss xs ys f ≤ b} with hS
  haveI : Nonempty S := by
    obtain ⟨f, hf, hfb⟩ := hfeas
    exact ⟨⟨f, hf, hfb⟩⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hL0 : ∀ (z : Fin n → ℝ) (f : X → ℝ), 0 ≤ empLoss xs z f := by
    intro z f
    unfold empLoss
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => l64_ell_nonneg _ _)
  let I : (Fin n → Bool) → ℝ := fun τ => ⨅ f : S, empLoss xs (UnderstandingML.signVec τ) f.1
  let h : (Fin n → Bool) → ℝ := fun τ => ∑ i, UnderstandingML.signVec τ i * ys i
  -- per-sigma identity
  have key : ∀ σ : Fin n → Bool,
      (⨆ a : lossVecs F xs ys b, ∑ i, UnderstandingML.signVec σ i * (a : Fin n → ℝ) i)
        = (n / 2 - h (l64_flip ys σ) / 2) - n * I (l64_flip ys σ) := by
    intro σ
    set τ := l64_flip ys σ with hτ
    let φ : S → lossVecs F xs ys b := fun s =>
      ⟨fun i => ell (s.1 (xs i)) (ys i), ⟨s.1, s.2.1, s.2.2, rfl⟩⟩
    have hφ : Function.Surjective φ := by
      rintro ⟨v, f, hf, hfb, rfl⟩
      exact ⟨⟨f, hf, hfb⟩, rfl⟩
    rw [← hφ.iSup_comp]
    have hval : ∀ s : S, ∑ i, UnderstandingML.signVec σ i * (φ s : Fin n → ℝ) i
        = (n / 2 - h τ / 2) - n * empLoss xs (UnderstandingML.signVec τ) s.1 := by
      intro s
      have e1 : (n : ℝ) * empLoss xs (UnderstandingML.signVec τ) s.1
          = ∑ i, ell (s.1 (xs i)) (UnderstandingML.signVec τ i) := by
        unfold empLoss; field_simp
      rw [e1]
      have hsv : ∀ i, UnderstandingML.signVec τ i = 1 ∨ UnderstandingML.signVec τ i = -1 := by
        intro i; unfold UnderstandingML.signVec; split_ifs <;> simp
      have : ∀ i, UnderstandingML.signVec σ i * (φ s : Fin n → ℝ) i
          = (1 / 2 - UnderstandingML.signVec τ i * ys i / 2)
            - ell (s.1 (xs i)) (UnderstandingML.signVec τ i) := by
        intro i
        have hs := l64_signVec_flip ys hys σ i
        rw [← hτ] at hs
        have hσ : UnderstandingML.signVec σ i = - UnderstandingML.signVec τ i * ys i := by
          rw [hs]
          rcases hys i with h1 | h1 <;> rw [h1] <;> ring_nf <;>
            (try (have := hsv i; rcases this with h2 | h2 <;> rw [h2] <;> norm_num))
        show UnderstandingML.signVec σ i * ell (s.1 (xs i)) (ys i) = _
        rw [hσ, l64_ell_pm _ _ (hF _ s.2.1 _) (hys i),
          l64_ell_pm _ _ (hF _ s.2.1 _) (hsv i)]
        rcases hys i with h1 | h1 <;> rw [h1] <;> ring
      have hd : ∑ x, UnderstandingML.signVec τ x * ys x / 2 = h τ / 2 := by
        simp only [h]; rw [← Finset.sum_div]
      rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_sub_distrib, Finset.sum_sub_distrib, hd]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    simp_rw [hval]
    have := Antitone.map_ciInf_of_continuousAt (f := fun x : ℝ => (n / 2 - h τ / 2) - n * x)
      (g := fun s : S => empLoss xs (UnderstandingML.signVec τ) s.1)
      (by fun_prop) (fun x y hxy => by simp only; nlinarith)
      ⟨0, by rintro _ ⟨s, rfl⟩; exact hL0 _ _⟩
    exact this.symm
  -- assemble
  let e : (Fin n → Bool) ≃ (Fin n → Bool) :=
    Function.Involutive.toPerm (l64_flip ys) (l64_flip_inv ys)
  have hsum : ∑ σ : Fin n → Bool, (⨆ a : lossVecs F xs ys b,
        ∑ i, UnderstandingML.signVec σ i * (a : Fin n → ℝ) i)
      = ∑ τ : Fin n → Bool, ((n / 2 - h τ / 2) - n * I τ) := by
    simp_rw [key]
    exact Equiv.sum_comp e (fun τ => ((n : ℝ) / 2 - h τ / 2) - n * I τ)
  unfold UnderstandingML.rademacher
  have h0 : ∑ τ : Fin n → Bool, h τ = 0 := l64_sum_zero ys
  have hh : ∑ τ : Fin n → Bool, h τ / 2 = 0 := by rw [← Finset.sum_div, h0, zero_div]
  rw [hsum, Finset.sum_sub_distrib, Finset.sum_sub_distrib, hh, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp
  ring

end LocalRademacher.Classif

open LocalRademacher.Classif


theorem solution {X : Type*} (n : ℕ) (hn : 0 < n) (xs : Fin n → X) (ys : Fin n → ℝ)
    (hys : ∀ i, ys i = 1 ∨ ys i = -1)
    (F : Set (X → ℝ)) (hF : ∀ f ∈ F, ∀ z, f z = 1 ∨ f z = -1)
    (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hfeas : ∃ f ∈ F, empLoss xs ys f ≤ b) :
    UnderstandingML.rademacher (lossVecs F xs ys b) =
      1 / 2 - (1 / 2 ^ n : ℝ) * ∑ σ : Fin n → Bool,
        ⨅ f : {f : X → ℝ // f ∈ F ∧ empLoss xs ys f ≤ b},
          empLoss xs (UnderstandingML.signVec σ) f.1 := by
  exact l64_core n hn xs ys hys F hF b hfeas
