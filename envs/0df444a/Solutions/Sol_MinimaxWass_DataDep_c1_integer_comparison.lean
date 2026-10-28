-- Prove2me | solution 1 for MinimaxWass.DataDep.c1_integer_comparison
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T21:05:36.224294+00:00
-- url     : https://prove2.me/submissions/c57d2e5b-d454-4c4f-8d00-2a6399a5e96c

import Mathlib
import Definitions.Def_MinimaxWass_DataDep_Setting

open MeasureTheory
open scoped ENNReal

namespace Aux_MWD_c1

open MinimaxWass.DataDep

variable {𝒵 : Type*} [MetricSpace 𝒵]

lemma bdd (p lam M : ℝ) (f : 𝒵 → ℝ) (hl : 0 ≤ lam) (hM : ∀ z, f z ≤ M) (z : 𝒵) :
    BddAbove (Set.range fun z' : 𝒵 => f z' - lam * dist z z' ^ p) := by
  refine ⟨M, ?_⟩
  rintro _ ⟨z', rfl⟩
  have : 0 ≤ lam * dist z z' ^ p := mul_nonneg hl (Real.rpow_nonneg dist_nonneg _)
  linarith [hM z']

lemma phi_nonneg (p lam M : ℝ) (hp : 1 ≤ p) (f : 𝒵 → ℝ) (hl : 0 ≤ lam)
    (hf : ∀ z, 0 ≤ f z ∧ f z ≤ M) (z : 𝒵) : 0 ≤ phi p lam f z := by
  unfold phi
  refine le_trans ?_ (le_ciSup (bdd p lam M f hl (fun z => (hf z).2) z) z)
  rw [dist_self, Real.zero_rpow (by linarith), mul_zero, sub_zero]
  exact (hf z).1

lemma phi_anti (p lam lam' M : ℝ) (f : 𝒵 → ℝ) (hl : 0 ≤ lam) (hll : lam ≤ lam')
    (hM : ∀ z, f z ≤ M) (z : 𝒵) : phi p lam' f z ≤ phi p lam f z := by
  unfold phi
  apply ciSup_mono (bdd p lam M f hl hM z)
  intro z'
  have := mul_le_mul_of_nonneg_right hll (Real.rpow_nonneg (dist_nonneg (x := z) (y := z')) p)
  linarith

end Aux_MWD_c1

open MinimaxWass.DataDep Aux_MWD_c1 in
theorem solution {𝒵 : Type*} [MetricSpace 𝒵] [MeasurableSpace 𝒵]
    [BorelSpace 𝒵] [PolishSpace 𝒵]
    (hbounded : Bornology.IsBounded (Set.univ : Set 𝒵))
    (p ϱ M : ℝ) (hp : 1 ≤ p) (hϱ : 0 < ϱ)
    (ℱ : Set (𝒵 → ℝ))
    (husc : ∀ f ∈ ℱ, UpperSemicontinuous f)
    (hval : ∀ f ∈ ℱ, ∀ z, 0 ≤ f z ∧ f z ≤ M)
    (hC : entropyIntegral ℱ < ⊤)
    (P : ProbabilityMeasure 𝒵) (n : ℕ) (hn : 0 < n)
    (t : ℝ) (ht : 0 < t)
    (ω : Fin n → 𝒵) (f : 𝒵 → ℝ) (hf : f ∈ ℱ) :
    (⨅ k : {k : ℕ // 1 ≤ k},
      (k.1 : ℝ) * ϱ ^ p +
      (1 / (n : ℝ)) * ∑ i : Fin n, phi p (k.1 : ℝ) f (ω i) +
      24 * (entropyIntegral ℱ).toReal / Real.sqrt n +
      M * (t + Real.sqrt (Real.log (k.1 : ℝ))) / Real.sqrt n) ≤
    ⨅ lam : Set.Ici (0 : ℝ),
      (lam.1 + 1) * ϱ ^ p +
      (1 / (n : ℝ)) * ∑ i : Fin n, phi p lam.1 f (ω i) +
      24 * (entropyIntegral ℱ).toReal / Real.sqrt n +
      M * t / Real.sqrt n +
      M * Real.sqrt (Real.log (lam.1 + 1)) / Real.sqrt n := by
  have hfv := hval f hf
  have hM : 0 ≤ M := le_trans (hfv (ω ⟨0, hn⟩)).1 (hfv (ω ⟨0, hn⟩)).2
  have hϱp : 0 < ϱ ^ p := Real.rpow_pos_of_pos hϱ p
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hn' : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  haveI : Nonempty (Set.Ici (0 : ℝ)) := ⟨⟨0, le_refl (0 : ℝ)⟩⟩
  have hbb : BddBelow (Set.range fun k : {k : ℕ // 1 ≤ k} =>
      (k.1 : ℝ) * ϱ ^ p +
      (1 / (n : ℝ)) * ∑ i : Fin n, phi p (k.1 : ℝ) f (ω i) +
      24 * (entropyIntegral ℱ).toReal / Real.sqrt n +
      M * (t + Real.sqrt (Real.log (k.1 : ℝ))) / Real.sqrt n) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨k, rfl⟩
    have h1 : 0 ≤ (k.1 : ℝ) * ϱ ^ p := by positivity
    have h2 : 0 ≤ (1 / (n : ℝ)) * ∑ i : Fin n, phi p (k.1 : ℝ) f (ω i) :=
      mul_nonneg hn'.le (Finset.sum_nonneg fun i _ =>
        phi_nonneg p _ M hp f (Nat.cast_nonneg _) hfv _)
    have h3 : 0 ≤ 24 * (entropyIntegral ℱ).toReal / Real.sqrt n := by positivity
    have h4 : 0 ≤ M * (t + Real.sqrt (Real.log (k.1 : ℝ))) / Real.sqrt n := by
      apply div_nonneg _ hsn.le
      exact mul_nonneg hM (by positivity)
    linarith
  apply le_ciInf
  rintro ⟨lam, hlam⟩
  simp only [Set.mem_Ici] at hlam
  have hk1 : 1 ≤ ⌊lam⌋₊ + 1 := Nat.le_add_left 1 _
  refine le_trans (ciInf_le hbb ⟨⌊lam⌋₊ + 1, hk1⟩) ?_
  dsimp only
  have hkl : (((⌊lam⌋₊ + 1 : ℕ)) : ℝ) ≤ lam + 1 := by
    push_cast; linarith [Nat.floor_le hlam]
  have hlk : lam ≤ (((⌊lam⌋₊ + 1 : ℕ)) : ℝ) := by
    push_cast; exact (Nat.lt_floor_add_one lam).le
  have hk0 : (0 : ℝ) < (((⌊lam⌋₊ + 1 : ℕ)) : ℝ) := by positivity
  have e1 : (((⌊lam⌋₊ + 1 : ℕ)) : ℝ) * ϱ ^ p ≤ (lam + 1) * ϱ ^ p :=
    mul_le_mul_of_nonneg_right hkl hϱp.le
  have e2 : (1 / (n : ℝ)) * ∑ i : Fin n, phi p (((⌊lam⌋₊ + 1 : ℕ)) : ℝ) f (ω i) ≤
      (1 / (n : ℝ)) * ∑ i : Fin n, phi p lam f (ω i) :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
      phi_anti p lam _ M f hlam hlk (fun z => (hfv z).2) _) hn'.le
  have e3 : Real.sqrt (Real.log (((⌊lam⌋₊ + 1 : ℕ)) : ℝ)) ≤ Real.sqrt (Real.log (lam + 1)) :=
    Real.sqrt_le_sqrt (Real.log_le_log hk0 hkl)
  have e4 : M * (t + Real.sqrt (Real.log (((⌊lam⌋₊ + 1 : ℕ)) : ℝ))) / Real.sqrt n ≤
      M * t / Real.sqrt n + M * Real.sqrt (Real.log (lam + 1)) / Real.sqrt n := by
    rw [← add_div, ← mul_add]
    apply div_le_div_of_nonneg_right _ hsn.le
    exact mul_le_mul_of_nonneg_left (by linarith) hM
  linarith
