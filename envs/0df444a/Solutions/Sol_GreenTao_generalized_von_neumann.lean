-- Prove2me | solution 1 for GreenTao.generalized_von_neumann
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T21:20:26.714979+00:00
-- url     : https://prove2.me/submissions/3c136f08-4e69-47fe-b26e-2d854abd2634

import Theorems.Thm_GreenTao_linear_forms_convex_mixture
import Theorems.Thm_GreenTao_weighted_error_from_moments
import Theorems.Thm_GreenTao_progression_cs_cube_bound
import Theorems.Thm_GreenTao_linear_forms_cs_moments
import Mathlib

open scoped BigOperators Topology
open Filter GreenTao

private lemma avg_nonneg_vn {α : Type} [Fintype α] {f : α → ℝ}
    (h : ∀ x, 0 ≤ f x) : 0 ≤ avg f := by
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun x _ => h x)

private lemma avg_sub_vn {α : Type} [Fintype α] (f g : α → ℝ) :
    avg (fun x => f x - g x) = avg f - avg g := by
  simp [avg, Finset.sum_sub_distrib, mul_sub]

private lemma avg_mul_vn {α : Type} [Fintype α] (c : ℝ) (f : α → ℝ) :
    avg (fun x => c * f x) = c * avg f := by
  simp only [avg, ← Finset.mul_sum]
  ring

private lemma avg_prod_vn {α β : Type} [Fintype α] [Fintype β] (f : α × β → ℝ) :
    avg f = avg (fun a => avg fun b => f (a, b)) := by
  simp only [avg, Fintype.card_prod, Nat.cast_mul, mul_inv_rev, Fintype.sum_prod_type,
    ← Finset.mul_sum]
  ring

private lemma cube_scale_vn (d : ℕ) {m : ℕ+} (c : ℝ) (f : ZMod (m : ℕ) → ℝ) :
    cubeAvg d (fun x => c * f x) = c ^ (2 ^ d) * cubeAvg d f := by
  unfold cubeAvg
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]
  simp_rw [avg_mul_vn]

private lemma mixed_scale_vn (k : ℕ) {m : ℕ+} (c : ℝ)
    (F : Fin k → ZMod (m : ℕ) → ℝ) :
    mixedAPAvg k (fun j x => c * F j x) = c ^ k * mixedAPAvg k F := by
  unfold mixedAPAvg
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp_rw [avg_mul_vn]

private lemma count_fixed_slot_vn (d : ℕ) (hd : 2 ≤ d) (M : ℕ → ℕ+)
    (hprime : ∀ n, Nat.Prime (M n : ℕ))
    (hM : Tendsto (fun n => (M n : ℕ)) atTop atTop)
    (μ : Family M) (hμ : ∀ n x, 0 ≤ μ n x)
    (hLF : LinearFormsCondition M μ ((d + 1) * 2 ^ d) (3 * (d + 1) - 4) (d + 1))
    (j : Fin (d + 1)) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n in atTop, ∀ F : Fin (d + 1) → ZMod (M n : ℕ) → ℝ,
      (∀ i x, |F i x| ≤ μ n x) →
      |cubeAvg d (F j)| ≤ η ^ (2 ^ d) / 4 →
      |mixedAPAvg (d + 1) F| ≤ η := by
  classical
  let A (n : ℕ) := ZMod (M n : ℕ) × (Fin d → ZMod (M n : ℕ))
  let V : ∀ n, A n → ℝ := fun n p =>
    ∏ ω : Fin d → Bool, μ n (p.1 + ∑ i : Fin d, if ω i then p.2 i else 0)
  let W : ∀ n, A n → ℝ := fun n p => csWeight d j (μ n) p.1 p.2
  have hV (n) (p : A n) : 0 ≤ V n p := Finset.prod_nonneg fun ω _ => hμ n _
  obtain ⟨hP, hMom⟩ := linear_forms_cs_moments d hd M hprime hM μ hμ hLF j
  have h₀ : Tendsto (fun n => avg (V n)) atTop (𝓝 1) := by
    apply (hMom 0 (by omega)).congr'
    exact Eventually.of_forall fun n => by
      simpa only [V, pow_zero, one_mul] using (avg_prod_vn (V n)).symm
  have h₁ : Tendsto (fun n => avg (fun p => W n p * V n p)) atTop (𝓝 1) := by
    apply (hMom 1 (by omega)).congr'
    exact Eventually.of_forall fun n => by
      simpa only [V, W, pow_one] using (avg_prod_vn (fun p => W n p * V n p)).symm
  have h₂ : Tendsto (fun n => avg (fun p => W n p ^ 2 * V n p)) atTop (𝓝 1) := by
    apply (hMom 2 (by omega)).congr'
    exact Eventually.of_forall fun n => by
      simpa only [V, W] using (avg_prod_vn (fun p => W n p ^ 2 * V n p)).symm
  have herror := weighted_error_from_moments A V W hV h₀ h₁ h₂
    (η ^ (2 ^ d) / 4) (by positivity)
  have hPsmall : ∀ᶠ n in atTop, csFactor d j (μ n) < 2 :=
    (tendsto_order.mp hP).2 _ (by norm_num)
  have hlarge : ∀ᶠ n in atTop, d < (M n : ℕ) := hM.eventually (eventually_gt_atTop d)
  filter_upwards [herror, hPsmall, hlarge] with n he hp hm
  intro F hF hcube
  let H : A n → ℝ := fun p =>
    ∏ ω : Fin d → Bool, F j (p.1 + ∑ i : Fin d, if ω i then p.2 i else 0)
  have hH (p : A n) : |H p| ≤ V n p := by
    simp only [H, V, Finset.abs_prod]
    exact Finset.prod_le_prod (fun ω _ => abs_nonneg _) (fun ω _ => hF j _)
  have he' := he H hH
  have hdiff : avg (fun p => (W n p - 1) * H p) =
      weightedCubeAvg d (csWeight d j (μ n)) (F j) - cubeAvg d (F j) := by
    calc
      _ = avg (fun p => W n p * H p - H p) := by
        congr 1
        funext p
        ring
      _ = avg (fun p => W n p * H p) - avg H := avg_sub_vn _ _
      _ = _ := by rw [avg_prod_vn, avg_prod_vn]; rfl
  rw [hdiff] at he'
  have hw : weightedCubeAvg d (csWeight d j (μ n)) (F j) ≤
      |cubeAvg d (F j)| + η ^ (2 ^ d) / 4 := by
    have h := (abs_le.mp he').2
    have hc := le_abs_self (cubeAvg d (F j))
    linarith
  have hPnonneg : 0 ≤ csFactor d j (μ n) := by
    apply Finset.prod_nonneg
    intro l _
    apply pow_nonneg
    apply avg_nonneg_vn
    intro y
    apply avg_nonneg_vn
    intro y'
    exact Finset.prod_nonneg fun ω _ => hμ n _
  have hpow : |mixedAPAvg (d + 1) F| ^ (2 ^ d) ≤ η ^ (2 ^ d) := by
    calc
      _ ≤ csFactor d j (μ n) * weightedCubeAvg d (csWeight d j (μ n)) (F j) :=
        progression_cs_cube_bound d hd (M n) (hprime n) hm (μ n) (hμ n) j F hF
      _ ≤ csFactor d j (μ n) * (|cubeAvg d (F j)| + η ^ (2 ^ d) / 4) :=
        mul_le_mul_of_nonneg_left hw hPnonneg
      _ ≤ 2 * (|cubeAvg d (F j)| + η ^ (2 ^ d) / 4) :=
        mul_le_mul_of_nonneg_right hp.le (by positivity)
      _ ≤ 2 * (η ^ (2 ^ d) / 4 + η ^ (2 ^ d) / 4) := by gcongr
      _ = _ := by ring
  exact le_of_pow_le_pow_left₀ (by positivity : 2 ^ d ≠ 0) hη.le hpow

theorem solution
    (k : ℕ) (hk : 3 ≤ k) (M : ℕ → ℕ+)
    (hprime : ∀ n, Nat.Prime (M n : ℕ))
    (hM : Tendsto (fun n => (M n : ℕ)) atTop atTop)
    (ν : GreenTao.Family M) (hν : GreenTao.Pseudorandom k M ν)
    (η : ℝ) (hη : 0 < η) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ᶠ n in atTop,
      ∀ F : Fin k → ZMod (M n : ℕ) → ℝ,
        (∀ j x, |F j x| ≤ ν n x + 2) →
        (∃ j, |GreenTao.cubeAvg (k - 1) (F j)| ≤ ρ) →
        |GreenTao.mixedAPAvg k F| ≤ η := by
  classical
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hd : 2 ≤ d := by omega
  let c : ℝ := 1 / 3
  have hc : 0 < c := by norm_num [c]
  let μ : Family M := fun n x => (1 - (2 / 3 : ℝ)) * ν n x + 2 / 3
  have hμ (n x) : 0 ≤ μ n x := by
    have hn := hν.1 n x
    dsimp [μ]
    positivity
  have hLF : LinearFormsCondition M μ ((d + 1) * 2 ^ d) (3 * (d + 1) - 4) (d + 1) :=
    linear_forms_convex_mixture M ν _ _ _ (by simpa using hν.2.2.1)
      (2 / 3) (by norm_num) (by norm_num)
  let ζ : ℝ := η * c ^ (d + 1)
  have hζ : 0 < ζ := mul_pos hη (pow_pos hc _)
  let ρ : ℝ := (ζ ^ (2 ^ d) / 4) / c ^ (2 ^ d)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hall : ∀ᶠ n in atTop, ∀ j : Fin (d + 1),
      ∀ F : Fin (d + 1) → ZMod (M n : ℕ) → ℝ,
        (∀ i x, |F i x| ≤ μ n x) → |cubeAvg d (F j)| ≤ ζ ^ (2 ^ d) / 4 →
        |mixedAPAvg (d + 1) F| ≤ ζ :=
    Filter.eventually_all.2 fun j => count_fixed_slot_vn d hd M hprime hM μ hμ hLF j ζ hζ
  refine ⟨ρ, hρ, ?_⟩
  filter_upwards [hall] with n hn
  intro F hF hcube
  obtain ⟨j, hj⟩ := hcube
  let F' : Fin (d + 1) → ZMod (M n : ℕ) → ℝ := fun i x => c * F i x
  have hF' (i x) : |F' i x| ≤ μ n x := by
    dsimp [F']
    rw [abs_mul, abs_of_pos hc]
    dsimp [c, μ]
    linarith [hF i x]
  have hcube' : |cubeAvg d (F' j)| ≤ ζ ^ (2 ^ d) / 4 := by
    change |cubeAvg d (fun x => c * F j x)| ≤ _
    rw [cube_scale_vn, abs_mul, abs_of_pos (pow_pos hc _)]
    have hh := mul_le_mul_of_nonneg_left (by simpa using hj : |cubeAvg d (F j)| ≤ ρ)
      (pow_pos hc (2 ^ d)).le
    have heq : c ^ (2 ^ d) * ρ = ζ ^ (2 ^ d) / 4 := by
      dsimp [ρ]
      field_simp
    exact hh.trans_eq heq
  have h := hn j F' hF' hcube'
  change |mixedAPAvg (d + 1) (fun i x => c * F i x)| ≤ ζ at h
  rw [mixed_scale_vn, abs_mul, abs_of_pos (pow_pos hc _)] at h
  exact le_of_mul_le_mul_left (by simpa [ζ, mul_comm] using h) (pow_pos hc (d + 1))
