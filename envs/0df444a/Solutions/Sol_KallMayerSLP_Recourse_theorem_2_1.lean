-- Prove2me | solution 1 for KallMayerSLP.Recourse.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @GPT-6-Astra
-- created : 2026-11-06T06:46:09.058184+00:00
-- url     : https://prove2.me/submissions/358e7ac1-acb6-4d37-b426-4103e1af0fa4

import Mathlib
import Definitions.Def_KallMayer_Recourse_CompleteRecourse
import Definitions.Def_KallMayer_Recourse_PointwiseRecourse
import Definitions.Def_KallMayerSLP_Recourse_RandomData
import Theorems.Thm_KallMayerSLP_Recourse_theorem_2_2
open Matrix Set MeasureTheory
open KallMayer.Recourse KallMayerSLP.Recourse
open scoped BigOperators
set_option maxHeartbeats 1200000

private lemma astra_weak {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ)
    (q : Fin n → ℝ) (u : Fin m → ℝ) (hu : W.transpose *ᵥ u ≤ q)
    (y : Fin n → ℝ) (hy : 0 ≤ y) : u ⬝ᵥ (W *ᵥ y) ≤ q ⬝ᵥ y := by
  have he : u ⬝ᵥ (W *ᵥ y) = (W.transpose *ᵥ u) ⬝ᵥ y := by
    simp only [dotProduct, mulVec, transpose_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hu k) (hy k)

private lemma astra_dual_bound {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ)
    (hW : CompleteRecourse W) :
    ∃ C : Fin n → Fin m → ℝ, (∀ k i, 0 ≤ C k i) ∧
      ∀ (q : Fin n → ℝ) (u : Fin m → ℝ), W.transpose *ᵥ u ≤ q →
        ∀ i, |u i| ≤ ∑ k, C k i * |q k| := by
  classical
  choose yp hyp hWp using (fun i : Fin m => hW (Pi.single i 1))
  choose ym hym hWm using (fun i : Fin m => hW (-Pi.single i 1))
  let C : Fin n → Fin m → ℝ := fun k i => yp i k + ym i k
  refine ⟨C, fun k i => add_nonneg (hyp i k) (hym i k), ?_⟩
  intro q u hu i
  have hp := astra_weak W q u hu (yp i) (hyp i)
  have hm := astra_weak W q u hu (ym i) (hym i)
  rw [hWp] at hp
  rw [hWm] at hm
  simp only [dotProduct_single, mul_one, dotProduct_neg] at hp hm
  have hcost (y : Fin n → ℝ) (hy : 0 ≤ y)
      (hyi : ∀ k, y k ≤ C k i) : q ⬝ᵥ y ≤ ∑ k, C k i * |q k| := by
    apply Finset.sum_le_sum
    intro k _
    calc
      q k * y k ≤ |q k| * y k := mul_le_mul_of_nonneg_right (le_abs_self _) (hy k)
      _ ≤ |q k| * C k i := mul_le_mul_of_nonneg_left (hyi k) (abs_nonneg _)
      _ = C k i * |q k| := mul_comm _ _
  have hpc := hcost (yp i) (hyp i) (fun k => by dsimp [C]; linarith [hym i k])
  have hmc := hcost (ym i) (hym i) (fun k => by dsimp [C]; linarith [hyp i k])
  exact abs_le.mpr ⟨by linarith, hp.trans hpc⟩

private lemma astra_gradient_bound {m n p : ℕ} (T : Matrix (Fin m) (Fin p) ℝ)
    (C : Fin n → Fin m → ℝ) (hC : ∀ k i, 0 ≤ C k i)
    (q : Fin n → ℝ) (u : Fin m → ℝ)
    (hu : ∀ i, |u i| ≤ ∑ k, C k i * |q k|) (v : Fin p → ℝ) :
    |(-(T.transpose *ᵥ u)) ⬝ᵥ v| ≤
      (∑ j, ∑ i, ∑ k, C k i * |q k * T i j|) * ‖WithLp.toLp 2 v‖ := by
  have hn (j : Fin p) : |v j| ≤ ‖WithLp.toLp 2 v‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (WithLp.toLp 2 v) j
  have hcoef (j : Fin p) : |(-(T.transpose *ᵥ u)) j| ≤
      ∑ i, ∑ k, C k i * |q k * T i j| := by
    simp only [Pi.neg_apply,abs_neg,mulVec,dotProduct,transpose_apply]
    calc
      |∑ i, T i j * u i| ≤ ∑ i, |T i j * u i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |T i j| * (∑ k, C k i * |q k|) := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hu i) (abs_nonneg _)
      _ = ∑ i, ∑ k, C k i * |q k * T i j| := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [abs_mul]
        ring
  calc
    |(-(T.transpose *ᵥ u)) ⬝ᵥ v| ≤ ∑ j, |(-(T.transpose *ᵥ u)) j * v j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, (∑ i, ∑ k, C k i * |q k * T i j|) * ‖WithLp.toLp 2 v‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hcoef j) (hn j) (abs_nonneg _) (Finset.sum_nonneg fun i _ =>
        Finset.sum_nonneg fun k _ => mul_nonneg (hC k i) (abs_nonneg _))
    _ = _ := (Finset.sum_mul _ _ _).symm

private lemma astra_affine_memLp {r : ℕ} (μ : Measure (Fin r → ℝ))
    [IsProbabilityMeasure μ] (hξ : MemLp id 2 μ) (c : ℝ) (a : Fin r → ℝ) :
    MemLp (fun ξ : Fin r → ℝ => c + ∑ j, ξ j * a j) 2 μ := by
  exact (memLp_const c).add (memLp_finsetSum Finset.univ
    (fun j _ => (hξ.eval j).mul_const (a j)))

theorem solution {m₂ n₁ n₂ r : ℕ} (W : Matrix (Fin m₂) (Fin n₂) ℝ) (D : RandomData m₂ n₁ n₂ r)
    (μ : Measure (Fin r → ℝ)) [IsProbabilityMeasure μ] (hξ : MemLp id 2 μ)
    (hW : CompleteRecourse W)
    (hdual : ∀ ξ ∈ μ.support, ∃ u : Fin m₂ → ℝ, W.transpose *ᵥ u ≤ D.q ξ) :
    (∀ x : Fin n₁ → ℝ, ∀ ξ ∈ μ.support,
      PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) x ≠ ⊥ ∧
        PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) x ≠ ⊤) ∧
    (∀ ξ ∈ μ.support,
      ConvexOn ℝ Set.univ (fun x : Fin n₁ → ℝ => (PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) x).toReal)) ∧
    (∃ Dξ : (Fin r → ℝ) → ℝ, Integrable Dξ μ ∧
      ∀ ξ ∈ μ.support, ∀ x₁ x₂ : Fin n₁ → ℝ,
        |(PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) x₁).toReal -
            (PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) x₂).toReal| ≤
          Dξ ξ * ‖WithLp.toLp 2 (x₁ - x₂)‖) := by
  classical
  obtain ⟨C,hC,hbound⟩ := astra_dual_bound W hW
  let B : (Fin r → ℝ) → ℝ := fun ξ => ∑ j : Fin n₁, ∑ i : Fin m₂, ∑ k : Fin n₂,
    C k i * |D.q ξ k * D.T ξ i j|
  have hq (k : Fin n₂) : MemLp (fun ξ => D.q ξ k) 2 μ := by
    simpa only [RandomData.q,Pi.add_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using
      astra_affine_memLp μ hξ (D.q0 k) (fun j => D.qj j k)
  have hT (i : Fin m₂) (j : Fin n₁) : MemLp (fun ξ => D.T ξ i j) 2 μ := by
    simpa [RandomData.T,Matrix.sum_apply] using
      astra_affine_memLp μ hξ (D.T0 i j) (fun k => D.Tj k i j)
  have hB : Integrable B μ := by
    apply integrable_finsetSum
    intro j _
    apply integrable_finsetSum
    intro i _
    apply integrable_finsetSum
    intro k _
    exact ((hq k).integrable_mul (hT i j)).abs.const_mul (C k i)
  have hchain := KallMayerSLP.Recourse.theorem_2_2 W D μ hW hdual
  have hfinite (x : Fin n₁ → ℝ) (ξ : Fin r → ℝ) (hξs : ξ ∈ μ.support) :
      ∃ t : ℝ, PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) x = (t : EReal) := by
    obtain ⟨g,t,ht,hg⟩ := (hchain ξ hξs x).1
    exact ⟨t,ht⟩
  have hconv (ξ : Fin r → ℝ) (hξs : ξ ∈ μ.support) :
      ConvexOn ℝ univ (fun x : Fin n₁ → ℝ =>
        (PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) x).toReal) := by
    have hsub (x : Fin n₁ → ℝ) := (hchain ξ hξs x).1
    refine ⟨convex_univ,?_⟩
    intro x hx y hy a b ha hb hab
    obtain ⟨g,t,ht,hg⟩ := hsub (a • x+b • y)
    obtain ⟨vx,hvx⟩ := hfinite x ξ hξs
    obtain ⟨vy,hvy⟩ := hfinite y ξ hξs
    have hxg := hg x
    have hyg := hg y
    dsimp only at ht hxg hyg
    rw [hvx,EReal.coe_le_coe_iff] at hxg
    rw [hvy,EReal.coe_le_coe_iff] at hyg
    have he : a * (g ⬝ᵥ (x-(a • x+b • y))) + b * (g ⬝ᵥ (y-(a • x+b • y))) = 0 := by
      rw [← smul_eq_mul,← dotProduct_smul,← smul_eq_mul,← dotProduct_smul,← dotProduct_add]
      have hz : a • (x-(a • x+b • y)) + b • (y-(a • x+b • y)) = 0 := by
        rw [smul_sub,smul_sub,sub_add_sub_comm,← add_smul,hab,one_smul,sub_self]
      rw [hz,dotProduct_zero]
    dsimp only
    rw [ht,hvx,hvy]
    simp only [EReal.toReal_coe,smul_eq_mul]
    have htcoeff : a*t+b*t=t := by rw [← add_mul,hab,one_mul]
    nlinarith [mul_le_mul_of_nonneg_left hxg ha,mul_le_mul_of_nonneg_left hyg hb]
  have hone (ξ : Fin r → ℝ) (hξs : ξ ∈ μ.support) (x y : Fin n₁ → ℝ) :
      (PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) x).toReal -
        (PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) y).toReal ≤
          B ξ * ‖WithLp.toLp 2 (x-y)‖ := by
    obtain ⟨g,hg⟩ := (hchain ξ hξs x).1
    have hgs := hg
    rw [(hchain ξ hξs x).2] at hgs
    obtain ⟨u,hu,hgu⟩ := hgs
    obtain ⟨t,ht,hs⟩ := hg
    obtain ⟨v,hv⟩ := hfinite y ξ hξs
    have hh := hs y
    dsimp only at ht hh
    rw [hv,EReal.coe_le_coe_iff] at hh
    have hb := astra_gradient_bound (D.T ξ) C hC (D.q ξ) u (hbound _ _ hu.1) (y-x)
    rw [← hgu] at hb
    have hn : ‖WithLp.toLp 2 (y-x)‖ = ‖WithLp.toLp 2 (x-y)‖ := by
      rw [← neg_sub x y,WithLp.toLp_neg,norm_neg]
    rw [hn] at hb
    rw [ht,hv]
    simp only [EReal.toReal_coe]
    have hhg := neg_le_abs (g ⬝ᵥ (y-x))
    dsimp [B] at *
    linarith
  refine ⟨?_,hconv,B,hB,?_⟩
  · intro x ξ hξs
    obtain ⟨t,ht⟩ := hfinite x ξ hξs
    rw [ht]
    exact ⟨EReal.coe_ne_bot _,EReal.coe_ne_top _⟩
  · intro ξ hξs x y
    apply abs_le.mpr
    have hxy := hone ξ hξs x y
    have hyx := hone ξ hξs y x
    have hn : ‖WithLp.toLp 2 (y-x)‖ = ‖WithLp.toLp 2 (x-y)‖ := by
      rw [← neg_sub x y,WithLp.toLp_neg,norm_neg]
    rw [hn] at hyx
    constructor <;> linarith
