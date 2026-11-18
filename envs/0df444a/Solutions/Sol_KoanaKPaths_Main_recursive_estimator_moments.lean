-- Prove2me | solution 1 for KoanaKPaths.Main.recursive_estimator_moments
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:29:14.995625+00:00
-- url     : https://prove2.me/submissions/461a7942-9f5b-4001-a112-32da1497ff66

import Theorems.Thm_KoanaKPaths_Main_determinant_tensor_moments
import Theorems.Thm_KoanaKPaths_Main_recursive_sketch_step_moments

open scoped BigOperators Classical
namespace KoanaKPaths.Main.RecursiveMoments

lemma mean_const {Ω : Type} [Fintype Ω] [Nonempty Ω] (a : ℝ) :
    uniformMean (fun _ : Ω => a) = a := by simp [uniformMean]

lemma mean_div {Ω : Type} [Fintype Ω] (f : Ω → ℝ) (a : ℝ) :
    uniformMean (fun w => f w / a) = uniformMean f / a := by
  simp only [uniformMean, ← Finset.sum_div]
  ring

lemma mean_prod {Ω A : Type} [Fintype Ω] [Fintype A] (f : Ω × A → ℝ) :
    uniformMean f = uniformMean (fun w : Ω => uniformMean (fun a : A => f (w,a))) := by
  simp only [uniformMean,Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul,← Finset.sum_div]
  ring

end KoanaKPaths.Main.RecursiveMoments

open KoanaKPaths.Main
open KoanaKPaths.Main.RecursiveMoments

theorem solution (n k ℓ : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hℓ : 1 ≤ ℓ)
    (c : (Fin k → Fin n) → ℤ) (hc : IsZeroOneTensor c) :
    (∀ i ≤ k,
      uniformMean (fun ω : Labels n k × SketchSigns n k ℓ => Yhat c i ω.1 ω.2) = (tensorN c : ℝ) ∧
      uniformMean (fun ω : Labels n k × SketchSigns n k ℓ => (Yhat c i ω.1 ω.2) ^ 2) ≤
        (1 + 2 / (ℓ : ℝ)) ^ i * (k : ℝ) ^ 3 * (tensorN c : ℝ) ^ 2) ∧
    (ℓ = k →
      uniformMean (fun ω : Labels n k × SketchSigns n k ℓ => Yhat c k ω.1 ω.2) = (tensorN c : ℝ) ∧
      uniformMean (fun ω : Labels n k × SketchSigns n k ℓ => (Yhat c k ω.1 ω.2) ^ 2) ≤
        Real.exp 2 * (k : ℝ) ^ 3 * (tensorN c : ℝ) ^ 2) := by
  have hlpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hlne : (ℓ : ℝ) ≠ 0 := hlpos.ne'
  have hfpos : (0 : ℝ) < Nat.factorial k := by exact_mod_cast Nat.factorial_pos k
  have hfne : (Nat.factorial k : ℝ) ≠ 0 := hfpos.ne'
  let F (i : ℕ) (w : Labels n k × SketchSigns n k ℓ) : ℝ := (sketchFrobSq c w.1 w.2 i : ℝ)
  let D (i : ℕ) : ℝ := (ℓ : ℝ)^i * (Nat.factorial k : ℝ)
  have hm (i : ℕ) :
      uniformMean (fun w : Labels n k × SketchSigns n k ℓ => Yhat c i w.1 w.2) =
        uniformMean (F i) / D i := by
    exact mean_div (F i) (D i)
  have hs (i : ℕ) :
      uniformMean (fun w : Labels n k × SketchSigns n k ℓ => Yhat c i w.1 w.2 ^ 2) =
        uniformMean (fun w => F i w ^ 2) / (D i)^2 := by
    simp only [Yhat,div_pow]
    exact mean_div (fun w => F i w ^ 2) ((D i)^2)
  have hbase := determinant_tensor_moments n k hn hk c hc
  have hb1 : uniformMean (F 0) = (Nat.factorial k : ℝ)*(tensorN c : ℝ) := by
    rw [mean_prod]
    simp only [F,sketchFrobSq,mean_const]
    exact hbase.1
  have hb2 : uniformMean (fun w => F 0 w ^ 2) ≤
      (Nat.factorial k : ℝ)^2 * (k : ℝ)^3 * (tensorN c : ℝ)^2 := by
    rw [mean_prod]
    simp only [F,sketchFrobSq,mean_const]
    exact hbase.2
  have hnorm1 (i : ℕ) (hi : i < k) :
      uniformMean (fun w : Labels n k × SketchSigns n k ℓ => Yhat c (i+1) w.1 w.2) =
        uniformMean (fun w : Labels n k × SketchSigns n k ℓ => Yhat c i w.1 w.2) := by
    rw [hm,hm]
    rw [show uniformMean (F (i+1)) = (ℓ : ℝ)*uniformMean (F i) from
      (recursive_sketch_step_moments n k ℓ c i hi).1]
    dsimp [D]
    field_simp [hlne,hfne]
    <;> simp only [pow_succ]
    <;> ring
  have hnorm2 (i : ℕ) (hi : i < k) :
      uniformMean (fun w : Labels n k × SketchSigns n k ℓ => Yhat c (i+1) w.1 w.2 ^ 2) ≤
        (1+2/(ℓ : ℝ)) *
          uniformMean (fun w : Labels n k × SketchSigns n k ℓ => Yhat c i w.1 w.2 ^ 2) := by
    rw [hs,hs]
    calc
      _ ≤ (((ℓ : ℝ)^2+2*ℓ) * uniformMean (fun w => F i w ^ 2)) / (D (i+1))^2 :=
        div_le_div_of_nonneg_right (recursive_sketch_step_moments n k ℓ c i hi).2 (sq_nonneg _)
      _ = _ := by
        dsimp [D]
        field_simp [pow_succ,hlne,hfne]
        <;> ring
  have hall : ∀ i ≤ k,
      uniformMean (fun w : Labels n k × SketchSigns n k ℓ => Yhat c i w.1 w.2) = (tensorN c : ℝ) ∧
      uniformMean (fun w : Labels n k × SketchSigns n k ℓ => Yhat c i w.1 w.2 ^ 2) ≤
        (1+2/(ℓ : ℝ))^i * (k : ℝ)^3 * (tensorN c : ℝ)^2 := by
    intro i hi
    induction i with
    | zero =>
      constructor
      · rw [hm,hb1]
        dsimp [D]
        field_simp
      · rw [hs]
        simp only [D,pow_zero,one_mul]
        apply (div_le_iff₀ (sq_pos_of_pos hfpos)).mpr
        nlinarith [hb2]
    | succ i ih =>
      have hile : i ≤ k := by omega
      have hilt : i < k := by omega
      obtain ⟨h1,h2⟩ := ih hile
      constructor
      · rw [hnorm1 i hilt,h1]
      · calc
          _ ≤ (1+2/(ℓ : ℝ)) * uniformMean (fun w : Labels n k × SketchSigns n k ℓ => Yhat c i w.1 w.2 ^ 2) :=
            hnorm2 i hilt
          _ ≤ (1+2/(ℓ : ℝ)) * ((1+2/(ℓ : ℝ))^i*(k : ℝ)^3*(tensorN c : ℝ)^2) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = _ := by rw [pow_succ]; ring
  refine ⟨hall,?_⟩
  intro heq
  obtain ⟨h1,h2⟩ := hall k le_rfl
  refine ⟨h1,?_⟩
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
  have hex : 1+2/(k : ℝ) ≤ Real.exp (2/(k : ℝ)) := by
    linarith [Real.add_one_le_exp (2/(k : ℝ))]
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1+2/(k : ℝ)) hex k
  rw [← Real.exp_nat_mul] at hp
  have he : (k : ℝ)*(2/(k : ℝ)) = 2 := by field_simp
  rw [he] at hp
  rw [heq] at h2
  rw [heq]
  apply h2.trans
  have hp' := mul_le_mul_of_nonneg_right hp
    (by positivity : (0 : ℝ) ≤ (k : ℝ)^3*(tensorN c : ℝ)^2)
  simpa only [mul_assoc] using hp' 
