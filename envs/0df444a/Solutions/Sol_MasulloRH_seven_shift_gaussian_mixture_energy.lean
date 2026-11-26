-- Prove2me | solution 1 for MasulloRH.seven_shift_gaussian_mixture_energy
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T20:18:56.621693+00:00
-- url     : https://prove2.me/submissions/07bbeb4d-c26a-446a-9590-e786e49203ff

import Theorems.Thm_MasulloRH_exponential_window_gaussian_mixture_gram_bound
import Theorems.Thm_MasulloRH_central_interval_arithmetic_sound
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith

open MeasureTheory Real MasulloRH MasulloRH.GaussianApproximation MasulloRH.GaussianMixture
open MasulloRH.CentralInterval

private def ratioBox (p q : ℚ) : Box :=
  if p=1 ∧ q=1 then (3989/10000,3990/10000)
  else if p=3 ∧ q=3 then (1329/10000,1330/10000)
  else (1784/10000,1785/10000)

private theorem ratio_ok (p q : ℚ) (hp : p=1 ∨ p=3) (hq : q=1 ∨ q=3) :
    Covers (ratioBox p q) (ratio ((p:ℝ)^2+(q:ℝ)^2)) := by
  have pl := mul_nonneg pi_pos.le (sub_nonneg.mpr pi_gt_d4.le)
  have pu := mul_nonneg pi_pos.le (sub_nonneg.mpr pi_lt_d4.le)
  rcases hp with rfl|rfl <;> rcases hq with rfl|rfl <;> norm_num [Covers,ratioBox,ratio,-Real.sqrt_div] <;> constructor
  all_goals rw [←Real.sqrt_div pi_pos.le]
  all_goals first
    | apply (le_div_iff₀ pi_pos).2
      apply (sq_le_sq₀ (by positivity) (sqrt_nonneg _)).1
      rw [sq_sqrt (by positivity)]
      nlinarith only [pl,pu,pi_pos]
    | apply (div_le_iff₀ pi_pos).2
      apply (sq_le_sq₀ (sqrt_nonneg _) (by positivity)).1
      rw [sq_sqrt (by positivity)]
      nlinarith only [pl,pu,pi_pos]

private def atomBox (p q y z t : ℚ) : Box :=
  mulB (mulB (point (p*q)) (ratioBox p q)) (expB (point (exponent p q y z t)))

private theorem atom_ok (p q y z t : ℚ) (hp : p=1 ∨ p=3) (hq : q=1 ∨ q=3) :
    Covers (atomBox p q y z t) (kernel (p:ℝ) q y z t) := by
  let S := MasulloRH.central_interval_arithmetic_sound
  have cast : ((exponent p q y z t : ℚ) : ℝ) = exponent (p:ℝ) q y z t := by
    unfold exponent;push_cast;rfl
  unfold atomBox kernel
  apply S.mul_ok
  · apply S.mul_ok _ (ratio_ok p q hp hq)
    simpa only [Rat.cast_mul] using S.point_ok (p*q)
  · exact S.exp_ok (cast ▸ S.point_ok (exponent p q y z t))

private def matrixBox (i j : Fin 8) : Box :=
  let box t := atomBox (scale8 i) (scale8 j) (shift8 i) (shift8 j) t
  mulB (point (weight8 i*weight8 j)) (box 2 + mulB (point (1/4)) (box 0))

private noncomputable def matrixEntry (i j : Fin 8) : ℝ :=
  let atom (t : ℝ) := kernel (scale8 i) (scale8 j) (shift8 i) (shift8 j) t
  (weight8 i : ℝ)*weight8 j*(atom 2+(1/4)*atom 0)

private theorem width_cases (i : Fin 8) : scale8 i=1 ∨ scale8 i=3 :=
  Fin.cases (Or.inl rfl) (fun _ => Or.inr rfl) i

private theorem matrix_ok (i j : Fin 8) : Covers (matrixBox i j) (matrixEntry i j) := by
  let S := MasulloRH.central_interval_arithmetic_sound
  have a (t : ℚ) := atom_ok (scale8 i) (scale8 j) (shift8 i) (shift8 j) t (width_cases i) (width_cases j)
  apply S.mul_ok
  · simpa only [Rat.cast_mul] using S.point_ok (weight8 i*weight8 j)
  · apply S.add_ok
    · simpa only [Rat.cast_ofNat] using a 2
    · apply S.mul_ok
      · simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using S.point_ok (1/4)
      · simpa only [Rat.cast_zero] using a 0

private def momentBox (i : Fin 7) : Box :=
  mulB (point (amplitude i)) (expB (point (2*max 0 (offset i))))

private theorem moment_ok (i : Fin 7) :
    Covers (momentBox i) ((amplitude i : ℝ)*exp (2*max 0 (offset i : ℝ))) := by
  let S := MasulloRH.central_interval_arithmetic_sound
  apply S.mul_ok (S.point_ok _)
  apply S.exp_ok
  simpa only [Rat.cast_mul,Rat.cast_ofNat,Rat.cast_max,Rat.cast_zero] using S.point_ok (2*max 0 (offset i))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
private theorem gram_upper : (∑ i, ∑ j, matrixBox i j).2 < (1/250 : ℚ) := by decide +kernel

set_option maxRecDepth 12000 in
private theorem moment_upper :
    (mulB (∑ i, point (amplitude i)) (∑ i, momentBox i)).2 < (5/2 : ℚ) := by decide +kernel

/-- The seven rational translates of the scale-three bell approximate the unit bell
in weighted squared energy, with a certified exponential moment for their shifts. -/
theorem solution (c b : ℝ) (hl : 1/2 ≤ c-b) (hr : c+b ≤ 1) :
    Integrable (fun x : ℝ => exp (2*c*x+2*b*|x|)*‖difference x‖^2) ∧
    energy c b difference < 1/250 ∧
    (∑ i : Fin 7, (amplitude i : ℝ))*(∑ i : Fin 7, (amplitude i : ℝ)*exp (2*max 0 (offset i : ℝ))) < 5/2 := by
  let S := MasulloRH.central_interval_arithmetic_sound
  have hp (i : Fin 8) : 0 < (scale8 i : ℝ) := by rcases width_cases i with h|h <;> rw [h] <;> norm_num
  have G := MasulloRH.exponential_window_gaussian_mixture_gram_bound
    (fun i => (weight8 i : ℝ)) (fun i => (scale8 i : ℝ)) (fun i => (shift8 i : ℝ)) hp c b hl hr
  let f := fun x : ℝ => ((∑ i : Fin 8, (weight8 i : ℝ)*bell (scale8 i) (shift8 i) x : ℝ) : ℂ)
  have repr : f=difference := by
    funext x
    dsimp only [f]
    rw [Fin.sum_univ_succ]
    simp only [weight8,scale8,shift8,Fin.cons_zero,Fin.cons_succ,Rat.cast_one,Rat.cast_zero,
      Rat.cast_ofNat,Rat.cast_neg,one_mul,neg_mul,Finset.sum_neg_distrib,sub_eq_add_neg,difference]
  change Integrable (fun x : ℝ => exp (2*c*x+2*b*|x|)*‖f x‖^2) ∧ energy c b f ≤ ∑ i, ∑ j, matrixEntry i j at G
  rw [repr] at G
  have gbox := S.sum_ok (fun i => ∑ j, matrixBox i j) (fun i => ∑ j, matrixEntry i j)
    (fun i => S.sum_ok _ _ (matrix_ok i))
  have mbox := S.mul_ok (S.sum_ok _ _ (fun i : Fin 7 => S.point_ok (amplitude i))) (S.sum_ok _ _ moment_ok)
  have lift {a b : ℚ} (h : a<b) : (a:ℝ)<(b:ℝ) := by exact_mod_cast h
  refine ⟨G.1,G.2.trans_lt (gbox.2.trans_lt ?_),mbox.2.trans_lt ?_⟩
  · simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using lift gram_upper
  · simpa only [Rat.cast_div,Rat.cast_ofNat] using lift moment_upper
