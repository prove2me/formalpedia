-- Prove2me | solution 1 for HighResODE.NAGC.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-28T03:43:48.87303+00:00
-- url     : https://prove2.me/submissions/4d5b57e3-0abb-49aa-8379-876f97f3e96e

import Mathlib
import Definitions.Def_HighResODE_NAGC_Setting


noncomputable section
namespace HighResODE.NAGC.NCFresh
open scoped InnerProductSpace

def weightT (k : ℕ) : ℝ := ((k : ℝ) + 2) / 2
def weightA (k : ℕ) : ℝ := ((k : ℝ) + 1) ^ 2 / 4
def estimateZ {n : ℕ} (x y : ℕ → HighResODE.NAGSC.E n) (k : ℕ) :=
  weightT k • x k - (weightT k - 1) • y k
def estimateEnergy {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (s : ℝ)
    (xs : HighResODE.NAGSC.E n) (x y : ℕ → HighResODE.NAGSC.E n) (k : ℕ) : ℝ :=
  s * weightA k * (f (y k) - f xs) + ‖estimateZ x y k - xs‖ ^ 2 / 2

end HighResODE.NAGC.NCFresh


namespace HighResODE.NAGC.NCFresh

theorem scalar_descent (f f' : ℝ → ℝ) (L : ℝ) (hd : ∀ z, HasDerivAt f (f' z) z)
    (hL : ∀ a b, |f' a-f' b| ≤ L*|a-b|) (a b : ℝ) :
    f b ≤ f a + f' a*(b-a) + L/2*(b-a)^2 := by
  let q : ℝ → ℝ := fun z => f z - f a - f' a*(z-a) - L/2*(z-a)^2
  have hq (z : ℝ) : HasDerivAt q (f' z-f' a-L*(z-a)) z := by
    have h := (((hd z).sub_const (f a)).sub (((hasDerivAt_id z).sub_const a).const_mul (f' a))).sub
      ((((hasDerivAt_id z).sub_const a).pow 2).const_mul (L/2)) 
    exact h.congr_deriv (by simp only [id_eq]; ring)
  have hc : Continuous q := continuous_iff_continuousAt.mpr fun z => (hq z).continuousAt
  have hdiff : Differentiable ℝ q := fun z => (hq z).differentiableAt
  have hqa : q a = 0 := by simp [q]
  rcases le_total a b with hab | hba
  · have hm : AntitoneOn q (Set.Ici a) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici a) hc.continuousOn hdiff.differentiableOn
      intro z hz
      rw [(hq z).deriv]
      have haz : a ≤ z := (interior_subset hz)
      have h := (abs_le.mp (hL z a)).2
      rw [abs_of_nonneg (sub_nonneg.mpr haz)] at h
      linarith
    have h := hm (by simp) hab hab
    rw [hqa] at h
    dsimp [q] at h
    linarith
  · have hm : MonotoneOn q (Set.Iic a) := by
      apply monotoneOn_of_deriv_nonneg (convex_Iic a) hc.continuousOn hdiff.differentiableOn
      intro z hz
      rw [(hq z).deriv]
      have hza : z ≤ a := (interior_subset (s := Set.Iic a) hz)
      have h := (abs_le.mp (hL z a)).1
      rw [abs_of_nonpos (sub_nonpos.mpr hza)] at h
      linarith
    have h := hm hba (by simp) hba
    rw [hqa] at h
    dsimp [q] at h
    linarith

end HighResODE.NAGC.NCFresh


open scoped RealInnerProductSpace
namespace HighResODE.NAGC.NCFresh
variable {p : ℕ}
lemma smooth_descent (f : EuclideanSpace ℝ (Fin p) → ℝ) (L : ℝ)
    (hf : Differentiable ℝ f)
    (hL : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x-y‖)
    (x y : EuclideanSpace ℝ (Fin p)) :
    f y ≤ f x + inner ℝ (gradient f x) (y-x) + L/2*‖y-x‖^2 := by
  let d := y-x
  let g : ℝ → ℝ := fun t => f (x+t • d)
  let g' : ℝ → ℝ := fun t => inner ℝ (gradient f (x+t • d)) d
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => x+s • d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add x
  have hg (t : ℝ) : HasDerivAt g (g' t) t := by
    exact ((hf _).hasGradientAt.hasFDerivAt.comp_hasDerivAt t (hd t))
  have hl (s t : ℝ) : |g' s - g' t| ≤ (L*‖d‖^2)*|s-t| := by
    dsimp [g']
    rw [← inner_sub_left]
    calc
      |inner ℝ (gradient f (x+s • d)-gradient f (x+t • d)) d| ≤
          ‖gradient f (x+s • d)-gradient f (x+t • d)‖*‖d‖ := abs_real_inner_le_norm _ _
      _ ≤ (L*‖(x+s • d)-(x+t • d)‖)*‖d‖ := mul_le_mul_of_nonneg_right (hL _ _) (norm_nonneg _)
      _ = (L*‖d‖^2)*|s-t| := by
        rw [show (x+s • d)-(x+t • d) = (s-t) • d by module]
        rw [norm_smul, Real.norm_eq_abs]
        ring
  have h := scalar_descent g g' (L*‖d‖^2) hg hl 0 1
  simp only [g, g', zero_smul, add_zero, one_smul, sub_zero, one_pow, mul_one] at h
  have he : x + (y-x) = y := by abel
  dsimp [d] at h
  rw [he] at h
  nlinarith [h]
end HighResODE.NAGC.NCFresh


namespace HighResODE.NAGC.NCFresh
open HighResODE.NAGSC
variable {n : ℕ} {f : E n → ℝ} {L : ℝ}
lemma gradient_min_zero (hf : IsF1 f L) (xs : E n) (hm : ∀ z, f xs ≤ f z) :
    gradient f xs = 0 := by
  have hl : IsLocalMin f xs := Filter.Eventually.of_forall hm
  apply (InnerProductSpace.toDual ℝ _).injective
  rw [← (hf.differentiable xs).hasGradientAt.hasFDerivAt.fderiv,
    hl.fderiv_eq_zero, map_zero]
lemma gap_upper (hf : IsF1 f L) (xs : E n) (hm : ∀ z, f xs ≤ f z) (x : E n) :
    f x-f xs ≤ L/2*‖x-xs‖^2 := by
  have h := smooth_descent f L hf.differentiable hf.lipschitz_gradient xs x
  rw [gradient_min_zero hf xs hm, inner_zero_left, add_zero] at h
  linarith
lemma descent_step (hf : IsF1 f L) (x : E n) {s : ℝ} (hs : 0 ≤ s) (hLs : L*s ≤ 1) :
    f (x-s • gradient f x) ≤ f x-s/2*‖gradient f x‖^2 := by
  have h := smooth_descent f L hf.differentiable hf.lipschitz_gradient x (x-s • gradient f x)
  rw [show x-s • gradient f x-x = -s • gradient f x by module] at h
  simp only [real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, neg_sq] at h
  nlinarith [sq_nonneg ‖gradient f x‖, mul_nonneg hs (sub_nonneg.mpr hLs)]
lemma gradient_gap (hf : IsF1 f L) (xs : E n) (hm : ∀ z, f xs ≤ f z) (x : E n) :
    ‖gradient f x‖^2 ≤ 2*L*(f x-f xs) := by
  have hL := hf.L_pos
  have h := descent_step hf x (s := 1/L) (by positivity) (by rw [mul_one_div_cancel hL.ne'])
  have hm' := hm (x-(1/L) • gradient f x)
  have he : (1/L)/2 = 1/(2*L) := by ring
  rw [he, one_div_mul_eq_div] at h
  have hh : ‖gradient f x‖^2/(2*L) ≤ f x-f xs := by linarith
  simpa only [mul_comm] using (div_le_iff₀ (by positivity : 0 < 2*L)).mp hh
lemma gap_compare (hf : IsF1 f L) (xs : E n) (hm : ∀ z, f xs ≤ f z) (x y : E n) :
    f x-f xs ≤ 2*(f y-f xs)+L*‖x-y‖^2 := by
  have h := smooth_descent f L hf.differentiable hf.lipschitz_gradient y x
  have hi := real_inner_le_norm (gradient f y) (x-y)
  have hg := gradient_gap hf xs hm y
  have hs := sq_nonneg (‖gradient f y‖-L*‖x-y‖)
  have hL := hf.L_pos
  nlinarith
end HighResODE.NAGC.NCFresh



noncomputable section
namespace HighResODE.NAGC.NCFresh
open scoped InnerProductSpace

lemma estimateZ_zero {n : ℕ} {f : HighResODE.NAGSC.E n → ℝ} {s : ℝ}
    {x y : ℕ → HighResODE.NAGSC.E n} (_hr : IsNAGC f s x y) :
    estimateZ x y 0 = x 0 := by
  simp [estimateZ, weightT]

lemma estimateZ_step {n : ℕ} {f : HighResODE.NAGSC.E n → ℝ} {s : ℝ}
    {x y : ℕ → HighResODE.NAGSC.E n} (hr : IsNAGC f s x y) (k : ℕ) :
    estimateZ x y (k+1) = estimateZ x y k - (s * weightT k) • gradient f (x k) := by
  have hm : weightT (k+1) * ((k : ℝ) / ((k : ℝ)+3)) = weightT k - 1 := by
    dsimp [weightT]
    push_cast
    field_simp
    ring
  rw [estimateZ, hr.step_x, smul_add, smul_smul, hm, hr.step_y]
  simp only [estimateZ]
  module

lemma y_scaled {n : ℕ} {f : HighResODE.NAGSC.E n → ℝ} {s : ℝ}
    {x y : ℕ → HighResODE.NAGSC.E n} (hr : IsNAGC f s x y)
    (xs : HighResODE.NAGSC.E n) (k : ℕ) :
    weightT k • (y (k+1)-xs) = (estimateZ x y (k+1)-xs) +
      (weightT k-1) • (y k-xs) := by
  rw [estimateZ_step hr, hr.step_y]
  simp only [estimateZ]
  module

lemma x_scaled {n : ℕ} (x y : ℕ → HighResODE.NAGSC.E n) (k : ℕ) :
    weightT k • (x k-y k) = estimateZ x y k-y k := by
  simp only [estimateZ]
  module

lemma convex_pair_identity {n : ℕ} (x y : ℕ → HighResODE.NAGSC.E n)
    (xs : HighResODE.NAGSC.E n) (k : ℕ) :
    (weightT k-1) • (y k-x k) + (xs-x k) = -(estimateZ x y k-xs) := by
  simp only [estimateZ]
  module

end HighResODE.NAGC.NCFresh



noncomputable section
open scoped BigOperators
namespace HighResODE.NAGC.NCFresh

lemma weightT_ge_one (k : ℕ) : 1 ≤ weightT k := by
  dsimp [weightT]
  have := Nat.cast_nonneg (α := ℝ) k
  linarith

lemma weightT_pos (k : ℕ) : 0 < weightT k := lt_of_lt_of_le zero_lt_one (weightT_ge_one k)

lemma weightA_pos (k : ℕ) : 0 < weightA k := by
  unfold weightA
  positivity

lemma weightA_next (k : ℕ) : weightA (k+1) = weightT k ^ 2 := by
  simp only [weightA, weightT, Nat.cast_add, Nat.cast_one]
  ring

lemma weight_difference (k : ℕ) : weightT k ^ 2 - weightT k = weightA k - 1/4 := by
  unfold weightT weightA
  ring

lemma weight_sum_lower (N : ℕ) : (N : ℝ)^3 / 12 ≤ ∑ i ∈ Finset.range N, weightT i ^ 2 := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    have hN := Nat.cast_nonneg (α := ℝ) N
    dsimp [weightT] at *
    nlinarith

end HighResODE.NAGC.NCFresh



noncomputable section
open scoped RealInnerProductSpace
namespace HighResODE.NAGC.NCFresh
open HighResODE.NAGSC
variable {n : ℕ} {f : E n → ℝ} {L s : ℝ} {x y : ℕ → E n}

lemma step_size (hf : IsF1 f L) (hsL : s ≤ 1/(3*L)) : L*s ≤ 1/3 := by
  have hLp := hf.L_pos
  have h := (le_div_iff₀ (by positivity : 0 < 3*L)).mp hsL
  nlinarith

lemma weighted_support (hf : IsF1 f L) (xs : E n) (k : ℕ) :
    weightT k ^ 2 * (f (x k)-f xs) ≤
      weightT k * (weightT k-1) * (f (y k)-f xs) +
        weightT k * ⟪gradient f (x k), estimateZ x y k-xs⟫ := by
  have ht := weightT_ge_one k
  have h1 := mul_le_mul_of_nonneg_left (hf.convex (x k) (y k))
    (show 0 ≤ weightT k*(weightT k-1) by positivity)
  have h2 := mul_le_mul_of_nonneg_left (hf.convex (x k) xs) (le_of_lt (weightT_pos k))
  have hi := congrArg (fun v => ⟪gradient f (x k), v⟫) (convex_pair_identity x y xs k)
  simp only [inner_add_right, real_inner_smul_right, inner_neg_right] at hi
  have his := congrArg (fun a : ℝ => weightT k * a) hi
  nlinarith only [h1,h2,his]

lemma estimate_energy_initial (hf : IsF1 f L) (xs : E n) (hmin : ∀ z, f xs ≤ f z)
    (hs : 0 < s) (hsL : s ≤ 1/(3*L)) (hr : IsNAGC f s x y) :
    estimateEnergy f s xs x y 0 ≤ ‖x 0-xs‖ ^ 2 := by
  have hu := gap_upper hf xs hmin (x 0)
  have hL := step_size hf hsL
  have hh := mul_le_mul_of_nonneg_left hu (show 0 ≤ s/4 by positivity)
  have hn := sq_nonneg ‖x 0-xs‖
  have hb := mul_le_mul_of_nonneg_right hL hn
  simp only [estimateEnergy, estimateZ_zero hr, hr.init, weightA, Nat.cast_zero] 
  norm_num
  nlinarith only [hh,hb,hn]

lemma estimate_energy_decrement (hf : IsF1 f L) (xs : E n) (hmin : ∀ z, f xs ≤ f z)
    (hs : 0 < s) (hsL : s ≤ 1/(3*L)) (hr : IsNAGC f s x y) (k : ℕ) :
    estimateEnergy f s xs x y (k+1) ≤ estimateEnergy f s xs x y k -
      s^2/3 * weightT k^2 * ‖gradient f (x k)‖^2 := by
  have hd := smooth_descent f L hf.differentiable hf.lipschitz_gradient (x k) (y (k+1))
  rw [hr.step_y, show x k-s • gradient f (x k)-x k = -s • gradient f (x k) by module] at hd
  simp only [real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, neg_sq] at hd
  rw [← hr.step_y k] at hd
  have hds := mul_le_mul_of_nonneg_left hd (show 0 ≤ s*weightT k^2 by positivity)
  have hc := mul_le_mul_of_nonneg_left (weighted_support (x := x) (y := y) hf xs k) hs.le
  have hz : ‖estimateZ x y (k+1)-xs‖^2 = ‖estimateZ x y k-xs‖^2 -
      2*s*weightT k*⟪gradient f (x k),estimateZ x y k-xs⟫ +
      s^2*weightT k^2*‖gradient f (x k)‖^2 := by
    rw [estimateZ_step hr]
    rw [show estimateZ x y k-(s*weightT k) • gradient f (x k)-xs =
      (estimateZ x y k-xs)-(s*weightT k) • gradient f (x k) by module]
    rw [norm_sub_sq_real]
    simp only [real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [real_inner_comm (estimateZ x y k-xs) (gradient f (x k))]
    ring
  have hcoef := weight_difference k
  have hf0 := hmin (y k)
  have hnon : 0 ≤ s/4*(f (y k)-f xs) := mul_nonneg (by positivity) (sub_nonneg.mpr hf0)
  have hbound := mul_le_mul_of_nonneg_right (step_size hf hsL)
    (show 0 ≤ s^2*weightT k^2*‖gradient f (x k)‖^2 by positivity)
  have ha : weightA k = weightT k^2-weightT k+1/4 := by linarith
  simp only [estimateEnergy, weightA_next, ha]
  nlinarith only [hds,hc,hz,hnon,hbound]

end HighResODE.NAGC.NCFresh



noncomputable section
open scoped BigOperators
namespace HighResODE.NAGC.NCFresh

lemma energy_telescope (E g : ℕ → ℝ) (s : ℝ)
    (hr : ∀ k, E (k+1) ≤ E k - s^2/3 * (weightT k)^2 * g k) (N : ℕ) :
    E N + s^2/3 * (∑ i ∈ Finset.range N, (weightT i)^2 * g i) ≤ E 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have h := hr N
    nlinarith

lemma energy_le_initial (E g : ℕ → ℝ) (s : ℝ) (hg : ∀ i, 0 ≤ g i)
    (hr : ∀ k, E (k+1) ≤ E k - s^2/3 * (weightT k)^2 * g k) (N : ℕ) :
    E N ≤ E 0 := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have hnon : 0 ≤ s^2/3 * (weightT N)^2 * g N :=
      mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (hg N)
    exact (hr N).trans (by linarith)

lemma weighted_gradient_budget (E g : ℕ → ℝ) {s R : ℝ} (hs : 0 < s)
    (hE : ∀ k, 0 ≤ E k) (hinit : E 0 ≤ R^2)
    (hr : ∀ k, E (k+1) ≤ E k - s^2/3 * (weightT k)^2 * g k) (N : ℕ) :
    (∑ i ∈ Finset.range N, (weightT i)^2 * g i) ≤ 3*R^2/s^2 := by
  have h := energy_telescope E g s hr N
  have hn := hE N
  apply (le_div_iff₀ (sq_pos_of_pos hs)).mpr
  nlinarith

lemma gradient_min_bound (g : ℕ → ℝ) {s R : ℝ} (hs : 0 < s)
    (hg : ∀ i, 0 ≤ g i)
    (hb : ∀ N, (∑ i ∈ Finset.range N, (weightT i)^2*g i) ≤ 3*R^2/s^2)
    (k : ℕ) :
    (Finset.range (k+1)).inf' Finset.nonempty_range_add_one g ≤
      8568*R^2/(s^2*((k:ℝ)+1)^3) := by
  let m := (Finset.range (k+1)).inf' Finset.nonempty_range_add_one g
  have hm : 0 ≤ m := Finset.le_inf' Finset.nonempty_range_add_one g (fun i _ => hg i)
  have hi : ∀ i ∈ Finset.range (k+1), m ≤ g i := fun i hi => Finset.inf'_le _ hi
  have hw := weight_sum_lower (k+1)
  simp only [Nat.cast_add, Nat.cast_one] at hw
  have hmul := mul_le_mul_of_nonneg_left hw hm
  have hsum : m*(∑ i ∈ Finset.range (k+1), weightT i^2) ≤
      ∑ i ∈ Finset.range (k+1), weightT i^2*g i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i hi' => by nlinarith [mul_le_mul_of_nonneg_left (hi i hi') (sq_nonneg (weightT i))])
  have hbound := hb (k+1)
  have hs2 := sq_pos_of_pos hs
  have hk : 0 < (k:ℝ)+1 := by positivity
  have hclear := (le_div_iff₀ hs2).mp (hmul.trans (hsum.trans hbound))
  apply (le_div_iff₀ (mul_pos hs2 (pow_pos hk 3))).mpr
  dsimp only [m] at *
  nlinarith [sq_nonneg R]

end HighResODE.NAGC.NCFresh



noncomputable section
namespace HighResODE.NAGC.NCFresh

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma propagated_radius (y z : ℕ → V) (xs : V) {R : ℝ}
    (hz : ∀ k, ‖z k-xs‖ ≤ 2*R) (h0 : ‖y 0-xs‖ ≤ 2*R)
    (hu : ∀ k, weightT k • (y (k+1)-xs) =
      (z (k+1)-xs)+(weightT k-1) • (y k-xs)) (k : ℕ) :
    ‖y k-xs‖ ≤ 2*R := by
  induction k with
  | zero => exact h0
  | succ k ih =>
    have ht := weightT_pos k
    have ht1 := weightT_ge_one k
    have he := congrArg norm (hu k)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht] at he
    have ha := norm_add_le (z (k+1)-xs) ((weightT k-1) • (y k-xs))
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht1)] at ha
    have hb := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr ht1)
    have hc := hz (k+1)
    nlinarith

lemma extrapolation_distance (x y z : ℕ → V) (xs : V) {R : ℝ}
    (hz : ∀ k, ‖z k-xs‖ ≤ 2*R) (hy : ∀ k, ‖y k-xs‖ ≤ 2*R)
    (hu : ∀ k, weightT k • (x k-y k) = z k-y k) (k : ℕ) :
    ‖x k-y k‖ ≤ 8*R/((k:ℝ)+1) := by
  have ht := weightT_pos k
  have he := congrArg norm (hu k)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht] at he
  have hd : ‖z k-y k‖ ≤ ‖z k-xs‖+‖y k-xs‖ := by
    calc
      _ = ‖(z k-xs)-(y k-xs)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  have hz' := hz k
  have hy' := hy k
  have hn := norm_nonneg (x k-y k)
  have hk := Nat.cast_nonneg (α := ℝ) k
  apply (le_div_iff₀ (by positivity : 0 < (k:ℝ)+1)).mpr
  dsimp [weightT] at he
  nlinarith

omit [NormedSpace ℝ V] in
lemma energy_radius {F E : ℝ} {z xs : V} {s a R : ℝ}
    (hF : 0 ≤ F) (hs : 0 ≤ s) (ha : 0 ≤ a) (hR : 0 ≤ R)
    (he : E = s*a*F+‖z-xs‖^2/2) (hb : E ≤ R^2) : ‖z-xs‖ ≤ 2*R := by
  have hp : 0 ≤ s*a*F := mul_nonneg (mul_nonneg hs ha) hF
  have hn := norm_nonneg (z-xs)
  nlinarith

omit [NormedSpace ℝ V] in
lemma output_gap_bound {F : V → ℝ} {x y z : ℕ → V} {xs : V} {s L R : ℝ}
    (hs : 0 < s) (hL : 0 < L) (hLs : L*s ≤ 1/3) (hR : 0 ≤ R)
    (hcompare : ∀ u v, F v ≤ 2*F u+L*‖v-u‖^2)
    (henergy : ∀ k, s*weightA k*F (y k)+‖z k-xs‖^2/2 ≤ R^2)
    (hdist : ∀ k, ‖x k-y k‖ ≤ 8*R/((k:ℝ)+1)) (k : ℕ) :
    F (x k) ≤ 119*R^2/(s*((k:ℝ)+1)^2) := by
  have hk : 0 < (k:ℝ)+1 := by positivity
  have hden : 0 < s*((k:ℝ)+1)^2 := mul_pos hs (pow_pos hk 2)
  have hy := henergy k
  have hsq := sq_nonneg ‖z k-xs‖
  have hd := (le_div_iff₀ hk).mp (hdist k)
  have hdn := norm_nonneg (x k-y k)
  have hdsq : ‖x k-y k‖^2*((k:ℝ)+1)^2 ≤ 64*R^2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hd)
      (add_nonneg (show 0 ≤ 8*R by positivity) (mul_nonneg hdn hk.le))
    nlinarith only [hp]
  have hc := mul_le_mul_of_nonneg_right (hcompare (y k) (x k)) hden.le
  have hdL := mul_le_mul_of_nonneg_left hdsq (mul_pos hL hs).le
  have hLR := mul_le_mul_of_nonneg_right hLs (sq_nonneg R)
  apply (le_div_iff₀ hden).mpr
  dsimp [weightA] at hy
  nlinarith

end HighResODE.NAGC.NCFresh



namespace HighResODE.NAGC.NCFresh
open scoped InnerProductSpace

theorem native_theorem_6 {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (L s : ℝ) (hf : HighResODE.NAGSC.IsF1 f L) (xs : HighResODE.NAGSC.E n)
    (hmin : ∀ z : HighResODE.NAGSC.E n, f xs ≤ f z) (hs : 0 < s) (hsL : s ≤ 1 / (3 * L))
    (x y : ℕ → HighResODE.NAGSC.E n) (hrun : IsNAGC f s x y) :
    (∀ k : ℕ, (Finset.range (k + 1)).inf' Finset.nonempty_range_add_one
        (fun i => ‖gradient f (x i)‖ ^ 2)
          ≤ 8568 * ‖x 0 - xs‖ ^ 2 / (s ^ 2 * ((k : ℝ) + 1) ^ 3)) ∧
    (∀ k : ℕ, f (x k) - f xs ≤ 119 * ‖x 0 - xs‖ ^ 2 / (s * ((k : ℝ) + 1) ^ 2)) := by
  let R := ‖x 0-xs‖
  let en := estimateEnergy f s xs x y
  let g := fun k => ‖gradient f (x k)‖^2
  have hR : 0 ≤ R := norm_nonneg _
  have hg : ∀ k, 0 ≤ g k := fun k => sq_nonneg _
  have hnon : ∀ k, 0 ≤ en k := by
    intro k
    have hF := sub_nonneg.mpr (hmin (y k))
    have ha := (weightA_pos k).le
    dsimp [en, estimateEnergy]
    positivity
  have hinit : en 0 ≤ R^2 := estimate_energy_initial hf xs hmin hs hsL hrun
  have hrec : ∀ k, en (k+1) ≤ en k-s^2/3*weightT k^2*g k :=
    estimate_energy_decrement hf xs hmin hs hsL hrun
  have hen : ∀ k, en k ≤ R^2 := fun k =>
    (energy_le_initial en g s hg hrec k).trans hinit
  have hz : ∀ k, ‖estimateZ x y k-xs‖ ≤ 2*R := by
    intro k
    exact energy_radius (F := f (y k)-f xs) (E := en k) (s := s)
      (a := weightA k) (sub_nonneg.mpr (hmin (y k))) hs.le (weightA_pos k).le hR rfl (hen k)
  have hy : ∀ k, ‖y k-xs‖ ≤ 2*R := by
    apply propagated_radius y (estimateZ x y) xs hz
    · rw [hrun.init]
      change R ≤ 2*R
      linarith
    · exact y_scaled hrun xs
  have hd : ∀ k, ‖x k-y k‖ ≤ 8*R/((k:ℝ)+1) :=
    extrapolation_distance x y (estimateZ x y) xs hz hy (x_scaled x y)
  constructor
  · intro k
    exact gradient_min_bound g hs hg (weighted_gradient_budget en g hs hnon hinit hrec) k
  · intro k
    exact output_gap_bound (F := fun u => f u-f xs) (x := x) (y := y)
      (z := estimateZ x y) (xs := xs) hs hf.L_pos (step_size hf hsL) hR
      (fun u v => gap_compare hf xs hmin v u) (fun k => hen k) hd k

end HighResODE.NAGC.NCFresh


namespace HighResODE.NAGC
open scoped InnerProductSpace
theorem theorem_6 {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (L s : ℝ) (hf : HighResODE.NAGSC.IsF1 f L) (xs : HighResODE.NAGSC.E n)
    (hmin : ∀ z : HighResODE.NAGSC.E n, f xs ≤ f z) (hs : 0 < s) (hsL : s ≤ 1 / (3 * L))
    (x y : ℕ → HighResODE.NAGSC.E n) (hrun : IsNAGC f s x y) :
    (∀ k : ℕ, (Finset.range (k + 1)).inf' Finset.nonempty_range_add_one
        (fun i => ‖gradient f (x i)‖ ^ 2)
          ≤ 8568 * ‖x 0 - xs‖ ^ 2 / (s ^ 2 * ((k : ℝ) + 1) ^ 3)) ∧
    (∀ k : ℕ, f (x k) - f xs ≤ 119 * ‖x 0 - xs‖ ^ 2 / (s * ((k : ℝ) + 1) ^ 2)) := by
  exact NCFresh.native_theorem_6 f L s hf xs hmin hs hsL x y hrun
end HighResODE.NAGC


open HighResODE.NAGC
open scoped InnerProductSpace
theorem solution {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (L s : ℝ) (hf : HighResODE.NAGSC.IsF1 f L) (xs : HighResODE.NAGSC.E n)
    (hmin : ∀ z : HighResODE.NAGSC.E n, f xs ≤ f z) (hs : 0 < s) (hsL : s ≤ 1 / (3 * L))
    (x y : ℕ → HighResODE.NAGSC.E n) (hrun : IsNAGC f s x y) :
    (∀ k : ℕ, (Finset.range (k + 1)).inf' Finset.nonempty_range_add_one
        (fun i => ‖gradient f (x i)‖ ^ 2)
          ≤ 8568 * ‖x 0 - xs‖ ^ 2 / (s ^ 2 * ((k : ℝ) + 1) ^ 3)) ∧
    (∀ k : ℕ, f (x k) - f xs ≤ 119 * ‖x 0 - xs‖ ^ 2 / (s * ((k : ℝ) + 1) ^ 2)) := by
  exact HighResODE.NAGC.theorem_6 f L s hf xs hmin hs hsL x y hrun
