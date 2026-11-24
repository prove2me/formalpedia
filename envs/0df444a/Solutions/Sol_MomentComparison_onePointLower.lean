-- Prove2me | solution 1 for MomentComparison.onePointLower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:09:11.275797+00:00
-- url     : https://prove2.me/submissions/9929757c-01c6-4a67-96a0-3b4f15415d6c

module
public import Definitions.Def_MomentComparison_Lens
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_MomentComparison_TwoPoint
section
public section
open Filter Topology Set
namespace MomentComparison
private theorem U_pos {y : ℝ} (hy : 0 < y) (x : ℝ) : 0 < U y x := by
  unfold U
  positivity
private theorem V_pos {y : ℝ} (hy : 0 < y) (x : ℝ) : 0 < V y x := by
  unfold V
  positivity
private theorem S_pos (s : ℝ) {y : ℝ} (hy : 0 < y) (x : ℝ) : 0 < S s y x :=
  div_pos (add_pos (Real.rpow_pos_of_pos (U_pos hy x) _)
    (Real.rpow_pos_of_pos (V_pos hy x) _)) (by norm_num)
private theorem deriv_U (y x : ℝ) : HasDerivAt (U y) (2 * (1 + x)) x := by
  refine ((((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)).pow 2).add_const y).congr_deriv ?_
  simp only [Pi.add_apply, id_eq]
  norm_num
private theorem deriv_V (y x : ℝ) : HasDerivAt (V y) (-2 * (1 - x)) x := by
  refine ((((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).pow 2).add_const y).congr_deriv ?_
  simp only [Pi.sub_apply, id_eq]
  norm_num
private theorem deriv_S (s x : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (S s y) (S₁ s y x) x := by
  have hU := (deriv_U y x).rpow_const (p := s) (Or.inl (U_pos hy x).ne')
  have hV := (deriv_V y x).rpow_const (p := s) (Or.inl (V_pos hy x).ne')
  refine ((hU.add hV).div_const 2).congr_deriv ?_
  unfold S₁
  ring
private theorem deriv_S₁ (s x : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (S₁ s y) (S₂ s y x) x := by
  have hU := (deriv_U y x).rpow_const (p := s - 1) (Or.inl (U_pos hy x).ne')
  have hV := (deriv_V y x).rpow_const (p := s - 1) (Or.inl (V_pos hy x).ne')
  have h₁ := hU.mul ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x))
  have h₂ := hV.mul ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x))
  refine ((h₁.sub h₂).const_mul s).congr_deriv ?_
  unfold S₂
  simp only [Pi.add_apply, Pi.sub_apply, id_eq, zero_add, zero_sub]
  rw [show s - 1 - 1 = s - 2 by ring]
  ring
private theorem convexOn_negative_rpow {q : ℝ} (hq : q ≤ 0) :
    ConvexOn ℝ (Set.Ioi 0) fun x : ℝ => x ^ q := by
  apply convexOn_of_deriv2_nonneg (convex_Ioi 0)
  · apply ContinuousOn.rpow_const continuous_id.continuousOn
    intro x hx
    exact Or.inl (Set.mem_Ioi.mp hx).ne'
  · intro x hx
    rw [interior_Ioi] at hx
    exact (Real.hasDerivAt_rpow_const (Or.inl (Set.mem_Ioi.mp hx).ne')).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hx' : 0 < x := hx
    have he : (deriv (fun x : ℝ => x ^ q)) =ᶠ[nhds x] (fun x => q * x ^ (q - 1)) :=
      Filter.eventuallyEq_of_mem (Ioi_mem_nhds hx') fun t ht =>
        (Real.hasDerivAt_rpow_const (Or.inl (Set.mem_Ioi.mp ht).ne')).deriv
    exact (((Real.hasDerivAt_rpow_const (x := x) (p := q - 1)
      (Or.inl hx'.ne')).const_mul q).congr_of_eventuallyEq he).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hx' : 0 < x := hx
    have he : (deriv (fun x : ℝ => x ^ q)) =ᶠ[nhds x] (fun x => q * x ^ (q - 1)) :=
      Filter.eventuallyEq_of_mem (Ioi_mem_nhds hx') fun t ht =>
        (Real.hasDerivAt_rpow_const (Or.inl (Set.mem_Ioi.mp ht).ne')).deriv
    change 0 ≤ deriv (deriv (fun x : ℝ => x ^ q)) x
    rw [he.deriv_eq, ((Real.hasDerivAt_rpow_const
      (x := x) (p := q - 1) (Or.inl hx'.ne')).const_mul q).deriv]
    exact mul_nonneg_of_nonpos_of_nonpos hq
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.rpow_nonneg hx'.le _))
private theorem power_mean_factor (s x : ℝ) {y : ℝ} (hy : 0 < y) (hs : 0 < s) :
    (1 ≤ s → S s y x ^ (s⁻¹ - 1) * ((U y x ^ (s - 1) + V y x ^ (s - 1)) / 2) ≤ 1) ∧
    (s ≤ 1 → 1 ≤ S s y x ^ (s⁻¹ - 1) * ((U y x ^ (s - 1) + V y x ^ (s - 1)) / 2)) := by
  let q := (s - 1) / s
  let u := U y x
  let v := V y x
  have hu : 0 < u := U_pos hy x
  have hv : 0 < v := V_pos hy x
  have hsq : s * q = s - 1 := by dsimp [q]; field_simp
  have hinv : s⁻¹ - 1 = -q := by dsimp [q]; field_simp; ring
  have hU : (u ^ s) ^ q = u ^ (s - 1) := by rw [← Real.rpow_mul hu.le, hsq]
  have hV : (v ^ s) ^ q = v ^ (s - 1) := by rw [← Real.rpow_mul hv.le, hsq]
  have hS : S s y x ^ (s⁻¹ - 1) * S s y x ^ q = 1 := by
    rw [hinv, ← Real.rpow_add (S_pos s hy x), neg_add_cancel, Real.rpow_zero]
  constructor
  · intro h
    have hconc := Real.concaveOn_rpow (p := q)
      (div_nonneg (by linarith) hs.le) ((div_le_iff₀ hs).mpr (by linarith))
    obtain ⟨_, hconc⟩ := hconc
    have hj := hconc (x := u ^ s) (y := v ^ s)
      (Real.rpow_nonneg hu.le _) (Real.rpow_nonneg hv.le _)
      (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    simp only [smul_eq_mul, hU, hV] at hj
    have he (l r : ℝ) : 1 / 2 * l + 1 / 2 * r = (l + r) / 2 := by ring
    rw [he, he] at hj
    change ((u ^ (s - 1) + v ^ (s - 1)) / 2) ≤ S s y x ^ q at hj
    simpa only [hS] using mul_le_mul_of_nonneg_left hj
      (Real.rpow_nonneg (S_pos s hy x).le (s⁻¹ - 1))
  · intro h
    have hconv := convexOn_negative_rpow (q := q) (div_nonpos_of_nonpos_of_nonneg (by linarith) hs.le)
    obtain ⟨_, hconv⟩ := hconv
    have hj := hconv (x := u ^ s) (y := v ^ s)
      (Real.rpow_pos_of_pos hu _) (Real.rpow_pos_of_pos hv _)
      (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    simp only [smul_eq_mul, hU, hV] at hj
    have he (l r : ℝ) : 1 / 2 * l + 1 / 2 * r = (l + r) / 2 := by ring
    rw [he, he] at hj
    change S s y x ^ q ≤ ((u ^ (s - 1) + v ^ (s - 1)) / 2) at hj
    simpa only [hS] using mul_le_mul_of_nonneg_left hj
      (Real.rpow_nonneg (S_pos s hy x).le (s⁻¹ - 1))
private theorem deriv_G (s x : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (G s y) (G₁ s y x) x := by
  refine ((deriv_S s x hy).rpow_const (p := s⁻¹) (Or.inl (S_pos s hy x).ne')).congr_deriv ?_
  unfold G₁
  ring
private theorem deriv_G₁ (s x : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (G₁ s y) (G₂ s y x) x := by
  have h := (deriv_S s x hy).rpow_const (p := s⁻¹ - 1) (Or.inl (S_pos s hy x).ne')
  refine ((h.const_mul s⁻¹).mul (deriv_S₁ s x hy)).congr_deriv ?_
  unfold G₂
  rw [show s⁻¹ - 1 - 1 = s⁻¹ - 2 by ring]
  ring
private theorem S₂_bound (s x : ℝ) {y : ℝ} (hy : 0 < y) (hs : 0 < s) :
    let T := s * (2 * s - 1) * (U y x ^ (s - 1) + V y x ^ (s - 1))
    (1 ≤ s → S₂ s y x ≤ T) ∧ (s ≤ 1 → T ≤ S₂ s y x) := by
  intro T
  have hu : (1 + x) ^ 2 ≤ U y x := by unfold U; linarith
  have hv : (1 - x) ^ 2 ≤ V y x := by unfold V; linarith
  have mulU : U y x ^ (s - 2) * U y x = U y x ^ (s - 1) := by
    calc
      _ = U y x ^ (s - 2) * U y x ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add (U_pos hy x)]; congr 1; ring
  have mulV : V y x ^ (s - 2) * V y x = V y x ^ (s - 1) := by
    calc
      _ = V y x ^ (s - 2) * V y x ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add (V_pos hy x)]; congr 1; ring
  have h₁ := mul_le_mul_of_nonneg_left hu (Real.rpow_nonneg (U_pos hy x).le (s - 2))
  have h₂ := mul_le_mul_of_nonneg_left hv (Real.rpow_nonneg (V_pos hy x).le (s - 2))
  rw [mulU] at h₁
  rw [mulV] at h₂
  have h := add_le_add h₁ h₂
  constructor
  · intro hs₁
    have h' := mul_le_mul_of_nonneg_left h
      (show 0 ≤ 2 * s * (s - 1) by positivity)
    dsimp [S₂, T]
    linarith
  · intro hs₁
    have h' := mul_le_mul_of_nonpos_left h
      (show 2 * s * (s - 1) ≤ 0 by
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith))
    dsimp [S₂, T]
    linarith
private theorem G₂_bound (s x : ℝ) {y : ℝ} (hy : 0 < y) (hs : 1 / 2 < s) :
    (1 ≤ s → G₂ s y x ≤ 2 * (2 * s - 1)) ∧
    (s ≤ 1 → 2 * (2 * s - 1) ≤ G₂ s y x) := by
  have hs0 : 0 < s := by linarith
  have hS := S₂_bound s x hy hs0
  have hF := power_mean_factor s x hy hs0
  let a := S s y x ^ (s⁻¹ - 1)
  let b := (U y x ^ (s - 1) + V y x ^ (s - 1)) / 2
  let K := 2 * (2 * s - 1)
  let D := s⁻¹ * a
  have ha : 0 ≤ a := Real.rpow_nonneg (S_pos s hy x).le _
  have hK : 0 ≤ K := by dsimp [K]; linarith
  have hD : 0 ≤ D := by dsimp [D]; exact mul_nonneg (inv_nonneg.mpr hs0.le) ha
  have hlim : D * (s * (2 * s - 1) * (U y x ^ (s - 1) + V y x ^ (s - 1))) =
      K * (a * b) := by
    dsimp [D, K, b]
    rw [show s⁻¹ * a * (s * (2 * s - 1) * (U y x ^ (s - 1) + V y x ^ (s - 1))) =
      (s⁻¹ * s) * ((2 * s - 1) * a * (U y x ^ (s - 1) + V y x ^ (s - 1))) by ring,
      inv_mul_cancel₀ hs0.ne']
    ring
  have hrem : 0 ≤ S s y x ^ (s⁻¹ - 2) * (S₁ s y x) ^ 2 :=
    mul_nonneg (Real.rpow_nonneg (S_pos s hy x).le _) (sq_nonneg _)
  constructor
  · intro hs₁
    have hleft := mul_le_mul_of_nonneg_left (hS.1 hs₁) hD
    rw [hlim] at hleft
    have hright := mul_le_mul_of_nonneg_left (hF.1 hs₁) hK
    have hinv : s⁻¹ - 1 ≤ 0 := sub_nonpos.mpr (inv_le_one_of_one_le₀ hs₁)
    have hlast := mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hs0.le) hinv) hrem
    unfold G₂
    change D * S₂ s y x + _ ≤ K
    change K * (a * b) ≤ K * 1 at hright
    linarith
  · intro hs₁
    have hleft := mul_le_mul_of_nonneg_left (hS.2 hs₁) hD
    rw [hlim] at hleft
    have hright := mul_le_mul_of_nonneg_left (hF.2 hs₁) hK
    have hinv : 0 ≤ s⁻¹ - 1 := sub_nonneg.mpr ((one_le_inv₀ hs0).mpr hs₁)
    have hlast := mul_nonneg (mul_nonneg (inv_nonneg.mpr hs0.le) hinv) hrem
    unfold G₂
    change K ≤ D * S₂ s y x + _
    change K * 1 ≤ K * (a * b) at hright
    linarith
private theorem le_of_second_nonneg {f f' f'' : ℝ → ℝ}
    (h₁ : ∀ x, HasDerivAt f (f' x) x) (h₂ : ∀ x, HasDerivAt f' (f'' x) x)
    (h₂0 : ∀ x ≥ 0, 0 ≤ f'' x) (h₁0 : f' 0 = 0) {x : ℝ} (hx : 0 ≤ x) :
    f 0 ≤ f x := by
  have hm' : MonotoneOn f' (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun z _ => (h₂ z).continuousAt.continuousWithinAt)
      (fun z _ => (h₂ z).differentiableAt.differentiableWithinAt)
    intro z hz
    rw [(h₂ z).deriv]
    exact h₂0 z (interior_subset hz)
  have hm : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun z _ => (h₁ z).continuousAt.continuousWithinAt)
      (fun z _ => (h₁ z).differentiableAt.differentiableWithinAt)
    intro z hz
    have h := hm' (le_refl (0 : ℝ)) (interior_subset hz) (interior_subset hz)
    rw [h₁0] at h
    simpa only [(h₁ z).deriv] using h
  exact hm (le_refl (0 : ℝ)) hx hx
private theorem G_bounds_pos (s x : ℝ) {y : ℝ} (hy : 0 < y)
    (hs : 1 / 2 < s) (hx : 0 ≤ x) :
    (1 ≤ s → G s y x ≤ 1 + y + (2 * s - 1) * x ^ 2) ∧
    (s ≤ 1 → 1 + y + (2 * s - 1) * x ^ 2 ≤ G s y x) := by
  let f : ℝ → ℝ := fun t => G s y t - (2 * s - 1) * t ^ 2
  let f' : ℝ → ℝ := fun t => G₁ s y t - (2 * s - 1) * 2 * t
  let f'' : ℝ → ℝ := fun t => G₂ s y t - (2 * s - 1) * 2
  have h₁ (t : ℝ) : HasDerivAt f (f' t) t := by
    refine ((deriv_G s t hy).sub (((hasDerivAt_id t).pow 2).const_mul (2 * s - 1))).congr_deriv ?_
    simp [f']
    ring
  have h₂ (t : ℝ) : HasDerivAt f' (f'' t) t := by
    refine ((deriv_G₁ s t hy).sub ((hasDerivAt_id t).const_mul ((2 * s - 1) * 2))).congr_deriv ?_
    simp [f'']
  have hf0 : f 0 = 1 + y := by
    unfold f G S U V
    simp only [add_zero, sub_zero, one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
    rw [← two_mul, mul_div_cancel_left₀ _ (by norm_num),
      ← Real.rpow_mul (by positivity), mul_inv_cancel₀ (by linarith : s ≠ 0), Real.rpow_one]
  have hderiv0 : f' 0 = 0 := by simp [f', G₁, S₁, U, V]
  constructor
  · intro hs₁
    have h := le_of_second_nonneg (f := fun t => -f t)
      (f' := fun t => -f' t) (f'' := fun t => -f'' t)
      (fun t => (h₁ t).neg) (fun t => (h₂ t).neg) (fun t _ => by
        dsimp [f'']
        linarith [(G₂_bound s t hy hs).1 hs₁])
      (by simp [hderiv0]) hx
    rw [hf0] at h
    dsimp [f] at h
    linarith
  · intro hs₁
    have h := le_of_second_nonneg h₁ h₂ (fun t _ => by
      dsimp [f'']
      linarith [(G₂_bound s t hy hs).2 hs₁]) hderiv0 hx
    rw [hf0] at h
    dsimp [f] at h
    linarith
private theorem G_even (s y x : ℝ) : G s y (-x) = G s y x := by
  unfold G S U V
  rw [← sub_eq_add_neg, sub_neg_eq_add, add_comm]
private theorem G_bounds (s x : ℝ) {y : ℝ} (hy : 0 ≤ y) (hs : 1 / 2 < s) :
    (1 ≤ s → G s y x ≤ 1 + y + (2 * s - 1) * x ^ 2) ∧
    (s ≤ 1 → 1 + y + (2 * s - 1) * x ^ 2 ≤ G s y x) := by
  have hpos (v : ℝ) (hv : 0 < v) := G_bounds_pos s |x| hv hs (abs_nonneg x)
  have hG (v : ℝ) : G s v |x| = G s v x := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, G_even]
  have hc : Continuous (fun v : ℝ => G s v x) := by
    unfold G S U V
    apply Continuous.rpow_const (by
      apply Continuous.div_const
      exact ((continuous_const.add continuous_id).rpow_const (fun _ => Or.inr (by linarith))).add
        ((continuous_const.add continuous_id).rpow_const (fun _ => Or.inr (by linarith))))
    exact fun _ => Or.inr (inv_nonneg.mpr (by linarith))
  have hd : Continuous (fun v : ℝ => 1 + v + (2 * s - 1) * x ^ 2) := by fun_prop
  have he : y ∈ closure (Ioi (0 : ℝ)) := by rw [closure_Ioi]; exact hy
  constructor
  · intro h
    apply closure_minimal _ (isClosed_le hc hd) he
    intro v hv
    have hv' := (hpos v (mem_Ioi.mp hv)).1 h
    simpa only [mem_ofPred_eq, hG, sq_abs] using hv'
  · intro h
    apply closure_minimal _ (isClosed_le hd hc) he
    intro v hv
    have hv' := (hpos v (mem_Ioi.mp hv)).2 h
    simpa only [mem_ofPred_eq, hG, sq_abs] using hv'
private theorem norm_rpow (p : ℝ) (z : ℂ) :
    ‖z‖ ^ p = (z.re ^ 2 + z.im ^ 2) ^ (p / 2) := by
  rw [Complex.norm_def, Real.sqrt_eq_rpow, ← Real.rpow_mul (Complex.normSq_nonneg z),
    Complex.normSq_apply, ← pow_two, ← pow_two]
  congr 1
  ring
private theorem G_norm_eq (p : ℝ) (z : ℂ) :
    G (p / 2) (z.im ^ 2) z.re =
      ((‖1 + z‖ ^ p + ‖1 - z‖ ^ p) / 2) ^ (2 / p) := by
  simp only [G, S, U, V, norm_rpow, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.one_re, Complex.one_im, zero_add, zero_sub, neg_sq, inv_div]
end MomentComparison
end
end

set_option autoImplicit true
@[expose] public section
public section
open Filter Topology Set
open MomentComparison
namespace MomentComparison
theorem _root_.solution {p : ℝ} (hp : 1 < p) (hp' : p ≤ 2) (z : ℂ) :
    1 + (p - 1) * z.re ^ 2 + z.im ^ 2 ≤
      ((‖1 + z‖ ^ p + ‖1 - z‖ ^ p) / 2) ^ (2 / p) := by
  rw [← G_norm_eq]
  have h := (G_bounds (p / 2) z.re (sq_nonneg z.im) (by linarith)).2 (by linarith)
  linarith
end MomentComparison
