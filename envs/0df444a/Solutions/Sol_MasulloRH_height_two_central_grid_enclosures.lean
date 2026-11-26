-- Prove2me | solution 1 for MasulloRH.height_two_central_grid_enclosures
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T10:24:18.987974+00:00
-- url     : https://prove2.me/submissions/45f25ce4-9984-4cdc-beda-11f6b006403d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_height_two_computed_grid_arithmetic
import Definitions.Def_MasulloRH_HeightTwoComputedGrid
import Theorems.Thm_MasulloRH_dyadic_exp_row_sound
import Theorems.Thm_MasulloRH_theta_disk_of_rational_exponential_certificates
import Theorems.Thm_MasulloRH_theta_reflection
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MasulloRH MasulloRH.DyadicExp MasulloRH.HeightTwoScalar MasulloRH.ComputedGrid
open MasulloRH.GaussianApproximation Set
open scoped BigOperators

private theorem rowBounds (t : ℚ) :
    ((row t).lower:ℝ) ≤ Real.exp (t:ℝ) ∧ Real.exp (t:ℝ) ≤ ((row t).upper:ℝ) :=
  (MasulloRH.dyadic_exp_row_sound t).2.2.2

private theorem disk_of_bounds (l u : ℚ) (v : ℝ) (hl : (l:ℝ) ≤ v) (hu : v ≤ (u:ℝ)) :
    ‖(v:ℂ)-((enclose l u).center:ℂ)‖ ≤ ((enclose l u).radius : ℝ) := by
  rw [show ((enclose l u).center:ℂ) = (((enclose l u).center:ℝ):ℂ) by norm_cast,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  dsimp [enclose]
  push_cast
  exact abs_le.mpr ⟨by linarith,by linarith⟩

private theorem abs_bounds (l u : ℚ) (x : ℝ) (hl : (l:ℝ) ≤ x) (hu : x ≤ (u:ℝ)) :
    (amin l u : ℝ) ≤ |x| ∧ |x| ≤ (amax l u : ℝ) := by
  have h1 : ((amin l u:ℚ):ℝ) = max 0 (max (l:ℝ) (-(u:ℝ))) := by
    unfold amin; push_cast; rfl
  have h2 : ((amax l u:ℚ):ℝ) = max (-(l:ℝ)) (u:ℝ) := by
    unfold amax; push_cast; rfl
  rw [h1,h2]
  constructor
  · exact max_le (abs_nonneg _) (max_le (hl.trans (le_abs_self _))
      ((neg_le_neg hu).trans (neg_le_abs _)))
  · apply abs_le.mpr
    exact ⟨(neg_le_neg (le_max_left (-(l:ℝ)) (u:ℝ))).trans (by simpa using hl),
      hu.trans (le_max_right _ _)⟩

private theorem pulse_weight (l u : ℚ) (x : ℝ) (hl : (l:ℝ) ≤ x) (hu : x ≤ (u:ℝ)) :
    0 ≤ (weightUpper l u : ℝ) ∧ ‖pulse 2 x - ((pulseDisk l u).center:ℂ)‖ ≤
      ((pulseDisk l u).radius:ℝ) ∧
      Real.exp (2*(3/4)*x+2*(11/48)*|x|) ≤ (weightUpper l u:ℝ) := by
  obtain ⟨hm,hM⟩ := abs_bounds l u x hl hu
  have hmn : (0:ℝ) ≤ (amin l u:ℝ) := by exact_mod_cast (le_max_left 0 (max l (-u)))
  have hsq1 := pow_le_pow_left₀ hmn hm 2
  have hsq2 := pow_le_pow_left₀ (abs_nonneg x) hM 2
  rw [sq_abs] at hsq1 hsq2
  have hleft := (rowBounds (-9*(amax l u)^2)).1
  have hright := (rowBounds (-9*(amin l u)^2)).2
  push_cast at hleft hright
  have heL := hleft.trans (Real.exp_le_exp.mpr (by linarith : -9*(amax l u:ℝ)^2 ≤ -9*x^2))
  have heU := (Real.exp_le_exp.mpr (by linarith : -9*x^2 ≤ -9*(amin l u:ℝ)^2)).trans hright
  have hspos := Real.sqrt_pos.mpr Real.pi_pos
  have hfactorL : (1692568/1000000:ℝ) ≤ 3/Real.sqrt Real.pi := by
    apply (le_div_iff₀ hspos).2
    have h : Real.sqrt Real.pi ≤ 3/(1692568/1000000:ℝ) :=
      (Real.sqrt_le_left (by norm_num)).2 (Real.pi_lt_d20.le.trans (by norm_num))
    linarith
  have hfactorU : 3/Real.sqrt Real.pi ≤ (1692569/1000000:ℝ) := by
    apply (div_le_iff₀ hspos).2
    have h : 3/(1692569/1000000:ℝ) ≤ Real.sqrt Real.pi :=
      Real.le_sqrt_of_sq_le ((by norm_num : (3/(1692569/1000000:ℝ))^2 ≤ 3.14159265358979323846).trans Real.pi_gt_d20.le)
    linarith
  have hn : (0:ℝ) ≤ ((row (-9*(amax l u)^2)).lower:ℝ) :=
    Rat.cast_nonneg.mpr (MasulloRH.dyadic_exp_row_sound _).2.2.1
  have low := mul_le_mul hfactorL heL hn (by positivity)
  have high := mul_le_mul hfactorU heU (Real.exp_pos _).le (by norm_num)
  have w := (rowBounds (3*u/2 + 11*amax l u/24)).2
  push_cast at w
  have ww : Real.exp (2*(3/4)*x+2*(11/48)*|x|) ≤ (weightUpper l u:ℝ) :=
    (Real.exp_le_exp.mpr (by linarith [hu,hM])).trans w
  refine ⟨(Real.exp_pos _).le.trans ww,?_,ww⟩
  have pform : pulse 2 x = (((3/Real.sqrt Real.pi)*Real.exp (-9*x^2):ℝ):ℂ) := by
    unfold pulse
    push_cast
    rw [show (2:ℂ)+1=3 by norm_num, show -((3:ℂ)*(x:ℂ))^2 = -9*(x:ℂ)^2 by ring]
  rw [pform]
  apply disk_of_bounds
  · push_cast; exact low
  · push_cast; exact high

private theorem disk_rescale (l u : ℚ) (v : Disk) (z : ℂ) (t : ℝ)
    (h0 : 0 ≤ t) (hl : (l:ℝ) ≤ t) (hu : t ≤ (u:ℝ))
    (hz : ‖z-(v.center:ℂ)‖ ≤ (v.radius:ℝ)) :
    ‖(t:ℂ)*z-((rescale l u v).center:ℂ)‖ ≤ ((rescale l u v).radius:ℝ) := by
  let m : ℚ := (l+u)/2
  have ha : |t-(m:ℝ)| ≤ (((u-l)/2:ℚ):ℝ) := by
    dsimp [m]; push_cast
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hsum : (t:ℂ)*z - ((rescale l u v).center:ℂ) =
      (t:ℂ)*(z-(v.center:ℂ)) + ((t-(m:ℝ):ℝ):ℂ)*(v.center:ℂ) := by
    dsimp [rescale,m]; push_cast; ring
  rw [hsum]
  apply (norm_add_le _ _).trans
  rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg h0,Complex.norm_ratCast]
  dsimp [rescale]
  push_cast
  push_cast at ha
  exact add_le_add (mul_le_mul hu hz (norm_nonneg _) (h0.trans hu))
    (mul_le_mul_of_nonneg_right ha (abs_nonneg _))

private theorem normalized_bound (l u : ℚ) (b : Bool) (z w : ℝ)
    (hw : ((innerLo l u b).argument:ℝ) ≤ w ∧ w ≤ ((innerHi l u b).argument:ℝ))
    (hz : (Real.exp z)^2*(divisor b:ℝ) = Real.exp w)
    (hU : (gaussianHi l u b).upper < 1) :
    let v := normalized (gaussianLo l u b).lower (gaussianHi l u b).upper
    ‖theta z - (v.center:ℂ)‖ ≤ (v.radius:ℝ) := by
  intro v
  let a := (gaussianLo l u b).lower
  let c := (gaussianHi l u b).upper
  let K := order c
  have hd : 0 < divisor b := by cases b <;> norm_num [divisor]
  apply MasulloRH.theta_disk_of_rational_exponential_certificates K (innerLo l u b)
    (innerHi l u b) (gaussianLo l u b) (gaussianHi l u b) (divisor b) v.center v.radius
  · exact ⟨(MasulloRH.dyadic_exp_row_sound _).2.1,(MasulloRH.dyadic_exp_row_sound _).2.1,
      (MasulloRH.dyadic_exp_row_sound _).2.1,(MasulloRH.dyadic_exp_row_sound _).2.1⟩
  · exact hd
  · exact (MasulloRH.dyadic_exp_row_sound _).2.2.1
  · dsimp only [gaussianLo,gaussianHi]
    rw [(MasulloRH.dyadic_exp_row_sound _).1,(MasulloRH.dyadic_exp_row_sound _).1,
      div_mul_cancel₀ _ hd.ne', div_mul_cancel₀ _ hd.ne']
    exact ⟨le_rfl,le_rfl⟩
  · exact ⟨(MasulloRH.dyadic_exp_row_sound _).2.2.1,hU⟩
  · change v.center-v.radius ≤ polynomial K a c-tail K c ∧
      polynomial K c a+tail K c ≤ v.center+v.radius
    have hs : (0:ℚ)<scale := by norm_num [scale]
    have h1 (t : ℚ) : down t ≤ t := (div_le_iff₀ hs).2 (Int.floor_le _)
    have h2 (t : ℚ) : t ≤ up t := (le_div_iff₀ hs).2 (Int.le_ceil _)
    let L := polynomial K a c-tail K c
    let H := polynomial K c a+tail K c
    change (down L+up H)/2-(up H-down L)/2 ≤ L ∧ H ≤ (down L+up H)/2+(up H-down L)/2
    constructor <;> linarith [h1 L,h2 H]
  · exact hw
  · exact hz

private theorem theta_cell (l u : ℚ) (b : Bool) (x : ℝ)
    (hl : (l:ℝ) ≤ x) (hu : x ≤ (u:ℝ)) (hU : (gaussianHi l u b).upper < 1) :
    ‖theta x-((thetaDisk l u b).center:ℂ)‖ ≤ ((thetaDisk l u b).radius:ℝ) := by
  have hexp (s : ℝ) : Real.exp (2*s) = (Real.exp s)^2 := by simpa using Real.exp_nat_mul s 2
  cases b
  · apply normalized_bound l u false x (2*x) _ _ hU
    · dsimp only [innerLo,innerHi,Bool.false_eq_true,↓reduceIte]
      rw [(MasulloRH.dyadic_exp_row_sound _).1,(MasulloRH.dyadic_exp_row_sound _).1]
      push_cast; constructor <;> linarith
    · norm_num [divisor,hexp]
  · let y := -x-Real.log 4
    let v := normalized (gaussianLo l u true).lower (gaussianHi l u true).upper
    have hv : ‖theta y - (v.center:ℂ)‖ ≤ (v.radius:ℝ) := by
      apply normalized_bound l u true y (-2*x) _ _ hU
      · dsimp only [innerLo,innerHi,↓reduceIte]
        rw [(MasulloRH.dyadic_exp_row_sound _).1,(MasulloRH.dyadic_exp_row_sound _).1]
        simp only [if_true]; push_cast; constructor <;> linarith
      · dsimp [y,divisor]
        rw [Real.exp_sub,Real.exp_log (by norm_num : (0:ℝ)<4),show -2*x=2*(-x) by ring,hexp]
        ring
    have pL := (rowBounds (-u)).1
    have pU := (rowBounds (-l)).2
    push_cast at pL pU
    have hL := pL.trans (Real.exp_le_exp.mpr (neg_le_neg hu))
    have hH := (Real.exp_le_exp.mpr (neg_le_neg hl)).trans pU
    rw [MasulloRH.theta_reflection x]
    apply disk_rescale ((row (-u)).lower/2) ((row (-l)).upper/2) v (theta y) (Real.exp (-x)/2)
    · positivity
    · push_cast; linarith
    · push_cast; linarith
    · exact hv

theorem solution :
    let h : ℝ := 1/8192
    let e (k : ℤ) := -4 + (k : ℝ) * h
    let s : Fin 11 → ℤ := ![-3072,-2048,1024,3072,6144,8192,11264,14336,16384,18432,19456]
    ∃ (P R W : ℕ → ℚ) (C D : ℤ → ℚ),
      (∀ (j : ℕ), j < 65536 → 0 ≤ (W j : ℝ) ∧ ∀ x ∈ Icc (e j) (e ((j : ℤ)+1)),
        ‖pulse 2 x - (P j : ℂ)‖ ≤ (R j : ℝ) ∧
          Real.exp (2*(3/4)*x + 2*(11/48)*|x|) ≤ (W j : ℝ)) ∧
      (∀ k : ℤ, 8192 ≤ k → k < 45056 → ∀ z ∈ Icc (e k) (e (k+1)),
        ‖theta z - (C k : ℂ)‖ ≤ (D k : ℝ)) ∧
      (let T (k : ℤ) : ℚ := if k < 8192 ∨ 45056 ≤ k then 0 else C k
       let U (k : ℤ) : ℚ := if k < 8192 ∨ 45056 ≤ k then 1/(2:ℚ)^64 else D k
       let A (j : ℕ) := ‖(P j : ℂ) - ∑ i, HeightTwoWitness.coeffs i * (T ((j : ℤ)-s i) : ℂ)‖ +
          ((R j : ℝ) + ∑ i, ‖HeightTwoWitness.coeffs i‖ * (U ((j : ℤ)-s i) : ℝ))
       ∑ j ∈ Finset.range 65536, h * ((W j : ℝ) * A j ^ 2) ≤ 1/100) := by
  intro h e s
  have edgeEq (k : ℤ) : ((edge k:ℚ):ℝ) = e k := by
    dsimp [edge,e,h]; push_cast; ring
  obtain ⟨hrange,hsum⟩ := MasulloRH.height_two_computed_grid_arithmetic
  refine ⟨fun j => (pulseAt j).center, fun j => (pulseAt j).radius, weightAt,
    fun k => (central k).center, fun k => (central k).radius, ?_, ?_, ?_⟩
  · intro j _
    constructor
    · exact (Real.exp_pos _).le.trans (rowBounds _).2
    · intro x hx
      have bun := pulse_weight (edge j) (edge ((j:ℤ)+1)) x
        (by rw [edgeEq]; exact hx.1) (by rw [edgeEq]; exact hx.2)
      exact bun.2
  · intro k hk hk' z hz
    exact theta_cell _ _ _ z (by rw [edgeEq]; exact hz.1) (by rw [edgeEq]; exact hz.2)
      (hrange k (Finset.mem_Ico.mpr ⟨hk,hk'⟩))
  · let T (k : ℤ) : ℚ := if k < 8192 ∨ 45056 ≤ k then 0 else (central k).center
    let U (k : ℤ) : ℚ := if k < 8192 ∨ 45056 ≤ k then 1/(2:ℚ)^64 else (central k).radius
    have tc (k : ℤ) : (fullTheta k).center = T k := by
      by_cases h : k < 8192 ∨ 45056 ≤ k <;> simp [fullTheta,T,h]
    have uc (k : ℤ) : (fullTheta k).radius = U k := by
      by_cases h : k < 8192 ∨ 45056 ≤ k <;> simp [fullTheta,U,h]
    have shiftEq : shifts = s := rfl
    let A (j : ℕ) : ℝ := ‖((pulseAt j).center:ℂ) -
          ∑ i, HeightTwoWitness.coeffs i * (T ((j:ℤ)-s i):ℂ)‖ +
      (((pulseAt j).radius:ℝ) + ∑ i, ‖HeightTwoWitness.coeffs i‖ * (U ((j:ℤ)-s i):ℝ))
    change ∑ j ∈ Finset.range 65536, h*((weightAt j:ℝ)*A j^2) ≤ 1/100
    have term (j : ℕ) : h*((weightAt j:ℝ)*A j^2) = (energyTerm j:ℝ) := by
      let a : ℚ := (pulseAt j).center - ∑ i, HeightTwoWitness.coeffsQ i * T ((j:ℤ)-s i)
      have ca : (a:ℂ) = ((pulseAt j).center:ℂ) -
          ∑ i, HeightTwoWitness.coeffs i*(T ((j:ℤ)-s i):ℂ) := by
        dsimp [a,HeightTwoWitness.coeffs]; push_cast; rfl
      dsimp only [A,h,energyTerm]
      rw [← ca]
      simp only [tc,uc,shiftEq,HeightTwoWitness.coeffs,Complex.norm_ratCast]
      dsimp only [a]
      push_cast
      rfl
    have total : ((∑ j ∈ Finset.range 65536, energyTerm j:ℚ):ℝ) ≤ ((1/100:ℚ):ℝ) :=
      Rat.cast_le.mpr hsum
    simpa only [term,Rat.cast_sum,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using total
