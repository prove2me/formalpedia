-- Prove2me | solution 1 for MasulloRH.five_shell_filter_mellin_and_sampling_zeros
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T15:15:19.008881+00:00
-- url     : https://prove2.me/submissions/c6dc0ca3-a89f-4c1d-89cd-3f8fc44096d0

import Mathlib
open MeasureTheory Set Filter
open scoped Topology ContDiff

theorem solution (n : ℕ) (hn : 0 < n) (b : ℝ → ℂ) (bd : ContDiff ℝ ∞ b)
    (bc : HasCompactSupport b) (bs : ∀ x, x ∉ Ioo 0 (Real.log 2) → b x = 0) :
    let L := Real.log 5
    let T := (n:ℝ)*L
    let D := fun (a : ℂ) (g : ℝ → ℂ) (x : ℝ) => g x - Complex.exp (-a*(T:ℂ))*g (x-T)
    let f := D (-1/2) (D (-1/2) (D (1/2) (D 1 b)))
    let M := fun (g : ℝ → ℂ) (s : ℂ) => ∫ x : ℝ, Complex.exp (s*(x:ℂ))*g x
    ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ (∀ x ∈ Ioo 0 (Real.log 2), f x = b x) ∧
    (∀ k : ℤ, f ((k:ℝ)*L) = 0) ∧
    (∀ s, M f s = (1-Complex.exp ((s+1/2)*(T:ℂ)))^2 *
      (1-Complex.exp ((s-1/2)*(T:ℂ)))*(1-Complex.exp ((s-1)*(T:ℂ)))*M b s) ∧
    HasDerivAt (M f) 0 (-1/2) ∧ M f (-1/2) = 0 ∧ M f (1/2) = 0 ∧ M f 1 = 0 ∧
    ∀ k : ℤ, M f (-1/2+(k:ℂ)*(2*(Real.pi:ℂ)*Complex.I)/(L:ℂ)) = 0 := by
  intro L T D f M
  have hL : 0 < L := Real.log_pos (by norm_num)
  have h2 : Real.log 2 < L := Real.log_lt_log (by norm_num) (by norm_num)
  have hT : L ≤ T := by dsimp [T]; nlinarith [show (1:ℝ) ≤ n by exact_mod_cast hn]
  let Good := fun (g : ℝ → ℂ) => ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ (∀ x ≤ 0, g x = 0) ∧
    (∀ x ∈ Ioo 0 (Real.log 2), g x = b x) ∧ ∀ k : ℤ, g ((k:ℝ)*L) = 0
  have base : Good b := by
    refine ⟨bd,bc,fun x hx => bs _ (fun hy => (not_lt_of_ge hx) hy.1),fun _ _ => rfl,?_⟩
    intro k
    apply bs
    intro hk
    by_cases h : k ≤ 0
    · exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h) hL.le)) hk.1
    · have h' : (1:ℝ) ≤ k := by exact_mod_cast (show (1:ℤ) ≤ k by omega)
      nlinarith [hk.2,mul_nonneg (sub_nonneg.mpr h') hL.le]
  have shiftComp (g : ℝ → ℂ) (hg : HasCompactSupport g) : HasCompactSupport (fun x => g (x-T)) := by
    simpa [Function.comp_def,sub_eq_add_neg] using hg.comp_homeomorph (Homeomorph.addRight (-T))
  have filterStep (a : ℂ) (g : ℝ → ℂ) (hg : Good g) : Good (D a g) := by
    obtain ⟨gd,gc,gneg,gbase,glatt⟩ := hg
    have gd' : ContDiff ℝ ∞ (fun x => g (x-T)) := gd.comp (contDiff_id.sub contDiff_const)
    refine ⟨gd.sub (contDiff_const.mul gd'),gc.sub ((shiftComp g gc).mul_left (f := fun _ => Complex.exp (-a*(T:ℂ)))),?_,?_,?_⟩
    · intro x hx
      simp [D,gneg x hx,gneg (x-T) (by linarith)]
    · intro x hx
      simp [D,gbase x hx,gneg (x-T) (by linarith [hx.2])]
    · intro k
      have hz : (k:ℝ)*L-T = ((k-(n:ℤ):ℤ):ℝ)*L := by dsimp [T]; push_cast; ring
      simp only [D,hz,glatt, mul_zero, sub_zero]
  have g1 := filterStep 1 b base
  have g2 := filterStep (1/2) _ g1
  have g3 := filterStep (-1/2) _ g2
  have g4 := filterStep (-1/2) _ g3
  have intg (s : ℂ) (g : ℝ → ℂ) (gd : Continuous g) (gc : HasCompactSupport g) :
      Integrable (fun x : ℝ => Complex.exp (s*(x:ℂ))*g x) :=
    ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul gd).integrable_of_hasCompactSupport
      (gc.mul_left (f := fun x : ℝ => Complex.exp (s*(x:ℂ))))
  have shiftM (s : ℂ) (g : ℝ → ℂ) : M (fun x => g (x-T)) s = Complex.exp (s*(T:ℂ))*M g s := by
    dsimp [M]
    rw [← integral_const_mul]
    rw [← integral_add_right_eq_self (fun x : ℝ => Complex.exp (s*(x:ℂ))*g (x-T)) T]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [add_sub_cancel_right,Complex.ofReal_add,mul_add,Complex.exp_add]
    ring
  have factor (a s : ℂ) (g : ℝ → ℂ) (hg : Good g) :
      M (D a g) s = (1-Complex.exp ((s-a)*(T:ℂ)))*M g s := by
    have minus : M (D a g) s = M g s - Complex.exp (-a*(T:ℂ))*M (fun x => g (x-T)) s := by
      dsimp [M,D]
      rw [← integral_const_mul,← integral_sub (intg s g hg.1.continuous hg.2.1)
        ((intg s (fun x => g (x-T)) (hg.1.continuous.comp (continuous_id.sub continuous_const)) (shiftComp g hg.2.1)).const_mul (Complex.exp (-a*(T:ℂ))))]
      apply integral_congr_ae; filter_upwards [] with x; ring
    rw [minus,shiftM,← mul_assoc,← Complex.exp_add]
    rw [show -a*(T:ℂ)+s*(T:ℂ) = (s-a)*(T:ℂ) by ring]
    ring
  have allfac (s : ℂ) : M f s = (1-Complex.exp ((s+1/2)*(T:ℂ)))^2 *
      (1-Complex.exp ((s-1/2)*(T:ℂ)))*(1-Complex.exp ((s-1)*(T:ℂ)))*M b s := by
    dsimp only [f]
    rw [factor _ _ _ g3,factor _ _ _ g2,factor _ _ _ g1,factor _ _ _ base]
    ring_nf
  let z : ℂ := -1/2
  have dMb : DifferentiableAt ℂ (M b) z := by
    let F := fun (s : ℂ) (x : ℝ) => Complex.exp (s*(x:ℂ))*b x
    let F' := fun (s : ℂ) (x : ℝ) => Complex.exp (s*(x:ℂ))*(x:ℂ)*b x
    let bound := fun x : ℝ => (Real.exp x*|x|)*‖b x‖
    have hi : Integrable bound := by
      apply ((Real.continuous_exp.mul continuous_abs).mul bd.continuous.norm).integrable_of_hasCompactSupport
      exact bc.norm.mul_left (f := fun x => Real.exp x*|x|)
    have derivF (s : ℂ) (x : ℝ) : HasDerivAt (fun w => F w x) (F' s x) s := by
      simpa [F,F',mul_assoc] using ((((hasDerivAt_id s).mul_const (x:ℂ)).cexp).mul_const (b x))
    have openN : {s : ℂ | s.re < 1} ∈ 𝓝 z :=
      (isOpen_lt Complex.continuous_re continuous_const).mem_nhds (by norm_num [z])
    have result := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F') (bound := bound)
      openN (Filter.Eventually.of_forall (fun s => (intg s b bd.continuous bc).aestronglyMeasurable))
      (intg z b bd.continuous bc)
      (show AEStronglyMeasurable (F' z) volume by
        have hcont : Continuous (F' z) := by dsimp [F']; fun_prop
        exact hcont.aestronglyMeasurable)
      (by
        filter_upwards [] with x
        intro s hs
        by_cases hx : x ∈ Ioo 0 (Real.log 2)
        · have hsr : s.re < 1 := hs
          dsimp [F',bound]
          simp only [norm_mul,Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
            mul_zero,sub_zero,Complex.norm_real,Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr hsr.le) hx.1.le])) (abs_nonneg _)) (norm_nonneg _)
        · simp [F',bound,bs x hx])
      hi (Filter.Eventually.of_forall (fun x s _ => derivF s x))
    exact result.2.differentiableAt
  have dw (a : ℂ) : DifferentiableAt ℂ (fun s : ℂ => 1-Complex.exp ((s-a)*(T:ℂ))) z := by fun_prop
  let G := fun s : ℂ => (1-Complex.exp ((s-1/2)*(T:ℂ)))*(1-Complex.exp ((s-1)*(T:ℂ)))*M b s
  have dG : DifferentiableAt ℂ G z := ((dw (1/2)).mul (dw 1)).mul dMb
  let Z := fun s : ℂ => 1-Complex.exp ((s+1/2)*(T:ℂ))
  have dZ : DifferentiableAt ℂ Z z := by dsimp [Z]; fun_prop
  have Z0 : Z z = 0 := by norm_num [Z,z]
  have dF : HasDerivAt (M f) 0 z := by
    have hid : M f = fun s => Z s^2*G s := by funext s; rw [allfac]; dsimp [Z,G]; ring
    rw [hid]
    simpa [Z0,Pi.mul_def,Pi.pow_def] using! (dZ.hasDerivAt.pow 2).mul dG.hasDerivAt
  refine ⟨g4.1,g4.2.1,g4.2.2.2.1,g4.2.2.2.2,allfac,dF,?_,?_,?_,?_⟩
  · rw [allfac]; norm_num
  · rw [allfac]; norm_num
  · rw [allfac]; norm_num
  · intro k
    rw [allfac]
    have hz : ((-1/2 + (k:ℂ)*(2*(Real.pi:ℂ)*Complex.I)/(L:ℂ))+1/2)*(T:ℂ) =
        (((k*(n:ℤ):ℤ):ℂ))*(2*(Real.pi:ℂ)*Complex.I) := by
      dsimp [T]; push_cast
      have nz : (L:ℂ) ≠ 0 := by exact_mod_cast hL.ne'
      field_simp [nz]; ring
    rw [hz,Complex.exp_int_mul_two_pi_mul_I]
    ring
