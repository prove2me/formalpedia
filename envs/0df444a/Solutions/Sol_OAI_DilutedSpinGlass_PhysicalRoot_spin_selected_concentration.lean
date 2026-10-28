-- Prove2me | solution 1 for OAI.DilutedSpinGlass.PhysicalRoot.spin_selected_concentration
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T08:00:01.788228+00:00
-- url     : https://prove2.me/submissions/9cf9ea3d-f191-43cc-9ef2-77e04ef91743

import Mathlib
import Definitions.Def_DilutedSpin
import Definitions.Def_OAIQ041D000

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FiniteLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)

theorem expect_congr {f g : Ω → ℝ} (h : ∀ x, f x = g x) : P.expect f = P.expect g := by
  exact congrArg P.expect (funext h)

theorem expect_mono {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) : P.expect f ≤ P.expect g := by
  exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (P.nonneg x))

theorem covariance_centered (f g : Ω → ℝ) :
    P.covariance f g = P.expect (fun x => (f x - P.expect f) * (g x - P.expect g)) := by
  rw [covariance]
  calc
    _ = P.expect (fun x => f x * g x - f x * P.expect g -
        P.expect f * g x + P.expect f * P.expect g) := by simp
    _ = _ := P.expect_congr (fun x => by ring)

variable {n : ℕ}

/-- Elementary Jensen for the square, proved from its nonnegative variance. -/
theorem expect_sq_sub_expect (f : Ω → ℝ) :
    P.expect (fun x => (f x - P.expect f)^2) =
      P.expect (fun x => f x ^ 2) - P.expect f ^ 2 := by
  calc
    _ = P.expect (fun x => f x ^ 2 - 2 * P.expect f * f x + P.expect f ^ 2) :=
      P.expect_congr (fun _ => by ring)
    _ = _ := by simp; ring

theorem sq_expect_le_expect_sq (f : Ω → ℝ) :
    P.expect f ^ 2 ≤ P.expect (fun x => f x ^ 2) := by
  have h := P.expect_nonneg (fun x => sq_nonneg (f x - P.expect f))
  rw [expect_sq_sub_expect] at h
  linarith

theorem logMean_mono {m : ℝ} (hm : 0 < m) {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) :
    P.logMean m f ≤ P.logMean m g := by
  apply div_le_div_of_nonneg_right _ hm.le
  apply Real.log_le_log (P.expMoment_pos _ _)
  exact P.expect_mono (fun x => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (h x) hm.le))

/-- Root-measurable uniform bounds pass unchanged through each power mean. -/
theorem logMean_stability {m c : ℝ} (hm : 0 < m) {f g : Ω → ℝ}
    (h : ∀ x, |f x - g x| ≤ c) : |P.logMean m f - P.logMean m g| ≤ c := by
  have hfg : P.logMean m f ≤ P.logMean m g + c := by
    rw [← P.logMean_add (ne_of_gt hm)]
    exact P.logMean_mono hm (fun x => by have hx := (abs_le.mp (h x)).2; linarith)
  have hgf : P.logMean m g ≤ P.logMean m f + c := by
    rw [← P.logMean_add (ne_of_gt hm)]
    exact P.logMean_mono hm (fun x => by have hx := (abs_le.mp (h x)).1; linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Differentiation commutes with a finite path kernel. -/
theorem hasDerivAt_expect {f : ℝ → Ω → ℝ} {f' : Ω → ℝ} {u : ℝ}
    (h : ∀ x, HasDerivAt (fun t => f t x) (f' x) u) :
    HasDerivAt (fun t => P.expect (f t)) (P.expect f') u := by
  have hd := HasDerivAt.sum (u := Finset.univ)
    (fun x _ => (h x).const_mul (P.weight x))
  have heq : (∑ x, fun t => P.weight x * f t x) = (fun t => P.expect (f t)) := by
    funext t
    simp only [Finset.sum_apply, expect]
  rw [heq] at hd
  exact hd

/-- First variation of a power-mean step: the derivative is the tilted score. -/
theorem hasDerivAt_logMean {m : ℝ} (hm : m ≠ 0)
    {f : ℝ → Ω → ℝ} {f' : Ω → ℝ} {u : ℝ}
    (h : ∀ x, HasDerivAt (fun t => f t x) (f' x) u) :
    HasDerivAt (fun t => P.logMean m (f t)) ((P.tilt m (f u)).expect f') u := by
  have he := P.hasDerivAt_expect (fun x => ((h x).const_mul m).exp)
  have hl := (he.log (ne_of_gt (P.expMoment_pos m (f u)))).div_const m
  change HasDerivAt (fun t => P.logMean m (f t)) _ u at hl
  suffices heqv : (P.tilt m (f u)).expect f' =
      (P.expect (fun x => Real.exp (m * f u x) * (m * f' x)) / P.expMoment m (f u)) / m by
    rw [heqv]
    exact hl
  rw [tilt_expect]
  have heq : P.expect (fun x => Real.exp (m * f u x) * (m * f' x)) =
      m * P.expect (fun x => Real.exp (m * f u x) * f' x) := by
    rw [← expect_mul_left]
    exact P.expect_congr (fun x => by ring)
  rw [heq]
  field_simp


/-- Differentiating an observable under a finite exponentially tilted kernel. -/
theorem hasDerivAt_tilt_expect {m : ℝ}
    {f g : ℝ → Ω → ℝ} {f' g' : Ω → ℝ} {u : ℝ}
    (hf : ∀ x, HasDerivAt (fun t => f t x) (f' x) u)
    (hg : ∀ x, HasDerivAt (fun t => g t x) (g' x) u) :
    HasDerivAt (fun t => (P.tilt m (f t)).expect (g t))
      ((P.tilt m (f u)).expect g' +
        m * (P.tilt m (f u)).covariance (g u) f') u := by
  have hnum := P.hasDerivAt_expect
    (fun x => (((hf x).const_mul m).exp).mul (hg x))
  have hden := P.hasDerivAt_expect (fun x => ((hf x).const_mul m).exp)
  have hd := hnum.div hden (ne_of_gt (P.expMoment_pos m (f u)))
  simp only [tilt_expect]
  apply hd.congr_deriv
  have hnum' : P.expect (fun x =>
      Real.exp (m * f u x) * (m * f' x) * g u x + Real.exp (m * f u x) * g' x) =
      m * P.expect (fun x => Real.exp (m * f u x) * (g u x * f' x)) +
        P.expect (fun x => Real.exp (m * f u x) * g' x) := by
    rw [expect_add, ← expect_mul_left]
    congr 1
    exact P.expect_congr (fun x => by ring)
  have hden' : P.expect (fun x => Real.exp (m * f u x) * (m * f' x)) =
      m * P.expect (fun x => Real.exp (m * f u x) * f' x) := by
    rw [← expect_mul_left]
    exact P.expect_congr (fun x => by ring)
  rw [hnum', hden', covariance, tilt_expect, tilt_expect, tilt_expect]
  simp only [expMoment, Pi.mul_apply]
  have hne : P.expect (fun x => Real.exp (m * f u x)) ≠ 0 :=
    ne_of_gt (P.expMoment_pos m (f u))
  field_simp [hne]
  ring

/-- Total variance at one edge of a finite probability tree. -/
theorem variance_bind {Λ : Type*} [Fintype Λ] (Q : Ω → FiniteLaw Λ)
    (f : Ω × Λ → ℝ) :
    (P.bind Q).covariance f f =
      P.expect (fun x => (Q x).covariance (fun y => f (x,y)) (fun y => f (x,y))) +
        P.covariance (fun x => (Q x).expect (fun y => f (x,y)))
          (fun x => (Q x).expect (fun y => f (x,y))) := by
  simp only [covariance, expect_bind, expect_sub]
  ring

theorem covariance_self_nonneg (f : Ω → ℝ) : 0 ≤ P.covariance f f := by
  rw [covariance_centered]
  exact P.expect_nonneg (fun x => mul_self_nonneg _)

theorem abs_expect_le {f : Ω → ℝ} {B : ℝ} (hf : ∀ x, |f x| ≤ B) :
    |P.expect f| ≤ B := by
  apply abs_le.mpr
  constructor
  · have h := P.expect_mono (fun x => (abs_le.mp (hf x)).1)
    simpa only [expect_const] using h
  · have h := P.expect_mono (fun x => (abs_le.mp (hf x)).2)
    simpa only [expect_const] using h

theorem continuousOn_expect {S : Set ℝ} {f : ℝ → Ω → ℝ}
    (hf : ∀ x, ContinuousOn (fun t => f t x) S) :
    ContinuousOn (fun t => P.expect (f t)) S := by
  unfold expect
  apply continuousOn_finsetSum
  intro x _
  exact continuousOn_const.mul (hf x)

theorem continuousOn_logMean {S : Set ℝ} {f : ℝ → Ω → ℝ}
    (hf : ∀ x, ContinuousOn (fun t => f t x) S) (m : ℝ) :
    ContinuousOn (fun t => P.logMean m (f t)) S := by
  apply ContinuousOn.div_const
  apply ContinuousOn.log
  · exact P.continuousOn_expect (fun x => (continuousOn_const.mul (hf x)).rexp)
  · intro t _
    exact ne_of_gt (P.expMoment_pos m (f t))

theorem continuousOn_tilt_expect {S : Set ℝ} {f g : ℝ → Ω → ℝ}
    (hf : ∀ x, ContinuousOn (fun t => f t x) S)
    (hg : ∀ x, ContinuousOn (fun t => g t x) S) (m : ℝ) :
    ContinuousOn (fun t => (P.tilt m (f t)).expect (g t)) S := by
  simp_rw [tilt_expect]
  apply ContinuousOn.div
  · exact P.continuousOn_expect (fun x => ((continuousOn_const.mul (hf x)).rexp).mul (hg x))
  · exact P.continuousOn_expect (fun x => (continuousOn_const.mul (hf x)).rexp)
  · intro t _
    exact ne_of_gt (P.expMoment_pos m (f t))

theorem continuousOn_tilt_covariance {S : Set ℝ} {f g : ℝ → Ω → ℝ}
    (hf : ∀ x, ContinuousOn (fun t => f t x) S)
    (hg : ∀ x, ContinuousOn (fun t => g t x) S) (m : ℝ) :
    ContinuousOn (fun t => (P.tilt m (f t)).covariance (g t) (g t)) S := by
  unfold covariance
  exact (P.continuousOn_tilt_expect hf (fun x => (hg x).mul (hg x)) m).sub
    ((P.continuousOn_tilt_expect hf hg m).mul (P.continuousOn_tilt_expect hf hg m))

end FiniteLaw
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_KernelTower
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass

namespace KernelTower

variable {Ω : Type} [Fintype Ω]

/-- First variation through the entire finite hierarchy, with all exponents
and all original path-dependent priors retained. -/
theorem hasDerivAt_backwardLog (n : ℕ) (T : KernelTower Ω n)
    (m : Fin n → ℝ) (hm : ∀ i, m i ≠ 0)
    {f : ℝ → FinitePath Ω n → ℝ} {f' : FinitePath Ω n → ℝ} {u : ℝ}
    (hf : ∀ x, HasDerivAt (fun t => f t x) (f' x) u) :
    HasDerivAt (fun t => backwardLog n T m (f t))
      ((law n (tilt n T m (f u))).expect f') u := by
  induction n with
  | zero =>
    rw [law_zero_expect (Ω := Ω)]
    exact hf ()
  | succ n ih =>
    have hs := fun x => ih (T.2 x) (fun j => m j.succ) (fun j => hm j.succ)
      (fun y => hf (x,y))
    rw [law_succ_expect (Ω := Ω) n]
    simpa only [backwardLog, tilt] using
      T.1.hasDerivAt_logMean (hm 0) hs


/-- The lower energy estimate in pert:second-derivative; the smallest exponent
controls the full terminal path variance, not merely the root variance. -/
theorem varianceEnergy_lower (n : ℕ) (T : KernelTower Ω n)
    (m : Fin n → ℝ) {c : ℝ} (hm : ∀ i, c ≤ m i) (f : FinitePath Ω n → ℝ) :
    c * (law n T).covariance f f ≤ varianceEnergy n T m f := by
  induction n with
  | zero => simp [FiniteLaw.covariance, law_zero_expect, varianceEnergy]
  | succ n ih =>
    let g := fun x => (law n (T.2 x)).expect (fun y => f (x,y))
    have hfirst : c * T.1.covariance g g ≤ m 0 * T.1.covariance g g :=
      mul_le_mul_of_nonneg_right (hm 0) (T.1.covariance_self_nonneg g)
    have hrest := T.1.expect_mono (fun x => ih (T.2 x) (fun j => m j.succ)
      (fun j => hm j.succ) (fun y => f (x,y)))
    have hv := T.1.variance_bind (fun x => law n (T.2 x)) f
    change (law (n+1) T).covariance f f = _ at hv
    rw [hv]
    simp only [varianceEnergy]
    dsimp only [g] at hfirst
    rw [FiniteLaw.expect_mul_left] at hrest
    nlinarith

/-- Second variation through a tower. Terminal derivatives plus the positive
weighted martingale energy from every depth. No concentration is assumed. -/
theorem hasDerivAt_path_score (n : ℕ) (T : KernelTower Ω n)
    (m : Fin n → ℝ) (hm : ∀ i, m i ≠ 0)
    {f f' : ℝ → FinitePath Ω n → ℝ} {f'' : FinitePath Ω n → ℝ} {u : ℝ}
    (hf : ∀ x, HasDerivAt (fun t => f t x) (f' u x) u)
    (hf' : ∀ x, HasDerivAt (fun t => f' t x) (f'' x) u) :
    HasDerivAt (fun t => (law n (tilt n T m (f t))).expect (f' t))
      ((law n (tilt n T m (f u))).expect f'' +
        varianceEnergy n (tilt n T m (f u)) m (f' u)) u := by
  induction n with
  | zero =>
    simp_rw [law_zero_expect (Ω := Ω)]
    simpa only [varianceEnergy, add_zero] using hf' ()
  | succ n ih =>
    have hfirst := fun x => hasDerivAt_backwardLog n (T.2 x)
      (fun j => m j.succ) (fun j => hm j.succ) (fun y => hf (x,y))
    have hsecond := fun x => ih (T.2 x) (fun j => m j.succ)
      (fun j => hm j.succ) (fun y => hf (x,y)) (fun y => hf' (x,y))
    have hd := T.1.hasDerivAt_tilt_expect hfirst hsecond (m := m 0)
    simp_rw [law_succ_expect (Ω := Ω) n]
    simpa only [tilt, backwardLog, varianceEnergy, FiniteLaw.expect_add, add_assoc, add_comm, add_left_comm] using hd

theorem backwardLog_const (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (hm : ∀ i, m i ≠ 0) (c : ℝ) : backwardLog n T m (fun _ => c) = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [backwardLog]
    have heq : (fun x => backwardLog n (T.2 x) (fun j => m j.succ) (fun _ => c)) =
        (fun _ => c) := by
      funext x
      exact ih (T.2 x) (fun j => m j.succ) (fun j => hm j.succ)
    rw [heq, FiniteLaw.logMean_const _ (hm 0)]

/-- The uniform insertion bound, with full arbitrary depth-dependent priors. -/
theorem backwardLog_stability (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (hm : ∀ i, 0 < m i) {f g : FinitePath Ω n → ℝ} {c : ℝ}
    (hfg : ∀ x, |f x - g x| ≤ c) :
    |backwardLog n T m f - backwardLog n T m g| ≤ c := by
  induction n with
  | zero => exact hfg ()
  | succ n ih =>
    apply T.1.logMean_stability (hm 0)
    intro x
    exact ih (T.2 x) (fun j => m j.succ) (fun j => hm j.succ) (fun y => hfg (x,y))

theorem continuousOn_backwardLog (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    {S : Set ℝ} {f : ℝ → FinitePath Ω n → ℝ}
    (hf : ∀ x, ContinuousOn (fun t => f t x) S) :
    ContinuousOn (fun t => backwardLog n T m (f t)) S := by
  induction n with
  | zero => exact hf ()
  | succ n ih =>
    exact T.1.continuousOn_logMean (fun x => ih (T.2 x) (fun j => m j.succ)
      (fun y => hf (x,y))) (m 0)

theorem continuousOn_path_expect (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    {S : Set ℝ} {f g : ℝ → FinitePath Ω n → ℝ}
    (hf : ∀ x, ContinuousOn (fun t => f t x) S)
    (hg : ∀ x, ContinuousOn (fun t => g t x) S) :
    ContinuousOn (fun t => (law n (tilt n T m (f t))).expect (g t)) S := by
  induction n with
  | zero => simpa only [law_zero_expect] using hg ()
  | succ n ih =>
    simp_rw [law_succ_expect (Ω := Ω) n]
    exact T.1.continuousOn_tilt_expect
      (fun x => continuousOn_backwardLog n (T.2 x) (fun j => m j.succ) (fun y => hf (x,y)))
      (fun x => ih (T.2 x) (fun j => m j.succ) (fun y => hf (x,y)) (fun y => hg (x,y))) (m 0)

theorem continuousOn_varianceEnergy_tilt (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    {S : Set ℝ} {f g : ℝ → FinitePath Ω n → ℝ}
    (hf : ∀ x, ContinuousOn (fun t => f t x) S)
    (hg : ∀ x, ContinuousOn (fun t => g t x) S) :
    ContinuousOn (fun t => varianceEnergy n (tilt n T m (f t)) m (g t)) S := by
  induction n with
  | zero => exact continuousOn_const
  | succ n ih =>
    have hF := fun x => continuousOn_backwardLog n (T.2 x) (fun j => m j.succ)
      (fun y => hf (x,y))
    have hG := fun x => continuousOn_path_expect n (T.2 x) (fun j => m j.succ)
      (fun y => hf (x,y)) (fun y => hg (x,y))
    exact (continuousOn_const.mul (T.1.continuousOn_tilt_covariance hF hG (m 0))).add
      (T.1.continuousOn_tilt_expect hF (fun x => ih (T.2 x) (fun j => m j.succ)
        (fun y => hf (x,y)) (fun y => hg (x,y))) (m 0))

 
theorem second_variation_lower (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    {c C : ℝ} (hm : ∀ i, c ≤ m i) (f g h : FinitePath Ω n → ℝ)
    (hh : ∀ x, -C ≤ h x) :
    c * (law n (tilt n T m f)).covariance g g - C ≤
      (law n (tilt n T m f)).expect h + varianceEnergy n (tilt n T m f) m g := by
  have hv := varianceEnergy_lower n (tilt n T m f) m hm g
  have he := (law n (tilt n T m f)).expect_mono hh
  rw [FiniteLaw.expect_const] at he
  linarith

 
theorem thermal_variance_integral (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    {a b c B C : ℝ} (hab : a ≤ b) (hc : 0 < c) (hm : ∀ i, c ≤ m i)
    {f g h : ℝ → FinitePath Ω n → ℝ}
    (hf : ∀ u ∈ Set.Icc a b, ∀ x, HasDerivAt (fun t => f t x) (g u x) u)
    (hg : ∀ u ∈ Set.Icc a b, ∀ x, HasDerivAt (fun t => g t x) (h u x) u)
    (hh : ∀ x, ContinuousOn (fun u => h u x) (Set.Icc a b))
    (hbound : ∀ u ∈ Set.Icc a b, ∀ x, |g u x| ≤ B)
    (hcurv : ∀ u ∈ Set.Icc a b, ∀ x, -C ≤ h u x) :
    (∫ u in a..b, (law n (tilt n T m (f u))).covariance (g u) (g u)) ≤
      (2*B + C*(b-a))/c := by
  let D := fun u => (law n (tilt n T m (f u))).expect (g u)
  let V := fun u => (law n (tilt n T m (f u))).covariance (g u) (g u)
  let E := fun u => (law n (tilt n T m (f u))).expect (h u) +
    varianceEnergy n (tilt n T m (f u)) m (g u)
  have hm' : ∀ i, m i ≠ 0 := fun i => ne_of_gt (hc.trans_le (hm i))
  have hfc : ∀ x, ContinuousOn (fun u => f u x) (Set.Icc a b) :=
    fun x u hu => (hf u hu x).continuousAt.continuousWithinAt
  have hgc : ∀ x, ContinuousOn (fun u => g u x) (Set.Icc a b) :=
    fun x u hu => (hg u hu x).continuousAt.continuousWithinAt
  have hDc : ContinuousOn D (Set.Icc a b) := continuousOn_path_expect n T m hfc hgc
  have hVc : ContinuousOn V (Set.Icc a b) := by
    unfold V FiniteLaw.covariance
    exact (continuousOn_path_expect n T m hfc (fun x => (hgc x).mul (hgc x))).sub (hDc.mul hDc)
  have hEc : ContinuousOn E (Set.Icc a b) :=
    (continuousOn_path_expect n T m hfc hh).add (continuousOn_varianceEnergy_tilt n T m hfc hgc)
  have hVi : IntervalIntegrable V MeasureTheory.volume a b :=
    hVc.intervalIntegrable_of_Icc hab
  have hEi : IntervalIntegrable E MeasureTheory.volume a b :=
    hEc.intervalIntegrable_of_Icc hab
  have hd : ∀ u ∈ Set.uIcc a b, HasDerivAt D (E u) u := by
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    exact hasDerivAt_path_score n T m hm' (hf u hu) (hg u hu)
  have hEq := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hEi
  have hmono := intervalIntegral.integral_mono_on hab
    ((hVi.const_mul c).sub intervalIntegrable_const) hEi
    (fun u hu => second_variation_lower n T m hm (f u) (g u) (h u) (hcurv u hu))
  rw [intervalIntegral.integral_sub (hVi.const_mul c) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, hEq] at hmono
  have hDa : |D a| ≤ B := (law n (tilt n T m (f a))).abs_expect_le (hbound a ⟨le_rfl,hab⟩)
  have hDb : |D b| ≤ B := (law n (tilt n T m (f b))).abs_expect_le (hbound b ⟨hab,le_rfl⟩)
  apply (le_div_iff₀ hc).mpr
  change (∫ u in a..b, V u) * c ≤ _
  simp only [smul_eq_mul] at hmono
  linarith [(abs_le.mp hDa).1, (abs_le.mp hDb).2]

end KernelTower
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PoissonMoments
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.DilutedSpinGlass.compoundRootLaw_prob _root_.OAI.DilutedSpinGlass.fullRootLaw_prob _root_.OAI.DilutedSpinGlass.rootPathCountable _root_.OAI.DilutedSpinGlass.rootPathSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass

/-- A bounded measurable score belongs to every finite Lp space. -/
theorem bounded_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Ω → ℝ} {B : ℝ} (hf : Measurable f)
    (hB : ∀ x, |f x| ≤ B) (p : ℝ≥0∞) : MemLp f p μ := by
  apply MemLp.of_bound hf.aestronglyMeasurable B
  exact ae_of_all _ (fun point => by simpa only [Real.norm_eq_abs] using hB point)

/-- The exact two-independent-copy identity for variance. -/
theorem variance_two_copies {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, ∫ y, (f x-f y)^2 ∂μ ∂μ) = 2 * variance f μ := by
  have hi := hf.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hs := hf.integrable_sq
  have hin (x : Ω) : (∫ y, (f x-f y)^2 ∂μ) =
      (f x)^2 - 2*f x*(∫ y, f y ∂μ) + ∫ y, (f y)^2 ∂μ := by
    have heq : (fun y => (f x-f y)^2) =
        (fun y => (f x)^2 - 2*f x*f y + (f y)^2) := by
      funext y; ring
    rw [heq]
    have hsub : Integrable (fun y => (f x)^2 - 2*f x*f y) μ :=
      (integrable_const _).sub (hi.const_mul (2*f x))
    rw [integral_add hsub hs,
      integral_sub (integrable_const ((f x)^2)) (hi.const_mul (2*f x)),
      integral_const_mul]
    simp
  simp_rw [hin]
  have hmul : Integrable (fun x => 2*f x*(∫ y, f y ∂μ)) μ :=
    (hi.const_mul 2).mul_const _
  have hsub : Integrable (fun x => (f x)^2 - 2*f x*(∫ y, f y ∂μ)) μ := hs.sub hmul
  rw [integral_add hsub (integrable_const (∫ y, (f y)^2 ∂μ))]
  rw [integral_sub hs hmul, variance_eq_sub hf]
  simp only [Pi.pow_apply]
  rw [show (fun x => 2*f x*(∫ y, f y ∂μ)) =
    (fun x => f x*(2*(∫ y, f y ∂μ))) by funext x; ring]
  rw [integral_mul_const]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

/-- Pairwise oscillation controls root variance without choosing a center. -/
theorem variance_le_oscillation {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} {C : ℝ} (hf : MemLp f 2 μ)
    (hC : ∀ x y, |f x-f y| ≤ C) : variance f μ ≤ C^2/2 := by
  have hp : ∀ x y, (f x-f y)^2 ≤ C^2 := by
    intro x y
    have h := hC x y
    nlinarith [sq_nonneg (C - |f x-f y|), sq_abs (f x-f y), abs_nonneg (f x-f y)]
  have hb : ∀ x, (∫ y, (f x-f y)^2 ∂μ) ≤ C^2 := by
    intro x
    have hsub : MemLp (fun y => f x - f y) 2 μ := (memLp_const (f x)).sub hf
    simpa using integral_mono hsub.integrable_sq (integrable_const (C^2)) (hp x)
  have hint : Integrable (fun x => ∫ y, (f x-f y)^2 ∂μ) μ := by
    have hprod : MemLp (fun z : Ω × Ω => f z.1 - f z.2) 2 (μ.prod μ) :=
      (hf.comp_fst μ).sub (hf.comp_snd μ)
    exact hprod.integrable_sq.integral_prod_left
  have h := integral_mono hint (integrable_const (C^2)) hb
  rw [variance_two_copies hf] at h
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  linarith

end DilutedSpinGlass

namespace DilutedSpinGlass

variable {Ω Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
    {μ : Measure Ω} {ν : Measure Λ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Uniform bounds survive averaging a physical root coordinate. -/
theorem abs_integral_le_bound {f : Ω → ℝ} {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    |∫ x, f x ∂μ| ≤ B := by
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using norm_integral_le_of_norm_le_const
    (μ := μ) (f := f) (C := B) (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hB x))

/-- Total variance for a bounded measurable function of two independent root blocks. -/
theorem variance_prod_decomposition {f : Ω × Λ → ℝ} {B : ℝ}
    (hf : Measurable f) (hB : ∀ x, |f x| ≤ B) :
    variance f (μ.prod ν) =
      (∫ x, variance (fun y => f (x,y)) ν ∂μ) +
        variance (fun x => ∫ y, f (x,y) ∂ν) μ := by
  have hLp := bounded_memLp (μ := μ.prod ν) hf hB 2
  have hLp' (x : Ω) : MemLp (fun y => f (x,y)) 2 ν :=
    bounded_memLp (hf.comp (measurable_const.prodMk measurable_id)) (fun y => hB (x,y)) 2
  have hm : Measurable (fun x => ∫ y, f (x,y) ∂ν) :=
    hf.stronglyMeasurable.integral_prod_right'.measurable
  have hmLp : MemLp (fun x => ∫ y, f (x,y) ∂ν) 2 μ :=
    bounded_memLp hm (fun x => abs_integral_le_bound (fun y => hB (x,y))) 2
  have hint : Integrable f (μ.prod ν) := hLp.integrable (by norm_num)
  rw [variance_eq_sub hLp, variance_eq_sub hmLp]
  simp_rw [variance_eq_sub (hLp' _)]
  simp only [Pi.pow_apply]
  rw [integral_sub hLp.integrable_sq.integral_prod_left hmLp.integrable_sq,
    integral_prod _ hint, integral_prod _ hLp.integrable_sq]
  ring

/-- An independent block average preserves each bounded-difference constant. -/
theorem integral_oscillation {f : Ω × Λ → ℝ} {B C : ℝ}
    (hf : Measurable f) (hB : ∀ z, |f z| ≤ B)
    (hC : ∀ x x' y, |f (x,y)-f (x',y)| ≤ C) :
    ∀ x x', |(∫ y, f (x,y) ∂ν) - (∫ y, f (x',y) ∂ν)| ≤ C := by
  intro x x'
  have hi (z : Ω) : Integrable (fun y => f (z,y)) ν :=
    (bounded_memLp (hf.comp (measurable_const.prodMk measurable_id))
      (fun y => hB (z,y)) 1).integrable le_rfl
  rw [← integral_sub (hi x) (hi x')]
  exact abs_integral_le_bound (hC x x')

end DilutedSpinGlass

namespace DilutedSpinGlass

universe u

/-- Bounded coordinate replacements give a variance bound additive in the
number of independent root coordinates, not quadratic in that number. -/
theorem root_variance_bound {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (μ : Fin n → Measure Ω) [hμ : ∀ i, IsProbabilityMeasure (μ i)]
    {F : RootPath Ω n → ℝ} {B : ℝ} (hF : Measurable F) (hB : ∀ x, |F x| ≤ B)
    (C : Fin n → ℝ)
    (hC : ∀ (i : Fin n) x y, |F x-F (replaceRoot n x i y)| ≤ C i) :
    variance F (rootLaw n μ) ≤ ∑ i, (C i)^2/2 := by
  induction n with
  | zero =>
    rw [variance_eq_integral hF.aemeasurable]
    simp [rootLaw]
  | succ n ih =>
    let ν := rootLaw n (fun i => μ i.succ)
    have : ∀ i : Fin n, IsProbabilityMeasure (μ i.succ) := fun i => hμ i.succ
    have ht (x : Ω) : variance (fun y => F (x,y)) ν ≤ ∑ i : Fin n, (C i.succ)^2/2 := by
      apply ih (fun i => μ i.succ)
        (hF.comp (measurable_const.prodMk measurable_id)) (fun y => hB (x,y))
        (fun i => C i.succ)
      intro i y z
      simpa [replaceRoot, Function.comp_def] using hC i.succ (x,y) z
    have hm : Measurable (fun x => ∫ y, F (x,y) ∂ν) :=
      hF.stronglyMeasurable.integral_prod_right'.measurable
    have hmLp : MemLp (fun x => ∫ y, F (x,y) ∂ν) 2 (μ 0) :=
      bounded_memLp hm (fun x => abs_integral_le_bound (fun y => hB (x,y))) 2
    have hosc : ∀ x x', |(∫ y, F (x,y) ∂ν)-(∫ y, F (x',y) ∂ν)| ≤ C 0 := by
      apply integral_oscillation hF hB
      intro x x' y
      simpa [replaceRoot] using hC 0 (x,y) x'
    have hroot := variance_le_oscillation hmLp hosc
    have hLp := bounded_memLp (μ := (μ 0).prod ν) hF hB 2
    have hs (x : Ω) : MemLp (fun y => F (x,y)) 2 ν :=
      bounded_memLp (hF.comp (measurable_const.prodMk measurable_id)) (fun y => hB (x,y)) 2
    have hint : Integrable (fun x => variance (fun y => F (x,y)) ν) (μ 0) := by
      simp_rw [variance_eq_sub (hs _)]
      exact hLp.integrable_sq.integral_prod_left.sub hmLp.integrable_sq
    have hintBound := integral_mono hint (integrable_const (∑ i : Fin n, (C i.succ)^2/2)) ht
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hintBound
    change variance F ((μ 0).prod ν) ≤ _
    rw [variance_prod_decomposition hF hB, Fin.sum_univ_succ]
    linarith

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MarkedPoisson
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.DilutedSpinGlass.compoundRootLaw_prob _root_.OAI.DilutedSpinGlass.fullRootLaw_prob _root_.OAI.DilutedSpinGlass.rootPathCountable _root_.OAI.DilutedSpinGlass.rootPathSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass

theorem poissonWeight_succ_mul (r : ℝ≥0) (n : ℕ) :
    poissonWeight r (n+1) * (n+1 : ℕ) = (r : ℝ) * poissonWeight r n := by
  unfold poissonWeight
  rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
  have hn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hn1 : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

/-- Poisson add-one (the count part of pert:palm), including zero rate. -/
theorem poisson_add_one (r : ℝ≥0) (f : ℕ → ℝ)
    (hf : Integrable (fun n => f (n+1)) (poissonMeasure r)) :
    (∫ n : ℕ, (n : ℝ) * f n ∂poissonMeasure r) =
      (r : ℝ) * ∫ n : ℕ, f (n+1) ∂poissonMeasure r := by
  have hs := (hasSum_integral_poissonMeasure hf).mul_left (r : ℝ)
  simp only [smul_eq_mul] at hs
  have ht : HasSum (fun n => poissonWeight r (n+1) * ((n+1 : ℕ) : ℝ) * f (n+1))
      ((r : ℝ) * ∫ n : ℕ, f (n+1) ∂poissonMeasure r) := by
    simp_rw [poissonWeight_succ_mul]
    simpa only [poissonWeight, mul_assoc] using hs
  have ht' := HasSum.zero_add (f := fun n => poissonWeight r n * (n : ℝ) * f n) ht
  simp only [Nat.cast_zero, mul_zero, zero_mul, zero_add] at ht'
  rw [integral_poissonMeasure]
  simpa only [smul_eq_mul, ← mul_assoc, poissonWeight] using ht'.tsum_eq

/-- Integrability of the count is proved from the same add-one recurrence. -/
theorem poisson_integrable_count (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  have hs := (hasSum_one_poissonMeasure r).mul_left (r : ℝ)
  have ht : HasSum (fun n => poissonWeight r (n+1) * ((n+1 : ℕ) : ℝ)) r := by
    simp_rw [poissonWeight_succ_mul]
    unfold poissonWeight
    simpa only [mul_one] using hs
  have ht' := HasSum.zero_add (f := fun n => poissonWeight r n * (n : ℝ)) ht
  simp only [Nat.cast_zero, mul_zero, zero_add] at ht'
  simpa only [Real.norm_natCast, poissonWeight] using ht'.summable

@[simp] theorem poisson_mean (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) ∂poissonMeasure r) = r := by
  simpa using poisson_add_one r (fun _ => 1) (integrable_const 1)

theorem poisson_integrable_linear (r : ℝ≥0) {f : ℕ → ℝ} {A B : ℝ}
    (h : ∀ n, |f n| ≤ A + B*n) : Integrable f (poissonMeasure r) := by
  apply ((integrable_const A).add ((poisson_integrable_count r).const_mul B)).mono
    (StronglyMeasurable.of_discrete.aestronglyMeasurable)
  exact ae_of_all _ (fun n => (h n).trans (le_abs_self _))

theorem poisson_integrable_count_sq (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)^2) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  have hnext : Integrable (fun n : ℕ => ((n+1 : ℕ) : ℝ)) (poissonMeasure r) := by
    apply poisson_integrable_linear r (A := 1) (B := 1)
    intro n
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ))]
    simp only [Nat.cast_add, Nat.cast_one, one_mul]
    exact le_of_eq (add_comm _ _)
  have hs := (hasSum_integral_poissonMeasure hnext).mul_left (r : ℝ)
  simp only [smul_eq_mul] at hs
  have ht : Summable (fun n => poissonWeight r (n+1) * ((n+1 : ℕ) : ℝ)^2) := by
    simp_rw [pow_two, ← mul_assoc, poissonWeight_succ_mul]
    simpa only [poissonWeight, mul_assoc] using hs.summable
  have ht' := Summable.comp_nat_add (f := fun n => poissonWeight r n * (n : ℝ)^2) (k := 1) ht
  simpa only [Real.norm_eq_abs, abs_sq, poissonWeight] using ht'

@[simp] theorem poisson_second_moment (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ)^2 ∂poissonMeasure r) = (r : ℝ)^2 + r := by
  have hi : Integrable (fun n : ℕ => ((n+1 : ℕ) : ℝ)) (poissonMeasure r) := by
    apply poisson_integrable_linear r (A := 1) (B := 1)
    intro n
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ))]
    simp only [Nat.cast_add, Nat.cast_one, one_mul]
    exact le_of_eq (add_comm _ _)
  have h := poisson_add_one r (fun n => (n : ℝ)) hi
  simp only [← pow_two, Nat.cast_add, Nat.cast_one] at h
  rw [integral_add (poisson_integrable_count r) (integrable_const 1), poisson_mean,
    integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  nlinarith

theorem poisson_variance (r : ℝ≥0) :
    (∫ n : ℕ, ((n : ℝ) - r)^2 ∂poissonMeasure r) = r := by
  have heq : (fun n : ℕ => ((n : ℝ)-r)^2) =
      (fun n : ℕ => (n : ℝ)^2 - 2*(r : ℝ)*(n : ℝ) + (r : ℝ)^2) := by
    funext n
    ring
  rw [heq]
  have hi : Integrable (fun n : ℕ => (n : ℝ)^2 - 2*(r : ℝ)*n) (poissonMeasure r) :=
    (poisson_integrable_count_sq r).sub ((poisson_integrable_count r).const_mul (2*(r : ℝ)))
  rw [integral_add hi (integrable_const ((r : ℝ)^2)),
    integral_sub (poisson_integrable_count_sq r) ((poisson_integrable_count r).const_mul (2*r)),
    integral_const_mul, poisson_second_moment, poisson_mean, integral_const,
    probReal_univ, smul_eq_mul, one_mul]
  ring

end DilutedSpinGlass

namespace DilutedSpinGlass

/-- A quadratic envelope suffices; no exponential moment is used. -/
theorem poisson_integrable_quadratic (r : ℝ≥0) {f : ℕ → ℝ} {A B : ℝ}
    (h : ∀ n, |f n| ≤ A + B*(n : ℝ)^2) : Integrable f (poissonMeasure r) := by
  apply ((integrable_const A).add ((poisson_integrable_count_sq r).const_mul B)).mono
    (StronglyMeasurable.of_discrete.aestronglyMeasurable)
  exact ae_of_all _ (fun n => (h n).trans (le_abs_self _))

/-- Lipschitz sequences have a square-integrable Poisson law. -/
theorem poisson_memLp_lipschitz (r : ℝ≥0) {f : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ n m, |f n-f m| ≤ C*|(n : ℝ)-(m : ℝ)|) :
    MemLp f 2 (poissonMeasure r) := by
  apply (memLp_two_iff_integrable_sq StronglyMeasurable.of_discrete.aestronglyMeasurable).mpr
  apply poisson_integrable_quadratic r (A := 2*(f 0)^2) (B := 2*C^2)
  intro n
  have h := hL n 0
  simp only [Nat.cast_zero, sub_zero, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)] at h
  have hh : |f n| ≤ C*(n : ℝ)+|f 0| := by
    calc |f n| = |(f n-f 0)+f 0| := by rw [sub_add_cancel]
         _ ≤ |f n-f 0| + |f 0| := abs_add_le _ _
         _ ≤ C*(n : ℝ)+|f 0| := by linarith
  have hb : 0 ≤ C*(n : ℝ)+|f 0| := by positivity
  rw [abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_abs (f n), sq_abs (f 0),
    sq_nonneg (C*(n : ℝ)-|f 0|), mul_nonneg (sub_nonneg.mpr hh) (add_nonneg hb (abs_nonneg (f n)))]

/-- Poisson random-coordinate count variance: a count-Lipschitz logarithm
has fluctuations of order sqrt(rate), not order rate. -/
theorem poisson_variance_lipschitz (r : ℝ≥0) {f : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ n m, |f n-f m| ≤ C*|(n : ℝ)-(m : ℝ)|) :
    variance f (poissonMeasure r) ≤ C^2 * (r : ℝ) := by
  have hf := poisson_memLp_lipschitz r hC hL
  have hn : MemLp (fun n : ℕ => (n : ℝ)) 2 (poissonMeasure r) :=
    (memLp_two_iff_integrable_sq StronglyMeasurable.of_discrete.aestronglyMeasurable).mpr
      (poisson_integrable_count_sq r)
  have hp : ∀ n m : ℕ, (f n-f m)^2 ≤ C^2*((n : ℝ)-(m : ℝ))^2 := by
    intro n m
    have h := hL n m
    have hnon : 0 ≤ C*|(n : ℝ)-(m : ℝ)| := mul_nonneg hC (abs_nonneg _)
    nlinarith [sq_abs (f n-f m), sq_abs ((n : ℝ)-(m : ℝ)),
      mul_nonneg (sub_nonneg.mpr h) (add_nonneg hnon (abs_nonneg (f n-f m)))]
  let μ := poissonMeasure r
  have hint (n : ℕ) := integral_mono
    ((memLp_const (f n)).sub hf).integrable_sq
    (((memLp_const (n : ℝ)).sub hn).integrable_sq.const_mul (C^2)) (hp n)
  have hfprod : MemLp (fun z : ℕ × ℕ => f z.1-f z.2) 2 (μ.prod μ) :=
    (hf.comp_fst μ).sub (hf.comp_snd μ)
  have hnprod : MemLp (fun z : ℕ × ℕ => (z.1 : ℝ)-(z.2 : ℝ)) 2 (μ.prod μ) :=
    (hn.comp_fst μ).sub (hn.comp_snd μ)
  have h := integral_mono hfprod.integrable_sq.integral_prod_left
    (hnprod.integrable_sq.const_mul (C^2)).integral_prod_left hint
  simp_rw [integral_const_mul] at h
  rw [variance_two_copies hf, variance_two_copies hn,
    variance_eq_integral (Measurable.of_discrete (f := fun n : ℕ => (n : ℝ))).aemeasurable, poisson_mean, poisson_variance] at h
  nlinarith

end DilutedSpinGlass

namespace DilutedSpinGlass

/-- Adding one root coordinate gives the full Lipschitz bound in the count. -/
theorem nat_lipschitz_of_step {f : ℕ → ℝ} {C : ℝ} (_hC : 0 ≤ C)
    (h : ∀ n, |f (n+1)-f n| ≤ C) : ∀ n m, |f n-f m| ≤ C*|(n : ℝ)-(m : ℝ)| := by
  have hle : ∀ n m, n ≤ m → |f m-f n| ≤ C*((m : ℝ)-(n : ℝ)) := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => simp
    | succ m hnm ih =>
      have ha : |f (m+1)-f n| ≤ |f (m+1)-f m|+|f m-f n| := by
        calc
          |f (m+1)-f n| = |(f (m+1)-f m)+(f m-f n)| := by congr 1; ring
          _ ≤ _ := abs_add_le _ _
      push_cast
      nlinarith [h m]
  intro n m
  rcases le_total n m with hnm | hmn
  · rw [abs_sub_comm (f n), abs_sub_comm (n : ℝ), abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hnm : (n : ℝ) ≤ m))]
    exact hle n m hnm
  · rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hmn : (m : ℝ) ≤ n))]
    exact hle m n hmn

/-- Centering at an arbitrary constant separates conditional variance and
squared conditional-mean displacement. -/
theorem integral_sq_sub_center {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) (a : ℝ) :
    (∫ x, (f x-a)^2 ∂μ) = variance f μ + ((∫ x, f x ∂μ)-a)^2 := by
  have hi := hf.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have heq : (fun x => (f x-a)^2) = (fun x => f x^2-2*a*f x+a^2) := by funext x; ring
  rw [heq]
  have hs : Integrable (fun x => f x^2-2*a*f x) μ := hf.integrable_sq.sub (hi.const_mul (2*a))
  rw [integral_add hs (integrable_const _), integral_sub hf.integrable_sq (hi.const_mul (2*a)),
    integral_const_mul, integral_const, probReal_univ, smul_eq_mul, one_mul, variance_eq_sub hf]
  simp only [Pi.pow_apply]
  ring

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Actual random-count root means inherit the addition/deletion constant. -/
theorem rootAverage_step {F : (n : ℕ) → RootPath Ω n → ℝ} {B : ℕ → ℝ} {D : ℝ}
    (hF : ∀ n, Measurable (F n)) (hB : ∀ n x, |F n x| ≤ B n)
    (hadd : ∀ n x y, |F (n+1) (x,y) - F n y| ≤ D) (n : ℕ) :
    |rootAverage μ F (n+1)-rootAverage μ F n| ≤ D := by
  let ν := rootLaw n (fun _ : Fin n => μ)
  have hp : Integrable (F (n+1)) (μ.prod ν) :=
    (bounded_memLp (hF (n+1)) (hB (n+1)) 1).integrable le_rfl
  have hi : Integrable (F n) ν := (bounded_memLp (hF n) (hB n) 1).integrable le_rfl
  have hs (x : Ω) : Integrable (fun y => F (n+1) (x,y)) ν :=
    (bounded_memLp ((hF (n+1)).comp (measurable_const.prodMk measurable_id))
      (fun y => hB (n+1) (x,y)) 1).integrable le_rfl
  change |(∫ z, F (n+1) z ∂μ.prod ν) - ∫ y, F n y ∂ν| ≤ D
  rw [integral_prod _ hp]
  have hc : (∫ _ : Ω, (∫ y, F n y ∂ν) ∂μ) = ∫ y, F n y ∂ν := by simp
  rw [← hc, ← integral_sub hp.integral_prod_left (integrable_const _)]
  apply abs_integral_le_bound
  intro x
  rw [← integral_sub (hs x) hi]
  exact abs_integral_le_bound (hadd n x)


end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ProductTowers
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge

namespace DilutedSpinGlass.KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

/-- Conditional power means commute with literal relabeling of every hidden
mark variable. This is needed for the physical Palm exchangeability. -/
theorem backwardLog_transport (e : Ω ≃ Λ) (n : ℕ) (T : KernelTower Ω n)
    (m : Fin n → ℝ) (f : FinitePath Λ n → ℝ) :
    backwardLog n (transport e n T) m f =
      backwardLog n T m (f ∘ pathEquiv e n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [backwardLog, transport]
    have he : (fun a : Λ => backwardLog n (transport e n (T.2 (e.symm a)))
        (fun j => m j.succ) (fun y => f (a,y))) =
      (fun a : Λ => backwardLog n (T.2 (e.symm a))
        (fun j => m j.succ) ((fun y => f (a,y)) ∘ pathEquiv e n)) :=
      funext (fun a => ih (T.2 (e.symm a)) (fun j => m j.succ) (fun y => f (a,y)))
    rw [he, FiniteLaw.logMean_transport]
    congr 1
    funext a
    simp only [Function.comp_def, Equiv.symm_apply_apply, pathEquiv_cons]

end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.FiniteLaw
variable {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]

theorem eq_of_weights {P Q : FiniteLaw Ω} (h : ∀ x, P.weight x = Q.weight x) : P = Q := by
  cases P
  cases Q
  congr
  exact funext h

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.FiniteLaw
variable {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]

/-- A mark block not present in a log weight integrates out, before or after
any one power-mean tilt. -/
theorem logMean_bind_fst (P : FiniteLaw Ω) (Q : FiniteLaw Λ) (m : ℝ) (f : Ω → ℝ) :
    (P.bind (fun _ => Q)).logMean m (fun z => f z.1) = P.logMean m f := by
  simp [logMean, expMoment]

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

theorem backwardLog_prod_fst (n : ℕ) (T : KernelTower Ω n) (U : KernelTower Λ n)
    (m : Fin n → ℝ) (f : FinitePath Ω n → ℝ) :
    backwardLog n (prod n T U) m (fun y => f (pathFst n y)) = backwardLog n T m f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [backwardLog, prod, pathFst]
    have hh : (fun z : Ω × Λ => backwardLog n
        (prod n (T.2 z.1) (U.2 z.2)) (fun j => m j.succ)
        (fun y => f (z.1, pathFst n y))) =
        (fun z : Ω × Λ => backwardLog n (T.2 z.1) (fun j => m j.succ)
          (fun y => f (z.1,y))) := by
      funext z
      exact ih (T.2 z.1) (U.2 z.2) (fun j => m j.succ) (fun y => f (z.1,y))
    rw [hh]
    exact FiniteLaw.logMean_bind_fst T.1 U.1 (m 0)
      (fun x => backwardLog n (T.2 x) (fun j => m j.succ) (fun y => f (x,y)))

end DilutedSpinGlass.KernelTower

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PoissonVariance
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.DilutedSpinGlass.compoundRootLaw_prob _root_.OAI.DilutedSpinGlass.fullRootLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge

namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem rootArray_replace {I : Type*} (n : ℕ) (x : RootPath I n) (j : Fin n) (i : I) :
    rootArray n (replaceRoot n x j i) = Function.update (rootArray n x) j i := by
  classical
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · funext q
      refine Fin.cases ?_ (fun q => ?_) q <;> simp [rootArray, replaceRoot]
    · funext q
      refine Fin.cases ?_ (fun q => ?_) q
      · simp [rootArray, replaceRoot, Function.update_of_ne (Ne.symm (Fin.succ_ne_zero j))]
      · simp only [rootArray, replaceRoot, Fin.cases_succ, Fin.cons_succ, ih]
        by_cases h : q = j
        · subst q; simp
        · simp [h, show q.succ ≠ j.succ by simpa using h]

end DilutedSpinGlass

namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- A parameter in a Poisson root average stays measurable, despite the
count-dependent dimension of the actual root state. -/
theorem measurable_poissonRootAverage (r : ℝ≥0)
    {F : X → (n : ℕ) → RootPath Ω n → ℝ}
    (hF : ∀ n, Measurable (fun z : X × RootPath Ω n => F z.1 n z.2)) :
    Measurable (fun x => poissonRootAverage μ r (F x)) := by
  have hm : Measurable (fun z : X × ℕ => rootAverage μ (F z.1) z.2) := by
    apply measurable_from_prod_countable_left
    intro n
    change Measurable (fun x => ∫ y, F x n y ∂rootLaw n (fun _ => μ))
    exact (hF n).stronglyMeasurable.integral_prod_right'.measurable
  change Measurable (fun x => ∫ n, rootAverage μ (F x) n ∂poissonMeasure r)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- The actual random-count squared displacement around any center. Both
conditional root fluctuations and random-count fluctuations are retained. -/
theorem poisson_root_second_moment (r : ℝ≥0)
    {F : (n : ℕ) → RootPath Ω n → ℝ} {B : ℕ → ℝ} {C D : ℝ}
    (hF : ∀ n, Measurable (F n)) (hB : ∀ n x, |F n x| ≤ B n)
    (hD : 0 ≤ D)
    (hrep : ∀ n (i : Fin n) x y, |F n x-F n (replaceRoot n x i y)| ≤ C)
    (hadd : ∀ n x y, |F (n+1) (x,y)-F n y| ≤ D) (c : ℝ) :
    (∫ n : ℕ, ∫ x, (F n x-c)^2 ∂rootLaw n (fun _ => μ) ∂poissonMeasure r) ≤
      (C^2/2+D^2)*(r : ℝ) + (poissonRootAverage μ r F-c)^2 := by
  have hvar (n : ℕ) : variance (F n) (rootLaw n (fun _ => μ)) ≤ C^2/2*(n : ℝ) := by
    have h := root_variance_bound n (fun _ => μ) (hF n) (hB n) (fun _ => C) (hrep n)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm] using h
  have hvint : Integrable (fun n => variance (F n) (rootLaw n (fun _ => μ))) (poissonMeasure r) := by
    apply poisson_integrable_linear r (A := 0) (B := C^2/2)
    intro n
    rw [abs_of_nonneg (variance_nonneg _ _), zero_add]
    exact hvar n
  have hmeanLp := poisson_memLp_lipschitz r hD
    (nat_lipschitz_of_step hD (rootAverage_step μ hF hB hadd))
  have hcount := poisson_variance_lipschitz r hD
    (nat_lipschitz_of_step hD (rootAverage_step μ hF hB hadd))
  simp_rw [integral_sq_sub_center (bounded_memLp (hF _) (hB _) 2)]
  change (∫ n, variance (F n) (rootLaw n (fun _ => μ)) + (rootAverage μ F n-c)^2
    ∂poissonMeasure r) ≤ _
  have hsq : Integrable (fun n => (rootAverage μ F n-c)^2) (poissonMeasure r) :=
    (hmeanLp.sub (memLp_const c)).integrable_sq
  rw [integral_add hvint hsq,
    integral_sq_sub_center hmeanLp c]
  have hi := integral_mono hvint ((poisson_integrable_count r).const_mul (C^2/2)) hvar
  rw [integral_const_mul,poisson_mean] at hi
  change _ ≤ (C^2/2+D^2)*(r : ℝ) + ((∫ n, rootAverage μ F n ∂poissonMeasure r)-c)^2
  nlinarith

/-- A linear root bound is sufficient for all count averages in the physical
model; no bounded support for the Poisson count is introduced. -/
theorem poissonRootAverage_bound (r : ℝ≥0)
    {F : (n : ℕ) → RootPath Ω n → ℝ} {A D : ℝ}
    (hB : ∀ n x, |F n x| ≤ A+D*n) :
    |poissonRootAverage μ r F| ≤ A+D*(r : ℝ) := by
  have hm (n : ℕ) : |rootAverage μ F n| ≤ A+D*n := abs_integral_le_bound (hB n)
  have hi : Integrable (rootAverage μ F) (poissonMeasure r) :=
    poisson_integrable_linear r hm
  have h := integral_mono (hi.norm) ((integrable_const A).add ((poisson_integrable_count r).const_mul D)) hm
  simp only [Real.norm_eq_abs,Pi.add_apply] at h
  rw [integral_add (integrable_const _) ((poisson_integrable_count r).const_mul D),
    integral_const_mul,poisson_mean] at h
  have hnorm := norm_integral_le_integral_norm (μ := poissonMeasure r) (f := rootAverage μ F)
  simpa only [poissonRootAverage,Real.norm_eq_abs,integral_const,probReal_univ,smul_eq_mul,one_mul] using
    hnorm.trans h

/-- Uniform stability passes through the entire marked-Poisson root law. -/
theorem poissonRootAverage_stability (r : ℝ≥0)
    {F G : (n : ℕ) → RootPath Ω n → ℝ} {A B D : ℝ}
    (hF : ∀ n, Measurable (F n)) (hG : ∀ n, Measurable (G n))
    (hBF : ∀ n x, |F n x| ≤ A+B*n) (hBG : ∀ n x, |G n x| ≤ A+B*n)
    (hdiff : ∀ n x, |F n x-G n x| ≤ D) :
    |poissonRootAverage μ r F-poissonRootAverage μ r G| ≤ D := by
  have hiF : Integrable (rootAverage μ F) (poissonMeasure r) :=
    poisson_integrable_linear r (fun n => abs_integral_le_bound (hBF n))
  have hiG : Integrable (rootAverage μ G) (poissonMeasure r) :=
    poisson_integrable_linear r (fun n => abs_integral_le_bound (hBG n))
  unfold poissonRootAverage
  rw [← integral_sub hiF hiG]
  apply abs_integral_le_bound
  intro n
  unfold rootAverage
  rw [← integral_sub ((bounded_memLp (hF n) (hBF n) 1).integrable le_rfl)
    ((bounded_memLp (hG n) (hBG n) 1).integrable le_rfl)]
  exact abs_integral_le_bound (hdiff n)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_Perturbations
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass.KernelTower
variable {Ω : Type} [Fintype Ω]

omit [Fintype Ω] in
theorem perturb_factor_lower {L n : ℕ} (D E : Fin n → FinitePath Ω L → ℝ)
    (hD : ∀ q y, |D q y| ≤ 1) (hE : ∀ q y, |E q y| ≤ 1)
    {t u : ℝ} (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) (q : Fin n) (y : FinitePath Ω L) :
    (1:ℝ)/2 ≤ 1+t*D q y+u*E q y := by
  have ht' := mul_le_mul_of_nonneg_left (hD q y) (abs_nonneg t)
  have hu' := mul_le_mul_of_nonneg_left (hE q y) (abs_nonneg u)
  rw [← abs_mul, mul_one] at ht' hu'
  linarith [(abs_le.mp (ht'.trans ht)).1, (abs_le.mp (hu'.trans hu)).1]

omit [Fintype Ω] in
theorem hasDerivAt_perturbLog {L n : ℕ} (base : FinitePath Ω L → ℝ)
    (D E : Fin n → FinitePath Ω L → ℝ) (t u : ℝ) (y : FinitePath Ω L)
    (hp : ∀ q, 0 < 1+t*D q y+u*E q y) :
    HasDerivAt (fun v => perturbLog base D E t v y) (perturbScore D E t u y) u := by
  have hh (q : Fin n) := (((hasDerivAt_id u).mul_const (E q y)).const_add
    (1+t*D q y)).log (ne_of_gt (hp q))
  simpa only [perturbLog, perturbScore, id_eq, one_mul] using
    (HasDerivAt.fun_sum (fun q (_ : q ∈ (Finset.univ : Finset (Fin n))) => hh q)).const_add (base y)

omit [Fintype Ω] in
theorem hasDerivAt_perturbScore {L n : ℕ}
    (D E : Fin n → FinitePath Ω L → ℝ) (t u : ℝ) (y : FinitePath Ω L)
    (hp : ∀ q, 0 < 1+t*D q y+u*E q y) :
    HasDerivAt (fun v => perturbScore D E t v y) (perturbCurvature D E t u y) u := by
  have hh (q : Fin n) := (hasDerivAt_const u (E q y)).div
    (((hasDerivAt_id u).mul_const (E q y)).const_add (1+t*D q y)) (ne_of_gt (hp q))
  have hsum := HasDerivAt.fun_sum (fun q (_ : q ∈ (Finset.univ : Finset (Fin n))) => hh q)
  change HasDerivAt (fun v => perturbScore D E t v y) _ u at hsum
  apply hsum.congr_deriv
  simp only [id_eq, one_mul, perturbCurvature, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro q _
  simp only [div_pow]
  ring

omit [Fintype Ω] in
theorem perturb_fraction_bound {L n : ℕ} (D E : Fin n → FinitePath Ω L → ℝ)
    (hD : ∀ q y, |D q y| ≤ 1) (hE : ∀ q y, |E q y| ≤ 1)
    {t u : ℝ} (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) (q : Fin n) (y : FinitePath Ω L) :
    |E q y / (1+t*D q y+u*E q y)| ≤ 2 := by
  have hb := perturb_factor_lower D E hD hE ht hu q y
  have hp : 0 < 1+t*D q y+u*E q y := by linarith
  rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]
  linarith [hE q y]

omit [Fintype Ω] in
theorem perturbScore_bound {L n : ℕ} (D E : Fin n → FinitePath Ω L → ℝ)
    (hD : ∀ q y, |D q y| ≤ 1) (hE : ∀ q y, |E q y| ≤ 1)
    {t u : ℝ} (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) (y : FinitePath Ω L) :
    |perturbScore D E t u y| ≤ 2*n := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    (∑ q, |E q y / (1+t*D q y+u*E q y)|) ≤ ∑ _q : Fin n, (2:ℝ) :=
      Finset.sum_le_sum (fun q _ => perturb_fraction_bound D E hD hE ht hu q y)
    _ = _ := by simp [mul_comm]

omit [Fintype Ω] in
theorem perturbCurvature_bounds {L n : ℕ} (D E : Fin n → FinitePath Ω L → ℝ)
    (hD : ∀ q y, |D q y| ≤ 1) (hE : ∀ q y, |E q y| ≤ 1)
    {t u : ℝ} (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) (y : FinitePath Ω L) :
    -4*n ≤ perturbCurvature D E t u y ∧ perturbCurvature D E t u y ≤ 0 := by
  have hsq (q : Fin n) : (E q y / (1+t*D q y+u*E q y))^2 ≤ 4 := by
    have hh := abs_le.mp (perturb_fraction_bound D E hD hE ht hu q y)
    nlinarith
  have hh := Finset.sum_le_sum (fun q (_ : q ∈ (Finset.univ : Finset (Fin n))) => hsq q)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  constructor
  · dsimp [perturbCurvature]
    linarith
  · exact neg_nonpos.mpr (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

 
theorem perturb_thermal_variance {L n : ℕ} (T : KernelTower Ω L) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (D E : Fin n → FinitePath Ω L → ℝ)
    (hD : ∀ q y, |D q y| ≤ 1) (hE : ∀ q y, |E q y| ≤ 1)
    {t a b c : ℝ} (ht : |t| ≤ 1/4) (hab : a ≤ b) (hc : 0 < c)
    (hm : ∀ i, c ≤ m i) (hI : Set.Icc a b ⊆ Set.Icc (-(1:ℝ)/4) (1/4)) :
    (∫ u in a..b, (law L (tilt L T m (perturbLog base D E t u))).covariance
      (perturbScore D E t u) (perturbScore D E t u)) ≤
      (4*n + 4*n*(b-a))/c := by
  have huv (u : ℝ) (hu : u ∈ Set.Icc a b) : |u| ≤ 1/4 := abs_le.mpr ⟨by linarith [(hI hu).1], (hI hu).2⟩
  have hp (u : ℝ) (hu : u ∈ Set.Icc a b) (q : Fin n) (y : FinitePath Ω L) :
      0 < 1+t*D q y+u*E q y := by
    linarith [perturb_factor_lower D E hD hE ht (huv u hu) q y]
  have hh (y : FinitePath Ω L) :
      ContinuousOn (fun u => perturbCurvature D E t u y) (Set.Icc a b) := by
    apply ContinuousOn.neg
    apply continuousOn_finsetSum
    intro q _
    apply ContinuousOn.pow
    apply continuousOn_const.div
    · fun_prop
    · intro u hu
      exact ne_of_gt (hp u hu q y)
  have H := thermal_variance_integral L T m hab hc hm
    (fun u hu y => hasDerivAt_perturbLog base D E t u y (fun q => hp u hu q y))
    (fun u hu y => hasDerivAt_perturbScore D E t u y (fun q => hp u hu q y)) hh
    (fun u hu y => perturbScore_bound D E hD hE ht (huv u hu) y)
    (C := 4*n) (fun u hu y => by
      simpa only [neg_mul] using (perturbCurvature_bounds D E hD hE ht (huv u hu) y).1)
  convert H using 2
  all_goals try with_reducible_and_instances rfl
  ring

end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.KernelTower
variable {Ω : Type} [Fintype Ω]

theorem hasDerivAt_correctedPerturbLog {L n : ℕ} (T : KernelTower Ω L) (m : Fin L → ℝ)
    (hm : ∀ i, m i ≠ 0) (base : FinitePath Ω L → ℝ)
    (D E : Fin n → FinitePath Ω L → ℝ) (t u : ℝ)
    (hp : ∀ q y, 0 < 1+t*D q y+u*E q y) :
    HasDerivAt (correctedPerturbLog T m base D E t)
      (correctedPerturbScore T m base D E t u) u := by
  have h1 := hasDerivAt_backwardLog L T m hm
    (fun y => hasDerivAt_perturbLog base D E t u y (fun q => hp q y))
  have h2 : HasDerivAt (fun v : ℝ => 2*(n:ℝ)*v^2) (4*n*u) u := by
    exact (((hasDerivAt_id u).pow 2).const_mul (2*(n:ℝ))).congr_deriv (by
      norm_num
      ring)
  have h3 := h1.add h2
  change HasDerivAt (fun v => backwardLog L T m (perturbLog base D E t v) + 2*n*v^2)
    ((law L (tilt L T m (perturbLog base D E t u))).expect (perturbScore D E t u) + 4*n*u) u
  exact h3

theorem hasDerivAt_correctedPerturbScore {L n : ℕ} (T : KernelTower Ω L) (m : Fin L → ℝ)
    (hm : ∀ i, m i ≠ 0) (base : FinitePath Ω L → ℝ)
    (D E : Fin n → FinitePath Ω L → ℝ) (t u : ℝ)
    (hp : ∀ q y, 0 < 1+t*D q y+u*E q y) :
    HasDerivAt (correctedPerturbScore T m base D E t)
      ((law L (tilt L T m (perturbLog base D E t u))).expect (perturbCurvature D E t u) +
        varianceEnergy L (tilt L T m (perturbLog base D E t u)) m (perturbScore D E t u) + 4*n) u := by
  have h1 := hasDerivAt_path_score L T m hm
    (fun y => hasDerivAt_perturbLog base D E t u y (fun q => hp q y))
    (fun y => hasDerivAt_perturbScore D E t u y (fun q => hp q y))
  have h2 : HasDerivAt (fun v : ℝ => 4*(n:ℝ)*v) (4*n) u := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id u).const_mul (4*(n:ℝ))
  change HasDerivAt (fun v =>
    (law L (tilt L T m (perturbLog base D E t v))).expect (perturbScore D E t v) + 4*n*v) _ u
  exact h1.add h2

 
theorem correctedPerturbLog_convex {L n : ℕ} (T : KernelTower Ω L) (m : Fin L → ℝ)
    (hm : ∀ i, 0 < m i) (base : FinitePath Ω L → ℝ)
    (D E : Fin n → FinitePath Ω L → ℝ)
    (hD : ∀ q y, |D q y| ≤ 1) (hE : ∀ q y, |E q y| ≤ 1)
    {t : ℝ} (ht : |t| ≤ 1/4) :
    ConvexOn ℝ (Set.Icc (-(1:ℝ)/4) (1/4)) (correctedPerturbLog T m base D E t) := by
  let J := Set.Icc (-(1:ℝ)/4) (1/4)
  have hu (u : ℝ) (h : u ∈ J) : |u| ≤ 1/4 := abs_le.mpr ⟨by linarith [h.1], h.2⟩
  have hp (u : ℝ) (h : u ∈ J) (q : Fin n) (y : FinitePath Ω L) :
      0 < 1+t*D q y+u*E q y := by
    linarith [perturb_factor_lower D E hD hE ht (hu u h) q y]
  have h1 (u : ℝ) (h : u ∈ J) := hasDerivAt_correctedPerturbLog T m
    (fun i => ne_of_gt (hm i)) base D E t u (hp u h)
  have h2 (u : ℝ) (h : u ∈ J) := hasDerivAt_correctedPerturbScore T m
    (fun i => ne_of_gt (hm i)) base D E t u (hp u h)
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
    (fun u h => (h1 u h).continuousAt.continuousWithinAt)
    (fun u h => (h1 u (interior_subset h)).hasDerivWithinAt)
    (fun u h => (h2 u (interior_subset h)).hasDerivWithinAt)
  intro u h
  have hb := (law L (tilt L T m (perturbLog base D E t u))).expect_mono
    (fun y => (perturbCurvature_bounds D E hD hE ht (hu u (interior_subset h)) y).1)
  rw [FiniteLaw.expect_const] at hb
  have hv := varianceEnergy_lower L (tilt L T m (perturbLog base D E t u)) m
    (c := 0) (fun i => (hm i).le) (perturbScore D E t u)
  simp only [zero_mul] at hv
  linarith

end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.FiniteLaw
variable {Ω X : Type} [Fintype Ω] [MeasurableSpace X]

/-- Conditional absolute score fluctuations are controlled by their exact
conditional variance; all randomness is still in the tilted path law. -/
theorem mean_absolute_deviation_sq (P : FiniteLaw Ω) (f : Ω → ℝ) :
    (P.expect (fun x => |f x-P.expect f|))^2 ≤ P.covariance f f := by
  have h := P.sq_expect_le_expect_sq (fun x => |f x-P.expect f|)
  simp only [sq_abs] at h
  rw [P.expect_sq_sub_expect] at h
  simpa only [covariance,pow_two] using h

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.KernelTower
variable {Ω X : Type} [Fintype Ω] [MeasurableSpace X]

theorem measurable_path_expect (L : ℕ) (T : KernelTower Ω L) (m : Fin L → ℝ)
    {f g : X → FinitePath Ω L → ℝ}
    (hf : ∀ y, Measurable (fun x => f x y))
    (hg : ∀ y, Measurable (fun x => g x y)) :
    Measurable (fun x => (law L (tilt L T m (f x))).expect (g x)) := by
  induction L with
  | zero => simpa only [law_zero_expect] using hg ()
  | succ L ih =>
    simp_rw [law_succ_expect (Ω := Ω) L]
    exact T.1.measurable_tilt_expect (m 0)
      (fun a => measurable_backwardLog L (T.2 a) (fun j => m j.succ) (fun b => hf (a,b)))
      (fun a => ih (T.2 a) (fun j => m j.succ) (fun b => hf (a,b)) (fun b => hg (a,b)))

omit [Fintype Ω] [MeasurableSpace X] in
theorem continuousOn_perturbLog {L n : ℕ} (base : FinitePath Ω L → ℝ)
    (D E : Fin n → FinitePath Ω L → ℝ) {t : ℝ} {S : Set ℝ}
    (hp : ∀ u ∈ S, ∀ q y, 0 < 1+t*D q y+u*E q y) (y : FinitePath Ω L) :
    ContinuousOn (fun u => perturbLog base D E t u y) S := by
  apply ContinuousOn.const_add
  apply continuousOn_finsetSum
  intro q _
  apply ContinuousOn.log
  · fun_prop
  · intro u hu
    exact ne_of_gt (hp u hu q y)

omit [Fintype Ω] [MeasurableSpace X] in
theorem continuousOn_perturbScore {L n : ℕ} (D E : Fin n → FinitePath Ω L → ℝ)
    {t : ℝ} {S : Set ℝ} (hp : ∀ u ∈ S, ∀ q y, 0 < 1+t*D q y+u*E q y)
    (y : FinitePath Ω L) :
    ContinuousOn (fun u => perturbScore D E t u y) S := by
  apply continuousOn_finsetSum
  intro q _
  apply continuousOn_const.div
  · fun_prop
  · intro u hu
    exact ne_of_gt (hp u hu q y)

omit [MeasurableSpace X] in
theorem thermalDefect_nonneg {L n : ℕ} (T : KernelTower Ω L) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (D E : Fin n → FinitePath Ω L → ℝ) (t u : ℝ) :
    0 ≤ thermalDefect T m base D E t u :=
  FiniteLaw.expect_nonneg _ (fun _ => abs_nonneg _)

omit [MeasurableSpace X] in
theorem continuousOn_thermalDefect {L n : ℕ} (T : KernelTower Ω L) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (D E : Fin n → FinitePath Ω L → ℝ) {t : ℝ} {S : Set ℝ}
    (hp : ∀ u ∈ S, ∀ q y, 0 < 1+t*D q y+u*E q y) :
    ContinuousOn (thermalDefect T m base D E t) S := by
  apply continuousOn_path_expect
  · exact continuousOn_perturbLog base D E hp
  · intro y
    exact ((continuousOn_perturbScore D E hp y).sub
      (continuousOn_path_expect L T m (continuousOn_perturbLog base D E hp)
        (continuousOn_perturbScore D E hp))).abs

end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.KernelTower
variable {Ω X : Type} [Fintype Ω] [MeasurableSpace X]

omit [Fintype Ω] in
theorem measurable_perturbLog {L n : ℕ}
    {base : X → FinitePath Ω L → ℝ} {D E : X → Fin n → FinitePath Ω L → ℝ}
    {t u : X → ℝ} (hbase : ∀ y, Measurable (fun x => base x y))
    (hD : ∀ q y, Measurable (fun x => D x q y))
    (hE : ∀ q y, Measurable (fun x => E x q y)) (ht : Measurable t) (hu : Measurable u)
    (y : FinitePath Ω L) :
    Measurable (fun x => perturbLog (base x) (D x) (E x) (t x) (u x) y) := by
  apply (hbase y).add
  apply Finset.measurable_sum
  intro q _
  exact ((measurable_const.add (ht.mul (hD q y))).add (hu.mul (hE q y))).log

omit [Fintype Ω] in
theorem measurable_perturbScore {L n : ℕ} {D E : X → Fin n → FinitePath Ω L → ℝ}
    {t u : X → ℝ} (hD : ∀ q y, Measurable (fun x => D x q y))
    (hE : ∀ q y, Measurable (fun x => E x q y)) (ht : Measurable t) (hu : Measurable u)
    (y : FinitePath Ω L) :
    Measurable (fun x => perturbScore (D x) (E x) (t x) (u x) y) := by
  apply Finset.measurable_sum
  intro q _
  exact (hE q y).div ((measurable_const.add (ht.mul (hD q y))).add (hu.mul (hE q y)))

theorem measurable_thermalDefect {L n : ℕ} (T : KernelTower Ω L) (m : Fin L → ℝ)
    {base : X → FinitePath Ω L → ℝ} {D E : X → Fin n → FinitePath Ω L → ℝ}
    {t u : X → ℝ} (hbase : ∀ y, Measurable (fun x => base x y))
    (hD : ∀ q y, Measurable (fun x => D x q y))
    (hE : ∀ q y, Measurable (fun x => E x q y)) (ht : Measurable t) (hu : Measurable u) :
    Measurable (fun x => thermalDefect T m (base x) (D x) (E x) (t x) (u x)) := by
  apply measurable_path_expect
  · exact measurable_perturbLog hbase hD hE ht hu
  · intro y
    exact ((measurable_perturbScore hD hE ht hu y).sub
      (measurable_path_expect L T m (measurable_perturbLog hbase hD hE ht hu)
        (measurable_perturbScore hD hE ht hu))).abs

end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass
open _root_.MeasureTheory intervalIntegral

theorem sq_intervalIntegral_le {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    (∫ u in a..b, f u)^2 ≤ (b-a)*(∫ u in a..b, (f u)^2) := by
  let l := b-a
  let z := ∫ u in a..b, f u
  have hl : 0 < l := sub_pos.mpr hab
  have hi : IntervalIntegrable f volume a b :=
    hf.intervalIntegrable_of_Icc (le_of_lt hab)
  have hi2 : IntervalIntegrable (fun u => (f u)^2) volume a b :=
    (hf.pow 2).intervalIntegrable_of_Icc (le_of_lt hab)
  have hprint (u : ℝ) : (f u-z/l)^2 = (f u)^2-2*(z/l)*f u+(z/l)^2 := by ring
  have h := integral_nonneg (μ := volume) (le_of_lt hab)
    (f := fun u => (f u-z/l)^2) (fun u _ => sq_nonneg _)
  simp_rw [hprint] at h
  rw [integral_add (hi2.sub (hi.const_mul (2*(z/l)))) intervalIntegrable_const,
    integral_sub hi2 (hi.const_mul (2*(z/l))),intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const,smul_eq_mul] at h
  change 0 ≤ (∫ u in a..b, (f u)^2)-2*(z/l)*z+l*(z/l)^2 at h
  have heq : (∫ u in a..b, (f u)^2)-2*(z/l)*z+l*(z/l)^2 =
      (∫ u in a..b, (f u)^2)-z^2/l := by
    field_simp [ne_of_gt hl]
    ring
  rw [heq] at h
  have hh : z^2/l ≤ ∫ u in a..b, (f u)^2 := by linarith
  have hh' := (div_le_iff₀ hl).mp hh
  change z^2 ≤ l*(∫ u in a..b, (f u)^2)
  nlinarith

end DilutedSpinGlass

namespace DilutedSpinGlass.KernelTower
open _root_.MeasureTheory intervalIntegral
variable {Ω : Type} [Fintype Ω]

 
theorem perturb_thermal_absolute {L n : ℕ} (T : KernelTower Ω L) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (D E : Fin n → FinitePath Ω L → ℝ)
    (hD : ∀ q y, |D q y| ≤ 1) (hE : ∀ q y, |E q y| ≤ 1)
    {t a b c : ℝ} (ht : |t| ≤ 1/4) (hab : a < b) (hc : 0 < c)
    (hm : ∀ i, c ≤ m i) (hI : Set.Icc a b ⊆ Set.Icc (-(1:ℝ)/4) (1/4)) :
    (∫ u in a..b, thermalDefect T m base D E t u)^2 ≤
      (b-a)*(4*n+4*n*(b-a))/c := by
  have huv (u : ℝ) (hu : u ∈ Set.Icc a b) : |u| ≤ 1/4 :=
    abs_le.mpr ⟨by linarith [(hI hu).1],(hI hu).2⟩
  have hp (u : ℝ) (hu : u ∈ Set.Icc a b) (q : Fin n) (y : FinitePath Ω L) :
      0 < 1+t*D q y+u*E q y := by
    linarith [perturb_factor_lower D E hD hE ht (huv u hu) q y]
  have hf := continuousOn_perturbLog base D E hp
  have hg := continuousOn_perturbScore D E hp
  have hd := continuousOn_thermalDefect T m base D E hp
  have hcov : ContinuousOn
      (fun u => (law L (tilt L T m (perturbLog base D E t u))).covariance
        (perturbScore D E t u) (perturbScore D E t u)) (Set.Icc a b) := by
    unfold FiniteLaw.covariance
    exact (continuousOn_path_expect L T m hf (fun y => (hg y).mul (hg y))).sub
      ((continuousOn_path_expect L T m hf hg).mul (continuousOn_path_expect L T m hf hg))
  have hb := integral_mono_on (μ := volume) (le_of_lt hab)
    ((hd.pow 2).intervalIntegrable_of_Icc (le_of_lt hab))
    (hcov.intervalIntegrable_of_Icc (le_of_lt hab))
    (fun u _ => (law L (tilt L T m (perturbLog base D E t u))).mean_absolute_deviation_sq
      (perturbScore D E t u))
  have h1 := sq_intervalIntegral_le hab hd
  have h2 := perturb_thermal_variance T m base D E hD hE ht (le_of_lt hab) hc hm hI
  have h3 := mul_le_mul_of_nonneg_left (hb.trans h2) (by linarith : 0 ≤ b-a)
  dsimp only [thermalDefect] at h1 ⊢
  calc
    _ ≤ _ := h1
    _ ≤ _ := by simpa only [mul_div_assoc,Pi.pow_apply,thermalDefect] using h3

end DilutedSpinGlass.KernelTower

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MixtureMeasures
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass

variable {I : Type*} {X : I → Type*} [MeasurableSpace I]
  [∀ i, MeasurableSpace (X i)]

omit [MeasurableSpace I] in
theorem measurable_sigmaUncurry {Y : Type*} [MeasurableSpace Y] {f : (i : I) → X i → Y}
    (hf : ∀ i, Measurable (f i)) : Measurable (fun x : Sigma X => f x.1 x.2) := by
  rw [measurable_iff_comap_le]
  apply le_iInf
  intro i
  rw [← MeasurableSpace.comap_le_iff_le_map]
  rw [MeasurableSpace.comap_comp]
  exact (hf i).comap_le

end DilutedSpinGlass

namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
variable {I : Type*} {X : I → Type*} [MeasurableSpace I] [DiscreteMeasurableSpace I]
    [∀ i, MeasurableSpace (X i)]
    (μ : Measure I) (ν : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (ν i)]

/-- Sufficient integrability on the genuine disjoint-union root law. -/
theorem familyLaw_integrable_bound (f : (i : I) → X i → ℝ)
    (hf : ∀ i, Measurable (f i)) {B : I → ℝ} (hB : Integrable B μ)
    (hb : ∀ i x, |f i x| ≤ B i) :
    Integrable (fun z : Sigma X => f z.1 z.2) (familyLaw μ ν) := by
  let F : Sigma X → ℝ := fun z => f z.1 z.2
  have hm : Measurable F := measurable_sigmaUncurry hf
  have hi (i : I) : Integrable (f i) (ν i) :=
    Integrable.of_bound (hf i).aestronglyMeasurable (B i) (ae_of_all _ (fun x => by
      simpa only [Real.norm_eq_abs] using hb i x))
  have hi' (i : I) : Integrable F (familyKernel ν i) := by
    change Integrable F ((ν i).map (Sigma.mk i))
    exact (integrable_map_measure hm.aestronglyMeasurable (measurable_sigmaMk i).aemeasurable).mpr (hi i)
  apply (Measure.integrable_comp_iff hm.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ hi', ?_⟩
  apply hB.mono' Measurable.of_discrete.aestronglyMeasurable
  apply ae_of_all
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
  change (∫ z, ‖F z‖ ∂(ν i).map (Sigma.mk i)) ≤ B i
  rw [integral_map (measurable_sigmaMk i).aemeasurable hm.norm.aestronglyMeasurable]
  have hh := integral_mono (hi i).norm (integrable_const (B i))
    (fun x => by simpa only [Real.norm_eq_abs] using hb i x)
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using hh

omit [∀ i, IsProbabilityMeasure (ν i)] in
 
theorem integral_familyLaw (f : (i : I) → X i → ℝ)
    (hf : ∀ i, Measurable (f i))
    (hi : Integrable (fun z : Sigma X => f z.1 z.2) (familyLaw μ ν)) :
    (∫ z : Sigma X, f z.1 z.2 ∂familyLaw μ ν) = ∫ i, ∫ x, f i x ∂ν i ∂μ := by
  unfold familyLaw at hi ⊢
  rw [Measure.comp_eq_comp_const_apply] at hi ⊢
  rw [Kernel.integral_comp hi]
  change (∫ i, ∫ z : Sigma X, f z.1 z.2 ∂(ν i).map (Sigma.mk i) ∂μ) = _
  apply integral_congr_ae
  apply ae_of_all
  intro i
  exact integral_map (measurable_sigmaMk i).aemeasurable
    (measurable_sigmaUncurry hf).aestronglyMeasurable

end DilutedSpinGlass

namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (ν : ∀ n, Measure (X n)) [∀ n, IsProbabilityMeasure (ν n)] (r : ℝ≥0)

theorem familyPoisson_count_integrable :
    Integrable (fun z : Sigma X => (z.1 : ℝ)) (familyLaw (poissonMeasure r) ν) := by
  apply familyLaw_integrable_bound (poissonMeasure r) ν (fun n _ => (n : ℝ)) (fun _ => measurable_const)
    (poisson_integrable_count r)
  intro n _
  simp

theorem familyPoisson_count_mean :
    (∫ z : Sigma X, (z.1 : ℝ) ∂familyLaw (poissonMeasure r) ν) = (r : ℝ) := by
  rw [integral_familyLaw (poissonMeasure r) ν (fun n _ => (n : ℝ)) (fun _ => measurable_const)
    (familyPoisson_count_integrable ν r)]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul,poisson_mean]

theorem familyPoisson_memLp_linear {f : (n : ℕ) → X n → ℝ}
    (hf : ∀ n, Measurable (f n)) {A B : ℝ} (hb : ∀ n x, |f n x| ≤ A+B*n) :
    MemLp (fun z : Sigma X => f z.1 z.2) 2 (familyLaw (poissonMeasure r) ν) := by
  apply (memLp_two_iff_integrable_sq (measurable_sigmaUncurry hf).aestronglyMeasurable).mpr
  apply familyLaw_integrable_bound (poissonMeasure r) ν (fun n x => (f n x)^2) (fun n => (hf n).pow_const 2)
    (B := fun n => 2*A^2+2*B^2*(n : ℝ)^2)
  · apply poisson_integrable_quadratic r (A := 2*A^2) (B := 2*B^2)
    intro n
    rw [abs_of_nonneg (by positivity)]
  · intro n x
    rw [abs_of_nonneg (sq_nonneg _)]
    have hsq : (f n x)^2 ≤ (A+B*n)^2 := by
      exact sq_le_sq' (abs_le.mp (hb n x)).1 (abs_le.mp (hb n x)).2
    nlinarith [sq_nonneg (A-B*n)]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ConvexBounds
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
open Set
namespace DilutedSpinGlass

/-- The deterministic three-point estimate used in pert:convex-bound. It
requires convexity only on the original open parameter domain, not globally. -/
theorem convex_derivative_fluctuation {S : Set ℝ} {f g f' g' : ℝ → ℝ}
    (hf : ConvexOn ℝ S f) (hg : ConvexOn ℝ S g)
    {u ρ : ℝ} (hρ : 0 < ρ) (hm : u-ρ ∈ S) (hu : u ∈ S) (hp : u+ρ ∈ S)
    (hfu : HasDerivAt f (f' u) u)
    (hgm : HasDerivAt g (g' (u-ρ)) (u-ρ))
    (hgu : HasDerivAt g (g' u) u)
    (hgp : HasDerivAt g (g' (u+ρ)) (u+ρ)) :
    |f' u - g' u| ≤
      (|f (u-ρ) - g (u-ρ)| + 2*|f u-g u| + |f (u+ρ)-g (u+ρ)|) / ρ +
        g' (u+ρ) - g' (u-ρ) := by
  have hum : u-ρ < u := by linarith
  have hup : u < u+ρ := by linarith
  have hfm := hf.slope_le_of_hasDerivAt hm hu hum hfu
  have hfp := hf.le_slope_of_hasDerivAt hu hp hup hfu
  have hgml := hg.le_slope_of_hasDerivAt hm hu hum hgm
  have hgmr := hg.slope_le_of_hasDerivAt hm hu hum hgu
  have hgpl := hg.le_slope_of_hasDerivAt hu hp hup hgu
  have hgpr := hg.slope_le_of_hasDerivAt hu hp hup hgp
  have hd1 : u - (u-ρ) = ρ := by ring
  have hd2 : u+ρ - u = ρ := by ring
  simp only [slope_def_field, hd1, hd2] at hfm hfp hgml hgmr hgpl hgpr
  have hfm' := (div_le_iff₀ hρ).mp hfm
  have hfp' := (le_div_iff₀ hρ).mp hfp
  have hgml' := (le_div_iff₀ hρ).mp hgml
  have hgmr' := (div_le_iff₀ hρ).mp hgmr
  have hgpl' := (le_div_iff₀ hρ).mp hgpl
  have hgpr' := (div_le_iff₀ hρ).mp hgpr
  let A := |f (u-ρ)-g (u-ρ)| + 2*|f u-g u| + |f (u+ρ)-g (u+ρ)|
  have ha : (A / ρ) * ρ = A := div_mul_cancel₀ _ (ne_of_gt hρ)
  apply abs_le.mpr
  constructor
  · apply (mul_le_mul_iff_left₀ hρ).mp
    dsimp only [A] at ha
    nlinarith [le_abs_self (f (u-ρ)-g (u-ρ)), neg_le_abs (f u-g u),
      abs_nonneg (f u-g u), abs_nonneg (f (u+ρ)-g (u+ρ))]
  · apply (mul_le_mul_iff_left₀ hρ).mp
    dsimp only [A] at ha
    nlinarith [le_abs_self (f (u+ρ)-g (u+ρ)), neg_le_abs (f u-g u),
      abs_nonneg (f u-g u), abs_nonneg (f (u-ρ)-g (u-ρ))]

end DilutedSpinGlass

namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

 
theorem integral_abs_le_sqrt_sq {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, |f x| ∂μ) ≤ Real.sqrt (∫ x, (f x)^2 ∂μ) := by
  have hn := variance_nonneg (fun x => ‖f x‖) μ
  rw [variance_eq_sub hf.norm] at hn
  simp only [Real.norm_eq_abs, Pi.pow_apply, sq_abs] at hn
  exact (Real.le_sqrt (integral_nonneg (fun _ => abs_nonneg _))
    (integral_nonneg (fun _ => sq_nonneg _))).mpr (by linarith)

theorem integral_deviation_le_sqrt_variance {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, |f x-∫ y, f y ∂μ| ∂μ) ≤ Real.sqrt (variance f μ) := by
  have hh := integral_abs_le_sqrt_sq μ (hf.sub (memLp_const (∫ y, f y ∂μ)))
  change (∫ x, |f x-∫ y, f y ∂μ| ∂μ) ≤ Real.sqrt (∫ x, (f x-∫ y, f y ∂μ)^2 ∂μ) at hh
  rw [← variance_eq_integral hf.aemeasurable] at hh
  exact hh

omit [IsProbabilityMeasure μ] in
/-- Taking a root expectation preserves convexity on the original parameter
domain. This does not extend the perturbation outside its factor-positive
interval. -/
theorem convexOn_integral {S : Set ℝ} {F : Ω → ℝ → ℝ}
    (hS : Convex ℝ S) (hF : ∀ x, ConvexOn ℝ S (F x))
    (hi : ∀ u ∈ S, Integrable (fun x => F x u) μ) :
    ConvexOn ℝ S (fun u => ∫ x, F x u ∂μ) := by
  refine ⟨hS, ?_⟩
  intro a ha b hb w v hw hv hwv
  have huv : w*a+v*b ∈ S := hS ha hb hw hv hwv
  have hh := integral_mono (hi _ huv)
    (((hi a ha).const_mul w).add ((hi b hb).const_mul v))
    (fun x => (hF x).2 ha hb hw hv hwv)
  change (∫ x, F x (w*a+v*b) ∂μ) ≤ ∫ x, (w*F x a+v*F x b) ∂μ at hh
  rw [integral_add ((hi a ha).const_mul w) ((hi b hb).const_mul v), integral_const_mul,integral_const_mul] at hh
  simpa only [smul_eq_mul] using hh

/-- The probabilistic three-point convexity estimate, with its genuine
standard-deviation (rather than variance) scale. -/
theorem convex_derivative_mean_bound {S : Set ℝ} {F F' : Ω → ℝ → ℝ}
    {g g' : ℝ → ℝ} (hf : ∀ x, ConvexOn ℝ S (F x)) (hg : ConvexOn ℝ S g)
    {u ρ V : ℝ} (hρ : 0 < ρ)
    (hm : u-ρ ∈ S) (hu : u ∈ S) (hp : u+ρ ∈ S)
    (hfu : ∀ x, HasDerivAt (F x) (F' x u) u)
    (hgm : HasDerivAt g (g' (u-ρ)) (u-ρ))
    (hgu : HasDerivAt g (g' u) u) (hgp : HasDerivAt g (g' (u+ρ)) (u+ρ))
    (hD : Integrable (fun x => F' x u) μ)
    (hi : ∀ w ∈ S, MemLp (fun x => F x w) 2 μ)
    (he : ∀ w ∈ S, g w = ∫ x, F x w ∂μ)
    (hv : ∀ w ∈ S, variance (fun x => F x w) μ ≤ V) :
    (∫ x, |F' x u-g' u| ∂μ) ≤ 4*Real.sqrt V/ρ+g' (u+ρ)-g' (u-ρ) := by
  have hb (w : ℝ) (hw : w ∈ S) :
      (∫ x, |F x w-g w| ∂μ) ≤ Real.sqrt V := by
    rw [he w hw]
    exact (integral_deviation_le_sqrt_variance μ (hi w hw)).trans
      (Real.sqrt_le_sqrt (hv w hw))
  have hj (w : ℝ) (hw : w ∈ S) : Integrable (fun x => |F x w-g w|) μ :=
    (((hi w hw).integrable (by norm_num)).sub (integrable_const _)).abs
  have hbound := integral_mono ((hD.sub (integrable_const _)).abs)
    (((((hj (u-ρ) hm).add ((hj u hu).const_mul 2)).add (hj (u+ρ) hp)).div_const ρ).add
      (integrable_const (g' (u+ρ)-g' (u-ρ))))
    (fun x => by
      have hh := convex_derivative_fluctuation (hf x) hg hρ hm hu hp (hfu x) hgm hgu hgp
      change |F' x u-g' u| ≤ (|F x (u-ρ)-g (u-ρ)|+2*|F x u-g u|+|F x (u+ρ)-g (u+ρ)|)/ρ+(g' (u+ρ)-g' (u-ρ))
      linarith)
  have hv1 := hb (u-ρ) hm
  have hv2 := hb u hu
  have hv3 := hb (u+ρ) hp
  change (∫ x, |F' x u-g' u| ∂μ) ≤
    ∫ x, ((|F x (u-ρ)-g (u-ρ)|+2*|F x u-g u|+|F x (u+ρ)-g (u+ρ)|)/ρ+
      (g' (u+ρ)-g' (u-ρ))) ∂μ at hbound
  erw [integral_add
    ((((hj (u-ρ) hm).add ((hj u hu).const_mul 2)).add (hj (u+ρ) hp)).div_const ρ)
    (integrable_const _), integral_div,
    integral_add ((hj (u-ρ) hm).add ((hj u hu).const_mul 2)) (hj (u+ρ) hp),
    integral_add (hj (u-ρ) hm) ((hj u hu).const_mul 2), integral_const_mul,
    integral_const,probReal_univ,smul_eq_mul,one_mul] at hbound
  have hsum : ((∫ x, |F x (u-ρ)-g (u-ρ)| ∂μ)+2*(∫ x, |F x u-g u| ∂μ)+
      (∫ x, |F x (u+ρ)-g (u+ρ)| ∂μ))/ρ ≤ 4*Real.sqrt V/ρ :=
    div_le_div_of_nonneg_right (by linarith) (le_of_lt hρ)
  linarith

end DilutedSpinGlass

namespace DilutedSpinGlass
open _root_.MeasureTheory Set intervalIntegral

/-- The boundary-layer estimate used in pert:convex-bound. It holds on the
specified finite domain only, including when the two boundary layers overlap. -/
theorem integral_monotone_shift {k : ℝ → ℝ} {a b ρ : ℝ}
    (hab : a ≤ b) (hρ : 0 ≤ ρ) (hk : MonotoneOn k (Icc (a-ρ) (b+ρ))) :
    (∫ u in a..b, k (u+ρ)-k (u-ρ)) ≤ 2*ρ*(k (b+ρ)-k (a-ρ)) := by
  have hlo : a-ρ ≤ b+ρ := by linarith
  have hint {x y : ℝ} (hx : x ∈ Icc (a-ρ) (b+ρ)) (hy : y ∈ Icc (a-ρ) (b+ρ)) :
      IntervalIntegrable k volume x y := by
    apply MonotoneOn.intervalIntegrable
    intro z hz w hw hzw
    apply hk _ _ hzw
    · change min x y ≤ z ∧ z ≤ max x y at hz
      exact ⟨le_trans (le_min hx.1 hy.1) hz.1, le_trans hz.2 (max_le hx.2 hy.2)⟩
    · change min x y ≤ w ∧ w ≤ max x y at hw
      exact ⟨le_trans (le_min hx.1 hy.1) hw.1, le_trans hw.2 (max_le hx.2 hy.2)⟩
  have ham : a-ρ ∈ Icc (a-ρ) (b+ρ) := ⟨le_rfl,hlo⟩
  have hap : a+ρ ∈ Icc (a-ρ) (b+ρ) := ⟨by linarith,by linarith⟩
  have hbm : b-ρ ∈ Icc (a-ρ) (b+ρ) := ⟨by linarith,by linarith⟩
  have hbp : b+ρ ∈ Icc (a-ρ) (b+ρ) := ⟨hlo,le_rfl⟩
  have hplus : IntervalIntegrable (fun u => k (u+ρ)) volume a b := by
    apply MonotoneOn.intervalIntegrable
    rw [uIcc_of_le hab]
    intro x hx y hy hxy
    exact hk ⟨by linarith [hx.1],by linarith [hx.2]⟩
      ⟨by linarith [hy.1],by linarith [hy.2]⟩ (by linarith)
  have hminus : IntervalIntegrable (fun u => k (u-ρ)) volume a b := by
    apply MonotoneOn.intervalIntegrable
    rw [uIcc_of_le hab]
    intro x hx y hy hxy
    exact hk ⟨by linarith [hx.1],by linarith [hx.2]⟩
      ⟨by linarith [hy.1],by linarith [hy.2]⟩ (by linarith)
  rw [integral_sub hplus hminus,integral_comp_add_right,integral_comp_sub_right]
  have he1 := integral_add_adjacent_intervals (hint ham hap) (hint hap hbp)
  have he2 := integral_add_adjacent_intervals (hint ham hbm) (hint hbm hbp)
  have hbnd := integral_mono_on (by linarith : b-ρ ≤ b+ρ) (hint hbm hbp)
    (intervalIntegrable_const (c := k (b+ρ))) (fun x hx =>
      hk ⟨by linarith [hx.1],hx.2⟩ hbp hx.2)
  have hand := integral_mono_on (by linarith : a-ρ ≤ a+ρ)
    (intervalIntegrable_const (c := k (a-ρ))) (hint ham hap) (fun x hx =>
      hk ham ⟨hx.1,by linarith [hx.2]⟩ hx.1)
  simp only [intervalIntegral.integral_const,smul_eq_mul] at hbnd hand
  nlinarith

end DilutedSpinGlass

namespace DilutedSpinGlass
open _root_.MeasureTheory Set intervalIntegral

 
theorem integral_convex_derivative_bound {D k : ℝ → ℝ} {a b ρ V B : ℝ}
    (hab : a < b) (hρ : 0 < ρ)
    (hD : IntervalIntegrable D volume a b)
    (hk : MonotoneOn k (Icc (a-ρ) (b+ρ)))
    (hpoint : ∀ u ∈ Icc a b, D u ≤ 4*Real.sqrt V/ρ+k (u+ρ)-k (u-ρ))
    (hB : k (b+ρ)-k (a-ρ) ≤ B) :
    (∫ u in a..b, D u)/(b-a) ≤ 4*Real.sqrt V/ρ+(2*ρ*B)/(b-a) := by
  have hi {c : ℝ} (hc : -ρ ≤ c ∧ c ≤ ρ) :
      IntervalIntegrable (fun u => k (u+c)) volume a b := by
    apply MonotoneOn.intervalIntegrable
    rw [uIcc_of_le (le_of_lt hab)]
    intro x hx y hy hxy
    exact hk ⟨by linarith [hx.1], by linarith [hx.2]⟩
      ⟨by linarith [hy.1], by linarith [hy.2]⟩ (by linarith)
  have hp := hi (c := ρ) ⟨by linarith,le_rfl⟩
  have hm : IntervalIntegrable (fun u => k (u-ρ)) volume a b := by
    simpa only [sub_eq_add_neg] using (hi (c := -ρ) ⟨le_rfl,by linarith⟩)
  have hs := integral_monotone_shift (le_of_lt hab) (le_of_lt hρ) hk
  have hbnd := integral_mono_on (le_of_lt hab) hD
    ((intervalIntegrable_const (c := 4*Real.sqrt V/ρ)).add (hp.sub hm))
    (fun u hu => by simpa only [add_sub_assoc] using hpoint u hu)
  change (∫ u in a..b, D u) ≤ ∫ u in a..b, (4*Real.sqrt V/ρ+(k (u+ρ)-k (u-ρ))) at hbnd
  rw [integral_add intervalIntegrable_const (hp.sub hm),intervalIntegral.integral_const,
    smul_eq_mul] at hbnd
  have hB' := mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ 2*ρ)
  apply (div_le_iff₀ (sub_pos.mpr hab)).mpr
  have hne : b-a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  rw [add_mul,div_mul_cancel₀ _ hne]
  nlinarith

end DilutedSpinGlass

namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem hasDerivAt_rootMean {F G : X → ℝ → ℝ} {S : Set ℝ}
    (hS : IsOpen S) (hFm : ∀ u, Measurable (fun x => F x u))
    (hGm : ∀ u, Measurable (fun x => G x u))
    (hi : ∀ u ∈ S, Integrable (fun x => F x u) μ)
    {B : X → ℝ} (hB : Integrable B μ) (hb : ∀ x u, u ∈ S → |G x u| ≤ B x)
    (hd : ∀ x u, u ∈ S → HasDerivAt (F x) (G x u) u) {u : ℝ} (hu : u ∈ S) :
    HasDerivAt (fun v => ∫ x, F x v ∂μ) (∫ x, G x u ∂μ) u := by
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (hS.mem_nhds hu)
    (Eventually.of_forall (fun v => (hFm v).aestronglyMeasurable)) (hi u hu)
    (hGm u).aestronglyMeasurable
    (ae_of_all _ (fun x v hv => by simpa only [Real.norm_eq_abs] using hb x v hv))
    hB (ae_of_all _ hd)).2

omit [IsProbabilityMeasure μ] in
theorem rootMean_abs_le {G : X → ℝ → ℝ} (hGm : ∀ u, Measurable (fun x => G x u))
    {B : X → ℝ} (hB : Integrable B μ) {u : ℝ} (hb : ∀ x, |G x u| ≤ B x) :
    |∫ x, G x u ∂μ| ≤ ∫ x, B x ∂μ := by
  exact (abs_integral_le_integral_abs).trans
    (integral_mono (hB.mono' (hGm u).aestronglyMeasurable (ae_of_all _ (fun x => by
      simpa only [Real.norm_eq_abs] using hb x))).abs hB hb)

/-- Root fluctuation estimate after averaging the actual convex score;
all differentiations of expectations are justified by the integrable
random count bound. -/
theorem root_derivative_integral_bound {F G : X → ℝ → ℝ} {S : Set ℝ}
    (hS : IsOpen S) (hSc : Convex ℝ S)
    (hFm : ∀ u, Measurable (fun x => F x u))
    (hGm : Measurable (fun z : X × ℝ => G z.1 z.2))
    (hfc : ∀ x, ConvexOn ℝ S (F x))
    (hLp : ∀ u ∈ S, MemLp (fun x => F x u) 2 μ)
    {B : X → ℝ} (hB : Integrable B μ) (hb : ∀ x u, u ∈ S → |G x u| ≤ B x)
    (hd : ∀ x u, u ∈ S → HasDerivAt (F x) (G x u) u)
    {a b ρ V : ℝ} (hab : a < b) (hρ : 0 < ρ)
    (hJ : Icc (a-ρ) (b+ρ) ⊆ S)
    (hv : ∀ u ∈ Icc (a-ρ) (b+ρ), variance (fun x => F x u) μ ≤ V) :
    (∫ u in a..b, (∫ x, |G x u-∫ y, G y u ∂μ| ∂μ))/(b-a) ≤
      4*Real.sqrt V/ρ+4*ρ*(∫ x, B x ∂μ)/(b-a) := by
  let g (u : ℝ) := ∫ x, F x u ∂μ
  let k (u : ℝ) := ∫ x, G x u ∂μ
  let D (u : ℝ) := ∫ x, |G x u-k u| ∂μ
  have hG (u : ℝ) : Measurable (fun x => G x u) :=
    hGm.comp (measurable_id.prodMk measurable_const)
  have hi (u : ℝ) (hu : u ∈ S) : Integrable (fun x => F x u) μ :=
    (hLp u hu).integrable (by norm_num)
  have hg : ConvexOn ℝ S g := convexOn_integral μ hSc hfc hi
  have hdg (u : ℝ) (hu : u ∈ S) : HasDerivAt g (k u) u :=
    hasDerivAt_rootMean μ hS hFm hG hi hB hb hd hu
  have hk : MonotoneOn k (Icc (a-ρ) (b+ρ)) := by
    intro x hx y hy hxy
    have hh := hg.monotoneOn_deriv (fun u hu => (hdg u hu).differentiableAt) (hJ hx) (hJ hy) hxy
    rwa [(hdg x (hJ hx)).deriv,(hdg y (hJ hy)).deriv] at hh
  have hki (u : ℝ) (hu : u ∈ S) : Integrable (fun x => G x u) μ :=
    hB.mono' (hG u).aestronglyMeasurable (ae_of_all _ (fun x => by
      simpa only [Real.norm_eq_abs] using hb x u hu))
  have hkab (u : ℝ) (hu : u ∈ S) : |k u| ≤ ∫ x, B x ∂μ :=
    rootMean_abs_le μ hG hB (fun x => hb x u hu)
  have hDm : Measurable D := by
    have hkm : Measurable k := (hGm.stronglyMeasurable.integral_prod_left').measurable
    exact (((hGm.sub (hkm.comp measurable_snd)).abs).stronglyMeasurable.integral_prod_left').measurable
  have hDb (u : ℝ) (hu : u ∈ Icc a b) : |D u| ≤ 2*(∫ x, B x ∂μ) := by
    have huS : u ∈ S := hJ ⟨by linarith [hu.1],by linarith [hu.2]⟩
    rw [abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))]
    have hh := integral_mono ((hki u huS).sub (integrable_const (k u))).abs
      (hB.add (integrable_const |k u|))
      (fun x => (abs_sub _ _).trans (add_le_add (hb x u huS) le_rfl))
    simp only [Pi.add_apply, Pi.sub_apply] at hh
    rw [integral_add hB (integrable_const _),integral_const,probReal_univ,smul_eq_mul,one_mul] at hh
    dsimp only [D]
    linarith [hkab u huS]
  have hDi : IntervalIntegrable D volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le]
    exact Measure.integrableOn_of_bounded (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      hDm.aestronglyMeasurable (ae_restrict_of_forall_mem measurableSet_Ioc
        (fun u hu => by simpa only [Real.norm_eq_abs] using hDb u ⟨hu.1.le,hu.2⟩))
  have hpoint (u : ℝ) (hu : u ∈ Icc a b) :
      D u ≤ 4*Real.sqrt V/ρ+k (u+ρ)-k (u-ρ) := by
    have hm : u-ρ ∈ Icc (a-ρ) (b+ρ) := ⟨by linarith [hu.1],by linarith [hu.2]⟩
    have h0 : u ∈ Icc (a-ρ) (b+ρ) := ⟨by linarith [hu.1],by linarith [hu.2]⟩
    have hp : u+ρ ∈ Icc (a-ρ) (b+ρ) := ⟨by linarith [hu.1],by linarith [hu.2]⟩
    apply convex_derivative_mean_bound μ
      (fun x => (hfc x).subset hJ (convex_Icc _ _)) (hg.subset hJ (convex_Icc _ _)) hρ hm h0 hp
      (fun x => hd x u (hJ h0)) (hdg _ (hJ hm)) (hdg _ (hJ h0)) (hdg _ (hJ hp))
      (hki u (hJ h0)) (fun w hw => hLp w (hJ hw)) (fun _ _ => rfl) hv
  have hB' : k (b+ρ)-k (a-ρ) ≤ 2*(∫ x, B x ∂μ) := by
    have hlo : a-ρ ≤ b+ρ := by linarith
    have h1 := hkab (b+ρ) (hJ ⟨hlo,le_rfl⟩)
    have h2 := hkab (a-ρ) (hJ ⟨le_rfl,hlo⟩)
    linarith [le_abs_self (k (b+ρ)), neg_abs_le (k (a-ρ))]
  have hh := integral_convex_derivative_bound hab hρ hDi hk hpoint hB'
  convert hh using 1 <;> first | rfl | ring

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ReservoirVariance
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
open Set

namespace DilutedSpinGlass.KernelTower
open _root_.MeasureTheory ProbabilityTheory
variable {Ω X : Type} [Fintype Ω] [MeasurableSpace X]

theorem measurable_correctedPerturbScore {L n : ℕ} (T : KernelTower Ω L) (m : Fin L → ℝ)
    {base : X → FinitePath Ω L → ℝ} {D E : X → Fin n → FinitePath Ω L → ℝ}
    {t u : X → ℝ} (hbase : ∀ y, Measurable (fun x => base x y))
    (hD : ∀ q y, Measurable (fun x => D x q y))
    (hE : ∀ q y, Measurable (fun x => E x q y)) (ht : Measurable t) (hu : Measurable u) :
    Measurable (fun x => correctedPerturbScore T m (base x) (D x) (E x) (t x) (u x)) := by
  apply (measurable_path_expect L T m (measurable_perturbLog hbase hD hE ht hu)
    (measurable_perturbScore hD hE ht hu)).add
  exact hu.const_mul _

omit [MeasurableSpace X] in
theorem correctedPerturbScore_bound {L n : ℕ} (T : KernelTower Ω L) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (D E : Fin n → FinitePath Ω L → ℝ)
    (hD : ∀ q y, |D q y| ≤ 1) (hE : ∀ q y, |E q y| ≤ 1)
    {t u : ℝ} (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) :
    |correctedPerturbScore T m base D E t u| ≤ 3*n := by
  unfold correctedPerturbScore
  have h1 := (law L (tilt L T m (perturbLog base D E t u))).abs_expect_le
    (perturbScore_bound D E hD hE ht hu)
  have h3 : |4*(n:ℝ)*u| ≤ (n : ℝ) := by
    rw [abs_mul,abs_of_nonneg (by positivity)]
    nlinarith [show 0 ≤ (n : ℝ) from Nat.cast_nonneg n]
  have h4 := abs_add_le
    ((law L (tilt L T m (perturbLog base D E t u))).expect (perturbScore D E t u)) (4*n*u)
  linarith

end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (ν : ∀ n, Measure (X n)) [∀ n, IsProbabilityMeasure (ν n)] (r : ℝ≥0)

theorem familyPoisson_count_memLp :
    MemLp (fun z : Sigma X => (z.1 : ℝ)) 2 (familyLaw (poissonMeasure r) ν) := by
  apply familyPoisson_memLp_linear ν r (fun _ => measurable_const) (A := 0) (B := 1)
  intro n x
  simp

theorem familyPoisson_count_variance :
    variance (fun z : Sigma X => (z.1 : ℝ)) (familyLaw (poissonMeasure r) ν) = r := by
  rw [variance_eq_integral (familyPoisson_count_memLp ν r).aemeasurable,
    familyPoisson_count_mean]
  rw [integral_familyLaw (poissonMeasure r) ν (fun n _ => ((n : ℝ)-r)^2)
    (fun _ => measurable_const) ((familyPoisson_count_memLp ν r).sub (memLp_const (r : ℝ))).integrable_sq]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul,poisson_variance]

theorem familyPoisson_count_deviation :
    (∫ z : Sigma X, |(z.1 : ℝ)-r| ∂familyLaw (poissonMeasure r) ν) ≤ Real.sqrt r := by
  have h := integral_deviation_le_sqrt_variance (familyLaw (poissonMeasure r) ν)
    (familyPoisson_count_memLp ν r)
  rwa [familyPoisson_count_mean,familyPoisson_count_variance] at h

end DilutedSpinGlass

namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem rootDeviation_nonneg (f : X → ℝ) : 0 ≤ rootDeviation μ f :=
  integral_nonneg (fun _ => abs_nonneg _)

theorem rootDeviation_add_le {f g : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    rootDeviation μ (f+g) ≤ rootDeviation μ f+rootDeviation μ g := by
  unfold rootDeviation
  simp only [Pi.add_apply]
  rw [integral_add hf hg]
  have hi := integral_mono ((hf.add hg).sub (integrable_const _)).abs
    (((hf.sub (integrable_const _)).abs).add ((hg.sub (integrable_const _)).abs))
    (fun x => (show |f x+g x-((∫ y, f y ∂μ)+(∫ y, g y ∂μ))| ≤
      |f x-(∫ y, f y ∂μ)|+|g x-(∫ y, g y ∂μ)| by
        have heq : f x+g x-((∫ y, f y ∂μ)+(∫ y, g y ∂μ)) =
            (f x-(∫ y, f y ∂μ))+(g x-(∫ y, g y ∂μ)) := by ring
        rw [heq]
        exact abs_add_le _ _))
  have hr := integral_add (hf.sub (integrable_const (∫ y, f y ∂μ))).abs
    (hg.sub (integrable_const (∫ y, g y ∂μ))).abs
  dsimp only [Pi.add_apply,Pi.sub_apply] at hr hi
  rw [hr] at hi
  exact hi

omit [IsProbabilityMeasure μ] in
theorem rootDeviation_smul (c : ℝ) (f : X → ℝ) :
    rootDeviation μ (fun x => c*f x) = |c| * rootDeviation μ f := by
  simp only [rootDeviation,integral_const_mul,← mul_sub,abs_mul]

theorem rootDeviation_sub_le {f g : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    rootDeviation μ (f-g) ≤ rootDeviation μ f+rootDeviation μ g := by
  have h := rootDeviation_add_le μ hf (hg.const_mul (-1))
  rw [rootDeviation_smul] at h
  have heq : f-g = f+(fun x => (-1:ℝ)*g x) := by
    ext x
    simp [sub_eq_add_neg]
  rw [heq]
  simpa only [abs_neg,abs_one,one_mul] using h

end DilutedSpinGlass

namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Set
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

theorem measurable_rootDeviation {G : X → ℝ → ℝ}
    (hG : Measurable (fun z : X × ℝ => G z.1 z.2)) :
    Measurable (fun u => rootDeviation μ (fun x => G x u)) := by
  have hk : Measurable (fun u => ∫ x, G x u ∂μ) :=
    (hG.stronglyMeasurable.integral_prod_left').measurable
  exact ((hG.sub (hk.comp measurable_snd)).abs.stronglyMeasurable.integral_prod_left').measurable

theorem rootDeviation_bound {f B : X → ℝ} (hf : Measurable f)
    (hB : Integrable B μ) (hb : ∀ x, |f x| ≤ B x) :
    rootDeviation μ f ≤ 2*(∫ x, B x ∂μ) := by
  have hi : Integrable f μ := hB.mono' hf.aestronglyMeasurable
    (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hb x))
  have hh := integral_mono ((hi.sub (integrable_const _)).abs)
    (hB.add (integrable_const |∫ x, f x ∂μ|))
      (fun x => (abs_sub _ _).trans (add_le_add (hb x) le_rfl))
  simp only [Pi.add_apply,integral_add hB (integrable_const _),integral_const,
    probReal_univ,smul_eq_mul,one_mul] at hh
  have hav : |∫ x, f x ∂μ| ≤ ∫ x, B x ∂μ :=
    (abs_integral_le_integral_abs).trans (integral_mono hi.abs hB hb)
  simp only [Pi.sub_apply] at hh
  dsimp only [rootDeviation]
  linarith

theorem intervalIntegrable_rootDeviation {G : X → ℝ → ℝ}
    (hG : Measurable (fun z : X × ℝ => G z.1 z.2)) {B : X → ℝ}
    (hB : Integrable B μ) {a b : ℝ} (hab : a ≤ b)
    (hb : ∀ x u, u ∈ Icc a b → |G x u| ≤ B x) :
    IntervalIntegrable (fun u => rootDeviation μ (fun x => G x u)) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  apply Measure.integrableOn_of_bounded
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    (measurable_rootDeviation μ hG).aestronglyMeasurable
  apply ae_restrict_of_forall_mem measurableSet_Ioc
  intro u hu
  rw [Real.norm_eq_abs,abs_of_nonneg (rootDeviation_nonneg μ _)]
  exact rootDeviation_bound μ (hG.comp (measurable_id.prodMk measurable_const)) hB
    (fun x => hb x u ⟨hu.1.le,hu.2⟩)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_HeterogeneousMarks
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
open Set
namespace DilutedSpinGlass.HeterogeneousMarks
open scoped BigOperators
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]

/-- Adding a type uses its own prior, independently of all old marks. -/
theorem tower_split {k : ℕ} (roots : Fin k → I) (i : I) (L : ℕ)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) :
    KernelTower.transport (split roots i) L (tower (Fin.cons i roots) L T Q) =
      KernelTower.prod L (tower roots L T Q) (markPrior L (Q i)) := by
  induction L with
  | zero => rfl
  | succ L ih =>
    apply Prod.ext
    · apply FiniteLaw.eq_of_weights
      intro z
      change T.1.weight z.1.1 *
          (∏ j : Fin (k+1), (Q ((Fin.cons i roots : Fin (k+1) → I) j) 0).weight
            ((Fin.cons z.2 z.1.2 : Row (A := A) (Fin.cons i roots)) j)) =
        (T.1.weight z.1.1 * ∏ j, (Q (roots j) 0).weight (z.1.2 j)) * (Q i 0).weight z.2
      rw [Fin.prod_univ_succ]
      change T.1.weight z.1.1 *
        ((Q i 0).weight z.2 * ∏ j, (Q (roots j) 0).weight (z.1.2 j)) =
        (T.1.weight z.1.1 * ∏ j, (Q (roots j) 0).weight (z.1.2 j)) * (Q i 0).weight z.2
      ring
    · funext z
      exact ih (T.2 z.1.1) (fun i j => Q i j.succ)

omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem physical_split {k : ℕ} (roots : Fin k → I) (i : I) (L : ℕ)
    (y : FinitePath (Ω × Row (A := A) (Fin.cons i roots)) L) :
    physical roots L (KernelTower.pathFst L (KernelTower.pathEquiv (split roots i) L y)) =
      physical (Fin.cons i roots) L y := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change (y.1.1, physical roots L (KernelTower.pathFst L
      (KernelTower.pathEquiv (split roots i) L y.2))) =
      (y.1.1, physical (Fin.cons i roots) L y.2)
    rw [ih]

omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem mark_split_succ {k : ℕ} (roots : Fin k → I) (i : I) (q : Fin k) (L : ℕ)
    (y : FinitePath (Ω × Row (A := A) (Fin.cons i roots)) L) :
    mark q L (KernelTower.pathFst L (KernelTower.pathEquiv (split roots i) L y)) =
      mark q.succ L y := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change (y.1.2 q.succ, mark q L (KernelTower.pathFst L
      (KernelTower.pathEquiv (split roots i) L y.2))) = (y.1.2 q.succ, mark q.succ L y.2)
    rw [ih]
    rfl

omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem mark_split_zero {k : ℕ} (roots : Fin k → I) (i : I) (L : ℕ)
    (y : FinitePath (Ω × Row (A := A) (Fin.cons i roots)) L) :
    KernelTower.pathSnd L (KernelTower.pathEquiv (split roots i) L y) = mark 0 L y := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change (y.1.2 0, KernelTower.pathSnd L (KernelTower.pathEquiv (split roots i) L y.2)) =
      (y.1.2 0, mark 0 L y.2)
    rw [ih]
    rfl

variable {k L : ℕ}

omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem insertedLog_split (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) (i : I)
    (y : FinitePath (Ω × Row (A := A) (Fin.cons i roots)) L) :
    insertedLog base roots factor i (KernelTower.pathEquiv (split roots i) L y) =
      logWeight base (Fin.cons i roots) factor y := by
  simp only [insertedLog, logWeight, physical_split, mark_split_succ,
    mark_split_zero, Fin.sum_univ_succ]
  change base (physical (Fin.cons i roots) L y) +
      (∑ q, Real.log (factor (roots q) (physical (Fin.cons i roots) L y) (mark q.succ L y))) +
      Real.log (factor i (physical (Fin.cons i roots) L y) (mark 0 L y)) =
    base (physical (Fin.cons i roots) L y) +
      (Real.log (factor i (physical (Fin.cons i roots) L y) (mark 0 L y)) +
      ∑ q, Real.log (factor (roots q) (physical (Fin.cons i roots) L y) (mark q.succ L y)))
  ring

/-- Uniform add/delete control does not depend on the mark dimension or type. -/
theorem root_cons_bound (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I) (i : I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) {C : ℝ}
    (hfactor : ∀ x y, |Real.log (factor i x y)| ≤ C) :
    |root T Q m base (Fin.cons i roots) factor - root T Q m base roots factor| ≤ C := by
  have h := KernelTower.backwardLog_transport (split roots i) L
    (tower (Fin.cons i roots) L T Q) m (insertedLog base roots factor i)
  have heq : insertedLog base roots factor i ∘ KernelTower.pathEquiv (split roots i) L =
      logWeight base (Fin.cons i roots) factor :=
    funext (fun y => insertedLog_split base roots factor i y)
  rw [heq, tower_split] at h
  unfold root
  rw [← h, ← KernelTower.backwardLog_prod_fst L (tower roots L T Q) (markPrior L (Q i)) m
    (logWeight base roots factor)]
  apply KernelTower.backwardLog_stability L _ m hm
  intro y
  simpa only [insertedLog, add_sub_cancel_left] using hfactor
    (physical roots L (KernelTower.pathFst L y)) (KernelTower.pathSnd L y)

/-- Typewise log-factor errors sum on the actual root list. -/
theorem root_factor_stability (T : KernelTower Ω L)
    (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor factor' : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (C : I → ℝ) (hC : ∀ i x y, |Real.log (factor i x y) - Real.log (factor' i x y)| ≤ C i) :
    |root T Q m base roots factor - root T Q m base roots factor'| ≤ ∑ q, C (roots q) := by
  apply KernelTower.backwardLog_stability L _ m hm
  intro y
  simp only [logWeight, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun q _ => hC _ _ _))

end DilutedSpinGlass.HeterogeneousMarks

namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
variable {k L : ℕ}

/-- The complete independent row can be integrated as a single finite mark.
Its dimension depends on the realized labels, never on a deterministic cutoff. -/
theorem tower_eq_prod (roots : Fin k → I) (L : ℕ) (T : KernelTower Ω L)
    (Q : (i : I) → Fin L → FiniteLaw (A i)) :
    tower roots L T Q = KernelTower.prod L T
      (markPrior L (fun d => FiniteLaw.pi (fun j => Q (roots j) d))) := by
  induction L with
  | zero => rfl
  | succ L ih =>
    apply Prod.ext
    · rfl
    · funext y
      exact ih (T.2 y.1) (fun i j => Q i j.succ)

omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem physical_eq_fst (roots : Fin k → I)
    (y : FinitePath (Ω × Row (A := A) roots) L) :
    physical roots L y = KernelTower.pathFst L y := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change (y.1.1, physical roots L y.2) = (y.1.1, KernelTower.pathFst L y.2)
    rw [ih]

/-- All unused finite priors integrate out, exactly, even if their dimension
varies over the full countable type list. -/
theorem root_one (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (base : FinitePath Ω L → ℝ) (roots : Fin k → I) :
    root T Q m base roots (fun _ _ _ => 1) = KernelTower.backwardLog L T m base := by
  unfold root
  have heq : logWeight (A := A) base roots (fun _ _ _ => 1) =
      base ∘ KernelTower.pathFst L := by
    funext y
    simp only [logWeight, Real.log_one, Finset.sum_const_zero, add_zero,
      physical_eq_fst, Function.comp_apply]
  rw [heq, tower_eq_prod]
  exact KernelTower.backwardLog_prod_fst L T _ m base

/-- The pathwise perturbation cost is additive over all realized labels. -/
theorem root_base_bound (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (C : I → ℝ) (hC : ∀ i x y, |Real.log (factor i x y)| ≤ C i) :
    |root T Q m base roots factor - KernelTower.backwardLog L T m base| ≤
      ∑ q, C (roots q) := by
  rw [← root_one T Q m base roots]
  exact root_factor_stability T Q m hm base roots factor (fun _ _ _ => 1) C
    (fun i x y => by simpa only [Real.log_one, sub_zero] using hC i x y)

/-- No lower bound on a type's intensity occurs in this global domination. -/
theorem abs_root_le (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) {C : ℝ}
    (hC : ∀ i x y, |Real.log (factor i x y)| ≤ C) :
    |root T Q m base roots factor| ≤ |KernelTower.backwardLog L T m base| + C*k := by
  have h := root_base_bound T Q m hm base roots factor (fun _ => C) hC
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  have ht := abs_add_le (root T Q m base roots factor - KernelTower.backwardLog L T m base)
    (KernelTower.backwardLog L T m base)
  rw [sub_add_cancel] at ht
  linarith

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MarkInsertion
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
open Set
namespace DilutedSpinGlass.HeterogeneousMarks
open scoped BigOperators
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]

theorem tower_transport {k : ℕ} (roots : Fin k → I) (σ : Equiv.Perm (Fin k)) (L : ℕ)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) :
    KernelTower.transport (rowPerm roots σ) L (tower roots L T Q) =
      tower (roots ∘ σ) L T Q := by
  induction L with
  | zero => rfl
  | succ L ih =>
    apply Prod.ext
    · apply FiniteLaw.eq_of_weights
      intro x
      change T.1.weight x.1 * (∏ q, (Q (roots q) 0).weight
          (Equiv.piCongrLeft (fun q => A (roots q)) σ x.2 q)) =
        T.1.weight x.1 * ∏ q, (Q (roots (σ q)) 0).weight (x.2 q)
      congr 1
      symm
      exact Fintype.prod_equiv σ _ _ (fun q => by rw [Equiv.piCongrLeft_apply_apply])
    · funext x
      exact ih (T.2 x.1) (fun i j => Q i j.succ)

omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem physical_rowPerm {k : ℕ} (roots : Fin k → I) (σ : Equiv.Perm (Fin k)) (L : ℕ)
    (y : FinitePath (Ω × Row (A := A) roots) L) :
    physical (roots ∘ σ) L (KernelTower.pathEquiv (rowPerm roots σ) L y) =
      physical roots L y := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change (y.1.1, physical (roots ∘ σ) L (KernelTower.pathEquiv (rowPerm roots σ) L y.2)) =
      (y.1.1, physical roots L y.2)
    rw [ih]

omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem mark_rowPerm {k : ℕ} (roots : Fin k → I) (σ : Equiv.Perm (Fin k)) (L : ℕ)
    (y : FinitePath (Ω × Row (A := A) roots) L) (q : Fin k) :
    mark q L (KernelTower.pathEquiv (rowPerm roots σ) L y) = mark (σ q) L y := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change (y.1.2 (σ q), mark q L (KernelTower.pathEquiv (rowPerm roots σ) L y.2)) =
      (y.1.2 (σ q), mark (σ q) L y.2)
    rw [ih]

variable {k L : ℕ}
omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem logWeight_rowPerm (roots : Fin k → I) (σ : Equiv.Perm (Fin k))
    (base : FinitePath Ω L → ℝ)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (y : FinitePath (Ω × Row (A := A) roots) L) :
    logWeight base (roots ∘ σ) factor (KernelTower.pathEquiv (rowPerm roots σ) L y) =
      logWeight base roots factor y := by
  simp only [logWeight, physical_rowPerm, mark_rowPerm, Function.comp_apply]
  congr 1
  exact Fintype.sum_equiv σ _ _ (fun _ => rfl)

theorem root_perm (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (σ : Equiv.Perm (Fin k)) :
    root T Q m base (roots ∘ σ) factor = root T Q m base roots factor := by
  have h := KernelTower.backwardLog_transport (rowPerm roots σ) L (tower roots L T Q) m
    (logWeight base (roots ∘ σ) factor)
  have heq : logWeight base (roots ∘ σ) factor ∘ KernelTower.pathEquiv (rowPerm roots σ) L =
      logWeight base roots factor := funext (fun y => logWeight_rowPerm roots σ base factor y)
  simpa only [tower_transport, heq, root] using h

end DilutedSpinGlass.HeterogeneousMarks

 

namespace DilutedSpinGlass.HeterogeneousMarks
open scoped BigOperators
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)] {L : ℕ}

/-- Replacement may change the complete mark alphabet and prior of that term;
it is proved by two independent insertions, not by identifying the alphabets. -/
theorem root_update_bound (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : FinitePath Ω L → ℝ) {k : ℕ} (roots : Fin k → I) (q : Fin k) (i : I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) {C : ℝ}
    (hf : ∀ i x y, |Real.log (factor i x y)| ≤ C) :
    |root T Q m base (Function.update roots q i) factor - root T Q m base roots factor| ≤ 2*C := by
  classical
  cases k with
  | zero => exact Fin.elim0 q
  | succ k =>
    let σ : Equiv.Perm (Fin (k+1)) := Equiv.swap 0 q
    let row := roots ∘ σ
    let tail := Fin.tail row
    have hrows : Function.update roots q i ∘ σ = Fin.cons i tail := by
      funext j
      refine Fin.cases ?_ (fun t => ?_) j
      · simp [σ]
      · have hneq : σ t.succ ≠ q := by
          have h0 : σ 0 = q := Equiv.swap_apply_left _ _
          rw [← h0]
          exact fun h => Fin.succ_ne_zero t (σ.injective h)
        simp only [Function.comp_apply, Function.update_of_ne hneq, Fin.cons_succ]
        rfl
    have hold : roots ∘ σ = Fin.cons (roots q) tail := by
      have hzero : row 0 = roots q := by simp [row, σ]
      rw [← hzero]
      exact (Fin.cons_self_tail row).symm
    rw [← root_perm T Q m base (Function.update roots q i) factor σ,
      ← root_perm T Q m base roots factor σ, hrows, hold]
    have hnew := root_cons_bound T Q m hm base tail i factor (hf i)
    have hold' := root_cons_bound T Q m hm base tail (roots q) factor (hf (roots q))
    calc
      _ ≤ |root T Q m base (Fin.cons i tail) factor - root T Q m base tail factor| +
          |root T Q m base tail factor - root T Q m base (Fin.cons (roots q) tail) factor| :=
        abs_sub_le _ _ _
      _ ≤ C+C := by rw [abs_sub_comm (root T Q m base tail factor)]; exact add_le_add hnew hold'
      _ = 2*C := by ring

/-- Physical disorder changes only the base energy, even with all countably
many type laws available to the finite realized auxiliary row. -/
theorem root_base_stability (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base base' : FinitePath Ω L → ℝ) {k : ℕ} (roots : Fin k → I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) {C : ℝ}
    (hb : ∀ x, |base x-base' x| ≤ C) :
    |root T Q m base roots factor-root T Q m base' roots factor| ≤ C := by
  apply KernelTower.backwardLog_stability L _ m hm
  intro y
  simpa only [logWeight, add_sub_add_right_eq_sub] using hb (physical roots L y)

end DilutedSpinGlass.HeterogeneousMarks



end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_UniformIndexCoupling
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.DilutedSpinGlass.compoundRootLaw_prob _root_.OAI.DilutedSpinGlass.fullRootLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
variable {Ω I X : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [MeasurableSpace X] {L : ℕ}

theorem root_uniform_bound (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j) (base : FinitePath Ω L → ℝ)
    {n : ℕ} (roots : Fin n → I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) {B C : ℝ}
    (hb : ∀ y, |base y| ≤ B) (hf : ∀ i x y, |Real.log (factor i x y)| ≤ C) :
    |root T Q m base roots factor| ≤ B+C*n := by
  have hh := KernelTower.backwardLog_stability L T m hm
    (f := base) (g := fun _ => 0) (by simpa only [sub_zero] using hb)
  rw [KernelTower.backwardLog_const L T m (fun j => ne_of_gt (hm j)) 0, sub_zero] at hh
  exact (abs_root_le T Q m hm base roots factor hf).trans (add_le_add hh le_rfl)

theorem measurable_root (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (base : X → FinitePath Ω L → ℝ) {n : ℕ} (roots : Fin n → I)
    (factor : X → (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (hb : ∀ y, Measurable (fun x => base x y))
    (hf : ∀ i y z, Measurable (fun x => factor x i y z)) :
    Measurable (fun x => root T Q m (base x) roots (factor x)) := by
  apply KernelTower.measurable_backwardLog
  intro y
  exact (hb _).add (Finset.measurable_sum _ (fun j _ => (hf _ _ _).log))

theorem measurable_root_base [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (base : X → FinitePath Ω L → ℝ)
    (hb : ∀ y, Measurable (fun x => base x y))
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) (n : ℕ) :
    Measurable (fun z : X × RootPath I n => root T Q m (base z.1) (rootArray n z.2) factor) := by
  apply measurable_from_prod_countable_left
  intro roots
  exact measurable_root T Q m base (rootArray n roots) (fun _ => factor) hb
    (fun _ _ _ => measurable_const)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_HeterogeneousTwoPoisson
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.DilutedSpinGlass.compoundRootLaw_prob _root_.OAI.DilutedSpinGlass.fullRootLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {I J : Type*} [MeasurableSpace I] [MeasurableSpace J]
    (μ : Measure I) [IsProbabilityMeasure μ] (ν : Measure J) [IsProbabilityMeasure ν]

/-- Quadratic integrability for a genuine random-dimensional root block. -/
theorem poisson_integrable_root_squared (r : ℝ≥0)
    {F : (n : ℕ) → RootPath I n → ℝ} {A D : ℝ}
    (hF : ∀ n x, |F n x| ≤ A+D*n) (c : ℝ) :
    Integrable (fun n : ℕ => ∫ x, (F n x-c)^2 ∂rootLaw n (fun _ => μ)) (poissonMeasure r) := by
  apply poisson_integrable_quadratic r (A := 2*(|A|+|c|)^2) (B := 2*D^2)
  intro n
  apply abs_integral_le_bound
  intro x
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1 : |F n x-c| ≤ |A|+|c|+|D| * n := by
    calc
      _ ≤ |F n x|+|c| := abs_sub _ _
      _ ≤ (A+D*n)+|c| := add_le_add (hF n x) le_rfl
      _ ≤ |A|+|c|+|D| * n := by
        have ha := le_abs_self A
        have hd := mul_le_mul_of_nonneg_right (le_abs_self D) hn
        linarith
  rw [abs_of_nonneg (sq_nonneg _)]
  have hs : (F n x-c)^2 ≤ (|A|+|c|+|D| * n)^2 := by
    nlinarith [sq_abs (F n x-c),abs_nonneg (F n x-c)]
  have hscaled_sq : (|D| * (n : ℝ))^2 = D^2 * (n : ℝ)^2 := by
    rw [mul_pow, sq_abs]
  nlinarith [sq_nonneg ((|A|+|c|)-|D| * n)]

/-- Two independent Poisson families, without converting both counts into
one process or conditioning away either of the count fluctuations. -/
theorem two_poisson_roots_second_moment (r s : ℝ≥0)
    {F : (k : ℕ) → RootPath I k → (n : ℕ) → RootPath J n → ℝ}
    {B C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hF : ∀ k n, Measurable (fun z : RootPath I k × RootPath J n => F k z.1 n z.2))
    (hB : ∀ k x n y, |F k x n y| ≤ B+C*k+D*n)
    (hrep1 : ∀ k (i : Fin k) x z n y, |F k x n y-F k (replaceRoot k x i z) n y| ≤ 2*C)
    (hadd1 : ∀ k z x n y, |F (k+1) (z,x) n y-F k x n y| ≤ C)
    (hrep2 : ∀ k x n (i : Fin n) y z, |F k x n y-F k x n (replaceRoot n y i z)| ≤ 2*D)
    (hadd2 : ∀ k x n z y, |F k x (n+1) (z,y)-F k x n y| ≤ D) (c : ℝ) :
    (∫ k : ℕ, ∫ x, ∫ n : ℕ, ∫ y, (F k x n y-c)^2
      ∂rootLaw n (fun _ => ν) ∂poissonMeasure s ∂rootLaw k (fun _ => μ) ∂poissonMeasure r) ≤
      3*C^2*(r : ℝ)+3*D^2*(s : ℝ)+
      (poissonRootAverage μ r (fun k x => poissonRootAverage ν s (F k x))-c)^2 := by
  let G (k : ℕ) (x : RootPath I k) := poissonRootAverage ν s (F k x)
  have hFm (k : ℕ) (x : RootPath I k) (n : ℕ) : Measurable (F k x n) :=
    (hF k n).comp (measurable_const.prodMk measurable_id)
  have hGm (k : ℕ) : Measurable (G k) := measurable_poissonRootAverage ν s (hF k)
  have hGB (k : ℕ) (x : RootPath I k) : |G k x| ≤ B+C*k+D*(s : ℝ) :=
    poissonRootAverage_bound ν s (hB k x)
  have hGr (k : ℕ) (i : Fin k) (x : RootPath I k) (z : I) :
      |G k x-G k (replaceRoot k x i z)| ≤ 2*C :=
    poissonRootAverage_stability ν s (hFm k x) (hFm k (replaceRoot k x i z))
      (hB k x) (hB k (replaceRoot k x i z)) (hrep1 k i x z)
  have hGa (k : ℕ) (z : I) (x : RootPath I k) : |G (k+1) (z,x)-G k x| ≤ C := by
    apply poissonRootAverage_stability ν s (A := B+C*(k+1)) (B := D)
      (hFm (k+1) (z,x)) (hFm k x)
    · simpa using hB (k+1) (z,x)
    · intro n y
      have h := hB k x n y
      have hk : (k : ℝ) ≤ k+1 := le_add_of_nonneg_right zero_le_one
      nlinarith
    · exact hadd1 k z x
  have houter := poisson_root_second_moment μ r hGm hGB hC hGr hGa c
  have hins (k : ℕ) (x : RootPath I k) :=
    poisson_root_second_moment ν s (hFm k x) (hB k x) hD (hrep2 k x) (hadd2 k x) c
  have hsqi (k : ℕ) : Integrable (fun x => (G k x-c)^2) (rootLaw k (fun _ => μ)) :=
    ((bounded_memLp (hGm k) (hGB k) 2).sub (memLp_const c)).integrable_sq
  have hstep (k : ℕ) :
      (∫ x, ∫ n : ℕ, ∫ y, (F k x n y-c)^2 ∂rootLaw n (fun _ => ν)
        ∂poissonMeasure s ∂rootLaw k (fun _ => μ)) ≤
      ((2*D)^2/2+D^2)*(s : ℝ) + ∫ x, (G k x-c)^2 ∂rootLaw k (fun _ => μ) := by
    have h := integral_mono_of_nonneg (μ := rootLaw k (fun _ => μ))
      (ae_of_all _ (fun _ => integral_nonneg (fun _ => integral_nonneg (fun _ => sq_nonneg _))))
      ((integrable_const (((2*D)^2/2+D^2)*(s : ℝ))).add (hsqi k)) (ae_of_all _ (hins k))
    simp only [Pi.add_apply] at h
    rwa [integral_add (integrable_const _) (hsqi k), integral_const,
      probReal_univ,smul_eq_mul,one_mul] at h
  have hsqint := poisson_integrable_root_squared μ r (A := B+D*(s : ℝ)) (D := C)
    (fun k x => by convert hGB k x using 1; ring) c
  have hnonneg (k : ℕ) : 0 ≤ (∫ x, ∫ n : ℕ, ∫ y, (F k x n y-c)^2
      ∂rootLaw n (fun _ => ν) ∂poissonMeasure s ∂rootLaw k (fun _ => μ)) :=
    integral_nonneg (fun _ => integral_nonneg (fun _ => integral_nonneg (fun _ => sq_nonneg _)))
  have h := integral_mono_of_nonneg (μ := poissonMeasure r)
    (ae_of_all _ hnonneg)
    ((integrable_const (((2*D)^2/2+D^2)*(s : ℝ))).add hsqint) (ae_of_all _ hstep)
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_const _) hsqint,integral_const,probReal_univ,smul_eq_mul,one_mul] at h
  dsimp only [G] at houter
  nlinarith

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_HeterogeneousFullVariance
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.DilutedSpinGlass.compoundRootLaw_prob _root_.OAI.DilutedSpinGlass.fullRootLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

/-- Both random counts and all physical fields contribute to this bound.
The heterogeneous auxiliary priors remain inside the finite power means. -/
theorem full_root_variance
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)] (r s : ℝ≥0)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (hbmeas : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    {B C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ h k x y, |base h k x y| ≤ B+C*k)
    (hf : ∀ i x y, |Real.log (factor i x y)| ≤ D)
    (hrep : ∀ h k (j : Fin k) x z y,
      |base h k x y-base h k (replaceRoot k x j z) y| ≤ 2*C)
    (hadd : ∀ h k z x y, |base h (k+1) (z,x) y-base h k x y| ≤ C)
    (E : Fin M → ℝ)
    (hfield : ∀ j h z k x y, |base h k x y-base (replaceRoot M h j z) k x y| ≤ E j)
    (c : ℝ) :
    let F := fun h k (x : RootPath X k) n (y : RootPath I n) =>
      root T Q m (base h k x) (rootArray n y) factor+c*n
    let G := fun h => poissonRootAverage μ r (fun k x => poissonRootAverage ν s (F h k x))
    (∫ h, ∫ k : ℕ, ∫ x, ∫ n : ℕ, ∫ y, (F h k x n y-(∫ z, G z ∂rootLaw M ξ))^2
      ∂rootLaw n (fun _ => ν) ∂poissonMeasure s ∂rootLaw k (fun _ => μ)
        ∂poissonMeasure r ∂rootLaw M ξ) ≤
      3*C^2*(r : ℝ)+3*(D+|c|)^2*(s : ℝ)+∑ j, (E j)^2/2 := by
  dsimp only
  let F := fun h k (x : RootPath X k) n (y : RootPath I n) =>
    root T Q m (base h k x) (rootArray n y) factor+c*n
  let H := fun h k x => poissonRootAverage ν s (F h k x)
  let G := fun h => poissonRootAverage μ r (H h)
  have hF (k n : ℕ) : Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n =>
      F z.1.1 k z.1.2 n z.2) :=
    (measurable_root_base T Q m (fun z : RootPath Y M × RootPath X k => base z.1 k z.2) (hbmeas k) factor n).add measurable_const
  have hFh (h : RootPath Y M) (k n : ℕ) :
      Measurable (fun z : RootPath X k × RootPath I n => F h k z.1 n z.2) :=
    (hF k n).comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hFm (h : RootPath Y M) (k : ℕ) (x : RootPath X k) (n : ℕ) :
      Measurable (F h k x n) := (hFh h k n).comp (measurable_const.prodMk measurable_id)
  have hB (h : RootPath Y M) (k : ℕ) (x : RootPath X k) (n : ℕ) (y : RootPath I n) :
      |F h k x n y| ≤ B+C*k+(D+|c|)*n := by
    have hh := root_uniform_bound T Q m hm (base h k x) (rootArray n y) factor (hb h k x) hf
    calc
      _ ≤ |root T Q m (base h k x) (rootArray n y) factor|+|c*(n:ℝ)| := abs_add_le _ _
      _ ≤ B+C*k+D*n+|c| *n := by
        rw [abs_mul,abs_of_nonneg (show (0:ℝ) ≤ n from Nat.cast_nonneg n)]
        exact add_le_add hh le_rfl
      _ = _ := by ring
  have hH (k : ℕ) : Measurable (fun z : RootPath Y M × RootPath X k => H z.1 k z.2) :=
    measurable_poissonRootAverage ν s (hF k)
  have hG : Measurable G := measurable_poissonRootAverage μ r hH
  have hHB (h : RootPath Y M) (k : ℕ) (x : RootPath X k) :
      |H h k x| ≤ B+C*k+(D+|c|)*(s:ℝ) := poissonRootAverage_bound ν s (hB h k x)
  have hGB (h : RootPath Y M) : |G h| ≤ (B+(D+|c|)*(s:ℝ))+C*r := by
    apply poissonRootAverage_bound μ r
    intro k x
    convert hHB h k x using 1 <;> first | rfl | ring
  have hHE (j : Fin M) (h : RootPath Y M) (z : Y) (k : ℕ) (x : RootPath X k) :
      |H h k x-H (replaceRoot M h j z) k x| ≤ E j := by
    apply poissonRootAverage_stability ν s (hFm h k x) (hFm (replaceRoot M h j z) k x)
      (hB h k x) (hB (replaceRoot M h j z) k x)
    intro n y
    dsimp only [F]
    rw [add_sub_add_right_eq_sub]
    exact root_base_stability T Q m hm _ _ _ factor (hfield j h z k x)
  have hGE (j : Fin M) (h : RootPath Y M) (z : Y) : |G h-G (replaceRoot M h j z)| ≤ E j := by
    apply poissonRootAverage_stability μ r (A := B+(D+|c|)*(s:ℝ)) (B := C)
      (fun k => (hH k).comp (measurable_const.prodMk measurable_id))
      (fun k => (hH k).comp (measurable_const.prodMk measurable_id))
    · intro k x; simpa only [add_right_comm, Function.comp_apply, id_eq] using hHB h k x
    · intro k x; simpa only [add_right_comm, Function.comp_apply, id_eq] using hHB (replaceRoot M h j z) k x
    · exact hHE j h z
  have hv := root_variance_bound M ξ hG hGB E hGE
  have hrep1 (h : RootPath Y M) (k : ℕ) (j : Fin k) (x : RootPath X k) (z : X)
      (n : ℕ) (y : RootPath I n) :
      |F h k x n y-F h k (replaceRoot k x j z) n y| ≤ 2*C := by
    dsimp only [F]
    rw [add_sub_add_right_eq_sub]
    exact root_base_stability T Q m hm _ _ _ factor (hrep h k j x z)
  have hadd1 (h : RootPath Y M) (k : ℕ) (z : X) (x : RootPath X k)
      (n : ℕ) (y : RootPath I n) : |F h (k+1) (z,x) n y-F h k x n y| ≤ C := by
    dsimp only [F]
    rw [add_sub_add_right_eq_sub]
    exact root_base_stability T Q m hm _ _ _ factor (hadd h k z x)
  have hrep2 (h : RootPath Y M) (k : ℕ) (x : RootPath X k) (n : ℕ)
      (j : Fin n) (y : RootPath I n) (z : I) :
      |F h k x n y-F h k x n (replaceRoot n y j z)| ≤ 2*(D+|c|) := by
    dsimp only [F]
    rw [add_sub_add_right_eq_sub,rootArray_replace,abs_sub_comm]
    exact (root_update_bound T Q m hm _ _ j z factor hf).trans (by linarith [abs_nonneg c])
  have hadd2 (h : RootPath Y M) (k : ℕ) (x : RootPath X k) (n : ℕ)
      (z : I) (y : RootPath I n) : |F h k x (n+1) (z,y)-F h k x n y| ≤ D+|c| := by
    change |root T Q m (base h k x) (Fin.cons z (rootArray n y)) factor+c*(n+1:ℕ)-
      (root T Q m (base h k x) (rootArray n y) factor+c*n)| ≤ _
    rw [Nat.cast_add,Nat.cast_one]
    calc
      _ = |root T Q m (base h k x) (Fin.cons z (rootArray n y)) factor-
        root T Q m (base h k x) (rootArray n y) factor+c| := by congr 1; ring
      _ ≤ |root T Q m (base h k x) (Fin.cons z (rootArray n y)) factor-
        root T Q m (base h k x) (rootArray n y) factor|+|c| := abs_add_le _ _
      _ ≤ D+|c| := add_le_add (root_cons_bound T Q m hm _ _ z factor (hf z)) le_rfl
  have hstep (h : RootPath Y M) := two_poisson_roots_second_moment μ ν r s hC
    (add_nonneg hD (abs_nonneg c)) (hFh h) (hB h) (hrep1 h) (hadd1 h) (hrep2 h) (hadd2 h)
    (∫ z, G z ∂rootLaw M ξ)
  have hi : Integrable (fun h => (G h-∫ z, G z ∂rootLaw M ξ)^2) (rootLaw M ξ) :=
    ((bounded_memLp hG hGB 2).sub (memLp_const (∫ z, G z ∂rootLaw M ξ))).integrable_sq
  have hnn (h : RootPath Y M) : 0 ≤ (∫ k : ℕ, ∫ x, ∫ n : ℕ, ∫ y,
      (F h k x n y-∫ z, G z ∂rootLaw M ξ)^2 ∂rootLaw n (fun _ => ν)
      ∂poissonMeasure s ∂rootLaw k (fun _ => μ) ∂poissonMeasure r) :=
    integral_nonneg (fun _ => integral_nonneg (fun _ => integral_nonneg (fun _ =>
      integral_nonneg (fun _ => sq_nonneg _))))
  have hh := integral_mono_of_nonneg (μ := rootLaw M ξ) (ae_of_all _ hnn)
    ((integrable_const (3*C^2*(r:ℝ)+3*(D+|c|)^2*(s:ℝ))).add hi) (ae_of_all _ hstep)
  simp only [Pi.add_apply] at hh
  rw [integral_add (integrable_const _) hi,integral_const,probReal_univ,smul_eq_mul,one_mul] at hh
  have heq : (∫ h, (G h-∫ z, G z ∂rootLaw M ξ)^2 ∂rootLaw M ξ) =
      variance G (rootLaw M ξ) := (variance_eq_integral hG.aemeasurable).symm
  change _ ≤ _
  exact hh.trans (add_le_add le_rfl (heq.le.trans hv))

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_JointRootLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {X I Y : Type} [MeasurableSpace X] [MeasurableSpace I] [MeasurableSpace Y] {M : ℕ}

theorem measurable_packRoot
    {F : RootPath Y M → (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → ℝ}
    (hF : ∀ k n, Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n => F z.1.1 k z.1.2 n z.2)) :
    Measurable (packRoot F) := by
  have hn (k : ℕ) : Measurable (fun z : (RootPath Y M × RootPath X k) × Sigma (RootPath I) =>
      F z.1.1 k z.1.2 z.2.1 z.2.2) := measurable_prodSigma (f := fun (z : RootPath Y M × RootPath X k) n y => F z.1 k z.2 n y) (hF k)
  have hk : Measurable (fun z : (RootPath Y M × Sigma (RootPath I)) × Sigma (RootPath X) =>
      F z.1.1 z.2.1 z.2.2 z.1.2.1 z.1.2.2) :=
    measurable_prodSigma (f := fun (z : RootPath Y M × Sigma (RootPath I)) k x => F z.1 k x z.2.1 z.2.2) (fun k => (hn k).comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd))
  exact hk.comp ((measurable_fst.prodMk measurable_snd.snd).prodMk measurable_snd.fst)

variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (r s : ℝ≥0)

theorem fullRoot_memLp_linear
    {F : RootPath Y M → (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → ℝ}
    (hF : ∀ k n, Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n => F z.1.1 k z.1.2 n z.2))
    {B C D : ℝ} (hb : ∀ h k x n y, |F h k x n y| ≤ B+C*k+D*n) :
    MemLp (packRoot F) 2 (fullRootLaw ξ μ ν r s) := by
  have hk := ((familyPoisson_count_memLp (fun k => rootLaw k (fun _ => μ)) r).comp_fst
    (compoundRootLaw ν s)).comp_snd (rootLaw M ξ)
  have hn := ((familyPoisson_count_memLp (fun n => rootLaw n (fun _ => ν)) s).comp_snd
    (compoundRootLaw μ r)).comp_snd (rootLaw M ξ)
  have he : MemLp (fun z : FullRootState Y X I M => B+C*z.2.1.1+D*z.2.2.1) 2
      (fullRootLaw ξ μ ν r s) := (memLp_const B).add (hk.const_mul C) |>.add (hn.const_mul D)
  exact he.mono' (measurable_packRoot hF).aestronglyMeasurable (ae_of_all _ (fun z => by
    simpa only [Real.norm_eq_abs,packRoot] using hb z.1 z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2))

/-- Quadratic envelopes allow both the pressure and its square to be passed
through the two independent compound laws, without any count cut-off. -/
theorem fullRoot_integrable_quadratic
    {F : RootPath Y M → (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → ℝ}
    (hF : ∀ k n, Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n => F z.1.1 k z.1.2 n z.2))
    {B C D : ℝ} (hb : ∀ h k x n y, |F h k x n y| ≤ B+C*(k:ℝ)^2+D*(n:ℝ)^2) :
    Integrable (packRoot F) (fullRootLaw ξ μ ν r s) := by
  have hk := (((familyPoisson_count_memLp (fun k => rootLaw k (fun _ => μ)) r).integrable_sq).comp_fst
    (compoundRootLaw ν s)).comp_snd (rootLaw M ξ)
  have hn := (((familyPoisson_count_memLp (fun n => rootLaw n (fun _ => ν)) s).integrable_sq).comp_snd
    (compoundRootLaw μ r)).comp_snd (rootLaw M ξ)
  have he : Integrable (fun z : FullRootState Y X I M => B+C*(z.2.1.1:ℝ)^2+D*(z.2.2.1:ℝ)^2)
      (fullRootLaw ξ μ ν r s) := (integrable_const B).add (hk.const_mul C) |>.add (hn.const_mul D)
  exact he.mono' (measurable_packRoot hF).aestronglyMeasurable (ae_of_all _ (fun z => by
    simpa only [Real.norm_eq_abs,packRoot] using hb z.1 z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2))


theorem twoCompound_integrable_quadratic
    {F : (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → ℝ}
    (hF : Measurable (fun z : Sigma (RootPath X) × Sigma (RootPath I) => F z.1.1 z.1.2 z.2.1 z.2.2))
    {B C D : ℝ} (hb : ∀ k x n y, |F k x n y| ≤ B+C*(k:ℝ)^2+D*(n:ℝ)^2) :
    Integrable (fun z : Sigma (RootPath X) × Sigma (RootPath I) => F z.1.1 z.1.2 z.2.1 z.2.2)
      ((compoundRootLaw μ r).prod (compoundRootLaw ν s)) := by
  have hk := ((familyPoisson_count_memLp (fun k => rootLaw k (fun _ => μ)) r).integrable_sq).comp_fst
    (compoundRootLaw ν s)
  have hn := ((familyPoisson_count_memLp (fun n => rootLaw n (fun _ => ν)) s).integrable_sq).comp_snd
    (compoundRootLaw μ r)
  have he : Integrable (fun z : Sigma (RootPath X) × Sigma (RootPath I) =>
      B+C*(z.1.1:ℝ)^2+D*(z.2.1:ℝ)^2) ((compoundRootLaw μ r).prod (compoundRootLaw ν s)) :=
    (integrable_const B).add (hk.const_mul C) |>.add (hn.const_mul D)
  exact he.mono' hF.aestronglyMeasurable (ae_of_all _ (fun z => by
    simpa only [Real.norm_eq_abs] using hb z.1.1 z.1.2 z.2.1 z.2.2))

/-- Exact Fubini identity for the full root law, with all count-dependent
root spaces and all physical fields retained. -/
theorem integral_fullRootLaw_quadratic
    {F : RootPath Y M → (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → ℝ}
    (hF : ∀ k n, Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n => F z.1.1 k z.1.2 n z.2))
    {B C D : ℝ} (hb : ∀ h k x n y, |F h k x n y| ≤ B+C*(k:ℝ)^2+D*(n:ℝ)^2) :
    (∫ z, packRoot F z ∂fullRootLaw ξ μ ν r s) =
      ∫ h, ∫ k : ℕ, ∫ x, ∫ n : ℕ, ∫ y, F h k x n y
        ∂rootLaw n (fun _ => ν) ∂poissonMeasure s ∂rootLaw k (fun _ => μ)
          ∂poissonMeasure r ∂rootLaw M ξ := by
  have hm := measurable_packRoot hF
  rw [fullRootLaw,integral_prod _ (fullRoot_integrable_quadratic ξ μ ν r s hF hb)]
  apply integral_congr_ae
  apply ae_of_all
  intro h
  have hhm : Measurable (fun z : Sigma (RootPath X) × Sigma (RootPath I) =>
      F h z.1.1 z.1.2 z.2.1 z.2.2) := hm.comp (measurable_const.prodMk measurable_id)
  have hhi := twoCompound_integrable_quadratic μ ν r s hhm (hb h)
  change (∫ z, F h z.1.1 z.1.2 z.2.1 z.2.2 ∂(compoundRootLaw μ r).prod (compoundRootLaw ν s)) = _
  rw [integral_prod _ hhi]
  have hg (k : ℕ) : Measurable (fun x : RootPath X k =>
      ∫ z : Sigma (RootPath I), F h k x z.1 z.2 ∂compoundRootLaw ν s) := by
    have hh : Measurable (fun z : RootPath X k × Sigma (RootPath I) => F h k z.1 z.2.1 z.2.2) :=
      hhm.comp (((measurable_sigmaMk k).comp measurable_fst).prodMk measurable_snd)
    exact hh.stronglyMeasurable.integral_prod_right'.measurable
  change (∫ z : Sigma (RootPath X), ∫ w : Sigma (RootPath I),
    F h z.1 z.2 w.1 w.2 ∂compoundRootLaw ν s
      ∂familyLaw (poissonMeasure r) (fun k => rootLaw k (fun _ => μ))) = _
  rw [integral_familyLaw (poissonMeasure r) (fun k => rootLaw k (fun _ => μ))
    (fun k x => ∫ z : Sigma (RootPath I), F h k x z.1 z.2 ∂compoundRootLaw ν s)
      hg hhi.integral_prod_left]
  apply integral_congr_ae
  apply ae_of_all
  intro k
  apply integral_congr_ae
  apply ae_of_all
  intro x
  have hfm (n : ℕ) : Measurable (F h k x n) :=
    (hF k n).comp ((measurable_const.prodMk measurable_const).prodMk measurable_id)
  exact integral_familyLaw (poissonMeasure s) (fun n => rootLaw n (fun _ => ν))
    (F h k x) hfm
    (familyLaw_integrable_bound (poissonMeasure s) (fun n => rootLaw n (fun _ => ν))
      (F h k x) hfm
      ((integrable_const (B+C*(k:ℝ)^2)).add ((poisson_integrable_count_sq s).const_mul D))
      (hb h k x))

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_AnchorExtension
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace DilutedSpinGlass.KernelTower
variable {Ω : Type} [Fintype Ω]
@[simp] theorem tilt_const (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (hm : ∀ j, m j ≠ 0) (c : ℝ) : tilt n T m (fun _ => c) = T := by
  induction n with
  | zero =>
    change () = T
    cases T
    rfl
  | succ n ih =>
    simp only [tilt, backwardLog_const n _ _ (fun j => hm j.succ),
      FiniteLaw.tilt_const, ih _ _ (fun j => hm j.succ)]
    cases T
    rfl
end DilutedSpinGlass.KernelTower

open Filter Set
open scoped Topology BigOperators

end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_SpinRootData
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.DilutedSpinGlass.compoundRootLaw_prob _root_.OAI.DilutedSpinGlass.fullRootLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {N : ℕ}

theorem sum_update_difference {Z : Type*} {n : ℕ} (g : Fin n → Z → ℝ)
    (x : Fin n → Z) (q : Fin n) (z : Z) :
    (∑ j, g j (x j))-(∑ j, g j (Function.update x q z j)) = g q (x q)-g q z := by
  classical
  rw [← Finset.sum_sub_distrib,Finset.sum_eq_single q]
  · simp only [Function.update_self]
  · intro j _ hj
    simp only [Function.update_of_ne hj,sub_self]
  · simp

theorem abs_spin (s : Spin) : |spin s| = 1 := by
  cases s <;> norm_num [spin]

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem energy_bound (V : X → (Fin N → Spin) → ℝ) (field : Y → ℝ)
    {C H : ℝ} (hV : ∀ x σ, |V x σ| ≤ C) (hh : ∀ y, |field y| ≤ H)
    (h : RootPath Y N) (k : ℕ) (x : RootPath X k) (σ : Fin N → Spin) :
    |energy V field h k x σ| ≤ H*N+C*k := by
  apply (abs_add_le _ _).trans
  have hx := (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin k))) => hV (rootArray k x j) σ))
  have hy : |∑ i, field (rootArray N h i)*spin (σ i)| ≤ H*N := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _i : Fin N, H := Finset.sum_le_sum (fun i _ => by
        simpa only [abs_mul,abs_spin,mul_one] using hh (rootArray N h i))
      _ = H*N := by simp [mul_comm]
  have hx' : |∑ j, V (rootArray k x j) σ| ≤ C*k := by simpa [mul_comm] using hx
  linarith

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem energy_replace_interaction (V : X → (Fin N → Spin) → ℝ) (field : Y → ℝ)
    {C : ℝ} (hV : ∀ x σ, |V x σ| ≤ C) (h : RootPath Y N)
    (k : ℕ) (q : Fin k) (x : RootPath X k) (z : X) (σ : Fin N → Spin) :
    |energy V field h k x σ-energy V field h k (replaceRoot k x q z) σ| ≤ 2*C := by
  simp only [energy,add_sub_add_right_eq_sub,rootArray_replace]
  rw [sum_update_difference (fun _ v => V v σ) (rootArray k x) q z]
  exact (abs_sub _ _).trans (by linarith [hV (rootArray k x q) σ,hV z σ])

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem energy_add_interaction (V : X → (Fin N → Spin) → ℝ) (field : Y → ℝ)
    {C : ℝ} (hV : ∀ x σ, |V x σ| ≤ C) (h : RootPath Y N)
    (k : ℕ) (z : X) (x : RootPath X k) (σ : Fin N → Spin) :
    |energy V field h (k+1) (z,x) σ-energy V field h k x σ| ≤ C := by
  simpa only [energy,add_sub_add_right_eq_sub,rootArray,Fin.sum_univ_succ,
    Fin.cons_zero,Fin.cons_succ,add_sub_cancel_right] using hV z σ

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem energy_replace_field (V : X → (Fin N → Spin) → ℝ) (field : Y → ℝ)
    {H : ℝ} (hh : ∀ y, |field y| ≤ H) (h : RootPath Y N) (q : Fin N) (z : Y)
    (k : ℕ) (x : RootPath X k) (σ : Fin N → Spin) :
    |energy V field h k x σ-energy V field (replaceRoot N h q z) k x σ| ≤ 2*H := by
  simp only [energy,add_sub_add_left_eq_sub,rootArray_replace]
  rw [sum_update_difference (fun i v => field v*spin (σ i)) (rootArray N h) q z,
    ← sub_mul,abs_mul,abs_spin,mul_one]
  exact (abs_sub _ _).trans (by linarith [hh (rootArray N h q),hh z])

end DilutedSpinGlass.PhysicalRoot
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RegularDepth
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
variable {X I Y : Type} [MeasurableSpace X] [MeasurableSpace I] [MeasurableSpace Y] {M : ℕ}
variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (r s : ℝ≥0)

theorem fullRoot_variance_eq
    {F : RootPath Y M → (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → ℝ}
    (hF : ∀ k n, Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n => F z.1.1 k z.1.2 n z.2))
    {B C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ h k x n y, |F h k x n y| ≤ B+C*k+D*n) :
    variance (packRoot F) (fullRootLaw ξ μ ν r s) =
      ∫ h, ∫ k : ℕ, ∫ x, ∫ n : ℕ, ∫ y,
        (F h k x n y-(∫ h', ∫ k' : ℕ, ∫ x', ∫ n' : ℕ, ∫ y', F h' k' x' n' y'
          ∂rootLaw n' (fun _ => ν) ∂poissonMeasure s ∂rootLaw k' (fun _ => μ)
            ∂poissonMeasure r ∂rootLaw M ξ))^2
        ∂rootLaw n (fun _ => ν) ∂poissonMeasure s ∂rootLaw k (fun _ => μ)
          ∂poissonMeasure r ∂rootLaw M ξ := by
  have hk (k : ℕ) : C*k ≤ C+C*(k:ℝ)^2 := by
    have h : (k:ℝ) ≤ 1+(k:ℝ)^2 := by nlinarith [sq_nonneg ((k:ℝ)-(1:ℝ)/2)]
    nlinarith [mul_le_mul_of_nonneg_left h hC]
  have hn (n : ℕ) : D*n ≤ D+D*(n:ℝ)^2 := by
    have h : (n:ℝ) ≤ 1+(n:ℝ)^2 := by nlinarith [sq_nonneg ((n:ℝ)-(1:ℝ)/2)]
    nlinarith [mul_le_mul_of_nonneg_left h hD]
  have hbq h k x n y : |F h k x n y| ≤ (B+C+D)+C*(k:ℝ)^2+D*(n:ℝ)^2 := by
    linarith [hb h k x n y,hk k,hn n]
  have he := integral_fullRootLaw_quadratic ξ μ ν r s hF hbq
  let center := ∫ z, packRoot F z ∂fullRootLaw ξ μ ν r s
  have hsq h k x n y : |(F h k x n y-center)^2| ≤
      3*(|B|+|center|)^2+3*C^2*(k:ℝ)^2+3*D^2*(n:ℝ)^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    have hbd : |F h k x n y-center| ≤ (|B|+|center|)+C*k+D*n := by
      have hh := abs_sub (F h k x n y) center
      linarith [hb h k x n y,le_abs_self B]
    have ha := abs_nonneg (F h k x n y-center)
    have hh : (F h k x n y-center)^2 ≤ ((|B|+|center|)+C*k+D*n)^2 := by
      nlinarith [sq_abs (F h k x n y-center)]
    nlinarith [sq_nonneg ((|B|+|center|)-C*k),sq_nonneg ((|B|+|center|)-D*n),
      sq_nonneg (C*k-D*n)]
  rw [variance_eq_integral (measurable_packRoot hF).aemeasurable]
  change (∫ z, packRoot (fun h k x n y => (F h k x n y-center)^2) z ∂fullRootLaw ξ μ ν r s) = _
  rw [integral_fullRootLaw_quadratic ξ μ ν r s
    (fun k n => ((hF k n).sub measurable_const).pow_const 2) hsq]
  dsimp only [center]
  rw [he]

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ActualRootVariance
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

/-- The concentration estimate under one genuine product probability measure,
with independent physical fields and both Poisson reservoirs. -/
theorem variance_actual_root
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)] (r s : ℝ≥0)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (hbmeas : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    {B C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ h k x y, |base h k x y| ≤ B+C*k)
    (hf : ∀ i x y, |Real.log (factor i x y)| ≤ D)
    (hrep : ∀ h k (j : Fin k) x z y,
      |base h k x y-base h k (replaceRoot k x j z) y| ≤ 2*C)
    (hadd : ∀ h k z x y, |base h (k+1) (z,x) y-base h k x y| ≤ C)
    (E : Fin M → ℝ)
    (hfield : ∀ j h z k x y, |base h k x y-base (replaceRoot M h j z) k x y| ≤ E j)
    (c : ℝ) :
    variance (packRoot (fun h k x n y => root T Q m (base h k x) (rootArray n y) factor+c*n))
      (fullRootLaw ξ μ ν r s) ≤
      3*C^2*(r : ℝ)+3*(D+|c|)^2*(s : ℝ)+∑ j, (E j)^2/2 := by
  have hF (k n : ℕ) : Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n =>
      root T Q m (base z.1.1 k z.1.2) (rootArray n z.2) factor+c*n) :=
    (measurable_root_base T Q m (fun z : RootPath Y M × RootPath X k => base z.1 k z.2) (hbmeas k) factor n).add measurable_const
  have hB (h : RootPath Y M) (k : ℕ) (x : RootPath X k) (n : ℕ) (y : RootPath I n) :
      |root T Q m (base h k x) (rootArray n y) factor+c*n| ≤ B+C*k+(D+|c|)*n := by
    have hh := root_uniform_bound T Q m hm (base h k x) (rootArray n y) factor (hb h k x) hf
    calc
      _ ≤ |root T Q m (base h k x) (rootArray n y) factor|+|c*(n:ℝ)| := abs_add_le _ _
      _ ≤ B+C*k+D*n+|c| *n := by
        rw [abs_mul,abs_of_nonneg (show (0:ℝ) ≤ n from Nat.cast_nonneg n)]
        exact add_le_add hh le_rfl
      _ = _ := by ring
  rw [fullRoot_variance_eq ξ μ ν r s hF hC (add_nonneg hD (abs_nonneg c)) hB]
  exact full_root_variance μ ν ξ r s T Q m hm base hbmeas factor hC hD hb hf hrep hadd E hfield c

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CountedSteps
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
variable {Ω I : Type} {A : I → Type} {L n : ℕ}

theorem selectedCoefficient_bound (roots : Fin n → I) (sel : I → Bool)
    (D : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (hD : ∀ i x y, |D i x y| ≤ 1) (q : Fin n) (y : FinitePath (Ω × Row (A := A) roots) L) :
    |selectedCoefficient roots sel D q y| ≤ 1 := by
  unfold selectedCoefficient
  split
  · exact hD _ _ _
  · norm_num

/-- Every unselected term remains in the same log weight and the same finite
mark prior. This is an identity, not a distributional truncation. -/
theorem selected_perturbLog_eq (base : FinitePath Ω L → ℝ) (roots : Fin n → I)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) :
    KernelTower.perturbLog (otherLog base roots sel fixed)
      (selectedCoefficient roots sel D) (selectedCoefficient roots sel E) t u =
      logWeight base roots (selectedFactor sel fixed D E t u) := by
  funext y
  unfold KernelTower.perturbLog otherLog logWeight
  rw [add_assoc,← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  cases h : sel (roots q) <;> simp [selectedFactor,selectedCoefficient,h]

variable [Fintype Ω] [∀ i, Fintype (A i)]

theorem corrected_log_eq (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (base : FinitePath Ω L → ℝ) (roots : Fin n → I)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) :
    KernelTower.correctedPerturbLog (tower roots L T Q) m (otherLog base roots sel fixed)
      (selectedCoefficient roots sel D) (selectedCoefficient roots sel E) t u =
      root T Q m base roots (selectedFactor sel fixed D E t u)+2*n*u^2 := by
  rw [KernelTower.correctedPerturbLog,selected_perturbLog_eq]
  rfl

theorem corrected_score_eq (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (base : FinitePath Ω L → ℝ) (roots : Fin n → I)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) :
    KernelTower.correctedPerturbScore (tower roots L T Q) m (otherLog base roots sel fixed)
      (selectedCoefficient roots sel D) (selectedCoefficient roots sel E) t u =
      selectedScore T Q m base roots sel fixed D E t u+4*n*u := by
  rw [KernelTower.correctedPerturbScore,selected_perturbLog_eq]
  rfl

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_JointRootParam
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
variable {X I Y U : Type} [MeasurableSpace X] [MeasurableSpace I] [MeasurableSpace Y] [MeasurableSpace U] {M : ℕ}

/-- Joint measurability through both random counts, with an external parameter. -/
theorem measurable_packRoot_param
    {F : RootPath Y M → (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → U → ℝ}
    (hF : ∀ k n, Measurable (fun z : ((RootPath Y M × RootPath X k) × RootPath I n) × U => F z.1.1.1 k z.1.1.2 n z.1.2 z.2)) :
    Measurable (fun z : FullRootState Y X I M × U => packRoot (fun h k x n y => F h k x n y z.2) z.1) := by
  have hn (k : ℕ) : Measurable (fun z : ((RootPath Y M × RootPath X k) × U) × Sigma (RootPath I) =>
      F z.1.1.1 k z.1.1.2 z.2.1 z.2.2 z.1.2) :=
    measurable_prodSigma (f := fun (z : (RootPath Y M × RootPath X k) × U) n y => F z.1.1 k z.1.2 n y z.2)
      (fun n => (hF k n).comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd))
  have hk : Measurable (fun z : ((RootPath Y M × Sigma (RootPath I)) × U) × Sigma (RootPath X) =>
      F z.1.1.1 z.2.1 z.2.2 z.1.1.2.1 z.1.1.2.2 z.1.2) :=
    measurable_prodSigma (f := fun (z : (RootPath Y M × Sigma (RootPath I)) × U) k x => F z.1.1 k x z.1.2.1 z.1.2.2 z.2)
      (fun k => (hn k).comp (((measurable_fst.fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd).prodMk measurable_fst.fst.snd))
  exact hk.comp (((measurable_fst.fst.prodMk measurable_fst.snd.snd).prodMk measurable_snd).prodMk measurable_fst.snd.fst)

variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (r s : ℝ≥0)

omit [MeasurableSpace U] in
theorem fullRoot_count_memLp :
    MemLp (fun z : FullRootState Y X I M => (z.2.2.1 : ℝ)) 2 (fullRootLaw ξ μ ν r s) := by
  exact ((familyPoisson_count_memLp (fun n => rootLaw n (fun _ => ν)) s).comp_snd
    (compoundRootLaw μ r)).comp_snd (rootLaw M ξ)

omit [MeasurableSpace U] in
theorem fullRoot_count_mean :
    (∫ z : FullRootState Y X I M, (z.2.2.1 : ℝ) ∂fullRootLaw ξ μ ν r s) = s := by
  change (∫ z, (fun w : Sigma (RootPath X) × Sigma (RootPath I) => (w.2.1:ℝ)) z.2
    ∂(rootLaw M ξ).prod ((compoundRootLaw μ r).prod (compoundRootLaw ν s))) = _
  rw [integral_fun_snd (fun w : Sigma (RootPath X) × Sigma (RootPath I) => (w.2.1:ℝ)),
    integral_fun_snd (fun w : Sigma (RootPath I) => (w.1:ℝ))]
  simp only [probReal_univ,one_smul]
  exact familyPoisson_count_mean (fun n => rootLaw n (fun _ => ν)) s

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FullCountCorrection
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
variable {X I Y : Type} [MeasurableSpace X] [MeasurableSpace I] [MeasurableSpace Y] {M : ℕ}
variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (r s : ℝ≥0)

theorem fullRoot_count_deviation :
    rootDeviation (fullRootLaw ξ μ ν r s) (fun z : FullRootState Y X I M => (z.2.2.1:ℝ)) ≤ Real.sqrt s := by
  rw [rootDeviation,fullRoot_count_mean]
  change (∫ z, (fun w : Sigma (RootPath X) × Sigma (RootPath I) => |(w.2.1:ℝ)-s|) z.2
    ∂(rootLaw M ξ).prod ((compoundRootLaw μ r).prod (compoundRootLaw ν s))) ≤ _
  rw [integral_fun_snd (fun w : Sigma (RootPath X) × Sigma (RootPath I) => |(w.2.1:ℝ)-s|),
    integral_fun_snd (fun w : Sigma (RootPath I) => |(w.1:ℝ)-s|)]
  simp only [probReal_univ,one_smul]
  exact familyPoisson_count_deviation (fun n => rootLaw n (fun _ => ν)) s

theorem fullRoot_deviation_sub_count {f : FullRootState Y X I M → ℝ}
    (hf : Integrable f (fullRootLaw ξ μ ν r s)) (c : ℝ) :
    rootDeviation (fullRootLaw ξ μ ν r s) (fun z => f z-c*(z.2.2.1:ℝ)) ≤
      rootDeviation (fullRootLaw ξ μ ν r s) f+|c| *Real.sqrt s := by
  have h := rootDeviation_sub_le (fullRootLaw ξ μ ν r s) hf
    (((fullRoot_count_memLp ξ μ ν r s).integrable (by norm_num)).const_mul c)
  rw [rootDeviation_smul] at h
  exact h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (fullRoot_count_deviation ξ μ ν r s) (abs_nonneg c)))

theorem fullRoot_deviation_sub_count_integral
    {G : FullRootState Y X I M → ℝ → ℝ}
    (hG : Measurable (fun z : FullRootState Y X I M × ℝ => G z.1 z.2))
    {B : FullRootState Y X I M → ℝ} (hB : Integrable B (fullRootLaw ξ μ ν r s))
    {a b : ℝ} (hab : a ≤ b)
    (hb : ∀ z u, u ∈ Icc a b → |G z u| ≤ B z)
    {c : ℝ → ℝ} (hc : Measurable c) (hcb : ∀ u ∈ Icc a b, |c u| ≤ 1) :
    (∫ u in a..b, rootDeviation (fullRootLaw ξ μ ν r s)
      (fun z => G z u-c u*(z.2.2.1:ℝ))) ≤
    (∫ u in a..b, rootDeviation (fullRootLaw ξ μ ν r s) (fun z => G z u)) +
      (b-a)*Real.sqrt s := by
  let P := fullRootLaw ξ μ ν r s
  have hcount : Measurable (fun z : FullRootState Y X I M × ℝ => (z.1.2.2.1:ℝ)) :=
    (measurable_sigmaUncurry (f := fun n (_ : RootPath I n) => (n:ℝ))
      (fun _ => measurable_const)).comp measurable_fst.snd.snd
  have hci := (fullRoot_count_memLp ξ μ ν r s).integrable (by norm_num)
  have hF : Measurable (fun z : FullRootState Y X I M × ℝ => G z.1 z.2-c z.2*(z.1.2.2.1:ℝ)) :=
    hG.sub ((hc.comp measurable_snd).mul hcount)
  have hFi : IntervalIntegrable (fun u => rootDeviation P
      (fun z => G z u-c u*(z.2.2.1:ℝ))) volume a b := by
    apply intervalIntegrable_rootDeviation P hF (hB.add hci) hab
    intro z u hu
    have hn : 0 ≤ (z.2.2.1:ℝ) := Nat.cast_nonneg _
    simpa only [Pi.add_apply] using
      (abs_sub (G z u) (c u*(z.2.2.1:ℝ))).trans
        (add_le_add (hb z u hu) (by rw [abs_mul,abs_of_nonneg hn]; nlinarith [hcb u hu]))
  have hGi := intervalIntegrable_rootDeviation P hG hB hab hb
  have hh := intervalIntegral.integral_mono_on hab hFi (hGi.add intervalIntegrable_const)
    (fun u hu => (fullRoot_deviation_sub_count ξ μ ν r s
      (hB.mono' (hG.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
        (ae_of_all _ (fun z => by change |G z u| ≤ B z; exact hb z u hu))) (c u)).trans
          (add_le_add le_rfl (show |c u| *Real.sqrt s ≤ Real.sqrt s by
            nlinarith [hcb u hu,Real.sqrt_nonneg (s:ℝ)])))
  simpa only [intervalIntegral.integral_add hGi intervalIntegrable_const,
    intervalIntegral.integral_const,smul_eq_mul] using hh

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_SelectedRegularity
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)] {L n : ℕ}

omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem selectedFactor_log_bound (sel : I → Bool)
    (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (hf : ∀ i x y, |Real.log (fixed i x y)| ≤ 1)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    {t u : ℝ} (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) (i : I) (x : FinitePath Ω L) (y : FinitePath (A i) L) :
    |Real.log (selectedFactor sel fixed D E t u i x y)| ≤ 1 := by
  unfold selectedFactor
  split
  · have ht' := mul_le_mul_of_nonneg_left (hD i x y) (abs_nonneg t)
    have hu' := mul_le_mul_of_nonneg_left (hE i x y) (abs_nonneg u)
    rw [← abs_mul,mul_one] at ht' hu'
    have hlo : (1:ℝ)/2 ≤ 1+t*D i x y+u*E i x y := by
      linarith [(abs_le.mp (ht'.trans ht)).1,(abs_le.mp (hu'.trans hu)).1]
    have hhi : 1+t*D i x y+u*E i x y ≤ (3:ℝ)/2 := by
      linarith [(abs_le.mp (ht'.trans ht)).2,(abs_le.mp (hu'.trans hu)).2]
    have hpos : 0 < 1+t*D i x y+u*E i x y := by linarith
    have hlog := Real.log_le_sub_one_of_pos hpos
    have hinv : (1+t*D i x y+u*E i x y)⁻¹ ≤ 2 := by
      apply (inv_le_iff_one_le_mul₀ hpos).mpr
      linarith
    have hlogInv := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
    rw [Real.log_inv] at hlogInv
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  · exact hf i x y

/-- Joint parameter regularity of the fully tilted selected score at fixed
labels. The countable random labels are reintroduced below. -/
theorem measurable_selected_correctedScore {X : Type} [MeasurableSpace X]
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (base : X → FinitePath Ω L → ℝ) (roots : Fin n → I)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (hb : ∀ y, Measurable (fun x => base x y)) (t : ℝ) :
    Measurable (fun z : X × ℝ => selectedScore T Q m (base z.1) roots sel fixed D E t z.2+4*n*z.2) := by
  have hh := KernelTower.measurable_correctedPerturbScore (tower roots L T Q) m
    (base := fun z : X × ℝ => otherLog (base z.1) roots sel fixed)
    (D := fun _ : X × ℝ => selectedCoefficient roots sel D)
    (E := fun _ : X × ℝ => selectedCoefficient roots sel E)
    (t := fun _ : X × ℝ => t) (u := fun z => z.2)
    (fun y => ((hb (physical roots L y)).comp measurable_fst).add measurable_const)
    (fun _ _ => measurable_const) (fun _ _ => measurable_const) measurable_const measurable_snd
  simpa only [corrected_score_eq] using hh

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FullSelectedRegularity
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

variable (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t : ℝ)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y] in
theorem fullSelectedLog_eq (z : FullRootState Y X I M) (u : ℝ) :
    fullSelectedLog T Q m base sel fixed D E t z u =
      KernelTower.correctedPerturbLog (tower (rootArray z.2.2.1 z.2.2.2) L T Q) m
        (otherLog (base z.1 z.2.1.1 z.2.1.2) (rootArray z.2.2.1 z.2.2.2) sel fixed)
        (selectedCoefficient (rootArray z.2.2.1 z.2.2.2) sel D)
        (selectedCoefficient (rootArray z.2.2.1 z.2.2.2) sel E) t u := by
  rw [corrected_log_eq]
  unfold fullSelectedLog packRoot
  ring

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y] in
theorem fullSelectedScore_eq (z : FullRootState Y X I M) (u : ℝ) :
    fullSelectedScore T Q m base sel fixed D E t z u =
      KernelTower.correctedPerturbScore (tower (rootArray z.2.2.1 z.2.2.2) L T Q) m
        (otherLog (base z.1 z.2.1.1 z.2.1.2) (rootArray z.2.2.1 z.2.2.2) sel fixed)
        (selectedCoefficient (rootArray z.2.2.1 z.2.2.2) sel D)
        (selectedCoefficient (rootArray z.2.2.1 z.2.2.2) sel E) t u := by
  rw [corrected_score_eq]
  rfl

theorem measurable_fullSelectedLog
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y)) (u : ℝ) :
    Measurable (fun z => fullSelectedLog T Q m base sel fixed D E t z u) := by
  apply measurable_packRoot
  intro k n
  exact (measurable_root_base T Q m (fun z : RootPath Y M × RootPath X k => base z.1 k z.2)
    (hb k) (selectedFactor sel fixed D E t u) n).add measurable_const

theorem measurable_fullSelectedScore
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y)) :
    Measurable (fun z : FullRootState Y X I M × ℝ => fullSelectedScore T Q m base sel fixed D E t z.1 z.2) := by
  apply measurable_packRoot_param (F := fun h k x n y u =>
    selectedScore T Q m (base h k x) (rootArray n y) sel fixed D E t u+4*n*u)
  intro k n
  have hh : Measurable (fun z : ((RootPath Y M × RootPath X k) × ℝ) × RootPath I n =>
      selectedScore T Q m (base z.1.1.1 k z.1.1.2) (rootArray n z.2) sel fixed D E t z.1.2+4*n*z.1.2) := by
    apply measurable_from_prod_countable_left
    intro roots
    exact measurable_selected_correctedScore T Q m
      (fun z : RootPath Y M × RootPath X k => base z.1 k z.2) (rootArray n roots) sel fixed D E (hb k) t
  exact hh.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FullSelectedConcentration
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

/-- Concentration of the actual selected corrected score under the full common
reservoir law. The variance estimate is produced from replacement controls,
not a premise. All unselected types keep their original factors and priors. -/
theorem full_selected_corrected_concentration
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)] (r s : ℝ≥0)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (hbmeas : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    {B C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ h k x y, |base h k x y| ≤ B+C*k)
    (hf : ∀ i x y, |Real.log (fixed i x y)| ≤ 1)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (hrep : ∀ h k (j : Fin k) x z y,
      |base h k x y-base h k (replaceRoot k x j z) y| ≤ 2*C)
    (hadd : ∀ h k z x y, |base h (k+1) (z,x) y-base h k x y| ≤ C)
    (fieldBound : Fin M → ℝ)
    (hfield : ∀ j h z k x y, |base h k x y-base (replaceRoot M h j z) k x y| ≤ fieldBound j)
    {t a b ρ : ℝ} (ht : |t| ≤ 1/4) (hab : a < b) (hρ : 0 < ρ)
    (hJ : Icc (a-ρ) (b+ρ) ⊆ Ioo (-(1:ℝ)/4) (1/4)) :
    let G := fullSelectedScore T Q m base sel fixed D E t
    (∫ u in a..b, (∫ z, |G z u-∫ w, G w u ∂fullRootLaw ξ μ ν r s| ∂fullRootLaw ξ μ ν r s))/(b-a) ≤
      4*Real.sqrt (3*C^2*(r:ℝ)+4*(s:ℝ)+∑ j, (fieldBound j)^2/2)/ρ+12*ρ*(s:ℝ)/(b-a) := by
  let F := fullSelectedLog T Q m base sel fixed D E t
  let G := fullSelectedScore T Q m base sel fixed D E t
  have hFeq (z : FullRootState Y X I M) : F z =
      KernelTower.correctedPerturbLog (tower (rootArray z.2.2.1 z.2.2.2) L T Q) m
        (otherLog (base z.1 z.2.1.1 z.2.1.2) (rootArray z.2.2.1 z.2.2.2) sel fixed)
        (selectedCoefficient (rootArray z.2.2.1 z.2.2.2) sel D)
        (selectedCoefficient (rootArray z.2.2.1 z.2.2.2) sel E) t :=
    funext (fun u => fullSelectedLog_eq T Q m base sel fixed D E t z u)
  have hu (u : ℝ) (h : u ∈ Ioo (-(1:ℝ)/4) (1/4)) : |u| ≤ 1/4 :=
    abs_le.mpr ⟨by linarith [h.1],h.2.le⟩
  have hbsel (u : ℝ) (h : u ∈ Ioo (-(1:ℝ)/4) (1/4)) :=
    selectedFactor_log_bound sel fixed D E hf hD hE ht (hu u h)
  have hFm (u : ℝ) : Measurable (fun z => F z u) :=
    measurable_fullSelectedLog T Q m base sel fixed D E t hbmeas u
  have hGm : Measurable (fun z : FullRootState Y X I M × ℝ => G z.1 z.2) :=
    measurable_fullSelectedScore T Q m base sel fixed D E t hbmeas
  have hfc (z : FullRootState Y X I M) : ConvexOn ℝ (Ioo (-(1:ℝ)/4) (1/4)) (F z) := by
    have hh := (KernelTower.correctedPerturbLog_convex
      (tower (rootArray z.2.2.1 z.2.2.2) L T Q) m hm
      (otherLog (base z.1 z.2.1.1 z.2.1.2) (rootArray z.2.2.1 z.2.2.2) sel fixed)
      (selectedCoefficient (rootArray z.2.2.1 z.2.2.2) sel D)
      (selectedCoefficient (rootArray z.2.2.1 z.2.2.2) sel E)
      (selectedCoefficient_bound _ sel D hD) (selectedCoefficient_bound _ sel E hE) ht).subset
      Ioo_subset_Icc_self (convex_Ioo _ _)
    rw [hFeq]
    exact hh
  have hLp (u : ℝ) (h : u ∈ Ioo (-(1:ℝ)/4) (1/4)) :
      MemLp (fun z => F z u) 2 (fullRootLaw ξ μ ν r s) := by
    refine fullRoot_memLp_linear ξ μ ν r s
      (F := fun h k x n y => root T Q m (base h k x) (rootArray n y)
        (selectedFactor sel fixed D E t u)+(2*u^2)*n)
      (B := B) (C := C) (D := 1+|2*u^2|) ?_ ?_
    · intro k n
      exact (measurable_root_base T Q m (fun z : RootPath Y M × RootPath X k => base z.1 k z.2)
        (hbmeas k) (selectedFactor sel fixed D E t u) n).add measurable_const
    · intro h' k x n y
      have hh := root_uniform_bound T Q m hm (base h' k x) (rootArray n y)
        (selectedFactor sel fixed D E t u) (hb h' k x) (hbsel u h)
      calc
        _ ≤ |root T Q m (base h' k x) (rootArray n y) (selectedFactor sel fixed D E t u)|+|(2*u^2)*(n:ℝ)| := abs_add_le _ _
        _ ≤ B+C*k+1*n+|2*u^2| *n := by
          rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n)]
          exact add_le_add hh le_rfl
        _ = _ := by ring
  have hbound (z : FullRootState Y X I M) (u : ℝ) (h : u ∈ Ioo (-(1:ℝ)/4) (1/4)) :
      |G z u| ≤ 3*(z.2.2.1:ℝ) := by
    rw [show G z u = _ from fullSelectedScore_eq T Q m base sel fixed D E t z u]
    exact KernelTower.correctedPerturbScore_bound _ _ _ _ _
      (selectedCoefficient_bound _ sel D hD) (selectedCoefficient_bound _ sel E hE) ht (hu u h)
  have hd (z : FullRootState Y X I M) (u : ℝ) (h : u ∈ Ioo (-(1:ℝ)/4) (1/4)) :
      HasDerivAt (F z) (G z u) u := by
    have hp (q : Fin z.2.2.1) (y : FinitePath (Ω × Row (A := A) (rootArray z.2.2.1 z.2.2.2)) L) :
        0 < 1+t*selectedCoefficient (rootArray z.2.2.1 z.2.2.2) sel D q y+
          u*selectedCoefficient (rootArray z.2.2.1 z.2.2.2) sel E q y := by
      have hh := KernelTower.perturb_factor_lower _ _
        (selectedCoefficient_bound _ sel D hD) (selectedCoefficient_bound _ sel E hE) ht (hu u h) q y
      linarith
    rw [hFeq,show G z u = _ from fullSelectedScore_eq T Q m base sel fixed D E t z u]
    exact KernelTower.hasDerivAt_correctedPerturbLog (tower (rootArray z.2.2.1 z.2.2.2) L T Q) m (fun j => ne_of_gt (hm j))
        (otherLog (base z.1 z.2.1.1 z.2.1.2) (rootArray z.2.2.1 z.2.2.2) sel fixed) _ _ t u hp
  have hv (u : ℝ) (h : u ∈ Icc (a-ρ) (b+ρ)) :
      variance (fun z => F z u) (fullRootLaw ξ μ ν r s) ≤
        3*C^2*(r:ℝ)+4*(s:ℝ)+∑ j, (fieldBound j)^2/2 := by
    have hh := variance_actual_root μ ν ξ r s T Q m hm base hbmeas
      (selectedFactor sel fixed D E t u) hC (by norm_num : (0:ℝ) ≤ 1) hb (hbsel u (hJ h))
      hrep hadd fieldBound hfield (2*u^2)
    have hsq := mul_self_le_mul_self (abs_nonneg u) (hu u (hJ h))
    simp only [← pow_two,sq_abs] at hsq
    have hc : |2*u^2| ≤ 1/8 := by
      rw [abs_of_nonneg (by positivity)]
      nlinarith
    have hcc := mul_self_le_mul_self (by positivity : (0:ℝ) ≤ 1+|2*u^2|)
      (show 1+|2*u^2| ≤ 9/8 by linarith)
    have hcoef : 3*(1+|2*u^2|)^2 ≤ 4 := by nlinarith
    exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_right hcoef s.coe_nonneg])
  have hh := root_derivative_integral_bound (fullRootLaw ξ μ ν r s)
    isOpen_Ioo (convex_Ioo _ _) hFm hGm hfc hLp
    (((fullRoot_count_memLp ξ μ ν r s).integrable (by norm_num)).const_mul 3) hbound hd hab hρ hJ hv
  rw [integral_const_mul,fullRoot_count_mean] at hh
  convert hh using 1 <;> first | rfl | ring

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FullSelectedRawConcentration
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y] in
theorem fullSelectedRawScore_eq
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t : ℝ) (z : FullRootState Y X I M) (u : ℝ) :
    fullSelectedRawScore T Q m base sel fixed D E t z u =
    fullSelectedScore T Q m base sel fixed D E t z u-(4*u)*(z.2.2.1:ℝ) := by
  unfold fullSelectedRawScore fullSelectedScore packRoot
  ring

/-- The actual selected score, with the auxiliary convex correction removed. -/
theorem full_selected_root_concentration
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)] (r s : ℝ≥0)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (hbmeas : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    {B C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ h k x y, |base h k x y| ≤ B+C*k)
    (hf : ∀ i x y, |Real.log (fixed i x y)| ≤ 1)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (hrep : ∀ h k (j : Fin k) x z y,
      |base h k x y-base h k (replaceRoot k x j z) y| ≤ 2*C)
    (hadd : ∀ h k z x y, |base h (k+1) (z,x) y-base h k x y| ≤ C)
    (fieldBound : Fin M → ℝ)
    (hfield : ∀ j h z k x y, |base h k x y-base (replaceRoot M h j z) k x y| ≤ fieldBound j)
    {t a b ρ : ℝ} (ht : |t| ≤ 1/4) (hab : a < b) (hρ : 0 < ρ)
    (hJ : Icc (a-ρ) (b+ρ) ⊆ Ioo (-(1:ℝ)/4) (1/4)) :
    let G := fullSelectedRawScore T Q m base sel fixed D E t
    (∫ u in a..b, (∫ z, |G z u-∫ w, G w u ∂fullRootLaw ξ μ ν r s| ∂fullRootLaw ξ μ ν r s))/(b-a) ≤
      4*Real.sqrt (3*C^2*(r:ℝ)+4*(s:ℝ)+∑ j, (fieldBound j)^2/2)/ρ+12*ρ*(s:ℝ)/(b-a)+Real.sqrt s := by
  let G := fullSelectedScore T Q m base sel fixed D E t
  let P := fullRootLaw ξ μ ν r s
  have hI : Icc a b ⊆ Ioo (-(1:ℝ)/4) (1/4) := by
    intro u hu
    exact hJ ⟨by linarith [hu.1],by linarith [hu.2]⟩
  have hu (u : ℝ) (h : u ∈ Icc a b) : |u| ≤ 1/4 :=
    abs_le.mpr ⟨by linarith [(hI h).1],(hI h).2.le⟩
  have hbG (z : FullRootState Y X I M) (u : ℝ) (h : u ∈ Icc a b) :
      |G z u| ≤ 3*(z.2.2.1:ℝ) := by
    rw [show G z u = _ from fullSelectedScore_eq T Q m base sel fixed D E t z u]
    exact KernelTower.correctedPerturbScore_bound _ _ _ _ _
      (selectedCoefficient_bound _ sel D hD) (selectedCoefficient_bound _ sel E hE) ht (hu u h)
  have hcor := fullRoot_deviation_sub_count_integral ξ μ ν r s
    (measurable_fullSelectedScore T Q m base sel fixed D E t hbmeas)
    (((fullRoot_count_memLp ξ μ ν r s).integrable (by norm_num)).const_mul 3)
    hab.le hbG (show Measurable (fun u : ℝ => 4*u) from measurable_const.mul measurable_id)
    (fun u h => by rw [abs_mul]; norm_num; linarith [hu u h])
  have hmain := full_selected_corrected_concentration μ ν ξ r s T Q m hm base hbmeas
    sel fixed D E hC hb hf hD hE hrep hadd fieldBound hfield ht hab hρ hJ
  dsimp only at hmain ⊢
  change (∫ u in a..b, rootDeviation P (fun z => fullSelectedRawScore T Q m base sel fixed D E t z u))/(b-a) ≤ _
  simp_rw [fullSelectedRawScore_eq]
  have hh := div_le_div_of_nonneg_right hcor (sub_pos.mpr hab).le
  rw [add_div,mul_div_cancel_left₀ _ (ne_of_gt (sub_pos.mpr hab))] at hh
  exact hh.trans (add_le_add hmain le_rfl)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FullSelectedThermal
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.KernelTower
variable {Ω : Type} [Fintype Ω]

theorem thermalDefect_bound {L n : ℕ} (T : KernelTower Ω L) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (D E : Fin n → FinitePath Ω L → ℝ)
    (hD : ∀ q y, |D q y| ≤ 1) (hE : ∀ q y, |E q y| ≤ 1)
    {t u : ℝ} (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) :
    thermalDefect T m base D E t u ≤ 4*n := by
  let P := law L (tilt L T m (perturbLog base D E t u))
  have hs := perturbScore_bound D E hD hE ht hu
  have he := P.abs_expect_le hs
  have hh := P.expect_mono (fun y =>
    (abs_sub (perturbScore D E t u y) (P.expect (perturbScore D E t u))).trans
      ((add_le_add (hs y) he).trans_eq (show 2*(n:ℝ)+2*n=4*n by ring)))
  simpa only [thermalDefect, P,FiniteLaw.expect_const] using hh

end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

variable (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t : ℝ)

theorem measurable_fullSelectedThermal
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y)) :
    Measurable (fun z : FullRootState Y X I M × ℝ => fullSelectedThermal T Q m base sel fixed D E t z.1 z.2) := by
  apply measurable_packRoot_param (F := fun h k x n y u =>
    KernelTower.thermalDefect (tower (rootArray n y) L T Q) m
      (otherLog (base h k x) (rootArray n y) sel fixed)
      (selectedCoefficient (rootArray n y) sel D)
      (selectedCoefficient (rootArray n y) sel E) t u)
  intro k n
  have hh : Measurable (fun z : ((RootPath Y M × RootPath X k) × ℝ) × RootPath I n =>
      KernelTower.thermalDefect (tower (rootArray n z.2) L T Q) m
        (otherLog (base z.1.1.1 k z.1.1.2) (rootArray n z.2) sel fixed)
        (selectedCoefficient (rootArray n z.2) sel D)
        (selectedCoefficient (rootArray n z.2) sel E) t z.1.2) := by
    apply measurable_from_prod_countable_left
    intro roots
    exact KernelTower.measurable_thermalDefect (tower (rootArray n roots) L T Q) m
      (base := fun z : (RootPath Y M × RootPath X k) × ℝ =>
        otherLog (base z.1.1 k z.1.2) (rootArray n roots) sel fixed)
      (D := fun _ : (RootPath Y M × RootPath X k) × ℝ => selectedCoefficient (rootArray n roots) sel D)
      (E := fun _ : (RootPath Y M × RootPath X k) × ℝ => selectedCoefficient (rootArray n roots) sel E)
      (t := fun _ : (RootPath Y M × RootPath X k) × ℝ => t) (u := fun z => z.2)
      (fun y => ((hb k (physical (rootArray n roots) L y)).comp measurable_fst).add measurable_const)
      (fun _ _ => measurable_const) (fun _ _ => measurable_const) measurable_const measurable_snd
  exact hh.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y] in
theorem fullSelectedThermal_nonneg (z : FullRootState Y X I M) (u : ℝ) :
    0 ≤ fullSelectedThermal T Q m base sel fixed D E t z u :=
  KernelTower.thermalDefect_nonneg _ _ _ _ _ _ _

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y] in
theorem fullSelectedThermal_bound
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (ht : |t| ≤ 1/4) {u : ℝ} (hu : |u| ≤ 1/4) (z : FullRootState Y X I M) :
    fullSelectedThermal T Q m base sel fixed D E t z u ≤ 4*(z.2.2.1:ℝ) :=
  KernelTower.thermalDefect_bound _ _ _ _ _
    (selectedCoefficient_bound _ sel D hD) (selectedCoefficient_bound _ sel E hE) ht hu

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y] in
theorem fullSelectedThermal_integral_sq
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (ht : |t| ≤ 1/4) {a b c : ℝ} (hab : a < b) (hc : 0 < c)
    (hm : ∀ j, c ≤ m j) (hI : Icc a b ⊆ Icc (-(1:ℝ)/4) (1/4)) (z : FullRootState Y X I M) :
    (∫ u in a..b, fullSelectedThermal T Q m base sel fixed D E t z u)^2 ≤
      (b-a)*(4+4*(b-a))/c*(z.2.2.1:ℝ) := by
  have hh := KernelTower.perturb_thermal_absolute
    (tower (rootArray z.2.2.1 z.2.2.2) L T Q) m
    (otherLog (base z.1 z.2.1.1 z.2.1.2) (rootArray z.2.2.1 z.2.2.2) sel fixed)
    (selectedCoefficient (rootArray z.2.2.1 z.2.2.2) sel D)
    (selectedCoefficient (rootArray z.2.2.1 z.2.2.2) sel E)
    (selectedCoefficient_bound _ sel D hD) (selectedCoefficient_bound _ sel E hE) ht hab hc hm hI
  unfold fullSelectedThermal
  convert hh using 1 <;> first | rfl | ring

end DilutedSpinGlass.HeterogeneousMarks

namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
variable {X I Y : Type} [MeasurableSpace X] [MeasurableSpace I] [MeasurableSpace Y] {M : ℕ}

/-- Jensen under the genuine entire disorder law, using its actual Poisson count. -/
theorem fullRoot_average_sq
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν] (r s : ℝ≥0)
    {F : FullRootState Y X I M → ℝ} (hF : Measurable F) {K : ℝ}
    (hb : ∀ z, (F z)^2 ≤ K*(z.2.2.1:ℝ)) :
    (∫ z, F z ∂fullRootLaw ξ μ ν r s)^2 ≤ K*s := by
  have hi := ((fullRoot_count_memLp ξ μ ν r s).integrable (by norm_num)).const_mul K
  have hsq : Integrable (fun z => (F z)^2) (fullRootLaw ξ μ ν r s) :=
    hi.mono' (hF.pow_const 2).aestronglyMeasurable (ae_of_all _ (fun z => by
      simpa only [Real.norm_eq_abs,abs_sq] using hb z))
  have hLp := (memLp_two_iff_integrable_sq hF.aestronglyMeasurable).mpr hsq
  have hv := variance_nonneg F (fullRootLaw ξ μ ν r s)
  rw [variance_eq_sub hLp] at hv
  have hh := integral_mono hsq hi hb
  rw [integral_const_mul,fullRoot_count_mean] at hh
  simp only [Pi.pow_apply] at hv
  linarith

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FullThermalAverage
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

 
theorem full_selected_thermal_average
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν] (r s : ℝ≥0)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    {t a b c : ℝ} (ht : |t| ≤ 1/4) (hab : a < b) (hc : 0 < c)
    (hm : ∀ j, c ≤ m j) (hI : Icc a b ⊆ Icc (-(1:ℝ)/4) (1/4)) :
    (∫ u in a..b, ∫ z, fullSelectedThermal T Q m base sel fixed D E t z u
      ∂fullRootLaw ξ μ ν r s)^2 ≤ (b-a)*(4+4*(b-a))/c*(s:ℝ) := by
  let F := fullSelectedThermal T Q m base sel fixed D E t
  let P := fullRootLaw ξ μ ν r s
  let J := volume.restrict (Ioc a b)
  have hFm : Measurable (fun z : FullRootState Y X I M × ℝ => F z.1 z.2) :=
    measurable_fullSelectedThermal T Q m base sel fixed D E t hb
  have hdom : Integrable (fun z : FullRootState Y X I M => 4*(z.2.2.1:ℝ)) P :=
    ((fullRoot_count_memLp ξ μ ν r s).integrable (by norm_num)).const_mul 4
  have hprod : Integrable (fun z : FullRootState Y X I M × ℝ => F z.1 z.2) (P.prod J) := by
    apply (hdom.comp_fst J).mono' hFm.aestronglyMeasurable
    filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := P) (ν := J)).ae (ae_restrict_mem measurableSet_Ioc)] with z hz
    rw [Real.norm_eq_abs,abs_of_nonneg (fullSelectedThermal_nonneg T Q m base sel fixed D E t z.1 z.2)]
    exact fullSelectedThermal_bound T Q m base sel fixed D E t hD hE ht
      (abs_le.mpr ⟨by linarith [(hI ⟨hz.1.le,hz.2⟩).1],(hI ⟨hz.1.le,hz.2⟩).2⟩) z.1
  have hswap : (∫ u in a..b, ∫ z, F z u ∂P) = ∫ z, (∫ u in a..b, F z u) ∂P := by
    apply intervalIntegral_integral_swap
    rw [uIoc_of_le hab.le]
    change Integrable (fun z : ℝ × FullRootState Y X I M => F z.2 z.1) (J.prod P)
    exact hprod.swap
  rw [show (∫ u in a..b, ∫ z, fullSelectedThermal T Q m base sel fixed D E t z u
    ∂fullRootLaw ξ μ ν r s) = _ from hswap]
  apply fullRoot_average_sq ξ μ ν r s
  · simp_rw [intervalIntegral.integral_of_le hab.le]
    exact hFm.stronglyMeasurable.integral_prod_right'.measurable
  · intro z
    exact fullSelectedThermal_integral_sq T Q m base sel fixed D E t hD hE ht hab hc hm hI z

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FullSelectedError
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

variable (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t : ℝ)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y] in
theorem fullSelectedDeviation_nonneg (z : FullRootState Y X I M) (u center : ℝ) :
    0 ≤ fullSelectedDeviation T Q m base sel fixed D E t z u center :=
  FiniteLaw.expect_nonneg _ (fun _ => abs_nonneg _)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y] in
theorem fullSelectedDeviation_split (z : FullRootState Y X I M) (u center : ℝ) :
    fullSelectedDeviation T Q m base sel fixed D E t z u center ≤
      fullSelectedThermal T Q m base sel fixed D E t z u+
        |fullSelectedRawScore T Q m base sel fixed D E t z u-center| := by
  let roots := rootArray z.2.2.1 z.2.2.2
  let f := KernelTower.perturbLog (otherLog (base z.1 z.2.1.1 z.2.1.2) roots sel fixed)
    (selectedCoefficient roots sel D) (selectedCoefficient roots sel E) t u
  let g := KernelTower.perturbScore (selectedCoefficient roots sel D) (selectedCoefficient roots sel E) t u
  let P := KernelTower.law L (KernelTower.tilt L (tower roots L T Q) m f)
  have hh := P.expect_mono (fun y => abs_sub_le (g y) (P.expect g) center)
  rw [FiniteLaw.expect_add,FiniteLaw.expect_const] at hh
  change P.expect (fun y => |g y-center|) ≤
    P.expect (fun y => |g y-P.expect g|)+|fullSelectedRawScore T Q m base sel fixed D E t z u-center|
  have hG : fullSelectedRawScore T Q m base sel fixed D E t z u = P.expect g := by
    dsimp [fullSelectedRawScore,packRoot,selectedScore,P,f,g,roots]
    rw [selected_perturbLog_eq]
  rw [hG]
  exact hh

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y] in
theorem fullSelectedDeviation_bound
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    {u : ℝ} (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) (z : FullRootState Y X I M) (center : ℝ) :
    fullSelectedDeviation T Q m base sel fixed D E t z u center ≤ 2*(z.2.2.1:ℝ)+|center| := by
  apply (FiniteLaw.expect_mono _ (fun y => (abs_sub _ _).trans
    (add_le_add (KernelTower.perturbScore_bound _ _
      (selectedCoefficient_bound _ sel D hD) (selectedCoefficient_bound _ sel E hE) ht hu y) le_rfl))).trans_eq
  exact FiniteLaw.expect_const _ _

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y] in
theorem fullSelectedRawScore_bound
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    {u : ℝ} (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) (z : FullRootState Y X I M) :
    |fullSelectedRawScore T Q m base sel fixed D E t z u| ≤ 2*(z.2.2.1:ℝ) := by
  apply FiniteLaw.abs_expect_le
  exact KernelTower.perturbScore_bound _ _ (selectedCoefficient_bound _ sel D hD)
    (selectedCoefficient_bound _ sel E hE) ht hu

theorem measurable_fullSelectedRawScore
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y)) :
    Measurable (fun z : FullRootState Y X I M × ℝ => fullSelectedRawScore T Q m base sel fixed D E t z.1 z.2) := by
  simp_rw [fullSelectedRawScore_eq]
  exact (measurable_fullSelectedScore T Q m base sel fixed D E t hb).sub
    ((measurable_const.mul measurable_snd).mul ((measurable_sigmaUncurry (f := fun n (_ : RootPath I n) => (n:ℝ)) (fun _ => measurable_const)).comp measurable_fst.snd.snd))

theorem measurable_fullSelectedDeviation
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    {center : ℝ → ℝ} (hc : Measurable center) :
    Measurable (fun z : FullRootState Y X I M × ℝ => fullSelectedDeviation T Q m base sel fixed D E t z.1 z.2 (center z.2)) := by
  apply measurable_packRoot_param (F := fun h k x n y u =>
    fullSelectedDeviation T Q m base sel fixed D E t (h,⟨k,x⟩,⟨n,y⟩) u (center u))
  intro k n
  have hh : Measurable (fun z : ((RootPath Y M × RootPath X k) × ℝ) × RootPath I n =>
      fullSelectedDeviation T Q m base sel fixed D E t (z.1.1.1,⟨k,z.1.1.2⟩,⟨n,z.2⟩) z.1.2 (center z.1.2)) := by
    apply measurable_from_prod_countable_left
    intro y
    dsimp only [fullSelectedDeviation]
    apply KernelTower.measurable_path_expect L (tower (rootArray n y) L T Q) m
      (f := fun z : (RootPath Y M × RootPath X k) × ℝ =>
        KernelTower.perturbLog (otherLog (base z.1.1 k z.1.2) (rootArray n y) sel fixed)
          (selectedCoefficient (rootArray n y) sel D) (selectedCoefficient (rootArray n y) sel E) t z.2)
      (g := fun z : (RootPath Y M × RootPath X k) × ℝ => fun w =>
        |KernelTower.perturbScore (selectedCoefficient (rootArray n y) sel D)
          (selectedCoefficient (rootArray n y) sel E) t z.2 w-center z.2|)
    · apply KernelTower.measurable_perturbLog
      · intro w
        exact ((hb k (physical (rootArray n y) L w)).comp measurable_fst).add measurable_const
      · exact fun _ _ => measurable_const
      · exact fun _ _ => measurable_const
      · exact measurable_const
      · exact measurable_snd
    · intro w
      exact ((KernelTower.measurable_perturbScore
        (D := fun _ : (RootPath Y M × RootPath X k) × ℝ => selectedCoefficient (rootArray n y) sel D)
        (E := fun _ : (RootPath Y M × RootPath X k) × ℝ => selectedCoefficient (rootArray n y) sel E)
        (t := fun _ : (RootPath Y M × RootPath X k) × ℝ => t) (u := fun z => z.2)
        (fun _ _ => measurable_const) (fun _ _ => measurable_const) measurable_const measurable_snd w).sub
          (hc.comp measurable_snd)).abs
  exact hh.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_GlobalSelectedError
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν] (r s : ℝ≥0)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t : ℝ)

omit [Countable I] [MeasurableSingletonClass I] [∀ index, IsProbabilityMeasure (ξ index)]
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
theorem fullSelectedError_nonneg (u : ℝ) :
    0 ≤ fullSelectedError ξ μ ν r s T Q m base sel fixed D E t u :=
  integral_nonneg (fun z => fullSelectedDeviation_nonneg T Q m base sel fixed D E t z u _)

theorem measurable_fullSelectedError
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y)) :
    Measurable (fullSelectedError ξ μ ν r s T Q m base sel fixed D E t) :=
  (measurable_fullSelectedDeviation T Q m base sel fixed D E t hb
    (measurable_fullSelectedRawScore T Q m base sel fixed D E t hb).stronglyMeasurable.integral_prod_left'.measurable).stronglyMeasurable.integral_prod_left'.measurable

/-- Conditional/root decomposition proved for the actual tilted score. -/
theorem fullSelectedError_split
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    {u : ℝ} (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) :
    fullSelectedError ξ μ ν r s T Q m base sel fixed D E t u ≤
      (∫ z, fullSelectedThermal T Q m base sel fixed D E t z u ∂fullRootLaw ξ μ ν r s)+
        rootDeviation (fullRootLaw ξ μ ν r s) (fun z => fullSelectedRawScore T Q m base sel fixed D E t z u) := by
  let P := fullRootLaw ξ μ ν r s
  let center := ∫ w, fullSelectedRawScore T Q m base sel fixed D E t w u ∂P
  have hci : Integrable (fun z : FullRootState Y X I M => (z.2.2.1:ℝ)) P :=
    (fullRoot_count_memLp ξ μ ν r s).integrable (by norm_num)
  have hiD : Integrable (fun z => fullSelectedDeviation T Q m base sel fixed D E t z u center) P := by
    apply ((hci.const_mul 2).add (integrable_const |center|)).mono'
      ((measurable_fullSelectedDeviation T Q m base sel fixed D E t hb measurable_const).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    exact ae_of_all _ (fun z => by
      dsimp only [Function.comp_apply,id_eq,Pi.add_apply,Pi.sub_apply]
      rw [Real.norm_eq_abs,abs_of_nonneg (fullSelectedDeviation_nonneg T Q m base sel fixed D E t z u center)]
      exact fullSelectedDeviation_bound T Q m base sel fixed D E t hD hE ht hu z center)
  have hiT : Integrable (fun z => fullSelectedThermal T Q m base sel fixed D E t z u) P := by
    apply (hci.const_mul 4).mono'
      ((measurable_fullSelectedThermal T Q m base sel fixed D E t hb).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    exact ae_of_all _ (fun z => by
      dsimp only [Function.comp_apply,id_eq,Pi.add_apply,Pi.sub_apply]
      rw [Real.norm_eq_abs,abs_of_nonneg (fullSelectedThermal_nonneg T Q m base sel fixed D E t z u)]
      exact fullSelectedThermal_bound T Q m base sel fixed D E t hD hE ht hu z)
  have hiS : Integrable (fun z => fullSelectedRawScore T Q m base sel fixed D E t z u) P := by
    apply (hci.const_mul 2).mono'
      ((measurable_fullSelectedRawScore T Q m base sel fixed D E t hb).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    exact ae_of_all _ (fun z => by
      dsimp only [Function.comp_apply,id_eq,Pi.add_apply,Pi.sub_apply]
      rw [Real.norm_eq_abs]
      exact fullSelectedRawScore_bound T Q m base sel fixed D E t hD hE ht hu z)
  have hh := integral_mono hiD (hiT.add ((hiS.sub (integrable_const center)).abs))
    (fun z => fullSelectedDeviation_split T Q m base sel fixed D E t z u center)
  simp only [Pi.add_apply,Pi.sub_apply] at hh
  rw [integral_add (f := fun z => fullSelectedThermal T Q m base sel fixed D E t z u)
    (g := fun z => |fullSelectedRawScore T Q m base sel fixed D E t z u-center|) hiT ((hiS.sub (integrable_const center)).abs)] at hh
  exact hh

theorem fullSelectedError_bound
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    {u : ℝ} (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) :
    fullSelectedError ξ μ ν r s T Q m base sel fixed D E t u ≤ 4*(s:ℝ) := by
  let P := fullRootLaw ξ μ ν r s
  let center := ∫ w, fullSelectedRawScore T Q m base sel fixed D E t w u ∂P
  have hci : Integrable (fun z : FullRootState Y X I M => (z.2.2.1:ℝ)) P :=
    (fullRoot_count_memLp ξ μ ν r s).integrable (by norm_num)
  have hiS : Integrable (fun z => fullSelectedRawScore T Q m base sel fixed D E t z u) P := by
    apply (hci.const_mul 2).mono'
      ((measurable_fullSelectedRawScore T Q m base sel fixed D E t hb).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    exact ae_of_all _ (fun z => by
      simpa only [Real.norm_eq_abs,Function.comp_apply,id_eq] using fullSelectedRawScore_bound T Q m base sel fixed D E t hD hE ht hu z)
  have hav : |center| ≤ 2*(s:ℝ) := by
    have hh := abs_integral_le_integral_abs.trans (integral_mono hiS.abs (hci.const_mul 2)
      (fun z => fullSelectedRawScore_bound T Q m base sel fixed D E t hD hE ht hu z))
    simpa only [P,integral_const_mul,fullRoot_count_mean] using hh
  have hiD : Integrable (fun z => fullSelectedDeviation T Q m base sel fixed D E t z u center) P := by
    apply ((hci.const_mul 2).add (integrable_const |center|)).mono'
      ((measurable_fullSelectedDeviation T Q m base sel fixed D E t hb measurable_const).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    exact ae_of_all _ (fun z => by
      dsimp only [Function.comp_apply,id_eq,Pi.add_apply,Pi.sub_apply]
      rw [Real.norm_eq_abs,abs_of_nonneg (fullSelectedDeviation_nonneg T Q m base sel fixed D E t z u center)]
      exact fullSelectedDeviation_bound T Q m base sel fixed D E t hD hE ht hu z center)
  have hh := integral_mono hiD ((hci.const_mul 2).add (integrable_const |center|))
    (fun z => fullSelectedDeviation_bound T Q m base sel fixed D E t hD hE ht hu z center)
  simp only [Pi.add_apply] at hh
  rw [integral_add (hci.const_mul 2) (integrable_const |center|), integral_const_mul] at hh
  simp only [P,fullRoot_count_mean,integral_const,probReal_univ,smul_eq_mul,one_mul] at hh
  change fullSelectedError ξ μ ν r s T Q m base sel fixed D E t u ≤ _
  change fullSelectedError ξ μ ν r s T Q m base sel fixed D E t u ≤ _ at hh
  linarith

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_GlobalSelectedAverage
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

/-- The actual complete score error, split into its thermal and disorder parts.
The only bounds used are the perturbation factors and positive exponents. -/
theorem full_selected_error_split_average
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν] (r s : ℝ≥0)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    {t a b c : ℝ} (ht : |t| ≤ 1/4) (hab : a < b) (hc : 0 < c)
    (hm : ∀ j, c ≤ m j) (hI : Icc a b ⊆ Icc (-(1:ℝ)/4) (1/4)) :
    (∫ u in a..b, fullSelectedError ξ μ ν r s T Q m base sel fixed D E t u) ≤
      Real.sqrt ((b-a)*(4+4*(b-a))/c*(s:ℝ))+
        ∫ u in a..b, rootDeviation (fullRootLaw ξ μ ν r s)
          (fun z => fullSelectedRawScore T Q m base sel fixed D E t z u) := by
  let P := fullRootLaw ξ μ ν r s
  let F := fullSelectedError ξ μ ν r s T Q m base sel fixed D E t
  let U := fun u => ∫ z, fullSelectedThermal T Q m base sel fixed D E t z u ∂P
  let V := fun u => rootDeviation P (fun z => fullSelectedRawScore T Q m base sel fixed D E t z u)
  have hu (u : ℝ) (h : u ∈ Icc a b) : |u| ≤ 1/4 :=
    abs_le.mpr ⟨by linarith [(hI h).1],(hI h).2⟩
  have hci := (fullRoot_count_memLp ξ μ ν r s).integrable (by norm_num)
  have hUn (u : ℝ) : 0 ≤ U u :=
    integral_nonneg (fun z => fullSelectedThermal_nonneg T Q m base sel fixed D E t z u)
  have hUb (u : ℝ) (h : u ∈ Icc a b) : U u ≤ 4*(s:ℝ) := by
    have hh := integral_mono_of_nonneg
      (ae_of_all P (fun z => fullSelectedThermal_nonneg T Q m base sel fixed D E t z u))
      (hci.const_mul 4)
      (ae_of_all P (fun z => fullSelectedThermal_bound T Q m base sel fixed D E t hD hE ht (hu u h) z))
    simpa only [P, U, integral_const_mul,fullRoot_count_mean] using hh
  have hUi : IntervalIntegrable U volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le]
    apply Measure.integrableOn_of_bounded (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      (measurable_fullSelectedThermal T Q m base sel fixed D E t hb).stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
    apply ae_restrict_of_forall_mem measurableSet_Ioc
    intro u h
    rw [Real.norm_eq_abs,abs_of_nonneg (hUn u)]
    exact hUb u ⟨h.1.le,h.2⟩
  have hFi : IntervalIntegrable F volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le]
    apply Measure.integrableOn_of_bounded (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      (measurable_fullSelectedError ξ μ ν r s T Q m base sel fixed D E t hb).aestronglyMeasurable
    apply ae_restrict_of_forall_mem measurableSet_Ioc
    intro u h
    rw [Real.norm_eq_abs,abs_of_nonneg (fullSelectedError_nonneg ξ μ ν r s T Q m base sel fixed D E t u)]
    exact fullSelectedError_bound ξ μ ν r s T Q m base sel fixed D E t hb hD hE ht (hu u ⟨h.1.le,h.2⟩)
  have hVi : IntervalIntegrable V volume a b :=
    intervalIntegrable_rootDeviation P (measurable_fullSelectedRawScore T Q m base sel fixed D E t hb)
      (hci.const_mul 2) hab.le
      (fun z u h => fullSelectedRawScore_bound T Q m base sel fixed D E t hD hE ht (hu u h) z)
  have hh := intervalIntegral.integral_mono_on hab.le hFi (hUi.add hVi)
    (fun u h => fullSelectedError_split ξ μ ν r s T Q m base sel fixed D E t hb hD hE ht (hu u h))
  rw [intervalIntegral.integral_add hUi hVi] at hh
  have hsq := full_selected_thermal_average ξ μ ν r s T Q m base hb sel fixed D E hD hE ht hab hc hm hI
  have hle : (∫ u in a..b, U u) ≤ Real.sqrt ((b-a)*(4+4*(b-a))/c*(s:ℝ)) := by
    have hK : 0 ≤ (b-a)*(4+4*(b-a))/c*(s:ℝ) := by positivity
    have hsq' : (∫ u in a..b, U u)^2 ≤ (Real.sqrt ((b-a)*(4+4*(b-a))/c*(s:ℝ)))^2 := by
      rw [Real.sq_sqrt hK]
      exact hsq
    nlinarith [Real.sqrt_nonneg ((b-a)*(4+4*(b-a))/c*(s:ℝ))]
  exact hh.trans (add_le_add hle le_rfl)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_GlobalSelectedConcentration
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

/-- An unconditional quantitative bound for the global-centered selected score
on the actual two-Poisson-plus-field law. Selection changes no prior and does
not discard any of the other perturbations. -/
theorem full_selected_error_concentration
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)] (r s : ℝ≥0)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) {c : ℝ} (hc : 0 < c) (hm : ∀ j, c ≤ m j)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (hbmeas : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    {B C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ h k x y, |base h k x y| ≤ B+C*k)
    (hf : ∀ i x y, |Real.log (fixed i x y)| ≤ 1)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (hrep : ∀ h k (j : Fin k) x z y,
      |base h k x y-base h k (replaceRoot k x j z) y| ≤ 2*C)
    (hadd : ∀ h k z x y, |base h (k+1) (z,x) y-base h k x y| ≤ C)
    (fieldBound : Fin M → ℝ)
    (hfield : ∀ j h z k x y, |base h k x y-base (replaceRoot M h j z) k x y| ≤ fieldBound j)
    {t a b ρ : ℝ} (ht : |t| ≤ 1/4) (hab : a < b) (hρ : 0 < ρ)
    (hJ : Icc (a-ρ) (b+ρ) ⊆ Ioo (-(1:ℝ)/4) (1/4)) :
    (∫ u in a..b, fullSelectedError ξ μ ν r s T Q m base sel fixed D E t u)/(b-a) ≤
      Real.sqrt ((b-a)*(4+4*(b-a))/c*(s:ℝ))/(b-a)+
      4*Real.sqrt (3*C^2*(r:ℝ)+4*(s:ℝ)+∑ j, (fieldBound j)^2/2)/ρ+
      12*ρ*(s:ℝ)/(b-a)+Real.sqrt s := by
  have hI : Icc a b ⊆ Icc (-(1:ℝ)/4) (1/4) := by
    intro u hu
    have hh := hJ (show u ∈ Icc (a-ρ) (b+ρ) from ⟨by linarith [hu.1],by linarith [hu.2]⟩)
    exact ⟨hh.1.le,hh.2.le⟩
  have h1 := full_selected_error_split_average ξ μ ν r s T Q m base hbmeas sel fixed D E
    hD hE ht hab hc hm hI
  have h2 := full_selected_root_concentration μ ν ξ r s T Q m (fun j => hc.trans_le (hm j))
    base hbmeas sel fixed D E hC hb hf hD hE hrep hadd fieldBound hfield ht hab hρ hJ
  have hh := div_le_div_of_nonneg_right h1 (sub_pos.mpr hab).le
  rw [add_div] at hh
  exact hh.trans (by dsimp only [rootDeviation]; dsimp only at h2; linarith)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalSelectedConcentration
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks Set
open scoped NNReal ENNReal BigOperators
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  {A : I → Type} [∀ i, Fintype (A i)] {N L : ℕ}

/-- The concentration envelope for the actual bounded physical spin energy,
with all heterogeneous dictionary marks retained. -/
theorem spin_selected_concentration_oai
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (r s : ℝ≥0)
    (V : X → (Fin N → Spin) → ℝ) (field : Y → ℝ)
    (hVm : ∀ σ, Measurable (fun x => V x σ)) (hhm : Measurable field)
    {C H c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hV : ∀ x σ, |V x σ| ≤ C) (hh : ∀ y, |field y| ≤ H)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ j, c ≤ m j)
    (sel : I → Bool)
    (fixed D E : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    (hf : ∀ i x y, |Real.log (fixed i x y)| ≤ 1)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    {t a b ρ : ℝ} (ht : |t| ≤ 1/4) (hab : a < b) (hρ : 0 < ρ)
    (hJ : Icc (a-ρ) (b+ρ) ⊆ Ioo (-(1:ℝ)/4) (1/4)) :
    let T := KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L
    let base := fun h k (x : RootPath X k) z => energy V field h k x (KernelTower.terminalState L z)
    (∫ u in a..b, fullSelectedError (fun _ : Fin N => ξ) μ ν r s T Q m base sel fixed D E t u)/(b-a) ≤
      Real.sqrt ((b-a)*(4+4*(b-a))/c*(s:ℝ))/(b-a)+
      4*Real.sqrt (3*C^2*(r:ℝ)+4*(s:ℝ)+2*H^2*N)/ρ+
      12*ρ*(s:ℝ)/(b-a)+Real.sqrt s := by
  dsimp only
  have h := full_selected_error_concentration μ ν (fun _ : Fin N => ξ) r s
    (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L) Q m hc hm
    (fun h k x z => energy V field h k x (KernelTower.terminalState L z))
    (fun k z => measurable_energy V field hVm hhm k (KernelTower.terminalState L z))
    sel fixed D E hC
    (fun h k x z => energy_bound V field hV hh h k x (KernelTower.terminalState L z)) hf hD hE
    (fun h k j x z w => energy_replace_interaction V field hV h k j x z (KernelTower.terminalState L w))
    (fun h k z x w => energy_add_interaction V field hV h k z x (KernelTower.terminalState L w))
    (fun _ => 2*H)
    (fun j h z k x w => energy_replace_field V field hh h j z k x (KernelTower.terminalState L w))
    ht hab hρ hJ
  have hfieldSum : (∑ _ : Fin N, (2*H)^2/2) = 2*H^2*N := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  simpa only [hfieldSum] using h

end DilutedSpinGlass.PhysicalRoot
end

end

end OAI
end

theorem solution : type_of% @OAI.DilutedSpinGlass.PhysicalRoot.spin_selected_concentration_oai := @OAI.DilutedSpinGlass.PhysicalRoot.spin_selected_concentration_oai
