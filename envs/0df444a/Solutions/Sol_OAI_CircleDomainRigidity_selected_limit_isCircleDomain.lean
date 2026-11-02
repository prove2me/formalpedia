-- Prove2me | solution 1 for OAI.CircleDomainRigidity.selected_limit_isCircleDomain
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T06:15:26.826023+00:00
-- url     : https://prove2.me/submissions/cf718024-6439-437c-bdf7-52e540f2f42b

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_Q146C010
import Theorems.Thm_OAI_CircleDomainRigidity_exists_ordered_protrusion_test

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_BandBudgetNorm
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real square norms of band widths are bounded by their ENNReal budgets,
including when the marked set is only a subset of the full budget support. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem real_square_norm_le_counting {A B : Type*}
    (v : A → ℝ) (w : B → ℝ≥0∞) (e : A → B) (he : Injective e)
    (hv : ∀ a, 0 ≤ v a) (hb : ∀ a, ENNReal.ofReal (v a) ≤ w (e a))
    (hw : (∑' b, w b ^ 2) < ∞) :
    Real.sqrt (∑' a, v a ^ 2) ≤ (countingSquareNorm w).toReal := by
  have hE : (∑' a, ENNReal.ofReal (v a ^ 2)) ≤ ∑' b, w b ^ 2 := by
    calc
      _ = ∑' a, ENNReal.ofReal (v a) ^ 2 := by
        congr 1
        funext a
        exact ENNReal.ofReal_pow (hv a) 2
      _ ≤ ∑' a, w (e a) ^ 2 := ENNReal.tsum_le_tsum
        (fun a => pow_le_pow_left' (hb a) 2)
      _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective he (fun b => w b ^ 2)
  have hr := ENNReal.toReal_mono hw.ne hE
  rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)] at hr
  simp only [ENNReal.toReal_ofReal (sq_nonneg _)] at hr
  rw [countingSquareNorm, ← ENNReal.toReal_rpow, ← Real.sqrt_eq_rpow]
  exact Real.sqrt_le_sqrt hr

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_CircleBoundaryOscillation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two offset-circle contributions in the Stokes estimate: zero
period costs radius times oscillation, and the distinguished constant
weight costs only that constant times the period. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem zero_period_weighted_integral_bound
    (φ dφ u du : ℝ → ℝ) {T K A : ℝ} (hT : 0 ≤ T)
    (hφ : ∀ x ∈ uIcc (0 : ℝ) T, HasDerivAt φ (dφ x) x)
    (hu : ∀ x ∈ uIcc (0 : ℝ) T, HasDerivAt u (du x) x)
    (hdφ : IntervalIntegrable dφ volume 0 T) (hdu : IntervalIntegrable du volume 0 T)
    (hperiod : u T = u 0)
    (hK : ∀ x ∈ Icc (0 : ℝ) T, |dφ x| ≤ K)
    (hA : ∀ x ∈ Icc (0 : ℝ) T, |u x - u 0| ≤ A) :
    |∫ x in (0 : ℝ)..T, φ x * du x| ≤ T * K * A := by
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hφ
    (fun x hx => (hu x hx).sub_const (u 0)) hdφ hdu
  have he : (∫ x in (0 : ℝ)..T, φ x * du x) =
      -(∫ x in (0 : ℝ)..T, dφ x * (u x - u 0)) := by
    simpa only [hperiod, sub_self, mul_zero, zero_sub] using hparts
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0 ⟨le_rfl, hT⟩)
  have hb : ‖∫ x in (0 : ℝ)..T, dφ x * (u x - u 0)‖ ≤
      ∫ _x in (0 : ℝ)..T, K * A := by
    apply intervalIntegral.norm_integral_le_of_norm_le hT _ (intervalIntegrable_const)
    apply Eventually.of_forall
    intro x hx
    have hx' : x ∈ Icc (0 : ℝ) T := ⟨hx.1.le, hx.2⟩
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hK x hx') (hA x hx') (abs_nonneg _) hK0
  rw [he, abs_neg]
  simpa only [Real.norm_eq_abs, intervalIntegral.integral_const, sub_zero, smul_eq_mul,
    mul_assoc] using hb

 theorem constant_weight_integral_eq_period
    (u du : ℝ → ℝ) (T ρ : ℝ)
    (hu : ∀ x ∈ uIcc (0 : ℝ) T, HasDerivAt u (du x) x)
    (hdu : IntervalIntegrable du volume 0 T) :
    (∫ x in (0 : ℝ)..T, ρ * du x) = ρ * (u T - u 0) := by
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hu hdu]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_FiniteGapPayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Variation payment across finitely many gaps

The domain intervals of a line crossing a finite circle domain contribute
their actual derivative variation. Each intervening hole contributes only
the difference of the two endpoint traces. This is the finite telescoping
step in the manuscript's parallel-line payment estimate.
-/

open Set MeasureTheory

namespace CircleDomainRigidity

theorem abs_sub_le_sum_segments_and_jumps (n : ℕ) (left right : Fin (n + 1) → ℝ) :
    |right (Fin.last n) - left 0| ≤
      (∑ i, |right i - left i|) +
        ∑ i : Fin n, |left i.succ - right i.castSucc| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprior := ih (fun i => left i.castSucc) (fun i => right i.castSucc)
    have htriangle : |right (Fin.last (n + 1)) - left 0| ≤
        |right (Fin.last (n + 1)) - left (Fin.last (n + 1))| +
        |left (Fin.last (n + 1)) - right (Fin.last n).castSucc| +
        |right (Fin.last n).castSucc - left 0| := by
      have heq : right (Fin.last (n + 1)) - left 0 =
          (right (Fin.last (n + 1)) - left (Fin.last (n + 1))) +
          (left (Fin.last (n + 1)) - right (Fin.last n).castSucc) +
          (right (Fin.last n).castSucc - left 0) := by ring
      rw [heq]
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    calc
      _ ≤ |right (Fin.last (n + 1)) - left (Fin.last (n + 1))| +
          |left (Fin.last (n + 1)) - right (Fin.last n).castSucc| +
          ((∑ i : Fin (n + 1), |right i.castSucc - left i.castSucc|) +
            ∑ i : Fin n, |left i.succ.castSucc - right i.castSucc.castSucc|) :=
        htriangle.trans (add_le_add le_rfl (by simpa only [Fin.castSucc_zero] using hprior))
      _ = _ := by
        rw [Fin.sum_univ_castSucc (fun i : Fin (n + 2) => |right i - left i|),
          Fin.sum_univ_castSucc (fun i : Fin (n + 1) => |left i.succ - right i.castSucc|)]
        simp only [Fin.castSucc_succ, Fin.succ_last]
        ring

theorem variation_le_integral_abs_deriv {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b) :
    |f b - f a| ≤ ∫ x in a..b, |deriv f x| := by
  rw [← hf.integral_deriv_eq_sub]
  simpa only [Real.norm_eq_abs] using
    (intervalIntegral.norm_integral_le_integral_norm (f := deriv f) hab)

theorem line_payment_across_finite_gaps
    (n : ℕ) (a b : Fin (n + 1) → ℝ) (f : Fin (n + 1) → ℝ → ℝ)
    (A : Fin n → ℝ) (hab : ∀ i, a i ≤ b i)
    (hf : ∀ i, AbsolutelyContinuousOnInterval (f i) (a i) (b i))
    (hzero : f 0 (a 0) = 0) (hone : f (Fin.last n) (b (Fin.last n)) = 1)
    (hjumps : ∀ i : Fin n,
      |f i.succ (a i.succ) - f i.castSucc (b i.castSucc)| ≤ A i) :
    1 ≤ (∑ i, ∫ x in a i..b i, |deriv (f i) x|) + ∑ i, A i := by
  have hchain := abs_sub_le_sum_segments_and_jumps n
    (fun i => f i (a i)) (fun i => f i (b i))
  rw [hone, hzero] at hchain
  norm_num only [sub_zero, abs_one] at hchain
  exact hchain.trans (add_le_add
    (Finset.sum_le_sum (fun i _ => variation_le_integral_abs_deriv (hab i) (hf i)))
    (Finset.sum_le_sum (fun i _ => hjumps i)))

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_OpenGapPayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Payment from smooth functions on open gaps

Finite energy supplies the endpoint traces, even when the function has
no prescribed values on the removed intervals. Bounds on the endpoint
traces are used only for the jumps across those intervals.
-/

open Set Function Filter MeasureTheory
open scoped Topology

namespace CircleDomainRigidity

theorem line_payment_from_open_gaps
    (n : ℕ) (a b : Fin (n + 1) → ℝ) (f : ℝ → ℝ) (d ρ : ℝ → ℝ)
    (A : Fin n → ℝ) (hab : ∀ i, a i < b i)
    (hd : ∀ i x, x ∈ Ioo (a i) (b i) → HasDerivAt f (d x) x)
    (hi : ∀ i, IntervalIntegrable d volume (a i) (b i))
    (hρ : Integrable ρ) (hpos : ∀ x, 0 ≤ ρ x)
    (hdom : ∀ i x, x ∈ Ioo (a i) (b i) → |d x| ≤ ρ x)
    (hdisj : Pairwise (Disjoint on fun i => Ioo (a i) (b i)))
    (hzero : Tendsto f (𝓝[Ioo (a 0) (b 0)] (a 0)) (𝓝 0))
    (hone : Tendsto f (𝓝[Ioo (a (Fin.last n)) (b (Fin.last n))]
      (b (Fin.last n))) (𝓝 1))
    (hjump : ∀ (i : Fin n) u v,
      Tendsto f (𝓝[Ioo (a i.castSucc) (b i.castSucc)] (b i.castSucc)) (𝓝 u) →
      Tendsto f (𝓝[Ioo (a i.succ) (b i.succ)] (a i.succ)) (𝓝 v) → |v - u| ≤ A i) :
    1 ≤ (∫ x, ρ x) + ∑ i, A i := by
  choose g hg heq hleft hright using fun i =>
    exists_absolutelyContinuous_extension_of_integrable_derivative (hab i) (hd i) (hi i)
  have hgderiv (i : Fin (n + 1)) (x : ℝ) (hx : x ∈ Ioo (a i) (b i)) :
      deriv (g i) x = d x := by
    have hevent : g i =ᶠ[𝓝 x] f := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with z hz
      exact heq i hz
    exact ((hd i x hx).congr_of_eventuallyEq hevent).deriv
  have hfirst : g 0 (a 0) = 0 := by
    have : NeBot (𝓝[Ioo (a 0) (b 0)] (a 0)) :=
      mem_closure_iff_nhdsWithin_neBot.mp (by simpa [closure_Ioo (hab 0).ne] using (hab 0).le)
    exact tendsto_nhds_unique (hleft 0) hzero
  have hlast : g (Fin.last n) (b (Fin.last n)) = 1 := by
    have : NeBot (𝓝[Ioo (a (Fin.last n)) (b (Fin.last n))] (b (Fin.last n))) :=
      mem_closure_iff_nhdsWithin_neBot.mp (by
        rw [closure_Ioo (hab (Fin.last n)).ne]
        exact right_mem_Icc.mpr (hab (Fin.last n)).le)
    exact tendsto_nhds_unique (hright (Fin.last n)) hone
  have hline := line_payment_across_finite_gaps n a b g A (fun i => (hab i).le)
    hg hfirst hlast (fun i => hjump i _ _ (hright i.castSucc) (hleft i.succ))
  have hbound (i : Fin (n + 1)) :
      (∫ x in a i..b i, |deriv (g i) x|) ≤ ∫ x in Ioo (a i) (b i), ρ x := by
    rw [intervalIntegral.integral_of_le (hab i).le, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_mono_on ?_ hρ.integrableOn measurableSet_Ioo ?_
    · exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (hab i).le).mp
        (hg i).intervalIntegrable_deriv.abs
    · intro x hx
      rw [hgderiv i x hx]
      exact hdom i x hx
  have hsum : (∑ i, ∫ x in a i..b i, |deriv (g i) x|) ≤ ∫ x, ρ x := by
    calc
      _ ≤ ∑ i, ∫ x in Ioo (a i) (b i), ρ x := Finset.sum_le_sum (fun i _ => hbound i)
      _ = ∫ x in ⋃ i, Ioo (a i) (b i), ρ x :=
        (integral_iUnion_fintype (fun _ => measurableSet_Ioo) hdisj
          (fun _ => hρ.integrableOn)).symm
      _ ≤ _ := setIntegral_le_integral hρ (Eventually.of_forall hpos)
  exact hline.trans (add_le_add hsum le_rfl)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FiniteLineGaps
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual gaps of finitely many disjoint line intervals

Sorting the closed holes supplies the open intervals on which variation
is paid. Every gap is nonempty, the gaps are disjoint, and no point of a
gap belongs to a hole. Point holes are allowed.
-/

open Set Function

namespace CircleDomainRigidity

theorem gapsAfterHoles_disjoint {n : ℕ} (a b : ℝ) (H : Fin n → ℝ × ℝ)
    (hvalid : ∀ i, (H i).1 ≤ (H i).2)
    (hfirst : Monotone (fun i => (H i).1)) :
    Pairwise (Disjoint on fun i => Ioo
      (gapsAfterHoles a b H i).1 (gapsAfterHoles a b H i).2) := by
  intro i j hij
  wlog hlt : i < j generalizing i j
  · exact (this hij.symm (lt_of_le_of_ne (le_of_not_gt hlt) hij.symm)).symm
  obtain ⟨k, rfl⟩ := Fin.eq_castSucc_of_ne_last
    (show i ≠ Fin.last n by
      intro he
      subst i
      exact (not_lt_of_ge (Fin.le_last j)) hlt)
  obtain ⟨l, rfl⟩ := Fin.eq_succ_of_ne_zero
    (show j ≠ 0 by intro he; simp [he] at hlt)
  have hkl : k ≤ l := by
    exact Fin.le_iff_val_le_val.mpr (Nat.le_of_lt_succ hlt)
  apply disjoint_left.mpr
  intro x hx hy
  dsimp only at hx hy
  rw [gapsAfterHoles_castSucc_snd] at hx
  rw [gapsAfterHoles_succ_fst] at hy
  exact (not_lt_of_ge (((hfirst hkl).trans (hvalid l)).trans hy.1.le)) hx.2

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_OrderedHolePayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Line payment for an actual finite family of closed intervals

The removed intervals are ordered and disjoint. Smoothness is required
only on their complement. Endpoint cluster bounds pay for the jumps;
absolute continuity of the individual domain intervals is derived.
-/

open Set Function Filter MeasureTheory
open scoped Topology

namespace CircleDomainRigidity

theorem line_payment_of_ordered_holes
    {n : ℕ} {a b : ℝ} (hab : a < b) (H : Fin n → ℝ × ℝ)
    (hinside : ∀ i, a < (H i).1 ∧ (H i).1 ≤ (H i).2 ∧ (H i).2 < b)
    (hsep : ∀ i j, i < j → (H i).2 < (H j).1)
    {f d ρ : ℝ → ℝ} (A : Fin n → ℝ)
    (hd : ∀ x ∈ Icc a b ∩ (⋃ i, Icc (H i).1 (H i).2)ᶜ, HasDerivAt f (d x) x)
    (hcd : ContinuousOn d (Icc a b ∩ (⋃ i, Icc (H i).1 (H i).2)ᶜ))
    (hρ : Integrable ρ) (hpos : ∀ x, 0 ≤ ρ x)
    (hdom : ∀ x ∈ Icc a b ∩ (⋃ i, Icc (H i).1 (H i).2)ᶜ, |d x| ≤ ρ x)
    (ha : ContinuousAt f a) (hb : ContinuousAt f b) (hzero : f a = 0) (hone : f b = 1)
    (hjump : ∀ i u v,
      MapClusterPt u (𝓝[Icc a b ∩ (⋃ j, Icc (H j).1 (H j).2)ᶜ] (H i).1) f →
      MapClusterPt v (𝓝[Icc a b ∩ (⋃ j, Icc (H j).1 (H j).2)ᶜ] (H i).2) f → |v - u| ≤ A i) :
    1 ≤ (∫ x, ρ x) + ∑ i, A i := by
  let gap := gapsAfterHoles a b H
  let D := Icc a b ∩ (⋃ i, Icc (H i).1 (H i).2)ᶜ
  have hfirst : Monotone (fun i => (H i).1) := by
    intro i j hij
    rcases hij.eq_or_lt with rfl | hij
    · rfl
    · exact (hinside i).2.1.trans (hsep i j hij).le
  have hlast : Monotone (fun i => (H i).2) := by
    intro i j hij
    rcases hij.eq_or_lt with rfl | hij
    · rfl
    · exact (hsep i j hij).le.trans (hinside j).2.1
  have hgap (i : Fin (n + 1)) : (gap i).1 < (gap i).2 :=
    gapsAfterHoles_strict hab H hinside hsep i
  have hgapAB (i : Fin (n + 1)) : Ioo (gap i).1 (gap i).2 ⊆ Icc a b := by
    have hleft : a ≤ (gap i).1 := by
      change a ≤ (gapsAfterHoles a b H i).1
      refine Fin.cases ?_ (fun j => ?_) i
      · exact le_rfl
      · exact (hinside j).1.le.trans (hinside j).2.1
    have hright : (gap i).2 ≤ b := by
      change (gapsAfterHoles a b H i).2 ≤ b
      refine Fin.lastCases (motive := fun j : Fin (n + 1) =>
        (gapsAfterHoles a b H j).2 ≤ b) ?_ (fun j => ?_) i
      · simp only [gapsAfterHoles_last_snd, le_refl]
      · simpa only [gapsAfterHoles_castSucc_snd] using (hinside j).2.1.trans (hinside j).2.2.le
    exact fun _ hx => ⟨hleft.trans hx.1.le, hx.2.le.trans hright⟩
  have hgapD (i : Fin (n + 1)) : Ioo (gap i).1 (gap i).2 ⊆ D := by
    intro x hx
    refine ⟨hgapAB i hx, ?_⟩
    exact fun h => by
      obtain ⟨j, hj⟩ := mem_iUnion.mp h
      exact gapsAfterHoles_avoid a b H hfirst hlast i hx j hj
  have hgi (i : Fin (n + 1)) : IntervalIntegrable d volume (gap i).1 (gap i).2 := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (hgap i).le).mpr
    apply hρ.integrableOn.mono' ((hcd.mono (hgapD i)).aestronglyMeasurable measurableSet_Ioo)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simpa only [Real.norm_eq_abs] using hdom x (hgapD i hx)
  apply line_payment_from_open_gaps n (fun i => (gap i).1) (fun i => (gap i).2)
    f d ρ A hgap (fun i x hx => hd x (hgapD i hx)) hgi hρ hpos
    (fun i x hx => hdom x (hgapD i hx))
    (gapsAfterHoles_disjoint a b H (fun i => (hinside i).2.1) hfirst)
  · simpa only [gap, gapsAfterHoles_zero_fst, ← hzero] using
      ha.mono_left nhdsWithin_le_nhds
  · simpa only [gap, gapsAfterHoles_last_snd, ← hone] using
      hb.mono_left nhdsWithin_le_nhds
  · intro i u v hu hv
    have hnleft : NeBot (𝓝[Ioo (gap i.castSucc).1 (gap i.castSucc).2] (gap i.castSucc).2) :=
      mem_closure_iff_nhdsWithin_neBot.mp (by
        rw [closure_Ioo (hgap i.castSucc).ne]
        exact right_mem_Icc.mpr (hgap i.castSucc).le)
    have hnright : NeBot (𝓝[Ioo (gap i.succ).1 (gap i.succ).2] (gap i.succ).1) :=
      mem_closure_iff_nhdsWithin_neBot.mp (by
        rw [closure_Ioo (hgap i.succ).ne]
        exact left_mem_Icc.mpr (hgap i.succ).le)
    have hlu := hu.mapClusterPt.mono (nhdsWithin_mono _ (hgapD i.castSucc))
    have hlv := hv.mapClusterPt.mono (nhdsWithin_mono _ (hgapD i.succ))
    apply hjump i u v
    · simpa only [gap, gapsAfterHoles_castSucc_snd] using hlu
    · simpa only [gap, gapsAfterHoles_succ_fst] using hlv

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_DisjointHolePayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Payment through an unordered finite set of holes

A finite set of disjoint closed intervals is sorted inside Lean; the
variation estimate is then applied to its actual complementary gaps.
-/

open Set Function Filter MeasureTheory
open scoped Topology

namespace CircleDomainRigidity

theorem line_payment_of_disjoint_holes
    {a b : ℝ} (hab : a < b) (F : Finset (ℝ × ℝ))
    (hinside : ∀ z ∈ F, a < z.1 ∧ z.1 ≤ z.2 ∧ z.2 < b)
    (hdisj : (↑F : Set (ℝ × ℝ)).PairwiseDisjoint (fun z => Icc z.1 z.2))
    {f d ρ : ℝ → ℝ} (A : ℝ × ℝ → ℝ)
    (hd : ∀ x ∈ Icc a b ∩ (⋃ z ∈ F, Icc z.1 z.2)ᶜ, HasDerivAt f (d x) x)
    (hcd : ContinuousOn d (Icc a b ∩ (⋃ z ∈ F, Icc z.1 z.2)ᶜ))
    (hρ : Integrable ρ) (hpos : ∀ x, 0 ≤ ρ x)
    (hdom : ∀ x ∈ Icc a b ∩ (⋃ z ∈ F, Icc z.1 z.2)ᶜ, |d x| ≤ ρ x)
    (ha : ContinuousAt f a) (hb : ContinuousAt f b) (hzero : f a = 0) (hone : f b = 1)
    (hjump : ∀ z ∈ F, ∀ u v,
      MapClusterPt u (𝓝[Icc a b ∩ (⋃ w ∈ F, Icc w.1 w.2)ᶜ] z.1) f →
      MapClusterPt v (𝓝[Icc a b ∩ (⋃ w ∈ F, Icc w.1 w.2)ᶜ] z.2) f → |v - u| ≤ A z) :
    1 ≤ (∫ x, ρ x) + ∑ z ∈ F, A z := by
  classical
  let H := F.orderEmbOfFin (α := ℝ ×ₗ ℝ) rfl
  have hmem (i : Fin F.card) : H i ∈ F := F.orderEmbOfFin_mem (α := ℝ ×ₗ ℝ) rfl i
  have honto (z : ℝ × ℝ) (hz : z ∈ F) : ∃ i : Fin F.card, H i = z := by
    let z' : (F : Finset (ℝ ×ₗ ℝ)) := ⟨z, hz⟩
    refine ⟨(F.orderIsoOfFin (α := ℝ ×ₗ ℝ) rfl).symm z', ?_⟩
    exact congrArg Subtype.val ((F.orderIsoOfFin (α := ℝ ×ₗ ℝ) rfl).apply_symm_apply z')
  have hcover : (⋃ i, Icc (H i).1 (H i).2) = ⋃ z ∈ F, Icc z.1 z.2 := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨H i, mem_iUnion.mpr ⟨hmem i, hi⟩⟩
    · intro hx
      obtain ⟨z, hz, hx⟩ := mem_iUnion₂.mp hx
      obtain ⟨i, rfl⟩ := honto z hz
      exact mem_iUnion.mpr ⟨i, hx⟩
  have h := line_payment_of_ordered_holes hab H (fun i => hinside _ (hmem i))
    (sorted_holes_separated F (fun z hz => (hinside z hz).2.1) hdisj)
    (fun i => A (H i))
    (by simpa only [hcover] using hd) (by simpa only [hcover] using hcd) hρ hpos
    (by simpa only [hcover] using hdom) ha hb hzero hone
    (by
      intro i u v hu hv
      apply hjump (H i) (hmem i) u v
      · simpa only [hcover] using hu
      · simpa only [hcover] using hv)
  have hsum : (∑ i : Fin F.card, A (H i)) = ∑ z ∈ F, A z := by
    apply Finset.sum_bij (fun i _ => H i)
    · exact fun i _ => hmem i
    · exact fun i _ j _ hij => H.injective hij
    · intro z hz
      obtain ⟨i, hi⟩ := honto z hz
      exact ⟨i, Finset.mem_univ _, hi⟩
    · exact fun _ _ => rfl
  exact h.trans_eq (congrArg (fun t => (∫ x, ρ x) + t) hsum)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ParallelDiskTolls
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact costs of round holes on parallel lines

The horizontal lines meeting a closed round disk form an interval of
length twice its radius. Integrating finitely many hole tolls therefore
gives exactly the radius-weighted sum. Disjointness and a common containing
disk bound this sum by the square norm of the oscillation tolls.
-/

open Set Function Metric MeasureTheory

namespace CircleDomainRigidity

theorem parallel_disk_tolls_le_square_norm
    {I : Type*} [Fintype I] (c : I → ℂ) (r A : I → ℝ) {L : ℝ}
    (hr : ∀ i, 0 ≤ r i) (hL : 0 ≤ L)
    (hdisj : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    (hsub : ∀ i, closedBall (c i) (r i) ⊆ closedBall 0 L) :
    (∫ y : ℝ, ∑ i, (Icc ((c i).im - r i) ((c i).im + r i)).indicator (fun _ => A i) y) ≤
      2 * L * Real.sqrt (∑ i, A i ^ 2) := by
  rw [integral_parallel_disk_tolls c r A hr]
  have hs : Real.sqrt (∑ i, r i ^ 2) ≤ L := by
    simpa only [Real.sqrt_sq hL] using Real.sqrt_le_sqrt
      (sum_radii_sq_le_of_disjoint_closed_disks c r hr hL hdisj hsub)
  calc
    _ = 2 * ∑ i, r i * A i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ 2 * (Real.sqrt (∑ i, r i ^ 2) * Real.sqrt (∑ i, A i ^ 2)) :=
      mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ r A) (by norm_num)
    _ ≤ 2 * (L * Real.sqrt (∑ i, A i ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _)) (by norm_num)
    _ = _ := by ring

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_DiskLinePayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Variation across the round holes met by one line

This derives the linewise payment directly from smoothness on the
complement of the actual disks and their cluster oscillations. No
endpoint extension or pre-existing line-payment hypothesis is assumed.
-/

open Set Function Filter Metric MeasureTheory
open scoped Topology

namespace CircleDomainRigidity

theorem line_payment_through_disks
    {I : Type*} [Fintype I] (c : I → ℂ) (r A : I → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hA : ∀ i, 0 ≤ A i)
    (hdisj : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    {y a b : ℝ} (hab : a < b)
    (ha : a ∈ diskLineDomain c r y) (hb : b ∈ diskLineDomain c r y)
    {f ρ : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (diskLineDomain c r y))
    (hzero : f a = 0) (hone : f b = 1)
    (hρ : Integrable ρ) (hpos : ∀ x, 0 ≤ ρ x)
    (hmajor : ∀ x ∈ Icc a b ∩ diskLineDomain c r y, |deriv f x| ≤ ρ x)
    (hcluster : ∀ i p q u v,
      (⟨p, y⟩ : ℂ) ∈ closedBall (c i) (r i) →
      (⟨q, y⟩ : ℂ) ∈ closedBall (c i) (r i) →
      MapClusterPt u (𝓝[diskLineDomain c r y] p) f →
      MapClusterPt v (𝓝[diskLineDomain c r y] q) f → |v - u| ≤ A i) :
    1 ≤ (∫ x, ρ x) +
      ∑ i, (Icc ((c i).im - r i) ((c i).im + r i)).indicator (fun _ => A i) y := by
  classical
  let F := crossingChords c r y a b
  let E := Icc a b ∩ (⋃ z ∈ F, Icc z.1 z.2)ᶜ
  have hED : E ⊆ diskLineDomain c r y := by
    intro x hx
    exact (crossingChords_domain c r hr hx.1).mp hx.2
  have hD := isOpen_diskLineDomain c r y
  have hfa := hf.contDiffAt (hD.mem_nhds ha)
  have hfb := hf.contDiffAt (hD.mem_nhds hb)
  have hp := line_payment_of_disjoint_holes hab F
    (crossingChords_inside c r hr
      (fun i hi => ha (mem_iUnion.mpr ⟨i, hi⟩))
      (fun i hi => hb (mem_iUnion.mpr ⟨i, hi⟩)))
    (crossingChords_disjoint c r hr hdisj) (chordToll c r A y a b)
    (fun x hx => (hf.contDiffAt (hD.mem_nhds (hED hx))).differentiableAt (by norm_num) |>.hasDerivAt)
    ((hf.continuousOn_deriv_of_isOpen hD le_rfl).mono hED)
    hρ hpos (fun x hx => hmajor x ⟨hx.1, hED hx⟩)
    hfa.continuousAt hfb.continuousAt hzero hone (by
      intro z hz u v hu hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      have hy := crossingDisk_line_hit hi
      have hp := (mem_closedBall_iff_mem_horizontalChord (c i) (hr i) hy).mpr
        (left_mem_Icc.mpr (horizontalChord_valid _ _ _))
      have hq := (mem_closedBall_iff_mem_horizontalChord (c i) (hr i) hy).mpr
        (right_mem_Icc.mpr (horizontalChord_valid _ _ _))
      exact (hcluster i _ _ u v hp hq
        (hu.mono (nhdsWithin_mono _ hED))
        (hv.mono (nhdsWithin_mono _ hED))).trans (le_chordToll c r A y a b hA hi))
  exact hp.trans (add_le_add le_rfl (sum_chordToll_le_line_hits c r A y a b hA))

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_TerminalNormBudget
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# From terminal excess to the full oscillation norm

The finite transfer bounds the square-sum of the positive excess above
the original band widths. The elementary Euclidean triangle inequality
then gives the full oscillation norm needed in parallel-line payment.
-/

open Set

namespace CircleDomainRigidity

theorem sqrt_sum_sq_le_of_excess_budget {I : Type*} [Fintype I]
    (a b : I → ℝ) {B ε : ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hband : Real.sqrt (∑ i, b i ^ 2) ≤ B)
    (hexcess : Real.sqrt (∑ i, max (a i - b i) 0 ^ 2) ≤ ε) :
    Real.sqrt (∑ i, a i ^ 2) ≤ B + ε :=
  (sqrt_sum_sq_le_band_add_excess a b ha hb).trans (add_le_add hband hexcess)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ComplexCovectorWedge
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact Euclidean determinant bound for two real covectors on the
complex plane, with constant one. -/

open Set Function

noncomputable section
namespace CircleDomainRigidity

 theorem complexCovector_wedge_bound (A B : ℂ →L[ℝ] ℝ) :
    |A 1 * B Complex.I - A Complex.I * B 1| ≤ ‖A‖ * ‖B‖ := by
  let z : ℂ := (B 1 : ℂ) + (B Complex.I : ℂ) * Complex.I
  let w : ℂ := -Complex.I * z
  have hwre : w.re = B Complex.I := by simp [w, z]
  have hwim : w.im = -B 1 := by simp [w, z]
  have hval : A w = A 1 * B Complex.I - A Complex.I * B 1 := by
    rw [complexCovector_apply, hwre, hwim]
    ring
  have hwnorm : ‖w‖ = ‖z‖ := by simp only [w, norm_mul, norm_neg, Complex.norm_I, one_mul]
  calc
    _ = ‖A w‖ := by rw [hval, Real.norm_eq_abs]
    _ ≤ ‖A‖ * ‖w‖ := A.le_opNorm w
    _ = ‖A‖ * ‖z‖ := by rw [hwnorm]
    _ ≤ ‖A‖ * ‖B‖ := mul_le_mul_of_nonneg_left
      (complexCovector_dualVector_norm_le B) (norm_nonneg _)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RoundHoleOffsets
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single positive offset works for a finite family of disjoint round
holes. The enlarged closed holes remain disjoint and inside the given
open region, including when an original hole has radius zero. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem exists_common_round_hole_offset
    {I : Type*} [Fintype I] (c : I → ℂ) (r : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hd : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    {U : Set ℂ} (hU : IsOpen U) (hin : ∀ i, closedBall (c i) (r i) ⊆ U) :
    ∃ ε > 0, ∀ ρ ∈ Ioc (0 : ℝ) ε,
      (∀ i, closedBall (c i) (r i + ρ) ⊆ U) ∧
      Pairwise (Disjoint on fun i => closedBall (c i) (r i + ρ)) := by
  classical
  have hn : Pairwise (Disjoint on fun i => 𝓝ˢ (closedBall (c i) (r i))) := by
    intro i j hij
    exact disjoint_nhdsSet_nhdsSet isClosed_closedBall isClosed_closedBall (hd hij)
  obtain ⟨V, hV, hVdisj⟩ := hn.exists_mem_filter_basis_of_disjoint
    (fun i => hasBasis_nhdsSet (closedBall (c i) (r i)))
  have he (i : I) : ∃ δ > 0, closedBall (c i) (r i + δ) ⊆ V i ∩ U := by
    obtain ⟨δ, hδ, hs⟩ := (isCompact_closedBall (c i) (r i)).exists_cthickening_subset_open
      ((hV i).1.inter hU) (fun z hz => ⟨(hV i).2 hz, hin i hz⟩)
    refine ⟨δ, hδ, ?_⟩
    simpa only [cthickening_closedBall hδ.le (hr i), add_comm δ] using hs
  choose δ hδ hδsub using he
  let S : Finset ℝ := insert 1 (Finset.univ.image δ)
  have hS : S.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  let ε := S.min' hS
  have hε : 0 < ε := by
    have hm : ε ∈ S := Finset.min'_mem S hS
    rcases Finset.mem_insert.mp hm with hm | hm
    · rw [hm]; exact zero_lt_one
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
      rw [← hi]
      exact hδ i
  have hεi (i : I) : ε ≤ δ i :=
    Finset.min'_le S (δ i) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
  refine ⟨ε, hε, ?_⟩
  intro ρ hρ
  have hsub (i : I) : closedBall (c i) (r i + ρ) ⊆ V i ∩ U :=
    (closedBall_subset_closedBall (add_le_add le_rfl (hρ.2.trans (hεi i)))).trans (hδsub i)
  exact ⟨fun i z hz => (hsub i hz).2, fun i j hij => (hVdisj hij).mono
    (fun z hz => (hsub i hz).1) (fun z hz => (hsub j hz).1)⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CircleLifts
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Real lifts of circle coordinates near filling disks

The quotient `ℝ → ℝ/ℤ` is a covering map in Mathlib. Its lifting theorem
therefore gives actual continuous real branches on simply connected open
sets. Smoothness is expressed in the ordinary real quotient charts
`AddCircle.equivIco`; a continuous lift is locally one of these charts plus
an integer, so the lift is smooth. No external lifting axiom is used.
-/

open Set Filter Function Metric
open scoped Topology ContDiff

namespace CircleDomainRigidity.FiniteTransfer

theorem exists_continuous_circle_lift
    {X : Type*} [TopologicalSpace X] {U : Set X}
    [SimplyConnectedSpace U] [LocallyPathConnectedSpace U]
    (f : X → UnitAddCircle) (hf : ContinuousOn f U)
    {x₀ : X} (hx₀ : x₀ ∈ U) (r₀ : ℝ) (hr₀ : (r₀ : UnitAddCircle) = f x₀) :
    ∃ u : X → ℝ, ContinuousOn u U ∧ u x₀ = r₀ ∧
      ∀ x ∈ U, (u x : UnitAddCircle) = f x := by
  classical
  let f' : C(U, UnitAddCircle) := ⟨fun x => f x, hf.domRestrict⟩
  obtain ⟨g, ⟨hg₀, hg⟩, _⟩ :=
    (AddCircle.isCoveringMap_coe (1 : ℝ)).existsUnique_continuousMap_lifts
      f' ⟨x₀, hx₀⟩ r₀ hr₀
  let u : X → ℝ := fun x => if hx : x ∈ U then g ⟨x, hx⟩ else 0
  refine ⟨u, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    convert g.continuous using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    change u x = g x
    simp only [u, dite_eq_left x.property]
  · simpa only [u, dite_eq_left hx₀] using hg₀
  · intro x hx
    have h := congrFun hg (⟨x, hx⟩ : U)
    change (g ⟨x, hx⟩ : UnitAddCircle) = f x at h
    simpa only [u, dite_eq_left hx] using h

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CircleCovectors
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth covector fields of periodic coordinates

The locally defined circle differential is an ordinary smooth covector
field on its open domain. This supplies the tensor used in the same
metric construction as for single-valued real coordinates.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem contDiffOn_circleFDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → UnitAddCircle} {U : Set E} (hU : IsOpen U) (hf : SmoothCircleOn f U) :
    ContDiffOn ℝ ∞ (circleFDeriv f) U := by
  intro x hx
  let a := circleCut f x
  let V := U ∩ f ⁻¹' ({(a : UnitAddCircle)} : Set UnitAddCircle)ᶜ
  have hV : IsOpen V := hf.continuousOn.isOpen_inter_preimage hU isClosed_singleton.isOpen_compl
  have hxV : x ∈ V := ⟨hx, circleCut_ne f x⟩
  have hu : ContDiffOn ℝ ∞ (circleBranch f a) V := by
    intro y hy
    exact (hf y hy.1 a hy.2).contDiffWithinAt
  have heq := circleFDeriv_eventuallyEq_lift hV (hf.continuousOn.mono inter_subset_left)
    hu (fun y _ => coe_circleBranch f a y) hxV
  exact (((hu.fderiv_of_isOpen (m := ∞) hV (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt (hV.mem_nhds hxV)).congr_of_eventuallyEq
    heq).contDiffWithinAt

theorem contDiffOn_circleGradient
    {f : (ℝ × ℝ) → UnitAddCircle} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hf : SmoothCircleOn f U) : ContDiffOn ℝ ∞ (circleGradient f) U := by
  have hd := contDiffOn_circleFDeriv hU hf
  exact (hd.clm_apply contDiffOn_const).prodMk (hd.clm_apply contDiffOn_const)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CircleDifferentialClosed
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The intrinsic differential of a smooth circle coordinate is closed.
The proof uses actual local real branches and symmetry of their Hessians. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem circleFDeriv_partial_commute
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → UnitAddCircle} {U : Set E} (hU : IsOpen U) (hf : SmoothCircleOn f U)
    {x : E} (hx : x ∈ U) (v w : E) :
    (fderiv ℝ (fun y => circleFDeriv f y w) x) v =
      (fderiv ℝ (fun y => circleFDeriv f y v) x) w := by
  let a := circleCut f x
  let V := U ∩ f ⁻¹' ({(a : UnitAddCircle)} : Set UnitAddCircle)ᶜ
  have hV : IsOpen V := hf.continuousOn.isOpen_inter_preimage hU isClosed_singleton.isOpen_compl
  have hxV : x ∈ V := ⟨hx, circleCut_ne f x⟩
  have hu : ContDiffOn ℝ (⊤ : ℕ∞) (circleBranch f a) V := by
    intro y hy
    exact (hf y hy.1 a hy.2).contDiffWithinAt
  have heq := circleFDeriv_eventuallyEq_lift hV (hf.continuousOn.mono inter_subset_left)
    hu (fun y _ => coe_circleBranch f a y) hxV
  have hp (z : E) : (fun y => circleFDeriv f y z) =ᶠ[𝓝 x]
      (fun y => (fderiv ℝ (circleBranch f a) y) z) :=
    heq.mono fun _ h => congrArg (fun L : E →L[ℝ] ℝ => L z) h
  rw [(hp w).fderiv_eq, (hp v).fderiv_eq]
  have huAt := hu.contDiffAt (hV.mem_nhds hxV)
  have hdu : DifferentiableAt ℝ (fderiv ℝ (circleBranch f a)) x :=
    (huAt.fderiv_right (m := 1) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt (by norm_num)
  rw [fderiv_clm_apply hdu (differentiableAt_const w),
    fderiv_clm_apply hdu (differentiableAt_const v)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add]
  exact huAt.isSymmSndFDerivAt (by simp) v w

 theorem circleFDeriv_closed_complex
    {f : ℂ → UnitAddCircle} {U : Set ℂ} (hU : IsOpen U) (hf : SmoothCircleOn f U)
    {z : ℂ} (hz : z ∈ U) :
    (fderiv ℝ (fun x => circleFDeriv f x Complex.I) z) 1 =
      (fderiv ℝ (fun x => circleFDeriv f x 1) z) Complex.I :=
    circleFDeriv_partial_commute hU hf hz 1 Complex.I

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ParallelLineIntegration
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integration of the parallel-line payments

The linewise variation and hole costs are integrated without a measurable
choice of crossing segments. Cauchy–Schwarz is applied only to the density
in the chosen bounded region. This is the integration step of the
parallel-line lemma in Section 5 of the Koebe manuscript.
-/

open Set Function Metric MeasureTheory

namespace CircleDomainRigidity

theorem integral_horizontal_slices {ρ : ℂ → ℝ} (hρ : Integrable ρ) :
    Integrable (fun y : ℝ => ∫ x : ℝ, ρ ⟨x, y⟩) ∧
      (∫ y : ℝ, ∫ x : ℝ, ρ ⟨x, y⟩) = ∫ z : ℂ, ρ z := by
  have he := (Complex.volume_preserving_equiv_real_prod.symm
    Complex.measurableEquivRealProd).integrable_comp hρ.aestronglyMeasurable
  have hp : Integrable (fun p : ℝ × ℝ => ρ ⟨p.1, p.2⟩) := he.mpr hρ
  refine ⟨hp.integral_prod_right, ?_⟩
  calc
    _ = ∫ p : ℝ × ℝ, ρ ⟨p.1, p.2⟩ := (integral_prod_symm _ hp).symm
    _ = _ := (Complex.volume_preserving_equiv_real_prod.symm
      Complex.measurableEquivRealProd).integral_comp' ρ

theorem integrated_parallel_line_payment
    {I : Type*} [Fintype I] (c : I → ℂ) (r A : I → ℝ)
    {ρ : ℂ → ℝ} {J : Set ℝ} {L : ℝ}
    (hJfinite : volume J ≠ ⊤)
    (hr : ∀ i, 0 ≤ r i) (hA : ∀ i, 0 ≤ A i) (hL : 0 ≤ L)
    (hρ : MemLp ρ 2 volume) (hpos : ∀ z, 0 ≤ ρ z)
    (hsupport : support ρ ⊆ closedBall 0 L)
    (hpay : ∀ᵐ y ∂volume.restrict J, 1 ≤ (∫ x : ℝ, ρ ⟨x, y⟩) +
      ∑ i, (Icc ((c i).im - r i) ((c i).im + r i)).indicator (fun _ => A i) y) :
    (volume J).toReal ≤ Real.sqrt Real.pi * L * Real.sqrt (∫ z, ρ z ^ 2) +
      ∑ i, 2 * r i * A i := by
  let : IsFiniteMeasure (volume.restrict J) := isFiniteMeasure_restrict.mpr hJfinite
  have hiρ := integral_le_disk_L2 hL hρ hpos hsupport
  have hslices := integral_horizontal_slices hiρ.1
  let toll : ℝ → ℝ := fun y =>
    ∑ i, (Icc ((c i).im - r i) ((c i).im + r i)).indicator (fun _ => A i) y
  have hitoll : Integrable toll := by
    apply integrable_finsetSum
    intro i _
    exact (integrableOn_const measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc
  have hsumpos : ∀ y, 0 ≤ (∫ x : ℝ, ρ ⟨x, y⟩) + toll y := by
    intro y
    exact add_nonneg (integral_nonneg (fun _ => hpos _))
      (Finset.sum_nonneg (fun i _ => indicator_nonneg (fun _ _ => hA i) y))
  calc
    (volume J).toReal = ∫ _y in J, (1 : ℝ) := by simp [measureReal_def]
    _ ≤ ∫ y in J, (∫ x : ℝ, ρ ⟨x, y⟩) + toll y :=
      integral_mono_ae (integrable_const _) (hslices.1.add hitoll).integrableOn hpay
    _ ≤ ∫ y : ℝ, (∫ x : ℝ, ρ ⟨x, y⟩) + toll y :=
      setIntegral_le_integral (hslices.1.add hitoll) (Filter.Eventually.of_forall hsumpos)
    _ = (∫ z, ρ z) + ∑ i, 2 * r i * A i := by
      rw [integral_add hslices.1 hitoll, hslices.2]
      exact congrArg _ (integral_parallel_disk_tolls c r A hr)
    _ ≤ _ := add_le_add hiρ.2 le_rfl

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ComplexWedgeIntegral
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The area contribution to the Stokes estimate has the sharp factor
sqrt(pi) times the containing radius. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem integral_complexCovector_wedge_le
    {Ω : Set ℂ} (hΩ : MeasurableSet Ω) {R : ℝ} (hR : 0 ≤ R)
    (hbounded : Ω ⊆ closedBall 0 R)
    (A B : ℂ → ℂ →L[ℝ] ℝ) (hA : ContinuousOn A Ω) (hB : ContinuousOn B Ω)
    (hB2 : MemLp B 2 (volume.restrict Ω))
    (hA1 : ∀ z ∈ Ω, ‖A z‖ ≤ 1) :
    |∫ z in Ω, A z 1 * B z Complex.I - A z Complex.I * B z 1| ≤
      Real.sqrt Real.pi * R * Real.sqrt (∫ z in Ω, ‖B z‖ ^ 2) := by
  let : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr ((measure_mono hbounded).trans_lt measure_closedBall_lt_top).ne
  have hnorm : Integrable (fun z => ‖B z‖) (volume.restrict Ω) :=
    hB2.norm.integrable (by norm_num)
  have hcont : ContinuousOn (fun z => A z 1 * B z Complex.I - A z Complex.I * B z 1) Ω :=
    ((hA.clm_apply continuousOn_const).mul (hB.clm_apply continuousOn_const)).sub
      ((hA.clm_apply continuousOn_const).mul (hB.clm_apply continuousOn_const))
  have hbound : ∀ᵐ z ∂(volume.restrict Ω),
      ‖A z 1 * B z Complex.I - A z Complex.I * B z 1‖ ≤ ‖B z‖ := by
    filter_upwards [ae_restrict_mem hΩ] with z hz
    rw [Real.norm_eq_abs]
    exact (complexCovector_wedge_bound (A z) (B z)).trans
      ((mul_le_mul_of_nonneg_right (hA1 z hz) (norm_nonneg _)).trans_eq (one_mul _))
  have hi := hnorm.mono' (hcont.aestronglyMeasurable hΩ) hbound
  have hm : Real.sqrt ((volume.restrict Ω).real univ) ≤ Real.sqrt Real.pi * R := by
    have hm' : (volume.restrict Ω).real univ ≤ Real.pi * R ^ 2 := by
      rw [Measure.real, Measure.restrict_apply_univ]
      exact (measureReal_mono hbounded measure_closedBall_lt_top.ne).trans_eq
        (real_volume_closedBall 0 hR)
    exact (Real.sqrt_le_sqrt hm').trans_eq (by rw [Real.sqrt_mul Real.pi_pos.le, Real.sqrt_sq hR])
  calc
    _ ≤ ∫ z in Ω, ‖A z 1 * B z Complex.I - A z Complex.I * B z 1‖ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun z => A z 1 * B z Complex.I - A z Complex.I * B z 1)
    _ ≤ ∫ z in Ω, ‖B z‖ := integral_mono_ae hi.norm hnorm hbound
    _ ≤ Real.sqrt ((volume.restrict Ω).real univ) *
        Real.sqrt (∫ z in Ω, ‖B z‖ ^ 2) :=
      integral_le_sqrt_measure_mul_L2 hB2.norm (Eventually.of_forall fun _ => norm_nonneg _)
    _ ≤ _ := by gcongr

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothRealLift
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous real lift of a smooth circle map is automatically smooth,
with exactly its intrinsic differential and no additional energy cost. -/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff ENNReal

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiffOn_real_lift {U : Set E} (hU : IsOpen U)
    {f : E → UnitAddCircle} (hf : SmoothCircleOn f U)
    {u : E → ℝ} (hu : ContinuousOn u U)
    (hproj : ∀ x ∈ U, (u x : UnitAddCircle) = f x) :
    ContDiffOn ℝ ∞ u U := by
  intro x hx
  have hux : ContinuousAt u x := (hu x hx).continuousAt (hU.mem_nhds hx)
  have hb := hf x hx (circleCut f x) (circleCut_ne f x)
  have heq : (fun y => (u y : UnitAddCircle)) =ᶠ[𝓝 x]
      fun y => (circleBranch f (circleCut f x) y : UnitAddCircle) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [hproj y hy, coe_circleBranch]
  obtain ⟨m, hm⟩ := eventually_lifts_differ_by_integer hux hb.continuousAt heq
  exact ((hb.add contDiffAt_const).congr_of_eventuallyEq hm).contDiffWithinAt

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_FiniteCircleStokes
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-region Stokes identity and area bound for the actual
intrinsic differential of a smooth circle coordinate. The only additional
published input is the precisely stated classical Green formula. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem circleFormIntegral_eq_real_lift
    {O : Set ℂ} (hO : IsOpen O) {u : ℂ → UnitAddCircle} (hu : SmoothCircleOn u O)
    (φ : ℂ → ℝ) (γ : ℝ → ℂ) (hγ : Differentiable ℝ γ) (hγO : ∀ t, γ t ∈ O)
    (v : ℝ → ℝ) (hv : Continuous v) (hproj : ∀ t, (v t : UnitAddCircle) = u (γ t)) :
    circleFormIntegral φ u γ = ∫ t in (0 : ℝ)..1, φ (γ t) * deriv v t := by
  have hd (t : ℝ) : deriv v t = circleFDeriv u (γ t) (deriv γ t) := by
    have he : fderiv ℝ v t = circleFDeriv (u ∘ γ) t := by
      symm
      apply circleFDeriv_eq_lift
        ((hu.continuousOn.continuousAt (hO.mem_nhds (hγO t))).comp (hγ t).continuousAt)
        hv.continuousAt
      exact Eventually.of_forall hproj
    rw [← fderiv_apply_one_eq_deriv, he, circleFDeriv_comp hO hu (hγ t) (hγO t)]
    simp only [ContinuousLinearMap.comp_apply, fderiv_apply_one_eq_deriv]
  unfold circleFormIntegral planarFormIntegral
  apply intervalIntegral.integral_congr
  intro t _
  change (φ (γ t) * circleFDeriv u (γ t) 1) * (deriv γ t).re +
    (φ (γ t) * circleFDeriv u (γ t) Complex.I) * (deriv γ t).im =
    φ (γ t) * deriv v t
  conv_rhs => rw [hd t, complexCovector_apply]
  ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CircleFormBoundary
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual boundary terms for the finite-circle Stokes formula. Smoothness
and integrability of real lifts follow from the circle coordinate, rather
than being extra analytic hypotheses on each boundary. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem contDiff_unitCircleParam (c : ℂ) (r : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (unitCircleParam c r) :=
  (contDiff_circleMap c r).comp (contDiff_const.mul contDiff_id)

 theorem lipschitzWith_unitCircleParam (c : ℂ) (r : ℝ) :
    LipschitzWith (Real.nnabs r * ‖(2 * Real.pi : ℝ)‖₊) (unitCircleParam c r) := by
  exact (lipschitzWith_circleMap c r).comp (lipschitzWith_smul (2 * Real.pi : ℝ))

 theorem contDiff_real_lift_along
    {O : Set ℂ} {u : ℂ → UnitAddCircle} (hu : SmoothCircleOn u O)
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) (hγO : ∀ t, γ t ∈ O)
    {v : ℝ → ℝ} (hv : Continuous v) (hproj : ∀ t, (v t : UnitAddCircle) = u (γ t)) :
    ContDiff ℝ (⊤ : ℕ∞) v := by
  apply contDiffOn_univ.mp
  apply contDiffOn_real_lift isOpen_univ _ hv.continuousOn (fun t _ => hproj t)
  intro t _ a ha
  exact (hu (γ t) (hγO t) a ha).comp t hγ.contDiffAt

 theorem circleFormIntegral_unitCircle_zero_period
    {O : Set ℂ} (hO : IsOpen O) {u : ℂ → UnitAddCircle} (hu : SmoothCircleOn u O)
    (φ : ℂ → ℝ) (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ O) (hφlip : LipschitzWith 1 φ)
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hcircle : ∀ t, unitCircleParam c r t ∈ O)
    (v : ℝ → ℝ) (hv : Continuous v)
    (hproj : ∀ t, (v t : UnitAddCircle) = u (unitCircleParam c r t))
    (hperiod : v 1 = v 0) (A : ℝ) (hA : ∀ t ∈ Icc (0 : ℝ) 1, |v t - v 0| ≤ A) :
    |circleFormIntegral φ u (unitCircleParam c r)| ≤ 2 * Real.pi * r * A := by
  have hc := contDiff_unitCircleParam c r
  have hvs := contDiff_real_lift_along hu hc hcircle hv hproj
  have hφs : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ unitCircleParam c r) := by
    apply contDiffOn_univ.mp
    intro t _
    exact ((hφ.contDiffAt (hO.mem_nhds (hcircle t))).comp t hc.contDiffAt).contDiffWithinAt
  rw [circleFormIntegral_eq_real_lift hO hu φ _ (hc.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hcircle v hv hproj]
  have hb := zero_period_weighted_integral_bound (K := 2 * Real.pi * r) (φ ∘ unitCircleParam c r)
    (deriv (φ ∘ unitCircleParam c r)) v (deriv v) zero_le_one
    (fun t _ => (hφs.differentiable (by simp) t).hasDerivAt)
    (fun t _ => (hvs.differentiable (by simp) t).hasDerivAt)
    ((hφs.continuous_deriv (by simp)).intervalIntegrable 0 1)
    ((hvs.continuous_deriv (by simp)).intervalIntegrable 0 1) hperiod ?_ hA
  · simpa only [one_mul, Function.comp_apply] using hb
  · intro t _
    have hd := (hφs.differentiable (by simp) t).hasDerivAt.le_of_lipschitz
      (hφlip.comp (lipschitzWith_unitCircleParam c r))
    have hb : |deriv (φ ∘ unitCircleParam c r) t| ≤ r * (2 * Real.pi) := by
      simpa only [Real.norm_eq_abs, NNReal.coe_mul, NNReal.coe_one, one_mul,
        Real.coe_nnabs, coe_nnnorm, abs_of_nonneg hr,
        abs_of_pos (show (0 : ℝ) < 2 * Real.pi by positivity)] using hd
    calc
      _ ≤ r * (2 * Real.pi) := hb
      _ = _ := by ring

 theorem circleFormIntegral_constant_weight
    {O : Set ℂ} (hO : IsOpen O) {u : ℂ → UnitAddCircle} (hu : SmoothCircleOn u O)
    (φ : ℂ → ℝ) (γ : ℝ → ℂ) (hγ : ContDiff ℝ (⊤ : ℕ∞) γ)
    (hγO : ∀ t, γ t ∈ O) (v : ℝ → ℝ) (hv : Continuous v)
    (hproj : ∀ t, (v t : UnitAddCircle) = u (γ t))
    (ρ : ℝ) (hφ : ∀ t ∈ Icc (0 : ℝ) 1, φ (γ t) = ρ) :
    circleFormIntegral φ u γ = ρ * (v 1 - v 0) := by
  have hvs := contDiff_real_lift_along hu hγ hγO hv hproj
  rw [circleFormIntegral_eq_real_lift hO hu φ γ (hγ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hγO v hv hproj]
  calc
    _ = ∫ t in (0 : ℝ)..1, ρ * deriv v t := by
      apply intervalIntegral.integral_congr
      intro t ht
      change φ (γ t) * deriv v t = ρ * deriv v t
      rw [hφ t (by simpa only [uIcc_of_le zero_le_one] using ht)]
    _ = ρ * (v 1 - v 0) := constant_weight_integral_eq_period v (deriv v) 1 ρ
      (fun t _ => (hvs.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) t).hasDerivAt)
      ((hvs.continuous_deriv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).intervalIntegrable 0 1)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_FiniteOffsetStokes
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite offset estimate from Green's formula. The nonzero period
is kept at the distinguished hole. All other boundary costs use the
oscillations of their real lifts. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology BigOperators

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem circle_boundary_mem_smooth_region
    {n : ℕ} (H : ℂ ≃ₜ ℂ) (c : Fin n → ℂ) (r : Fin n → ℝ)
    (hr : ∀ i, 0 ≤ r i)
    (hd : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    (hin : ∀ i, closedBall (c i) (r i) ⊆ jordanInterior H)
    {O : Set ℂ} (hsub : (closure (jordanInterior H) \ ⋃ i, ball (c i) (r i)) ⊆ O)
    (i : Fin n) (t : ℝ) : unitCircleParam (c i) (r i) t ∈ O := by
  have hs : unitCircleParam (c i) (r i) t ∈ sphere (c i) (r i) :=
    circleMap_mem_sphere _ (hr i) _
  have hc := sphere_subset_closedBall hs
  apply hsub
  refine ⟨subset_closure (hin i hc), ?_⟩
  rintro hm
  obtain ⟨j, hj⟩ := mem_iUnion.mp hm
  by_cases hij : i = j
  · subst j
    have he := mem_sphere.mp hs
    have hl := mem_ball.mp hj
    linarith
  · exact Set.disjoint_left.mp (hd hij) hc (ball_subset_closedBall hj)

 theorem circle_costs_le_square_norm
    {I : Type*} [DecidableEq I] (s : Finset I) (r A : I → ℝ) {L : ℝ}
    (hL : 0 ≤ L) (hr : ∑ i ∈ s, r i ^ 2 ≤ L ^ 2) :
    (∑ i ∈ s, 2 * Real.pi * r i * A i) ≤
      2 * Real.pi * L * Real.sqrt (∑ i ∈ s, A i ^ 2) := by
  have hs : Real.sqrt (∑ i ∈ s, r i ^ 2) ≤ L := by
    simpa only [Real.sqrt_sq hL] using Real.sqrt_le_sqrt hr
  calc
    _ = (2 * Real.pi) * ∑ i ∈ s, r i * A i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ (2 * Real.pi) * (Real.sqrt (∑ i ∈ s, r i ^ 2) *
        Real.sqrt (∑ i ∈ s, A i ^ 2)) :=
      mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt s r A) (by positivity)
    _ ≤ (2 * Real.pi) * (L * Real.sqrt (∑ i ∈ s, A i ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _)) (by positivity)
    _ = _ := by ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RoundDiskDistance
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual distance weight in the Stokes estimate: it is smooth off
the closed round disk and equals the offset on a concentric circle. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem infDist_closedBall_of_dist_gt (c z : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hz : r < dist z c) :
    infDist z (closedBall c r) = dist z c - r := by
  have hd : 0 < dist z c := hr.trans_lt hz
  have hne : dist z c ≠ 0 := hd.ne'
  let a := r / dist z c
  let p := c + a • (z - c)
  have ha : 0 ≤ a := div_nonneg hr hd.le
  have ha1 : a ≤ 1 := (div_le_one hd).mpr hz.le
  have hp : p ∈ closedBall c r := by
    rw [mem_closedBall, dist_eq_norm]
    dsimp only [p]
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
    rw [← dist_eq_norm, div_mul_cancel₀ r hne]
  have hdist : dist z p = dist z c - r := by
    have heq : z - p = (1 - a) • (z - c) := by dsimp only [p]; module
    rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr ha1), ← dist_eq_norm]
    dsimp only [a]
    rw [sub_mul, one_mul, div_mul_cancel₀ r hne]
  apply le_antisymm
  · exact (infDist_le_dist_of_mem hp).trans_eq hdist
  · apply (le_infDist ⟨c, mem_closedBall_self hr⟩).mpr
    intro y hy
    have htri := dist_triangle z y c
    have hy' := mem_closedBall.mp hy
    linarith

 theorem contDiffOn_infDist_closedBall (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => infDist z (closedBall c r)) (closedBall c r)ᶜ := by
  intro z hz
  have hzr : r < dist z c := lt_of_not_ge hz
  have hzc : z ≠ c := by
    intro he
    subst z
    simp only [dist_self] at hzr
    linarith
  have hs : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : ℂ => dist w c - r) z :=
    (contDiffAt_id.dist ℝ contDiffAt_const hzc).sub contDiffAt_const
  apply (hs.congr_of_eventuallyEq _).contDiffWithinAt
  filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hz] with w hw
  exact infDist_closedBall_of_dist_gt c w hr (lt_of_not_ge hw)

 theorem infDist_closedBall_unitCircle_offset (c : ℂ) {r ρ : ℝ}
    (hr : 0 ≤ r) (hρ : 0 < ρ) (t : ℝ) :
    infDist (unitCircleParam c (r + ρ) t) (closedBall c r) = ρ := by
  have hc : dist (unitCircleParam c (r + ρ) t) c = r + ρ :=
    mem_sphere.mp (circleMap_mem_sphere c (by linarith : 0 ≤ r + ρ) _)
  rw [infDist_closedBall_of_dist_gt c _ hr (by rw [hc]; linarith), hc]
  ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_FinitePeriodStokes
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The distinguished offset disappears for every fixed finite period.
No normalization of that period is needed for the Stokes upper bound. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology BigOperators

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem abs_le_of_boundary_costs
    {I : Type*} [Fintype I] [DecidableEq I] (b : I)
    (outer : ℝ) (inner : I → ℝ) (E B : ℝ) (cost : I → ℝ)
    (harea : |outer - ∑ i, inner i| ≤ E) (hb : |inner b| ≤ B)
    (hother : ∀ i ≠ b, |inner i| ≤ cost i) :
    |outer| ≤ E + B + ∑ i ∈ Finset.univ.erase b, cost i := by
  have hsum : (∑ i, |inner i|) ≤ B + ∑ i ∈ Finset.univ.erase b, cost i := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ b), add_comm]
    exact add_le_add hb (Finset.sum_le_sum fun i hi => hother i (Finset.mem_erase.mp hi).1)
  calc
    |outer| = |(outer - ∑ i, inner i) + ∑ i, inner i| := by congr 1; ring
    _ ≤ |outer - ∑ i, inner i| + |∑ i, inner i| := abs_add_le _ _
    _ ≤ E + ∑ i, |inner i| := add_le_add harea (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ E + (B + ∑ i ∈ Finset.univ.erase b, cost i) := add_le_add le_rfl hsum
    _ = _ := by ring

 theorem zero_offset_stokes_bound_of_period
    {I : Type*} (s : Finset I) (r A : I → ℝ) (hA : ∀ i ∈ s, 0 ≤ A i)
    (outer E k : ℝ)
    (hbound : ∀ ε > 0, ∃ ρ > 0, ρ ≤ ε ∧
      |outer| ≤ E + ε + ρ * |k| + ∑ i ∈ s, 2 * Real.pi * (r i + ρ) * (A i + ε)) :
    |outer| ≤ E + ∑ i ∈ s, 2 * Real.pi * r i * A i := by
  let g : ℝ → ℝ := fun ε => E + ε + ε * |k| + ∑ i ∈ s, 2 * Real.pi * (r i + ε) * (A i + ε)
  have hg : Continuous g := by dsimp only [g]; fun_prop
  have hlim : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 (E + ∑ i ∈ s, 2 * Real.pi * r i * A i)) := by
    simpa only [g, add_zero, zero_mul] using
      (hg.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  obtain ⟨ρ, _, hρε, hI⟩ := hbound ε hε
  refine hI.trans ?_
  apply add_le_add
  · exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hρε (abs_nonneg k))
  · apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hρε) (by positivity))
      (add_nonneg (hA i hi) hε.le)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_OffsetRegions
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometry and energy monotonicity for the actual regions obtained by
moving finitely many round boundaries a common positive distance. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem offset_closed_region_subset
    {I : Type*} (H : ℂ ≃ₜ ℂ) (c : I → ℂ) (r : I → ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    closure (jordanInterior H) \ ⋃ i, ball (c i) (r i + ρ) ⊆
      closure (jordanInterior H) \ ⋃ i, closedBall (c i) (r i) := by
  intro z hz
  refine ⟨hz.1, ?_⟩
  rintro hm
  obtain ⟨i, hi⟩ := mem_iUnion.mp hm
  apply hz.2
  apply mem_iUnion.mpr
  refine ⟨i, ?_⟩
  rw [mem_ball]
  exact (mem_closedBall.mp hi).trans_lt (by linarith)

 theorem offset_open_region_subset
    {I : Type*} (H : ℂ ≃ₜ ℂ) (c : I → ℂ) (r : I → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    jordanInterior H \ ⋃ i, closedBall (c i) (r i + ρ) ⊆
      jordanInterior H \ ⋃ i, closedBall (c i) (r i) := by
  intro z hz
  refine ⟨hz.1, ?_⟩
  rintro hm
  obtain ⟨i, hi⟩ := mem_iUnion.mp hm
  exact hz.2 (mem_iUnion.mpr ⟨i, closedBall_subset_closedBall (by linarith) hi⟩)

 theorem circle_energy_mono {S T : Set ℂ} (hST : S ⊆ T)
    (u : ℂ → UnitAddCircle) (hE : MemLp (circleFDeriv u) 2 (volume.restrict T)) :
    Real.sqrt (∫ z in S, ‖circleFDeriv u z‖ ^ 2) ≤
      Real.sqrt (∫ z in T, ‖circleFDeriv u z‖ ^ 2) := by
  apply Real.sqrt_le_sqrt
  exact setIntegral_mono_set (hE.integrable_norm_pow (p := 2) (by norm_num))
    (Eventually.of_forall fun _ => sq_nonneg _)
    (Eventually.of_forall fun _ hz => hST hz)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JordanFillLimits
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Upper containment for limits of Jordan fills

Uniform convergence of boundary parametrizations traps the approximating
closed fills in every neighborhood of the limiting closed fill. The proof
uses Jordan nesting and radial enlargement.
-/

open Set Filter Function Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem eventually_jordan_fill_subset_open
    (H : ℂ ≃ₜ ℂ) (J : ℕ → ℂ ≃ₜ ℂ)
    (γ : Circle → ℂ) (γn : ℕ → Circle → ℂ)
    (hγ : Continuous γ) (hfront : range γ = frontier (jordanInterior H))
    (hfrontn : ∀ᶠ n in atTop, range (γn n) = frontier (jordanInterior (J n)))
    (hlim : TendstoUniformly γn γ atTop)
    {O : Set ℂ} (hO : IsOpen O) (hHO : closure (jordanInterior H) ⊆ O) :
    ∀ᶠ n in atTop, closure (jordanInterior (J n)) ⊆ O := by
  obtain ⟨r, hr, hrO, _⟩ := exists_disjoint_jordan_enlargements
    (fun _ : Unit => H) (by intro i j hij; exact (hij (Subsingleton.elim _ _)).elim)
    (fun _ => O) (fun _ => hO) (fun _ => hHO)
  let K := dilatedJordan H (r Unit.unit) (by linarith [hr Unit.unit])
  have hK : jordanInterior K = H '' ball (0 : ℂ) (r Unit.unit) :=
    jordanInterior_dilated H _
  have hγK : range γ ⊆ jordanInterior K := by
    rw [hfront, frontier_jordanInterior, hK]
    apply image_mono
    intro z hz
    simpa only [mem_ball, mem_sphere, dist_zero_right] using
      (show ‖z‖ < r Unit.unit by
        have hz' : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
        linarith [hr Unit.unit])
  obtain ⟨δ, hδ, hδK⟩ := (isCompact_range hγ).exists_thickening_subset_open
    (jordanInterior_isOpen K) hγK
  have hclose := Metric.tendstoUniformly_iff.mp hlim δ hδ
  filter_upwards [hclose, hfrontn] with n hn hnfront
  apply (closed_jordanInterior_subset_of_frontier_subset (J n) K ?_).trans
    (show jordanInterior K ⊆ O by
      rw [hK]
      exact (image_mono ball_subset_closedBall).trans (hrO Unit.unit))
  rw [← hnfront]
  rintro _ ⟨t, rfl⟩
  apply hδK
  apply mem_thickening_iff.mpr
  exact ⟨γ t, mem_range_self t, by simpa only [dist_comm] using hn t⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothJordanNeighborhoods
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite smooth Jordan neighborhoods

The contour construction in Section 1 of the Koebe manuscript is derived
from the smooth cutoff and regular level, scalar Sard, compact
one-manifold classification, and planar Schoenflies. Outer selection and containment
give the finite family of Jordan neighborhoods.
-/

open Set Filter Function
open scoped Topology ContDiff Manifold

namespace CircleDomainRigidity

/-- Actual finite smooth Jordan disks covering a chosen compact part of an
obstacle, with disjoint closures contained in the prescribed physical open
set. Its complement is required connected and unbounded precisely for the
hole-filling containment argument. -/
theorem exists_finite_smooth_jordan_cover
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {A F V : Set ℂ} (hA : IsCompact A) (hAF : A ⊆ F)
    (hFA : IsClosed (F \ A)) (hV : IsOpen V) (hAV : A ⊆ V)
    (hVconn : IsPreconnected Vᶜ) (hVunbounded : ¬ Bornology.IsBounded Vᶜ) :
    ∃ (f : ℂ → ℝ) (t : ℝ)
      (γ : ConnectedComponents {z // f z = t} → Circle → ℂ)
      (H : ConnectedComponents {z // f z = t} → ℂ ≃ₜ ℂ)
      (s : Set (ConnectedComponents {z // f z = t})),
      s.Finite ∧ A ⊆ ⋃ i ∈ s, jordanInterior (H i) ∧
      s.Pairwise (fun i j => Disjoint (closure (jordanInterior (H i)))
        (closure (jordanInterior (H j)))) ∧
      (∀ i ∈ s, closure (jordanInterior (H i)) ⊆ V) ∧
      ∀ i ∈ s, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ i) ∧
        Topology.IsEmbedding (γ i) ∧
        frontier (jordanInterior (H i)) = range (γ i) ∧
        Disjoint (frontier (jordanInterior (H i))) F := by
  classical
  obtain ⟨f, t, hf, ht, hU, hAU, hUc, hUV, _, hlevel, hregular, havoid, _⟩ :=
    exists_regular_superlevel_isolating_obstacle hsard hA hAF hFA hV hAV
  obtain ⟨hfinite, γ, hγ, hγdisj, hγcover⟩ :=
    compact_regular_level_circle_contours hf hregular hlevel
  let : Finite (ConnectedComponents {z // f z = t}) := hfinite
  choose H hH using fun i => hschoenflies (γ i) (hγ i).2.continuous (hγ i).2.injective
  have hfront (i) : frontier (jordanInterior (H i)) = range (γ i) :=
    frontier_jordanInterior_eq_circle_range (H i) (γ i) (hH i)
  have hUd : frontier {z | t < f z} = {z | f z = t} :=
    frontier_superlevel_eq_regular_level hf.continuous hregular
  have hfrontlevel (i) : frontier (jordanInterior (H i)) ⊆ {z | f z = t} := by
    rw [hfront, ← hγcover]
    exact subset_iUnion (fun i => range (γ i)) i
  have hpair : Pairwise (fun i j => Disjoint (frontier (jordanInterior (H i)))
      (frontier (jordanInterior (H j)))) := by
    intro i j hij
    simpa only [hfront] using hγdisj hij
  obtain ⟨s, hs, hsd, hdom, _⟩ := exists_outer_jordanInteriors H hpair
  let : Finite s := hs.to_subtype
  have hsd' : Pairwise (Disjoint on fun i : s => closure (jordanInterior (H i))) := by
    intro i j hij
    exact hsd i.property j.property (fun h => hij (Subtype.ext h))
  have hcover : frontier {z | t < f z} ⊆ ⋃ i : s, closure (jordanInterior (H i)) := by
    intro z hz
    rw [hUd, ← hγcover] at hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    have hi' : z ∈ closure (jordanInterior (H i)) := by
      apply frontier_subset_closure
      simpa only [hfront] using hi
    obtain ⟨j, hj, hij⟩ := hdom i
    exact mem_iUnion.mpr ⟨⟨j, hj⟩, hij hi'⟩
  have hUcover : {z | t < f z} ⊆ ⋃ i : s, jordanInterior (H i) :=
    open_subset_finite_jordanInteriors_of_frontier_subset (fun i : s => H i) hsd'
      hU (hUc.isBounded.subset subset_closure) hcover
      (fun i => hUd.symm ▸ hfrontlevel i)
  refine ⟨f, t, γ, H, s, hs, ?_, hsd, ?_, ?_⟩
  · intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hUcover (hAU hz))
    exact mem_iUnion₂.mpr ⟨i, i.property, hi⟩
  · intro i _
    apply closed_jordanInterior_subset_of_unbounded_connected_compl (H i) hVconn hVunbounded
    intro z hz
    apply hUV
    apply frontier_subset_closure
    rw [hUd]
    exact hfrontlevel i hz
  · intro i _
    exact ⟨(hγ i).1, (hγ i).2, hfront i, havoid.mono_left (hfrontlevel i)⟩

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_FiniteUniformization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The published finite circle-uniformization input

Conway, *Functions of One Complex Variable II*, GTM 159 (1995),
Theorem 15.7.9, p. 106, gives circle uniformization of nondegenerate
finitely connected regions. `FiniteCircleUniformization` records only
its existence conclusion on the sphere, omitting normalization and
uniqueness. It is an explicit proposition parameter, not an axiom.

The complement components of a finite family of disjoint closed
connected sets are identified below. This checks the finiteness and
nondegeneracy hypotheses for completed surfaces, also after an arbitrary
sphere homeomorphism such as compact metric uniformization.
-/

open Set Function
open scoped Topology OnePoint

noncomputable section

namespace CircleDomainRigidity

theorem connectedComponentIn_finite_disjoint_closed
    {X I : Type*} [TopologicalSpace X] [Finite I]
    (C : I → Set X) (hC : ∀ i, IsClosed (C i))
    (hconn : ∀ i, IsPreconnected (C i)) (hdisj : Pairwise (Disjoint on C))
    {i : I} {p : X} (hp : p ∈ C i) :
    connectedComponentIn (⋃ j, C j) p = C i := by
  classical
  let R : Set X := ⋃ j : {j : I // j ≠ i}, C j
  have hR : IsClosed R := isClosed_iUnion_of_finite (fun j => hC j)
  have hCR : Disjoint (C i) R := by
    apply Set.disjoint_left.mpr
    intro x hx hxR
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxR
    exact Set.disjoint_left.mp (hdisj j.property.symm) hx hj
  have hcover : (⋃ j, C j) ⊆ C i ∪ R := by
    intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hj)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)
  have hsub : connectedComponentIn (⋃ j, C j) p ⊆ C i := by
    have hs := isPreconnected_iff_subset_of_disjoint_closed.mp
      (isPreconnected_connectedComponentIn (F := ⋃ j, C j) (x := p))
      (C i) R (hC i) hR ((connectedComponentIn_subset _ _).trans hcover)
      (by rw [hCR.inter_eq, inter_empty])
    rcases hs with h | h
    · exact h
    · exact fun x hx => (Set.disjoint_left.mp hCR hp
        (h (mem_connectedComponentIn (mem_iUnion.mpr ⟨i, hp⟩)))).elim
  exact hsub.antisymm ((hconn i).subset_connectedComponentIn hp (subset_iUnion C i))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_FiniteCompletionUniformization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite uniformization of the actual terminal-disk complement

The complementary components are exactly the closed physical terminal
caps. In particular they are finite and nondegenerate. The published
finite circle theorem therefore applies after compact metric
uniformization; the resulting map is conformal on the retained core.
-/

open Set Function Filter
open scoped Topology OnePoint

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem isConnected_openCompletedRegion {I : Type*} [Finite I] (H : I → ℂ ≃ₜ ℂ)
    (hdisj : Pairwise (Disjoint on fun i => closure (jordanInterior (H i)))) :
    IsConnected (openCompletedRegion H) := by
  let S : Set ℂ := (⋃ i, closure (jordanInterior (H i)))ᶜ
  have hS : IsPreconnected S := isPreconnected_exterior_finite_jordanInteriors H hdisj
  have hinf : (∞ : Sphere) ∈ closure (((↑) : ℂ → Sphere) '' S) := by
    have hmem : ∀ᶠ z : ℂ in coclosedCompact ℂ, z ∈ S := by
      rw [coclosedCompact_eq_cocompact]
      exact (isCompact_iUnion fun i => isCompact_closure_jordanInterior (H i)).compl_mem_cocompact
    exact mem_closure_of_tendsto OnePoint.tendsto_coe_infty
      (hmem.mono fun z hz => ⟨z, hz, rfl⟩)
  have hsub : ((↑) : ℂ → Sphere) '' S ⊆ openCompletedRegion H := by
    rintro _ ⟨z, hz, rfl⟩ hb
    obtain ⟨i, x, hx, heq⟩ := mem_iUnion.mp hb
    have hxz : x = z := OnePoint.coe_injective heq
    exact hz (mem_iUnion.mpr ⟨i, hxz ▸ hx⟩)
  have hupper : openCompletedRegion H ⊆ closure (((↑) : ℂ → Sphere) '' S) := by
    intro p hp
    cases p using OnePoint.rec with
    | infty => exact hinf
    | coe z =>
      apply subset_closure
      refine ⟨z, ?_, rfl⟩
      intro hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      exact hp (mem_iUnion.mpr ⟨i, z, hi, rfl⟩)
  refine ⟨⟨∞, ?_⟩, (hS.image _ OnePoint.continuous_coe.continuousOn).subset_closure hsub hupper⟩
  intro hb
  obtain ⟨i, z, _, heq⟩ := mem_iUnion.mp hb
  exact OnePoint.coe_ne_infty z heq

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CovectorMetric
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Metric selection for local covectors

Periodic coordinates need not have a global scalar potential. The Gram
argument applies to their smooth covector fields, retaining the spherical
metric near a closed core and near infinity, and realizing masked fields
by smooth extensions.
-/

open Set Filter MeasureTheory Finset Metric
open scoped Topology ContDiff Manifold Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem continuousOn_fieldEnergy
    {Ω : Set (ℝ × ℝ)} {v : (ℝ × ℝ) → ℝ × ℝ} (hv : ContinuousOn v Ω)
    {g : (ℝ × ℝ) → PlanarMetric} (hg : Continuous g) (hPD : ∀ z, (g z).PosDef) :
    ContinuousOn (fieldEnergy v g) Ω := by
  have hw : ContinuousOn (fun z => ![(v z).1, (v z).2]) Ω := by
    apply continuousOn_pi.mpr
    intro i
    fin_cases i
    · exact hv.fst
    · exact hv.snd
  have hA : ContinuousOn (fun z => Matrix.vecMulVec ![(v z).1, (v z).2]
      ![(v z).1, (v z).2]) Ω := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact (continuousOn_pi.mp hw i).mul (continuousOn_pi.mp hw j)
  change ContinuousOn (fun z => covectorEnergy ![(v z).1, (v z).2] (g z)) Ω
  simpa only [covectorEnergy_eq_matrixEnergy] using
    continuousOn_matrixEnergy_local hA hg.continuousOn (fun z _ => hPD z)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CircleEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Localized energy for periodic differentials

Agreement of circle maps near the retained core implies agreement of
their intrinsic differentials. Original L² energy controls the entire
unbounded core; smoothness on a compact tail controls the remainder.
-/

open Set Filter MeasureTheory Finset
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem fieldEnergy_spherical (v : (ℝ × ℝ) → ℝ × ℝ) (z : ℝ × ℝ) :
    fieldEnergy v (fun z => sphericalMetricFactor z • 1) z = (v z).1 ^ 2 + (v z).2 ^ 2 := by
  unfold fieldEnergy
  rw [covectorEnergy_eq_matrixEnergy,
    matrixEnergy_pos_smul _ Matrix.PosDef.one (sphericalMetricFactor_pos z),
    ← covectorEnergy_eq_matrixEnergy, covectorEnergy_identity]

theorem integrable_fieldEnergy_spherical_of_memLp
    {μ : Measure (ℝ × ℝ)} {v : (ℝ × ℝ) → ℝ × ℝ} (hv : MemLp v 2 μ) :
    Integrable (fieldEnergy v (fun z => sphericalMetricFactor z • 1)) μ := by
  have hx := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp_memLp' hv
  have hy := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp_memLp' hv
  have hxx : MemLp (fun z => (v z).1 * (v z).1) 1 μ := hx.mul hx
  have hyy : MemLp (fun z => (v z).2 * (v z).2) 1 μ := hy.mul hy
  have hi := (memLp_one_iff_integrable.mp hxx).add (memLp_one_iff_integrable.mp hyy)
  exact hi.congr (Eventually.of_forall fun z => by
    simpa only [pow_two, Pi.add_apply] using (fieldEnergy_spherical v z).symm)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_NormalizedLimitEquivalence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The normalized limit as a sphere conformal equivalence

The source includes infinity. The inverse on the image is constructed
by the local inverse theorem, so the limiting map satisfies the same
two-sided conformal predicate as the final circle-domain target.
-/

open Set Filter Function Asymptotics Bornology
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem isOpen_finite_domain_with_infty
    {D : Set ℂ} (hD : IsOpen D) {R : ℝ}
    (hext : {z : ℂ | R ≤ ‖z‖} ⊆ D) :
    IsOpen (((↑) : ℂ → Sphere) '' D ∪ {OnePoint.infty}) := by
  have hc : IsCompact Dᶜ := by
    apply (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset hD.isClosed_compl
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hn
    exact hz (hext (le_of_lt (lt_of_not_ge hn)))
  apply (OnePoint.isOpen_iff_of_mem' (by simp)).mpr
  simpa only [preimage_union, OnePoint.coe_injective.preimage_image,
    OnePoint.coe_preimage_infty, union_empty] using And.intro hc hD

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ConnectedCoreExhaustion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Connected retained-core exhaustions

Compact exhaustion and paths in an open plane domain give nested connected
open cores with compact closure in that domain. Adjoining one fixed exterior
then gives the cofinite cores required by normalized model compactness.
-/

open Set Filter Function Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem exists_connected_plane_exhaustion
    {G : Set ℂ} (hG : IsOpen G) (hconn : IsConnected G)
    {z₀ : ℂ} (hz₀ : z₀ ∈ G) :
    ∃ U : ℕ → Set ℂ,
      (∀ n, IsOpen (U n)) ∧ (∀ n, IsConnected (U n)) ∧ Monotone U ∧
      (∀ n, IsCompact (closure (U n)) ∧ closure (U n) ⊆ G) ∧
      (⋃ n, U n) = G ∧ z₀ ∈ U 0 := by
  let : LocallyCompactSpace G := hG.locallyCompactSpace
  let : LocallyPathConnectedSpace G := hG.locallyPathConnectedSpace
  let C := CompactExhaustion.choice G
  let x₀ : G := ⟨z₀, hz₀⟩
  obtain ⟨k₀, hk₀⟩ := C.exists_mem x₀
  let A : ℕ → Set G := fun n => connectedComponentIn (interior (C (n + k₀ + 1))) x₀
  have hxA (n : ℕ) : x₀ ∈ A n := by
    apply mem_connectedComponentIn
    apply C.subset_interior (by omega : k₀ < n + k₀ + 1)
    exact hk₀
  have hAo (n : ℕ) : IsOpen (A n) := isOpen_interior.connectedComponentIn
  have hAc (n : ℕ) : IsConnected (A n) :=
    ⟨⟨x₀, hxA n⟩, isPreconnected_connectedComponentIn⟩
  have hAm : Monotone A := by
    intro m n hmn
    exact connectedComponentIn_mono _ (interior_mono (C.subset (by omega)))
  let U : ℕ → Set ℂ := fun n => Subtype.val '' A n
  have hUclosed (n : ℕ) : closure (U n) ⊆ Subtype.val '' C (n + k₀ + 1) := by
    apply closure_minimal _ ((C.isCompact _).image continuous_subtype_val).isClosed
    exact image_mono ((connectedComponentIn_subset _ _).trans interior_subset)
  refine ⟨U, fun n => hG.isOpenMap_subtype_val _ (hAo n),
    fun n => (hAc n).image _ continuous_subtype_val.continuousOn,
    fun m n hmn => image_mono (hAm hmn), ?_, ?_, ⟨x₀, hxA 0, rfl⟩⟩
  · intro n
    exact ⟨((C.isCompact _).image continuous_subtype_val).of_isClosed_subset
      isClosed_closure (hUclosed n), (hUclosed n).trans (by rintro _ ⟨x, _, rfl⟩; exact x.property)⟩
  · apply Subset.antisymm
    · exact iUnion_subset fun n => by rintro _ ⟨x, _, rfl⟩; exact x.property
    · intro z hz
      let x : G := ⟨z, hz⟩
      have hj : Joined x₀ x := (hG.isConnected_iff_isPathConnected.mp hconn).joinedIn
        z₀ hz₀ z hz |>.joined_subtype
      let γ := hj.somePath
      obtain ⟨k, hk⟩ := C.exists_superset_of_isCompact (isCompact_range γ.continuous)
      have hrange : range γ ⊆ interior (C (k + k₀ + 1)) :=
        hk.trans (C.subset_interior (by omega : k < k + k₀ + 1))
      have hx : x ∈ A k :=
        (isConnected_range γ.continuous).isPreconnected.subset_connectedComponentIn
          (by exact ⟨0, γ.source⟩) hrange (by exact ⟨1, γ.target⟩)
      exact mem_iUnion.mpr ⟨k, x, hx, rfl⟩

/-- The cofinite cores retain a full fixed exterior, while the closure
of every core stays in the original domain. -/
theorem exists_cofinite_connected_plane_exhaustion
    {G : Set ℂ} (hG : IsOpen G) (hconn : IsConnected G)
    {R : ℝ} (hR : 0 < R) (hext : {z : ℂ | R ≤ ‖z‖} ⊆ G) :
    ∃ D : ℕ → Set ℂ,
      (∀ n, IsOpen (D n)) ∧ (∀ n, IsConnected (D n)) ∧ Monotone D ∧
      (∀ n, closure (D n) ⊆ G) ∧ (⋃ n, D n) = G ∧
      {z : ℂ | 2 * R ≤ ‖z‖} ⊆ D 0 := by
  let z₀ : ℂ := (2 * R : ℝ)
  have hnorm : ‖z₀‖ = 2 * R := by
    simp only [z₀, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * R)]
  have hz₀ : z₀ ∈ G := hext (by change R ≤ ‖z₀‖; rw [hnorm]; linarith)
  obtain ⟨U, hUo, hUc, hUm, hUcl, hUunion, hbase⟩ :=
    exists_connected_plane_exhaustion hG hconn hz₀
  let E : Set ℂ := (closedBall (0 : ℂ) R)ᶜ
  have hEo : IsOpen E := isClosed_closedBall.isOpen_compl
  have hEc : IsConnected E := isConnected_complex_exterior_closedBall hR.le
  have hzE : z₀ ∈ E := by
    simpa only [E, mem_compl_iff, mem_closedBall, dist_zero_right, not_le, hnorm] using
      (by linarith : R < 2 * R)
  have hEcl : closure E ⊆ G := by
    rw [closure_compl, interior_closedBall (0 : ℂ) hR.ne']
    intro z hz
    apply hext
    change R ≤ ‖z‖
    simpa only [mem_compl_iff, mem_ball, dist_zero_right, not_lt] using hz
  refine ⟨fun n => U n ∪ E, fun n => (hUo n).union hEo,
    fun n => (hUc n).union ⟨z₀, hUm (Nat.zero_le n) hbase, hzE⟩ hEc,
    fun m n hmn => union_subset_union_left E (hUm hmn), ?_, ?_, ?_⟩
  · intro n
    rw [closure_union]
    exact union_subset (hUcl n).2 hEcl
  · ext z
    simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨n, hz | hz⟩
      · exact (hUcl n).2 (subset_closure hz)
      · exact hEcl (subset_closure hz)
    · intro hz
      obtain ⟨n, hn⟩ := mem_iUnion.mp (hUunion.symm ▸ hz)
      exact ⟨n, Or.inl hn⟩
  · intro z hz
    right
    have hz' : 2 * R ≤ ‖z‖ := hz
    change z ∉ closedBall (0 : ℂ) R
    rw [mem_closedBall, dist_zero_right, not_le]
    linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SphereCoreExhaustion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual source cores for domains containing infinity

The open connected cores exhaust the given domain. Their finite closures,
with infinity added, are compact subsets of the domain and can therefore
be prescribed in the finite-transfer construction.
-/

open Set Filter Function Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem isClosed_finite_set_with_infty {C : Set ℂ} (hC : IsClosed C) :
    IsClosed (((↑) : ℂ → Sphere) '' C ∪ {OnePoint.infty}) := by
  have he : (((↑) : ℂ → Sphere) '' C ∪ {OnePoint.infty})ᶜ =
      ((↑) : ℂ → Sphere) '' Cᶜ := by
    ext p
    cases p using OnePoint.rec with
    | infty => simp
    | coe z => simp only [mem_compl_iff, mem_union, OnePoint.coe_injective.mem_set_image,
        mem_singleton_iff, OnePoint.coe_ne_infty, or_false]
  rw [← isOpen_compl_iff, he]
  exact OnePoint.isOpen_image_coe.mpr hC.isOpen_compl

theorem exists_sphere_connected_core_exhaustion
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) :
    ∃ (R : ℝ) (D : ℕ → Set ℂ) (K : ℕ → Set Sphere),
      0 < R ∧ (∀ n, IsOpen (D n)) ∧ (∀ n, IsConnected (D n)) ∧ Monotone D ∧
      (∀ n, K n = ((↑) : ℂ → Sphere) '' closure (D n) ∪ {OnePoint.infty}) ∧
      (∀ n, IsCompact (K n) ∧ K n ⊆ G) ∧
      (∀ n, ((↑) : ℂ → Sphere) '' D n ∪ {OnePoint.infty} ⊆ interior (K n)) ∧
      (⋃ n, ((↑) : ℂ → Sphere) '' D n ∪ {OnePoint.infty}) = G ∧
      {z : ℂ | 2 * R ≤ ‖z‖} ⊆ D 0 ∧
      ((((↑) : ℂ → Sphere) '' ball 0 R)ᶜ) ⊆ G := by
  let A : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' G
  have hA : IsOpen A := hG.preimage OnePoint.continuous_coe
  have hAc : IsCompact Aᶜ := ((OnePoint.isOpen_iff_of_mem hinf).mp hG).2
  obtain ⟨R, hR, hbound⟩ := hAc.isBounded.exists_pos_norm_lt
  have hext : {z : ℂ | R ≤ ‖z‖} ⊆ A := by
    intro z hz
    by_contra hzA
    exact (not_lt_of_ge hz) (hbound z hzA)
  have hAn : A.Nonempty := by
    refine ⟨(R : ℂ), hext ?_⟩
    change R ≤ ‖(R : ℂ)‖
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, le_refl]
  have hconnA : IsConnected A := ⟨hAn,
    (finite_part_connected_unbounded hconn.isPreconnected (mem_interior_iff_mem_nhds.mpr (hG.mem_nhds hinf))).1⟩
  obtain ⟨D, hDo, hDc, hDm, hDcl, hDunion, hDexterior⟩ :=
    exists_cofinite_connected_plane_exhaustion hA hconnA hR hext
  let K : ℕ → Set Sphere := fun n => ((↑) : ℂ → Sphere) '' closure (D n) ∪ {OnePoint.infty}
  have hDG (n : ℕ) : ((↑) : ℂ → Sphere) '' D n ∪ {OnePoint.infty} ⊆ G := by
    rintro p (⟨z, hz, rfl⟩ | hp)
    · exact hDcl n (subset_closure hz)
    · exact mem_singleton_iff.mp hp ▸ hinf
  have hDE (n : ℕ) : {z : ℂ | 2 * R ≤ ‖z‖} ⊆ D n :=
    hDexterior.trans (hDm (Nat.zero_le n))
  refine ⟨R, D, K, hR, hDo, hDc, hDm, fun _ => rfl, ?_, ?_, ?_, hDexterior, ?_⟩
  · intro n
    refine ⟨(isClosed_finite_set_with_infty isClosed_closure).isCompact, ?_⟩
    rintro p (⟨z, hz, rfl⟩ | hp)
    · exact hDcl n hz
    · exact mem_singleton_iff.mp hp ▸ hinf
  · intro n
    apply interior_maximal ?_ (isOpen_finite_domain_with_infty (hDo n) (hDE n))
    exact union_subset_union_left _ (image_mono subset_closure)
  · apply Subset.antisymm (iUnion_subset hDG)
    intro p hp
    cases p using OnePoint.rec with
    | infty => exact mem_iUnion.mpr ⟨0, Or.inr rfl⟩
    | coe z =>
      have hz : z ∈ A := hp
      obtain ⟨n, hn⟩ := mem_iUnion.mp (hDunion.symm ▸ hz)
      exact mem_iUnion.mpr ⟨n, Or.inl ⟨z, hn, rfl⟩⟩
  · intro p hp
    cases p using OnePoint.rec with
    | infty => exact hinf
    | coe z =>
      apply hext
      change R ≤ ‖z‖
      simpa only [OnePoint.coe_injective.mem_set_image, mem_compl_iff, mem_ball,
        dist_zero_right, not_lt] using hp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ConnectedCoreNeighborhood
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compact connected neighborhoods inside the source

A compact subset of a domain containing infinity lies strictly inside a
compact connected subset of that domain which also contains a neighborhood
of infinity. This lets successive finite Jordan cores retain earlier ones.
-/

open Set Function Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem closure_finite_domain_with_infty (D : Set ℂ) :
    closure (((↑) : ℂ → Sphere) '' D ∪ {OnePoint.infty}) =
      ((↑) : ℂ → Sphere) '' closure D ∪ {OnePoint.infty} := by
  apply Subset.antisymm
  · exact closure_minimal (union_subset_union_left _ (image_mono subset_closure))
      (isClosed_finite_set_with_infty isClosed_closure)
  · apply union_subset
    · exact (image_closure_subset_closure_image OnePoint.continuous_coe).trans
        (closure_mono subset_union_left)
    · exact subset_union_right.trans subset_closure

theorem isConnected_finite_domain_with_infty
    {D : Set ℂ} (hD : IsConnected D) {R : ℝ}
    (hext : {z : ℂ | R ≤ ‖z‖} ⊆ D) :
    IsConnected (((↑) : ℂ → Sphere) '' D ∪ {OnePoint.infty}) := by
  have hunbounded : ¬ Bornology.IsBounded D := by
    intro h
    have hc := (isBounded_closedBall (x := (0 : ℂ)) (r := R)).union h
    apply NormedSpace.unbounded_univ ℝ ℂ
    apply hc.subset
    intro z _
    by_cases hz : ‖z‖ ≤ R
    · exact Or.inl (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)
    · exact Or.inr (hext (le_of_lt (lt_of_not_ge hz)))
  have hinf := infty_mem_closure_image_of_unbounded hunbounded
  apply (hD.image _ OnePoint.continuous_coe.continuousOn).subset_closure subset_union_left
  exact union_subset subset_closure (singleton_subset_iff.mpr hinf)

theorem exists_compact_connected_core_neighborhood
    {G S : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hS : IsCompact S) (hSG : S ⊆ G) :
    ∃ P : Set Sphere, IsCompact P ∧ IsConnected P ∧ P ⊆ G ∧
      S ⊆ interior P ∧ OnePoint.infty ∈ interior P := by
  obtain ⟨R, D, K, hR, hDo, hDc, hDm, hKdef, hK, hDK, hcover, hext, _⟩ :=
    exists_sphere_connected_core_exhaustion hG hconn hinf
  let U : ℕ → Set Sphere := fun n => ((↑) : ℂ → Sphere) '' D n ∪ {OnePoint.infty}
  have hUo (n : ℕ) : IsOpen (U n) :=
    isOpen_finite_domain_with_infty (hDo n) (hext.trans (hDm (Nat.zero_le n)))
  have hUm : Monotone U := fun _ _ h => union_subset_union_left _ (image_mono (hDm h))
  obtain ⟨n, hn⟩ := hS.elim_directed_cover U hUo
    (fun p hp => hcover.symm ▸ hSG hp) hUm.directed_le
  refine ⟨K n, (hK n).1, ?_, (hK n).2, hn.trans (hDK n), hDK n (Or.inr rfl)⟩
  rw [hKdef n, ← closure_finite_domain_with_infty]
  exact (isConnected_finite_domain_with_infty (hDc n)
    (hext.trans (hDm (Nat.zero_le n)))).closure

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ClosedJordanCore
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Closed cores bounded by a finite disjoint Jordan family

The closed common exterior is regular closed, its interior is the already
constructed connected open completed region, and its boundary is exactly
the union of the specified Jordan curves.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem interior_finite_disjoint_closed
    {I : Type*} [Finite I] (C : I → Set Sphere)
    (hC : ∀ i, IsClosed (C i)) (hd : Pairwise (Disjoint on C)) :
    interior (⋃ i, C i) = ⋃ i, interior (C i) := by
  classical
  apply Subset.antisymm
  · intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp (interior_subset hp)
    let B : Set Sphere := ⋃ j : {j : I // j ≠ i}, C j
    have hB : IsClosed B := isClosed_iUnion_of_finite fun j => hC j
    have hpB : p ∉ B := by
      intro h
      obtain ⟨j, hj⟩ := mem_iUnion.mp h
      exact Set.disjoint_left.mp (hd j.property.symm) hi hj
    have hsub : interior (⋃ j, C j) ∩ Bᶜ ⊆ C i := by
      rintro q ⟨hq, hqB⟩
      obtain ⟨j, hj⟩ := mem_iUnion.mp (interior_subset hq)
      by_cases hji : j = i
      · exact hji ▸ hj
      · exact (hqB (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)).elim
    exact mem_iUnion.mpr ⟨i, interior_maximal hsub (isOpen_interior.inter hB.isOpen_compl) ⟨hp, hpB⟩⟩
  · exact iUnion_subset fun i => interior_mono (subset_iUnion C i)

theorem closure_interior_closedJordanCore
    {I : Type*} [Finite I] (H : I → ℂ ≃ₜ ℂ)
    (hd : Pairwise (Disjoint on fun i => closure (jordanInterior (H i)))) :
    closure (interior (closedJordanCore H)) = closedJordanCore H := by
  rw [interior_closedJordanCore, openCompletedRegion, closure_compl,
    interior_finite_disjoint_closed (fun i => closedTerminalCap (H i))
      (fun i => (isCompact_closedTerminalCap (H i)).isClosed) (disjoint_closedTerminalCaps H hd)]
  simp only [interior_closedTerminalCap, closedJordanCore]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PrescribedJordanCore
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A finite smooth Jordan core retaining a prescribed connected set

Sard, compact one-manifold classification and Schoenflies produce disjoint
smooth filled contours around the complement. Their common exterior stays
in the original domain and retains the prescribed compact set in its interior.
-/

open Set Function
open scoped Topology Manifold ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem exists_prescribed_jordan_core
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {G P : Set Sphere} (hG : IsOpen G) (hP : IsCompact P) (hPG : P ⊆ G)
    (hconn : IsPreconnected P) (hinf : OnePoint.infty ∈ interior P) :
    ∃ (n : ℕ) (H : Fin n → ℂ ≃ₜ ℂ) (γ : Fin n → Circle → ℂ),
      Pairwise (Disjoint on fun i => closure (jordanInterior (H i))) ∧
      closedJordanCore H ⊆ G ∧ P ⊆ interior (closedJordanCore H) ∧
      (∀ i, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ i) ∧ Topology.IsEmbedding (γ i) ∧
        frontier (jordanInterior (H i)) = range (γ i)) := by
  let A : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' Gᶜ
  let V : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' Pᶜ
  have hinfG : OnePoint.infty ∈ G := hPG (interior_subset hinf)
  have hAc : IsCompact A := isCompact_finite_preimage hG.isClosed_compl
    (by simpa only [mem_compl_iff, not_not] using hinfG)
  have hVo : IsOpen V := hP.isClosed.isOpen_compl.preimage OnePoint.continuous_coe
  have hAV : A ⊆ V := preimage_mono (compl_subset_compl.mpr hPG)
  have hVc : IsPreconnected Vᶜ ∧ ¬ Bornology.IsBounded Vᶜ := by
    simpa only [V, ← preimage_compl, compl_compl] using
      finite_part_connected_unbounded hconn hinf
  obtain ⟨f, t, γ₀, H₀, s, hs, hcover, hdisj, hinside, hcurves⟩ :=
    exists_finite_smooth_jordan_cover hsard hschoenflies hAc (Subset.refl A)
      (by simp only [sdiff_self, isClosed_empty]) hVo hAV hVc.1 hVc.2
  let : Fintype s := hs.fintype
  let e : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  let H : Fin (Fintype.card s) → ℂ ≃ₜ ℂ := fun i => H₀ (e.symm i)
  let γ : Fin (Fintype.card s) → Circle → ℂ := fun i => γ₀ (e.symm i)
  have hd : Pairwise (Disjoint on fun i => closure (jordanInterior (H i))) := by
    intro i j hij
    exact hdisj (e.symm i).property (e.symm j).property
      (fun h => hij (e.symm.injective (Subtype.ext h)))
  have hcover' : A ⊆ ⋃ i, jordanInterior (H i) := by
    intro z hz
    obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp (hcover hz)
    refine mem_iUnion.mpr ⟨e ⟨j, hj⟩, ?_⟩
    simpa only [H, e.symm_apply_apply] using hzj
  have hinside' (i : Fin (Fintype.card s)) : closure (jordanInterior (H i)) ⊆ V :=
    hinside _ (e.symm i).property
  refine ⟨Fintype.card s, H, γ, hd, ?_, ?_, ?_⟩
  · intro p hp
    by_contra hpG
    cases p using OnePoint.rec with
    | infty => exact hpG hinfG
    | coe z =>
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover' hpG)
      exact hp (mem_iUnion.mpr ⟨i, z, hi, rfl⟩)
  · rw [interior_closedJordanCore]
    intro p hp hbad
    obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp hbad
    exact hinside' i hz hp
  · intro i
    obtain ⟨hsm, hemb, hfront, _⟩ := hcurves _ (e.symm i).property
    exact ⟨hsm, hemb, hfront⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothJordanExhaustion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A strict exhaustion by finite smooth Jordan cores

Every prescribed compact subset is retained in the interior of a finite
Jordan core. Recursive application retains the preceding core and the next
compact exhaustion set. The construction uses Sard, one-manifold
classification, and Schoenflies.
-/

open Set Function
open scoped Topology Manifold ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

namespace SmoothJordanCore

variable {G : Set Sphere} (C : SmoothJordanCore G)

theorem regular : closure (interior C.carrier) = C.carrier :=
  closure_interior_closedJordanCore C.disk C.disjoint

theorem connected_interior : IsConnected (interior C.carrier) := by
  rw [carrier, interior_closedJordanCore]
  exact isConnected_openCompletedRegion C.disk C.disjoint

theorem infty_interior : OnePoint.infty ∈ interior C.carrier := by
  rw [carrier, interior_closedJordanCore]
  intro h
  obtain ⟨i, z, _, hz⟩ := mem_iUnion.mp h
  exact OnePoint.coe_ne_infty z hz

end SmoothJordanCore

theorem exists_smooth_jordan_core_containing
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {G S : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hS : IsCompact S) (hSG : S ⊆ G) :
    ∃ C : SmoothJordanCore G, S ⊆ interior C.carrier := by
  obtain ⟨P, hPc, hPconn, hPG, hSP, hinfP⟩ :=
    exists_compact_connected_core_neighborhood hG hconn hinf hS hSG
  obtain ⟨n, H, γ, hd, hKG, hPK, hcurves⟩ :=
    exists_prescribed_jordan_core hsard hschoenflies hG hPc hPG hPconn.isPreconnected hinfP
  let C : SmoothJordanCore G := ⟨n, H, γ, hd, hKG,
    fun i => (hcurves i).1, fun i => (hcurves i).2.1, fun i => (hcurves i).2.2⟩
  exact ⟨C, (hSP.trans interior_subset).trans hPK⟩

theorem exists_smooth_jordan_exhaustion
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) :
    ∃ C : ℕ → SmoothJordanCore G,
      (∀ n, (C n).carrier ⊆ interior (C (n + 1)).carrier) ∧
      (⋃ n, interior (C n).carrier) = G := by
  classical
  obtain ⟨R, D, K, _, _, _, _, _, hK, hDK, hcover, _, _⟩ :=
    exists_sphere_connected_core_exhaustion hG hconn hinf
  have hex (S : Set Sphere) (hS : IsCompact S) (hSG : S ⊆ G) :=
    exists_smooth_jordan_core_containing hsard hschoenflies hG hconn hinf hS hSG
  let initial : SmoothJordanCore G := Classical.choose (hex (K 0) (hK 0).1 (hK 0).2)
  have hinitial : K 0 ⊆ interior initial.carrier :=
    Classical.choose_spec (hex (K 0) (hK 0).1 (hK 0).2)
  let next (n : ℕ) (C : SmoothJordanCore G) : SmoothJordanCore G :=
    Classical.choose (hex (C.carrier ∪ K (n + 1))
      (C.isCompact.union (hK (n + 1)).1) (union_subset C.subset (hK (n + 1)).2))
  have hnext (n : ℕ) (C : SmoothJordanCore G) :
      C.carrier ∪ K (n + 1) ⊆ interior (next n C).carrier :=
    Classical.choose_spec (hex (C.carrier ∪ K (n + 1))
      (C.isCompact.union (hK (n + 1)).1) (union_subset C.subset (hK (n + 1)).2))
  let C : ℕ → SmoothJordanCore G := fun n => Nat.rec initial next n
  have hstep (n : ℕ) : C (n + 1) = next n (C n) := rfl
  have hretain (n : ℕ) : K n ⊆ interior (C n).carrier := by
    cases n with
    | zero => exact hinitial
    | succ n => exact subset_union_right.trans (hnext n (C n))
  refine ⟨C, fun n => subset_union_left.trans (hnext n (C n)), ?_⟩
  apply Subset.antisymm
  · exact iUnion_subset fun n => interior_subset.trans (C n).subset
  · intro p hp
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hcover.symm ▸ hp)
    exact mem_iUnion.mpr ⟨n, hretain n (interior_subset (hDK n hn))⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ImageCoreBoundary
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Images of compact retained cores

A conformal injection on an open neighborhood carries a compact core's
interior and boundary to the interior and boundary of its image. Regular
closed cores remain regular closed. These facts use local openness, not a
boundary extension of the conformal map.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem frontier_image_of_continuous_open
    {f : Sphere → Sphere} {G K : Set Sphere}
    (hc : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S))
    (hG : IsOpen G) (hi : InjOn f G) (hK : IsCompact K) (hKG : K ⊆ G) :
    frontier (f '' K) = f '' frontier K := by
  have hfc : IsClosed (f '' K) := (hK.image_of_continuousOn (hc.mono hKG)).isClosed
  rw [frontier, hfc.closure_eq, interior_image_of_continuous_open hc ho hG hi hKG,
    frontier, hK.isClosed.closure_eq]
  exact ((hi.mono hKG).image_sdiff_subset interior_subset).symm

theorem closure_image_interior_of_continuous
    {f : Sphere → Sphere} {G K : Set Sphere}
    (hf : ContinuousOn f G) (hK : IsCompact K) (hKG : K ⊆ G)
    (hregular : closure (interior K) = K) :
    closure (f '' interior K) = f '' K := by
  have hc : ContinuousOn f K := hf.mono hKG
  apply Subset.antisymm
  · exact closure_minimal (image_mono interior_subset) (hK.image_of_continuousOn hc).isClosed
  · have hci : ContinuousOn f (closure (interior K)) := hregular.symm ▸ hc
    simpa only [hregular] using hci.image_closure

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JordanCoreRecognition
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Recognizing the exterior bounded by a finite Jordan family

A regular closed sphere set with connected interior containing infinity
and with finitely many disjoint Jordan boundary curves is exactly their
common closed exterior. The filled disks are disjoint. This supplies the
image-side identification of retained cores without assuming orientation
or a boundary extension theorem.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem unbounded_preconnected_subset_jordan_exterior
    {T : Set ℂ} (hT : IsPreconnected T) (hunbounded : ¬ Bornology.IsBounded T)
    (H : ℂ ≃ₜ ℂ) (havoid : Disjoint T (frontier (jordanInterior H))) :
    T ⊆ (closure (jordanInterior H))ᶜ := by
  have hsplit : T ⊆ jordanInterior H ∨ T ⊆ (closure (jordanInterior H))ᶜ := by
    apply hT.subset_or_subset (jordanInterior_isOpen H) isClosed_closure.isOpen_compl
    · exact Set.disjoint_left.mpr fun _ hx hy => hy (subset_closure hx)
    · intro z hz
      by_cases hi : z ∈ jordanInterior H
      · exact Or.inl hi
      · right
        intro hc
        exact Set.disjoint_left.mp havoid hz (by
          rw [(jordanInterior_isOpen H).frontier_eq]
          exact ⟨hc, hi⟩)
  rcases hsplit with h | h
  · exact (hunbounded ((isCompact_closure_jordanInterior H).isBounded.subset
      (h.trans subset_closure))).elim
  · exact h

theorem sphere_jordan_core_recognition
    {I : Type*} [Finite I] {A : Set Sphere}
    (hregular : closure (interior A) = A)
    (hconn : IsPreconnected (interior A)) (hinf : OnePoint.infty ∈ interior A)
    (H : I → ℂ ≃ₜ ℂ)
    (hpair : Pairwise (fun i j => Disjoint (frontier (jordanInterior (H i)))
      (frontier (jordanInterior (H j)))))
    (hfront : frontier A = ⋃ i, ((↑) : ℂ → Sphere) '' frontier (jordanInterior (H i))) :
    Pairwise (Disjoint on fun i => closure (jordanInterior (H i))) ∧
      Aᶜ = ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (H i) := by
  have hAclosed : IsClosed A := hregular ▸ isClosed_closure
  let T : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' interior A
  have hT := finite_part_connected_unbounded hconn (by
    simpa only [interior_interior] using hinf)
  have hfrontA (i : I) : ((↑) : ℂ → Sphere) '' frontier (jordanInterior (H i)) ⊆ frontier A := by
    rw [hfront]
    exact subset_iUnion (fun j : I => ((↑) : ℂ → Sphere) '' frontier (jordanInterior (H j))) i
  have hTout (i : I) : T ⊆ (closure (jordanInterior (H i)))ᶜ := by
    apply unbounded_preconnected_subset_jordan_exterior hT.1 hT.2 (H i)
    apply Set.disjoint_left.mpr
    intro z hz hzfront
    have hzf := hfrontA i (mem_image_of_mem _ hzfront)
    exact hzf.2 hz
  have hAout (i : I) : A ⊆ (((↑) : ℂ → Sphere) '' jordanInterior (H i))ᶜ := by
    rw [← hregular]
    apply closure_minimal ?_ (OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen (H i))).isClosed_compl
    intro p hp hinside
    obtain ⟨z, hz, rfl⟩ := hinside
    exact hTout i hp (subset_closure hz)
  have hd : Pairwise (Disjoint on fun i => closure (jordanInterior (H i))) := by
    intro i j hij
    rcases disjoint_or_nested_jordanInteriors (H i) (H j) (hpair hij) with hd | hn | hn
    · exact hd
    · obtain ⟨z, hz⟩ := (isConnected_frontier_jordanInterior (H i)).nonempty
      have hzA : (z : Sphere) ∈ A := by
        simpa only [hAclosed.closure_eq] using frontier_subset_closure
          (hfrontA i (mem_image_of_mem _ hz))
      exact (hAout j hzA (mem_image_of_mem _ (hn (frontier_subset_closure hz)))).elim
    · obtain ⟨z, hz⟩ := (isConnected_frontier_jordanInterior (H j)).nonempty
      have hzA : (z : Sphere) ∈ A := by
        simpa only [hAclosed.closure_eq] using frontier_subset_closure
          (hfrontA j (mem_image_of_mem _ hz))
      exact (hAout i hzA (mem_image_of_mem _ (hn (frontier_subset_closure hz)))).elim
  let U : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' Aᶜ
  have hUo : IsOpen U := hAclosed.isOpen_compl.preimage OnePoint.continuous_coe
  have hUb : Bornology.IsBounded U := by
    have hc := ((OnePoint.isOpen_iff_of_mem hinf).mp isOpen_interior).2
    apply hc.isBounded.subset
    intro z hz hzint
    exact hz (interior_subset hzint)
  have hprefront : frontier U = ((↑) : ℂ → Sphere) ⁻¹' frontier A := by
    change frontier (((↑) : ℂ → Sphere) ⁻¹' Aᶜ) = _
    rw [← OnePoint.isOpenEmbedding_coe.isOpenMap.preimage_frontier_eq_frontier_preimage
      OnePoint.continuous_coe, frontier_compl]
  have hcover : frontier U ⊆ ⋃ i, closure (jordanInterior (H i)) := by
    intro z hz
    rw [hprefront] at hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hfront ▸ hz)
    have hzi : z ∈ frontier (jordanInterior (H i)) := OnePoint.coe_injective.mem_set_image.mp hi
    exact mem_iUnion.mpr ⟨i, frontier_subset_closure hzi⟩
  have hselected (i : I) : frontier (jordanInterior (H i)) ⊆ frontier U := by
    intro z hz
    rw [hprefront]
    exact hfrontA i (mem_image_of_mem _ hz)
  have hUfill := open_subset_finite_jordanInteriors_of_frontier_subset H hd hUo hUb hcover hselected
  refine ⟨hd, Subset.antisymm ?_ ?_⟩
  · intro p hp
    cases p using OnePoint.rec with
    | infty => exact (hp (interior_subset hinf)).elim
    | coe z =>
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hUfill hp)
      exact mem_iUnion.mpr ⟨i, z, hi, rfl⟩
  · intro p hp hpA
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact hAout i hpA hi

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ImageCoreJordan
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual Jordan disks bounded by an image core

Schoenflies is applied only to the images of the given boundary circles.
The image-core theorem then proves that their filled sides are pairwise
disjoint and exhaust the complement of the image core.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem exists_jordan_image_core_of_continuous_open
    (hschoenflies : PlanarSchoenflies)
    {f : Sphere → Sphere} {G K : Set Sphere}
    (hG : IsOpen G) (hf : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hi : InjOn f G)
    (hK : IsCompact K) (hKG : K ⊆ G)
    (hregular : closure (interior K) = K)
    (hconn : IsPreconnected (interior K)) (hinf : OnePoint.infty ∈ interior K)
    (hfix : f OnePoint.infty = OnePoint.infty)
    {I : Type*} [Finite I] (γ : I → Circle → ℂ)
    (hγ : ∀ i, Continuous (γ i)) (hγinj : ∀ i, Injective (γ i))
    (hγpair : Pairwise (fun i j => Disjoint (range (γ i)) (range (γ j))))
    (hfront : frontier K = ⋃ i, ((↑) : ℂ → Sphere) '' range (γ i)) :
    ∃ H : I → ℂ ≃ₜ ℂ,
      (∀ i, frontier (jordanInterior (H i)) =
        range (fun t => finiteCoord (f ((γ i t : ℂ) : Sphere)))) ∧
      Pairwise (Disjoint on fun i => closure (jordanInterior (H i))) ∧
      (f '' K)ᶜ = ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (H i) := by
  have hγK (i : I) (t : Circle) : ((γ i t : ℂ) : Sphere) ∈ K := by
    apply hK.isClosed.closure_eq ▸ frontier_subset_closure
    rw [hfront]
    exact mem_iUnion.mpr ⟨i, γ i t, ⟨t, rfl⟩, rfl⟩
  have hinfG : OnePoint.infty ∈ G := hKG (interior_subset hinf)
  have hfinite (i : I) (t : Circle) : f ((γ i t : ℂ) : Sphere) ≠ OnePoint.infty :=
    finite_image_of_fixes_infty hi hinfG hfix (hKG (hγK i t))
  let δ : I → Circle → ℂ := fun i t => finiteCoord (f ((γ i t : ℂ) : Sphere))
  have hcoords (i : I) (t : Circle) : (δ i t : Sphere) = f ((γ i t : ℂ) : Sphere) :=
    CannonMobius.coe_coordinate (hfinite i t)
  have hδ (i : I) : Continuous (δ i) := by
    apply OnePoint.isOpenEmbedding_coe.isInducing.continuous_iff.mpr
    have he : ((↑) : ℂ → Sphere) ∘ δ i = f ∘ ((↑) : ℂ → Sphere) ∘ γ i :=
      funext (hcoords i)
    rw [he]
    exact hf.comp_continuous (OnePoint.continuous_coe.comp (hγ i))
      (fun t => hKG (hγK i t))
  have hδinj (i : I) : Injective (δ i) := by
    intro x y hxy
    apply hγinj i
    apply OnePoint.coe_injective
    apply hi (hKG (hγK i x)) (hKG (hγK i y))
    exact (hcoords i x).symm.trans ((congrArg ((↑) : ℂ → Sphere) hxy).trans (hcoords i y))
  choose H hH using fun i => hschoenflies (δ i) (hδ i) (hδinj i)
  have hHfront (i : I) : frontier (jordanInterior (H i)) = range (δ i) :=
    frontier_jordanInterior_eq_circle_range (H i) (δ i) (hH i)
  have hHp : Pairwise (fun i j => Disjoint (frontier (jordanInterior (H i)))
      (frontier (jordanInterior (H j)))) := by
    intro i j hij
    rw [hHfront i, hHfront j]
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx⟩ ⟨y, hy⟩
    have he : ((γ i x : ℂ) : Sphere) = ((γ j y : ℂ) : Sphere) := by
      apply hi (hKG (hγK i x)) (hKG (hγK j y))
      exact (hcoords i x).symm.trans
        ((congrArg ((↑) : ℂ → Sphere) (hx.trans hy.symm)).trans (hcoords j y))
    exact Set.disjoint_left.mp (hγpair hij) ⟨x, rfl⟩ ⟨y, OnePoint.coe_injective he.symm⟩
  have himages (i : I) : f '' (((↑) : ℂ → Sphere) '' range (γ i)) =
      ((↑) : ℂ → Sphere) '' range (δ i) := by
    ext p
    constructor
    · rintro ⟨_, ⟨_, ⟨t, rfl⟩, rfl⟩, rfl⟩
      exact ⟨δ i t, ⟨t, rfl⟩, hcoords i t⟩
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨((γ i t : ℂ) : Sphere), ⟨γ i t, ⟨t, rfl⟩, rfl⟩, (hcoords i t).symm⟩
  have htargetfront : frontier (f '' K) =
      ⋃ i, ((↑) : ℂ → Sphere) '' frontier (jordanInterior (H i)) := by
    rw [frontier_image_of_continuous_open hf ho hG hi hK hKG, hfront, image_iUnion]
    congr 1
    funext i
    rw [hHfront i]
    exact himages i
  have htargetint := interior_image_of_continuous_open hf ho hG hi hKG
  have htargetregular : closure (interior (f '' K)) = f '' K := by
    rw [htargetint]
    exact closure_image_interior_of_continuous hf hK hKG hregular
  have htargetconn : IsPreconnected (interior (f '' K)) := by
    rw [htargetint]
    exact hconn.image f (hf.mono (interior_subset.trans hKG))
  have htargetinf : OnePoint.infty ∈ interior (f '' K) := by
    rw [htargetint]
    exact ⟨OnePoint.infty, hinf, hfix⟩
  obtain ⟨hd, he⟩ := sphere_jordan_core_recognition htargetregular htargetconn htargetinf H hHp htargetfront
  exact ⟨H, hHfront, hd, he⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JordanIntersectionConnectivity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Connectivity on the inside of a retained Jordan boundary

A radial clamp onto a slightly smaller disk fixes any prescribed pair of
interior points and maps the whole domain into its intersection with the
disk. The inner circle stays in the domain by compactness of the retained
boundary. This proves the connectedness needed to track source and image
sides under refinement.
-/

open Set Function Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem continuous_radialClamp {r : ℝ} (hr : 0 < r) : Continuous (radialClamp r) := by
  apply (continuous_const.div (continuous_const.max continuous_norm) ?_).smul continuous_id
  intro z
  exact ne_of_gt (lt_of_lt_of_le hr (le_max_left _ _))

theorem radialClamp_eq_self {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : ‖z‖ ≤ r) :
    radialClamp r z = z := by
  simp only [radialClamp, max_eq_left hz, div_self hr.ne', one_smul]

theorem norm_radialClamp_of_le {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : r ≤ ‖z‖) :
    ‖radialClamp r z‖ = r := by
  have hn : ‖z‖ ≠ 0 := ne_of_gt (hr.trans_le hz)
  rw [radialClamp, max_eq_right hz, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hr.le (norm_nonneg z)), div_mul_cancel₀ _ hn]

theorem inner_circle_subset_of_retained_boundary
    {W : Set ℂ} (hW : IsOpen W) (hboundary : sphere (0 : ℂ) 1 ⊆ W) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r < 1 → 1 - r < δ → sphere (0 : ℂ) r ⊆ W := by
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_sphere (0 : ℂ) 1).exists_cthickening_subset_open hW hboundary
  refine ⟨δ, hδ, ?_⟩
  intro r hr hr1 hnear z hz
  have hzn : ‖z‖ = r := mem_sphere_zero_iff_norm.mp hz
  let w : ℂ := r⁻¹ • z
  have hwn : ‖w‖ = 1 := by
    simp only [w, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, hzn,
      inv_mul_cancel₀ hr.ne']
  have hzw : z = r • w := by simp only [w, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  apply hsub
  apply mem_cthickening_of_dist_le z w δ (sphere (0 : ℂ) 1)
    (mem_sphere_zero_iff_norm.mpr hwn)
  calc
    dist z w = ‖(r - 1) • w‖ := by rw [hzw, dist_eq_norm, sub_smul, one_smul]
    _ = 1 - r := by rw [norm_smul, Real.norm_eq_abs, hwn, mul_one, abs_of_neg (sub_neg.mpr hr1)]; ring
    _ ≤ δ := hnear.le

theorem isPreconnected_inter_unitDisk
    {W : Set ℂ} (hW : IsOpen W) (hconn : IsPreconnected W)
    (hboundary : sphere (0 : ℂ) 1 ⊆ W) :
    IsPreconnected (W ∩ ball 0 1) := by
  obtain ⟨δ, hδ, hcircle⟩ := inner_circle_subset_of_retained_boundary hW hboundary
  apply isPreconnected_of_forall_pair
  intro x hx y hy
  have hxn : ‖x‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hx.2
  have hyn : ‖y‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hy.2
  have hmax : max (max ‖x‖ ‖y‖) (1 - δ) < 1 :=
    max_lt (max_lt hxn hyn) (by linarith)
  obtain ⟨r, hrlo, hrhi⟩ := exists_between hmax
  have hxr : ‖x‖ < r := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hrlo)
  have hyr : ‖y‖ < r := (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hrlo)
  have hr : 0 < r := (norm_nonneg x).trans_lt hxr
  have hnear : 1 - r < δ := by linarith [le_max_right (max ‖x‖ ‖y‖) (1 - δ)]
  have hmap : radialClamp r '' W ⊆ W ∩ ball 0 1 := by
    rintro _ ⟨z, hz, rfl⟩
    by_cases hzr : ‖z‖ ≤ r
    · rw [radialClamp_eq_self hr hzr]
      exact ⟨hz, by simpa only [mem_ball, dist_zero_right] using hzr.trans_lt hrhi⟩
    · have he := norm_radialClamp_of_le hr (le_of_lt (lt_of_not_ge hzr))
      exact ⟨hcircle r hr hrhi hnear (mem_sphere_zero_iff_norm.mpr he), by
        simpa only [mem_ball, dist_zero_right, he] using hrhi⟩
  refine ⟨radialClamp r '' W, hmap, ?_, ?_, hconn.image _ (continuous_radialClamp hr).continuousOn⟩
  · exact ⟨x, hx.1, radialClamp_eq_self hr hxr.le⟩
  · exact ⟨y, hy.1, radialClamp_eq_self hr hyr.le⟩

theorem isPreconnected_inter_jordanInterior
    {W : Set ℂ} (hW : IsOpen W) (hconn : IsPreconnected W)
    (H : ℂ ≃ₜ ℂ) (hboundary : frontier (jordanInterior H) ⊆ W) :
    IsPreconnected (W ∩ jordanInterior H) := by
  have hpre : IsPreconnected (H ⁻¹' W) := H.isPreconnected_preimage.mpr hconn
  have hbd : sphere (0 : ℂ) 1 ⊆ H ⁻¹' W := by
    intro z hz
    apply hboundary
    rw [frontier_jordanInterior]
    exact mem_image_of_mem _ hz
  have hi := isPreconnected_inter_unitDisk (hW.preimage H.continuous) hpre hbd
  have he : H '' ((H ⁻¹' W) ∩ ball 0 1) = W ∩ jordanInterior H := by
    rw [image_preimage_inter]
    rfl
  exact he ▸ hi.image H H.continuous.continuousOn

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JordanSideCorrespondence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Correspondence of the source and image sides of a core boundary

Connectivity of the source on a disk's inside, together with local openness
at its retained boundary, determines which target Jordan disk it maps into.
This tracks the labels of boundary curves without extending the conformal
map across any omitted component.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem isPreconnected_sphere_jordan_intersection
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsPreconnected G)
    (hinf : OnePoint.infty ∈ G) (H : ℂ ≃ₜ ℂ)
    (hboundary : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G) :
    IsPreconnected (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H)) := by
  let W : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' G
  have hW : IsPreconnected W := (finite_part_connected_unbounded hconn
    (mem_interior_iff_mem_nhds.mpr (hG.mem_nhds hinf))).1
  have hi := isPreconnected_inter_jordanInterior (hG.preimage OnePoint.continuous_coe) hW H
    (fun z hz => hboundary (mem_image_of_mem _ hz))
  have he : ((↑) : ℂ → Sphere) '' (W ∩ jordanInterior H) =
      G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H) := image_preimage_inter _ _ _
  exact he ▸ hi.image _ OnePoint.continuous_coe.continuousOn

theorem open_image_jordan_side_subset
    {I : Type*} [Finite I] (H J : I → ℂ ≃ₜ ℂ)
    (hd : Pairwise (Disjoint on fun i => closure (jordanInterior (H i))))
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hKG : closedJordanCore H ⊆ G)
    {f : Sphere → Sphere} (hf : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hi : InjOn f G)
    (hboundary : ∀ i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (H i))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J i)))
    (himage : (f '' closedJordanCore H)ᶜ =
      ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (J i)) (i : I) :
    f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (H i))) ⊆
      ((↑) : ℂ → Sphere) '' jordanInterior (J i) := by
  classical
  let S : Set Sphere := G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (H i))
  let O : Set Sphere := ((↑) : ℂ → Sphere) '' jordanInterior (J i)
  have hOo : IsOpen O := OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen (J i))
  have hKclosed : IsClosed (closedJordanCore H) :=
    (isOpen_iUnion fun j => OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen (H j))).isClosed_compl
  have hsrcboundary (j : I) : ((↑) : ℂ → Sphere) '' frontier (jordanInterior (H j)) ⊆ G := by
    intro q hq
    apply hKG
    have hfq : q ∈ frontier (closedJordanCore H) := by
      rw [frontier_closedJordanCore H hd]
      exact mem_iUnion.mpr ⟨j, hq⟩
    simpa only [hKclosed.closure_eq] using frontier_subset_closure hfq
  have hS : IsPreconnected S :=
    isPreconnected_sphere_jordan_intersection hG hconn.isPreconnected hinf (H i) (hsrcboundary i)
  have hfrontO : frontier O = ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J i)) :=
    frontier_sphere_image_jordanInterior (J i)
  have havoid : Disjoint (f '' S) (frontier O) := by
    apply Set.disjoint_left.mpr
    rintro q ⟨x, hx, rfl⟩ hq
    rw [hfrontO, ← hboundary i] at hq
    obtain ⟨y, hy, he⟩ := hq
    have hyx : y = x := hi (hsrcboundary i hy) hx.1 he
    rw [hyx] at hy
    obtain ⟨z, hz, hez⟩ := hy
    obtain ⟨w, hw, hew⟩ := hx.2
    have hwz : w = z := OnePoint.coe_injective (hew.trans hez.symm)
    exact hz.2 ((jordanInterior_isOpen (H i)).interior_eq.symm ▸ (hwz ▸ hw))
  obtain ⟨z, hz⟩ := (isConnected_frontier_jordanInterior (H i)).nonempty
  let x : Sphere := (z : Sphere)
  have hxfront : x ∈ ((↑) : ℂ → Sphere) '' frontier (jordanInterior (H i)) := ⟨z, hz, rfl⟩
  let B : Set Sphere := ⋃ j : {j : I // j ≠ i}, closedTerminalCap (H j)
  have hBclosed : IsClosed B := isClosed_iUnion_of_finite fun j =>
    (isCompact_closedTerminalCap (H j)).isClosed
  have hxB : x ∉ B := by
    intro h
    obtain ⟨j, w, hw, he⟩ := mem_iUnion.mp h
    have hwz : w = z := OnePoint.coe_injective he
    exact Set.disjoint_left.mp (hd j.property.symm) (frontier_subset_closure hz) (hwz ▸ hw)
  let N : Set Sphere := G ∩ Bᶜ
  have hN : IsOpen N := hG.inter hBclosed.isOpen_compl
  have hxN : x ∈ N := ⟨hsrcboundary i hxfront, hxB⟩
  have hfN : IsOpen (f '' N) := ho _ hN inter_subset_left
  have hfxfront : f x ∈ frontier O := by
    rw [hfrontO, ← hboundary i]
    exact mem_image_of_mem _ hxfront
  obtain ⟨y, hyN, hyO⟩ := mem_closure_iff_nhds.mp (frontier_subset_closure hfxfront)
    (f '' N) (hfN.mem_nhds (mem_image_of_mem _ hxN))
  obtain ⟨w, hwN, rfl⟩ := hyN
  have hwK : w ∉ closedJordanCore H := by
    intro hw
    have htarget : f w ∈ (f '' closedJordanCore H)ᶜ := by
      rw [himage]
      exact mem_iUnion.mpr ⟨i, hyO⟩
    exact htarget (mem_image_of_mem _ hw)
  have hwS : w ∈ S := by
    refine ⟨hwN.1, ?_⟩
    have hwU : w ∈ ⋃ j, ((↑) : ℂ → Sphere) '' jordanInterior (H j) := not_not.mp hwK
    obtain ⟨j, v, hv, he⟩ := mem_iUnion.mp hwU
    by_cases hji : j = i
    · exact hji ▸ ⟨v, hv, he⟩
    · exact (hwN.2 (mem_iUnion.mpr ⟨⟨j, hji⟩, v, subset_closure hv, he⟩)).elim
  have hmeet : (f '' S ∩ O).Nonempty := ⟨f w, mem_image_of_mem _ hwS, hyO⟩
  have hcover : f '' S ⊆ O ∪ (closure O)ᶜ := by
    intro q hq
    by_cases hqo : q ∈ O
    · exact Or.inl hqo
    · right
      intro hqc
      exact Set.disjoint_left.mp havoid hq ⟨hqc, by
        simpa only [hOo.interior_eq] using hqo⟩
  exact (hS.image f (hf.mono inter_subset_left)).subset_left_of_subset_union
    hOo isClosed_closure.isOpen_compl
    (Set.disjoint_left.mpr fun _ h₁ h₂ => h₂ (subset_closure h₁)) hcover hmeet


theorem open_image_jordan_side_eq
    {I : Type*} [Finite I] (H J : I → ℂ ≃ₜ ℂ)
    (hd : Pairwise (Disjoint on fun i => closure (jordanInterior (H i))))
    (hJd : Pairwise (Disjoint on fun i => closure (jordanInterior (J i))))
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hKG : closedJordanCore H ⊆ G)
    {f : Sphere → Sphere} (hf : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hi : InjOn f G)
    (hboundary : ∀ i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (H i))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J i)))
    (himage : (f '' closedJordanCore H)ᶜ =
      ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (J i)) (i : I) :
    f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (H i))) =
      f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J i)) := by
  have hsides := open_image_jordan_side_subset H J hd hG hconn hinf hKG hf ho hi hboundary himage
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨mem_image_of_mem _ hx.1, hsides i (mem_image_of_mem _ hx)⟩
  · rintro y ⟨⟨x, hx, rfl⟩, hy⟩
    have hnotK : x ∉ closedJordanCore H := by
      intro hxK
      have hnot : f x ∈ (f '' closedJordanCore H)ᶜ := by
        rw [himage]
        exact mem_iUnion.mpr ⟨i, hy⟩
      exact hnot (mem_image_of_mem _ hxK)
    obtain ⟨j, hj⟩ := mem_iUnion.mp (not_not.mp hnotK)
    have hj' := hsides j (mem_image_of_mem f ⟨hx, hj⟩)
    have hji : j = i := by
      by_contra hne
      exact Set.disjoint_left.mp (disjoint_closedTerminalCaps J hJd hne)
        (by obtain ⟨z, hz, he⟩ := hj'; exact ⟨z, subset_closure hz, he⟩)
        (by obtain ⟨z, hz, he⟩ := hy; exact ⟨z, subset_closure hz, he⟩)
    exact ⟨x, ⟨hx, hji ▸ hj⟩, rfl⟩


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedImageCores
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Matched source and target Jordan cores

The actual mapped boundary parametrizations identify each target disk's
label. Both inclusions of the corresponding source/target side equality
are proved, so refinement can carry those labels to end components.
-/

open Set Function
open scoped Topology Manifold ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem exists_matched_image_core_of_continuous_open
    (hschoenflies : PlanarSchoenflies)
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G)
    {f : Sphere → Sphere} (hf : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hi : InjOn f G)
    (hfix : f OnePoint.infty = OnePoint.infty) (C : SmoothJordanCore G) :
    ∃ J : Fin C.count → ℂ ≃ₜ ℂ,
      Pairwise (Disjoint on fun i => closure (jordanInterior (J i))) ∧
      (f '' C.carrier)ᶜ = ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (J i) ∧
      (∀ i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (C.disk i))) =
        ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J i))) ∧
      ∀ i, f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (C.disk i))) =
        f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J i)) := by
  have hsrcfront : frontier C.carrier = ⋃ i, ((↑) : ℂ → Sphere) '' range (C.curve i) := by
    rw [SmoothJordanCore.carrier, frontier_closedJordanCore C.disk C.disjoint]
    simp only [C.boundary]
  have hcurvesG (i : Fin C.count) (t : Circle) : ((C.curve i t : ℂ) : Sphere) ∈ G := by
    apply C.subset
    have hfront : ((C.curve i t : ℂ) : Sphere) ∈ frontier C.carrier := by
      rw [hsrcfront]
      exact mem_iUnion.mpr ⟨i, C.curve i t, ⟨t, rfl⟩, rfl⟩
    simpa only [C.isCompact.isClosed.closure_eq] using frontier_subset_closure hfront
  obtain ⟨J, hJfront, hJd, hJe⟩ := exists_jordan_image_core_of_continuous_open hschoenflies hG hf ho hi
    C.isCompact C.subset C.regular C.connected_interior.isPreconnected C.infty_interior hfix
    C.curve (fun i => (C.embedding i).continuous) (fun i => (C.embedding i).injective)
    (by
      intro i j hij
      apply (C.disjoint hij).mono
      · rw [← C.boundary i]
        exact frontier_subset_closure
      · rw [← C.boundary j]
        exact frontier_subset_closure) hsrcfront
  have hboundary (i : Fin C.count) :
      f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (C.disk i))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J i)) := by
    rw [C.boundary i, hJfront i, image_image, ← range_comp, ← range_comp]
    congr 1
    funext t
    exact (CannonMobius.coe_coordinate
      (finite_image_of_fixes_infty hi hinf hfix (hcurvesG i t))).symm
  refine ⟨J, hJd, hJe, hboundary, ?_⟩
  exact open_image_jordan_side_eq C.disk J C.disjoint hJd hG hconn hinf C.subset
    hf ho hi hboundary hJe


theorem exists_matched_image_core
    (hschoenflies : PlanarSchoenflies)
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G)
    {f : Sphere → Sphere} (hf : IsConformalOn f G) (hi : InjOn f G)
    (hfix : f OnePoint.infty = OnePoint.infty) (C : SmoothJordanCore G) :
    ∃ J : Fin C.count → ℂ ≃ₜ ℂ,
      Pairwise (Disjoint on fun i => closure (jordanInterior (J i))) ∧
      (f '' C.carrier)ᶜ = ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (J i) ∧
      (∀ i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (C.disk i))) =
        ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J i))) ∧
      ∀ i, f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (C.disk i))) =
        f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J i)) :=
  exists_matched_image_core_of_continuous_open hschoenflies hG hconn hinf
    (fun p hp => (hf p hp).1.continuousWithinAt)
    (fun _ hS hSG => hf.isOpen_image hG hS hSG) hi hfix C

theorem exists_matched_jordan_exhaustion_of_continuous_open
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G)
    {f : Sphere → Sphere} (hf : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hi : InjOn f G)
    (hfix : f OnePoint.infty = OnePoint.infty) :
    ∃ (C : ℕ → SmoothJordanCore G) (J : (n : ℕ) → Fin (C n).count → ℂ ≃ₜ ℂ),
      (∀ n, (C n).carrier ⊆ interior (C (n + 1)).carrier) ∧
      (⋃ n, interior (C n).carrier) = G ∧
      (∀ n, Pairwise (Disjoint on fun i => closure (jordanInterior (J n i)))) ∧
      (∀ n, (f '' (C n).carrier)ᶜ = ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (J n i)) ∧
      (∀ n i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C n).disk i))) =
        ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J n i))) ∧
      ∀ n i, f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior ((C n).disk i))) =
        f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J n i)) := by
  classical
  obtain ⟨C, hs, hc⟩ := exists_smooth_jordan_exhaustion hsard hschoenflies hG hconn hinf
  choose J hd he hb hi' using fun n => exists_matched_image_core_of_continuous_open hschoenflies hG hconn hinf hf ho hi hfix (C n)
  exact ⟨C, J, hs, hc, hd, he, hb, hi'⟩


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedComponentSides
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Trapping a corresponding component by any retained contour

The source end need only lie inside the chosen contour. Compactness places
a sufficiently late source collar there, and the matched side equality
places its target collar inside the target contour.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem SmoothJordanCore.omitted_point_mem_side
    {G : Set Sphere} (A : SmoothJordanCore G) {q : Sphere} (hq : q ∈ Gᶜ)
    {j : Fin A.count} (hqj : q ∈ closedTerminalCap (A.disk j)) :
    q ∈ ((↑) : ℂ → Sphere) '' jordanInterior (A.disk j) := by
  have hnot : q ∉ A.carrier := fun h => hq (A.subset h)
  have hqunion : q ∈ ⋃ k, ((↑) : ℂ → Sphere) '' jordanInterior (A.disk k) :=
    not_not.mp hnot
  obtain ⟨k, z, hz, he⟩ := mem_iUnion.mp hqunion
  by_cases hkj : k = j
  · exact hkj ▸ ⟨z, hz, he⟩
  · exact (Set.disjoint_left.mp (disjoint_closedTerminalCaps A.disk A.disjoint hkj)
      ⟨z, subset_closure hz, he⟩ hqj).elim

theorem matched_component_subset_retained_side
    {G : Set Sphere} {f : Sphere → Sphere}
    (C : ℕ → SmoothJordanCore G) (J : (n : ℕ) → Fin (C n).count → ℂ ≃ₜ ℂ)
    (b : (n : ℕ) → Fin (C n).count)
    (hsourceNest : Antitone (fun n => closedTerminalCap ((C n).disk (b n))))
    (hboundary : ∀ n i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C n).disk i))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J n i)))
    {S E : Set Sphere}
    (hsource : S = ⋂ n, closedTerminalCap ((C n).disk (b n)))
    (htarget : E = ⋂ n, closedTerminalCap (J n (b n)))
    (H L : ℂ ≃ₜ ℂ)
    (hside : f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H)) =
      f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior L))
    (hS : S ⊆ ((↑) : ℂ → Sphere) '' jordanInterior H) :
    E ⊆ ((↑) : ℂ → Sphere) '' jordanInterior L := by
  obtain ⟨n, hn⟩ := nested_sphere_sets_eventually_subset
    (fun n => (isCompact_closedTerminalCap ((C n).disk (b n))).isClosed)
    hsourceNest (OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen H)) (hsource ▸ hS)
  have hfrontG : ((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C n).disk (b n))) ⊆ G := by
    intro x hx
    apply (C n).subset
    have hxf : x ∈ frontier (C n).carrier := by
      rw [SmoothJordanCore.carrier, frontier_closedJordanCore (C n).disk (C n).disjoint]
      exact mem_iUnion.mpr ⟨b n, hx⟩
    simpa only [(C n).isCompact.isClosed.closure_eq] using frontier_subset_closure hxf
  have hfront : frontier (jordanInterior (J n (b n))) ⊆ jordanInterior L := by
    intro z hz
    have hzimage : (z : Sphere) ∈
        f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C n).disk (b n)))) := by
      rw [hboundary n (b n)]
      exact mem_image_of_mem _ hz
    obtain ⟨x, hx, hxe⟩ := hzimage
    have hxcap : x ∈ closedTerminalCap ((C n).disk (b n)) := by
      obtain ⟨w, hw, rfl⟩ := hx
      exact ⟨w, frontier_subset_closure hw, rfl⟩
    have hzside : (z : Sphere) ∈ ((↑) : ℂ → Sphere) '' jordanInterior L := by
      have hmem : (z : Sphere) ∈ f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H)) :=
        ⟨x, ⟨hfrontG hx, hn hxcap⟩, hxe⟩
      rw [hside] at hmem
      exact hmem.2
    exact OnePoint.coe_injective.mem_set_image.mp hzside
  rw [htarget]
  exact (iInter_subset _ n).trans
    (image_mono (closed_jordanInterior_subset_of_frontier_subset (J n (b n)) L hfront))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_EndCluster
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Cluster values at a specified end

The matched side identity places images of a sequence approaching the
source end eventually in every target collar. A convergent image sequence
therefore limits in the full target component, without extending the map
across that component.
-/

open Set Function Filter
open scoped Topology

namespace CircleDomainRigidity

open FiniteTransfer

theorem cluster_mem_matched_end
    {G : Set Sphere} {f : Sphere → Sphere}
    (H J : ℕ → ℂ ≃ₜ ℂ)
    (hside : ∀ j, f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (H j))) =
      f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J j)))
    {q p : Sphere} (hq : ∀ j, q ∈ ((↑) : ℂ → Sphere) '' jordanInterior (H j))
    {x : ℕ → Sphere} (hx : Tendsto x atTop (𝓝 q)) (hxG : ∀ᶠ n in atTop, x n ∈ G)
    (hy : Tendsto (f ∘ x) atTop (𝓝 p)) :
    p ∈ ⋂ j, closedTerminalCap (J j) := by
  apply mem_iInter.mpr
  intro j
  have hevent : ∀ᶠ n in atTop, x n ∈ ((↑) : ℂ → Sphere) '' jordanInterior (H j) :=
    hx.eventually ((OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen (H j))).mem_nhds (hq j))
  apply (isCompact_closedTerminalCap (J j)).isClosed.mem_of_tendsto hy
  filter_upwards [hevent, hxG] with n hn hnG
  have hfn : f (x n) ∈ f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J j)) := by
    rw [← hside j]
    exact mem_image_of_mem _ ⟨hnG, hn⟩
  obtain ⟨z, hz, he⟩ := hfn.2
  exact ⟨z, subset_closure hz, he⟩

theorem cluster_mem_corresponding_component
    {G : Set Sphere} {f : Sphere → Sphere}
    (H J : ℕ → ℂ ≃ₜ ℂ)
    (hside : ∀ j, f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (H j))) =
      f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J j)))
    {q p p₀ : Sphere} (hq : ∀ j, q ∈ ((↑) : ℂ → Sphere) '' jordanInterior (H j))
    (hcomponent : connectedComponentIn (f '' G)ᶜ p₀ = ⋂ j, closedTerminalCap (J j))
    {x : ℕ → Sphere} (hx : Tendsto x atTop (𝓝 q)) (hxG : ∀ᶠ n in atTop, x n ∈ G)
    (hy : Tendsto (f ∘ x) atTop (𝓝 p)) :
    p ∈ connectedComponentIn (f '' G)ᶜ p₀ := by
  rw [hcomponent]
  exact cluster_mem_matched_end H J hside hq hx hxG hy

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_FiniteModelEnds
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Terminal components of an actual finite circle model

Every physical terminal disk determines a target complementary component.
The assignment exhausts all target components and respects every retained
Jordan contour. Only the existing topological inputs are used.
-/

open Set Function Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem jordan_address_eq_of_common_point
    {I : ℕ → Type*} (C : (n : ℕ) → I n → ℂ ≃ₜ ℂ)
    (hd : ∀ n, Pairwise (Disjoint on fun i => closure (jordanInterior (C n i))))
    {b d : (n : ℕ) → I n} {x : Sphere}
    (hb : x ∈ ⋂ n, closedTerminalCap (C n (b n)))
    (hd' : x ∈ ⋂ n, closedTerminalCap (C n (d n))) : b = d := by
  funext n
  by_contra hne
  exact Set.disjoint_left.mp (disjoint_closedTerminalCaps (C n) (hd n) hne)
    (mem_iInter.mp hb n) (mem_iInter.mp hd' n)

theorem exists_finite_model_terminal_assignment
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {I : Type*} [Finite I] (T : I → ℂ ≃ₜ ℂ)
    (hTd : Pairwise (Disjoint on fun i => closure (jordanInterior (T i))))
    {f fi : Sphere → Sphere} {V : Set Sphere}
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (hV : IsOpen V) (hfix : f OnePoint.infty = OnePoint.infty) :
    ∃ p : I → Sphere,
      (∀ i, p i ∈ Vᶜ) ∧
      Pairwise (Disjoint on fun i => connectedComponentIn Vᶜ (p i)) ∧
      (∀ y ∈ Vᶜ, ∃ i, connectedComponentIn Vᶜ y = connectedComponentIn Vᶜ (p i)) ∧
      (∀ i q, q ∈ closedTerminalCap (T i) → ∀ x : ℕ → Sphere,
        Tendsto x Filter.atTop (𝓝 q) → (∀ᶠ n in Filter.atTop, x n ∈ openCompletedRegion T) →
        ∀ y, Tendsto (f ∘ x) Filter.atTop (𝓝 y) → y ∈ connectedComponentIn Vᶜ (p i)) ∧
      ∀ A : SmoothJordanCore (openCompletedRegion T),
        ∃ L : Fin A.count → ℂ ≃ₜ ℂ,
          (∀ j, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (A.disk j))) =
            ((↑) : ℂ → Sphere) '' frontier (jordanInterior (L j))) ∧
          ∀ i j, closedTerminalCap (T i) ⊆
            ((↑) : ℂ → Sphere) '' jordanInterior (A.disk j) →
            connectedComponentIn Vᶜ (p i) ⊆ ((↑) : ℂ → Sphere) '' jordanInterior (L j) := by
  classical
  let Q := openCompletedRegion T
  have hQ : IsOpen Q := isOpen_openCompletedRegion T
  have hQc : IsConnected Q := isConnected_openCompletedRegion T hTd
  have hQcomp : Qᶜ = ⋃ j, closedTerminalCap (T j) := compl_compl _
  have hinf : OnePoint.infty ∈ Q := by
    intro h
    obtain ⟨i, z, _, hz⟩ := mem_iUnion.mp h
    exact OnePoint.coe_ne_infty z hz
  have hcont : ContinuousOn f Q := fun x hx => (hf.smooth x hx).1.continuousWithinAt
  have hopen : ∀ S, IsOpen S → S ⊆ Q → IsOpen (f '' S) :=
    fun _ hS hSQ => hf.isOpen_image hV hS hSQ
  have hi : InjOn f Q := hf.bijOn.injOn
  have himage : f '' Q = V := hf.bijOn.image_eq
  have hcomponent {i : I} {q : Sphere} (hq : q ∈ closedTerminalCap (T i)) :
      connectedComponentIn Qᶜ q = closedTerminalCap (T i) := by
    rw [hQcomp]
    exact connectedComponentIn_finite_disjoint_closed _
      (fun j => (isCompact_closedTerminalCap (T j)).isClosed)
      (fun j => isPreconnected_closedTerminalCap (T j)) (disjoint_closedTerminalCaps T hTd) hq
  obtain ⟨C, J, hs, hc, hd, he, hb, hside⟩ :=
    exists_matched_jordan_exhaustion_of_continuous_open hsard hschoenflies
      hQ hQc hinf hcont hopen hi hfix
  have hex (i : I) : ∃ (b : (n : ℕ) → Fin (C n).count) (p : Sphere),
      p ∈ Vᶜ ∧ closedTerminalCap (T i) = ⋂ n, closedTerminalCap ((C n).disk (b n)) ∧
      connectedComponentIn Vᶜ p = ⋂ n, closedTerminalCap (J n (b n)) ∧
      Antitone (fun n => closedTerminalCap ((C n).disk (b n))) := by
    obtain ⟨q, hq⟩ := (nontrivial_closedTerminalCap (T i)).nonempty
    have hqQ : q ∈ Qᶜ := by
      rw [hQcomp]
      exact mem_iUnion.mpr ⟨i, hq⟩
    obtain ⟨b, p, hp, hsrc, htgt, hnest⟩ :=
      corresponding_target_end_of_source_of_continuous_open hQ hcont hopen hi
        C J hs hc hd he hb hside hqQ
    rw [hcomponent hq] at hsrc
    rw [himage] at hp htgt
    refine ⟨b, p, hp, hsrc, htgt, ?_⟩
    apply antitone_nat_of_succ_le
    intro n x hx
    have hn := (matched_jordan_disk_subset_iff hi
      ((C n).disk (b n)) ((C (n + 1)).disk (b (n + 1)))
      (J n (b n)) (J (n + 1) (b (n + 1)))
      ((C (n + 1)).boundary_subset_domain _) (hb _ _) (hside _ _)).mpr (hnest n)
    obtain ⟨z, hz, hez⟩ := hn hx
    exact ⟨z, subset_closure hz, hez⟩
  choose b p hp hsrc htgt hanti using hex
  refine ⟨p, hp, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    change x ∈ connectedComponentIn Vᶜ (p i) at hxi
    change x ∈ connectedComponentIn Vᶜ (p j) at hxj
    have hbij : b i = b j := jordan_address_eq_of_common_point J hd
      (htgt i ▸ hxi) (htgt j ▸ hxj)
    have hcaps : closedTerminalCap (T i) = closedTerminalCap (T j) := by
      rw [hsrc i, hsrc j, hbij]
    obtain ⟨z, hz⟩ := (nontrivial_closedTerminalCap (T i)).nonempty
    have hzj : z ∈ closedTerminalCap (T j) := by rwa [← hcaps]
    exact Set.disjoint_left.mp (disjoint_closedTerminalCaps T hTd hij) hz hzj
  · intro y hy
    have hy' : y ∈ (f '' Q)ᶜ := himage.symm ▸ hy
    obtain ⟨d, q, hq, hqsrc, hytgt, _⟩ :=
      corresponding_source_end_of_target_of_continuous_open hQ hcont hopen hi
        C J hs hc hd he hb hside hy'
    rw [hQcomp] at hq
    obtain ⟨i, hqi⟩ := mem_iUnion.mp hq
    rw [hcomponent hqi] at hqsrc
    have hbd : b i = d := jordan_address_eq_of_common_point
      (fun n => (C n).disk) (fun n => (C n).disjoint)
      (hsrc i ▸ hqi) (hqsrc ▸ hqi)
    refine ⟨i, ?_⟩
    rw [← himage, hytgt, himage, htgt i, hbd]
  · intro i q hqi x hx hxQ y hy
    have hqQ : q ∈ Qᶜ := by
      rw [hQcomp]
      exact mem_iUnion.mpr ⟨i, hqi⟩
    have hqside (n : ℕ) : q ∈ ((↑) : ℂ → Sphere) '' jordanInterior ((C n).disk (b i n)) :=
      (C n).omitted_point_mem_side hqQ (mem_iInter.mp (hsrc i ▸ hqi) n)
    have htgt' : connectedComponentIn (f '' Q)ᶜ (p i) = ⋂ n, closedTerminalCap (J n (b i n)) := by
      simpa only [himage] using htgt i
    simpa only [himage] using cluster_mem_corresponding_component
      (fun n => (C n).disk (b i n)) (fun n => J n (b i n))
      (fun n => hside n (b i n)) hqside htgt' hx hxQ hy
  · intro A
    obtain ⟨L, _, _, hboundary, hsideA⟩ :=
      exists_matched_image_core_of_continuous_open hschoenflies hQ hQc hinf
        hcont hopen hi hfix A
    refine ⟨L, hboundary, ?_⟩
    intro i j hij
    exact matched_component_subset_retained_side C J (b i) (hanti i) hb
      (hsrc i) (htgt i) (A.disk j) (L j) (hsideA j) hij

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FiniteMarkedTrapping
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Marked-disk trapping for the actual finite terminal assignment

The assignment is constructed from a finite model. Once a fixed source
core is retained, a terminal inside one of its holes has its target disk
inside the corresponding image contour. Uniform convergence on that
contour passes this containment to the limiting closed disk.
-/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem exists_terminal_component_assignment
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {I : Type*} [Finite I] (T : I → ℂ ≃ₜ ℂ)
    (hTd : Pairwise (Disjoint on fun i => closure (jordanInterior (T i))))
    {f fi : Sphere → Sphere} {V : Set Sphere}
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (hV : IsOpen V) (hfix : f OnePoint.infty = OnePoint.infty) :
    Nonempty (TerminalComponentAssignment T f V) := by
  obtain ⟨p, hp, hd, hc, hcl, hr⟩ := exists_finite_model_terminal_assignment
    hsard hschoenflies T hTd hf hV hfix
  exact ⟨⟨p, hp, hd, hc, hcl, hr⟩⟩

theorem range_finite_image_boundary
    {f : Sphere → Sphere} {γ : Circle → ℂ} {H L : ℂ ≃ₜ ℂ}
    (hγ : frontier (jordanInterior H) = range γ)
    (hb : f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior L))
    (hfinite : ∀ t, f ((γ t : ℂ) : Sphere) ≠ OnePoint.infty) :
    range (fun t => finiteCoord (f ((γ t : ℂ) : Sphere))) = frontier (jordanInterior L) := by
  apply OnePoint.coe_injective.image_injective
  rw [← hb, hγ, image_image, ← range_comp, ← range_comp]
  congr 1
  funext t
  exact coe_finiteCoord (hfinite t)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_TerminalBoundaryLimits
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Inverse images approach the assigned terminal boundary

A target sequence approaching an assigned complementary component has
preimages eventually in every neighborhood of the corresponding physical
terminal boundary. Compactness and the proved component assignment replace
any assumption of a boundary extension of the uniformizing map.
-/

open Set Function Filter
open scoped Topology

namespace CircleDomainRigidity

open FiniteTransfer

theorem TerminalComponentAssignment.inverse_eventually_near_boundary
    {I : Type*} {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    {i : I} {y : Sphere} (hy : y ∈ connectedComponentIn Vᶜ (a.point i))
    {yn : ℕ → Sphere} (hyn : Tendsto yn atTop (𝓝 y))
    (hynV : ∀ᶠ n in atTop, yn n ∈ V)
    {O : Set Sphere} (hO : IsOpen O)
    (hboundary : ((↑) : ℂ → Sphere) '' frontier (jordanInterior (T i)) ⊆ O) :
    ∀ᶠ n in atTop, fi (yn n) ∈ O := by
  by_contra hnot
  have hfreq : ∃ᶠ n in atTop, fi (yn n) ∈ Oᶜ := not_eventually.mp hnot
  obtain ⟨q, hq, s, hs, hqs⟩ := hO.isClosed_compl.isCompact.tendsto_subseq' hfreq
  have hxQ : ∀ᶠ n in atTop, fi (yn (s n)) ∈ openCompletedRegion T := by
    filter_upwards [hs.tendsto_atTop hynV] with n hn
    exact hf.mapsTo_inv hn
  have hfn : (fun n => f (fi (yn (s n)))) =ᶠ[atTop] (yn ∘ s) := by
    filter_upwards [hs.tendsto_atTop hynV] with n hn
    exact hf.right_inv _ hn
  have hfqs : Tendsto (fun n => f (fi (yn (s n)))) atTop (𝓝 y) :=
    (hyn.comp hs.tendsto_atTop).congr' hfn.symm
  exact hq (hboundary (a.source_cluster_mem_boundary hf hy hqs hxQ hfqs))

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_TerminalCollarOscillation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform oscillation on target collars, derived from the proved
assignment of target ends to physical terminal boundaries. No boundary
extension of the uniformizing map is assumed. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem TerminalComponentAssignment.inverse_boundary_neighborhood
    {I : Type*} {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    {i : I} {O : Set Sphere} (hO : IsOpen O)
    (hboundary : ((↑) : ℂ → Sphere) '' frontier (jordanInterior (T i)) ⊆ O) :
    ∃ W : Set Sphere, IsOpen W ∧ connectedComponentIn Vᶜ (a.point i) ⊆ W ∧
      ∀ y ∈ W ∩ V, fi y ∈ O := by
  let B : Set Sphere := {y | y ∈ V ∧ fi y ∉ O}
  refine ⟨(closure B)ᶜ, isClosed_closure.isOpen_compl, ?_, ?_⟩
  · intro y hy hyB
    obtain ⟨s, hs, hlim⟩ := mem_closure_iff_seq_limit.mp hyB
    have he := a.inverse_eventually_near_boundary hf hy hlim
      (Eventually.of_forall fun n => (hs n).1) hO hboundary
    obtain ⟨n, hn⟩ := he.exists
    exact (hs n).2 hn
  · intro y hy
    by_contra hn
    exact hy.1 (subset_closure (show y ∈ B from ⟨hy.2, hn⟩))

 theorem exists_open_oscillation_bound
    {X : Type*} [TopologicalSpace X] {K U : Set X}
    (hK : IsCompact K) (hne : K.Nonempty) (hU : IsOpen U) (hKU : K ⊆ U)
    (v : X → ℝ) (hv : ContinuousOn v U) (A : ℝ)
    (hA : ∀ x ∈ K, ∀ y ∈ K, |v x - v y| ≤ A) {ε : ℝ} (hε : 0 < ε) :
    ∃ O : Set X, IsOpen O ∧ K ⊆ O ∧ O ⊆ U ∧
      ∀ x ∈ O, ∀ y ∈ O, |v x - v y| ≤ A + ε := by
  obtain ⟨a, ha, hmin⟩ := hK.exists_isMinOn hne (hv.mono hKU)
  obtain ⟨b, hb, hmax⟩ := hK.exists_isMaxOn hne (hv.mono hKU)
  let O : Set X := U ∩ v ⁻¹' Ioo (v a - ε / 2) (v b + ε / 2)
  have hO : IsOpen O := hv.isOpen_inter_preimage hU isOpen_Ioo
  have hKO : K ⊆ O := by
    intro x hx
    refine ⟨hKU hx, ?_, ?_⟩
    · have hh : v a ≤ v x := hmin hx
      linarith
    · have hh : v x ≤ v b := hmax hx
      linarith
  refine ⟨O, hO, hKO, inter_subset_left, ?_⟩
  intro x hx y hy
  have hba := (abs_le.mp (hA b hb a ha)).2
  exact abs_le.mpr ⟨by linarith [hx.2.1, hy.2.2], by linarith [hx.2.2, hy.2.1]⟩

 theorem TerminalComponentAssignment.round_collar_oscillation
    {I : Type*} {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (i : I) (c : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (htarget : ((↑) : ℂ → Sphere) '' closedBall c r ⊆
      connectedComponentIn Vᶜ (a.point i))
    {U : Set Sphere} (hU : IsOpen U)
    (hboundary : ((↑) : ℂ → Sphere) '' frontier (jordanInterior (T i)) ⊆ U)
    (v : Sphere → ℝ) (hv : ContinuousOn v U) (A : ℝ)
    (hA : ∀ x ∈ frontier (jordanInterior (T i)),
      ∀ y ∈ frontier (jordanInterior (T i)), |v (x : Sphere) - v (y : Sphere)| ≤ A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ closedBall c (r + δ), ∀ y ∈ closedBall c (r + δ),
      (x : Sphere) ∈ V → (y : Sphere) ∈ V →
      |v (fi (x : Sphere)) - v (fi (y : Sphere))| ≤ A + ε := by
  let K := ((↑) : ℂ → Sphere) '' frontier (jordanInterior (T i))
  have hK : IsCompact K :=
    ((isCompact_closure_jordanInterior (T i)).of_isClosed_subset
      isClosed_frontier frontier_subset_closure).image OnePoint.continuous_coe
  have hne : K.Nonempty := (isConnected_frontier_jordanInterior (T i)).nonempty.image _
  obtain ⟨O, hO, hKO, _, hosc⟩ := exists_open_oscillation_bound hK hne hU hboundary v hv A
    (by rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩; exact hA x hx y hy) hε
  obtain ⟨W, hW, hcomp, hmap⟩ := a.inverse_boundary_neighborhood hf hO hKO
  have hin : closedBall c r ⊆ ((↑) : ℂ → Sphere) ⁻¹' W :=
    fun x hx => hcomp (htarget ⟨x, hx, rfl⟩)
  obtain ⟨δ, hδ, hδsub⟩ := (isCompact_closedBall c r).exists_cthickening_subset_open
    (hW.preimage OnePoint.continuous_coe) hin
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy hxV hyV
  have hxW : (x : Sphere) ∈ W := hδsub (by
    simpa only [cthickening_closedBall hδ.le hr, add_comm δ] using hx)
  have hyW : (y : Sphere) ∈ W := hδsub (by
    simpa only [cthickening_closedBall hδ.le hr, add_comm δ] using hy)
  exact hosc _ (hmap _ ⟨hxW, hxV⟩) _ (hmap _ ⟨hyW, hyV⟩)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RoundCollarLifts
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual zero-period real lift on a target collar is the source
branch composed with the inverse finite model. Its oscillation follows
from the terminal assignment, not from a boundary extension. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem unitCircleParam_one_eq_zero (c : ℂ) (r : ℝ) :
    unitCircleParam c r 1 = unitCircleParam c r 0 := by
  simpa only [unitCircleParam, mul_one, mul_zero, zero_add] using (periodic_circleMap c r) 0

 theorem unitCircleParam_mem_round_exterior
    {I : Type*} (c : I → ℂ) (r : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hd : Pairwise (Disjoint on fun i => closedBall (c i) (r i + ρ)))
    (i : I) (t : ℝ) : unitCircleParam (c i) (r i + ρ) t ∉ ⋃ j, closedBall (c j) (r j) := by
  have hs : unitCircleParam (c i) (r i + ρ) t ∈ sphere (c i) (r i + ρ) :=
    circleMap_mem_sphere _ (by linarith [hr i]) _
  rintro hm
  obtain ⟨j, hj⟩ := mem_iUnion.mp hm
  by_cases hij : i = j
  · subst j
    have he := mem_sphere.mp hs
    have hl := mem_closedBall.mp hj
    linarith
  · exact Set.disjoint_left.mp (hd hij) (sphere_subset_closedBall hs)
      (closedBall_subset_closedBall (by linarith : r j ≤ r j + ρ) hj)

 theorem TerminalComponentAssignment.round_collar_mapsTo
    {I : Type*} {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (i : I) (c : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (htarget : ((↑) : ℂ → Sphere) '' closedBall c r ⊆
      connectedComponentIn Vᶜ (a.point i))
    {U : Set Sphere} (hU : IsOpen U)
    (hboundary : ((↑) : ℂ → Sphere) '' frontier (jordanInterior (T i)) ⊆ U) :
    ∃ δ > 0, ∀ x ∈ closedBall c (r + δ), (x : Sphere) ∈ V → fi (x : Sphere) ∈ U := by
  obtain ⟨W, hW, hcomp, hmap⟩ := a.inverse_boundary_neighborhood hf hU hboundary
  obtain ⟨δ, hδ, hδsub⟩ := (isCompact_closedBall c r).exists_cthickening_subset_open
    (hW.preimage OnePoint.continuous_coe) (fun x hx => hcomp (htarget ⟨x, hx, rfl⟩))
  refine ⟨δ, hδ, fun x hx hxV => hmap x ?_⟩
  exact ⟨hδsub (by simpa only [cthickening_closedBall hδ.le hr, add_comm δ] using hx), hxV⟩

 theorem TerminalComponentAssignment.exists_round_collar_lifts
    {I : Type*} [Fintype I] {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (c : I → ℂ) (r : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hd : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    (hext : ((↑) : ℂ → Sphere) ⁻¹' V = (⋃ i, closedBall (c i) (r i))ᶜ)
    (i : I) (htarget : ((↑) : ℂ → Sphere) '' closedBall (c i) (r i) ⊆
      connectedComponentIn Vᶜ (a.point i))
    {U : Set Sphere} (hU : IsOpen U)
    (hboundary : ((↑) : ℂ → Sphere) '' frontier (jordanInterior (T i)) ⊆ U)
    (v : Sphere → ℝ) (hv : ContinuousOn v U) (w : Sphere → UnitAddCircle)
    (hproj : ∀ x ∈ U, (v x : UnitAddCircle) = w x)
    (A : ℝ) (hA : ∀ x ∈ frontier (jordanInterior (T i)),
      ∀ y ∈ frontier (jordanInterior (T i)), |v (x : Sphere) - v (y : Sphere)| ≤ A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ ρ ∈ Ioc (0 : ℝ) δ,
      Continuous (roundCollarRealLift fi v (c i) (r i + ρ)) ∧
      (∀ t, (roundCollarRealLift fi v (c i) (r i + ρ) t : UnitAddCircle) =
        w (fi (unitCircleParam (c i) (r i + ρ) t : Sphere))) ∧
      roundCollarRealLift fi v (c i) (r i + ρ) 1 = roundCollarRealLift fi v (c i) (r i + ρ) 0 ∧
      ∀ t ∈ Icc (0 : ℝ) 1, |roundCollarRealLift fi v (c i) (r i + ρ) t -
        roundCollarRealLift fi v (c i) (r i + ρ) 0| ≤ A + ε := by
  obtain ⟨δU, hδU, hmap⟩ := a.round_collar_mapsTo hf i (c i) (hr i) htarget hU hboundary
  obtain ⟨δA, hδA, hosc⟩ := a.round_collar_oscillation hf i (c i) (hr i) htarget
    hU hboundary v hv A hA hε
  obtain ⟨δG, hδG, hgeom⟩ := exists_common_round_hole_offset c r hr hd isOpen_univ
    (fun _ => subset_univ _)
  refine ⟨min δU (min δA δG), lt_min hδU (lt_min hδA hδG), ?_⟩
  intro ρ hρ
  have hρU : ρ ≤ δU := hρ.2.trans (min_le_left _ _)
  have hρA : ρ ≤ δA := hρ.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρG : ρ ≤ δG := hρ.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hdisj := (hgeom ρ ⟨hρ.1, hρG⟩).2
  have hV (t : ℝ) : (unitCircleParam (c i) (r i + ρ) t : Sphere) ∈ V := by
    change unitCircleParam (c i) (r i + ρ) t ∈ ((↑) : ℂ → Sphere) ⁻¹' V
    rw [hext]
    exact unitCircleParam_mem_round_exterior c r hr hρ.1 hdisj i t
  have hc (t : ℝ) : unitCircleParam (c i) (r i + ρ) t ∈ closedBall (c i) (r i + ρ) :=
    sphere_subset_closedBall (circleMap_mem_sphere _ (by linarith [hr i, hρ.1]) _)
  have hsource (t : ℝ) : fi (unitCircleParam (c i) (r i + ρ) t : Sphere) ∈ U :=
    hmap _ (closedBall_subset_closedBall (add_le_add le_rfl hρU) (hc t)) (hV t)
  refine ⟨?_, fun t => hproj _ (hsource t), ?_, ?_⟩
  · apply continuous_iff_continuousAt.mpr
    intro t
    have hcurve : Continuous (fun s : ℝ => (unitCircleParam (c i) (r i + ρ) s : Sphere)) :=
      OnePoint.continuous_coe.comp (contDiff_unitCircleParam _ _).continuous
    have hfic : ContinuousAt fi (unitCircleParam (c i) (r i + ρ) t : Sphere) :=
      (hf.smooth_inv _ (hV t)).1
    have hic : ContinuousAt (fun s : ℝ => fi (unitCircleParam (c i) (r i + ρ) s : Sphere)) t :=
      hfic.comp (f := fun s : ℝ => (unitCircleParam (c i) (r i + ρ) s : Sphere)) hcurve.continuousAt
    exact (hv.continuousAt (hU.mem_nhds (hsource t))).comp
      (f := fun s : ℝ => fi (unitCircleParam (c i) (r i + ρ) s : Sphere)) hic
  · unfold roundCollarRealLift
    rw [unitCircleParam_one_eq_zero]
  · intro t _
    exact hosc _ (closedBall_subset_closedBall (add_le_add le_rfl hρA) (hc t))
      _ (closedBall_subset_closedBall (add_le_add le_rfl hρA) (hc 0)) (hV t) (hV 0)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RoundCollarPeriod
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One jointly continuous real lift on the unwrapped annulus gives the
same finite period on every small concentric circle. The period need not
be specified as an additional hypothesis for removing offsets. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem continuous_unitCircleParam_family (c : ℂ) (r : ℝ) :
    Continuous (fun p : ℝ × ℝ => unitCircleParam c (r + p.1) p.2) := by
  unfold unitCircleParam circleMap
  fun_prop

 theorem exists_constant_period_round_collars
    {O : Set ℂ} {u : ℂ → UnitAddCircle} (hu : ContinuousOn u O)
    (c : ℂ) (r : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hc : ∀ ρ ∈ Ioo (0 : ℝ) δ, ∀ t, unitCircleParam c (r + ρ) t ∈ O) :
    ∃ (v : ℝ → ℝ → ℝ) (k : ℝ), ∀ ρ ∈ Ioo (0 : ℝ) δ,
      Continuous (v ρ) ∧
      (∀ t, (v ρ t : UnitAddCircle) = u (unitCircleParam c (r + ρ) t)) ∧
      v ρ 1 - v ρ 0 = k := by
  let D : Set (ℝ × ℝ) := Ioo 0 δ ×ˢ univ
  have hD : IsOpen D := isOpen_Ioo.prod isOpen_univ
  have hmid : δ / 2 ∈ Ioo (0 : ℝ) δ := ⟨half_pos hδ, half_lt_self hδ⟩
  let : ContractibleSpace D :=
    ((convex_Ioo (0 : ℝ) δ).prod convex_univ).contractibleSpace ⟨(δ / 2, 0), hmid, mem_univ _⟩
  let : LocallyPathConnectedSpace D := hD.locallyPathConnectedSpace
  let F : ℝ × ℝ → UnitAddCircle := fun p => u (unitCircleParam c (r + p.1) p.2)
  have hF : ContinuousOn F D := hu.comp (continuous_unitCircleParam_family c r).continuousOn
    (fun p hp => hc p.1 hp.1 p.2)
  obtain ⟨v, hv, _, hp⟩ := exists_continuous_circle_lift F hF
    (show (δ / 2, 0) ∈ D from ⟨hmid, mem_univ _⟩)
    (circleRepresentative (F (δ / 2, 0))) (coe_circleRepresentative _)
  let A := Ioo (0 : ℝ) δ
  let : PreconnectedSpace A := Subtype.preconnectedSpace (convex_Ioo (0 : ℝ) δ).isPreconnected
  let v₀ : A → ℝ := fun ρ => v (ρ, 0)
  let v₁ : A → ℝ := fun ρ => v (ρ, 1)
  have hv₀ : Continuous v₀ := hv.comp_continuous (continuous_subtype_val.prodMk continuous_const)
    (fun ρ => ⟨ρ.property, mem_univ _⟩)
  have hv₁ : Continuous v₁ := hv.comp_continuous (continuous_subtype_val.prodMk continuous_const)
    (fun ρ => ⟨ρ.property, mem_univ _⟩)
  have hperiod := isLocallyConstant_real_lift_difference hv₁ hv₀ (fun ρ => by
    rw [hp (ρ, 1) ⟨ρ.property, mem_univ _⟩, hp (ρ, 0) ⟨ρ.property, mem_univ _⟩]
    exact congrArg u (unitCircleParam_one_eq_zero c (r + ρ)))
  refine ⟨fun ρ t => v (ρ, t), v₁ ⟨δ / 2, hmid⟩ - v₀ ⟨δ / 2, hmid⟩, ?_⟩
  intro ρ hρ
  refine ⟨hv.comp_continuous (continuous_const.prodMk continuous_id)
    (fun t => ⟨hρ, mem_univ t⟩), fun t => hp (ρ, t) ⟨hρ, mem_univ _⟩, ?_⟩
  exact hperiod.apply_eq_of_preconnectedSpace ⟨ρ, hρ⟩ ⟨δ / 2, hmid⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SimultaneousRoundCollars
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finitely many actual source branches give all the nonsingular target
collar lifts at one common positive width. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem exists_common_positive_bound {I : Type*} [Fintype I]
    (d : I → ℝ) (hd : ∀ i, 0 < d i) :
    ∃ δ > 0, ∀ i, δ ≤ d i := by
  classical
  let S : Finset ℝ := insert 1 (Finset.univ.image d)
  have hS : S.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨S.min' hS, ?_, ?_⟩
  · have hm := Finset.min'_mem S hS
    rcases Finset.mem_insert.mp hm with hm | hm
    · rw [hm]; exact zero_lt_one
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
      rw [← hi]
      exact hd i
  · intro i
    exact Finset.min'_le S (d i)
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_StokesBudget
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Stokes estimate with distinct terminal labels and the actual
positive-excess budget. The second theorem performs the diagonal limit; its
hypotheses are the numerical estimates proved by finite transfer and Stokes. -/

open Set Function Filter
open scoped Topology BigOperators

noncomputable section
namespace CircleDomainRigidity

 theorem circle_stokes_bound_of_excess
    {I S : Type*} [Fintype I] (label : I → S) (hinj : Injective label)
    (band : S → ℝ) (hband : Summable (fun s => band s ^ 2))
    (r A : I → ℝ) (hA : ∀ i, 0 ≤ A i) (hb : ∀ i, 0 ≤ band (label i))
    {L e η outer : ℝ} (hL : 0 ≤ L)
    (hr : ∑ i, r i ^ 2 ≤ L ^ 2)
    (hexcess : Real.sqrt (∑ i, max (A i - band (label i)) 0 ^ 2) ≤ η)
    (hstokes : |outer| ≤ Real.sqrt Real.pi * L * e +
      ∑ i, 2 * Real.pi * r i * A i) :
    |outer| ≤ Real.sqrt Real.pi * L * e +
      2 * Real.pi * L * (Real.sqrt (∑' s, band s ^ 2) + η) := by
  classical
  have hnorm := sqrt_sum_sq_le_of_excess_budget A (band ∘ label) hA hb
    (finite_label_band_norm_le label hinj band hband) hexcess
  have hcost := circle_costs_le_square_norm Finset.univ r A hL hr
  exact hstokes.trans (add_le_add le_rfl (hcost.trans
    (mul_le_mul_of_nonneg_left hnorm (by positivity))))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_DistinguishedStokesBudget
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The singular terminal is absent from the Stokes boundary sum. Restrict
both the finite terminal norm and the original countable band budget to
its complement before applying Cauchy--Schwarz. -/

open Set Function
open scoped BigOperators

noncomputable section
namespace CircleDomainRigidity

 theorem sum_off_distinguished {I : Type*} [Fintype I] [DecidableEq I]
    (b : I) (f : I → ℝ) :
    (∑ i : {i : I // i ≠ b}, f i) = ∑ i ∈ Finset.univ.erase b, f i :=
  (Finset.sum_subtype (Finset.univ.erase b) (by simp) f).symm

 theorem sum_off_distinguished_le {I : Type*} [Fintype I] [DecidableEq I]
    (b : I) (f : I → ℝ) (hf : ∀ i, 0 ≤ f i) :
    (∑ i : {i : I // i ≠ b}, f i) ≤ ∑ i, f i := by
  rw [sum_off_distinguished]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
    (fun i _ _ => hf i)

 theorem circle_stokes_bound_off_distinguished
    {I S : Type*} [Fintype I] [DecidableEq I] (label : I → S) (hinj : Injective label) (b : I)
    (band : S → ℝ) (hband : Summable (fun s => band s ^ 2))
    (r A : I → ℝ) (hA : ∀ i ≠ b, 0 ≤ A i) (hb : ∀ s, 0 ≤ band s)
    {L e η outer : ℝ} (hL : 0 ≤ L)
    (hr : ∑ i, r i ^ 2 ≤ L ^ 2)
    (hexcess : Real.sqrt (∑ i, max (A i - band (label i)) 0 ^ 2) ≤ η)
    (hstokes : |outer| ≤ Real.sqrt Real.pi * L * e +
      ∑ i ∈ Finset.univ.erase b, 2 * Real.pi * r i * A i) :
    |outer| ≤ Real.sqrt Real.pi * L * e +
      2 * Real.pi * L *
        (Real.sqrt (∑' s : {s : S // s ≠ label b}, band s ^ 2) + η) := by
  classical
  let label' : {i : I // i ≠ b} → {s : S // s ≠ label b} :=
    fun i => ⟨label i, fun h => i.property (hinj h)⟩
  have hi : Injective label' := by
    intro i j h
    exact Subtype.ext (hinj (congrArg Subtype.val h))
  have hr' : (∑ i : {i : I // i ≠ b}, r i ^ 2) ≤ L ^ 2 :=
    (sum_off_distinguished_le b (fun i => r i ^ 2) (fun i => sq_nonneg _)).trans hr
  have he' : Real.sqrt (∑ i : {i : I // i ≠ b}, max (A i - band (label i)) 0 ^ 2) ≤ η :=
    (Real.sqrt_le_sqrt (sum_off_distinguished_le b _ (fun i => sq_nonneg _))).trans hexcess
  have hs' : |outer| ≤ Real.sqrt Real.pi * L * e +
      ∑ i : {i : I // i ≠ b}, 2 * Real.pi * r i * A i := by
    rwa [sum_off_distinguished b (fun i => 2 * Real.pi * r i * A i)]
  exact circle_stokes_bound_of_excess label' hi (fun s => band s)
    (hband.subtype _) (fun i => r i) (fun i => A i)
    (fun i => hA i i.property) (fun i => hb _) hL hr' he' hs'

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_FiniteCircleLinePayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.axisSwap_horizontalLine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Parallel-line payment on a finite circle domain

For a smooth real function on the complement of finitely many round
disks, crossing segments pay through the actual Euclidean gradient and
cluster oscillations. All endpoint traces and gap decompositions are
constructed in the preceding modules.
-/

open Set Function Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem parallel_line_payment_on_finite_disk_complement
    {I : Type*} [Fintype I] (c : I → ℂ) (r A : I → ℝ) {L : ℝ}
    (hr : ∀ i, 0 ≤ r i) (hA : ∀ i, 0 ≤ A i) (hL : 0 ≤ L)
    (hdisj : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    {v : ℂ → ℝ} (hv : ContDiffOn ℝ 1 v (⋃ i, closedBall (c i) (r i))ᶜ)
    (henergy : IntegrableOn (euclideanGradientEnergy v)
      ((⋃ i, closedBall (c i) (r i))ᶜ ∩ closedBall 0 L))
    (hcluster : ∀ i p q u w, p ∈ closedBall (c i) (r i) → q ∈ closedBall (c i) (r i) →
      MapClusterPt u (𝓝[(⋃ j, closedBall (c j) (r j))ᶜ] p) v →
      MapClusterPt w (𝓝[(⋃ j, closedBall (c j) (r j))ᶜ] q) v → |w - u| ≤ A i)
    {J : Set ℝ} (hJ : MeasurableSet J)
    (hcross : ∀ y ∈ J, ∃ a b : ℝ, a < b ∧ a ∈ diskLineDomain c r y ∧
      b ∈ diskLineDomain c r y ∧ horizontalLine y a ∈ closedBall 0 L ∧
      horizontalLine y b ∈ closedBall 0 L ∧ v (horizontalLine y a) = 0 ∧
      v (horizontalLine y b) = 1) :
    (volume J).toReal ≤ Real.sqrt Real.pi * L * Real.sqrt
      (∫ z in (⋃ i, closedBall (c i) (r i))ᶜ ∩ closedBall 0 L, euclideanGradientEnergy v z) +
      ∑ i, 2 * r i * A i := by
  let U := (⋃ i, closedBall (c i) (r i))ᶜ
  let E := U ∩ closedBall (0 : ℂ) L
  let ρ := E.indicator (euclideanGradientNorm v)
  have hU : IsOpen U := (isClosed_iUnion_of_finite (fun i => isClosed_closedBall)).isOpen_compl
  have hE : MeasurableSet E := hU.measurableSet.inter measurableSet_closedBall
  have hρ : MemLp ρ 2 volume := memLp_indicator_euclideanGradientNorm hE henergy
  have hρpos : ∀ z, 0 ≤ ρ z := fun _ => indicator_nonneg
    (fun z _ => Real.sqrt_nonneg (euclideanGradientEnergy v z)) _
  have hρsupport : support ρ ⊆ closedBall 0 L := by
    intro z hz
    by_contra h
    exact hz (indicator_of_notMem (fun he : z ∈ E => h he.2) _)
  have hρint := (integral_le_disk_L2 hL hρ hρpos hρsupport).1
  have hp : Integrable (fun p : ℝ × ℝ => ρ ⟨p.1, p.2⟩) :=
    ((Complex.volume_preserving_equiv_real_prod.symm
      Complex.measurableEquivRealProd).integrable_comp hρint.aestronglyMeasurable).mpr hρint
  have hJsub : J ⊆ Icc (-L) L := by
    intro y hy
    obtain ⟨a, _, _, _, _, ha, _⟩ := hcross y hy
    simpa only [Complex.zero_im, zero_sub, zero_add] using
      (horizontal_line_meets_closedBall (0 : ℂ)).mp ⟨a, ha⟩
  have hJfinite : volume J ≠ ⊤ := ne_of_lt ((measure_mono hJsub).trans_lt measure_Icc_lt_top)
  have hpay : ∀ᵐ y ∂volume.restrict J, 1 ≤ (∫ x : ℝ, ρ ⟨x, y⟩) +
      ∑ i, (Icc ((c i).im - r i) ((c i).im + r i)).indicator (fun _ => A i) y := by
    filter_upwards [ae_restrict_of_ae hp.prod_left_ae, ae_restrict_mem hJ] with y hiy hy
    obtain ⟨a, b, hab, haD, hbD, haB, hbB, hzero, hone⟩ := hcross y hy
    have hf : ContDiffOn ℝ 1 (v ∘ horizontalLine y) (diskLineDomain c r y) :=
      hv.comp (contDiff_horizontalLine y).contDiffOn (fun _ hx => hx)
    apply line_payment_through_disks c r A hr hA hdisj hab haD hbD hf hzero hone hiy
      (fun x => hρpos _) _ _
    · intro x hx
      have hyL := (horizontal_line_meets_closedBall (0 : ℂ)).mp ⟨a, haB⟩
      have hai := (mem_closedBall_iff_mem_horizontalChord (0 : ℂ) hL hyL).mp haB
      have hbi := (mem_closedBall_iff_mem_horizontalChord (0 : ℂ) hL hyL).mp hbB
      have hxB : horizontalLine y x ∈ closedBall 0 L :=
        (mem_closedBall_iff_mem_horizontalChord (0 : ℂ) hL hyL).mpr
          ⟨hai.1.trans hx.1.1, hx.1.2.trans hbi.2⟩
      have hxE : horizontalLine y x ∈ E := ⟨hx.2, hxB⟩
      change |deriv (v ∘ horizontalLine y) x| ≤ E.indicator (euclideanGradientNorm v) (horizontalLine y x)
      rw [indicator_of_mem hxE]
      exact horizontal_derivative_le_gradient ((hv.contDiffAt (hU.mem_nhds hx.2)).differentiableAt (by norm_num))
    · intro i p q u w hp hq hu hw
      exact hcluster i _ _ u w hp hq (horizontal_cluster_is_planar hu)
        (horizontal_cluster_is_planar hw)
  have h := integrated_parallel_line_payment c r A hJfinite hr hA hL hρ hρpos hρsupport hpay
  have hsq : (fun z => ρ z ^ 2) = E.indicator (euclideanGradientEnergy v) := by
    funext z
    by_cases hz : z ∈ E
    · simp only [ρ, indicator_of_mem hz, euclideanGradientNorm_sq]
    · simp only [ρ, indicator_of_notMem hz, zero_pow (by norm_num : 2 ≠ 0)]
  rw [hsq, integral_indicator hE] at h
  exact h


theorem parallel_line_payment_on_finite_disk_complement_square_norm
    {I : Type*} [Fintype I] (c : I → ℂ) (r A : I → ℝ) {L : ℝ}
    (hr : ∀ i, 0 ≤ r i) (hA : ∀ i, 0 ≤ A i) (hL : 0 ≤ L)
    (hdisj : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    (hsub : ∀ i, closedBall (c i) (r i) ⊆ closedBall 0 L)
    {v : ℂ → ℝ} (hv : ContDiffOn ℝ 1 v (⋃ i, closedBall (c i) (r i))ᶜ)
    (henergy : IntegrableOn (euclideanGradientEnergy v)
      ((⋃ i, closedBall (c i) (r i))ᶜ ∩ closedBall 0 L))
    (hcluster : ∀ i p q u w, p ∈ closedBall (c i) (r i) → q ∈ closedBall (c i) (r i) →
      MapClusterPt u (𝓝[(⋃ j, closedBall (c j) (r j))ᶜ] p) v →
      MapClusterPt w (𝓝[(⋃ j, closedBall (c j) (r j))ᶜ] q) v → |w - u| ≤ A i)
    {J : Set ℝ} (hJ : MeasurableSet J)
    (hcross : ∀ y ∈ J, ∃ a b : ℝ, a < b ∧ a ∈ diskLineDomain c r y ∧
      b ∈ diskLineDomain c r y ∧ horizontalLine y a ∈ closedBall 0 L ∧
      horizontalLine y b ∈ closedBall 0 L ∧ v (horizontalLine y a) = 0 ∧
      v (horizontalLine y b) = 1) :
    (volume J).toReal ≤ Real.sqrt Real.pi * L * Real.sqrt
      (∫ z in (⋃ i, closedBall (c i) (r i))ᶜ ∩ closedBall 0 L, euclideanGradientEnergy v z) +
      2 * L * Real.sqrt (∑ i, A i ^ 2) := by
  have h := parallel_line_payment_on_finite_disk_complement c r A hr hA hL hdisj hv henergy
    hcluster hJ hcross
  have ht := parallel_disk_tolls_le_square_norm c r A hr hL hdisj hsub
  rw [integral_parallel_disk_tolls c r A hr] at ht
  exact h.trans (add_le_add le_rfl ht)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_FiniteCircleBarrierCollapse
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Collapse from vanishing finite-circle barriers

The proved finite-hole line estimate rules out a fixed positive-length
set of crossings when both the actual gradient norms and terminal
oscillation norms vanish. This is the analytic contradiction used for
unmarked limiting complementary components.
-/

open Set Function Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem subsingleton_of_zero_projection_measure {K : Set ℂ}
    (hK : IsCompact K) (hconn : IsConnected K)
    (hre : volume (Complex.re '' K) = 0) (him : volume (Complex.im '' K) = 0) :
    K.Subsingleton := by
  have hRe : Complex.re '' K = Icc (sInf (Complex.re '' K)) (sSup (Complex.re '' K)) :=
    eq_Icc_of_connected_compact
      (hconn.image _ Complex.continuous_re.continuousOn) (hK.image Complex.continuous_re)
  have hIm : Complex.im '' K = Icc (sInf (Complex.im '' K)) (sSup (Complex.im '' K)) :=
    eq_Icc_of_connected_compact
      (hconn.image _ Complex.continuous_im.continuousOn) (hK.image Complex.continuous_im)
  have hRele : sInf (Complex.re '' K) ≤ sSup (Complex.re '' K) :=
    nonempty_Icc.mp (hRe ▸ hconn.nonempty.image Complex.re)
  have hImle : sInf (Complex.im '' K) ≤ sSup (Complex.im '' K) :=
    nonempty_Icc.mp (hIm ▸ hconn.nonempty.image Complex.im)
  rw [hRe, Real.volume_Icc, ENNReal.ofReal_eq_zero] at hre
  rw [hIm, Real.volume_Icc, ENNReal.ofReal_eq_zero] at him
  intro z hz w hw
  have hzr : z.re ∈ Icc (sInf (Complex.re '' K)) (sSup (Complex.re '' K)) :=
    hRe ▸ mem_image_of_mem _ hz
  have hwr : w.re ∈ Icc (sInf (Complex.re '' K)) (sSup (Complex.re '' K)) :=
    hRe ▸ mem_image_of_mem _ hw
  have hzi : z.im ∈ Icc (sInf (Complex.im '' K)) (sSup (Complex.im '' K)) :=
    hIm ▸ mem_image_of_mem _ hz
  have hwi : w.im ∈ Icc (sInf (Complex.im '' K)) (sSup (Complex.im '' K)) :=
    hIm ▸ mem_image_of_mem _ hw
  apply Complex.ext <;> linarith [hzr.1, hzr.2, hwr.1, hwr.2, hzi.1, hzi.2, hwi.1, hwi.2]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_BoundedRoundDisks
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Bounded spherical round disks are Euclidean disks

The projective matrix action is converted to a norm inequality for its
inverse. Excluding infinity makes the leading quadratic coefficient
positive, so the completed-square formula gives a positive radius.
-/

open Set Function
open scoped ComplexConjugate

noncomputable section

namespace CircleDomainRigidity

theorem coe_closedBall_is_singleton_or_round (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    (∃ p : Sphere, ((↑) : ℂ → Sphere) '' Metric.closedBall c r = {p}) ∨
      IsRoundClosedDisk (((↑) : ℂ → Sphere) '' Metric.closedBall c r) := by
  rcases hr.eq_or_lt with he | hp
  · left
    refine ⟨(c : Sphere), ?_⟩
    rw [← he, Metric.closedBall_zero, image_singleton]
  · exact Or.inr (isRoundClosedDisk_coe_closedBall c hp)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskedCircleEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Localized energy on the actual coordinate masks

The retained core contains the mask boundaries. Smoothness on the
compact tail and original masked L² data suffice for whole-domain
integrability and comparison after deleting any measurable part of the
core. No extension across a mask boundary is required.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem integrableOn_masked_circle_energy_tail
    {Ω Q K M : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hQ : IsClosed Q)
    (hKc : IsCompact (closure Kᶜ)) (htail : Q ∩ closure Kᶜ ⊆ Ω)
    (hM : IsClosed M) (hboundary : frontier M ⊆ interior K)
    {f : (ℝ × ℝ) → UnitAddCircle} (hf : SmoothCircleOn f (Ω ∩ interior M))
    {g : (ℝ × ℝ) → PlanarMetric} (hg : Continuous g) (hPD : ∀ z, (g z).PosDef) :
    IntegrableOn (fieldEnergy (circleGradient f) g) ((Q \ K) ∩ M) := by
  have hC : IsCompact ((Q ∩ closure Kᶜ) ∩ M) :=
    (hKc.of_isClosed_subset (hQ.inter isClosed_closure) inter_subset_right).inter_right hM
  have hCΩ : (Q ∩ closure Kᶜ) ∩ M ⊆ Ω ∩ interior M := by
    intro z hz
    refine ⟨htail hz.1, (mem_interior_iff_notMem_frontier hz.2).mpr ?_⟩
    intro hb
    have hn : z ∉ interior K := by
      simpa only [closure_compl, mem_compl_iff] using hz.1.2
    exact hn (hboundary hb)
  have hc := continuousOn_fieldEnergy
    (contDiffOn_circleGradient (hΩ.inter isOpen_interior) hf).continuousOn hg hPD
  exact ((hc.mono hCΩ).integrableOn_compact hC).mono_set
    (fun z hz => ⟨⟨hz.1.1, subset_closure hz.1.2⟩, hz.2⟩)

theorem integrableOn_masked_circle_energy
    {Ω Q G K M : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hQ : IsClosed Q)
    (hK : IsClosed K) (hKc : IsCompact (closure Kᶜ))
    (htail : Q ∩ closure Kᶜ ⊆ Ω) (hKG : K ⊆ G)
    (hM : IsClosed M) (hboundary : frontier M ⊆ interior K)
    {f u : (ℝ × ℝ) → UnitAddCircle} (hf : SmoothCircleOn f (Ω ∩ interior M))
    (hu : MemLp (circleGradient u) 2 (volume.restrict (G ∩ M)))
    (hretain : f =ᶠ[𝓝ˢ K] u) {g : (ℝ × ℝ) → PlanarMetric}
    (hg : Continuous g) (hPD : ∀ z, (g z).PosDef)
    (hmetric : ∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1) :
    IntegrableOn (fieldEnergy (circleGradient f) g) (Q ∩ M) := by
  have ht : IntegrableOn (fieldEnergy (circleGradient f) g) ((Q ∩ M) \ K) := by
    have heq : (Q ∩ M) \ K = (Q \ K) ∩ M := by ext z; simp only [Set.mem_sdiff, mem_inter_iff]; tauto
    rw [heq]
    exact integrableOn_masked_circle_energy_tail hΩ hQ hKc htail hM hboundary hf hg hPD
  have hsource : IntegrableOn (fieldEnergy (circleGradient u)
      (fun z => sphericalMetricFactor z • 1)) (G ∩ M) :=
    integrable_fieldEnergy_spherical_of_memLp hu
  have hc : IntegrableOn (fieldEnergy (circleGradient f) g) ((Q ∩ M) ∩ K) := by
    apply (hsource.mono_set
      (fun z hz => ⟨hKG hz.2, hz.1.2⟩)).congr
    filter_upwards [ae_restrict_mem ((hQ.measurableSet.inter hM.measurableSet).inter hK.measurableSet)] with z hz
    have hgrad := circleGradient_congr_of_eventuallyEq
      (hretain.filter_mono (nhds_le_nhdsSet hz.2))
    simp only [fieldEnergy, hgrad, hmetric.self_of_nhdsSet z hz.2]
  simpa only [inter_union_sdiff] using hc.union ht

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_TransportedTerminalBranches
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Cluster oscillation of transported terminal branches

The finite model's actual inverse transports a real branch near a physical
terminal. All its cluster values at the assigned complementary component
come from the physical boundary. Thus the physical square-sum oscillation
estimate survives uniformization without a boundary-extension hypothesis.
-/

open Set Function Filter
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem sphere_branch_of_real_branch {T : ℂ ≃ₜ ℂ}
    {w : (ℝ × ℝ) → ℝ} {F : (ℝ × ℝ) → UnitAddCircle}
    (hbranch : ∀ᶠ x in 𝓝ˢ (frontier (realJordanInterior T)),
      (w x : UnitAddCircle) = F x) :
    ∀ᶠ q in 𝓝ˢ (((↑) : ℂ → Sphere) '' frontier (jordanInterior T)),
      ((sphereRealFunction w q : ℝ) : UnitAddCircle) = sphereRealFunction F q := by
  apply eventually_nhdsSet_iff_forall.mpr
  rintro q ⟨z, hz, rfl⟩
  have hreal : Complex.equivRealProdCLM z ∈ frontier (realJordanInterior T) := by
    rw [frontier_realJordanInterior]
    exact mem_image_of_mem _ hz
  have hp := eventually_nhdsSet_iff_forall.mp hbranch _ hreal
  have hc := continuousAt_sphereRealFunction (w := id) (z := z) continuousAt_id
  exact hc.tendsto hp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SphereClusterBridge
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite-chart cluster bounds from the assigned sphere ends

The line-payment lemma uses planar cluster points. They are the same
finite cluster values controlled by the inverse terminal-boundary
argument, so no boundary extension of the finite uniformization is needed.
-/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem TerminalComponentAssignment.planar_cluster_gap_le
    {I : Type*} {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (i : I) (w : Sphere → ℝ)
    (hw : ∀ q ∈ ((↑) : ℂ → Sphere) '' frontier (jordanInterior (T i)), ContinuousAt w q)
    (hbounded : Bornology.IsBounded
      (w '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (T i)))))
    {p q : ℂ} {u v : ℝ}
    (hp : (p : Sphere) ∈ connectedComponentIn Vᶜ (a.point i))
    (hq : (q : Sphere) ∈ connectedComponentIn Vᶜ (a.point i))
    (hu : MapClusterPt u (𝓝[((↑) : ℂ → Sphere) ⁻¹' V] p)
      ((w ∘ fi) ∘ ((↑) : ℂ → Sphere)))
    (hv : MapClusterPt v (𝓝[((↑) : ℂ → Sphere) ⁻¹' V] q)
      ((w ∘ fi) ∘ ((↑) : ℂ → Sphere))) :
    |v - u| ≤ Metric.diam
      (w '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (T i)))) := by
  have hsub := a.cluster_values_subset_boundary hf i w hw
  have hu' := hsub (planar_mapClusterPt_mem_componentClusterValues hp hu)
  have hv' := hsub (planar_mapClusterPt_mem_componentClusterValues hq hv)
  simpa only [Real.dist_eq] using Metric.dist_le_diam_of_mem hbounded hv' hu'

theorem TerminalComponentAssignment.real_planar_cluster_gap_le
    {I : Type*} {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (i : I) (w : (ℝ × ℝ) → ℝ)
    {O : Set (ℝ × ℝ)} (hO : IsOpen O)
    (hAO : frontier (realJordanInterior (T i)) ⊆ O) (hw : ContinuousOn w O)
    {p q : ℂ} {u v : ℝ}
    (hp : (p : Sphere) ∈ connectedComponentIn Vᶜ (a.point i))
    (hq : (q : Sphere) ∈ connectedComponentIn Vᶜ (a.point i))
    (hu : MapClusterPt u (𝓝[((↑) : ℂ → Sphere) ⁻¹' V] p)
      ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere)))
    (hv : MapClusterPt v (𝓝[((↑) : ℂ → Sphere) ⁻¹' V] q)
      ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere))) :
    |v - u| ≤ Metric.diam (w '' frontier (realJordanInterior (T i))) := by
  have hfront := frontier_realJordanInterior (T i)
  have himage : sphereRealFunction w '' (((↑) : ℂ → Sphere) ''
      frontier (jordanInterior (T i))) = w '' frontier (realJordanInterior (T i)) := by
    rw [hfront, image_image, image_image]
    rfl
  have hbounded : Bornology.IsBounded (w '' frontier (realJordanInterior (T i))) :=
    ((realJordanInterior_geometry (T i)).2.1.image_of_continuousOn (hw.mono hAO)).isBounded
  rw [← himage]
  apply a.planar_cluster_gap_le hf i (sphereRealFunction w) _ (himage.symm ▸ hbounded) hp hq hu hv
  rintro q ⟨z, hz, rfl⟩
  apply continuousAt_sphereRealFunction
  apply hw.continuousAt (hO.mem_nhds (hAO ?_))
  rw [hfront]
  exact mem_image_of_mem _ hz

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_TerminalLinePayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Parallel-line payment for an actual normalized finite model

The round holes are taken from the model's terminal assignment. Their
cluster costs are derived from the real function on the physical terminal
boundaries. This joins line payment to the finite-transfer construction.
-/

open Set Function Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem TerminalComponentAssignment.parallel_line_payment
    {I : Type*} [Fintype I] {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (hV : IsCircleDomain V) (hinf : OnePoint.infty ∈ V)
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : Vᶜ ⊆ ((↑) : ℂ → Sphere) '' closedBall (0 : ℂ) L)
    (w : (ℝ × ℝ) → ℝ) {O : Set (ℝ × ℝ)} (hO : IsOpen O)
    (hTO : ∀ i, frontier (realJordanInterior (T i)) ⊆ O) (hw : ContinuousOn w O)
    (hv : ContDiffOn ℝ 1 ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere))
      (((↑) : ℂ → Sphere) ⁻¹' V))
    (henergy : IntegrableOn
      (euclideanGradientEnergy ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere)))
      ((((↑) : ℂ → Sphere) ⁻¹' V) ∩ closedBall 0 L))
    {J : Set ℝ} (hJ : MeasurableSet J)
    (hcross : ∀ y ∈ J, ∃ s t : ℝ, s < t ∧
      (horizontalLine y s : Sphere) ∈ V ∧ (horizontalLine y t : Sphere) ∈ V ∧
      horizontalLine y s ∈ closedBall 0 L ∧ horizontalLine y t ∈ closedBall 0 L ∧
      sphereRealFunction w (fi (horizontalLine y s)) = 0 ∧
      sphereRealFunction w (fi (horizontalLine y t)) = 1) :
    (volume J).toReal ≤ Real.sqrt Real.pi * L * Real.sqrt
      (∫ z in (((↑) : ℂ → Sphere) ⁻¹' V) ∩ closedBall 0 L,
        euclideanGradientEnergy ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere)) z) +
      2 * L * Real.sqrt (∑ i, Metric.diam (w '' frontier (realJordanInterior (T i))) ^ 2) := by
  obtain ⟨c, r, hr, he, hd, hU⟩ := a.exists_disk_coordinates hV hinf
  let A : I → ℝ := fun i => Metric.diam (w '' frontier (realJordanInterior (T i)))
  have hsub : ∀ i, closedBall (c i) (r i) ⊆ closedBall (0 : ℂ) L :=
    fun i => terminal_disk_subset_bound (he i) hbound
  have hcl : ∀ i p q u v, p ∈ closedBall (c i) (r i) → q ∈ closedBall (c i) (r i) →
      MapClusterPt u (𝓝[(⋃ j, closedBall (c j) (r j))ᶜ] p)
        ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere)) →
      MapClusterPt v (𝓝[(⋃ j, closedBall (c j) (r j))ᶜ] q)
        ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere)) → |v - u| ≤ A i := by
    intro i p q u v hp hq hu hv
    apply a.real_planar_cluster_gap_le hf i w hO (hTO i) hw
    · rw [he i]
      exact mem_image_of_mem _ hp
    · rw [he i]
      exact mem_image_of_mem _ hq
    · simpa only [hU] using hu
    · simpa only [hU] using hv
  have hv' : ContDiffOn ℝ 1 ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere))
      (⋃ j, closedBall (c j) (r j))ᶜ := by simpa only [hU] using hv
  have he' : IntegrableOn
      (euclideanGradientEnergy ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere)))
      ((⋃ j, closedBall (c j) (r j))ᶜ ∩ closedBall 0 L) := by simpa only [hU] using henergy
  rw [hU]
  apply parallel_line_payment_on_finite_disk_complement_square_norm c r A hr
    (fun _ => Metric.diam_nonneg) hL hd hsub hv' he' hcl hJ
  intro y hy
  obtain ⟨s, t, hst, hsV, htV, hsB, htB, hs0, ht1⟩ := hcross y hy
  refine ⟨s, t, hst, ?_, ?_, hsB, htB, hs0, ht1⟩
  · change horizontalLine y s ∈ (⋃ j, closedBall (c j) (r j))ᶜ
    rw [← hU]
    exact hsV
  · change horizontalLine y t ∈ (⋃ j, closedBall (c j) (r j))ᶜ
    rw [← hU]
    exact htV

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_TransportedRealEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite-chart energy of the actual transported real function

Both integrability and the energy identity follow from the Jacobian
formula. Restriction to the bounded disk used by line payment only
decreases this energy.
-/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem transported_real_energy_on_disk_le
    {f fi : Sphere → Sphere} {U V : Set Sphere}
    (heq : IsSmoothSphereEquivalence f fi U V) (hU : IsOpen U) (hV : IsOpen V)
    (hUinf : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty)
    (w : (ℝ × ℝ) → ℝ) (hw : ContDiffOn ℝ ∞ w (realChartDomain U))
    {g : (ℝ × ℝ) → PlanarMetric}
    (hf : ∀ p ∈ U, IsMetricConformalAt g f p)
    (hg : ∀ x ∈ realChartDomain U, (g x).PosDef)
    (hi : IntegrableOn (gradientEnergy w g) (realChartDomain U)) (L : ℝ) :
    IntegrableOn (euclideanGradientEnergy ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere)))
        ((((↑) : ℂ → Sphere) ⁻¹' V) ∩ Metric.closedBall 0 L) ∧
      (∫ z in (((↑) : ℂ → Sphere) ⁻¹' V) ∩ Metric.closedBall 0 L,
        euclideanGradientEnergy ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere)) z) ≤
        ∫ x in realChartDomain U, gradientEnergy w g x := by
  obtain ⟨_, hfull, he⟩ := transported_real_energy heq hU hV hUinf hfix w hw hf hg hi
  refine ⟨hfull.mono_set inter_subset_left, ?_⟩
  rw [← he]
  exact setIntegral_mono_set hfull
    (ae_of_all _ (fun z => euclideanGradientEnergy_nonneg _ z))
    (Eventually.of_forall fun _ hz => hz.1)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_TerminalSourcePayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Line payment charged to the physical source

The target energy in the finite-hole inequality is bounded by the actual
source metric energy. Boundary tolls are the physical terminal-boundary
diameters, as in the real-coordinate finite transfer.
-/

open Set Function Filter Metric MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem TerminalComponentAssignment.parallel_line_payment_source_energy
    {I : Type*} [Fintype I] {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (heq : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (hV : IsCircleDomain V) (hinf : OnePoint.infty ∈ openCompletedRegion T)
    (hfix : f OnePoint.infty = OnePoint.infty)
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : Vᶜ ⊆ ((↑) : ℂ → Sphere) '' closedBall (0 : ℂ) L)
    (w : (ℝ × ℝ) → ℝ)
    (hw : ContDiffOn ℝ ∞ w (realChartDomain (openCompletedRegion T)))
    {O : Set (ℝ × ℝ)} (hO : IsOpen O)
    (hTO : ∀ i, frontier (realJordanInterior (T i)) ⊆ O) (hwO : ContinuousOn w O)
    {g : (ℝ × ℝ) → PlanarMetric}
    (hmetric : ∀ p ∈ openCompletedRegion T, IsMetricConformalAt g f p)
    (hg : ∀ x ∈ realChartDomain (openCompletedRegion T), (g x).PosDef)
    (hi : IntegrableOn (gradientEnergy w g) (realChartDomain (openCompletedRegion T)))
    {J : Set ℝ} (hJ : MeasurableSet J)
    (hcross : ∀ y ∈ J, ∃ s t : ℝ, s < t ∧
      (horizontalLine y s : Sphere) ∈ V ∧ (horizontalLine y t : Sphere) ∈ V ∧
      horizontalLine y s ∈ closedBall 0 L ∧ horizontalLine y t ∈ closedBall 0 L ∧
      sphereRealFunction w (fi (horizontalLine y s)) = 0 ∧
      sphereRealFunction w (fi (horizontalLine y t)) = 1) :
    (volume J).toReal ≤ Real.sqrt Real.pi * L * Real.sqrt
      (∫ x in realChartDomain (openCompletedRegion T), gradientEnergy w g x) +
      2 * L * Real.sqrt (∑ i, Metric.diam (w '' frontier (realJordanInterior (T i))) ^ 2) := by
  have hU := isOpen_openCompletedRegion T
  obtain ⟨hv, _, _⟩ := transported_real_energy heq hU hV.1 hinf hfix w hw hmetric hg hi
  obtain ⟨hlocal, hle⟩ := transported_real_energy_on_disk_le heq hU hV.1 hinf hfix
    w hw hmetric hg hi L
  have hp := a.parallel_line_payment heq hV (heq.infty_mem_target hinf hfix)
    hL hbound w hO hTO hwO hv hlocal hJ hcross
  exact hp.trans (add_le_add
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hle)
      (mul_nonneg (Real.sqrt_nonneg _) hL)) le_rfl)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_TerminalLimitPayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.axisSwap_horizontalLine _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.metricBeltramiCoefficient_scalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Limiting payment by source energy and band widths

For a fixed barrier the transfer errors vanish while the original source
energy and band norm remain. This is the limit required before choosing
successively smaller barriers in the unmarked-end argument.
-/

open Set Function Filter Metric MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem limiting_terminal_line_payment
    {I : ℕ → Type*} [∀ n, Fintype (I n)]
    (T : (n : ℕ) → I n → ℂ ≃ₜ ℂ) (f fi : ℕ → Sphere → Sphere) (V : ℕ → Set Sphere)
    (a : ∀ n, TerminalComponentAssignment (T n) (f n) (V n))
    (heq : ∀ n, IsSmoothSphereEquivalence (f n) (fi n) (openCompletedRegion (T n)) (V n))
    (hV : ∀ n, IsCircleDomain (V n))
    (hinf : ∀ n, OnePoint.infty ∈ openCompletedRegion (T n))
    (hfix : ∀ n, f n OnePoint.infty = OnePoint.infty)
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ n, (V n)ᶜ ⊆ ((↑) : ℂ → Sphere) '' closedBall (0 : ℂ) L)
    (w : ℕ → (ℝ × ℝ) → ℝ)
    (hw : ∀ n, ContDiffOn ℝ ∞ (w n) (realChartDomain (openCompletedRegion (T n))))
    (O : ℕ → Set (ℝ × ℝ)) (hO : ∀ n, IsOpen (O n))
    (hTO : ∀ n i, frontier (realJordanInterior (T n i)) ⊆ O n)
    (hwO : ∀ n, ContinuousOn (w n) (O n))
    (g : ℕ → (ℝ × ℝ) → PlanarMetric)
    (hmetric : ∀ n p, p ∈ openCompletedRegion (T n) → IsMetricConformalAt (g n) (f n) p)
    (hg : ∀ n x, x ∈ realChartDomain (openCompletedRegion (T n)) → (g n x).PosDef)
    (hi : ∀ n, IntegrableOn (gradientEnergy (w n) (g n))
      (realChartDomain (openCompletedRegion (T n))))
    (band : (n : ℕ) → I n → ℝ) (hband : ∀ n i, 0 ≤ band n i)
    {E B : ℝ} (hE : 0 ≤ E)
    (hbandnorm : ∀ n, Real.sqrt (∑ i, band n i ^ 2) ≤ B)
    (e δ : ℕ → ℝ) (he : Tendsto e atTop (𝓝 (E ^ 2))) (hδ : Tendsto δ atTop (𝓝 0))
    (henergy : ∀ᶠ n in atTop,
      (∫ x in realChartDomain (openCompletedRegion (T n)), gradientEnergy (w n) (g n) x) ≤ e n)
    (hexcess : ∀ᶠ n in atTop, Real.sqrt (∑ i,
      max (diam (w n '' frontier (realJordanInterior (T n i))) - band n i) 0 ^ 2) ≤ δ n)
    {J : Set ℝ} (hJ : MeasurableSet J)
    (hcross : ∀ᶠ n in atTop, ∀ y ∈ J, ∃ s t : ℝ, s < t ∧
      (horizontalLine y s : Sphere) ∈ V n ∧ (horizontalLine y t : Sphere) ∈ V n ∧
      horizontalLine y s ∈ closedBall 0 L ∧ horizontalLine y t ∈ closedBall 0 L ∧
      sphereRealFunction (w n) (fi n (horizontalLine y s)) = 0 ∧
      sphereRealFunction (w n) (fi n (horizontalLine y t)) = 1) :
    (volume J).toReal ≤ Real.sqrt Real.pi * L * E + 2 * L * B := by
  have hpay : ∀ᶠ n in atTop, (volume J).toReal ≤
      Real.sqrt Real.pi * L * Real.sqrt (e n) + 2 * L * (B + δ n) := by
    filter_upwards [hcross, henergy, hexcess] with n hn hnE hnA
    have hp := (a n).parallel_line_payment_source_energy (heq n) (hV n)
      (hinf n) (hfix n) hL (hbound n) (w n) (hw n) (hO n) (hTO n) (hwO n)
      (hmetric n) (hg n) (hi n) hJ hn
    have hcost := sqrt_sum_sq_le_of_excess_budget
      (fun i => diam (w n '' frontier (realJordanInterior (T n i)))) (band n)
      (fun _ => diam_nonneg) (hband n) (hbandnorm n) hnA
    exact hp.trans (add_le_add
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hnE)
        (mul_nonneg (Real.sqrt_nonneg _) hL))
      (mul_le_mul_of_nonneg_left hcost (mul_nonneg (by norm_num) hL)))
  have hs : Tendsto (fun n => Real.sqrt (e n)) atTop (𝓝 E) := by
    simpa only [Function.comp_def, Real.sqrt_sq hE] using
      Real.continuous_sqrt.continuousAt.tendsto.comp he
  have ht : Tendsto (fun n => Real.sqrt Real.pi * L * Real.sqrt (e n) +
      2 * L * (B + δ n)) atTop (𝓝 (Real.sqrt Real.pi * L * E + 2 * L * B)) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.mul hs).add
        (tendsto_const_nhds.mul (tendsto_const_nhds.add hδ))
  exact ge_of_tendsto ht hpay

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RealSequencePayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFiniteElemEdgeSetOfFinite _root_.Graph.instFiniteElemVertexSetOfFinite _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.axisSwap_horizontalLine _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.metricBeltramiCoefficient_scalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The line-payment limit for a fixed test in the constructed countable sequence. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

namespace RealModelExhaustion

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  (M : RealModelExhaustion d O ε)

theorem limiting_line_payment
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (harea : ExteriorCoefficientAreaTheorem)
    (hε : Tendsto ε atTop (𝓝 0)) (r : ℕ → ℕ) (hr : Tendsto r atTop atTop) (l : ℕ)
    {L : ℝ} (hL : 3 * M.radius ≤ L)
    {J : Set ℝ} (hJ : MeasurableSet J)
    (hcross : ∀ᶠ n in atTop, ∀ y ∈ J, ∃ s t : ℝ, s < t ∧
      (horizontalLine y s : Sphere) ∈ (M.stages (r n)).domain ∧
      (horizontalLine y t : Sphere) ∈ (M.stages (r n)).domain ∧
      horizontalLine y s ∈ closedBall 0 L ∧
      horizontalLine y t ∈ closedBall 0 L ∧
      sphereRealFunction ((M.stages (r n)).functions (prefixIndex l (r n)))
        ((M.stages (r n)).inverse (horizontalLine y s)) = 0 ∧
      sphereRealFunction ((M.stages (r n)).functions (prefixIndex l (r n)))
        ((M.stages (r n)).inverse (horizontalLine y t)) = 1) :
    (volume J).toReal ≤ Real.sqrt Real.pi * L * Real.sqrt
        (∫ x in realChartDomain G,
          gradientEnergy (d.physical l) (fun z => sphericalMetricFactor z • 1) x) +
      2 * L * Real.sqrt (∑' s, (d.upper l s - d.lower l s) ^ 2) := by
  classical
  let _ : ∀ n, Fintype (M.stages (r n)).indices := fun n => (M.stages (r n)).finite_indices.fintype
  let T (n : ℕ) := (M.stages (r n)).terminals.H
  let f (n : ℕ) := (M.stages (r n)).forward
  let fi (n : ℕ) := (M.stages (r n)).inverse
  let V (n : ℕ) := (M.stages (r n)).domain
  let w (n : ℕ) := (M.stages (r n)).functions (prefixIndex l (r n))
  let E := ∫ x in realChartDomain G,
    gradientEnergy (d.physical l) (fun z => sphericalMetricFactor z • 1) x
  have hE : 0 ≤ E := integral_nonneg (fun x => by
    rw [gradientEnergy_spherical]
    positivity)
  have hbound (n : ℕ) : (V n)ᶜ ⊆ ((↑) : ℂ → Sphere) '' closedBall 0 L := by
    have h := (normalized_model_uniform_bound harea (M.stages (r n)).equivalence
      (M.stages (r n)).circle_domain.1 M.radius_pos
      ((M.exterior_core (r n)).trans (M.core_model (r n)))
      ((M.core_conformal (r n)).mono
        ((compl_subset_compl.mpr (image_mono ball_subset_closedBall)).trans (M.exterior_core (r n))))
      (M.stages (r n)).principal).1
    exact fun p hp => image_mono (closedBall_subset_closedBall hL) (h p hp)
  have ha (n : ℕ) : Nonempty (TerminalComponentAssignment (T n) (f n) (V n)) :=
    exists_terminal_component_assignment hsard hsch (T n)
      (M.stages (r n)).terminals.disjoint_closures (M.stages (r n)).equivalence
      (M.stages (r n)).circle_domain.1 (M.stages (r n)).principal.1
  let a (n : ℕ) := Classical.choice (ha n)
  apply limiting_terminal_line_payment T f fi V a
    (fun n => (M.stages (r n)).equivalence) (fun n => (M.stages (r n)).circle_domain)
    (fun n => (M.stages (r n)).source_infty) (fun n => (M.stages (r n)).principal.1)
    ((mul_nonneg (by norm_num) M.radius_pos.le).trans hL) hbound w
    (fun n => (M.stages (r n)).functions_smooth_source (prefixIndex l (r n)))
    (fun n => (M.stages (r n)).extension) (fun n => (M.stages (r n)).extension_open)
    (fun n => (M.stages (r n)).terminal_frontier_extension)
    (fun n => ((M.stages (r n)).functions_smooth (prefixIndex l (r n))).continuousOn)
    (fun n => (M.stages (r n)).metric) (fun n => (M.stages (r n)).metric_conformal)
    (fun n x _ => (M.stages (r n)).metric_pos x)
    (fun n => (M.stages (r n)).functions_integrable_source (prefixIndex l (r n)))
    (fun n s => d.upper l s - d.lower l s) (fun _ s => d.width_nonneg l s)
    (Real.sqrt_nonneg E) (fun n =>
      finite_label_band_norm_le (fun s : (M.stages (r n)).indices => (s : S))
        Subtype.val_injective (fun s => d.upper l s - d.lower l s) (d.width_summable l))
    (fun n => E + ε (r n)) (fun n => ε (r n)) ?_ (hε.comp hr) ?_ ?_ hJ hcross
  · simpa only [Real.sq_sqrt hE, add_zero, Function.comp_def] using
      tendsto_const_nhds.add (hε.comp hr)
  · filter_upwards [hr (prefixIndex_eq l)] with n hn
    change (prefixIndex l (r n)).val = l at hn
    have h := (M.stages (r n)).source_energy_lt (prefixIndex l (r n))
    simpa only [CountableRealCoordinates.Stage, hn] using h.le
  · filter_upwards [hr (prefixIndex_eq l)] with n hn
    change (prefixIndex l (r n)).val = l at hn
    have h := (M.stages (r n)).excess (prefixIndex l (r n))
    simpa only [terminalOscillation, hn, tsum_fintype] using h.le

end RealModelExhaustion

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_HorizontalFrontierCrossings
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Crossing segments from nested bounded regions

On any horizontal line meeting the inner region, the leftmost points of
the inner and outer closures lie on their frontiers. Strict containment
puts the outer point strictly to the left. Thus prescribed zero/one
frontier values provide the crossing segments needed by line payment.
-/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem exists_leftmost_horizontal_frontier
    {U : Set ℂ} (hU : IsOpen U) (hcompact : IsCompact (closure U))
    {y : ℝ} (hne : ∃ z ∈ closure U, z.im = y) :
    ∃ x : ℝ, horizontalLine y x ∈ frontier U ∧
      ∀ z ∈ closure U, z.im = y → x ≤ z.re := by
  let K := closure U ∩ {z : ℂ | z.im = y}
  have hK : IsCompact K := hcompact.inter_right (isClosed_eq Complex.continuous_im continuous_const)
  have hKne : K.Nonempty := by
    obtain ⟨z, hz, hy⟩ := hne
    exact ⟨z, hz, hy⟩
  obtain ⟨x, hx⟩ := (hK.image Complex.continuous_re).exists_isLeast (hKne.image Complex.re)
  obtain ⟨p, hp, hpx⟩ := hx.1
  have hpeq : p = horizontalLine y x := by
    apply Complex.ext
    · exact hpx
    · exact hp.2
  have hxclosure : horizontalLine y x ∈ closure U := hpeq ▸ hp.1
  have hmin : ∀ z ∈ closure U, z.im = y → x ≤ z.re := by
    intro z hz hy
    exact hx.2 (mem_image_of_mem _ ⟨hz, hy⟩)
  have hxnot : horizontalLine y x ∉ U := by
    intro hxU
    have hpre : (horizontalLine y) ⁻¹' U ∈ 𝓝 x :=
      (hU.preimage (continuous_horizontalLine y)).mem_nhds hxU
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
    have hnear : x - ε / 2 ∈ ball x ε := by
      rw [mem_ball, Real.dist_eq]
      rw [show x - ε / 2 - x = -(ε / 2) by ring, abs_neg, abs_of_pos (half_pos hε)]
      linarith
    have hback : horizontalLine y (x - ε / 2) ∈ U := hball hnear
    have hbound := hmin (horizontalLine y (x - ε / 2)) (subset_closure hback) rfl
    change x ≤ x - ε / 2 at hbound
    linarith
  refine ⟨x, ?_, hmin⟩
  rw [frontier, hU.interior_eq]
  exact ⟨hxclosure, hxnot⟩

theorem exists_horizontal_frontier_crossing
    {W U : Set ℂ} (hW : IsOpen W) (hU : IsOpen U)
    (hWcompact : IsCompact (closure W)) (hUcompact : IsCompact (closure U))
    (hWU : closure W ⊆ U) {y : ℝ} (hne : ∃ z ∈ closure W, z.im = y) :
    ∃ a b : ℝ, a < b ∧ horizontalLine y a ∈ frontier U ∧
      horizontalLine y b ∈ frontier W := by
  obtain ⟨b, hb, hminb⟩ := exists_leftmost_horizontal_frontier hW hWcompact hne
  have hbU : horizontalLine y b ∈ U := hWU (frontier_subset_closure hb)
  obtain ⟨a, ha, hmina⟩ := exists_leftmost_horizontal_frontier hU hUcompact
    ⟨horizontalLine y b, subset_closure hbU, rfl⟩
  refine ⟨a, b, ?_, ha, hb⟩
  have hab : a ≤ b := hmina _ (subset_closure hbU) rfl
  apply lt_of_le_of_ne hab
  intro he
  have haU : horizontalLine y a ∈ U := he.symm ▸ hbU
  have hnot : horizontalLine y a ∉ U := by
    simpa only [horizontalLine, hU.interior_eq] using ha.2
  exact hnot haU

theorem horizontal_frontier_crossings_give_values
    {W U D : Set ℂ} (hW : IsOpen W) (hU : IsOpen U)
    (hWcompact : IsCompact (closure W)) (hUcompact : IsCompact (closure U))
    (hWU : closure W ⊆ U) {L : ℝ} (hUL : closure U ⊆ closedBall 0 L)
    (hUD : frontier U ⊆ D) (hWD : frontier W ⊆ D)
    {v : ℂ → ℝ} (hzero : ∀ z ∈ frontier U, v z = 0)
    (hone : ∀ z ∈ frontier W, v z = 1) {J : Set ℝ}
    (hJ : J ⊆ Complex.im '' closure W) :
    ∀ y ∈ J, ∃ a b : ℝ, a < b ∧ horizontalLine y a ∈ D ∧
      horizontalLine y b ∈ D ∧ horizontalLine y a ∈ closedBall 0 L ∧
      horizontalLine y b ∈ closedBall 0 L ∧ v (horizontalLine y a) = 0 ∧
      v (horizontalLine y b) = 1 := by
  intro y hy
  obtain ⟨z, hz, hzy⟩ := hJ hy
  obtain ⟨a, b, hab, ha, hb⟩ := exists_horizontal_frontier_crossing hW hU hWcompact hUcompact
    hWU ⟨z, hz, hzy⟩
  exact ⟨a, b, hab, hUD ha, hWD hb, hUL (frontier_subset_closure ha),
    hUL (subset_closure (hWU (frontier_subset_closure hb))), hzero _ ha, hone _ hb⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_NestedJordanLimits
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Strict nesting survives anchored Jordan limits

An intermediate compact Jordan disk separates the limiting contours.
Upper containment retains the inner approximations in that disk; the
interior-anchor lemma retains that disk inside the outer approximations.
-/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem eventually_nested_jordanInteriors_of_anchor
    (H K : ℂ ≃ₜ ℂ) (Hn Kn : ℕ → ℂ ≃ₜ ℂ)
    (γ δ : Circle → ℂ) (γn δn : ℕ → Circle → ℂ)
    (hγ : Continuous γ) (hδ : Continuous δ)
    (hγfront : range γ = frontier (jordanInterior H))
    (hδfront : range δ = frontier (jordanInterior K))
    (hγn : ∀ᶠ n in atTop, range (γn n) = frontier (jordanInterior (Hn n)))
    (hδn : ∀ᶠ n in atTop, range (δn n) = frontier (jordanInterior (Kn n)))
    (hγlim : TendstoUniformly γn γ atTop) (hδlim : TendstoUniformly δn δ atTop)
    (hHK : closure (jordanInterior H) ⊆ jordanInterior K)
    {z : ℂ} {zn : ℕ → ℂ} (hz : z ∈ jordanInterior K)
    (hzn : Tendsto zn atTop (𝓝 z))
    (hanchor : ∀ᶠ n in atTop, zn n ∈ jordanInterior (Kn n)) :
    ∀ᶠ n in atTop, closure (jordanInterior (Hn n)) ⊆ jordanInterior (Kn n) := by
  obtain ⟨r, hr, hrsub, _⟩ := exists_disjoint_jordan_enlargements (fun _ : Unit => H)
    (by intro i j hij; exact (hij (Subsingleton.elim _ _)).elim)
    (fun _ => jordanInterior K) (fun _ => jordanInterior_isOpen K) (fun _ => hHK)
  let r₀ := r Unit.unit
  let C := H '' closedBall (0 : ℂ) r₀
  let O := H '' ball (0 : ℂ) r₀
  have hC : IsCompact C := (isCompact_closedBall (0 : ℂ) r₀).image H.continuous
  have hO : IsOpen O := H.isOpenMap _ isOpen_ball
  have hCO : O ⊆ C := image_mono ball_subset_closedBall
  have hHC : closure (jordanInterior H) ⊆ O := by
    rw [closure_jordanInterior]
    exact image_mono (closedBall_subset_ball (hr Unit.unit))
  have hCK : C ⊆ jordanInterior K := hrsub Unit.unit
  have hinner := eventually_jordan_fill_subset_open H Hn γ γn hγ hγfront hγn hγlim hO hHC
  have houter := eventually_compact_subset_jordanInterior_of_anchor K Kn δ δn hδ hδfront
    hδn hδlim hz hzn hanchor hC hCK
  filter_upwards [hinner, houter] with n hn hn'
  exact hn.trans (hCO.trans hn')

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JordanCrossingStability
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Crossing segments persist in converging finite models

Anchored convergence of the inner and outer Jordan contours retains a
fixed compact subset of the inner fill and the strict nesting. Their
prescribed zero/one boundary values then yield crossings over the same
fixed projection set for all sufficiently late models.
-/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem eventually_crossings_of_anchored_jordan_limits
    (H K : ℂ ≃ₜ ℂ) (Hn Kn : ℕ → ℂ ≃ₜ ℂ)
    (γ δ : Circle → ℂ) (γn δn : ℕ → Circle → ℂ)
    (hγ : Continuous γ) (hδ : Continuous δ)
    (hγfront : range γ = frontier (jordanInterior H))
    (hδfront : range δ = frontier (jordanInterior K))
    (hγn : ∀ᶠ n in atTop, range (γn n) = frontier (jordanInterior (Hn n)))
    (hδn : ∀ᶠ n in atTop, range (δn n) = frontier (jordanInterior (Kn n)))
    (hγlim : TendstoUniformly γn γ atTop) (hδlim : TendstoUniformly δn δ atTop)
    (hHK : closure (jordanInterior H) ⊆ jordanInterior K)
    {z w : ℂ} {zn wn : ℕ → ℂ}
    (hz : z ∈ jordanInterior H) (hw : w ∈ jordanInterior K)
    (hzn : Tendsto zn atTop (𝓝 z)) (hwn : Tendsto wn atTop (𝓝 w))
    (hzanchor : ∀ᶠ n in atTop, zn n ∈ jordanInterior (Hn n))
    (hwanchor : ∀ᶠ n in atTop, wn n ∈ jordanInterior (Kn n))
    {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ jordanInterior H)
    (D : ℕ → Set ℂ) (v : ℕ → ℂ → ℝ) {L : ℝ}
    (hbound : ∀ᶠ n in atTop, closure (jordanInterior (Kn n)) ⊆ closedBall 0 L)
    (hboundary : ∀ᶠ n in atTop, frontier (jordanInterior (Hn n)) ⊆ D n ∧
      frontier (jordanInterior (Kn n)) ⊆ D n)
    (hvalues : ∀ᶠ n in atTop,
      (∀ p ∈ frontier (jordanInterior (Kn n)), v n p = 0) ∧
      (∀ p ∈ frontier (jordanInterior (Hn n)), v n p = 1))
    {J : Set ℝ} (hJ : J ⊆ Complex.im '' C) :
    ∀ᶠ n in atTop, ∀ y ∈ J, ∃ a b : ℝ, a < b ∧ horizontalLine y a ∈ D n ∧
      horizontalLine y b ∈ D n ∧ horizontalLine y a ∈ closedBall 0 L ∧
      horizontalLine y b ∈ closedBall 0 L ∧ v n (horizontalLine y a) = 0 ∧
      v n (horizontalLine y b) = 1 := by
  have hretain := eventually_compact_subset_jordanInterior_of_anchor H Hn γ γn
    hγ hγfront hγn hγlim hz hzn hzanchor hC hCH
  have hnested := eventually_nested_jordanInteriors_of_anchor H K Hn Kn γ δ γn δn
    hγ hδ hγfront hδfront hγn hδn hγlim hδlim hHK hw hwn hwanchor
  filter_upwards [hretain, hnested, hbound, hboundary, hvalues] with n hnC hnested hnB hnD hnv
  apply horizontal_frontier_crossings_give_values
    (jordanInterior_isOpen (Hn n)) (jordanInterior_isOpen (Kn n))
    (isCompact_closure_jordanInterior (Hn n)) (isCompact_closure_jordanInterior (Kn n))
    hnested hnB hnD.2 hnD.1 hnv.1 hnv.2
  exact hJ.trans (image_mono (hnC.trans subset_closure))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RetainedJordanConvergence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Anchors for the Jordan curves of actual finite models

A point of the physical domain on the inside of a retained contour gives
an interior anchor in every sufficiently late model. The proved side
correspondence identifies that side, and local uniform convergence gives
the anchor and boundary convergence needed for the crossing argument.
-/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem exists_domain_point_inside_jordan
    {G : Set Sphere} (hG : IsOpen G) (H : ℂ ≃ₜ ℂ)
    (hboundary : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G) :
    ∃ q : ℂ, (q : Sphere) ∈ G ∧ q ∈ jordanInterior H := by
  obtain ⟨p, hp⟩ := (isConnected_frontier_jordanInterior H).nonempty
  have hpG : p ∈ ((↑) : ℂ → Sphere) ⁻¹' G := hboundary ⟨p, hp, rfl⟩
  exact mem_closure_iff_nhds.mp (frontier_subset_closure hp)
    (((↑) : ℂ → Sphere) ⁻¹' G) ((hG.preimage OnePoint.continuous_coe).mem_nhds hpG)

theorem exists_anchored_retained_jordan_models
    (hsch : PlanarSchoenflies)
    {I : ℕ → Type*} [∀ n, Finite (I n)] (T : (n : ℕ) → I n → ℂ ≃ₜ ℂ)
    (hTd : ∀ n, Pairwise (Disjoint on fun i => closure (jordanInterior (T n i))))
    (f fi : ℕ → Sphere → Sphere) (V : ℕ → Set Sphere)
    (heq : ∀ n, IsSmoothSphereEquivalence (f n) (fi n) (openCompletedRegion (T n)) (V n))
    (hV : ∀ n, IsOpen (V n)) (hfix : ∀ n, f n OnePoint.infty = OnePoint.infty)
    {G : Set Sphere} (hG : IsOpen G) (A : SmoothJordanCore G) (j : Fin A.count)
    (hret : ∀ᶠ n in atTop, A.carrier ⊆ openCompletedRegion (T n))
    (hpoint : ∀ q ∈ G, ∀ᶠ n in atTop, q ∈ openCompletedRegion (T n))
    (F : ℂ → ℂ) (hF : ContinuousOn F (((↑) : ℂ → Sphere) ⁻¹' G))
    (hlim : TendstoLocallyUniformlyOn (fun n (z : ℂ) => finiteCoord (f n (z : Sphere)))
      F atTop (((↑) : ℂ → Sphere) ⁻¹' G))
    (H : ℂ ≃ₜ ℂ)
    (hH : extendAtInfinity F '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (A.disk j))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior H))
    (hside : extendAtInfinity F '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (A.disk j))) =
      (extendAtInfinity F '' G) ∩ (((↑) : ℂ → Sphere) '' jordanInterior H)) :
    ∃ (J : ℕ → ℂ ≃ₜ ℂ) (q : ℂ),
      (q : Sphere) ∈ G ∧ q ∈ jordanInterior (A.disk j) ∧ F q ∈ jordanInterior H ∧
      Continuous (F ∘ A.curve j) ∧
      range (F ∘ A.curve j) = frontier (jordanInterior H) ∧
      TendstoUniformly (fun n s => finiteCoord (f n ((A.curve j s : ℂ) : Sphere)))
        (F ∘ A.curve j) atTop ∧
      Tendsto (fun n => finiteCoord (f n (q : Sphere))) atTop (𝓝 (F q)) ∧
      (∀ᶠ n in atTop, finiteCoord (f n (q : Sphere)) ∈ jordanInterior (J n)) ∧
      (∀ᶠ n in atTop,
        f n '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (A.disk j))) =
          ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J n))) ∧
      (∀ᶠ n in atTop, range (fun s => finiteCoord (f n ((A.curve j s : ℂ) : Sphere))) =
        frontier (jordanInterior (J n))) := by
  classical
  have hinf (n : ℕ) : OnePoint.infty ∈ openCompletedRegion (T n) := by
    intro h
    obtain ⟨i, z, _, hz⟩ := mem_iUnion.mp h
    exact OnePoint.coe_ne_infty z hz
  have hex (n : ℕ) : ∃ J : Fin A.count → ℂ ≃ₜ ℂ,
      A.carrier ⊆ openCompletedRegion (T n) →
      (∀ i, f n '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (A.disk i))) =
        ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J i))) ∧
      ∀ i, f n '' (openCompletedRegion (T n) ∩
          (((↑) : ℂ → Sphere) '' jordanInterior (A.disk i))) =
        (f n '' openCompletedRegion (T n)) ∩
          (((↑) : ℂ → Sphere) '' jordanInterior (J i)) := by
    by_cases hn : A.carrier ⊆ openCompletedRegion (T n)
    · obtain ⟨J, _, _, hb, hs⟩ := exists_matched_image_core_of_continuous_open hsch
        (isOpen_openCompletedRegion (T n)) (isConnected_openCompletedRegion (T n) (hTd n))
        (hinf n) (fun p hp => ((heq n).smooth p hp).1.continuousWithinAt)
        (fun S hS hSQ => (heq n).isOpen_image (hV n) hS hSQ)
        (heq n).bijOn.injOn (hfix n) (A.inDomain hn)
      exact ⟨J, fun _ => ⟨hb, hs⟩⟩
    · exact ⟨fun _ => H, fun h => (hn h).elim⟩
  choose J hJ using hex
  obtain ⟨q, hqG, hqA⟩ := exists_domain_point_inside_jordan hG (A.disk j)
    (A.boundary_subset_domain j)
  have hqH : F q ∈ jordanInterior H := by
    have hq : extendAtInfinity F (q : Sphere) ∈
        (extendAtInfinity F '' G) ∩ (((↑) : ℂ → Sphere) '' jordanInterior H) := by
      rw [← hside]
      exact mem_image_of_mem _ ⟨hqG, q, hqA, rfl⟩
    simpa only [extendAtInfinity_coe, OnePoint.coe_injective.mem_set_image] using hq.2
  have hcurveG (s : Circle) : ((A.curve j s : ℂ) : Sphere) ∈ G := by
    apply A.boundary_subset_domain j
    exact ⟨A.curve j s, (A.boundary j) ▸ mem_range_self s, rfl⟩
  have hγ : Continuous (A.curve j) := (A.embedding j).continuous
  have hγF : Continuous (F ∘ A.curve j) := hF.comp_continuous hγ hcurveG
  have hfront : range (F ∘ A.curve j) = frontier (jordanInterior H) := by
    simpa only [extendAtInfinity_coe, finiteCoord_coe, Function.comp_def] using
      range_finite_image_boundary (A.boundary j) hH
        (fun s => by simp only [extendAtInfinity_coe]; exact OnePoint.coe_ne_infty _)
  have hγlim : TendstoUniformly
      (fun n s => finiteCoord (f n ((A.curve j s : ℂ) : Sphere))) (F ∘ A.curve j) atTop := by
    apply tendstoUniformlyOn_univ.mp
    apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_univ).mp
    exact hlim.comp (A.curve j) (fun s _ => hcurveG s) hγ.continuousOn
  refine ⟨fun n => J n j, q, hqG, hqA, hqH, hγF, hfront, hγlim,
    hlim.tendsto_at hqG, ?_, ?_, ?_⟩
  · filter_upwards [hret, hpoint (q : Sphere) hqG] with n hn hqn
    have ht : f n (q : Sphere) ∈ ((↑) : ℂ → Sphere) '' jordanInterior (J n j) := by
      have hh := mem_image_of_mem (f n) (show (q : Sphere) ∈
        openCompletedRegion (T n) ∩ (((↑) : ℂ → Sphere) '' jordanInterior (A.disk j)) from
          ⟨hqn, q, hqA, rfl⟩)
      rw [(hJ n hn).2 j] at hh
      exact hh.2
    obtain ⟨r, hr, her⟩ := ht
    simpa only [← her, finiteCoord_coe] using hr
  · filter_upwards [hret] with n hn
    exact (hJ n hn).1 j
  · filter_upwards [hret] with n hn
    apply range_finite_image_boundary (A.boundary j) ((hJ n hn).1 j)
    intro s
    exact (heq n).finite_forward (hinf n) (hfix n)
      ((A.inDomain hn).boundary_subset_domain j
        ⟨A.curve j s, (A.boundary j) ▸ mem_range_self s, rfl⟩)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_RetainedTestCrossings
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Crossing segments for an actual retained test

The source test has value one on an inner retained contour and zero on
an outer one. Their actual finite-model images produce the common
crossings used in line payment, with anchors derived from source points.
-/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem values_on_image_jordan_boundary
    {f fi : Sphere → Sphere} {U V : Set Sphere}
    (heq : IsSmoothSphereEquivalence f fi U V)
    {H K : ℂ ≃ₜ ℂ}
    (hsource : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ U)
    (himage : f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior K))
    (w : Sphere → ℝ) {c : ℝ} (hvalue : ∀ z ∈ frontier (jordanInterior H), w z = c) :
    frontier (jordanInterior K) ⊆ ((↑) : ℂ → Sphere) ⁻¹' V ∧
      ∀ z ∈ frontier (jordanInterior K), w (fi z) = c := by
  have hpre (z : ℂ) (hz : z ∈ frontier (jordanInterior K)) :
      ∃ p ∈ (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)), f p = z := by
    have hh : (z : Sphere) ∈ f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) := by
      rw [himage]
      exact ⟨z, hz, rfl⟩
    exact hh
  constructor
  · intro z hz
    obtain ⟨p, hp, he⟩ := hpre z hz
    change (z : Sphere) ∈ V
    rw [← he]
    exact heq.mapsTo (hsource hp)
  · intro z hz
    obtain ⟨p, hp, he⟩ := hpre z hz
    have hpinv := heq.left_inv p (hsource hp)
    rw [he] at hpinv
    rw [hpinv]
    obtain ⟨q, hq, rfl⟩ := hp
    exact hvalue q hq

theorem eventually_crossings_of_retained_test
    (hsch : PlanarSchoenflies)
    {I : ℕ → Type*} [∀ n, Finite (I n)] (T : (n : ℕ) → I n → ℂ ≃ₜ ℂ)
    (hTd : ∀ n, Pairwise (Disjoint on fun i => closure (jordanInterior (T n i))))
    (f fi : ℕ → Sphere → Sphere) (V : ℕ → Set Sphere)
    (heq : ∀ n, IsSmoothSphereEquivalence (f n) (fi n) (openCompletedRegion (T n)) (V n))
    (hV : ∀ n, IsOpen (V n)) (hfix : ∀ n, f n OnePoint.infty = OnePoint.infty)
    {G : Set Sphere} (hG : IsOpen G)
    (A B : SmoothJordanCore G) (i : Fin A.count) (j : Fin B.count)
    (hretA : ∀ᶠ n in atTop, A.carrier ⊆ openCompletedRegion (T n))
    (hretB : ∀ᶠ n in atTop, B.carrier ⊆ openCompletedRegion (T n))
    (hpoint : ∀ q ∈ G, ∀ᶠ n in atTop, q ∈ openCompletedRegion (T n))
    (F : ℂ → ℂ) (hF : ContinuousOn F (((↑) : ℂ → Sphere) ⁻¹' G))
    (hlim : TendstoLocallyUniformlyOn (fun n (z : ℂ) => finiteCoord (f n (z : Sphere)))
      F atTop (((↑) : ℂ → Sphere) ⁻¹' G))
    (H K : ℂ ≃ₜ ℂ)
    (hH : extendAtInfinity F '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (A.disk i))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior H))
    (hK : extendAtInfinity F '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (B.disk j))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior K))
    (hsideH : extendAtInfinity F '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (A.disk i))) =
      (extendAtInfinity F '' G) ∩ (((↑) : ℂ → Sphere) '' jordanInterior H))
    (hsideK : extendAtInfinity F '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (B.disk j))) =
      (extendAtInfinity F '' G) ∩ (((↑) : ℂ → Sphere) '' jordanInterior K))
    (hHK : closure (jordanInterior H) ⊆ jordanInterior K)
    {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ jordanInterior H)
    {L : ℝ} (hKL : closure (jordanInterior K) ⊆ ball 0 L)
    (w : ℕ → Sphere → ℝ)
    (hvalues : ∀ᶠ n in atTop,
      (∀ z ∈ frontier (jordanInterior (A.disk i)), w n z = 1) ∧
      (∀ z ∈ frontier (jordanInterior (B.disk j)), w n z = 0)) :
    ∀ᶠ n in atTop, ∀ y ∈ Complex.im '' C, ∃ a b : ℝ, a < b ∧
      (horizontalLine y a : Sphere) ∈ V n ∧ (horizontalLine y b : Sphere) ∈ V n ∧
      horizontalLine y a ∈ closedBall 0 L ∧ horizontalLine y b ∈ closedBall 0 L ∧
      w n (fi n (horizontalLine y a)) = 0 ∧ w n (fi n (horizontalLine y b)) = 1 := by
  obtain ⟨Hn, q, _, _, hq, hγ, hfront, hγlim, hqlim, hqa, hHb, hHnf⟩ :=
    exists_anchored_retained_jordan_models hsch T hTd f fi V heq hV hfix hG A i
      hretA hpoint F hF hlim H hH hsideH
  obtain ⟨Kn, p, _, _, hp, hδ, hfrontK, hδlim, hplim, hpa, hKb, hKnf⟩ :=
    exists_anchored_retained_jordan_models hsch T hTd f fi V heq hV hfix hG B j
      hretB hpoint F hF hlim K hK hsideK
  have hbound : ∀ᶠ n in atTop, closure (jordanInterior (Kn n)) ⊆ closedBall 0 L :=
    (eventually_jordan_fill_subset_open K Kn _ _ hδ hfrontK hKnf hδlim isOpen_ball hKL).mono
      (fun _ hn => hn.trans ball_subset_closedBall)
  have hdata : ∀ᶠ n in atTop,
      (frontier (jordanInterior (Hn n)) ⊆ ((↑) : ℂ → Sphere) ⁻¹' V n ∧
       frontier (jordanInterior (Kn n)) ⊆ ((↑) : ℂ → Sphere) ⁻¹' V n) ∧
      ((∀ z ∈ frontier (jordanInterior (Kn n)), w n (fi n z) = 0) ∧
       (∀ z ∈ frontier (jordanInterior (Hn n)), w n (fi n z) = 1)) := by
    filter_upwards [hretA, hretB, hHb, hKb, hvalues] with n hnA hnB hnH hnK hnv
    have ha := values_on_image_jordan_boundary (heq n)
      ((A.inDomain hnA).boundary_subset_domain i) hnH (w n) hnv.1
    have hb := values_on_image_jordan_boundary (heq n)
      ((B.inDomain hnB).boundary_subset_domain j) hnK (w n) hnv.2
    exact ⟨⟨ha.1, hb.1⟩, hb.2, ha.2⟩
  exact eventually_crossings_of_anchored_jordan_limits H K Hn Kn
    _ _ _ _ hγ hδ hfront hfrontK hHnf hKnf hγlim hδlim hHK hq hp hqlim hplim hqa hpa
    hC hCH (fun n => ((↑) : ℂ → Sphere) ⁻¹' V n)
    (fun n z => w n (fi n z)) hbound (hdata.mono fun _ h => h.1)
    (hdata.mono fun _ h => h.2) (Subset.refl _)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RealSequenceRetention
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFiniteElemEdgeSetOfFinite _root_.Graph.instFiniteElemVertexSetOfFinite _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retention of actual tests and their crossing segments along model subsequences. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer.RealModelExhaustion

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  (M : RealModelExhaustion d O ε)

theorem eventually_test_crossings
    (hsch : PlanarSchoenflies) (hG : IsOpen G)
    (r : ℕ → ℕ) (hr : Tendsto r atTop atTop)
    (F : ℂ → ℂ) (hF : ContinuousOn F (((↑) : ℂ → Sphere) ⁻¹' G))
    (hlim : TendstoLocallyUniformlyOn (fun n (z : ℂ) =>
      finiteCoord ((M.stages (r n)).forward (z : Sphere))) F
      atTop (((↑) : ℂ → Sphere) ⁻¹' G))
    (A B : SmoothJordanCore G) (i : Fin A.count) (j : Fin B.count) (l : ℕ)
    (hOne : ∀ z ∈ frontier (jordanInterior (A.disk i)),
      d.physical l (Complex.equivRealProdCLM z) = 1)
    (hZero : ∀ z ∈ frontier (jordanInterior (B.disk j)),
      d.physical l (Complex.equivRealProdCLM z) = 0)
    (H K : ℂ ≃ₜ ℂ)
    (hH : extendAtInfinity F '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (A.disk i))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior H))
    (hK : extendAtInfinity F '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (B.disk j))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior K))
    (hsideH : extendAtInfinity F '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (A.disk i))) =
      (extendAtInfinity F '' G) ∩ (((↑) : ℂ → Sphere) '' jordanInterior H))
    (hsideK : extendAtInfinity F '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (B.disk j))) =
      (extendAtInfinity F '' G) ∩ (((↑) : ℂ → Sphere) '' jordanInterior K))
    (hHK : closure (jordanInterior H) ⊆ jordanInterior K)
    {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ jordanInterior H)
    {L : ℝ} (hKL : closure (jordanInterior K) ⊆ ball 0 L) :
    ∀ᶠ n in atTop, ∀ y ∈ Complex.im '' C, ∃ a b : ℝ, a < b ∧
      (horizontalLine y a : Sphere) ∈ (M.stages (r n)).domain ∧
      (horizontalLine y b : Sphere) ∈ (M.stages (r n)).domain ∧
      horizontalLine y a ∈ closedBall 0 L ∧ horizontalLine y b ∈ closedBall 0 L ∧
      sphereRealFunction ((M.stages (r n)).functions (prefixIndex l (r n)))
        ((M.stages (r n)).inverse (horizontalLine y a)) = 0 ∧
      sphereRealFunction ((M.stages (r n)).functions (prefixIndex l (r n)))
        ((M.stages (r n)).inverse (horizontalLine y b)) = 1 := by
  let _ : ∀ n, Fintype (M.stages (r n)).indices :=
    fun n => (M.stages (r n)).finite_indices.fintype
  apply eventually_crossings_of_retained_test hsch
    (fun n => (M.stages (r n)).terminals.H)
    (fun n => (M.stages (r n)).terminals.disjoint_closures)
    (fun n => (M.stages (r n)).forward) (fun n => (M.stages (r n)).inverse)
    (fun n => (M.stages (r n)).domain) (fun n => (M.stages (r n)).equivalence)
    (fun n => (M.stages (r n)).circle_domain.1) (fun n => (M.stages (r n)).principal.1)
    hG A B i j (hr (M.eventually_model_contains A.isCompact A.subset))
    (hr (M.eventually_model_contains B.isCompact B.subset)) ?_ F hF hlim H K
    hH hK hsideH hsideK hHK hC hCH hKL
    (fun n => sphereRealFunction ((M.stages (r n)).functions (prefixIndex l (r n)))) ?_
  · intro q hq
    exact hr ((M.eventually_model_contains isCompact_singleton (singleton_subset_iff.mpr hq)).mono
      (fun _ hn => hn (mem_singleton q)))
  · have ha := hr (M.eventually_test_eq A.isCompact A.subset l)
    have hb := hr (M.eventually_test_eq B.isCompact B.subset l)
    filter_upwards [ha, hb] with n hnA hnB
    constructor
    · intro z hz
      simpa only [sphereRealFunction, finiteCoord_coe] using
        (hnA z ((A.inDomain (Subset.refl _)).boundary_subset_domain i ⟨z, hz, rfl⟩)).trans (hOne z hz)
    · intro z hz
      simpa only [sphereRealFunction, finiteCoord_coe] using
        (hnB z ((B.inDomain (Subset.refl _)).boundary_subset_domain j ⟨z, hz, rfl⟩)).trans (hZero z hz)

end CircleDomainRigidity.FiniteTransfer.RealModelExhaustion

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RealBarrierProjection
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Projection payment for a retained real barrier

The test is specified by its actual values on two source contours and
their matched target contours. All finite-model crossings and analytic
estimates are supplied by the constructed sequence.
-/

open Set Function Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem RealModelExhaustion.projection_payment
    {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
    (M : RealModelExhaustion d O ε)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (harea : ExteriorCoefficientAreaTheorem)
    (hG : IsOpen G) (hε : Tendsto ε atTop (𝓝 0))
    (r : ℕ → ℕ) (hr : Tendsto r atTop atTop)
    (F : ℂ → ℂ) (hF : ContinuousOn F (((↑) : ℂ → Sphere) ⁻¹' G))
    (hlim : TendstoLocallyUniformlyOn (fun n (z : ℂ) =>
      finiteCoord ((M.stages (r n)).forward (z : Sphere))) F
      atTop (((↑) : ℂ → Sphere) ⁻¹' G))
    {l : ℕ} (B : RetainedRealBarrier d F l)
    {C : Set ℂ} (hC : IsCompact C) (hCB : C ⊆ jordanInterior B.target_inner)
    {L : ℝ} (hL : 3 * M.radius ≤ L)
    (hBL : closure (jordanInterior B.target_outer) ⊆ ball 0 L) :
    (volume (Complex.im '' C)).toReal ≤ Real.sqrt Real.pi * L * Real.sqrt
        (∫ x in realChartDomain G,
          gradientEnergy (d.physical l) (fun z => sphericalMetricFactor z • 1) x) +
      2 * L * Real.sqrt (∑' s, (d.upper l s - d.lower l s) ^ 2) := by
  apply M.limiting_line_payment hsard hsch harea hε r hr l hL
    (hC.image Complex.continuous_im).measurableSet
  exact M.eventually_test_crossings hsch hG r hr F hF hlim B.inner B.outer
    B.inner_index B.outer_index l B.value_one B.value_zero B.target_inner B.target_outer
    B.inner_image B.outer_image B.inner_side B.outer_side B.nested hC hCB hBL

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RealBarrierVanishing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.metricBeltramiCoefficient_scalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vanishing source barrier norms force a zero-length target projection. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem RealModelExhaustion.projection_zero_of_vanishing_barriers
    {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
    (M : RealModelExhaustion d O ε)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (harea : ExteriorCoefficientAreaTheorem)
    (hG : IsOpen G) (hε : Tendsto ε atTop (𝓝 0))
    (r : ℕ → ℕ) (hr : Tendsto r atTop atTop)
    (F : ℂ → ℂ) (hF : ContinuousOn F (((↑) : ℂ → Sphere) ⁻¹' G))
    (hlim : TendstoLocallyUniformlyOn (fun n (z : ℂ) =>
      finiteCoord ((M.stages (r n)).forward (z : Sphere))) F
      atTop (((↑) : ℂ → Sphere) ⁻¹' G))
    (labels : ℕ → ℕ) (B : ∀ k, RetainedRealBarrier d F (labels k))
    {C : Set ℂ} (hC : IsCompact C)
    (hCB : ∀ k, C ⊆ jordanInterior (B k).target_inner)
    {L : ℝ} (hL : 3 * M.radius ≤ L)
    (hBL : ∀ k, closure (jordanInterior (B k).target_outer) ⊆ ball 0 L)
    (hsmall : Tendsto (fun k =>
      Real.sqrt (∫ x in realChartDomain G,
        gradientEnergy (d.physical (labels k)) (fun z => sphericalMetricFactor z • 1) x) +
      Real.sqrt (∑' s, (d.upper (labels k) s - d.lower (labels k) s) ^ 2))
      atTop (𝓝 0)) : volume (Complex.im '' C) = 0 := by
  have hL0 : 0 ≤ L := (mul_nonneg (by norm_num) M.radius_pos.le).trans hL
  have hpay (k : ℕ) := M.projection_payment hsard hsch harea hG hε r hr F hF hlim
    (B k) hC (hCB k) hL (hBL k)
  have hbound : ∀ k, (volume (Complex.im '' C)).toReal ≤
      ((Real.sqrt Real.pi + 2) * L) *
        (Real.sqrt (∫ x in realChartDomain G,
          gradientEnergy (d.physical (labels k)) (fun z => sphericalMetricFactor z • 1) x) +
        Real.sqrt (∑' s, (d.upper (labels k) s - d.lower (labels k) s) ^ 2)) := by
    intro k
    apply (hpay k).trans
    have ha := Real.sqrt_nonneg (∫ x in realChartDomain G,
      gradientEnergy (d.physical (labels k)) (fun z => sphericalMetricFactor z • 1) x)
    have hb := Real.sqrt_nonneg (∑' s, (d.upper (labels k) s - d.lower (labels k) s) ^ 2)
    have hp := Real.sqrt_nonneg Real.pi
    nlinarith [mul_nonneg hL0 ha, mul_nonneg hL0 hb, mul_nonneg hp (mul_nonneg hL0 hb)]
  have hz : (volume (Complex.im '' C)).toReal = 0 := by
    apply le_antisymm _ ENNReal.toReal_nonneg
    have ht := hsmall.const_mul ((Real.sqrt Real.pi + 2) * L)
    rw [mul_zero] at ht
    exact ge_of_tendsto ht (Eventually.of_forall hbound)
  have hfinite : volume (Complex.im '' C) ≠ ⊤ :=
    (hC.image Complex.continuous_im).measure_ne_top
  simpa only [ENNReal.toReal_eq_zero_iff, hfinite, or_false] using hz

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_VerticalCirclePayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-circle payment estimate in the second Cartesian direction. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem vertical_line_payment_on_finite_disk_complement
    {I : Type*} [Fintype I] (c : I → ℂ) (r A : I → ℝ) {L : ℝ}
    (hr : ∀ i, 0 ≤ r i) (hA : ∀ i, 0 ≤ A i) (hL : 0 ≤ L)
    (hdisj : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    (hsub : ∀ i, closedBall (c i) (r i) ⊆ closedBall 0 L)
    {v : ℂ → ℝ} (hv : ContDiffOn ℝ 1 v (⋃ i, closedBall (c i) (r i))ᶜ)
    (henergy : IntegrableOn (euclideanGradientEnergy v) (⋃ i, closedBall (c i) (r i))ᶜ)
    (hcluster : ∀ i p q u w, p ∈ closedBall (c i) (r i) → q ∈ closedBall (c i) (r i) →
      MapClusterPt u (𝓝[(⋃ j, closedBall (c j) (r j))ᶜ] p) v →
      MapClusterPt w (𝓝[(⋃ j, closedBall (c j) (r j))ᶜ] q) v → |w - u| ≤ A i)
    {J : Set ℝ} (hJ : MeasurableSet J)
    (hcross : ∀ x ∈ J, ∃ a b : ℝ, a < b ∧
      verticalLine x a ∈ (⋃ i, closedBall (c i) (r i))ᶜ ∧
      verticalLine x b ∈ (⋃ i, closedBall (c i) (r i))ᶜ ∧
      verticalLine x a ∈ closedBall 0 L ∧ verticalLine x b ∈ closedBall 0 L ∧
      v (verticalLine x a) = 0 ∧ v (verticalLine x b) = 1) :
    (volume J).toReal ≤ Real.sqrt Real.pi * L * Real.sqrt
      (∫ z in (⋃ i, closedBall (c i) (r i))ᶜ, euclideanGradientEnergy v z) +
      2 * L * Real.sqrt (∑ i, A i ^ 2) := by
  let U := (⋃ i, closedBall (c i) (r i))ᶜ
  let V := (⋃ i, closedBall (axisSwap (c i)) (r i))ᶜ
  have hU : IsOpen U := (isClosed_iUnion_of_finite fun _ => isClosed_closedBall).isOpen_compl
  have hVU : V = axisSwap ⁻¹' U := by
    simp only [V, U, preimage_compl, preimage_iUnion, axisSwap_preimage_closedBall]
  have hV : IsOpen V := hVU ▸ hU.preimage axisSwap.continuous
  have hvV : ContDiffOn ℝ 1 (v ∘ axisSwap) V := by
    rw [hVU]
    exact hv.comp axisSwap.toContinuousLinearEquiv.contDiff.contDiffOn (fun _ hx => hx)
  obtain ⟨hiV, heV⟩ := integral_energy_axisSwap hU hv henergy
  rw [← hVU] at hiV heV
  have hdisjV : Pairwise (Disjoint on fun i => closedBall (axisSwap (c i)) (r i)) := by
    intro i j hij
    simpa only [axisSwap_preimage_closedBall] using (hdisj hij).preimage axisSwap
  have hsubV (i : I) : closedBall (axisSwap (c i)) (r i) ⊆ closedBall 0 L := by
    intro z hz
    have hz' : axisSwap z ∈ closedBall (c i) (r i) := by
      change z ∈ axisSwap ⁻¹' closedBall (c i) (r i)
      rwa [axisSwap_preimage_closedBall]
    have hb := hsub i hz'
    simpa only [mem_closedBall, dist_zero_right, axisSwap.norm_map] using hb
  have hclusterV : ∀ i p q u w,
      p ∈ closedBall (axisSwap (c i)) (r i) → q ∈ closedBall (axisSwap (c i)) (r i) →
      MapClusterPt u (𝓝[V] p) (v ∘ axisSwap) →
      MapClusterPt w (𝓝[V] q) (v ∘ axisSwap) → |w - u| ≤ A i := by
    intro i p q u w hp hq hu hw
    have hp' : axisSwap p ∈ closedBall (c i) (r i) := by
      change p ∈ axisSwap ⁻¹' closedBall (c i) (r i)
      rwa [axisSwap_preimage_closedBall]
    have hq' : axisSwap q ∈ closedBall (c i) (r i) := by
      change q ∈ axisSwap ⁻¹' closedBall (c i) (r i)
      rwa [axisSwap_preimage_closedBall]
    apply hcluster i _ _ u w hp' hq'
    · apply MapClusterPt.of_comp _ hu
      rw [hVU]
      exact tendsto_nhdsWithin_iff.mpr
        ⟨axisSwap.continuous.continuousAt.mono_left nhdsWithin_le_nhds, self_mem_nhdsWithin⟩
    · apply MapClusterPt.of_comp _ hw
      rw [hVU]
      exact tendsto_nhdsWithin_iff.mpr
        ⟨axisSwap.continuous.continuousAt.mono_left nhdsWithin_le_nhds, self_mem_nhdsWithin⟩
  have hcrossV : ∀ x ∈ J, ∃ a b : ℝ, a < b ∧
      a ∈ diskLineDomain (fun i => axisSwap (c i)) r x ∧
      b ∈ diskLineDomain (fun i => axisSwap (c i)) r x ∧
      horizontalLine x a ∈ closedBall 0 L ∧ horizontalLine x b ∈ closedBall 0 L ∧
      (v ∘ axisSwap) (horizontalLine x a) = 0 ∧
      (v ∘ axisSwap) (horizontalLine x b) = 1 := by
    intro x hx
    obtain ⟨a, b, hab, ha, hb, haL, hbL, ha0, hb1⟩ := hcross x hx
    have hmem (y : ℝ) : horizontalLine x y ∈ V ↔ verticalLine x y ∈ U := by
      rw [hVU]
      simp only [mem_preimage, axisSwap_horizontalLine]
    have hball (y : ℝ) : horizontalLine x y ∈ closedBall (0 : ℂ) L ↔
        verticalLine x y ∈ closedBall (0 : ℂ) L := by
      have he := axisSwap_preimage_closedBall (0 : ℂ) L
      simpa only [map_zero, mem_preimage, axisSwap_horizontalLine] using
        (Set.ext_iff.mp he (horizontalLine x y)).symm
    exact ⟨a, b, hab, (hmem a).mpr ha, (hmem b).mpr hb,
      (hball a).mpr haL, (hball b).mpr hbL,
      by simpa only [comp_apply, axisSwap_horizontalLine] using ha0,
      by simpa only [comp_apply, axisSwap_horizontalLine] using hb1⟩
  have hpay := parallel_line_payment_on_finite_disk_complement_square_norm
    (fun i => axisSwap (c i)) r A hr hA hL hdisjV hsubV hvV
    (hiV.mono_set inter_subset_left) hclusterV hJ hcrossV
  have hmono : (∫ z in V ∩ closedBall 0 L, euclideanGradientEnergy (v ∘ axisSwap) z) ≤
      ∫ z in V, euclideanGradientEnergy (v ∘ axisSwap) z :=
    setIntegral_mono_set hiV (ae_of_all _ (fun z => euclideanGradientEnergy_nonneg _ z))
      (Eventually.of_forall fun _ hz => hz.1)
  rw [heV] at hmono
  exact hpay.trans (add_le_add
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmono)
      (mul_nonneg (Real.sqrt_nonneg _) hL)) le_rfl)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_VerticalFrontierCrossings
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Crossing segments from nested bounded regions

On any vertical line meeting the inner region, the bottommost points of
the inner and outer closures lie on their frontiers. Strict containment
puts the outer point strictly below. Thus prescribed zero/one
frontier values provide the crossing segments needed by line payment.
-/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem exists_bottommost_vertical_frontier
    {U : Set ℂ} (hU : IsOpen U) (hcompact : IsCompact (closure U))
    {y : ℝ} (hne : ∃ z ∈ closure U, z.re = y) :
    ∃ x : ℝ, verticalLine y x ∈ frontier U ∧
      ∀ z ∈ closure U, z.re = y → x ≤ z.im := by
  let K := closure U ∩ {z : ℂ | z.re = y}
  have hK : IsCompact K := hcompact.inter_right (isClosed_eq Complex.continuous_re continuous_const)
  have hKne : K.Nonempty := by
    obtain ⟨z, hz, hy⟩ := hne
    exact ⟨z, hz, hy⟩
  obtain ⟨x, hx⟩ := (hK.image Complex.continuous_im).exists_isLeast (hKne.image Complex.im)
  obtain ⟨p, hp, hpx⟩ := hx.1
  have hpeq : p = verticalLine y x := by
    apply Complex.ext
    · exact hp.2
    · exact hpx
  have hxclosure : verticalLine y x ∈ closure U := hpeq ▸ hp.1
  have hmin : ∀ z ∈ closure U, z.re = y → x ≤ z.im := by
    intro z hz hy
    exact hx.2 (mem_image_of_mem _ ⟨hz, hy⟩)
  have hxnot : verticalLine y x ∉ U := by
    intro hxU
    have hpre : (verticalLine y) ⁻¹' U ∈ 𝓝 x :=
      (hU.preimage (continuous_verticalLine y)).mem_nhds hxU
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
    have hnear : x - ε / 2 ∈ ball x ε := by
      rw [mem_ball, Real.dist_eq]
      rw [show x - ε / 2 - x = -(ε / 2) by ring, abs_neg, abs_of_pos (half_pos hε)]
      linarith
    have hback : verticalLine y (x - ε / 2) ∈ U := hball hnear
    have hbound := hmin (verticalLine y (x - ε / 2)) (subset_closure hback) rfl
    change x ≤ x - ε / 2 at hbound
    linarith
  refine ⟨x, ?_, hmin⟩
  rw [frontier, hU.interior_eq]
  exact ⟨hxclosure, hxnot⟩

theorem exists_vertical_frontier_crossing
    {W U : Set ℂ} (hW : IsOpen W) (hU : IsOpen U)
    (hWcompact : IsCompact (closure W)) (hUcompact : IsCompact (closure U))
    (hWU : closure W ⊆ U) {y : ℝ} (hne : ∃ z ∈ closure W, z.re = y) :
    ∃ a b : ℝ, a < b ∧ verticalLine y a ∈ frontier U ∧
      verticalLine y b ∈ frontier W := by
  obtain ⟨b, hb, hminb⟩ := exists_bottommost_vertical_frontier hW hWcompact hne
  have hbU : verticalLine y b ∈ U := hWU (frontier_subset_closure hb)
  obtain ⟨a, ha, hmina⟩ := exists_bottommost_vertical_frontier hU hUcompact
    ⟨verticalLine y b, subset_closure hbU, rfl⟩
  refine ⟨a, b, ?_, ha, hb⟩
  have hab : a ≤ b := hmina _ (subset_closure hbU) rfl
  apply lt_of_le_of_ne hab
  intro he
  have haU : verticalLine y a ∈ U := he.symm ▸ hbU
  have hnot : verticalLine y a ∉ U := by
    simpa only [verticalLine, hU.interior_eq] using ha.2
  exact hnot haU

theorem vertical_frontier_crossings_give_values
    {W U D : Set ℂ} (hW : IsOpen W) (hU : IsOpen U)
    (hWcompact : IsCompact (closure W)) (hUcompact : IsCompact (closure U))
    (hWU : closure W ⊆ U) {L : ℝ} (hUL : closure U ⊆ closedBall 0 L)
    (hUD : frontier U ⊆ D) (hWD : frontier W ⊆ D)
    {v : ℂ → ℝ} (hzero : ∀ z ∈ frontier U, v z = 0)
    (hone : ∀ z ∈ frontier W, v z = 1) {J : Set ℝ}
    (hJ : J ⊆ Complex.re '' closure W) :
    ∀ y ∈ J, ∃ a b : ℝ, a < b ∧ verticalLine y a ∈ D ∧
      verticalLine y b ∈ D ∧ verticalLine y a ∈ closedBall 0 L ∧
      verticalLine y b ∈ closedBall 0 L ∧ v (verticalLine y a) = 0 ∧
      v (verticalLine y b) = 1 := by
  intro y hy
  obtain ⟨z, hz, hzy⟩ := hJ hy
  obtain ⟨a, b, hab, ha, hb⟩ := exists_vertical_frontier_crossing hW hU hWcompact hUcompact
    hWU ⟨z, hz, hzy⟩
  exact ⟨a, b, hab, hUD ha, hWD hb, hUL (frontier_subset_closure ha),
    hUL (subset_closure (hWU (frontier_subset_closure hb))), hzero _ ha, hone _ hb⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_VerticalRetainedCrossings
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retained target contours give crossing segments in the vertical direction. -/

open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem eventually_vertical_crossings_of_anchored_jordan_limits
    (H K : ℂ ≃ₜ ℂ) (Hn Kn : ℕ → ℂ ≃ₜ ℂ)
    (γ δ : Circle → ℂ) (γn δn : ℕ → Circle → ℂ)
    (hγ : Continuous γ) (hδ : Continuous δ)
    (hγfront : range γ = frontier (jordanInterior H))
    (hδfront : range δ = frontier (jordanInterior K))
    (hγn : ∀ᶠ n in atTop, range (γn n) = frontier (jordanInterior (Hn n)))
    (hδn : ∀ᶠ n in atTop, range (δn n) = frontier (jordanInterior (Kn n)))
    (hγlim : TendstoUniformly γn γ atTop) (hδlim : TendstoUniformly δn δ atTop)
    (hHK : closure (jordanInterior H) ⊆ jordanInterior K)
    {z w : ℂ} {zn wn : ℕ → ℂ}
    (hz : z ∈ jordanInterior H) (hw : w ∈ jordanInterior K)
    (hzn : Tendsto zn atTop (𝓝 z)) (hwn : Tendsto wn atTop (𝓝 w))
    (hzanchor : ∀ᶠ n in atTop, zn n ∈ jordanInterior (Hn n))
    (hwanchor : ∀ᶠ n in atTop, wn n ∈ jordanInterior (Kn n))
    {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ jordanInterior H)
    (D : ℕ → Set ℂ) (v : ℕ → ℂ → ℝ) {L : ℝ}
    (hbound : ∀ᶠ n in atTop, closure (jordanInterior (Kn n)) ⊆ closedBall 0 L)
    (hboundary : ∀ᶠ n in atTop, frontier (jordanInterior (Hn n)) ⊆ D n ∧
      frontier (jordanInterior (Kn n)) ⊆ D n)
    (hvalues : ∀ᶠ n in atTop,
      (∀ p ∈ frontier (jordanInterior (Kn n)), v n p = 0) ∧
      (∀ p ∈ frontier (jordanInterior (Hn n)), v n p = 1))
    {J : Set ℝ} (hJ : J ⊆ Complex.re '' C) :
    ∀ᶠ n in atTop, ∀ y ∈ J, ∃ a b : ℝ, a < b ∧ verticalLine y a ∈ D n ∧
      verticalLine y b ∈ D n ∧ verticalLine y a ∈ closedBall 0 L ∧
      verticalLine y b ∈ closedBall 0 L ∧ v n (verticalLine y a) = 0 ∧
      v n (verticalLine y b) = 1 := by
  have hretain := eventually_compact_subset_jordanInterior_of_anchor H Hn γ γn
    hγ hγfront hγn hγlim hz hzn hzanchor hC hCH
  have hnested := eventually_nested_jordanInteriors_of_anchor H K Hn Kn γ δ γn δn
    hγ hδ hγfront hδfront hγn hδn hγlim hδlim hHK hw hwn hwanchor
  filter_upwards [hretain, hnested, hbound, hboundary, hvalues] with n hnC hnested hnB hnD hnv
  apply vertical_frontier_crossings_give_values
    (jordanInterior_isOpen (Hn n)) (jordanInterior_isOpen (Kn n))
    (isCompact_closure_jordanInterior (Hn n)) (isCompact_closure_jordanInterior (Kn n))
    hnested hnB hnD.2 hnD.1 hnv.1 hnv.2
  exact hJ.trans (image_mono (hnC.trans subset_closure))

theorem eventually_vertical_crossings_of_retained_test
    (hsch : PlanarSchoenflies)
    {I : ℕ → Type*} [∀ n, Finite (I n)] (T : (n : ℕ) → I n → ℂ ≃ₜ ℂ)
    (hTd : ∀ n, Pairwise (Disjoint on fun i => closure (jordanInterior (T n i))))
    (f fi : ℕ → Sphere → Sphere) (V : ℕ → Set Sphere)
    (heq : ∀ n, IsSmoothSphereEquivalence (f n) (fi n) (openCompletedRegion (T n)) (V n))
    (hV : ∀ n, IsOpen (V n)) (hfix : ∀ n, f n OnePoint.infty = OnePoint.infty)
    {G : Set Sphere} (hG : IsOpen G)
    (A B : SmoothJordanCore G) (i : Fin A.count) (j : Fin B.count)
    (hretA : ∀ᶠ n in atTop, A.carrier ⊆ openCompletedRegion (T n))
    (hretB : ∀ᶠ n in atTop, B.carrier ⊆ openCompletedRegion (T n))
    (hpoint : ∀ q ∈ G, ∀ᶠ n in atTop, q ∈ openCompletedRegion (T n))
    (F : ℂ → ℂ) (hF : ContinuousOn F (((↑) : ℂ → Sphere) ⁻¹' G))
    (hlim : TendstoLocallyUniformlyOn (fun n (z : ℂ) => finiteCoord (f n (z : Sphere)))
      F atTop (((↑) : ℂ → Sphere) ⁻¹' G))
    (H K : ℂ ≃ₜ ℂ)
    (hH : extendAtInfinity F '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (A.disk i))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior H))
    (hK : extendAtInfinity F '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (B.disk j))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior K))
    (hsideH : extendAtInfinity F '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (A.disk i))) =
      (extendAtInfinity F '' G) ∩ (((↑) : ℂ → Sphere) '' jordanInterior H))
    (hsideK : extendAtInfinity F '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (B.disk j))) =
      (extendAtInfinity F '' G) ∩ (((↑) : ℂ → Sphere) '' jordanInterior K))
    (hHK : closure (jordanInterior H) ⊆ jordanInterior K)
    {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ jordanInterior H)
    {L : ℝ} (hKL : closure (jordanInterior K) ⊆ ball 0 L)
    (w : ℕ → Sphere → ℝ)
    (hvalues : ∀ᶠ n in atTop,
      (∀ z ∈ frontier (jordanInterior (A.disk i)), w n z = 1) ∧
      (∀ z ∈ frontier (jordanInterior (B.disk j)), w n z = 0)) :
    ∀ᶠ n in atTop, ∀ y ∈ Complex.re '' C, ∃ a b : ℝ, a < b ∧
      (verticalLine y a : Sphere) ∈ V n ∧ (verticalLine y b : Sphere) ∈ V n ∧
      verticalLine y a ∈ closedBall 0 L ∧ verticalLine y b ∈ closedBall 0 L ∧
      w n (fi n (verticalLine y a)) = 0 ∧ w n (fi n (verticalLine y b)) = 1 := by
  obtain ⟨Hn, q, _, _, hq, hγ, hfront, hγlim, hqlim, hqa, hHb, hHnf⟩ :=
    exists_anchored_retained_jordan_models hsch T hTd f fi V heq hV hfix hG A i
      hretA hpoint F hF hlim H hH hsideH
  obtain ⟨Kn, p, _, _, hp, hδ, hfrontK, hδlim, hplim, hpa, hKb, hKnf⟩ :=
    exists_anchored_retained_jordan_models hsch T hTd f fi V heq hV hfix hG B j
      hretB hpoint F hF hlim K hK hsideK
  have hbound : ∀ᶠ n in atTop, closure (jordanInterior (Kn n)) ⊆ closedBall 0 L :=
    (eventually_jordan_fill_subset_open K Kn _ _ hδ hfrontK hKnf hδlim isOpen_ball hKL).mono
      (fun _ hn => hn.trans ball_subset_closedBall)
  have hdata : ∀ᶠ n in atTop,
      (frontier (jordanInterior (Hn n)) ⊆ ((↑) : ℂ → Sphere) ⁻¹' V n ∧
       frontier (jordanInterior (Kn n)) ⊆ ((↑) : ℂ → Sphere) ⁻¹' V n) ∧
      ((∀ z ∈ frontier (jordanInterior (Kn n)), w n (fi n z) = 0) ∧
       (∀ z ∈ frontier (jordanInterior (Hn n)), w n (fi n z) = 1)) := by
    filter_upwards [hretA, hretB, hHb, hKb, hvalues] with n hnA hnB hnH hnK hnv
    have ha := values_on_image_jordan_boundary (heq n)
      ((A.inDomain hnA).boundary_subset_domain i) hnH (w n) hnv.1
    have hb := values_on_image_jordan_boundary (heq n)
      ((B.inDomain hnB).boundary_subset_domain j) hnK (w n) hnv.2
    exact ⟨⟨ha.1, hb.1⟩, hb.2, ha.2⟩
  exact eventually_vertical_crossings_of_anchored_jordan_limits H K Hn Kn
    _ _ _ _ hγ hδ hfront hfrontK hHnf hKnf hγlim hδlim hHK hq hp hqlim hplim hqa hpa
    hC hCH (fun n => ((↑) : ℂ → Sphere) ⁻¹' V n)
    (fun n z => w n (fi n z)) hbound (hdata.mono fun _ h => h.1)
    (hdata.mono fun _ h => h.2) (Subset.refl _)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_VerticalRealRetention
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFiniteElemEdgeSetOfFinite _root_.Graph.instFiniteElemVertexSetOfFinite _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual retained real tests give vertical target crossing segments. -/

open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer.RealModelExhaustion
variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  (M : RealModelExhaustion d O ε)

theorem eventually_vertical_test_crossings
    (hsch : PlanarSchoenflies) (hG : IsOpen G)
    (r : ℕ → ℕ) (hr : Tendsto r atTop atTop)
    (F : ℂ → ℂ) (hF : ContinuousOn F (((↑) : ℂ → Sphere) ⁻¹' G))
    (hlim : TendstoLocallyUniformlyOn (fun n (z : ℂ) =>
      finiteCoord ((M.stages (r n)).forward (z : Sphere))) F
      atTop (((↑) : ℂ → Sphere) ⁻¹' G))
    (A B : SmoothJordanCore G) (i : Fin A.count) (j : Fin B.count) (l : ℕ)
    (hOne : ∀ z ∈ frontier (jordanInterior (A.disk i)),
      d.physical l (Complex.equivRealProdCLM z) = 1)
    (hZero : ∀ z ∈ frontier (jordanInterior (B.disk j)),
      d.physical l (Complex.equivRealProdCLM z) = 0)
    (H K : ℂ ≃ₜ ℂ)
    (hH : extendAtInfinity F '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (A.disk i))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior H))
    (hK : extendAtInfinity F '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (B.disk j))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior K))
    (hsideH : extendAtInfinity F '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (A.disk i))) =
      (extendAtInfinity F '' G) ∩ (((↑) : ℂ → Sphere) '' jordanInterior H))
    (hsideK : extendAtInfinity F '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (B.disk j))) =
      (extendAtInfinity F '' G) ∩ (((↑) : ℂ → Sphere) '' jordanInterior K))
    (hHK : closure (jordanInterior H) ⊆ jordanInterior K)
    {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ jordanInterior H)
    {L : ℝ} (hKL : closure (jordanInterior K) ⊆ ball 0 L) :
    ∀ᶠ n in atTop, ∀ y ∈ Complex.re '' C, ∃ a b : ℝ, a < b ∧
      (verticalLine y a : Sphere) ∈ (M.stages (r n)).domain ∧
      (verticalLine y b : Sphere) ∈ (M.stages (r n)).domain ∧
      verticalLine y a ∈ closedBall 0 L ∧ verticalLine y b ∈ closedBall 0 L ∧
      sphereRealFunction ((M.stages (r n)).functions (prefixIndex l (r n)))
        ((M.stages (r n)).inverse (verticalLine y a)) = 0 ∧
      sphereRealFunction ((M.stages (r n)).functions (prefixIndex l (r n)))
        ((M.stages (r n)).inverse (verticalLine y b)) = 1 := by
  let _ : ∀ n, Fintype (M.stages (r n)).indices :=
    fun n => (M.stages (r n)).finite_indices.fintype
  apply eventually_vertical_crossings_of_retained_test hsch
    (fun n => (M.stages (r n)).terminals.H)
    (fun n => (M.stages (r n)).terminals.disjoint_closures)
    (fun n => (M.stages (r n)).forward) (fun n => (M.stages (r n)).inverse)
    (fun n => (M.stages (r n)).domain) (fun n => (M.stages (r n)).equivalence)
    (fun n => (M.stages (r n)).circle_domain.1) (fun n => (M.stages (r n)).principal.1)
    hG A B i j (hr (M.eventually_model_contains A.isCompact A.subset))
    (hr (M.eventually_model_contains B.isCompact B.subset)) ?_ F hF hlim H K
    hH hK hsideH hsideK hHK hC hCH hKL
    (fun n => sphereRealFunction ((M.stages (r n)).functions (prefixIndex l (r n)))) ?_
  · intro q hq
    exact hr ((M.eventually_model_contains isCompact_singleton (singleton_subset_iff.mpr hq)).mono
      (fun _ hn => hn (mem_singleton q)))
  · have ha := hr (M.eventually_test_eq A.isCompact A.subset l)
    have hb := hr (M.eventually_test_eq B.isCompact B.subset l)
    filter_upwards [ha, hb] with n hnA hnB
    constructor
    · intro z hz
      simpa only [sphereRealFunction, finiteCoord_coe] using
        (hnA z ((A.inDomain (Subset.refl _)).boundary_subset_domain i ⟨z, hz, rfl⟩)).trans (hOne z hz)
    · intro z hz
      simpa only [sphereRealFunction, finiteCoord_coe] using
        (hnB z ((B.inDomain (Subset.refl _)).boundary_subset_domain j ⟨z, hz, rfl⟩)).trans (hZero z hz)

end CircleDomainRigidity.FiniteTransfer.RealModelExhaustion

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_VerticalTerminalPayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Vertical-line payment for an actual normalized finite model

The round holes are taken from the model's terminal assignment. Their
cluster costs are derived from the real function on the physical terminal
boundaries. This joins line payment to the finite-transfer construction.
-/

open Set Function Filter Metric MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem TerminalComponentAssignment.vertical_line_payment
    {I : Type*} [Fintype I] {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (hV : IsCircleDomain V) (hinf : OnePoint.infty ∈ V)
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : Vᶜ ⊆ ((↑) : ℂ → Sphere) '' closedBall (0 : ℂ) L)
    (w : (ℝ × ℝ) → ℝ) {O : Set (ℝ × ℝ)} (hO : IsOpen O)
    (hTO : ∀ i, frontier (realJordanInterior (T i)) ⊆ O) (hw : ContinuousOn w O)
    (hv : ContDiffOn ℝ 1 ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere))
      (((↑) : ℂ → Sphere) ⁻¹' V))
    (henergy : IntegrableOn
      (euclideanGradientEnergy ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere)))
      (((↑) : ℂ → Sphere) ⁻¹' V))
    {J : Set ℝ} (hJ : MeasurableSet J)
    (hcross : ∀ y ∈ J, ∃ s t : ℝ, s < t ∧
      (verticalLine y s : Sphere) ∈ V ∧ (verticalLine y t : Sphere) ∈ V ∧
      verticalLine y s ∈ closedBall 0 L ∧ verticalLine y t ∈ closedBall 0 L ∧
      sphereRealFunction w (fi (verticalLine y s)) = 0 ∧
      sphereRealFunction w (fi (verticalLine y t)) = 1) :
    (volume J).toReal ≤ Real.sqrt Real.pi * L * Real.sqrt
      (∫ z in (((↑) : ℂ → Sphere) ⁻¹' V),
        euclideanGradientEnergy ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere)) z) +
      2 * L * Real.sqrt (∑ i, Metric.diam (w '' frontier (realJordanInterior (T i))) ^ 2) := by
  obtain ⟨c, r, hr, he, hd, hU⟩ := a.exists_disk_coordinates hV hinf
  let A : I → ℝ := fun i => Metric.diam (w '' frontier (realJordanInterior (T i)))
  have hsub : ∀ i, closedBall (c i) (r i) ⊆ closedBall (0 : ℂ) L :=
    fun i => terminal_disk_subset_bound (he i) hbound
  have hcl : ∀ i p q u v, p ∈ closedBall (c i) (r i) → q ∈ closedBall (c i) (r i) →
      MapClusterPt u (𝓝[(⋃ j, closedBall (c j) (r j))ᶜ] p)
        ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere)) →
      MapClusterPt v (𝓝[(⋃ j, closedBall (c j) (r j))ᶜ] q)
        ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere)) → |v - u| ≤ A i := by
    intro i p q u v hp hq hu hv
    apply a.real_planar_cluster_gap_le hf i w hO (hTO i) hw
    · rw [he i]
      exact mem_image_of_mem _ hp
    · rw [he i]
      exact mem_image_of_mem _ hq
    · simpa only [hU] using hu
    · simpa only [hU] using hv
  have hv' : ContDiffOn ℝ 1 ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere))
      (⋃ j, closedBall (c j) (r j))ᶜ := by simpa only [hU] using hv
  have he' : IntegrableOn
      (euclideanGradientEnergy ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere)))
      ((⋃ j, closedBall (c j) (r j))ᶜ) := by simpa only [hU] using henergy
  rw [hU]
  apply vertical_line_payment_on_finite_disk_complement c r A hr
    (fun _ => Metric.diam_nonneg) hL hd hsub hv' he' hcl hJ
  intro y hy
  obtain ⟨s, t, hst, hsV, htV, hsB, htB, hs0, ht1⟩ := hcross y hy
  refine ⟨s, t, hst, ?_, ?_, hsB, htB, hs0, ht1⟩
  · change verticalLine y s ∈ (⋃ j, closedBall (c j) (r j))ᶜ
    rw [← hU]
    exact hsV
  · change verticalLine y t ∈ (⋃ j, closedBall (c j) (r j))ᶜ
    rw [← hU]
    exact htV

theorem TerminalComponentAssignment.vertical_line_payment_source_energy
    {I : Type*} [Fintype I] {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (heq : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (hV : IsCircleDomain V) (hinf : OnePoint.infty ∈ openCompletedRegion T)
    (hfix : f OnePoint.infty = OnePoint.infty)
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : Vᶜ ⊆ ((↑) : ℂ → Sphere) '' closedBall (0 : ℂ) L)
    (w : (ℝ × ℝ) → ℝ)
    (hw : ContDiffOn ℝ ∞ w (realChartDomain (openCompletedRegion T)))
    {O : Set (ℝ × ℝ)} (hO : IsOpen O)
    (hTO : ∀ i, frontier (realJordanInterior (T i)) ⊆ O) (hwO : ContinuousOn w O)
    {g : (ℝ × ℝ) → PlanarMetric}
    (hmetric : ∀ p ∈ openCompletedRegion T, IsMetricConformalAt g f p)
    (hg : ∀ x ∈ realChartDomain (openCompletedRegion T), (g x).PosDef)
    (hi : IntegrableOn (gradientEnergy w g) (realChartDomain (openCompletedRegion T)))
    {J : Set ℝ} (hJ : MeasurableSet J)
    (hcross : ∀ x ∈ J, ∃ s t : ℝ, s < t ∧
      (verticalLine x s : Sphere) ∈ V ∧ (verticalLine x t : Sphere) ∈ V ∧
      verticalLine x s ∈ closedBall 0 L ∧ verticalLine x t ∈ closedBall 0 L ∧
      sphereRealFunction w (fi (verticalLine x s)) = 0 ∧
      sphereRealFunction w (fi (verticalLine x t)) = 1) :
    (volume J).toReal ≤ Real.sqrt Real.pi * L * Real.sqrt
      (∫ x in realChartDomain (openCompletedRegion T), gradientEnergy w g x) +
      2 * L * Real.sqrt (∑ i, Metric.diam (w '' frontier (realJordanInterior (T i))) ^ 2) := by
  obtain ⟨hv, hfull, he⟩ := transported_real_energy heq (isOpen_openCompletedRegion T)
    hV.1 hinf hfix w hw hmetric hg hi
  have hp := a.vertical_line_payment heq hV (heq.infty_mem_target hinf hfix)
    hL hbound w hO hTO hwO hv hfull hJ hcross
  rwa [he] at hp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_VerticalLimitPayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.metricBeltramiCoefficient_scalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Limiting payment by source energy and band widths

For a fixed barrier the transfer errors vanish while the original source
energy and band norm remain. This is the limit required before choosing
successively smaller barriers in the unmarked-end argument.
-/

open Set Function Filter Metric MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem limiting_vertical_terminal_line_payment
    {I : ℕ → Type*} [∀ n, Fintype (I n)]
    (T : (n : ℕ) → I n → ℂ ≃ₜ ℂ) (f fi : ℕ → Sphere → Sphere) (V : ℕ → Set Sphere)
    (a : ∀ n, TerminalComponentAssignment (T n) (f n) (V n))
    (heq : ∀ n, IsSmoothSphereEquivalence (f n) (fi n) (openCompletedRegion (T n)) (V n))
    (hV : ∀ n, IsCircleDomain (V n))
    (hinf : ∀ n, OnePoint.infty ∈ openCompletedRegion (T n))
    (hfix : ∀ n, f n OnePoint.infty = OnePoint.infty)
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ n, (V n)ᶜ ⊆ ((↑) : ℂ → Sphere) '' closedBall (0 : ℂ) L)
    (w : ℕ → (ℝ × ℝ) → ℝ)
    (hw : ∀ n, ContDiffOn ℝ ∞ (w n) (realChartDomain (openCompletedRegion (T n))))
    (O : ℕ → Set (ℝ × ℝ)) (hO : ∀ n, IsOpen (O n))
    (hTO : ∀ n i, frontier (realJordanInterior (T n i)) ⊆ O n)
    (hwO : ∀ n, ContinuousOn (w n) (O n))
    (g : ℕ → (ℝ × ℝ) → PlanarMetric)
    (hmetric : ∀ n p, p ∈ openCompletedRegion (T n) → IsMetricConformalAt (g n) (f n) p)
    (hg : ∀ n x, x ∈ realChartDomain (openCompletedRegion (T n)) → (g n x).PosDef)
    (hi : ∀ n, IntegrableOn (gradientEnergy (w n) (g n))
      (realChartDomain (openCompletedRegion (T n))))
    (band : (n : ℕ) → I n → ℝ) (hband : ∀ n i, 0 ≤ band n i)
    {E B : ℝ} (hE : 0 ≤ E)
    (hbandnorm : ∀ n, Real.sqrt (∑ i, band n i ^ 2) ≤ B)
    (e δ : ℕ → ℝ) (he : Tendsto e atTop (𝓝 (E ^ 2))) (hδ : Tendsto δ atTop (𝓝 0))
    (henergy : ∀ᶠ n in atTop,
      (∫ x in realChartDomain (openCompletedRegion (T n)), gradientEnergy (w n) (g n) x) ≤ e n)
    (hexcess : ∀ᶠ n in atTop, Real.sqrt (∑ i,
      max (diam (w n '' frontier (realJordanInterior (T n i))) - band n i) 0 ^ 2) ≤ δ n)
    {J : Set ℝ} (hJ : MeasurableSet J)
    (hcross : ∀ᶠ n in atTop, ∀ y ∈ J, ∃ s t : ℝ, s < t ∧
      (verticalLine y s : Sphere) ∈ V n ∧ (verticalLine y t : Sphere) ∈ V n ∧
      verticalLine y s ∈ closedBall 0 L ∧ verticalLine y t ∈ closedBall 0 L ∧
      sphereRealFunction (w n) (fi n (verticalLine y s)) = 0 ∧
      sphereRealFunction (w n) (fi n (verticalLine y t)) = 1) :
    (volume J).toReal ≤ Real.sqrt Real.pi * L * E + 2 * L * B := by
  have hpay : ∀ᶠ n in atTop, (volume J).toReal ≤
      Real.sqrt Real.pi * L * Real.sqrt (e n) + 2 * L * (B + δ n) := by
    filter_upwards [hcross, henergy, hexcess] with n hn hnE hnA
    have hp := (a n).vertical_line_payment_source_energy (heq n) (hV n)
      (hinf n) (hfix n) hL (hbound n) (w n) (hw n) (hO n) (hTO n) (hwO n)
      (hmetric n) (hg n) (hi n) hJ hn
    have hcost := sqrt_sum_sq_le_of_excess_budget
      (fun i => diam (w n '' frontier (realJordanInterior (T n i)))) (band n)
      (fun _ => diam_nonneg) (hband n) (hbandnorm n) hnA
    exact hp.trans (add_le_add
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hnE)
        (mul_nonneg (Real.sqrt_nonneg _) hL))
      (mul_le_mul_of_nonneg_left hcost (mul_nonneg (by norm_num) hL)))
  have hs : Tendsto (fun n => Real.sqrt (e n)) atTop (𝓝 E) := by
    simpa only [Function.comp_def, Real.sqrt_sq hE] using
      Real.continuous_sqrt.continuousAt.tendsto.comp he
  have ht : Tendsto (fun n => Real.sqrt Real.pi * L * Real.sqrt (e n) +
      2 * L * (B + δ n)) atTop (𝓝 (Real.sqrt Real.pi * L * E + 2 * L * B)) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.mul hs).add
        (tendsto_const_nhds.mul (tendsto_const_nhds.add hδ))
  exact ge_of_tendsto ht hpay

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_VerticalRealSequence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFiniteElemEdgeSetOfFinite _root_.Graph.instFiniteElemVertexSetOfFinite _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.metricBeltramiCoefficient_scalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical payment along cofinal subsequences of actual real models. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer
namespace RealModelExhaustion


variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  (M : RealModelExhaustion d O ε)

theorem limiting_vertical_line_payment
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (harea : ExteriorCoefficientAreaTheorem)
    (hε : Tendsto ε atTop (𝓝 0)) (r : ℕ → ℕ) (hr : Tendsto r atTop atTop) (l : ℕ)
    {L : ℝ} (hL : 3 * M.radius ≤ L)
    {J : Set ℝ} (hJ : MeasurableSet J)
    (hcross : ∀ᶠ n in atTop, ∀ y ∈ J, ∃ s t : ℝ, s < t ∧
      (verticalLine y s : Sphere) ∈ (M.stages (r n)).domain ∧
      (verticalLine y t : Sphere) ∈ (M.stages (r n)).domain ∧
      verticalLine y s ∈ closedBall 0 L ∧
      verticalLine y t ∈ closedBall 0 L ∧
      sphereRealFunction ((M.stages (r n)).functions (prefixIndex l (r n)))
        ((M.stages (r n)).inverse (verticalLine y s)) = 0 ∧
      sphereRealFunction ((M.stages (r n)).functions (prefixIndex l (r n)))
        ((M.stages (r n)).inverse (verticalLine y t)) = 1) :
    (volume J).toReal ≤ Real.sqrt Real.pi * L * Real.sqrt
        (∫ x in realChartDomain G,
          gradientEnergy (d.physical l) (fun z => sphericalMetricFactor z • 1) x) +
      2 * L * Real.sqrt (∑' s, (d.upper l s - d.lower l s) ^ 2) := by
  classical
  let _ : ∀ n, Fintype (M.stages (r n)).indices := fun n => (M.stages (r n)).finite_indices.fintype
  let T (n : ℕ) := (M.stages (r n)).terminals.H
  let f (n : ℕ) := (M.stages (r n)).forward
  let fi (n : ℕ) := (M.stages (r n)).inverse
  let V (n : ℕ) := (M.stages (r n)).domain
  let w (n : ℕ) := (M.stages (r n)).functions (prefixIndex l (r n))
  let E := ∫ x in realChartDomain G,
    gradientEnergy (d.physical l) (fun z => sphericalMetricFactor z • 1) x
  have hE : 0 ≤ E := integral_nonneg (fun x => by
    rw [gradientEnergy_spherical]
    positivity)
  have hbound (n : ℕ) : (V n)ᶜ ⊆ ((↑) : ℂ → Sphere) '' closedBall 0 L := by
    have h := (normalized_model_uniform_bound harea (M.stages (r n)).equivalence
      (M.stages (r n)).circle_domain.1 M.radius_pos
      ((M.exterior_core (r n)).trans (M.core_model (r n)))
      ((M.core_conformal (r n)).mono
        ((compl_subset_compl.mpr (image_mono ball_subset_closedBall)).trans (M.exterior_core (r n))))
      (M.stages (r n)).principal).1
    exact fun p hp => image_mono (closedBall_subset_closedBall hL) (h p hp)
  have ha (n : ℕ) : Nonempty (TerminalComponentAssignment (T n) (f n) (V n)) :=
    exists_terminal_component_assignment hsard hsch (T n)
      (M.stages (r n)).terminals.disjoint_closures (M.stages (r n)).equivalence
      (M.stages (r n)).circle_domain.1 (M.stages (r n)).principal.1
  let a (n : ℕ) := Classical.choice (ha n)
  apply limiting_vertical_terminal_line_payment T f fi V a
    (fun n => (M.stages (r n)).equivalence) (fun n => (M.stages (r n)).circle_domain)
    (fun n => (M.stages (r n)).source_infty) (fun n => (M.stages (r n)).principal.1)
    ((mul_nonneg (by norm_num) M.radius_pos.le).trans hL) hbound w
    (fun n => (M.stages (r n)).functions_smooth_source (prefixIndex l (r n)))
    (fun n => (M.stages (r n)).extension) (fun n => (M.stages (r n)).extension_open)
    (fun n => (M.stages (r n)).terminal_frontier_extension)
    (fun n => ((M.stages (r n)).functions_smooth (prefixIndex l (r n))).continuousOn)
    (fun n => (M.stages (r n)).metric) (fun n => (M.stages (r n)).metric_conformal)
    (fun n x _ => (M.stages (r n)).metric_pos x)
    (fun n => (M.stages (r n)).functions_integrable_source (prefixIndex l (r n)))
    (fun n s => d.upper l s - d.lower l s) (fun _ s => d.width_nonneg l s)
    (Real.sqrt_nonneg E) (fun n =>
      finite_label_band_norm_le (fun s : (M.stages (r n)).indices => (s : S))
        Subtype.val_injective (fun s => d.upper l s - d.lower l s) (d.width_summable l))
    (fun n => E + ε (r n)) (fun n => ε (r n)) ?_ (hε.comp hr) ?_ ?_ hJ hcross
  · simpa only [Real.sq_sqrt hE, add_zero, Function.comp_def] using
      tendsto_const_nhds.add (hε.comp hr)
  · filter_upwards [hr (prefixIndex_eq l)] with n hn
    change (prefixIndex l (r n)).val = l at hn
    have h := (M.stages (r n)).source_energy_lt (prefixIndex l (r n))
    simpa only [CountableRealCoordinates.Stage, hn] using h.le
  · filter_upwards [hr (prefixIndex_eq l)] with n hn
    change (prefixIndex l (r n)).val = l at hn
    have h := (M.stages (r n)).excess (prefixIndex l (r n))
    simpa only [terminalOscillation, hn, tsum_fintype] using h.le

end RealModelExhaustion

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RealBarrierCollapse
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.metricBeltramiCoefficient_scalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vanishing retained real barriers collapse compact target continua. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem RealModelExhaustion.real_projection_payment
    {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
    (M : RealModelExhaustion d O ε)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (harea : ExteriorCoefficientAreaTheorem)
    (hG : IsOpen G) (hε : Tendsto ε atTop (𝓝 0))
    (r : ℕ → ℕ) (hr : Tendsto r atTop atTop)
    (F : ℂ → ℂ) (hF : ContinuousOn F (((↑) : ℂ → Sphere) ⁻¹' G))
    (hlim : TendstoLocallyUniformlyOn (fun n (z : ℂ) =>
      finiteCoord ((M.stages (r n)).forward (z : Sphere))) F
      atTop (((↑) : ℂ → Sphere) ⁻¹' G))
    {l : ℕ} (B : RetainedRealBarrier d F l)
    {C : Set ℂ} (hC : IsCompact C) (hCB : C ⊆ jordanInterior B.target_inner)
    {L : ℝ} (hL : 3 * M.radius ≤ L)
    (hBL : closure (jordanInterior B.target_outer) ⊆ ball 0 L) :
    (volume (Complex.re '' C)).toReal ≤ Real.sqrt Real.pi * L * Real.sqrt
        (∫ x in realChartDomain G,
          gradientEnergy (d.physical l) (fun z => sphericalMetricFactor z • 1) x) +
      2 * L * Real.sqrt (∑' s, (d.upper l s - d.lower l s) ^ 2) := by
  apply M.limiting_vertical_line_payment hsard hsch harea hε r hr l hL
    (hC.image Complex.continuous_re).measurableSet
  exact M.eventually_vertical_test_crossings hsch hG r hr F hF hlim B.inner B.outer
    B.inner_index B.outer_index l B.value_one B.value_zero B.target_inner B.target_outer
    B.inner_image B.outer_image B.inner_side B.outer_side B.nested hC hCB hBL

theorem RealModelExhaustion.real_projection_zero_of_vanishing_barriers
    {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
    (M : RealModelExhaustion d O ε)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (harea : ExteriorCoefficientAreaTheorem)
    (hG : IsOpen G) (hε : Tendsto ε atTop (𝓝 0))
    (r : ℕ → ℕ) (hr : Tendsto r atTop atTop)
    (F : ℂ → ℂ) (hF : ContinuousOn F (((↑) : ℂ → Sphere) ⁻¹' G))
    (hlim : TendstoLocallyUniformlyOn (fun n (z : ℂ) =>
      finiteCoord ((M.stages (r n)).forward (z : Sphere))) F
      atTop (((↑) : ℂ → Sphere) ⁻¹' G))
    (labels : ℕ → ℕ) (B : ∀ k, RetainedRealBarrier d F (labels k))
    {C : Set ℂ} (hC : IsCompact C)
    (hCB : ∀ k, C ⊆ jordanInterior (B k).target_inner)
    {L : ℝ} (hL : 3 * M.radius ≤ L)
    (hBL : ∀ k, closure (jordanInterior (B k).target_outer) ⊆ ball 0 L)
    (hsmall : Tendsto (fun k =>
      Real.sqrt (∫ x in realChartDomain G,
        gradientEnergy (d.physical (labels k)) (fun z => sphericalMetricFactor z • 1) x) +
      Real.sqrt (∑' s, (d.upper (labels k) s - d.lower (labels k) s) ^ 2))
      atTop (𝓝 0)) : volume (Complex.re '' C) = 0 := by
  have hL0 : 0 ≤ L := (mul_nonneg (by norm_num) M.radius_pos.le).trans hL
  have hpay (k : ℕ) := M.real_projection_payment hsard hsch harea hG hε r hr F hF hlim
    (B k) hC (hCB k) hL (hBL k)
  have hbound : ∀ k, (volume (Complex.re '' C)).toReal ≤
      ((Real.sqrt Real.pi + 2) * L) *
        (Real.sqrt (∫ x in realChartDomain G,
          gradientEnergy (d.physical (labels k)) (fun z => sphericalMetricFactor z • 1) x) +
        Real.sqrt (∑' s, (d.upper (labels k) s - d.lower (labels k) s) ^ 2)) := by
    intro k
    apply (hpay k).trans
    have ha := Real.sqrt_nonneg (∫ x in realChartDomain G,
      gradientEnergy (d.physical (labels k)) (fun z => sphericalMetricFactor z • 1) x)
    have hb := Real.sqrt_nonneg (∑' s, (d.upper (labels k) s - d.lower (labels k) s) ^ 2)
    have hp := Real.sqrt_nonneg Real.pi
    nlinarith [mul_nonneg hL0 ha, mul_nonneg hL0 hb, mul_nonneg hp (mul_nonneg hL0 hb)]
  have hz : (volume (Complex.re '' C)).toReal = 0 := by
    apply le_antisymm _ ENNReal.toReal_nonneg
    have ht := hsmall.const_mul ((Real.sqrt Real.pi + 2) * L)
    rw [mul_zero] at ht
    exact ge_of_tendsto ht (Eventually.of_forall hbound)
  have hfinite : volume (Complex.re '' C) ≠ ⊤ :=
    (hC.image Complex.continuous_re).measure_ne_top
  simpa only [ENNReal.toReal_eq_zero_iff, hfinite, or_false] using hz

theorem RealModelExhaustion.subsingleton_of_vanishing_barriers
    {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
    (M : RealModelExhaustion d O ε)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (harea : ExteriorCoefficientAreaTheorem)
    (hG : IsOpen G) (hε : Tendsto ε atTop (𝓝 0))
    (r : ℕ → ℕ) (hr : Tendsto r atTop atTop)
    (F : ℂ → ℂ) (hF : ContinuousOn F (((↑) : ℂ → Sphere) ⁻¹' G))
    (hlim : TendstoLocallyUniformlyOn (fun n (z : ℂ) =>
      finiteCoord ((M.stages (r n)).forward (z : Sphere))) F
      atTop (((↑) : ℂ → Sphere) ⁻¹' G))
    (labels : ℕ → ℕ) (B : ∀ k, RetainedRealBarrier d F (labels k))
    {C : Set ℂ} (hC : IsCompact C) (hconn : IsConnected C)
    (hCB : ∀ k, C ⊆ jordanInterior (B k).target_inner)
    {L : ℝ} (hL : 3 * M.radius ≤ L)
    (hBL : ∀ k, closure (jordanInterior (B k).target_outer) ⊆ ball 0 L)
    (hsmall : Tendsto (fun k =>
      Real.sqrt (∫ x in realChartDomain G,
        gradientEnergy (d.physical (labels k)) (fun z => sphericalMetricFactor z • 1) x) +
      Real.sqrt (∑' s, (d.upper (labels k) s - d.lower (labels k) s) ^ 2))
      atTop (𝓝 0)) : C.Subsingleton :=
  subsingleton_of_zero_projection_measure hC hconn
    (M.real_projection_zero_of_vanishing_barriers hsard hsch harea hG hε
      r hr F hF hlim labels B hC hCB hL hBL hsmall)
    (M.projection_zero_of_vanishing_barriers hsard hsch harea hG hε
      r hr F hF hlim labels B hC hCB hL hBL hsmall)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_RealMarkedModels
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assign the actual countable real-model terminals to their original source ends. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

namespace RealModelExhaustion

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  (M : RealModelExhaustion d O ε)

theorem eventually_markIndex (s : S) :
    ∀ᶠ n in atTop, (M.markIndex n s : S) = s := by
  classical
  filter_upwards [M.marks s] with n hn
  simp [markIndex, hn]

end RealModelExhaustion

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_RealTargetEnds
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full corresponding target ends and their collapse by actual source tests. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

namespace RealTargetEnd

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} {L : AssignedRealModelLimit M} {q : Sphere}
  (E : RealTargetEnd L q)

theorem infinity_not_mem : OnePoint.infty ∉
    connectedComponentIn (extendAtInfinity L.function '' G)ᶜ E.point := by
  intro h
  have hinf : OnePoint.infty ∈ G := M.core_source 0 (M.plane_core 0 (Or.inr rfl))
  apply connectedComponentIn_subset _ _ h
  exact ⟨OnePoint.infty, hinf, by simp⟩

theorem sphere_image_plane : ((↑) : ℂ → Sphere) '' E.plane =
    connectedComponentIn (extendAtInfinity L.function '' G)ᶜ E.point := by
  apply image_preimage_eq_of_subset
  intro p hp
  cases p using OnePoint.rec with
  | infty => exact (E.infinity_not_mem hp).elim
  | coe z => exact ⟨z, rfl⟩

theorem plane_compact : IsCompact E.plane := by
  apply isCompact_finite_preimage _ E.infinity_not_mem
  rw [E.target]
  exact isClosed_iInter fun n => (isCompact_closedTerminalCap _).isClosed

theorem plane_connected : IsConnected E.plane := by
  have hc : IsConnected (((↑) : ℂ → Sphere) '' E.plane) := by
    rw [E.sphere_image_plane]
    exact isConnected_connectedComponentIn_iff.mpr E.outside
  refine ⟨?_, OnePoint.isOpenEmbedding_coe.isEmbedding.isInducing.isPreconnected_image.mp
    hc.isPreconnected⟩
  obtain ⟨p, z, hz, _⟩ := hc.nonempty
  exact ⟨z, hz⟩

end RealTargetEnd

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ShrinkingRealModels
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vanishing transfer errors and shrinking physical marked neighborhoods. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem modelError_pos (n : ℕ) : 0 < modelError n := by
  unfold modelError
  positivity

attribute [local instance] sphereMetric

theorem markedNeighborhoods_shrink {S : Type*} (σ : S → Sphere) (s : S)
    {W : Set Sphere} (hW : W ∈ 𝓝 (σ s)) :
    ∀ᶠ n in atTop, markedNeighborhoods σ n s ⊆ W := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hW
  filter_upwards [modelError_tendsto.eventually (gt_mem_nhds hδ)] with n hn
  exact (ball_subset_ball hn.le).trans hball

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RealSourceBarriers
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local plateaus of the original quotient tests collapse their corresponding full ends. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer.RealTargetEnd

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} {L : AssignedRealModelLimit M} {q : Sphere}
  (E : RealTargetEnd L q)

theorem target_eq_singleton_of_plane_subsingleton (h : E.plane.Subsingleton) :
    connectedComponentIn (extendAtInfinity L.function '' G)ᶜ E.point = {E.point} := by
  apply Subset.antisymm
  · intro p hp
    have hpoint : E.point ∈ ((↑) : ℂ → Sphere) '' E.plane :=
      E.sphere_image_plane.symm ▸ mem_connectedComponentIn E.outside
    rw [← E.sphere_image_plane] at hp
    obtain ⟨z, hz, rfl⟩ := hp
    obtain ⟨w, hw, he⟩ := hpoint
    exact (congrArg ((↑) : ℂ → Sphere) (h hz hw)).trans he
  · exact singleton_subset_iff.mpr (mem_connectedComponentIn E.outside)

end CircleDomainRigidity.FiniteTransfer.RealTargetEnd

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RealAnchoredBarriers
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.metricBeltramiCoefficient_scalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Collapse with a fixed outer zero contour, as used by the selected barriers. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer.RealTargetEnd

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} {L : AssignedRealModelLimit M} {q : Sphere}
  (E : RealTargetEnd L q)

theorem exists_positive_level_in_source_open
    {W : Set Sphere} (hW : IsOpen W) (hCW : connectedComponentIn Gᶜ q ⊆ W) :
    ∃ n, 0 < n ∧ closedTerminalCap ((L.cores n).disk (E.address n)) ⊆ W := by
  obtain ⟨n, hn⟩ := nested_sphere_sets_eventually_subset
    (fun n => (isCompact_closedTerminalCap _).isClosed) E.source_cap_antitone hW
    (E.source ▸ hCW)
  exact ⟨n + 1, Nat.succ_pos _, (E.source_cap_antitone (Nat.le_succ n)).trans hn⟩

/-- The source outer contour is fixed independently of the shrinking tests.
Its target contour and the common radius bound are constructed once. -/
theorem target_eq_singleton_of_small_anchored_plateaus
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (harea : ExteriorCoefficientAreaTheorem)
    (hG : IsOpen G) (hconn : IsConnected G) (hε : Tendsto ε atTop (𝓝 0))
    (hπ : Continuous π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hq : q ∈ Gᶜ) (A : SmoothJordanCore G) (j : Fin A.count)
    (hCA : connectedComponentIn Gᶜ q ⊆ ((↑) : ℂ → Sphere) '' jordanInterior (A.disk j))
    (hsmall : ∀ δ : ℝ, 0 < δ → ∃ (l : ℕ) (U : Set Sphere),
      IsOpen U ∧ π q ∈ U ∧ (∀ x ∈ U ∩ d.source, d.coordinate l x = 1) ∧
      (∀ z ∈ frontier (jordanInterior (A.disk j)),
        d.physical l (Complex.equivRealProdCLM z) = 0) ∧
      Real.sqrt (∫ x in realChartDomain G,
        gradientEnergy (d.physical l) (fun z => sphericalMetricFactor z • 1) x) +
      Real.sqrt (∑' s, (d.upper l s - d.lower l s) ^ 2) < δ) :
    connectedComponentIn (extendAtInfinity L.function '' G)ᶜ E.point = {E.point} := by
  have hinf : OnePoint.infty ∈ G := M.core_source 0 (M.plane_core 0 (Or.inr rfl))
  obtain ⟨J, _, _, hJ, hJs⟩ := exists_matched_image_core hsch hG hconn hinf
    L.conformal.1 L.conformal.bijOn.injOn (by simp) A
  choose labels U hU hqU hOne hZero hsize using fun k => hsmall (modelError k) (modelError_pos k)
  have hlevels (k : ℕ) : ∃ n, 0 < n ∧
      closedTerminalCap ((L.cores n).disk (E.address n)) ⊆
        (π ⁻¹' U k) ∩ (((↑) : ℂ → Sphere) '' jordanInterior (A.disk j)) := by
    apply E.exists_positive_level_in_source_open
      ((hU k).preimage hπ |>.inter (OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen _)))
    intro x hx
    refine ⟨?_, hCA hx⟩
    change π x ∈ U k
    rw [← (hr q x).mpr (Or.inr ⟨hq, hx⟩)]
    exact hqU k
  choose levels hpos hcap using hlevels
  have hone (k : ℕ) : ∀ z ∈ frontier (jordanInterior ((L.cores (levels k)).disk (E.address (levels k)))),
      d.physical (labels k) (Complex.equivRealProdCLM z) = 1 := by
    intro z hz
    have hzG := (L.cores (levels k)).boundary_subset_domain (E.address (levels k)) ⟨z, hz, rfl⟩
    rw [d.pullback _ z hzG]
    exact hOne k (π z) ⟨(hcap k ⟨z, frontier_subset_closure hz, rfl⟩).1, d.source_map z hzG⟩
  have hnested (k : ℕ) : closure (jordanInterior (L.contours (levels k) (E.address (levels k)))) ⊆
      jordanInterior (J j) := by
    have ht := (matched_jordan_disk_subset_iff L.conformal.bijOn.injOn
      (A.disk j) ((L.cores (levels k)).disk (E.address (levels k)))
      (J j) (L.contours (levels k) (E.address (levels k)))
      ((L.cores (levels k)).boundary_subset_domain (E.address (levels k)))
      (L.boundary (levels k) (E.address (levels k))) (hJs j)).mp
        ((hcap k).trans inter_subset_right)
    intro z hz
    exact OnePoint.coe_injective.mem_set_image.mp (ht ⟨z, hz, rfl⟩)
  let B (k : ℕ) : RetainedRealBarrier d L.function (labels k) := {
    inner := L.cores (levels k), outer := A,
    inner_index := E.address (levels k), outer_index := j,
    value_one := hone k, value_zero := hZero k,
    target_inner := L.contours (levels k) (E.address (levels k)), target_outer := J j,
    inner_image := L.boundary (levels k) (E.address (levels k)), outer_image := hJ j,
    inner_side := L.side (levels k) (E.address (levels k)), outer_side := hJs j,
    nested := hnested k }
  obtain ⟨R, _, hR⟩ := (isCompact_closure_jordanInterior (J j)).isBounded.exists_pos_norm_lt
  have hF : ContinuousOn L.function (((↑) : ℂ → Sphere) ⁻¹' G) := by
    intro z hz
    have h := continuousAt_finite_part_of_conformalAt (L.conformal.1 _ hz)
      (by simp only [extendAtInfinity_coe]; exact OnePoint.coe_ne_infty _)
    simpa only [extendAtInfinity_coe, finiteCoord_coe] using h.continuousWithinAt
  apply E.target_eq_singleton_of_plane_subsingleton
  apply M.subsingleton_of_vanishing_barriers (L := max (3 * M.radius) R)
    hsard hsch harea hG hε L.subsequence L.strict.tendsto_atTop
    L.function hF L.converges labels B E.plane_compact E.plane_connected
    (fun k => E.plane_inside (levels k)) (le_max_left _ _) ?_ ?_
  · intro k z hz
    rw [mem_ball, dist_zero_right]
    exact (hR z hz).trans_le (le_max_right _ _)
  · exact squeeze_zero (fun k => add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (fun k => (hsize k).le) modelError_tendsto

end CircleDomainRigidity.FiniteTransfer.RealTargetEnd

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RealBarrierTests
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.metricBeltramiCoefficient_scalar _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual real tests used by the countable selection. Compatibility is
with every finite sublist of previously selected tests, retaining repetitions. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

namespace UngatedRealTest
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {EStar : Set Sphere}

theorem ordinary_norm_le_size
    (R : UngatedRealTest d π EStar)
    (hclosure : d.dust ⊆ closure d.quotientDomain)
    {A : Type*} (a : A → Sphere) (ha : Injective a) (haB : range a ⊆ d.dust) :
    Real.sqrt (∫ x in FiniteTransfer.realChartDomain d.physicalDomain,
      FiniteTransfer.gradientEnergy R.coordinate.physical
        (fun z => FiniteTransfer.sphericalMetricFactor z • 1) x) +
    Real.sqrt (∑' s, (limsup R.coordinate.quotient (𝓝[d.quotientDomain] (a s)) -
      liminf R.coordinate.quotient (𝓝[d.quotientDomain] (a s))) ^ 2) ≤
      R.size.toReal := by
  have hunit (x : Sphere) (_ : x ∈ d.quotientDomain) : |R.coordinate.quotient x| ≤ 1 := by
    rw [abs_of_nonneg (R.coordinate.quotient_unit x).1]
    exact (R.coordinate.quotient_unit x).2
  have hnorm := real_square_norm_le_counting
    (fun s => limsup R.coordinate.quotient (𝓝[d.quotientDomain] (a s)) -
      liminf R.coordinate.quotient (𝓝[d.quotientDomain] (a s))) R.weight a ha
    (fun s => boundary_width_nonneg hunit (hclosure (haB (mem_range_self s))))
    (fun s => R.band_bound (a s) (haB (mem_range_self s))) R.weight_finite
  rw [size, ENNReal.toReal_add ENNReal.ofReal_ne_top
    (show countingSquareNorm R.weight ≠ ∞ from
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) R.weight_finite.ne),
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  exact add_le_add le_rfl hnorm


end UngatedRealTest
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MixedSequenceRetention
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every fixed coordinate is eventually retained, with its actual
values and differential, on every compact source set of the common
model sequence. -/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

variable {S C : Type*} [LinearOrder C]
  {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ}
  {data : C → MaskedCoordinateData G d.source π σ} {retained : ℕ → C}
  {O : ℕ → S → Set Sphere} {ε ρ : ℕ → ℝ}

namespace MixedModelExhaustion

variable (M : MixedModelExhaustion d data retained O ε ρ)

theorem coordinateIndex_eventually (c : C) :
    ∀ᶠ n in atTop, M.label n (M.coordinateIndex c n) = c := by
  classical
  filter_upwards [M.coordinate_eventually c] with n hn
  simp only [coordinateIndex, dite_eq_left hn]
  exact Classical.choose_spec hn

theorem eventually_coordinate_eq {K : Set Sphere} (hK : IsCompact K) (hKG : K ⊆ G) (c : C) :
    ∀ᶠ n in atTop, ∀ x ∈ realChartDomain K,
      (M.stages n).model.functions (M.coordinateIndex c n) =ᶠ[𝓝 x] (data c).physical := by
  filter_upwards [M.real.eventually_core_contains hK hKG, M.coordinateIndex_eventually c]
    with n hn hc
  intro x hx
  have hcore : x ∈ (M.stages n).core :=
    interior_subset ((M.stages n).core_contains (show x ∈ realChartDomain (M.real.cores n) from hn hx))
  change ∀ᶠ y in 𝓝 x, (M.stages n).model.functions (M.coordinateIndex c n) y = (data c).physical y
  filter_upwards [(M.stages n).model.retained.filter_mono (nhds_le_nhdsSet hcore)] with y hy
  simpa only [hc] using hy (M.coordinateIndex c n)

theorem eventually_coordinate_values {K : Set Sphere} (hK : IsCompact K) (hKG : K ⊆ G) (c : C) :
    ∀ᶠ n in atTop, ∀ x ∈ realChartDomain K,
      (M.stages n).model.functions (M.coordinateIndex c n) x = (data c).physical x :=
  (M.eventually_coordinate_eq hK hKG c).mono fun _ hn x hx => (hn x hx).self_of_nhds

end MixedModelExhaustion
end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MixedCircuitRetention
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed source circuit keeps exactly the same circle values on the
actual mixed models and hence supplies a fixed real lift for the Stokes
limit. -/

open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem MixedModelExhaustion.eventually_circuit_values
    {S C : Type*} [LinearOrder C]
    {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates G π σ}
    {data : C → MaskedCoordinateData G d.source π σ} {retained : ℕ → C}
    {O : ℕ → S → Set Sphere} {ε ρ : ℕ → ℝ}
    (M : MixedModelExhaustion d data retained O ε ρ)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : PositiveJordanParametrization H γ)
    (hG : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G) (c : C) :
    ∀ᶠ n in atTop, ∀ t : ℝ,
      sphereRealFunction ((M.stages n).model.functions (M.coordinateIndex c n))
        ((M.stages n).model.inverse
          ((finiteCoord ((M.stages n).model.forward (γ t : Sphere)) : ℂ) : Sphere)) =
      (data c).physical (Complex.equivRealProdCLM (γ t)) := by
  let K := ((↑) : ℂ → Sphere) '' frontier (jordanInterior H)
  have hK : IsCompact K :=
    (isCompact_closure_jordanInterior H).of_isClosed_subset isClosed_frontier frontier_subset_closure |>.image
      OnePoint.continuous_coe
  filter_upwards [M.eventually_coordinate_values hK hG c,
    M.real.eventually_core_contains hK hG] with n hn hcore
  intro t
  have hgt : (γ t : Sphere) ∈ K := mem_image_of_mem _ (hγ.mem_frontier t)
  have hx : Complex.equivRealProdCLM (γ t) ∈ (M.stages n).core := by
    apply interior_subset ((M.stages n).core_contains ?_)
    change ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM (γ t)) : ℂ) : Sphere) ∈
      M.real.cores n
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hcore hgt
  have hxQ : (γ t : Sphere) ∈ openCompletedRegion (M.stages n).terminals.H := by
    apply (M.stages n).core_model
    exact (coe_mem_sphericalCore _ _).mpr hx
  have hi : OnePoint.infty ∈ openCompletedRegion (M.stages n).terminals.H :=
    (M.stages n).core_model (infty_mem_sphericalCore (M.stages n).core)
  have hfin := finite_image_of_fixes_infty (M.stages n).model.equivalence.bijOn.injOn hi
    (M.stages n).model.principal.1 hxQ
  rw [coe_finiteCoord hfin, (M.stages n).model.equivalence.left_inv _ hxQ]
  apply hn
  change ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM (γ t)) : ℂ) : Sphere) ∈ K
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using hgt

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JordanBoundaryBound
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bound on a Jordan boundary bounds its filled side. -/

open Set Function Metric
noncomputable section
namespace CircleDomainRigidity

 theorem jordan_closure_subset_closedBall_of_frontier
    (H : ℂ ≃ₜ ℂ) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hbound : frontier (jordanInterior H) ⊆ closedBall c R) :
    closure (jordanInterior H) ⊆ closedBall c R := by
  have hinside : jordanInterior H ⊆ closedBall c R := by
    have h := open_subset_finite_jordan_fills_of_frontier_subset
      (fun _ : Unit => roundJordanAt c R hR) (by intro i j hij; exact (hij (Subsingleton.elim i j)).elim)
      (jordanInterior_isOpen H) ((isCompact_closure_jordanInterior H).isBounded.subset subset_closure)
      (show frontier (jordanInterior H) ⊆ ⋃ _ : Unit,
        closure (jordanInterior (roundJordanAt c R hR)) from by
        intro z hz
        exact mem_iUnion.mpr ⟨(), by rw [roundJordanAt_closure]; exact hbound hz⟩)
    simpa only [iUnion_const, roundJordanAt_closure] using h

  exact closure_minimal hinside isClosed_closedBall

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_MixedCollarBound
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The common exterior normalization bounds every retained image collar
by one fixed ball, independently of its finite terminal family. -/

open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem MixedModelExhaustion.eventually_all_image_collar_bounds
    (harea : ExteriorCoefficientAreaTheorem)
    {S C : Type*} [LinearOrder C]
    {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates G π σ}
    {data : C → MaskedCoordinateData G d.source π σ} {retained : ℕ → C}
    {O : ℕ → S → Set Sphere} {ε ρ : ℕ → ℝ}
    (M : MixedModelExhaustion d data retained O ε ρ)
    (H : ℂ ≃ₜ ℂ)
    (hG : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G)
    (hH : ∀ z ∈ frontier (jordanInterior H), ‖z‖ ≤ 4 * M.real.radius)
    : ∀ᶠ n in atTop, ∀ J : ℂ ≃ₜ ℂ,
      (M.stages n).model.forward '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) =
        ((↑) : ℂ → Sphere) '' frontier (jordanInterior J) →
      closure (jordanInterior J) ⊆ closedBall 0 (5 * M.real.radius) := by
  have hbound (n : ℕ) := (normalized_model_uniform_bound harea (M.real.stages n).equivalence
    (M.real.stages n).circle_domain.1 M.real.radius_pos
    ((M.real.exterior_core n).trans (M.real.core_model n))
    ((M.real.core_conformal n).mono
      ((compl_subset_compl.mpr (image_mono ball_subset_closedBall)).trans (M.real.exterior_core n)))
    (M.real.stages n).principal).2
  have hK : IsCompact (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) :=
    ((isCompact_closure_jordanInterior H).of_isClosed_subset isClosed_frontier
      frontier_subset_closure).image OnePoint.continuous_coe
  filter_upwards [M.real.eventually_model_contains hK hG] with n hret
  intro J hn
  apply jordan_closure_subset_closedBall_of_frontier J (mul_pos (by norm_num) M.real.radius_pos)
  intro z hz
  have hm : (z : Sphere) ∈ (M.stages n).model.forward ''
      (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) := hn.symm ▸ mem_image_of_mem _ hz
  obtain ⟨_, ⟨w, hw, rfl⟩, he⟩ := hm
  have hb := hbound n w (hret (mem_image_of_mem _ hw)) (hH w hw)
  rw [← M.same_forward n, he] at hb
  exact OnePoint.coe_injective.mem_set_image.mp hb


end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ComplexCovectorEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complex-chart differential norm is exactly the two-coordinate
Euclidean energy used by the finite transfer. -/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem circleFDeriv_complex_norm_sq
    {D : Set (ℝ × ℝ)} (hD : IsOpen D) {u : (ℝ × ℝ) → UnitAddCircle}
    (hu : SmoothCircleOn u D) {z : ℂ} (hz : Complex.equivRealProdCLM z ∈ D) :
    ‖circleFDeriv (u ∘ Complex.equivRealProdCLM) z‖ ^ 2 =
      fieldEnergy (circleGradient u) (fun _ => 1) (Complex.equivRealProdCLM z) := by
  rw [complexCovector_norm_sq, circleFDeriv_comp hD hu Complex.equivRealProdCLM.differentiableAt hz,
    Complex.equivRealProdCLM.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    Complex.equivRealProdCLM_apply, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
    fieldEnergy, circleGradient, covectorEnergy_identity]

theorem integral_circleFDeriv_complex_norm_sq
    {D A : Set (ℝ × ℝ)} (hD : IsOpen D) (hA : MeasurableSet A) (hAD : A ⊆ D)
    {u : (ℝ × ℝ) → UnitAddCircle} (hu : SmoothCircleOn u D) :
    (∫ z in Complex.equivRealProdCLM ⁻¹' A,
      ‖circleFDeriv (u ∘ Complex.equivRealProdCLM) z‖ ^ 2) =
      ∫ x in A, fieldEnergy (circleGradient u) (fun _ => 1) x := by
  calc
    _ = ∫ z in Complex.equivRealProdCLM ⁻¹' A,
        fieldEnergy (circleGradient u) (fun _ => 1) (Complex.equivRealProdCLM z) := by
      apply setIntegral_congr_fun (hA.preimage Complex.equivRealProdCLM.continuous.measurable)
      intro z hz
      exact circleFDeriv_complex_norm_sq hD hu (hAD hz)
    _ = _ := Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
      Complex.measurableEquivRealProd.measurableEmbedding _ A

theorem memLp_circleFDeriv_complex
    {D A : Set (ℝ × ℝ)} (hD : IsOpen D) (hA : MeasurableSet A) (hAD : A ⊆ D)
    {u : (ℝ × ℝ) → UnitAddCircle} (hu : SmoothCircleOn u D)
    (hi : IntegrableOn (fieldEnergy (circleGradient u) (fun _ => 1)) A) :
    MemLp (circleFDeriv (u ∘ Complex.equivRealProdCLM)) 2
      (volume.restrict (Complex.equivRealProdCLM ⁻¹' A)) := by
  have hmp := Complex.volume_preserving_equiv_real_prod.restrict_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding A
  have hcomp : IntegrableOn (fun z : ℂ => fieldEnergy (circleGradient u) (fun _ => 1)
      (Complex.equivRealProdCLM z)) (Complex.equivRealProdCLM ⁻¹' A) :=
    (hmp.integrable_comp hi.aestronglyMeasurable).mpr hi
  have hsm : SmoothCircleOn (u ∘ Complex.equivRealProdCLM) (Complex.equivRealProdCLM ⁻¹' D) := by
    intro z hz a ha
    exact (hu _ hz a ha).comp z Complex.equivRealProdCLM.contDiff.contDiffAt
  have hm : AEStronglyMeasurable (circleFDeriv (u ∘ Complex.equivRealProdCLM))
      (volume.restrict (Complex.equivRealProdCLM ⁻¹' A)) := ((contDiffOn_circleFDeriv (hD.preimage Complex.equivRealProdCLM.continuous) hsm).continuousOn.mono
    (preimage_mono hAD)).aestronglyMeasurable (hA.preimage Complex.equivRealProdCLM.continuous.measurable)
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply hcomp.congr
  filter_upwards [ae_restrict_mem (hA.preimage Complex.equivRealProdCLM.continuous.measurable)] with z hz
  exact (circleFDeriv_complex_norm_sq hD hu (hAD hz)).symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskedStageEnergy
attribute [-instance] _root_.Graph.instFiniteElemEdgeSetOfFinite _root_.Graph.instFiniteElemVertexSetOfFinite _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrability and full masked energy on the actual finite model.
The geometric facts retained from construction justify comparison of
ordinary integrals on all later subregions. -/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

variable {S : Type*} {n : ℕ} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {C : Fin n → MaskedCoordinateData G U π σ} {Flag : Set S} {O : S → Set Sphere}
  {K₀ : Set (ℝ × ℝ)} {ε ρ : ℝ} {k₀ : ℕ}

 theorem MaskedCoordinateStage.integrable_energy
    (T : MaskedCoordinateStage C Flag O K₀ ε ρ k₀) (hG : IsOpen G) (hπ : Continuous π) (l : Fin n) :
    IntegrableOn (fieldEnergy (circleGradient (T.model.functions l)) T.model.metric)
      (realChartDomain (completedRegion T.terminals.H) ∩ physicalMask π (C l).mask) := by
  have hM : IsClosed (physicalMask π (C l).mask) :=
    (C l).mask_closed.preimage (hπ.comp (OnePoint.continuous_coe.comp Complex.equivRealProdCLM.symm.continuous))
  have hi : MemLp (circleGradient (C l).physical) 2
      (volume.restrict (realChartDomain G ∩ physicalMask π (C l).mask)) := by
    simpa only [Measure.restrict_restrict hM.measurableSet, inter_comm] using (C l).energy
  exact integrableOn_masked_circle_energy
    ((isOpen_realChartDomain hG).union (isOpen_iUnion fun j => (realJordanInterior_geometry (T.filling j)).1))
    (isClosed_real_completedRegion T.terminals.H) T.core_closed T.core_cocompact
    (fun _ hx => T.model.extension_contains hx.1) T.core_source hM (T.model.mask_boundary_core l)
    (T.model.filled.1 l) hi (T.model.retained.mono fun _ hx => hx l)
    T.model.metric_smooth.continuous T.model.metric_pos T.model.metric_core

 theorem MaskedCoordinateStage.energy_lt
    (T : MaskedCoordinateStage C Flag O K₀ ε ρ k₀) (l : Fin n) :
    (∫ x in realChartDomain (completedRegion T.terminals.H) ∩ physicalMask π (C l).mask,
      fieldEnergy (circleGradient (T.model.functions l)) T.model.metric x) <
      (∫ x in realChartDomain G ∩ physicalMask π (C l).mask,
        fieldEnergy (circleGradient (C l).physical) (fun x => sphericalMetricFactor x • 1) x) + ε := by
  simpa only [sdiff_empty] using T.model.localized l ∅ MeasurableSet.empty (empty_subset _)

 theorem MaskedCoordinateStage.transported_energy_lt
    (T : MaskedCoordinateStage C Flag O K₀ ε ρ k₀) (hG : IsOpen G) (hπ : Continuous π)
    (hmetric : ∀ p ∈ openCompletedRegion T.terminals.H,
      IsMetricConformalAt T.model.metric T.model.forward p) (l : Fin n) :
    IntegrableOn (fieldEnergy (circleGradient (T.model.functions l ∘ sphereRealMap T.model.inverse))
      (fun _ => 1)) (T.targetMask l) ∧
    (∫ y in T.targetMask l,
      fieldEnergy (circleGradient (T.model.functions l ∘ sphereRealMap T.model.inverse)) (fun _ => 1) y) <
      (∫ x in realChartDomain G ∩ physicalMask π (C l).mask,
        fieldEnergy (circleGradient (C l).physical) (fun x => sphericalMetricFactor x • 1) x) + ε := by
  let : Fintype T.indices := T.indices_finite.fintype
  have hsource : IsOpen (T.sourceMask l) :=
    (isOpen_realChartDomain (isOpen_openCompletedRegion T.terminals.H)).inter isOpen_interior
  have hsub : T.sourceMask l ⊆
      realChartDomain (completedRegion T.terminals.H) ∩ physicalMask π (C l).mask :=
    fun _ hx => ⟨openCompletedRegion_subset_completedRegion T.terminals.H hx.1, interior_subset hx.2⟩
  have hi := T.integrable_energy hG hπ l
  have his := hi.mono_set hsub
  have htarget := T.model.transported l
  have hUinf : OnePoint.infty ∈ openCompletedRegion T.terminals.H :=
    T.core_model (infty_mem_sphericalCore T.core)
  have hmeas := hsource.measurableSet
  have hit := (integrable_filled_circleEnergy_metric_sphere_map_iff hmeas htarget.1
    T.model.equivalence.bijOn.injOn (fun _ hx => hx.1) hmetric
    (fun x _ => T.model.metric_pos x)
    (fun x hx => finite_image_of_fixes_infty T.model.equivalence.bijOn.injOn hUinf
      T.model.principal.1 hx.1)
    (fun x hx => mem_image_of_mem _ hx)
    (T.model.functions l ∘ sphereRealMap T.model.inverse) (T.model.functions l)
    htarget.2.1 htarget.2.2).mpr his
  refine ⟨hit, ?_⟩
  rw [MaskedCoordinateStage.targetMask, T.model.transported_energy l (T.sourceMask l) hmeas (Subset.refl _)]
  exact (setIntegral_mono_set hi
    (ae_of_all _ (fun x => covectorEnergy_nonneg _ (T.model.metric_pos x)))
    (ae_of_all _ hsub)).trans_lt (T.energy_lt l)

 theorem MaskedCoordinateStage.complex_energy_lt
    (T : MaskedCoordinateStage C Flag O K₀ ε ρ k₀) (hG : IsOpen G) (hπ : Continuous π)
    (hmetric : ∀ p ∈ openCompletedRegion T.terminals.H,
      IsMetricConformalAt T.model.metric T.model.forward p) (l : Fin n) :
    MemLp (circleFDeriv ((T.model.functions l ∘ sphereRealMap T.model.inverse) ∘ Complex.equivRealProdCLM))
      2 (volume.restrict (Complex.equivRealProdCLM ⁻¹' T.targetMask l)) ∧
    (∫ z in Complex.equivRealProdCLM ⁻¹' T.targetMask l,
      ‖circleFDeriv ((T.model.functions l ∘ sphereRealMap T.model.inverse) ∘ Complex.equivRealProdCLM) z‖ ^ 2) <
      (∫ x in realChartDomain G ∩ physicalMask π (C l).mask,
        fieldEnergy (circleGradient (C l).physical) (fun x => sphericalMetricFactor x • 1) x) + ε := by
  have htarget := T.model.transported l
  obtain ⟨hi, he⟩ := T.transported_energy_lt hG hπ hmetric l
  refine ⟨memLp_circleFDeriv_complex htarget.1 htarget.1.measurableSet (Subset.refl _) htarget.2.1 hi, ?_⟩
  rw [integral_circleFDeriv_complex_norm_sq (D := T.targetMask l) (A := T.targetMask l) htarget.1 htarget.1.measurableSet (Subset.refl _) htarget.2.1]
  exact he

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RetainedJordanSides
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CannonMobius.affine_coe _root_.OAI.CannonMobius.affine_infty _root_.OAI.CannonMobius.inv_inv_apply _root_.OAI.CannonMobius.roundChart_coe _root_.OAI.CannonMobius.tripleMap_mul _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A retained Jordan curve separates the two sides of an open connected
sphere domain. This applies to the actual finite models without extending
the model map across any terminal disk. -/

open Set Function Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem isPreconnected_finite_part {G : Set Sphere}
    (hG : IsOpen G) (hconn : IsPreconnected G) :
    IsPreconnected (((↑) : ℂ → Sphere) ⁻¹' G) := by
  by_cases hi : OnePoint.infty ∈ G
  · exact (finite_part_connected_unbounded hconn
      (mem_interior_iff_mem_nhds.mpr (hG.mem_nhds hi))).1
  · have he : finiteCoord '' G = ((↑) : ℂ → Sphere) ⁻¹' G := by
      ext z
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact (CannonMobius.coe_coordinate (fun h => hi (h ▸ hp))).symm ▸ hp
      · intro hz
        exact ⟨(z : Sphere), hz, finiteCoord_coe z⟩
    rw [← he]
    exact hconn.image _ (continuousOn_finiteCoord_of_avoids_infty hi)

 theorem isPreconnected_sphere_inter_jordan
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsPreconnected G)
    (H : ℂ ≃ₜ ℂ)
    (hboundary : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G) :
    IsPreconnected (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H)) := by
  have hi := isPreconnected_inter_jordanInterior
    (hG.preimage OnePoint.continuous_coe) (isPreconnected_finite_part hG hconn) H
    (fun z hz => hboundary (mem_image_of_mem _ hz))
  rw [← image_preimage_inter ((↑) : ℂ → Sphere) (jordanInterior H) G]
  exact hi.image _ OnePoint.continuous_coe.continuousOn

 theorem isPreconnected_sphere_inter_jordan_exterior
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsPreconnected G)
    (H : ℂ ≃ₜ ℂ)
    (hboundary : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G) :
    IsPreconnected (G ∩ (closedTerminalCap H)ᶜ) := by
  let e : Sphere ≃ₜ Sphere := H.onePointCongr.symm.trans CannonMobius.inversion
  have hpre : e ⁻¹' (((↑) : ℂ → Sphere) '' ball (0 : ℂ) 1) =
      (closedTerminalCap H)ᶜ := by
    change H.onePointCongr.symm ⁻¹' (CannonMobius.inversion ⁻¹'
      (((↑) : ℂ → Sphere) '' ball (0 : ℂ) 1)) = _
    rw [inversion_preimage_unitDisk, preimage_compl, ← H.onePointCongr.image_eq_preimage_symm]
    congr 1
    simp only [closedTerminalCap, closure_jordanInterior, image_image,
      Homeomorph.onePointCongr_apply, OnePoint.map_some]
  have hbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior (Homeomorph.refl ℂ)) ⊆ e '' G := by
    rintro p ⟨z, hz, rfl⟩
    have hzn : ‖z‖ = 1 := by simpa [frontier_jordanInterior] using hz
    have hz0 : z ≠ 0 := by intro h; simp [h] at hzn
    refine ⟨(H z⁻¹ : ℂ), hboundary ?_, ?_⟩
    · refine ⟨H z⁻¹, ?_, rfl⟩
      rw [frontier_jordanInterior]
      exact ⟨z⁻¹, by simp [norm_inv, hzn], rfl⟩
    · change CannonMobius.inv (H.onePointCongr.symm ((H z⁻¹ : ℂ) : Sphere)) = (z : Sphere)
      have hx : H.onePointCongr.symm ((H z⁻¹ : ℂ) : Sphere) = ((z⁻¹ : ℂ) : Sphere) := by
        change H.onePointCongr.symm (H.onePointCongr ((z⁻¹ : ℂ) : Sphere)) = _
        exact H.onePointCongr.symm_apply_apply _
      rw [hx]
      simp [CannonMobius.inv, hz0]
  have hc := isPreconnected_sphere_inter_jordan (e.isOpenMap G hG)
    (hconn.image e e.continuous.continuousOn) (Homeomorph.refl ℂ) hbd
  have he : e.symm '' (e '' G ∩ (((↑) : ℂ → Sphere) ''
      jordanInterior (Homeomorph.refl ℂ))) = G ∩ (closedTerminalCap H)ᶜ := by
    rw [e.symm.image_eq_preimage_symm, Homeomorph.symm_symm, preimage_inter,
      e.injective.preimage_image]
    simpa only [jordanInterior, Homeomorph.refl_apply, image_id] using
      congrArg (G ∩ ·) hpre
  rw [← he]
  exact hc.image e.symm e.symm.continuous.continuousOn

 theorem open_image_retained_jordan_side_eq
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsPreconnected G)
    (hinf : OnePoint.infty ∈ G) (H J : ℂ ≃ₜ ℂ)
    (hbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G)
    {f : Sphere → Sphere} (hf : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hi : InjOn f G)
    (hfix : f OnePoint.infty = OnePoint.infty)
    (hboundary : f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior J)) :
    f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H)) =
      f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior J) := by
  let A : Set Sphere := ((↑) : ℂ → Sphere) '' jordanInterior H
  let B : Set Sphere := ((↑) : ℂ → Sphere) '' jordanInterior J
  have hAo : IsOpen A := OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen H)
  have hBo : IsOpen B := OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen J)
  have hAf : frontier A = ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) :=
    frontier_sphere_image_jordanInterior H
  have hBf : frontier B = ((↑) : ℂ → Sphere) '' frontier (jordanInterior J) :=
    frontier_sphere_image_jordanInterior J
  have hAcl : closure A = closedTerminalCap H := closure_sphere_image_jordanInterior H
  have havoid (x : Sphere) (hx : x ∈ G) (hxA : x ∉ frontier A) : f x ∉ frontier B := by
    intro hy
    rw [hBf, ← hboundary] at hy
    obtain ⟨y, hy, he⟩ := hy
    have hyx := hi (hbd hy) hx he
    exact hxA (hAf.symm ▸ (hyx ▸ hy))
  have hsplit (S : Set Sphere) (hS : S ⊆ G) (ha : Disjoint S (frontier A)) :
      f '' S ⊆ B ∪ (closure B)ᶜ := by
    rintro _ ⟨x, hx, rfl⟩
    by_cases hb : f x ∈ B
    · exact Or.inl hb
    · exact Or.inr (fun hc => havoid x (hS hx)
        (fun h => Set.disjoint_left.mp ha hx h) ⟨hc, hBo.interior_eq.symm ▸ hb⟩)
  have hdisj : Disjoint B (closure B)ᶜ :=
    Set.disjoint_left.mpr (fun _ h h' => h' (subset_closure h))
  have houtside : f '' (G ∩ (closure A)ᶜ) ⊆ (closure B)ᶜ := by
    have hc : IsPreconnected (f '' (G ∩ (closure A)ᶜ)) :=
      ((hAcl.symm ▸ isPreconnected_sphere_inter_jordan_exterior hG hconn H hbd).image
        f (hf.mono inter_subset_left))
    apply hc.subset_right_of_subset_union hBo isClosed_closure.isOpen_compl hdisj
      (hsplit _ inter_subset_left (Set.disjoint_left.mpr (fun (x : Sphere) (h : x ∈ G ∩ (closure A)ᶜ)
        (h' : x ∈ frontier A) => h.2 (frontier_subset_closure h'))))
    refine ⟨OnePoint.infty, ?_, ?_⟩
    · refine ⟨OnePoint.infty, ⟨hinf, ?_⟩, hfix⟩
      rw [hAcl]
      rintro ⟨z, _, hz⟩
      exact OnePoint.coe_ne_infty z hz
    · rw [closure_sphere_image_jordanInterior J]
      rintro ⟨z, _, hz⟩
      exact OnePoint.coe_ne_infty z hz
  have hinverse : f '' G ∩ B ⊆ f '' (G ∩ A) := by
    rintro _ ⟨⟨x, hx, rfl⟩, hb⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    by_contra hxA
    by_cases hxc : x ∈ closure A
    · have hxf : x ∈ frontier A := ⟨hxc, hAo.interior_eq.symm ▸ hxA⟩
      have hyf : f x ∈ frontier B := by
        rw [hBf, ← hboundary]
        exact mem_image_of_mem f (hAf ▸ hxf)
      exact hyf.2 (hBo.interior_eq.symm ▸ hb)
    · exact houtside (mem_image_of_mem f ⟨hx, hxc⟩) (subset_closure hb)
  have hmeet : (f '' (G ∩ A) ∩ B).Nonempty := by
    obtain ⟨z, hz⟩ := (isConnected_frontier_jordanInterior H).nonempty
    have hzA : (z : Sphere) ∈ frontier A := hAf.symm ▸ mem_image_of_mem _ hz
    have hzG : (z : Sphere) ∈ G := hbd (mem_image_of_mem _ hz)
    have hzf : f (z : Sphere) ∈ frontier B := by
      rw [hBf, ← hboundary]
      exact mem_image_of_mem f (mem_image_of_mem _ hz)
    obtain ⟨y, hy, hyB⟩ := mem_closure_iff_nhds.mp (frontier_subset_closure hzf)
      (f '' G) ((ho G hG Subset.rfl).mem_nhds (mem_image_of_mem f hzG))
    exact ⟨y, hinverse ⟨hy, hyB⟩, hyB⟩
  have hins : f '' (G ∩ A) ⊆ B := by
    apply ((isPreconnected_sphere_inter_jordan hG hconn H hbd).image
      f (hf.mono inter_subset_left)).subset_left_of_subset_union
      hBo isClosed_closure.isOpen_compl hdisj
      (hsplit _ inter_subset_left (Set.disjoint_left.mpr (fun _ h h' =>
        h'.2 (hAo.interior_eq.symm ▸ h.2)))) hmeet
  exact Subset.antisymm (fun _ h => ⟨image_mono inter_subset_left h, hins h⟩) hinverse

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RetainedImageBoundary
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual image boundary of a retained source collar, and its bounded
side. Schoenflies supplies only a chart for the embedded image circle. -/

open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem exists_jordan_image_retained_boundary
    (hsch : PlanarSchoenflies) {G : Set Sphere}
    {f : Sphere → Sphere} (hf : ContinuousOn f G) (hi : InjOn f G)
    (hinf : OnePoint.infty ∈ G) (hfix : f OnePoint.infty = OnePoint.infty)
    (H : ℂ ≃ₜ ℂ)
    (hbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G) :
    ∃ J : ℂ ≃ₜ ℂ,
      f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) =
        ((↑) : ℂ → Sphere) '' frontier (jordanInterior J) := by
  let γ : Circle → Sphere := fun t => (H (t : ℂ) : ℂ)
  have hγ : Continuous γ := OnePoint.continuous_coe.comp
    (H.continuous.comp continuous_subtype_val)
  have hγG (t : Circle) : γ t ∈ G :=
    hbd ⟨H t, by rw [frontier_jordanInterior]; exact ⟨t, t.property, rfl⟩, rfl⟩
  have hfinite (t : Circle) : f (γ t) ≠ OnePoint.infty :=
    finite_image_of_fixes_infty hi hinf hfix (hγG t)
  let δ : Circle → ℂ := fun t => finiteCoord (f (γ t))
  have hδc (t : Circle) : (δ t : Sphere) = f (γ t) :=
    CannonMobius.coe_coordinate (hfinite t)
  have hδ : Continuous δ := by
    apply OnePoint.isOpenEmbedding_coe.isInducing.continuous_iff.mpr
    have he : ((↑) : ℂ → Sphere) ∘ δ = f ∘ γ := funext hδc
    rw [he]
    exact hf.comp_continuous hγ hγG
  have hδi : Injective δ := by
    intro x y hxy
    apply Subtype.ext
    apply H.injective
    apply OnePoint.coe_injective
    apply hi (hγG x) (hγG y)
    exact (hδc x).symm.trans ((congrArg ((↑) : ℂ → Sphere) hxy).trans (hδc y))
  obtain ⟨J, hJ⟩ := hsch δ hδ hδi
  refine ⟨J, ?_⟩
  rw [frontier_jordanInterior_eq_circle_range J δ hJ, frontier_jordanInterior]
  ext p
  constructor
  · rintro ⟨_, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
    exact ⟨δ ⟨z, hz⟩, ⟨⟨z, hz⟩, rfl⟩, hδc ⟨z, hz⟩⟩
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨γ t, ⟨H t, ⟨t, t.property, rfl⟩, rfl⟩, (hδc t).symm⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JordanHoleSelection
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Select exactly the finite round holes inside a retained Jordan curve.
Its punctured closed side is therefore contained in the actual target
domain, including its outer boundary. -/

open Set Function Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem round_hole_jordan_side (H : ℂ ≃ₜ ℂ) (c : ℂ) (r : ℝ)
    (havoid : Disjoint (closedBall c r) (frontier (jordanInterior H))) :
    closedBall c r ⊆ jordanInterior H ∨
      Disjoint (closedBall c r) (closure (jordanInterior H)) := by
  have ho := jordanInterior_isOpen H
  have hs : closedBall c r ⊆ jordanInterior H ∪ (closure (jordanInterior H))ᶜ := by
    intro z hz
    by_cases hi : z ∈ jordanInterior H
    · exact Or.inl hi
    · exact Or.inr (fun hc => Set.disjoint_left.mp havoid hz
        ⟨hc, ho.interior_eq.symm ▸ hi⟩)
  rcases isPreconnected_closedBall.subset_or_subset ho isClosed_closure.isOpen_compl
    (Set.disjoint_left.mpr (fun _ h h' => h' (subset_closure h))) hs with h | h
  · exact Or.inl h
  · exact Or.inr (Set.disjoint_left.mpr (fun _ hz hc => h hz hc))

 theorem exists_round_holes_inside_jordan
    {I : Type*} [Fintype I] (c : I → ℂ) (r : I → ℝ)
    (V : Set Sphere) (hext : ((↑) : ℂ → Sphere) ⁻¹' V = (⋃ i, closedBall (c i) (r i))ᶜ)
    (H : ℂ ≃ₜ ℂ)
    (hbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ V) :
    ∃ (m : ℕ) (κ : Fin m → I), Injective κ ∧
      (∀ j, closedBall (c (κ j)) (r (κ j)) ⊆ jordanInterior H) ∧
      (∀ i, i ∈ range κ ↔ closedBall (c i) (r i) ⊆ jordanInterior H) ∧
      closure (jordanInterior H) \ ⋃ j, closedBall (c (κ j)) (r (κ j)) =
        closure (jordanInterior H) ∩ ((↑) : ℂ → Sphere) ⁻¹' V := by
  classical
  let A := {i : I | closedBall (c i) (r i) ⊆ jordanInterior H}
  let e := (Fintype.equivFin A).symm
  let κ : Fin (Fintype.card A) → I := fun j => (e j).val
  have hk : Injective κ := Subtype.val_injective.comp e.injective
  have hki (j) : closedBall (c (κ j)) (r (κ j)) ⊆ jordanInterior H := (e j).property
  have hrange (i : I) : i ∈ range κ ↔ closedBall (c i) (r i) ⊆ jordanInterior H := by
    constructor
    · rintro ⟨j, rfl⟩
      exact hki j
    · intro hi
      exact ⟨e.symm ⟨i, hi⟩, congrArg Subtype.val (e.apply_symm_apply ⟨i, hi⟩)⟩
  refine ⟨Fintype.card A, κ, hk, hki, hrange, ?_⟩
  ext z
  rw [mem_sdiff, mem_inter_iff, hext, mem_compl_iff]
  constructor
  · rintro ⟨hz, hnot⟩
    refine ⟨hz, ?_⟩
    intro hu
    obtain ⟨i, hi⟩ := mem_iUnion.mp hu
    have hav : Disjoint (closedBall (c i) (r i)) (frontier (jordanInterior H)) := by
      apply Set.disjoint_left.mpr
      intro x hx hxf
      have hv : (x : Sphere) ∈ V := hbd ⟨x, hxf, rfl⟩
      rw [← mem_preimage, hext] at hv
      exact hv (mem_iUnion.mpr ⟨i, hx⟩)
    rcases round_hole_jordan_side H (c i) (r i) hav with hin | hout
    · obtain ⟨j, hj⟩ := (hrange i).mpr hin
      apply hnot
      exact mem_iUnion.mpr ⟨j, hj.symm ▸ hi⟩
    · exact Set.disjoint_left.mp hout hi hz
  · rintro ⟨hz, hnot⟩
    refine ⟨hz, ?_⟩
    intro hu
    obtain ⟨j, hj⟩ := mem_iUnion.mp hu
    exact hnot (mem_iUnion.mpr ⟨κ j, hj⟩)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskedStageCollar
attribute [-instance] _root_.Graph.instFiniteElemEdgeSetOfFinite _root_.Graph.instFiniteElemVertexSetOfFinite _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite model carries a retained source collar to a Jordan
collar. Exactly the holes inside that image are selected, and the punctured
closed region lies in the transported coordinate's smooth mask. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem MaskedCoordinateStage.exists_collar_region
    (hsch : PlanarSchoenflies)
    {S : Type*} {n : ℕ} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {C : Fin n → MaskedCoordinateData G U π σ}
    {Flag : Set S} {O : S → Set Sphere} {K₀ : Set (ℝ × ℝ)} {ε ρ : ℝ} {k₀ : ℕ}
    (T : MaskedCoordinateStage C Flag O K₀ ε ρ k₀) (l : Fin n)
    (H : ℂ ≃ₜ ℂ)
    (hbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆
      openCompletedRegion T.terminals.H)
    (hmask : realChartDomain (closedTerminalCap H) ⊆ interior (physicalMask π (C l).mask))
    (c : T.indices → ℂ) (r : T.indices → ℝ)
    (hext : ((↑) : ℂ → Sphere) ⁻¹' T.model.domain = (⋃ i, closedBall (c i) (r i))ᶜ) :
    ∃ (J : ℂ ≃ₜ ℂ) (m : ℕ) (κ : Fin m → T.indices),
      Injective κ ∧
      T.model.forward '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) =
        ((↑) : ℂ → Sphere) '' frontier (jordanInterior J) ∧
      (∀ j, closedBall (c (κ j)) (r (κ j)) ⊆ jordanInterior J) ∧
      (∀ i, i ∈ range κ ↔ closedBall (c i) (r i) ⊆ jordanInterior J) ∧
      closure (jordanInterior J) \ ⋃ j, closedBall (c (κ j)) (r (κ j)) ⊆
        Complex.equivRealProdCLM ⁻¹' T.targetMask l := by
  classical
  let : Fintype T.indices := T.indices_finite.fintype
  let Q := openCompletedRegion T.terminals.H
  have hQ : IsOpen Q := isOpen_openCompletedRegion T.terminals.H
  have hQc : IsConnected Q :=
    isConnected_openCompletedRegion T.terminals.H T.terminals.disjoint_closures
  have hi : OnePoint.infty ∈ Q := T.core_model (infty_mem_sphericalCore T.core)
  have hf : ContinuousOn T.model.forward Q :=
    fun p hp => (T.model.equivalence.smooth p hp).1.continuousWithinAt
  obtain ⟨J, hJ⟩ := exists_jordan_image_retained_boundary hsch hf
    T.model.equivalence.bijOn.injOn hi T.model.principal.1 H hbd
  have hside := open_image_retained_jordan_side_eq hQ hQc.isPreconnected hi H J hbd
    hf (fun _ hS hSQ => T.model.equivalence.isOpen_image T.model.circle_domain.1 hS hSQ)
    T.model.equivalence.bijOn.injOn T.model.principal.1 hJ
  rw [T.model.equivalence.bijOn.image_eq] at hside
  have htargetbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior J) ⊆ T.model.domain := by
    rw [← hJ]
    exact (image_mono hbd).trans (image_subset_iff.mpr T.model.equivalence.mapsTo)
  obtain ⟨m, κ, hκ, hin, hexact, hregion⟩ :=
    exists_round_holes_inside_jordan c r T.model.domain hext J htargetbd
  refine ⟨J, m, κ, hκ, hJ, hin, hexact, ?_⟩
  intro z hz
  rw [hregion] at hz
  have hp : (z : Sphere) ∈ T.model.domain ∩ closedTerminalCap J :=
    ⟨hz.2, z, hz.1, rfl⟩
  obtain ⟨x, hx, hfx⟩ := target_closed_collar_subset_image H J hbd hJ hside
    (show Q ∩ closedTerminalCap H ⊆ Q ∩ closedTerminalCap H from Subset.rfl) hp
  obtain ⟨w, hw, rfl⟩ := hx.2
  refine ⟨Complex.equivRealProdCLM w, ⟨?_, ?_⟩, ?_⟩
  · change ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM w) : ℂ) : Sphere) ∈
      openCompletedRegion T.terminals.H
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hx.1
  · apply hmask
    change ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM w) : ℂ) : Sphere) ∈
      closedTerminalCap H
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using
      (show (w : Sphere) ∈ closedTerminalCap H from ⟨w, hw, rfl⟩)
  · simp only [sphereRealMap, ContinuousLinearEquiv.symm_apply_apply, hfx, finiteCoord_coe]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskedStageTerminalLifts
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual nonsingular terminal branches give real lifts on open
sphere neighborhoods, as required by the finite Stokes estimate. -/

open Set Function Filter Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem exists_sphere_terminal_lift
    (H : ℂ ≃ₜ ℂ) (F : (ℝ × ℝ) → UnitAddCircle) (w : (ℝ × ℝ) → ℝ)
    (E : Set (ℝ × ℝ)) (hE : IsOpen E)
    (hHE : frontier (realJordanInterior H) ⊆ E)
    (hw : ContDiffOn ℝ ∞ w E)
    (hproj : ∀ᶠ x in 𝓝ˢ (frontier (realJordanInterior H)), (w x : UnitAddCircle) = F x) :
    ∃ V : Set Sphere, IsOpen V ∧
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ V ∧
      ContinuousOn (sphereRealFunction w) V ∧
      (∀ x ∈ V, ((sphereRealFunction w x : ℝ) : UnitAddCircle) = sphereRealFunction F x) ∧
      ∀ x ∈ frontier (jordanInterior H), ∀ y ∈ frontier (jordanInterior H),
        |sphereRealFunction w (x : Sphere) - sphereRealFunction w (y : Sphere)| ≤
          Metric.diam (w '' frontier (realJordanInterior H)) := by
  obtain ⟨P, hP, hHP, hPeq⟩ := mem_nhdsSet_iff_exists.mp (sphere_branch_of_real_branch hproj)
  let V := ((↑) : ℂ → Sphere) '' (Complex.equivRealProdCLM ⁻¹' E) ∩ P
  have hVE : IsOpen V :=
    (OnePoint.isOpenEmbedding_coe.isOpenMap _ (hE.preimage Complex.equivRealProdCLM.continuous)).inter hP
  have hHV : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ V := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨⟨z, hHE (by rw [frontier_realJordanInterior]; exact mem_image_of_mem _ hz), rfl⟩,
      hHP (mem_image_of_mem _ hz)⟩
  refine ⟨V, hVE, hHV, ?_, fun _ hx => hPeq hx.2, ?_⟩
  · rintro p ⟨⟨z, hz, rfl⟩, _⟩
    exact (continuousAt_sphereRealFunction (hw.continuousOn.continuousAt (hE.mem_nhds hz))).continuousWithinAt
  · intro x hx y hy
    have hxf : Complex.equivRealProdCLM x ∈ frontier (realJordanInterior H) := by
      rw [frontier_realJordanInterior]
      exact mem_image_of_mem _ hx
    have hyf : Complex.equivRealProdCLM y ∈ frontier (realJordanInterior H) := by
      rw [frontier_realJordanInterior]
      exact mem_image_of_mem _ hy
    have hb : Bornology.IsBounded (w '' frontier (realJordanInterior H)) :=
      ((realJordanInterior_geometry H).2.1.image_of_continuousOn (hw.continuousOn.mono hHE)).isBounded
    simpa only [sphereRealFunction, finiteCoord_coe, Real.dist_eq] using
      Metric.dist_le_diam_of_mem hb (mem_image_of_mem w hxf) (mem_image_of_mem w hyf)

theorem MaskedCoordinateStage.nonsingular_terminal_lift
    {S : Type*} {n : ℕ} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {C : Fin n → MaskedCoordinateData G U π σ}
    {Flag : Set S} {O : S → Set Sphere} {K₀ : Set (ℝ × ℝ)} {ε ρ : ℝ} {k₀ : ℕ}
    (T : MaskedCoordinateStage C Flag O K₀ ε ρ k₀) (l : Fin n) (s : T.indices)
    (hs : σ s ∈ (C l).mask) (hne : σ s ≠ σ (C l).singular) :
    ∃ V : Set Sphere, IsOpen V ∧
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior (T.terminals.H s)) ⊆ V ∧
      ContinuousOn (sphereRealFunction (T.terminal_branch s l)) V ∧
      (∀ x ∈ V, ((sphereRealFunction (T.terminal_branch s l) x : ℝ) : UnitAddCircle) =
        sphereRealFunction (T.model.functions l) x) ∧
      ∀ x ∈ frontier (jordanInterior (T.terminals.H s)),
        ∀ y ∈ frontier (jordanInterior (T.terminals.H s)),
          |sphereRealFunction (T.terminal_branch s l) (x : Sphere) -
            sphereRealFunction (T.terminal_branch s l) (y : Sphere)| ≤
              Metric.diam (T.terminal_branch s l '' frontier (realJordanInterior (T.terminals.H s))) :=
  exists_sphere_terminal_lift (T.terminals.H s) (T.model.functions l) (T.terminal_branch s l)
    (T.terminal_domain s) (T.terminal_open s) (T.terminal_frontier s)
    (T.terminal_lift l s hs hne).1 (T.terminal_lift l s hs hne).2

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskedTerminalLabel
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A terminal inside a physical mask has its original quotient label in
that mask. Nonempty label fibers are supplied by the component quotient. -/

open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem MaskedCoordinateStage.label_mem_mask_of_terminal_inside
    {S : Type*} {n : ℕ} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {C : Fin n → MaskedCoordinateData G U π σ}
    {Flag : Set S} {O : S → Set Sphere} {K₀ : Set (ℝ × ℝ)} {ε ρ : ℝ} {k₀ : ℕ}
    (T : MaskedCoordinateStage C Flag O K₀ ε ρ k₀) (l : Fin n)
    (hinf : OnePoint.infty ∈ G) (hσB : ∀ s, σ s ∈ π '' Gᶜ)
    (H : ℂ ≃ₜ ℂ)
    (hmask : realChartDomain (closedTerminalCap H) ⊆ interior (physicalMask π (C l).mask))
    (s : T.indices)
    (hs : closedTerminalCap (T.terminals.H s) ⊆ ((↑) : ℂ → Sphere) '' jordanInterior H) :
    σ s ∈ (C l).mask := by
  obtain ⟨p, hp, hps⟩ := hσB s
  have hpinf : p ≠ OnePoint.infty := fun he => hp (he ▸ hinf)
  obtain ⟨z, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hpinf
  have hz : z ∈ jordanInterior (T.terminals.H s) := T.terminals.fiber_subset s hps
  have hzH := hs (show (z : Sphere) ∈ closedTerminalCap (T.terminals.H s) from
    ⟨z, subset_closure hz, rfl⟩)
  have hzH' : z ∈ jordanInterior H := OnePoint.coe_injective.mem_set_image.mp hzH
  have hm := interior_subset (hmask (show Complex.equivRealProdCLM z ∈
      realChartDomain (closedTerminalCap H) from by
    change ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM z) : ℂ) : Sphere) ∈ closedTerminalCap H
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact ⟨z, subset_closure hzH', rfl⟩))
  change π ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM z) : ℂ) : Sphere) ∈
    (C l).mask at hm
  simpa only [ContinuousLinearEquiv.symm_apply_apply, hps] using hm

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_RoundExteriorPoint
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every neighborhood of one finite round hole meets the exterior of
all the holes, also when the chosen hole is a point. -/

open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem exists_exterior_point_near_round_hole
    {I : Type*} [Fintype I] (c : I → ℂ) (r : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hd : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    (i : I) {O : Set ℂ} (hO : IsOpen O) (hiO : closedBall (c i) (r i) ⊆ O) :
    ∃ z ∈ O, z ∉ ⋃ j, closedBall (c j) (r j) := by
  obtain ⟨δ, hδ, hdδ⟩ := exists_common_round_hole_offset c r hr hd
    isOpen_univ (fun _ => subset_univ _)
  obtain ⟨η, hη, hηO⟩ := (isCompact_closedBall (c i) (r i)).exists_cthickening_subset_open hO hiO
  let ρ := min δ η / 2
  have hρ : 0 < ρ := half_pos (lt_min hδ hη)
  have hρδ : ρ ≤ δ := (half_le_self (le_of_lt (lt_min hδ hη))).trans (min_le_left _ _)
  have hρη : ρ ≤ η := (half_le_self (le_of_lt (lt_min hδ hη))).trans (min_le_right _ _)
  let z := unitCircleParam (c i) (r i + ρ) 0
  have hz : z ∈ closedBall (c i) (r i + ρ) :=
    sphere_subset_closedBall (circleMap_mem_sphere _ (by linarith [hr i]) _)
  refine ⟨z, ?_, unitCircleParam_mem_round_exterior c r hr hρ (hdδ ρ ⟨hρ, hρδ⟩).2 i 0⟩
  apply hηO
  have hzη : z ∈ closedBall (c i) (r i + η) :=
    closedBall_subset_closedBall (show r i + ρ ≤ r i + η by linarith) hz
  simpa only [cthickening_closedBall hη.le (hr i), add_comm] using hzη

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_TerminalJordanSide
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A target hole inside a retained image collar comes from a source
terminal inside the original collar. The inverse boundary-neighborhood
theorem proves this without a boundary extension. -/

open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem TerminalComponentAssignment.source_inside_of_target_inside
    {I : Type*} [Fintype I] {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (c : I → ℂ) (r : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hd : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    (hext : ((↑) : ℂ → Sphere) ⁻¹' V = (⋃ i, closedBall (c i) (r i))ᶜ)
    (htarget : ∀ i, ((↑) : ℂ → Sphere) '' closedBall (c i) (r i) ⊆
      connectedComponentIn Vᶜ (a.point i))
    (H J : ℂ ≃ₜ ℂ)
    (hbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ openCompletedRegion T)
    (hside : f '' (openCompletedRegion T ∩ (((↑) : ℂ → Sphere) '' jordanInterior H)) =
      V ∩ (((↑) : ℂ → Sphere) '' jordanInterior J))
    (i : I) (hin : closedBall (c i) (r i) ⊆ jordanInterior J) :
    closedTerminalCap (T i) ⊆ ((↑) : ℂ → Sphere) '' jordanInterior H := by
  let A : Set Sphere := ((↑) : ℂ → Sphere) '' jordanInterior H
  have hAo : IsOpen A := OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen H)
  have hAf : frontier A = ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) :=
    frontier_sphere_image_jordanInterior H
  have hav : Disjoint (closedTerminalCap (T i)) (frontier A) := by
    apply Set.disjoint_left.mpr
    intro x hx hxf
    exact (hbd (hAf ▸ hxf)) (mem_iUnion.mpr ⟨i, hx⟩)
  have hcover : closedTerminalCap (T i) ⊆ A ∪ (closure A)ᶜ := by
    intro x hx
    by_cases hxa : x ∈ A
    · exact Or.inl hxa
    · exact Or.inr (fun hc => Set.disjoint_left.mp hav hx ⟨hc, hAo.interior_eq.symm ▸ hxa⟩)
  rcases (isPreconnected_closedTerminalCap (T i)).subset_or_subset hAo
    isClosed_closure.isOpen_compl
    (Set.disjoint_left.mpr (fun _ h h' => h' (subset_closure h))) hcover with hs | hs
  · exact hs
  · obtain ⟨W, hW, hcomp, hmap⟩ := a.inverse_boundary_neighborhood hf
      isClosed_closure.isOpen_compl
      (fun x hx => hs (by obtain ⟨z, hz, rfl⟩ := hx; exact ⟨z, frontier_subset_closure hz, rfl⟩))
    have hopen : IsOpen (((↑) : ℂ → Sphere) ⁻¹' W ∩ jordanInterior J) :=
      (hW.preimage OnePoint.continuous_coe).inter (jordanInterior_isOpen J)
    have hball : closedBall (c i) (r i) ⊆ ((↑) : ℂ → Sphere) ⁻¹' W ∩ jordanInterior J :=
      fun z hz => ⟨hcomp (htarget i (mem_image_of_mem _ hz)), hin hz⟩
    obtain ⟨z, hz, hzout⟩ := exists_exterior_point_near_round_hole c r hr hd i hopen hball
    have hzV : (z : Sphere) ∈ V := by
      change z ∈ ((↑) : ℂ → Sphere) ⁻¹' V
      rw [hext]
      exact hzout
    have hfi := hmap (z : Sphere) ⟨hz.1, hzV⟩
    obtain ⟨x, hx, he⟩ := hside.symm ▸
      (show (z : Sphere) ∈ V ∩ (((↑) : ℂ → Sphere) '' jordanInterior J) from
        ⟨hzV, z, hz.2, rfl⟩)
    have hfix : fi (z : Sphere) = x := by rw [← he, hf.left_inv x hx.1]
    rw [hfix] at hfi
    exact (hfi (subset_closure hx.2)).elim

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_TerminalJordanForward
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The converse collar incidence: a source terminal in the retained
bounded side has its assigned target component in the target bounded side. -/

open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem TerminalComponentAssignment.target_inside_of_source_inside
    {I : Type*} [Finite I] {T : I → ℂ ≃ₜ ℂ}
    (hTd : Pairwise (Disjoint on fun i => closure (jordanInterior (T i))))
    {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (_hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (H J : ℂ ≃ₜ ℂ)
    (hbdJ : ((↑) : ℂ → Sphere) '' frontier (jordanInterior J) ⊆ V)
    (hside : f '' (openCompletedRegion T ∩ (((↑) : ℂ → Sphere) '' jordanInterior H)) =
      V ∩ (((↑) : ℂ → Sphere) '' jordanInterior J))
    (i : I) (hin : closedTerminalCap (T i) ⊆ ((↑) : ℂ → Sphere) '' jordanInterior H) :
    connectedComponentIn Vᶜ (a.point i) ⊆ ((↑) : ℂ → Sphere) '' jordanInterior J := by
  let A : Set Sphere := ((↑) : ℂ → Sphere) '' jordanInterior J
  have hAo : IsOpen A := OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen J)
  have hAf : frontier A = ((↑) : ℂ → Sphere) '' frontier (jordanInterior J) :=
    frontier_sphere_image_jordanInterior J
  have hav : Disjoint (connectedComponentIn Vᶜ (a.point i)) (frontier A) := by
    exact Set.disjoint_left.mpr (fun _ h h' =>
      connectedComponentIn_subset _ _ h (hbdJ (hAf ▸ h')))
  obtain ⟨q, hq⟩ := (isConnected_frontier_jordanInterior (T i)).nonempty
  have hqcap : (q : Sphere) ∈ closedTerminalCap (T i) := ⟨q, frontier_subset_closure hq, rfl⟩
  have hqcl : (q : Sphere) ∈ closure (openCompletedRegion T) := by
    rw [← interior_closedJordanCore, closure_interior_closedJordanCore T hTd]
    intro hu
    obtain ⟨j, z, hz, he⟩ := mem_iUnion.mp hu
    have hzq := OnePoint.coe_injective he
    subst z
    by_cases hji : j = i
    · subst j
      exact hq.2 ((jordanInterior_isOpen (T i)).interior_eq.symm ▸ hz)
    · exact Set.disjoint_left.mp (hTd hji) (subset_closure hz) (frontier_subset_closure hq)
  obtain ⟨x, hxQ, hx⟩ := mem_closure_iff_seq_limit.mp hqcl
  obtain ⟨y, _, s, hs, hy⟩ := isCompact_univ.tendsto_subseq (fun n => mem_univ (f (x n)))
  have hys : y ∈ connectedComponentIn Vᶜ (a.point i) :=
    a.cluster i (q : Sphere) hqcap (x ∘ s) (hx.comp hs.tendsto_atTop)
      (Eventually.of_forall fun n => hxQ (s n)) y hy
  have hxH : ∀ᶠ n in atTop, x (s n) ∈ ((↑) : ℂ → Sphere) '' jordanInterior H :=
    (hx.comp hs.tendsto_atTop).eventually
      ((OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen H)).mem_nhds (hin hqcap))
  have hycl : y ∈ closure A := by
    apply mem_closure_of_tendsto hy
    filter_upwards [hxH] with n hn
    have hh : f (x (s n)) ∈ V ∩ (((↑) : ℂ → Sphere) '' jordanInterior J) := by
      rw [← hside]
      exact mem_image_of_mem f ⟨hxQ (s n), hn⟩
    exact hh.2
  have hyA : y ∈ A := by
    by_contra hn
    exact Set.disjoint_left.mp hav hys ⟨hycl, hAo.interior_eq.symm ▸ hn⟩
  have hcover : connectedComponentIn Vᶜ (a.point i) ⊆ A ∪ (closure A)ᶜ := by
    intro z hz
    by_cases hza : z ∈ A
    · exact Or.inl hza
    · exact Or.inr (fun hc => Set.disjoint_left.mp hav hz ⟨hc, hAo.interior_eq.symm ▸ hza⟩)
  exact isPreconnected_connectedComponentIn.subset_left_of_subset_union hAo
    isClosed_closure.isOpen_compl
    (Set.disjoint_left.mpr (fun _ h h' => h' (subset_closure h))) hcover ⟨y, hys, hyA⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RegularJordanParametrization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Regular Jordan circuits with either orientation. The absolute Stokes
estimate does not need a choice of orientation. -/

open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem PositiveJordanParametrization.toRegular
    {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ} (hγ : PositiveJordanParametrization H γ) :
    RegularJordanParametrization H γ :=
  ⟨hγ.smooth, hγ.periodic, hγ.injective, hγ.regular, hγ.boundary⟩

 theorem RegularJordanParametrization.mem_frontier
    {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ} (hγ : RegularJordanParametrization H γ) (t : ℝ) :
    γ t ∈ frontier (jordanInterior H) := by
  have he : γ (Int.fract t) = γ t := by
    simpa only [Int.fract, mul_one] using hγ.periodic.sub_int_mul_eq (x := t) ⌊t⌋
  rw [← he]
  exact hγ.boundary ▸ mem_image_of_mem γ
    (show Int.fract t ∈ Icc (0 : ℝ) 1 from ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_UnorientedCircleGreen
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The orientation-independent form of the same published Green input.

M. Spivak, Calculus on Manifolds (1965), Theorem 5-5, p.124. A regular
once-traversed Jordan boundary has one of the two orientations; the sign
below changes its integral to the positive boundary orientation. Inner
circles retain their positive disk orientation. This is the signed
parametrized specialization of the same manifold Stokes theorem cited in
`FiniteCircleGreen.lean`, not an energy or uniformization assumption.
The sign is chosen before the holes and the differential form.
-/

open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem finiteCircleGreen_regular_weighted_closed_form
    (hgreen : UnorientedFiniteCircleGreenFormula)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : RegularJordanParametrization H γ)
    (n : ℕ) (c : Fin n → ℂ) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (hd : Pairwise (Disjoint on fun i => Metric.closedBall (c i) (r i)))
    (hin : ∀ i, Metric.closedBall (c i) (r i) ⊆ jordanInterior H)
    (O : Set ℂ) (hO : IsOpen O)
    (hsub : (closure (jordanInterior H) \ ⋃ i, Metric.ball (c i) (r i)) ⊆ O)
    (φ P Q : ℂ → ℝ) (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ O)
    (hP : ContDiffOn ℝ (⊤ : ℕ∞) P O) (hQ : ContDiffOn ℝ (⊤ : ℕ∞) Q O)
    (hclosed : ∀ z ∈ O, (fderiv ℝ Q z) 1 = (fderiv ℝ P z) Complex.I) :
    ∃ e : ℝ, |e| = 1 ∧
      e * planarFormIntegral (φ * P) (φ * Q) γ -
        ∑ i, planarFormIntegral (φ * P) (φ * Q) (unitCircleParam (c i) (r i)) =
        ∫ z in jordanInterior H \ ⋃ i, Metric.closedBall (c i) (r i),
          (fderiv ℝ φ z) 1 * Q z - (fderiv ℝ φ z) Complex.I * P z := by
  obtain ⟨e, he, hg⟩ := hgreen H γ hγ
  refine ⟨e, he, ?_⟩
  rw [hg n c r hr hd hin O hO hsub (φ * P) (φ * Q) (hφ.mul hP) (hφ.mul hQ)]
  apply setIntegral_congr_fun
  · exact (jordanInterior_isOpen H).measurableSet.diff
      (MeasurableSet.iUnion fun _ => isClosed_closedBall.measurableSet)
  · intro z hz
    have hzO : z ∈ O := hsub ⟨subset_closure hz.1, fun hm => by
      obtain ⟨i, hi⟩ := mem_iUnion.mp hm
      exact hz.2 (mem_iUnion.mpr ⟨i, Metric.ball_subset_closedBall hi⟩)⟩
    have hφd := (hφ.differentiableOn (by simp)).differentiableAt (hO.mem_nhds hzO)
    have hPd := (hP.differentiableOn (by simp)).differentiableAt (hO.mem_nhds hzO)
    have hQd := (hQ.differentiableOn (by simp)).differentiableAt (hO.mem_nhds hzO)
    change (fderiv ℝ (φ * Q) z) 1 - (fderiv ℝ (φ * P) z) Complex.I = _
    rw [fderiv_mul hφd hQd, fderiv_mul hφd hPd]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    rw [hclosed z hzO]
    ring

 theorem finite_circle_stokes_area_bound_regular
    (hgreen : UnorientedFiniteCircleGreenFormula)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : RegularJordanParametrization H γ)
    (n : ℕ) (c : Fin n → ℂ) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (hd : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    (hin : ∀ i, closedBall (c i) (r i) ⊆ jordanInterior H)
    (O : Set ℂ) (hO : IsOpen O)
    (hsub : (closure (jordanInterior H) \ ⋃ i, ball (c i) (r i)) ⊆ O)
    (φ : ℂ → ℝ) (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ O) (hφlip : LipschitzWith 1 φ)
    (u : ℂ → UnitAddCircle) (hu : SmoothCircleOn u O)
    {R : ℝ} (hR : 0 ≤ R)
    (hbounded : jordanInterior H \ ⋃ i, closedBall (c i) (r i) ⊆ closedBall 0 R)
    (henergy : MemLp (circleFDeriv u) 2
      (volume.restrict (jordanInterior H \ ⋃ i, closedBall (c i) (r i)))) :
    ∃ e : ℝ, |e| = 1 ∧
    |e * circleFormIntegral φ u γ - ∑ i, circleFormIntegral φ u (unitCircleParam (c i) (r i))| ≤
      Real.sqrt Real.pi * R * Real.sqrt
        (∫ z in jordanInterior H \ ⋃ i, closedBall (c i) (r i), ‖circleFDeriv u z‖ ^ 2) := by
  have hc := contDiffOn_circleFDeriv hO hu
  obtain ⟨e, he, hformula⟩ := finiteCircleGreen_regular_weighted_closed_form hgreen H γ hγ n c r hr hd hin O hO hsub
    φ (fun z => circleFDeriv u z 1) (fun z => circleFDeriv u z Complex.I) hφ
    (hc.clm_apply contDiffOn_const) (hc.clm_apply contDiffOn_const)
    (fun z hz => circleFDeriv_closed_complex hO hu hz)
  refine ⟨e, he, ?_⟩
  change |e * planarFormIntegral _ _ γ - ∑ i, planarFormIntegral _ _ (unitCircleParam (c i) (r i))| ≤ _
  rw [hformula]
  have hΩ : MeasurableSet (jordanInterior H \ ⋃ i, closedBall (c i) (r i)) :=
    (jordanInterior_isOpen H).measurableSet.diff (MeasurableSet.iUnion fun _ => isClosed_closedBall.measurableSet)
  have hΩO : jordanInterior H \ ⋃ i, closedBall (c i) (r i) ⊆ O := by
    intro z hz
    apply hsub
    refine ⟨subset_closure hz.1, ?_⟩
    intro hm
    obtain ⟨i, hi⟩ := mem_iUnion.mp hm
    exact hz.2 (mem_iUnion.mpr ⟨i, ball_subset_closedBall hi⟩)
  exact integral_complexCovector_wedge_le hΩ hR hbounded (fderiv ℝ φ) (circleFDeriv u)
    ((hφ.fderiv_of_isOpen (m := 0) hO (by simp)).continuousOn.mono hΩO)
    (hc.continuousOn.mono hΩO) henergy (fun z _ => by
      simpa only [NNReal.coe_one] using norm_fderiv_le_of_lipschitz ℝ hφlip (x₀ := z))


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_RegularOffsetStokes
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Offset estimates with either orientation of the outer regular circuit. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology BigOperators
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem finite_offset_stokes_bound_with_period_regular
    (hgreen : UnorientedFiniteCircleGreenFormula)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : RegularJordanParametrization H γ)
    (n : ℕ) (c : Fin n → ℂ) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (hd : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    (hin : ∀ i, closedBall (c i) (r i) ⊆ jordanInterior H)
    (O : Set ℂ) (hO : IsOpen O)
    (hsub : (closure (jordanInterior H) \ ⋃ i, ball (c i) (r i)) ⊆ O)
    (φ : ℂ → ℝ) (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ O) (hφlip : LipschitzWith 1 φ)
    (u : ℂ → UnitAddCircle) (hu : SmoothCircleOn u O)
    {R : ℝ} (hR : 0 ≤ R)
    (hbounded : jordanInterior H \ ⋃ i, closedBall (c i) (r i) ⊆ closedBall 0 R)
    (henergy : MemLp (circleFDeriv u) 2
      (volume.restrict (jordanInterior H \ ⋃ i, closedBall (c i) (r i))))
    (b : Fin n) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (v : Fin n → ℝ → ℝ) (hv : ∀ i, Continuous (v i))
    (hproj : ∀ i t, (v i t : UnitAddCircle) = u (unitCircleParam (c i) (r i) t))
    (hφb : ∀ t ∈ Icc (0 : ℝ) 1, φ (unitCircleParam (c b) (r b) t) = ρ)
    (hzero : ∀ i ≠ b, v i 1 = v i 0)
    (A : Fin n → ℝ) (hA : ∀ i ≠ b, ∀ t ∈ Icc (0 : ℝ) 1, |v i t - v i 0| ≤ A i) :
    |circleFormIntegral φ u γ| ≤
      Real.sqrt Real.pi * R * Real.sqrt
        (∫ z in jordanInterior H \ ⋃ i, closedBall (c i) (r i), ‖circleFDeriv u z‖ ^ 2) +
      ρ * |v b 1 - v b 0| + ∑ i ∈ Finset.univ.erase b, 2 * Real.pi * r i * A i := by
  have hc (i : Fin n) := circle_boundary_mem_smooth_region H c r
    (fun i => (hr i).le) hd hin hsub i
  obtain ⟨e, he, harea⟩ := finite_circle_stokes_area_bound_regular hgreen H γ hγ
    n c r hr hd hin O hO hsub φ hφ hφlip u hu hR hbounded henergy
  have hresult := abs_le_of_boundary_costs b _ _ _ (ρ * |v b 1 - v b 0|)
    (fun i => 2 * Real.pi * r i * A i) harea
  rw [abs_mul, he, one_mul] at hresult
  apply hresult
  · rw [circleFormIntegral_constant_weight hO hu φ _ (contDiff_unitCircleParam _ _)
      (hc b) (v b) (hv b) (hproj b) ρ hφb, abs_mul, abs_of_nonneg hρ]
  · intro i hi
    exact circleFormIntegral_unitCircle_zero_period hO hu φ hφ hφlip _ (hr i).le
      (hc i) (v i) (hv i) (hproj i) (hzero i hi) (A i) (hA i hi)


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_RegularAnnulusStokes
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Function Filter MeasureTheory Metric
open scoped Topology BigOperators
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem finite_annulus_stokes_bound_regular
    (hgreen : UnorientedFiniteCircleGreenFormula)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : RegularJordanParametrization H γ)
    (n : ℕ) (c : Fin n → ℂ) (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hd : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    (hin : ∀ i, closedBall (c i) (r i) ⊆ jordanInterior H)
    (O : Set ℂ) (hO : IsOpen O)
    (hsub : (closure (jordanInterior H) \ ⋃ i, closedBall (c i) (r i)) ⊆ O)
    (u : ℂ → UnitAddCircle) (hu : SmoothCircleOn u O)
    {L : ℝ} (hL : 0 ≤ L) (hbounded : jordanInterior H ⊆ closedBall 0 L)
    (henergy : MemLp (circleFDeriv u) 2
      (volume.restrict (jordanInterior H \ ⋃ i, closedBall (c i) (r i))))
    (b : Fin n) (A : Fin n → ℝ) (hA : ∀ i ≠ b, 0 ≤ A i)
    (hcollars : ∀ ε > 0, ∃ δ > 0, ∀ ρ ∈ Ioo (0 : ℝ) δ,
      ∃ v : Fin n → ℝ → ℝ, ∀ i ≠ b,
        Continuous (v i) ∧
        (∀ t, (v i t : UnitAddCircle) = u (unitCircleParam (c i) (r i + ρ) t)) ∧
        v i 1 = v i 0 ∧
        ∀ t ∈ Icc (0 : ℝ) 1, |v i t - v i 0| ≤ A i + ε) :
    |circleFormIntegral (fun z => infDist z (closedBall (c b) (r b))) u γ| ≤
      Real.sqrt Real.pi * L * Real.sqrt
        (∫ z in jordanInterior H \ ⋃ i, closedBall (c i) (r i), ‖circleFDeriv u z‖ ^ 2) +
      ∑ i ∈ Finset.univ.erase b, 2 * Real.pi * r i * A i := by
  classical
  obtain ⟨δG, hδG, hgeom⟩ := exists_common_round_hole_offset c r hr hd
    (jordanInterior_isOpen H) hin
  have hcircle (ρ : ℝ) (hρ : ρ ∈ Ioo (0 : ℝ) δG) (i : Fin n) (t : ℝ) :
      unitCircleParam (c i) (r i + ρ) t ∈ O := by
    obtain ⟨hinside, hdisj⟩ := hgeom ρ ⟨hρ.1, hρ.2.le⟩
    exact circle_boundary_mem_smooth_region H c (fun j => r j + ρ)
      (fun j => by linarith [hr j, hρ.1]) hdisj hinside
      ((offset_closed_region_subset H c r hρ.1).trans hsub) i t
  obtain ⟨vB, k, hB⟩ := exists_constant_period_round_collars hu.continuousOn (c b) (r b) hδG
    (fun ρ hρ => hcircle ρ hρ b)
  apply zero_offset_stokes_bound_of_period (Finset.univ.erase b) r A
    (fun i hi => hA i (Finset.mem_erase.mp hi).1) _ _ k
  intro ε hε
  obtain ⟨δC, hδC, hC⟩ := hcollars ε hε
  let ρ := min (ε / 2) (min (δG / 2) (δC / 2))
  have hρ : 0 < ρ := lt_min (half_pos hε) (lt_min (half_pos hδG) (half_pos hδC))
  have hρε : ρ ≤ ε := (min_le_left _ _).trans (half_le_self hε.le)
  have hρG : ρ < δG :=
    ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hδG)
  have hρC : ρ < δC :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (half_lt_self hδC)
  obtain ⟨v₀, hv₀⟩ := hC ρ ⟨hρ, hρC⟩
  let v : Fin n → ℝ → ℝ := fun i => if i = b then vB ρ else v₀ i
  have hv (i : Fin n) : Continuous (v i) := by
    by_cases hi : i = b
    · subst i
      simpa only [v, ite_eq_left rfl] using (hB ρ ⟨hρ, hρG⟩).1
    · simpa only [v, ite_eq_right hi] using (hv₀ i hi).1
  have hvp (i : Fin n) (t : ℝ) :
      (v i t : UnitAddCircle) = u (unitCircleParam (c i) (r i + ρ) t) := by
    by_cases hi : i = b
    · subst i
      simpa only [v, ite_eq_left rfl] using (hB ρ ⟨hρ, hρG⟩).2.1 t
    · simpa only [v, ite_eq_right hi] using (hv₀ i hi).2.1 t
  have hvzero (i : Fin n) (hi : i ≠ b) : v i 1 = v i 0 := by
    simpa only [v, ite_eq_right hi] using (hv₀ i hi).2.2.1
  have hvosc (i : Fin n) (hi : i ≠ b) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      |v i t - v i 0| ≤ (fun j => A j + ε) i := by
    simpa only [v, ite_eq_right hi] using (hv₀ i hi).2.2.2 t ht
  have hvb : v b 1 - v b 0 = k := by
    simpa only [v, ite_eq_left rfl] using (hB ρ ⟨hρ, hρG⟩).2.2
  let Oρ := O ∩ (closedBall (c b) (r b))ᶜ
  have hOρ : IsOpen Oρ := hO.inter isClosed_closedBall.isOpen_compl
  have hsubρ : closure (jordanInterior H) \ ⋃ i, ball (c i) (r i + ρ) ⊆ Oρ := by
    intro z hz
    have hbase := offset_closed_region_subset H c r hρ hz
    exact ⟨hsub hbase, fun hm => hbase.2 (mem_iUnion.mpr ⟨b, hm⟩)⟩
  have hregion := offset_open_region_subset H c r hρ.le
  have henergyρ : MemLp (circleFDeriv u) 2
      (volume.restrict (jordanInterior H \ ⋃ i, closedBall (c i) (r i + ρ))) :=
    MemLp.mono_measure (Measure.restrict_mono hregion le_rfl) henergy
  obtain ⟨hinside, hdisj⟩ := hgeom ρ ⟨hρ, hρG.le⟩
  have he := finite_offset_stokes_bound_with_period_regular hgreen H γ hγ n c (fun i => r i + ρ)
    (fun i => by linarith [hr i]) hdisj hinside Oρ hOρ hsubρ
    (fun z => infDist z (closedBall (c b) (r b)))
    ((contDiffOn_infDist_closedBall (c b) (hr b)).mono inter_subset_right)
    (lipschitz_infDist_pt _) u (fun z hz => hu z hz.1) hL
    (fun z hz => hbounded hz.1) henergyρ b ρ hρ.le v hv hvp
    (fun t _ => infDist_closedBall_unitCircle_offset (c b) (hr b) hρ t) hvzero
    (fun i => A i + ε) hvosc
  rw [hvb] at he
  have hE := mul_le_mul_of_nonneg_left (circle_energy_mono hregion u henergy)
    (mul_nonneg (Real.sqrt_nonneg Real.pi) hL)
  refine ⟨ρ, hρ, hρε, ?_⟩
  linarith


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RegularAssignedStokes
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Function Filter MeasureTheory Metric
open scoped Topology BigOperators
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem assigned_model_stokes_bound_regular
    (hgreen : UnorientedFiniteCircleGreenFormula)
    {I : Type*} [Fintype I] {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (c : I → ℂ) (r : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hd : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    (hext : ((↑) : ℂ → Sphere) ⁻¹' V = (⋃ i, closedBall (c i) (r i))ᶜ)
    (htarget : ∀ i, ((↑) : ℂ → Sphere) '' closedBall (c i) (r i) ⊆
      connectedComponentIn Vᶜ (a.point i))
    (n : ℕ) (κ : Fin n → I) (hκ : Injective κ) (b : Fin n)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : RegularJordanParametrization H γ)
    (hin : ∀ j, closedBall (c (κ j)) (r (κ j)) ⊆ jordanInterior H)
    (O : Set ℂ) (hO : IsOpen O)
    (hsub : (closure (jordanInterior H) \ ⋃ j, closedBall (c (κ j)) (r (κ j))) ⊆ O)
    (w : Sphere → UnitAddCircle)
    (hu : SmoothCircleOn (fun z : ℂ => w (fi (z : Sphere))) O)
    {L : ℝ} (hL : 0 ≤ L) (hbounded : jordanInterior H ⊆ closedBall 0 L)
    (henergy : MemLp (circleFDeriv (fun z : ℂ => w (fi (z : Sphere)))) 2
      (volume.restrict (jordanInterior H \ ⋃ j, closedBall (c (κ j)) (r (κ j)))))
    (U : Fin n → Set Sphere) (v : Fin n → Sphere → ℝ)
    (hU : ∀ j ≠ b, IsOpen (U j))
    (hboundary : ∀ j ≠ b, ((↑) : ℂ → Sphere) '' frontier (jordanInterior (T (κ j))) ⊆ U j)
    (hv : ∀ j ≠ b, ContinuousOn (v j) (U j))
    (hproj : ∀ j ≠ b, ∀ x ∈ U j, (v j x : UnitAddCircle) = w x)
    (A : Fin n → ℝ) (hA : ∀ j ≠ b, ∀ x ∈ frontier (jordanInterior (T (κ j))),
      ∀ y ∈ frontier (jordanInterior (T (κ j))), |v j (x : Sphere) - v j (y : Sphere)| ≤ A j) :
    |circleFormIntegral (fun z => infDist z (closedBall (c (κ b)) (r (κ b))))
      (fun z : ℂ => w (fi (z : Sphere))) γ| ≤
      Real.sqrt Real.pi * L * Real.sqrt
        (∫ z in jordanInterior H \ ⋃ j, closedBall (c (κ j)) (r (κ j)),
          ‖circleFDeriv (fun z : ℂ => w (fi (z : Sphere))) z‖ ^ 2) +
      ∑ j ∈ Finset.univ.erase b, 2 * Real.pi * r (κ j) * A j := by
  classical
  apply finite_annulus_stokes_bound_regular hgreen H γ hγ n (c ∘ κ) (r ∘ κ) (fun j => hr (κ j))
    (fun j k hjk => hd (fun he => hjk (hκ he))) hin O hO hsub _ hu hL hbounded henergy b A
  · intro j hj
    obtain ⟨x, hx⟩ := (isConnected_frontier_jordanInterior (T (κ j))).nonempty
    simpa only [sub_self, abs_zero] using hA j hj x hx x hx
  · intro ε hε
    have hex (j : Fin n) : ∃ δ > 0, ∀ ρ ∈ Ioo (0 : ℝ) δ, j ≠ b →
        Continuous (roundCollarRealLift fi (v j) (c (κ j)) (r (κ j) + ρ)) ∧
        (∀ t, (roundCollarRealLift fi (v j) (c (κ j)) (r (κ j) + ρ) t : UnitAddCircle) =
          w (fi (unitCircleParam (c (κ j)) (r (κ j) + ρ) t : Sphere))) ∧
        roundCollarRealLift fi (v j) (c (κ j)) (r (κ j) + ρ) 1 =
          roundCollarRealLift fi (v j) (c (κ j)) (r (κ j) + ρ) 0 ∧
        ∀ t ∈ Icc (0 : ℝ) 1, |roundCollarRealLift fi (v j) (c (κ j)) (r (κ j) + ρ) t -
          roundCollarRealLift fi (v j) (c (κ j)) (r (κ j) + ρ) 0| ≤ A j + ε := by
      by_cases hj : j = b
      · exact ⟨1, zero_lt_one, fun _ _ hne => (hne hj).elim⟩
      · obtain ⟨δ, hδ, hvalid⟩ := a.exists_round_collar_lifts hf c r hr hd hext (κ j) (htarget (κ j))
          (hU j hj) (hboundary j hj) (v j) (hv j hj) w (hproj j hj) (A j) (hA j hj) hε
        exact ⟨δ, hδ, fun ρ hρ _ => hvalid ρ ⟨hρ.1, hρ.2.le⟩⟩
    choose d hdpos hvalid using hex
    obtain ⟨δ, hδ, hδle⟩ := exists_common_positive_bound d hdpos
    refine ⟨δ, hδ, ?_⟩
    intro ρ hρ
    exact ⟨fun j => roundCollarRealLift fi (v j) (c (κ j)) (r (κ j) + ρ),
      fun j hj => hvalid j ρ ⟨hρ.1, hρ.2.trans_le (hδle j)⟩ hj⟩

 theorem assigned_model_stokes_band_bound_regular
    (hgreen : UnorientedFiniteCircleGreenFormula)
    {I S : Type*} [Fintype I] {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (c : I → ℂ) (r : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hd : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    (hext : ((↑) : ℂ → Sphere) ⁻¹' V = (⋃ i, closedBall (c i) (r i))ᶜ)
    (htarget : ∀ i, ((↑) : ℂ → Sphere) '' closedBall (c i) (r i) ⊆
      connectedComponentIn Vᶜ (a.point i))
    (n : ℕ) (κ : Fin n → I) (hκ : Injective κ) (b : Fin n)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : RegularJordanParametrization H γ)
    (hin : ∀ j, closedBall (c (κ j)) (r (κ j)) ⊆ jordanInterior H)
    (O : Set ℂ) (hO : IsOpen O)
    (hsub : (closure (jordanInterior H) \ ⋃ j, closedBall (c (κ j)) (r (κ j))) ⊆ O)
    (w : Sphere → UnitAddCircle)
    (hu : SmoothCircleOn (fun z : ℂ => w (fi (z : Sphere))) O)
    {L : ℝ} (hL : 0 ≤ L) (hbounded : jordanInterior H ⊆ closedBall 0 L)
    (henergy : MemLp (circleFDeriv (fun z : ℂ => w (fi (z : Sphere)))) 2
      (volume.restrict (jordanInterior H \ ⋃ j, closedBall (c (κ j)) (r (κ j)))))
    (U : Fin n → Set Sphere) (v : Fin n → Sphere → ℝ)
    (hU : ∀ j ≠ b, IsOpen (U j))
    (hboundary : ∀ j ≠ b, ((↑) : ℂ → Sphere) '' frontier (jordanInterior (T (κ j))) ⊆ U j)
    (hv : ∀ j ≠ b, ContinuousOn (v j) (U j))
    (hproj : ∀ j ≠ b, ∀ x ∈ U j, (v j x : UnitAddCircle) = w x)
    (A : Fin n → ℝ) (hA : ∀ j ≠ b, ∀ x ∈ frontier (jordanInterior (T (κ j))),
      ∀ y ∈ frontier (jordanInterior (T (κ j))), |v j (x : Sphere) - v j (y : Sphere)| ≤ A j)
    (label : I → S) (hlabel : Injective label)
    (band : S → ℝ) (hband : Summable (fun s => band s ^ 2)) (hb : ∀ s, 0 ≤ band s)
    {η : ℝ} (hexcess : Real.sqrt
      (∑ j, max (A j - band (label (κ j))) 0 ^ 2) ≤ η) :
    |circleFormIntegral (fun z => infDist z (closedBall (c (κ b)) (r (κ b))))
      (fun z : ℂ => w (fi (z : Sphere))) γ| ≤
      Real.sqrt Real.pi * L * Real.sqrt
        (∫ z in jordanInterior H \ ⋃ j, closedBall (c (κ j)) (r (κ j)),
          ‖circleFDeriv (fun z : ℂ => w (fi (z : Sphere))) z‖ ^ 2) +
      2 * Real.pi * L *
        (Real.sqrt (∑' s : {s : S // s ≠ label (κ b)}, band s ^ 2) + η) := by
  classical
  have hnonneg (j : Fin n) (hj : j ≠ b) : 0 ≤ A j := by
    obtain ⟨x, hx⟩ := (isConnected_frontier_jordanInterior (T (κ j))).nonempty
    simpa only [sub_self, abs_zero] using hA j hj x hx x hx
  have hradius : (∑ j, r (κ j) ^ 2) ≤ L ^ 2 :=
    sum_radii_sq_le_of_disjoint_closed_disks (c ∘ κ) (r ∘ κ)
      (fun j => hr (κ j)) hL (fun j k hjk => hd (fun h => hjk (hκ h)))
      (fun j => (hin j).trans hbounded)
  exact circle_stokes_bound_off_distinguished (label ∘ κ) (hlabel.comp hκ) b band hband
    (r ∘ κ) A hnonneg hb hL hradius hexcess
    (assigned_model_stokes_bound_regular hgreen a hf c r hr hd hext htarget n κ hκ b H γ hγ
      hin O hO hsub w hu hL hbounded henergy U v hU hboundary hv hproj A hA)

 theorem assigned_model_stokes_nonsingular_bound_regular
    (hgreen : UnorientedFiniteCircleGreenFormula)
    {I S : Type*} [Fintype I] {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (c : I → ℂ) (r : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hd : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    (hext : ((↑) : ℂ → Sphere) ⁻¹' V = (⋃ i, closedBall (c i) (r i))ᶜ)
    (htarget : ∀ i, ((↑) : ℂ → Sphere) '' closedBall (c i) (r i) ⊆
      connectedComponentIn Vᶜ (a.point i))
    (n : ℕ) (κ : Fin n → I) (hκ : Injective κ) (b : Fin n)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : RegularJordanParametrization H γ)
    (hin : ∀ j, closedBall (c (κ j)) (r (κ j)) ⊆ jordanInterior H)
    (O : Set ℂ) (hO : IsOpen O)
    (hsub : (closure (jordanInterior H) \ ⋃ j, closedBall (c (κ j)) (r (κ j))) ⊆ O)
    (w : Sphere → UnitAddCircle)
    (hu : SmoothCircleOn (fun z : ℂ => w (fi (z : Sphere))) O)
    {L : ℝ} (hL : 0 ≤ L) (hbounded : jordanInterior H ⊆ closedBall 0 L)
    (henergy : MemLp (circleFDeriv (fun z : ℂ => w (fi (z : Sphere)))) 2
      (volume.restrict (jordanInterior H \ ⋃ j, closedBall (c (κ j)) (r (κ j)))))
    (U : Fin n → Set Sphere) (v : Fin n → Sphere → ℝ)
    (hU : ∀ j ≠ b, IsOpen (U j))
    (hboundary : ∀ j ≠ b, ((↑) : ℂ → Sphere) '' frontier (jordanInterior (T (κ j))) ⊆ U j)
    (hv : ∀ j ≠ b, ContinuousOn (v j) (U j))
    (hproj : ∀ j ≠ b, ∀ x ∈ U j, (v j x : UnitAddCircle) = w x)
    (A : Fin n → ℝ) (hA : ∀ j ≠ b, ∀ x ∈ frontier (jordanInterior (T (κ j))),
      ∀ y ∈ frontier (jordanInterior (T (κ j))), |v j (x : Sphere) - v j (y : Sphere)| ≤ A j)
    (label : I → S) (hlabel : Injective label)
    (band : S → ℝ) (hband : Summable (fun s => band s ^ 2)) (hb : ∀ s, 0 ≤ band s)
    {η : ℝ} (hexcess : Real.sqrt
      (∑ j : {j : Fin n // j ≠ b}, max (A j - band (label (κ j))) 0 ^ 2) ≤ η) :
    |circleFormIntegral (fun z => infDist z (closedBall (c (κ b)) (r (κ b))))
      (fun z : ℂ => w (fi (z : Sphere))) γ| ≤
      Real.sqrt Real.pi * L * Real.sqrt
        (∫ z in jordanInterior H \ ⋃ j, closedBall (c (κ j)) (r (κ j)),
          ‖circleFDeriv (fun z : ℂ => w (fi (z : Sphere))) z‖ ^ 2) +
      2 * Real.pi * L *
        (Real.sqrt (∑' s : {s : S // s ≠ label (κ b)}, band s ^ 2) + η) := by
  classical
  let A' (j : Fin n) := if j = b then band (label (κ j)) else A j
  have hAe (j : Fin n) (hj : j ≠ b) : A' j = A j := ite_eq_right hj
  have heq : (∑ j, max (A' j - band (label (κ j))) 0 ^ 2) =
      ∑ j : {j : Fin n // j ≠ b}, max (A j - band (label (κ j))) 0 ^ 2 := by
    rw [sum_off_distinguished b (fun j : Fin n => max (A j - band (label (κ j))) 0 ^ 2)]
    calc
      _ = ∑ j ∈ Finset.univ.erase b, max (A' j - band (label (κ j))) 0 ^ 2 := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ b)]
        simp only [A', ite_eq_left rfl, sub_self, max_self, zero_pow (by norm_num : 2 ≠ 0), add_zero]
      _ = _ := Finset.sum_congr rfl (fun j hj => by rw [hAe j (Finset.mem_erase.mp hj).1])
  apply assigned_model_stokes_band_bound_regular hgreen a hf c r hr hd hext htarget n κ hκ b H γ hγ
    hin O hO hsub w hu hL hbounded henergy U v hU hboundary hv hproj A'
    (fun j hj => by simpa only [hAe j hj] using hA j hj) label hlabel band hband hb
  simpa only [heq] using hexcess


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_RegularMaskedStokes
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Function Filter MeasureTheory Metric
open scoped Topology BigOperators
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem MaskedCoordinateStage.stokes_bound_regular
    (hgreen : UnorientedFiniteCircleGreenFormula)
    {S : Type*} {n : ℕ} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {C : Fin n → MaskedCoordinateData G U π σ}
    {Flag : Set S} {O : S → Set Sphere} {K₀ : Set (ℝ × ℝ)} {ε ρ : ℝ} {k₀ : ℕ}
    (T : MaskedCoordinateStage C Flag O K₀ ε ρ k₀) (hσ : Injective σ) (l : Fin n)
    (a : TerminalComponentAssignment T.terminals.H T.model.forward T.model.domain)
    (c : T.indices → ℂ) (r : T.indices → ℝ) (hr : ∀ s, 0 ≤ r s)
    (hd : Pairwise (Disjoint on fun s => closedBall (c s) (r s)))
    (hext : ((↑) : ℂ → Sphere) ⁻¹' T.model.domain = (⋃ s, closedBall (c s) (r s))ᶜ)
    (htarget : ∀ s, ((↑) : ℂ → Sphere) '' closedBall (c s) (r s) ⊆
      connectedComponentIn T.model.domainᶜ (a.point s))
    (m : ℕ) (κ : Fin m → T.indices) (hκ : Injective κ) (b : Fin m)
    (hsing : (κ b : S) = (C l).singular) (hmask : ∀ j, σ (κ j) ∈ (C l).mask)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : RegularJordanParametrization H γ)
    (hin : ∀ j, closedBall (c (κ j)) (r (κ j)) ⊆ jordanInterior H)
    (W : Set ℂ) (hW : IsOpen W)
    (hsub : closure (jordanInterior H) \ ⋃ j, closedBall (c (κ j)) (r (κ j)) ⊆ W)
    (hsmooth : SmoothCircleOn (fun z : ℂ => sphereRealFunction (T.model.functions l)
      (T.model.inverse (z : Sphere))) W)
    {L : ℝ} (hL : 0 ≤ L) (hbounded : jordanInterior H ⊆ closedBall 0 L)
    (henergy : MemLp (circleFDeriv (fun z : ℂ => sphereRealFunction (T.model.functions l)
      (T.model.inverse (z : Sphere)))) 2
      (volume.restrict (jordanInterior H \ ⋃ j, closedBall (c (κ j)) (r (κ j))))) :
    |circleFormIntegral (fun z => infDist z (closedBall (c (κ b)) (r (κ b))))
      (fun z : ℂ => sphereRealFunction (T.model.functions l) (T.model.inverse (z : Sphere))) γ| ≤
      Real.sqrt Real.pi * L * Real.sqrt
        (∫ z in jordanInterior H \ ⋃ j, closedBall (c (κ j)) (r (κ j)),
          ‖circleFDeriv (fun z : ℂ => sphereRealFunction (T.model.functions l)
            (T.model.inverse (z : Sphere))) z‖ ^ 2) +
      2 * Real.pi * L *
        (Real.sqrt (∑' s : {s : S // s ≠ (C l).singular},
          ((C l).upper s - (C l).lower s) ^ 2) + ε) := by
  classical
  let : Fintype T.indices := T.indices_finite.fintype
  have hne (j : Fin m) (hj : j ≠ b) : σ (κ j) ≠ σ (C l).singular := by
    intro he
    apply hj
    apply hκ
    apply Subtype.ext
    exact (hσ he).trans hsing.symm
  choose V hV hboundary hcont hproj hosc using
    (fun j : {j : Fin m // j ≠ b} => T.nonsingular_terminal_lift l (κ j) (hmask j) (hne j j.property))
  let V' (j : Fin m) := if h : j ≠ b then V ⟨j, h⟩ else univ
  let A (j : Fin m) := Metric.diam
    (T.terminal_branch (κ j) l '' frontier (realJordanInterior (T.terminals.H (κ j))))
  let P := {s : T.indices // σ s ∈ (C l).mask ∧ σ s ≠ σ (C l).singular}
  let label : {j : Fin m // j ≠ b} → P := fun j => ⟨κ j, hmask j, hne j j.property⟩
  have hlabel : Injective label := by
    intro i j he
    apply Subtype.ext
    exact hκ (congrArg Subtype.val he)
  have hexc : Real.sqrt (∑ j : {j : Fin m // j ≠ b},
      max (A j - ((C l).upper (κ j) - (C l).lower (κ j))) 0 ^ 2) ≤ ε := by
    have h := finite_label_band_norm_le label hlabel
      (fun s : P => max (Metric.diam (T.terminal_branch s l ''
        frontier (realJordanInterior (T.terminals.H s))) -
          ((C l).upper s - (C l).lower s)) 0)
      (hasSum_fintype _).summable
    exact h.trans (T.terminal_excess l).le
  have hb := assigned_model_stokes_nonsingular_bound_regular hgreen a T.model.equivalence
    c r hr hd hext htarget m κ hκ b H γ hγ hin W hW hsub
    (sphereRealFunction (T.model.functions l)) hsmooth hL hbounded henergy V'
    (fun j => sphereRealFunction (T.terminal_branch (κ j) l))
    (fun j hj => by simpa only [V', dite_eq_left hj] using hV ⟨j, hj⟩)
    (fun j hj => by simpa only [V', dite_eq_left hj] using hboundary ⟨j, hj⟩)
    (fun j hj => by simpa only [V', dite_eq_left hj] using hcont ⟨j, hj⟩)
    (fun j hj => by simpa only [V', dite_eq_left hj] using hproj ⟨j, hj⟩)
    A (fun j hj => hosc ⟨j, hj⟩) (fun s : T.indices => (s : S)) Subtype.val_injective
    (fun s => (C l).upper s - (C l).lower s) (C l).width_summable (C l).width_nonneg hexc
  rw [hsing] at hb
  exact hb

 theorem MaskedCoordinateStage.source_stokes_bound_regular
    (hgreen : UnorientedFiniteCircleGreenFormula)
    {S : Type*} {n : ℕ} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {C : Fin n → MaskedCoordinateData G U π σ}
    {Flag : Set S} {O : S → Set Sphere} {K₀ : Set (ℝ × ℝ)} {ε ρ : ℝ} {k₀ : ℕ}
    (T : MaskedCoordinateStage C Flag O K₀ ε ρ k₀)
    (hG : IsOpen G) (hπ : Continuous π) (hσ : Injective σ)
    (hmetric : ∀ p ∈ openCompletedRegion T.terminals.H,
      IsMetricConformalAt T.model.metric T.model.forward p) (l : Fin n)
    (a : TerminalComponentAssignment T.terminals.H T.model.forward T.model.domain)
    (c : T.indices → ℂ) (r : T.indices → ℝ) (hr : ∀ s, 0 ≤ r s)
    (hd : Pairwise (Disjoint on fun s => closedBall (c s) (r s)))
    (hext : ((↑) : ℂ → Sphere) ⁻¹' T.model.domain = (⋃ s, closedBall (c s) (r s))ᶜ)
    (htarget : ∀ s, ((↑) : ℂ → Sphere) '' closedBall (c s) (r s) ⊆
      connectedComponentIn T.model.domainᶜ (a.point s))
    (m : ℕ) (κ : Fin m → T.indices) (hκ : Injective κ) (b : Fin m)
    (hsing : (κ b : S) = (C l).singular) (hmask : ∀ j, σ (κ j) ∈ (C l).mask)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : RegularJordanParametrization H γ)
    (hin : ∀ j, closedBall (c (κ j)) (r (κ j)) ⊆ jordanInterior H)
    (hregion : closure (jordanInterior H) \ ⋃ j, closedBall (c (κ j)) (r (κ j)) ⊆
      Complex.equivRealProdCLM ⁻¹' T.targetMask l)
    {L : ℝ} (hL : 0 ≤ L) (hbounded : jordanInterior H ⊆ closedBall 0 L) :
    |circleFormIntegral (fun z => infDist z (closedBall (c (κ b)) (r (κ b))))
      (fun z : ℂ => sphereRealFunction (T.model.functions l) (T.model.inverse (z : Sphere))) γ| ≤
      Real.sqrt Real.pi * L * Real.sqrt
        ((∫ x in realChartDomain G ∩ physicalMask π (C l).mask,
          fieldEnergy (circleGradient (C l).physical) (fun x => sphericalMetricFactor x • 1) x) + ε) +
      2 * Real.pi * L *
        (Real.sqrt (∑' s : {s : S // s ≠ (C l).singular},
          ((C l).upper s - (C l).lower s) ^ 2) + ε) := by
  let u := fun z : ℂ => sphereRealFunction (T.model.functions l) (T.model.inverse (z : Sphere))
  have hueq : u = (T.model.functions l ∘ sphereRealMap T.model.inverse) ∘ Complex.equivRealProdCLM := by
    funext z
    simp only [u, sphereRealFunction, sphereRealMap, Function.comp_apply,
      ContinuousLinearEquiv.symm_apply_apply]
  have hs := T.model.transported l
  have hW : IsOpen (Complex.equivRealProdCLM ⁻¹' T.targetMask l) :=
    hs.1.preimage Complex.equivRealProdCLM.continuous
  have hu : SmoothCircleOn u (Complex.equivRealProdCLM ⁻¹' T.targetMask l) := by
    rw [hueq]
    intro z hz a ha
    exact (hs.2.1 _ hz a ha).comp z Complex.equivRealProdCLM.contDiff.contDiffAt
  obtain ⟨hi, he⟩ := T.complex_energy_lt hG hπ hmetric l
  rw [← hueq] at hi he
  have hsub : jordanInterior H \ ⋃ j, closedBall (c (κ j)) (r (κ j)) ⊆
      Complex.equivRealProdCLM ⁻¹' T.targetMask l :=
    fun z hz => hregion ⟨subset_closure hz.1, hz.2⟩
  have hi' := hi.mono_measure (Measure.restrict_mono_set volume hsub)
  have hb := T.stokes_bound_regular hgreen hσ l a c r hr hd hext htarget m κ hκ b hsing hmask H γ hγ hin
    (Complex.equivRealProdCLM ⁻¹' T.targetMask l) hW hregion hu hL hbounded hi'
  have hle := setIntegral_mono_set
    ((memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).mp hi)
    (ae_of_all _ (fun z => sq_nonneg ‖circleFDeriv u z‖)) (ae_of_all _ hsub)
  exact hb.trans (add_le_add
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hle.trans he.le))
      (mul_nonneg (Real.sqrt_nonneg _) hL)) le_rfl)

 theorem StokesCollarGeometry.source_stokes_bound_regular
    (hgreen : UnorientedFiniteCircleGreenFormula)
    {S : Type*} {n : ℕ} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {C : Fin n → MaskedCoordinateData G U π σ}
    {Flag : Set S} {O : S → Set Sphere} {K₀ : Set (ℝ × ℝ)} {ε ρ : ℝ} {k₀ : ℕ}
    {T : MaskedCoordinateStage C Flag O K₀ ε ρ k₀} {l : Fin n}
    {s : T.indices} {H : ℂ ≃ₜ ℂ}
    {a : TerminalComponentAssignment T.terminals.H T.model.forward T.model.domain}
    (D : StokesCollarGeometry T l s H a)
    (hG : IsOpen G) (hπ : Continuous π) (hσ : Injective σ)
    (hmetric : ∀ p ∈ openCompletedRegion T.terminals.H,
      IsMetricConformalAt T.model.metric T.model.forward p)
    (hsing : (s : S) = (C l).singular)
    (γ : ℝ → ℂ) (hγ : RegularJordanParametrization D.target γ)
    {L : ℝ} (hL : 0 ≤ L) (hbounded : jordanInterior D.target ⊆ closedBall 0 L) :
    |circleFormIntegral (fun z => infDist z (closedBall (D.center s) (D.radius s)))
      (fun z : ℂ => sphereRealFunction (T.model.functions l) (T.model.inverse (z : Sphere))) γ| ≤
      Real.sqrt Real.pi * L * Real.sqrt
        ((∫ x in realChartDomain G ∩ physicalMask π (C l).mask,
          fieldEnergy (circleGradient (C l).physical) (fun x => sphericalMetricFactor x • 1) x) + ε) +
      2 * Real.pi * L *
        (Real.sqrt (∑' t : {t : S // t ≠ (C l).singular},
          ((C l).upper t - (C l).lower t) ^ 2) + ε) := by
  have hb := T.source_stokes_bound_regular hgreen hG hπ hσ hmetric l a
    D.center D.radius D.radius_nonneg D.disjoint D.exterior
    (fun i => D.disks i ▸ Subset.rfl) D.count D.label D.injective D.base
    (by rw [D.distinguished]; exact hsing) D.mask D.target γ hγ D.inside D.region hL hbounded
  simpa only [D.distinguished] using hb


end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PrescribedStokesGeometry
attribute [-instance] _root_.Graph.instFiniteElemEdgeSetOfFinite _root_.Graph.instFiniteElemVertexSetOfFinite _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The retained-collar geometry uses any prescribed actual round coordinates
of the terminal assignment, including the coordinates of a normal limit. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem MaskedCoordinateStage.exists_stokes_collar_geometry_prescribed
    (hsch : PlanarSchoenflies)
    {S : Type*} {n : ℕ} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {C : Fin n → MaskedCoordinateData G U π σ}
    {Flag : Set S} {O : S → Set Sphere} {K₀ : Set (ℝ × ℝ)} {ε ρ : ℝ} {k₀ : ℕ}
    (T : MaskedCoordinateStage C Flag O K₀ ε ρ k₀) (l : Fin n)
    (hinf : OnePoint.infty ∈ G) (hσB : ∀ s, σ s ∈ π '' Gᶜ)
    (H : ℂ ≃ₜ ℂ)
    (hbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ openCompletedRegion T.terminals.H)
    (hmask : realChartDomain (closedTerminalCap H) ⊆ interior (physicalMask π (C l).mask))
    (s : T.indices)
    (hs : closedTerminalCap (T.terminals.H s) ⊆ ((↑) : ℂ → Sphere) '' jordanInterior H)
    (a : TerminalComponentAssignment T.terminals.H T.model.forward T.model.domain) :
    ∀ (c : T.indices → ℂ) (r : T.indices → ℝ), (∀ i, 0 ≤ r i) →
    (∀ i, connectedComponentIn T.model.domainᶜ (a.point i) =
      ((↑) : ℂ → Sphere) '' closedBall (c i) (r i)) →
    Pairwise (Disjoint on fun i => closedBall (c i) (r i)) →
    ((↑) : ℂ → Sphere) ⁻¹' T.model.domain = (⋃ i, closedBall (c i) (r i))ᶜ →
    ∃ D : StokesCollarGeometry T l s H a, D.center = c ∧ D.radius = r := by
  intro c r hr he hd hext
  classical
  let : Fintype T.indices := T.indices_finite.fintype
  have hi : OnePoint.infty ∈ openCompletedRegion T.terminals.H :=
    T.core_model (infty_mem_sphericalCore T.core)
  obtain ⟨J, m, κ, hκ, hJ, hinside, hexact, hregion⟩ :=
    T.exists_collar_region hsch l H hbd hmask c r hext
  have hside := open_image_retained_jordan_side_eq
    (isOpen_openCompletedRegion T.terminals.H)
    (isConnected_openCompletedRegion T.terminals.H T.terminals.disjoint_closures).isPreconnected
    hi H J hbd (fun p hp => (T.model.equivalence.smooth p hp).1.continuousWithinAt)
    (fun _ hW hWQ => T.model.equivalence.isOpen_image T.model.circle_domain.1 hW hWQ)
    T.model.equivalence.bijOn.injOn T.model.principal.1 hJ
  rw [T.model.equivalence.bijOn.image_eq] at hside
  have hbdJ : ((↑) : ℂ → Sphere) '' frontier (jordanInterior J) ⊆ T.model.domain := by
    rw [← hJ]
    exact (image_mono hbd).trans (image_subset_iff.mpr T.model.equivalence.mapsTo)
  have hsJ := a.target_inside_of_source_inside T.terminals.disjoint_closures
    T.model.equivalence H J hbdJ hside s hs
  have hsball : closedBall (c s) (r s) ⊆ jordanInterior J := by
    intro z hz
    have h := hsJ (he s ▸ mem_image_of_mem ((↑) : ℂ → Sphere) hz)
    exact OnePoint.coe_injective.mem_set_image.mp h
  obtain ⟨b, hb⟩ := (hexact s).mpr hsball
  refine ⟨{
    center := c
    radius := r
    radius_nonneg := hr
    disks := he
    disjoint := hd
    exterior := hext
    target := J
    boundary := hJ
    count := m
    label := κ
    injective := hκ
    base := b
    distinguished := hb
    inside := hinside
    mask := ?_
    region := hregion }, rfl, rfl⟩
  intro j
  apply T.label_mem_mask_of_terminal_inside l hinf hσB H hmask (κ j)
  exact a.source_inside_of_target_inside T.model.equivalence c r hr hd hext
    (fun i => he i ▸ Subset.rfl) H J hbd hside (κ j) (hinside j)


end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_MixedCircuitSmoothness
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A retained source circuit has a smooth image in the actual transported
mask. These are the domains required by the fixed-lift boundary integral. -/

open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem IsSmoothSphereAt.contDiffAt_finiteMap
    {f : Sphere → Sphere} {z : ℂ} (hf : IsSmoothSphereAt f (z : Sphere))
    (hfin : f (z : Sphere) ≠ OnePoint.infty) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun w : ℂ => finiteCoord (f (w : Sphere))) z := by
  have hs : IsSmoothSphereAt f
      ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM z) : ℂ) : Sphere) := by
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hf
  have hfin' : f ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM z) : ℂ) : Sphere) ≠
      OnePoint.infty := by
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hfin
  have h := Complex.equivRealProdCLM.symm.contDiff.contDiffAt.comp z
    ((hs.contDiffAt_sphereRealMap hfin').comp z Complex.equivRealProdCLM.contDiff.contDiffAt)
  simpa only [Function.comp_def, sphereRealMap, ContinuousLinearEquiv.symm_apply_apply] using h

namespace FiniteTransfer

 theorem MixedModelExhaustion.eventually_circuit_smooth_in_mask
    {S C : Type*} [LinearOrder C]
    {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates G π σ}
    {data : C → MaskedCoordinateData G d.source π σ} {retained : ℕ → C}
    {O : ℕ → S → Set Sphere} {ε ρ : ℕ → ℝ}
    (M : MixedModelExhaustion d data retained O ε ρ)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : PositiveJordanParametrization H γ)
    (hG : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G) (c : C)
    (hmask : ∀ z ∈ frontier (jordanInterior H), Complex.equivRealProdCLM z ∈
      interior (physicalMask π (data c).mask)) :
    ∀ᶠ n in atTop,
      ContDiff ℝ (⊤ : ℕ∞) (fun t => finiteCoord ((M.stages n).model.forward (γ t : Sphere))) ∧
      ∀ t : ℝ, finiteCoord ((M.stages n).model.forward (γ t : Sphere)) ∈
        Complex.equivRealProdCLM ⁻¹' (M.stages n).toMaskedCoordinateStage.targetMask
          (M.coordinateIndex c n) := by
  let K := ((↑) : ℂ → Sphere) '' frontier (jordanInterior H)
  have hK : IsCompact K :=
    ((isCompact_closure_jordanInterior H).of_isClosed_subset isClosed_frontier
      frontier_subset_closure).image OnePoint.continuous_coe
  filter_upwards [M.real.eventually_core_contains hK hG, M.coordinateIndex_eventually c]
    with n hn hc
  have hpoint (t : ℝ) : (γ t : Sphere) ∈ openCompletedRegion (M.stages n).terminals.H := by
    apply (M.stages n).core_model
    apply (coe_mem_sphericalCore _ _).mpr
    apply interior_subset ((M.stages n).core_contains ?_)
    change ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM (γ t)) : ℂ) : Sphere) ∈
      M.real.cores n
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact hn (mem_image_of_mem _ (hγ.mem_frontier t))
  have hi : OnePoint.infty ∈ openCompletedRegion (M.stages n).terminals.H :=
    (M.stages n).core_model (infty_mem_sphericalCore (M.stages n).core)
  have hfinite (t : ℝ) := finite_image_of_fixes_infty (M.stages n).model.equivalence.bijOn.injOn hi
    (M.stages n).model.principal.1 (hpoint t)
  constructor
  · apply contDiff_iff_contDiffAt.mpr
    intro t
    exact ((M.stages n).model.equivalence.smooth _ (hpoint t)).contDiffAt_finiteMap
      (hfinite t) |>.comp t hγ.smooth.contDiffAt
  · intro t
    refine ⟨Complex.equivRealProdCLM (γ t), ⟨?_, ?_⟩, ?_⟩
    · change ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM (γ t)) : ℂ) : Sphere) ∈
        openCompletedRegion (M.stages n).terminals.H
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using hpoint t
    · change Complex.equivRealProdCLM (γ t) ∈
        interior (physicalMask π (data (M.label n (M.coordinateIndex c n))).mask)
      rw [hc]
      exact hmask _ (hγ.mem_frontier t)
    · simp only [sphereRealMap, ContinuousLinearEquiv.symm_apply_apply]

end FiniteTransfer
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_RegularImageCircuit
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual image of a regular source circuit is regular. No orientation
choice is needed here: the inverse differential prevents zero tangents. -/

open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem IsSmoothSphereEquivalence.regular_image_circuit
    {f fi : Sphere → Sphere} {U V : Set Sphere}
    (hf : IsSmoothSphereEquivalence f fi U V)
    (hU : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty)
    {H J : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ} (hγ : RegularJordanParametrization H γ)
    (hbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ U)
    (himage : f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior J)) :
    RegularJordanParametrization J (fun t => finiteCoord (f (γ t : Sphere))) := by
  let δ := fun t => finiteCoord (f (γ t : Sphere))
  let g := fun z : ℂ => finiteCoord (fi (z : Sphere))
  have hpoint (t : ℝ) : (γ t : Sphere) ∈ U :=
    hbd (mem_image_of_mem _ (hγ.mem_frontier t))
  have hfinite (t : ℝ) : f (γ t : Sphere) ≠ OnePoint.infty :=
    hf.finite_forward hU hfix (hpoint t)
  have hδ : ContDiff ℝ (⊤ : ℕ∞) δ := by
    apply contDiff_iff_contDiffAt.mpr
    intro t
    exact ((hf.smooth _ (hpoint t)).contDiffAt_finiteMap (hfinite t)).comp t
      hγ.smooth.contDiffAt
  have hleft : g ∘ δ = γ := by
    funext t
    simp only [Function.comp_apply, g, δ, coe_finiteCoord (hfinite t),
      hf.left_inv _ (hpoint t), finiteCoord_coe]
  refine ⟨hδ, fun t => congrArg (fun z : ℂ => finiteCoord (f (z : Sphere))) (hγ.periodic t),
    ?_, ?_, ?_⟩
  · intro x hx y hy he
    apply hγ.injective hx hy
    apply OnePoint.coe_injective
    apply hf.bijOn.injOn (hpoint x) (hpoint y)
    have hh := congrArg (fun z : ℂ => (z : Sphere)) he
    simpa only [δ, coe_finiteCoord (hfinite x), coe_finiteCoord (hfinite y)] using hh
  · intro t hz
    have hV : (δ t : Sphere) ∈ V := by
      simpa only [δ, coe_finiteCoord (hfinite t)] using hf.mapsTo (hpoint t)
    have hg : DifferentiableAt ℝ g (δ t) :=
      ((hf.smooth_inv _ hV).contDiffAt_finiteMap (hf.finite_inv hU hfix hV)).differentiableAt
        (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    have he := (hg.hasFDerivAt.comp_hasDerivAt t (hδ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) t).hasDerivAt).deriv
    rw [hleft, hz, map_zero] at he
    exact hγ.regular t he
  · apply Set.image_injective.mpr OnePoint.coe_injective
    calc
      ((↑) : ℂ → Sphere) '' (δ '' Icc 0 1) =
          f '' (((↑) : ℂ → Sphere) '' (γ '' Icc 0 1)) := by
        simp only [image_image]
        apply image_congr
        intro t _
        exact coe_finiteCoord (hfinite t)
      _ = ((↑) : ℂ → Sphere) '' frontier (jordanInterior J) := by
        rw [hγ.boundary, himage]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SourceCollarStokes
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The numerical source-energy bound on an actual image of a retained
source collar. All target holes and the regular image circuit are derived. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem MaskedCoordinateStage.source_collar_stokes_bound
    (hgreen : UnorientedFiniteCircleGreenFormula) (hsch : PlanarSchoenflies)
    {S : Type*} {n : ℕ} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {C : Fin n → MaskedCoordinateData G U π σ}
    {Flag : Set S} {O : S → Set Sphere} {K₀ : Set (ℝ × ℝ)} {ε ρ : ℝ} {k₀ : ℕ}
    (T : MaskedCoordinateStage C Flag O K₀ ε ρ k₀)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hπ : Continuous π) (hσ : Injective σ) (hσB : ∀ s, σ s ∈ π '' Gᶜ)
    (hmetric : ∀ p ∈ openCompletedRegion T.terminals.H,
      IsMetricConformalAt T.model.metric T.model.forward p) (l : Fin n)
    (a : TerminalComponentAssignment T.terminals.H T.model.forward T.model.domain)
    (c : T.indices → ℂ) (r : T.indices → ℝ) (hr : ∀ i, 0 ≤ r i)
    (he : ∀ i, connectedComponentIn T.model.domainᶜ (a.point i) =
      ((↑) : ℂ → Sphere) '' closedBall (c i) (r i))
    (hd : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    (hext : ((↑) : ℂ → Sphere) ⁻¹' T.model.domain = (⋃ i, closedBall (c i) (r i))ᶜ)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : RegularJordanParametrization H γ)
    (hbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ openCompletedRegion T.terminals.H)
    (hmask : realChartDomain (closedTerminalCap H) ⊆ interior (physicalMask π (C l).mask))
    (s : T.indices) (hsing : (s : S) = (C l).singular)
    (hs : closedTerminalCap (T.terminals.H s) ⊆ ((↑) : ℂ → Sphere) '' jordanInterior H)
    {L : ℝ} (hL : 0 ≤ L)
    (hbounded : ∀ J : ℂ ≃ₜ ℂ,
      T.model.forward '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) =
        ((↑) : ℂ → Sphere) '' frontier (jordanInterior J) →
      jordanInterior J ⊆ closedBall 0 L) :
    |circleFormIntegral (fun z => infDist z (closedBall (c s) (r s)))
      (fun z : ℂ => sphereRealFunction (T.model.functions l) (T.model.inverse (z : Sphere)))
      (fun t => finiteCoord (T.model.forward (γ t : Sphere)))| ≤
      Real.sqrt Real.pi * L * Real.sqrt
        ((∫ x in realChartDomain G ∩ physicalMask π (C l).mask,
          fieldEnergy (circleGradient (C l).physical) (fun x => sphericalMetricFactor x • 1) x) + ε) +
      2 * Real.pi * L * (Real.sqrt (∑' t : {t : S // t ≠ (C l).singular},
        ((C l).upper t - (C l).lower t) ^ 2) + ε) := by
  obtain ⟨D, hDc, hDr⟩ := T.exists_stokes_collar_geometry_prescribed hsch l hinf hσB
    H hbd hmask s hs a c r hr he hd hext
  have hp := T.model.equivalence.regular_image_circuit
    (T.core_model (infty_mem_sphericalCore T.core)) T.model.principal.1 hγ hbd D.boundary
  have hb := D.source_stokes_bound_regular hgreen hG hπ hσ hmetric hsing _ hp hL
    (hbounded D.target D.boundary)
  simpa only [hDc, hDr] using hb

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RoundBoundaryStability
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative persistence of the fixed-source boundary integral under
uniform changes of the map and center-radius changes of the target disk. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem infDist_closedBall_eq_max (c z : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    infDist z (closedBall c r) = max (dist z c - r) 0 := by
  by_cases hz : dist z c ≤ r
  · rw [infDist_zero_of_mem (mem_closedBall.mpr hz), max_eq_right (sub_nonpos.mpr hz)]
  · rw [infDist_closedBall_of_dist_gt c z hr (lt_of_not_ge hz),
      max_eq_left (sub_nonneg.mpr (le_of_not_ge hz))]

 theorem round_disk_distance_change (c d z w : ℂ) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    |infDist z (closedBall c r) - infDist w (closedBall d s)| ≤
      dist z w + dist c d + |r - s| := by
  rw [infDist_closedBall_eq_max c z hr, infDist_closedBall_eq_max d w hs]
  calc
    _ ≤ max |(dist z c - r) - (dist w d - s)| |(0 : ℝ) - 0| :=
      abs_max_sub_max_le_max _ _ _ _
    _ = |(dist z c - dist w d) - (r - s)| := by
      rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)]
      congr 1
      ring
    _ ≤ |dist z c - dist w d| + |r - s| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (dist z c - dist w d) (-(r - s))
    _ ≤ dist z w + dist c d + |r - s| := by
      exact add_le_add (by simpa only [Real.dist_eq] using dist_dist_dist_le z c w d) le_rfl

 theorem roundDiskBoundaryPairing_stability
    (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (c d : ℂ) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (v : ℝ → ℝ) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    {e M : ℝ} (he : 0 ≤ e)
    (hclose : ∀ t ∈ Icc (0 : ℝ) 1, dist (f t) (g t) ≤ e)
    (hderiv : ∀ t ∈ Icc (0 : ℝ) 1, |deriv v t| ≤ M) :
    |roundDiskBoundaryPairing f c r v - roundDiskBoundaryPairing g d s v| ≤
      (e + dist c d + |r - s|) * M := by
  have hdv : Continuous (deriv v) := hv.continuous_deriv (by simp)
  have hfi : IntervalIntegrable (fun t => infDist (f t) (closedBall c r) * deriv v t) volume 0 1 := ((continuous_infDist_pt _).comp hf).mul hdv |>.intervalIntegrable 0 1
  have hgi : IntervalIntegrable (fun t => infDist (g t) (closedBall d s) * deriv v t) volume 0 1 := ((continuous_infDist_pt _).comp hg).mul hdv |>.intervalIntegrable 0 1
  unfold roundDiskBoundaryPairing
  rw [← intervalIntegral.integral_sub hfi hgi]
  have hb : ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖infDist (f t) (closedBall c r) * deriv v t -
        infDist (g t) (closedBall d s) * deriv v t‖ ≤
      (e + dist c d + |r - s|) * M := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    have hweight := (round_disk_distance_change c d (f t) (g t) hr hs).trans
      (add_le_add (add_le_add (hclose t ht') le_rfl) le_rfl)
    rw [← sub_mul, Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul_of_nonneg_right hweight (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (hderiv t ht') (by positivity))
  simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using
    intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := (1 : ℝ))
      (fun t ht => hb t (by simpa only [uIoc_of_le zero_le_one] using ht))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CircleBoundaryPersistence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A retained real lift converts the actual target-circuit Stokes
integral into the fixed-source boundary functional. Uniform convergence
of the maps and convergence of the terminal disks then pass the proved
finite Stokes bound to the limiting pair. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem circleFormIntegral_eq_roundBoundaryPairing
    (O : Set ℂ) (hO : IsOpen O) (u : ℂ → UnitAddCircle) (hu : SmoothCircleOn u O)
    (γ : ℝ → ℂ) (hγ : Differentiable ℝ γ) (hγO : ∀ t, γ t ∈ O)
    (v : ℝ → ℝ) (hv : Continuous v) (hproj : ∀ t, (v t : UnitAddCircle) = u (γ t))
    (c : ℂ) (r : ℝ) :
    circleFormIntegral (fun z => infDist z (closedBall c r)) u γ =
      roundDiskBoundaryPairing γ c r v :=
  circleFormIntegral_eq_real_lift hO hu _ γ hγ hγO v hv hproj

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_BoundaryPairNeighborhood
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Open exclusion neighborhoods use the actual fixed-source boundary
functional. Its continuity is proved from the disk-distance estimate;
no stability or exclusion assertion is assumed. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology NNReal

noncomputable section
namespace CircleDomainRigidity

 theorem boundaryPairFunctional_trace (γ : ℝ → ℂ) (hγ : Continuous γ)
    (c : ℂ) (r : ℝ≥0) (v : ℝ → ℝ) :
    boundaryPairFunctional v (boundaryCurveTrace γ hγ, c, r) =
      roundDiskBoundaryPairing γ c r v := by
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
  change infDist (γ (projIcc 0 1 zero_le_one t)) (closedBall c (r : ℝ)) * deriv v t = _
  rw [coe_projIcc, min_eq_right ht'.2, max_eq_right ht'.1]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_SourceStokesEventual
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Discard the finite initial segment before a source circuit has been
retained. The limit exclusion requires only eventual model identities. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

 theorem boundaryExclusionSet_excludes_eventual_source_stokes
    (γ : ℕ → ℝ → ℂ) (γ₀ : ℝ → ℂ) (hγ₀ : Continuous γ₀)
    (O : ℕ → Set ℂ) (u : ℕ → ℂ → UnitAddCircle)
    (v : ℝ → ℝ) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (c : ℕ → ℂ) (c₀ : ℂ) (hc : Tendsto c atTop (𝓝 c₀))
    (r : ℕ → ℝ) (r₀ : ℝ≥0) (hrr : Tendsto r atTop (𝓝 (r₀ : ℝ)))
    (e : ℕ → ℝ) (he0 : Tendsto e atTop (𝓝 0))
    (hvalid : ∀ᶠ n in atTop, Differentiable ℝ (γ n) ∧ IsOpen (O n) ∧
      FiniteTransfer.SmoothCircleOn (u n) (O n) ∧
      (∀ t, γ n t ∈ O n) ∧ (∀ t, (v t : UnitAddCircle) = u n (γ n t)) ∧
      0 ≤ r n ∧ 0 ≤ e n ∧
      ∀ t ∈ Icc (0 : ℝ) 1, dist (γ n t) (γ₀ t) ≤ e n)
    (L I B : ℝ) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop,
      |circleFormIntegral (fun z => infDist z (closedBall (c n) (r n))) (u n) (γ n)| ≤
        Real.sqrt Real.pi * L * Real.sqrt (I + ε n) + 2 * Real.pi * L * (B + ε n)) :
    (boundaryCurveTrace γ₀ hγ₀, c₀, r₀) ∉
      boundaryExclusionSet v (Real.sqrt Real.pi * L * Real.sqrt I + 2 * Real.pi * L * B) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    (hv.continuous_deriv (by simp)).continuousOn
  have hestimate : ∀ᶠ n in atTop,
      dist (roundDiskBoundaryPairing (γ n) (c n) (r n) v)
        (roundDiskBoundaryPairing γ₀ c₀ (r₀ : ℝ) v) ≤
      (e n + dist (c n) c₀ + |r n - r₀|) * M := by
    filter_upwards [hvalid] with n hn
    obtain ⟨hdγ, _, _, _, _, hr, he, hclose⟩ := hn
    rw [Real.dist_eq]
    exact roundDiskBoundaryPairing_stability
      (γ n) γ₀ hdγ.continuous hγ₀ (c n) c₀ (s := (r₀ : ℝ)) hr r₀.property v hv he hclose
      (fun t ht => by simpa only [Real.norm_eq_abs] using hM t ht)
  have herror : Tendsto (fun n => (e n + dist (c n) c₀ + |r n - r₀|) * M) atTop (𝓝 0) := by
    simpa only [dist_self, sub_self, abs_zero, add_zero, zero_add, zero_mul] using
      ((he0.add (hc.dist (tendsto_const_nhds (x := c₀)))).add
        (hrr.sub (tendsto_const_nhds (x := (r₀ : ℝ)))).abs).mul_const M
  have hpair : Tendsto (fun n => roundDiskBoundaryPairing (γ n) (c n) (r n) v) atTop
      (𝓝 (roundDiskBoundaryPairing γ₀ c₀ (r₀ : ℝ) v)) :=
    tendsto_iff_dist_tendsto_zero.mpr
      (squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg)) hestimate herror)
  have hpairbound : ∀ᶠ n in atTop,
      |roundDiskBoundaryPairing (γ n) (c n) (r n) v| ≤
        Real.sqrt Real.pi * L * Real.sqrt (I + ε n) + 2 * Real.pi * L * (B + ε n) := by
    filter_upwards [hvalid, hbound] with n hn hb
    obtain ⟨hdγ, hO, hu, hγO, hproj, _, _, _⟩ := hn
    rwa [circleFormIntegral_eq_roundBoundaryPairing (O n) hO (u n) hu (γ n)
      hdγ hγO v hv.continuous hproj (c n) (r n)] at hb
  have hsum : Tendsto (fun n => I + ε n) atTop (𝓝 I) := by
    simpa only [add_zero] using tendsto_const_nhds.add hε
  have hsqrt := (Real.continuous_sqrt.tendsto I).comp hsum
  have hbudget : Tendsto
      (fun n => Real.sqrt Real.pi * L * Real.sqrt (I + ε n) + 2 * Real.pi * L * (B + ε n))
      atTop (𝓝 (Real.sqrt Real.pi * L * Real.sqrt I + 2 * Real.pi * L * B)) := by
    simpa only [Function.comp_apply, add_zero] using
      (hsqrt.const_mul (Real.sqrt Real.pi * L)).add
        ((tendsto_const_nhds.add hε).const_mul (2 * Real.pi * L))
  change ¬ _ < |boundaryPairFunctional v _|
  rw [boundaryPairFunctional_trace]
  exact not_lt_of_ge (le_of_tendsto_of_tendsto hpair.abs hbudget hpairbound)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_CircuitUniformError
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform convergence on a source circuit gives a vanishing numerical
error bound. No regularity of the finitely many early models is needed. -/

open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem exists_circuit_uniform_error
    (f : ℕ → ℝ → ℂ) (g : ℝ → ℂ)
    (hf : TendstoUniformlyOn f g atTop (Icc (0 : ℝ) 1)) :
    ∃ e : ℕ → ℝ, (∀ n, 0 ≤ e n) ∧ Tendsto e atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) 1, dist (f n t) (g t) ≤ e n := by
  classical
  let D (n : ℕ) := (fun t => dist (f n t) (g t)) '' Icc (0 : ℝ) 1
  have hD (n) : (D n).Nonempty := ⟨dist (f n 0) (g 0), 0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  let e (n : ℕ) := if h : BddAbove (D n) then sSup (D n) else 0
  have he (n) : 0 ≤ e n := by
    by_cases h : BddAbove (D n)
    · exact (dist_nonneg : 0 ≤ dist (f n 0) (g 0)).trans
        (by simp only [e, dite_eq_left h]; exact le_csSup h ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩)
    · simp only [e, dite_eq_right h, le_refl]
  have hε (δ : ℝ) (hδ : 0 < δ) :
      ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) 1, dist (f n t) (g t) < δ := by
    simpa only [dist_comm] using (Metric.tendstoUniformlyOn_iff.mp hf δ hδ)
  have hbounded {n : ℕ} {δ : ℝ}
      (h : ∀ t ∈ Icc (0 : ℝ) 1, dist (f n t) (g t) < δ) : BddAbove (D n) := by
    refine ⟨δ, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact (h t ht).le
  refine ⟨e, he, ?_, ?_⟩
  · apply Metric.tendsto_nhds.mpr
    intro δ hδ
    filter_upwards [hε (δ / 2) (half_pos hδ)] with n hn
    have hnB := hbounded hn
    have hle : e n ≤ δ / 2 := by
      simp only [e, dite_eq_left hnB]
      exact csSup_le (hD n) (by rintro _ ⟨t, ht, rfl⟩; exact (hn t ht).le)
    simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (he n)] using
      (hle.trans_lt (half_lt_self hδ))
  · filter_upwards [hε 1 zero_lt_one] with n hn t ht
    simp only [e, dite_eq_left (hbounded hn)]
    exact le_csSup (hbounded hn) ⟨t, ht, rfl⟩

 theorem tendstoUniformlyOn_retained_circuit
    (f : ℕ → Sphere → Sphere) (F : ℂ → ℂ) {G : Set Sphere}
    (hf : TendstoLocallyUniformlyOn (fun n (z : ℂ) => finiteCoord (f n (z : Sphere))) F atTop
      (((↑) : ℂ → Sphere) ⁻¹' G))
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : PositiveJordanParametrization H γ)
    (hG : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G) :
    TendstoUniformlyOn (fun n t => finiteCoord (f n (γ t : Sphere))) (F ∘ γ) atTop
      (Icc (0 : ℝ) 1) := by
  apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_Icc).mp
  exact hf.comp γ (fun t _ => hG (mem_image_of_mem _ (hγ.mem_frontier t)))
    hγ.smooth.continuous.continuousOn

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_MixedStokesLimit
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed-source exclusion for an actual mixed model sequence.
Smoothness, mask containment, a common lifted coordinate and the uniform
error are derived from retention and local uniform convergence. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem MixedModelExhaustion.excludes_source_stokes_limit
    {S C : Type*} [LinearOrder C]
    {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates G π σ}
    {data : C → MaskedCoordinateData G d.source π σ} {retained : ℕ → C}
    {O : ℕ → S → Set Sphere} {ε ρ : ℕ → ℝ}
    (M : MixedModelExhaustion d data retained O ε ρ)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : PositiveJordanParametrization H γ)
    (hG : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G) (j : C)
    (hmask : ∀ z ∈ frontier (jordanInterior H), Complex.equivRealProdCLM z ∈
      interior (physicalMask π (data j).mask))
    (v : ℝ → ℝ) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hproj : ∀ t, (v t : UnitAddCircle) = (data j).physical (Complex.equivRealProdCLM (γ t)))
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop)
    (F : ℂ → ℂ) (hF : ContinuousOn F (((↑) : ℂ → Sphere) ⁻¹' G))
    (hlim : TendstoLocallyUniformlyOn
      (fun n (z : ℂ) => finiteCoord ((M.stages (k n)).model.forward (z : Sphere))) F atTop
      (((↑) : ℂ → Sphere) ⁻¹' G))
    (c : ℕ → ℂ) (c₀ : ℂ) (hc : Tendsto c atTop (𝓝 c₀))
    (r : ℕ → ℝ) (r₀ : ℝ≥0) (hr : ∀ n, 0 ≤ r n) (hrr : Tendsto r atTop (𝓝 (r₀ : ℝ)))
    (L I B : ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop,
      |circleFormIntegral (fun z => infDist z (closedBall (c n) (r n)))
        (fun z => sphereRealFunction ((M.stages (k n)).model.functions (M.coordinateIndex j (k n)))
          ((M.stages (k n)).model.inverse (z : Sphere)))
        (fun t => finiteCoord ((M.stages (k n)).model.forward (γ t : Sphere)))| ≤
      Real.sqrt Real.pi * L * Real.sqrt (I + ε (k n)) + 2 * Real.pi * L * (B + ε (k n))) :
    (boundaryCurveTrace (F ∘ γ) (hF.comp_continuous hγ.smooth.continuous
      (fun t => hG (mem_image_of_mem _ (hγ.mem_frontier t)))), c₀, r₀) ∉
      boundaryExclusionSet v (Real.sqrt Real.pi * L * Real.sqrt I + 2 * Real.pi * L * B) := by
  let γn := fun n t => finiteCoord ((M.stages (k n)).model.forward (γ t : Sphere))
  let un := fun n (z : ℂ) => sphereRealFunction
    ((M.stages (k n)).model.functions (M.coordinateIndex j (k n)))
    ((M.stages (k n)).model.inverse (z : Sphere))
  let W := fun n => Complex.equivRealProdCLM ⁻¹'
    (M.stages (k n)).toMaskedCoordinateStage.targetMask (M.coordinateIndex j (k n))
  have hg₀ := hF.comp_continuous hγ.smooth.continuous
    (fun t => hG (mem_image_of_mem _ (hγ.mem_frontier t)))
  obtain ⟨e, he, he0, hclose⟩ := exists_circuit_uniform_error γn (F ∘ γ)
    (tendstoUniformlyOn_retained_circuit (fun n => (M.stages (k n)).model.forward)
      F hlim H γ hγ hG)
  apply boundaryExclusionSet_excludes_eventual_source_stokes γn (F ∘ γ) hg₀ W un v hv
    c c₀ hc r r₀ hrr e he0 ?_ L I B (fun n => ε (k n)) (hε.comp hk) hbound
  filter_upwards [hk (M.eventually_circuit_smooth_in_mask H γ hγ hG j hmask),
    hk (M.eventually_circuit_values H γ hγ hG j), hclose] with n hn hvn hcn
  have ht := (M.stages (k n)).model.transported (M.coordinateIndex j (k n))
  refine ⟨hn.1.differentiable (by simp), ht.1.preimage Complex.equivRealProdCLM.continuous,
    ?_, hn.2, ?_, hr n, he n, hcn⟩
  · intro z hz a ha
    have hh := (ht.2.1 _ hz a ha).comp z Complex.equivRealProdCLM.contDiff.contDiffAt
    simpa only [un, sphereRealFunction, sphereRealMap, Function.comp_def,
      ContinuousLinearEquiv.symm_apply_apply] using hh
  · intro t
    exact (hproj t).trans (hvn t).symm

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_MixedCollarStokes
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.metricBeltramiCoefficient_scalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite Stokes bounds along a mixed exhaustion. The source
collar determines the holes; normalization supplies the common radius. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem MixedModelExhaustion.eventually_source_collar_stokes
    (hgreen : UnorientedFiniteCircleGreenFormula) (hsch : PlanarSchoenflies)
    (harea : ExteriorCoefficientAreaTheorem)
    {S C : Type*} [LinearOrder C]
    {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates G π σ}
    {data : C → MaskedCoordinateData G d.source π σ} {retained : ℕ → C}
    {O : ℕ → S → Set Sphere} {ε ρ : ℕ → ℝ}
    (M : MixedModelExhaustion d data retained O ε ρ)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G) (hπ : Continuous π)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : PositiveJordanParametrization H γ)
    (hbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G)
    (hH : ∀ z ∈ frontier (jordanInterior H), ‖z‖ ≤ 4 * M.real.radius)
    (j : C)
    (hmask : realChartDomain (closedTerminalCap H) ⊆ interior (physicalMask π (data j).mask))
    (a : ∀ n, TerminalComponentAssignment (M.stages n).terminals.H
      (M.stages n).model.forward (M.stages n).model.domain)
    (s : ∀ n, (M.stages n).indices)
    (hs : ∀ᶠ n in atTop, (s n : S) = (data j).singular)
    (hcap : ∀ᶠ n in atTop, closedTerminalCap ((M.stages n).terminals.H (s n)) ⊆
      ((↑) : ℂ → Sphere) '' jordanInterior H)
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop)
    (c : ℕ → ℂ) (r : ℕ → ℝ)
    (hdisks : ∀ᶠ n in atTop,
      connectedComponentIn (M.stages (k n)).model.domainᶜ ((a (k n)).point (s (k n))) =
        ((↑) : ℂ → Sphere) '' closedBall (c n) (r n)) :
    ∀ᶠ n in atTop,
      |circleFormIntegral (fun z => infDist z (closedBall (c n) (r n)))
        (fun z => sphereRealFunction ((M.stages (k n)).model.functions (M.coordinateIndex j (k n)))
          ((M.stages (k n)).model.inverse (z : Sphere)))
        (fun t => finiteCoord ((M.stages (k n)).model.forward (γ t : Sphere)))| ≤
      Real.sqrt Real.pi * (5 * M.real.radius) * Real.sqrt
        ((∫ x in realChartDomain G ∩ physicalMask π (data j).mask,
          fieldEnergy (circleGradient (data j).physical) (fun x => sphericalMetricFactor x • 1) x) + ε (k n)) +
      2 * Real.pi * (5 * M.real.radius) * (Real.sqrt
        (∑' t : {t : S // t ≠ (data j).singular}, ((data j).upper t - (data j).lower t) ^ 2) + ε (k n)) := by
  have hK : IsCompact (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) :=
    ((isCompact_closure_jordanInterior H).of_isClosed_subset isClosed_frontier
      frontier_subset_closure).image OnePoint.continuous_coe
  filter_upwards [hk (M.eventually_all_image_collar_bounds harea H hbd hH),
    hk (M.coordinateIndex_eventually j), hk (M.real.eventually_core_contains hK hbd),
    hk hs, hk hcap, hdisks] with n hbounds hj hcore hsn hcn hdn
  change M.label (k n) (M.coordinateIndex j (k n)) = j at hj
  change (s (k n) : S) = (data j).singular at hsn
  have hretain : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆
      openCompletedRegion (M.stages (k n)).terminals.H := by
    rintro _ ⟨z, hz, rfl⟩
    apply (M.stages (k n)).core_model
    apply (coe_mem_sphericalCore _ _).mpr
    apply interior_subset ((M.stages (k n)).core_contains ?_)
    change ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM z) : ℂ) : Sphere) ∈ M.real.cores (k n)
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact hcore (mem_image_of_mem _ hz)
  have hi : OnePoint.infty ∈ (M.stages (k n)).model.domain := by
    rw [← (M.stages (k n)).model.principal.1]
    exact (M.stages (k n)).model.equivalence.mapsTo
      ((M.stages (k n)).core_model (infty_mem_sphericalCore (M.stages (k n)).core))
  obtain ⟨cn, rn, hrn, hends, hdn', hext⟩ :=
    (a (k n)).exists_disk_coordinates (M.stages (k n)).model.circle_domain hi
  have heq : closedBall (cn (s (k n))) (rn (s (k n))) = closedBall (c n) (r n) :=
    Set.image_injective.mpr OnePoint.coe_injective ((hends (s (k n))).symm.trans hdn)
  have hb := (M.stages (k n)).toMaskedCoordinateStage.source_collar_stokes_bound hgreen hsch
    hG hinf hπ d.labels_injective d.labels_dust (M.stages (k n)).real.metric_conformal
    (M.coordinateIndex j (k n)) (a (k n)) cn rn hrn hends hdn' hext H γ hγ.toRegular hretain
    (by simpa only [hj] using hmask) (s (k n)) (by simpa only [hj] using hsn) hcn
    (mul_nonneg (by norm_num) M.real.radius_pos.le)
    (fun J hJ => subset_closure.trans (hbounds J hJ))
  rw [hj] at hb
  simpa only [heq] using hb

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_MixedMarkedModels
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Original marked ends in the common mixed model. These constructions
use the actual terminal fibers; no transport of dependent terminal types
from the real subfamily is necessary. -/

open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

variable {S C : Type*} [LinearOrder C]
  {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ}
  {data : C → MaskedCoordinateData G d.source π σ} {retained : ℕ → C}
  {O : ℕ → S → Set Sphere} {ε ρ : ℕ → ℝ}

namespace MixedModelExhaustion

variable (M : MixedModelExhaustion d data retained O ε ρ)

 theorem eventually_markIndex (s : S) : ∀ᶠ n in atTop, (M.markIndex n s : S) = s :=
  M.real.eventually_markIndex s

 theorem eventually_marked_cap_subset (s : S) {W : Set Sphere}
    (hO : ∀ᶠ n in atTop, O n s ⊆ W) :
    ∀ᶠ n in atTop, closedTerminalCap ((M.stages n).terminals.H (M.markIndex n s)) ⊆ π ⁻¹' W := by
  filter_upwards [M.eventually_markIndex s, hO] with n hn hOn
  rintro p ⟨z, hz, rfl⟩
  have h := (M.stages n).terminals.closure_subset (M.markIndex n s) hz
  change π (z : Sphere) ∈ O n (M.markIndex n s) at h
  rw [hn] at h
  exact hOn h

end MixedModelExhaustion

 theorem MixedModelExhaustion.eventually_marked_cap_in_nhds
    {ρ : ℕ → ℝ}
    (M : MixedModelExhaustion d data retained (markedNeighborhoods σ) modelError ρ)
    (s : S) {W : Set Sphere} (hW : W ∈ 𝓝 (σ s)) :
    ∀ᶠ n in atTop, closedTerminalCap ((M.stages n).terminals.H (M.markIndex n s)) ⊆ π ⁻¹' W :=
  M.eventually_marked_cap_subset s (markedNeighborhoods_shrink σ s hW)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_AssignedCollarExclusion
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every assigned mixed normal limit satisfies the actual fixed-source
collar exclusion. The terminal containment is derived from the shrinking
neighborhoods and the closed component quotient. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem MixedModelExhaustion.eventually_marked_cap_in_open
    {S C : Type*} [LinearOrder C] {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates G π σ}
    {data : C → MaskedCoordinateData G d.source π σ} {retained : ℕ → C} {ρ : ℕ → ℝ}
    (M : MixedModelExhaustion d data retained (markedNeighborhoods σ) modelError ρ)
    (hclosed : IsClosedMap π) (s : S) {A : Set Sphere} (hA : IsOpen A)
    (hfiber : π ⁻¹' {σ s} ⊆ A) :
    ∀ᶠ n in atTop, closedTerminalCap ((M.stages n).terminals.H (M.markIndex n s)) ⊆ A := by
  let W := (π '' Aᶜ)ᶜ
  have hW : IsOpen W := (hclosed _ hA.isClosed_compl).isOpen_compl
  have hs : σ s ∈ W := by
    rintro ⟨p, hp, he⟩
    exact hp (hfiber he)
  have hpre : π ⁻¹' W ⊆ A := by
    intro p hp
    by_contra hn
    exact hp (mem_image_of_mem _ hn)
  exact (M.eventually_marked_cap_in_nhds s (hW.mem_nhds hs)).mono fun _ hn => hn.trans hpre

 theorem AssignedMixedModelLimit.excludes_source_collar
    (hgreen : UnorientedFiniteCircleGreenFormula) (hsch : PlanarSchoenflies)
    (harea : ExteriorCoefficientAreaTheorem)
    {S C : Type*} [LinearOrder C] {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates G π σ}
    {data : C → MaskedCoordinateData G d.source π σ} {retained : ℕ → C} {ρ : ℕ → ℝ}
    {M : MixedModelExhaustion d data retained (markedNeighborhoods σ) modelError ρ}
    (L : AssignedMixedModelLimit M)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G) (hπ : Continuous π) (hclosed : IsClosedMap π)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : PositiveJordanParametrization H γ)
    (hbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G)
    (hH : ∀ z ∈ frontier (jordanInterior H), ‖z‖ ≤ 4 * M.real.radius)
    (j : C)
    (hmask : realChartDomain (closedTerminalCap H) ⊆ interior (physicalMask π (data j).mask))
    (hfiber : π ⁻¹' {σ (data j).singular} ⊆ ((↑) : ℂ → Sphere) '' jordanInterior H)
    (v : ℝ → ℝ) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hp : ∀ t, (v t : UnitAddCircle) = (data j).physical (Complex.equivRealProdCLM (γ t))) :
    (boundaryCurveTrace (L.function ∘ γ) (L.continuousOn.comp_continuous hγ.smooth.continuous
      (fun t => hbd (mem_image_of_mem _ (hγ.mem_frontier t)))), L.center (data j).singular,
        (⟨L.radius (data j).singular, (L.bounds _).2.1⟩ : ℝ≥0)) ∉
      boundaryExclusionSet v ((data j).sourceStokesBudget (5 * M.real.radius)) := by
  have hm : ∀ z ∈ frontier (jordanInterior H), Complex.equivRealProdCLM z ∈
      interior (physicalMask π (data j).mask) := by
    intro z hz
    apply hmask
    change ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM z) : ℂ) : Sphere) ∈
      closedTerminalCap H
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact mem_image_of_mem _ (frontier_subset_closure hz)
  have hcap := M.eventually_marked_cap_in_open hclosed (data j).singular
    (OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen H)) hfiber
  have hb := M.eventually_source_collar_stokes hgreen hsch harea hG hinf hπ H γ hγ hbd hH j
    hmask L.assignment (fun n => M.markIndex n (data j).singular)
    (M.eventually_markIndex _) hcap L.subsequence L.strict.tendsto_atTop
    (fun n => L.disk_center n (data j).singular) (fun n => L.disk_radius n (data j).singular)
    (L.disk_eq _)
  exact M.excludes_source_stokes_limit H γ hγ hbd j hm v hv hp
    L.subsequence L.strict.tendsto_atTop L.function L.continuousOn L.converges
    (fun n => L.disk_center n (data j).singular) (L.center _) (L.center_tendsto _)
    (fun n => L.disk_radius n (data j).singular) ⟨L.radius _, (L.bounds _).2.1⟩
    (fun n => (L.disk_bounds n _).2.1) (L.radius_tendsto _) (5 * M.real.radius) _ _
    modelError_tendsto hb

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_SelectableMaskedCoordinate
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected coordinate retains the precise level and flag data needed
for a later endpoint-law construction. Weighted coarea is proved for the
actual physical mean before placing it in this interface. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

namespace SelectableMaskedCoordinate
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}

theorem CompatibleWith.mono {c : SelectableMaskedCoordinate d π}
    {A B : Set (SelectableMaskedCoordinate d π)}
    (h : c.CompatibleWith B) (hAB : A ⊆ B) : c.CompatibleWith A :=
  ⟨fun a ha => h.1 a (hAB ha), fun n q hq => h.2 n q (fun i => hAB (hq i))⟩

end SelectableMaskedCoordinate

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SelectedMixedSmallness
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real seed's collapse estimates survive the common mixed construction, even when
its real coordinates are enumerated differently and further marked points are retained. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

namespace SelectedMixedModels
variable {hsch : PlanarSchoenflies} {base : PathCodeData Sphere Sphere}
  {hU : IsOpen base.quotientDomain} {hdense : Dense base.quotientDomain}
  {π : Sphere → Sphere}
  {he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val}
  {hB : base.dust = π '' base.physicalDomainᶜ}
  {L : Type*} [LinearOrder L] {D : L → SelectableMaskedCoordinate base π}
  {presentation : ∀ l, SelectedLevelPresentation hsch base π (D l).coordinate}
  {B₀ : Set base.dust}

 theorem retains_real_presentation
    (F : SelectedMixedModels hsch base hU hdense π he hB D presentation B₀)
    (l : L) (R : RealCoordinatePresentation base π (D l).coordinate)
    (hR : presentation l = Sum.inl R) :
    ∃ n, F.realLabels n = l ∧ F.realCoordinates.physical n = R.coordinate.physical ∧
      F.realCoordinates.coordinate n = R.coordinate.quotient :=
  F.real_cover l R hR

end SelectedMixedModels
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_SelectedRealBandNorm
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact retained quotient functions give the actual band-norm bound in
the common countable model, even after re-enumeration and added marks. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace SelectedMixedModels
variable {hsch : PlanarSchoenflies} {base : PathCodeData Sphere Sphere}
  {hU : IsOpen base.quotientDomain} {hdense : Dense base.quotientDomain}
  {π : Sphere → Sphere}
  {he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val}
  {hB : base.dust = π '' base.physicalDomainᶜ}
  {I : Type*} [LinearOrder I] {D : I → SelectableMaskedCoordinate base π}
  {presentation : ∀ l, SelectedLevelPresentation hsch base π (D l).coordinate}
  {B₀ : Set base.dust}

 theorem retains_real_band_norm
    (F : SelectedMixedModels hsch base hU hdense π he hB D presentation B₀)
    (l : I) (P : RealCoordinatePresentation base π (D l).coordinate)
    (hP : presentation l = Sum.inl P)
    (w : Sphere → ℝ≥0∞) (hw : (∑' x, w x ^ 2) < ∞)
    (hband : ∀ x ∈ base.dust, ENNReal.ofReal
      (limsup P.coordinate.quotient (𝓝[base.quotientDomain] x) -
        liminf P.coordinate.quotient (𝓝[base.quotientDomain] x)) ≤ w x) :
    ∃ n, F.realCoordinates.physical n = P.coordinate.physical ∧
      Real.sqrt (∑' s, (F.realCoordinates.upper n s - F.realCoordinates.lower n s) ^ 2) ≤
        (countingSquareNorm w).toReal := by
  obtain ⟨n, _, hphysical, hquotient⟩ := F.retains_real_presentation l P hP
  refine ⟨n, hphysical, ?_⟩
  apply real_square_norm_le_counting _ w (fun s : F.marks => s.val.val)
    (Subtype.val_injective.comp Subtype.val_injective)
    (F.realCoordinates.width_nonneg n) _ hw
  intro s
  change ENNReal.ofReal
    (limsup (F.realPresentation n).coordinate.quotient (𝓝[base.quotientDomain] s.val.val) -
      liminf (F.realPresentation n).coordinate.quotient (𝓝[base.quotientDomain] s.val.val)) ≤ _
  change (F.realPresentation n).coordinate.quotient = P.coordinate.quotient at hquotient
  rw [hquotient]
  exact hband s.val.val s.val.property

end SelectedMixedModels
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RealExclusionWitness
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A real barrier test retains its actual presentation, band weight,
open map neighborhood, and the proved radius-dependent exclusion. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

namespace SelectedMixedModels
variable {hsch : PlanarSchoenflies} {base : PathCodeData Sphere Sphere}
  {hU : IsOpen base.quotientDomain} {hdense : Dense base.quotientDomain}
  {π : Sphere → Sphere}
  {he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val}
  {hB : base.dust = π '' base.physicalDomainᶜ}
  {I : Type*} [LinearOrder I] {D : I → SelectableMaskedCoordinate base π}
  {presentation : ∀ l, SelectedLevelPresentation hsch base π (D l).coordinate}
  {B₀ : Set base.dust}

 theorem excludes_retained_sized_real
    (F : SelectedMixedModels hsch base hU hdense π he hB D presentation B₀)
    (A : AssignedMixedModelLimit F.model) (hG : IsOpen base.physicalDomain)
    (l : I) (W : RealExclusionWitness base π (D l).coordinate)
    (hW : presentation l = Sum.inl W.presentation) (c : ℂ) (r : ℝ≥0) :
    ((finiteSourceMap A.function A.continuousOn, c, r), F.model.real.radius) ∉
      W.sizedNeighborhood := by
  intro hp
  obtain ⟨n, hphysical, hnorm⟩ := F.retains_real_band_norm l W.presentation hW
    W.weight W.weight_finite W.band_bound
  have hn := W.excludes F.model.real A.toReal n hG modelError_tendsto
    (show 3 * F.model.real.radius ≤ W.radius from by
      have h : F.model.real.radius < W.radius / 3 := hp.2
      linarith) hphysical hnorm
  exact hn hp.1.1

end SelectedMixedModels
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_MixedMapDiskExclusion
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual assigned mixed limit avoids every retained source test in
the map--disk topology used for countable selection. -/

open Set Function Filter
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem AssignedMixedModelLimit.not_mem_mapDiskExclusion
    (hgreen : UnorientedFiniteCircleGreenFormula) (hsch : PlanarSchoenflies)
    (harea : ExteriorCoefficientAreaTheorem)
    {S C : Type*} [LinearOrder C] {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates G π σ}
    {data : C → MaskedCoordinateData G d.source π σ} {retained : ℕ → C} {ρ : ℕ → ℝ}
    {M : MixedModelExhaustion d data retained (markedNeighborhoods σ) modelError ρ}
    (L : AssignedMixedModelLimit M)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G) (hπ : Continuous π) (hclosed : IsClosedMap π)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : PositiveJordanParametrization H γ)
    (hbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G)
    (hH : ∀ z ∈ frontier (jordanInterior H), ‖z‖ ≤ 4 * M.real.radius)
    (j : C)
    (hmask : realChartDomain (closedTerminalCap H) ⊆ interior (physicalMask π (data j).mask))
    (hfiber : π ⁻¹' {σ (data j).singular} ⊆ ((↑) : ℂ → Sphere) '' jordanInterior H)
    (v : ℝ → ℝ) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hp : ∀ t, (v t : UnitAddCircle) = (data j).physical (Complex.equivRealProdCLM (γ t))) :
    (finiteSourceMap L.function L.continuousOn, L.center (data j).singular,
      (⟨L.radius (data j).singular, (L.bounds _).2.1⟩ : ℝ≥0)) ∉
      mapDiskExclusion
        (sourceCircuit γ hγ.smooth.continuous (fun t => hbd (mem_image_of_mem _ (hγ.mem_frontier t))))
        v ((data j).sourceStokesBudget (5 * M.real.radius)) := by
  exact L.excludes_source_collar hgreen hsch harea hG hinf hπ hclosed H γ hγ hbd hH j
    hmask hfiber v hv hp

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RestrictedMeanExclusion
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricting to the common countable marks preserves a mean exclusion.
Its source budget can only decrease, so the original open neighborhood
remains excluded by a mixed limit retaining that coordinate. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MeanExclusionWitness
variable {T : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : T → Sphere}
    {N : MaskedCoordinateData G U π σ} {F₀ : ℂ → ℂ}
    {hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' G)} {c : ℂ} {r : ℝ≥0} {R : ℝ}
    (W : MeanExclusionWitness N F₀ hF₀ c r R)

 theorem neighborhood_subset_restrictMarks (A : Set T) (hsing : N.singular ∈ A)
    (hsupport : ∀ s, N.upper s - N.lower s ≠ 0 → s ∈ A) (hR : 0 ≤ R) :
    W.neighborhood ⊆ (W.restrictMarks A hsing hsupport hR).neighborhood := by
  intro p hp
  exact (N.restrictMarks_sourceStokesBudget_le A hsing hsupport hR).trans_lt hp

 theorem not_mem_neighborhood
    (hgreen : UnorientedFiniteCircleGreenFormula) (hsch : PlanarSchoenflies)
    (harea : ExteriorCoefficientAreaTheorem)
    {J : Type*} [LinearOrder J] {d : CountableRealCoordinates G π σ}
    {data : J → MaskedCoordinateData G d.source π σ} {retained : ℕ → J} {ρ : ℕ → ℝ}
    {M : MixedModelExhaustion d data retained (markedNeighborhoods σ) modelError ρ}
    (L : AssignedMixedModelLimit M)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G) (hπ : Continuous π) (hclosed : IsClosedMap π)
    (hU : d.source = U) (j : J) (hN : HEq (data j) N)
    (hsize : R = 5 * M.real.radius)
    (hbound : ∀ z ∈ frontier (jordanInterior W.disk), ‖z‖ ≤ 4 * M.real.radius) :
    (finiteSourceMap L.function L.continuousOn, L.center (data j).singular,
      (⟨L.radius (data j).singular, (L.bounds _).2.1⟩ : ℝ≥0)) ∉ W.neighborhood := by
  subst U
  cases eq_of_heq hN
  subst R
  exact L.not_mem_mapDiskExclusion hgreen hsch harea hG hinf hπ hclosed
    W.disk W.curve W.regular W.boundary hbound j W.mask W.fiber W.lift W.smooth_lift W.projects

end MeanExclusionWitness
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MeanExclusionRadius
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed mean exclusion remains valid for every smaller target-radius
budget. This permits an open radius interval in the common selection space. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

namespace MeanExclusionWitness
variable {T : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : T → Sphere}
    {N : MaskedCoordinateData G U π σ} {F₀ : ℂ → ℂ}
    {hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' G)} {c : ℂ} {r : ℝ≥0} {R : ℝ}
    (W : MeanExclusionWitness N F₀ hF₀ c r R)

 theorem neighborhood_subset_smallerRadius {R' : ℝ} (hR : R' ≤ R) :
    W.neighborhood ⊆ (W.smallerRadius hR).neighborhood :=
  fun _ hp => (N.sourceStokesBudget_mono hR).trans_lt hp

 theorem not_mem_of_radius_le
    (hgreen : UnorientedFiniteCircleGreenFormula) (hsch : PlanarSchoenflies)
    (harea : ExteriorCoefficientAreaTheorem)
    {J : Type*} [LinearOrder J] {d : CountableRealCoordinates G π σ}
    {data : J → MaskedCoordinateData G d.source π σ} {retained : ℕ → J} {ρ : ℕ → ℝ}
    {M : MixedModelExhaustion d data retained (markedNeighborhoods σ) modelError ρ}
    (L : AssignedMixedModelLimit M)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G) (hπ : Continuous π) (hclosed : IsClosedMap π)
    (hU : d.source = U) (j : J) (hN : HEq (data j) N)
    (hsize : 5 * M.real.radius ≤ R)
    (hbound : ∀ z ∈ frontier (jordanInterior W.disk), ‖z‖ ≤ 4 * M.real.radius) :
    (finiteSourceMap L.function L.continuousOn, L.center (data j).singular,
      (⟨L.radius (data j).singular, (L.bounds _).2.1⟩ : ℝ≥0)) ∉ W.neighborhood := by
  have hnot := (W.smallerRadius hsize).not_mem_neighborhood hgreen hsch harea L
    hG hinf hπ hclosed hU j hN rfl hbound
  exact fun hp => hnot (W.neighborhood_subset_smallerRadius hsize hp)

end MeanExclusionWitness
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SizedMeanExclusion
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Record the exterior model radius in the same second countable test
space. An open radius interval retains the quantitative Stokes exclusion
under subsequent common-model selection. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MeanExclusionWitness
variable {T : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : T → Sphere}
    {N : MaskedCoordinateData G U π σ} {F₀ : ℂ → ℂ}
    {hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' G)} {c : ℂ} {r : ℝ≥0} {R : ℝ}
    (W : MeanExclusionWitness N F₀ hF₀ c r R)

 theorem not_mem_sizedNeighborhood
    (hgreen : UnorientedFiniteCircleGreenFormula) (hsch : PlanarSchoenflies)
    (harea : ExteriorCoefficientAreaTheorem)
    {J : Type*} [LinearOrder J] {d : CountableRealCoordinates G π σ}
    {data : J → MaskedCoordinateData G d.source π σ} {retained : ℕ → J} {ρ : ℕ → ℝ}
    {M : MixedModelExhaustion d data retained (markedNeighborhoods σ) modelError ρ}
    (L : AssignedMixedModelLimit M)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G) (hπ : Continuous π) (hclosed : IsClosedMap π)
    (hU : d.source = U) (j : J) (hN : HEq (data j) N)
    (B : ℝ) (hbound : ∀ z ∈ frontier (jordanInterior W.disk), ‖z‖ ≤ 4 * B) :
    ((finiteSourceMap L.function L.continuousOn, L.center (data j).singular,
      (⟨L.radius (data j).singular, (L.bounds _).2.1⟩ : ℝ≥0)), M.real.radius) ∉
        W.sizedNeighborhood B := by
  intro hp
  apply W.not_mem_of_radius_le hgreen hsch harea L hG hinf hπ hclosed hU j hN
    (by have h := hp.2.2; linarith) (fun z hz => (hbound z hz).trans (by have h := hp.2.1; linarith))
  exact hp.1

end MeanExclusionWitness
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SelectedMixedSizedMeanExclusion
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The open radius interval and the original mean exclusion survive the
restriction to the selected common marks. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace SelectedMixedModels
variable {hsch : PlanarSchoenflies} {base : PathCodeData Sphere Sphere}
  {hU : IsOpen base.quotientDomain} {hdense : Dense base.quotientDomain}
  {π : Sphere → Sphere}
  {he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val}
  {hB : base.dust = π '' base.physicalDomainᶜ}
  {I : Type*} [LinearOrder I] {D : I → SelectableMaskedCoordinate base π}
  {presentation : ∀ l, SelectedLevelPresentation hsch base π (D l).coordinate}
  {B₀ : Set base.dust}

 theorem excludes_retained_sized_mean
    (F : SelectedMixedModels hsch base hU hdense π he hB D presentation B₀)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (A : AssignedMixedModelLimit F.model)
    (hG : IsOpen base.physicalDomain) (hinf : OnePoint.infty ∈ base.physicalDomain)
    (hπ : Continuous π) (hclosed : IsClosedMap π)
    (l : I) {F₀ : ℂ → ℂ}
    {hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' base.physicalDomain)}
    {c : ℂ} {r : ℝ≥0} {R : ℝ}
    (W : MeanExclusionWitness (D l).coordinate F₀ hF₀ c r R)
    (B : ℝ) (hbound : ∀ z ∈ frontier (jordanInterior W.disk), ‖z‖ ≤ 4 * B) :
    ((finiteSourceMap A.function A.continuousOn,
      A.center ⟨(D l).coordinate.singular, F.singular l⟩,
      (⟨A.radius ⟨(D l).coordinate.singular, F.singular l⟩,
        (A.bounds _).2.1⟩ : ℝ≥0)), F.model.real.radius) ∉ W.sizedNeighborhood B := by
  intro hp
  have hR : 0 ≤ R := by
    have hpos := F.model.real.radius_pos
    have hupper := hp.2.2
    linarith
  let W' := W.restrictMarks F.marks (F.singular l) (F.support l) hR
  apply W'.not_mem_sizedNeighborhood hgreen hsch harea A hG hinf hπ hclosed rfl l
    HEq.rfl B hbound
  exact ⟨W.neighborhood_subset_restrictMarks F.marks (F.singular l) (F.support l) hR hp.1,
    hp.2⟩

end SelectedMixedModels
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_CoordinateExclusionTest
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real and mean tests use one common map--disk--radius space. The mark
index is kept discrete, so each selected test retains the component it excludes. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

namespace CoordinateExclusionTest
variable {hsch : PlanarSchoenflies} {base : PathCodeData Sphere Sphere}
  {π : Sphere → Sphere} {B₀ : Set base.dust} {B : ℝ}
  (T : CoordinateExclusionTest hsch base π B₀ B)

 theorem excludes_retained
    {hU : IsOpen base.quotientDomain} {hdense : Dense base.quotientDomain}
    {he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val}
    {hB : base.dust = π '' base.physicalDomainᶜ}
    {I : Type*} [LinearOrder I] {D : I → SelectableMaskedCoordinate base π}
    {pres : ∀ l, SelectedLevelPresentation hsch base π (D l).coordinate}
    (F : SelectedMixedModels hsch base hU hdense π he hB D pres B₀)
    (A : AssignedMixedModelLimit F.model)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (hG : IsOpen base.physicalDomain) (hinf : OnePoint.infty ∈ base.physicalDomain)
    (hπ : Continuous π) (hclosed : IsClosedMap π)
    (l : I) (hD : D l = T.coordinate) (hpres : HEq (pres l) T.presentation) :
    (T.mark, (finiteSourceMap A.function A.continuousOn,
      A.center ⟨T.mark.val, F.mandatory T.mark.property⟩,
      (⟨A.radius ⟨T.mark.val, F.mandatory T.mark.property⟩,
        (A.bounds _).2.1⟩ : ℝ≥0)), F.model.real.radius) ∉ T.neighborhood := by
  rcases T with ⟨p, c, W⟩
  dsimp only at hD
  cases hD
  cases W with
  | inl W =>
    have hp : pres l = Sum.inl W.presentation := eq_of_heq hpres
    exact fun hx => F.excludes_retained_sized_real A hG l W hp _ _ hx.2
  | inr W =>
    have hs : (D l).coordinate.singular = p.val := W.singular
    have hidx : (⟨(D l).coordinate.singular, F.singular l⟩ : F.marks) =
        ⟨p.val, F.mandatory p.property⟩ := Subtype.ext hs
    have hn := F.excludes_retained_sized_mean hgreen harea A hG hinf hπ hclosed l
      W.witness B W.source_bound
    rw [hidx] at hn
    exact fun hx => hn hx.2

end CoordinateExclusionTest
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FullSelectedCompatibility
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compatibility against the whole ordered selected family implies
admissibility for the same greedy open selection. -/
open Set Function
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

 theorem seed_and_selected_subset_ordered_range
    {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    (seed : ℕ → SelectableMaskedCoordinate base π) {T : Type*}
    (data : T → SelectableMaskedCoordinate base π)
    (S : ℕ → Set T) (q : ℕ → Option T)
    (hpref : ∀ n c, c ∈ S n ↔ ∃ k < n, q k = some c) :
    range seed ∪ data '' (⋃ n, S n) ⊆ range (orderedSelectedCoordinates seed data q) := by
  rintro c (⟨n, rfl⟩ | ⟨t, ht, rfl⟩)
  · exact ⟨Sum.inlₗ n, rfl⟩
  · obtain ⟨n, hn⟩ := mem_iUnion.mp ht
    obtain ⟨k, _, hk⟩ := (hpref n t).mp hn
    exact ⟨Sum.inrₗ k, by simp only [orderedSelectedCoordinates, ofLex_toLex, hk, Option.elim_some]⟩

 theorem seeded_allowed_of_ordered_compatible
    {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    (seed : ℕ → SelectableMaskedCoordinate base π) {T : Type*}
    (data : T → SelectableMaskedCoordinate base π)
    (S : ℕ → Set T) (q : ℕ → Option T)
    (hpref : ∀ n c, c ∈ S n ↔ ∃ k < n, q k = some c)
    (t : T) (ht : (data t).CompatibleWith (range (orderedSelectedCoordinates seed data q))) :
    seededMaskedAllowed seed data (⋃ n, S n) t :=
  ht.mono (seed_and_selected_subset_ordered_range seed data S q hpref)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SeededLevelPresentations
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Carry the actual real or mean presentation through the ordered selection, including
unused slots filled by the original zero coordinate. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

 theorem orderedSelectedPresentations_some
    {hsch : PlanarSchoenflies} {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    (seed : ℕ → SelectableMaskedCoordinate d π)
    (seedPresentation : ∀ n, RealCoordinatePresentation d π (seed n).coordinate)
    {T : Type*} (data : T → SelectableMaskedCoordinate d π)
    (presentation : ∀ t, SelectedLevelPresentation hsch d π (data t).coordinate)
    (q : ℕ → Option T) (n : ℕ) (t : T) (h : q n = some t) :
    HEq (orderedSelectedPresentations seed seedPresentation data presentation q (Sum.inrₗ n))
      (presentation t) := by
  simp only [orderedSelectedPresentations, Lex.rec, ofLex_toLex, orderedSelectedCoordinates]
  generalize hopt : q n = opt at *
  cases opt with
  | none => cases h
  | some t' => cases Option.some.inj h; rfl

 theorem orderedSelectedPresentations_seed
    {hsch : PlanarSchoenflies} {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    (seed : ℕ → SelectableMaskedCoordinate d π)
    (seedPresentation : ∀ n, RealCoordinatePresentation d π (seed n).coordinate)
    {T : Type*} (data : T → SelectableMaskedCoordinate d π)
    (presentation : ∀ t, SelectedLevelPresentation hsch d π (data t).coordinate)
    (q : ℕ → Option T) (n : ℕ) :
    orderedSelectedPresentations seed seedPresentation data presentation q (Sum.inlₗ n) =
      Sum.inl (seedPresentation n) := rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SelectedExclusionUnion
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every neighborhood chosen by the actual ordered selection is excluded
by its common mixed limit, with its original component label retained. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

 theorem selected_limit_avoids_test_union
    {hsch : PlanarSchoenflies} {base : PathCodeData Sphere Sphere}
    {hU : IsOpen base.quotientDomain} {hdense : Dense base.quotientDomain}
    {π : Sphere → Sphere}
    {he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val}
    {hB : base.dust = π '' base.physicalDomainᶜ}
    (seed : ℕ → SelectableMaskedCoordinate base π)
    (seedPresentation : ∀ n, RealCoordinatePresentation base π (seed n).coordinate)
    {B₀ : Set base.dust} {B : ℝ}
    (S : ℕ → Set (CoordinateExclusionTest hsch base π B₀ B))
    (q : ℕ → Option (CoordinateExclusionTest hsch base π B₀ B))
    (hpref : ∀ n c, c ∈ S n ↔ ∃ k < n, q k = some c)
    (F : SelectedMixedModels hsch base hU hdense π he hB
      (orderedSelectedCoordinates seed CoordinateExclusionTest.coordinate q)
      (orderedSelectedPresentations seed seedPresentation CoordinateExclusionTest.coordinate
        CoordinateExclusionTest.presentation q) B₀)
    (A : AssignedMixedModelLimit F.model)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (hG : IsOpen base.physicalDomain) (hinf : OnePoint.infty ∈ base.physicalDomain)
    (hπ : Continuous π) (hclosed : IsClosedMap π) :
    ∀ p : B₀,
      (p, (finiteSourceMap A.function A.continuousOn,
        A.center ⟨p.val, F.mandatory p.property⟩,
        (⟨A.radius ⟨p.val, F.mandatory p.property⟩, (A.bounds _).2.1⟩ : ℝ≥0)),
          F.model.real.radius) ∉ ⋃ t ∈ ⋃ n, S n, t.neighborhood := by
  intro p hx
  obtain ⟨t, ht, hx⟩ := mem_iUnion₂.mp hx
  obtain ⟨n, hn⟩ := mem_iUnion.mp ht
  obtain ⟨k, _, hk⟩ := (hpref n t).mp hn
  have hp : p = t.mark := (mem_singleton_iff.mp hx.1)
  subst p
  apply t.excludes_retained F A hgreen harea hG hinf hπ hclosed (Sum.inrₗ k) _ _ hx
  · simp only [orderedSelectedCoordinates, ofLex_toLex, hk, Option.elim_some]
  · exact orderedSelectedPresentations_some seed seedPresentation
      CoordinateExclusionTest.coordinate CoordinateExclusionTest.presentation q k t hk

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SelectedMarkedEndEquality
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coverage and the constructed local test rule out every protrusion at
a mandatory marked end of the actual selected mixed limit. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_34
theorem selected_marked_end_eq_disk
    (hcoarea : PlanarLipschitzFiberCoarea) (hweighted : WeightedPlanarScalarCoarea)
    (hLusin : FiniteTorusAnalyticMeasurability)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcollar : SmoothRegularJordanCollars) (hselect : BorelPathRelationSelection)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (base : PathCodeData Sphere Sphere)
    (hG : IsOpen base.physicalDomain) (hconn : IsConnected base.physicalDomain)
    (hU : IsOpen base.quotientDomain) (hdense : Dense base.quotientDomain)
    (hdust : base.dust = base.quotientDomainᶜ) (hinftyU : OnePoint.infty ∈ base.quotientDomain)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val)
    (hTD : IsTotallyDisconnected base.quotientDomainᶜ)
    (hbad : ∀ p ∈ base.physicalDomainᶜ, π p ∈ base.quotientDomainᶜ)
    (hinf : OnePoint.infty ∈ base.physicalDomain)
    (hBimage : base.dust = π '' base.physicalDomainᶜ)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀ K : Set Sphere, IsCompact K → LocallyConnectedSpace K →
      HasSimpleArcsInConnectedOpens K)
    (E₀ : Set Sphere) (hE₀ : IsCompact E₀) (hE₀U : E₀ ⊆ base.quotientDomain)
    (B : ℝ) (hfar : ∀ z : ℂ, B ≤ ‖z‖ → π (z : Sphere) ∈ E₀)
    (B₀ : Set base.dust)
    (seed : ℕ → SelectableMaskedCoordinate base π)
    (seedPresentation : ∀ n, RealCoordinatePresentation base π (seed n).coordinate)
    (S : ℕ → Set (CoordinateExclusionTest hsch base π B₀ (B / 4)))
    (q : ℕ → Option (CoordinateExclusionTest hsch base π B₀ (B / 4)))
    (hpref : ∀ n c, c ∈ S n ↔ ∃ k < n, q k = some c)
    (hcover : ∀ t, seededMaskedAllowed seed CoordinateExclusionTest.coordinate (⋃ n, S n) t →
      t.neighborhood ⊆ ⋃ t ∈ ⋃ n, S n, t.neighborhood)
    (hcompat : let D := orderedSelectedCoordinates seed CoordinateExclusionTest.coordinate q
      ∀ (j : ℕ ⊕ₗ ℕ) (n : ℕ) (labels : Fin n → ℕ ⊕ₗ ℕ), (∀ i, labels i < j) →
        (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
          (freeComponentFailure (base.dust \ ⋃ k, (D k).flags) (D j).coordinate.graph
            (fun k => (D k).coordinate.graph) labels) = 0)
    (F : SelectedMixedModels hsch base hU hdense π he hBimage
      (orderedSelectedCoordinates seed CoordinateExclusionTest.coordinate q)
      (orderedSelectedPresentations seed seedPresentation CoordinateExclusionTest.coordinate
        CoordinateExclusionTest.presentation q) B₀)
    (A : AssignedMixedModelLimit F.model) (hB : B / 4 < F.model.real.radius)
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hderiv : ∀ z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C₀ / (1 + ‖z‖ ^ 2))
    (hstandard : ∀ e : PathCodeData Sphere Sphere, [StandardBorelSpace (BasePathCode e)] →
      StandardBorelProbabilityLaws (BasePathCode e))
    (hpath : PolishProbabilityLaws C(PathTime, Sphere))
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (hω : ∀ i, ω i ≠ 0) (hωsum : (∑' i, ω i) < ∞)
    (hdual : ∀ (e : PathCodeData Sphere Sphere)
      (J : Set ℕ) [PolishSpace J] (b : J → Sphere) (c : J → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasureImageDuality (ConstrainedCostCode e b c ν) (PathCostSpace Sphere J))
    (hlift : ∀ (e : PathCodeData Sphere Sphere)
      (J : Set ℕ) [PolishSpace J] (b : J → Sphere) (c : J → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasurePlanLifting (ConstrainedCostCode e b c ν) (PathCostSpace Sphere J)) :
    ∀ (p : B₀) (x : Sphere), x ∈ base.physicalDomainᶜ → π x = p.val.val →
      ∀ E : RealTargetEnd A.toReal x,
        E.plane = Metric.closedBall (A.center ⟨p.val, F.mandatory p.property⟩)
          (A.radius ⟨p.val, F.mandatory p.property⟩) := by
  classical
  let : Countable (ℕ ⊕ₗ ℕ) := Function.Injective.countable
    (show Injective (ofLex : (ℕ ⊕ₗ ℕ) → ℕ ⊕ ℕ) from fun _ _ h => by
      simpa only [toLex_ofLex] using congrArg toLex h)
  intro p x hx hxp E
  by_contra hne
  have hpfinite : p.val.val ≠ OnePoint.infty := by
    intro hp
    have hd : p.val.val ∈ base.quotientDomainᶜ := hdust ▸ p.val.property
    exact hd (hp ▸ hinftyU)
  obtain ⟨T, _, hT, hmem⟩ := exists_ordered_protrusion_test hcoarea hweighted hLusin
    hsard hsch hsep hcollar hselect harea base hG hconn hU hdense hdust π hπ hclosed
    hsurj hr he hTD hbad hinf hfiber harcs selectedCoordinateEnumeration
    (orderedSelectedCoordinates seed CoordinateExclusionTest.coordinate q)
    (orderedSelectedPresentations seed seedPresentation CoordinateExclusionTest.coordinate
      CoordinateExclusionTest.presentation q) hcompat E₀ hE₀ hE₀U B hfar B₀ p hpfinite
    E hx ⟨p.val, F.mandatory p.property⟩ hxp rfl hne hB C₀ hC₀ hderiv hstandard hpath
    ω hω hωsum hdual hlift
  exact selected_limit_avoids_test_union seed seedPresentation S q hpref F A
    hgreen harea hG hinf hπ hclosed p
    (hcover T (seeded_allowed_of_ordered_compatible seed CoordinateExclusionTest.coordinate
      S q hpref T hT) hmem)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SelectedRealCollapse
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the selected small tests to the full target boundary component. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer.RealTargetEnd

attribute [local instance] sphereMetric sphereBorel

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} {L : AssignedRealModelLimit M} {q : Sphere}

local instance instBorelSpaceSphere_r77f24d_1 : BorelSpace Sphere := ⟨rfl⟩
theorem target_eq_singleton_of_small_anchored_coordinates
    (E : RealTargetEnd L q)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (harea : ExteriorCoefficientAreaTheorem)
    (hG : IsOpen G) (hconn : IsConnected G) (hε : Tendsto ε atTop (𝓝 0))
    (hπ : Continuous π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hq : q ∈ Gᶜ) (A : SmoothJordanCore G) (j : Fin A.count)
    (hCA : connectedComponentIn Gᶜ q ⊆ ((↑) : ℂ → Sphere) '' jordanInterior (A.disk j))
    (EStar : Set Sphere)
    (hzero : ∀ z ∈ frontier (jordanInterior (A.disk j)), π (z : Sphere) ∈ EStar)
    (hsmall : SmallAnchoredPlateaus d EStar (π q)) :
    connectedComponentIn (extendAtInfinity L.function '' G)ᶜ E.point = {E.point} := by
  apply E.target_eq_singleton_of_small_anchored_plateaus hsard hsch harea
    hG hconn hε hπ hr hq A j hCA
  intro δ hδ
  obtain ⟨i, U, hU, hpU, hone, hz, hnorm⟩ := hsmall δ hδ
  refine ⟨i, U, hU, hpU, hone, ?_, hnorm⟩
  intro z hza
  rw [d.pullback i z (A.boundary_subset_domain j ⟨z, hza, rfl⟩)]
  exact hz _ (hzero z hza)

end CircleDomainRigidity.FiniteTransfer.RealTargetEnd

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_RetainedSmallTests
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real seed's collapse estimates survive the common mixed construction, even when
its real coordinates are enumerated differently and further marked points are retained. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

namespace SelectedMixedModels
variable {hsch : PlanarSchoenflies} {base : PathCodeData Sphere Sphere}
  {hU : IsOpen base.quotientDomain} {hdense : Dense base.quotientDomain}
  {π : Sphere → Sphere}
  {he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val}
  {hB : base.dust = π '' base.physicalDomainᶜ}
  {L : Type*} [LinearOrder L] {D : L → SelectableMaskedCoordinate base π}
  {presentation : ∀ l, SelectedLevelPresentation hsch base π (D l).coordinate}
  {B₀ : Set base.dust}

 theorem small_anchored_of_retained_tests_at
    (F : SelectedMixedModels hsch base hU hdense π he hB D presentation B₀)
    (EStar : Set Sphere) (A : Set (GradedRealTest base π EStar))
    (hpresentation : ∀ b ∈ A, ∃ (l : L)
      (R : RealCoordinatePresentation base π (D l).coordinate),
        presentation l = Sum.inl R ∧ R.coordinate = b.coordinate)
    (p : Sphere) (hcover : ∀ k, ∃ b ∈ A, b.grade = k ∧ p ∈ b.region) :
    SmallAnchoredPlateaus F.realCoordinates EStar p := by
  intro δ hδ
  obtain ⟨k, hk⟩ := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (gt_mem_nhds hδ)).exists
  obtain ⟨b, hb, hbk, hpb⟩ := hcover k
  obtain ⟨l, R, hR, hRb⟩ := hpresentation b hb
  obtain ⟨n, _, hphysical, hquotient⟩ := F.retains_real_presentation l R hR
  have hpq : F.realCoordinates.physical n = b.coordinate.physical := by
    rw [hphysical, hRb]
  have hqq : F.realCoordinates.coordinate n = b.coordinate.quotient := by
    rw [hquotient, hRb]
  refine ⟨n, b.region, b.region_open, hpb, ?_, ?_, ?_⟩
  · intro x hx
    rw [hqq]
    exact b.one x hx
  · intro x hx
    rw [hqq]
    exact b.zero x hx
  · have hn := b.toUngatedRealTest.ordinary_norm_le_size
      (by rw [hdense.closure_eq]; exact subset_univ _)
      (fun s : F.marks => s.val.val)
      (Subtype.val_injective.comp Subtype.val_injective)
      (by rintro _ ⟨s, rfl⟩; exact s.val.property)
    have hbsmall : b.toUngatedRealTest.size.toReal < 1 / ((k : ℝ) + 1) := by
      apply ENNReal.toReal_lt_of_lt_ofReal
      rw [← hbk]
      exact b.small
    apply lt_of_le_of_lt _ (hbsmall.trans hk)
    change Real.sqrt (∫ x in realChartDomain base.physicalDomain,
      gradientEnergy (F.realCoordinates.physical n)
        (fun z => sphericalMetricFactor z • 1) x) +
      Real.sqrt (∑' s : F.marks,
        (limsup (F.realPresentation n).coordinate.quotient (𝓝[base.quotientDomain] s.val.val) -
          liminf (F.realPresentation n).coordinate.quotient (𝓝[base.quotientDomain] s.val.val)) ^ 2) ≤ _
    change (F.realPresentation n).coordinate.quotient = b.coordinate.quotient at hqq
    simpa only [hpq, hqq] using hn

end SelectedMixedModels
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_RoundOuterCore
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed round outer zero contour is an actual smooth source core. -/

open Set Function Filter Metric
open scoped Topology Manifold ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

namespace FiniteTransfer.RealModelExhaustion

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  (M : RealModelExhaustion d O ε)

theorem outerCore_interior : jordanInterior (M.outerCore.disk 0) = ball 0 (2 * M.radius) :=
  roundOuterJordan_interior (2 * M.radius) (mul_pos (by norm_num) M.radius_pos)

theorem component_inside_outerCore (q : Sphere) :
    connectedComponentIn Gᶜ q ⊆ ((↑) : ℂ → Sphere) '' jordanInterior (M.outerCore.disk 0) := by
  rw [M.outerCore_interior]
  intro p hp
  have hpG := connectedComponentIn_subset Gᶜ q hp
  have hpball : p ∈ ((↑) : ℂ → Sphere) '' ball 0 M.radius := by
    by_contra h
    exact hpG (M.core_source 0 (M.exterior_core 0 h))
  exact (image_mono (ball_subset_ball (by linarith [M.radius_pos]))) hpball

end FiniteTransfer.RealModelExhaustion

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SelectedCircleDomain
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected mixed limit is a circle domain: its mandatory ends are the
exact selected disks, and the original graded real tests collapse all other ends. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_35
theorem selected_limit_isCircleDomain_oai
    (hcoarea : PlanarLipschitzFiberCoarea) (hweighted : WeightedPlanarScalarCoarea)
    (hLusin : FiniteTorusAnalyticMeasurability)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcollar : SmoothRegularJordanCollars) (hselect : BorelPathRelationSelection)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (base : PathCodeData Sphere Sphere)
    (hG : IsOpen base.physicalDomain) (hconn : IsConnected base.physicalDomain)
    (hU : IsOpen base.quotientDomain) (hdense : Dense base.quotientDomain)
    (hdust : base.dust = base.quotientDomainᶜ) (hinftyU : OnePoint.infty ∈ base.quotientDomain)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val)
    (hTD : IsTotallyDisconnected base.quotientDomainᶜ)
    (hbad : ∀ p ∈ base.physicalDomainᶜ, π p ∈ base.quotientDomainᶜ)
    (hinf : OnePoint.infty ∈ base.physicalDomain)
    (hBimage : base.dust = π '' base.physicalDomainᶜ)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀ K : Set Sphere, IsCompact K → LocallyConnectedSpace K →
      HasSimpleArcsInConnectedOpens K)
    (E₀ : Set Sphere) (hE₀ : IsCompact E₀) (hE₀U : E₀ ⊆ base.quotientDomain)
    (B : ℝ) (hfar : ∀ z : ℂ, B ≤ ‖z‖ → π (z : Sphere) ∈ E₀)
    (B₀ : Set base.dust)
    (seed : ℕ → SelectableMaskedCoordinate base π)
    (seedPresentation : ∀ n, RealCoordinatePresentation base π (seed n).coordinate)
    (S : ℕ → Set (CoordinateExclusionTest hsch base π B₀ (B / 4)))
    (q : ℕ → Option (CoordinateExclusionTest hsch base π B₀ (B / 4)))
    (hpref : ∀ n c, c ∈ S n ↔ ∃ k < n, q k = some c)
    (hcover : ∀ t, seededMaskedAllowed seed CoordinateExclusionTest.coordinate (⋃ n, S n) t →
      t.neighborhood ⊆ ⋃ t ∈ ⋃ n, S n, t.neighborhood)
    (hcompat : let D := orderedSelectedCoordinates seed CoordinateExclusionTest.coordinate q
      ∀ (j : ℕ ⊕ₗ ℕ) (n : ℕ) (labels : Fin n → ℕ ⊕ₗ ℕ), (∀ i, labels i < j) →
        (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
          (freeComponentFailure (base.dust \ ⋃ k, (D k).flags) (D j).coordinate.graph
            (fun k => (D k).coordinate.graph) labels) = 0)
    (F : SelectedMixedModels hsch base hU hdense π he hBimage
      (orderedSelectedCoordinates seed CoordinateExclusionTest.coordinate q)
      (orderedSelectedPresentations seed seedPresentation CoordinateExclusionTest.coordinate
        CoordinateExclusionTest.presentation q) B₀)
    (A : AssignedMixedModelLimit F.model) (hB : B / 4 < F.model.real.radius)
    (hBouter : B ≤ 2 * F.model.real.radius)
    (tests : Set (GradedRealTest base π E₀))
    (hretained : ∀ b ∈ tests, ∃ (i : ℕ), (seedPresentation i).coordinate = b.coordinate)
    (htests : ∀ p ∈ base.dust \ (Subtype.val '' B₀),
      ∀ k, ∃ b ∈ tests, b.grade = k ∧ p ∈ b.region)
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hderiv : ∀ z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C₀ / (1 + ‖z‖ ^ 2))
    (hstandard : ∀ e : PathCodeData Sphere Sphere, [StandardBorelSpace (BasePathCode e)] →
      StandardBorelProbabilityLaws (BasePathCode e))
    (hpath : PolishProbabilityLaws C(PathTime, Sphere))
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (hω : ∀ i, ω i ≠ 0) (hωsum : (∑' i, ω i) < ∞)
    (hdual : ∀ (e : PathCodeData Sphere Sphere)
      (J : Set ℕ) [PolishSpace J] (b : J → Sphere) (c : J → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasureImageDuality (ConstrainedCostCode e b c ν) (PathCostSpace Sphere J))
    (hlift : ∀ (e : PathCodeData Sphere Sphere)
      (J : Set ℕ) [PolishSpace J] (b : J → Sphere) (c : J → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasurePlanLifting (ConstrainedCostCode e b c ν) (PathCostSpace Sphere J)) :
    IsCircleDomain (extendAtInfinity A.function '' base.physicalDomain) := by
  classical
  refine ⟨A.conformal.1.isOpen_image hG hG (Subset.refl _),
    hconn.image _ (fun z hz => (A.conformal.1 z hz).1.continuousWithinAt), ?_⟩
  intro p hp
  obtain ⟨x, hx, E, hE⟩ := A.toReal.exists_source_end hG hp
  have hpx : π x ∈ base.dust := hBimage ▸ ⟨x, hx, rfl⟩
  by_cases hm : π x ∈ Subtype.val '' B₀
  · obtain ⟨b, hb, hbx⟩ := hm
    let b₀ : B₀ := ⟨b, hb⟩
    have hdisk := selected_marked_end_eq_disk hcoarea hweighted hLusin hsard hsch hsep hcollar hselect hgreen harea base hG hconn hU hdense hdust hinftyU
      π hπ hclosed hsurj hr he hTD hbad hinf hBimage hfiber harcs E₀ hE₀ hE₀U
      B hfar B₀ seed seedPresentation S q hpref hcover hcompat F A hB C₀ hC₀ hderiv
      hstandard hpath ω hω hωsum hdual hlift b₀ x hx hbx.symm E
    have hsphere := E.sphere_image_plane
    rw [hdisk, hE] at hsphere
    change ((↑) : ℂ → Sphere) '' Metric.closedBall
      (A.center ⟨b₀.val, F.mandatory b₀.property⟩) (A.radius ⟨b₀.val, F.mandatory b₀.property⟩) =
        connectedComponentIn (extendAtInfinity A.function '' base.physicalDomain)ᶜ p at hsphere
    exact hsphere ▸ coe_closedBall_is_singleton_or_round _ (A.bounds _).2.1
  · have hsmall : SmallAnchoredPlateaus F.realCoordinates E₀ (π x) := by
      apply F.small_anchored_of_retained_tests_at E₀ tests ?_ (π x) (htests _ ⟨hpx, hm⟩)
      intro b hb
      obtain ⟨i, hi⟩ := hretained b hb
      exact ⟨Sum.inlₗ i, seedPresentation i,
        orderedSelectedPresentations_seed seed seedPresentation
          CoordinateExclusionTest.coordinate CoordinateExclusionTest.presentation q i, hi⟩
    have hzero : ∀ z ∈ frontier (jordanInterior (F.model.real.outerCore.disk 0)),
        π (z : Sphere) ∈ E₀ := by
      rw [F.model.real.outerCore_interior,
        frontier_ball _ (ne_of_gt (mul_pos (by norm_num) F.model.real.radius_pos))]
      intro z hz
      apply hfar
      have hn : ‖z‖ = 2 * F.model.real.radius := by
        simpa only [Metric.mem_sphere, dist_zero_right] using hz
      exact hn ▸ hBouter
    have hc := E.target_eq_singleton_of_small_anchored_coordinates hsard hsch harea
      hG hconn modelError_tendsto hπ hr hx F.model.real.outerCore 0
      (F.model.real.component_inside_outerCore x) E₀ hzero hsmall
    change connectedComponentIn (extendAtInfinity A.function '' base.physicalDomain)ᶜ
      E.point = {E.point} at hc
    exact Or.inl ⟨p, hE ▸ hc⟩

end CircleDomainRigidity

end

end OAI
end

theorem solution : type_of% @OAI.CircleDomainRigidity.selected_limit_isCircleDomain_oai := @OAI.CircleDomainRigidity.selected_limit_isCircleDomain_oai
