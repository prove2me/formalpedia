-- Prove2me | solution 1 for OAI.MetricKMedian.FixedBatch.forced_step_local_bound_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:12:17.744996+00:00
-- url     : https://prove2.me/submissions/8ef581c4-c9e3-439d-b71b-a2fbe09e2abb

import Mathlib
import Definitions.Def_OAIQ053K015
import Definitions.Def_OAIQ053K018
import Definitions.Def_OAIQ053K020
import Theorems.Thm_OAI_MetricKMedian_Analytic_P_le_half_s53
import Theorems.Thm_OAI_MetricKMedian_Analytic_P_nonneg_s53
import Theorems.Thm_OAI_MetricKMedian_Analytic_m_nonneg_s53
import Theorems.Thm_OAI_MetricKMedian_FixedBatch_post_force_bound_s53

section
-- module Solutions.OAIQ053_KM.KMedian_Analysis_Coefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace MetricKMedian.Analytic

theorem texp_integrable (x : ℝ) :
    IntervalIntegrable (fun t : ℝ => t * Real.exp (-t * x)) MeasureTheory.volume 0 1 := by
  apply Continuous.intervalIntegrable
  fun_prop

theorem P_antitone : Antitone P := by
  intro x y hxy
  apply intervalIntegral.integral_mono_on (by norm_num) (texp_integrable y) (texp_integrable x)
  intro t ht
  apply mul_le_mul_of_nonneg_left _ ht.1
  apply Real.exp_le_exp.mpr
  nlinarith [ht.1]

theorem exp_neg_half_le_P {x : ℝ} (hx : 0 ≤ x) : Real.exp (-x) / 2 ≤ P x := by
  have hint : IntervalIntegrable (fun t : ℝ => t * Real.exp (-x))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    (a := (0 : ℝ)) (b := 1) (by norm_num) hint (texp_integrable x) (fun t ht =>
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [ht.2])) ht.1)
  rw [intervalIntegral.integral_mul_const] at h
  norm_num at h
  unfold P
  simp only [neg_mul]
  linarith

theorem P_pos {x : ℝ} (hx : 0 ≤ x) : 0 < P x := by
  exact lt_of_lt_of_le (div_pos (Real.exp_pos _) (by norm_num)) (exp_neg_half_le_P hx)

theorem A_le_one_add (x : ℝ) : A x ≤ 1 + x := by
  have hi : IntervalIntegrable (fun t : ℝ => 1 - Real.exp (-t * x))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hi' : IntervalIntegrable (fun t : ℝ => t * x) MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    (a := (0 : ℝ)) (b := 1) (by norm_num) hi hi' (fun t _ => by
      have he := Real.add_one_le_exp (-t * x)
      nlinarith)
  rw [intervalIntegral.integral_mul_const] at h
  norm_num at h
  unfold A
  simp only [neg_mul]
  linarith

theorem A_le_two {x : ℝ} (hx : x ≤ 1) : A x ≤ 2 := by
  linarith [A_le_one_add x]

end MetricKMedian.Analytic


end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_MomentAnalysis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Analytic

open MeasureTheory Set Filter
open scoped Topology Filter Interval

theorem moment_integrable (n : ℕ) (x : ℝ) :
    IntervalIntegrable (fun t : ℝ => t^n*Real.exp (-t*x)) volume 0 1 := by
  apply Continuous.intervalIntegrable
  fun_prop

theorem moment_nonneg (n : ℕ) (x : ℝ) : 0 ≤ moment n x := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro t ht
  exact mul_nonneg (pow_nonneg ht.1 n) (Real.exp_pos _).le

theorem moment_le_one (n : ℕ) {x : ℝ} (hx0 : 0 ≤ x) : moment n x ≤ 1 := by
  have h := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
    (moment_integrable n x) (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume 0 1)
    (fun t (ht : t ∈ Icc (0:ℝ) 1) => show t^n*Real.exp (-t*x) ≤ (1:ℝ) from by
      have hpow : t^n ≤ 1 := pow_le_one₀ ht.1 ht.2
      have he : Real.exp (-t*x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg ht.1 hx0])
      exact (mul_le_of_le_one_left (Real.exp_pos _).le hpow).trans he)
  simpa only [moment, intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul] using h

theorem coefficient_eq (x y : ℝ) : coefficient x y = 1+m x+B x*y := by
  unfold coefficient m B
  ring

theorem coefficient_ge_one {x y : ℝ} (hy : 0 ≤ y) : 1 ≤ coefficient x y := by
  rw [coefficient_eq]
  have hm := m_nonneg_s53 x
  have hB : 0 ≤ B x := mul_nonneg (by norm_num) (P_nonneg_s53 x)
  nlinarith only [hm, mul_nonneg hB hy]

end MetricKMedian.Analytic
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.PhysicalPotential

open Analytic

variable {I : Type*}

theorem mass_nonneg {g : ℝ} (hg : 0 ≤ g) (S : Finset I) : 0 ≤ mass g S := by
  exact mul_nonneg hg (Nat.cast_nonneg _)

theorem cost_nonneg {g : ℝ} {d : I → ℝ} {S : Finset I} (hg : 0 ≤ g)
    (hd : ∀ i ∈ S, 0 ≤ d i) : 0 ≤ cost g d S := by
  exact Finset.sum_nonneg (fun i hi => mul_nonneg hg (hd i hi))

theorem mass_mono {g : ℝ} {S T : Finset I} (hg : 0 ≤ g) (hST : S ⊆ T) :
    mass g S ≤ mass g T := by
  apply mul_le_mul_of_nonneg_left _ hg
  exact_mod_cast Finset.card_le_card hST

theorem cost_mono {g : ℝ} {d : I → ℝ} {S T : Finset I} (hg : 0 ≤ g)
    (hd : ∀ i ∈ T, 0 ≤ d i) (hST : S ⊆ T) : cost g d S ≤ cost g d T := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hST (fun i hi _ => mul_nonneg hg (hd i hi))

theorem mass_sdiff [DecidableEq I] (g : ℝ) {S T : Finset I} (hTS : T ⊆ S) :
    mass g (S \ T) = mass g S - mass g T := by
  unfold mass
  rw [Finset.card_sdiff_of_subset hTS, Nat.cast_sub (Finset.card_le_card hTS)]
  ring

theorem cost_sdiff [DecidableEq I] (g : ℝ) (d : I → ℝ) {S T : Finset I} (hTS : T ⊆ S) :
    cost g d (S \ T) = cost g d S - cost g d T := by
  exact Finset.sum_sdiff_eq_sub hTS

theorem cost_ge_mass_mul {g b : ℝ} {d : I → ℝ} {S : Finset I}
    (hg : 0 ≤ g) (hb : ∀ i ∈ S, b ≤ d i) : mass g S * b ≤ cost g d S := by
  have h := Finset.sum_le_sum (fun i (hi : i ∈ S) => mul_le_mul_of_nonneg_left (hb i hi) hg)
  simpa only [cost, mass, Finset.sum_const, nsmul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using h

theorem point_cost_le {g : ℝ} {d : I → ℝ} {S : Finset I} (hg : 0 ≤ g)
    (hd : ∀ i ∈ S, 0 ≤ d i) {i : I} (hi : i ∈ S) : g * d i ≤ cost g d S := by
  exact Finset.single_le_sum (fun j hj => mul_nonneg hg (hd j hj)) hi

theorem B_nonneg (x : ℝ) : 0 ≤ B x := mul_nonneg (by norm_num) (P_nonneg_s53 x)

theorem removal_identity [DecidableEq I] (x g : ℝ) (d : I → ℝ) {S E : Finset I}
    (hES : E ⊆ S) (b b' : ℝ) :
    potential x g d (S \ E) b' - potential x g d S b =
      mass g E * b' - (1 + m x + B x * mass g S) * cost g d E -
      B x * mass g E * (cost g d S - cost g d E) +
      (1 - mass g S) * (b' - b) := by
  simp only [potential, mass_sdiff g hES, cost_sdiff g d hES]
  ring

theorem force_savings [DecidableEq I] {x g b b' : ℝ} {d : I → ℝ} {S E : Finset I}
    (hg : 0 ≤ g) (hd : ∀ i ∈ S, 0 ≤ d i)
    (hES : E ⊆ S) (hδ : g ≤ mass g E) (hbE : ∀ i ∈ E, b' ≤ d i) :
    B x * g * cost g d S + (1 - mass g S) * (b - b') ≤
      potential x g d S b - potential x g d (S \ E) b' := by
  have hY := cost_nonneg hg (fun i hi => hd i (hES hi))
  have hV := cost_nonneg hg hd
  have hδy := mass_mono hg hES
  have hcap := cost_ge_mass_mul hg hbE
  have h1 := mul_nonneg (m_nonneg_s53 x) hY
  have h2 := mul_nonneg (B_nonneg x) (mul_nonneg (sub_nonneg.mpr hδy) hY)
  have h3 := mul_nonneg (B_nonneg x) (mul_nonneg (sub_nonneg.mpr hδ) hV)
  have hid := removal_identity x g d hES b b'
  nlinarith only [hcap, h1, h2, h3, hid]

theorem force_cap_bound {g b' : ℝ} {d : I → ℝ} {S E : Finset I}
    (hg : 0 < g) (hd : ∀ i ∈ S, 0 ≤ d i) (hES : E ⊆ S)
    (hE : E.Nonempty) (hbE : ∀ i ∈ E, b' ≤ d i) : b' ≤ cost g d S / g := by
  obtain ⟨i, hi⟩ := hE
  apply (le_div_iff₀ hg).mpr
  have hc := point_cost_le hg.le hd (hES hi)
  have hb := mul_le_mul_of_nonneg_left (hbE i hi) hg.le
  nlinarith only [hc, hb]

theorem savingsFraction_pos {g : ℝ} (hg : 0 < g) : 0 < savingsFraction g := by
  apply lt_min (by norm_num)
  exact div_pos (mul_pos (mul_pos (by norm_num) (P_pos (by norm_num))) hg)
    (by positivity)

theorem force_fraction [DecidableEq I] {x g b b' : ℝ} {d : I → ℝ} {S E : Finset I}
    (hx : x ≤ 1) (hg : 0 < g) (hd : ∀ i ∈ S, 0 ≤ d i)
    (hES : E ⊆ S) (hδ : g ≤ mass g E) (hy : mass g S ≤ 1)
    (hb' : 0 ≤ b') (hb : b' ≤ b) (hbE : ∀ i ∈ E, b' ≤ d i) :
    savingsFraction g * (cost g d S + (1 - mass g S) * b) ≤
      potential x g d S b - potential x g d (S \ E) b' := by
  have hE : E.Nonempty := by
    by_contra he
    have hzero : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    simp only [hzero, mass, Finset.card_empty, Nat.cast_zero, mul_zero] at hδ
    linarith
  have hcap := force_cap_bound hg hd hES hE hbE
  have hm0 := mass_nonneg hg.le S
  have hV := cost_nonneg hg.le hd
  have hD : 0 ≤ (1 - mass g S) * (b - b') :=
    mul_nonneg (sub_nonneg.mpr hy) (sub_nonneg.mpr hb)
  have hs0 := (savingsFraction_pos hg).le
  have hs1 : savingsFraction g ≤ 1 := min_le_left _ _
  have hs2 : savingsFraction g * (1 + 1 / g) ≤ 2 * P 1 * g :=
    (le_div_iff₀ (by positivity : 0 < (1:ℝ) + 1 / g)).mp (min_le_right _ _)
  have hB : 2 * P 1 ≤ B x := by
    exact mul_le_mul_of_nonneg_left (P_antitone hx) (by norm_num)
  have hVB := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hB hg.le) hV
  have hsmall : (1 - mass g S) * b' ≤ b' :=
    mul_le_of_le_one_left hb' (by linarith)
  have hQ : cost g d S + (1 - mass g S) * b ≤
      (1 + 1 / g) * cost g d S + (1 - mass g S) * (b - b') := by
    have hvdiv : cost g d S / g = (1 / g) * cost g d S := by ring
    rw [hvdiv] at hcap
    nlinarith only [hsmall, hcap]
  have hsQ := mul_le_mul_of_nonneg_left hQ hs0
  have hsV := mul_le_mul_of_nonneg_right hs2 hV
  have hsD := mul_le_mul_of_nonneg_right hs1 hD
  have hsavings := force_savings (x := x) (b := b) hg.le hd hES hδ hbE
  nlinarith only [hsQ, hsV, hsD, hVB, hsavings]

end MetricKMedian.PhysicalPotential
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_FixedBatchTransition
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic

variable {I E : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]

 theorem mem_relevant (D : Actions I E) (S : Finset I) (e : E) :
    e ∈ relevant D S ↔ (e ∈ D.ordinary ∧ D.source e ∈ S) ∨ (S ∩ D.erase e).Nonempty := by
  simp only [relevant, mem_filter, mem_univ, true_and]

omit [Fintype E] in
 theorem nextCap_nonneg (D : Actions I E) (d : I → ℝ) {bForce : ℝ} (A : Finset E)
    (hb : 0 ≤ bForce) (hd : ∀ e ∈ A ∩ D.ordinary, 0 ≤ d (D.source e)) :
    0 ≤ nextCap D d bForce A := (le_fold_min _).mpr ⟨hb, hd⟩

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_PotentialBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.PhysicalPotential
open Analytic Finset

variable {I : Type*}

theorem B_le_one {x : ℝ} (hx : 0 ≤ x) : B x ≤ 1 := by
  have h := P_le_half_s53 hx
  unfold B
  linarith only [h]

theorem m_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : m x ≤ 1 := by
  have hA := A_le_two hx1
  have hBx := mul_nonneg (B_nonneg x) hx0
  unfold m
  unfold B at hBx
  linarith only [hA, hBx]

theorem coefficient_bounds {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : 1 ≤ coefficient x y ∧ coefficient x y ≤ 3 := by
  refine ⟨coefficient_ge_one hy0, ?_⟩
  rw [coefficient_eq]
  have hm := m_le_one hx0 hx1
  have hB := (mul_le_of_le_one_left hy0 (B_le_one hx0)).trans hy1
  linarith only [hm, hB]

theorem cost_le_mass_mul {g R : ℝ} {d : I → ℝ} {S : Finset I}
    (hg : 0 ≤ g) (hd : ∀ i ∈ S, d i ≤ R) : cost g d S ≤ mass g S*R := by
  have h := sum_le_sum (fun i (hi : i ∈ S) => mul_le_mul_of_nonneg_left (hd i hi) hg)
  simpa only [cost, mass, sum_const, nsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using h

theorem cost_le_radius {g R : ℝ} {d : I → ℝ} {S : Finset I}
    (hg : 0 ≤ g) (hR : 0 ≤ R) (hd : ∀ i ∈ S, d i ≤ R) (hy : mass g S ≤ 1) :
    cost g d S ≤ R := by
  exact (cost_le_mass_mul hg hd).trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hy hR)

theorem potential_bounds {x g R b : ℝ} {d : I → ℝ} {S : Finset I}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg : 0 ≤ g) (hR : 0 ≤ R)
    (hd0 : ∀ i ∈ S, 0 ≤ d i) (hdR : ∀ i ∈ S, d i ≤ R)
    (hy : mass g S ≤ 1) (hb0 : 0 ≤ b) (hbR : b ≤ 5*R) :
    0 ≤ potential x g d S b ∧ potential x g d S b ≤ 8*R := by
  have hy0 := mass_nonneg hg S
  have hV0 := cost_nonneg hg hd0
  have hVR := cost_le_radius hg hR hdR hy
  have ha := coefficient_bounds hx0 hx1 hy0 hy
  have hcap0 := mul_nonneg (sub_nonneg.mpr hy) hb0
  have hcap := mul_le_mul_of_nonneg_right (show 1-mass g S ≤ 1 by linarith only [hy0]) hb0
  have hc := mul_le_mul ha.2 hVR hV0 (by norm_num : (0:ℝ) ≤ 3)
  rw [potential, ← coefficient_eq]
  constructor
  · exact add_nonneg (mul_nonneg (by linarith only [ha.1]) hV0) hcap0
  · nlinarith only [hc, hcap, hbR]

theorem internal_charge_bound {x g R b dh : ℝ} {d : I → ℝ} {S T : Finset I}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg : 0 ≤ g) (hR : 0 ≤ R)
    (hd0 : ∀ i ∈ S, 0 ≤ d i) (hdR : ∀ i ∈ S, d i ≤ R)
    (hy : mass g S ≤ 1) (hb0 : 0 ≤ b) (hbR : b ≤ 5*R)
    (hTS : T ⊆ S) (hdh0 : 0 ≤ dh) (hdhR : dh ≤ R) :
    |dh-(∑ i ∈ T, g*max (dh-coefficient x (mass g S)*d i) 0)-potential x g d S b| ≤ 8*R := by
  have hf := potential_bounds hx0 hx1 hg hR hd0 hdR hy hb0 hbR
  have ha := (coefficient_bounds hx0 hx1 (mass_nonneg hg S) hy).1
  have hhinge0 : 0 ≤ ∑ i ∈ T, g*max (dh-coefficient x (mass g S)*d i) 0 :=
    sum_nonneg (fun _ _ => mul_nonneg hg (le_max_right _ _))
  have hhinge : (∑ i ∈ T, g*max (dh-coefficient x (mass g S)*d i) 0) ≤ dh := by
    calc
      _ ≤ ∑ _i ∈ T, g*dh := by
        apply sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_left _ hg
        apply max_le _ hdh0
        have hmul := mul_nonneg (show 0 ≤ coefficient x (mass g S) by linarith only [ha]) (hd0 i (hTS hi))
        linarith only [hmul]
      _ = mass g T*dh := by simp only [mass, sum_const, nsmul_eq_mul]; ring
      _ ≤ dh := mul_le_of_le_one_left hdh0 ((mass_mono hg hTS).trans hy)
  exact abs_le.mpr ⟨by linarith only [hf.2, hhinge], by linarith only [hf.1, hhinge0, hdhR, hR]⟩

theorem external_charge_bound {x y R δ Y V b : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hR : 0 ≤ R) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hY0 : 0 ≤ Y) (hYV : Y ≤ V) (hVR : V ≤ R)
    (hb0 : 0 ≤ b) (hbR : b ≤ 5*R) :
    |δ*b-coefficient x y*Y-B x*δ*(V-Y)| ≤ 8*R := by
  have ha := coefficient_bounds hx0 hx1 hy0 hy1
  have ha0 : 0 ≤ coefficient x y := by linarith only [ha.1]
  have hB0 := B_nonneg x
  have hB1 := B_le_one hx0
  have hδb0 := mul_nonneg hδ0 hb0
  have hδbR : δ*b ≤ 5*R := (mul_le_of_le_one_left hb0 hδ1).trans hbR
  have haY0 := mul_nonneg ha0 hY0
  have haYR := mul_le_mul ha.2 (hYV.trans hVR) hY0 (by norm_num : (0:ℝ) ≤ 3)
  have hBY0 := mul_nonneg (mul_nonneg hB0 hδ0) (sub_nonneg.mpr hYV)
  have hBYR : B x*δ*(V-Y) ≤ R := by
    have hm : B x*δ ≤ 1 := (mul_le_of_le_one_left hδ0 hB1).trans hδ1
    have h := mul_le_mul_of_nonneg_right hm (sub_nonneg.mpr hYV)
    nlinarith only [h, hY0, hVR]
  exact abs_le.mpr ⟨by linarith only [hδb0, haYR, hBYR, hR],
    by linarith only [hδbR, haY0, hBY0, hR]⟩

end MetricKMedian.PhysicalPotential
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_TimeAdvance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Analytic
open Set

theorem abs_timeRate {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : |timeRate x y| ≤ 2 := by
  have hdiff : |y-x| ≤ 1 := abs_le.mpr ⟨by linarith only [hy0, hx1], by linarith only [hy1, hx0]⟩
  have hm0 := moment_nonneg 2 x
  have hm1 := moment_le_one 2 hx0
  rw [timeRate, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
    abs_of_nonneg hx0, abs_of_nonneg hm0]
  have hprod : x*|y-x| ≤ 1 := (mul_le_of_le_one_left (abs_nonneg _) hx1).trans hdiff
  have h := mul_le_mul hprod hm1 hm0 (by norm_num : (0:ℝ) ≤ 1)
  nlinarith only [h]

end MetricKMedian.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_FrozenBatchBound
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic
variable {I E : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]

omit [Fintype E] in
 theorem charge_bound (D : Actions I E) {x g R b : ℝ} (d : I → ℝ) (S : Finset I)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg : 0 ≤ g) (hR : 0 ≤ R)
    (hd0 : ∀ i, 0 ≤ d i) (hdR : ∀ i ∈ S, d i ≤ R)
    (hy : mass g S ≤ 1) (hb0 : 0 ≤ b) (hbR : b ≤ 5*R) (e : E) :
    |charge D x g b d S e| ≤ 8*R := by
  unfold charge
  split_ifs with he
  · exact internal_charge_bound hx0 hx1 hg hR (fun i _ => hd0 i) hdR hy hb0 hbR
      sdiff_subset (hd0 _) (hdR _ he.2)
  · apply external_charge_bound hx0 hx1 (mass_nonneg hg S) hy hR
      (mass_nonneg hg _) ((mass_mono hg inter_subset_left).trans hy)
      (cost_nonneg hg (fun i _ => hd0 i)) (cost_mono hg (fun i _ => hd0 i) inter_subset_left)
      (cost_le_radius hg hR hdR hy) (le_min hb0 (hd0 _))
      ((min_le_left _ _).trans hbR)

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_LocalForceScale
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.PhysicalPotential
open Finset Analytic
variable {I : Type*} [DecidableEq I]

omit [DecidableEq I] in
 theorem local_point_scale {g b : ℝ} {d : I → ℝ} {S : Finset I}
    (hg : 0 < g) (hd : ∀ i ∈ S, 0 ≤ d i) (hb : 0 ≤ b) (hy : mass g S ≤ 1) :
    ∀ i ∈ S, d i ≤ (cost g d S+(1-mass g S)*b)/g := by
  intro i hi
  apply (le_div_iff₀ hg).mpr
  have hp := point_cost_le hg.le hd hi
  have hmiss := mul_nonneg (sub_nonneg.mpr hy) hb
  nlinarith only [hp, hmiss]

end MetricKMedian.PhysicalPotential

namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic
variable {I E : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]

 theorem relevant_mono (D : Actions I E) {S T : Finset I} (hS : S ⊆ T) :
    relevant D S ⊆ relevant D T := by
  intro e he
  rw [mem_relevant] at he ⊢
  rcases he with he | ⟨i, hi⟩
  · exact Or.inl ⟨he.1, hS he.2⟩
  · exact Or.inr ⟨i, mem_inter.mpr ⟨hS (mem_inter.mp hi).1, (mem_inter.mp hi).2⟩⟩

theorem ideal_local_lower (D : Actions I E) {x g b Q : ℝ}
    (d : I → ℝ) (S : Finset I)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg : 0 < g) (hQ : 0 ≤ Q)
    (hd0 : ∀ i, 0 ≤ d i) (hdQ : ∀ i ∈ S, d i ≤ Q/g)
    (hy : mass g S ≤ 1) (hVQ : PhysicalPotential.cost g d S ≤ Q)
    (hb0 : 0 ≤ b) (hbQ : b ≤ 5*(Q/g)) :
    -(8*((relevant D S).card:ℝ)+2)*Q ≤
      timeRate x (mass g S)*PhysicalPotential.cost g d S+
        g*(∑ e ∈ relevant D S, charge D x g b d S e) := by
  have hc : ∀ e ∈ relevant D S, -(8*(Q/g)) ≤ charge D x g b d S e := by
    intro e _
    exact (abs_le.mp (charge_bound D d S hx0 hx1 hg.le (div_nonneg hQ hg.le)
      hd0 hdQ hy hb0 hbQ e)).1
  have hs := sum_le_sum hc
  simp only [sum_const, nsmul_eq_mul] at hs
  have hg' := mul_le_mul_of_nonneg_left hs hg.le
  have he : g*(((relevant D S).card:ℝ)* -(8*(Q/g)))=
      -(8*((relevant D S).card:ℝ)*Q) := by field_simp
  rw [he] at hg'
  have hr := (abs_le.mp (abs_timeRate hx0 hx1 (mass_nonneg hg.le S) hy)).1
  have hV0 : 0 ≤ PhysicalPotential.cost g d S := cost_nonneg hg.le (fun i _ => hd0 i)
  have ht := mul_le_mul_of_nonneg_right hr hV0
  nlinarith only [hg', ht, hVQ]

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_ForcedLocal
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic
variable {I E H : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]
  [DecidableEq H] [Fintype H]

theorem forced_step_local_bound_s53_oai (D : Actions I E) (Full : Actions I H)
    (μ : FiniteLaw (Finset E)) {x g h b b' : ℝ} {N : ℕ}
    (d : I → ℝ) (S F : Finset I)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg0 : 0 < g) (hg1 : g ≤ 1)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hsmall : (16*(N:ℝ)+10)*h ≤ savingsFraction g)
    (hy : mass g S ≤ 1) (hF : F ⊆ S) (hδ : g ≤ mass g F)
    (hd0 : ∀ i, 0 ≤ d i) (hb0 : 0 ≤ b)
    (hbQ : b ≤ 5*((PhysicalPotential.cost g d S+(1-mass g S)*b)/g))
    (hb'0 : 0 ≤ b') (hb' : b' ≤ b) (hbF : ∀ i ∈ F, b' ≤ d i)
    (hD : (relevant D S).card ≤ N) (hFull : (relevant Full S).card ≤ N)
    (hmarg : ∀ e ∈ relevant D S, μ.prob (fun A => e ∈ A) ≤ 2*h*g) :
    μ.expect (fun A => potential (x*Real.exp (-h)) g d
      (nextAliveAt D (coefficient x (mass g S)) d (S \ F) A)
      (nextCap D d b' A)-potential x g d S b) ≤
      h*(timeRate x (mass g S)*PhysicalPotential.cost g d S+
        g*(∑ e ∈ relevant Full S, charge Full x g b d S e)) := by
  let V := PhysicalPotential.cost g d S
  let Q := V+(1-mass g S)*b
  have hV : 0 ≤ V := cost_nonneg hg0.le (fun i _ => hd0 i)
  have hVQ : V ≤ Q := le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hy) hb0)
  have hQ : 0 ≤ Q := hV.trans hVQ
  have hFne : F.Nonempty := by
    by_contra hne
    have he : F=∅ := not_nonempty_iff_eq_empty.mp hne
    simp only [he, mass, card_empty, Nat.cast_zero, mul_zero] at hδ
    exact not_lt_of_ge hδ hg0
  have hcap := force_cap_bound hg0 (fun i _ => hd0 i) hF hFne hbF
  have hsaving := force_fraction hx1 hg0 (fun i _ => hd0 i) hF hδ hy hb'0 hb' hbF
  change savingsFraction g*Q ≤ potential x g d S b-potential x g d (S \ F) b' at hsaving
  have hpost := post_force_bound_s53 D μ (coefficient x (mass g S)) d (S \ F)
    hx0 hx1 hg0 hg1 hh0 hh1 hV (fun i _ => hd0 i)
    ((mass_mono hg0.le sdiff_subset).trans hy)
    (cost_mono hg0.le (fun i _ => hd0 i) sdiff_subset) hb'0 hcap
    (fun A => nextCap_nonneg D d A hb'0 (fun e _ => hd0 _))
    (fun e he => hmarg e (relevant_mono D sdiff_subset he))
  have hcard : ((relevant D (S \ F)).card:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast (card_le_card (relevant_mono D sdiff_subset)).trans hD
  have hpostM : (8*((relevant D (S \ F)).card:ℝ)+8)*h*V ≤ (8*(N:ℝ)+8)*h*Q := by
    have hc := mul_le_mul_of_nonneg_right (show 8*((relevant D (S \ F)).card:ℝ)+8 ≤ 8*(N:ℝ)+8 by
      linarith only [hcard]) hh0
    exact mul_le_mul hc hVQ hV (by positivity)
  have hpoint : ∀ i ∈ S, d i ≤ Q/g := local_point_scale hg0 (fun i _ => hd0 i) hb0 hy
  have hJ := ideal_local_lower Full d S hx0 hx1 hg0 hQ hd0 hpoint hy hVQ hb0 hbQ
  have hfcard : ((relevant Full S).card:ℝ) ≤ (N:ℝ) := by exact_mod_cast hFull
  have hJM : -(8*(N:ℝ)+2)*Q ≤
      timeRate x (mass g S)*V+g*(∑ e ∈ relevant Full S, charge Full x g b d S e) := by
    apply le_trans _ hJ
    exact mul_le_mul_of_nonneg_right (by linarith only [hfcard]) hQ
  have htarget := mul_le_mul_of_nonneg_left hJM hh0
  have hsmallQ := mul_le_mul_of_nonneg_right hsmall hQ
  rw [μ.expect_sub, μ.expect_const] at hpost ⊢
  change μ.expect _-potential x g d S b ≤
    h*(timeRate x (mass g S)*V+g*(∑ e ∈ relevant Full S, charge Full x g b d S e))
  nlinarith only [hpost, hpostM, hsaving, htarget, hsmallQ]

end MetricKMedian.FixedBatch
end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.MetricKMedian.FixedBatch.forced_step_local_bound_s53_oai.{u_1, u_2, u_3} := @OAI.MetricKMedian.FixedBatch.forced_step_local_bound_s53_oai.{u_1, u_2, u_3}
