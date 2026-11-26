-- Prove2me | solution 1 for MasulloRH.theta_disk_of_rational_exponential_certificates
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T09:58:03.817959+00:00
-- url     : https://prove2.me/submissions/133e869f-290d-4d02-9c43-e8d591cd173f

import Theorems.Thm_MasulloRH_HeightTwoScalar_exp_row_sound
import Theorems.Thm_MasulloRH_theta_value_enclosure_of_gaussian_parameter
import Theorems.Thm_MasulloRH_theta_reflection
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MasulloRH.GaussianApproximation MasulloRH.HeightTwoScalar
open scoped BigOperators

theorem solution (K : ℕ) (iL iU qL qU : ExpRow) (d C R : ℚ)
    (hrows : iL.Valid ∧ iU.Valid ∧ qL.Valid ∧ qU.Valid)
    (hd : 0 < d) (hi : 0 ≤ iL.lower)
    (ha : qL.argument*d ≤ -piUpperQ*iU.upper ∧
          -piLowerQ*iL.lower ≤ qU.argument*d)
    (hq : 0 ≤ qL.lower ∧ qU.upper < 1)
    (hwin : let B (a b : ℚ) := 2 * ∑ n ∈ Finset.range K,
               (a^((n+1)^2) - 3*b^(4*(n+1)^2) + 2*a^(16*(n+1)^2))
            let E := 12*qU.upper^((K+1)^2)/(1-qU.upper^(2*K+3))
            C-R ≤ B qL.lower qU.upper-E ∧ B qU.upper qL.lower+E ≤ C+R)
    (z w : ℝ) (hw : (iL.argument : ℝ) ≤ w ∧ w ≤ (iU.argument : ℝ))
    (hz : (Real.exp z)^2 * (d:ℝ) = Real.exp w) :
    ‖theta z - (C : ℂ)‖ ≤ (R : ℝ) := by
  rcases hrows with ⟨hil,hiu,hql,hqu⟩
  have il := (MasulloRH.HeightTwoScalar.exp_row_sound iL hil).1.trans (Real.exp_le_exp.mpr hw.1)
  have iu := (Real.exp_le_exp.mpr hw.2).trans (MasulloRH.HeightTwoScalar.exp_row_sound iU hiu).2
  have pp : (piLowerQ : ℝ) ≤ Real.pi := le_trans (by norm_num [piLowerQ]) Real.pi_gt_d20.le
  have pp' : Real.pi ≤ (piUpperQ : ℝ) := Real.pi_lt_d20.le.trans (by norm_num [piUpperQ])
  have lo := mul_le_mul pp il (Rat.cast_nonneg.mpr hi) Real.pi_pos.le
  have up := mul_le_mul pp' iu (Real.exp_pos _).le (Real.pi_pos.le.trans pp')
  have hlo : (qL.argument:ℝ)*(d:ℝ) ≤ -(piUpperQ:ℝ)*(iU.upper:ℝ) := by exact_mod_cast ha.1
  have hup : -(piLowerQ:ℝ)*(iL.lower:ℝ) ≤ (qU.argument:ℝ)*(d:ℝ) := by exact_mod_cast ha.2
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  have ll : (qL.argument:ℝ) ≤ -Real.pi*(Real.exp z)^2 := by
    apply le_of_mul_le_mul_right (a := (d:ℝ)) _ hd'
    rw [mul_assoc,hz]
    linarith
  have uu : -Real.pi*(Real.exp z)^2 ≤ (qU.argument:ℝ) := by
    apply le_of_mul_le_mul_right (a := (d:ℝ)) _ hd'
    rw [mul_assoc,hz]
    linarith
  have thetaBounds := MasulloRH.theta_value_enclosure_of_gaussian_parameter K z
    (qL.lower:ℝ) (qU.upper:ℝ) (Rat.cast_nonneg.mpr hq.1)
    ((MasulloRH.HeightTwoScalar.exp_row_sound qL hql).1.trans (Real.exp_le_exp.mpr ll))
    ((Real.exp_le_exp.mpr uu).trans (MasulloRH.HeightTwoScalar.exp_row_sound qU hqu).2)
    (by exact_mod_cast hq.2)
  obtain ⟨him,hl,hu⟩ := thetaBounds
  obtain ⟨ha,hb⟩ := hwin
  dsimp only at ha hb
  have hla := (Rat.cast_le (K := ℝ)).mpr ha
  have hua := (Rat.cast_le (K := ℝ)).mpr hb
  push_cast at hla hua
  have low : (C:ℝ)-(R:ℝ) ≤ (theta z).re := hla.trans hl
  have high : (theta z).re ≤ (C:ℝ)+(R:ℝ) := hu.trans hua
  have ht : theta z = (((theta z).re : ℝ) : ℂ) := Complex.ext rfl (by simpa using him)
  have hc : (C : ℂ) = ((C:ℝ):ℂ) := by norm_cast
  calc ‖theta z - (C : ℂ)‖ = ‖(((theta z).re-(C:ℝ):ℝ):ℂ)‖ := by
         conv_lhs => rw [ht,hc,← Complex.ofReal_sub]
       _ = |(theta z).re-(C:ℝ)| := by rw [Complex.norm_real,Real.norm_eq_abs]
       _ ≤ _ := abs_le.mpr ⟨by linarith,by linarith⟩

namespace MasulloGridExamples

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private def directIL : ExpRow :=
  ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩

private def directIU : ExpRow :=
  ⟨1, 1/512, 525313/524288, 268960257/268435456, 1/512, 525313/524288, 268960257/268435456, 1, 9, 0⟩

private def directQL : ExpRow :=
  ⟨2, -52810223/16777216, 5764559/134217728, 360285/8388608, 52810223/218103808, 341977151/268435456, 5343393/4194304, 13, 9, 0⟩

private def directQU : ExpRow :=
  ⟨2, -105414357/33554432, 11600147/268435456, 11600149/268435456, 105414357/436207616, 85453905/67108864, 341815621/268435456, 13, 9, 0⟩

private theorem directBlock (x : ℝ) (hx : (0:ℝ) ≤ x ∧ x ≤ (1/1024:ℝ)) :
    ‖theta x - ((23125567/268435456:ℚ):ℂ)‖ ≤ ((71123/268435456:ℚ):ℝ) := by
  have h := solution 3 directIL directIU directQL directQU 1 (23125567/268435456) (71123/268435456)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) x (2*x) (by
      constructor <;> norm_num [directIL,directIU] <;> linarith [hx.1,hx.2]) (by
      norm_num
      simpa using (Real.exp_nat_mul x 2).symm)
  exact h

private def reflectedIL : ExpRow :=
  ⟨1, 1279/512, 3263832333/268435456, 3263832429/268435456, 1279/5120, 172305317/134217728, 344610635/268435456, 10, 9, 0⟩

private def reflectedIU : ExpRow :=
  ⟨1, 5/2, 1635106649/134217728, 1635106697/134217728, 1/4, 86169487/67108864, 344677949/268435456, 10, 9, 0⟩

private def reflectedQL : ExpRow :=
  ⟨2, -642104899/268435456, 24546845/268435456, 12273423/134217728, 642104899/2684354560, 340976381/268435456, 170488191/134217728, 10, 9, 0⟩

private def reflectedQU : ExpRow :=
  ⟨2, -640851979/268435456, 6165421/67108864, 12330843/134217728, 640851979/2684354560, 85204317/67108864, 340817269/268435456, 10, 9, 0⟩

private def reflectedPL : ExpRow :=
  ⟨1, 1279/1024, 936017265/268435456, 936017279/268435456, 1279/5120, 172305317/134217728, 344610635/268435456, 5, 9, 0⟩

private def reflectedPU : ExpRow :=
  ⟨1, 5/4, 117116475/33554432, 468465907/134217728, 1/4, 86169487/67108864, 344677949/268435456, 5, 9, 0⟩

private theorem reflectedBlock (x : ℝ) (hx : (-5/4:ℝ) ≤ x ∧ x ≤ (-1279/1024:ℝ)) :
    ‖theta x - ((85703313/268435456:ℚ):ℂ)‖ ≤ ((244639/268435456:ℚ):ℝ) := by
  have h := solution 3 reflectedIL reflectedIU reflectedQL reflectedQU 16 (49132743/268435456) (116257/268435456)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (-x - Real.log 4) (-2*x) (by
      constructor <;> norm_num [reflectedIL,reflectedIU] <;> linarith [hx.1,hx.2]) (by
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0:ℝ)<4), show -2*x = 2*(-x) by ring, show Real.exp (2*(-x)) = (Real.exp (-x))^2 by simpa using Real.exp_nat_mul (-x) 2]
      norm_num
      ring)
  have pl := (MasulloRH.HeightTwoScalar.exp_row_sound reflectedPL (by decide +kernel)).1
  have pu := (MasulloRH.HeightTwoScalar.exp_row_sound reflectedPU (by decide +kernel)).2
  norm_num [reflectedPL] at pl
  norm_num [reflectedPU] at pu
  have pfL : (936017265/268435456:ℝ) ≤ Real.exp (-x) := pl.trans (Real.exp_le_exp.mpr (by linarith [hx.2]))
  have pfU : Real.exp (-x) ≤ (468465907/134217728:ℝ) := (Real.exp_le_exp.mpr (by linarith [hx.1])).trans pu
  have him : (theta (-x-Real.log 4)).im = 0 := by
    apply Complex.conj_eq_iff_im.mp
    simp only [theta, Complex.conj_tsum, Complex.conj_ofReal]
  have hrc := (Complex.abs_re_le_norm _).trans h
  rw [Complex.sub_re,Complex.ratCast_re] at hrc
  obtain ⟨hl,hu⟩ := abs_le.mp hrc
  have hs : (49132743/268435456:ℝ)-(116257/268435456:ℝ) ≤ (theta (-x-Real.log 4)).re := by norm_num at hl ⊢; linarith
  have ht : (theta (-x-Real.log 4)).re ≤ (49132743/268435456:ℝ)+(116257/268435456:ℝ) := by norm_num at hu ⊢; linarith
  have prodL := mul_le_mul pfL hs (by norm_num : (0:ℝ) ≤ (49132743/268435456:ℝ)-(116257/268435456:ℝ)) (Real.exp_pos _).le
  have prodU := mul_le_mul pfU ht (by linarith [hs] : 0 ≤ (theta (-x-Real.log 4)).re) (by norm_num)
  have hr : theta (-x-Real.log 4) = (((theta (-x-Real.log 4)).re:ℝ):ℂ) := Complex.ext rfl (by simpa using him)
  rw [MasulloRH.theta_reflection x,hr]
  rw [show ((85703313/268435456:ℚ):ℂ) = ((85703313/268435456:ℝ):ℂ) by norm_num]
  rw [← Complex.ofReal_mul,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  apply abs_le.mpr
  norm_num at prodL prodU ⊢
  constructor <;> linarith

end MasulloGridExamples
