-- Prove2me | solution 1 for OAI.SevenEighths.ProbeEuler.unramifiedSelected_central_quotient
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T23:00:42.97361+00:00
-- url     : https://prove2.me/submissions/9c955eb9-31e7-4362-ba53-7bf9e89fdb6b

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B008

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.Euler
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

theorem unramified_marked_error (R V qInv K W D : ℂ)
    (hR : 1 - R ≠ 0) (hV : 1 - V ≠ 0) :
    markedFactor R V qInv K (-D + W * R) 1 + D =
      (R * ((1 - qInv) + (1 - V) * (W - D)) - K * V) /
        ((1 - R) * (1 - V)) := by
  unfold markedFactor
  field_simp
  ring

end SevenEighths.ProbeEuler
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.Local
namespace OAI

namespace SevenEighths.ProbeLocal
noncomputable section

theorem continuedCorrection_defect (V W D Pstar : ℂ) (hD : 1 - D ≠ 0) :
    continuedCorrection V W D Pstar - 1 =
      (D * (V + W - V * W) - V * W +
        (1 - V) * (1 - W) * (Pstar + D)) / (1 - D) := by
  unfold continuedCorrection
  field_simp
  ring

theorem continued_normalized_cancellation (V W D Pstar B q vInv : ℂ)
    (hV : 1 - V ≠ 0) (hD : 1 - D ≠ 0)
    (hBD : B * D = vInv) (hvW : vInv * W = q) :
    compensatedReplacement V W D Pstar B q +
        continuedCorrection V W D Pstar * vInv =
      (1 - V) * (1 - W) / (1 - D) *
        ((vInv - q) * (V / (1 - V) - D) +
          (B + vInv - q) * (Pstar + D)) := by
  unfold compensatedReplacement continuedCorrection
  field_simp
  linear_combination -(1 - V) * (1 - W) * hBD + (1 - V) * hvW

end
end SevenEighths.ProbeLocal

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.CorrectionBounds
namespace OAI

noncomputable section
namespace SevenEighths.ProbeLocal

lemma one_sub_ne_zero_of_norm_le_half (a : ℂ) (ha : ‖a‖ ≤ 1/2) : 1 - a ≠ 0 := by
  intro h
  have : a = 1 := by linear_combination -h
  rw [this, norm_one] at ha
  norm_num at ha

lemma inv_one_sub_norm_le_two (a : ℂ) (ha : ‖a‖ ≤ 1/2) : ‖(1-a)⁻¹‖ ≤ 2 := by
  have hl := norm_sub_norm_le (1 : ℂ) a
  simp only [norm_one] at hl
  have hd : 0 < ‖1-a‖ := by linarith
  rw [norm_inv, ← one_div, div_le_iff₀ hd]
  linarith

theorem unramified_marked_error_bound (R V qInv K W D : ℂ)
    (hR : ‖R‖ ≤ 1/2) (hV : ‖V‖ ≤ 1/2) (hq : ‖qInv‖ ≤ 1) (hD : ‖D‖ ≤ 1/2) :
    ‖ProbeEuler.markedFactor R V qInv K (-D + W*R) 1 + D‖ ≤
      12 * ‖R‖ * (1 + ‖W‖) + 4 * ‖K‖ * ‖V‖ := by
  rw [ProbeEuler.unramified_marked_error R V qInv K W D
    (one_sub_ne_zero_of_norm_le_half R hR) (one_sub_ne_zero_of_norm_le_half V hV),
    div_eq_mul_inv, mul_inv, norm_mul, norm_mul]
  have hnum : ‖R*((1-qInv)+(1-V)*(W-D))-K*V‖ ≤
      ‖R‖ * (2 + (1 + ‖V‖) * (‖W‖ + ‖D‖)) + ‖K‖ * ‖V‖ := by
    calc
      _ ≤ ‖R*((1-qInv)+(1-V)*(W-D))‖ + ‖K*V‖ := norm_sub_le _ _
      _ = ‖R‖ * ‖(1-qInv)+(1-V)*(W-D)‖ + ‖K‖*‖V‖ := by rw [norm_mul, norm_mul]
      _ ≤ ‖R‖ * (‖1-qInv‖ + ‖1-V‖*‖W-D‖) + ‖K‖*‖V‖ := by
        gcongr
        simpa only [norm_mul] using norm_add_le (1-qInv) ((1-V)*(W-D))
      _ ≤ ‖R‖ * (2 + (1+‖V‖)*(‖W‖+‖D‖)) + ‖K‖*‖V‖ := by
        gcongr
        · calc ‖1-qInv‖ ≤ ‖(1:ℂ)‖+‖qInv‖ := norm_sub_le _ _
               _ ≤ 2 := by simp only [norm_one]; linarith
        · simpa only [norm_one] using norm_sub_le (1:ℂ) V
        · exact norm_sub_le W D
  have hv := inv_one_sub_norm_le_two V hV
  have hr := inv_one_sub_norm_le_two R hR
  calc
    _ ≤ (‖R‖ * (2 + (1 + ‖V‖) * (‖W‖ + ‖D‖)) + ‖K‖ * ‖V‖) * (2*2) := by
      gcongr
    _ ≤ 12 * ‖R‖ * (1+‖W‖) + 4*‖K‖*‖V‖ := by
      have he : 2 + (1+‖V‖)*(‖W‖+‖D‖) ≤ 3*(1+‖W‖) := by
        have : (1+‖V‖)*(‖W‖+‖D‖) ≤ (3/2:ℝ)*(‖W‖+1/2) := by gcongr ; linarith
        nlinarith [norm_nonneg W]
      nlinarith [mul_le_mul_of_nonneg_left he (norm_nonneg R)]

theorem continuedCorrection_defect_bound (V W D Pstar : ℂ)
    (hV : ‖V‖ ≤ 1/2) (hD : ‖D‖ ≤ 1/2) :
    ‖continuedCorrection V W D Pstar - 1‖ ≤
      2 * (‖D‖ * (‖V‖+‖W‖+‖V‖*‖W‖) + ‖V‖*‖W‖ +
        2*(1+‖W‖)*‖Pstar+D‖) := by
  rw [continuedCorrection_defect _ _ _ _ (one_sub_ne_zero_of_norm_le_half D hD),
    div_eq_mul_inv, norm_mul]
  have hA : ‖V+W-V*W‖ ≤ ‖V‖+‖W‖+‖V‖*‖W‖ := by
    calc
      _ ≤ ‖V+W‖+‖V*W‖ := norm_sub_le _ _
      _ ≤ _ := by rw [norm_mul]; gcongr; exact norm_add_le V W
  have hnum : ‖D*(V+W-V*W)-V*W+(1-V)*(1-W)*(Pstar+D)‖ ≤
      ‖D‖*(‖V‖+‖W‖+‖V‖*‖W‖)+‖V‖*‖W‖+2*(1+‖W‖)*‖Pstar+D‖ := by
    calc
      _ ≤ ‖D*(V+W-V*W)-V*W‖+‖(1-V)*(1-W)*(Pstar+D)‖ := norm_add_le _ _
      _ ≤ ‖D*(V+W-V*W)‖+‖V*W‖+‖(1-V)*(1-W)*(Pstar+D)‖ := by gcongr; exact norm_sub_le _ _
      _ = ‖D‖*‖V+W-V*W‖+‖V‖*‖W‖+‖1-V‖*‖1-W‖*‖Pstar+D‖ := by simp only [norm_mul]
      _ ≤ _ := by
        gcongr
        · calc ‖1-V‖ ≤ 1+‖V‖ := by simpa only [norm_one] using norm_sub_le (1:ℂ) V
               _ ≤ 2 := by linarith
        · simpa only [norm_one] using norm_sub_le (1:ℂ) W
  calc
    _ ≤ (‖D‖*(‖V‖+‖W‖+‖V‖*‖W‖)+‖V‖*‖W‖+2*(1+‖W‖)*‖Pstar+D‖)*2 := by
      gcongr
      exact inv_one_sub_norm_le_two D hD
    _ = _ := by ring

end SevenEighths.ProbeLocal
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.EulerCoordinates
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss
local notation "O" => ActualEisensteinCubic.O

lemma coordV_norm (Q : ℝ) (hQ : 0 < Q) (z : ℂ) :
    ‖coordV Q z‖ = Q ^ (-6*z.re) := by
  rw [coordV, Complex.norm_cpow_eq_rpow_re_of_pos hQ]
  simp

lemma coordR_norm_le (Q : ℝ) (hQ : 0 < Q) (A x z : ℂ) (hA : ‖A‖ ≤ 1) :
    ‖coordR Q A x z‖ ≤ Q ^ (4-6*x.re-6*z.re) := by
  rw [coordR, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hQ]
  simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
    zero_mul, sub_zero]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hQ.le _) hA

lemma coordW_norm_le (Q : ℝ) (hQ : 0 < Q) (v w : ℂ) (hv : ‖v‖ ≤ 1) :
    ‖coordW Q v w‖ ≤ Q ^ (-w.re) := by
  rw [coordW, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hQ, Complex.neg_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hQ.le _) hv

lemma coordD_norm_le (Q : ℝ) (hQ : 0 < Q) (eta v x : ℂ)
    (he : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖coordD Q eta v x‖ ≤ Q ^ (-x.re) := by
  rw [coordD, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hQ, Complex.neg_re]
  apply mul_le_of_le_one_left (Real.rpow_nonneg hQ.le _)
  rw [norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) he).trans hv

lemma coordK_norm_le (Q : ℝ) (hQ : 1 ≤ Q) (eta x w : ℂ) (he : ‖eta‖ ≤ 1) :
    ‖coordK Q eta x w‖ ≤ Q ^ (1-x.re-w.re) := by
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hsub : ‖(Q:ℂ)-1‖ = Q-1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hQ)]
  rw [coordK, norm_mul, norm_mul, hsub, Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
  have heq : (1-x.re-w.re) = 1 + (-x.re-w.re) := by ring
  rw [heq, Real.rpow_add hQ0, Real.rpow_one]
  simp only [Complex.sub_re, Complex.neg_re]
  gcongr
  calc ‖eta‖*(Q-1) ≤ 1*(Q-1) := mul_le_mul_of_nonneg_right he (sub_nonneg.mpr hQ)
       _ ≤ Q := by linarith

end SevenEighths.ProbeEuler
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.EulerRegion
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

lemma rpow_le_half (Q a : ℝ) (hQ : 4 ≤ Q) (ha : a ≤ -(1/2)) : Q^a ≤ 1/2 := by
  have hQ0 : 0 < Q := by linarith
  have hs : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ0
  have hs2 := Real.sq_sqrt hQ0.le
  calc
    Q^a ≤ Q^(-(1/2:ℝ)) := Real.rpow_le_rpow_of_exponent_le (by linarith) ha
    _ = (Real.sqrt Q)⁻¹ := by rw [Real.rpow_neg hQ0.le, ← Real.sqrt_eq_rpow]
    _ ≤ 1/2 := by rw [← one_div, div_le_iff₀ hs]; nlinarith [Real.sqrt_nonneg Q]

end SevenEighths.ProbeEuler
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrincipalSlotEstimate
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Complex

namespace SevenEighths.PrincipalSlotEstimate
open ProbeEuler ProbeLocal

theorem unit_phase_inverse (η : ℂ) (hη : ‖η‖ = 1) : star η * η = 1 := by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hη]
  norm_num

end SevenEighths.PrincipalSlotEstimate

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.HighRowsCentralCancellation
namespace OAI

noncomputable section
namespace SevenEighths.ProbeLocal

theorem central_phase_error_bound (V W D P B q vInv : ℂ) (A T : ℝ)
    (hA : 1≤A) (hV : ‖V‖≤1/2) (hD : ‖D‖≤1/2)
    (hW : ‖W‖≤A) (hq : ‖q‖≤A) (hv : ‖vInv‖≤1)
    (hVT : A^2*‖V‖≤T) (hDT : A^2*‖D‖≤T)
    (hET : A^2*‖P+D‖≤28*T) (hBET : A*‖B‖*‖P+D‖≤28*T)
    (hBD : B*D=vInv) (hWq : vInv*W=q) :
    ‖compensatedReplacement V W D P B q+continuedCorrection V W D P*vInv‖≤720*T := by
  have hA0 : 0≤A := by linarith
  have hT : 0≤T := (mul_nonneg (sq_nonneg A) (norm_nonneg V)).trans hVT
  have h1V : ‖1-V‖≤2 := by
    have hh := norm_sub_le (1:ℂ) V
    rw [norm_one] at hh
    linarith
  have h1W : ‖1-W‖≤2*A := by
    have hh := norm_sub_le (1:ℂ) W
    rw [norm_one] at hh
    linarith
  have hdiff : ‖vInv-q‖≤2*A := (norm_sub_le vInv q).trans (by linarith)
  have hfac : ‖(1-V)*(1-W)/(1-D)‖≤8*A := by
    rw [div_eq_mul_inv,norm_mul,norm_mul]
    have hi := inv_one_sub_norm_le_two D hD
    calc
      _ ≤ 2*(2*A)*2 := by gcongr
      _ = _ := by ring
  have hleft : ‖(vInv-q)*(V/(1-V)-D)‖≤2*A*(2*‖V‖+‖D‖) := by
    rw [norm_mul]
    apply mul_le_mul hdiff _ (norm_nonneg _) (by positivity)
    calc
      _ ≤ ‖V/(1-V)‖+‖D‖ := norm_sub_le _ _
      _ ≤ _ := by
        rw [div_eq_mul_inv,norm_mul]
        have hi := inv_one_sub_norm_le_two V hV
        nlinarith [mul_le_mul_of_nonneg_left hi (norm_nonneg V)]
  have hright : ‖(B+vInv-q)*(P+D)‖≤(‖B‖+2*A)*‖P+D‖ := by
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      _ = ‖B+(vInv-q)‖ := by congr 1;ring
      _ ≤ ‖B‖+‖vInv-q‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  rw [continued_normalized_cancellation V W D P B q vInv
    (one_sub_ne_zero_of_norm_le_half V hV) (one_sub_ne_zero_of_norm_le_half D hD) hBD hWq,norm_mul]
  calc
    _ ≤ (8*A)*(2*A*(2*‖V‖+‖D‖)+(‖B‖+2*A)*‖P+D‖) := by
      apply mul_le_mul hfac _ (norm_nonneg _) (by positivity)
      exact (norm_add_le _ _).trans (add_le_add hleft hright)
    _ = 32*(A^2*‖V‖)+16*(A^2*‖D‖)+8*(A*‖B‖*‖P+D‖)+16*(A^2*‖P+D‖) := by ring
    _ ≤ 720*T := by linarith

end SevenEighths.ProbeLocal
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.HighRowsFirstRegion
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

theorem unramifiedClosed_first_region_bound (Q : ℝ) (A eta v x w z : ℂ) (eps : ℝ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (heta : ‖eta‖≤1) (hv : ‖v‖≤1)
    (heps : 0<eps) (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    ‖unramifiedClosed Q A eta v x w z-1‖≤240*Q^(-1-min eps (1/50:ℝ)) := by
  have hQ0 : 0<Q := by linarith
  have hQ1 : 1≤Q := by linarith
  let V := coordV Q z
  let R := coordR Q A x z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  let L := Q^(1/100:ℝ)
  let E := Q^(-(109/100:ℝ))
  let T := Q^(-1-min eps (1/50:ℝ))
  have hL1 : 1≤L := Real.one_le_rpow hQ1 (by norm_num)
  have hT : 0≤T := Real.rpow_nonneg hQ0.le _
  have hV : ‖V‖≤Q^(-(51/25:ℝ)) := by
    rw [show V=coordV Q z from rfl,coordV_norm Q hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hR : ‖R‖≤Q^(-(11/10:ℝ)) :=
    (coordR_norm_le Q hQ0 A x z hA).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hW : ‖W‖≤L :=
    (coordW_norm_le Q hQ0 v w hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hD : ‖D‖≤Q^(-(51/100:ℝ)) :=
    (coordD_norm_le Q hQ0 eta v x heta hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hK : ‖K‖≤Q^(-eps) :=
    (coordK_norm_le Q hQ1 eta x w heta).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hVh : ‖V‖≤1/2 := hV.trans (rpow_le_half Q _ hQ (by norm_num))
  have hRh : ‖R‖≤1/2 := hR.trans (rpow_le_half Q _ hQ (by norm_num))
  have hDh : ‖D‖≤1/2 := hD.trans (rpow_le_half Q _ hQ (by norm_num))
  have hqi : ‖(Q:ℂ)⁻¹‖≤1 := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hQ0,←one_div]
    exact (div_le_one hQ0).mpr hQ1
  have hprod (a b aa bb c : ℝ) (ha : 0≤a) (hb : 0≤b)
      (haa : a≤Q^aa) (hbb : b≤Q^bb) (hc : aa+bb≤ c) : a*b≤Q^c := by
    calc
      a*b≤Q^aa*Q^bb := mul_le_mul haa hbb hb (Real.rpow_nonneg hQ0.le _)
      _=Q^(aa+bb) := (Real.rpow_add hQ0 _ _).symm
      _≤Q^c := Real.rpow_le_rpow_of_exponent_le hQ1 hc
  have hRL : ‖R‖*L≤E := hprod _ _ _ _ _ (norm_nonneg _) (by positivity) hR le_rfl (by norm_num)
  have hKV : ‖K‖*‖V‖≤E := hprod _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) hK hV (by linarith)
  have hRW : ‖R‖*(1+‖W‖)≤2*E := by
    calc
      _≤‖R‖*(2*L) := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
      _≤2*E := by nlinarith
  let P := markedFactor R V (Q:ℂ)⁻¹ K (-D+W*R) 1
  have hPE : ‖P+D‖≤28*E := by
    have hh := ProbeLocal.unramified_marked_error_bound R V (Q:ℂ)⁻¹ K W D hRh hVh hqi hDh
    dsimp only [P]
    nlinarith
  have hEL : E*L≤T := hprod _ _ _ _ _ (by positivity) (by positivity) le_rfl le_rfl
    (by have := min_le_right eps (1/50:ℝ);linarith)
  have hWE : (1+‖W‖)*‖P+D‖≤56*T := by
    calc
      _≤(2*L)*(28*E) := mul_le_mul (by linarith) hPE (norm_nonneg _) (by positivity)
      _≤56*T := by nlinarith
  have hDV : ‖D‖*‖V‖≤T := hprod _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hV
    (by have := min_le_right eps (1/50:ℝ);linarith)
  have hVW : ‖V‖*‖W‖≤T := hprod _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) hV hW
    (by have := min_le_right eps (1/50:ℝ);linarith)
  have hDW : ‖D‖*‖W‖≤T := hprod _ _ _ _ _ (norm_nonneg _) (norm_nonneg _)
    (coordD_norm_le Q hQ0 eta v x heta hv) (coordW_norm_le Q hQ0 v w hv)
    (by have := min_le_left eps (1/50:ℝ);linarith)
  have hDVW : ‖D‖*‖V‖*‖W‖≤T := by
    calc
      _ = (‖D‖*‖W‖)*‖V‖ := by ring
      _ ≤ ‖D‖*‖W‖ := mul_le_of_le_one_right (by positivity) (by linarith)
      _ ≤ T := hDW
  have hh := ProbeLocal.continuedCorrection_defect_bound V W D P hVh hDh
  change ‖ProbeLocal.continuedCorrection V W D P-1‖≤240*T
  nlinarith

end SevenEighths.ProbeEuler
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedUnramified
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ProbeLocal

lemma selected_phase_identities (Q : ℝ) (eta v x w : ℂ)
    (hQ : 0<Q) (heta : ‖eta‖=1) (hv : ‖v‖=1) :
    (star eta*(Q:ℂ)^x)*coordD Q eta v x=star v ∧
      star v*coordW Q v w=(Q:ℂ)^(-w) := by
  have hQ0 : (Q:ℂ)≠0 := by exact_mod_cast hQ.ne'
  constructor
  · unfold coordD
    calc
      _=(star eta*eta)*((Q:ℂ)^x*(Q:ℂ)^(-x))*star v := by ring
      _=star v := by rw [PrincipalSlotEstimate.unit_phase_inverse eta heta,←Complex.cpow_add _ _ hQ0];simp
  · unfold coordW
    rw [←mul_assoc,PrincipalSlotEstimate.unit_phase_inverse v hv,one_mul]

end SevenEighths.ProbeEuler
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.HighRowsCentralError
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ProbeLocal

lemma central_unramified_error_weights (Q a e : ℝ) (A eta v x w z : ℂ)
    (hQ : 4≤Q) (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (he : 0<e) (he1 : e≤1/1000)
    (hA : ‖A‖≤1) (heta : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50) :
    let L := Q^(6*e)
    let E := unramifiedMarked Q A eta v x w z+coordD Q eta v x
    L^2*‖coordV Q z‖≤Q^(-(51/100:ℝ)) ∧
    L^2*‖coordD Q eta v x‖≤Q^(-(51/100:ℝ)) ∧
    L^2*‖E‖≤28*Q^(-(51/100:ℝ)) ∧
    L*‖star eta*(Q:ℂ)^x‖*‖E‖≤28*Q^(-(51/100:ℝ)) := by
  dsimp only
  have hQ0 : 0<Q := by linarith
  have hQ1 : 1≤Q := by linarith
  let R := coordR Q A x z
  let V := coordV Q z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  let B := star eta*(Q:ℂ)^x
  let L : ℝ := Q^(6*e)
  have hL : 1≤L := Real.one_le_rpow hQ1 (by positivity)
  have hL0 : 0≤L := by positivity
  have hR := coordR_norm_le Q hQ0 A x z hA
  have hV := coordV_norm Q hQ0 z
  have hD := coordD_norm_le Q hQ0 eta v x heta hv
  have hK := coordK_norm_le Q hQ1 eta x w heta
  have hW : ‖W‖≤L := (coordW_norm_le Q hQ0 v w hv).trans
    (Real.rpow_le_rpow_of_exponent_le hQ1 (by rw [hw];linarith))
  have hB : ‖B‖≤Q^x.re := by
    dsimp only [B]
    rw [norm_mul,norm_star,Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) heta
  have hRh : ‖R‖≤1/2 := hR.trans (rpow_le_half Q _ hQ (by rw [hx,hz];linarith))
  have hVh : ‖V‖≤1/2 := hV.le.trans (rpow_le_half Q _ hQ (by rw [hz];norm_num))
  have hDh : ‖D‖≤1/2 := hD.trans (rpow_le_half Q _ hQ (by rw [hx];linarith))
  have hqi : ‖(Q:ℂ)⁻¹‖≤1 := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hQ0,←one_div]
    exact (div_le_one hQ0).mpr hQ1
  have hE : ‖unramifiedMarked Q A eta v x w z+D‖≤24*L*‖R‖+4*‖K‖*‖V‖ := by
    have hh := unramified_marked_error_bound R V (Q:ℂ)⁻¹ K W D hRh hVh hqi hDh
    apply hh.trans
    nlinarith [mul_le_mul_of_nonneg_left (show 1+‖W‖≤2*L by linarith) (norm_nonneg R)]
  have weighted (k r : ℝ) (N : ℝ) (hN : N≤Q^r) (hexp : k+r≤-(51/100:ℝ)) :
      Q^k*N≤Q^(-(51/100:ℝ)) := by
    calc
      _ ≤ Q^k*Q^r := mul_le_mul_of_nonneg_left hN (Real.rpow_nonneg hQ0.le _)
      _ = Q^(k+r) := (Real.rpow_add hQ0 _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hQ1 hexp
  have hLR : L^3*‖R‖≤Q^(-(51/100:ℝ)) := by
    dsimp [L]
    rw [←Real.rpow_mul_natCast hQ0.le]
    exact weighted _ _ _ hR (by rw [hx,hz];linarith)
  have hLKV : L^2*(‖K‖*‖V‖)≤Q^(-(51/100:ℝ)) := by
    have hkv : ‖K‖*‖V‖≤Q^(1-x.re-w.re-6*z.re) := by
      calc
        _ ≤ Q^(1-x.re-w.re)*Q^(-6*z.re) := mul_le_mul hK hV.le (norm_nonneg _) (Real.rpow_nonneg hQ0.le _)
        _ = _ := by rw [←Real.rpow_add hQ0];congr 1;ring
    dsimp [L]
    rw [←Real.rpow_mul_natCast hQ0.le]
    exact weighted _ _ _ hkv (by rw [hx,hw,hz];linarith)
  have hLBR : L^2*(‖B‖*‖R‖)≤Q^(-(51/100:ℝ)) := by
    have hbr : ‖B‖*‖R‖≤Q^(4-5*x.re-6*z.re) := by
      calc
        _ ≤ Q^x.re*Q^(4-6*x.re-6*z.re) := mul_le_mul hB hR (norm_nonneg _) (Real.rpow_nonneg hQ0.le _)
        _ = _ := by rw [←Real.rpow_add hQ0];congr 1;ring
    dsimp [L]
    rw [←Real.rpow_mul_natCast hQ0.le]
    exact weighted _ _ _ hbr (by rw [hx,hz];linarith)
  have hLBKV : L*(‖B‖*‖K‖*‖V‖)≤Q^(-(51/100:ℝ)) := by
    have hbkv : ‖B‖*‖K‖*‖V‖≤Q^(1-w.re-6*z.re) := by
      calc
        _ ≤ Q^x.re*Q^(1-x.re-w.re)*Q^(-6*z.re) := by
          gcongr
          exact hV.le
        _ = _ := by rw [←Real.rpow_add hQ0,←Real.rpow_add hQ0];congr 1;ring
    exact weighted _ _ _ hbkv (by rw [hw,hz];linarith)
  refine ⟨?_,?_,?_,?_⟩
  · change L^2*‖V‖≤_
    dsimp [L]
    rw [←Real.rpow_mul_natCast hQ0.le]
    exact weighted _ _ _ hV.le (by rw [hz];linarith)
  · change L^2*‖D‖≤_
    dsimp [L]
    rw [←Real.rpow_mul_natCast hQ0.le]
    exact weighted _ _ _ hD (by rw [hx];linarith)
  · have hh := mul_le_mul_of_nonneg_left hE (sq_nonneg L)
    change L^2*‖unramifiedMarked Q A eta v x w z+D‖≤_
    nlinarith [hLR,hLKV]
  · have hh := mul_le_mul_of_nonneg_left hE (mul_nonneg hL0 (norm_nonneg B))
    change L*‖B‖*‖unramifiedMarked Q A eta v x w z+D‖≤_
    nlinarith [hLBR,hLBKV]

end SevenEighths.ProbeEuler
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.HighRowsCentralSelected
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ProbeLocal

lemma unramifiedSelected_central_error (Q a e : ℝ) (A eta v x w z : ℂ)
    (hQ : 4≤Q) (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (he : 0<e) (he1 : e≤1/1000)
    (hA : ‖A‖≤1) (heta : ‖eta‖=1) (hv : ‖v‖=1)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50) :
    ‖unramifiedSelected Q A eta v x w z+unramifiedClosed Q A eta v x w z*star v‖≤
      720*Q^(-(51/100:ℝ)) := by
  have hQ0 : 0<Q := by linarith
  have hQ1 : 1≤Q := by linarith
  have hL : 1≤Q^(6*e) := Real.one_le_rpow hQ1 (by positivity)
  have hV : ‖coordV Q z‖≤1/2 := by
    rw [coordV_norm Q hQ0]
    exact rpow_le_half Q _ hQ (by rw [hz];norm_num)
  have hD : ‖coordD Q eta v x‖≤1/2 :=
    (coordD_norm_le Q hQ0 eta v x heta.le hv.le).trans
      (rpow_le_half Q _ hQ (by rw [hx];linarith))
  have hW : ‖coordW Q v w‖≤Q^(6*e) := (coordW_norm_le Q hQ0 v w hv.le).trans
    (Real.rpow_le_rpow_of_exponent_le hQ1 (by rw [hw];linarith))
  have hq : ‖(Q:ℂ)^(-w)‖≤Q^(6*e) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0,Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by rw [hw];linarith)
  obtain ⟨hVT,hDT,hET,hBET⟩ := central_unramified_error_weights Q a e A eta v x w z
    hQ ha ha1 he he1 hA heta.le hv.le hx hw hz
  have hi := selected_phase_identities Q eta v x w hQ0 heta hv
  have hh := central_phase_error_bound (coordV Q z) (coordW Q v w) (coordD Q eta v x)
    (unramifiedMarked Q A eta v x w z) (star eta*(Q:ℂ)^x) ((Q:ℂ)^(-w)) (star v)
    (Q^(6*e)) (Q^(-(51/100:ℝ))) hL hV hD hW hq (by rw [norm_star,hv])
    hVT hDT hET hBET hi.1 hi.2
  simpa only [unramifiedSelected,unramifiedClosed,unramifiedMarked] using hh

end SevenEighths.ProbeEuler
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.HighRowsCentralQuotient
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

lemma unramifiedClosed_central_lower (Q a e : ℝ) (A eta v x w z : ℂ)
    (hQ : 480≤Q) (ha : (51/100:ℝ)≤a) (ha1 : a≤1)
    (he : 0<e) (he1 : e≤1/1000) (hA : ‖A‖≤1) (heta : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50) :
    1/2≤‖unramifiedClosed Q A eta v x w z‖ := by
  have hQ0 : 0<Q := by linarith
  have hd := unramifiedClosed_first_region_bound Q A eta v x w z (10*e)
    (by linarith) hA heta hv (by positivity) (by rw [hx];linarith)
    (by rw [hz]) (by rw [hw];linarith) (by rw [hx,hw];linarith)
  have hp : Q^(-1-min (10*e) (1/50:ℝ))≤Q^(-1:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by
      have hm : 0≤ min (10*e) (1/50:ℝ) := by positivity
      linarith)
  have hi : Q^(-1:ℝ)≤1/480 := by
    rw [Real.rpow_neg_one,←one_div]
    exact one_div_le_one_div_of_le (by norm_num) hQ
  have ht := norm_sub_le (1:ℂ) (unramifiedClosed Q A eta v x w z)
  have ht' := norm_add_le (1-unramifiedClosed Q A eta v x w z)
    (unramifiedClosed Q A eta v x w z)
  rw [sub_add_cancel,norm_one,norm_sub_rev] at ht'
  nlinarith

lemma unramifiedSelected_central_quotient_oai (Q a e : ℝ) (A eta v x w z : ℂ)
    (hQ : 480≤Q) (ha : (51/100:ℝ)≤a) (ha1 : a≤1)
    (he : 0<e) (he1 : e≤1/1000) (hA : ‖A‖≤1) (heta : ‖eta‖=1) (hv : ‖v‖=1)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50) :
    ‖unramifiedSelected Q A eta v x w z/unramifiedClosed Q A eta v x w z+star v‖≤
      1440*Q^(-(51/100:ℝ)) := by
  have hh := unramifiedClosed_central_lower Q a e A eta v x w z hQ ha ha1 he he1 hA heta.le hv.le hx hw hz
  have hn : unramifiedClosed Q A eta v x w z≠0 := by
    intro hz;rw [hz,norm_zero] at hh;norm_num at hh
  have hp : 0<‖unramifiedClosed Q A eta v x w z‖ := by linarith
  have hb := unramifiedSelected_central_error Q a e A eta v x w z
    (by linarith) ha ha1 he he1 hA heta hv hx hw hz
  have hid : unramifiedSelected Q A eta v x w z/unramifiedClosed Q A eta v x w z+star v=
      (unramifiedSelected Q A eta v x w z+unramifiedClosed Q A eta v x w z*star v)/
      unramifiedClosed Q A eta v x w z := by field_simp
  rw [hid,norm_div]
  apply (div_le_iff₀ hp).mpr
  have ht : 0≤Q^(-(51/100:ℝ)) := Real.rpow_nonneg (by linarith) _
  nlinarith
end SevenEighths.ProbeEuler
end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.ProbeEuler.unramifiedSelected_central_quotient_oai := @OAI.SevenEighths.ProbeEuler.unramifiedSelected_central_quotient_oai
