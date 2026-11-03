-- Prove2me | solution 1 for OAI.Laughlin.Spin.source_fourBody_error_matrix_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:09:26.911948+00:00
-- url     : https://prove2.me/submissions/9999e36b-865d-4561-9b59-c1096de82c37

import Mathlib
import Definitions.Def_OAIQ050L007
import Definitions.Def_OAIQ050L008
import Definitions.Def_OAIQ050L010
import Theorems.Thm_OAI_Laughlin_Spin_source_fourBody_factorial_coefficient_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_ErrorLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

theorem source_rows_admissible : ∀ row ∈ Certificate.rows, ∀ e ∈ row.2.2,
    row.1 ≤ e.1+e.2.1 := by decide

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_RadicalCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin

theorem fourBodyRadical_factorial (r D T p j k : ℕ) (hr : r ≤ T) :
    fourBodyRadical r D T p j k =
      Real.sqrt 2 * (Real.sqrt (1/2))^(j+k+(T-r)) *
      sqrtFactorial j * sqrtFactorial k * sqrtFactorial p /
        (sqrtFactorial r * sqrtFactorial (D-r) * sqrtFactorial (T-D)) := by
  let m := j+k+(T-r)
  have hm : (1 : ℤ)-(j : ℤ)-k-T+r = 1-(m : ℤ) := by
    dsimp [m]
    simp only [Nat.cast_sub hr]
    omega
  have hp : (2 : ℝ)^((1 : ℤ)-(j : ℤ)-k-T+r) = 2*(1/2 : ℝ)^m := by
    rw [hm,zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0),zpow_one,zpow_natCast]
    simp [div_eq_mul_inv]
  let a := Real.sqrt 2 * (Real.sqrt (1/2))^m *
    sqrtFactorial j * sqrtFactorial k * sqrtFactorial p /
      (sqrtFactorial r * sqrtFactorial (D-r) * sqrtFactorial (T-D))
  have ha : 0 ≤ a := by dsimp [a]; unfold sqrtFactorial; positivity
  have hs : a^2 = (2 : ℝ)^((1 : ℤ)-(j : ℤ)-k-T+r) *
    ((j.factorial : ℝ)*(k.factorial : ℝ)*(p.factorial : ℝ) /
      ((r.factorial : ℝ)*((D-r).factorial : ℝ)*((T-D).factorial : ℝ))) := by
    rw [hp]
    dsimp [a]
    simp only [div_pow,mul_pow,sqrtFactorial]
    rw [show ((Real.sqrt (1/2))^m)^2 = (1/2 : ℝ)^m by
      rw [← pow_mul,mul_comm m 2,pow_mul,Real.sq_sqrt (by norm_num)]]
    simp only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),Real.sq_sqrt (Nat.cast_nonneg _)]
    ring_nf
    norm_num
  change Real.sqrt _ = a
  rw [← hs,Real.sqrt_sq ha]

theorem source_fourBody_radical_coefficient (r D T p j k : ℕ)
    (hrD : r ≤ D) (hDT : D ≤ T) (hT : p+j+k=T) :
    fourBodyLimitCoefficient r D T p j k =
      (Certificate.V r D T p j k : ℝ) * fourBodyRadical r D T p j k := by
  by_cases hr : r ≤ j+k
  · rw [source_fourBody_factorial_coefficient_s50 r D T p j k hrD hDT hT hr,
      fourBodyRadical_factorial r D T p j k (by omega)]
    ring
  · simp [fourBodyLimitCoefficient,Certificate.V,hr]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_RadicalCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin

theorem source_Y_radical_cancellation (D r s t p j q l : ℕ)
    (hor : Odd r) (hos : Odd s) (he : t ≤ p+j) (hf : t ≤ q+l) :
    alphaRadical t p j * alphaRadical t q l *
      fourBodyRadical r D (p+j+(q+l-t)) p j (q+l-t) *
      fourBodyRadical s D (p+j+(q+l-t)) q l (p+j-t) =
    Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s) * sourceYFactor D r s t p j q l := by
  let i := p+j-t
  let k := q+l-t
  let T := p+j+k
  let e : ℤ := 1-2*(T : ℤ)+p+q-t+((r+s)/2 : ℕ)
  have hT : p+j+k=T := rfl
  have hT' : q+l+i=T := by dsimp [i,k,T]; omega
  have hTr : (p : ℤ)+j+k=T := by exact_mod_cast hT
  have hTr' : (q : ℤ)+l+i=T := by exact_mod_cast hT'
  have heven : (((r+s)/2 : ℕ) : ℤ)*2=(r : ℤ)+s := by
    rcases hor with ⟨a,ha⟩; rcases hos with ⟨b,hb⟩
    omega
  have hex : ((p : ℤ)-t)+((q : ℤ)-t)+((1 : ℤ)-j-k-T+r)+((1 : ℤ)-l-i-T+s)=e*2 := by
    dsimp [e]; omega
  have hpowers : (2 : ℝ)^((p : ℤ)-t) * (2 : ℝ)^((q : ℤ)-t) *
      (2 : ℝ)^((1 : ℤ)-j-k-T+r) * (2 : ℝ)^((1 : ℤ)-l-i-T+s) = ((2 : ℝ)^e)^2 := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
      ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),hex,zpow_mul]
    norm_num
  let F : ℝ := ((i.factorial : ℝ)*(k.factorial : ℝ)*(t.factorial : ℝ))^2 /
    ((r.factorial : ℝ)*((D-r).factorial : ℝ)*(s.factorial : ℝ)*((D-s).factorial : ℝ)*((T-D).factorial : ℝ)^2)
  have hsq : (alphaRadical t p j * alphaRadical t q l * fourBodyRadical r D T p j k *
      fourBodyRadical s D T q l i)^2 =
      (Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s) * sourceYFactor D r s t p j q l)^2 := by
    simp only [alphaRadical,fourBodyRadical,mul_pow]
    have hc0 : 0 ≤ sourceCopyWeight D r * sourceCopyWeight D s := by
      unfold sourceCopyWeight; positivity
    rw [Real.sq_sqrt hc0]
    repeat rw [Real.sq_sqrt (by positivity)]
    change (2^((p : ℤ)-t)*((t.factorial : ℝ)*i.factorial/(p.factorial*j.factorial))) *
      (2^((q : ℤ)-t)*((t.factorial : ℝ)*k.factorial/(q.factorial*l.factorial))) *
      (2^((1 : ℤ)-j-k-T+r)*((j.factorial : ℝ)*k.factorial*p.factorial /
        (r.factorial*(D-r).factorial*(T-D).factorial))) *
      (2^((1 : ℤ)-l-i-T+s)*((l.factorial : ℝ)*i.factorial*q.factorial /
        (s.factorial*(D-s).factorial*(T-D).factorial))) = _
    calc
      _ = (2^((p : ℤ)-t)*2^((q : ℤ)-t)*2^((1 : ℤ)-j-k-T+r)*2^((1 : ℤ)-l-i-T+s))*F := by
        dsimp [F]
        field_simp
      _ = ((2 : ℝ)^e)^2*F := by rw [hpowers]
      _ = _ := by
        dsimp [F,sourceYFactor,sourceCopyWeight]
        change ((2 : ℝ)^e)^2 * _ = (1/((r.factorial : ℝ)*(D-r).factorial) *
          (1/((s.factorial : ℝ)*(D-s).factorial))) *
          ((2 : ℝ)^e * ((i.factorial : ℝ)*k.factorial*t.factorial/(T-D).factorial))^2
        field_simp
  have hl : 0 ≤ alphaRadical t p j * alphaRadical t q l * fourBodyRadical r D T p j k *
      fourBodyRadical s D T q l i := by unfold alphaRadical fourBodyRadical; positivity
  have hr : 0 ≤ Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s) * sourceYFactor D r s t p j q l := by
    unfold sourceYFactor; positivity
  nlinarith only [hsq,hl,hr]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_ErrorCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem sourceAlpha_factor (t : ℕ) (e : ℕ × ℕ × ℤ) :
    sourceAlpha t e = (e.2.2 : ℝ)/(10^7) * alphaRadical t e.1 e.2.1 := rfl

theorem fourErrorLimitEntry_certificate (D r s t : ℕ) (e f : ℕ × ℕ × ℤ)
    (hr : r ≤ D) (hs : s ≤ D) (hor : Odd r) (hos : Odd s)
    (he : t ≤ e.1+e.2.1) (hf : t ≤ f.1+f.2.1) :
    fourErrorLimitEntry D r s t e f =
      (Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s)/(10^14)) *
        (Certificate.yEntry D r s t e f : ℝ) := by
  rcases e with ⟨p,j,a⟩
  rcases f with ⟨q,l,b⟩
  dsimp only at he hf ⊢
  let i := p+j-t
  let k := q+l-t
  let T := p+j+k
  have hT' : q+l+i=T := by dsimp [i,k,T]; omega
  by_cases hD : D ≤ T
  · have heq : fourErrorLimitEntry D r s t (p,j,a) (q,l,b) =
        sourceAlpha t (p,j,a) * sourceAlpha t (q,l,b) *
          fourBodyLimitCoefficient r D T p j k * fourBodyLimitCoefficient s D T q l i := by
      simp only [fourErrorLimitEntry]; exact ite_eq_left hD
    rw [heq,sourceAlpha_factor,sourceAlpha_factor,
      source_fourBody_radical_coefficient r D T p j k hr hD rfl,
      source_fourBody_radical_coefficient s D T q l i hs hD hT']
    dsimp only
    calc
      _ = ((a : ℝ)*(b : ℝ)*(Certificate.V r D T p j k : ℝ)*(Certificate.V s D T q l i : ℝ)/(10^14)) *
          (alphaRadical t p j * alphaRadical t q l * fourBodyRadical r D T p j k * fourBodyRadical s D T q l i) := by ring
      _ = ((a : ℝ)*(b : ℝ)*(Certificate.V r D T p j k : ℝ)*(Certificate.V s D T q l i : ℝ)/(10^14)) *
          (Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s)*sourceYFactor D r s t p j q l) := by
        rw [source_Y_radical_cancellation D r s t p j q l hor hos he hf]
      _ = _ := by
        simp only [Certificate.yEntry]
        rw [ite_eq_left hD]
        push_cast
        dsimp [sourceYFactor,i,k,T]
        ring
  · simp only [fourErrorLimitEntry,Certificate.yEntry]
    rw [ite_eq_right hD,ite_eq_right hD]
    simp

theorem real_list_sum_scale {I : Type*} (l : List I) (c : ℝ) (f : I → ℝ) :
    (l.map (fun i => c*f i)).sum = c*(l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons,List.sum_cons,ih]; ring

theorem fourErrorLimitRow_certificate (D r s : ℕ) (hr : r ≤ D) (hs : s ≤ D)
    (hor : Odd r) (hos : Odd s) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) (hrow : row ∈ Certificate.rows) :
    fourErrorLimitRow D r s row =
      (Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s)/(10^14)) *
        (Certificate.yRow D r s row : ℝ) := by
  unfold fourErrorLimitRow
  have he : ∀ e ∈ row.2.2, ∀ f ∈ row.2.2,
      fourErrorLimitEntry D r s row.1 e f =
        (Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s)/(10^14)) *
          (Certificate.yEntry D r s row.1 e f : ℝ) := by
    intro e he f hf
    exact fourErrorLimitEntry_certificate D r s row.1 e f hr hs hor hos
      (source_rows_admissible row hrow e he) (source_rows_admissible row hrow f hf)
  calc
    _ = (row.2.2.map (fun e => (row.2.2.map (fun f =>
        (Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s)/(10^14)) *
          (Certificate.yEntry D r s row.1 e f : ℝ))).sum)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left; intro e he'
      apply congrArg List.sum
      apply List.map_congr_left; intro f hf'
      exact he e he' f hf'
    _ = _ := by
      simp_rw [real_list_sum_scale]
      unfold Certificate.yRow
      push_cast
      simp only [List.map_map,Function.comp_def]
      push_cast
      simp only [List.map_map,Function.comp_def]

theorem source_fourBody_error_certificate_identity (D r s : ℕ) (hr : r ≤ D) (hs : s ≤ D)
    (hor : Odd r) (hos : Odd s) :
    limitFourError D r s = Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s) *
      (Certificate.Y D r s : ℝ) := by
  unfold limitFourError
  have he : Certificate.rows.map (fourErrorLimitRow D r s) = Certificate.rows.map (fun row =>
      (Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s)/(10^14)) *
        (Certificate.yRow D r s row : ℝ)) := by
    apply List.map_congr_left; intro row hrow
    exact fourErrorLimitRow_certificate D r s hr hs hor hos row hrow
  rw [he,real_list_sum_scale]
  unfold Certificate.Y
  push_cast
  simp only [List.map_map,Function.comp_def]
  ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Scaled
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix

theorem copyWeight_nonneg (D : ℕ) (i : Fin ((D+1)/2)) : 0 ≤ (copyWeight D i : ℝ) := by
  unfold copyWeight
  positivity

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_ErrorMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Matrix Topology
open Filter

theorem sourceCopyWeight_certificate (D : ℕ) (i : Fin ((D+1)/2)) :
    sourceCopyWeight D (Certificate.copyLabel i) = (Certificate.copyWeight D i : ℝ) := by
  simp [sourceCopyWeight,Certificate.copyWeight]

theorem source_fourBody_error_matrix_s50_oai (D : ℕ) (i j : Fin ((D+1)/2)) :
    limitFourError D (Certificate.copyLabel i) (Certificate.copyLabel j) = Certificate.scaledError D i j := by
  have hi : Certificate.copyLabel i ≤ D := by unfold Certificate.copyLabel; have := i.isLt; omega
  have hj : Certificate.copyLabel j ≤ D := by unfold Certificate.copyLabel; have := j.isLt; omega
  have hoi : Odd (Certificate.copyLabel i) := ⟨i.val,by unfold Certificate.copyLabel; omega⟩
  have hoj : Odd (Certificate.copyLabel j) := ⟨j.val,by unfold Certificate.copyLabel; omega⟩
  rw [source_fourBody_error_certificate_identity D _ _ hi hj hoi hoj,
    sourceCopyWeight_certificate,sourceCopyWeight_certificate,
    Real.sqrt_mul (Certificate.copyWeight_nonneg D i)]
  simp only [Certificate.scaledError,Certificate.weightSqrtDiagonal,Matrix.diagonal_mul,
    Matrix.mul_diagonal,Matrix.map_apply,Certificate.errorRational,Rat.coe_castHom]
  ring

end Laughlin.Spin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Spin.source_fourBody_error_matrix_s50_oai := @OAI.Laughlin.Spin.source_fourBody_error_matrix_s50_oai
