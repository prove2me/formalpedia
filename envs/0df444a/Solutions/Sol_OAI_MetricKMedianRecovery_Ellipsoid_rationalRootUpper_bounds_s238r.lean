-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.Ellipsoid.rationalRootUpper_bounds_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:23:19.211203+00:00
-- url     : https://prove2.me/submissions/a80f6447-1ebc-49de-bcdc-36a49284892b

import Mathlib
import Definitions.Def_Q238L001

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_GridFloor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid

lemma sqrtUpperFraction_bounds (p q D : ℕ) (hp : 0<p) (hq : 0<q) (hD : 0<D) :
    Real.sqrt ((p:ℝ)/(q:ℝ)) ≤ (sqrtUpperFraction p q D:ℝ) ∧
    (sqrtUpperFraction p q D:ℝ) ≤ (1+1/(D:ℝ))*Real.sqrt ((p:ℝ)/(q:ℝ)) := by
  let w := Real.sqrt ((p:ℝ)/(q:ℝ))
  have hpR : 0<(p:ℝ) := by exact_mod_cast hp
  have hqR : 0<(q:ℝ) := by exact_mod_cast hq
  have hDR : 0<(D:ℝ) := by exact_mod_cast hD
  have hw : 0≤w := Real.sqrt_nonneg _
  have hw2 : w^2=(p:ℝ)/(q:ℝ) := Real.sq_sqrt (div_nonneg hpR.le hqR.le)
  have hf : ((q:ℝ)*(D:ℝ)*w)^2=(p:ℝ)*(q:ℝ)*(D:ℝ)^2 := by
    rw [mul_pow,mul_pow,hw2]
    field_simp
  let k := Nat.sqrt (p*q*D^2)
  have hk2 : (k:ℝ)^2≤(p:ℝ)*(q:ℝ)*(D:ℝ)^2 := by
    exact_mod_cast Nat.sqrt_le' (p*q*D^2)
  have hks : (p:ℝ)*(q:ℝ)*(D:ℝ)^2<((k:ℝ)+1)^2 := by
    exact_mod_cast Nat.lt_succ_sqrt' (p*q*D^2)
  have hkw : (k:ℝ)≤(q:ℝ)*(D:ℝ)*w := by
    have : 0≤(q:ℝ)*(D:ℝ)*w := by positivity
    nlinarith
  have hwk : (q:ℝ)*(D:ℝ)*w≤(k:ℝ)+1 := by
    have : 0≤(k:ℝ) := by positivity
    nlinarith
  have hqw : 1≤(q:ℝ)*w := by
    have hp1 : (1:ℝ)≤p := by exact_mod_cast hp
    have hq1 : (1:ℝ)≤q := by exact_mod_cast hq
    have hab : (1:ℝ)≤(p:ℝ)*(q:ℝ) := by nlinarith
    have hs : ((q:ℝ)*w)^2=(p:ℝ)*(q:ℝ) := by rw [mul_pow,hw2]; field_simp
    have : 0≤(q:ℝ)*w := by positivity
    nlinarith
  have he : (sqrtUpperFraction p q D:ℝ)=((k:ℝ)+1)/((q:ℝ)*(D:ℝ)) := by
    simp [sqrtUpperFraction,k]
  rw [he]
  constructor
  · apply (le_div_iff₀ (mul_pos hqR hDR)).mpr
    nlinarith [hwk]
  · apply (div_le_iff₀ (mul_pos hqR hDR)).mpr
    have hh : ((1+1/(D:ℝ))*w)*((q:ℝ)*(D:ℝ))=(q:ℝ)*(D:ℝ)*w+(q:ℝ)*w := by
      field_simp
    rw [hh]
    linarith

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RealVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid

section
open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma rationalRootUpper_bounds_s238r_oai (D : ℕ) (hD : 0<D) (q : ℚ) (hq : 0<q) :
    Real.sqrt (q:ℝ) ≤ (rationalRootUpper D q:ℝ) ∧
    (rationalRootUpper D q:ℝ) ≤ (1+1/(D:ℝ))*Real.sqrt (q:ℝ) := by
  have hn := Rat.num_pos.mpr hq
  have hp : 0<q.num.natAbs := Int.natAbs_pos.mpr (ne_of_gt hn)
  have hc : (q.num.natAbs:ℤ)=q.num := Int.natAbs_of_nonneg hn.le
  have he : ((q.num.natAbs:ℚ)/(q.den:ℚ))=q := by
    rw [←Int.cast_natCast,hc,q.num_div_den]
  have her : (q.num.natAbs:ℝ)/(q.den:ℝ)=(q:ℝ) := by
    have hh := congrArg (fun z : ℚ => (z:ℝ)) he
    simpa only [Rat.cast_div,Rat.cast_natCast] using hh
  have hh := sqrtUpperFraction_bounds q.num.natAbs q.den D hp q.pos hD
  simpa only [her,rationalRootUpper] using hh

end

open Matrix
open scoped Matrix

end MetricKMedianRecovery.Ellipsoid

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.Ellipsoid.rationalRootUpper_bounds_s238r_oai := @OAI.MetricKMedianRecovery.Ellipsoid.rationalRootUpper_bounds_s238r_oai
