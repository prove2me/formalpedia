-- Prove2me | solution 1 for OAI.RVM.Admissible.projected_source_stable_far_log_sum
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:10:49.125949+00:00
-- url     : https://prove2.me/submissions/23822ed5-e5bc-43f1-bd12-5916a633a40c

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_Admissible_projected_source_baseline_far

section
-- module Solutions.OAIQ073_VM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ConeMotion
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary relativistic geometry needed by the retarded-force identity. -/

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace RVM

lemma q_pos (v : Vec) : 0 < q v := by
  exact Real.sqrt_pos.2 (by positivity)

open scoped Topology

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_RetardedPhaseDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

namespace EnergyPrefix
variable {s : Solution} {T : ℝ}

lemma particle_energy_nonneg (hs : EnergyPrefix s T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec) :
    0 ≤ particleEnergy s (t,x) := by
  apply integral_nonneg
  intro v
  exact mul_nonneg (q_pos v).le (hs.nonnegative t ht (x,v))

lemma total_energy_nonneg (hs : EnergyPrefix s T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec) :
    0 ≤ totalEnergy s (t,x) := by
  dsimp [totalEnergy]
  have hp := particle_energy_nonneg hs ht x
  positivity

end EnergyPrefix

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SelectionWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology

namespace RVM

lemma div_stabilityLength (P C₁ M A p w φ t : ℝ) :
    t/stabilityLength P C₁ M A p w φ =
      t*(stabilityRate P C₁ M A p w φ)^2 := by
  simp [stabilityLength, div_eq_mul_inv, inv_pow]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_NormalisedPartialCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma product_le_min_scale {P p w : ℝ} (hp : 0≤p) (hw : 0≤w)
    (hpP : p≤P) (hwP : w≤P) : w*p≤P*min p w := by
  rcases le_total p w with h|h
  · rw [min_eq_left h]
    exact mul_le_mul_of_nonneg_right hwP hp
  · rw [min_eq_right h]
    calc w*p≤w*P := mul_le_mul_of_nonneg_left hpP hw
         _ = P*w := by ring

lemma sqrt_div_stabilityLength {P C M A p w φ I : ℝ}
    (hP : 0≤P) (hC : 0≤C) (hM : 0≤M) (hp : 0≤p) (hw : 0≤w)
    (hφ : 0≤φ) (hI : 0≤I) :
    Real.sqrt (I/stabilityLength P C M A p w φ)=
      Real.sqrt I*stabilityRate P C M A p w φ := by
  rw [div_stabilityLength,Real.sqrt_mul hI,Real.sqrt_sq]
  unfold stabilityRate
  positivity

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SqrtBaselineClippedLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma sqrt_baseline_clipped_length {I lam : ℝ} (hI : 0 < I) (hlam : 0 < lam) :
    Real.sqrt (1+I/min I (lam/2))  ≤  2*(1+Real.sqrt (I/lam)) := by
  have hlen : 0 < min I (lam/2) := lt_min hI (by positivity)
  have hq : 0 ≤ I/lam := by positivity
  have hR : 0 ≤ Real.sqrt (I/lam) := Real.sqrt_nonneg _
  have hRsq := Real.sq_sqrt hq
  have hdiv : I/min I (lam/2)  ≤  1+2*(I/lam) := by
    rcases le_total I (lam/2) with h|h
    · rw [min_eq_left h,div_self hI.ne']
      linarith
    · rw [min_eq_right h]
      have he : I/(lam/2)=2*(I/lam) := by ring
      rw [he]
      linarith
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  nlinarith

lemma stabilityLength_pos {P C M A p w φ : ℝ} (hP : 0 < P) (hC : 0 < C)
    (hM : 0 < M) (hp : 0 < p) (hw : 0 < w) (hφ : 0 < φ) :
    0 < stabilityLength P C M A p w φ := by
  unfold stabilityLength stabilityRate
  have hm : 0 < min p w := lt_min hp hw
  have hr : 0  <  M/φ+Real.sqrt (A*Real.log (2+P)/φ) :=
    add_pos_of_pos_of_nonneg (div_pos hM hφ) (Real.sqrt_nonneg _)
  positivity

lemma stability_massScale_identity (P C M A p w φ : ℝ) :
    (C*(P/(min p w/128))*(M/φ+Real.sqrt (A*Real.log (2+P)/φ)))⁻¹^2 =
      stabilityLength P (128*C) M A p w φ := by
  unfold stabilityLength stabilityRate
  congr 2
  ring

lemma direction_baseline_R_bound128 {P C M A p w φ : ℝ}
    (hP : 0<P) (hC : 0≤C) (hM : 0≤M) (hA : 0≤A)
    (hp : 0<p) (hw : 0<w) (hφ : 0<φ) (hφ1 : φ≤1)
    (hpP : p≤128*P) (hwP : w≤P) :
    Real.sqrt ((w/P)^2)*(1+Real.sqrt (((w/P)^2)/stabilityLength P C M A p w φ))*p*φ≤
      128*w*(1+C*(M+Real.sqrt (A*Real.log (2+P)))) := by
  have hL : 0≤Real.log (2+P) := Real.log_nonneg (by linarith)
  have hm : 0 < min p w := lt_min hp hw
  have hwP' : w≤128*P := hwP.trans (by linarith only [hP])
  have hwp := product_le_min_scale hp.le hw.le hpP hwP'
  have hmain : w^2*p/(P*min p w)≤128*w := by
    apply (div_le_iff₀ (mul_pos hP hm)).mpr
    nlinarith
  have hfirst : w*p*φ/P≤128*w := by
    apply (div_le_iff₀ hP).mpr
    have hh : p*φ≤128*P := (mul_le_of_le_one_right hp.le hφ1).trans hpP
    nlinarith
  have hroot : φ*Real.sqrt (A*Real.log (2+P)/φ)=
      Real.sqrt (A*Real.log (2+P)*φ) := by
    calc
      _ = Real.sqrt (φ^2)*Real.sqrt (A*Real.log (2+P)/φ) := by rw [Real.sqrt_sq hφ.le]
      _ = Real.sqrt (A*Real.log (2+P)*φ) := by
        rw [←Real.sqrt_mul (sq_nonneg φ)]
        congr 1
        field_simp
  have hsqrt : Real.sqrt (A*Real.log (2+P)*φ)≤Real.sqrt (A*Real.log (2+P)) :=
    Real.sqrt_le_sqrt (mul_le_of_le_one_right (mul_nonneg hA hL) hφ1)
  rw [Real.sqrt_sq (div_nonneg hw.le hP.le),
    sqrt_div_stabilityLength hP.le hC hM hp.le hw.le hφ.le (sq_nonneg _),
    Real.sqrt_sq (div_nonneg hw.le hP.le)]
  have he : (w/P)*(1+(w/P)*stabilityRate P C M A p w φ)*p*φ=
      w*p*φ/P+C*(w^2*p/(P*min p w))*(M+φ*Real.sqrt (A*Real.log (2+P)/φ)) := by
    unfold stabilityRate
    field_simp
  rw [he,hroot]
  calc
    _ ≤ 128*w+C*(128*w)*(M+Real.sqrt (A*Real.log (2+P))) := by gcongr
    _ = _ := by ring

lemma direction_baseline_R_log_bound128 {P C M A p w φ : ℝ}
    (hP : 0<P) (hL : 1≤Real.log (2+P)) (hC : 0≤C) (hM : 0≤M) (hA : 0≤A)
    (hp : 0<p) (hw : 0<w) (hφ : 0<φ) (hφ1 : φ≤1)
    (hpP : p≤128*P) (hwP : w≤P) :
    Real.sqrt ((w/P)^2)*(1+Real.sqrt (((w/P)^2)/stabilityLength P C M A p w φ))*p*φ≤
      128*(1+C*(M+Real.sqrt A))*w*Real.sqrt (Real.log (2+P)) := by
  apply (direction_baseline_R_bound128 hP hC hM hA hp hw hφ hφ1 hpP hwP).trans
  rw [Real.sqrt_mul hA]
  have hroot : 1≤Real.sqrt (Real.log (2+P)) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hL
  have h0 : 0≤1+C*M := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hroot (mul_nonneg (show 0≤128*w by positivity) h0)]

lemma direction_clipped_baseline_R_log_bound128 {P C M A p w φ : ℝ}
    (hP : 0 < P) (hL : 1 ≤ Real.log (2+P)) (hC : 0 < C) (hM : 0 < M) (hA : 0 ≤ A)
    (hp : 0 < p) (hw : 0 < w) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hpP : p ≤ 128*P) (hwP : w ≤ P) :
    let I := (w/P)^2
    let lam := stabilityLength P C M A p w φ
    Real.sqrt I*Real.sqrt (1+I/min I (lam/2))*p*φ  ≤
      256*(1+C*(M+Real.sqrt A))*w*Real.sqrt (Real.log (2+P)) := by
  dsimp only
  have hI : 0 < (w/P)^2 := sq_pos_of_pos (div_pos hw hP)
  have hlam := stabilityLength_pos hP hC hM hp hw hφ (A:=A)
  have hroot := sqrt_baseline_clipped_length hI hlam
  have hbound := direction_baseline_R_log_bound128 hP hL hC.le hM.le hA hp hw hφ hφ1 hpP hwP
  calc
    _  ≤  Real.sqrt ((w/P)^2)*(2*(1+Real.sqrt (((w/P)^2)/stabilityLength P C M A p w φ)))*p*φ := by gcongr
    _ = 2*(Real.sqrt ((w/P)^2)*(1+Real.sqrt (((w/P)^2)/stabilityLength P C M A p w φ))*p*φ) := by ring
    _  ≤  2*(128*(1+C*(M+Real.sqrt A))*w*Real.sqrt (Real.log (2+P))) := by gcongr
    _ = _ := by ring

lemma direction_clipped_source_angle_bound {P C M A p w θ φ : ℝ}
    (hP : 0 < P) (hL : 1 ≤ Real.log (2+P)) (hC : 0 < C) (hM : 0 < M) (hA : 0 ≤ A)
    (hp : 1 ≤ p) (hw : 1 ≤ w) (hθ : 0 ≤ θ) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hθφ : θ ≤ φ) :
    let I := (w/P)^2
    let lam := stabilityLength P C M A p w φ
    Real.sqrt (1+I/min I (lam/2))*θ ≤
      2*(1+C*(M+Real.sqrt A))*w*Real.sqrt (Real.log (2+P)) := by
  dsimp only
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hw0 : 0 < w := zero_lt_one.trans_le hw
  have hm : 1 ≤ min p w := le_min hp hw
  have hm0 : 0 < min p w := zero_lt_one.trans_le hm
  have hI : 0 < (w/P)^2 := sq_pos_of_pos (div_pos hw0 hP)
  have hlam := stabilityLength_pos hP hC hM hp0 hw0 hφ (A:=A)
  have hroot := sqrt_baseline_clipped_length hI hlam
  have hlog : 0 ≤ Real.log (2+P) := le_trans (by norm_num) hL
  have hθ1 : θ ≤ 1 := hθφ.trans hφ1
  have hquot : θ/φ ≤ 1 := (div_le_one hφ).mpr hθφ
  have hwm : w/min p w ≤ w := div_le_self hw0.le hm
  have hsqrt : θ*Real.sqrt (A*Real.log (2+P)/φ) ≤ Real.sqrt (A*Real.log (2+P)) := by
    calc
      _ ≤ φ*Real.sqrt (A*Real.log (2+P)/φ) := mul_le_mul_of_nonneg_right hθφ (Real.sqrt_nonneg _)
      _ = Real.sqrt (φ^2)*Real.sqrt (A*Real.log (2+P)/φ) := by rw [Real.sqrt_sq hφ.le]
      _ = Real.sqrt (A*Real.log (2+P)*φ) := by
        rw [←Real.sqrt_mul (sq_nonneg φ)]
        congr 1
        field_simp
      _ ≤ _ := Real.sqrt_le_sqrt (mul_le_of_le_one_right (mul_nonneg hA hlog) hφ1)
  have hr : 1 ≤ Real.sqrt (Real.log (2+P)) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hL
  have he : 2*(1+(w/P)*stabilityRate P C M A p w φ)*θ=
      2*θ+2*C*(w/min p w)*(M*(θ/φ)+θ*Real.sqrt (A*Real.log (2+P)/φ)) := by
    unfold stabilityRate
    field_simp
  have hMQ : M*(θ/φ)≤M := mul_le_of_le_one_right hM.le hquot
  have hθw : θ≤w := hθ1.trans hw
  rw [sqrt_div_stabilityLength hP.le hC.le hM.le hp0.le hw0.le hφ.le hI.le,
    Real.sqrt_sq (div_nonneg hw0.le hP.le)] at hroot
  calc
    _ ≤ 2*(1+(w/P)*stabilityRate P C M A p w φ)*θ := mul_le_mul_of_nonneg_right hroot hθ
    _ = _ := he
    _ ≤ 2*w+2*C*w*(M+Real.sqrt (A*Real.log (2+P))) := by gcongr
    _ ≤ _ := by
      rw [Real.sqrt_mul hA]
      have h0 : 0≤1+C*M := by positivity
      nlinarith only [mul_le_mul_of_nonneg_left hr (mul_nonneg hw0.le h0)]

lemma direction_source_far_scale {P C M A p w θ r φ : ℝ}
    (hP : 0 < P) (hL : 1 ≤ Real.log (2+P)) (hC : 0 < C) (hM : 0 < M) (hA : 0 ≤ A)
    (hp : 1 ≤ p) (hw : 1 ≤ w) (hθ : 0 < θ) (hr : 0 < r) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) (hθφ : θ ≤ φ) (hpP : p ≤ 128*P) (hwP : w ≤ P)
    (hfar : 1/32 ≤ p*θ*Real.sqrt r) :
    let I := (w/P)^2
    let lam := stabilityLength P C M A p w φ
    let R := Real.sqrt (1+I/min I (lam/2))
    Real.sqrt I*R*φ/(θ*Real.sqrt r)+2*R*θ ≤
      8196*(1+C*(M+Real.sqrt A))*w*Real.sqrt (Real.log (2+P)) := by
  dsimp only
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hw0 : 0 < w := zero_lt_one.trans_le hw
  have hB := direction_clipped_baseline_R_log_bound128 hP hL hC hM hA hp0 hw0 hφ hφ1 hpP hwP
  have hR := direction_clipped_source_angle_bound hP hL hC hM hA hp hw hθ.le hφ hφ1 hθφ
  have hfirst : Real.sqrt ((w/P)^2)*Real.sqrt (1+(w/P)^2/min ((w/P)^2)
      (stabilityLength P C M A p w φ/2))*φ/(θ*Real.sqrt r) ≤
      8192*(1+C*(M+Real.sqrt A))*w*Real.sqrt (Real.log (2+P)) := by
    let B := (1+C*(M+Real.sqrt A))*w*Real.sqrt (Real.log (2+P))
    have h0 : 0≤B := by dsimp [B]; positivity
    apply (div_le_iff₀ (mul_pos hθ (Real.sqrt_pos.mpr hr))).mpr
    have hh := mul_le_mul_of_nonneg_left hfar (show 0≤8192*B by positivity)
    have hB' : Real.sqrt ((w/P)^2)*Real.sqrt (1+(w/P)^2/min ((w/P)^2)
        (stabilityLength P C M A p w φ/2))*p*φ ≤ 256*B := by simpa only [B,mul_assoc] using hB
    apply (mul_le_mul_iff_right₀ hp0).mp
    dsimp [B] at *
    nlinarith only [hh,hB']
  nlinarith only [hfirst,hR]

end RVM

end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_CappedRepresentativePos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma cappedRepresentative_pos (n : ℕ) : 0 < cappedRepresentative n := by
  dsimp [cappedRepresentative]
  positivity

lemma cappedRepresentative_le_one (n : ℕ) : cappedRepresentative n ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

lemma source_far_sqrt_mass {b p θ R r φ : ℝ}
    (hb : 0≤b) (hp : 0<p) (hθ : 0<θ) (hR : 0≤R) (hr : 0 < r) (hφ : 0<φ) :
    Real.sqrt (b*p^2*θ^2*R^2/(r*φ^2)) =
      Real.sqrt b*p*θ*R/(Real.sqrt r*φ) := by
  rw [Real.sqrt_div (by positivity),Real.sqrt_mul (by positivity : 0≤b*p^2*θ^2),
    Real.sqrt_mul (by positivity : 0≤b*p^2),Real.sqrt_mul hb,
    Real.sqrt_mul hr.le,Real.sqrt_sq hp.le,Real.sqrt_sq hθ.le,
    Real.sqrt_sq hR,Real.sqrt_sq hφ.le]

lemma source_far_good_scalar {a b I p θ R r φ : ℝ}
    (ha : 0≤a) (hb : 0≤b) (hp : 0<p) (hθ : 0<θ)
    (hR : 0≤R) (hr : 0 < r) (hφ : 0<φ) :
    φ^2/(p*θ^2)*Real.sqrt (a*I)*Real.sqrt (b*p^2*θ^2*R^2/(r*φ^2)) =
      Real.sqrt (a*b)*Real.sqrt I*R*φ/(θ*Real.sqrt r) := by
  rw [source_far_sqrt_mass hb hp hθ hR hr hφ,Real.sqrt_mul ha,Real.sqrt_mul ha]
  field_simp [hp.ne',hθ.ne',hφ.ne',(Real.sqrt_pos.mpr hr).ne']

lemma source_far_magnetic_scalar {a b I p θ R r φ : ℝ}
    (ha : 0≤a) (hb : 0≤b) (hI : 0≤I) (hp : 0<p) (hθ : 0<θ)
    (hR : 0≤R) (hr : 0 < r) (hφ : 0<φ) :
    φ/p*Real.sqrt (a*(I+2*r))*Real.sqrt (b*p^2*θ^2*R^2/(r*φ^2)) =
      Real.sqrt (a*b)*R*θ*Real.sqrt (I/r+2) := by
  have hs : Real.sqrt (I/r+2)=Real.sqrt (I+2*r)/Real.sqrt r := by
    rw [show I/r+2=(I+2*r)/r by field_simp,Real.sqrt_div (by positivity)]
  rw [hs,source_far_sqrt_mass hb hp hθ hR hr hφ,Real.sqrt_mul ha,Real.sqrt_mul ha]
  field_simp [hp.ne',hφ.ne',(Real.sqrt_pos.mpr hr).ne']

lemma source_far_magnetic_le {I θ R r φ : ℝ}
    (hI : 0≤I) (hθ : 0<θ) (hR : 0≤R) (hr : 0 < r) (hθφ : θ^2≤φ) :
    R*θ*Real.sqrt (I/r+2) ≤ Real.sqrt I*R*φ/(θ*Real.sqrt r)+2*R*θ := by
  have hs : Real.sqrt (I/r+2) ≤ Real.sqrt I/Real.sqrt r+2 := by
    calc
      _ ≤ Real.sqrt (I/r)+Real.sqrt 2 := by
        apply (Real.sqrt_le_left (by positivity)).mpr
        nlinarith only [Real.sq_sqrt (show 0≤I/r by positivity),
          Real.sq_sqrt (show (0:ℝ)≤2 by norm_num),
          mul_nonneg (Real.sqrt_nonneg (I/r)) (Real.sqrt_nonneg 2)]
      _ ≤ _ := by rw [Real.sqrt_div hI]; gcongr; norm_num
  have hθ' : θ≤φ/θ := (le_div_iff₀ hθ).mpr (by simpa only [sq] using hθφ)
  calc
    _ ≤ R*θ*(Real.sqrt I/Real.sqrt r+2) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = Real.sqrt I*R*θ/Real.sqrt r+2*R*θ := by ring
    _ ≤ Real.sqrt I*R*(φ/θ)/Real.sqrt r+2*R*θ := by gcongr
    _ = _ := by ring

lemma ennreal_half_ofReal {x : ℝ} (hx : 0≤x) :
    (ENNReal.ofReal x)^(1/2:ℝ)=ENNReal.ofReal (Real.sqrt x) := by
  rw [Real.sqrt_eq_rpow,ENNReal.ofReal_rpow_of_nonneg hx (by norm_num)]

lemma sqrt_energy_pair {a b E : ℝ} (ha : 0≤a) (hb : 0≤b) (hE : 0≤E) :
    Real.sqrt ((a*E)*(b*E))=Real.sqrt (a*b)*E := by
  rw [show (a*E)*(b*E)=(a*b)*E^2 by ring,Real.sqrt_mul (mul_nonneg ha hb),Real.sqrt_sq hE]

lemma source_far_energy_scalar {K b g E I p θ R r φ : ℝ}
    (hK : 0≤K) (hb : 0≤b) (hg : 0≤g) (hE : 0≤E) (hI : 0≤I)
    (hp : 0<p) (hθ : 0<θ) (hR : 0≤R) (hr : 0 < r) (hφ : 0<φ) (hθφ : θ^2≤φ) :
    K*(φ^2/(p*θ^2)*Real.sqrt ((20*E)*I)*Real.sqrt ((b*E)*p^2*θ^2*R^2/(r*φ^2)))+
    K*(φ/p*Real.sqrt ((40*E)*(I+2*r))*Real.sqrt ((g*E)*p^2*θ^2*R^2/(r*φ^2))) ≤
    K*(Real.sqrt (20*b)+Real.sqrt (40*g))*E*(Real.sqrt I*R*φ/(θ*Real.sqrt r)+2*R*θ) := by
  rw [source_far_good_scalar (by positivity) (mul_nonneg hb hE) hp hθ hR hr hφ,
    source_far_magnetic_scalar (by positivity) (mul_nonneg hg hE) hI hp hθ hR hr hφ,
    sqrt_energy_pair (by norm_num) hb hE,sqrt_energy_pair (by norm_num) hg hE]
  have hm := source_far_magnetic_le hI hθ hR hr hθφ
  calc
    _ = K*(Real.sqrt (20*b)*E*(Real.sqrt I*R*φ/(θ*Real.sqrt r)))+
        K*(Real.sqrt (40*g)*E*(R*θ*Real.sqrt (I/r+2))) := by ring
    _ ≤ K*(Real.sqrt (20*b)*E*(Real.sqrt I*R*φ/(θ*Real.sqrt r)+2*R*θ))+
        K*(Real.sqrt (40*g)*E*(Real.sqrt I*R*φ/(θ*Real.sqrt r)+2*R*θ)) := by
      gcongr
      exact le_add_of_nonneg_right (by positivity)
    _ = _ := by ring

lemma source_far_ennreal_scalar {K Cg Cb E I p θ r φ len : ℝ}
    (hK : 0≤K) (hCg : 0≤Cg) (hCb : 0≤Cb) (hE : 0≤E) (hI : 0<I)
    (hp : 0<p) (hθ : 0<θ) (hr : 0 < r) (hφ : 0<φ) (hlen : 0<len) (hθφ : θ^2≤φ) :
    let R := Real.sqrt (1+I/len)
    let mass := ENNReal.ofReal (568197120*E*(1+I/len)/(p*r*φ^2))
    ENNReal.ofReal (K*φ^2/(p*θ^2))*
      ((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*
        (ENNReal.ofReal (128*Cg*p^3*θ^2)*mass)^(1/2:ℝ))+
    ENNReal.ofReal (K*φ/p)*
      ((ENNReal.ofReal (40*(I+2*r)*E))^(1/2:ℝ)*
        (ENNReal.ofReal (128*Cb*p^3*θ^2)*mass)^(1/2:ℝ)) ≤
    ENNReal.ofReal (K*(Real.sqrt (20*(128*568197120*Cg))+Real.sqrt (40*(128*568197120*Cb)))*E*
      (Real.sqrt I*R*φ/(θ*Real.sqrt r)+2*R*θ)) := by
  dsimp only
  let R := Real.sqrt (1+I/len)
  have hR : 0≤R := Real.sqrt_nonneg _
  have hRsq : R^2=1+I/len := Real.sq_sqrt (by positivity)
  have he (C : ℝ) : (128*C*p^3*θ^2)*(568197120*E*(1+I/len)/(p*r*φ^2))=
      ((128*568197120*C)*E)*p^2*θ^2*R^2/(r*φ^2) := by
    rw [hRsq]
    field_simp [hp.ne',hr.ne',hφ.ne']
  rw [←ENNReal.ofReal_mul (by positivity : 0≤128*Cg*p^3*θ^2),
    ←ENNReal.ofReal_mul (by positivity : 0≤128*Cb*p^3*θ^2),he Cg,he Cb]
  rw [ennreal_half_ofReal (by positivity),ennreal_half_ofReal (by positivity),
    ennreal_half_ofReal (by positivity),ennreal_half_ofReal (by positivity)]
  rw [←ENNReal.ofReal_mul (Real.sqrt_nonneg _),←ENNReal.ofReal_mul (by positivity : 0≤K*φ^2/(p*θ^2)),
    ←ENNReal.ofReal_mul (Real.sqrt_nonneg _),←ENNReal.ofReal_mul (by positivity : 0≤K*φ/p),
    ←ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have h := source_far_energy_scalar hK (show 0≤128*568197120*Cg by positivity)
    (show 0≤128*568197120*Cb by positivity) hE hI.le hp hθ hR hr hφ hθφ
  convert h using 1; congr 1 <;> ring_nf

lemma Admissible.projected_source_baseline_radius_bound {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ, 0≤C ∧
    ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (S : Set Phase) (Q : Set (Fin 4→ℕ)) (k : Fin 4→ℕ)
        (a b I len w M A P L massScale Cs : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → 0 < len → len ≤ I → b-a ≤ I →
      0 < M → 0 ≤ A → 0 < P → 0 ≤ L → 0 < massScale → 0 < w → 128 ≤ Cs →
      massScale ≤ sourceRepresentative (k 0)/128 → massScale ≤ w/8 →
      cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 →
      32 ≤ cappedRepresentative (k 2)*w →
      2*len ≤ (Cs*(P/massScale)*(M/cappedRepresentative (k 2)+
        Real.sqrt (A*L/cappedRepresentative (k 2))))⁻¹^2 →
      (∀t∈Icc a b,w/16 ≤ ‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P L →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P L) →
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let r := max 1 T*cappedRepresentative (k 3)
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := representativeClosedBin T w k
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∫⁻z : ConeCoordinate,physicalProjectedSourceDensity s X V B T w Q z
        ∂physicalBinMeasure V B (Icc a b)) ≤
      ENNReal.ofReal (C*E*(Real.sqrt I*Real.sqrt (1+I/len)*φ/(θ*Real.sqrt r)+
        2*Real.sqrt (1+I/len)*θ)) := by
  obtain ⟨Cg,Cb,c,hCg,hCb,hc,hsource⟩ := hd₀.projected_source_baseline_far
  let K := 128*(3840+94080000*c)
  let C := K*(Real.sqrt (20*(128*568197120*Cg))+Real.sqrt (40*(128*568197120*Cb)))
  have hK : 0≤K := by dsimp [K]; positivity
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro s T F hs hT h0 zX S Q k a b I len w M A P L massScale Cs hS hS0 ha hb hlen hlenI hab
    hM hA hP hL hm hw hCs hmq hmw hsmall hwφ hstable hband HX HZ
  dsimp only
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let r := max 1 T*cappedRepresentative (k 3)
  let E := ∫x : Vec,totalEnergy s (0,x)
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hr : 0 < r := mul_pos (zero_lt_one.trans_le (le_max_left _ _)) (cappedRepresentative_pos _)
  have hE : 0≤E := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hI : 0<I := hlen.trans_le hlenI
  have hθφ : θ^2≤φ := by
    have hh : θ≤φ := by have h := hsmall; change θ≤φ/16 at h; linarith only [h,hφ]
    have h1 : θ≤1 := cappedRepresentative_le_one _
    simpa only [sq,mul_one] using mul_le_mul hh h1 hθ.le hφ.le
  have hbound := hsource s T F hs hT h0 zX S Q k a b I len w M A P L massScale Cs
    hS hS0 ha hb hlen hlenI hab hM hA hP hL hm hw hCs hmq hmw hsmall hwφ hstable hband HX HZ
  exact hbound.trans (source_far_ennreal_scalar hK hCg hCb hE hI hp hθ hr hφ hlen hθφ)

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_IndexTwoPow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma index_lt_of_two_pow_le {n N : ℕ} {B : ℝ}
    (hn : (2:ℝ)^n ≤ B) (hN : B < (2:ℝ)^N) : n<N := by
  by_contra hc
  have he := pow_le_pow_right₀ (show (1:ℝ)≤2 by norm_num) (Nat.le_of_not_gt hc)
  exact (not_lt_of_ge (he.trans hn)) hN

lemma cappedRepresentative_mul_pow (n : ℕ) : cappedRepresentative n*(2:ℝ)^n=1 := by
  simp [cappedRepresentative,inv_pow]

lemma direction_far_indices {P T : ℝ} {N : ℕ} {k : Fin 4→ℕ}
    (hP : 0 < P) (hp : sourceRepresentative (k 0) ≤ 128*P)
    (hθφ : cappedRepresentative (k 1) ≤ cappedRepresentative (k 2))
    (hfar : 1/32 ≤ sourceRepresentative (k 0)*cappedRepresentative (k 1)*
      Real.sqrt (max 1 T*cappedRepresentative (k 3)))
    (hN₀ : 2*P < (2:ℝ)^N)
    (hN₁ : 4096*P*Real.sqrt (max 1 T) < (2:ℝ)^N)
    (hN₃ : (4096*P)^2*max 1 T < (2:ℝ)^N) : ∀i,k i<N := by
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let H := max 1 T
  let r := H*cappedRepresentative (k 3)
  have hθ : 0 ≤ θ := (cappedRepresentative_pos _).le
  have hθ1 : θ ≤ 1 := cappedRepresentative_le_one _
  have hH : 0 ≤ H := (show (0:ℝ)≤1 by norm_num).trans (le_max_left _ _)
  have hr : 0 ≤ r := mul_nonneg hH (cappedRepresentative_pos _).le
  have hrH : r ≤ H := mul_le_of_le_one_right hH (cappedRepresentative_le_one _)
  have hsqrt : Real.sqrt r ≤ Real.sqrt H := Real.sqrt_le_sqrt hrH
  have hfp : 1/32 ≤ 128*P*θ*Real.sqrt r := hfar.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp hθ) (Real.sqrt_nonneg _))
  have hfθ : 1/32 ≤ 128*P*θ*Real.sqrt H := hfp.trans
    (mul_le_mul_of_nonneg_left hsqrt (by positivity))
  have hfφ : 1/32 ≤ 128*P*φ*Real.sqrt H := hfθ.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hθφ (by positivity)) (Real.sqrt_nonneg _))
  have hrfirst : 1/32 ≤ 128*P*Real.sqrt r := hfp.trans
    (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (by positivity) hθ1) (Real.sqrt_nonneg _))
  have hrbound : 1 ≤ (4096*P)^2*r := by
    have hsq := mul_self_le_mul_self (show (0:ℝ)≤1/32 by norm_num) hrfirst
    have hsq' : (1/32:ℝ)^2 ≤ (128*P*Real.sqrt r)^2 := by simpa only [pow_two] using hsq
    rw [mul_pow,Real.sq_sqrt hr] at hsq'
    nlinarith only [hsq']
  have hn0 : (2:ℝ)^(k 0) ≤ 2*P := by
    dsimp [sourceRepresentative] at hp
    linarith only [hp]
  have hn1 : (2:ℝ)^(k 1) ≤ 4096*P*Real.sqrt H := by
    have hh := mul_le_mul_of_nonneg_right hfθ (show (0:ℝ)≤2^(k 1) by positivity)
    have he : θ*(2:ℝ)^(k 1)=1 := cappedRepresentative_mul_pow _
    have hprod : 128*P*θ*Real.sqrt H*(2:ℝ)^(k 1)=128*P*Real.sqrt H := by
      calc
        _ = 128*P*Real.sqrt H*(θ*(2:ℝ)^(k 1)) := by ring
        _ = _ := by rw [he,mul_one]
    rw [hprod] at hh
    linarith only [hh]
  have hn2 : (2:ℝ)^(k 2) ≤ 4096*P*Real.sqrt H := by
    have hh := mul_le_mul_of_nonneg_right hfφ (show (0:ℝ)≤2^(k 2) by positivity)
    have he : φ*(2:ℝ)^(k 2)=1 := cappedRepresentative_mul_pow _
    have hprod : 128*P*φ*Real.sqrt H*(2:ℝ)^(k 2)=128*P*Real.sqrt H := by
      calc
        _ = 128*P*Real.sqrt H*(φ*(2:ℝ)^(k 2)) := by ring
        _ = _ := by rw [he,mul_one]
    rw [hprod] at hh
    linarith only [hh]
  have hn3 : (2:ℝ)^(k 3) ≤ (4096*P)^2*H := by
    have hh := mul_le_mul_of_nonneg_right hrbound (show (0:ℝ)≤2^(k 3) by positivity)
    have he : r*(2:ℝ)^(k 3)=H := by
      dsimp [r]
      rw [mul_assoc,cappedRepresentative_mul_pow,mul_one]
    rw [one_mul,mul_assoc,he] at hh
    exact hh
  intro i
  fin_cases i
  · exact index_lt_of_two_pow_le hn0 hN₀
  · exact index_lt_of_two_pow_le hn1 hN₁
  · exact index_lt_of_two_pow_le hn2 hN₁
  · exact index_lt_of_two_pow_le hn3 hN₃

end RVM

open Set

namespace RVM

lemma exists_dyadic_count_log {B : ℝ} (hB : 1 ≤ B) :
    ∃N : ℕ, B < (2:ℝ)^N ∧ (N:ℝ) ≤ 2+Real.log B/Real.log 2 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h0 : 0 ≤ Real.log B/Real.log 2 := div_nonneg (Real.log_nonneg hB) h2.le
  let n := ⌈Real.log B/Real.log 2⌉₊
  refine ⟨n+1,?_,?_⟩
  · apply (Real.log_lt_log_iff (zero_lt_one.trans_le hB) (by positivity)).mp
    rw [Real.log_pow,Nat.cast_add,Nat.cast_one]
    have hc : Real.log B/Real.log 2 < (n:ℝ)+1 := by
      have hh := Nat.le_ceil (Real.log B/Real.log 2)
      dsimp [n]
      linarith only [hh]
    exact (div_lt_iff₀ h2).mp hc
  · have hh : (n:ℝ) < Real.log B/Real.log 2+1 := Nat.ceil_lt_add_one h0
    push_cast
    linarith only [hh]

lemma exists_far_dyadic_count (T : ℝ) :
    ∃C : ℝ, 0 ≤ C ∧ ∀P : ℝ, 0 < P → 1 ≤ Real.log (2+P) →
      ∃N : ℕ, 2*P < (2:ℝ)^N ∧
        4096*P*Real.sqrt (max 1 T) < (2:ℝ)^N ∧
        (4096*P)^2*max 1 T < (2:ℝ)^N ∧
        (N:ℝ) ≤ C*Real.log (2+P) := by
  let H := max 1 T
  let D := 16777216*H
  let C := 2+Real.log D/Real.log 2+2/Real.log 2
  have hH1 : 1 ≤ H := le_max_left _ _
  have hH : 0 < H := zero_lt_one.trans_le hH1
  have hD1 : 1 ≤ D := by dsimp [D]; linarith only [hH1]
  have hD : 0 < D := zero_lt_one.trans_le hD1
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro P hP hL
  let B := D*(2+P)^2
  have hB1 : 1 ≤ B := by
    have hs : 1 ≤ (2+P)^2 := by nlinarith only [hP,sq_nonneg P]
    simpa only [one_mul] using (mul_le_mul hD1 hs (by norm_num) hD.le : (1:ℝ)*1 ≤ D*(2+P)^2)
  obtain ⟨N,hN,hNc⟩ := exists_dyadic_count_log hB1
  refine ⟨N,?_,?_,?_,?_⟩
  · have hh : 2*P < D*(2+P)^2 := by
      have hd : (2:ℝ) ≤ D := by dsimp [D]; linarith only [hH1]
      have hx : 2*(2+P)^2 ≤ D*(2+P)^2 := mul_le_mul_of_nonneg_right hd (sq_nonneg _)
      nlinarith only [hx,hP,sq_nonneg P]
    exact hh.trans hN
  · have hsH : 1 ≤ Real.sqrt H := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hH1
    have hsqH : (Real.sqrt H)^2=H := Real.sq_sqrt hH.le
    have hterm : 4096*P*Real.sqrt H < D*(2+P)^2 := by
      have hx : 0 ≤ P*(Real.sqrt H)*(Real.sqrt H-1) := mul_nonneg (mul_nonneg hP.le (Real.sqrt_nonneg _)) (sub_nonneg.mpr hsH)
      have hy : 0 ≤ H*P^2 := mul_nonneg hH.le (sq_nonneg _)
      dsimp [D]
      nlinarith only [hx,hy,hsqH,hH1,hP,mul_pos hP hH]
    exact hterm.trans hN
  · have hterm : (4096*P)^2*H < D*(2+P)^2 := by
      have hh : P^2 < (2+P)^2 := by nlinarith only [hP]
      have hm := mul_lt_mul_of_pos_left hh (show 0 < 16777216*H by positivity)
      dsimp [D]
      nlinarith only [hm]
    exact hterm.trans hN
  · have hlog : Real.log B=Real.log D+2*Real.log (2+P) := by
      dsimp [B]
      rw [Real.log_mul (ne_of_gt hD) (ne_of_gt (sq_pos_of_pos (by linarith only [hP]))),Real.log_pow]
      norm_num
    rw [hlog] at hNc
    apply hNc.trans
    have hcoeff : 0 ≤ 2+Real.log D/Real.log 2 := by positivity
    have hh := mul_le_mul_of_nonneg_left hL hcoeff
    dsimp [C]
    calc
      _ = (2+Real.log D/Real.log 2)+(2/Real.log 2)*Real.log (2+P) := by ring
      _ ≤ (2+Real.log D/Real.log 2)*Real.log (2+P)+(2/Real.log 2)*Real.log (2+P) := by linarith only [hh]
      _ = _ := by ring

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_QuadIndexEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma tsum_quad_index (f : (Fin 4→ℕ)→ℝ≥0∞) :
    (∑'k,f k)=∑'np,∑'nt,∑'nf,∑'nr,f ![np,nt,nf,nr] := by
  have h := quadIndexEquiv.symm.tsum_eq f
  rw [←h]
  simp only [ENNReal.tsum_prod']
  rfl

lemma ennreal_tsum_indicator_lt (N : ℕ) (c : ℝ≥0∞) :
    (∑'n : ℕ,if n<N then c else 0)=(N:ℝ≥0∞)*c := by
  classical
  calc
    _ = ∑n∈Finset.range N,if n<N then c else 0 := by
      apply tsum_eq_sum
      intro n hn
      exact ite_eq_right (fun h=>hn (Finset.mem_range.mpr h))
    _ = _ := by
      rw [Finset.sum_ite_of_true (fun n hn=>Finset.mem_range.mp hn)]
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ProjectedSourceStableFarBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.projected_source_stable_far_bound {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ, 0 ≤ C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (S : Set Phase) (Q : Set (Fin 4→ℕ)) (k : Fin 4→ℕ)
        (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → b-a ≤ (w/P)^2 →
      0 < M → 0 ≤ A → 0 < P → 1 ≤ Real.log (2+P) → 1 ≤ w → w ≤ P →
      sourceRepresentative (k 0) ≤ 128*P →
      cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 →
      32 ≤ cappedRepresentative (k 2)*w →
      1/32 ≤ sourceRepresentative (k 0)*cappedRepresentative (k 1)*
        Real.sqrt (max 1 T*cappedRepresentative (k 3)) →
      (∀t∈Icc a b,w/16 ≤ ‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := representativeClosedBin T w k
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∫⁻z : ConeCoordinate,physicalProjectedSourceDensity s X V B T w Q z
        ∂physicalBinMeasure V B (Icc a b)) ≤
      ENNReal.ofReal (C*E*(1+16384*(M+Real.sqrt A))*w*Real.sqrt (Real.log (2+P))) := by
  obtain ⟨C,hC,hbound⟩ := hd₀.projected_source_baseline_radius_bound
  refine ⟨8196*C,by positivity,?_⟩
  intro s T F hs hT h0 zX S Q k a b w M A P hS hS0 ha hb hab hM hA hP hL hw hwP
    hpP hsmall hwφ hfar hband HX HZ
  dsimp only
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let r := max 1 T*cappedRepresentative (k 3)
  let L := Real.log (2+P)
  let I := (w/P)^2
  let lam := stabilityLength P 16384 M A p w φ
  let len := min I (lam/2)
  let m := min p w/128
  let E := ∫x : Vec,totalEnergy s (0,x)
  have hp1 : 1 ≤ p := by
    have hh : (1:ℝ) ≤ 2^(k 0) := one_le_pow₀ (by norm_num)
    dsimp [p,sourceRepresentative]
    linarith only [hh]
  have hp : 0 < p := zero_lt_one.trans_le hp1
  have hw0 : 0 < w := zero_lt_one.trans_le hw
  have hθ : 0 < θ := cappedRepresentative_pos _
  have hφ : 0 < φ := cappedRepresentative_pos _
  have hr : 0 < r := mul_pos (zero_lt_one.trans_le (le_max_left _ _)) (cappedRepresentative_pos _)
  have hθφ : θ ≤ φ := by change θ≤φ/16 at hsmall; linarith only [hsmall,hφ]
  have hI : 0 < I := sq_pos_of_pos (div_pos hw0 hP)
  have hlam : 0 < lam := stabilityLength_pos hP (by norm_num) hM hp hw0 hφ
  have hlen : 0 < len := lt_min hI (by positivity)
  have hlenI : len ≤ I := min_le_left _ _
  have hlenlam : 2*len ≤ lam := by
    have hh : len ≤ lam/2 := min_le_right _ _
    linarith only [hh]
  have hm : 0 < m := div_pos (lt_min hp hw0) (by norm_num)
  have hmq : m ≤ p/128 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hmw : m ≤ w/8 := by
    have hh : min p w ≤ w := min_le_right _ _
    dsimp [m]
    linarith only [hh,hw0]
  have hstable : 2*len ≤ (128*(P/m)*(M/φ+Real.sqrt (A*L/φ)))⁻¹^2 := by
    dsimp only [m,L]
    rw [stability_massScale_identity]
    convert hlenlam using 1; norm_num [lam]
  have hbnd := hbound s T F hs hT h0 zX S Q k a b I len w M A P L m 128
    hS hS0 ha hb hlen hlenI hab hM hA hP (by dsimp [L]; linarith only [hL]) hm hw0 (by norm_num)
    hmq hmw hsmall hwφ hstable hband HX HZ
  have hscale := direction_source_far_scale hP hL (show (0:ℝ) < 16384 by norm_num)
    hM hA hp1 hw hθ hr hφ (cappedRepresentative_le_one _) hθφ hpP hwP hfar
  have hE : 0 ≤ E := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  apply hbnd.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ C*E*(8196*(1+16384*(M+Real.sqrt A))*w*Real.sqrt L) :=
      mul_le_mul_of_nonneg_left hscale (mul_nonneg hC hE)
    _ = _ := by dsimp [E,L]; ring

lemma tsum_quad_cutoff_bound (f : (Fin 4→ℕ)→ℝ≥0∞) (N : ℕ) (c : ℝ≥0∞)
    (h : ∀k,f k ≤ if ∀i,k i<N then c else 0) :
    (∑'k,f k) ≤ c*(N:ℝ≥0∞)^4 := by
  classical
  have he (np nt nf nr : ℕ) : (∀i : Fin 4,(![np,nt,nf,nr] : Fin 4→ℕ) i<N) ↔
      np<N ∧ nt<N ∧ nf<N ∧ nr<N := by simp [Fin.forall_fin_succ]
  calc
    _ ≤ ∑'k,if ∀i,k i<N then c else 0 := ENNReal.tsum_le_tsum h
    _ = ∑'np,∑'nt,∑'nf,∑'nr,if np<N ∧ nt<N ∧ nf<N ∧ nr<N then c else 0 := by
      rw [tsum_quad_index]
      simp_rw [he]
    _ = ∑'np,if np<N then ∑'nt,if nt<N then ∑'nf,if nf<N then ∑'nr,if nr<N then c else 0 else 0 else 0 else 0 := by
      apply tsum_congr
      intro np
      by_cases hp : np<N
      · simp only [hp,true_and,ite_true]
        apply tsum_congr
        intro nt
        by_cases ht : nt<N
        · simp only [ht,true_and,ite_true]
          apply tsum_congr
          intro nf
          by_cases hf : nf<N <;> simp [hf]
        · simp [ht]
      · simp [hp]
    _ = c*(N:ℝ≥0∞)^4 := by simp only [ennreal_tsum_indicator_lt]; ring

lemma Admissible.projected_source_stable_far_sum {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ, 0 ≤ C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (S : Set Phase) (Q : Set (Fin 4→ℕ)) (N : ℕ)
        (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → b-a ≤ (w/P)^2 →
      0 < M → 0 ≤ A → 0 < P → 1 ≤ Real.log (2+P) → 1 ≤ w → w ≤ P →
      (∀t∈Icc a b,w/16 ≤ ‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let sector : Set (Fin 4→ℕ) := {k | (∀i,k i<N) ∧ sourceRepresentative (k 0) ≤ 128*P ∧
        cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 ∧
        32 ≤ cappedRepresentative (k 2)*w ∧
        1/32 ≤ sourceRepresentative (k 0)*cappedRepresentative (k 1)*
          Real.sqrt (max 1 T*cappedRepresentative (k 3))}
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∑'k : Fin 4→ℕ,sector.indicator (fun k=>∫⁻z : ConeCoordinate,
        physicalProjectedSourceDensity s X V (representativeClosedBin T w k) T w Q z
          ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b)) k) ≤
      ENNReal.ofReal (C*E*(1+16384*(M+Real.sqrt A))*w*
        Real.sqrt (Real.log (2+P))*(N:ℝ)^4) := by
  classical
  obtain ⟨C,hC,hbound⟩ := hd₀.projected_source_stable_far_bound
  refine ⟨C,hC,?_⟩
  intro s T F hs hT h0 zX S Q N a b w M A P hS hS0 ha hb hab hM hA hP hL hw hwP hband HX HZ
  dsimp only
  let E := ∫x : Vec,totalEnergy s (0,x)
  let c := C*E*(1+16384*(M+Real.sqrt A))*w*Real.sqrt (Real.log (2+P))
  let sector : Set (Fin 4→ℕ) := {k | (∀i,k i<N) ∧ sourceRepresentative (k 0) ≤ 128*P ∧
    cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 ∧
    32 ≤ cappedRepresentative (k 2)*w ∧
    1/32 ≤ sourceRepresentative (k 0)*cappedRepresentative (k 1)*
      Real.sqrt (max 1 T*cappedRepresentative (k 3))}
  let f := sector.indicator (fun k=>∫⁻z : ConeCoordinate,
    physicalProjectedSourceDensity s (fun t=>(prefixFlow F.flow T zX t).1)
      (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) T w Q z
        ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2)
          (representativeClosedBin T w k) (Icc a b))
  have hE : 0 ≤ E := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hbin (k : Fin 4→ℕ) : f k ≤ if ∀i,k i<N then ENNReal.ofReal c else 0 := by
    by_cases hk : k∈sector
    · have he : f k = ∫⁻z : ConeCoordinate,
          physicalProjectedSourceDensity s (fun t=>(prefixFlow F.flow T zX t).1)
            (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) T w Q z
            ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2)
              (representativeClosedBin T w k) (Icc a b) := indicator_of_mem hk _
      rw [he,ite_eq_left hk.1]
      exact hbound s T F hs hT h0 zX S Q k a b w M A P hS hS0 ha hb hab hM hA hP hL hw hwP
        hk.2.1 hk.2.2.1 hk.2.2.2.1 hk.2.2.2.2 hband HX HZ
    · have he : f k=0 := indicator_of_notMem hk _
      rw [he]
      exact bot_le
  have hsum := tsum_quad_cutoff_bound f N (ENNReal.ofReal c) hbin
  apply hsum.trans_eq
  rw [show (N:ℝ≥0∞)^4=ENNReal.ofReal ((N:ℝ)^4) by
    rw [ENNReal.ofReal_pow (Nat.cast_nonneg N),ENNReal.ofReal_natCast],←ENNReal.ofReal_mul hc]

end RVM

end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.projected_source_stable_far_log_sum_oai {d : Datum} (hd₀ : Admissible d)
    (T₀ : ℝ) :
    ∃C : ℝ, 0 ≤ C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → T ≤ T₀ → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (S : Set Phase) (Q : Set (Fin 4→ℕ))
        (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → b-a ≤ (w/P)^2 →
      0 < M → 0 ≤ A → 0 < P → 1 ≤ Real.log (2+P) → 1 ≤ w → w ≤ P →
      (∀t∈Icc a b,w/16 ≤ ‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let sector : Set (Fin 4→ℕ) := {k | sourceRepresentative (k 0) ≤ 128*P ∧
        cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 ∧
        32 ≤ cappedRepresentative (k 2)*w ∧
        1/32 ≤ sourceRepresentative (k 0)*cappedRepresentative (k 1)*
          Real.sqrt (max 1 T*cappedRepresentative (k 3))}
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∑'k : Fin 4→ℕ,sector.indicator (fun k=>∫⁻z : ConeCoordinate,
        physicalProjectedSourceDensity s X V (representativeClosedBin T w k) T w Q z
          ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b)) k) ≤
      ENNReal.ofReal (C*E*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^5) := by
  classical
  obtain ⟨Cs,hCs,hsum⟩ := hd₀.projected_source_stable_far_sum
  obtain ⟨Cn,hCn,hcount⟩ := exists_far_dyadic_count T₀
  refine ⟨Cs*Cn^4,by positivity,?_⟩
  intro s T F hs hT hTT h0 zX S Q a b w M A P hS hS0 ha hb hab hM hA hP hL hw hwP
    hband HX HZ
  dsimp only
  let E := ∫x : Vec,totalEnergy s (0,x)
  let sector : Set (Fin 4→ℕ) := {k | sourceRepresentative (k 0) ≤ 128*P ∧
    cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 ∧
    32 ≤ cappedRepresentative (k 2)*w ∧
    1/32 ≤ sourceRepresentative (k 0)*cappedRepresentative (k 1)*
      Real.sqrt (max 1 T*cappedRepresentative (k 3))}
  obtain ⟨N,hN0,hN1,hN3,hNc⟩ := hcount P hP hL
  have hH : max (1:ℝ) T ≤ max 1 T₀ := max_le_max_left 1 hTT
  have hN1' : 4096*P*Real.sqrt (max 1 T) < (2:ℝ)^N :=
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hH) (by positivity)).trans_lt hN1
  have hN3' : (4096*P)^2*max 1 T < (2:ℝ)^N :=
    (mul_le_mul_of_nonneg_left hH (sq_nonneg _)).trans_lt hN3
  have hidx (k : Fin 4→ℕ) (hk : k∈sector) : ∀i,k i<N := by
    have hφ : 0 < cappedRepresentative (k 2) := cappedRepresentative_pos _
    have hθφ : cappedRepresentative (k 1) ≤ cappedRepresentative (k 2) := by
      have hh := hk.2.1
      linarith only [hh,hφ]
    exact direction_far_indices hP hk.1 hθφ hk.2.2.2 hN0 hN1' hN3'
  have heq : {k : Fin 4→ℕ | (∀i,k i<N) ∧ sourceRepresentative (k 0) ≤ 128*P ∧
      cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 ∧
      32 ≤ cappedRepresentative (k 2)*w ∧
      1/32 ≤ sourceRepresentative (k 0)*cappedRepresentative (k 1)*
        Real.sqrt (max 1 T*cappedRepresentative (k 3))} = sector := by
    ext k
    exact ⟨fun hk=>hk.2,fun hk=>⟨hidx k hk,hk⟩⟩
  have hbnd := hsum s T F hs hT h0 zX S Q N a b w M A P hS hS0 ha hb hab hM hA hP hL hw hwP
    hband HX HZ
  dsimp only at hbnd
  rw [heq] at hbnd
  have hE : 0 ≤ E := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hL0 : 0 ≤ Real.log (2+P) := zero_le_one.trans hL
  have hroot : Real.sqrt (Real.log (2+P)) ≤ Real.log (2+P) := Real.sqrt_le_self_iff.mpr (Or.inr hL)
  have hpower : (N:ℝ)^4 ≤ (Cn*Real.log (2+P))^4 := pow_le_pow_left₀ (Nat.cast_nonneg N) hNc _
  have hscalar : Real.sqrt (Real.log (2+P))*(N:ℝ)^4 ≤ Cn^4*(Real.log (2+P))^5 := by
    calc
      _ ≤ Real.log (2+P)*(Cn*Real.log (2+P))^4 := mul_le_mul hroot hpower (by positivity) hL0
      _ = _ := by ring
  apply hbnd.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = (Cs*E*(1+16384*(M+Real.sqrt A))*w)*(Real.sqrt (Real.log (2+P))*(N:ℝ)^4) := by ring
    _ ≤ (Cs*E*(1+16384*(M+Real.sqrt A))*w)*(Cn^4*(Real.log (2+P))^5) :=
      mul_le_mul_of_nonneg_left hscalar (by positivity)
    _ = _ := by dsimp [E]; ring

end RVM

end

end OAI
end

theorem solution : type_of% @OAI.RVM.Admissible.projected_source_stable_far_log_sum_oai := @OAI.RVM.Admissible.projected_source_stable_far_log_sum_oai
