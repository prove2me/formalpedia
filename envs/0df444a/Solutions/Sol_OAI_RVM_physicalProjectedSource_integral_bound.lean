-- Prove2me | solution 1 for OAI.RVM.physicalProjectedSource_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:39:47.203799+00:00
-- url     : https://prove2.me/submissions/815ed4e0-2f4d-4efb-bd2b-87b6b38609bc

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000

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

lemma q_sq (v : Vec) : q v ^ 2 = 1 + ‖v‖ ^ 2 := by
  exact Real.sq_sqrt (by positivity)

lemma norm_lt_q (v : Vec) : ‖v‖ < q v := by
  have hp := q_pos v
  have hs := q_sq v
  nlinarith [sq_nonneg ‖v‖, norm_nonneg v]

lemma norm_velocity_lt_one (v : Vec) : ‖velocity v‖ < 1 := by
  rw [velocity, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (q_pos v))]
  rw [← div_eq_inv_mul]
  exact (div_lt_one (q_pos v)).2 (norm_lt_q v)

lemma dot_comm (a b : Vec) : dot a b = dot b a := by
  simp only [dot, mul_comm]

lemma dot_add_left (a b c : Vec) : dot (a + b) c = dot a c + dot b c := by
  simp [dot, add_mul, Finset.sum_add_distrib]

lemma dot_sub_left (a b c : Vec) : dot (a - b) c = dot a c - dot b c := by
  simp [dot, sub_mul, Finset.sum_sub_distrib]

lemma dot_smul_left (r : ℝ) (a b : Vec) : dot (r • a) b = r * dot a b := by
  simp [dot, mul_assoc, Finset.mul_sum]

lemma dot_add_right (a b c : Vec) : dot a (b + c) = dot a b + dot a c := by
  rw [dot_comm, dot_add_left, dot_comm b a, dot_comm c a]

lemma dot_sub_right (a b c : Vec) : dot a (b - c) = dot a b - dot a c := by
  rw [dot_comm, dot_sub_left, dot_comm b a, dot_comm c a]

lemma dot_smul_right (r : ℝ) (a b : Vec) : dot a (r • b) = r * dot a b := by
  rw [dot_comm, dot_smul_left, dot_comm b a]

lemma dot_le_norm (a b : Vec) : dot a b ≤ ‖a‖ * ‖b‖ := by
  rw [dot_eq_inner]
  exact real_inner_le_norm a b

lemma cone_denom_pos (v n : Vec) (hn : ‖n‖ = 1) :
    0 < 1 - dot n (velocity v) := by
  have h := dot_le_norm n (velocity v)
  rw [hn, one_mul] at h
  linarith [norm_velocity_lt_one v]

lemma velocity_self (v : Vec) : dot (velocity v) (velocity v) = 1 - (q v)⁻¹ ^ 2 := by
  rw [velocity, dot_smul_left, dot_smul_right, dot_self]
  have hq := q_sq v
  have hn := ne_of_gt (q_pos v)
  field_simp
  nlinarith

lemma cone_angle_identity (v n : Vec) (hn : ‖n‖ = 1) :
    2 * (1 - dot n (velocity v)) = ‖n - velocity v‖ ^ 2 + (q v)⁻¹ ^ 2 := by
  rw [norm_sub_sq_real, ← dot_eq_inner, hn, ← dot_self (velocity v), velocity_self]
  ring

lemma hasDerivAt_dot {f g : ℝ → Vec} {f' g' : Vec} {s : ℝ}
    (hf : HasDerivAt f f' s) (hg : HasDerivAt g g' s) :
    HasDerivAt (fun t => dot (f t) (g t))
      (dot (f s) g' + dot f' (g s)) s := by
  simpa only [dot_eq_inner] using hf.inner ℝ hg

open scoped Topology

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_ExtendedLorentz
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace RVM
open scoped Topology

lemma hasDerivAt_particle_energy {V : ℝ → Vec} {K : Vec} {s : ℝ}
    (hV : HasDerivAt V K s) :
    HasDerivAt (fun t => q (V t)) (dot (velocity (V s)) K) s := by
  have hp : 1+‖V s‖^2 ≠ 0 := ne_of_gt (by positivity)
  have h := ((hV.norm_sq).const_add 1).sqrt hp
  convert h using 1 <;> try rfl
  rw [velocity, dot_smul_left, dot_eq_inner]
  dsimp [q]
  have hq : Real.sqrt (1+‖V s‖^2) ≠ 0 := ne_of_gt (q_pos (V s))
  field_simp

lemma hasDerivAt_particle_velocity {V : ℝ → Vec} {K : Vec} {s : ℝ}
    (hV : HasDerivAt V K s) :
    HasDerivAt (fun t => velocity (V t))
      ((q (V s))⁻¹ • (K-dot (velocity (V s)) K • velocity (V s))) s := by
  have hq := hasDerivAt_particle_energy hV
  have h := (hq.inv (ne_of_gt (q_pos (V s)))).smul hV
  convert h using 1 <;> try rfl
  ext i
  simp only [Pi.inv_apply, velocity, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

lemma dot_cross_self_left (a b : Vec) : dot a (cross a b) = 0 := by
  simp [dot, cross, Fin.sum_univ_succ]
  ring

lemma hasDerivAt_lorentz_energy {V : ℝ → Vec} {E B : Vec} {s : ℝ}
    (hV : HasDerivAt V (E+cross (velocity (V s)) B) s) :
    HasDerivAt (fun t => q (V t)) (dot (velocity (V s)) E) s := by
  simpa only [dot_add_right, dot_cross_self_left, add_zero] using hasDerivAt_particle_energy hV

lemma contDiff_q {k : ℕ∞ω} : ContDiff ℝ k q := by
  exact ((contDiff_const : ContDiff ℝ k (fun _ : Vec => (1 : ℝ))).add
    (contDiff_id.norm_sq ℝ)).sqrt (fun v => by positivity)

lemma contDiff_velocity {k : ℕ∞ω} : ContDiff ℝ k velocity := by
  exact (contDiff_q.inv (fun v => ne_of_gt (q_pos v))).smul contDiff_id

lemma contDiff_cross {k : ℕ∞ω} : ContDiff ℝ k (fun z : Vec × Vec => cross z.1 z.2) := by
  apply contDiff_euclidean.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ k (fun z : Vec × Vec => z.1 1 * z.2 2 - z.1 2 * z.2 1)
    fun_prop
  · change ContDiff ℝ k (fun z : Vec × Vec => z.1 2 * z.2 0 - z.1 0 * z.2 2)
    fun_prop
  · change ContDiff ℝ k (fun z : Vec × Vec => z.1 0 * z.2 1 - z.1 1 * z.2 0)
    fun_prop

lemma fderiv_velocity_apply (v h : Vec) :
    fderiv ℝ velocity v h = (q v)⁻¹ • (h-dot (velocity v) h • velocity v) := by
  have hc : HasDerivAt (fun r : ℝ => v+r • h) h 0 := by
    have hh := (hasDerivAt_const (0 : ℝ) v).add
      ((hasDerivAt_id (0 : ℝ)).smul_const h)
    change HasDerivAt (fun r : ℝ => v+r • h) (0+(1 : ℝ) • h) 0 at hh
    simpa only [zero_add, one_smul] using hh
  have hv : HasFDerivAt velocity (fderiv ℝ velocity v) (v+(0 : ℝ) • h) := by
    simpa only [zero_smul, add_zero] using
      (contDiff_velocity.differentiable (by simp : (1 : ℕ∞ω) ≠ 0) v).hasFDerivAt
  have h₁ := hv.comp_hasDerivAt 0 hc
  have h₂ := hasDerivAt_particle_velocity hc
  have he := h₁.unique h₂
  simpa using he

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ConeArgument
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
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
open Set MeasureTheory Filter
open scoped Topology NNReal
open scoped Topology ContDiff
open Set MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma sphere_norm (n : Sphere) : ‖n.1‖ = 1 := by
  simpa only [mem_sphere,dist_zero_right] using n.2

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_BallCutoff
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
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
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma continuous_dot : Continuous (fun p : Vec × Vec => dot p.1 p.2) := by
  simp only [dot_eq_inner]
  exact continuous_fst.inner continuous_snd

end RVM
end

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
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Continuation_PrefixClamp
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
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma prefixClamp_mem {T : ℝ} (hT : 0≤T) (t : ℝ) : prefixClamp T t∈Icc 0 T :=
  ⟨le_max_left _ _,max_le hT (min_le_left _ _)⟩

lemma prefixClamp_eq {T t : ℝ} (ht : t∈Icc 0 T) : prefixClamp T t=t := by
  simp [prefixClamp,min_eq_right ht.2,max_eq_right ht.1]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_RetardedSameTimeSeparation
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
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal RealInnerProductSpace

namespace RVM

lemma norm_sub_le_of_deficit {u a : Vec} {δ : ℝ} (hu : ‖u‖≤1) (ha : ‖a‖≤1)
    (hδ : 0≤δ) (hd : 1-dot u a≤δ^2/2) : ‖u-a‖≤δ := by
  have he : ‖u-a‖^2=‖u‖^2+‖a‖^2-2*dot u a := by rw [norm_sub_sq_real,dot_eq_inner]; ring
  have hu2 : ‖u‖^2≤1 := by nlinarith [norm_nonneg u]
  have ha2 : ‖a‖^2≤1 := by nlinarith [norm_nonneg a]
  nlinarith [norm_nonneg (u-a)]

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
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

namespace RVM

lemma measurableSet_coneBinMomentumSet (B : ClosedConeBin) (n a : Vec) :
    MeasurableSet (coneBinMomentumSet B n a) := by
  exact ((measurableSet_Icc.preimage (contDiff_q (k:=0)).continuous.measurable).inter
    ((measurableSet_Icc.preimage (continuous_const.sub (continuous_dot.comp
      (continuous_const.prodMk (contDiff_velocity (k:=0)).continuous))).measurable).inter
      (measurableSet_Icc.preimage (continuous_const.sub (continuous_dot.comp
      (continuous_const.prodMk (contDiff_velocity (k:=0)).continuous))).measurable)))

lemma measurableSet_physicalBinBase {V : ℝ → Vec} (hV : Measurable V)
    (B : ClosedConeBin) {J : Set ℝ} (hJ : MeasurableSet J) :
    MeasurableSet (physicalBinBase V B J) := by
  have htime : MeasurableSet {z : ConeCoordinate | z.2.1 ∈ Icc 0 z.1} :=
    (measurableSet_le measurable_const (measurable_fst.comp measurable_snd)).inter
      (measurableSet_le (measurable_fst.comp measurable_snd) measurable_fst)
  exact (hJ.preimage measurable_fst).inter (htime.inter
    ((measurableSet_Icc.preimage (measurable_fst.sub (measurable_fst.comp measurable_snd))).inter
      ((measurableSet_Icc.preimage ((contDiff_q (k:=0)).continuous.measurable.comp
        (hV.comp measurable_fst))).inter
      (measurableSet_Icc.preimage (measurable_const.sub (continuous_dot.measurable.comp
        ((measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)).prodMk
          ((contDiff_velocity (k:=0)).continuous.measurable.comp (hV.comp measurable_fst)))))))))

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_NullConeFlux
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
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
open Set MeasureTheory Filter
open scoped Topology NNReal
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory Metric
open scoped Topology Pointwise

namespace RVM

lemma velocityProjection_add (u b c : Vec) :
    velocityProjection u (b+c) = velocityProjection u b + velocityProjection u c := by
  simp only [velocityProjection,dot_add_right,add_smul]
  module

lemma velocityProjection_norm (u b : Vec) (hu : ‖u‖ ≤ 1) :
    ‖velocityProjection u b‖ ≤ ‖b‖ := by
  have hsq : ‖u‖^2 ≤ 1 := by nlinarith [norm_nonneg u]
  have he : ‖velocityProjection u b‖^2 =
      ‖b‖^2 - 2*(dot u b)^2+(dot u b)^2*‖u‖^2 := by
    rw [velocityProjection,norm_sub_sq_real,norm_smul,Real.norm_eq_abs,
      mul_pow,sq_abs,inner_smul_right,← dot_eq_inner,dot_comm b u]
    ring
  have hh := mul_le_mul_of_nonneg_left hsq (sq_nonneg (dot u b))
  nlinarith [norm_nonneg (velocityProjection u b), norm_nonneg b]

lemma velocityProjection_dot_symm (u b n : Vec) :
    dot n (velocityProjection u b) = dot (velocityProjection u n) b := by
  simp only [velocityProjection,dot_sub_right,dot_sub_left,dot_smul_left,dot_smul_right]
  rw [dot_comm n u]
  ring

lemma norm_velocityProjection_normal (u n : Vec) (hu : ‖u‖ ≤ 1) (hn : ‖n‖=1) :
    ‖velocityProjection u n‖ ≤ Real.sqrt (2*(1-dot n u)) := by
  have hs : ‖u‖^2 ≤ 1 := by nlinarith [norm_nonneg u]
  have hdot := dot_le_norm n u
  rw [hn,one_mul] at hdot
  have hd : 0 ≤ 2*(1-dot n u) := by linarith
  have he : ‖velocityProjection u n‖^2 =
      1-2*(dot n u)^2+(dot n u)^2*‖u‖^2 := by
    rw [velocityProjection,norm_sub_sq_real,norm_smul,Real.norm_eq_abs,
      mul_pow,sq_abs,inner_smul_right,← dot_eq_inner,dot_comm u n,hn]
    ring
  have hh := mul_le_mul_of_nonneg_left hs (sq_nonneg (dot n u))
  have hsq := Real.sq_sqrt hd
  nlinarith [Real.sqrt_nonneg (2*(1-dot n u)),sq_nonneg (1-dot n u)]

lemma cross_sub_left (a b c : Vec) : cross (a-b) c = cross a c-cross b c := by
  ext i
  fin_cases i <;> simp [cross] <;> ring

lemma cross_normal_decomposition (u n B : Vec) :
    dot n n • cross u B = dot n u • cross n B +
      dot n (cross u B) • n + dot n B • cross u n := by
  ext i
  fin_cases i <;> simp [cross,dot,Fin.sum_univ_succ] <;> ring

lemma magnetic_projection_identity (u n B : Vec) (hn : ‖n‖=1) :
    velocityProjection u (cross (u-n) B) =
      -(1-dot n u) • cross n B - dot n (cross (u-n) B) • (u-n) +
        dot n B • cross u n := by
  have hn' : dot n n=1 := by rw [dot_self,hn]; norm_num
  have hd := cross_normal_decomposition u n B
  rw [hn',one_smul] at hd
  have hc : dot u (cross (u-n) B) = dot n (cross (u-n) B) := by
    have hh := dot_cross_self_left (u-n) B
    rw [dot_sub_left] at hh
    linarith
  unfold velocityProjection
  rw [hc,cross_sub_left]
  have he : dot n (cross u B-cross n B) = dot n (cross u B) := by
    rw [dot_sub_right,dot_cross_self_left,sub_zero]
  rw [he]
  ext i
  have hi := congrArg (fun w : Vec => w i) hd
  simp only [PiLp.sub_apply,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul] at hi ⊢
  linear_combination hi

lemma magnetic_projection_normal_identity (u n B : Vec) :
    dot n (velocityProjection u (cross (u-n) B)) =
      (1-dot n u)*dot n (cross (u-n) B) := by
  have hc : dot u (cross (u-n) B) = dot n (cross (u-n) B) := by
    have hh := dot_cross_self_left (u-n) B
    rw [dot_sub_left] at hh
    linarith
  simp only [velocityProjection,dot_sub_right,dot_smul_right,hc]
  ring

lemma abs_dot_le (a b : Vec) : |dot a b| ≤ ‖a‖*‖b‖ := by
  rw [dot_eq_inner]
  exact abs_real_inner_le_norm a b

lemma velocity_normal_distance_bound (v n : Vec) (hn : ‖n‖=1) :
    ‖velocity v-n‖ ≤ Real.sqrt (2*(1-dot n (velocity v))) := by
  have hi := cone_angle_identity v n hn
  rw [norm_sub_rev] at hi
  have hd := (cone_denom_pos v n hn).le
  have hh := Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hd)
  nlinarith [sq_nonneg ((q v)⁻¹), Real.sqrt_nonneg (2*(1-dot n (velocity v))),
    norm_nonneg (velocity v-n)]

lemma source_energy_rate_bound (v E B n : Vec) (hn : ‖n‖=1) :
    |dot (velocity v) E| ≤ goodField E B n +
      Real.sqrt (2*(1-dot n (velocity v)))*‖B‖ := by
  let u := velocity v
  have he : dot u E = dot u (E+cross n B)-dot (u-n) (cross n B) := by
    rw [dot_add_right,dot_sub_left,dot_cross_self_left]
    ring
  have hh := (abs_sub _ _).trans (add_le_add (abs_dot_le u (E+cross n B))
    (abs_dot_le (u-n) (cross n B)))
  rw [← he] at hh
  have hu : ‖u‖ ≤ 1 := (norm_velocity_lt_one v).le
  have hcross : ‖cross n B‖ ≤ ‖B‖ := by simpa only [hn,one_mul] using norm_cross_le n B
  have hb := mul_le_mul (velocity_normal_distance_bound v n hn) hcross
    (norm_nonneg _) (Real.sqrt_nonneg _)
  have hg := mul_le_mul_of_nonneg_right hu (norm_nonneg (E+cross n B))
  dsimp [goodField]
  dsimp only [u] at hh hg
  linarith [abs_nonneg (dot n B)]

lemma magnetic_projection_bound (v n B : Vec) (hn : ‖n‖=1) :
    ‖velocityProjection (velocity v) (cross (velocity v-n) B)‖ ≤
      3*(1-dot n (velocity v))*‖B‖+|dot n B| := by
  let u := velocity v
  let d := 1-dot n u
  let θ := Real.sqrt (2*d)
  have hd : 0 ≤ d := (cone_denom_pos v n hn).le
  have ht : 0 ≤ θ := Real.sqrt_nonneg _
  have ht2 : θ^2=2*d := Real.sq_sqrt (by positivity)
  have hk : ‖u-n‖ ≤ θ := velocity_normal_distance_bound v n hn
  have hb : ‖cross n B‖ ≤ ‖B‖ := by simpa only [hn,one_mul] using norm_cross_le n B
  have hcn : ‖cross u n‖ ≤ 1 := by
    have hh := norm_cross_le u n
    rw [hn,mul_one] at hh
    exact hh.trans (norm_velocity_lt_one v).le
  have hc : |dot n (cross (u-n) B)| ≤ θ*‖B‖ := by
    have hh := abs_dot_le n (cross (u-n) B)
    rw [hn,one_mul] at hh
    exact hh.trans ((norm_cross_le (u-n) B).trans
      (mul_le_mul_of_nonneg_right hk (norm_nonneg B)))
  have hmul := mul_le_mul hc hk (norm_nonneg _) (mul_nonneg ht (norm_nonneg B))
  have hmul' : |dot n (cross (u-n) B)| *‖u-n‖ ≤ 2*d*‖B‖ := by
    calc
      _ ≤ θ*‖B‖*θ := hmul
      _ = θ^2*‖B‖ := by ring
      _ = 2*d*‖B‖ := by rw [ht2]
  have htri := norm_add_le (-(1-dot n u) • cross n B -
      dot n (cross (u-n) B) • (u-n)) (dot n B • cross u n)
  rw [magnetic_projection_identity _ _ _ hn]
  have hsub := norm_sub_le (-(1-dot n u) • cross n B)
    (dot n (cross (u-n) B) • (u-n))
  simp only [norm_smul,Real.norm_eq_abs,abs_neg] at htri hsub
  rw [abs_of_nonneg hd] at hsub
  have hh₁ := mul_le_mul_of_nonneg_left hb hd
  have hh₂ := mul_le_mul_of_nonneg_left hcn (abs_nonneg (dot n B))
  dsimp only [u,d] at *
  linarith

lemma lorentz_source_acceleration_bound (v E B n : Vec) (hn : ‖n‖=1) :
    ‖fderiv ℝ velocity v (E+cross (velocity v) B)‖ ≤
      (q v)⁻¹*(goodField E B n+3*(1-dot n (velocity v))*‖B‖) := by
  rw [fderiv_velocity_apply,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (q_pos v))]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (q_pos v).le)
  have he : E+cross (velocity v) B =
      (E+cross n B)+cross (velocity v-n) B := by
    rw [cross_sub_left]
    module
  change ‖velocityProjection (velocity v) (E+cross (velocity v) B)‖ ≤ _
  rw [he,velocityProjection_add]
  have ht := norm_add_le (velocityProjection (velocity v) (E+cross n B))
      (velocityProjection (velocity v) (cross (velocity v-n) B))
  have hg := velocityProjection_norm (velocity v) (E+cross n B) (norm_velocity_lt_one v).le
  have hb := magnetic_projection_bound v n B hn
  dsimp only [goodField]
  linarith

lemma lorentz_source_normal_acceleration_bound (v E B n : Vec) (hn : ‖n‖=1) :
    |dot n (fderiv ℝ velocity v (E+cross (velocity v) B))| ≤
      (q v)⁻¹*Real.sqrt (2*(1-dot n (velocity v)))*
        (goodField E B n+(1-dot n (velocity v))*‖B‖) := by
  let u := velocity v
  let d := 1-dot n u
  let θ := Real.sqrt (2*d)
  have hd : 0 ≤ d := (cone_denom_pos v n hn).le
  have ht : 0 ≤ θ := Real.sqrt_nonneg _
  have he : E+cross u B = (E+cross n B)+cross (u-n) B := by
    rw [cross_sub_left]
    module
  have hg : |dot n (velocityProjection u (E+cross n B))| ≤ θ*‖E+cross n B‖ := by
    rw [velocityProjection_dot_symm]
    exact (abs_dot_le _ _).trans (mul_le_mul_of_nonneg_right
      (norm_velocityProjection_normal u n (norm_velocity_lt_one v).le hn) (norm_nonneg _))
  have hb : |dot n (velocityProjection u (cross (u-n) B))| ≤ d*θ*‖B‖ := by
    rw [magnetic_projection_normal_identity,abs_mul,abs_of_nonneg hd]
    have hc : |dot n (cross (u-n) B)| ≤ θ*‖B‖ := by
      have hh := abs_dot_le n (cross (u-n) B)
      rw [hn,one_mul] at hh
      exact hh.trans ((norm_cross_le _ _).trans (mul_le_mul_of_nonneg_right
        (velocity_normal_distance_bound v n hn) (norm_nonneg _)))
    nlinarith [mul_le_mul_of_nonneg_left hc hd]
  have hsum : |dot n (velocityProjection u (E+cross u B))| ≤
      θ*(goodField E B n+d*‖B‖) := by
    rw [he,velocityProjection_add,dot_add_right]
    have hh := abs_add_le (dot n (velocityProjection u (E+cross n B)))
      (dot n (velocityProjection u (cross (u-n) B)))
    dsimp only [goodField]
    nlinarith [mul_nonneg ht (abs_nonneg (dot n B))]
  rw [fderiv_velocity_apply,dot_smul_right,abs_mul,
    abs_of_pos (inv_pos.mpr (q_pos v))]
  have h := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (q_pos v).le)
  convert! h using 1; ring

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Continuation_PrefixParticle
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
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

namespace RVM

lemma EnergyPrefix.continuous_prefixParticle {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) (hT : 0 ≤ T) : Continuous (prefixParticle s T) :=
  hs.f_smooth.continuousOn.comp_continuous
    ((continuous_const.max (continuous_const.min continuous_fst)).prodMk continuous_snd)
    (fun p => ⟨prefixClamp_mem hT p.1,mem_univ _⟩)

lemma continuous_prefixField {E : Field} {T : ℝ}
    (hE : ContinuousOn E (Icc 0 T ×ˢ (univ : Set Vec))) (hT : 0 ≤ T) :
    Continuous (prefixField E T) :=
  hE.comp_continuous
    ((continuous_const.max (continuous_const.min continuous_fst)).prodMk continuous_snd)
    (fun p => ⟨prefixClamp_mem hT p.1,mem_univ _⟩)

lemma measurable_coneBinDensity {g : Particle} (hg : Measurable g)
    {X V : ℝ → Vec} (hX : Measurable X) (hV : Measurable V) (B : ClosedConeBin) :
    Measurable (fun z : ConeCoordinate => ∫⁻ v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
      ENNReal.ofReal (g (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v)))) := by
  let H : Set (ConeCoordinate × Vec) :=
    {p | p.2∈coneBinMomentumSet B p.1.2.2.1 (velocity (V p.1.1))}
  have hn : Measurable (fun p : ConeCoordinate × Vec => p.1.2.2.1) :=
    measurable_subtype_coe.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))
  have hv : Measurable (fun p : ConeCoordinate × Vec => velocity p.2) :=
    (contDiff_velocity (k:=0)).continuous.measurable.comp measurable_snd
  have ha : Measurable (fun p : ConeCoordinate × Vec => velocity (V p.1.1)) :=
    (contDiff_velocity (k:=0)).continuous.measurable.comp (hV.comp (measurable_fst.comp measurable_fst))
  have hH : MeasurableSet H := by
    exact (measurableSet_Icc.preimage ((contDiff_q (k:=0)).continuous.measurable.comp measurable_snd)).inter
      ((measurableSet_Icc.preimage (measurable_const.sub (continuous_dot.measurable.comp (hn.prodMk hv)))).inter
        (measurableSet_Icc.preimage (measurable_const.sub (continuous_dot.measurable.comp (ha.prodMk hv)))))
  have hf : Measurable (fun p : ConeCoordinate × Vec =>
      ENNReal.ofReal (g (p.1.2.1,(X p.1.1-(p.1.1-p.1.2.1) • p.1.2.2.1,p.2)))) := by
    exact (hg.comp ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
      (((hX.comp (measurable_fst.comp measurable_fst)).sub
        (((measurable_fst.comp measurable_fst).sub (measurable_fst.comp (measurable_snd.comp measurable_fst))).smul hn)).prodMk
        measurable_snd))).ennreal_ofReal
  have hm : Measurable (fun z : ConeCoordinate =>
      ∫⁻ v : Vec, H.indicator (fun p => ENNReal.ofReal (g (p.1.2.1,
        (X p.1.1-(p.1.1-p.1.2.1) • p.1.2.2.1,p.2)))) (z,v)) :=
    (hf.indicator hH).lintegral_prod_right'
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  rw [← lintegral_indicator (measurableSet_coneBinMomentumSet B _ _)]
  apply lintegral_congr
  intro v
  rfl

lemma physicalBinDensity_aemeasurable {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
    (hT : 0 ≤ T) {X V : ℝ → Vec} (hX : Measurable X) (hV : Measurable V)
    (B : ClosedConeBin) {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T) :
    AEMeasurable (fun z : ConeCoordinate => physicalBinDensity s X V B z.1 z.2.1 z.2.2)
      (physicalBinMeasure V B J) := by
  have hm := (measurable_coneBinDensity (hs.continuous_prefixParticle hT).measurable hX hV B).aemeasurable
    (μ := physicalBinMeasure V B J)
  apply hm.congr
  apply ae_restrict_of_forall_mem (measurableSet_physicalBinBase hV B hJ)
  intro z hz
  unfold physicalBinDensity
  apply lintegral_congr
  intro v
  rw [prefixParticle,prefixClamp_eq (show z.2.1∈Icc 0 T from ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩)]

lemma EnergyPrefix.measurable_prefixConeGood {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) (hT : 0 ≤ T) {X : ℝ → Vec} (hX : Measurable X) :
    Measurable (prefixConeGood s T X) := by
  have hn : Measurable (fun z : ConeCoordinate => z.2.2.1) :=
    measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)
  have hy : Measurable (fun z : ConeCoordinate =>
      (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1)) :=
    (measurable_fst.comp measurable_snd).prodMk
      ((hX.comp measurable_fst).sub ((measurable_fst.sub (measurable_fst.comp measurable_snd)).smul hn))
  have hE := (continuous_prefixField hs.E_smooth.continuousOn hT).measurable.comp hy
  have hB := (continuous_prefixField hs.B_smooth.continuousOn hT).measurable.comp hy
  exact (hE.add ((contDiff_cross (k:=0)).continuous.measurable.comp (hn.prodMk hB))).norm.add
    (continuous_dot.measurable.comp (hn.prodMk hB)).abs

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ReceiverQ
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
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
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma sourceNumerator_tangent (n u b : Vec) (hn : ‖n‖=1) :
    dot n (sourceNumerator n u b)=0 := by
  simp only [sourceNumerator,dot_sub_right,dot_smul_right,dot_self,hn,one_pow]
  ring

lemma sourceNumerator_bound (v E B n : Vec) (hn : ‖n‖=1) :
    ‖sourceNumerator n (velocity v) (fderiv ℝ velocity v (E+cross (velocity v) B))‖ ≤
      5*(1-dot n (velocity v))*(q v)⁻¹*(goodField E B n+(1-dot n (velocity v))*‖B‖) := by
  let d := 1-dot n (velocity v)
  let b := fderiv ℝ velocity v (E+cross (velocity v) B)
  have hd : 0≤d := (cone_denom_pos v n hn).le
  have hq : 0≤(q v)⁻¹ := (inv_pos.mpr (q_pos v)).le
  have hG : 0≤goodField E B n := add_nonneg (norm_nonneg _) (abs_nonneg _)
  have hb := lorentz_source_acceleration_bound v E B n hn
  have hnb := lorentz_source_normal_acceleration_bound v E B n hn
  have hnu : ‖n-velocity v‖≤Real.sqrt (2*d) := by
    rw [norm_sub_rev]
    exact velocity_normal_distance_bound v n hn
  have hprod : |dot n b| *‖n-velocity v‖ ≤
      (q v)⁻¹*(2*d)*(goodField E B n+d*‖B‖) := by
    calc
      _ ≤ ((q v)⁻¹*Real.sqrt (2*d)*(goodField E B n+d*‖B‖))*Real.sqrt (2*d) :=
        mul_le_mul hnb hnu (norm_nonneg _) (by positivity)
      _ = (q v)⁻¹*(Real.sqrt (2*d))^2*(goodField E B n+d*‖B‖) := by ring
      _ = _ := by rw [Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ)≤2) hd)]
  have hdb := mul_le_mul_of_nonneg_left hb hd
  calc
    _ ≤ |dot n b| *‖n-velocity v‖+d*‖b‖ := by
      exact (norm_sub_le _ _).trans (by rw [norm_smul,norm_smul,Real.norm_eq_abs,
        Real.norm_eq_abs,abs_of_nonneg hd])
    _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hd hq) hG]

lemma transverseProjection_norm (w h : Vec) : ‖transverseProjection w h‖≤‖h‖ := by
  apply velocityProjection_norm
  by_cases hw : w=0
  · simp [hw]
  · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg w)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]

lemma velocityProjection_smul (u h : Vec) (c : ℝ) :
    velocityProjection u (c • h)=c • velocityProjection u h := by
  simp only [velocityProjection,dot_smul_right,smul_sub,smul_smul]

lemma transverseProjection_velocity (w : Vec) : transverseProjection w (velocity w)=0 := by
  by_cases hw : w=0
  · simp [hw,transverseProjection,velocityProjection,velocity,dot]
  · have hn := norm_ne_zero_iff.mpr hw
    ext i
    simp only [transverseProjection,velocityProjection,velocity,dot_smul_left,dot_smul_right,
      dot_self,PiLp.sub_apply,PiLp.smul_apply,PiLp.zero_apply,smul_eq_mul]
    field_simp
    ring

lemma transverseProjection_normal_bound (w n : Vec) (hn : ‖n‖=1) :
    ‖transverseProjection w n‖≤Real.sqrt (2*(1-dot n (velocity w))) := by
  have he : transverseProjection w n=transverseProjection w (n-velocity w) := by
    have h := velocityProjection_add (‖w‖⁻¹ • w) (n-velocity w) (velocity w)
    rw [sub_add_cancel] at h
    change transverseProjection w n=transverseProjection w (n-velocity w)+transverseProjection w (velocity w) at h
    rwa [transverseProjection_velocity,add_zero] at h
  rw [he]
  exact (transverseProjection_norm _ _).trans (by simpa only [norm_sub_rev] using velocity_normal_distance_bound w n hn)

lemma transverse_receiverQ_tangent_bound (w n h : Vec) (hn : ‖n‖=1) (hh : dot n h=0) :
    ‖transverseProjection w (receiverQ (velocity w) n h)‖≤3*(1-dot n (velocity w))*‖h‖ := by
  let D := 1-dot n (velocity w)
  have hD : 0≤D := (cone_denom_pos w n hn).le
  have ha : |dot (velocity w) h|≤Real.sqrt (2*D)*‖h‖ := by
    rw [show dot (velocity w) h=dot (velocity w-n) h by rw [dot_sub_left,hh,sub_zero]]
    exact (abs_dot_le _ _).trans (mul_le_mul_of_nonneg_right
      (velocity_normal_distance_bound w n hn) (norm_nonneg h))
  have hp := transverseProjection_normal_bound w n hn
  have he : transverseProjection w (receiverQ (velocity w) n h)=
      D • transverseProjection w h+dot (velocity w) h • transverseProjection w n := by
    exact (velocityProjection_add _ _ _).trans
      (congrArg₂ (·+·) (velocityProjection_smul _ _ _) (velocityProjection_smul _ _ _))
  rw [he]
  calc
    _ ≤ ‖D • transverseProjection w h‖+‖dot (velocity w) h • transverseProjection w n‖ := norm_add_le _ _
    _ = D*‖transverseProjection w h‖+|dot (velocity w) h| *‖transverseProjection w n‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hD]
    _ ≤ D*‖h‖+(Real.sqrt (2*D)*‖h‖)*Real.sqrt (2*D) :=
      add_le_add (mul_le_mul_of_nonneg_left (transverseProjection_norm _ _) hD)
        (mul_le_mul ha hp (norm_nonneg _) (by positivity))
    _ = D*‖h‖+(Real.sqrt (2*D))^2*‖h‖ := by ring
    _ = _ := by rw [Real.sq_sqrt (by positivity : 0≤2*D)]; ring

lemma transverse_receiverQ_source_bound (w v E B n : Vec) (hn : ‖n‖=1) :
    ‖transverseProjection w (receiverQ (velocity w) n
        (sourceNumerator n (velocity v) (fderiv ℝ velocity v (E+cross (velocity v) B))))‖ ≤
      15*(1-dot n (velocity w))*(1-dot n (velocity v))*(q v)⁻¹*
        (goodField E B n+(1-dot n (velocity v))*‖B‖) := by
  apply (transverse_receiverQ_tangent_bound _ _ _ hn (sourceNumerator_tangent _ _ _ hn)).trans
  convert mul_le_mul_of_nonneg_left (sourceNumerator_bound v E B n hn)
    (show 0≤3*(1-dot n (velocity w)) by positivity [cone_denom_pos w n hn]) using 1
  all_goals try with_reducible_and_instances rfl
  ring

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_BinHits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

open MeasureTheory Set
open Filter Set
open scoped Topology
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
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal



open MeasureTheory Set
open Filter Set
open scoped Topology
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
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal



open MeasureTheory Set
open Filter Set
open scoped Topology
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
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace


lemma signedPrimitive_decomposition (a u n : Vec) (hD : 1-dot n a ≠ 0) :
    signedPrimitive a u n = (u-n)+
      ((1-dot n a-(1-dot a u))/(1-dot n a)) • n := by
  ext i
  simp only [signedPrimitive,PiLp.sub_apply,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  field_simp
  ring

lemma small_deficit_difference {a u n : Vec} {θ φ : ℝ}
    (hn : ‖n‖=1) (hθ : 0 ≤ θ) (hφ : 0 ≤ φ) (hsmall : θ ≤ φ)
    (hd0 : 0 ≤ 1-dot n u) (hd : 1-dot n u ≤ 8*θ^2)
    (hun : ‖u-n‖ ≤ 4*θ) (han : ‖a-n‖ ≤ 4*φ) :
    |(1-dot a u)-(1-dot n a)| ≤ 24*φ*θ := by
  have he : (1-dot a u)-(1-dot n a)=(1-dot n u)+dot (a-n) (n-u) := by
    simp only [dot_sub_left,dot_sub_right,dot_self,hn,one_pow,dot_comm a n]
    ring
  rw [he]
  calc
    _ ≤ |1-dot n u|+|dot (a-n) (n-u)| := abs_add_le _ _
    _ ≤ 8*θ^2+‖a-n‖*‖n-u‖ := by
      gcongr
      · rwa [abs_of_nonneg hd0]
      · rw [dot_eq_inner]
        exact abs_real_inner_le_norm _ _
    _ ≤ 8*θ^2+(4*φ)*(4*θ) := by
      gcongr
      rwa [norm_sub_rev]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hsmall hθ]

lemma transverseProjection_add (w h k : Vec) :
    transverseProjection w (h+k)=transverseProjection w h+transverseProjection w k :=
  velocityProjection_add _ _ _

lemma transverseProjection_smul (w h : Vec) (c : ℝ) :
    transverseProjection w (c • h)=c • transverseProjection w h := velocityProjection_smul _ _ _

lemma transverseProjection_normal_dist (w n : Vec) :
    ‖transverseProjection w n‖ ≤ ‖n-velocity w‖ := by
  have he : transverseProjection w n=transverseProjection w (n-velocity w) := by
    have hh := transverseProjection_add w (n-velocity w) (velocity w)
    rw [sub_add_cancel,transverseProjection_velocity,add_zero] at hh
    exact hh
  rw [he]
  exact transverseProjection_norm _ _

lemma small_primitive_transverse {w u n : Vec} {θ φ : ℝ}
    (hθ : 0 ≤ θ) (hφ : 0 < φ)
    (hD : φ^2/2 ≤ 1-dot n (velocity w))
    (hun : ‖u-n‖ ≤ 4*θ) (han : ‖velocity w-n‖ ≤ 4*φ)
    (he : |(1-dot (velocity w) u)-(1-dot n (velocity w))| ≤ 24*φ*θ) :
    ‖transverseProjection w (signedPrimitive (velocity w) u n)‖ ≤ 196*θ := by
  have hDpos : 0 < 1-dot n (velocity w) := lt_of_lt_of_le (by positivity) hD
  have hratio : |(1-dot n (velocity w)-(1-dot (velocity w) u))/(1-dot n (velocity w))| ≤ 48*θ/φ := by
    rw [abs_div,abs_of_pos hDpos,abs_sub_comm]
    apply (div_le_iff₀ hDpos).mpr
    have hm := mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ 48*θ/φ)
    have hh : 48*θ/φ*(φ^2/2)=24*φ*θ := by field_simp; ring
    rw [hh] at hm
    exact he.trans hm
  have hpn : ‖transverseProjection w n‖ ≤ 4*φ :=
    (transverseProjection_normal_dist w n).trans (by rwa [norm_sub_rev])
  rw [signedPrimitive_decomposition _ _ _ hDpos.ne',transverseProjection_add,transverseProjection_smul]
  calc
    _ ≤ ‖transverseProjection w (u-n)‖+
        ‖((1-dot n (velocity w)-(1-dot (velocity w) u))/(1-dot n (velocity w))) • transverseProjection w n‖ := norm_add_le _ _
    _ ≤ 4*θ+(48*θ/φ)*(4*φ) := by
      rw [norm_smul,Real.norm_eq_abs]
      exact add_le_add ((transverseProjection_norm _ _).trans hun) (mul_le_mul hratio hpn (norm_nonneg _) (by positivity))
    _ = _ := by field_simp; ring


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal



open MeasureTheory Set
open Filter Set
open scoped Topology
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
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal


open Set MeasureTheory
open scoped ENNReal


end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_DyadicCut
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
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma contDiff_dyadicCut : ContDiff ℝ ∞ dyadicCut :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))
lemma contDiff_dyadicBump : ContDiff ℝ ∞ dyadicBump :=
  contDiff_dyadicCut.sub (contDiff_dyadicCut.comp (contDiff_const.mul contDiff_id))
lemma contDiff_dyadicFactor (n : ℕ) : ContDiff ℝ ∞ (dyadicFactor n) :=
  contDiff_dyadicBump.comp (contDiff_const.mul contDiff_id)

lemma dyadicCut_one {x : ℝ} (hx : x≤1) : dyadicCut x=1 := by
  simp only [dyadicCut,Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hx),sub_zero]
lemma dyadicCut_zero {x : ℝ} (hx : 2≤x) : dyadicCut x=0 := by
  rw [dyadicCut,Real.smoothTransition.one_of_one_le (by linarith),sub_self]
lemma dyadicCut_antitone : Antitone dyadicCut := by
  intro x y hxy
  exact sub_le_sub_left (Real.smoothTransition.monotone (sub_le_sub_right hxy 1)) 1
lemma dyadicCut_nonneg (x : ℝ) : 0≤dyadicCut x := sub_nonneg.mpr (Real.smoothTransition.le_one _)
lemma dyadicCut_le_one (x : ℝ) : dyadicCut x≤1 := sub_le_self _ (Real.smoothTransition.nonneg _)
lemma dyadicBump_zero_left {x : ℝ} (hx : x≤1/2) : dyadicBump x=0 := by
  rw [dyadicBump,dyadicCut_one (by linarith),dyadicCut_one (by linarith),sub_self]
lemma dyadicBump_zero_right {x : ℝ} (hx : 2≤x) : dyadicBump x=0 := by
  rw [dyadicBump,dyadicCut_zero hx,dyadicCut_zero (by linarith),sub_self]
lemma dyadicBump_nonneg (x : ℝ) : 0≤dyadicBump x := by
  by_cases hx : x≤1/2
  · rw [dyadicBump_zero_left hx]
  · exact sub_nonneg.mpr (dyadicCut_antitone (by linarith : x≤2*x))
lemma dyadicBump_le_one (x : ℝ) : dyadicBump x≤1 :=
  (sub_le_self _ (dyadicCut_nonneg _)).trans (dyadicCut_le_one _)
lemma dyadicFactor_nonneg (n : ℕ) (x : ℝ) : 0≤dyadicFactor n x := dyadicBump_nonneg _
lemma dyadicFactor_le_one (n : ℕ) (x : ℝ) : dyadicFactor n x≤1 := dyadicBump_le_one _

lemma dyadicFactor_zero_large {x : ℝ} {n : ℕ} (hn : 2≤(2:ℝ)^n*x) :
    dyadicFactor n x=0 := dyadicBump_zero_right hn

lemma dyadicFactor_tsupport {n : ℕ} {x : ℝ} (hx : x ∈ tsupport (dyadicFactor n)) :
    DyadicBand n x := by
  have hcl : IsClosed {x : ℝ | DyadicBand n x} :=
    (isClosed_le continuous_const (continuous_const.mul continuous_id)).inter
      (isClosed_le (continuous_const.mul continuous_id) continuous_const)
  apply (closure_minimal (s:=(Function.support (dyadicFactor n))) ?_ hcl) hx
  intro y hy
  constructor
  · by_contra hn
    exact hy (dyadicBump_zero_left (le_of_lt (lt_of_not_ge hn)))
  · by_contra hn
    exact hy (dyadicBump_zero_right (le_of_lt (lt_of_not_ge hn)))

lemma dyadicBand_index_le {n m : ℕ} {x : ℝ} (hn : DyadicBand n x) (hm : DyadicBand m x) :
    m≤n+2 := by
  by_contra hmn
  have hnm : n+3 ≤ m := by omega
  have hx : 0≤x := by
    have hp : 0<(2:ℝ)^n := by positivity
    by_contra hh
    have he := mul_neg_of_pos_of_neg hp (lt_of_not_ge hh)
    linarith [hn.1]
  have he := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hnm) hx
  rw [pow_add] at he
  norm_num at he
  nlinarith [hn.1,hm.2]

lemma dyadicBand_card_le (S : Finset ℕ) {x : ℝ} (hS : ∀ n ∈ S, DyadicBand n x) :
    S.card≤5 := by
  classical
  by_cases hs : S.Nonempty
  · obtain ⟨n,hn⟩ := hs
    have hsub : S ⊆ Finset.Icc (n-2) (n+2) := by
      intro m hm
      have hlo := dyadicBand_index_le (hS m hm) (hS n hn)
      have hhi := dyadicBand_index_le (hS n hn) (hS m hm)
      exact Finset.mem_Icc.mpr ⟨by omega,hhi⟩
    have hcard := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hcard
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp

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
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma dyadicMultiFactor_nonneg {ι : Type*} [Fintype ι] (n : ι→ℕ) (x : ι→ℝ) :
    0≤dyadicMultiFactor n x := Finset.prod_nonneg (fun _i _ => dyadicFactor_nonneg _ _)

lemma differentiableAt_dyadicMultiFactor_curve {ι : Type*} [Fintype ι]
    {g : ι → ℝ → ℝ} {t : ℝ} (hg : ∀ i, DifferentiableAt ℝ (g i) t) (n : ι→ℕ) :
    DifferentiableAt ℝ (fun r => dyadicMultiFactor n (fun i => g i r)) t := by
  classical
  exact DifferentiableAt.fun_finsetProd (fun i _ =>
    (contDiff_dyadicFactor (n i)).differentiable (by simp) (g i t) |>.comp t (hg i))

lemma dyadicMultiFactor_positive_bands {ι : Type*} [Fintype ι]
    {n : ι→ℕ} {x : ι→ℝ} (h : 0<dyadicMultiFactor n x) : ∀ i,DyadicBand (n i) (x i) := by
  classical
  intro i
  apply dyadicFactor_tsupport
  apply subset_tsupport
  intro he
  have hz : dyadicMultiFactor n x=0 := Finset.prod_eq_zero (Finset.mem_univ i) he
  linarith

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_PhysicalCutoffCoordinates
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
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
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma physicalCutoffCoordinates_pos {T r : ℝ} {n v w : Vec}
    (hn : ‖n‖=1) (hr : 0 < r) : ∀ i,0<physicalCutoffCoordinates T r n v w i := by
  intro i
  fin_cases i <;> simp only [physicalCutoffCoordinates]
  · exact one_div_pos.mpr (q_pos v)
  · exact Real.sqrt_pos.mpr (div_pos (cone_denom_pos v n hn) (by norm_num))
  · exact Real.sqrt_pos.mpr (div_pos (cone_denom_pos w n hn) (by norm_num))
  · exact div_pos hr (lt_of_lt_of_le (by norm_num) (le_max_left _ _))

lemma real_deficit_le_two {n : Vec} (hn : ‖n‖=1) (v : Vec) : 1-dot n (velocity v) ≤ 2 := by
  have h := (abs_dot_le n (velocity v)).trans (by simpa only [hn,one_mul] using (norm_velocity_lt_one v).le)
  linarith [neg_abs_le (dot n (velocity v))]

lemma angularCoordinate_log_deriv {d : ℝ→ℝ} {d' t : ℝ}
    (hd : HasDerivAt d d' t) (hp : 0<d t) :
    deriv (fun s => Real.sqrt (d s/2)) t / Real.sqrt (d t/2) = d'/(2*d t) := by
  have hhalf : 0<d t/2 := by positivity
  have hs := ((hd.div_const 2).sqrt hhalf.ne').deriv
  rw [hs]
  have hq := Real.sq_sqrt hhalf.le
  have hn := (Real.sqrt_pos.mpr hhalf).ne'
  field_simp
  rw [hq]
  ring

lemma dyadicMultiFactor_curve_locally_finite {ι : Type*} [Fintype ι]
    {g : ι → ℝ → ℝ} {t : ℝ} (hg : ∀ i, ContinuousAt (g i) t) (hx : ∀ i,0<g i t) :
    ∃ N : ℕ, (∀ i,2≤(2:ℝ)^N*g i t) ∧
      ∀ᶠ r in 𝓝 t, ∀ n : ι→ℕ, n∉dyadicBox ι N → dyadicMultiFactor n (fun i => g i r)=0 := by
  classical
  have hp (i : ι) := pow_unbounded_of_one_lt (4/g i t) (by norm_num : (1:ℝ)<2)
  choose Ns hNs using hp
  let N := ∑ i,Ns i
  have hN (i : ι) : 4<(2:ℝ)^N*g i t := by
    have hNi : Ns i≤N := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    exact ((div_lt_iff₀ (hx i)).mp (hNs i)).trans_le
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hNi) (hx i).le)
  refine ⟨N,fun i => by linarith [hN i],?_⟩
  have he : ∀ᶠ r in 𝓝 t, ∀ i,g i t/2<g i r := by
    apply Filter.eventually_all.mpr
    intro i
    exact (hg i).eventually (Ioi_mem_nhds (by linarith [hx i]))
  filter_upwards [he] with r hr n hn
  have hb : ∃ i,N≤n i := by
    by_contra hb
    push Not at hb
    apply hn
    simpa only [dyadicBox,Fintype.mem_piFinset,Finset.mem_range] using hb
  obtain ⟨i,hi⟩ := hb
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  apply dyadicFactor_zero_large
  have hpN : 0<(2:ℝ)^N := by positivity
  have hpni : (2:ℝ)^N≤(2:ℝ)^(n i) := pow_le_pow_right₀ (by norm_num) hi
  have hgr : 0≤g i r := le_of_lt ((by linarith [hx i] : 0<g i t/2).trans (hr i))
  have hh := mul_le_mul_of_nonneg_right hpni hgr
  have hh' := mul_lt_mul_of_pos_left (hr i) hpN
  linarith [hN i]

lemma selectedDyadicCutoff_curve_eventually {ι : Type*} [Fintype ι]
    {g : ι → ℝ → ℝ} {t : ℝ} (hg : ∀ i, ContinuousAt (g i) t) (hx : ∀ i,0<g i t)
    (S : Set (ι→ℕ)) :
    ∃ N : ℕ, (∀ i,2≤(2:ℝ)^N*g i t) ∧
      (fun r => selectedDyadicCutoff S (fun i => g i r)) =ᶠ[𝓝 t]
        (fun r => ∑ n∈selectedDyadicBox N S,dyadicMultiFactor n (fun i => g i r)) := by
  classical
  obtain ⟨N,hN,he⟩ := dyadicMultiFactor_curve_locally_finite hg hx
  refine ⟨N,hN,?_⟩
  filter_upwards [he] with r hr
  unfold selectedDyadicCutoff
  rw [tsum_eq_sum (s:=dyadicBox ι N) (fun n hn => ?_)]
  · simpa only [selectedDyadicBox,id_eq] using (Finset.sum_indicator_eq_sum_filter (dyadicBox ι N) (fun _ n => dyadicMultiFactor n (fun i => g i r)) (fun _ => S) id)
  · by_cases hs : n∈S
    · rw [indicator_of_mem hs,hr n hn]
    · exact indicator_of_notMem hs _

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ConeRadius
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

open MeasureTheory Set
open Filter Set
open scoped Topology
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
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
open Set


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


lemma dot_zero_left_rvm (a : Vec) : dot 0 a=0 := by simp [dot]

lemma hasDerivAt_line_rvm (y u : Vec) :
    HasDerivAt (fun s : ℝ => y+s • u) u 0 := by
  have hh := (hasDerivAt_const (0:ℝ) y).add ((hasDerivAt_id (0:ℝ)).smul_const u)
  change HasDerivAt (fun s : ℝ => y+s • u) (0+(1:ℝ) • u) 0 at hh
  simpa only [zero_add,one_smul] using hh



section
open MeasureTheory Set
open Filter Set
open scoped Topology
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
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


lemma contDiff_dot_pair {k : ℕ∞ω} :
    ContDiff ℝ k (fun z : Vec × Vec => dot z.1 z.2) := by
  unfold dot
  fun_prop

end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_ContDiffDyadicMultiFactor
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
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
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma inverseCoordinate_log_deriv {d : ℝ→ℝ} {d' t : ℝ}
    (hd : HasDerivAt d d' t) (hp : 0<d t) :
    deriv (fun s=>1/d s) t / (1/d t) = -d'/d t := by
  have hh := ((hasDerivAt_const t (1:ℝ)).div hd hp.ne').deriv
  change deriv ((fun _ : ℝ => (1:ℝ))/d) t / (1/d t) = -d'/d t
  rw [hh]
  field_simp
  ring

lemma source_cutoff_logarithmic_rates {V : ℝ→Vec} {E B n : Vec} {t : ℝ}
    (hV : HasDerivAt V (E+cross (velocity (V t)) B) t) (hn : ‖n‖=1) :
    let θ := Real.sqrt ((1-dot n (velocity (V t)))/2)
    |deriv (fun s=>1/q (V s)) t / (1/q (V t))| +
      |deriv (fun s=>Real.sqrt ((1-dot n (velocity (V s)))/2)) t / θ| ≤
      (3/q (V t))*(goodField E B n/θ+θ*‖B‖) := by
  let d := 1-dot n (velocity (V t))
  let θ := Real.sqrt (d/2)
  let U := fderiv ℝ velocity (V t) (E+cross (velocity (V t)) B)
  have hdpos : 0<d := cone_denom_pos (V t) n hn
  have hθ : 0<θ := Real.sqrt_pos.mpr (by positivity)
  have hθsq : θ^2=d/2 := Real.sq_sqrt (by positivity)
  have hθ1 : θ≤1 := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by norm_num,by nlinarith [real_deficit_le_two hn (V t)]⟩
  have htwo : Real.sqrt (2*d)=2*θ := by
    have hs := Real.sq_sqrt (show 0≤2*d by positivity)
    nlinarith [Real.sqrt_nonneg (2*d)]
  have hu : HasDerivAt (fun s=>velocity (V s)) U t :=
    ((contDiff_velocity (k:=1)).differentiable one_ne_zero (V t)).hasFDerivAt.comp_hasDerivAt t hV
  have hd : HasDerivAt (fun s=>1-dot n (velocity (V s))) (-dot n U) t := by
    have hh := (hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_dot (hasDerivAt_const t n) hu)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    try rfl
    simp only [dot_zero_left_rvm,add_zero,zero_sub]
  have hq := inverseCoordinate_log_deriv (hasDerivAt_lorentz_energy hV) (q_pos (V t))
  have ha := angularCoordinate_log_deriv hd hdpos
  change |deriv (fun s=>1/q (V s)) t / (1/q (V t))|+
      |deriv (fun s=>Real.sqrt ((1-dot n (velocity (V s)))/2)) t/θ| ≤ _
  rw [hq]
  change |-dot (velocity (V t)) E/q (V t)|+
    |deriv (fun s=>Real.sqrt ((1-dot n (velocity (V s)))/2)) t/Real.sqrt ((1-dot n (velocity (V t)))/2)| ≤ _
  rw [ha,abs_div,abs_neg,abs_of_pos (q_pos (V t)),abs_div,abs_neg]
  change |dot (velocity (V t)) E|/q (V t)+|dot n U|/|2*d| ≤ _
  rw [abs_of_pos (by positivity : 0<2*d)]
  have he : |dot (velocity (V t)) E|≤goodField E B n+2*θ*‖B‖ := by
    simpa only [← htwo] using source_energy_rate_bound (V t) E B n hn
  have hu' : |dot n U|≤(q (V t))⁻¹*(2*θ)*(goodField E B n+d*‖B‖) := by
    simpa only [U,← htwo] using lorentz_source_normal_acceleration_bound (V t) E B n hn
  have hG : 0≤goodField E B n := by unfold goodField; positivity
  calc
    _ ≤ (goodField E B n+2*θ*‖B‖)/q (V t)+
        ((q (V t))⁻¹*(2*θ)*(goodField E B n+d*‖B‖))/(2*d) :=
      add_le_add (div_le_div_of_nonneg_right he (q_pos _).le)
        (div_le_div_of_nonneg_right hu' (by positivity))
    _ = (q (V t))⁻¹*(goodField E B n+goodField E B n/(2*θ)+3*θ*‖B‖) := by
      have hdθ : d=2*θ^2 := by linarith
      rw [hdθ]
      field_simp
      ring
    _ ≤ (q (V t))⁻¹*(3*(goodField E B n/θ+θ*‖B‖)) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (q_pos _).le)
      apply (mul_le_mul_iff_right₀ hθ).mp
      field_simp
      nlinarith [mul_le_mul_of_nonneg_left hθ1 hG]
    _ = _ := by ring

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_MomentumDirection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

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
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


lemma dyadicFactor_curve_log_bound {C : ℝ}
    (hC : ∀ n : ℕ, ∀ x : ℝ, |x*deriv (dyadicFactor n) x|≤C)
    {g : ℝ → ℝ} {t : ℝ} (hg : DifferentiableAt ℝ g t) (hx : 0<g t) (n : ℕ) :
    |deriv (fun r => dyadicFactor n (g r)) t|≤C*|deriv g t/g t| := by
  change |deriv (dyadicFactor n ∘ g) t| ≤ _
  rw [deriv_comp t ((contDiff_dyadicFactor n).differentiable (by simp) (g t)) hg]
  calc
    _ = |(g t*deriv (dyadicFactor n) (g t))*(deriv g t/g t)| := by
      congr 1
      field_simp [hx.ne']
    _ = |g t*deriv (dyadicFactor n) (g t)| * |deriv g t/g t| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (hC n (g t)) (abs_nonneg _)

lemma dyadicMultiFactor_curve_zero_derivative {ι : Type*} [Fintype ι]
    {g : ι → ℝ → ℝ} {t : ℝ} (n : ι→ℕ)
    (hz : dyadicMultiFactor n (fun i => g i t)=0) :
    deriv (fun r => dyadicMultiFactor n (fun i => g i r)) t=0 := by
  apply IsLocalMin.deriv_eq_zero
  exact Filter.Eventually.of_forall (fun r => by
    dsimp only
    rw [hz]
    exact dyadicMultiFactor_nonneg _ _)

lemma dyadicMultiFactor_curve_log_bound {C : ℝ}
    (hC : ∀ n : ℕ, ∀ x : ℝ, |x*deriv (dyadicFactor n) x|≤C)
    {ι : Type*} [Fintype ι] {g : ι → ℝ → ℝ} {t : ℝ}
    (hg : ∀ i, DifferentiableAt ℝ (g i) t) (hx : ∀ i, 0<g i t) (n : ι→ℕ) :
    |deriv (fun r => dyadicMultiFactor n (fun i => g i r)) t| ≤
      C * ∑ i, |deriv (g i) t/g i t| := by
  classical
  have hd (i : ι) : DifferentiableAt ℝ (fun r => dyadicFactor (n i) (g i r)) t :=
    ((contDiff_dyadicFactor (n i)).differentiable (by simp) (g i t)).comp t (hg i)
  unfold dyadicMultiFactor
  dsimp only
  rw [deriv_fun_finsetProd (u:=Finset.univ) (fun i _ => hd i)]
  simp only [smul_eq_mul]
  apply le_trans (Finset.abs_sum_le_sum_abs _ _)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hp0 : 0≤∏ j∈Finset.univ.erase i,dyadicFactor (n j) (g j t) :=
    Finset.prod_nonneg (fun j _ => dyadicFactor_nonneg _ _)
  have hp1 : (∏ j∈Finset.univ.erase i,dyadicFactor (n j) (g j t))≤1 :=
    Finset.prod_le_one (fun j _ => dyadicFactor_nonneg _ _) (fun j _ => dyadicFactor_le_one _ _)
  rw [abs_mul,abs_of_nonneg hp0]
  exact (mul_le_of_le_one_left (abs_nonneg _) hp1).trans
    (dyadicFactor_curve_log_bound hC (hg i) (hx i) (n i))

lemma dyadicBand_multi_card_le {ι : Type*} [Fintype ι] (S : Finset (ι→ℕ)) {x : ι→ℝ}
    (hS : ∀ n∈S,∀ i,DyadicBand (n i) (x i)) : S.card≤5^Fintype.card ι := by
  classical
  let A : ι→Finset ℕ := fun i=>S.image (fun n=>n i)
  have hA : ∀ i,(A i).card≤5 := by
    intro i
    apply dyadicBand_card_le
    intro n hn
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hn
    exact hS m hm i
  calc
    S.card ≤ (Fintype.piFinset A).card := Finset.card_le_card (by
      intro n hn
      exact Fintype.mem_piFinset.mpr (fun i=>Finset.mem_image.mpr ⟨n,hn,rfl⟩))
    _ = ∏ i,(A i).card := Fintype.card_piFinset A
    _ ≤ ∏ _i : ι,5 := Finset.prod_le_prod' (fun i _=>hA i)
    _ = _ := by simp

lemma selectedDyadicCutoff_uniform_log_bound {C : ℝ}
    (hC0 : 0≤C) (hC : ∀ n : ℕ,∀ x : ℝ,|x*deriv (dyadicFactor n) x|≤C)
    {ι : Type*} [Fintype ι] {g : ι→ℝ→ℝ} {t : ℝ}
    (hg : ∀ i,DifferentiableAt ℝ (g i) t) (hp : ∀ i,0<g i t) (S : Set (ι→ℕ)) :
    |deriv (fun r=>selectedDyadicCutoff S (fun i=>g i r)) t| ≤
      (5:ℝ)^Fintype.card ι*C*∑ i,|deriv (g i) t/g i t| := by
  classical
  obtain ⟨N,_hN,he⟩ := selectedDyadicCutoff_curve_eventually (fun i=>(hg i).continuousAt) hp S
  rw [he.deriv_eq,deriv_fun_sum (fun n _=>differentiableAt_dyadicMultiFactor_curve hg n)]
  let A := (selectedDyadicBox N S).filter (fun n=>∀ i,DyadicBand (n i) (g i t))
  have hac : A.card≤5^Fintype.card ι := dyadicBand_multi_card_le A
    (fun n hn=>(Finset.mem_filter.mp hn).2)
  have hz (n : ι→ℕ) (hnb : ¬∀ i,DyadicBand (n i) (g i t)) :
      deriv (fun r=>dyadicMultiFactor n (fun i=>g i r)) t=0 := by
    apply dyadicMultiFactor_curve_zero_derivative
    by_contra h
    exact hnb (dyadicMultiFactor_positive_bands
      (lt_of_le_of_ne (dyadicMultiFactor_nonneg _ _) (Ne.symm h)))
  have heq : (∑ n∈selectedDyadicBox N S,deriv (fun r=>dyadicMultiFactor n (fun i=>g i r)) t)=
      ∑ n∈A,deriv (fun r=>dyadicMultiFactor n (fun i=>g i r)) t := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hna
    exact hz n (by simpa only [A,Finset.mem_filter,hn,true_and] using hna)
  rw [heq]
  calc
    _ ≤ ∑ n∈A,|deriv (fun r=>dyadicMultiFactor n (fun i=>g i r)) t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n∈A,C*∑ i,|deriv (g i) t/g i t| :=
      Finset.sum_le_sum (fun n _=>dyadicMultiFactor_curve_log_bound hC hg hp n)
    _ = (A.card:ℝ)*(C*∑ i,|deriv (g i) t/g i t|) := by simp
    _ ≤ (5:ℝ)^Fintype.card ι*(C*∑ i,|deriv (g i) t/g i t|) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hac
    _ = _ := by ring

lemma transverseCLM_apply (v h : Vec) : transverseCLM v h=transverseProjection v h := by
  simp only [transverseCLM,sub_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply,InnerProductSpace.toDual_apply_apply,← dot_eq_inner]
  rfl

lemma angularMultiplierCLM_apply (w : ℝ) (v h : Vec) :
    angularMultiplierCLM w v h=angularMultiplier w v h := by
  simp only [angularMultiplierCLM,smul_apply,transverseCLM_apply,angularMultiplier]



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


end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Maxwell_ElectricBoundaryField
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
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma transverse_forceSourceKernel_bound (r : ℝ) (n w v E B : Vec) (hr : 0 < r) (hn : ‖n‖=1) :
    ‖transverseProjection w (forceSourceKernel r n (velocity w) v
      (fderiv ℝ velocity v (E+cross (velocity v) B)))‖ ≤
      (15*(1-dot n (velocity w)))/(r*q v*(1-dot n (velocity v)))*
        (goodField E B n+(1-dot n (velocity v))*‖B‖) := by
  have hd := cone_denom_pos v n hn
  have hq := q_pos v
  unfold forceSourceKernel
  rw [show transverseProjection w (_ • _) = _ • transverseProjection w _ from
    velocityProjection_smul _ _ _,norm_smul,Real.norm_of_nonneg (by positivity)]
  apply (mul_le_mul_of_nonneg_left (transverse_receiverQ_source_bound w v E B n hn)
    (by positivity)).trans_eq
  field_simp

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_CutoffState
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
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma selectedDyadicCutoff_eventually {ι : Type*} [Fintype ι]
    {x : ι→ℝ} (hx : ∀ i,0<x i) (S : Set (ι→ℕ)) :
    ∃ N : ℕ, selectedDyadicCutoff S =ᶠ[𝓝 x]
      (fun y => ∑ n∈selectedDyadicBox N S,dyadicMultiFactor n y) := by
  classical
  have hp (i : ι) := pow_unbounded_of_one_lt (4/x i) (by norm_num : (1:ℝ)<2)
  choose Ns hNs using hp
  let N := ∑ i,Ns i
  have hN (i : ι) : 4<(2:ℝ)^N*x i := by
    have hNi : Ns i≤N := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    exact ((div_lt_iff₀ (hx i)).mp (hNs i)).trans_le
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hNi) (hx i).le)
  have he : ∀ᶠ y in 𝓝 x, ∀ i,x i/2<y i := by
    apply Filter.eventually_all.mpr
    intro i
    exact (continuous_apply i).continuousAt.eventually (Ioi_mem_nhds (by linarith [hx i]))
  refine ⟨N,?_⟩
  filter_upwards [he] with y hy
  have hz : ∀ n : ι→ℕ,n∉dyadicBox ι N → dyadicMultiFactor n y=0 := by
    intro n hn
    have hb : ∃ i,N≤n i := by
      by_contra hb
      push Not at hb
      apply hn
      simpa only [dyadicBox,Fintype.mem_piFinset,Finset.mem_range] using hb
    obtain ⟨i,hi⟩ := hb
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    apply dyadicFactor_zero_large
    have hpN : 0<(2:ℝ)^N := by positivity
    have hpni : (2:ℝ)^N≤(2:ℝ)^(n i) := pow_le_pow_right₀ (by norm_num) hi
    have hyr : 0≤y i := le_of_lt ((by linarith [hx i] : 0<x i/2).trans (hy i))
    have hh := mul_le_mul_of_nonneg_right hpni hyr
    have hh' := mul_lt_mul_of_pos_left (hy i) hpN
    linarith [hN i]
  unfold selectedDyadicCutoff
  rw [tsum_eq_sum (s:=dyadicBox ι N) (fun n hn => ?_)]
  · simpa only [selectedDyadicBox,id_eq] using
      (Finset.sum_indicator_eq_sum_filter (dyadicBox ι N)
        (fun _ n => dyadicMultiFactor n y) (fun _ => S) id)
  · by_cases hs : n∈S
    · rw [indicator_of_mem hs,hz n hn]
    · exact indicator_of_notMem hs _

lemma contDiffAt_selectedDyadicCutoff {ι : Type*} [Fintype ι]
    {x : ι→ℝ} (hx : ∀ i,0<x i) (S : Set (ι→ℕ)) :
    ContDiffAt ℝ ∞ (selectedDyadicCutoff S) x := by
  classical
  obtain ⟨N,he⟩ := selectedDyadicCutoff_eventually hx S
  apply (ContDiffAt.sum (s:=selectedDyadicBox N S) (fun n _ => ?_)).congr_of_eventuallyEq he
  exact contDiffAt_prod (fun i _ => (contDiff_dyadicFactor (n i)).contDiffAt.comp x (contDiff_apply ℝ ℝ i).contDiffAt)

lemma contDiffAt_stateCutoff (T : ℝ) (Q : Set (Fin 4→ℕ)) {z : CutoffState}
    (hr : 0<z.1) (hn : ‖z.2.1‖=1) : ContDiffAt ℝ ∞ (stateCutoff T Q) z := by
  have hc : ContDiffAt ℝ ∞ (fun z : CutoffState =>
      physicalCutoffCoordinates T z.1 z.2.1 z.2.2.1 z.2.2.2) z := by
    apply contDiffAt_pi.mpr
    intro i
    have hv : ContDiffAt ℝ ∞ (fun z : CutoffState=>velocity z.2.2.1) z :=
      (contDiff_velocity (k:=∞)).contDiffAt.comp z contDiffAt_id.snd.snd.fst
    have hw : ContDiffAt ℝ ∞ (fun z : CutoffState=>velocity z.2.2.2) z :=
      (contDiff_velocity (k:=∞)).contDiffAt.comp z contDiffAt_id.snd.snd.snd
    have hd := (contDiffAt_const (c:=(1:ℝ))).sub
      ((contDiff_dot_pair (k:=∞)).contDiffAt.comp z (contDiffAt_id.snd.fst.prodMk hv))
    have hD := (contDiffAt_const (c:=(1:ℝ))).sub
      ((contDiff_dot_pair (k:=∞)).contDiffAt.comp z (contDiffAt_id.snd.fst.prodMk hw))
    fin_cases i <;> simp only [physicalCutoffCoordinates]
    · exact contDiffAt_const.div ((contDiff_q (k:=∞)).contDiffAt.comp z contDiffAt_id.snd.snd.fst) (q_pos _).ne'
    · exact (hd.div_const 2).sqrt (div_pos (cone_denom_pos _ _ hn) (by norm_num)).ne'
    · exact (hD.div_const 2).sqrt (div_pos (cone_denom_pos _ _ hn) (by norm_num)).ne'
    · exact contDiffAt_id.fst.div_const _
  exact (contDiffAt_selectedDyadicCutoff (physicalCutoffCoordinates_pos hn hr) Q).comp z hc

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_RetardedMomentumForce
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

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
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


lemma projected_time_weight_small_kernel {w f r θ φ : ℝ} {v u n : Vec}
    (hf : 0≤f) (hr : 0 < r) (hθ : 0≤θ) (hφ : 0<φ)
    (hD : φ^2/2≤1-dot n (velocity v)) (hun : ‖u-n‖≤4*θ)
    (han : ‖velocity v-n‖≤4*φ)
    (he : |(1-dot (velocity v) u)-(1-dot n (velocity v))|≤24*φ*θ) :
    ‖(f/r) • angularMultiplierCLM w v (signedPrimitive (velocity v) u n)‖ ≤
      196*f*|w| *θ/(r*‖v‖) := by
  rw [angularMultiplierCLM_apply,angularMultiplier,norm_smul,norm_smul,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (div_nonneg hf hr.le),
    abs_div,abs_norm]
  calc
    _ ≤ (f/r)*(|w|/‖v‖*(196*θ)) := by
      gcongr
      exact small_primitive_transverse hθ hφ hD hun han he
    _ = _ := by ring



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
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


lemma projected_primitive_highband_kernel {w f r θ φ : ℝ} {v u n : Vec}
    (hw : 0<w) (hv : w/16≤‖v‖) (hf : 0≤f) (hr : 0 < r)
    (hθ : 0≤θ) (hφ : 0<φ) (hD : φ^2/2≤1-dot n (velocity v))
    (hun : ‖u-n‖≤4*θ) (han : ‖velocity v-n‖≤4*φ)
    (he : |(1-dot (velocity v) u)-(1-dot n (velocity v))|≤24*φ*θ) :
    ‖(f/r) • angularMultiplierCLM w v (signedPrimitive (velocity v) u n)‖≤
      (3136*θ/r)*f := by
  have hvp : 0<‖v‖ := (div_pos hw (by norm_num : (0:ℝ)<16)).trans_le hv
  have hratio : w/‖v‖≤16 := (div_le_iff₀ hvp).mpr (by linarith)
  calc
    _ ≤ 196*f*|w| *θ/(r*‖v‖) := projected_time_weight_small_kernel hf hr hθ hφ hD hun han he
    _ = (f/r)*((w/‖v‖)*(196*θ)) := by rw [abs_of_pos hw]; ring
    _ ≤ (f/r)*(16*(196*θ)) := by gcongr
    _ = _ := by ring


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal



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
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_CutoffSourceTangent
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
open scoped ENNReal Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma contDiffAt_physicalCutoffCoordinates {T : ℝ} {z : CutoffState}
    (_hr : 0<z.1) (hn : ‖z.2.1‖=1) :
    ContDiffAt ℝ ∞ (fun z : CutoffState =>
      physicalCutoffCoordinates T z.1 z.2.1 z.2.2.1 z.2.2.2) z := by
  apply contDiffAt_pi.mpr
  intro i
  have hv : ContDiffAt ℝ ∞ (fun z : CutoffState=>velocity z.2.2.1) z :=
    (contDiff_velocity (k:=∞)).contDiffAt.comp z contDiffAt_id.snd.snd.fst
  have hw : ContDiffAt ℝ ∞ (fun z : CutoffState=>velocity z.2.2.2) z :=
    (contDiff_velocity (k:=∞)).contDiffAt.comp z contDiffAt_id.snd.snd.snd
  have hd := (contDiffAt_const (c:=(1:ℝ))).sub
    ((contDiff_dot_pair (k:=∞)).contDiffAt.comp z (contDiffAt_id.snd.fst.prodMk hv))
  have hD := (contDiffAt_const (c:=(1:ℝ))).sub
    ((contDiff_dot_pair (k:=∞)).contDiffAt.comp z (contDiffAt_id.snd.fst.prodMk hw))
  fin_cases i <;> simp only [physicalCutoffCoordinates]
  · exact contDiffAt_const.div ((contDiff_q (k:=∞)).contDiffAt.comp z contDiffAt_id.snd.snd.fst) (q_pos _).ne'
  · exact (hd.div_const 2).sqrt (div_pos (cone_denom_pos _ _ hn) (by norm_num)).ne'
  · exact (hD.div_const 2).sqrt (div_pos (cone_denom_pos _ _ hn) (by norm_num)).ne'
  · exact contDiffAt_id.fst.div_const _

lemma stateCutoff_curve_log_bound {C T t : ℝ}
    (hC0 : 0≤C) (hC : ∀n : ℕ,∀x : ℝ,|x*deriv (dyadicFactor n) x|≤C)
    {z : ℝ→CutoffState} {h : CutoffState}
    (hz : HasDerivAt z h t) (hr : 0<(z t).1) (hn : ‖(z t).2.1‖=1)
    (Q : Set (Fin 4→ℕ)) :
    |fderiv ℝ (stateCutoff T Q) (z t) h| ≤
      625*C*∑i : Fin 4,|deriv (fun s=>physicalCutoffCoordinates T
        (z s).1 (z s).2.1 (z s).2.2.1 (z s).2.2.2 i) t /
        physicalCutoffCoordinates T (z t).1 (z t).2.1 (z t).2.2.1 (z t).2.2.2 i| := by
  have hd := ((contDiffAt_stateCutoff T Q hr hn).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hz
  rw [←hd.deriv]
  change |deriv (fun s=>selectedDyadicCutoff Q (physicalCutoffCoordinates T
    (z s).1 (z s).2.1 (z s).2.2.1 (z s).2.2.2)) t| ≤ _
  have hc := (contDiffAt_physicalCutoffCoordinates (T:=T) hr hn).differentiableAt (by simp)
  have hh := selectedDyadicCutoff_uniform_log_bound hC0 hC
    (fun i=>differentiableAt_pi.mp (hc.comp t hz.differentiableAt) i)
    (physicalCutoffCoordinates_pos (T:=T) hn hr) Q
  simpa only [stateCutoff,Function.comp_apply,Fintype.card_fin,show (5:ℝ)^4=625 by norm_num] using hh

lemma stateCutoff_source_bound {C T r : ℝ} {n v w E B : Vec}
    (hC0 : 0≤C) (hC : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x|≤C)
    (hr : 0 < r) (hn : ‖n‖=1) (Q : Set (Fin 4→ℕ)) :
    |fderiv ℝ (stateCutoff T Q) (r,n,v,w)
      (cutoffSourceTangent (E+cross (velocity v) B))| ≤
      625*C*((3/q v)*(goodField E B n/Real.sqrt ((1-dot n (velocity v))/2)+
        Real.sqrt ((1-dot n (velocity v))/2)*‖B‖)) := by
  let V : ℝ→Vec := fun t=>v+t • (E+cross (velocity v) B)
  have hV : HasDerivAt V (E+cross (velocity v) B) 0 := hasDerivAt_line_rvm v _
  have hv0 : V 0=v := by simp [V]
  have hz : HasDerivAt (fun t : ℝ=>(r,n,V t,w))
      (cutoffSourceTangent (E+cross (velocity v) B)) 0 :=
    (hasDerivAt_const 0 r).prodMk ((hasDerivAt_const 0 n).prodMk (hV.prodMk (hasDerivAt_const 0 w)))
  have hb := stateCutoff_curve_log_bound (T:=T) hC0 hC hz hr hn Q
  have hs := source_cutoff_logarithmic_rates (hV.congr_deriv (by rw [hv0])) hn
  simp only [hv0] at hb hs
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [Fin.sum_univ_succ,Fin.isValue,physicalCutoffCoordinates,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero,add_zero,
    deriv_const,zero_div,abs_zero] using hs

lemma projected_physical_small_primitive {v W n : Vec} {w : ℝ}
    (hn : ‖n‖=1) (hw : 0<w) (hW : w/16≤‖W‖)
    (hsmall : 1-dot n (velocity v)≤1-dot n (velocity W)) :
    ‖angularMultiplierCLM w W (signedPrimitive (velocity W) (velocity v) n)‖ ≤
      3136*Real.sqrt ((1-dot n (velocity v))/2) := by
  let θ := Real.sqrt ((1-dot n (velocity v))/2)
  let φ := Real.sqrt ((1-dot n (velocity W))/2)
  have hd := cone_denom_pos v n hn
  have hD := cone_denom_pos W n hn
  have hθ : 0<θ := Real.sqrt_pos.mpr (by positivity)
  have hφ : 0<φ := Real.sqrt_pos.mpr (by positivity)
  have hθsq : θ^2=(1-dot n (velocity v))/2 := Real.sq_sqrt (by positivity)
  have hφsq : φ^2=(1-dot n (velocity W))/2 := Real.sq_sqrt (by positivity)
  have hθφ : θ≤φ := Real.sqrt_le_sqrt (by linarith)
  have hun : ‖velocity v-n‖≤4*θ := by
    apply norm_sub_le_of_deficit (norm_velocity_lt_one _).le hn.le (by positivity)
    rw [dot_comm]
    nlinarith
  have han : ‖velocity W-n‖≤4*φ := by
    apply norm_sub_le_of_deficit (norm_velocity_lt_one _).le hn.le (by positivity)
    rw [dot_comm]
    nlinarith
  have he := small_deficit_difference hn hθ.le hφ.le hθφ hd.le (by nlinarith) hun han
  simpa only [one_div_one,one_smul,div_one,mul_one] using
    projected_primitive_highband_kernel (w:=w) (f:=1) (r:=1) hw hW (by norm_num) (by norm_num)
      hθ.le hφ (by nlinarith) hun han he

lemma projected_physical_cutoff_cost {v W n : Vec} {w r f c L : ℝ}
    (hn : ‖n‖=1) (hw : 0<w) (hW : w/16≤‖W‖) (hr : 0 < r) (hf : 0≤f)
    (hsmall : 1-dot n (velocity v)≤1-dot n (velocity W)) (hL : |L| ≤ c) :
    let θ := Real.sqrt ((1-dot n (velocity v))/2)
    let φ := Real.sqrt ((1-dot n (velocity W))/2)
    ‖(f*(1-dot n (velocity W))/(r*(1-dot n (velocity v)))*L) •
      angularMultiplierCLM w W (signedPrimitive (velocity W) (velocity v) n)‖ ≤
      3136*(f/r)*(φ^2/θ)*c := by
  let d := 1-dot n (velocity v)
  let D := 1-dot n (velocity W)
  let θ := Real.sqrt (d/2)
  let φ := Real.sqrt (D/2)
  have hd : 0<d := cone_denom_pos v n hn
  have hD : 0<D := cone_denom_pos W n hn
  have hθ : 0<θ := Real.sqrt_pos.mpr (by positivity)
  have hφ : 0<φ := Real.sqrt_pos.mpr (by positivity)
  have hθsq : θ^2=d/2 := Real.sq_sqrt (by positivity)
  have hφsq : φ^2=D/2 := Real.sq_sqrt (by positivity)
  have hcb : 0 ≤ c := (abs_nonneg _).trans hL
  have hp := projected_physical_small_primitive hn hw hW hsmall
  change ‖(f*D/(r*d)*L) • _‖≤3136*(f/r)*(φ^2/θ)*c
  rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (by positivity : 0≤f*D/(r*d))]
  calc
    _ ≤ (f*D/(r*d)*c)*(3136*θ) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hL (by positivity)) hp (norm_nonneg _) (by positivity)
    _ = _ := by
      have he : d=2*θ^2 := by linarith
      have hE : D=2*φ^2 := by linarith
      rw [he,hE]
      field_simp

lemma projected_source_cutoff_cost {C T r f w : ℝ} {n v W E B : Vec}
    (hC0 : 0≤C) (hC : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x|≤C)
    (hn : ‖n‖=1) (hw : 0<w) (hW : w/16≤‖W‖) (hr : 0 < r) (hf : 0≤f)
    (hsmall : 1-dot n (velocity v)≤1-dot n (velocity W)) (Q : Set (Fin 4→ℕ)) :
    let θ := Real.sqrt ((1-dot n (velocity v))/2)
    let φ := Real.sqrt ((1-dot n (velocity W))/2)
    ‖(f*(1-dot n (velocity W))/(r*(1-dot n (velocity v)))*
      fderiv ℝ (stateCutoff T Q) (r,n,v,W)
        (cutoffSourceTangent (E+cross (velocity v) B))) •
      angularMultiplierCLM w W (signedPrimitive (velocity W) (velocity v) n)‖ ≤
      5880000*C*(f/r)*(φ^2/q v)*(goodField E B n/θ^2+‖B‖) := by
  have hd := cone_denom_pos v n hn
  have hθ : 0<Real.sqrt ((1-dot n (velocity v))/2) := Real.sqrt_pos.mpr (by positivity)
  have hb := projected_physical_cutoff_cost hn hw hW hr hf hsmall
    (stateCutoff_source_bound (T:=T) (v:=v) (w:=W) (E:=E) (B:=B) hC0 hC hr hn Q)
  exact hb.trans_eq (by field_simp; ring)

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_PhysicalProjectedRemainderDensity
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

lemma angularMultiplierCLM_highband_transverse {w : ℝ} {W x : Vec}
    (hw : 0<w) (hW : w/16 ≤ ‖W‖) :
    ‖angularMultiplierCLM w W x‖ ≤ 16*‖transverseProjection W x‖ := by
  have hρ : 0<‖W‖ := lt_of_lt_of_le (by positivity) hW
  rw [angularMultiplierCLM_apply,angularMultiplier,norm_smul,Real.norm_eq_abs,
    abs_of_pos (div_pos hw hρ)]
  exact mul_le_mul_of_nonneg_right ((div_le_iff₀ hρ).mpr (by linarith)) (norm_nonneg _)

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

lemma projected_source_direct_bin_bound {r w p θ φ : ℝ} (n W v E B : Vec)
    (hr : 0 < r) (hw : 0<w) (hW : w/16≤‖W‖) (hn : ‖n‖=1)
    (hp : 0<p) (hθ : 0<θ) (hq : p≤q v)
    (hdlo : θ^2/2≤1-dot n (velocity v)) (hDhi : 1-dot n (velocity W)≤8*φ^2) :
    ‖angularMultiplierCLM w W (forceSourceKernel r n (velocity W) v
      (fderiv ℝ velocity v (E+cross (velocity v) B)))‖≤
      (3840*φ^2/(r*p))*(goodField E B n/θ^2+‖B‖) := by
  let d := 1-dot n (velocity v)
  let D := 1-dot n (velocity W)
  have hd : 0<d := cone_denom_pos v n hn
  have hD : 0<D := cone_denom_pos W n hn
  have hG : 0≤goodField E B n := add_nonneg (norm_nonneg _) (abs_nonneg _)
  have hprim := angularMultiplierCLM_highband_transverse
    (x:=forceSourceKernel r n (velocity W) v (fderiv ℝ velocity v (E+cross (velocity v) B))) hw hW
  have hsrc := transverse_forceSourceKernel_bound r n W v E B hr hn
  change _ ≤ (15*D)/(r*q v*d)*(goodField E B n+d*‖B‖) at hsrc
  have hc : 240*D/(r*q v)≤1920*φ^2/(r*p) := by
    calc
      240*D/(r*q v)≤240*(8*φ^2)/(r*p) := by gcongr
      _ = _ := by ring
  have hg : goodField E B n/d≤2*(goodField E B n/θ^2) := by
    calc
      goodField E B n/d≤goodField E B n/(θ^2/2) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ 16*((15*D)/(r*q v*d)*(goodField E B n+d*‖B‖)) :=
      hprim.trans (mul_le_mul_of_nonneg_left hsrc (by norm_num))
    _ = (240*D/(r*q v))*(goodField E B n/d+‖B‖) := by field_simp; ring
    _ ≤ (1920*φ^2/(r*p))*(2*(goodField E B n/θ^2+‖B‖)) := by
      apply mul_le_mul hc _ (by positivity) (by positivity)
      linarith [norm_nonneg B]
    _ = _ := by ring

lemma projected_source_cutoff_bin_bound {C T r f w p θ φ : ℝ} {n v W E B : Vec}
    (hC0 : 0≤C) (hC : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x|≤C)
    (hn : ‖n‖=1) (hw : 0<w) (hW : w/16≤‖W‖) (hr : 0 < r) (hf : 0≤f)
    (hp : 0<p) (hθ : 0<θ) (hq : p≤q v)
    (hdlo : θ^2/2≤1-dot n (velocity v)) (hDhi : 1-dot n (velocity W)≤8*φ^2)
    (hsmall : 1-dot n (velocity v)≤1-dot n (velocity W)) (Q : Set (Fin 4→ℕ)) :
    ‖(f*(1-dot n (velocity W))/(r*(1-dot n (velocity v)))*
      fderiv ℝ (stateCutoff T Q) (r,n,v,W)
        (cutoffSourceTangent (E+cross (velocity v) B))) •
      angularMultiplierCLM w W (signedPrimitive (velocity W) (velocity v) n)‖ ≤
      (94080000*C*φ^2/(r*p))*(goodField E B n/θ^2+‖B‖)*f := by
  let d := 1-dot n (velocity v)
  let D := 1-dot n (velocity W)
  have hd : 0<d := cone_denom_pos v n hn
  have hD : 0<D := cone_denom_pos W n hn
  have hG : 0≤goodField E B n := add_nonneg (norm_nonneg _) (abs_nonneg _)
  have hb := projected_source_cutoff_cost (T:=T) (E:=E) (B:=B) hC0 hC hn hw hW hr hf hsmall Q
  change _≤5880000*C*(f/r)*((Real.sqrt (D/2))^2/q v)*
    (goodField E B n/(Real.sqrt (d/2))^2+‖B‖) at hb
  rw [Real.sq_sqrt (by positivity : 0≤D/2),Real.sq_sqrt (by positivity : 0≤d/2)] at hb
  have hc : (D/2)/q v≤4*φ^2/p := by
    calc
      (D/2)/q v≤((8*φ^2)/2)/p := by gcongr
      _ = _ := by ring
  have hg : goodField E B n/(d/2)≤4*(goodField E B n/θ^2) := by
    calc
      goodField E B n/(d/2)≤goodField E B n/((θ^2/2)/2) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ 5880000*C*(f/r)*((D/2)/q v)*(goodField E B n/(d/2)+‖B‖) := hb
    _ ≤ 5880000*C*(f/r)*(4*φ^2/p)*(4*(goodField E B n/θ^2+‖B‖)) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hc (by positivity)) _ (by positivity) (by positivity)
      linarith [norm_nonneg B]
    _ = _ := by ring

lemma projected_source_combined_bin_bound {C T r f w p θ φ : ℝ} {n v W E B : Vec}
    (hC0 : 0≤C) (hC : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x|≤C)
    (hn : ‖n‖=1) (hw : 0<w) (hW : w/16≤‖W‖) (hr : 0 < r) (hf : 0≤f)
    (hp : 0<p) (hθ : 0<θ) (hq : p≤q v)
    (hdlo : θ^2/2≤1-dot n (velocity v)) (hDhi : 1-dot n (velocity W)≤8*φ^2)
    (hsmall : 1-dot n (velocity v)≤1-dot n (velocity W)) (Q : Set (Fin 4→ℕ)) :
    ‖f • angularMultiplierCLM w W (forceSourceKernel r n (velocity W) v
      (fderiv ℝ velocity v (E+cross (velocity v) B)))‖+
    ‖(f*(1-dot n (velocity W))/(r*(1-dot n (velocity v)))*
      fderiv ℝ (stateCutoff T Q) (r,n,v,W)
        (cutoffSourceTangent (E+cross (velocity v) B))) •
      angularMultiplierCLM w W (signedPrimitive (velocity W) (velocity v) n)‖ ≤
      ((3840+94080000*C)*φ^2/(r*p))*(goodField E B n/θ^2+‖B‖)*f := by
  have hdir := projected_source_direct_bin_bound n W v E B hr hw hW hn hp hθ hq hdlo hDhi
  have hcut := projected_source_cutoff_bin_bound (T:=T) (E:=E) (B:=B) hC0 hC hn hw hW hr hf hp hθ hq hdlo hDhi hsmall Q
  rw [norm_smul,Real.norm_of_nonneg hf]
  exact (add_le_add (mul_le_mul_of_nonneg_left hdir hf) hcut).trans_eq (by ring)

lemma physicalProjectedSourceDensity_bound {s : Solution} {X V : ℝ→Vec}
    {C : ClosedConeBin} {T w p θ φ c : ℝ} {z : ConeCoordinate} (Q : Set (Fin 4→ℕ))
    (hc : 0 ≤ c) (hcut : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x| ≤ c)
    (hw : 0<w) (hW : w/16≤‖V z.1‖) (hr : 0<z.1-z.2.1) (hp : 0<p) (hθ : 0<θ)
    (hq : p≤C.qmin) (hd : θ^2/2≤C.dmin)
    (hD : 1-dot z.2.2.1 (velocity (V z.1))≤8*φ^2)
    (hsmall : C.dmax≤1-dot z.2.2.1 (velocity (V z.1)))
    (hf : ∀v,0 ≤ s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))) :
    physicalProjectedSourceDensity s X V C T w Q z ≤
      ENNReal.ofReal (((3840+94080000*c)*φ^2/p)*(z.1-z.2.1)*
        (goodField (s.E (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1))
          (s.B (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1)) z.2.2.1/θ^2+
          ‖s.B (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1)‖))*
        physicalBinDensity s X V C z.1 z.2.1 z.2.2 := by
  let G := goodField (s.E (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1))
    (s.B (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1)) z.2.2.1
  let b := ‖s.B (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1)‖
  have hG : 0≤G := add_nonneg (norm_nonneg _) (abs_nonneg _)
  have hb : 0≤b := norm_nonneg _
  unfold physicalProjectedSourceDensity
  calc
    _ ≤ ENNReal.ofReal ((z.1-z.2.1)^2) *
        ∫⁻v in coneBinMomentumSet C z.2.2.1 (velocity (V z.1)),
          ENNReal.ofReal (((3840+94080000*c)*φ^2/((z.1-z.2.1)*p))*(G/θ^2+b))*
            ENNReal.ofReal (s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))) := by
      apply mul_le_mul' le_rfl
      apply setLIntegral_mono' (measurableSet_coneBinMomentumSet _ _ _)
      intro v hv
      rw [←ENNReal.ofReal_mul (by positivity :
        0≤((3840+94080000*c)*φ^2/((z.1-z.2.1)*p))*(G/θ^2+b))]
      exact ENNReal.ofReal_le_ofReal (projected_source_combined_bin_bound hc hcut (sphere_norm _)
        hw hW hr (hf v) hp hθ (hq.trans hv.1.1) (hd.trans hv.2.1.1) hD
        (hv.2.1.2.trans hsmall) Q)
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,←mul_assoc,
        ←ENNReal.ofReal_mul (sq_nonneg _)]
      congr 1
      congr 1
      field_simp [hr.ne']
      rfl

lemma physicalProjectedSource_integral_bound_oai {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) (hT : 0≤T) {X V : ℝ→Vec}
    (hX : Measurable X) (hV : Measurable V) (B : ClosedConeBin)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T) {w p θ φ c : ℝ}
    (Q : Set (Fin 4→ℕ)) (hc : 0 ≤ c)
    (hcut : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x| ≤ c)
    (hw : 0<w) (hp : 0<p) (hθ : 0<θ) (hφ : 0<φ)
    (hr : 0<B.rmin) (hq : p≤B.qmin) (hdlo : θ^2/2≤B.dmin)
    (hDhi : B.Dmax≤8*φ^2) (hsmall : B.dmax≤B.Dmin)
    (hband : ∀t∈J,w/16≤‖V t‖) :
    (∫⁻z : ConeCoordinate,physicalProjectedSourceDensity s X V B T w Q z ∂physicalBinMeasure V B J)≤
      ENNReal.ofReal ((3840+94080000*c)*φ^2/(p*θ^2))*(∫⁻z : ConeCoordinate,
        ENNReal.ofReal (z.1-z.2.1)*ENNReal.ofReal (prefixConeGood s T X z)*
          physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B J)+
      ENNReal.ofReal ((3840+94080000*c)*φ/p)*(∫⁻z : ConeCoordinate,
        ENNReal.ofReal (z.1-z.2.1)*ENNReal.ofReal φ*ENNReal.ofReal (prefixConeMagnetic s T X z)*
          physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B J) := by
  have hN := physicalBinDensity_aemeasurable hs hT hX hV B hJ hJT
  have hG := hs.measurable_prefixConeGood hT hX
  have hR : Measurable (fun z : ConeCoordinate=>ENNReal.ofReal (z.1-z.2.1)) :=
    (measurable_fst.sub (measurable_fst.comp measurable_snd)).ennreal_ofReal
  have hb : (∫⁻z : ConeCoordinate,physicalProjectedSourceDensity s X V B T w Q z ∂physicalBinMeasure V B J)≤
      ∫⁻z : ConeCoordinate,
        ENNReal.ofReal ((3840+94080000*c)*φ^2/(p*θ^2))*(ENNReal.ofReal (z.1-z.2.1)*
          ENNReal.ofReal (prefixConeGood s T X z)*physicalBinDensity s X V B z.1 z.2.1 z.2.2)+
        ENNReal.ofReal ((3840+94080000*c)*φ/p)*(ENNReal.ofReal (z.1-z.2.1)*ENNReal.ofReal φ*
          ENNReal.ofReal (prefixConeMagnetic s T X z)*physicalBinDensity s X V B z.1 z.2.1 z.2.2)
          ∂physicalBinMeasure V B J := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV B hJ)] with z hz
    have hzT : z.2.1∈Icc 0 T := ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩
    have hrz : 0<z.1-z.2.1 := hr.trans_le hz.2.2.1.1
    have hb := physicalProjectedSourceDensity_bound (X:=X) (T:=T) Q hc hcut hw (hband z.1 hz.1)
      hrz hp hθ hq hdlo (hz.2.2.2.2.2.trans hDhi) (hsmall.trans hz.2.2.2.2.1)
      (fun v=>hs.nonnegative _ hzT _)
    apply hb.trans_eq
    let G := prefixConeGood s T X z
    let b := prefixConeMagnetic s T X z
    have hG0 : 0≤G := add_nonneg (norm_nonneg _) (abs_nonneg _)
    have hb0 : 0≤b := norm_nonneg _
    have heG : goodField (s.E (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1))
        (s.B (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1)) z.2.2.1=G := by
      simp [G,prefixConeGood,prefixField,prefixClamp_eq hzT]
    have heb : ‖s.B (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1)‖=b := by
      simp [b,prefixConeMagnetic,coneFoot,prefixField,prefixClamp_eq hzT]
    rw [heG,heb]
    have he : ((3840+94080000*c)*φ^2/p)*(z.1-z.2.1)*(G/θ^2+b)=
        ((3840+94080000*c)*φ^2/(p*θ^2))*((z.1-z.2.1)*G)+
          ((3840+94080000*c)*φ/p)*((z.1-z.2.1)*φ*b) := by ring
    rw [he,ENNReal.ofReal_add (by positivity) (by positivity),add_mul]
    simp only [ENNReal.ofReal_mul (by positivity : 0≤(3840+94080000*c)*φ^2/(p*θ^2)),
      ENNReal.ofReal_mul (by positivity : 0≤(3840+94080000*c)*φ/p),
      ENNReal.ofReal_mul (mul_nonneg hrz.le hφ.le),ENNReal.ofReal_mul hrz.le]
    dsimp only [G,b]
    ac_rfl
  refine hb.trans_eq ?_
  have hMG : AEMeasurable (fun z : ConeCoordinate=>
      ENNReal.ofReal ((3840+94080000*c)*φ^2/(p*θ^2))*(ENNReal.ofReal (z.1-z.2.1)*
          ENNReal.ofReal (prefixConeGood s T X z)*physicalBinDensity s X V B z.1 z.2.1 z.2.2))
      (physicalBinMeasure V B J) := by
    simpa only [Pi.mul_apply] using (((hR.mul hG.ennreal_ofReal).aemeasurable.mul hN).const_mul
      (ENNReal.ofReal ((3840+94080000*c)*φ^2/(p*θ^2))))
  rw [lintegral_add_left' hMG,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end RVM

end

end OAI
end

theorem solution : type_of% @OAI.RVM.physicalProjectedSource_integral_bound_oai := @OAI.RVM.physicalProjectedSource_integral_bound_oai
