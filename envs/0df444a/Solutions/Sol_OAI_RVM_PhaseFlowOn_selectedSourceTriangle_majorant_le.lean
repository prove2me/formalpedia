-- Prove2me | solution 1 for OAI.RVM.PhaseFlowOn.selectedSourceTriangle_majorant_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:58:16.344833+00:00
-- url     : https://prove2.me/submissions/b9373017-0590-431f-9007-d591ec2d66c7

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

lemma contDiff_q {k : ℕ∞ω} : ContDiff ℝ k q := by
  exact ((contDiff_const : ContDiff ℝ k (fun _ : Vec => (1 : ℝ))).add
    (contDiff_id.norm_sq ℝ)).sqrt (fun v => by positivity)

lemma contDiff_velocity {k : ℕ∞ω} : ContDiff ℝ k velocity := by
  exact (contDiff_q.inv (fun v => ne_of_gt (q_pos v))).smul contDiff_id

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

lemma prefixClamp_eq {T t : ℝ} (ht : t∈Icc 0 T) : prefixClamp T t=t := by
  simp [prefixClamp,min_eq_right ht.2,max_eq_right ht.1]

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

lemma receiverQ_add (a n h k : Vec) : receiverQ a n (h+k)=receiverQ a n h+receiverQ a n k := by
  simp only [receiverQ,dot_add_right,smul_add,add_smul]
  module

lemma receiverQ_smul (a n h : Vec) (c : ℝ) : receiverQ a n (c • h)=c • receiverQ a n h := by
  simp only [receiverQ,dot_smul_right,smul_add,smul_smul]
  module

lemma cone_denom_le_two (v n : Vec) (hn : ‖n‖=1) : 1-dot n (velocity v)≤2 := by
  have h := abs_dot_le n (velocity v)
  rw [hn,one_mul] at h
  have h' := (neg_le_abs (dot n (velocity v))).trans h
  linarith [norm_velocity_lt_one v]

lemma receiverQ_tangent_bound (w n h : Vec) (hn : ‖n‖=1) (hh : dot n h=0) :
    ‖receiverQ (velocity w) n h‖≤2*Real.sqrt (2*(1-dot n (velocity w)))*‖h‖ := by
  let D := 1-dot n (velocity w)
  have hD : 0≤D := (cone_denom_pos w n hn).le
  have hD2 : D≤2 := cone_denom_le_two w n hn
  have hDs : D≤Real.sqrt (2*D) := by
    nlinarith [Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ)≤2) hD),Real.sqrt_nonneg (2*D)]
  have ha : |dot (velocity w) h|≤Real.sqrt (2*D)*‖h‖ := by
    rw [show dot (velocity w) h=dot (velocity w-n) h by rw [dot_sub_left,hh,sub_zero]]
    exact (abs_dot_le _ _).trans (mul_le_mul_of_nonneg_right
      (velocity_normal_distance_bound w n hn) (norm_nonneg h))
  calc
    _ ≤ ‖D • h‖+‖dot (velocity w) h • n‖ := norm_add_le _ _
    _ = D*‖h‖+|dot (velocity w) h| := by rw [norm_smul,norm_smul,Real.norm_eq_abs,
        Real.norm_eq_abs,abs_of_nonneg hD,hn,mul_one]
    _ ≤ 2*Real.sqrt (2*D)*‖h‖ := by nlinarith [mul_le_mul_of_nonneg_right hDs (norm_nonneg h)]

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

lemma receiverQ_source_bound (w v E B n : Vec) (hn : ‖n‖=1) :
    ‖receiverQ (velocity w) n
        (sourceNumerator n (velocity v) (fderiv ℝ velocity v (E+cross (velocity v) B)))‖ ≤
      10*Real.sqrt (2*(1-dot n (velocity w)))*(1-dot n (velocity v))*(q v)⁻¹*
        (goodField E B n+(1-dot n (velocity v))*‖B‖) := by
  exact (receiverQ_tangent_bound _ _ _ hn (sourceNumerator_tangent _ _ _ hn)).trans
    (by convert mul_le_mul_of_nonneg_left (sourceNumerator_bound v E B n hn)
          (show 0≤2*Real.sqrt (2*(1-dot n (velocity w))) by positivity) using 1; ring)

lemma transverseProjection_norm (w h : Vec) : ‖transverseProjection w h‖≤‖h‖ := by
  apply velocityProjection_norm
  by_cases hw : w=0
  · simp [hw]
  · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg w)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]

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

lemma dyadicCut_one {x : ℝ} (hx : x≤1) : dyadicCut x=1 := by
  simp only [dyadicCut,Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hx),sub_zero]
lemma dyadicCut_zero {x : ℝ} (hx : 2≤x) : dyadicCut x=0 := by
  rw [dyadicCut,Real.smoothTransition.one_of_one_le (by linarith),sub_self]
lemma dyadicCut_antitone : Antitone dyadicCut := by
  intro x y hxy
  exact sub_le_sub_left (Real.smoothTransition.monotone (sub_le_sub_right hxy 1)) 1
lemma dyadicBump_zero_left {x : ℝ} (hx : x≤1/2) : dyadicBump x=0 := by
  rw [dyadicBump,dyadicCut_one (by linarith),dyadicCut_one (by linarith),sub_self]
lemma dyadicBump_zero_right {x : ℝ} (hx : 2≤x) : dyadicBump x=0 := by
  rw [dyadicBump,dyadicCut_zero hx,dyadicCut_zero (by linarith),sub_self]
lemma dyadicBump_nonneg (x : ℝ) : 0≤dyadicBump x := by
  by_cases hx : x≤1/2
  · rw [dyadicBump_zero_left hx]
  · exact sub_nonneg.mpr (dyadicCut_antitone (by linarith : x≤2*x))
lemma dyadicFactor_nonneg (n : ℕ) (x : ℝ) : 0≤dyadicFactor n x := dyadicBump_nonneg _

lemma dyadicFactor_eq (n : ℕ) (x : ℝ) :
    dyadicFactor n x=dyadicCut ((2:ℝ)^n*x)-dyadicCut ((2:ℝ)^(n+1)*x) := by
  simp only [dyadicFactor,dyadicBump,pow_succ]
  congr 2
  ring
lemma sum_dyadicFactor (N : ℕ) (x : ℝ) :
    ∑ n ∈ Finset.range N, dyadicFactor n x=dyadicCut x-dyadicCut ((2:ℝ)^N*x) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ,ih,dyadicFactor_eq]; ring

lemma dyadicFactor_zero_large {x : ℝ} {n : ℕ} (hn : 2≤(2:ℝ)^n*x) :
    dyadicFactor n x=0 := dyadicBump_zero_right hn

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

lemma sum_dyadicMultiFactor {ι : Type*} [Fintype ι] (N : ℕ) (x : ι→ℝ) :
    ∑ n∈dyadicBox ι N, dyadicMultiFactor n x =
      ∏ i, (dyadicCut (x i)-dyadicCut ((2:ℝ)^N*x i)) := by
  classical
  unfold dyadicBox dyadicMultiFactor
  convert Finset.sum_prod_piFinset (Finset.range N) (fun i n => dyadicFactor n (x i)) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [sum_dyadicFactor]

lemma sum_dyadicMultiFactor_eq_one {ι : Type*} [Fintype ι] (N : ℕ) (x : ι→ℝ)
    (hx : ∀ i, x i≤1) (hN : ∀ i, 2≤(2:ℝ)^N*x i) :
    ∑ n∈dyadicBox ι N, dyadicMultiFactor n x=1 := by
  rw [sum_dyadicMultiFactor]
  simp only [dyadicCut_one (hx _),dyadicCut_zero (hN _),sub_zero,Finset.prod_const_one]

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

lemma physicalCutoffCoordinates_le_one {T r : ℝ} {n v w : Vec}
    (hn : ‖n‖=1) (hr : r ≤ max 1 T) : ∀ i,physicalCutoffCoordinates T r n v w i≤1 := by
  intro i
  fin_cases i <;> simp only [physicalCutoffCoordinates]
  · apply (div_le_one (q_pos v)).mpr
    have hs := q_sq v
    nlinarith [q_pos v,sq_nonneg ‖v‖]
  · apply (Real.sqrt_le_iff).mpr
    constructor
    · norm_num
    · nlinarith [real_deficit_le_two hn v]
  · apply (Real.sqrt_le_iff).mpr
    constructor
    · norm_num
    · nlinarith [real_deficit_le_two hn w]
  · exact (div_le_one (lt_of_lt_of_le (by norm_num) (le_max_left _ _))).mpr hr

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


lemma dot_zero_right_rvm (a : Vec) : dot a 0=0 := by simp [dot]

lemma hasDerivAt_norm_nonzero {Y : ℝ → Vec} {u : Vec} {s : ℝ}
    (hY : HasDerivAt Y u s) (h0 : Y s≠0) :
    HasDerivAt (fun t => ‖Y t‖) (dot (Y s) u / ‖Y s‖) s := by
  have hn := (hY.differentiableAt.norm ℝ h0).hasDerivAt
  have he := (hn.pow 2).unique hY.norm_sq
  simp only [Nat.cast_ofNat,Nat.reduceSub,pow_one,← dot_eq_inner] at he
  have hr : ‖Y s‖≠0 := norm_ne_zero_iff.mpr h0
  have he' : deriv (fun t => ‖Y t‖) s = dot (Y s) u / ‖Y s‖ := by
    apply (eq_div_iff hr).mpr
    linarith
  rwa [he'] at hn

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


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


lemma hasDerivAt_momentumDirection {V : ℝ → Vec} {K : Vec} {t : ℝ}
    (hV : HasDerivAt V K t) (hv : V t ≠ 0) :
    HasDerivAt (momentumDirection ∘ V)
      (‖V t‖⁻¹ • transverseProjection (V t) K) t := by
  have hn := hasDerivAt_norm_nonzero hV hv
  have hh := (hn.inv (norm_ne_zero_iff.mpr hv)).smul hV
  convert hh using 1 <;> try rfl
  ext i
  simp only [Pi.inv_apply,transverseProjection,velocityProjection,dot_smul_left,
      PiLp.smul_apply,PiLp.add_apply,PiLp.sub_apply,smul_eq_mul]
  field_simp
  ring

lemma hasDerivAt_angularMultiplier {V : ℝ → Vec} {K : Vec} {t : ℝ}
    (hV : HasDerivAt V K t) (hv : V t ≠ 0) (w : ℝ) (h : Vec) :
    HasDerivAt (fun r => angularMultiplier w (V r) h)
      ((-w/‖V t‖^2) •
        (dot (momentumDirection (V t)) K • transverseProjection (V t) h +
         dot (momentumDirection (V t)) h • transverseProjection (V t) K +
         dot (transverseProjection (V t) K) h • momentumDirection (V t))) t := by
  have hn := hasDerivAt_norm_nonzero hV hv
  have hξ := hasDerivAt_momentumDirection hV hv
  have hP := (hasDerivAt_const t h).sub
    ((hasDerivAt_dot hξ (hasDerivAt_const t h)).smul hξ)
  have hh := ((hasDerivAt_const t w).div hn (norm_ne_zero_iff.mpr hv)).smul hP
  convert hh using 1 <;> try rfl
  ext i
  simp only [Pi.div_apply,Pi.sub_apply,Pi.smul_apply',momentumDirection,transverseProjection,velocityProjection,dot_smul_left,
      dot_sub_left,dot_zero_right_rvm,Function.comp_apply,zero_add,zero_sub,
      PiLp.smul_apply,PiLp.add_apply,PiLp.sub_apply,PiLp.neg_apply,smul_eq_mul,
      zero_mul]
  field_simp
  ring

lemma selectedDyadicCutoff_mem_unit {ι : Type*} [Fintype ι] {x : ι→ℝ}
    (hp : ∀ i,0<x i) (h1 : ∀ i,x i≤1) (S : Set (ι→ℕ)) :
    selectedDyadicCutoff S x∈Icc (0:ℝ) 1 := by
  classical
  obtain ⟨N,hN,he⟩ := selectedDyadicCutoff_curve_eventually
    (t:=0) (g:=fun i (_r : ℝ)=>x i) (fun _=>continuousAt_const) hp S
  have hh := he.eq_of_nhds
  change selectedDyadicCutoff S x = ∑ n∈selectedDyadicBox N S,dyadicMultiFactor n x at hh
  rw [hh]
  refine ⟨Finset.sum_nonneg (fun n _=>dyadicMultiFactor_nonneg n x),?_⟩
  calc
    _ ≤ ∑ n∈dyadicBox ι N,dyadicMultiFactor n x := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (fun n _ _=>dyadicMultiFactor_nonneg n x)
    _ = 1 := sum_dyadicMultiFactor_eq_one N x h1 hN

lemma transverseCLM_apply (v h : Vec) : transverseCLM v h=transverseProjection v h := by
  simp only [transverseCLM,sub_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply,InnerProductSpace.toDual_apply_apply,← dot_eq_inner]
  rfl

lemma angularMultiplierCLM_apply (w : ℝ) (v h : Vec) :
    angularMultiplierCLM w v h=angularMultiplier w v h := by
  simp only [angularMultiplierCLM,smul_apply,transverseCLM_apply,angularMultiplier]

lemma contDiffAt_transverseCLM {v : Vec} (hv : v≠0) {k : ℕ∞ω}
    (hk : k≤((⊤ : ℕ∞) : ℕ∞ω)) : ContDiffAt ℝ k transverseCLM v := by
  have hξ : ContDiffAt ℝ k momentumDirection v :=
    ((contDiffAt_id.norm ℝ hv).inv (norm_ne_zero_iff.mpr hv)).smul contDiffAt_id
  exact contDiffAt_const.sub (((InnerProductSpace.toDual ℝ Vec).contDiff.of_le hk).contDiffAt.comp v hξ |>.smulRight hξ)

lemma contDiffAt_angularMultiplierCLM (w : ℝ) {v : Vec} (hv : v≠0) {k : ℕ∞ω}
    (hk : k≤((⊤ : ℕ∞) : ℕ∞ω)) : ContDiffAt ℝ k (angularMultiplierCLM w) v := by
  exact (contDiffAt_const.div (contDiffAt_id.norm ℝ hv) (norm_ne_zero_iff.mpr hv)).smul
    (contDiffAt_transverseCLM hv hk)

lemma angularDerivativeCLM_apply (w : ℝ) (v K h : Vec) :
    angularDerivativeCLM w v K h = (-w/‖v‖^2) •
      (dot (momentumDirection v) K • transverseProjection v h +
       dot (momentumDirection v) h • transverseProjection v K +
       dot (transverseProjection v K) h • momentumDirection v) := by
  simp only [angularDerivativeCLM,smul_apply,add_apply,
    transverseCLM_apply,ContinuousLinearMap.smulRight_apply,InnerProductSpace.toDual_apply_apply,← dot_eq_inner]

lemma hasDerivAt_angularMultiplierCLM {V : ℝ→Vec} {K : Vec} {t : ℝ}
    (hV : HasDerivAt V K t) (hv : V t≠0) (w : ℝ) :
    HasDerivAt (fun r=>angularMultiplierCLM w (V r)) (angularDerivativeCLM w (V t) K) t := by
  have hd := ((contDiffAt_angularMultiplierCLM w hv (k:=1) (by simp)).differentiableAt one_ne_zero).comp t hV.differentiableAt
  have he : deriv (fun r=>angularMultiplierCLM w (V r)) t=angularDerivativeCLM w (V t) K := by
    apply ContinuousLinearMap.ext
    intro h
    have hh := hd.hasDerivAt.clm_apply (hasDerivAt_const t h)
    simp only [ContinuousLinearMap.map_zero,add_zero,Function.comp_apply,angularMultiplierCLM_apply] at hh
    exact hh.unique (by simpa only [angularDerivativeCLM_apply] using hasDerivAt_angularMultiplier hV hv w h)
  rw [←he]
  exact hd.hasDerivAt



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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_AngularBump
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
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma extendedAngularCLM_contDiff (w : ℝ) (hw : 0<w) :
    ContDiff ℝ ∞ (extendedAngularCLM w hw) := by
  rw [contDiff_iff_contDiffAt]
  intro v
  by_cases hv : v=0
  · subst v
    apply (contDiffAt_const (c:=(0:Vec→L[ℝ]Vec))).congr_of_eventuallyEq
    have he := (angularZeroBump w hw).eventuallyEq_one_of_mem_ball
      (show (0:Vec)∈ball 0 (angularZeroBump w hw).rIn by simpa only [mem_ball,dist_self,angularZeroBump] using div_pos hw (by norm_num : (0:ℝ)<64))
    filter_upwards [he] with v hv
    change (1-angularZeroBump w hw v) • angularMultiplierCLM w v=0
    simp only [hv,Pi.one_apply,sub_self]
    exact zero_smul ℝ (angularMultiplierCLM w v)
  · exact ((contDiffAt_const.sub (angularZeroBump w hw).contDiff.contDiffAt).smul
      (contDiffAt_angularMultiplierCLM w hv le_rfl))

lemma extendedAngularCLM_eq (w : ℝ) (hw : 0<w) {v : Vec} (hv : w/32≤‖v‖) :
    extendedAngularCLM w hw v=angularMultiplierCLM w v := by
  have hz := (angularZeroBump w hw).zero_of_le_dist (by simpa only [dist_zero_right,angularZeroBump] using hv)
  simp only [extendedAngularCLM,hz,sub_zero,one_smul]

lemma extendedAngularCLM_eventuallyEq (w : ℝ) (hw : 0<w) {v : Vec} (hv : w/32<‖v‖) :
    extendedAngularCLM w hw =ᶠ[𝓝 v] angularMultiplierCLM w := by
  have he : ∀ᶠ z : Vec in 𝓝 v,w/32<‖z‖ := continuous_norm.continuousAt.eventually (lt_mem_nhds hv)
  filter_upwards [he] with z hz
  exact extendedAngularCLM_eq w hw hz.le

lemma hasDerivAt_extendedAngularCLM {V : ℝ→Vec} {K : Vec} {t : ℝ}
    (hV : HasDerivAt V K t) (w : ℝ) (hw : 0<w) :
    HasDerivAt (fun r=>extendedAngularCLM w hw (V r))
      (fderiv ℝ (extendedAngularCLM w hw) (V t) K) t :=
  ((extendedAngularCLM_contDiff w hw).differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt t hV

lemma extendedAngularCLM_fderiv (w : ℝ) (hw : 0<w) {v : Vec} (hv : w/32<‖v‖) (K : Vec) :
    fderiv ℝ (extendedAngularCLM w hw) v K=angularDerivativeCLM w v K := by
  have hv0 : v≠0 := norm_pos_iff.mp ((div_pos hw (by norm_num : (0:ℝ)<32)).trans hv)
  have hcurve : HasDerivAt (fun r : ℝ=>v+r • K) K 0 := by
    convert (hasDerivAt_const (0:ℝ) v).add ((hasDerivAt_id (0:ℝ)).smul_const K) using 1 <;> first | rfl | simp only [one_smul,zero_add]
  have ht : Tendsto (fun r : ℝ=>v+r • K) (𝓝 0) (𝓝 v) := by
    have hc : Tendsto (fun r : ℝ=>v+r • K) (𝓝 0) (𝓝 (v+(0:ℝ) • K)) := hcurve.continuousAt
    simpa only [zero_smul,add_zero] using hc
  have he := (extendedAngularCLM_eventuallyEq w hw hv).comp_tendsto ht
  have ha := (hasDerivAt_angularMultiplierCLM hcurve (by simpa using hv0) w).congr_of_eventuallyEq he
  have hb := hasDerivAt_extendedAngularCLM hcurve w hw
  simpa only [zero_smul,add_zero] using hb.unique ha

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Continuation_PrefixMomentumForce
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
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma prefixAngular_highband {s : Solution} {α : Phase→ℝ→Phase} {T t w : ℝ}
    (hw : 0<w) (z : Phase) (ht : t∈Icc 0 T) (hv : w/16≤‖(α z t).2‖) :
    prefixAngularMultiplier s α T w hw z t=angularMultiplierCLM w (α z t).2 ∧
    prefixAngularRate s α T w hw z t=angularDerivativeCLM w (α z t).2
      (lorentzField s.E s.B (t,α z t)).2 := by
  have hnorm : w/32<‖(α z t).2‖ := by linarith
  simp only [prefixAngularMultiplier,prefixAngularRate,prefixMomentumForce,prefixFlow,prefixClamp_eq ht]
  exact ⟨extendedAngularCLM_eq w hw hnorm.le,extendedAngularCLM_fderiv w hw hnorm _⟩

end RVM

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_SourceWaveSpatialIbp
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
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma normalisedElectricKernel_eq {r : ℝ} (hr : r≠0) (n u b : Vec) :
    normalisedElectricKernel r n u b=r^2 • physicalElectricKernel r n u b := by
  ext i
  simp only [normalisedElectricKernel,physicalElectricKernel,PiLp.add_apply,PiLp.smul_apply,
    PiLp.sub_apply,smul_eq_mul]
  field_simp

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

lemma physical_force_kernel (r : ℝ) (n a v b : Vec) (hr : r≠0) (hn : ‖n‖=1) :
    (1-dot n (velocity v)) • receiverQ a n (physicalElectricKernel r n (velocity v) b) =
      forceTransportKernel r n a v+forceSourceKernel r n a v b := by
  have hd := (cone_denom_pos v n hn).ne'
  have hq := (q_pos v).ne'
  have h1 : (1-dot n (velocity v))*((1-dot (velocity v) (velocity v))/(r^2*(1-dot n (velocity v))^3)) =
      (r^2*(q v)^2*(1-dot n (velocity v))^2)⁻¹ := by
    rw [velocity_self]
    field_simp
    ring
  have h2 : (1-dot n (velocity v))*(r*(1-dot n (velocity v))^3)⁻¹ =
      (r*(1-dot n (velocity v))^2)⁻¹ := by
    field_simp
  simp only [physicalElectricKernel,receiverQ_add,receiverQ_smul,smul_add,smul_smul,h1,h2,
    forceTransportKernel,forceSourceKernel,sourceNumerator]

lemma forceSourceKernel_bound (r : ℝ) (n w v E B : Vec) (hr : 0 < r) (hn : ‖n‖=1) :
    ‖forceSourceKernel r n (velocity w) v (fderiv ℝ velocity v (E+cross (velocity v) B))‖ ≤
      (10*Real.sqrt (2*(1-dot n (velocity w))))/(r*q v*(1-dot n (velocity v)))*
        (goodField E B n+(1-dot n (velocity v))*‖B‖) := by
  have hd := cone_denom_pos v n hn
  have hq := q_pos v
  unfold forceSourceKernel
  rw [norm_smul,Real.norm_of_nonneg (by positivity)]
  apply (mul_le_mul_of_nonneg_left (receiverQ_source_bound w v E B n hn) (by positivity)).trans_eq
  field_simp

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_IntegralBallPolarFlip
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
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma normalisedSignedForce_flux {r : ℝ} (n a v b : Vec)
    (hr : r≠0) (hn : ‖n‖=1) (hD : 1-dot n a≠0) :
    (1-dot n a) • normalisedSignedForce r a (velocity v) n b=
      r^2 • (forceTransportKernel r n a v+forceSourceKernel r n a v b) := by
  rw [normalisedSignedForce,smul_smul]
  have hc : (1-dot n a)*((1-dot n (velocity v))/(1-dot n a))=1-dot n (velocity v) := by
    field_simp
  rw [hc,normalisedElectricKernel_eq hr,receiverQ_smul,smul_comm,
    ←physical_force_kernel r n a v b hr hn]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_RepresentativeClosedBinSourceIndices
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

lemma angularMultiplierCLM_norm_le {w : ℝ} (hw : 0<w) {v : Vec}
    (hv : w/64 ≤ ‖v‖) : ‖angularMultiplierCLM w v‖ ≤ 64 := by
  have hρ : 0<‖v‖ := (div_pos hw (by norm_num)).trans_le hv
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro h
  rw [angularMultiplierCLM_apply,angularMultiplier,norm_smul,Real.norm_eq_abs,
    abs_of_pos (div_pos hw hρ)]
  apply mul_le_mul _ (transverseProjection_norm v h) (norm_nonneg _) (by norm_num)
  apply (div_le_iff₀ hρ).mpr
  linarith only [hv]

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_SourceMajorant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma forceSourceKernel_le_majorant {r : ℝ} (n W v E B : Vec)
    (hr : 0 < r) (hn : ‖n‖=1) :
    ‖forceSourceKernel r n (velocity W) v
      (fderiv ℝ velocity v (E+cross (velocity v) B))‖≤ sourceMajorantKernel r n W v E B := by
  have hd := cone_denom_pos v n hn
  apply (forceSourceKernel_bound r n W v E B hr hn).trans_eq
  unfold sourceMajorantKernel
  field_simp

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_SelectedRemainderPhysical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma selectedConeTriangle_norm_le {s : Solution} {α : Phase→ℝ→Phase} {zX : Phase} {T : ℝ}
    (Q : Set (Fin 4→ℕ)) (A : ConeKernelState→Vec) (W : ℝ→Vec→L[ℝ]Vec) (J : Set ℝ)
    (p : TrianglePhase) :
    ‖selectedConeTriangle s α zX T Q A W J p‖≤
      ‖J.indicator W p.1.1 (triangleConeKernel s α zX T A p)‖ := by
  classical
  by_cases hp : p∈trianglePhaseDomain T
  · have hr : 0<p.1.1-p.1.2.1 := sub_pos.mpr hp.2.2
    have hrT : p.1.1-p.1.2.1≤ max 1 T := by
      linarith only [hp.1.2,hp.2.1,le_max_right (1:ℝ) T]
    have hu := selectedDyadicCutoff_mem_unit
      (physicalCutoffCoordinates_pos (T:=T) (v:=p.2) (w:=(α zX p.1.1).2) (sphere_norm p.1.2.2) hr)
      (physicalCutoffCoordinates_le_one (T:=T) (sphere_norm p.1.2.2) hrT) Q
    have he : selectedConeTriangle s α zX T Q A W J p=
        stateCutoff T Q (p.1.1-p.1.2.1,p.1.2.2.1,p.2,(α zX p.1.1).2) •
          J.indicator W p.1.1 (triangleConeKernel s α zX T A p) := by
      simp only [selectedConeTriangle,triangleConeKernel,Set.indicator_of_mem hp,
        selectedConeKernel,coneCutoffState,triangleKernelState,map_smul]
      module
    rw [he,norm_smul,Real.norm_eq_abs]
    change |selectedDyadicCutoff Q _| * _ ≤ _
    rw [abs_of_nonneg hu.1]
    exact (mul_le_mul_of_nonneg_right hu.2 (norm_nonneg _)).trans_eq (one_mul _)
  · simp only [selectedConeTriangle,triangleConeKernel,Set.indicator_of_notMem hp,map_zero]
    exact le_rfl

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ConeForceSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma forceSourceKernel_zero (r : ℝ) (n a v : Vec) : forceSourceKernel r n a v 0=0 := by
  simp [forceSourceKernel,sourceNumerator,dot,receiverQ]

lemma normalised_transport_flux {r : ℝ} (n W v : Vec) (hr : r≠0) (hn : ‖n‖=1) :
    (1-dot n (velocity W)) • normalisedSignedForce r (velocity W) (velocity v) n 0=
      r^2 • forceTransportKernel r n (velocity W) v := by
  rw [normalisedSignedForce_flux _ _ _ _ hr hn (cone_denom_pos W n hn).ne',
    forceSourceKernel_zero,add_zero]

lemma normalised_source_flux {r : ℝ} (n W v b : Vec) (hr : r≠0) (hn : ‖n‖=1) :
    (1-dot n (velocity W)) •
      (normalisedSignedForce r (velocity W) (velocity v) n b-
       normalisedSignedForce r (velocity W) (velocity v) n 0)=
      r^2 • forceSourceKernel r n (velocity W) v b := by
  rw [smul_sub,normalisedSignedForce_flux _ _ _ _ hr hn (cone_denom_pos W n hn).ne',
    normalised_transport_flux n W v hr hn,smul_add,add_sub_cancel_left]

lemma triangleConeKernel_source {s : Solution} {α : Phase→ℝ→Phase} {zX : Phase} {T : ℝ}
    {p : TrianglePhase} (hp : p∈trianglePhaseDomain T) :
    triangleConeKernel s α zX T (sourceOnlyConeKernel s α zX) p=
      (p.1.1-p.1.2.1)^2 • (s.f (p.1.2.1,((α zX p.1.1).1-(p.1.1-p.1.2.1) • p.1.2.2.1,p.2)) •
        forceSourceKernel (p.1.1-p.1.2.1) p.1.2.2.1 (velocity (α zX p.1.1).2) p.2
          (sourceAcceleration s (p.1.2.1,((α zX p.1.1).1-(p.1.1-p.1.2.1) • p.1.2.2.1,p.2)))) := by
  simp only [triangleConeKernel,Set.indicator_of_mem hp,sourceOnlyConeKernel,sourceForceConeKernel,
    transportOnlyConeKernel,triangleKernelState]
  rw [smul_comm,normalised_source_flux _ _ _ _ (sub_pos.mpr hp.2.2).ne' (sphere_norm _),smul_comm]

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma PhaseFlowOn.selectedSourceTriangle_majorant_le_oai {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hw : 0<w) (zX : Phase) (Q : Set (Fin 4→ℕ))
    {J : Set ℝ} (hJT : J⊆Icc 0 T) (hband : ∀t∈J,w/16≤‖(F.flow zX t).2‖)
    (B : ClosedConeBin) {z : ConeCoordinate}
    (hz : z∈physicalBinBase (fun t=>(prefixFlow F.flow T zX t).2) B J) :
    (∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (prefixFlow F.flow T zX z.1).2),
      ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T Q (sourceOnlyConeKernel s F.flow zX)
        (prefixAngularMultiplier s F.flow T w hw zX) J (z,v)‖)≤
      ENNReal.ofReal 64*physicalSourceMajorantDensity s (fun t=>(prefixFlow F.flow T zX t).1)
        (fun t=>(prefixFlow F.flow T zX t).2) B z := by
  classical
  unfold physicalSourceMajorantDensity
  rw [←mul_assoc,←lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
  apply lintegral_mono
  intro v
  apply (ENNReal.ofReal_le_ofReal (selectedConeTriangle_norm_le Q _ _ J (z,v))).trans
  rw [Set.indicator_of_mem hz.1]
  by_cases hp : (z,v)∈trianglePhaseDomain T
  · have ht := hJT hz.1
    have hσ : z.2.1∈Icc 0 T := ⟨hp.2.1.le,hp.2.2.le.trans ht.2⟩
    have hf := hs.nonnegative z.2.1 hσ ((F.flow zX z.1).1-(z.1-z.2.1) • z.2.2.1,v)
    rw [(prefixAngular_highband hw zX ht (hband _ hz.1)).1,triangleConeKernel_source hp]
    have hbound : ‖angularMultiplierCLM w (F.flow zX z.1).2‖≤64 :=
      angularMultiplierCLM_norm_le hw (by linarith only [hband _ hz.1,hw])
    have hn := (angularMultiplierCLM w (F.flow zX z.1).2).le_opNorm
      ((z.1-z.2.1)^2 • (s.f (z.2.1,((F.flow zX z.1).1-(z.1-z.2.1) • z.2.2.1,v)) •
        forceSourceKernel (z.1-z.2.1) z.2.2.1 (velocity (F.flow zX z.1).2) v
          (sourceAcceleration s (z.2.1,((F.flow zX z.1).1-(z.1-z.2.1) • z.2.2.1,v)))))
    apply (ENNReal.ofReal_le_ofReal (hn.trans (mul_le_mul_of_nonneg_right hbound (norm_nonneg _)))).trans
    simp only [prefixFlow,prefixClamp_eq ht]
    rw [←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤64),←ENNReal.ofReal_mul (by positivity : (0:ℝ)≤64*(z.1-z.2.1)^2)]
    apply ENNReal.ofReal_le_ofReal
    simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (z.1-z.2.1)),abs_of_nonneg hf]
    have hh := forceSourceKernel_le_majorant z.2.2.1 (F.flow zX z.1).2 v
      (s.E (z.2.1,(F.flow zX z.1).1-(z.1-z.2.1) • z.2.2.1))
      (s.B (z.2.1,(F.flow zX z.1).1-(z.1-z.2.1) • z.2.2.1)) (sub_pos.mpr hp.2.2) (sphere_norm _)
    dsimp only [sourceAcceleration,lorentzField,lorentzPhase] at ⊢
    nlinarith only [mul_le_mul_of_nonneg_left hh (mul_nonneg (sq_nonneg (z.1-z.2.1)) hf)]
  · simp only [triangleConeKernel,Set.indicator_of_notMem hp,map_zero,norm_zero,ENNReal.ofReal_zero]
    exact bot_le

end RVM

end

end OAI
end

theorem solution : type_of% @OAI.RVM.PhaseFlowOn.selectedSourceTriangle_majorant_le_oai := @OAI.RVM.PhaseFlowOn.selectedSourceTriangle_majorant_le_oai
