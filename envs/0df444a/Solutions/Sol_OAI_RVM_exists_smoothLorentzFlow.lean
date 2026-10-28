-- Prove2me | solution 1 for OAI.RVM.exists_smoothLorentzFlow
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:25:49.163454+00:00
-- url     : https://prove2.me/submissions/63c6faf0-de47-4dbd-8fe9-10b032f68a31

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000

section
-- module Solutions.OAIQ073_VM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
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

lemma dot_smul_left (r : ℝ) (a b : Vec) : dot (r • a) b = r * dot a b := by
  simp [dot, mul_assoc, Finset.mul_sum]

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

lemma spatialPartial_velocity (v : Vec) (i j : Fin 3) :
    spatialPartial (fun w => velocity w j) v i =
      (q v)⁻¹ * ((if i=j then 1 else 0)-velocity v i*velocity v j) := by
  have hv : DifferentiableAt ℝ velocity v := contDiff_velocity.differentiable (by simp : (1 : ℕ∞ω) ≠ 0) v
  have hj := (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) j).hasFDerivAt.comp v hv.hasFDerivAt
  have hp := congrArg (fun L : Vec →L[ℝ] ℝ => L (basis i)) hj.fderiv
  have h : spatialPartial (fun w => velocity w j) v i =
      (fderiv ℝ velocity v (basis i)) j := by
    convert hp using 1 <;> rfl
  rw [h, fderiv_velocity_apply]
  simp [basis, dot, eq_comm]

lemma spatialPartial_mul {f g : Vec → ℝ} {x : Vec}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 3) :
    spatialPartial (fun y => f y*g y) x i =
      f x*spatialPartial g x i+g x*spatialPartial f x i := by
  change fderiv ℝ (f*g) x (basis i) = _
  rw [fderiv_mul hf hg]
  rfl

lemma spatialPartial_sub {f g : Vec → ℝ} {x : Vec}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 3) :
    spatialPartial (fun y => f y-g y) x i =
      spatialPartial f x i-spatialPartial g x i := by
  change fderiv ℝ (f-g) x (basis i) = _
  rw [fderiv_sub hf hg]
  rfl

lemma divergence_magnetic_force (v B : Vec) :
    divergence (fun w => cross (velocity w) B) v = 0 := by
  have hd (j : Fin 3) : DifferentiableAt ℝ (fun w : Vec => velocity w j) v :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) j).differentiableAt.comp v
      (contDiff_velocity.differentiable (by simp : (1 : ℕ∞ω) ≠ 0) v)
  simp only [divergence, Fin.sum_univ_succ]
  change spatialPartial (fun w => velocity w 1 * B 2 - velocity w 2 * B 1) v 0 +
    (spatialPartial (fun w => velocity w 2 * B 0 - velocity w 0 * B 2) v 1 +
    (spatialPartial (fun w => velocity w 0 * B 1 - velocity w 1 * B 0) v 2 + 0)) = 0
  simp only [spatialPartial_sub ((hd _).mul_const _) ((hd _).mul_const _),
    spatialPartial_mul (hd _) (differentiableAt_const _), spatialPartial_velocity]
  simp [spatialPartial]
  ring

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Maxwell_Variational
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
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory Metric
open scoped Topology Pointwise
open Set MeasureTheory Filter
open scoped Topology NNReal

namespace RVM
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma taylor_bound_lipschitz_derivative {f : E → E} {s : Set E} {L : ℝ≥0}
    (hs : Convex ℝ s) (hf : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hL : LipschitzOnWith L (fderiv ℝ f) s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    ‖f y-f x-fderiv ℝ f x (y-x)‖ ≤ L * ‖y-x‖^2 := by
  have hsub : segment ℝ x y ⊆ s := hs.segment_subset hx hy
  have hseg (z : E) (hz : z ∈ segment ℝ x y) : ‖z-x‖ ≤ ‖y-x‖ := by
    simpa only [Metric.mem_closedBall,dist_eq_norm] using ((convex_closedBall x ‖y-x‖).segment_subset (by simp : x ∈ Metric.closedBall x ‖y-x‖)
      (by simp [dist_eq_norm] : y ∈ Metric.closedBall x ‖y-x‖)) hz
  have h := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le'
    (fun z hz => hf z (hsub hz))
    (fun z hz => (hL.norm_sub_le (hsub hz) hx).trans
      (mul_le_mul_of_nonneg_left (hseg z hz) L.2))
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa [pow_two,mul_assoc] using h

lemma variational_remainder_bound
    {f : ℝ → E → E} {x y : ℝ → E} {A D : ℝ → E →L[ℝ] E}
    {a b K ε : ℝ} {v : E}
    (hx : ContinuousOn x (Icc a b)) (hy : ContinuousOn y (Icc a b))
    (hA : ContinuousOn A (Icc a b))
    (hxd : ∀ t ∈ Ico a b, HasDerivWithinAt x (f t (x t)) (Ici t) t)
    (hyd : ∀ t ∈ Ico a b, HasDerivWithinAt y (f t (y t)) (Ici t) t)
    (hAd : ∀ t ∈ Ico a b, HasDerivWithinAt A ((D t).comp (A t)) (Ici t) t)
    (hinit : y a-x a = A a v)
    (hK : ∀ t ∈ Ico a b, ‖D t‖ ≤ K)
    (hε : ∀ t ∈ Ico a b, ‖f t (y t)-f t (x t)-D t (y t-x t)‖ ≤ ε) :
    ∀ t ∈ Icc a b, ‖y t-x t-A t v‖ ≤ gronwallBound 0 K ε (t-a) := by
  have hd : ∀ t ∈ Ico a b, HasDerivWithinAt
      (fun s => y s-x s-A s v)
      (f t (y t)-f t (x t)-D t (A t v)) (Ici t) t := by
    intro t ht
    convert! ((hyd t ht).sub (hxd t ht)).sub ((hAd t ht).clm_apply (hasDerivWithinAt_const t (Ici t) v)) using 1; simp
  apply norm_le_gronwallBound_of_norm_deriv_right_le (δ := 0)
    ((hy.sub hx).sub (hA.clm_apply continuousOn_const)) hd
  · change ‖y a-x a-A a v‖ ≤ 0
    rw [hinit,sub_self,norm_zero]
  · intro t ht
    have heq : f t (y t)-f t (x t)-D t (A t v) =
        D t (y t-x t-A t v) + (f t (y t)-f t (x t)-D t (y t-x t)) := by
      simp only [map_sub]
      abel
    rw [heq]
    calc
      _ ≤ ‖D t (y t-x t-A t v)‖ + ‖f t (y t)-f t (x t)-D t (y t-x t)‖ := norm_add_le _ _
      _ ≤ K*‖y t-x t-A t v‖ + ε := add_le_add
        (((D t).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hK t ht) (norm_nonneg _)))
        (hε t ht)

lemma hasFDerivAt_of_quadratic_bound {g : E → E} {x : E} {A : E →L[ℝ] E}
    {C : ℝ} (_hC : 0 ≤ C)
    (h : ∀ᶠ y in 𝓝 x, ‖g y-g x-A (y-x)‖ ≤ C*‖y-x‖^2) : HasFDerivAt g A x := by
  rw [hasFDerivAt_iff_tendsto]
  apply squeeze_zero' (g := fun y => C*‖y-x‖) (Eventually.of_forall (fun y => mul_nonneg (inv_nonneg.mpr (norm_nonneg _))
    (norm_nonneg _))) ?_ ?_
  · filter_upwards [h] with y hy
    calc
      ‖y-x‖⁻¹*‖g y-g x-A (y-x)‖ ≤ ‖y-x‖⁻¹*(C*‖y-x‖^2) :=
        mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr (norm_nonneg _))
      _ ≤ C*‖y-x‖ := by
        by_cases heq : y = x
        · simp [heq]
        · have hh : ‖y-x‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr heq)
          exact le_of_eq (by field_simp)
  · have ht : Tendsto (fun y : E => C*‖y-x‖) (𝓝 x) (𝓝 (C*‖x-x‖)) := by
      exact (continuous_const.mul (continuous_id.sub continuous_const).norm).tendsto x
    simpa using ht
end RVM

open Set MeasureTheory Metric ODE
open scoped Topology NNReal

namespace RVM

lemma picard_flow_with_range {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax}
    {x₀ : E} {a r L K : ℝ≥0}
    (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ∃ α : E → ℝ → E,
      (∀ x ∈ closedBall x₀ r, α x t₀ = x ∧
        (∀ t ∈ Icc tmin tmax, HasDerivWithinAt (α x) (f t (α x t)) (Icc tmin tmax) t) ∧
        ∀ t, α x t ∈ closedBall x₀ a) ∧
      ∃ L' : ℝ≥0, ∀ t ∈ Icc tmin tmax, LipschitzOnWith L' (α · t) (closedBall x₀ r) := by
  classical
  have (x) (hx : x ∈ closedBall x₀ r) := FunSpace.exists_isFixedPt_next hf hx
  choose α hα using this
  set α' := fun (x : E) ↦ if hx : x ∈ closedBall x₀ r then
    α x hx |>.compProj else 0 with hα'
  refine ⟨α', fun x hx ↦ ⟨?_, fun t ht ↦ ?_, fun t => ?_⟩, ?_⟩
  · rw [hα']
    beta_reduce
    rw [dite_eq_left hx, FunSpace.compProj_val, ← hα, FunSpace.next_apply₀]
  · rw [hα']
    beta_reduce
    rw [dite_eq_left hx, FunSpace.compProj_apply]
    apply hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
      (α x hx |>.continuous_compProj.continuousOn)
      (fun _ ht' ↦ α x hx |>.compProj_mem_closedBall hf.mul_max_le)
      x ht |>.congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hα]
    rw [FunSpace.compProj_of_mem ht', FunSpace.next_apply]
  · simp only [hα',dite_eq_left hx]
    exact (α x hx).compProj_mem_closedBall hf.mul_max_le
  · obtain ⟨L', h⟩ := FunSpace.exists_forall_closedBall_funSpace_dist_le_mul hf
    refine ⟨L', fun t ht ↦ LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_⟩
    simp_rw [hα']
    rw [dite_eq_left hx, dite_eq_left hy, FunSpace.compProj_apply, FunSpace.compProj_apply,
      ← FunSpace.toContinuousMap_apply_eq_apply, ← FunSpace.toContinuousMap_apply_eq_apply]
    have : Nonempty (Icc tmin tmax) := ⟨t₀⟩
    apply ContinuousMap.dist_le_iff_of_nonempty.mp
    exact h x y hx hy (α x hx) (α y hy) (hα x hx) (hα y hy)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_FlowDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory Metric
open scoped Topology Pointwise
open Set MeasureTheory Filter
open Set MeasureTheory Metric ODE
open scoped Topology NNReal

open Set MeasureTheory

namespace RVM

lemma determinant_derivative {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ℝ → Matrix ι ι ℝ} {A' : Matrix ι ι ℝ} {t : ℝ}
    (hA : HasDerivAt A A' t) :
    HasDerivAt (fun s => (A s).det)
      (∑ i, ((A t).updateRow i (A' i)).det) t := by
  have h := ((determinantMultilinear ι).hasFDerivAt (A t)).comp_hasDerivAt t hA
  have hd : ((determinantMultilinear ι).linearDeriv (A t)) A' =
      ∑ i, ((A t).updateRow i (A' i)).det := by
    erw [ContinuousMultilinearMap.linearDeriv_apply]
    rfl
  rw [hd] at h
  exact h

lemma determinant_row_mul_derivative {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A C : Matrix ι ι ℝ) :
    (∑ i, (A.updateRow i ((C*A) i)).det) = C.trace * A.det := by
  have hrow (i : ι) : (C*A) i = ∑ j, C i j • A j := by
    ext k
    simp [Matrix.mul_apply,Finset.sum_apply]
  simp_rw [hrow,Matrix.det_updateRow_sum,smul_eq_mul]
  rw [← Finset.sum_mul]
  rfl

lemma determinant_variational_derivative {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ℝ → Matrix ι ι ℝ} {C : Matrix ι ι ℝ} {t : ℝ}
    (hA : HasDerivAt A (C*A t) t) :
    HasDerivAt (fun s => (A s).det) (C.trace*(A t).det) t := by
  simpa only [determinant_row_mul_derivative] using determinant_derivative hA

lemma determinant_eq_one_of_trace_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A C : ℝ → Matrix ι ι ℝ} {a b : ℝ} (hab : a ≤ b)
    (hA : ContinuousOn A (Icc a b)) (hinit : A a = 1)
    (hder : ∀ t ∈ Ioo a b, HasDerivAt A (C t*A t) t)
    (htrace : ∀ t ∈ Ioo a b, (C t).trace = 0) :
    ∀ t ∈ Icc a b, (A t).det = 1 := by
  have hcont : ContinuousOn (fun t => (A t).det) (Icc a b) :=
    continuous_id.matrix_det.comp_continuousOn hA
  have hz : ∀ t ∈ Ioo a b, HasDerivAt (fun s => (A s).det) 0 t := by
    intro t ht
    simpa [htrace t ht] using determinant_variational_derivative (hder t ht)
  rcases hab.eq_or_lt with heq | hlt
  · subst b
    intro t ht
    have : t = a := le_antisymm ht.2 ht.1
    simp [this,hinit]
  obtain ⟨c,hc⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero
    (convex_Ioo a b).isPreconnected
    (fun x hx => (hz x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hz x hx).deriv)
  have heq : EqOn (fun t => (A t).det) (fun _ => c) (Icc a b) := by
    rw [← closure_Ioo hlt.ne] at hcont ⊢
    exact Set.EqOn.of_subset_closure hc hcont continuousOn_const subset_closure Subset.rfl
  have ha := heq (left_mem_Icc.mpr hab)
  have hc1 : c = 1 := by simpa [hinit] using ha.symm
  intro t ht
  exact (heq ht).trans hc1

end RVM

end

open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory Metric
open scoped Topology Pointwise
open Set MeasureTheory Filter
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open Set MeasureTheory

namespace RVM
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]

lemma endomorphismMatrix_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) (A : E →L[ℝ] E) :
    endomorphismMatrix b A = LinearMap.toMatrix b b A.toLinearMap := rfl

lemma endomorphismMatrix_comp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) (A C : E →L[ℝ] E) :
    endomorphismMatrix b (C.comp A) = endomorphismMatrix b C * endomorphismMatrix b A := by
  exact LinearMap.toMatrix_comp b b b _ _

lemma hasDerivAt_endomorphismMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) {A : ℝ → E →L[ℝ] E} {D : E →L[ℝ] E} {t : ℝ}
    (hA : HasDerivAt A D t) :
    HasDerivAt (fun s => endomorphismMatrix b (A s)) (endomorphismMatrix b D) t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have hd : HasDerivAt (fun s => A s (b j)) (D (b j)) t := by
    simpa using hA.clm_apply (hasDerivAt_const t (b j))
  have hh := (b.coord i).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hd
  simpa only [Function.comp_def,endomorphismMatrix_apply,LinearMap.toMatrix_apply,
    LinearMap.coe_toContinuousLinearMap',Module.Basis.coord_apply,ContinuousLinearMap.coe_coe] using hh

lemma determinant_clm_eq_one_of_trace_zero
    {A C : ℝ → E →L[ℝ] E} {a b : ℝ} (hab : a ≤ b)
    (hA : ContinuousOn A (Icc a b)) (hinit : A a = ContinuousLinearMap.id ℝ E)
    (hder : ∀ t ∈ Ioo a b, HasDerivAt A ((C t).comp (A t)) t)
    (htrace : ∀ t ∈ Ioo a b, LinearMap.trace ℝ E (C t).toLinearMap = 0) :
    ∀ t ∈ Icc a b, (A t).det = 1 := by
  let e := Module.finBasis ℝ E
  have h := determinant_eq_one_of_trace_zero hab
    ((endomorphismMatrix e).continuous.comp_continuousOn hA)
    (show endomorphismMatrix e (A a) = 1 by
      rw [hinit,endomorphismMatrix_apply]
      exact LinearMap.toMatrix_id _)
    (A := fun t => endomorphismMatrix e (A t))
    (C := fun t => endomorphismMatrix e (C t))
    (fun t ht => by
      have hh := hasDerivAt_endomorphismMatrix e (hder t ht)
      simpa only [endomorphismMatrix_comp] using hh)
    (fun t ht => by
      rw [endomorphismMatrix_apply,← LinearMap.trace_eq_matrix_trace ℝ e]
      exact htrace t ht)
  simpa only [endomorphismMatrix_apply,LinearMap.det_toMatrix] using h

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_ParticleBySpacetime
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

lemma contDiff_lorentz (E B : Vec) {k : ℕ∞ω} :
    ContDiff ℝ k (fun v => E+cross (velocity v) B) := by
  exact contDiff_const.add (contDiff_cross.comp (contDiff_velocity.prodMk contDiff_const))

lemma divergence_lorentz (v E B : Vec) :
    divergence (fun w => E+cross (velocity w) B) v = 0 := by
  have hh (i : Fin 3) : spatialPartial (fun w => (E+cross (velocity w) B) i) v i =
      spatialPartial (fun w => cross (velocity w) B i) v i := by
    simp only [PiLp.add_apply, spatialPartial]
    rw [fderiv_const_add]
  simpa only [divergence, hh] using divergence_magnetic_force v B

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_LorentzPhase
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
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory Metric
open scoped Topology Pointwise
open Set MeasureTheory Filter
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open Set MeasureTheory
open scoped ContDiff

namespace RVM

lemma trace_prod_diagonal {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (L : (E × F) →ₗ[ℝ] E × F) :
    LinearMap.trace ℝ (E × F) L =
      LinearMap.trace ℝ E ((LinearMap.fst ℝ E F).comp (L.comp (LinearMap.inl ℝ E F))) +
      LinearMap.trace ℝ F ((LinearMap.snd ℝ E F).comp (L.comp (LinearMap.inr ℝ E F))) := by
  have heq : L = (LinearMap.inl ℝ E F).comp ((LinearMap.fst ℝ E F).comp L) +
      (LinearMap.inr ℝ E F).comp ((LinearMap.snd ℝ E F).comp L) := by
    ext z <;> simp
  calc
    _ = LinearMap.trace ℝ (E × F) ((LinearMap.inl ℝ E F).comp ((LinearMap.fst ℝ E F).comp L)) +
        LinearMap.trace ℝ (E × F) ((LinearMap.inr ℝ E F).comp ((LinearMap.snd ℝ E F).comp L)) := by
      conv_lhs => rw [heq, map_add]
    _ = _ := congrArg₂ (· + ·)
      (LinearMap.trace_comp_comm' (LinearMap.inl ℝ E F) ((LinearMap.fst ℝ E F).comp L)).symm
      (LinearMap.trace_comp_comm' (LinearMap.inr ℝ E F) ((LinearMap.snd ℝ E F).comp L)).symm

lemma trace_fderiv_eq_divergence {F : Vec → Vec} {x : Vec} (hF : DifferentiableAt ℝ F x) :
    LinearMap.trace ℝ Vec (fderiv ℝ F x).toLinearMap = divergence F x := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis]
  unfold Matrix.trace divergence spatialPartial
  apply Finset.sum_congr rfl
  intro i _
  have hd := (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp x hF.hasFDerivAt
  have hd' : fderiv ℝ (fun y => F y i) x = (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).comp (fderiv ℝ F x) := hd.fderiv
  rw [hd']
  simp only [Matrix.diag_apply,LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply,OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_coe,PiLp.proj_apply]
  rfl

lemma trace_lorentzPhase {E B : Vec → Vec} (hE : Differentiable ℝ E)
    (hB : Differentiable ℝ B) (z : Phase) :
    LinearMap.trace ℝ Phase (fderiv ℝ (lorentzPhase E B) z).toLinearMap = 0 := by
  have hF : DifferentiableAt ℝ (lorentzPhase E B) z := by
    exact (contDiff_velocity.differentiable (by simp : (1 : ℕ∞ω) ≠ 0) z.2 |>.comp z differentiableAt_snd).prodMk
      (((hE z.1).comp z differentiableAt_fst).add
        ((contDiff_cross.differentiable (by simp : (1 : ℕ∞ω) ≠ 0) _).comp z
          ((contDiff_velocity.differentiable (by simp : (1 : ℕ∞ω) ≠ 0) z.2 |>.comp z differentiableAt_snd).prodMk
            ((hB z.1).comp z differentiableAt_fst))))
  let D := fderiv ℝ (lorentzPhase E B) z
  have hleft : (LinearMap.fst ℝ Vec Vec).comp (D.toLinearMap.comp (LinearMap.inl ℝ Vec Vec)) = 0 := by
    have hd := hF.hasFDerivAt.fst.comp (f := fun x : Vec => (x,z.2)) z.1
      ((hasFDerivAt_id z.1).prodMk (hasFDerivAt_const z.2 z.1))
    have hc : HasFDerivAt (fun _ : Vec => velocity z.2) (0 : Vec →L[ℝ] Vec) z.1 := hasFDerivAt_const _ _
    have hh := hd.unique hc
    exact congrArg ContinuousLinearMap.toLinearMap hh
  have hright : (LinearMap.snd ℝ Vec Vec).comp (D.toLinearMap.comp (LinearMap.inr ℝ Vec Vec)) =
      (fderiv ℝ (fun v => E z.1 + cross (velocity v) (B z.1)) z.2).toLinearMap := by
    have hd := hF.hasFDerivAt.snd.comp (f := fun v : Vec => (z.1,v)) z.2
      ((hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id z.2))
    exact congrArg ContinuousLinearMap.toLinearMap hd.fderiv.symm
  rw [trace_prod_diagonal,hleft,hright,map_zero,zero_add,
    trace_fderiv_eq_divergence ((contDiff_lorentz (E z.1) (B z.1)).differentiable
      (by simp : (1 : ℕ∞ω) ≠ 0) z.2)]
  exact divergence_lorentz z.2 (E z.1) (B z.1)

end RVM

open Set MeasureTheory Metric
open scoped Topology ContDiff NNReal

namespace RVM

lemma exists_bounded_ode_on_Icc {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [FiniteDimensional ℝ H] {f : ℝ × H → H}
    {a b t₀ L : ℝ} (hab : a ≤ b) (ht₀ : t₀ ∈ Icc a b) (hL : 0 ≤ L)
    (hf : ContDiffOn ℝ 1 f (Icc a b ×ˢ (univ : Set H)))
    (hb : ∀ t ∈ Icc a b, ∀ z, ‖f (t,z)‖ ≤ L) (z₀ : H) :
    ∃ α : ℝ → H, α t₀ = z₀ ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt α (f (t,α t)) (Icc a b) t := by
  let R : ℝ≥0 := ⟨L*(b-a),mul_nonneg hL (sub_nonneg.mpr hab)⟩
  have hsub : Icc a b ×ˢ closedBall z₀ (R:ℝ) ⊆ Icc a b ×ˢ (univ : Set H) :=
    prod_mono_right (subset_univ _)
  obtain ⟨K,hK⟩ := (hf.mono hsub).exists_lipschitzOnWith (by norm_num)
    ((convex_Icc a b).prod (convex_closedBall z₀ (R:ℝ)))
    (isCompact_Icc.prod (isCompact_closedBall z₀ (R:ℝ)))
  have hpic : IsPicardLindelof (fun t z => f (t,z)) ⟨t₀,ht₀⟩ z₀ R 0 ⟨L,hL⟩ K := by
    refine ⟨?_,?_,?_,?_⟩
    · intro t ht
      apply LipschitzOnWith.of_dist_le_mul
      intro z hz w hw
      simpa using hK.dist_le_mul (t,z) (show (t,z) ∈ Icc a b ×ˢ closedBall z₀ (R:ℝ) from ⟨ht,hz⟩)
        (t,w) (show (t,w) ∈ Icc a b ×ˢ closedBall z₀ (R:ℝ) from ⟨ht,hw⟩)
    · intro z _
      exact hf.continuousOn.comp (continuousOn_id.prodMk continuousOn_const)
        (fun t ht => ⟨ht,mem_univ z⟩)
    · intro t ht z _
      exact hb t ht z
    · change L * max (b-t₀) (t₀-a) ≤ (R:ℝ)-0
      simp only [sub_zero]
      exact mul_le_mul_of_nonneg_left (max_le (by linarith [ht₀.1]) (by linarith [ht₀.2])) hL
  exact hpic.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Maxwell_ExtendedField
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
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Filter
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set MeasureTheory

open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace RVM
section TimeFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma det_time_triangular (L : (ℝ × E) →ₗ[ℝ] (ℝ × E))
    (hL : (LinearMap.fst ℝ ℝ E).comp L = LinearMap.fst ℝ ℝ E) :
    L.det = ((LinearMap.snd ℝ ℝ E).comp (L.comp (LinearMap.inr ℝ ℝ E))).det := by
  classical
  let b := Module.Basis.singleton Unit ℝ
  let c := Module.finBasis ℝ E
  let C := (LinearMap.snd ℝ ℝ E).comp (L.comp (LinearMap.inl ℝ ℝ E))
  let D := (LinearMap.snd ℝ ℝ E).comp (L.comp (LinearMap.inr ℝ ℝ E))
  have hf (z : ℝ × E) : (L z).1 = z.1 := LinearMap.congr_fun hL z
  have hm : LinearMap.toMatrix (b.prod c) (b.prod c) L =
      Matrix.fromBlocks 1 0 (LinearMap.toMatrix b c C) (LinearMap.toMatrix c c D) := by
    ext (i | i) (j | j)
    · simp [LinearMap.toMatrix, b, hf]
    · simp [LinearMap.toMatrix, b, hf]
    · simp [LinearMap.toMatrix, C]
    · simp [LinearMap.toMatrix, D]
  rw [← LinearMap.det_toMatrix (b.prod c), hm, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_one, one_mul, LinearMap.det_toMatrix]

end TimeFlow

lemma contDiff_lorentzField {E B : Field} {k : ℕ∞ω}
    (hE : ContDiff ℝ k E) (hB : ContDiff ℝ k B) : ContDiff ℝ k (lorentzField E B) := by
  have hx : ContDiff ℝ k (fun z : ℝ × Phase => (z.1,z.2.1)) :=
    contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)
  have hu : ContDiff ℝ k (fun z : ℝ × Phase => velocity z.2.2) :=
    contDiff_velocity.comp (contDiff_snd.comp contDiff_snd)
  exact hu.prodMk ((hE.comp hx).add (contDiff_cross.comp (hu.prodMk (hB.comp hx))))

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Maxwell_FiniteFlow
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
open scoped Topology ContDiff NNReal
open Set MeasureTheory
open Set MeasureTheory Filter
open scoped Topology ContDiff
open Set MeasureTheory Metric Filter ODE
open scoped Topology NNReal ContDiff

namespace RVM
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma exists_bounded_picard_flow {f : ℝ × E → E} {T L : ℝ}
    (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hf : ContDiffOn ℝ 1 f (Icc 0 T ×ˢ (univ : Set E)))
    (hb : ∀ t ∈ Icc 0 T, ∀ z, ‖f (t,z)‖ ≤ L) (x₀ : E) :
    ∃ α : E → ℝ → E, ∃ K : ℝ≥0,
      (∀ x ∈ closedBall x₀ (1/2 : ℝ), α x 0 = x ∧
        ∀ t ∈ Icc 0 T, HasDerivWithinAt (α x) (f (t,α x t)) (Icc 0 T) t) ∧
      ∀ t ∈ Icc 0 T, LipschitzOnWith K (α · t) (closedBall x₀ (1/2 : ℝ)) := by
  let R : ℝ≥0 := ⟨L*T+1/2,by positivity⟩
  have hsub : Icc 0 T ×ˢ closedBall x₀ (R:ℝ) ⊆ Icc 0 T ×ˢ (univ : Set E) :=
    prod_mono_right (subset_univ _)
  obtain ⟨K,hK⟩ := (hf.mono hsub).exists_lipschitzOnWith (by norm_num)
    ((convex_Icc 0 T).prod (convex_closedBall x₀ (R:ℝ)))
    (isCompact_Icc.prod (isCompact_closedBall x₀ (R:ℝ)))
  have hpic : IsPicardLindelof (fun t z => f (t,z)) ⟨0,⟨le_rfl,hT⟩⟩
      x₀ R (1/2) ⟨L,hL⟩ K := by
    refine ⟨?_,?_,?_,?_⟩
    · intro t ht
      apply LipschitzOnWith.of_dist_le_mul
      intro z hz w hw
      simpa using hK.dist_le_mul (t,z) (show (t,z) ∈ Icc 0 T ×ˢ closedBall x₀ (R:ℝ) from ⟨ht,hz⟩)
        (t,w) (show (t,w) ∈ Icc 0 T ×ˢ closedBall x₀ (R:ℝ) from ⟨ht,hw⟩)
    · intro z _
      exact hf.continuousOn.comp (continuousOn_id.prodMk continuousOn_const)
        (fun t ht => ⟨ht,mem_univ z⟩)
    · intro t ht z _
      exact hb t ht z
    · change L * max (T-0) (0-0) ≤ (R:ℝ)-(1/2:ℝ≥0)
      simp only [NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat,sub_zero,max_eq_left hT]
      change L*T ≤ L*T+1/2-1/2
      linarith
  obtain ⟨α,hα,K',hK'⟩ := picard_flow_with_range hpic
  refine ⟨α,K',?_,?_⟩
  · intro x hx
    exact ⟨(hα x (by simpa using hx)).1,(hα x (by simpa using hx)).2.1⟩
  · simpa using hK'

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_WithinFlow
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
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set MeasureTheory
open Set MeasureTheory Filter
open scoped Topology ContDiff
open Set MeasureTheory Metric Filter ODE
open scoped Topology NNReal ContDiff

section WithinFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma hasFDerivAt_time_slice {f : ℝ × E → E} {T : ℝ}
    (hf : ContDiffOn ℝ 1 f (Icc 0 T ×ˢ (univ : Set E))) {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
    HasFDerivAt (fun y => f (t,y))
      ((fderivWithin ℝ f (Icc 0 T ×ˢ (univ : Set E)) (t,x)).comp (ContinuousLinearMap.inr ℝ ℝ E)) x := by
  have hh := (hf.differentiableOn (by norm_num) (t,x) ⟨ht,mem_univ x⟩).hasFDerivWithinAt
  exact hh.comp_hasFDerivAt x ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
    (Filter.Eventually.of_forall (fun _ => ⟨ht,mem_univ _⟩))

lemma contDiffOn_spaceDerivative {f : ℝ × E → E} {T : ℝ} (hT : 0 < T)
    (hf : ContDiffOn ℝ 2 f (Icc 0 T ×ˢ (univ : Set E))) :
    ContDiffOn ℝ 1 (spaceDerivative f) (Icc 0 T ×ˢ (univ : Set E)) := by
  have hu : UniqueDiffOn ℝ (Icc 0 T ×ˢ (univ : Set E)) :=
    (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ
  have hh := (hf.fderivWithin hu (m := 1) (by norm_num)).clm_comp
    (contDiffOn_const (c := ContinuousLinearMap.inr ℝ ℝ E))
  apply hh.congr
  intro z hz
  exact (hasFDerivAt_time_slice (hf.of_le (by norm_num)) hz.1 z.2).fderiv

lemma contDiffOn_withinVariationalField {f : ℝ × E → E} {χ : (E →L[ℝ] E) → ℝ}
    {T : ℝ} (hT : 0 < T) (hf : ContDiffOn ℝ 2 f (Icc 0 T ×ˢ (univ : Set E)))
    (hχ : ContDiff ℝ 1 χ) :
    ContDiffOn ℝ 1 (withinVariationalField f χ)
      (Icc 0 T ×ˢ (univ : Set (E × (E →L[ℝ] E)))) := by
  have hp : ContDiff ℝ 1 (fun z : ℝ × (E × (E →L[ℝ] E)) => (z.1,z.2.1)) :=
    contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)
  have hm : MapsTo (fun z : ℝ × (E × (E →L[ℝ] E)) => (z.1,z.2.1))
      (Icc 0 T ×ˢ (univ : Set (E × (E →L[ℝ] E)))) (Icc 0 T ×ˢ (univ : Set E)) :=
    fun _ h => ⟨h.1,mem_univ _⟩
  exact ((hf.of_le (by norm_num)).comp hp.contDiffOn hm).prodMk
    (((hχ.comp (contDiff_snd.comp contDiff_snd)).contDiffOn).smul
      (((contDiffOn_spaceDerivative hT hf).comp hp.contDiffOn hm).clm_comp
        (contDiff_snd.comp contDiff_snd).contDiffOn))

omit [NormedSpace ℝ E] in

lemma continuousOn_time_label_of_lipschitz {F : Type*} [PseudoMetricSpace F]
    {α : E → ℝ → F} {J : Set ℝ} {S : Set E} {L : ℝ≥0}
    (hc : ∀ x ∈ S, ContinuousOn (α x) J)
    (hl : ∀ t ∈ J, LipschitzOnWith L (α · t) S) :
    ContinuousOn (fun z : ℝ × E => α z.2 z.1) (J ×ˢ S) := by
  intro z hz
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ,hδ,htime⟩ := Metric.continuousWithinAt_iff.mp (hc z.2 hz.2 z.1 hz.1) (ε/2) (by positivity)
  refine ⟨min δ (ε/(2*((L:ℝ)+1))),lt_min hδ (by positivity),?_⟩
  intro y hy hdist
  have hd₁ : dist y.1 z.1 < δ :=
    (le_max_left _ _).trans_lt ((show max (dist y.1 z.1) (dist y.2 z.2) < _ from hdist).trans_le (min_le_left _ _))
  have hd₂ : dist y.2 z.2 < ε/(2*((L:ℝ)+1)) :=
    (le_max_right _ _).trans_lt ((show max (dist y.1 z.1) (dist y.2 z.2) < _ from hdist).trans_le (min_le_right _ _))
  have hx : (L:ℝ)*dist y.2 z.2 < ε/2 := by
    have hh := (lt_div_iff₀ (show 0 < 2*((L:ℝ)+1) by positivity)).mp hd₂
    nlinarith [dist_nonneg (x := y.2) (y := z.2)]
  exact (dist_triangle _ (α z.2 y.1) _).trans_lt
    (add_lt_add_of_le_of_lt ((hl y.1 hy.1).dist_le_mul y.2 hy.2 z.2 hz.2)
      (htime hy.1 hd₁) |>.trans_le (by linarith))

lemma hasStrictFDerivAt_time_flow {f : ℝ × E → E} {α : E → ℝ → E}
    {A : E → ℝ → (E →L[ℝ] E)} {T r : ℝ} {x₀ x : E} {t : ℝ}
    (hf : ContinuousOn f (Icc 0 T ×ˢ (univ : Set E)))
    (hαc : ContinuousOn (fun z : ℝ × E => α z.2 z.1) (Icc 0 T ×ˢ ball x₀ r))
    (hAc : ContinuousOn (fun z : ℝ × E => A z.2 z.1) (Icc 0 T ×ˢ ball x₀ r))
    (hαd : ∀ y ∈ ball x₀ r, ∀ s ∈ Icc 0 T,
      HasDerivWithinAt (α y) (f (s,α y s)) (Icc 0 T) s)
    (hAd : ∀ s ∈ Icc 0 T, ∀ y ∈ ball x₀ r, HasFDerivAt (α · s) (A y s) y)
    (ht : t ∈ Ioo 0 T) (hx : x ∈ ball x₀ r) :
    HasStrictFDerivAt (fun z : ℝ × E => α z.2 z.1)
      ((ContinuousLinearMap.toSpanSingleton ℝ (f (t,α x t))).coprod (A x t)) (t,x) := by
  have hn : Icc 0 T ×ˢ ball x₀ r ∈ 𝓝 (t,x) :=
    prod_mem_nhds (Icc_mem_nhds ht.1 ht.2) (isOpen_ball.mem_nhds hx)
  have hni : Ioo 0 T ×ˢ ball x₀ r ∈ 𝓝 (t,x) :=
    (isOpen_Ioo.prod isOpen_ball).mem_nhds ⟨ht,hx⟩
  have hfc : ContinuousAt (fun z : ℝ × E => f (z.1,α z.2 z.1)) (t,x) := by
    apply (hf.comp (continuousOn_fst.prodMk hαc) (fun z hz => ⟨hz.1,mem_univ _⟩)).continuousAt hn
  apply hasStrictFDerivAt_uncurry_coprod (f := fun s y => α y s) (u := (t,x))
    (f₁ := fun s y => ContinuousLinearMap.toSpanSingleton ℝ (f (s,α y s)))
    (f₂ := fun s y => A y s)
  · filter_upwards [hni] with z hz
    exact ((hαd z.2 hz.2 z.1 (Ioo_subset_Icc_self hz.1)).hasDerivAt
      (Icc_mem_nhds hz.1.1 hz.1.2)).hasFDerivAt
  · filter_upwards [hn] with z hz
    exact hAd z.1 hz.1 z.2 hz.2
  · exact (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := E)).continuous.continuousAt.comp hfc
  · exact hAc.continuousAt hn

variable [FiniteDimensional ℝ E]

lemma withinVariationalField_bounded {f : ℝ × E → E} {T L K : ℝ}
    (hL : 0 ≤ L) (hK : 0 ≤ K) (hb : ∀ t ∈ Icc 0 T, ∀ x, ‖f (t,x)‖ ≤ L)
    (hd : ∀ t ∈ Icc 0 T, ∀ x, ‖spaceDerivative f (t,x)‖ ≤ K)
    (χ : ContDiffBump (0 : E →L[ℝ] E)) {t : ℝ} (ht : t ∈ Icc 0 T) (z : E × (E →L[ℝ] E)) :
    ‖withinVariationalField f χ (t,z)‖ ≤ max L (K*χ.rOut) := by
  change max ‖f (t,z.1)‖ ‖χ z.2 • (spaceDerivative f (t,z.1)).comp z.2‖ ≤ _
  refine max_le ((hb t ht _).trans (le_max_left _ _)) ?_
  by_cases hz : χ z.2 = 0
  · simp only [hz,zero_smul,norm_zero]
    exact hL.trans (le_max_left _ _)
  have hnorm : ‖z.2‖ ≤ χ.rOut := by
    have hh : z.2 ∈ Metric.ball 0 χ.rOut := by rwa [← χ.support_eq]
    exact (show ‖z.2‖ < χ.rOut by simpa only [Metric.mem_ball,dist_zero_right] using hh).le
  calc
    _ = χ z.2 * ‖(spaceDerivative f (t,z.1)).comp z.2‖ := by rw [norm_smul,Real.norm_of_nonneg χ.nonneg]
    _ ≤ ‖(spaceDerivative f (t,z.1)).comp z.2‖ := mul_le_of_le_one_left (norm_nonneg _) χ.le_one
    _ ≤ ‖spaceDerivative f (t,z.1)‖ * ‖z.2‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ K*χ.rOut := mul_le_mul (hd t ht _) hnorm (norm_nonneg _) hK
    _ ≤ _ := le_max_right _ _
lemma exists_within_variational_flow {f : ℝ × E → E} {T L K : ℝ}
    (hT : 0 < T) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hf : ContDiffOn ℝ 2 f (Icc 0 T ×ˢ (univ : Set E)))
    (hb : ∀ t ∈ Icc 0 T, ∀ x, ‖f (t,x)‖ ≤ L)
    (hd : ∀ t ∈ Icc 0 T, ∀ x, ‖spaceDerivative f (t,x)‖ ≤ K) (x₀ : E) :
    ∃ α : E → ℝ → E, ∃ A : E → ℝ → (E →L[ℝ] E), ∃ L' : ℝ≥0,
      (∀ x ∈ closedBall x₀ (1/2 : ℝ), α x 0 = x ∧ A x 0 = ContinuousLinearMap.id ℝ E ∧
        (∀ t ∈ Icc 0 T, HasDerivWithinAt (α x) (f (t,α x t)) (Icc 0 T) t) ∧
        (∀ t ∈ Icc 0 T, HasDerivWithinAt (A x)
          ((spaceDerivative f (t,α x t)).comp (A x t)) (Icc 0 T) t) ∧
        ∀ t ∈ Icc 0 T, α x t ∈ closedBall x₀ (L*T+1/2)) ∧
      ∀ t ∈ Icc 0 T, LipschitzOnWith L' (α · t) (closedBall x₀ (1/2 : ℝ)) ∧
        LipschitzOnWith L' (A · t) (closedBall x₀ (1/2 : ℝ)) := by
  let χ : ContDiffBump (0 : E →L[ℝ] E) :=
    ⟨Real.exp (K*T)+1,Real.exp (K*T)+2,by positivity,by linarith⟩
  let M := max L (K*χ.rOut)
  let z₀ : E × (E →L[ℝ] E) := (x₀,ContinuousLinearMap.id ℝ E)
  obtain ⟨β,L',hβ,hLip⟩ := exists_bounded_picard_flow hT.le
    (hL.trans (le_max_left L (K*χ.rOut)))
    (contDiffOn_withinVariationalField hT hf χ.contDiff)
    (fun _ ht z => withinVariationalField_bounded hL hK hb hd χ ht z) z₀
  let α : E → ℝ → E := fun x t => (β (x,ContinuousLinearMap.id ℝ E) t).1
  let A : E → ℝ → (E →L[ℝ] E) := fun x t => (β (x,ContinuousLinearMap.id ℝ E) t).2
  have hmem {x : E} (hx : x ∈ closedBall x₀ (1/2 : ℝ)) :
      (x,ContinuousLinearMap.id ℝ E) ∈ closedBall z₀ (1/2 : ℝ) := by
    simpa only [z₀,Metric.mem_closedBall,Prod.dist_eq,dist_self,max_eq_left (dist_nonneg : 0 ≤ dist x x₀)] using hx
  have hα₀ {x : E} (hx : x ∈ closedBall x₀ (1/2 : ℝ)) : α x 0 = x :=
    congrArg Prod.fst (hβ _ (hmem hx)).1
  have hA₀ {x : E} (hx : x ∈ closedBall x₀ (1/2 : ℝ)) : A x 0 = ContinuousLinearMap.id ℝ E :=
    congrArg Prod.snd (hβ _ (hmem hx)).1
  have hαd {x : E} (hx : x ∈ closedBall x₀ (1/2 : ℝ)) {t : ℝ} (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt (α x) (f (t,α x t)) (Icc 0 T) t :=
    ((hβ _ (hmem hx)).2 t ht).fst
  have hAd {x : E} (hx : x ∈ closedBall x₀ (1/2 : ℝ)) {t : ℝ} (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt (A x) (χ (A x t) • (spaceDerivative f (t,α x t)).comp (A x t)) (Icc 0 T) t :=
    ((hβ _ (hmem hx)).2 t ht).snd
  have hAbound {x : E} (hx : x ∈ closedBall x₀ (1/2 : ℝ)) {t : ℝ} (ht : t ∈ Icc 0 T) :
      ‖A x t‖ ≤ Real.exp (K*T) := by
    have hh := norm_le_gronwallBound_of_norm_deriv_right_le
      (HasDerivWithinAt.continuousOn (fun t ht => hAd hx ht))
      (fun t ht => (hAd hx (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
      (δ := 1) (K := K) (ε := 0)
      (by rw [hA₀ hx]; exact ContinuousLinearMap.norm_id_le)
      (fun t ht => by
        rw [norm_smul,Real.norm_of_nonneg χ.nonneg,add_zero]
        calc
          _ ≤ ‖(spaceDerivative f (t,α x t)).comp (A x t)‖ := mul_le_of_le_one_left (norm_nonneg _) χ.le_one
          _ ≤ ‖spaceDerivative f (t,α x t)‖ * ‖A x t‖ := ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ K*‖A x t‖ := mul_le_mul_of_nonneg_right (hd t (Ico_subset_Icc_self ht) _) (norm_nonneg _)) t ht
    rw [gronwallBound_ε0,one_mul,sub_zero] at hh
    exact hh.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hK))
  have hone {x : E} (hx : x ∈ closedBall x₀ (1/2 : ℝ)) {t : ℝ} (ht : t ∈ Icc 0 T) :
      χ (A x t) = 1 := by
    apply χ.one_of_mem_closedBall
    simp only [Metric.mem_closedBall,dist_zero_right]
    exact (hAbound hx ht).trans (by dsimp [χ]; linarith)
  refine ⟨α,A,L',?_,?_⟩
  · intro x hx
    refine ⟨hα₀ hx,hA₀ hx,(fun _ ht => hαd hx ht),?_,?_⟩
    · intro t ht
      simpa only [hone hx ht,one_smul] using hAd hx ht
    · intro t ht
      have hl : LipschitzOnWith ⟨L,hL⟩ (α x) (Icc 0 T) :=
        (convex_Icc 0 T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
          (fun s hs => hαd hx hs) (fun s _ => by exact_mod_cast hb s (by assumption) (α x s))
      have hh := hl.dist_le_mul t ht 0 (show 0 ∈ Icc 0 T from ⟨le_rfl,hT.le⟩)
      rw [hα₀ hx,Real.dist_eq,sub_zero,abs_of_nonneg ht.1] at hh
      change dist (α x t) x₀ ≤ L*T+1/2
      exact (dist_triangle _ x _).trans (add_le_add
        (hh.trans (mul_le_mul_of_nonneg_left ht.2 hL)) hx)
  · intro t ht
    constructor
    · apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      exact (le_max_left _ _).trans (by
        simpa [Prod.dist_eq] using (hLip t ht).dist_le_mul _ (hmem hx) _ (hmem hy))
    · apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      exact (le_max_right _ _).trans (by
        simpa [Prod.dist_eq] using (hLip t ht).dist_le_mul _ (hmem hx) _ (hmem hy))

lemma hasFDerivAt_within_variational_flow {f : ℝ × E → E}
    {x₀ : E} {r R T : ℝ} (hT : 0 < T)
    (hf : ContDiffOn ℝ 2 f (Icc 0 T ×ˢ (univ : Set E)))
    {α : E → ℝ → E} {A : E → ℝ → (E →L[ℝ] E)} {L : ℝ≥0}
    (hsol : ∀ x ∈ closedBall x₀ r, α x 0 = x ∧ A x 0 = ContinuousLinearMap.id ℝ E ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt (α x) (f (t,α x t)) (Icc 0 T) t) ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt (A x)
        ((spaceDerivative f (t,α x t)).comp (A x t)) (Icc 0 T) t) ∧
      ∀ t ∈ Icc 0 T, α x t ∈ closedBall x₀ R)
    (hLip : ∀ t ∈ Icc 0 T, LipschitzOnWith L (α · t) (closedBall x₀ r))
    {x : E} (hx : x ∈ ball x₀ r) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasFDerivAt (fun y => α y t) (A x t) x := by
  have hx' := ball_subset_closedBall hx
  have hdf := contDiffOn_spaceDerivative hT hf
  have hsub : Icc 0 T ×ˢ closedBall x₀ R ⊆ Icc 0 T ×ˢ (univ : Set E) :=
    prod_mono Subset.rfl (subset_univ _)
  obtain ⟨LD,hLD⟩ := (hdf.mono hsub).exists_lipschitzOnWith (by norm_num)
    ((convex_Icc 0 T).prod (convex_closedBall x₀ R)) (isCompact_Icc.prod (isCompact_closedBall x₀ R))
  obtain ⟨M,hM⟩ := (isCompact_Icc.prod (isCompact_closedBall x₀ R)).bddAbove_image
    (hdf.continuousOn.mono hsub).norm
  have hLDslice (s : ℝ) (hs : s ∈ Icc 0 T) :
      LipschitzOnWith LD (spaceDerivative f ∘ (fun x => (s,x))) (closedBall x₀ R) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [Function.comp_apply,Prod.dist_eq,dist_self,max_eq_right (dist_nonneg : 0 ≤ dist x y)]
      using hLD.dist_le_mul (s,x) ⟨hs,hx⟩ (s,y) ⟨hs,hy⟩
  let K := max 1 M
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let C : ℝ := ((LD : ℝ)*(L : ℝ)^2)/K * (Real.exp (K*t)-1)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (div_nonneg (mul_nonneg LD.2 (sq_nonneg _)) hK.le)
      (sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg hK.le ht.1)))
  apply hasFDerivAt_of_quadratic_bound hC
  filter_upwards [closedBall_mem_nhds_of_mem hx] with y hy
  have hxs := hsol x hx'
  have hys := hsol y hy
  have hdα (z : E) (hz : z ∈ closedBall x₀ r) (s : ℝ) (hs : s ∈ Ico 0 T) :
      HasDerivWithinAt (α z) (f (s,α z s)) (Ici s) s :=
    ((hsol z hz).2.2.1 s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hs)
  have hdA (s : ℝ) (hs : s ∈ Ico 0 T) :
      HasDerivWithinAt (A x) ((spaceDerivative f (s,α x s)).comp (A x s)) (Ici s) s :=
    (hxs.2.2.2.1 s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hs)
  have hb := variational_remainder_bound (f := fun t x => f (t,x))
    (D := fun s => spaceDerivative f (s,α x s))
    (HasDerivWithinAt.continuousOn hxs.2.2.1)
    (HasDerivWithinAt.continuousOn hys.2.2.1)
    (HasDerivWithinAt.continuousOn hxs.2.2.2.1)
    (hdα x hx') (hdα y hy) hdA
    (v := y-x) (K := K) (ε := (LD : ℝ)*(L : ℝ)^2*‖y-x‖^2)
    (by simp [hxs.1,hys.1,hxs.2.1])
    (fun s hs => (hM ⟨(s,α x s),⟨Ico_subset_Icc_self hs,hxs.2.2.2.2 s (Ico_subset_Icc_self hs)⟩,rfl⟩).trans (le_max_right _ _))
    (fun s hs => ?_)
  · have hb' := hb t ht
    apply hb'.trans_eq
    rw [gronwallBound_of_K_ne_0 hK.ne']
    dsimp [C]
    ring_nf
  · have hTaylor := taylor_bound_lipschitz_derivative
      (convex_closedBall x₀ R)
      (fun z _ => (hasFDerivAt_time_slice (hf.of_le (by norm_num)) (Ico_subset_Icc_self hs) z).differentiableAt)
      (hLDslice s (Ico_subset_Icc_self hs)) (hxs.2.2.2.2 s (Ico_subset_Icc_self hs)) (hys.2.2.2.2 s (Ico_subset_Icc_self hs))
    apply hTaylor.trans
    have hn := (hLip s (Ico_subset_Icc_self hs)).norm_sub_le hy hx'
    have hsq : ‖α y s-α x s‖^2 ≤ ((L : ℝ)*‖y-x‖)^2 :=
      sq_le_sq₀ (norm_nonneg _) (mul_nonneg L.2 (norm_nonneg _)) |>.mpr hn
    calc
      _ ≤ (LD : ℝ)*((L : ℝ)*‖y-x‖)^2 := mul_le_mul_of_nonneg_left hsq LD.2
      _ = _ := by ring

lemma flow_injOn_of_within_ode {f : ℝ × E → E}
    {x₀ : E} {r R T : ℝ}
    (hf : ContDiffOn ℝ 1 f (Icc 0 T ×ˢ (univ : Set E))) {α : E → ℝ → E}
    (hinit : ∀ x ∈ closedBall x₀ r, α x 0 = x)
    (hder : ∀ x ∈ closedBall x₀ r, ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (α x) (f (t,α x t)) (Icc 0 T) t)
    (hrange : ∀ x ∈ closedBall x₀ r, ∀ t ∈ Icc 0 T, α x t ∈ closedBall x₀ R)
    {t : ℝ} (ht : t ∈ Icc 0 T) : Set.InjOn (fun x => α x t) (closedBall x₀ r) := by
  obtain ⟨K,hK⟩ := (hf.mono (prod_mono Subset.rfl (subset_univ (closedBall x₀ R)))).exists_lipschitzOnWith
    (by norm_num) ((convex_Icc 0 T).prod (convex_closedBall x₀ R))
    (isCompact_Icc.prod (isCompact_closedBall x₀ R))
  have hKslice (s : ℝ) (hs : s ∈ Icc 0 T) :
      LipschitzOnWith K (fun x => f (s,x)) (closedBall x₀ R) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [Prod.dist_eq,dist_self,max_eq_right (dist_nonneg : 0 ≤ dist x y)]
      using hK.dist_le_mul (s,x) ⟨hs,hx⟩ (s,y) ⟨hs,hy⟩
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have hd (x : E) (hx : x ∈ closedBall x₀ r) (s : ℝ) (hs : s ∈ Ioc 0 t) :
      HasDerivWithinAt (α x) (f (s,α x s)) (Iic s) s :=
    ((hder x hx s (hsub (Ioc_subset_Icc_self hs))).mono hsub).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsLE_of_mem hs)
  intro x hx y hy heq
  have hu := ODE_solution_unique_of_mem_Icc_left
    (v := fun s x => f (s,x)) (s := fun _ => closedBall x₀ R)
    (fun s hs => hKslice s (hsub (Ioc_subset_Icc_self hs)))
    ((HasDerivWithinAt.continuousOn (hder x hx)).mono hsub) (hd x hx)
    (fun s hs => hrange x hx s (hsub (Ioc_subset_Icc_self hs)))
    ((HasDerivWithinAt.continuousOn (hder y hy)).mono hsub) (hd y hy)
    (fun s hs => hrange y hy s (hsub (Ioc_subset_Icc_self hs))) heq (show 0 ∈ Icc 0 t from ⟨le_rfl,ht.1⟩)
  simpa [hinit x hx,hinit y hy] using hu

lemma exists_bounded_within_variational_flow {f : ℝ × E → E} {T L : ℝ}
    (hT : 0 < T) (hL : 0 ≤ L)
    (hf : ContDiffOn ℝ 2 f (Icc 0 T ×ˢ (univ : Set E)))
    (hb : ∀ t ∈ Icc 0 T, ∀ x, ‖f (t,x)‖ ≤ L) (x₀ : E) :
    ∃ α : E → ℝ → E, ∃ A : E → ℝ → (E →L[ℝ] E), ∃ L' : ℝ≥0,
      (∀ x ∈ closedBall x₀ (1/2 : ℝ), α x 0 = x ∧ A x 0 = ContinuousLinearMap.id ℝ E ∧
        (∀ t ∈ Icc 0 T, HasDerivWithinAt (α x) (f (t,α x t)) (Icc 0 T) t) ∧
        (∀ t ∈ Icc 0 T, HasDerivWithinAt (A x)
          ((spaceDerivative f (t,α x t)).comp (A x t)) (Icc 0 T) t) ∧
        ∀ t ∈ Icc 0 T, α x t ∈ closedBall x₀ (L*T+1/2)) ∧
      ∀ t ∈ Icc 0 T, LipschitzOnWith L' (α · t) (closedBall x₀ (1/2 : ℝ)) ∧
        LipschitzOnWith L' (A · t) (closedBall x₀ (1/2 : ℝ)) := by
  let χ : ContDiffBump x₀ := ⟨L*T+1,L*T+2,by positivity,by linarith⟩
  let g : ℝ × E → E := fun z => χ z.2 • f z
  have hg : ContDiffOn ℝ 2 g (Icc 0 T ×ˢ (univ : Set E)) :=
    (χ.contDiff.comp contDiff_snd).contDiffOn.smul hf
  have hgb (t : ℝ) (ht : t ∈ Icc 0 T) (x : E) : ‖g (t,x)‖ ≤ L := by
    change ‖χ x • f (t,x)‖ ≤ L
    rw [norm_smul,Real.norm_of_nonneg χ.nonneg]
    exact (mul_le_of_le_one_left (norm_nonneg _) χ.le_one).trans (hb t ht x)
  obtain ⟨K,hK⟩ := (isCompact_Icc.prod (isCompact_closedBall x₀ χ.rOut)).bddAbove_image
    ((contDiffOn_spaceDerivative hT hg).continuousOn.mono
      (prod_mono Subset.rfl (subset_univ _))).norm
  have hd (t : ℝ) (ht : t ∈ Icc 0 T) (x : E) : ‖spaceDerivative g (t,x)‖ ≤ max 0 K := by
    by_cases hx : x ∈ closedBall x₀ χ.rOut
    · exact (hK ⟨(t,x),⟨ht,hx⟩,rfl⟩).trans (le_max_right _ _)
    have he : (fun y => g (t,y)) =ᶠ[𝓝 x] 0 := by
      have hn : x ∉ tsupport (χ : E → ℝ) := by rwa [χ.tsupport_eq]
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with y hy
      change χ y • f (t,y) = 0
      simp only [hy,Pi.zero_apply,zero_smul]
    have hzero : spaceDerivative g (t,x) = 0 := by
      change fderiv ℝ (fun y => g (t,y)) x = 0
      rw [he.fderiv_eq]
      simp
    rw [hzero,norm_zero]
    exact le_max_left _ _
  obtain ⟨α,A,L',hsol,hLip⟩ := exists_within_variational_flow hT hL
    (le_max_left 0 K) hg hgb hd x₀
  have hlocal {x : E} (hx : x ∈ closedBall x₀ (1/2 : ℝ)) {t : ℝ} (ht : t ∈ Icc 0 T) :
      (fun y => g (t,y)) =ᶠ[𝓝 (α x t)] (fun y => f (t,y)) := by
    have hm : α x t ∈ ball x₀ χ.rIn := by
      have hh := (hsol x hx).2.2.2.2 t ht
      change dist (α x t) x₀ < L*T+1
      change dist (α x t) x₀ ≤ L*T+1/2 at hh
      linarith
    filter_upwards [χ.eventuallyEq_one_of_mem_ball hm] with y hy
    change χ y • f (t,y) = f (t,y)
    rw [hy]
    exact one_smul ℝ (f (t,y))
  refine ⟨α,A,L',?_,hLip⟩
  intro x hx
  have hh := hsol x hx
  refine ⟨hh.1,hh.2.1,?_,?_,hh.2.2.2.2⟩
  · intro t ht
    simpa only [(hlocal hx ht).eq_of_nhds] using hh.2.2.1 t ht
  · intro t ht
    have he : spaceDerivative g (t,α x t) = spaceDerivative f (t,α x t) :=
      (hlocal hx ht).fderiv_eq
    simpa only [he] using hh.2.2.2.1 t ht

lemma exists_bounded_within_volume_flow_joint {f : ℝ × E → E} {T L : ℝ}
    (hT : 0 < T) (hL : 0 ≤ L)
    (hf : ContDiffOn ℝ 2 f (Icc 0 T ×ˢ (univ : Set E)))
    (hb : ∀ t ∈ Icc 0 T, ∀ x, ‖f (t,x)‖ ≤ L)
    (hdiv : ∀ t ∈ Icc 0 T, ∀ x, LinearMap.trace ℝ E (spaceDerivative f (t,x)).toLinearMap = 0)
    (x₀ : E) :
    ∃ α : E → ℝ → E, ∃ A : E → ℝ → (E →L[ℝ] E),
      (∀ x ∈ ball x₀ (1/2 : ℝ), α x 0 = x ∧
        (∀ t ∈ Icc 0 T, HasDerivWithinAt (α x) (f (t,α x t)) (Icc 0 T) t) ∧
        (∀ t ∈ Icc 0 T, HasFDerivAt (fun y => α y t) (A x t) x) ∧
        (∀ t ∈ Icc 0 T, (A x t).det = 1) ∧
        ∀ t ∈ Ioo 0 T, HasStrictFDerivAt (fun z : ℝ × E => α z.2 z.1)
          ((ContinuousLinearMap.toSpanSingleton ℝ (f (t,α x t))).coprod (A x t)) (t,x)) ∧
      ∀ t ∈ Icc 0 T, Set.InjOn (fun x => α x t) (ball x₀ (1/2 : ℝ)) := by
  obtain ⟨α,A,L',hsol,hLip⟩ := exists_bounded_within_variational_flow hT hL hf hb x₀
  have hαc := continuousOn_time_label_of_lipschitz (fun x hx =>
    HasDerivWithinAt.continuousOn (hsol x hx).2.2.1) (fun t ht => (hLip t ht).1)
  have hAc := continuousOn_time_label_of_lipschitz (fun x hx =>
    HasDerivWithinAt.continuousOn (hsol x hx).2.2.2.1) (fun t ht => (hLip t ht).2)
  have hAd : ∀ t ∈ Icc 0 T, ∀ x ∈ ball x₀ (1/2 : ℝ), HasFDerivAt (α · t) (A x t) x :=
    fun _ ht _ hx => hasFDerivAt_within_variational_flow hT hf hsol (fun t ht => (hLip t ht).1) hx ht
  refine ⟨α,A,?_,?_⟩
  · intro x hx
    have hh := hsol x (ball_subset_closedBall hx)
    refine ⟨hh.1,hh.2.2.1,(fun t ht => hAd t ht x hx),?_,?_⟩
    · exact determinant_clm_eq_one_of_trace_zero hT.le
        (HasDerivWithinAt.continuousOn hh.2.2.2.1) hh.2.1
        (fun t ht => (hh.2.2.2.1 t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
        (fun t ht => hdiv t (Ioo_subset_Icc_self ht) _)
    · intro t ht
      exact hasStrictFDerivAt_time_flow hf.continuousOn
        (hαc.mono (Set.prod_mono Subset.rfl ball_subset_closedBall))
        (hAc.mono (Set.prod_mono Subset.rfl ball_subset_closedBall))
        (fun y hy => (hsol y (ball_subset_closedBall hy)).2.2.1) hAd ht hx
  · intro t ht
    exact (flow_injOn_of_within_ode (hf.of_le (by norm_num))
      (fun x hx => (hsol x hx).1) (fun x hx => (hsol x hx).2.2.1)
      (fun x hx => (hsol x hx).2.2.2.2) ht).mono ball_subset_closedBall

end WithinFlow
lemma cutLorentz_regular_slab {E B : Field} {χ : Vec → ℝ} {T : ℝ}
    (hE : ContDiffOn ℝ 2 E (Icc 0 T ×ˢ (univ : Set Vec))) (hB : ContDiffOn ℝ 2 B (Icc 0 T ×ˢ (univ : Set Vec)))
    (hχ : ContDiff ℝ 2 χ) :
    ContDiffOn ℝ 2 (cutLorentz E B χ) (Icc 0 T ×ˢ (univ : Set Phase)) := by
  have hx : ContDiff ℝ 2 (fun p : ℝ × Phase => (p.1,p.2.1)) :=
    contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)
  have hm : MapsTo (fun p : ℝ × Phase => (p.1,p.2.1))
      (Icc 0 T ×ˢ (univ : Set Phase)) (Icc 0 T ×ˢ (univ : Set Vec)) := fun _ hp => ⟨hp.1,mem_univ _⟩
  have hu : ContDiff ℝ 2 (fun p : ℝ × Phase => velocity p.2.2) :=
    contDiff_velocity.comp (contDiff_snd.comp contDiff_snd)
  exact hu.contDiffOn.prodMk
    ((hχ.comp (contDiff_fst.comp contDiff_snd)).contDiffOn.smul
      ((hE.comp hx.contDiffOn hm).add
        (contDiff_cross.contDiffOn.comp (hu.contDiffOn.prodMk (hB.comp hx.contDiffOn hm))
          (mapsTo_univ _ _))))

lemma cutLorentz_bounded_slab {E B : Field} {T : ℝ} (_hT : 0 ≤ T) {x₀ : Vec}
    (hE : ContinuousOn E (Icc 0 T ×ˢ (univ : Set Vec))) (hB : ContinuousOn B (Icc 0 T ×ˢ (univ : Set Vec)))
    (χ : ContDiffBump x₀) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t ∈ Icc 0 T, ∀ z, ‖cutLorentz E B χ (t,z)‖ ≤ L := by
  have hsub : Icc 0 T ×ˢ closedBall x₀ χ.rOut ⊆ (Icc 0 T ×ˢ (univ : Set Vec)) := fun _ hp => ⟨hp.1,mem_univ _⟩
  obtain ⟨M,hM⟩ := (isCompact_Icc.prod (isCompact_closedBall x₀ χ.rOut)).bddAbove_image
    ((hE.norm.add hB.norm).mono hsub)
  refine ⟨max 1 M, (zero_le_one.trans (le_max_left _ _)),?_⟩
  intro t ht z
  rw [Prod.norm_def]
  apply max_le
  · exact (norm_velocity_lt_one z.2).le.trans (le_max_left _ _)
  change ‖χ z.1 • (E (t,z.1)+cross (velocity z.2) (B (t,z.1)))‖ ≤ max 1 M
  by_cases hχ : χ z.1 = 0
  · simp only [hχ,zero_smul,norm_zero]
    exact zero_le_one.trans (le_max_left _ _)
  have hz : z.1 ∈ closedBall x₀ χ.rOut := ball_subset_closedBall (by
    rw [← χ.support_eq]
    exact hχ)
  calc
    _ = χ z.1 * ‖E (t,z.1)+cross (velocity z.2) (B (t,z.1))‖ := by
      rw [norm_smul,Real.norm_of_nonneg χ.nonneg]
    _ ≤ ‖E (t,z.1)+cross (velocity z.2) (B (t,z.1))‖ :=
      mul_le_of_le_one_left (norm_nonneg _) χ.le_one
    _ ≤ ‖E (t,z.1)‖+‖B (t,z.1)‖ := by
      have hc : ‖cross (velocity z.2) (B (t,z.1))‖ ≤ ‖B (t,z.1)‖ :=
        (norm_cross_le (velocity z.2) (B (t,z.1))).trans
          (mul_le_of_le_one_left (norm_nonneg (B (t,z.1))) (norm_velocity_lt_one z.2).le)
      exact (norm_add_le (E (t,z.1)) (cross (velocity z.2) (B (t,z.1)))).trans
        (add_le_add le_rfl hc)
    _ ≤ M := hM ⟨(t,z.1),⟨ht,hz⟩,rfl⟩
    _ ≤ _ := le_max_right _ _

lemma cutLorentz_eq_lorentzPhase (E B : Field) (χ : Vec → ℝ) (t : ℝ) :
    (fun z => cutLorentz E B χ (t,z)) =
      lorentzPhase (fun x => χ x • E (t,x)) (fun x => χ x • B (t,x)) := by
  ext z : 1
  simp only [cutLorentz,lorentzPhase,cross_smul_right,smul_add]

lemma trace_cutLorentz_slab {E B : Field} {χ : Vec → ℝ} {T : ℝ}
    (hE : ContDiffOn ℝ 1 E (Icc 0 T ×ˢ (univ : Set Vec)))
    (hB : ContDiffOn ℝ 1 B (Icc 0 T ×ˢ (univ : Set Vec)))
    (hχ : ContDiff ℝ 1 χ) {t : ℝ} (ht : t ∈ Icc 0 T) (z : Phase) :
    LinearMap.trace ℝ Phase (spaceDerivative (cutLorentz E B χ) (t,z)).toLinearMap = 0 := by
  rw [spaceDerivative,cutLorentz_eq_lorentzPhase]
  exact trace_lorentzPhase
    ((hχ.differentiable (by norm_num)).smul (fun x => (hasFDerivAt_time_slice hE ht x).differentiableAt))
    ((hχ.differentiable (by norm_num)).smul (fun x => (hasFDerivAt_time_slice hB ht x).differentiableAt)) z

lemma exists_finite_lorentz_within_volume_flow {E B : Field} {T : ℝ} (hT : 0 < T)
    (hE : ContDiffOn ℝ 2 E (Icc 0 T ×ˢ (univ : Set Vec)))
    (hB : ContDiffOn ℝ 2 B (Icc 0 T ×ˢ (univ : Set Vec))) (z₀ : Phase) :
    ∃ α : Phase → ℝ → Phase, ∃ A : Phase → ℝ → (Phase →L[ℝ] Phase),
      (∀ z ∈ ball z₀ (1/2 : ℝ), α z 0 = z ∧
        (∀ t ∈ Icc 0 T, HasDerivWithinAt (α z) (lorentzField E B (t,α z t)) (Icc 0 T) t) ∧
        (∀ t ∈ Icc 0 T, HasFDerivAt (fun y => α y t) (A z t) z) ∧
        (∀ t ∈ Icc 0 T, (A z t).det = 1) ∧
        ∀ t ∈ Ioo 0 T, HasStrictFDerivAt (fun p : ℝ × Phase => α p.2 p.1)
          ((ContinuousLinearMap.toSpanSingleton ℝ (lorentzField E B (t,α z t))).coprod (A z t)) (t,z)) ∧
      ∀ t ∈ Icc 0 T, Set.InjOn (fun z => α z t) (ball z₀ (1/2 : ℝ)) := by
  let χ : ContDiffBump z₀.1 := ⟨T+1,T+2,by linarith,by linarith⟩
  obtain ⟨L,hL,hbound⟩ := cutLorentz_bounded_slab hT.le hE.continuousOn hB.continuousOn χ
  obtain ⟨α,A,hsol,hinj⟩ := exists_bounded_within_volume_flow_joint hT hL
    (cutLorentz_regular_slab hE hB χ.contDiff) hbound
    (fun _ ht z => trace_cutLorentz_slab (hE.of_le (by norm_num)) (hB.of_le (by norm_num)) χ.contDiff ht z) z₀
  have hX {z : Phase} (hz : z ∈ ball z₀ (1/2 : ℝ)) :
      LipschitzOnWith 1 (fun t => (α z t).1) (Icc 0 T) := by
    apply (convex_Icc 0 T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun t ht => ((hsol z hz).2.1 t ht).fst)
    intro t _
    exact_mod_cast (norm_velocity_lt_one (α z t).2).le
  have hone {z : Phase} (hz : z ∈ ball z₀ (1/2 : ℝ)) {t : ℝ} (ht : t ∈ Icc 0 T) :
      χ (α z t).1 = 1 := by
    apply χ.one_of_mem_closedBall
    have hh := (hX hz).dist_le_mul t ht 0 (show 0 ∈ Icc 0 T from ⟨le_rfl,hT.le⟩)
    simp only [(hsol z hz).1,NNReal.coe_one,one_mul,Real.dist_eq,sub_zero,abs_of_nonneg ht.1] at hh
    have hz' : dist z.1 z₀.1 < (1/2 : ℝ) := (le_max_left _ _).trans_lt hz
    change dist (α z t).1 z₀.1 ≤ T+1
    exact (dist_triangle _ z.1 _).trans (add_le_add hh hz'.le) |>.trans (by linarith [ht.2])
  have heq {z : Phase} (hz : z ∈ ball z₀ (1/2 : ℝ)) {t : ℝ} (ht : t ∈ Icc 0 T) :
      cutLorentz E B χ (t,α z t) = lorentzField E B (t,α z t) := by
    simp only [cutLorentz,lorentzField,lorentzPhase,hone hz ht,one_smul]
  refine ⟨α,A,?_,hinj⟩
  intro z hz
  refine ⟨(hsol z hz).1,?_,(hsol z hz).2.2.1,(hsol z hz).2.2.2.1,?_⟩
  · intro t ht
    simpa only [heq hz ht] using (hsol z hz).2.1 t ht
  · intro t ht
    simpa only [heq hz (Ioo_subset_Icc_self ht)] using (hsol z hz).2.2.2.2 t ht


open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set MeasureTheory
open Set MeasureTheory Filter
open scoped Topology ContDiff
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open scoped Topology NNReal ContDiff

section SlabUniqueness
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma eqOn_of_within_ode {f : ℝ × E → E} {α β : ℝ → E} {T t₀ : ℝ}
    (hf : ContDiffOn ℝ 1 f (Icc 0 T ×ˢ (univ : Set E)))
    (hα : ∀ t ∈ Icc 0 T, HasDerivWithinAt α (f (t,α t)) (Icc 0 T) t)
    (hβ : ∀ t ∈ Icc 0 T, HasDerivWithinAt β (f (t,β t)) (Icc 0 T) t)
    (ht₀ : t₀ ∈ Icc 0 T) (hinit : α t₀ = β t₀) : EqOn α β (Icc 0 T) := by
  have hαc := HasDerivWithinAt.continuousOn hα
  have hβc := HasDerivWithinAt.continuousOn hβ
  obtain ⟨R,hR⟩ := isCompact_Icc.bddAbove_image (hαc.norm.add hβc.norm)
  have hαR (t : ℝ) (ht : t ∈ Icc 0 T) : α t ∈ closedBall (0 : E) R := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using (le_add_of_nonneg_right (norm_nonneg (β t))).trans (hR ⟨t,ht,rfl⟩)
  have hβR (t : ℝ) (ht : t ∈ Icc 0 T) : β t ∈ closedBall (0 : E) R := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using (le_add_of_nonneg_left (norm_nonneg (α t))).trans (hR ⟨t,ht,rfl⟩)
  obtain ⟨K,hK⟩ := (hf.mono (prod_mono Subset.rfl (subset_univ (closedBall (0 : E) R)))).exists_lipschitzOnWith
    (by norm_num) ((convex_Icc 0 T).prod (convex_closedBall (0 : E) R))
    (isCompact_Icc.prod (isCompact_closedBall (0 : E) R))
  have hKslice (t : ℝ) (ht : t ∈ Icc 0 T) :
      LipschitzOnWith K (fun x => f (t,x)) (closedBall (0 : E) R) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [Prod.dist_eq,dist_self,max_eq_right (dist_nonneg : 0 ≤ dist x y)]
      using hK.dist_le_mul (t,x) ⟨ht,hx⟩ (t,y) ⟨ht,hy⟩
  have hl : Icc 0 t₀ ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht₀.2
  have hr : Icc t₀ T ⊆ Icc 0 T := Icc_subset_Icc ht₀.1 le_rfl
  have hleft : EqOn α β (Icc 0 t₀) :=
    ODE_solution_unique_of_mem_Icc_left (v := fun t x => f (t,x)) (s := fun _ => closedBall (0 : E) R)
      (fun t ht => hKslice t (hl (Ioc_subset_Icc_self ht))) (hαc.mono hl)
      (fun t ht => ((hα t (hl (Ioc_subset_Icc_self ht))).mono hl).mono_of_mem_nhdsWithin (Icc_mem_nhdsLE_of_mem ht))
      (fun t ht => hαR t (hl (Ioc_subset_Icc_self ht))) (hβc.mono hl)
      (fun t ht => ((hβ t (hl (Ioc_subset_Icc_self ht))).mono hl).mono_of_mem_nhdsWithin (Icc_mem_nhdsLE_of_mem ht))
      (fun t ht => hβR t (hl (Ioc_subset_Icc_self ht))) hinit
  have hright : EqOn α β (Icc t₀ T) :=
    ODE_solution_unique_of_mem_Icc_right (v := fun t x => f (t,x)) (s := fun _ => closedBall (0 : E) R)
      (fun t ht => hKslice t (hr (Ico_subset_Icc_self ht))) (hαc.mono hr)
      (fun t ht => ((hα t (hr (Ico_subset_Icc_self ht))).mono hr).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
      (fun t ht => hαR t (hr (Ico_subset_Icc_self ht))) (hβc.mono hr)
      (fun t ht => ((hβ t (hr (Ico_subset_Icc_self ht))).mono hr).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
      (fun t ht => hβR t (hr (Ico_subset_Icc_self ht))) hinit
  intro t ht
  rcases le_total t t₀ with h | h
  · exact hleft ⟨ht.1,h⟩
  · exact hright ⟨h,ht.2⟩
end SlabUniqueness

lemma contDiffOn_lorentzField_slab {E B : Field} {T : ℝ} {k : ℕ∞ω}
    (hE : ContDiffOn ℝ k E (Icc 0 T ×ˢ (univ : Set Vec)))
    (hB : ContDiffOn ℝ k B (Icc 0 T ×ˢ (univ : Set Vec))) :
    ContDiffOn ℝ k (lorentzField E B) (Icc 0 T ×ˢ (univ : Set Phase)) := by
  have hx : ContDiff ℝ k (fun z : ℝ × Phase => (z.1,z.2.1)) :=
    contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)
  have hm : MapsTo (fun z : ℝ × Phase => (z.1,z.2.1))
      (Icc 0 T ×ˢ (univ : Set Phase)) (Icc 0 T ×ˢ (univ : Set Vec)) := fun _ h => ⟨h.1,mem_univ _⟩
  have hu : ContDiff ℝ k (fun z : ℝ × Phase => velocity z.2.2) :=
    contDiff_velocity.comp (contDiff_snd.comp contDiff_snd)
  exact hu.contDiffOn.prodMk ((hE.comp hx.contDiffOn hm).add
    (contDiff_cross.contDiffOn.comp (hu.contDiffOn.prodMk (hB.comp hx.contDiffOn hm)) (mapsTo_univ _ _)))

lemma exists_lorentz_ode_on_slab {E B : Field} {T t₀ : ℝ} (hT : 0 ≤ T)
    (ht₀ : t₀ ∈ Icc 0 T) (hE : ContDiffOn ℝ 2 E (Icc 0 T ×ˢ (univ : Set Vec)))
    (hB : ContDiffOn ℝ 2 B (Icc 0 T ×ˢ (univ : Set Vec))) (z₀ : Phase) :
    ∃ α : ℝ → Phase, α t₀=z₀ ∧
      ∀ t ∈ Icc 0 T, HasDerivWithinAt α (lorentzField E B (t,α t)) (Icc 0 T) t := by
  let χ : ContDiffBump z₀.1 := ⟨T+1,T+2,by linarith,by linarith⟩
  obtain ⟨L,hL,hbound⟩ := cutLorentz_bounded_slab hT hE.continuousOn hB.continuousOn χ
  obtain ⟨α,hα₀,hα⟩ := exists_bounded_ode_on_Icc hT ht₀ hL
    ((cutLorentz_regular_slab hE hB χ.contDiff).of_le (by norm_num)) hbound z₀
  have hX : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun r => (α r).1)
      (velocity (α t).2) (Icc 0 T) t := fun t ht => (hα t ht).fst
  have hLip : LipschitzOnWith 1 (fun r => (α r).1) (Icc 0 T) :=
    (convex_Icc 0 T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le hX
      (fun t _ => by exact_mod_cast (norm_velocity_lt_one (α t).2).le)
  have hone : ∀ t ∈ Icc 0 T, χ (α t).1=1 := by
    intro t ht
    apply χ.one_of_mem_closedBall
    have hdist := hLip.dist_le_mul t ht t₀ ht₀
    simp only [hα₀,NNReal.coe_one,one_mul] at hdist
    change dist (α t).1 z₀.1 ≤ T+1
    have hd : dist t t₀ ≤ T := by
      rw [Real.dist_eq,abs_le]
      constructor <;> linarith [ht.1,ht.2,ht₀.1,ht₀.2]
    linarith
  refine ⟨α,hα₀,?_⟩
  intro t ht
  simpa only [cutLorentz,lorentzField,lorentzPhase,hone t ht,one_smul] using hα t ht

lemma exists_global_lorentz_flow_on_slab {E B : Field} {T : ℝ} (hT : 0 < T)
    (hE : ContDiffOn ℝ 2 E (Icc 0 T ×ˢ (univ : Set Vec)))
    (hB : ContDiffOn ℝ 2 B (Icc 0 T ×ˢ (univ : Set Vec))) :
    ∃ α : Phase → ℝ → Phase, ∃ A : Phase → ℝ → (Phase →L[ℝ] Phase),
      (∀ z, α z 0 = z ∧
        (∀ t ∈ Icc 0 T, HasDerivWithinAt (α z) (lorentzField E B (t,α z t)) (Icc 0 T) t) ∧
        (∀ t ∈ Icc 0 T, HasFDerivAt (α · t) (A z t) z) ∧
        (∀ t ∈ Icc 0 T, (A z t).det = 1) ∧
        ∀ t ∈ Ioo 0 T, HasStrictFDerivAt (fun p : ℝ × Phase => α p.2 p.1)
          ((ContinuousLinearMap.toSpanSingleton ℝ (lorentzField E B (t,α z t))).coprod (A z t)) (t,z)) ∧
      ∀ t ∈ Icc 0 T, Function.Bijective (α · t) := by
  choose β D hβ _ using fun z₀ => exists_finite_lorentz_within_volume_flow hT hE hB z₀
  let α : Phase → ℝ → Phase := fun z => β z z
  let A : Phase → ℝ → (Phase →L[ℝ] Phase) := fun z => D z z
  have hmem (z : Phase) : z ∈ ball z (1/2 : ℝ) := mem_ball_self (by norm_num)
  have hinit (z : Phase) : α z 0 = z := (hβ z z (hmem z)).1
  have hder (z : Phase) : ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (α z) (lorentzField E B (t,α z t)) (Icc 0 T) t := (hβ z z (hmem z)).2.1
  have hf : ContDiffOn ℝ 1 (lorentzField E B) (Icc 0 T ×ˢ (univ : Set Phase)) :=
    contDiffOn_lorentzField_slab (hE.of_le (by norm_num)) (hB.of_le (by norm_num))
  have heq (x y : Phase) (hy : y ∈ ball x (1/2 : ℝ)) : EqOn (α y) (β x y) (Icc 0 T) :=
    eqOn_of_within_ode hf (hder y) (hβ x y hy).2.1 ⟨le_rfl,hT.le⟩
      ((hinit y).trans (hβ x y hy).1.symm)
  refine ⟨α,A,?_,?_⟩
  · intro z
    refine ⟨hinit z,hder z,?_,(hβ z z (hmem z)).2.2.2.1,?_⟩
    · intro t ht
      apply ((hβ z z (hmem z)).2.2.1 t ht).congr_of_eventuallyEq
      filter_upwards [isOpen_ball.mem_nhds (hmem z)] with y hy
      exact heq z y hy ht
    · intro t ht
      have hh := (hβ z z (hmem z)).2.2.2.2 t ht
      change HasStrictFDerivAt (fun p : ℝ × Phase => α p.2 p.1) _ (t,z)
      apply hh.congr_of_eventuallyEq
      filter_upwards [(isOpen_Ioo.prod isOpen_ball).mem_nhds ⟨ht,hmem z⟩] with p hp
      exact (heq z p.2 hp.2 (Ioo_subset_Icc_self hp.1)).symm
  · intro t ht
    constructor
    · intro x y he
      have hh := eqOn_of_within_ode hf (hder x) (hder y) ht he ⟨le_rfl,hT.le⟩
      simpa only [hinit] using hh
    · intro y
      obtain ⟨γ,hγ₀,hγ⟩ := exists_lorentz_ode_on_slab hT.le ht hE hB y
      refine ⟨γ 0,?_⟩
      exact (eqOn_of_within_ode hf (hder (γ 0)) hγ ⟨le_rfl,hT.le⟩ (hinit (γ 0)) ht).trans hγ₀


open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set MeasureTheory
open Set MeasureTheory Filter
open scoped Topology ContDiff
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma timeFlowDerivative_det (v : E) (A : E →L[ℝ] E) :
    (timeFlowDerivative v A).det = A.det := by
  have hh := det_time_triangular (timeFlowDerivative v A).toLinearMap (by apply LinearMap.ext; intro p; rfl)
  have he : (LinearMap.snd ℝ ℝ E).comp ((timeFlowDerivative v A).toLinearMap.comp (LinearMap.inr ℝ ℝ E)) = A.toLinearMap := by
    ext x
    simp [timeFlowDerivative]
  rwa [he] at hh

lemma inverse_timeFlowDerivative {v : E} {A : E →L[ℝ] E} (hA : A.det = 1) :
    ∃ e : (ℝ × E) ≃L[ℝ] (ℝ × E), ∃ D : E →L[ℝ] E,
      (e : (ℝ × E) →L[ℝ] (ℝ × E)) = timeFlowDerivative v A ∧ D.det = 1 ∧
      (ContinuousLinearMap.snd ℝ ℝ E).comp (e.symm : (ℝ × E) →L[ℝ] (ℝ × E)) =
        (ContinuousLinearMap.toSpanSingleton ℝ (-D v)).coprod D := by
  have hdet : (timeFlowDerivative v A).toLinearMap.det = 1 := (timeFlowDerivative_det v A).trans hA
  have hunit : IsUnit (timeFlowDerivative v A).toLinearMap.det := hdet.symm ▸ isUnit_one
  let e : (ℝ × E) ≃L[ℝ] (ℝ × E) := (LinearMap.equivOfIsUnitDet hunit).toContinuousLinearEquiv
  have he : (e : (ℝ × E) →L[ℝ] (ℝ × E)) = timeFlowDerivative v A := by
    apply ContinuousLinearMap.ext
    intro z
    exact LinearMap.congr_fun (LinearMap.coe_equivOfIsUnitDet hunit) z
  have happ (z : ℝ × E) : e z = (z.1,z.1 • v+A z.2) := by
    rw [← ContinuousLinearEquiv.coe_coe,he]
    rfl
  have hfst (z : ℝ × E) : (e.symm z).1 = z.1 := by
    have hh := congrArg Prod.fst (e.apply_symm_apply z)
    simpa only [happ] using hh
  let D : E →L[ℝ] E := (ContinuousLinearMap.snd ℝ ℝ E).comp
    ((e.symm : (ℝ × E) →L[ℝ] (ℝ × E)).comp (ContinuousLinearMap.inr ℝ ℝ E))
  have hD : D.det = 1 := by
    have hh := det_time_triangular (e.symm : (ℝ × E) →L[ℝ] (ℝ × E)).toLinearMap (by apply LinearMap.ext; intro z; exact hfst z)
    change (e.symm : (ℝ × E) →L[ℝ] (ℝ × E)).det = D.det at hh
    rw [ContinuousLinearEquiv.det_coe_symm,he,timeFlowDerivative_det,hA,inv_one] at hh
    exact hh.symm
  have hi : e.symm (1,v) = (1,0) := by
    apply e.injective
    simp only [e.apply_symm_apply,happ,one_smul,map_zero,add_zero]
  refine ⟨e,D,he,hD,?_⟩
  apply ContinuousLinearMap.ext
  intro p
  change (e.symm p).2 = p.1 • (-D v)+D p.2
  have hp : p = p.1 • (1,v)+(0,p.2-p.1 • v) := by
    ext <;> simp
  calc
    (e.symm p).2 = (e.symm (p.1 • (1,v)+(0,p.2-p.1 • v))).2 := congrArg (fun z => (e.symm z).2) hp
    _ = D (p.2-p.1 • v) := by
      rw [map_add,map_smul,hi]
      change p.1 • (0 : E)+(e.symm (0,p.2-p.1 • v)).2 = D (p.2-p.1 • v)
      rw [smul_zero,zero_add]
      rfl
    _ = p.1 • (-D v)+D p.2 := by simp only [map_sub,map_smul,smul_neg]; abel

end

open Set MeasureTheory Filter
open scoped Topology ContDiff


open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff


lemma exists_phaseFlowOn {E B : Field} {T : ℝ} (hT : 0 < T)
    (hE : ContDiffOn ℝ 2 E (Icc 0 T ×ˢ (univ : Set Vec)))
    (hB : ContDiffOn ℝ 2 B (Icc 0 T ×ˢ (univ : Set Vec))) :
    Nonempty (PhaseFlowOn E B T) := by
  obtain ⟨α,A,hα,hbij⟩ := exists_global_lorentz_flow_on_slab hT hE hB
  exact ⟨⟨α,A,fun z => (hα z).1,fun z => (hα z).2.1,fun z => (hα z).2.2.1,
    fun z => (hα z).2.2.2.1,fun z => (hα z).2.2.2.2,hbij⟩⟩

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal


lemma PhaseFlowOn.inversePhase_flow {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (hs : s ∈ Icc 0 T) (z : Phase) : inversePhase F.flow (s,F.flow z s) = z :=
  Function.leftInverse_invFun (F.bijective s hs).1 z

lemma PhaseFlowOn.flow_inversePhase {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (hs : s ∈ Icc 0 T) (z : Phase) : F.flow (inversePhase F.flow (s,z)) s = z :=
  Function.invFun_eq ((F.bijective s hs).2 z)

open Set MeasureTheory Filter
open scoped Topology ContDiff


end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_LabelOccupationDurationMass
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
open scoped Topology ContDiff NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal RealInnerProductSpace

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma PhaseFlowOn.position_lipschitz {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (z : Phase) :
    LipschitzOnWith 1 (fun t => (F.flow z t).1) (Icc 0 T) := by
  apply (convex_Icc 0 T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t ht => (F.ode z t ht).fst)
  intro t _
  exact_mod_cast (norm_velocity_lt_one (F.flow z t).2).le

lemma PhaseFlowOn.continuousOn_joint {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (hT : 0≤T)
    (hE : ContinuousOn E (Icc 0 T ×ˢ (univ : Set Vec)))
    (hB : ContinuousOn B (Icc 0 T ×ˢ (univ : Set Vec))) :
    ContinuousOn (fun p : ℝ × Phase => F.flow p.2 p.1)
      (Icc 0 T ×ˢ (univ : Set Phase)) := by
  intro p hp
  obtain ⟨M,hM⟩ := (isCompact_Icc.prod (isCompact_closedBall p.2.1 (T+1))).bddAbove_image
    ((hE.norm.add hB.norm).mono (prod_mono Subset.rfl (subset_univ _)))
  let L : ℝ≥0 := ⟨max 1 M, zero_le_one.trans (le_max_left _ _)⟩
  have hpos (z : Phase) (hz : z ∈ ball p.2 (1/2:ℝ)) (t : ℝ) (ht : t ∈ Icc 0 T) :
      (F.flow z t).1 ∈ closedBall p.2.1 (T+1) := by
    have hh := (F.position_lipschitz z).dist_le_mul t ht 0 ⟨le_rfl,hT⟩
    simp only [F.initial,NNReal.coe_one,one_mul,Real.dist_eq,sub_zero,abs_of_nonneg ht.1] at hh
    have hz' : dist z.1 p.2.1 < (1/2:ℝ) := (le_max_left _ _).trans_lt hz
    exact (dist_triangle _ z.1 _).trans (add_le_add hh hz'.le) |>.trans (by linarith [ht.2])
  have hLip (z : Phase) (hz : z ∈ ball p.2 (1/2:ℝ)) :
      LipschitzOnWith L (F.flow z) (Icc 0 T) := by
    apply (convex_Icc 0 T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le (F.ode z)
    intro t ht
    apply NNReal.coe_le_coe.mp
    change ‖lorentzField E B (t,F.flow z t)‖ ≤ max 1 M
    rw [lorentzField,lorentzPhase,Prod.norm_def]
    apply max_le
    · exact (norm_velocity_lt_one _).le.trans (le_max_left _ _)
    · calc
        _ ≤ ‖E (t,(F.flow z t).1)‖+‖B (t,(F.flow z t).1)‖ := by
          exact (norm_add_le _ _).trans (add_le_add le_rfl
            ((norm_cross_le _ _).trans
              (mul_le_of_le_one_left (norm_nonneg _) (norm_velocity_lt_one _).le)))
        _ ≤ M := hM ⟨(t,(F.flow z t).1),⟨ht,hpos z hz t ht⟩,rfl⟩
        _ ≤ _ := le_max_right _ _
  have hc : ContinuousAt (fun z => F.flow z p.1) p.2 := (F.label p.2 p.1 hp.1).continuousAt
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ,hδ,hlabel⟩ := Metric.continuousAt_iff.mp hc (ε/2) (by positivity)
  refine ⟨min (1/2:ℝ) (min δ (ε/(2*((L:ℝ)+1)))),by positivity,?_⟩
  intro q hq hdist
  have hd₁ : dist q.1 p.1 < ε/(2*((L:ℝ)+1)) :=
    (le_max_left _ _).trans_lt (hdist.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  have hd₂ : dist q.2 p.2 < δ :=
    (le_max_right _ _).trans_lt (hdist.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hqball : q.2 ∈ ball p.2 (1/2:ℝ) :=
    (le_max_right _ _).trans_lt (hdist.trans_le (min_le_left _ _))
  have hh : (L:ℝ)*dist q.1 p.1 < ε/2 := by
    have hh := (lt_div_iff₀ (show 0<2*((L:ℝ)+1) by positivity)).mp hd₁
    nlinarith [dist_nonneg (x := q.1) (y := p.1)]
  exact (dist_triangle _ (F.flow q.2 p.1) _).trans_lt
    (add_lt_add_of_le_of_lt ((hLip q.2 hqball).dist_le_mul q.1 hq.1 p.1 hp.1)
      (hlabel hd₂) |>.trans_le (by linarith))

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_VlasovConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open Set MeasureTheory Metric Filter ODE
open scoped Topology NNReal ContDiff

namespace RVM

universe u

lemma contDiff_spaceDerivative {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × E → E} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (spaceDerivative f) := by
  have h := (hf.fderiv_right (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)).clm_comp
    (contDiff_const (c := ContinuousLinearMap.inr ℝ ℝ E))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  exact ((hf.differentiable (by simp) z).hasFDerivAt.comp z.2
    ((hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id z.2))).fderiv

lemma smooth_ode_unique {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : ℝ × E → E} {T : ℝ}
    (hf : ContDiff ℝ 1 f) {α β : ℝ → E}
    (hα : ∀ t ∈ Icc 0 T, HasDerivWithinAt α (f (t,α t)) (Icc 0 T) t)
    (hβ : ∀ t ∈ Icc 0 T, HasDerivWithinAt β (f (t,β t)) (Icc 0 T) t)
    (h0 : α 0 = β 0) : EqOn α β (Icc 0 T) := by
  have hαc := HasDerivWithinAt.continuousOn hα
  have hβc := HasDerivWithinAt.continuousOn hβ
  obtain ⟨R,hR⟩ := ((isCompact_Icc.image_of_continuousOn hαc).union
    (isCompact_Icc.image_of_continuousOn hβc)).isBounded.subset_closedBall (0 : E)
  obtain ⟨K,hK⟩ := hf.contDiffOn.exists_lipschitzOnWith (by norm_num)
    ((convex_Icc 0 T).prod (convex_closedBall (0 : E) R))
    (isCompact_Icc.prod (isCompact_closedBall (0 : E) R))
  apply ODE_solution_unique_of_mem_Icc_right (v := fun t x => f (t,x))
    (s := fun _ => closedBall (0 : E) R) (K := K) _ hαc _ _ hβc _ _ h0
  · intro t ht
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [Prod.dist_eq,dist_self,max_eq_right (dist_nonneg : 0 ≤ dist x y)]
      using hK.dist_le_mul (t,x) ⟨Ico_subset_Icc_self ht,hx⟩
        (t,y) ⟨Ico_subset_Icc_self ht,hy⟩
  · intro t ht
    exact (hα t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
  · intro t ht
    exact hR (Or.inl ⟨t,Ico_subset_Icc_self ht,rfl⟩)
  · intro t ht
    exact (hβ t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
  · intro t ht
    exact hR (Or.inr ⟨t,Ico_subset_Icc_self ht,rfl⟩)

lemma bounded_cutoff_vector_field {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : ℝ × E → E} (hf : ContDiff ℝ ∞ f) (T R : ℝ) :
    ∃ g : ℝ × E → E, ∃ L : ℝ, 0 ≤ L ∧ ContDiff ℝ ∞ g ∧
      (∀ t ∈ Icc 0 T, ∀ x, ‖g (t,x)‖ ≤ L) ∧
      ∀ t x, x ∈ closedBall (0 : E) R → g (t,x) = f (t,x) := by
  let χ : ContDiffBump (0 : E) := ⟨max 0 R + 1,max 0 R + 2,by positivity,by linarith⟩
  let g : ℝ × E → E := fun z => χ z.2 • f z
  have hg : ContDiff ℝ ∞ g := (χ.contDiff.comp contDiff_snd).smul hf
  obtain ⟨L,hL⟩ := (isCompact_Icc.prod (isCompact_closedBall (0 : E) χ.rOut)).bddAbove_image
    hg.continuous.norm.continuousOn
  refine ⟨g,max 0 L,le_max_left _ _,hg,?_,?_⟩
  · intro t ht x
    by_cases hx : x ∈ closedBall (0 : E) χ.rOut
    · exact (hL ⟨(t,x),⟨ht,hx⟩,rfl⟩).trans (le_max_right _ _)
    have hz : χ x = 0 := by
      apply Function.notMem_support.mp
      rw [χ.support_eq]
      exact fun hm => hx (ball_subset_closedBall hm)
    simp only [g,hz,zero_smul,norm_zero]
    exact le_max_left _ _
  · intro t x hx
    have hm : x ∈ closedBall (0 : E) χ.rIn := by
      exact closedBall_subset_closedBall (by dsimp [χ]; linarith [le_max_right (0 : ℝ) R]) hx
    change χ x • f (t,x) = f (t,x)
    rw [χ.one_of_mem_closedBall hm,one_smul]

lemma contDiffAt_flow_transfer {E Z : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : ℝ × E → E} {T : ℝ} {U : Set Z} {V : Set E} {g : Z → E}
    {α : Z → ℝ → E} {β : E → ℝ → E} {n : ℕ} {t : ℝ} {x : Z}
    (hf : ContDiff ℝ 1 f) (hU : IsOpen U) (hV : IsOpen V)
    (hg : ContDiffOn ℝ n g U)
    (hα0 : ∀ x ∈ U, α x 0 = g x)
    (hαd : ∀ x ∈ U, ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (α x) (f (t,α x t)) (Icc 0 T) t)
    (hβ0 : ∀ y ∈ V, β y 0 = y)
    (hβd : ∀ y ∈ V, ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (β y) (f (t,β y t)) (Icc 0 T) t)
    (hβ : ContDiffOn ℝ n (fun z : ℝ × E => β z.2 z.1) (Ioo 0 T ×ˢ V))
    (ht : t ∈ Ioo 0 T) (hx : x ∈ U) (hmem : g x ∈ V) :
    ContDiffAt ℝ n (fun z : ℝ × Z => α z.2 z.1) (t,x) := by
  have hgc := (hg.contDiffAt (hU.mem_nhds hx)).comp (t,x) contDiffAt_snd
  have hh := (hβ.contDiffAt ((isOpen_Ioo.prod hV).mem_nhds ⟨ht,hmem⟩)).comp
    (t,x) (contDiffAt_fst.prodMk hgc)
  apply hh.congr_of_eventuallyEq
  have heU : ∀ᶠ z : ℝ × Z in 𝓝 (t,x), z.2 ∈ U :=
    continuousAt_snd.eventually (hU.mem_nhds hx)
  have heV : ∀ᶠ z : ℝ × Z in 𝓝 (t,x), g z.2 ∈ V :=
    hgc.continuousAt.eventually (hV.mem_nhds hmem)
  have heT : ∀ᶠ z : ℝ × Z in 𝓝 (t,x), z.1 ∈ Ioo 0 T :=
    continuousAt_fst.eventually (isOpen_Ioo.mem_nhds ht)
  filter_upwards [heU,heV,heT] with z hzU hzV hzT
  exact smooth_ode_unique hf (hαd z.2 hzU) (hβd (g z.2) hzV)
    ((hα0 z.2 hzU).trans (hβ0 (g z.2) hzV).symm) (Ioo_subset_Icc_self hzT)

lemma boundedFlowRegularity_zero : BoundedFlowRegularity.{u} 0 := by
  intro E Z _ _ _ _ _ f T L U g α hT hL hf hb hU hg hα0 hαd z hz
  obtain ⟨β,A,K,hsol,hLip⟩ := exists_bounded_within_variational_flow hT hL
    (contDiff_infty.mp hf 2).contDiffOn hb (g z.2)
  have hβc : ContinuousOn (fun w : ℝ × E => β w.2 w.1)
      (Icc 0 T ×ˢ closedBall (g z.2) (1/2 : ℝ)) :=
    continuousOn_time_label_of_lipschitz
      (fun y hy => HasDerivWithinAt.continuousOn (hsol y hy).2.2.1)
      (fun t ht => (hLip t ht).1)
  have hreg : ContDiffOn ℝ 0 (fun w : ℝ × E => β w.2 w.1)
      (Ioo 0 T ×ˢ ball (g z.2) (1/2 : ℝ)) :=
    contDiffOn_zero.mpr (hβc.mono (prod_mono Ioo_subset_Icc_self ball_subset_closedBall))
  exact (contDiffAt_flow_transfer (hf.of_le (by simp)) hU isOpen_ball (hg.of_le (by simp))
    hα0 hαd (fun y hy => (hsol y (ball_subset_closedBall hy)).1)
    (fun y hy => (hsol y (ball_subset_closedBall hy)).2.2.1)
    hreg hz.1 hz.2 (by simp)).contDiffWithinAt

lemma boundedFlowRegularity_succ {n : ℕ} (hn : BoundedFlowRegularity.{u} n) :
    BoundedFlowRegularity.{u} (n+1) := by
  intro E Z _ _ _ _ _ f T L U g α hT hL hf hb hU hg hα0 hαd z hz
  obtain ⟨β,A,K,hsol,hLip⟩ := exists_bounded_within_variational_flow hT hL
    (contDiff_infty.mp hf 2).contDiffOn hb (g z.2)
  have hβc : ContinuousOn (fun w : ℝ × E => β w.2 w.1)
      (Icc 0 T ×ˢ closedBall (g z.2) (1/2 : ℝ)) :=
    continuousOn_time_label_of_lipschitz
      (fun y hy => HasDerivWithinAt.continuousOn (hsol y hy).2.2.1)
      (fun t ht => (hLip t ht).1)
  have hAc : ContinuousOn (fun w : ℝ × E => A w.2 w.1)
      (Icc 0 T ×ˢ closedBall (g z.2) (1/2 : ℝ)) :=
    continuousOn_time_label_of_lipschitz
      (fun y hy => HasDerivWithinAt.continuousOn (hsol y hy).2.2.2.1)
      (fun t ht => (hLip t ht).2)
  obtain ⟨R,hR⟩ := (isCompact_Icc.prod (isCompact_closedBall (g z.2) (1/2 : ℝ))).bddAbove_image
    (hβc.prodMk hAc).norm
  let F : ℝ × (E × (E →L[ℝ] E)) → E × (E →L[ℝ] E) :=
    fun w => (f (w.1,w.2.1),(spaceDerivative f (w.1,w.2.1)).comp w.2.2)
  have hp : ContDiff ℝ ∞ (fun w : ℝ × (E × (E →L[ℝ] E)) => (w.1,w.2.1)) :=
    contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)
  have hF : ContDiff ℝ ∞ F := (hf.comp hp).prodMk
    (((contDiff_spaceDerivative hf).comp hp).clm_comp (contDiff_snd.comp contDiff_snd))
  obtain ⟨Fc,Lc,hLc,hFc,hFcb,hFceq⟩ := bounded_cutoff_vector_field hF T R
  have heq (x : E) (hx : x ∈ closedBall (g z.2) (1/2 : ℝ)) (t : ℝ) (ht : t ∈ Icc 0 T) :
      Fc (t,(β x t,A x t)) = F (t,(β x t,A x t)) := by
    apply hFceq
    simpa only [mem_closedBall,dist_zero_right] using hR ⟨(t,x),⟨ht,hx⟩,rfl⟩
  have hlift : ContDiffOn ℝ n (fun w : ℝ × E => (β w.2 w.1,A w.2 w.1))
      (Ioo 0 T ×ˢ ball (g z.2) (1/2 : ℝ)) := by
    apply hn (E × (E →L[ℝ] E)) E Fc T Lc (ball (g z.2) (1/2 : ℝ))
      (fun x => (x,ContinuousLinearMap.id ℝ E)) (fun x t => (β x t,A x t))
      hT hLc hFc hFcb isOpen_ball (contDiff_id.prodMk contDiff_const).contDiffOn
    · intro x hx
      exact Prod.ext (hsol x (ball_subset_closedBall hx)).1
        (hsol x (ball_subset_closedBall hx)).2.1
    · intro x hx t ht
      rw [heq x (ball_subset_closedBall hx) t ht]
      exact ((hsol x (ball_subset_closedBall hx)).2.2.1 t ht).prodMk
        ((hsol x (ball_subset_closedBall hx)).2.2.2.1 t ht)
  have hβn : ContDiffOn ℝ n (fun w : ℝ × E => β w.2 w.1)
      (Ioo 0 T ×ˢ ball (g z.2) (1/2 : ℝ)) := contDiff_fst.comp_contDiffOn hlift
  have hAn : ContDiffOn ℝ n (fun w : ℝ × E => A w.2 w.1)
      (Ioo 0 T ×ˢ ball (g z.2) (1/2 : ℝ)) := contDiff_snd.comp_contDiffOn hlift
  let D : ℝ × E → (ℝ × E →L[ℝ] E) := fun w =>
    (ContinuousLinearMap.toSpanSingleton ℝ (f (w.1,β w.2 w.1))).coprod (A w.2 w.1)
  have hDn : ContDiffOn ℝ n D (Ioo 0 T ×ˢ ball (g z.2) (1/2 : ℝ)) := by
    have hfn := (contDiff_infty.mp hf n).comp_contDiffOn
      (contDiffOn_fst.prodMk hβn)
    have hcol := (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := E)).contDiff.comp_contDiffOn hfn
    exact (hcol.clm_comp (contDiffOn_const (c := ContinuousLinearMap.fst ℝ ℝ E))).add
      (hAn.clm_comp (contDiffOn_const (c := ContinuousLinearMap.snd ℝ ℝ E)))
  have hβd (w : ℝ × E) (hw : w ∈ Ioo 0 T ×ˢ ball (g z.2) (1/2 : ℝ)) :
      HasFDerivAt (fun v : ℝ × E => β v.2 v.1) (D w) w := by
    exact (hasStrictFDerivAt_time_flow hf.continuous.continuousOn
      (hβc.mono (prod_mono Subset.rfl ball_subset_closedBall))
      (hAc.mono (prod_mono Subset.rfl ball_subset_closedBall))
      (fun x hx => (hsol x (ball_subset_closedBall hx)).2.2.1)
      (fun t ht x hx => hasFDerivAt_within_variational_flow hT
        (contDiff_infty.mp hf 2).contDiffOn hsol (fun t ht => (hLip t ht).1) hx ht)
      hw.1 hw.2).hasFDerivAt
  have hreg : ContDiffOn ℝ (n+1) (fun w : ℝ × E => β w.2 w.1)
      (Ioo 0 T ×ˢ ball (g z.2) (1/2 : ℝ)) := by
    intro w hw
    have hnh := (isOpen_Ioo.prod isOpen_ball).mem_nhds hw
    exact (contDiffAt_succ_iff_hasFDerivAt.mpr
      ⟨D,⟨Ioo 0 T ×ˢ ball (g z.2) (1/2 : ℝ),hnh,hβd⟩,hDn.contDiffAt hnh⟩).contDiffWithinAt
  exact (contDiffAt_flow_transfer (contDiff_infty.mp hf 1) hU isOpen_ball (contDiffOn_infty.mp hg (n+1))
    hα0 hαd (fun y hy => (hsol y (ball_subset_closedBall hy)).1)
    (fun y hy => (hsol y (ball_subset_closedBall hy)).2.2.1)
    hreg hz.1 hz.2 (by simp)).contDiffWithinAt

lemma boundedFlowRegularity_all (n : ℕ) : BoundedFlowRegularity.{u} n := by
  induction n with
  | zero => exact boundedFlowRegularity_zero
  | succ n hn => exact boundedFlowRegularity_succ hn

lemma contDiffOn_bounded_flow {E Z : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : ℝ × E → E} {T L : ℝ} {U : Set Z} {g : Z → E} {α : Z → ℝ → E}
    (hT : 0 < T) (hL : 0 ≤ L) (hf : ContDiff ℝ ∞ f)
    (hb : ∀ t ∈ Icc 0 T, ∀ x, ‖f (t,x)‖ ≤ L)
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    (hα0 : ∀ x ∈ U, α x 0 = g x)
    (hαd : ∀ x ∈ U, ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (α x) (f (t,α x t)) (Icc 0 T) t) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Z => α z.2 z.1) (Ioo 0 T ×ˢ U) := by
  rw [contDiffOn_infty]
  intro n
  exact boundedFlowRegularity_all n E Z f T L U g α hT hL hf hb hU hg hα0 hαd

lemma PhaseFlowOn.contDiffOn_joint {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (hT : 0 < T)
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B) :
    ContDiffOn ℝ ∞ (fun w : ℝ × Phase => F.flow w.2 w.1)
      (Ioo 0 T ×ˢ (univ : Set Phase)) := by
  have hc := F.continuousOn_joint hT.le hE.continuous.continuousOn hB.continuous.continuousOn
  have hf := contDiff_lorentzField hE hB
  intro z hz
  obtain ⟨R,hR⟩ := (isCompact_Icc.prod (isCompact_closedBall z.2 (1 : ℝ))).bddAbove_image
    (hc.mono (prod_mono Subset.rfl (subset_univ _))).norm
  obtain ⟨f,L,hL,hf,hb,heq⟩ := bounded_cutoff_vector_field hf T R
  have hreg : ContDiffOn ℝ ∞ (fun w : ℝ × Phase => F.flow w.2 w.1)
      (Ioo 0 T ×ˢ ball z.2 1) := by
    apply contDiffOn_bounded_flow hT hL hf hb isOpen_ball contDiffOn_id
      (fun x _ => F.initial x)
    intro x hx t ht
    rw [heq t (F.flow x t) (by
      simpa only [mem_closedBall,dist_zero_right] using
        hR ⟨(t,x),⟨ht,ball_subset_closedBall hx⟩,rfl⟩)]
    exact F.ode x t ht
  exact (hreg.contDiffAt ((isOpen_Ioo.prod isOpen_ball).mem_nhds
    ⟨hz.1,mem_ball_self zero_lt_one⟩)).contDiffWithinAt

lemma contDiffAt_inversePhase {Q : Type u}
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
    {α : Q → ℝ → Q} {v x : Q} {A : Q →L[ℝ] Q} {T t : ℝ}
    (hbij : ∀ s ∈ Ioo 0 T, Function.Bijective (α · s)) (ht : t ∈ Ioo 0 T)
    (hA : A.det = 1)
    (hα : HasFDerivAt (fun z : ℝ × Q => α z.2 z.1)
      ((ContinuousLinearMap.toSpanSingleton ℝ v).coprod A) (t,x))
    (hreg : ContDiffAt ℝ ∞ (fun z : ℝ × Q => α z.2 z.1) (t,x)) :
    ContDiffAt ℝ ∞ (inversePhase α) (t,α x t) := by
  obtain ⟨e,D,he,hD,hder⟩ := inverse_timeFlowDerivative hA
  let Φ : ℝ × Q → ℝ × Q := fun z => (z.1,α z.2 z.1)
  have hΦd : HasFDerivAt Φ (e : (ℝ × Q) →L[ℝ] (ℝ × Q)) (t,x) := by
    rw [he]
    exact hasFDerivAt_fst.prodMk hα
  have hΦc : ContDiffAt ℝ ∞ Φ (t,x) := contDiffAt_fst.prodMk hreg
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  let Z := hΦc.localInverse hΦd hn
  have hZ : ContDiffAt ℝ ∞ Z (t,α x t) := hΦc.to_localInverse hΦd hn
  have hr := (hΦc.hasStrictFDerivAt' hΦd hn).eventually_right_inverse
  have heq : inversePhase α =ᶠ[𝓝 (t,α x t)] (fun z => (Z z).2) := by
    have htime : ∀ᶠ z : ℝ × Q in 𝓝 (t,α x t), z.1 ∈ Ioo 0 T :=
      continuous_fst.continuousAt.eventually (isOpen_Ioo.mem_nhds ht)
    filter_upwards [hr,htime] with z hz hzt
    have hx : (Z z).1 = z.1 := by
      have hh := congrArg Prod.fst hz
      exact hh
    have hy : α (Z z).2 z.1 = z.2 := by
      have hh := congrArg Prod.snd hz
      change α (Z z).2 (Z z).1 = z.2 at hh
      rwa [hx] at hh
    apply (hbij z.1 hzt).1
    exact (Function.invFun_eq ((hbij z.1 hzt).2 z.2)).trans hy.symm
  exact hZ.snd.congr_of_eventuallyEq heq

lemma PhaseFlowOn.contDiffOn_inverse {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (hT : 0 < T)
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B) :
    ContDiffOn ℝ ∞ (inversePhase F.flow) (Ioo 0 T ×ˢ (univ : Set Phase)) := by
  intro z hz
  let y := inversePhase F.flow z
  have hy : F.flow y z.1 = z.2 := F.flow_inversePhase (Ioo_subset_Icc_self hz.1) z.2
  have hh := contDiffAt_inversePhase
    (fun s hs => F.bijective s (Ioo_subset_Icc_self hs)) hz.1
    (F.det_one y z.1 (Ioo_subset_Icc_self hz.1))
    (F.joint y z.1 hz.1).hasFDerivAt
    ((F.contDiffOn_joint hT hE hB).contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
      ⟨hz.1,mem_univ y⟩))
  simpa only [hy] using hh.contDiffWithinAt

lemma exists_symmetricLorentzFlow {E B : Field} {R : ℝ} (hR : 0 < R)
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B) :
    Nonempty (SymmetricLorentzFlow E B R) := by
  let E' : Field := fun z => E (z.1-R,z.2)
  let B' : Field := fun z => B (z.1-R,z.2)
  have hs : ContDiff ℝ ∞ (fun z : ℝ × Vec => (z.1-R,z.2)) :=
    (contDiff_fst.sub contDiff_const).prodMk contDiff_snd
  have hE' : ContDiff ℝ ∞ E' := hE.comp hs
  have hB' : ContDiff ℝ ∞ B' := hB.comp hs
  obtain ⟨F⟩ := exists_phaseFlowOn (show 0 < 2*R by positivity)
    (contDiff_infty.mp hE' 2).contDiffOn (contDiff_infty.mp hB' 2).contDiffOn
  have hmid : R ∈ Ioo 0 (2*R) := ⟨hR,by linarith⟩
  have htime {t : ℝ} (ht : t ∈ Ioo (-R) R) : t+R ∈ Ioo 0 (2*R) :=
    ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hfc := F.contDiffOn_joint (by positivity) hE' hB'
  have hic := F.contDiffOn_inverse (by positivity) hE' hB'
  have hfmid : ContDiff ℝ ∞ (fun z => F.flow z R) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    exact (hfc.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
      ⟨hmid,mem_univ z⟩)).comp z (contDiffAt_const.prodMk contDiffAt_id)
  have himid : ContDiff ℝ ∞ (fun z => inversePhase F.flow (R,z)) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    exact (hic.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
      ⟨hmid,mem_univ z⟩)).comp z (contDiffAt_const.prodMk contDiffAt_id)
  let fw : Phase → ℝ → Phase := fun z t => F.flow (inversePhase F.flow (R,z)) (t+R)
  let bw : ℝ × Phase → Phase := fun w => F.flow (inversePhase F.flow (w.1+R,w.2)) R
  refine ⟨⟨fw,bw,?_,?_,?_,?_,?_,?_⟩⟩
  · intro z
    simpa only [fw,zero_add] using F.flow_inversePhase (Ioo_subset_Icc_self hmid) z
  · intro z t ht
    have hd := (F.ode (inversePhase F.flow (R,z)) (t+R) (Ioo_subset_Icc_self (htime ht))).hasDerivAt
      (Icc_mem_nhds (htime ht).1 (htime ht).2)
    simpa [fw,E',B',lorentzField,lorentzPhase,Function.comp_def] using
      hd.scomp t ((hasDerivAt_id t).add_const R)
  · exact hfc.comp ((contDiff_fst.add contDiff_const).prodMk
        (himid.comp contDiff_snd)).contDiffOn (fun _ hw => ⟨htime hw.1,mem_univ _⟩)
  · exact hfmid.comp_contDiffOn
      (hic.comp ((contDiff_fst.add contDiff_const).prodMk contDiff_snd).contDiffOn
        (fun _ hw => ⟨htime hw.1,mem_univ _⟩))
  · intro t ht z
    change F.flow (inversePhase F.flow
      (t+R,F.flow (inversePhase F.flow (R,z)) (t+R))) R = z
    rw [F.inversePhase_flow (Ioo_subset_Icc_self (htime ht))]
    exact F.flow_inversePhase (Ioo_subset_Icc_self hmid) z
  · intro t ht z
    change F.flow (inversePhase F.flow
      (R,F.flow (inversePhase F.flow (t+R,z)) R)) (t+R) = z
    rw [F.inversePhase_flow (Ioo_subset_Icc_self hmid)]
    exact F.flow_inversePhase (Ioo_subset_Icc_self (htime ht)) z

lemma smooth_ode_unique_Icc {Q : Type u}
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
    {f : ℝ × Q → Q} {a b t₀ : ℝ} (hf : ContDiff ℝ 1 f) {α β : ℝ → Q}
    (hα : ∀ t ∈ Icc a b, HasDerivAt α (f (t,α t)) t)
    (hβ : ∀ t ∈ Icc a b, HasDerivAt β (f (t,β t)) t)
    (ht₀ : t₀ ∈ Ioo a b) (h0 : α t₀ = β t₀) : EqOn α β (Icc a b) := by
  have hαc : ContinuousOn α (Icc a b) := fun _ ht => (hα _ ht).continuousAt.continuousWithinAt
  have hβc : ContinuousOn β (Icc a b) := fun _ ht => (hβ _ ht).continuousAt.continuousWithinAt
  obtain ⟨R,hR⟩ := ((isCompact_Icc.image_of_continuousOn hαc).union
    (isCompact_Icc.image_of_continuousOn hβc)).isBounded.subset_closedBall (0 : Q)
  obtain ⟨K,hK⟩ := hf.contDiffOn.exists_lipschitzOnWith (by norm_num)
    ((convex_Icc a b).prod (convex_closedBall (0 : Q) R))
    (isCompact_Icc.prod (isCompact_closedBall (0 : Q) R))
  apply ODE_solution_unique_of_mem_Icc (v := fun t x => f (t,x))
    (s := fun _ => closedBall (0 : Q) R) (K := K) _ ht₀ hαc _ _ hβc _ _ h0
  · intro t ht
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [Prod.dist_eq,dist_self,max_eq_right (dist_nonneg : 0 ≤ dist x y)]
      using hK.dist_le_mul (t,x) ⟨Ioo_subset_Icc_self ht,hx⟩
        (t,y) ⟨Ioo_subset_Icc_self ht,hy⟩
  · intro t ht
    exact hα t (Ioo_subset_Icc_self ht)
  · intro t ht
    exact hR (Or.inl ⟨t,Ioo_subset_Icc_self ht,rfl⟩)
  · intro t ht
    exact hβ t (Ioo_subset_Icc_self ht)
  · intro t ht
    exact hR (Or.inr ⟨t,Ioo_subset_Icc_self ht,rfl⟩)

lemma SymmetricLorentzFlow.agree {E B : Field} {R S t : ℝ}
    (F : SymmetricLorentzFlow E B R) (G : SymmetricLorentzFlow E B S)
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
    (htR : |t| < R) (htS : |t| < S) (z : Phase) : F.forward z t = G.forward z t := by
  let r := (|t|+min R S)/2
  have hr : |t| < r := by dsimp [r]; have := lt_min htR htS; linarith
  have hrR : r < R := by dsimp [r]; linarith [min_le_left R S]
  have hrS : r < S := by dsimp [r]; linarith [min_le_right R S]
  have hr0 : 0 < r := (abs_nonneg t).trans_lt hr
  have hsubR : Icc (-r) r ⊆ Ioo (-R) R := by
    intro u hu; exact ⟨by linarith [hu.1],by linarith [hu.2]⟩
  have hsubS : Icc (-r) r ⊆ Ioo (-S) S := by
    intro u hu; exact ⟨by linarith [hu.1],by linarith [hu.2]⟩
  exact smooth_ode_unique_Icc (contDiff_infty.mp (contDiff_lorentzField hE hB) 1)
    (fun u hu => F.ode z u (hsubR hu)) (fun u hu => G.ode z u (hsubS hu))
    ⟨by linarith,hr0⟩ ((F.initial z).trans (G.initial z).symm)
    ⟨by linarith [(neg_le_abs t)],by linarith [le_abs_self t]⟩

lemma SymmetricLorentzFlow.backward_agree {E B : Field} {R S t : ℝ}
    (F : SymmetricLorentzFlow E B R) (G : SymmetricLorentzFlow E B S)
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
    (htR : |t| < R) (htS : |t| < S) (z : Phase) : F.backward (t,z) = G.backward (t,z) := by
  have hR : t ∈ Ioo (-R) R := abs_lt.mp htR
  have hS : t ∈ Ioo (-S) S := abs_lt.mp htS
  calc
    F.backward (t,z) = F.backward (t,G.forward (G.backward (t,z)) t) := by
      rw [G.right_inverse t hS z]
    _ = F.backward (t,F.forward (G.backward (t,z)) t) := by
      rw [F.agree G hE hB htR htS]
    _ = G.backward (t,z) := F.left_inverse t hR _

lemma exists_smoothLorentzFlow_oai {E B : Field}
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B) : Nonempty (SmoothLorentzFlow E B) := by
  let F : (R : ℝ) → 0 < R → SymmetricLorentzFlow E B R :=
    fun R hR => Classical.choice (exists_symmetricLorentzFlow hR hE hB)
  let rad : ℝ → ℝ := fun t => |t|+1
  have hrad0 : ∀ t, |t| < rad t := fun t => by dsimp [rad]; linarith
  have hrad : ∀ t, |t| < rad t := hrad0
  have hpos : ∀ t, 0 < rad t := fun t => (abs_nonneg t).trans_lt (hrad t)
  let fw : Phase → ℝ → Phase := fun z t => (F (rad t) (hpos t)).forward z t
  let bw : ℝ × Phase → Phase := fun w => (F (rad w.1) (hpos w.1)).backward w
  have hfw {R : ℝ} (hR : 0 < R) {t : ℝ} (ht : |t| < R) (z : Phase) :
      fw z t = (F R hR).forward z t :=
    (F (rad t) (hpos t)).agree (F R hR) hE hB (hrad t) ht z
  have hbw {R : ℝ} (hR : 0 < R) {t : ℝ} (ht : |t| < R) (z : Phase) :
      bw (t,z) = (F R hR).backward (t,z) :=
    (F (rad t) (hpos t)).backward_agree (F R hR) hE hB (hrad t) ht z
  have hlocal (t : ℝ) : ∀ᶠ u : ℝ in 𝓝 t, |u| < rad t :=
    continuous_abs.continuousAt.eventually_lt_const (hrad t)
  refine ⟨⟨fw,bw,?_,?_,?_,?_,?_,?_⟩⟩
  · intro z
    exact (F (rad 0) (hpos 0)).initial z
  · intro z t
    have heq : fw z =ᶠ[𝓝 t] (F (rad t) (hpos t)).forward z := by
      filter_upwards [hlocal t] with u hu
      exact hfw (hpos t) hu z
    exact ((F (rad t) (hpos t)).ode z t (abs_lt.mp (hrad t))).congr_of_eventuallyEq heq
  · rw [contDiff_iff_contDiffAt]
    intro w
    have heq : (fun w : ℝ × Phase => fw w.2 w.1) =ᶠ[𝓝 w]
        (fun v : ℝ × Phase => (F (rad w.1) (hpos w.1)).forward v.2 v.1) := by
      filter_upwards [continuous_fst.continuousAt.tendsto.eventually (hlocal w.1)] with v hv
      exact hfw (hpos w.1) hv v.2
    exact ((F (rad w.1) (hpos w.1)).smooth_forward.contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨abs_lt.mp (hrad w.1),mem_univ w.2⟩)).congr_of_eventuallyEq heq
  · rw [contDiff_iff_contDiffAt]
    intro w
    have heq : bw =ᶠ[𝓝 w] (F (rad w.1) (hpos w.1)).backward := by
      filter_upwards [continuous_fst.continuousAt.tendsto.eventually (hlocal w.1)] with v hv
      exact hbw (hpos w.1) hv v.2
    exact ((F (rad w.1) (hpos w.1)).smooth_backward.contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨abs_lt.mp (hrad w.1),mem_univ w.2⟩)).congr_of_eventuallyEq heq
  · intro t z
    exact (F (rad t) (hpos t)).left_inverse t (abs_lt.mp (hrad t)) z
  · intro t z
    exact (F (rad t) (hpos t)).right_inverse t (abs_lt.mp (hrad t)) z

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

end

end OAI
end

theorem solution : type_of% @OAI.RVM.exists_smoothLorentzFlow_oai := @OAI.RVM.exists_smoothLorentzFlow_oai
