-- Prove2me | solution 1 for OAI.PinchedHartogs.BaseConstruction.uniform_representing_densities
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T16:07:06.472441+00:00
-- url     : https://prove2.me/submissions/cf53637c-7d29-4b44-919f-1ad7754f2c5b

import Mathlib
import Definitions.Def_PinchedKahler
import Definitions.Def_OAIQWPH001

section
-- module Solutions.OAIQW_PinchedHartogs.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseLogTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ContDiff
open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ComplexOrder
namespace PinchedHartogs
namespace BaseConstruction

lemma bracket_analytic (p : Base) : AnalyticOnNhd ℂ (fun z => bracket z p) univ :=
  fun z _ => (innerSL ℂ p).analyticAt z

end BaseConstruction
end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseMeans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler8561_1

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open Set Filter Topology MeasureTheory
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal
namespace PinchedHartogs.BaseConstruction

lemma base_eq_sum_single (z : Base) : z = ∑ i : Fin 2, z i • EuclideanSpace.single i 1 := by
  ext j
  fin_cases j <;> simp

lemma continuous_integrable {E : Type uKahler8561_1} [NormedAddCommGroup E] {μ : Measure Sphere}
    [IsFiniteMeasure μ] {f : Sphere → E} (hf : Continuous f) : Integrable f μ := by
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseSphere
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler8786_1

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma sphereAction_preserves (U : Base ≃ₗᵢ[ℂ] Base) :
    MeasurePreserving (sphereAction U) sigma sigma := by
  have hm : MeasurePreserving (sphereAction U)
      (volume : Measure Base).toSphere (volume : Measure Base).toSphere := by
    refine ⟨(sphereAction U).measurable, ?_⟩
    apply Measure.ext
    intro s hs
    rw [Measure.map_apply (sphereAction U).measurable hs,
      (volume : Measure Base).toSphere_apply' ((sphereAction U).measurable hs),
      (volume : Measure Base).toSphere_apply' hs]
    congr 1
    have he : Ioo (0:ℝ) 1 • ((↑) '' (sphereAction U ⁻¹' s)) =
        U ⁻¹' (Ioo (0:ℝ) 1 • ((↑) '' s)) := by
      ext z
      simp only [mem_preimage, Set.mem_smul, mem_image]
      constructor
      · rintro ⟨r,hr,v,⟨ξ,hξ,rfl⟩,rfl⟩
        exact ⟨r,hr,U (ξ:Base),⟨sphereAction U ξ,hξ,rfl⟩,(realIsometry U).map_smul r ξ |>.symm⟩
      · rintro ⟨r,hr,v,⟨ξ,hξ,rfl⟩,hz⟩
        refine ⟨r,hr,U.symm (ξ:Base),⟨(sphereAction U).symm ξ, ?_, rfl⟩,?_⟩
        · simpa using hξ
        · apply U.injective
          rw [← hz]
          calc
            U (r • U.symm (ξ:Base)) = r • U (U.symm (ξ:Base)) := (realIsometry U).map_smul _ _
            _ = _ := by rw [U.apply_symm_apply]
    rw [he]
    exact (realIsometry U).measurePreserving.measure_preimage_emb
      U.toHomeomorph.measurableEmbedding _
  exact hm.smul_measure _

lemma sigma_integral_unitary {E : Type uKahler8786_1} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Base ≃ₗᵢ[ℂ] Base) (f : Sphere → E) :
    (∫ ξ, f (sphereAction U ξ) ∂sigma) = ∫ ξ, f ξ ∂sigma :=
  (sphereAction_preserves U).integral_comp (sphereAction U).measurableEmbedding f

lemma exists_unit_pow_neg_one {n : ℕ} (hn : n ≠ 0) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ c^n = -1 := by
  refine ⟨Complex.exp (Real.pi/n*Complex.I), ?_, ?_⟩
  · simp [Complex.norm_exp]
  · rw [← Complex.exp_nat_mul]
    have h : (n:ℂ)*(Real.pi/n*Complex.I) = Real.pi*Complex.I := by
      have hn' : (n:ℂ) ≠ 0 := by exact_mod_cast hn
      field_simp
    rw [h,Complex.exp_pi_mul_I]

lemma monomial_sigma_mean (d : Fin 2 →₀ ℕ) (a : ℂ) :
    (∫ ξ : Sphere, MvPolynomial.eval (fun i => (ξ:Base) i) (MvPolynomial.monomial d a) ∂sigma) =
      MvPolynomial.eval (fun _ => (0:ℂ)) (MvPolynomial.monomial d a) := by
  classical
  by_cases hd : d = 0
  · subst d
    simp
  have hn : d 0 + d 1 ≠ 0 := by
    intro hn
    have h0 : d 0 = 0 := (Nat.add_eq_zero_iff.mp hn).1
    have h1 : d 1 = 0 := (Nat.add_eq_zero_iff.mp hn).2
    apply hd
    ext i
    fin_cases i <;> assumption
  obtain ⟨c,hc,hcn⟩ := exists_unit_pow_neg_one hn
  have hh := sigma_integral_unitary (phaseIsometry c hc)
    (fun ξ => MvPolynomial.eval (fun i => (ξ:Base) i) (MvPolynomial.monomial d a))
  simp only [MvPolynomial.eval_monomial,Finsupp.prod_pow,Fin.prod_univ_two,
    sphereAction_coe,phaseIsometry_apply,PiLp.smul_apply,smul_eq_mul] at hh ⊢
  have he : ∀ ξ : Sphere, a*((c*(ξ:Base) 0)^(d 0)*(c*(ξ:Base) 1)^(d 1)) =
      -(a*((ξ:Base) 0^(d 0)*(ξ:Base) 1^(d 1))) := by
    intro ξ
    simp only [mul_pow]
    calc
      _ = c^(d 0+d 1)*(a*((ξ:Base) 0^(d 0)*(ξ:Base) 1^(d 1))) := by rw [pow_add]; ring
      _ = _ := by rw [hcn]; ring
  simp_rw [he] at hh
  rw [integral_neg] at hh
  have hz : (0:ℂ)^d 0*(0:ℂ)^d 1 = 0 := by
    rw [← pow_add,zero_pow hn]
  rw [hz,mul_zero]
  linear_combination -hh / 2

lemma sigma_represents : Represents sigma := by
  classical
  intro p
  induction p using MvPolynomial.induction_on' with
  | monomial d a => exact monomial_sigma_mean d a
  | add p q hp hq =>
    simp only [map_add]
    rw [integral_add, hp,hq]
    · exact continuous_integrable (p.continuous_eval.comp
        (continuous_pi (fun i => (EuclideanSpace.proj i).continuous.comp continuous_subtype_val)))
    · exact continuous_integrable (q.continuous_eval.comp
        (continuous_pi (fun i => (EuclideanSpace.proj i).continuous.comp continuous_subtype_val)))

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseRadialMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma radialRI (ξ : Sphere) : radialR ξ^2+radialJ ξ^2 = radialU ξ*radialV ξ := by
  simp [radialR,radialJ,radialU,radialV,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,
    Complex.conj_re,Complex.conj_im]
  ring

lemma radialJ_continuous : Continuous radialJ := by
  exact Complex.continuous_im.comp (((EuclideanSpace.proj 0).continuous.comp continuous_subtype_val).mul
    (((EuclideanSpace.proj 1).continuous.comp continuous_subtype_val).star))

lemma radial_phase_square (n : ℕ) :
    (∫ ξ, radialU ξ^n * radialR ξ^2 ∂sigma) =
      ∫ ξ, radialU ξ^n * radialJ ξ^2 ∂sigma := by
  have hi := sigma_integral_unitary (diagIsometry Complex.I 1 (by simp) (by simp))
    (fun ξ => radialU ξ^n * radialR ξ^2)
  have he : ∀ ξ : Sphere,
      radialU (sphereAction (diagIsometry Complex.I 1 (by simp) (by simp)) ξ)^n *
      radialR (sphereAction (diagIsometry Complex.I 1 (by simp) (by simp)) ξ)^2 =
      radialU ξ^n*radialJ ξ^2 := by
    intro ξ
    simp [radialU,radialR,radialJ,Complex.normSq_mul,mul_assoc]
    left
    ring
  simpa only [he] using hi.symm

lemma radial_square_integral (n : ℕ) :
    2*(∫ ξ, radialU ξ^n*radialR ξ^2 ∂sigma) =
      ∫ ξ, radialU ξ^(n+1)*radialV ξ ∂sigma := by
  have hR : Integrable (fun ξ => radialU ξ^n*radialR ξ^2) sigma :=
    continuous_integrable ((radialU_continuous.pow n).mul (radialR_continuous.pow 2))
  have hJ : Integrable (fun ξ => radialU ξ^n*radialJ ξ^2) sigma :=
    continuous_integrable ((radialU_continuous.pow n).mul (radialJ_continuous.pow 2))
  calc
    _ = (∫ ξ, radialU ξ^n*radialR ξ^2 ∂sigma) +
        (∫ ξ, radialU ξ^n*radialJ ξ^2 ∂sigma) := by rw [← radial_phase_square n]; ring
    _ = ∫ ξ, radialU ξ^n*radialR ξ^2 + radialU ξ^n*radialJ ξ^2 ∂sigma :=
      (integral_add hR hJ).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      rw [← mul_add,radialRI,pow_succ]
      ring

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseRadialMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma hasDerivAt_sphere_integral {F F' : ℝ → Sphere → ℝ}
    (hF : Continuous (fun p : ℝ × Sphere => F p.1 p.2))
    (hF' : Continuous (fun p : ℝ × Sphere => F' p.1 p.2))
    (hd : ∀ t ξ, HasDerivAt (fun r => F r ξ) (F' t ξ) t) (t : ℝ) :
    HasDerivAt (fun r => ∫ ξ, F r ξ ∂sigma) (∫ ξ, F' t ξ ∂sigma) t := by
  obtain ⟨C,hC⟩ := ((isCompact_closedBall t 1).prod (isCompact_univ : IsCompact (univ : Set Sphere))).bddAbove_image hF'.norm.continuousOn
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := sigma)
    (F := F) (F' := F') (bound := fun _ => C) (s := Metric.ball t 1)
    (Metric.ball_mem_nhds t (by norm_num)) ?_ ?_ ?_ ?_ (integrable_const C) ?_).2
  · exact Eventually.of_forall (fun r => (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  · exact continuous_integrable (hF.comp (continuous_const.prodMk continuous_id))
  · exact (hF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [] with ξ r hr
    exact hC (mem_image_of_mem (fun p : ℝ × Sphere => ‖F' p.1 p.2‖)
      (show (r,ξ) ∈ Metric.closedBall t 1 ×ˢ (univ : Set Sphere) from ⟨Metric.ball_subset_closedBall hr,mem_univ _⟩))
  · exact Eventually.of_forall (fun ξ r _ => hd r ξ)

private lemma rotA_deriv (u v r t : ℝ) : HasDerivAt (rotA u v r) (rotA' u v r t) t := by
  convert (((Real.hasDerivAt_cos t).pow 2 |>.mul_const u).add
    ((Real.hasDerivAt_sin t).pow 2 |>.mul_const v)).add
    ((((Real.hasDerivAt_cos t).const_mul 2).mul (Real.hasDerivAt_sin t)).mul_const r) using 1 <;> try rfl
  all_goals
    (try dsimp [rotA,rotA']); ring

private lemma rotA'_deriv (u v r t : ℝ) : HasDerivAt (rotA' u v r) (rotA'' u v r t) t := by
  convert (((((Real.hasDerivAt_cos t).const_mul 2).mul (Real.hasDerivAt_sin t)).mul_const (v-u)).add
    (((((Real.hasDerivAt_cos t).pow 2).sub ((Real.hasDerivAt_sin t).pow 2)).const_mul 2).mul_const r)) using 1 <;> try rfl
  all_goals
    (try dsimp [rotA',rotA'']); ring

private lemma rotated_radialU (t : ℝ) (ξ : Sphere) :
    radialU (sphereAction (rotationIsometry t) ξ) = rotA (radialU ξ) (radialV ξ) (radialR ξ) t := by
  simp only [radialU,radialV,radialR,rotationIsometry,rotA,sphereAction_coe,suIsometry_zero,Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.star_def,Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im]
  ring

private lemma rotF_deriv (n : ℕ) (t : ℝ) (ξ : Sphere) :
    HasDerivAt (fun s => rotF n s ξ) (rotF' n t ξ) t := by
  convert (rotA_deriv (radialU ξ) (radialV ξ) (radialR ξ) t).pow (n+2) using 1 <;> try rfl
  all_goals
    (try simp only [rotF',Nat.cast_add,Nat.cast_ofNat]); try rfl

private lemma rotF'_deriv (n : ℕ) (t : ℝ) (ξ : Sphere) :
    HasDerivAt (fun s => rotF' n s ξ) (rotF'' n t ξ) t := by
  convert ((((rotA_deriv (radialU ξ) (radialV ξ) (radialR ξ) t).pow (n+1)).const_mul (n+2:ℝ)).mul
    (rotA'_deriv (radialU ξ) (radialV ξ) (radialR ξ) t)) using 1 <;> try rfl
  all_goals
    (try simp only [rotF'',Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel,Pi.pow_apply]); ring

attribute [local fun_prop] radialU_continuous radialV_continuous radialR_continuous

private lemma rotF_continuous (n : ℕ) : Continuous (fun p : ℝ × Sphere => rotF n p.1 p.2) := by
  unfold rotF rotA
  fun_prop
private lemma rotF'_continuous (n : ℕ) : Continuous (fun p : ℝ × Sphere => rotF' n p.1 p.2) := by
  unfold rotF' rotA rotA'
  fun_prop
private lemma rotF''_continuous (n : ℕ) : Continuous (fun p : ℝ × Sphere => rotF'' n p.1 p.2) := by
  unfold rotF'' rotA rotA' rotA''
  fun_prop

lemma radial_moment_recurrence (n : ℕ) :
    (n+3 : ℝ)*(∫ ξ, radialU ξ^(n+2) ∂sigma) =
      (n+2 : ℝ)*(∫ ξ, radialU ξ^(n+1) ∂sigma) := by
  have hconst : ∀ t, (∫ ξ, rotF n t ξ ∂sigma) = ∫ ξ, radialU ξ^(n+2) ∂sigma := by
    intro t
    simpa only [rotated_radialU,rotF] using sigma_integral_unitary (rotationIsometry t)
      (fun ξ => radialU ξ^(n+2))
  have hzero : ∀ t, (∫ ξ, rotF' n t ξ ∂sigma) = 0 := by
    intro t
    have hc : HasDerivAt (fun s => ∫ ξ, rotF n s ξ ∂sigma) 0 t := by
      simpa only [hconst] using hasDerivAt_const t (∫ ξ, radialU ξ^(n+2) ∂sigma)
    exact (hasDerivAt_sphere_integral (rotF_continuous n) (rotF'_continuous n) (rotF_deriv n) t).unique hc
  have hsecond : (∫ ξ, rotF'' n 0 ξ ∂sigma) = 0 := by
    have hc : HasDerivAt (fun s => ∫ ξ, rotF' n s ξ ∂sigma) 0 0 := by
      simpa only [hzero] using hasDerivAt_const (0:ℝ) (0:ℝ)
    exact (hasDerivAt_sphere_integral (rotF'_continuous n) (rotF''_continuous n) (rotF'_deriv n) 0).unique hc
  have he : ∀ ξ : Sphere, rotF'' n 0 ξ = (n+2:ℝ)*
      (4*(n+1:ℝ)*(radialU ξ^n*radialR ξ^2)+
        2*(radialU ξ^(n+1)*radialV ξ)-2*radialU ξ^(n+2)) := by
    intro ξ
    simp only [rotF'',rotA,rotA',rotA'',Real.cos_zero,Real.sin_zero,zero_mul,mul_zero,one_pow,one_mul,add_zero,sub_zero,pow_succ]
    ring
  simp_rw [he] at hsecond
  have hR : Integrable (fun ξ => radialU ξ^n*radialR ξ^2) sigma :=
    continuous_integrable ((radialU_continuous.pow n).mul (radialR_continuous.pow 2))
  have hUV : Integrable (fun ξ => radialU ξ^(n+1)*radialV ξ) sigma :=
    continuous_integrable ((radialU_continuous.pow (n+1)).mul radialV_continuous)
  have hU : Integrable (fun ξ => radialU ξ^(n+2)) sigma := continuous_integrable (radialU_continuous.pow (n+2))
  have hparts := integral_sub (μ := sigma)
    (f := fun ξ => 4*(n+1:ℝ)*(radialU ξ^n*radialR ξ^2)+2*(radialU ξ^(n+1)*radialV ξ))
    (g := fun ξ => 2*radialU ξ^(n+2))
    ((hR.const_mul (4*(n+1:ℝ))).add (hUV.const_mul 2)) (hU.const_mul 2)
  have hparts' := integral_add (μ := sigma)
    (f := fun ξ => 4*(n+1:ℝ)*(radialU ξ^n*radialR ξ^2))
    (g := fun ξ => 2*(radialU ξ^(n+1)*radialV ξ))
    (hR.const_mul (4*(n+1:ℝ))) (hUV.const_mul 2)
  rw [integral_const_mul,hparts,hparts',integral_const_mul,integral_const_mul,integral_const_mul] at hsecond
  have huv : (∫ ξ, radialU ξ^(n+1)*radialV ξ ∂sigma) =
      (∫ ξ, radialU ξ^(n+1) ∂sigma)-(∫ ξ, radialU ξ^(n+2) ∂sigma) := by
    rw [← integral_sub (f := fun ξ => radialU ξ^(n+1)) (g := fun ξ => radialU ξ^(n+2))
      (continuous_integrable (radialU_continuous.pow (n+1))) hU]
    apply integral_congr_ae
    filter_upwards [] with ξ
    have hv : radialV ξ = 1-radialU ξ := by linarith [radialUV ξ]
    rw [hv,show n+2 = (n+1)+1 from rfl,pow_succ]
    ring
  have hs := radial_square_integral n
  rw [huv] at hs hsecond
  have hn : (0:ℝ) < n+2 := by positivity
  have hh := (mul_eq_zero.mp hsecond).resolve_left hn.ne'
  linear_combination (n+1:ℝ)*hs-hh/2

lemma radial_first_moment : (∫ ξ, radialU ξ ∂sigma) = 1/2 := by
  have hi := sigma_integral_unitary (suIsometry 0 1 (by simp)) radialU
  have he : ∀ ξ : Sphere, radialU (sphereAction (suIsometry 0 1 (by simp)) ξ) = radialV ξ := by
    intro ξ
    simp [radialU,radialV]
  simp_rw [he] at hi
  have huv : (∫ ξ, radialU ξ ∂sigma)+(∫ ξ, radialV ξ ∂sigma) = 1 := by
    rw [← integral_add (continuous_integrable radialU_continuous) (continuous_integrable radialV_continuous)]
    simp_rw [radialUV]
    simp
  linarith

lemma radial_moment (n : ℕ) : (∫ ξ, radialU ξ^n ∂sigma) = 1/(n+1:ℝ) := by
  rcases n with _|n
  · simp
  induction n with
  | zero => simpa only [Nat.zero_add,Nat.cast_one,pow_one,show (1:ℝ)+1 = 2 by norm_num] using radial_first_moment
  | succ n ih =>
    have hr := radial_moment_recurrence n
    rw [ih] at hr
    have hn : (n+2:ℝ) ≠ 0 := by positivity
    have hn' : (n+3:ℝ) ≠ 0 := by positivity
    simp only [Nat.cast_add,Nat.cast_one] at *
    field_simp at hr ⊢
    nlinarith

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseRadialLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler9159_1 uKahler9161_1

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma radialUnit_continuous : Continuous radialUnit := radialU_continuous.subtype_mk _

lemma unit_moment (n : ℕ) : (∫ t : unitInterval, (t:ℝ)^n) = 1/(n+1:ℝ) := by
  rw [unitInterval.volume_def,integral_subtype_comap measurableSet_Icc (fun t : ℝ => t^n)]
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),integral_pow]
  simp

lemma radial_polynomial_integral (p : Polynomial ℝ) :
    (∫ ξ, p.eval (radialU ξ) ∂sigma) = ∫ t : unitInterval, p.eval (t:ℝ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add]
    rw [integral_add,integral_add,hp,hq]
    all_goals first
      | exact continuous_integrable (p.continuous.comp radialU_continuous)
      | exact continuous_integrable (q.continuous.comp radialU_continuous)
      | exact (p.continuous.comp continuous_subtype_val).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      | exact (q.continuous.comp continuous_subtype_val).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  | monomial n a =>
    simp only [Polynomial.eval_monomial,integral_const_mul,radial_moment,unit_moment]

lemma radial_continuous_integral (f : C(unitInterval,ℝ)) :
    (∫ ξ, f (radialUnit ξ) ∂sigma) = ∫ t : unitInterval, f t := by
  let L := integralCM sigma radialUnit radialUnit_continuous
  let R := integralCM (volume : Measure unitInterval) id continuous_id
  have hc : IsClosed {f : C(unitInterval,ℝ) | L f = R f} := isClosed_eq L.continuous R.continuous
  have hpoly : (polynomialFunctions (Icc (0:ℝ) 1) : Set C(unitInterval,ℝ)) ⊆ {f | L f = R f} := by
    rw [polynomialFunctions_coe]
    rintro _ ⟨p,rfl⟩
    exact radial_polynomial_integral p
  have hcl := hc.closure_subset_iff.mpr hpoly
  have hd : closure (polynomialFunctions (Icc (0:ℝ) 1) : Set C(unitInterval,ℝ)) = univ := by
    simpa only [Subalgebra.topologicalClosure_coe,show ((⊤ : Subalgebra ℝ C(unitInterval,ℝ)) : Set C(unitInterval,ℝ)) = univ from rfl] using
      congrArg (fun A : Subalgebra ℝ C(unitInterval,ℝ) => (A : Set C(unitInterval,ℝ)))
        (polynomialFunctions.topologicalClosure (Icc (0:ℝ) 1))
  exact hcl (by rw [hd]; trivial)

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma bracket_coordinates (z p : Base) : bracket z p = z 0*star (p 0)+z 1*star (p 1) := by
  simp [bracket,Fin.sum_univ_two,inner]

lemma bracket_radial_identity (ξ p : Sphere) :
    ‖bracket (ξ:Base) (p:Base)‖^2 = radialU ξ*radialU p+radialV ξ*radialV p+
      2*(radialR ξ*radialR p+radialJ ξ*radialJ p) := by
  rw [← Complex.normSq_eq_norm_sq,bracket_coordinates]
  simp only [radialU,radialV,radialR,radialJ,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

lemma bloch_dist_sq (ξ p : Sphere) :
    dist (bloch ξ) (bloch p)^2 = 1-‖bracket (ξ:Base) (p:Base)‖^2 := by
  rw [dist_eq_norm,EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_three,PiLp.sub_apply]
  change |radialU ξ-radialU p|^2+|radialR ξ-radialR p|^2+|radialJ ξ-radialJ p|^2 = _
  simp only [sq_abs]
  rw [bracket_radial_identity]
  have hvξ : radialV ξ = 1-radialU ξ := by linarith [radialUV ξ]
  have hvp : radialV p = 1-radialU p := by linarith [radialUV p]
  have hξ := radialRI ξ
  have hp := radialRI p
  rw [hvξ] at hξ ⊢
  rw [hvp] at hp ⊢
  linarith

lemma projectiveDistance_eq_dist (ξ p : Sphere) : projectiveDistance ξ p = dist (bloch ξ) (bloch p) := by
  rw [projectiveDistance,← bloch_dist_sq,Real.sqrt_sq (dist_nonneg)]

lemma projectiveDistance_triangle (ξ p q : Sphere) :
    projectiveDistance ξ q ≤ projectiveDistance ξ p+projectiveDistance p q := by
  simp only [projectiveDistance_eq_dist]
  exact dist_triangle _ _ _

lemma projectiveDistance_nonneg (ξ p : Sphere) : 0 ≤ projectiveDistance ξ p := Real.sqrt_nonneg _
lemma projectiveDistance_symm (ξ p : Sphere) : projectiveDistance ξ p = projectiveDistance p ξ := by
  simp only [projectiveDistance_eq_dist,dist_comm]

lemma bracket_norm_le_one (ξ p : Sphere) : ‖bracket (ξ:Base) (p:Base)‖ ≤ 1 := by
  simpa only [bracket,sphere_norm,one_mul] using norm_inner_le_norm (p:Base) (ξ:Base)

lemma projectiveDistance_sq (ξ p : Sphere) : projectiveDistance ξ p^2 = 1-‖bracket (ξ:Base) (p:Base)‖^2 := by
  rw [projectiveDistance_eq_dist,bloch_dist_sq]

lemma adaptedIsometry_zero (p : Sphere) (z : Base) : adaptedIsometry p z 0 = bracket z (p:Base) := by
  simp only [adaptedIsometry,suIsometry_zero,bracket_coordinates]
  ring

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseHopf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler10884_1 uKahler10884_2 uKahler10889_1 uKahler10889_2 uKahler10889_3

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma torusAction_continuous : Continuous (fun p : (Circle × Circle) × Sphere => torusAction p.1 p.2) := by
  apply Continuous.subtype_mk
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℂ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun p : (Circle × Circle) × Sphere => (torusAction p.1 p.2 : Base) 0)
    simp_rw [torusAction_zero]
    fun_prop
  · change Continuous (fun p : (Circle × Circle) × Sphere => (torusAction p.1 p.2 : Base) 1)
    simp_rw [torusAction_one]
    fun_prop

lemma torusAction_mul (z w : Circle × Circle) (ξ : Sphere) :
    torusAction z (torusAction w ξ) = torusAction (z*w) ξ := by
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [mul_assoc]

attribute [local semireducible] radialSphere in
lemma radialSphere_continuous : Continuous radialSphere := by
  apply Continuous.subtype_mk
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℂ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp only [] <;> fun_prop

lemma hopf_continuous : Continuous hopf :=
by
  unfold hopf
  exact torusAction_continuous.comp (continuous_snd.prodMk (radialSphere_continuous.comp continuous_fst))

lemma exists_circle_norm_factor (z : ℂ) : ∃ a : Circle, (a:ℂ)*(‖z‖:ℂ) = z := by
  by_cases hz : z = 0
  · subst z; exact ⟨1,by simp⟩
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  refine ⟨⟨z/(‖z‖:ℂ),?_⟩,?_⟩
  · apply mem_sphere_zero_iff_norm.mpr
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),div_self hn]
  · exact div_mul_cancel₀ z (by exact_mod_cast hn)

lemma exists_hopf (ξ : Sphere) : ∃ z : Circle × Circle, torusAction z (radialSphere (radialUnit ξ)) = ξ := by
  obtain ⟨a,ha⟩ := exists_circle_norm_factor ((ξ:Base) 0)
  obtain ⟨b,hb⟩ := exists_circle_norm_factor ((ξ:Base) 1)
  refine ⟨(a,b),?_⟩
  apply Subtype.ext
  ext i
  fin_cases i
  · simpa [radialUnit,radialU,Complex.normSq_eq_norm_sq,Real.sqrt_sq (norm_nonneg _)] using ha
  · have hv : 1-radialU ξ = radialV ξ := by linarith [radialUV ξ]
    change (torusAction (a,b) (radialSphere (radialUnit ξ)) : Base) 1 = (ξ:Base) 1
    rw [torusAction_one,radialSphere_one]
    change (b:ℂ)*(Real.sqrt (1-radialU ξ):ℂ) = (ξ:Base) 1
    rw [hv,radialV,Complex.normSq_eq_norm_sq,Real.sqrt_sq (norm_nonneg _)]
    exact hb

lemma compact_continuous_integrable {X : Type uKahler10884_1} {E : Type uKahler10884_2} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} [IsFiniteMeasure μ] {f : X → E} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma continuous_compact_integral {X : Type uKahler10889_1} {Y : Type uKahler10889_2} {E : Type uKahler10889_3} [TopologicalSpace X] [CompactSpace X] [FirstCountableTopology X]
    [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopology E] {μ : Measure Y} [IsFiniteMeasure μ]
    {F : X × Y → E} (hF : Continuous F) : Continuous (fun x => ∫ y, F (x,y) ∂μ) := by
  obtain ⟨C,hC⟩ := isCompact_univ.bddAbove_image hF.norm.continuousOn
  apply continuous_of_dominated
    (fun x => (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (fun x => Eventually.of_forall (fun y => hC (mem_image_of_mem _ (mem_univ _))))
    (integrable_const C)
  exact Eventually.of_forall (fun y => hF.comp (continuous_id.prodMk continuous_const))

lemma hopf_integral (f : C(Sphere,ℝ)) :
    (∫ ξ, f ξ ∂sigma) = ∫ u : unitInterval, ∫ z, f (hopf (u,z)) ∂torusMeasure := by
  let A (ξ : Sphere) := ∫ z, f (torusAction z ξ) ∂torusMeasure
  have hc : Continuous A := continuous_compact_integral
    (f.continuous.comp (torusAction_continuous.comp continuous_swap))
  have havg : (∫ ξ, A ξ ∂sigma) = ∫ ξ, f ξ ∂sigma := by
    rw [show (∫ ξ, A ξ ∂sigma) = ∫ z, ∫ ξ, f (torusAction z ξ) ∂sigma ∂torusMeasure from
      integral_integral_swap (compact_continuous_integrable (f.continuous.comp (torusAction_continuous.comp continuous_swap)))]
    simp only [torusAction,sigma_integral_unitary]
    simp
  have hA : ∀ ξ, A ξ = A (radialSphere (radialUnit ξ)) := by
    intro ξ
    obtain ⟨w,hw⟩ := exists_hopf ξ
    conv_lhs => rw [← hw]
    simp only [A,torusAction_mul]
    exact integral_mul_right_eq_self (fun z => f (torusAction z (radialSphere (radialUnit ξ)))) w
  rw [← havg]
  calc
    _ = ∫ ξ, A (radialSphere (radialUnit ξ)) ∂sigma := integral_congr_ae (Eventually.of_forall hA)
    _ = _ := radial_continuous_integral ⟨A ∘ radialSphere,hc.comp radialSphere_continuous⟩

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BasePhaseFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma phaseChar_add (n m : ℤ) (z : Circle) : phaseChar (n+m) z=phaseChar n z*phaseChar m z := by
  simp [phaseChar,zpow_add]
lemma phaseChar_exp (n : ℤ) (t : ℝ) : phaseChar n (Circle.exp t)=Complex.exp ((n:ℂ)*t*Complex.I) := by
  simp only [phaseChar,Circle.coe_zpow,Circle.coe_exp,← Complex.exp_int_mul]
  congr 1
  ring
lemma phaseChar_continuous (n : ℤ) : Continuous (phaseChar n) := by
  exact continuous_subtype_val.comp (continuous_id.zpow n)

lemma circle_char_mean (n : ℤ) : (∫ z, phaseChar n z ∂circleMeasure) = if n=0 then 1 else 0 := by
  by_cases hn : n=0
  · subst n; simp
  rw [ite_eq_right hn]
  let w := Circle.exp (Real.pi/(n:ℝ))
  have hw : phaseChar n w = -1 := by
    rw [phaseChar_exp]
    have hn0 : (n:ℂ) ≠ 0 := by exact_mod_cast hn
    have hh : (n:ℂ)*(Real.pi/(n:ℝ):ℝ)*Complex.I = Real.pi*Complex.I := by push_cast; field_simp
    rw [hh,Complex.exp_pi_mul_I]
  apply integral_eq_zero_of_mul_left_eq_neg (g := w)
  intro z
  rw [phaseChar_mul,hw,neg_one_mul]

lemma phaseSum_continuous (s : Finset ℤ) (a : ℤ → ℂ) : Continuous (phaseSum s a) :=
  continuous_finsetSum _ (fun n _ => continuous_const.mul (phaseChar_continuous n))

lemma phaseSum_mean (s : Finset ℤ) (a : ℤ → ℂ) :
    (∫ z, phaseSum s a z ∂circleMeasure) = if 0 ∈ s then a 0 else 0 := by
  classical
  unfold phaseSum
  rw [MeasureTheory.integral_finsetSum s (fun n _ => (compact_continuous_integrable (phaseChar_continuous n)).const_mul (a n))]
  simp_rw [integral_const_mul,circle_char_mean]
  simp

lemma phaseBandwidth_one : PhaseBandwidth (fun _ => 1) 0 := by
  intro p
  refine ⟨{0},fun _ => 1,?_,?_⟩
  · intro n hn; have hn0 : n=0 := Finset.mem_singleton.mp hn; simp [hn0]
  · intro z; simp [phaseSum]

lemma orbitMean_one : OrbitMeanOne (fun _ => 1) := by intro p; simp

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BasePhaseSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler11043_1

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma mem_phaseBand (ℓ : ℕ) (n : ℤ) : n ∈ phaseBand ℓ ↔ |n| ≤ (ℓ:ℤ) := by simp [phaseBand,abs_le]

lemma phaseSum_extend {s t : Finset ℤ} (hst : s ⊆ t) (a : ℤ → ℂ) (z : Circle) :
    phaseSum s a z = phaseSum t (fun n => if n ∈ s then a n else 0) z := by
  classical
  unfold phaseSum
  calc
    _ = ∑ n ∈ s, (if n ∈ s then a n else 0)*phaseChar n z := by
      apply Finset.sum_congr rfl; intro n hn; simp [hn]
    _ = _ := Finset.sum_subset hst (fun n _ hn => by simp [hn])

lemma phaseBandwidth_band {W : Base → ℝ} {ℓ : ℕ} (hW : PhaseBandwidth W ℓ) (p : Sphere) :
    ∃ a : ℤ → ℂ, ∀ z : Circle, (W ((z:ℂ) • (p:Base)):ℂ) = phaseSum (phaseBand ℓ) a z := by
  classical
  obtain ⟨s,a,hs,he⟩ := hW p
  refine ⟨fun n => if n ∈ s then a n else 0,?_⟩
  intro z
  rw [he]
  exact phaseSum_extend (fun n hn => (mem_phaseBand ℓ n).mpr (hs n hn)) a z

lemma phaseBandwidth_mono {W : Base → ℝ} {ℓ m : ℕ} (hW : PhaseBandwidth W ℓ) (hℓ : ℓ ≤ m) :
    PhaseBandwidth W m := by
  intro p
  obtain ⟨s,a,hs,he⟩ := hW p
  exact ⟨s,a,fun n hn => le_trans (hs n hn) (by exact_mod_cast hℓ),he⟩

lemma phaseBandwidth_add {W V : Base → ℝ} {ℓ : ℕ} (hW : PhaseBandwidth W ℓ) (hV : PhaseBandwidth V ℓ) :
    PhaseBandwidth (fun z => W z+V z) ℓ := by
  intro p
  obtain ⟨a,ha⟩ := phaseBandwidth_band hW p
  obtain ⟨b,hb⟩ := phaseBandwidth_band hV p
  refine ⟨phaseBand ℓ,fun n => a n+b n,fun n hn => (mem_phaseBand ℓ n).mp hn,?_⟩
  intro z
  simp only [Complex.ofReal_add,ha,hb,phaseSum,add_mul,Finset.sum_add_distrib]

lemma phaseBandwidth_zero (ℓ : ℕ) : PhaseBandwidth (fun _ => 0) ℓ := by
  intro p
  exact ⟨∅,fun _ => 0,by simp,by simp [phaseSum]⟩

lemma phaseBandwidth_sum {ι : Type uKahler11043_1} (s : Finset ι) (W : ι → Base → ℝ) {ℓ : ℕ}
    (hW : ∀ i ∈ s, PhaseBandwidth (W i) ℓ) : PhaseBandwidth (fun z => ∑ i ∈ s, W i z) ℓ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using phaseBandwidth_zero ℓ
  | @insert a s ha ih =>
    simpa [Finset.sum_insert ha] using phaseBandwidth_add (hW a (by simp))
      (ih (fun i hi => hW i (by simp [hi])))

lemma phaseChar_conj (n : ℤ) (z : Circle) : star (phaseChar n z)=phaseChar (-n) z := by
  unfold phaseChar
  rw [zpow_neg,Circle.coe_inv_eq_conj]
  rfl

lemma phaseSum_shift (s : Finset ℤ) (a : ℤ → ℂ) (k : ℤ) (z : Circle) :
    (∑ n ∈ s, a n*phaseChar (k+n) z) =
      phaseSum (s.image (fun n => k+n)) (fun m => a (m-k)) z := by
  classical
  unfold phaseSum
  rw [Finset.sum_image (s := s) (g := fun n : ℤ => k+n) (fun n _ m _ he => add_left_cancel he)]
  apply Finset.sum_congr rfl
  intro n hn
  congr 2
  omega

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BasePhaseReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma phaseSum_conj (s : Finset ℤ) (a : ℤ → ℂ) (z : Circle) :
    star (phaseSum s a z) = phaseSum (s.image Neg.neg) (fun n => star (a (-n))) z := by
  classical
  unfold phaseSum
  rw [star_sum]
  simp only [star_mul,phaseChar_conj]
  rw [Finset.sum_image (s := s) (g := Neg.neg) (fun n _ m _ he => neg_injective he)]
  simp [mul_comm]

lemma phaseSum_real_band {s : Finset ℤ} {ℓ : ℕ} (hs : ∀ n ∈ s, |n| ≤ (ℓ:ℤ))
    (a : ℤ → ℂ) : ∃ b : ℤ → ℂ, ∀ z : Circle,
      ((phaseSum s a z).re:ℂ) = phaseSum (phaseBand ℓ) b z := by
  classical
  let t := s.image Neg.neg
  let a' : ℤ → ℂ := fun n => if n ∈ s then a n else 0
  let b' : ℤ → ℂ := fun n => if n ∈ t then star (a (-n)) else 0
  have hs' : s ⊆ phaseBand ℓ := fun n hn => (mem_phaseBand ℓ n).mpr (hs n hn)
  have ht' : t ⊆ phaseBand ℓ := by
    intro n hn
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hn
    exact (mem_phaseBand ℓ (-m)).mpr (by simpa using hs m hm)
  refine ⟨fun n => (a' n + b' n)/2,?_⟩
  intro z
  have hr : ((phaseSum s a z).re:ℂ) = (phaseSum s a z+star (phaseSum s a z))/2 := by
    apply Complex.ext <;> simp
  rw [hr,phaseSum_conj,phaseSum_extend hs' a z,phaseSum_extend ht' (fun n => star (a (-n))) z]
  simp only [phaseSum,← Finset.sum_add_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  dsimp [a',b',t]
  ring

lemma phaseSum_integral {s : Finset ℤ} (a : ℤ → ℂ) (hs : 0 ∉ s) :
    (∫ z : Circle, phaseSum s a z ∂circleMeasure) = 0 := by
  rw [phaseSum_mean,ite_eq_right hs]

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BasePhaseMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma real_cast_eq_conj (z : ℂ) : (z.re:ℂ)=(z+star z)/2 := by
  apply Complex.ext <;> simp

lemma phase_real_moment (a : ℂ) (m : ℤ) (n : ℕ) (hm : 0 < m) :
    (∫ z : Circle, phaseChar n z*((a*phaseChar m z).re:ℂ) ∂circleMeasure) =
      if m=(n:ℤ) then star a/2 else 0 := by
  have he : ∀ z : Circle, phaseChar n z*((a*phaseChar m z).re:ℂ) =
      (a/2)*phaseChar ((n:ℤ)+m) z + (star a/2)*phaseChar ((n:ℤ)-m) z := by
    intro z
    rw [real_cast_eq_conj,star_mul,phaseChar_conj]
    rw [phaseChar_add,sub_eq_add_neg,phaseChar_add]
    ring
  simp_rw [he]
  rw [integral_add]
  · rw [integral_const_mul,integral_const_mul,circle_char_mean,circle_char_mean]
    have hplus : (n:ℤ)+m ≠ 0 := by omega
    rw [ite_eq_right hplus,mul_zero,zero_add]
    by_cases heq : m=(n:ℤ)
    · simp [heq]
    · have hminus : (n:ℤ)-m ≠ 0 := by omega
      simp [hminus,heq]
  · exact (compact_continuous_integrable (phaseChar_continuous _)).const_mul _
  · exact (compact_continuous_integrable (phaseChar_continuous _)).const_mul _

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseDensityDefinitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma phaseDerivative_smooth {W : Base → ℝ} (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (phaseDerivative W) := by
  exact (hW.fderiv_right (by simp)).clm_apply ((Complex.I • (1 : Base →L[ℂ] Base)).restrictScalars ℝ).contDiff

lemma centralPoint_smoothAt (p : Sphere) {z : Base} (hz : bracket z (p:Base) ≠ 0) :
    ContDiffAt ℝ ∞ (centralPoint p) z := by
  have hc : ContDiff ℝ ∞ (fun z : Base => bracket z (p:Base)) := (bracket_analytic (p:Base)).contDiff.restrict_scalars ℝ
  have hn : ContDiffAt ℝ ∞ (fun z : Base => ‖bracket z (p:Base)‖) z := hc.contDiffAt.norm ℂ hz
  simpa only [centralPoint,div_eq_mul_inv,Function.comp_def,Complex.ofRealCLM_apply] using!
    ((hc.contDiffAt.mul ((Complex.ofRealCLM.contDiff.comp_contDiffAt z hn).inv
      (by simpa only [Function.comp_def,Complex.ofRealCLM_apply,ne_eq,Complex.ofReal_eq_zero] using norm_ne_zero_iff.mpr hz))).smul (contDiffAt_const (c := (p:Base))))

lemma densityHeight_smoothAt (k : ℕ) (p : Sphere) {z : Base} (hz : bracket z (p:Base) ≠ 0) :
    ContDiffAt ℝ ∞ (densityHeight k p) z := by
  have hc : ContDiff ℝ ∞ (fun z : Base => bracket z (p:Base)) := (bracket_analytic (p:Base)).contDiff.restrict_scalars ℝ
  exact contDiffAt_const.mul ((hc.contDiffAt.norm ℂ hz).log (norm_ne_zero_iff.mpr hz))

lemma densityCorrectionRaw_smoothAt (k : ℕ) {f b : ℝ → ℝ} {W : Base → ℝ}
    (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b) (hW : ContDiff ℝ ∞ W)
    (p : Sphere) {z : Base} (hz : bracket z (p:Base) ≠ 0) :
    ContDiffAt ℝ ∞ (densityCorrectionRaw k f b W p) z := by
  have hc : ContDiff ℝ ∞ (fun z : Base => bracket z (p:Base)) := (bracket_analytic (p:Base)).contDiff.restrict_scalars ℝ
  have hn := hc.contDiffAt.norm ℂ hz
  have hn0 := norm_ne_zero_iff.mpr hz
  have hphase : ContDiffAt ℝ ∞ (fun z : Base => bracket z (p:Base)/(‖bracket z (p:Base)‖:ℂ)) z := by
    simpa only [div_eq_mul_inv,Function.comp_def,Complex.ofRealCLM_apply] using! hc.contDiffAt.mul ((Complex.ofRealCLM.contDiff.comp_contDiffAt z hn).inv
      (by exact_mod_cast hn0 : (‖bracket z (p:Base)‖:ℂ) ≠ 0))
  have hy := densityHeight_smoothAt k p hz
  have hs := centralPoint_smoothAt p hz
  have hreal := Complex.reCLM.contDiff.comp_contDiffAt z (hphase.pow k)
  have him := Complex.imCLM.contDiff.comp_contDiffAt z (hphase.pow k)
  exact ((hn.pow 2).inv (pow_ne_zero 2 hn0)).mul
    ((((hf.contDiffAt.comp z hy).mul (hW.contDiffAt.comp z hs)).mul hreal).sub
      ((((hb.contDiffAt.comp z hy).div_const (k:ℝ)).mul ((phaseDerivative_smooth hW).contDiffAt.comp z hs)).mul him))

lemma densityCorrection_zero_low {k : ℕ} (hk : 0 < k) {R E : ℝ} {f b : ℝ → ℝ}
    (htail : ∀ y, E ≤ y → f y=0 ∧ b y=0) (W : Base → ℝ) (p : Sphere) (z : Base)
    (hz : ‖bracket z (p:Base)‖ ≤ Real.exp (-E/k)) : densityCorrection k R f b W p z=0 := by
  unfold densityCorrection
  split_ifs with hc
  · have hn : 0 < ‖bracket z (p:Base)‖ := lt_trans (Real.exp_pos _) hc
    have hh := Real.log_le_log hn hz
    rw [Real.log_exp] at hh
    have hk0 : (0:ℝ) < k := by exact_mod_cast hk
    have hhy : E ≤ densityHeight k p z := by
      have hm := (le_div_iff₀ hk0).mp hh
      unfold densityHeight
      linarith
    obtain ⟨hf,hb⟩ := htail _ hhy
    simp [densityCorrectionRaw,hf,hb]
  · rfl

lemma densityCorrection_smooth {k : ℕ} (hk : 0 < k) {R E : ℝ} (hER : E < R)
    {f b : ℝ → ℝ} {W : Base → ℝ}
    (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b) (hW : ContDiff ℝ ∞ W)
    (htail : ∀ y, E ≤ y → f y=0 ∧ b y=0) (p : Sphere) :
    ContDiff ℝ ∞ (densityCorrection k R f b W p) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  have hc : Continuous (fun z : Base => ‖bracket z (p:Base)‖) := (bracket_analytic (p:Base)).continuous.norm
  by_cases hz : Real.exp (-R/k) < ‖bracket z (p:Base)‖
  · have he : densityCorrection k R f b W p =ᶠ[𝓝 z] densityCorrectionRaw k f b W p := by
      filter_upwards [(isOpen_lt continuous_const hc).mem_nhds hz] with v hv
      exact ite_eq_left hv
    exact (densityCorrectionRaw_smoothAt k hf hb hW p (norm_pos_iff.mp (lt_trans (Real.exp_pos _) hz))).congr_of_eventuallyEq he
  · have hk0 : (0:ℝ) < k := by exact_mod_cast hk
    have hcut : Real.exp (-R/k) < Real.exp (-E/k) := Real.exp_lt_exp.mpr ((div_lt_div_iff_of_pos_right hk0).mpr (neg_lt_neg hER))
    have hzE : ‖bracket z (p:Base)‖ < Real.exp (-E/k) := lt_of_le_of_lt (le_of_not_gt hz) hcut
    have he : densityCorrection k R f b W p =ᶠ[𝓝 z] (fun _ => 0) := by
      filter_upwards [(isOpen_lt hc continuous_const).mem_nhds hzE] with v hv
      exact densityCorrection_zero_low hk htail W p v hv.le
    exact contDiffAt_const.congr_of_eventuallyEq he

lemma density_smooth {Q : ℕ} (hQ : 0 < Q) {R E : ℝ} (hER : E < R)
    {f b : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b)
    (htail : ∀ y, E ≤ y → f y=0 ∧ b y=0) (P : ℕ → Finset Sphere) (j : ℕ) :
    ContDiff ℝ ∞ (density Q R f b P j) := by
  induction j with
  | zero => exact contDiff_const
  | succ j ih =>
    exact ih.add (ContDiff.sum (fun p hp => densityCorrection_smooth (pow_pos hQ _) hER hf hb ih htail p))

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseWeightedDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler11626_1 uKahler11629_1 uKahler11634_1 uKahler11642_1 uKahler11661_1 uKahler11675_1 uKahler11691_1 uKahler11701_1 uKahler11718_1 uKahler11754_1 uKahler11763_1 uKahler11780_1

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma bounded_half_plane {f : ℂ → ℂ} {C M : ℝ}
    (hd : DiffContOnCl ℂ f {z | 0 < z.re})
    (hb : ∀ z : ℂ, 0 ≤ z.re → ‖f z‖ ≤ M)
    (hboundary : ∀ x : ℝ, ‖f ((x:ℂ)*Complex.I)‖ ≤ C)
    {z : ℂ} (hz : 0 ≤ z.re) : ‖f z‖ ≤ C := by
  apply PhragmenLindelof.right_half_plane_of_bounded_on_real hd _ _ hboundary hz
  · refine ⟨0,by norm_num,0,Asymptotics.IsBigO.of_bound M ?_⟩
    apply eventually_inf_principal.mpr
    exact Eventually.of_forall (fun z hz => by simpa using hb z (le_of_lt hz))
  · apply isBoundedUnder_of_eventually_le (a := M)
    filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    exact hb x (by simpa using hx)

lemma expSum_differentiable {ι : Type uKahler11629_1} (s : Finset ι) (a : ι → ℂ) (w : ι → ℝ) :
    Differentiable ℂ (expSum s a w) := by
  unfold expSum
  fun_prop

private lemma half_plane_norm_one_add {z : ℂ} (hz : 0 ≤ z.re) : 1 ≤ ‖1+z‖ := by
  have h := Complex.re_le_norm (1+z)
  simp only [Complex.add_re,Complex.one_re] at h
  linarith

private lemma dampedSum_bound {ι : Type uKahler11642_1} (s : Finset ι) (a : ι → ℂ) (w : ι → ℝ) (N : ℕ)
    (hw : ∀ i ∈ s, -2 ≤ w i) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖dampedSum s a w N z‖ ≤ ∑ i ∈ s, ‖a i‖ := by
  unfold dampedSum
  rw [norm_div,norm_pow]
  apply (div_le_iff₀ (pow_pos (lt_of_lt_of_le zero_lt_one (half_plane_norm_one_add hz)) N)).mpr
  have he : ∀ i ∈ s, ‖Complex.exp (-((2:ℝ)+w i:ℝ)*z)‖ ≤ 1 := by
    intro i hi
    rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.mpr
    simpa only [Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.neg_im,Complex.ofReal_im,neg_zero,zero_mul,sub_zero] using
      mul_nonpos_of_nonpos_of_nonneg (show -(2+w i) ≤ 0 by linarith [hw i hi]) hz
  calc
    ‖∑ i ∈ s, a i * Complex.exp (-((2:ℝ)+w i:ℝ)*z)‖ ≤ ∑ i ∈ s, ‖a i‖*1 := by
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun i hi => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (he i hi) (norm_nonneg _))
    _ = ∑ i ∈ s, ‖a i‖ := by simp
    _ ≤ (∑ i ∈ s, ‖a i‖)*‖1+z‖^N := le_mul_of_one_le_right (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (one_le_pow₀ (half_plane_norm_one_add hz))

private lemma dampedSum_diffCont {ι : Type uKahler11661_1} (s : Finset ι) (a : ι → ℂ) (w : ι → ℝ) (N : ℕ) :
    DiffContOnCl ℂ (dampedSum s a w N) {z | 0 < z.re} := by
  have hnum : Differentiable ℂ (fun z : ℂ => ∑ i ∈ s, a i * Complex.exp (-((2:ℝ)+w i:ℝ)*z)) := by
    fun_prop
  have hn : ∀ z : ℂ, 0 ≤ z.re → (1+z)^N ≠ 0 := by
    intro z hz
    apply pow_ne_zero
    exact norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one (half_plane_norm_one_add hz))
  constructor
  · intro z hz
    exact ((hnum z).div (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => (1+z)^N) z) (hn z (le_of_lt hz))).differentiableWithinAt
  · rw [Complex.closure_setOfPred_lt_re]
    exact hnum.continuous.continuousOn.div ((continuous_const.add continuous_id).pow N).continuousOn hn

private lemma dampedSum_eq {ι : Type uKahler11675_1} (s : Finset ι) (a : ι → ℂ) (w : ι → ℝ) (N : ℕ) (z : ℂ) :
    dampedSum s a w N z = Complex.exp (-2*z)*expSum s a w (Complex.I*z)/(1+z)^N := by
  unfold dampedSum expSum
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_left_comm,mul_assoc,← Complex.exp_add]
  congr 2
  push_cast
  have hi2 := Complex.I_sq
  calc
    -(2+(w i:ℂ))*z = -2*z + Complex.I^2*(w i:ℂ)*z := by rw [hi2]; ring
    _ = _ := by ring

private lemma dampedSum_imag_norm {ι : Type uKahler11691_1} (s : Finset ι) (a : ι → ℂ) (w : ι → ℝ) (N : ℕ) (x : ℝ) :
    ‖dampedSum s a w N ((x:ℂ)*Complex.I)‖ = ‖expSum s a w (-x)‖/‖1+(x:ℂ)*Complex.I‖^N := by
  rw [dampedSum_eq,norm_div,norm_mul,norm_pow]
  have he : Complex.I*((x:ℂ)*Complex.I) = -(x:ℂ) := by calc
    _ = (x:ℂ)*Complex.I^2 := by ring
    _ = _ := by rw [Complex.I_sq]; ring
  rw [he,Complex.norm_exp]
  have hr : (-2*((x:ℂ)*Complex.I)).re = 0 := by simp [Complex.mul_re,Complex.mul_im]
  rw [hr,Real.exp_zero,one_mul]

private lemma dampedSum_boundary {ι : Type uKahler11701_1} (s : Finset ι) (a : ι → ℂ) (w : ι → ℝ) (N : ℕ)
    {B : ℝ} (hB : 0 ≤ B)
    (hg : ∀ x : ℝ, ‖expSum s a w x‖ ≤ B*(1+|x|)^N) (x : ℝ) :
    ‖dampedSum s a w N ((x:ℂ)*Complex.I)‖ ≤ B*2^N := by
  rw [dampedSum_imag_norm]
  have hn := half_plane_norm_one_add (z := (x:ℂ)*Complex.I) (by simp)
  have hd : ‖1+(x:ℂ)*Complex.I‖ > 0 := lt_of_lt_of_le zero_lt_one hn
  apply (div_le_iff₀ (pow_pos hd N)).mpr
  have him := Complex.abs_im_le_norm (1+(x:ℂ)*Complex.I)
  simp only [Complex.add_im,Complex.one_im,Complex.mul_im,Complex.ofReal_re,Complex.I_im,
    Complex.ofReal_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add] at him
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1+|x|) (show 1+|x| ≤ 2*‖1+(x:ℂ)*Complex.I‖ by linarith) N
  have hb := hg (-x)
  rw [abs_neg,Complex.ofReal_neg] at hb
  apply hb.trans
  simpa only [mul_pow,mul_assoc] using mul_le_mul_of_nonneg_left hp hB

private lemma expSum_upper_bound {ι : Type uKahler11718_1} (s : Finset ι) (a : ι → ℂ) (w : ι → ℝ) (N : ℕ)
    (hw : ∀ i ∈ s, -2 ≤ w i) {B : ℝ} (hB : 0 ≤ B)
    (hg : ∀ x : ℝ, ‖expSum s a w x‖ ≤ B*(1+|x|)^N)
    {z : ℂ} (hz : 0 ≤ z.im) (hz1 : ‖z‖ ≤ 1) :
    ‖expSum s a w z‖ ≤ B*4^N*Real.exp 2 := by
  let v := -Complex.I*z
  have hv : v.re = z.im := by simp [v,Complex.mul_re]
  have hv0 : 0 ≤ v.re := by rwa [hv]
  have hv1 : ‖v‖ ≤ 1 := by simpa [v,norm_mul] using hz1
  have hvz : Complex.I*v = z := by
    dsimp [v]
    calc
      _ = -Complex.I^2*z := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  have hb := bounded_half_plane (dampedSum_diffCont s a w N)
    (fun z hz => dampedSum_bound s a w N hw hz) (dampedSum_boundary s a w N hB hg) hv0
  rw [dampedSum_eq,norm_div,norm_mul,norm_pow,hvz,Complex.norm_exp] at hb
  have he : (-2*v).re = -2*z.im := by simp [Complex.mul_re,hv]
  rw [he] at hb
  have hd := half_plane_norm_one_add hv0
  have hdp : 0 < ‖1+v‖^N := pow_pos (lt_of_lt_of_le zero_lt_one hd) N
  have hb' := (div_le_iff₀ hdp).mp hb
  have hh := mul_le_mul_of_nonneg_left hb' (Real.exp_pos (2*z.im)).le
  have hexp : Real.exp (2*z.im)*Real.exp (-2*z.im) = 1 := by rw [← Real.exp_add]; convert Real.exp_zero using 1; ring_nf
  rw [← mul_assoc,hexp,one_mul] at hh
  have hv2 : ‖1+v‖ ≤ 2 := by have := norm_add_le (1:ℂ) v; simp only [norm_one] at this; linarith
  have hp : ‖1+v‖^N ≤ 2^N := pow_le_pow_left₀ (norm_nonneg _) hv2 N
  have hei : Real.exp (2*z.im) ≤ Real.exp 2 := by
    apply Real.exp_le_exp.mpr
    have hm := Complex.im_le_norm z
    linarith
  apply hh.trans
  calc
    _ ≤ Real.exp 2*((B*2^N)*2^N) := mul_le_mul hei (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity) (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc B,← mul_pow]; norm_num; ring

lemma expSum_neg_frequencies {ι : Type uKahler11754_1} (s : Finset ι) (a : ι → ℂ) (w : ι → ℝ) (z : ℂ) :
    expSum s a (fun i => -w i) z = expSum s a w (-z) := by
  unfold expSum
  apply Finset.sum_congr rfl
  intro i hi
  congr 2
  push_cast
  ring

lemma expSum_disk_bound {ι : Type uKahler11763_1} (s : Finset ι) (a : ι → ℂ) (w : ι → ℝ) (N : ℕ)
    (hw : ∀ i ∈ s, |w i| ≤ 2) {B : ℝ} (hB : 0 ≤ B)
    (hg : ∀ x : ℝ, ‖expSum s a w x‖ ≤ B*(1+|x|)^N)
    {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖expSum s a w z‖ ≤ B*4^N*Real.exp 2 := by
  by_cases him : 0 ≤ z.im
  · exact expSum_upper_bound s a w N (fun i hi => (abs_le.mp (hw i hi)).1) hB hg him hz
  · have hw' : ∀ i ∈ s, -2 ≤ -w i := fun i hi => by linarith [(abs_le.mp (hw i hi)).2]
    have hg' : ∀ x : ℝ, ‖expSum s a (fun i => -w i) x‖ ≤ B*(1+|x|)^N := by
      intro x
      rw [expSum_neg_frequencies]
      simpa only [Complex.ofReal_neg,abs_neg] using hg (-x)
    have hh := expSum_upper_bound s a (fun i => -w i) N hw' hB hg'
      (z := -z) (by simpa using (le_of_not_ge him)) (by simpa using hz)
    simpa only [expSum_neg_frequencies,neg_neg] using hh

lemma expSum_second_derivative_bound {ι : Type uKahler11780_1} (s : Finset ι) (a : ι → ℂ) (w : ι → ℝ) (N : ℕ)
    (hw : ∀ i ∈ s, |w i| ≤ 2) {B : ℝ} (hB : 0 ≤ B)
    (hg : ∀ x : ℝ, ‖expSum s a w x‖ ≤ B*(1+|x|)^N) :
    ‖iteratedDeriv 2 (expSum s a w) 0‖ ≤ 2*B*4^N*Real.exp 2 := by
  have hh := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := (0:ℂ)) 2 (by norm_num : (0:ℝ)<1)
    (expSum_differentiable s a w).diffContOnCl (fun z hz => expSum_disk_bound s a w N hw hB hg
      (show ‖z‖ ≤ 1 by simpa only [Metric.mem_sphere,dist_zero_right] using le_of_eq hz))
  convert hh using 1; norm_num; ring

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BasePhaseDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma phaseChar_derivative (n : ℤ) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => phaseChar n (Circle.exp t))
      ((n:ℂ)*Complex.I*phaseChar n (Circle.exp θ)) θ := by
  have hh : HasDerivAt (fun t : ℝ => (n:ℂ)*(t:ℂ)*Complex.I) ((n:ℂ)*Complex.I) θ := by
    simpa using (Complex.ofRealCLM.hasDerivAt.const_mul (n:ℂ)).mul_const Complex.I
  simpa only [phaseChar_exp,mul_comm] using hh.cexp

lemma phaseSum_derivative (s : Finset ℤ) (a : ℤ → ℂ) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => phaseSum s a (Circle.exp t))
      (phaseSum s (fun n => (n:ℂ)*Complex.I*a n) (Circle.exp θ)) θ := by
  have hh := HasDerivAt.sum (u := s) (fun n _ => (phaseChar_derivative n θ).const_mul (a n))
  convert! hh using 1
  · ext t; simp only [phaseSum,Finset.sum_apply]
  · unfold phaseSum
    apply Finset.sum_congr rfl
    intro n hn
    ring

lemma phase_curve_derivative (z : Base) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => (Circle.exp t:ℂ) • z)
      (Complex.I • ((Circle.exp θ:ℂ) • z)) θ := by
  have hh : HasDerivAt (fun t : ℝ => Complex.exp ((t:ℂ)*Complex.I))
      (Complex.exp ((θ:ℂ)*Complex.I)*Complex.I) θ := by
    simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one,one_mul] using (Complex.ofRealCLM.hasDerivAt.mul_const Complex.I).cexp
  simpa only [Circle.coe_exp,smul_smul,mul_comm] using hh.smul_const z

lemma phaseDerivative_curve {W : Base → ℝ} (hW : Differentiable ℝ W) (z : Base) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => W ((Circle.exp t:ℂ) • z))
      (phaseDerivative W ((Circle.exp θ:ℂ) • z)) θ := by
  exact (hW _).hasFDerivAt.comp_hasDerivAt θ (phase_curve_derivative z θ)

lemma phaseDerivative_expansion {W : Base → ℝ} (hW : Differentiable ℝ W) (p : Sphere)
    (s : Finset ℤ) (a : ℤ → ℂ)
    (he : ∀ z : Circle, (W ((z:ℂ) • (p:Base)):ℂ) = phaseSum s a z) (z : Circle) :
    (phaseDerivative W ((z:ℂ) • (p:Base)):ℂ) = phaseSum s (fun n => (n:ℂ)*Complex.I*a n) z := by
  obtain ⟨θ,rfl⟩ := Circle.exp_surjective z
  have hleft := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt θ (phaseDerivative_curve hW (p:Base) θ)
  have hfun : (fun t : ℝ => (W ((Circle.exp t:ℂ) • (p:Base)):ℂ)) =
      (fun t : ℝ => phaseSum s a (Circle.exp t)) := funext (fun t => he _)
  change HasDerivAt (fun t : ℝ => (W ((Circle.exp t:ℂ) • (p:Base)):ℂ))
    (phaseDerivative W ((Circle.exp θ:ℂ) • (p:Base)):ℂ) θ at hleft
  rw [hfun] at hleft
  exact hleft.unique (phaseSum_derivative s a θ)

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseDensityFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma circle_bracket_norm (z : Circle) (ξ : Base) (p : Sphere) :
    ‖bracket ((z:ℂ) • ξ) (p:Base)‖ = ‖bracket ξ (p:Base)‖ := by simp [bracket_smul,z.norm_coe]

lemma centralPoint_phase (p : Sphere) (z : Circle) (ξ : Base) :
    centralPoint p ((z:ℂ) • ξ) = (z:ℂ) • centralPoint p ξ := by
  unfold centralPoint
  rw [circle_bracket_norm,bracket_smul,smul_smul]
  congr 1
  ring

lemma densityHeight_phase (k : ℕ) (p : Sphere) (z : Circle) (ξ : Base) :
    densityHeight k p ((z:ℂ) • ξ) = densityHeight k p ξ := by simp only [densityHeight,circle_bracket_norm]

lemma densityCorrectionRaw_eq_re (k : ℕ) (f b : ℝ → ℝ) (W : Base → ℝ) (p : Sphere) (ξ : Base) :
    densityCorrectionRaw k f b W p ξ =
      (((‖bracket ξ (p:Base)‖^2)⁻¹:ℝ) *
        (bracket ξ (p:Base)/(‖bracket ξ (p:Base)‖:ℂ))^k *
        ((f (densityHeight k p ξ)*W (centralPoint p ξ):ℝ) + Complex.I*
          (b (densityHeight k p ξ)/k*phaseDerivative W (centralPoint p ξ):ℝ))).re := by
  simp only [densityCorrectionRaw,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,zero_mul,mul_zero,
    zero_add,add_zero,sub_zero,one_mul]
  ring

lemma densityCorrectionRaw_phase_expansion (k : ℕ) (f b : ℝ → ℝ) {W : Base → ℝ}
    (hW : Differentiable ℝ W) (p : Sphere) (ξ : Base) (hξ : bracket ξ (p:Base) ≠ 0)
    (s : Finset ℤ) (a : ℤ → ℂ)
    (he : ∀ z : Circle, (W ((z:ℂ) • centralPoint p ξ):ℂ) = phaseSum s a z) (z : Circle) :
    densityCorrectionRaw k f b W p ((z:ℂ) • ξ) =
      (∑ n ∈ s,
        (((‖bracket ξ (p:Base)‖^2)⁻¹:ℝ) *
          (bracket ξ (p:Base)/(‖bracket ξ (p:Base)‖:ℂ))^k * a n *
          ((f (densityHeight k p ξ) - (n:ℝ)/k*b (densityHeight k p ξ):ℝ):ℂ)) *
          phaseChar ((k:ℤ)+n) z).re := by
  let q : Sphere := ⟨centralPoint p ξ,by simpa only [Metric.mem_sphere,dist_zero_right] using centralPoint_norm p hξ⟩
  have hT := phaseDerivative_expansion hW q s a he z
  rw [densityCorrectionRaw_eq_re,circle_bracket_norm,bracket_smul,centralPoint_phase,densityHeight_phase]
  have hph : ((z:ℂ)*bracket ξ (p:Base)/(‖bracket ξ (p:Base)‖:ℂ))^k =
      (z:ℂ)^k*(bracket ξ (p:Base)/(‖bracket ξ (p:Base)‖:ℂ))^k := by rw [mul_div_assoc,mul_pow]
  rw [hph]
  change (phaseDerivative W ((z:ℂ) • centralPoint p ξ):ℂ) = _ at hT
  push_cast
  rw [he,hT]
  unfold phaseSum
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [phaseChar_add]
  simp only [phaseChar,Circle.coe_zpow,zpow_natCast]
  have hi : Complex.I*Complex.I = -1 := Complex.I_mul_I
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseDensityBandwidth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma densityCorrection_phase_band {W : Base → ℝ} (hW : Differentiable ℝ W)
    {ℓ k : ℕ} (hband : PhaseBandwidth W ℓ) (R : ℝ) (f b : ℝ → ℝ) (p : Sphere) :
    PhaseBandwidth (densityCorrection k R f b W p) (k+ℓ) := by
  classical
  intro ξ
  by_cases hc : Real.exp (-R/k) < ‖bracket (ξ:Base) (p:Base)‖
  · have hξ : bracket (ξ:Base) (p:Base) ≠ 0 := norm_pos_iff.mp (lt_trans (Real.exp_pos _) hc)
    let q : Sphere := ⟨centralPoint p ξ,by simpa only [Metric.mem_sphere,dist_zero_right] using centralPoint_norm p hξ⟩
    obtain ⟨s,a,hs,he⟩ := hband q
    let A : ℤ → ℂ := fun n => (((‖bracket (ξ:Base) (p:Base)‖^2)⁻¹:ℝ) *
          (bracket (ξ:Base) (p:Base)/(‖bracket (ξ:Base) (p:Base)‖:ℂ))^k * a n *
          ((f (densityHeight k p ξ) - (n:ℝ)/k*b (densityHeight k p ξ):ℝ):ℂ))
    have hh : ∀ z : Circle, densityCorrection k R f b W p ((z:ℂ) • (ξ:Base)) =
        (phaseSum (s.image (fun n => (k:ℤ)+n)) (fun n => A (n-k)) z).re := by
      intro z
      rw [densityCorrection,circle_bracket_norm,ite_eq_left hc]
      rw [densityCorrectionRaw_phase_expansion k f b hW p ξ hξ s a he z]
      rw [phaseSum_shift]
    have hbound : ∀ n ∈ s.image (fun n => (k:ℤ)+n), |n| ≤ ((k+ℓ:ℕ):ℤ) := by
      intro n hn
      obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hn
      have ht := abs_add_le (k:ℤ) m
      have hm' := hs m hm
      simpa only [Nat.cast_add,abs_of_nonneg (Int.natCast_nonneg k)] using
        le_trans ht (by simpa using add_le_add_right hm' (k:ℤ))
    obtain ⟨b',hb'⟩ := phaseSum_real_band hbound (fun n => A (n-k))
    refine ⟨phaseBand (k+ℓ),b',fun n hn => (mem_phaseBand _ _).mp hn,?_⟩
    intro z
    rw [hh,hb']
  · refine ⟨∅,fun _ => 0,by simp,?_⟩
    intro z
    simp only [densityCorrection,circle_bracket_norm,ite_eq_right hc,Complex.ofReal_zero,phaseSum,Finset.sum_empty]

lemma densityCorrection_orbit_zero {W : Base → ℝ} (hW : Differentiable ℝ W)
    {ℓ k : ℕ} (hband : PhaseBandwidth W ℓ) (hℓ : ℓ < k)
    (R : ℝ) (f b : ℝ → ℝ) (p ξ : Sphere) :
    (∫ z : Circle, densityCorrection k R f b W p ((z:ℂ) • (ξ:Base)) ∂circleMeasure) = 0 := by
  classical
  by_cases hc : Real.exp (-R/k) < ‖bracket (ξ:Base) (p:Base)‖
  · have hξ : bracket (ξ:Base) (p:Base) ≠ 0 := norm_pos_iff.mp (lt_trans (Real.exp_pos _) hc)
    let q : Sphere := ⟨centralPoint p ξ,by simpa only [Metric.mem_sphere,dist_zero_right] using centralPoint_norm p hξ⟩
    obtain ⟨s,a,hs,he⟩ := hband q
    let A : ℤ → ℂ := fun n => (((‖bracket (ξ:Base) (p:Base)‖^2)⁻¹:ℝ) *
          (bracket (ξ:Base) (p:Base)/(‖bracket (ξ:Base) (p:Base)‖:ℂ))^k * a n *
          ((f (densityHeight k p ξ) - (n:ℝ)/k*b (densityHeight k p ξ):ℝ):ℂ))
    have hh : ∀ z : Circle, densityCorrection k R f b W p ((z:ℂ) • (ξ:Base)) =
        (phaseSum (s.image (fun n => (k:ℤ)+n)) (fun n => A (n-k)) z).re := by
      intro z
      rw [densityCorrection,circle_bracket_norm,ite_eq_left hc]
      rw [densityCorrectionRaw_phase_expansion k f b hW p ξ hξ s a he z,phaseSum_shift]
    simp_rw [hh]
    rw [show (∫ z : Circle, (phaseSum (s.image (fun n => (k:ℤ)+n)) (fun n => A (n-k)) z).re ∂circleMeasure) =
      (∫ z : Circle, phaseSum (s.image (fun n => (k:ℤ)+n)) (fun n => A (n-k)) z ∂circleMeasure).re from
      integral_re (compact_continuous_integrable (phaseSum_continuous _ _))]
    have hn : 0 ∉ s.image (fun n => (k:ℤ)+n) := by
      intro hn
      obtain ⟨m,hm,he⟩ := Finset.mem_image.mp hn
      have hm' := (abs_le.mp (hs m hm)).1
      omega
    rw [phaseSum_integral _ hn]
    rfl
  · simp only [densityCorrection,circle_bracket_norm,ite_eq_right hc,integral_zero]

lemma densityBandwidth_succ (Q j : ℕ) : densityBandwidth Q (j+1)=Q^(j+1)+densityBandwidth Q j := by
  simp [densityBandwidth,Finset.sum_range_succ,Nat.add_comm]

lemma densityBandwidth_lt {Q : ℕ} (hQ : 2 ≤ Q) (j : ℕ) : densityBandwidth Q j < Q^(j+1) := by
  induction j with
  | zero => simp [densityBandwidth]; omega
  | succ j ih =>
    rw [densityBandwidth_succ]
    have hp : 0 < Q^(j+1) := pow_pos (by omega) _
    calc
      Q^(j+1)+densityBandwidth Q j < Q^(j+1)*2 := by omega
      _ ≤ Q^(j+1)*Q := Nat.mul_le_mul_left _ hQ
      _ = _ := by simp only [pow_succ]

lemma density_bandwidth {Q : ℕ} (hQ : 0 < Q) {R E : ℝ} (hER : E < R)
    {f b : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b)
    (htail : ∀ y, E ≤ y → f y=0 ∧ b y=0) (P : ℕ → Finset Sphere) (j : ℕ) :
    PhaseBandwidth (density Q R f b P j) (densityBandwidth Q j) := by
  induction j with
  | zero => exact phaseBandwidth_one
  | succ j ih =>
    rw [densityBandwidth_succ]
    apply phaseBandwidth_add (phaseBandwidth_mono ih (Nat.le_add_left _ _))
    apply phaseBandwidth_sum
    intro p hp
    exact densityCorrection_phase_band ((density_smooth hQ hER hf hb htail P j).differentiable (by simp)) ih R f b p

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseRadialSubstitution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff ENNReal Pointwise
open scoped ContDiff
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma hopf_law : Measure.map hopf ((volume : Measure unitInterval).prod torusMeasure) = sigma := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  rw [integral_map (f := fun x => f x) hopf_continuous.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  rw [integral_prod (fun x => f (hopf x)) (compact_continuous_integrable (f.continuous.comp hopf_continuous))]
  exact (hopf_integral f.toContinuousMap).symm

lemma hopf_integral_complex {f : Sphere → ℂ} (hf : Continuous f) :
    (∫ ξ, f ξ ∂sigma) = ∫ u : unitInterval, ∫ z, f (hopf (u,z)) ∂torusMeasure := by
  rw [← hopf_law,integral_map hopf_continuous.measurable.aemeasurable hf.aestronglyMeasurable]
  exact integral_prod _ (compact_continuous_integrable (hf.comp hopf_continuous))

lemma weight_profile_integral {f b : ℝ → ℝ} (hf : Continuous f) (hb : Continuous b)
    (hode : ∀ y, HasDerivAt b (b y+f y) y) {R : ℝ} (hR : 0 ≤ R)
    (hzero : b 0=0) (htail : b R=0) (v : ℝ) :
    (∫ y in 0..R, Real.exp (-v*y)*(f y+(1-v)*b y)) = 0 := by
  have hd : ∀ y, HasDerivAt (fun y => Real.exp (-v*y)*b y)
      (Real.exp (-v*y)*(f y+(1-v)*b y)) y := by
    intro y
    have hh := (((hasDerivAt_id y).const_mul (-v)).exp).mul (hode y)
    convert! hh using 1; dsimp [id]; ring
  have hc : Continuous (fun y => Real.exp (-v*y)*(f y+(1-v)*b y)) := by fun_prop
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => hd y) (hc.intervalIntegrable 0 R)
  rw [intervalIntegral.integral_of_le hR] at hh ⊢
  simpa [hzero,htail] using hh

lemma log_radial_substitution {k R : ℝ} (hk : 0 < k) (hR : 0 < R)
    {F : ℝ → ℂ} (hF : Continuous F) :
    (∫ t in Real.exp (-2*R/k)..1, (t⁻¹:ℝ) • F (-k/2*Real.log t)) =
      (2/k:ℝ) • ∫ y in 0..R, F y := by
  let g : ℝ → ℂ := fun t => (t⁻¹:ℝ) • F (-k/2*Real.log t)
  let e : ℝ → ℝ := fun y => Real.exp (-2*y/k)
  let e' : ℝ → ℝ := fun y => (-2/k)*Real.exp (-2*y/k)
  have he : ∀ y ∈ uIcc 0 R, HasDerivAt e (e' y) y := by
    rw [uIcc_of_le hR.le]
    intro y hy
    convert! (((hasDerivAt_id y).const_mul (-2)).div_const k).exp using 1; dsimp [e,e']; ring
  have he' : ContinuousOn e' (uIcc 0 R) := by unfold e'; fun_prop
  have heg : ContinuousOn g (e '' uIcc 0 R) := by
    intro t ht
    obtain ⟨y,hy,rfl⟩ := ht
    have hp : 0 < e y := Real.exp_pos _
    exact ((continuousAt_id.inv₀ hp.ne').smul
      (hF.continuousAt.comp ((continuousAt_const.mul (Real.continuousAt_log hp.ne'))))).continuousWithinAt
  have hs := intervalIntegral.integral_deriv_smul_comp' he he' heg
  have hcomp : ∀ y, e' y • g (e y) = (-2/k:ℝ) • F y := by
    intro y
    change ((-2/k)*Real.exp (-2*y/k):ℝ) •
      ((Real.exp (-2*y/k))⁻¹:ℝ) • F (-k/2*Real.log (Real.exp (-2*y/k))) = _
    rw [smul_smul,Real.log_exp]
    have hh : -k/2*(-2*y/k)=y := by field_simp
    rw [hh]
    congr 1
    field_simp
  change (∫ y in 0..R, e' y • g (e y)) = _ at hs
  simp_rw [hcomp] at hs
  rw [intervalIntegral.integral_smul] at hs
  have he0 : e 0=1 := by simp [e]
  have heR : e R=Real.exp (-2*R/k) := rfl
  rw [he0,heR] at hs
  conv_rhs at hs => rw [intervalIntegral.integral_symm]
  change _ = -(∫ t in Real.exp (-2*R/k)..1, (t⁻¹:ℝ) • F (-k/2*Real.log t)) at hs
  have hh := congrArg Neg.neg hs
  simpa only [neg_neg,← neg_smul,neg_div,neg_neg] using hh.symm

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseAdaptedHopf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma adaptedHopf_integral {F : Sphere → ℂ} (hF : Continuous F) (p : Sphere) :
    (∫ ξ, F ξ ∂sigma) = ∫ t : unitInterval, ∫ z, F (adaptedHopf p t z) ∂torusMeasure := by
  rw [← sigma_integral_unitary (adaptedIsometry p).symm F]
  exact hopf_integral_complex (hF.comp (sphereAction _).continuous)

lemma adaptedHopf_bracket (p : Sphere) (t : unitInterval) (z : Circle × Circle) :
    bracket (adaptedHopf p t z : Base) (p:Base)=(z.1:ℂ)*(Real.sqrt (t:ℝ):ℂ) := by
  rw [← adaptedIsometry_zero]
  simp only [adaptedHopf,sphereAction_coe,LinearIsometryEquiv.apply_symm_apply,hopf,torusAction_zero,radialSphere_zero]

lemma adaptedHopf_bracket_norm (p : Sphere) (t : unitInterval) (z : Circle × Circle) :
    ‖bracket (adaptedHopf p t z : Base) (p:Base)‖=Real.sqrt (t:ℝ) := by
  rw [adaptedHopf_bracket,norm_mul,z.1.norm_coe,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]

lemma adaptedHopf_phase (p : Sphere) (t : unitInterval) (ht : 0 < (t:ℝ)) (z : Circle × Circle) :
    bracket (adaptedHopf p t z : Base) (p:Base)/(‖bracket (adaptedHopf p t z : Base) (p:Base)‖:ℂ)=(z.1:ℂ) := by
  rw [adaptedHopf_bracket_norm,adaptedHopf_bracket,mul_div_cancel_right₀]
  exact_mod_cast Real.sqrt_ne_zero'.mpr ht

lemma adaptedHopf_height (k : ℕ) (p : Sphere) (t : unitInterval) (z : Circle × Circle) :
    densityHeight k p (adaptedHopf p t z) = -(k:ℝ)/2*Real.log (t:ℝ) := by
  rw [densityHeight,adaptedHopf_bracket_norm,Real.log_sqrt t.property.1]
  ring

lemma adaptedHopf_correction_expansion {W : Base → ℝ} (hW : Differentiable ℝ W)
    (k : ℕ) (f b : ℝ → ℝ) (p : Sphere) (t : unitInterval) (ht : 0 < (t:ℝ))
    (s : Finset ℤ) (a : ℤ → ℂ) (he : ∀ z : Circle, (W ((z:ℂ) • (p:Base)):ℂ)=phaseSum s a z)
    (z : Circle × Circle) :
    densityCorrectionRaw k f b W p (adaptedHopf p t z) =
      (∑ n ∈ s, ((t:ℝ)⁻¹:ℂ)*a n*
        ((f (-(k:ℝ)/2*Real.log (t:ℝ))-(n:ℝ)/k*b (-(k:ℝ)/2*Real.log (t:ℝ))):ℂ)*phaseChar ((k:ℤ)+n) z.1).re := by
  have hT := phaseDerivative_expansion hW p s a he z.1
  rw [densityCorrectionRaw_eq_re,adaptedHopf_phase p t ht z,adaptedHopf_bracket_norm,Real.sq_sqrt t.property.1,adaptedHopf_height]
  have hcentral : centralPoint p (adaptedHopf p t z)=(z.1:ℂ) • (p:Base) := by
    rw [centralPoint,adaptedHopf_phase p t ht z]
  rw [hcentral]
  push_cast
  rw [he,hT]
  unfold phaseSum
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [phaseChar_add]
  simp only [phaseChar,Circle.coe_zpow,zpow_natCast]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

lemma phase_shifted_real_moment (s : Finset ℤ) (a : ℤ → ℂ) (k : ℤ) (N : ℕ)
    (hs : ∀ n ∈ s, 0 < k+n) :
    (∫ z : Circle, phaseChar N z*((∑ n ∈ s, a n*phaseChar (k+n) z).re:ℂ) ∂circleMeasure) =
      if (N:ℤ)-k ∈ s then star (a ((N:ℤ)-k))/2 else 0 := by
  classical
  have he : ∀ z : Circle, phaseChar N z*((∑ n ∈ s, a n*phaseChar (k+n) z).re:ℂ) =
      ∑ n ∈ s, phaseChar N z*((a n*phaseChar (k+n) z).re:ℂ) := by
    intro z
    simp only [Complex.re_sum,Complex.ofReal_sum,Finset.mul_sum]
  simp_rw [he]
  rw [MeasureTheory.integral_finsetSum s (fun n hn => compact_continuous_integrable (by
    exact (phaseChar_continuous _).mul (Complex.continuous_ofReal.comp
      (Complex.continuous_re.comp (continuous_const.mul (phaseChar_continuous _))))))]
  have hsum : (∑ n ∈ s, ∫ z : Circle, phaseChar N z*((a n*phaseChar (k+n) z).re:ℂ) ∂circleMeasure) =
      ∑ n ∈ s, if k+n=(N:ℤ) then star (a n)/2 else 0 :=
    Finset.sum_congr rfl (fun n hn => phase_real_moment _ _ _ (hs n hn))
  rw [hsum]
  have hh : ∀ n : ℤ, k+n=(N:ℤ) ↔ n=(N:ℤ)-k := by intro n; omega
  simp_rw [hh]
  simp

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseRadialCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma log_sqrt_power {t : ℝ} (ht : 0 < t) (n : ℕ) :
    (Real.sqrt t)^n = Real.exp ((n:ℝ)/2*Real.log t) := by
  rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos ht,← Real.exp_nat_mul]
  congr 1
  ring

lemma interval_indicator_above {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (g : ℝ → ℂ) :
    (∫ t in (0:ℝ)..1, if a<t then g t else 0) = ∫ t in a..1, g t := by
  classical
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),intervalIntegral.integral_of_le ha1]
  change (∫ t in Ioc (0:ℝ) 1, (Ioi a).indicator g t) = _
  rw [integral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi]
  have hset : Ioi a ∩ Ioc (0:ℝ) 1 = Ioc a 1 := by
    ext t
    simp only [mem_inter_iff,mem_Ioi,mem_Ioc]
    constructor
    · rintro ⟨ht,_,ht1⟩; exact ⟨ht,ht1⟩
    · rintro ⟨ht,ht1⟩; exact ⟨ht,lt_of_le_of_lt ha ht,ht1⟩
  rw [hset]

lemma radial_profile_moment {f b : ℝ → ℝ} (hf : Continuous f) (hb : Continuous b)
    (hode : ∀ y, HasDerivAt b (b y+f y) y) {k R : ℝ} (hk : 0 < k) (hR : 0 < R)
    (hzero : b 0=0) (htail : b R=0) (n : ℕ) :
    (∫ t in (0:ℝ)..1, if Real.exp (-2*R/k)<t then
      ((t⁻¹*(Real.sqrt t)^n*(f (-k/2*Real.log t)+(1-(n:ℝ)/k)*b (-k/2*Real.log t)):ℝ):ℂ) else 0)=0 := by
  let F : ℝ → ℂ := fun y => ((Real.exp (-(n:ℝ)/k*y)*(f y+(1-(n:ℝ)/k)*b y):ℝ):ℂ)
  have hF : Continuous F := by unfold F; fun_prop
  have ha : Real.exp (-2*R/k) ≤ 1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith) hk.le)
  rw [interval_indicator_above (Real.exp_pos _).le ha]
  have he : (∫ t in Real.exp (-2*R/k)..1,
      ((t⁻¹*(Real.sqrt t)^n*(f (-k/2*Real.log t)+(1-(n:ℝ)/k)*b (-k/2*Real.log t)):ℝ):ℂ)) =
      ∫ t in Real.exp (-2*R/k)..1, (t⁻¹:ℝ) • F (-k/2*Real.log t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le ha] at ht
    have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos _) ht.1
    dsimp only
    rw [log_sqrt_power ht0 n]
    unfold F
    have hex : -(n:ℝ)/k*(-k/2*Real.log t)=(n:ℝ)/2*Real.log t := by field_simp
    rw [hex]
    simp only [Complex.real_smul,Complex.ofReal_mul]
    ring
  rw [he,log_radial_substitution hk hR hF]
  have hi : (∫ y in 0..R, F y)=0 := by
    unfold F
    rw [intervalIntegral.integral_ofReal]
    rw [show -(n:ℝ)/k = -((n:ℝ)/k) by ring,
      weight_profile_integral hf hb hode hR.le hzero htail ((n:ℝ)/k)]
    rfl
  rw [hi,smul_zero]

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseCorrectionMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma adaptedMonomial_continuous (p : Sphere) (n m : ℕ) : Continuous (adaptedMonomial p n m) := by
  unfold adaptedMonomial
  fun_prop

lemma adaptedMonomial_hopf (p : Sphere) (n m : ℕ) (t : unitInterval) (z : Circle × Circle) :
    adaptedMonomial p n m (adaptedHopf p t z) =
      (Real.sqrt (t:ℝ):ℂ)^n*phaseChar n z.1*(Real.sqrt (1-(t:ℝ)):ℂ)^m*phaseChar m z.2 := by
  simp only [adaptedMonomial,adaptedHopf,sphereAction_coe,LinearIsometryEquiv.apply_symm_apply,
    hopf,torusAction_zero,torusAction_one,radialSphere_zero,radialSphere_one,phaseChar,zpow_natCast,Circle.coe_pow,mul_pow]
  ring

lemma patch_cutoff_squared (k : ℕ) (R : ℝ) (t : unitInterval) :
    Real.exp (-R/k)<Real.sqrt (t:ℝ) ↔ Real.exp (-2*R/k)<(t:ℝ) := by
  have he : Real.exp (-R/k)^2=Real.exp (-2*R/k) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hh := (sq_lt_sq₀ (Real.exp_pos (-R/k)).le (Real.sqrt_nonneg (t:ℝ))).symm
  rwa [he,Real.sq_sqrt t.property.1] at hh

lemma correction_torus_moment {W : Base → ℝ} (hW : Differentiable ℝ W)
    (k : ℕ) (hk : 0 < k) (R : ℝ) (f b : ℝ → ℝ) (p : Sphere)
    (s : Finset ℤ) (a : ℤ → ℂ) (he : ∀ z : Circle, (W ((z:ℂ) • (p:Base)):ℂ)=phaseSum s a z)
    (hs : ∀ n ∈ s, 0 < (k:ℤ)+n) (N M : ℕ) (t : unitInterval) :
    (∫ z : Circle × Circle, adaptedMonomial p N M (adaptedHopf p t z)*
      (densityCorrection k R f b W p (adaptedHopf p t z):ℂ) ∂torusMeasure) =
    if M=0 ∧ (N:ℤ)-(k:ℤ) ∈ s then (star (a ((N:ℤ)-(k:ℤ)))/2)*
      (if Real.exp (-2*R/k)<(t:ℝ) then
        (((t:ℝ)⁻¹*(Real.sqrt (t:ℝ))^N*(f (-(k:ℝ)/2*Real.log (t:ℝ))+(1-(N:ℝ)/k)*b (-(k:ℝ)/2*Real.log (t:ℝ))) : ℝ) : ℂ) else 0)
    else 0 := by
  classical
  by_cases ht : Real.exp (-2*R/k)<(t:ℝ)
  · have ht0 : 0 < (t:ℝ) := lt_trans (Real.exp_pos _) ht
    have hcut : Real.exp (-R/k)<Real.sqrt (t:ℝ) := (patch_cutoff_squared k R t).mpr ht
    let y := -(k:ℝ)/2*Real.log (t:ℝ)
    let A : ℤ → ℂ := fun n => (((t:ℝ)⁻¹:ℝ):ℂ)*a n*((f y-(n:ℝ)/k*b y:ℝ):ℂ)
    let S : Circle → ℂ := fun z => ∑ n ∈ s, A n*phaseChar ((k:ℤ)+n) z
    have hcorr : ∀ z : Circle × Circle, densityCorrection k R f b W p (adaptedHopf p t z)=(S z.1).re := by
      intro z
      rw [densityCorrection,adaptedHopf_bracket_norm,ite_eq_left hcut]
      simpa only [S,A,y,Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_inv,Complex.ofReal_natCast] using adaptedHopf_correction_expansion hW k f b p t ht0 s a he z
    have hprod : ∀ z : Circle × Circle,
        adaptedMonomial p N M (adaptedHopf p t z)*(densityCorrection k R f b W p (adaptedHopf p t z):ℂ) =
        ((Real.sqrt (t:ℝ):ℂ)^N*(Real.sqrt (1-(t:ℝ)):ℂ)^M*(phaseChar N z.1*((S z.1).re:ℂ)))*phaseChar M z.2 := by
      intro z
      rw [adaptedMonomial_hopf,hcorr]
      ring
    simp_rw [hprod]
    rw [show torusMeasure=circleMeasure.prod circleMeasure from rfl,
      integral_prod_mul (fun z : Circle => (Real.sqrt (t:ℝ):ℂ)^N*(Real.sqrt (1-(t:ℝ)):ℂ)^M*(phaseChar N z*((S z).re:ℂ))) (phaseChar M),integral_const_mul,
      phase_shifted_real_moment s A k N hs,circle_char_mean]
    rw [ite_eq_left ht]
    by_cases hM : M=0
    · subst M
      simp only [Nat.cast_zero,ite_true,pow_zero,mul_one,true_and]
      by_cases hN : (N:ℤ)-(k:ℤ) ∈ s
      · rw [ite_eq_left hN,ite_eq_left hN]
        unfold A y
        simp only [Complex.star_def,map_mul,Complex.conj_ofReal]
        push_cast
        have hk0 : (k:ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hk)
        field_simp
        ring
      · simp only [ite_eq_right hN,mul_zero]
    · have hM' : (M:ℤ) ≠ 0 := by exact_mod_cast hM
      simp only [ite_eq_right hM',mul_zero,hM,false_and,ite_false]
  · have hcut : ¬ Real.exp (-R/k)<Real.sqrt (t:ℝ) := fun h => ht ((patch_cutoff_squared k R t).mp h)
    have hz : ∀ z : Circle × Circle, densityCorrection k R f b W p (adaptedHopf p t z)=0 := by
      intro z
      simp only [densityCorrection,adaptedHopf_bracket_norm,ite_eq_right hcut]
    simp only [hz,Complex.ofReal_zero,mul_zero,integral_zero,ite_eq_right ht,ite_self]

lemma unitInterval_integral_complex (f : ℝ → ℂ) :
    (∫ t : unitInterval, f t) = ∫ t in (0:ℝ)..1, f t := by
  rw [unitInterval.volume_def,integral_subtype_comap measurableSet_Icc f,
    integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]

lemma densityCorrection_monomial_moment {k : ℕ} (hk : 0 < k) {R E : ℝ} (hR : 0 < R) (hER : E < R)
    {f b : ℝ → ℝ} {W : Base → ℝ} (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b)
    (hode : ∀ y, HasDerivAt b (b y+f y) y) (hzero : b 0=0)
    (htail : ∀ y, E ≤ y → f y=0 ∧ b y=0) (hW : ContDiff ℝ ∞ W)
    {ℓ : ℕ} (hband : PhaseBandwidth W ℓ) (hℓ : ℓ<k) (p : Sphere) (N M : ℕ) :
    (∫ ξ : Sphere, adaptedMonomial p N M ξ*(densityCorrection k R f b W p ξ:ℂ) ∂sigma)=0 := by
  have hcont : Continuous (fun ξ : Sphere => adaptedMonomial p N M ξ*(densityCorrection k R f b W p ξ:ℂ)) :=
    ((adaptedMonomial_continuous p N M).comp continuous_subtype_val).mul
      (Complex.continuous_ofReal.comp ((densityCorrection_smooth hk hER hf hb hW htail p).continuous.comp continuous_subtype_val))
  rw [adaptedHopf_integral hcont p]
  obtain ⟨s,a,hs,he⟩ := hband p
  have hspos : ∀ n ∈ s, 0 < (k:ℤ)+n := by
    intro n hn
    have hn' := (abs_le.mp (hs n hn)).1
    omega
  simp_rw [correction_torus_moment (hW.differentiable (by simp)) k hk R f b p s a he hspos N M]
  split_ifs with hNM
  · rw [integral_const_mul]
    rw [unitInterval_integral_complex (fun t : ℝ => if Real.exp (-2*R/k)<t then ((t⁻¹*(Real.sqrt t)^N*(f (-(k:ℝ)/2*Real.log t)+(1-(N:ℝ)/k)*b (-(k:ℝ)/2*Real.log t)):ℝ):ℂ) else 0),
      radial_profile_moment hf.continuous hb.continuous hode (by exact_mod_cast hk) hR hzero (htail R hER.le).2 N,mul_zero]
  · simp

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BasePolynomialChange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma linearSubstitution_eval (U : Base →ₗ[ℂ] Base) (z : Base) (i : Fin 2) :
    MvPolynomial.eval (fun j => z j) (linearSubstitution U i)=U z i := by
  simp only [linearSubstitution,map_sum,map_mul,MvPolynomial.eval_C,MvPolynomial.eval_X]
  conv_rhs => rw [base_eq_sum_single z,map_sum]
  simp only [map_smul,Fin.sum_univ_two,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  ring

lemma polynomial_change_coords (U : Base ≃ₗᵢ[ℂ] Base) (P : MvPolynomial (Fin 2) ℂ) :
    ∃ Q : MvPolynomial (Fin 2) ℂ, ∀ z : Base,
      MvPolynomial.eval (fun i => U z i) Q = MvPolynomial.eval (fun i => z i) P := by
  refine ⟨MvPolynomial.bind₁ (linearSubstitution U.symm.toLinearEquiv.toLinearMap) P,?_⟩
  intro z
  change MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun i => U z i) _=_
  rw [MvPolynomial.eval₂Hom_bind₁]
  have he : (fun i => MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun j => U z j)
      (linearSubstitution U.symm.toLinearEquiv.toLinearMap i))=fun i => z i := by
    funext i
    change MvPolynomial.eval (fun j => U z j) _=z i
    rw [linearSubstitution_eval]
    simp
  rw [he]
  rfl

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseDensityMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal
namespace PinchedHartogs.BaseConstruction

lemma polynomial_weight_integrable {W : Base → ℝ} (hW : Continuous W)
    (P : MvPolynomial (Fin 2) ℂ) (U : Base ≃ₗᵢ[ℂ] Base) :
    Integrable (fun ξ : Sphere => MvPolynomial.eval (fun i => U (ξ:Base) i) P*(W ξ:ℂ)) sigma := by
  apply continuous_integrable
  apply Continuous.mul
  · exact P.continuous_eval.comp (continuous_pi (fun i => (EuclideanSpace.proj i).continuous.comp (U.continuous.comp continuous_subtype_val)))
  · exact Complex.continuous_ofReal.comp (hW.comp continuous_subtype_val)

lemma densityCorrection_polynomial_moment {k : ℕ} (hk : 0 < k) {R E : ℝ} (hR : 0 < R) (hER : E < R)
    {f b : ℝ → ℝ} {W : Base → ℝ} (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b)
    (hode : ∀ y, HasDerivAt b (b y+f y) y) (hzero : b 0=0)
    (htail : ∀ y, E ≤ y → f y=0 ∧ b y=0) (hW : ContDiff ℝ ∞ W)
    {ℓ : ℕ} (hband : PhaseBandwidth W ℓ) (hℓ : ℓ<k) (p : Sphere) (P : MvPolynomial (Fin 2) ℂ) :
    (∫ ξ : Sphere, MvPolynomial.eval (fun i => (ξ:Base) i) P*(densityCorrection k R f b W p ξ:ℂ) ∂sigma)=0 := by
  classical
  obtain ⟨Q,hQ⟩ := polynomial_change_coords (adaptedIsometry p) P
  simp_rw [← hQ]
  clear hQ
  have hc := (densityCorrection_smooth hk hER hf hb hW htail p).continuous
  induction Q using MvPolynomial.induction_on' with
  | monomial d a =>
    simp only [MvPolynomial.eval_monomial,Finsupp.prod_pow,Fin.prod_univ_two]
    have he : ∀ ξ : Sphere, a*((adaptedIsometry p (ξ:Base) 0)^d 0*(adaptedIsometry p (ξ:Base) 1)^d 1)*
        (densityCorrection k R f b W p ξ:ℂ)=a*(adaptedMonomial p (d 0) (d 1) ξ*(densityCorrection k R f b W p ξ:ℂ)) := by
      intro ξ; dsimp [adaptedMonomial]; ring
    simp_rw [he]
    rw [integral_const_mul,densityCorrection_monomial_moment hk hR hER hf hb hode hzero htail hW hband hℓ,mul_zero]
  | add Q₁ Q₂ ih₁ ih₂ =>
    simp only [map_add,add_mul]
    rw [integral_add (polynomial_weight_integrable hc Q₁ (adaptedIsometry p))
      (polynomial_weight_integrable hc Q₂ (adaptedIsometry p)),ih₁,ih₂,add_zero]

lemma density_polynomial_moment {Q : ℕ} (hQ : 2 ≤ Q) {R E : ℝ} (hR : 0 < R) (hER : E < R)
    {f b : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b)
    (hode : ∀ y, HasDerivAt b (b y+f y) y) (hzero : b 0=0)
    (htail : ∀ y, E ≤ y → f y=0 ∧ b y=0) (P : ℕ → Finset Sphere) (j : ℕ)
    (p : MvPolynomial (Fin 2) ℂ) :
    (∫ ξ : Sphere, MvPolynomial.eval (fun i => (ξ:Base) i) p*(density Q R f b P j ξ:ℂ) ∂sigma)=
      MvPolynomial.eval (fun _ => 0) p := by
  classical
  have hQ0 : 0 < Q := by omega
  induction j with
  | zero => simpa only [density,Complex.ofReal_one,mul_one] using sigma_represents p
  | succ j ih =>
    have hw := density_smooth hQ0 hER hf hb htail P j
    have hband := density_bandwidth hQ0 hER hf hb htail P j
    have hi : ∀ q ∈ P (Q^(j+1)), Integrable (fun ξ : Sphere =>
        MvPolynomial.eval (fun i => (ξ:Base) i) p*(densityCorrection (Q^(j+1)) R f b (density Q R f b P j) q ξ:ℂ)) sigma := by
      intro q hq
      exact polynomial_weight_integrable (densityCorrection_smooth (pow_pos hQ0 _) hER hf hb hw htail q).continuous p (LinearIsometryEquiv.refl ℂ Base)
    have hiw : Integrable (fun ξ : Sphere => MvPolynomial.eval (fun i => (ξ:Base) i) p*(density Q R f b P j ξ:ℂ)) sigma := by
      simpa using polynomial_weight_integrable hw.continuous p (LinearIsometryEquiv.refl ℂ Base)
    simp only [density,Complex.ofReal_add,Complex.ofReal_sum,mul_add,Finset.mul_sum]
    rw [integral_add hiw (MeasureTheory.integrable_finsetSum _ hi),
      MeasureTheory.integral_finsetSum _ hi,ih]
    have hz : (∑ q ∈ P (Q^(j+1)), ∫ ξ : Sphere, MvPolynomial.eval (fun i => (ξ:Base) i) p*
        (densityCorrection (Q^(j+1)) R f b (density Q R f b P j) q ξ:ℂ) ∂sigma)=0 := by
      apply Finset.sum_eq_zero
      intro q hq
      exact densityCorrection_polynomial_moment (pow_pos hQ0 _) hR hER hf hb hode hzero htail hw hband (densityBandwidth_lt hQ j) q p
    rw [hz,add_zero]

lemma density_mass_one {Q : ℕ} (hQ : 2 ≤ Q) {R E : ℝ} (hR : 0 < R) (hER : E < R)
    {f b : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b)
    (hode : ∀ y, HasDerivAt b (b y+f y) y) (hzero : b 0=0)
    (htail : ∀ y, E ≤ y → f y=0 ∧ b y=0) (P : ℕ → Finset Sphere) (j : ℕ) :
    (∫ ξ : Sphere, density Q R f b P j ξ ∂sigma)=1 := by
  have hh := density_polynomial_moment hQ hR hER hf hb hode hzero htail P j (1:MvPolynomial (Fin 2) ℂ)
  simp only [map_one,one_mul,integral_complex_ofReal] at hh
  exact Complex.ofReal_injective hh

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseDensityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler13116_1

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff ENNReal Pointwise
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal
namespace PinchedHartogs.BaseConstruction

lemma densityMeasure_integral {W : Base → ℝ} (hW : Continuous W) (hpos : ∀ ξ : Sphere, 0 ≤ W ξ)
    {E : Type uKahler13116_1} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Sphere → E) :
    (∫ ξ, g ξ ∂densityMeasure W) = ∫ ξ, W ξ • g ξ ∂sigma := by
  change (∫ ξ, g ξ ∂sigma.withDensity (fun ξ : Sphere => ENNReal.ofReal (W ξ))) = _
  have hm : Measurable (fun ξ : Sphere => ENNReal.ofReal (W ξ)) := (hW.comp continuous_subtype_val).measurable.ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hm (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) g]
  simp_rw [ENNReal.toReal_ofReal (hpos _)]

lemma densityMeasure_probability {W : Base → ℝ} (hW : Continuous W) (hpos : ∀ ξ : Sphere, 0 ≤ W ξ)
    (hmass : (∫ ξ : Sphere, W ξ ∂sigma)=1) : IsProbabilityMeasure (densityMeasure W) := by
  constructor
  have hi : Integrable (fun ξ : Sphere => W ξ) sigma := continuous_integrable (hW.comp continuous_subtype_val)
  rw [densityMeasure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hpos),hmass]
  norm_num

lemma densityMeasure_represents {W : Base → ℝ} (hW : Continuous W) (hpos : ∀ ξ : Sphere, 0 ≤ W ξ)
    (hmoment : ∀ p : MvPolynomial (Fin 2) ℂ,
      (∫ ξ : Sphere, MvPolynomial.eval (fun i => (ξ:Base) i) p*(W ξ:ℂ) ∂sigma)=MvPolynomial.eval (fun _ => 0) p) :
    Represents (densityMeasure W) := by
  intro p
  rw [densityMeasure_integral hW hpos]
  simpa only [Complex.real_smul,mul_comm] using hmoment p

lemma density_orbit_mean {Q : ℕ} (hQ : 2 ≤ Q) {R E : ℝ} (hER : E < R)
    {f b : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b)
    (htail : ∀ y, E ≤ y → f y=0 ∧ b y=0) (P : ℕ → Finset Sphere) (j : ℕ) :
    OrbitMeanOne (density Q R f b P j) := by
  classical
  have hq : 0 < Q := by omega
  induction j with
  | zero => exact orbitMean_one
  | succ j ih =>
    intro ξ
    have hw := density_smooth hq hER hf hb htail P j
    have hi : Integrable (fun z : Circle => density Q R f b P j ((z:ℂ) • (ξ:Base))) circleMeasure := by
      apply compact_continuous_integrable
      exact hw.continuous.comp ((continuous_subtype_val : Continuous (fun z : Circle => (z:ℂ))).smul continuous_const)
    have hic : ∀ p ∈ P (Q^(j+1)), Integrable (fun z : Circle => densityCorrection (Q^(j+1)) R f b (density Q R f b P j) p ((z:ℂ) • (ξ:Base))) circleMeasure := by
      intro p hp
      apply compact_continuous_integrable
      exact (densityCorrection_smooth (pow_pos hq _) hER hf hb hw htail p).continuous.comp ((continuous_subtype_val : Continuous (fun z : Circle => (z:ℂ))).smul continuous_const)
    simp only [density]
    rw [integral_add hi (integrable_finsetSum _ hic),integral_finsetSum _ hic,ih ξ]
    have hz : (∑ p ∈ P (Q^(j+1)), ∫ z : Circle, densityCorrection (Q^(j+1)) R f b (density Q R f b P j) p ((z:ℂ) • (ξ:Base)) ∂circleMeasure)=0 := by
      apply Finset.sum_eq_zero
      intro p hp
      exact densityCorrection_orbit_zero (hw.differentiable (by simp)) (density_bandwidth hq hER hf hb htail P j) (densityBandwidth_lt hQ j) R f b p ξ
    rw [hz,add_zero]

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BasePatches
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff ENNReal Pointwise
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma peakPatch_norm_pos {k : ℕ} {R : ℝ} {p ξ : Sphere} (hξ : ξ ∈ peakPatch k R p) :
    0 < ‖bracket (ξ:Base) (p:Base)‖ := lt_trans (Real.exp_pos _) hξ

lemma patchHeight_nonneg (k : ℕ) (p ξ : Sphere) : 0 ≤ patchHeight k p (ξ:Base) := by
  unfold patchHeight
  exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (Nat.cast_nonneg k)) (Real.log_nonpos (norm_nonneg _) (bracket_norm_le_one ξ p))

lemma peakPatch_iff_height {k : ℕ} (hk : 0 < k) (R : ℝ) (p ξ : Sphere) :
    ξ ∈ peakPatch k R p ↔ 0 < ‖bracket (ξ:Base) (p:Base)‖ ∧ patchHeight k p (ξ:Base) < R := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  constructor
  · intro hξ
    refine ⟨peakPatch_norm_pos hξ,?_⟩
    have hh := Real.log_lt_log (Real.exp_pos (-R/k)) hξ
    rw [Real.log_exp] at hh
    unfold patchHeight
    have hm := (div_lt_iff₀ hk0).mp hh
    linarith
  · rintro ⟨hn,hy⟩
    apply (Real.log_lt_log_iff (Real.exp_pos _) hn).mp
    rw [Real.log_exp]
    apply (div_lt_iff₀ hk0).mpr
    unfold patchHeight at hy
    linarith

lemma peakPatch_radius {k : ℕ} (hk : 0 < k) {R : ℝ} (hR : 0 < R)
    {p ξ : Sphere} (hξ : ξ ∈ peakPatch k R p) :
    Real.sqrt (k:ℝ)*projectiveDistance ξ p < Real.sqrt (2*R) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hnorm := peakPatch_norm_pos hξ
  have he : Real.exp (-R/k)^2 = Real.exp (-2*R/k) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hsq : Real.exp (-2*R/k) < ‖bracket (ξ:Base) (p:Base)‖^2 := by
    rw [← he]
    have hp : Real.exp (-R/k) < ‖bracket (ξ:Base) (p:Base)‖ := hξ
    exact sq_lt_sq₀ (Real.exp_pos _).le (norm_nonneg _) |>.mpr hp
  have hl := Real.one_sub_le_exp_neg (2*R/k)
  rw [← neg_div] at hl
  have hh2 : -(2*R) / (k:ℝ) = -2*R/k := by ring
  rw [hh2] at hl
  have hd := projectiveDistance_sq ξ p
  have hmul : (k:ℝ)*projectiveDistance ξ p^2 < 2*R := by
    have hh : projectiveDistance ξ p^2 < 2*R/k := by linarith
    simpa only [mul_comm] using (lt_div_iff₀ hk0).mp hh
  have hkn := Real.sq_sqrt hk0.le
  have hrn := Real.sq_sqrt (show 0 ≤ 2*R by positivity)
  have hd0 := projectiveDistance_nonneg ξ p
  have hk1 := Real.sqrt_nonneg (k:ℝ)
  have hr1 := Real.sqrt_nonneg (2*R)
  have heq : (Real.sqrt (k:ℝ)*projectiveDistance ξ p)^2 = (k:ℝ)*projectiveDistance ξ p^2 := by rw [mul_pow,hkn]
  nlinarith

lemma peakPatch_disjoint {k : ℕ} (hk : 0 < k) {R D : ℝ} (hR : 0 < R)
    (hD : 2*Real.sqrt (2*R) < D) {P : Finset Sphere}
    (hP : ProjectivelySeparated (D/Real.sqrt k) P) :
    (P : Set Sphere).PairwiseDisjoint (peakPatch k R) := by
  intro p hp q hq hpq
  apply Set.disjoint_left.mpr
  intro ξ hξp hξq
  have hs : 0 < Real.sqrt (k:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hk)
  have hp1 := peakPatch_radius hk hR hξp
  have hq1 := peakPatch_radius hk hR hξq
  have hh := hP p hp q hq hpq
  have ht := projectiveDistance_triangle p ξ q
  rw [projectiveDistance_symm p ξ] at ht
  have hm := mul_le_mul_of_nonneg_left ht hs.le
  have hd := (div_le_iff₀ hs).mp hh
  linarith

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BasePhaseDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff ENNReal
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma norm_derivative_complex {c : ℝ → ℂ} {v : ℂ} {t : ℝ}
    (hc : HasDerivAt c v t) (h0 : c t ≠ 0) :
    HasDerivAt (fun s => ‖c s‖) ((v/(c t)).re*‖c t‖) t := by
  have hn : ‖c t‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  have hh := hc.norm_sq.sqrt (pow_ne_zero 2 hn)
  have he : (fun s => Real.sqrt (‖c s‖^2)) = fun s => ‖c s‖ := by funext s; exact Real.sqrt_sq (norm_nonneg _)
  rw [he] at hh
  convert! hh using 1
  rw [Real.sqrt_sq (norm_nonneg _)]
  simp only [Complex.div_re,Complex.normSq_eq_norm_sq,real_inner_eq_re_inner ℂ,RCLike.inner_apply]
  field_simp
  change _ = (v*star (c t)).re
  simp [Complex.mul_re]

lemma phase_derivative_complex {c : ℝ → ℂ} {v : ℂ} {t : ℝ}
    (hc : HasDerivAt c v t) (h0 : c t ≠ 0) :
    HasDerivAt (fun s => c s/(‖c s‖:ℂ))
      ((Complex.I*(v/(c t)).im)*(c t/(‖c t‖:ℂ))) t := by
  have hn : (‖c t‖:ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h0
  have hr := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (norm_derivative_complex hc h0)
  have hh := hc.div hr hn
  convert! hh using 1
  simp only [Function.comp_def,Complex.ofRealCLM_apply,Complex.ofReal_mul]
  have hsplit : v/(c t) = ((v/(c t)).re:ℂ)+Complex.I*((v/(c t)).im:ℂ) := by
    apply Complex.ext <;> simp
  have hv : v = (((v/(c t)).re:ℂ)+Complex.I*((v/(c t)).im:ℂ))*c t := by rw [← hsplit,div_mul_cancel₀ _ h0]
  nth_rewrite 2 [hv]
  field_simp
  ring

lemma centralPoint_curve_derivative (p : Sphere) {γ : ℝ → Base} {v : Base} {t : ℝ}
    (hγ : HasDerivAt γ v t) (h0 : bracket (γ t) (p:Base) ≠ 0) :
    HasDerivAt (fun s => centralPoint p (γ s))
      ((bracket v (p:Base)/bracket (γ t) (p:Base)).im • (Complex.I • centralPoint p (γ t))) t := by
  have hc : HasDerivAt (fun s => bracket (γ s) (p:Base)) (bracket v (p:Base)) t := by
    exact (((innerSL ℂ (p:Base)).restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt t hγ
  convert! (phase_derivative_complex hc h0).smul_const (p:Base) using 1
  rw [← Complex.coe_smul]
  simp only [centralPoint,smul_smul]
  congr 1
  ring

lemma densityHeight_curve_derivative (k : ℕ) (p : Sphere) {γ : ℝ → Base} {v : Base} {t : ℝ}
    (hγ : HasDerivAt γ v t) (h0 : bracket (γ t) (p:Base) ≠ 0) :
    HasDerivAt (fun s => densityHeight k p (γ s))
      (-(k:ℝ)*(bracket v (p:Base)/bracket (γ t) (p:Base)).re) t := by
  have hc : HasDerivAt (fun s => bracket (γ s) (p:Base)) (bracket v (p:Base)) t := by
    exact (((innerSL ℂ (p:Base)).restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt t hγ
  convert! ((norm_derivative_complex hc h0).log (norm_ne_zero_iff.mpr h0)).const_mul (-(k:ℝ)) using 1
  simp [mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr h0)]

lemma centralValue_curve_derivative {W : Base → ℝ} (hW : Differentiable ℝ W)
    (p : Sphere) {γ : ℝ → Base} {v : Base} {t : ℝ}
    (hγ : HasDerivAt γ v t) (h0 : bracket (γ t) (p:Base) ≠ 0) :
    HasDerivAt (fun s => W (centralPoint p (γ s)))
      ((bracket v (p:Base)/bracket (γ t) (p:Base)).im * phaseDerivative W (centralPoint p (γ t))) t := by
  convert! (hW _).hasFDerivAt.comp_hasDerivAt t (centralPoint_curve_derivative p hγ h0) using 1
  simp only [map_smul,smul_eq_mul,phaseDerivative]

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseHorizontalGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff ENNReal
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma orthogonal_residual_norm (ξ p : Sphere) :
    ‖(p:Base)-bracket (p:Base) (ξ:Base) • (ξ:Base)‖ = projectiveDistance ξ p := by
  apply (sq_eq_sq₀ (norm_nonneg _) (projectiveDistance_nonneg _ _)).mp
  rw [norm_sub_sq (𝕜 := ℂ),norm_smul,sphere_norm,sphere_norm,mul_one,projectiveDistance_sq]
  simp only [bracket,inner_smul_right]
  have hconj : inner ℂ (ξ:Base) (p:Base) = star (inner ℂ (p:Base) (ξ:Base)) := (inner_conj_symm _ _).symm
  have he : (inner ℂ (ξ:Base) (p:Base)*(inner ℂ (p:Base) (ξ:Base))).re = ‖inner ℂ (p:Base) (ξ:Base)‖^2 := by
    rw [hconj]
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.star_def,Complex.mul_re,Complex.conj_re,Complex.conj_im,Complex.normSq_apply]
    ring
  have hn : ‖inner ℂ (ξ:Base) (p:Base)‖=‖inner ℂ (p:Base) (ξ:Base)‖ := norm_inner_symm _ _
  change 1^2-2*(inner ℂ (ξ:Base) (p:Base)*inner ℂ (p:Base) (ξ:Base)).re+_=_
  rw [he,hn]
  ring

lemma horizontal_bracket_bound (ξ p : Sphere) (v : Base) (hv : Horizontal ξ v) :
    ‖bracket v (p:Base)‖ ≤ projectiveDistance ξ p*‖v‖ := by
  have he : bracket v ((p:Base)-bracket (p:Base) (ξ:Base) • (ξ:Base)) = bracket v (p:Base) := by
    dsimp [bracket,Horizontal] at hv ⊢
    rw [inner_sub_left,inner_smul_left,hv,mul_zero,sub_zero]
  calc
    ‖bracket v (p:Base)‖ = ‖bracket v ((p:Base)-bracket (p:Base) (ξ:Base) • (ξ:Base))‖ := by rw [he]
    _ ≤ ‖(p:Base)-bracket (p:Base) (ξ:Base) • (ξ:Base)‖*‖v‖ := norm_inner_le_norm _ _
    _ = _ := by rw [orthogonal_residual_norm]

lemma patch_bracket_lower {k : ℕ} {R : ℝ} (hk : 0 < k) (hR : 0 ≤ R) (hkR : 2*R ≤ k)
    (p ξ : Sphere) (hξ : ξ ∈ peakPatch k R p) :
    (1:ℝ)/2 < ‖bracket (ξ:Base) (p:Base)‖ := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have radiusBound : |R/k| ≤ (1:ℝ)/2 := by
    rw [abs_of_nonneg (div_nonneg hR hk0.le)]
    exact (div_le_iff₀ hk0).mpr (by linarith)
  have hh : -(1:ℝ)/2 ≤ -R/k := by
    simpa only [neg_div] using neg_le_neg ((le_abs_self (R/k)).trans radiusBound)
  have he := Real.add_one_le_exp (-R/k)
  have hc := hξ
  change Real.exp (-R/k) < ‖bracket (ξ:Base) (p:Base)‖ at hc
  linarith

lemma horizontal_patch_log_derivative_bound {k : ℕ} {R : ℝ} (hk : 0 < k) (hR : 0 < R)
    (hkR : 2*R ≤ k) (p ξ : Sphere) (hξ : ξ ∈ peakPatch k R p)
    (v : Base) (hv : Horizontal ξ v) :
    ‖bracket v (p:Base)/bracket (ξ:Base) (p:Base)‖ ≤ 2*Real.sqrt (2*R/(k:ℝ))*‖v‖ := by
  have hn := patch_bracket_lower hk hR.le hkR p ξ hξ
  have hd0 := peakPatch_radius hk hR hξ
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hd : projectiveDistance ξ p < Real.sqrt (2*R/(k:ℝ)) := by
    rw [Real.sqrt_div (by positivity)]
    apply (lt_div_iff₀ (Real.sqrt_pos.mpr hk0)).mpr
    linarith
  rw [norm_div]
  apply (div_le_iff₀ (by linarith : 0 < ‖bracket (ξ:Base) (p:Base)‖)).mpr
  have hb := horizontal_bracket_bound ξ p v hv
  have hm := mul_le_mul_of_nonneg_right hd.le (norm_nonneg v)
  have hnn : 0 ≤ Real.sqrt (2*R/(k:ℝ))*‖v‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseOrbitGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
namespace PinchedHartogs.BaseConstruction

lemma positive_log_growth {f : ℝ → ℝ} (hf : Differentiable ℝ f) (hp : ∀ t, 0 < f t)
    {K : ℝ} (hK : 0 ≤ K) (hd : ∀ t, |deriv f t| ≤ K*f t) (θ u : ℝ) :
    f (θ+u) ≤ Real.exp (K*|u|)*f θ := by
  let bound : NNReal := ⟨K,hK⟩
  have hlog : ∀ t, HasDerivAt (fun t => Real.log (f t)) (deriv f t/f t) t :=
    fun t => (hf t).hasDerivAt.log (hp t).ne'
  have hbound : ∀ t ∈ (univ : Set ℝ), ‖deriv (fun t => Real.log (f t)) t‖ ≤ bound := by
    intro t ht
    rw [(hlog t).deriv,Real.norm_eq_abs,abs_div,abs_of_pos (hp t)]
    exact (div_le_iff₀ (hp t)).mpr (hd t)
  have hh := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun t _ => (hlog t).differentiableAt) hbound (mem_univ θ) (mem_univ (θ+u))
  simp only [add_sub_cancel_left,Real.norm_eq_abs] at hh
  change |Real.log (f (θ+u))-Real.log (f θ)| ≤ K*|u| at hh
  have hb : Real.log (f (θ+u)) ≤ K*|u|+Real.log (f θ) := by linarith [le_abs_self (Real.log (f (θ+u))-Real.log (f θ))]
  have he := Real.exp_le_exp.mpr hb
  simpa only [Real.exp_add,Real.exp_log (hp (θ+u)),Real.exp_log (hp θ)] using he

lemma orbit_growth_nat {Q n N : ℕ} (hQ : 2 ≤ Q) {c K : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hK : 0 ≤ K) (hN : 2/c ≤ (2:ℝ)^N) (W : ℕ → ℝ → ℝ)
    (hzero : W 0 = fun _ => 1)
    (hpos : ∀ j ≤ n, ∀ θ, 0 < W j θ)
    (hdiff : ∀ j ≤ n, Differentiable ℝ (W j))
    (hder : ∀ j ≤ n, ∀ θ, |deriv (W j) θ| ≤ K*Q^j*W j θ)
    (hstep : ∀ j, j < n → ∀ θ, c*W j θ ≤ W (j+1) θ ∧ W (j+1) θ ≤ 2*W j θ)
    (θ u : ℝ) :
    W n (θ+u) ≤ Real.exp K*(2/c)*(max 1 ((Q:ℝ)^n*|u|))^N*W n θ := by
  have hQ0 : (0:ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hQ2 : (2:ℝ) ≤ Q := by exact_mod_cast hQ
  have hR : 1 ≤ 2/c := (le_div_iff₀ hc).mpr (by linarith)
  have hRQ : 2/c ≤ (Q:ℝ)^N := hN.trans (pow_le_pow_left₀ (by norm_num) hQ2 N)
  have hexp : 1 ≤ Real.exp K := Real.one_le_exp hK
  have hall : ∀ j ≤ n, W j (θ+u) ≤ Real.exp K*(2/c)*(max 1 ((Q:ℝ)^j*|u|))^N*W j θ := by
    intro j hj
    induction j with
    | zero =>
      rw [hzero]
      have hm : (1:ℝ) ≤ (max 1 ((Q:ℝ)^0*|u|))^N := one_le_pow₀ (le_max_left _ _)
      linarith [mul_le_mul_of_nonneg_left hR (Real.exp_pos K).le,
        mul_le_mul_of_nonneg_left hm (show 0 ≤ Real.exp K*(2/c) by positivity)]
    | succ j ih =>
      have hjn : j ≤ n := by omega
      have hjlt : j < n := by omega
      have hsθ := (hstep j hjlt θ).1
      have hsu := (hstep j hjlt (θ+u)).2
      have hwn : 0 < W (j+1) θ := hpos _ hj θ
      have hwp : 0 < W j θ := hpos _ hjn θ
      have hratio : W j θ ≤ (1/c)*W (j+1) θ := by
        have hh : W j θ ≤ W (j+1) θ / c := (le_div_iff₀ hc).mpr (by linarith)
        calc
          W j θ ≤ W (j+1) θ/c := hh
          _ = (1/c)*W (j+1) θ := by ring
      by_cases hsmall : (Q:ℝ)^j*|u| ≤ 1
      · have hg := positive_log_growth (hdiff j hjn) (hpos j hjn)
          (mul_nonneg hK (pow_nonneg hQ0.le _)) (hder j hjn) θ u
        have he : Real.exp (K*(Q:ℝ)^j*|u|) ≤ Real.exp K := by
          apply Real.exp_le_exp.mpr
          nlinarith
        have hg1 : W j (θ+u) ≤ Real.exp K*W j θ := hg.trans (mul_le_mul_of_nonneg_right he hwp.le)
        have hg2 : W (j+1) (θ+u) ≤ Real.exp K*(2/c)*W (j+1) θ := by
          have hm := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 2*Real.exp K by positivity)
          simp only [div_eq_mul_inv,one_mul] at hm ⊢
          linarith
        have hm : 1 ≤ (max 1 ((Q:ℝ)^(j+1)*|u|))^N := one_le_pow₀ (le_max_left _ _)
        have hmul := mul_le_mul_of_nonneg_left hm (show 0 ≤ Real.exp K*(2/c)*W (j+1) θ by positivity)
        linarith
      · have hpj : 1 < (Q:ℝ)^j*|u| := lt_of_not_ge hsmall
        have hcur : 1 ≤ (Q:ℝ)^(j+1)*|u| := by
          rw [pow_succ]
          nlinarith
        have hp : 0 ≤ ((Q:ℝ)^j*|u|)^N := pow_nonneg (by positivity) _
        have hi := ih hjn
        rw [max_eq_right hpj.le] at hi
        rw [max_eq_right hcur]
        have heq : ((Q:ℝ)^(j+1)*|u|)^N = (Q:ℝ)^N*((Q:ℝ)^j*|u|)^N := by
          rw [show (Q:ℝ)^(j+1)*|u| = (Q:ℝ)*((Q:ℝ)^j*|u|) by rw [pow_succ]; ring,mul_pow]
        rw [heq]
        have hm := mul_le_mul_of_nonneg_right hRQ hp
        have hm2 := mul_le_mul_of_nonneg_right hm (show 0 ≤ Real.exp K*(2/c)*W (j+1) θ by positivity)
        have hm3 := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 2*Real.exp K*(2/c)*((Q:ℝ)^j*|u|)^N by positivity)
        simp only [div_eq_mul_inv,one_mul] at hi hm2 hm3 ⊢
        linarith
  exact hall n le_rfl

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseHorizontalArc
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open scoped ContDiff
open Set Filter Topology
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma horizontalArc_derivative (q d : Base) (t : ℝ) :
    HasDerivAt (horizontalArc q d) (horizontalArcVelocity q d t) t := by
  have hpos : 0 < 1+t^2*‖d‖^2 := by positivity
  have hh := (((((hasDerivAt_id t).pow 2).mul_const (‖d‖^2)).const_add 1).sqrt hpos.ne').inv (Real.sqrt_ne_zero'.mpr hpos)
  have hv := ((hasDerivAt_id t).smul_const d).const_add q
  convert! hh.smul hv using 1
  simp only [horizontalArcVelocity,Pi.pow_apply,id,one_smul]
  rw [add_comm]
  congr 1
  congr 1
  field_simp
  ring

lemma horizontalArc_norm (q : Sphere) (d : Base) (hd : bracket d (q:Base)=0) (t : ℝ) :
    ‖horizontalArc (q:Base) d t‖=1 := by
  have hpos : 0 < 1+t^2*‖d‖^2 := by positivity
  have hn : ‖(q:Base)+t • d‖^2=1+t^2*‖d‖^2 := by
    rw [norm_add_sq (𝕜 := ℂ),sphere_norm,norm_smul,Real.norm_eq_abs, mul_pow,sq_abs]
    have hinner : inner ℂ (q:Base) (t • d) = 0 := by
      rw [← Complex.coe_smul,inner_smul_right]
      change (t:ℂ)*bracket d (q:Base)=0
      rw [hd,mul_zero]
    rw [hinner]
    simp
  unfold horizontalArc
  rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (Real.sqrt_nonneg _)]
  have he : ‖(q:Base)+t • d‖=Real.sqrt (1+t^2*‖d‖^2) := by
    rw [← hn,Real.sqrt_sq (norm_nonneg _)]
  rw [he,inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr hpos)]

lemma horizontalArc_horizontal (q : Sphere) (d : Base) (hd : bracket d (q:Base)=0) (t : ℝ) :
    bracket (horizontalArcVelocity q d t) (horizontalArc q d t)=0 := by
  have hpos : 0 < 1+t^2*‖d‖^2 := by positivity
  have hroot : Real.sqrt (1+t^2*‖d‖^2) ≠ 0 := Real.sqrt_ne_zero'.mpr hpos
  have hsq := Real.sq_sqrt hpos.le
  have hqd : inner ℂ (q:Base) d=0 := hd
  have hdq : inner ℂ d (q:Base)=0 := by rw [← inner_conj_symm (d) (q:Base),hqd]; simp
  have hqq : inner ℂ (q:Base) (q:Base)=1 := by rw [inner_self_eq_norm_sq_to_K,sphere_norm]; norm_num
  have hdd : inner ℂ d d=(‖d‖^2:ℝ) := by simp [inner_self_eq_norm_sq_to_K]
  simp only [bracket,horizontalArc,horizontalArcVelocity,← Complex.coe_smul,
    inner_smul_left,inner_smul_right,inner_add_left,inner_add_right,hqd,hdq,hqq,hdd]
  push_cast
  simp only [map_inv₀,Complex.conj_ofReal,mul_zero,add_zero,zero_add,mul_one]
  have hrootC : (Real.sqrt (1+t^2*‖d‖^2):ℂ) ≠ 0 := by exact_mod_cast hroot
  have hsqC : (Real.sqrt (1+t^2*‖d‖^2):ℂ)^2=1+(t:ℂ)^2*(‖d‖:ℂ)^2 := by exact_mod_cast hsq
  field_simp [hrootC]
  rw [hsqC]
  ring

lemma horizontalArc_velocity_norm (q : Sphere) (d : Base) (hd : bracket d (q:Base)=0) (t : ℝ) :
    ‖horizontalArcVelocity q d t‖ ≤ ‖d‖ := by
  let r := Real.sqrt (1+t^2*‖d‖^2)
  have hpos : 0 < 1+t^2*‖d‖^2 := by positivity
  have hr : 0 < r := Real.sqrt_pos.mpr hpos
  have hrsq : r^2=1+t^2*‖d‖^2 := Real.sq_sqrt hpos.le
  have he : horizontalArcVelocity q d t = (-t*‖d‖^2/r^3) • (q:Base)+(1/r^3) • d := by
    unfold horizontalArcVelocity
    dsimp only [r] at *
    rw [smul_add,smul_smul,add_assoc,← add_smul]
    congr 1
    · congr 1; ring
    · congr 1
      field_simp
      linarith [Real.sq_sqrt hpos.le]
  have hn : ‖horizontalArcVelocity q d t‖^2=‖d‖^2/r^4 := by
    rw [he,norm_add_sq (𝕜 := ℂ),norm_smul,norm_smul,sphere_norm,mul_one,Real.norm_eq_abs,Real.norm_eq_abs,mul_pow,sq_abs,sq_abs]
    have hi : inner ℂ ((-t*‖d‖^2/r^3) • (q:Base)) ((1/r^3) • d)=0 := by
      rw [← Complex.coe_smul,← Complex.coe_smul,inner_smul_left,inner_smul_right]
      change _*(_*bracket d (q:Base))=0
      rw [hd,mul_zero,mul_zero]
    rw [hi]
    simp only [map_zero,mul_zero,add_zero]
    field_simp
    nlinarith [sq_nonneg ‖d‖]
  have hr1 : 1 ≤ r := by nlinarith [sq_nonneg t,sq_nonneg ‖d‖]
  have hh : ‖d‖^2/r^4 ≤ ‖d‖^2 := div_le_self (sq_nonneg _) (one_le_pow₀ hr1)
  have : ‖horizontalArcVelocity q d t‖^2 ≤ ‖d‖^2 := hn.trans_le hh
  nlinarith [norm_nonneg d,norm_nonneg (horizontalArcVelocity q d t)]

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseCentralComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma horizontalArc_reaches {r : ℝ} (hr : 0 < r) (q d ξ : Base)
    (hn : r^2+‖d‖^2=1) (he : ξ=r • q+d) : horizontalArc q d (1/r)=ξ := by
  have hh : Real.sqrt (1+(1/r)^2*‖d‖^2)=1/r := by
    apply Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity) |>.mpr
    field_simp
    linarith
  unfold horizontalArc
  rw [hh]
  simp only [one_div,inv_inv,smul_add,smul_smul]
  rw [mul_inv_cancel₀ hr.ne',one_smul]
  exact he.symm

lemma horizontal_growth {W : Base → ℝ} (hW : Differentiable ℝ W)
    (hp : ∀ ξ : Sphere, 0 < W ξ) {H : ℝ} (hH : 0 ≤ H) (hd : HorizontalBound W H)
    (q : Sphere) (d : Base) (hq : bracket d (q:Base)=0) (t : ℝ) :
    W (horizontalArc q d t) ≤ Real.exp (H*‖d‖*|t|)*W q ∧
    W q ≤ Real.exp (H*‖d‖*|t|)*W (horizontalArc q d t) := by
  let γ := horizontalArc (q:Base) d
  let f := fun u => W (γ u)
  have hg : ∀ u, HasDerivAt γ (horizontalArcVelocity q d u) u := horizontalArc_derivative _ _
  have hsp : ∀ u, γ u ∈ Sphere := fun u => by
    simpa only [Metric.mem_sphere,dist_zero_right] using horizontalArc_norm q d hq u
  have hfp : ∀ u, 0 < f u := fun u => hp ⟨γ u,hsp u⟩
  have hfd : ∀ u, HasDerivAt f (fderiv ℝ W (γ u) (horizontalArcVelocity q d u)) u :=
    fun u => (hW _).hasFDerivAt.comp_hasDerivAt u (hg u)
  have hfb : ∀ u, |deriv f u| ≤ (H*‖d‖)*f u := by
    intro u
    rw [(hfd u).deriv]
    have hh := hd ⟨γ u,hsp u⟩ (horizontalArcVelocity q d u) (horizontalArc_horizontal q d hq u)
    simpa only [Complex.star_def,Complex.ofReal_pow] using hh.trans (by
      apply mul_le_mul_of_nonneg_right _ (hfp u).le
      exact mul_le_mul_of_nonneg_left (horizontalArc_velocity_norm q d hq u) hH)
  have hf0 : f 0=W q := by simp [f,γ,horizontalArc]
  have hforward := positive_log_growth (fun u => (hfd u).differentiableAt) hfp (mul_nonneg hH (norm_nonneg _)) hfb 0 t
  have hback := positive_log_growth (fun u => (hfd u).differentiableAt) hfp (mul_nonneg hH (norm_nonneg _)) hfb t (-t)
  simp only [zero_add] at hforward
  simp only [add_neg_cancel,abs_neg] at hback
  rw [hf0] at hforward hback
  exact ⟨hforward,hback⟩

lemma central_residual (p ξ : Sphere) (h0 : bracket (ξ:Base) (p:Base) ≠ 0) :
    let q := centralPoint p ξ
    let r := ‖bracket (ξ:Base) (p:Base)‖
    let d := (ξ:Base)-r • q
    bracket d q=0 ∧ r^2+‖d‖^2=1 ∧ ‖d‖=projectiveDistance ξ p := by
  dsimp only
  let c := bracket (ξ:Base) (p:Base)
  have hr : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  have hc : (‖c‖:ℂ) ≠ 0 := by exact_mod_cast hr
  have hq : bracket (ξ:Base) (centralPoint p ξ)=(‖c‖:ℂ) := by
    simp only [centralPoint,bracket,inner_smul_left]
    change star (c/(‖c‖:ℂ))*c=(‖c‖:ℂ)
    rw [star_div₀,Complex.star_def,Complex.conj_ofReal]
    have hh : star c*c=(‖c‖^2:ℝ) := by
      simpa only [Complex.star_def,Complex.ofReal_pow] using Complex.conj_mul' c
    field_simp
    simpa only [Complex.star_def,Complex.ofReal_pow] using hh
  have hqq : bracket (centralPoint p ξ) (centralPoint p ξ)=1 := by
    simp only [bracket,inner_self_eq_norm_sq_to_K,centralPoint_norm p h0]
    norm_num
  have hd : bracket ((ξ:Base)-‖c‖ • centralPoint p ξ) (centralPoint p ξ)=0 := by
    rw [bracket,inner_sub_right,← Complex.coe_smul,inner_smul_right]
    change bracket (ξ:Base) (centralPoint p ξ)-(‖c‖:ℂ)*bracket (centralPoint p ξ) (centralPoint p ξ)=0
    rw [hq,hqq,mul_one,sub_self]
  have hn : ‖(ξ:Base)-‖c‖ • centralPoint p ξ‖^2=1-‖c‖^2 := by
    rw [norm_sub_sq (𝕜 := ℂ),sphere_norm,norm_smul,centralPoint_norm p h0,mul_one,Real.norm_eq_abs,abs_norm]
    have hi : inner ℂ (ξ:Base) (‖c‖ • centralPoint p ξ)=(‖c‖^2:ℝ) := by
      rw [← Complex.coe_smul,inner_smul_right,← inner_conj_symm]
      change (‖c‖:ℂ)*star (bracket (ξ:Base) (centralPoint p ξ))=_
      rw [hq,Complex.star_def,Complex.conj_ofReal]
      push_cast; ring
    rw [hi]
    change 1^2-2*‖c‖^2+‖c‖^2=1-‖c‖^2
    ring
  refine ⟨hd,by linarith,?_⟩
  apply (sq_eq_sq₀ (norm_nonneg _) (projectiveDistance_nonneg _ _)).mp
  rw [hn,projectiveDistance_sq]

lemma central_comparison {W : Base → ℝ} (hW : Differentiable ℝ W)
    (hp : ∀ ξ : Sphere, 0 < W ξ) {H : ℝ} (hH : 0 ≤ H) (hd : HorizontalBound W H)
    {k : ℕ} {R : ℝ} (hk : 0 < k) (hR : 0 < R) (hkR : 2*R ≤ k)
    (p ξ : Sphere) (hξ : ξ ∈ peakPatch k R p) :
    W (centralPoint p ξ) ≤ Real.exp (H*(2*Real.sqrt (2*R)/Real.sqrt (k:ℝ)))*W ξ ∧
    W ξ ≤ Real.exp (H*(2*Real.sqrt (2*R)/Real.sqrt (k:ℝ)))*W (centralPoint p ξ) := by
  have hc : bracket (ξ:Base) (p:Base) ≠ 0 := norm_pos_iff.mp (peakPatch_norm_pos hξ)
  let q : Sphere := ⟨centralPoint p ξ,by simpa only [Metric.mem_sphere,dist_zero_right] using centralPoint_norm p hc⟩
  let r := ‖bracket (ξ:Base) (p:Base)‖
  let d := (ξ:Base)-r • (q:Base)
  obtain ⟨hdq,hn,hdn⟩ := central_residual p ξ hc
  change bracket d (q:Base)=0 at hdq
  change r^2+‖d‖^2=1 at hn
  change ‖d‖=projectiveDistance ξ p at hdn
  have hr : 0 < r := peakPatch_norm_pos hξ
  have he : horizontalArc q d (1/r)=(ξ:Base) := horizontalArc_reaches hr q d ξ hn (by dsimp [d]; abel)
  obtain ⟨h1,h2⟩ := horizontal_growth hW hp hH hd q d hdq (1/r)
  rw [he] at h1 h2
  have hlen : ‖d‖*|1/r| ≤ 2*Real.sqrt (2*R)/Real.sqrt (k:ℝ) := by
    rw [hdn,abs_of_pos (one_div_pos.mpr hr)]
    have hr2 : 1/2 < r := patch_bracket_lower hk hR.le hkR p ξ hξ
    have hk0 : (0:ℝ) < k := by exact_mod_cast hk
    apply (le_div_iff₀ (Real.sqrt_pos.mpr hk0)).mpr
    have hpdist := peakPatch_radius hk hR hξ
    have hrinv : 1/r ≤ 2 := (div_le_iff₀ hr).mpr (by linarith)
    have hm := mul_le_mul_of_nonneg_left hrinv (mul_nonneg (projectiveDistance_nonneg ξ p) (Real.sqrt_nonneg (k:ℝ)))
    linarith
  have hex : Real.exp (H*‖d‖*|1/r|) ≤ Real.exp (H*(2*Real.sqrt (2*R)/Real.sqrt (k:ℝ))) :=
    Real.exp_le_exp.mpr (by nlinarith)
  exact ⟨h2.trans (mul_le_mul_of_nonneg_right hex (hp ξ).le),h1.trans (mul_le_mul_of_nonneg_right hex (hp q).le)⟩

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseCorrectionEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma densityCorrectionRaw_model {k : ℕ} (hk : 0 < k) (f b : ℝ → ℝ) (W : Base → ℝ)
    (p : Sphere) {ξ : Base} (hξ : bracket ξ (p:Base) ≠ 0) :
    densityCorrectionRaw k f b W p ξ = correctionModel k f b (densityHeight k p ξ)
      (W (centralPoint p ξ)) (phaseDerivative W (centralPoint p ξ))
      ((bracket ξ (p:Base)/(‖bracket ξ (p:Base)‖:ℂ))^k) := by
  have hk0 : (k:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have he : 2*densityHeight k p ξ/(k:ℝ) = -2*Real.log ‖bracket ξ (p:Base)‖ := by
    unfold densityHeight
    field_simp
  have hx : Real.exp (-2*Real.log ‖bracket ξ (p:Base)‖) = (‖bracket ξ (p:Base)‖^2)⁻¹ := by
    rw [show -2*Real.log ‖bracket ξ (p:Base)‖ = -(2*Real.log ‖bracket ξ (p:Base)‖) by ring,
      Real.exp_neg,show (2:ℝ) = (2:ℕ) by norm_num,
      Real.exp_nat_mul,Real.exp_log (norm_pos_iff.mpr hξ)]
  simp only [densityCorrectionRaw,correctionModel,he,hx]

lemma abs_sub_triangle (a b : ℝ) : |a-b| ≤ |a|+|b| := by
  simpa only [sub_eq_add_neg,abs_neg] using abs_add_le a (-b)

lemma correctionModel_derivative_bound {k D F B F₁ B₁ : ℝ} (hk : 1 ≤ k) (hD : 0 ≤ D)
    (hF : 0 ≤ F) (hB : 0 ≤ B) (hF₁ : 0 ≤ F₁) (hB₁ : 0 ≤ B₁)
    {f b y S T : ℝ → ℝ} {z : ℝ → ℂ} {t dy dS dT df db : ℝ} {dz : ℂ}
    (hy : HasDerivAt y dy t) (hS : HasDerivAt S dS t) (hT : HasDerivAt T dT t)
    (hz : HasDerivAt z dz t) (hf : HasDerivAt f df (y t)) (hb : HasDerivAt b db (y t))
    (hSp : 0 ≤ S t) (hyb : |dy| ≤ D) (hSb : |dS| ≤ D*S t) (hTb : |dT| ≤ D*k*S t)
    (hTv : |T t| ≤ k*S t) (hzv : ‖z t‖ ≤ 1) (hzb : ‖dz‖ ≤ D)
    (hfv : |f (y t)| ≤ F) (hbv : |b (y t)| ≤ B) (hfd : |df| ≤ F₁) (hbd : |db| ≤ B₁) :
    |deriv (fun u => correctionModel k f b (y u) (S u) (T u) (z u)) t| ≤
      D*Real.exp (2*y t/k)*S t*(4*(F+B)+F₁+B₁) := by
  have hk0 : 0 < k := by linarith
  have hzr : |(z t).re| ≤ 1 := (Complex.abs_re_le_norm _).trans hzv
  have hzi : |(z t).im| ≤ 1 := (Complex.abs_im_le_norm _).trans hzv
  have hdr : |dz.re| ≤ D := (Complex.abs_re_le_norm _).trans hzb
  have hdi : |dz.im| ≤ D := (Complex.abs_im_le_norm _).trans hzb
  have hbdv : |b (y t)/k| ≤ B/k := by rw [abs_div,abs_of_pos hk0]; exact div_le_div_of_nonneg_right hbv hk0.le
  have hbdd : |db*dy/k| ≤ B₁*D/k := by rw [abs_div,abs_mul,abs_of_pos hk0]; gcongr
  have hfdd : |df*dy| ≤ F₁*D := by rw [abs_mul]; gcongr
  let H := f (y t)*S t*(z t).re-b (y t)/k*T t*(z t).im
  let dH := (df*dy*S t+f (y t)*dS)*(z t).re+f (y t)*S t*dz.re-
    ((db*dy/k*T t+b (y t)/k*dT)*(z t).im+b (y t)/k*T t*dz.im)
  have hH : |H| ≤ (F+B)*S t := by
    unfold H
    calc
      _ ≤ |f (y t)| * |S t| * |(z t).re| + |b (y t)/k| * |T t| * |(z t).im| := by
        simpa only [abs_mul] using abs_sub_triangle (f (y t)*S t*(z t).re) (b (y t)/k*T t*(z t).im)
      _ ≤ F*S t*1+(B/k)*(k*S t)*1 := by rw [abs_of_nonneg hSp]; gcongr
      _ = _ := by field_simp
  have hdH : |dH| ≤ D*S t*(2*(F+B)+F₁+B₁) := by
    unfold dH
    calc
      _ ≤ (|df*dy| * |S t| + |f (y t)| * |dS|)*|(z t).re| + |f (y t)| * |S t| * |dz.re| +
          ((|db*dy/k| * |T t| + |b (y t)/k| * |dT|)*|(z t).im| + |b (y t)/k| * |T t| * |dz.im|) := by
        apply (abs_sub_triangle _ _).trans
        apply add_le_add
        · apply (abs_add_le _ _).trans
          rw [abs_mul,abs_mul,abs_mul]
          gcongr
          simpa [abs_mul] using abs_add_le (df*dy*S t) (f (y t)*dS)
        · apply (abs_add_le _ _).trans
          rw [abs_mul,abs_mul,abs_mul]
          gcongr
          simpa [abs_mul] using abs_add_le (db*dy/k*T t) (b (y t)/k*dT)
      _ ≤ (F₁*D*S t+F*(D*S t))*1+F*S t*D+
          ((B₁*D/k*(k*S t)+(B/k)*(D*k*S t))*1+(B/k)*(k*S t)*D) := by
        rw [abs_of_nonneg hSp]
        gcongr
      _ = _ := by field_simp; ring
  have hex := ((hy.const_mul 2).div_const k).exp
  have hzrD := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hz
  have hziD := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hz
  have hprod := hex.mul (((hf.comp t hy).mul hS |>.mul hzrD).sub (((hb.comp t hy).div_const k).mul hT |>.mul hziD))
  have hder : deriv (fun u => correctionModel k f b (y u) (S u) (T u) (z u)) t =
      Real.exp (2*y t/k)*(2*dy/k)*H+Real.exp (2*y t/k)*dH := by
    convert! hprod.deriv using 1
  rw [hder]
  have he0 : 0 ≤ Real.exp (2*y t/k) := (Real.exp_pos _).le
  have hdy : |2*dy/k| ≤ 2*D/k := by rw [abs_div,abs_mul,abs_of_pos hk0]; norm_num; gcongr
  calc
    _ ≤ Real.exp (2*y t/k)*(2*D/k)*((F+B)*S t)+Real.exp (2*y t/k)*(D*S t*(2*(F+B)+F₁+B₁)) := by
      apply (abs_add_le _ _).trans
      simp only [abs_mul,abs_of_nonneg he0]
      gcongr
    _ ≤ Real.exp (2*y t/k)*(2*D)*((F+B)*S t)+Real.exp (2*y t/k)*(D*S t*(2*(F+B)+F₁+B₁)) := by
      gcongr
      exact div_le_self (by positivity) hk
    _ = _ := by ring

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseCorrectionDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma densityCorrectionRaw_direction_bound {k : ℕ} (hk : 0 < k)
    {D F B F₁ B₁ : ℝ} (hD : 0 ≤ D) (hF : 0 ≤ F) (hB : 0 ≤ B) (hF₁ : 0 ≤ F₁) (hB₁ : 0 ≤ B₁)
    {f b : ℝ → ℝ} {W : Base → ℝ} (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b) (hW : ContDiff ℝ ∞ W)
    (p : Sphere) (ξ v : Base) (hξ : bracket ξ (p:Base) ≠ 0)
    (hdir : ‖bracket v (p:Base)/bracket ξ (p:Base)‖ ≤ D/k)
    (hS : 0 ≤ W (centralPoint p ξ))
    (hT : |phaseDerivative W (centralPoint p ξ)| ≤ k*W (centralPoint p ξ))
    (hTT : |phaseDerivative (phaseDerivative W) (centralPoint p ξ)| ≤ (k:ℝ)^2*W (centralPoint p ξ))
    (hfv : |f (densityHeight k p ξ)| ≤ F) (hbv : |b (densityHeight k p ξ)| ≤ B)
    (hfd : |deriv f (densityHeight k p ξ)| ≤ F₁) (hbd : |deriv b (densityHeight k p ξ)| ≤ B₁) :
    |fderiv ℝ (densityCorrectionRaw k f b W p) ξ v| ≤
      D*Real.exp (2*densityHeight k p ξ/k)*W (centralPoint p ξ)*(4*(F+B)+F₁+B₁) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  let γ : ℝ → Base := fun t => ξ+t • v
  have hγ : HasDerivAt γ v 0 := by simpa [γ] using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add ξ
  have hγ0 : γ 0=ξ := by simp [γ]
  let ratio := bracket v (p:Base)/bracket ξ (p:Base)
  have hr : |ratio.re| ≤ D/k := (Complex.abs_re_le_norm _).trans hdir
  have hi : |ratio.im| ≤ D/k := (Complex.abs_im_le_norm _).trans hdir
  have hy := densityHeight_curve_derivative k p hγ (by rwa [hγ0])
  have hSd := centralValue_curve_derivative (hW.differentiable (by simp)) p hγ (by rwa [hγ0])
  have hTd := centralValue_curve_derivative ((phaseDerivative_smooth hW).differentiable (by simp)) p hγ (by rwa [hγ0])
  rw [hγ0] at hy hSd hTd
  have hc : HasDerivAt (fun t => bracket (γ t) (p:Base)) (bracket v (p:Base)) 0 :=
    (((innerSL ℂ (p:Base)).restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt 0 hγ
  have hz := (phase_derivative_complex hc (by rwa [hγ0])).pow k
  rw [hγ0] at hz
  have hpn : ‖bracket ξ (p:Base)/(‖bracket ξ (p:Base)‖:ℂ)‖=1 := by
    simp [Complex.norm_real,div_self (norm_ne_zero_iff.mpr hξ)]
  have hzb : ‖(k:ℂ)*(bracket ξ (p:Base)/(‖bracket ξ (p:Base)‖:ℂ))^(k-1) *
      ((Complex.I*ratio.im)*(bracket ξ (p:Base)/(‖bracket ξ (p:Base)‖:ℂ)))‖ ≤ D := by
    simp only [norm_mul,norm_pow,hpn,one_pow,Complex.norm_natCast,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,one_mul,mul_one]
    exact (mul_le_mul_of_nonneg_left hi hk0.le).trans_eq (by field_simp)
  have hyb : |-(k:ℝ)*ratio.re| ≤ D := by
    rw [abs_mul,abs_neg,abs_of_pos hk0]
    exact (mul_le_mul_of_nonneg_left hr hk0.le).trans_eq (by field_simp)
  have hSb : |ratio.im*phaseDerivative W (centralPoint p ξ)| ≤ D*W (centralPoint p ξ) := by
    rw [abs_mul]
    calc
      _ ≤ (D/k)*(k*W (centralPoint p ξ)) := mul_le_mul hi hT (abs_nonneg _) (by positivity)
      _ = _ := by field_simp
  have hTb : |ratio.im*phaseDerivative (phaseDerivative W) (centralPoint p ξ)| ≤ D*k*W (centralPoint p ξ) := by
    rw [abs_mul]
    calc
      _ ≤ (D/k)*((k:ℝ)^2*W (centralPoint p ξ)) := mul_le_mul hi hTT (abs_nonneg _) (by positivity)
      _ = _ := by field_simp
  have hmodel := correctionModel_derivative_bound hk1 hD hF hB hF₁ hB₁ hy hSd hTd hz
    (hf.differentiable (by simp) _ |>.hasDerivAt) (hb.differentiable (by simp) _ |>.hasDerivAt)
    (by simpa only [hγ0] using hS) hyb (by simpa only [hγ0] using hSb)
    (by simpa only [hγ0] using hTb) (by simpa only [hγ0] using hT)
    (by simp only [Pi.pow_apply,hγ0,norm_pow,hpn,one_pow,le_refl]) hzb
    (by simpa only [hγ0] using hfv) (by simpa only [hγ0] using hbv)
    (by simpa only [hγ0] using hfd) (by simpa only [hγ0] using hbd)
  have hlocal : (fun t => densityCorrectionRaw k f b W p (γ t)) =ᶠ[𝓝 0]
      (fun t => correctionModel k f b (densityHeight k p (γ t))
        (W (centralPoint p (γ t))) (phaseDerivative W (centralPoint p (γ t)))
        ((bracket (γ t) (p:Base)/(‖bracket (γ t) (p:Base)‖:ℂ))^k)) := by
    have hne := (hc.continuousAt.eventually_ne (by rwa [hγ0] : bracket (γ 0) (p:Base) ≠ 0))
    filter_upwards [hne] with t ht
    exact densityCorrectionRaw_model hk f b W p ht
  have hraw := (densityCorrectionRaw_smoothAt k hf hb hW p hξ).differentiableAt (by simp)
  rw [← hγ0] at hraw
  have hdr := hraw.hasFDerivAt.comp_hasDerivAt 0 hγ
  rw [hγ0] at hdr
  simp only [Pi.pow_apply] at hmodel
  rw [← hlocal.deriv_eq] at hmodel
  change HasDerivAt (fun t => densityCorrectionRaw k f b W p (γ t)) _ 0 at hdr
  rw [hdr.deriv,hγ0] at hmodel
  exact hmodel

lemma densityCorrection_fderiv_zero {k : ℕ} (hk : 0 < k) {R E : ℝ} (hER : E < R)
    {f b : ℝ → ℝ} (htail : ∀ y, E ≤ y → f y=0 ∧ b y=0)
    (W : Base → ℝ) (p : Sphere) (ξ : Base) (hξ : ¬ Real.exp (-R/k)<‖bracket ξ (p:Base)‖) :
    fderiv ℝ (densityCorrection k R f b W p) ξ=0 := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hl : ‖bracket ξ (p:Base)‖ < Real.exp (-E/k) :=
    (le_of_not_gt hξ).trans_lt (Real.exp_lt_exp.mpr ((div_lt_div_iff_of_pos_right hk0).mpr (neg_lt_neg hER)))
  have he : densityCorrection k R f b W p =ᶠ[𝓝 ξ] fun _ => 0 := by
    have hc : Continuous (fun z : Base => ‖bracket z (p:Base)‖) := (bracket_analytic (p:Base)).continuous.norm
    filter_upwards [(isOpen_lt hc continuous_const).mem_nhds hl] with z hz
    exact densityCorrection_zero_low hk htail W p z hz.le
  rw [he.fderiv_eq]
  exact (hasFDerivAt_const (0:ℝ) ξ).fderiv

lemma densityCorrection_fderiv_raw {k : ℕ} {R : ℝ} (f b : ℝ → ℝ) (W : Base → ℝ)
    (p : Sphere) (ξ : Base) (hξ : Real.exp (-R/k)<‖bracket ξ (p:Base)‖) :
    fderiv ℝ (densityCorrection k R f b W p) ξ=fderiv ℝ (densityCorrectionRaw k f b W p) ξ := by
  have he : densityCorrection k R f b W p =ᶠ[𝓝 ξ] densityCorrectionRaw k f b W p := by
    have hc : Continuous (fun z : Base => ‖bracket z (p:Base)‖) := (bracket_analytic (p:Base)).continuous.norm
    filter_upwards [(isOpen_lt continuous_const hc).mem_nhds hξ] with z hz
    exact ite_eq_left hz
  exact he.fderiv_eq

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseDensityUpdate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler14283_1

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma disjoint_sum_abs_bound {α : Type uKahler14283_1} (s : Finset α) (active : α → Prop)
    (hu : ∀ p ∈ s, ∀ q ∈ s, active p → active q → p=q)
    (A : α → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hzero : ∀ p ∈ s, ¬ active p → A p=0)
    (hbound : ∀ p ∈ s, active p → |A p| ≤ B) :
    |∑ p ∈ s, A p| ≤ B := by
  classical
  by_cases ha : ∃ p ∈ s, active p
  · obtain ⟨p,hp,hap⟩ := ha
    rw [Finset.sum_eq_single p]
    · exact hbound p hp hap
    · intro q hq hqp
      exact hzero q hq (fun haq => hqp (hu q hq p hp haq hap))
    · exact fun h => (h hp).elim
  · have hz : ∑ p ∈ s, A p=0 := Finset.sum_eq_zero (fun p hp => hzero p hp (fun h => ha ⟨p,hp,h⟩))
    rw [hz,abs_zero]
    exact hB

lemma densityCorrectionRaw_value_bound {k : ℕ} (hk : 0 < k)
    (f b : ℝ → ℝ) (W : Base → ℝ) (p : Sphere) (ξ : Base) (hξ : bracket ξ (p:Base) ≠ 0)
    {F B r : ℝ} (hF : 0 ≤ F) (hB : 0 ≤ B) (hr : 0 ≤ r)
    (hS : 0 ≤ W (centralPoint p ξ))
    (hT : |phaseDerivative W (centralPoint p ξ)| ≤ (k:ℝ)*r*W (centralPoint p ξ))
    (hf : |f (densityHeight k p ξ)| ≤ F) (hb : |b (densityHeight k p ξ)| ≤ B) :
    |densityCorrectionRaw k f b W p ξ| ≤
      Real.exp (2*densityHeight k p ξ/k)*W (centralPoint p ξ)*(F+B*r) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  let z := (bracket ξ (p:Base)/(‖bracket ξ (p:Base)‖:ℂ))^k
  have hn : ‖z‖=1 := by
    dsimp [z]
    rw [norm_pow,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_norm,div_self (norm_ne_zero_iff.mpr hξ),one_pow]
  have hzre : |z.re| ≤ 1 := (Complex.abs_re_le_norm z).trans_eq hn
  have hzim : |z.im| ≤ 1 := (Complex.abs_im_le_norm z).trans_eq hn
  rw [densityCorrectionRaw_model hk f b W p hξ]
  unfold correctionModel
  rw [abs_mul,abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (2*densityHeight k p ξ/k)*
      (|f (densityHeight k p ξ)| * |W (centralPoint p ξ)| * |z.re| +
       |b (densityHeight k p ξ)/k| * |phaseDerivative W (centralPoint p ξ)| * |z.im|) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      simpa only [abs_mul] using abs_sub_triangle
        (f (densityHeight k p ξ)*W (centralPoint p ξ)*z.re)
        (b (densityHeight k p ξ)/k*phaseDerivative W (centralPoint p ξ)*z.im)
    _ ≤ Real.exp (2*densityHeight k p ξ/k)*(F*W (centralPoint p ξ)*1+
      (B/k)*((k:ℝ)*r*W (centralPoint p ξ))*1) := by
      rw [abs_of_nonneg hS,abs_div,abs_of_pos hk0]
      gcongr
    _ = _ := by field_simp

lemma horizontal_direction_ratio {k : ℕ} {R D : ℝ} (hk : 0 < k) (hR : 0 < R)
    (hkR : 2*R ≤ k) (hD : 2*Real.sqrt (2*R) ≤ D)
    (p ξ : Sphere) (hξ : ξ ∈ peakPatch k R p) (v : Base) (hv : Horizontal ξ v) :
    ‖bracket v (p:Base)/bracket (ξ:Base) (p:Base)‖ ≤ D*Real.sqrt (k:ℝ)*‖v‖/k := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hb := horizontal_patch_log_derivative_bound hk hR hkR p ξ hξ v hv
  rw [Real.sqrt_div (by positivity)] at hb
  apply hb.trans
  have hroot := Real.sq_sqrt hk0.le
  have hroot0 : 0 < Real.sqrt (k:ℝ) := Real.sqrt_pos.mpr hk0
  apply (le_div_iff₀ hk0).mpr
  have he : 2*(Real.sqrt (2*R)/Real.sqrt (k:ℝ))*‖v‖*(k:ℝ)=
      (2*Real.sqrt (2*R))*Real.sqrt (k:ℝ)*‖v‖ := by
    rw [← hroot]
    rw [Real.sqrt_sq (Real.sqrt_nonneg _)]
    field_simp
  rw [he]
  gcongr

lemma phase_direction_ratio (p ξ : Sphere) (hξ : bracket (ξ:Base) (p:Base) ≠ 0) :
    ‖bracket (Complex.I • (ξ:Base)) (p:Base)/bracket (ξ:Base) (p:Base)‖=1 := by
  rw [bracket_smul,mul_div_cancel_right₀ Complex.I hξ,Complex.norm_I]

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseDensityPatchEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma density_central_envelope {W : Base → ℝ} (hW : Differentiable ℝ W)
    (hpos : ∀ ξ : Sphere, 0 < W ξ) {H : ℝ} (hH : 0 ≤ H) (hd : HorizontalBound W H)
    {k : ℕ} {R : ℝ} (hk : 0 < k) (hR : 0 < R) (hkR : 2*R ≤ k)
    (p ξ : Sphere) (hξ : ξ ∈ peakPatch k R p) :
    Real.exp (2*densityHeight k p ξ/k)*W (centralPoint p ξ) ≤
      Real.exp (H*(2*Real.sqrt (2*R)/Real.sqrt (k:ℝ))+2*R/k)*W ξ := by
  have hh : densityHeight k p ξ < R := ((peakPatch_iff_height hk R p ξ).mp hξ).2
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hw := (central_comparison hW hpos hH hd hk hR hkR p ξ hξ).1
  calc
    _ ≤ Real.exp (2*R/k)*(Real.exp (H*(2*Real.sqrt (2*R)/Real.sqrt (k:ℝ)))*W ξ) := by
      apply mul_le_mul _ hw (le_of_lt (hpos ⟨centralPoint p ξ,by simpa only [Metric.mem_sphere,dist_zero_right] using centralPoint_norm p (norm_pos_iff.mp (peakPatch_norm_pos hξ))⟩)) (Real.exp_pos _).le
      exact Real.exp_le_exp.mpr (by gcongr)
    _ = _ := by rw [← mul_assoc,← Real.exp_add]; congr 2; ring

lemma densityCorrection_patch_value {k : ℕ} (hk : 0 < k)
    (f b : ℝ → ℝ) (W : Base → ℝ) {R F B r H : ℝ}
    (hF : 0 ≤ F) (hB : 0 ≤ B) (hr : 0 ≤ r)
    (hpos : ∀ ξ : Sphere, 0 < W ξ)
    (hT : ∀ ξ : Sphere, |phaseDerivative W ξ| ≤ (k:ℝ)*r*W ξ)
    (hf : ∀ y, 0 ≤ y → |f y| ≤ F) (hb : ∀ y, 0 ≤ y → |b y| ≤ B)
    (p ξ : Sphere) (hξ : ξ ∈ peakPatch k R p)
    (henv : Real.exp (2*densityHeight k p ξ/k)*W (centralPoint p ξ) ≤ H*W ξ) :
    |densityCorrection k R f b W p ξ| ≤ H*(F+B*r)*W ξ := by
  have hc : bracket (ξ:Base) (p:Base) ≠ 0 := norm_pos_iff.mp (peakPatch_norm_pos hξ)
  change Real.exp (-R/k)<‖bracket (ξ:Base) (p:Base)‖ at hξ
  rw [densityCorrection,ite_eq_left hξ]
  have hh := densityCorrectionRaw_value_bound hk f b W p ξ hc hF hB hr
    (hpos (centralSphere p ξ hc)).le (hT (centralSphere p ξ hc)) (hf _ (patchHeight_nonneg k p ξ)) (hb _ (patchHeight_nonneg k p ξ))
  exact hh.trans ((mul_le_mul_of_nonneg_right henv (by positivity)).trans_eq (by ring))

lemma densityCorrection_patch_direction {k : ℕ} (hk : 0 < k)
    {f b : ℝ → ℝ} {W : Base → ℝ} (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b) (hW : ContDiff ℝ ∞ W)
    {R F B F₁ B₁ H D : ℝ} (hF : 0 ≤ F) (hB : 0 ≤ B) (hF₁ : 0 ≤ F₁) (hB₁ : 0 ≤ B₁) (hD : 0 ≤ D)
    (hpos : ∀ ξ : Sphere, 0 < W ξ)
    (hT : ∀ ξ : Sphere, |phaseDerivative W ξ| ≤ (k:ℝ)*W ξ)
    (hTT : ∀ ξ : Sphere, |phaseDerivative (phaseDerivative W) ξ| ≤ (k:ℝ)^2*W ξ)
    (hfv : ∀ y, 0 ≤ y → |f y| ≤ F) (hbv : ∀ y, 0 ≤ y → |b y| ≤ B)
    (hfd : ∀ y, 0 ≤ y → |deriv f y| ≤ F₁) (hbd : ∀ y, 0 ≤ y → |deriv b y| ≤ B₁)
    (p ξ : Sphere) (hξ : ξ ∈ peakPatch k R p) (v : Base)
    (hdir : ‖bracket v (p:Base)/bracket (ξ:Base) (p:Base)‖ ≤ D/k)
    (henv : Real.exp (2*densityHeight k p ξ/k)*W (centralPoint p ξ) ≤ H*W ξ) :
    |fderiv ℝ (densityCorrection k R f b W p) ξ v| ≤ D*H*(4*(F+B)+F₁+B₁)*W ξ := by
  have hc : bracket (ξ:Base) (p:Base) ≠ 0 := norm_pos_iff.mp (peakPatch_norm_pos hξ)
  rw [densityCorrection_fderiv_raw f b W p ξ hξ]
  have hh := densityCorrectionRaw_direction_bound hk hD hF hB hF₁ hB₁ hf hb hW p ξ v hc hdir
    (hpos (centralSphere p ξ hc)).le (hT (centralSphere p ξ hc)) (hTT (centralSphere p ξ hc)) (hfv _ (patchHeight_nonneg k p ξ)) (hbv _ (patchHeight_nonneg k p ξ)) (hfd _ (patchHeight_nonneg k p ξ)) (hbd _ (patchHeight_nonneg k p ξ))
  calc
    _ ≤ D*(Real.exp (2*densityHeight k p ξ/k)*W (centralPoint p ξ))*(4*(F+B)+F₁+B₁) := by simpa only [mul_assoc] using hh
    _ ≤ D*(H*W ξ)*(4*(F+B)+F₁+B₁) := by gcongr
    _ = _ := by ring

lemma fderiv_density_update {k : ℕ} (hk : 0 < k) {R E : ℝ} (hER : E < R)
    {f b : ℝ → ℝ} {W : Base → ℝ} (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b) (hW : ContDiff ℝ ∞ W)
    (htail : ∀ y, E ≤ y → f y=0 ∧ b y=0) (P : Finset Sphere) (ξ v : Base) :
    fderiv ℝ (fun z => W z+∑ p ∈ P, densityCorrection k R f b W p z) ξ v =
      fderiv ℝ W ξ v+∑ p ∈ P, fderiv ℝ (densityCorrection k R f b W p) ξ v := by
  have hw := hW.differentiable (by simp) ξ
  have hp : ∀ p ∈ P, DifferentiableAt ℝ (densityCorrection k R f b W p) ξ :=
    fun p hp => (densityCorrection_smooth hk hER hf hb hW htail p).differentiable (by simp) ξ
  rw [fderiv_fun_add hw (DifferentiableAt.fun_sum hp),fderiv_fun_sum hp]
  simp only [add_apply,sum_apply]

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseDensityStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma patch_unique {P : Finset Sphere} {k : ℕ} {R : ℝ}
    (hd : (P:Set Sphere).PairwiseDisjoint (peakPatch k R)) (ξ : Sphere)
    (p : Sphere) (hp : p ∈ P) (q : Sphere) (hq : q ∈ P)
    (hξp : ξ ∈ peakPatch k R p) (hξq : ξ ∈ peakPatch k R q) : p=q := by
  by_contra hpq
  exact Set.disjoint_left.mp (hd hp hq hpq) hξp hξq

lemma density_update_value {k : ℕ} (hk : 0 < k)
    (f b : ℝ → ℝ) (W : Base → ℝ) {R F B r H c : ℝ}
    (hF : 0 ≤ F) (hB : 0 ≤ B) (hr : 0 ≤ r) (hc : 0 < c) (hc1 : 2*c ≤ 1)
    (hpos : ∀ ξ : Sphere, 0 < W ξ)
    (hT : ∀ ξ : Sphere, |phaseDerivative W ξ| ≤ (k:ℝ)*r*W ξ)
    (hf : ∀ y, 0 ≤ y → |f y| ≤ F) (hb : ∀ y, 0 ≤ y → |b y| ≤ B)
    (P : Finset Sphere) (hd : (P:Set Sphere).PairwiseDisjoint (peakPatch k R))
    (henv : ∀ p ∈ P, ∀ ξ ∈ peakPatch k R p,
      Real.exp (2*densityHeight k p ξ/k)*W (centralPoint p ξ) ≤ H*W ξ)
    (hsmall : H*(F+B*r) ≤ 1-2*c) (ξ : Sphere) :
    let V := W ξ+∑ p ∈ P, densityCorrection k R f b W p ξ
    0 < V ∧ c*W ξ ≤ V ∧ V ≤ 2*W ξ := by
  have ha : |∑ p ∈ P, densityCorrection k R f b W p ξ| ≤ (1-2*c)*W ξ := by
    apply disjoint_sum_abs_bound P (fun p => ξ ∈ peakPatch k R p) (patch_unique hd ξ) _ (by nlinarith [hpos ξ])
    · intro p hp hn
      exact ite_eq_right hn
    · intro p hp ht
      exact (densityCorrection_patch_value hk f b W hF hB hr hpos hT hf hb p ξ ht (henv p hp ξ ht)).trans
        (mul_le_mul_of_nonneg_right hsmall (hpos ξ).le)
  obtain ⟨hlo,hhi⟩ := abs_le.mp ha
  dsimp only
  have hp := hpos ξ
  have hcp : 0 < c*W ξ := mul_pos hc hp
  constructor
  · linarith
  constructor <;> linarith

lemma density_update_direction {k : ℕ} (hk : 0 < k) {R E : ℝ} (hER : E < R)
    {f b : ℝ → ℝ} {W : Base → ℝ} (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b) (hW : ContDiff ℝ ∞ W)
    (htail : ∀ y, E ≤ y → f y=0 ∧ b y=0)
    {F B F₁ B₁ H D : ℝ} (hF : 0 ≤ F) (hB : 0 ≤ B) (hF₁ : 0 ≤ F₁) (hB₁ : 0 ≤ B₁) (hD : 0 ≤ D) (hH : 0 ≤ H)
    (hpos : ∀ ξ : Sphere, 0 < W ξ)
    (hT : ∀ ξ : Sphere, |phaseDerivative W ξ| ≤ (k:ℝ)*W ξ)
    (hTT : ∀ ξ : Sphere, |phaseDerivative (phaseDerivative W) ξ| ≤ (k:ℝ)^2*W ξ)
    (hfv : ∀ y, 0 ≤ y → |f y| ≤ F) (hbv : ∀ y, 0 ≤ y → |b y| ≤ B)
    (hfd : ∀ y, 0 ≤ y → |deriv f y| ≤ F₁) (hbd : ∀ y, 0 ≤ y → |deriv b y| ≤ B₁)
    (P : Finset Sphere) (hd : (P:Set Sphere).PairwiseDisjoint (peakPatch k R))
    (ξ : Sphere) (v : Base)
    (hdir : ∀ p ∈ P, ξ ∈ peakPatch k R p → ‖bracket v (p:Base)/bracket (ξ:Base) (p:Base)‖ ≤ D/k)
    (henv : ∀ p ∈ P, ξ ∈ peakPatch k R p →
      Real.exp (2*densityHeight k p ξ/k)*W (centralPoint p ξ) ≤ H*W ξ) :
    |fderiv ℝ (fun z => W z+∑ p ∈ P, densityCorrection k R f b W p z) ξ v| ≤
      |fderiv ℝ W ξ v|+D*H*(4*(F+B)+F₁+B₁)*W ξ := by
  rw [fderiv_density_update hk hER hf hb hW htail]
  apply (abs_add_le _ _).trans
  apply add_le_add le_rfl
  have hw0 := (hpos ξ).le
  apply disjoint_sum_abs_bound P (fun p => ξ ∈ peakPatch k R p) (patch_unique hd ξ) _ (by positivity)
  · intro p hp hn
    rw [densityCorrection_fderiv_zero hk hER htail W p ξ hn]
    rfl
  · intro p hp ht
    exact densityCorrection_patch_direction hk hf hb hW hF hB hF₁ hB₁ hD hpos hT hTT hfv hbv hfd hbd p ξ ht v (hdir p hp ht) (henv p hp ht)

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseCentralSecond
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma expSum_hasDeriv (s : Finset ℤ) (a : ℤ → ℂ) (w : ℤ → ℝ) (z : ℂ) :
    HasDerivAt (expSum s a w) (expSum s (fun n => Complex.I*(w n:ℂ)*a n) w z) z := by
  have hh := HasDerivAt.sum (u := s) (fun n hn =>
    (((hasDerivAt_id z).const_mul (Complex.I*(w n:ℂ))).cexp).const_mul (a n))
  convert! hh using 1
  · ext t; simp [expSum,Finset.sum_apply]
  · unfold expSum
    apply Finset.sum_congr rfl
    intro n hn
    dsimp only [id]
    ring

lemma expSum_iteratedDeriv_two (s : Finset ℤ) (a : ℤ → ℂ) (w : ℤ → ℝ) :
    iteratedDeriv 2 (expSum s a w) 0 = ∑ n ∈ s, -(w n:ℂ)^2*a n := by
  have hd : deriv (expSum s a w)=expSum s (fun n => Complex.I*(w n:ℂ)*a n) w :=
    funext (fun z => (expSum_hasDeriv s a w z).deriv)
  rw [iteratedDeriv_succ,iteratedDeriv_one,hd,(expSum_hasDeriv _ _ _ _).deriv]
  unfold expSum
  simp only [mul_zero,Complex.exp_zero,mul_one]
  apply Finset.sum_congr rfl
  intro n hn
  calc
    _ = Complex.I^2*(w n:ℂ)^2*a n := by ring
    _ = _ := by rw [Complex.I_sq]; ring

lemma phase_second_weighted {W : Base → ℝ} (hW : ContDiff ℝ ∞ W)
    {ℓ : ℕ} (hband : PhaseBandwidth W ℓ) {q A : ℝ} (hq : 0 < q) (hA : 0 ≤ A)
    (hℓ : (ℓ:ℝ) ≤ 2*q) (N : ℕ) (ξ : Sphere)
    (hpos : ∀ z : Circle, 0 < W ((z:ℂ) • (ξ:Base)))
    (hg : ∀ u : ℝ, W ((Circle.exp u:ℂ) • (ξ:Base)) ≤ A*(1+q*|u|)^N*W ξ) :
    |phaseDerivative (phaseDerivative W) ξ| ≤ (2*A*4^N*Real.exp 2)*q^2*W ξ := by
  obtain ⟨s,a,hs,he⟩ := hband ξ
  let w : ℤ → ℝ := fun n => (n:ℝ)/q
  have hw : ∀ n ∈ s, |w n| ≤ 2 := by
    intro n hn
    rw [show w n=(n:ℝ)/q from rfl,abs_div,abs_of_pos hq]
    apply (div_le_iff₀ hq).mpr
    have hn' : |(n:ℝ)| ≤ (ℓ:ℝ) := by exact_mod_cast hs n hn
    linarith
  have hfun : ∀ x : ℝ, expSum s a w x = (W ((Circle.exp (x/q):ℂ) • (ξ:Base)):ℂ) := by
    intro x
    rw [he]
    unfold expSum phaseSum
    apply Finset.sum_congr rfl
    intro n hn
    rw [phaseChar_exp]
    congr 2
    dsimp [w]
    push_cast
    ring
  have hp : 0 < W ξ := by simpa using hpos 1
  have hb : ∀ x : ℝ, ‖expSum s a w x‖ ≤ (A*W ξ)*(1+|x|)^N := by
    intro x
    rw [hfun,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hpos (Circle.exp (x/q)))]
    have ht := hg (x/q)
    rw [abs_div,abs_of_pos hq,mul_div_cancel₀ _ hq.ne'] at ht
    linarith
  have hbd := expSum_second_derivative_bound s a w N hw (mul_nonneg hA hp.le) hb
  rw [expSum_iteratedDeriv_two] at hbd
  have hdiff := hW.differentiable (by simp)
  have hdiffT := (phaseDerivative_smooth hW).differentiable (by simp)
  have hT : ∀ z : Circle, (phaseDerivative W ((z:ℂ) • (ξ:Base)):ℂ) =
      phaseSum s (fun n => (n:ℂ)*Complex.I*a n) z := phaseDerivative_expansion hdiff ξ s a he
  have hTT := phaseDerivative_expansion hdiffT ξ s _ hT 1
  simp only [Circle.coe_one,one_smul,phaseSum,phaseChar_one,mul_one] at hTT
  have hsc : (phaseDerivative (phaseDerivative W) ξ:ℂ) =
      (q:ℂ)^2 * ∑ n ∈ s, -(w n:ℂ)^2*a n := by
    rw [hTT,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [w]
    push_cast
    have hq' : (q:ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    field_simp
    calc
      _ = Complex.I^2*(n:ℂ)^2*a n := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  have hh := congrArg norm hsc
  simp only [Complex.norm_real,Real.norm_eq_abs,norm_mul,norm_pow,abs_of_pos hq] at hh
  rw [hh]
  have ht := mul_le_mul_of_nonneg_left hbd (sq_nonneg q)
  linarith

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseDensityStepSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma densityBandwidth_le_twice {Q : ℕ} (hQ : 2 ≤ Q) (j : ℕ) :
    densityBandwidth Q j ≤ 2*Q^j := by
  cases j with
  | zero => simp [densityBandwidth]
  | succ j =>
    rw [densityBandwidth_succ]
    have hh := densityBandwidth_lt hQ j
    omega

lemma phase_second_from_steps {Q n N : ℕ} (hQ : 2 ≤ Q)
    {c K : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hK : 0 ≤ K) (hN : 2/c ≤ (2:ℝ)^N)
    (W : ℕ → Base → ℝ) (hzero : W 0=fun _ => 1)
    (hsm : ∀ j ≤ n, ContDiff ℝ ∞ (W j))
    (hpos : ∀ j ≤ n, ∀ ξ : Sphere, 0 < W j ξ)
    (hder : ∀ j ≤ n, ∀ ξ : Sphere, |phaseDerivative (W j) ξ| ≤ K*(Q:ℝ)^j*W j ξ)
    (hstep : ∀ j, j < n → ∀ ξ : Sphere, c*W j ξ ≤ W (j+1) ξ ∧ W (j+1) ξ ≤ 2*W j ξ)
    (hband : PhaseBandwidth (W n) (densityBandwidth Q n)) (ξ : Sphere) :
    |phaseDerivative (phaseDerivative (W n)) ξ| ≤
      (2*(Real.exp K*(2/c))*4^N*Real.exp 2)*((Q:ℝ)^n)^2*W n ξ := by
  let A := Real.exp K*(2/c)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hQ0 : (0:ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hg : ∀ u : ℝ, W n ((Circle.exp u:ℂ) • (ξ:Base)) ≤ A*(1+(Q:ℝ)^n*|u|)^N*W n ξ := by
    intro u
    let V : ℕ → ℝ → ℝ := fun j θ => W j ((Circle.exp θ:ℂ) • (ξ:Base))
    have hv0 : V 0=fun _ => 1 := by funext θ; simp [V,hzero]
    have hvd : ∀ j ≤ n, ∀ θ, HasDerivAt (V j) (phaseDerivative (W j) ((Circle.exp θ:ℂ) • (ξ:Base))) θ :=
      fun j hj θ => phaseDerivative_curve ((hsm j hj).differentiable (by simp)) ξ θ
    have hvder : ∀ j ≤ n, ∀ θ, |deriv (V j) θ| ≤ K*(Q:ℝ)^j*V j θ := by
      intro j hj θ
      rw [(hvd j hj θ).deriv]
      exact hder j hj (phaseSphere (Circle.exp θ) ξ)
    have hh := orbit_growth_nat hQ hc hc1 hK hN V hv0
      (fun j hj θ => hpos j hj (phaseSphere (Circle.exp θ) ξ))
      (fun j hj θ => (hvd j hj θ).differentiableAt) hvder
      (fun j hj θ => hstep j hj (phaseSphere (Circle.exp θ) ξ)) 0 u
    simp only [V,zero_add,Circle.exp_zero,Circle.coe_one,one_smul] at hh
    refine hh.trans ?_
    apply mul_le_mul_of_nonneg_right _ (hpos n le_rfl ξ).le
    apply mul_le_mul_of_nonneg_left _ hA
    apply pow_le_pow_left₀ (by positivity)
    exact max_le (by linarith [mul_nonneg (pow_nonneg hQ0.le n) (abs_nonneg u)]) (by linarith : (Q:ℝ)^n*|u| ≤ 1+(Q:ℝ)^n*|u|)
  exact phase_second_weighted (hsm n le_rfl) hband (pow_pos hQ0 n) hA
    (by exact_mod_cast densityBandwidth_le_twice hQ n) N ξ
    (fun z => hpos n le_rfl (phaseSphere z ξ)) hg

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseDensityScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
namespace PinchedHartogs.BaseConstruction

lemma density_degree_ge {Q : ℕ} (hQ : 1 ≤ Q) (j : ℕ) : (Q:ℝ) ≤ (Q:ℝ)^(j+1) := by
  have hq : (1:ℝ) ≤ Q := by exact_mod_cast hQ
  rw [pow_succ]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (one_le_pow₀ hq) (by positivity : (0:ℝ) ≤ Q)

lemma density_sqrt_scale {Q : ℕ} (hQ : 0 < Q) (j : ℕ) :
    Real.sqrt ((Q:ℝ)^(j+1))=Real.sqrt ((Q:ℝ)^j)*Real.sqrt (Q:ℝ) := by
  rw [pow_succ,Real.sqrt_mul (by positivity)]

lemma density_envelope_bound {Q : ℕ} (hQ : 1 ≤ Q) {K R D : ℝ}
    (hK : 0 ≤ K) (hR : 0 ≤ R) (hD : 2*Real.sqrt (2*R) ≤ D) (j : ℕ) :
    K*Real.sqrt ((Q:ℝ)^j)*(2*Real.sqrt (2*R)/Real.sqrt ((Q:ℝ)^(j+1)))+2*R/(Q:ℝ)^(j+1) ≤
      K*D/Real.sqrt (Q:ℝ)+2*R/Q := by
  have hQ0 : 0 < Q := by omega
  have hq : (0:ℝ) < Q := by exact_mod_cast hQ0
  have hs : Real.sqrt ((Q:ℝ)^j) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (pow_pos hq j))
  rw [density_sqrt_scale hQ0 j]
  have he : K*Real.sqrt ((Q:ℝ)^j)*(2*Real.sqrt (2*R)/(Real.sqrt ((Q:ℝ)^j)*Real.sqrt (Q:ℝ)))=
      K*(2*Real.sqrt (2*R))/Real.sqrt (Q:ℝ) := by field_simp
  rw [he]
  apply add_le_add
  · gcongr
  · exact div_le_div_of_nonneg_left (by positivity) hq (density_degree_ge hQ j)

lemma density_phase_scale {Q : ℕ} (hQ : 0 < Q) (K : ℝ) (j : ℕ) :
    (Q:ℝ)^(j+1)*(K/Q)=K*(Q:ℝ)^j := by
  have hq : (Q:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hQ)
  rw [pow_succ]
  field_simp

lemma density_second_scale {Q : ℕ} (hQ : 0 < Q) (C : ℝ) (j : ℕ) :
    ((Q:ℝ)^(j+1))^2*(C/(Q:ℝ)^2)=C*((Q:ℝ)^j)^2 := by
  have hq : (Q:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hQ)
  rw [pow_succ]
  field_simp
  simp only [pow_succ]
  ring

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseDensityInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open scoped ContDiff
open Set Filter Topology
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma density_induction {Q N : ℕ} (hQ : 2 ≤ Q) {R E F B F₁ B₁ D c K : ℝ}
    (hR : 0 < R) (hER : E < R) (hQR : 2*R ≤ Q)
    (hF : 0 ≤ F) (hB : 0 ≤ B) (hF₁ : 0 ≤ F₁) (hB₁ : 0 ≤ B₁)
    (hD1 : 1 ≤ D) (hDR : 2*Real.sqrt (2*R) ≤ D)
    (hc : 0 < c) (hc1 : 2*c ≤ 1) (hK : 0 ≤ K) (hN : 2/c ≤ (2:ℝ)^N)
    {f b : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b)
    (htail : ∀ y, E ≤ y → f y=0 ∧ b y=0)
    (hfv : ∀ y, 0 ≤ y → |f y| ≤ F) (hbv : ∀ y, 0 ≤ y → |b y| ≤ B)
    (hfd : ∀ y, 0 ≤ y → |deriv f y| ≤ F₁) (hbd : ∀ y, 0 ≤ y → |deriv b y| ≤ B₁)
    (P : ℕ → Finset Sphere)
    (hdis : ∀ j, (P (Q^(j+1)):Set Sphere).PairwiseDisjoint (peakPatch (Q^(j+1)) R))
    (hH : Real.exp (K*D/Real.sqrt (Q:ℝ)+2*R/Q) ≤ 2)
    (hsmall : Real.exp (K*D/Real.sqrt (Q:ℝ)+2*R/Q)*(F+B*(K/Q)) ≤ 1-2*c)
    (hphase : K/Q ≤ 1)
    (hsecond : (2*(Real.exp K*(2/c))*4^N*Real.exp 2)/(Q:ℝ)^2 ≤ 1)
    (hderH : 2*D*(4*(F+B)+F₁+B₁)+K/Real.sqrt (Q:ℝ) ≤ K*c)
    (hderT : 2*D*(4*(F+B)+F₁+B₁)+K/Q ≤ K*c) :
    ∀ j, DensityStage (density Q R f b P) Q c K j := by
  have hQ0 : 0 < Q := by omega
  have hq : (0:ℝ) < Q := by exact_mod_cast hQ0
  have hD : 0 ≤ D := by linarith
  have hC : 0 ≤ 4*(F+B)+F₁+B₁ := by positivity
  let W := density Q R f b P
  have hsm : ∀ j, ContDiff ℝ ∞ (W j) := density_smooth hQ0 hER hf hb htail P
  have hfder : ∀ ξ : Base, fderiv ℝ (fun _ : Base => (1:ℝ)) ξ=0 := fun ξ => (hasFDerivAt_const (1:ℝ) ξ).fderiv
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero =>
      constructor
      · intro ξ; norm_num [W,density]
      · intro ξ v hv
        simp only [density,hfder,zero_apply,abs_zero,pow_zero,Real.sqrt_one,mul_one]
        positivity
      · intro ξ
        simp only [density,phaseDerivative,hfder,zero_apply,abs_zero,pow_zero,mul_one]
        exact hK
      · intro i hi; omega
    | succ j =>
      have old := ih j (Nat.lt_succ_self j)
      have hk : 0 < Q^(j+1) := pow_pos hQ0 _
      have hk0 : (0:ℝ) < (Q:ℝ)^(j+1) := pow_pos hq _
      have hsk : 0 < Real.sqrt ((Q:ℝ)^(j+1)) := Real.sqrt_pos.mpr hk0
      have hsQ : 0 < Real.sqrt (Q:ℝ) := Real.sqrt_pos.mpr hq
      have hkR : 2*R ≤ (Q^(j+1):ℕ) := by
        exact_mod_cast hQR.trans (density_degree_ge (by omega : 1 ≤ Q) j)
      have henv : ∀ p ∈ P (Q^(j+1)), ∀ ξ ∈ peakPatch (Q^(j+1)) R p,
          Real.exp (2*densityHeight (Q^(j+1)) p ξ/(Q^(j+1):ℕ))*W j (centralPoint p ξ) ≤
          Real.exp (K*D/Real.sqrt (Q:ℝ)+2*R/Q)*W j ξ := by
        intro p hp ξ ht
        have hh := density_central_envelope ((hsm j).differentiable (by simp)) old.positive
          (by positivity : 0 ≤ K*Real.sqrt ((Q:ℝ)^j)) old.horizontal hk hR hkR p ξ ht
        apply hh.trans
        apply mul_le_mul_of_nonneg_right _ (old.positive ξ).le
        apply Real.exp_le_exp.mpr
        simpa only [Nat.cast_pow] using density_envelope_bound (by omega : 1 ≤ Q) hK hR.le hDR j
      have henv2 : ∀ p ∈ P (Q^(j+1)), ∀ ξ ∈ peakPatch (Q^(j+1)) R p,
          Real.exp (2*densityHeight (Q^(j+1)) p ξ/(Q^(j+1):ℕ))*W j (centralPoint p ξ) ≤ 2*W j ξ := by
        intro p hp ξ ht
        exact (henv p hp ξ ht).trans (mul_le_mul_of_nonneg_right hH (old.positive ξ).le)
      have hTscaled : ∀ ξ : Sphere, |phaseDerivative (W j) ξ| ≤ (Q^(j+1):ℕ)*(K/Q)*W j ξ := by
        intro ξ
        simpa only [Nat.cast_pow,density_phase_scale hQ0 K j] using old.phase ξ
      have hT : ∀ ξ : Sphere, |phaseDerivative (W j) ξ| ≤ (Q^(j+1):ℕ)*W j ξ := by
        intro ξ
        apply (hTscaled ξ).trans
        simp only [Nat.cast_pow]
        exact mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left hphase hk0.le).trans_eq (mul_one _)) (old.positive ξ).le
      have hTT : ∀ ξ : Sphere, |phaseDerivative (phaseDerivative (W j)) ξ| ≤ ((Q^(j+1):ℕ):ℝ)^2*W j ξ := by
        intro ξ
        have hh := phase_second_from_steps hQ hc (by linarith) hK hN W rfl
          (fun i hi => hsm i) (fun i hi => (ih i (by omega)).positive)
          (fun i hi => (ih i (by omega)).phase)
          (fun i hi => (ih (i+1) (by omega)).step i rfl)
          (density_bandwidth hQ0 hER hf hb htail P j) ξ
        have he := density_second_scale hQ0 (2*(Real.exp K*(2/c))*4^N*Real.exp 2) j
        rw [← he] at hh
        apply hh.trans
        simp only [Nat.cast_pow]
        have hp := (old.positive ξ).le
        exact mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left hsecond (sq_nonneg _)).trans_eq (mul_one _)) hp
      have hval : ∀ ξ : Sphere, 0 < W (j+1) ξ ∧ c*W j ξ ≤ W (j+1) ξ ∧ W (j+1) ξ ≤ 2*W j ξ := by
        intro ξ
        exact density_update_value hk f b (W j) hF hB (by positivity : 0 ≤ K/Q) hc hc1 old.positive hTscaled hfv hbv
          (P (Q^(j+1))) (hdis j) henv hsmall ξ
      constructor
      · intro ξ; exact (hval ξ).1
      · intro ξ v hv
        have hdir : ∀ p ∈ P (Q^(j+1)), ξ ∈ peakPatch (Q^(j+1)) R p →
            ‖bracket v (p:Base)/bracket (ξ:Base) (p:Base)‖ ≤ (D*Real.sqrt ((Q:ℝ)^(j+1))*‖v‖)/(Q^(j+1):ℕ) := by
          intro p hp ht
          simpa only [Nat.cast_pow] using horizontal_direction_ratio hk hR hkR hDR p ξ ht v hv
        have hh := density_update_direction hk hER hf hb (hsm j) htail hF hB hF₁ hB₁
          (by positivity : 0 ≤ D*Real.sqrt ((Q:ℝ)^(j+1))*‖v‖) (by norm_num : (0:ℝ) ≤ 2)
          old.positive hT hTT hfv hbv hfd hbd (P (Q^(j+1))) (hdis j) ξ v hdir (fun p hp ht => henv2 p hp ξ ht)
        have hx := old.horizontal ξ v hv
        have he : K*Real.sqrt ((Q:ℝ)^j)*‖v‖*W j ξ+
            (D*Real.sqrt ((Q:ℝ)^(j+1))*‖v‖)*2*(4*(F+B)+F₁+B₁)*W j ξ =
            (2*D*(4*(F+B)+F₁+B₁)+K/Real.sqrt (Q:ℝ))*Real.sqrt ((Q:ℝ)^(j+1))*‖v‖*W j ξ := by
          rw [density_sqrt_scale hQ0 j]
          field_simp
          ring
        calc
          _ ≤ |fderiv ℝ (W j) ξ v|+(D*Real.sqrt ((Q:ℝ)^(j+1))*‖v‖)*2*(4*(F+B)+F₁+B₁)*W j ξ := hh
          _ ≤ K*Real.sqrt ((Q:ℝ)^j)*‖v‖*W j ξ+(D*Real.sqrt ((Q:ℝ)^(j+1))*‖v‖)*2*(4*(F+B)+F₁+B₁)*W j ξ := add_le_add hx le_rfl
          _ = _ := he
          _ ≤ (K*c)*Real.sqrt ((Q:ℝ)^(j+1))*‖v‖*W j ξ := by gcongr; exact (old.positive ξ).le
          _ = K*Real.sqrt ((Q:ℝ)^(j+1))*‖v‖*(c*W j ξ) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (hval ξ).2.1 (by positivity)
      · intro ξ
        have hdir : ∀ p ∈ P (Q^(j+1)), ξ ∈ peakPatch (Q^(j+1)) R p →
            ‖bracket (Complex.I • (ξ:Base)) (p:Base)/bracket (ξ:Base) (p:Base)‖ ≤ (D*(Q:ℝ)^(j+1))/(Q^(j+1):ℕ) := by
          intro p hp ht
          rw [phase_direction_ratio p ξ (norm_pos_iff.mp (peakPatch_norm_pos ht))]
          simp only [Nat.cast_pow]
          rw [mul_div_cancel_right₀ D hk0.ne']
          exact hD1
        have hh := density_update_direction hk hER hf hb (hsm j) htail hF hB hF₁ hB₁
          (by positivity : 0 ≤ D*(Q:ℝ)^(j+1)) (by norm_num : (0:ℝ) ≤ 2)
          old.positive hT hTT hfv hbv hfd hbd (P (Q^(j+1))) (hdis j) ξ (Complex.I • (ξ:Base)) hdir (fun p hp ht => henv2 p hp ξ ht)
        have hx := old.phase ξ
        have he : K*(Q:ℝ)^j*W j ξ+(D*(Q:ℝ)^(j+1))*2*(4*(F+B)+F₁+B₁)*W j ξ =
            (2*D*(4*(F+B)+F₁+B₁)+K/Q)*(Q:ℝ)^(j+1)*W j ξ := by
          rw [pow_succ]
          field_simp
          ring
        calc
          _ ≤ |phaseDerivative (W j) ξ|+(D*(Q:ℝ)^(j+1))*2*(4*(F+B)+F₁+B₁)*W j ξ := hh
          _ ≤ K*(Q:ℝ)^j*W j ξ+(D*(Q:ℝ)^(j+1))*2*(4*(F+B)+F₁+B₁)*W j ξ := add_le_add hx le_rfl
          _ = _ := he
          _ ≤ (K*c)*(Q:ℝ)^(j+1)*W j ξ := by gcongr; exact (old.positive ξ).le
          _ = K*(Q:ℝ)^(j+1)*(c*W j ξ) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (hval ξ).2.1 (by positivity)
      · intro i hi ξ
        have he : i=j := by omega
        subst i
        exact (hval ξ).2

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseProfileBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma halfline_bound_of_tail {f : ℝ → ℝ} (hf : Continuous f) {E : ℝ}
    (htail : ∀ y, E ≤ y → f y=0) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y, 0 ≤ y → |f y| ≤ C := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hf.continuousOn (s := Icc 0 E))
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro y hy
  by_cases he : y ≤ E
  · have hh : |f y| ≤ C := by simpa only [Real.norm_eq_abs] using hC y ⟨hy,he⟩
    exact hh.trans (le_max_left _ _)
  · rw [htail y (le_of_lt (lt_of_not_ge he)),abs_zero]
    exact le_max_right _ _

lemma deriv_tail_zero {f : ℝ → ℝ} {E : ℝ} (htail : ∀ y, E ≤ y → f y=0)
    {y : ℝ} (hy : E < y) : deriv f y=0 := by
  have he : f =ᶠ[𝓝 y] fun _ => 0 := by
    filter_upwards [Ioi_mem_nhds hy] with z hz
    exact htail z (le_of_lt hz)
  rw [he.deriv_eq,deriv_const]

lemma RadialProfiles.bounds {a : ℝ} (p : RadialProfiles a) :
    ∃ B F₁ B₁ : ℝ, 0 ≤ B ∧ 0 ≤ F₁ ∧ 0 ≤ B₁ ∧
      (∀ y, 0 ≤ y → |p.b y| ≤ B) ∧
      (∀ y, 0 ≤ y → |deriv p.f y| ≤ F₁) ∧
      (∀ y, 0 ≤ y → |deriv p.b y| ≤ B₁) := by
  obtain ⟨B,hB,hbv⟩ := halfline_bound_of_tail p.smooth_b.continuous (fun y hy => (p.tail y hy).2)
  obtain ⟨F₁,hF₁,hfv⟩ := halfline_bound_of_tail (p.smooth_f.continuous_deriv (by simp))
    (E := p.cutoff+1) (fun y hy => deriv_tail_zero (fun y hy => (p.tail y hy).1) (by linarith))
  obtain ⟨B₁,hB₁,hbd⟩ := halfline_bound_of_tail (p.smooth_b.continuous_deriv (by simp))
    (E := p.cutoff+1) (fun y hy => deriv_tail_zero (fun y hy => (p.tail y hy).2) (by linarith))
  exact ⟨B,F₁,B₁,hB,hF₁,hB₁,hbv,hfv,hbd⟩

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseDensityThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
namespace PinchedHartogs.BaseConstruction

lemma density_conditions_eventually {F B D K c C₁ C₂ R : ℝ}
    (hgap : F < 1-2*c) (hder : C₂ < K*c) :
    ∀ᶠ q : ℝ in atTop,
      Real.exp (K*D/Real.sqrt q+2*R/q) ≤ 2 ∧
      Real.exp (K*D/Real.sqrt q+2*R/q)*(F+B*(K/q)) ≤ 1-2*c ∧
      K/q ≤ 1 ∧ C₁/q^2 ≤ 1 ∧ C₂+K/Real.sqrt q ≤ K*c ∧ C₂+K/q ≤ K*c := by
  have hq : Tendsto (fun q : ℝ => K/q) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hqs : Tendsto (fun q : ℝ => K/Real.sqrt q) atTop (𝓝 0) := tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have hqd : Tendsto (fun q : ℝ => K*D/Real.sqrt q) atTop (𝓝 0) := tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have hqr : Tendsto (fun q : ℝ => 2*R/q) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hq₂ : Tendsto (fun q : ℝ => C₁/q^2) atTop (𝓝 0) := tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num : 2 ≠ 0))
  have hH : Tendsto (fun q : ℝ => Real.exp (K*D/Real.sqrt q+2*R/q)) atTop (𝓝 1) := by
    have hadd : Tendsto (fun q : ℝ => K*D/Real.sqrt q+2*R/q) atTop (𝓝 0) := by simpa using hqd.add hqr
    simpa only [Function.comp_def, Real.exp_zero] using (Real.continuous_exp.tendsto 0).comp hadd
  have hprod : Tendsto (fun q : ℝ => Real.exp (K*D/Real.sqrt q+2*R/q)*(F+B*(K/q))) atTop (𝓝 F) := by
    simpa using hH.mul (tendsto_const_nhds.add (tendsto_const_nhds.mul hq))
  have hdH : Tendsto (fun q : ℝ => C₂+K/Real.sqrt q) atTop (𝓝 C₂) := by simpa using tendsto_const_nhds.add hqs
  have hdT : Tendsto (fun q : ℝ => C₂+K/q) atTop (𝓝 C₂) := by simpa using tendsto_const_nhds.add hq
  filter_upwards [hH.eventually (gt_mem_nhds (by norm_num : (1:ℝ)<2)),hprod.eventually (gt_mem_nhds hgap),
    hq.eventually (gt_mem_nhds zero_lt_one),hq₂.eventually (gt_mem_nhds zero_lt_one),
    hdH.eventually (gt_mem_nhds hder),hdT.eventually (gt_mem_nhds hder)] with q h1 h2 h3 h4 h5 h6
  exact ⟨h1.le,h2.le,h3.le,h4.le,h5.le,h6.le⟩

lemma exists_density_constants {a : ℝ} (p : RadialProfiles a) {B F₁ B₁ : ℝ}
    (hB : 0 ≤ B) (hF₁ : 0 ≤ F₁) (hB₁ : 0 ≤ B₁) :
    ∃ c K : ℝ, ∃ N : ℕ, 0 < c ∧ 2*c ≤ 1 ∧ 0 < K ∧ 2/c ≤ (2:ℝ)^N ∧
      p.F<1-2*c ∧ 2*(1+2*Real.sqrt (2*p.R))*(4*(p.F+B)+F₁+B₁) < K*c := by
  let c := (1-p.F)/4
  have hc : 0 < c := by dsimp [c]; linarith [p.F_lt]
  let C₂ := 2*(1+2*Real.sqrt (2*p.R))*(4*(p.F+B)+F₁+B₁)
  have hC : 0 ≤ C₂ := by dsimp [C₂]; have hF := p.F_nonneg; positivity
  let K := C₂/c+1
  have hK : 0 < K := by dsimp [K]; positivity
  have hc2 : c ≤ 2 := by dsimp [c]; linarith [p.F_nonneg]
  obtain ⟨N,hN⟩ := exists_nat_pow_near ((one_le_div hc).mpr hc2) (by norm_num : (1:ℝ)<2)
  refine ⟨c,K,N+1,hc,?_,hK,?_,?_,?_⟩
  · dsimp [c]; linarith [p.F_nonneg]
  · exact hN.2.le
  · dsimp [c]; linarith [p.F_lt]
  · dsimp [K]
    have he : (C₂/c+1)*c=C₂+c := by field_simp
    rw [he]
    linarith

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseDensityTheorem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open scoped ContDiff
open Set Filter Topology
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

theorem uniform_representing_densities_oai {a : ℝ} (p : RadialProfiles a) :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ D : ℝ, 2*Real.sqrt (2*p.R) < D →
    ∀ kmin : ℕ, ∃ Q₀ : ℕ, ∀ Q : ℕ, Q₀ ≤ Q →
    2 ≤ Q ∧ kmin ≤ Q ∧ ∀ P : ℕ → Finset Sphere,
      (∀ j, ProjectivelySeparated (D/Real.sqrt (Q^(j+1):ℕ)) (P (Q^(j+1)))) →
      ∀ j, ContDiff ℝ ∞ (density Q p.R p.f p.b P j) ∧
        DensityStage (density Q p.R p.f p.b P) Q c K j ∧
        PhaseBandwidth (density Q p.R p.f p.b P j) (densityBandwidth Q j) ∧
        OrbitMeanOne (density Q p.R p.f p.b P j) ∧
        IsProbabilityMeasure (densityMeasure (density Q p.R p.f p.b P j)) ∧
        Represents (densityMeasure (density Q p.R p.f p.b P j)) := by
  obtain ⟨B,F₁,B₁,hB,hF₁,hB₁,hbv,hfd,hbd⟩ := p.bounds
  obtain ⟨c,K,N,hc,hc1,hK,hN,hgap,hder⟩ := exists_density_constants p hB hF₁ hB₁
  refine ⟨c,K,hc,hK,?_⟩
  intro D hD kmin
  have hev := density_conditions_eventually (C₁ := 2*(Real.exp K*(2/c))*4^N*Real.exp 2)
    (R := p.R) (B := B) (D := 1+2*Real.sqrt (2*p.R)) hgap hder
  have hnat := tendsto_natCast_atTop_atTop.eventually hev
  obtain ⟨Q₁,hQ₁⟩ := eventually_atTop.mp hnat
  obtain ⟨Q₂,hQ₂⟩ := exists_nat_ge (2*p.R)
  refine ⟨max (max Q₁ Q₂) (max 2 kmin),?_⟩
  intro Q hQ
  have hQ1 : Q₁ ≤ Q := (le_max_left _ _).trans ((le_max_left _ _).trans hQ)
  have hQ2 : Q₂ ≤ Q := (le_max_right _ _).trans ((le_max_left _ _).trans hQ)
  have hQn : 2 ≤ Q := (le_max_left _ _).trans ((le_max_right _ _).trans hQ)
  have hQk : kmin ≤ Q := (le_max_right _ _).trans ((le_max_right _ _).trans hQ)
  have hQR : 2*p.R ≤ Q := hQ₂.trans (by exact_mod_cast hQ2)
  obtain ⟨hH,hsmall,hphase,hsecond,hderH,hderT⟩ := hQ₁ Q hQ1
  refine ⟨hQn,hQk,?_⟩
  intro P hP j
  have hq : 0 < Q := by omega
  have hdis : ∀ i, (P (Q^(i+1)):Set Sphere).PairwiseDisjoint (peakPatch (Q^(i+1)) p.R) :=
    fun i => peakPatch_disjoint (pow_pos hq _) p.R_pos hD (hP i)
  have hstage := density_induction hQn p.R_pos p.cutoff_lt hQR p.F_nonneg hB hF₁ hB₁
    (by linarith [Real.sqrt_nonneg (2*p.R)] : 1 ≤ 1+2*Real.sqrt (2*p.R)) (by linarith : 2*Real.sqrt (2*p.R) ≤ 1+2*Real.sqrt (2*p.R))
    hc hc1 hK.le hN p.smooth_f p.smooth_b p.tail p.small hbv hfd hbd P hdis
    hH hsmall hphase hsecond hderH hderT j
  have hsm := density_smooth hq p.cutoff_lt p.smooth_f p.smooth_b p.tail P j
  refine ⟨hsm,hstage,density_bandwidth hq p.cutoff_lt p.smooth_f p.smooth_b p.tail P j,
    density_orbit_mean hQn p.cutoff_lt p.smooth_f p.smooth_b p.tail P j,?_,?_⟩
  · exact densityMeasure_probability hsm.continuous (fun ξ => (hstage.positive ξ).le)
      (density_mass_one hQn p.R_pos p.cutoff_lt p.smooth_f p.smooth_b p.ode p.b_zero p.tail P j)
  · exact densityMeasure_represents hsm.continuous (fun ξ => (hstage.positive ξ).le)
      (density_polynomial_moment hQn p.R_pos p.cutoff_lt p.smooth_f p.smooth_b p.ode p.b_zero p.tail P j)

end PinchedHartogs.BaseConstruction

end

end OAI
end

theorem solution : type_of% @OAI.PinchedHartogs.BaseConstruction.uniform_representing_densities_oai := @OAI.PinchedHartogs.BaseConstruction.uniform_representing_densities_oai
