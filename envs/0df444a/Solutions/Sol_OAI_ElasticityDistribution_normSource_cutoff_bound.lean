-- Prove2me | solution 1 for OAI.ElasticityDistribution.normSource_cutoff_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:16:56.649731+00:00
-- url     : https://prove2.me/submissions/ce24aed5-361f-44d9-bc3d-ecace89b3377

import Mathlib
import Definitions.Def_OAIQ6El003
import Definitions.Def_OAIQ6El004
import Theorems.Thm_OAI_ElasticityDistribution_affine_cutoff_bound

section
-- module Solutions.OAIQ6_Elast.Elasticity_Regularity
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Actual distributional elliptic regularity dependencies of the physical and
planar weak-limit constructions. No regularity assumption on an L2 unknown is
used in the gain of Sobolev order below. -/
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal
namespace ElasticityRegularity

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma compact_derivative {g : E → ℂ} (hg : HasCompactSupport g) (m : E) :
    HasCompactSupport (fun x => fderiv ℝ g x m) :=
  (hg.fderiv ℝ).comp_left (g := fun T : E →L[ℝ] ℂ => T m) (by simp)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma smooth_derivative {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (m : E) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ g x m) :=
  (hg.fderiv_right (by simp)).clm_apply contDiff_const

lemma sobolev_zero_product {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (hb : MemLp g ∞ (volume : Measure E)) {u : 𝓢'(E,F)} (hu : MemSobolev 0 2 u) :
    MemSobolev 0 2 (smulLeftCLM F g u) := by
  obtain ⟨v,rfl⟩ := memSobolev_zero_iff.mp hu
  apply memSobolev_zero_iff.mpr
  exact ⟨hb.toLp g • v, (Lp.toTemperedDistribution_smul_eq hg hb v).symm⟩

end ElasticityRegularity

open scoped BigOperators SchwartzMap LineDeriv
open scoped SchwartzMap LineDeriv BigOperators
namespace ElasticityDistribution

open ElasticityAugmented ElasticityRegularity TemperedDistribution
lemma eval_smooth (a : Coeff) : ContDiff ℝ (⊤ : ℕ∞) (eval a) := (growth a).1

lemma dd_apply (i : Fin 3) (u : Dist) : dd i u = ∂_{e i} u := rfl

open ElasticityAugmented TrivSqZeroExt

lemma sd_apply (z : Fin 3 → ℂ) (i : Fin 3) (u : Dist) : sd z i u = dd i u+z i • u := rfl
end ElasticityDistribution

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Real ENNReal
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators
namespace ElasticityRegularity


section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma sobolev_sum {ι : Type*} (S : Finset ι) {s : ℝ} {v : ι → 𝓢'(E,F)}
    (hv : ∀ i ∈ S, MemSobolev s 2 (v i)) : MemSobolev s 2 (∑ i ∈ S, v i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi hS =>
    rw [Finset.sum_insert hi]
    exact (hv i (Finset.mem_insert_self _ _)).add
      (hS (fun j hj => hv j (Finset.mem_insert_of_mem hj)))

end

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma derivative_support_subset (g : E → ℂ) (m : E) :
    tsupport (fun x => fderiv ℝ g x m) ⊆ tsupport g :=
  (tsupport_comp_subset (g := fun T : E →L[ℝ] ℂ => T m) (by simp) (fderiv ℝ g)).trans
    (tsupport_fderiv_subset ℝ)

lemma LocalSobolev.mono {Ω : Set E} {s t : ℝ} {u : 𝓢'(E,F)}
    (h : LocalSobolev Ω s u) (hst : t ≤ s) : LocalSobolev Ω t u :=
  fun g hg hc hs => (h g hg hc hs).mono hst

lemma LocalSobolev.product_derivative {Ω : Set E} {s : ℝ} {u : 𝓢'(E,F)}
    (h : LocalSobolev Ω s u) {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ Ω) (m : E) :
    MemSobolev (s-1) 2 (smulLeftCLM F g (∂_{m} u)) := by
  have hdg := (compact_derivative hc m).hasTemperateGrowth (smooth_derivative hg m)
  have h1 := (h g hg hc hs).lineDerivOp (m := m)
  have h2 := h _ (smooth_derivative hg m) (compact_derivative hc m)
    ((derivative_support_subset g m).trans hs)
  have h3 := h1.sub (h2.mono (by linarith : s-1 ≤ s))
  rw [distribution_leibniz (hc.hasTemperateGrowth hg) m hdg,add_sub_cancel_left] at h3
  exact h3

end ElasticityRegularity

open scoped SchwartzMap LineDeriv BigOperators
open scoped SchwartzMap LineDeriv Laplacian BigOperators

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators
namespace ElasticityRegularity
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma MemSobolev.local_zero {u : 𝓢'(E,F)} (hu : MemSobolev 0 2 u) (Ω : Set E) :
    LocalSobolev Ω 0 u := by
  intro g hg hc _
  exact sobolev_zero_product (hc.hasTemperateGrowth hg) (compact_bounded_multiplier hg hc) hu

end ElasticityRegularity

open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators
open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators ENNReal
namespace ElasticityDistribution
open ElasticityAugmented ElasticityRegularity
namespace LocalSobolev
variable {Ω : Set X} {s t : ℝ} {u v : Dist}
lemma add (h : ElasticityRegularity.LocalSobolev Ω s u)
    (h' : ElasticityRegularity.LocalSobolev Ω s v) :
    ElasticityRegularity.LocalSobolev Ω s (u+v) := by
  intro g hg hc hs
  rw [map_add]
  exact (h g hg hc hs).add (h' g hg hc hs)
lemma sub (h : ElasticityRegularity.LocalSobolev Ω s u)
    (h' : ElasticityRegularity.LocalSobolev Ω s v) :
    ElasticityRegularity.LocalSobolev Ω s (u-v) := by
  intro g hg hc hs
  rw [map_sub]
  exact (h g hg hc hs).sub (h' g hg hc hs)
lemma smul (h : ElasticityRegularity.LocalSobolev Ω s u) (c : ℂ) :
    ElasticityRegularity.LocalSobolev Ω s (c • u) := by
  intro g hg hc hs
  rw [map_smul]
  exact (h g hg hc hs).smul c
lemma sum {ι : Type*} (S : Finset ι) {u : ι → Dist}
    (h : ∀ i ∈ S, ElasticityRegularity.LocalSobolev Ω s (u i)) :
    ElasticityRegularity.LocalSobolev Ω s (∑ i ∈ S, u i) := by
  intro g hg hc hs
  rw [map_sum]
  exact sobolev_sum S (fun i hi => h i hi g hg hc hs)
lemma coeff (h : ElasticityRegularity.LocalSobolev Ω s u) (a : Coeff) :
    ElasticityRegularity.LocalSobolev Ω s (a • u) := by
  intro g hg hc hs
  have := h (g*eval a) (hg.mul (eval_smooth a)) hc.mul_right (tsupport_mul_subset_left.trans hs)
  change MemSobolev s 2 (smulLeftCLM ℂ g (smulLeftCLM ℂ (eval a) u))
  rw [smulLeftCLM_smulLeftCLM_apply (growth a) (hc.hasTemperateGrowth hg),mul_comm]
  exact this
lemma derivative (h : ElasticityRegularity.LocalSobolev Ω s u) (i : Fin 3) :
    ElasticityRegularity.LocalSobolev Ω (s-1) (dd i u) := by
  intro g hg hc hs
  exact h.product_derivative hg hc hs (e i)
lemma shifted (h : ElasticityRegularity.LocalSobolev Ω s u) (z : Fin 3 → ℂ) (i : Fin 3) :
    ElasticityRegularity.LocalSobolev Ω (s-1) (sd z i u) :=
  add (derivative h i) (smul (h.mono (by linarith)) (z i))
lemma divergence {u : Fin 3 → Dist} (h : ∀ i, ElasticityRegularity.LocalSobolev Ω s (u i))
    (z : Fin 3 → ℂ) : ElasticityRegularity.LocalSobolev Ω (s-1) (divd z u) :=
  sum Finset.univ (fun i _ => shifted (h i) z i)
end LocalSobolev

lemma normSource_local {Ω : Set X} {s : ℝ} (z : Fin 3 → ℂ) (m n o : Coeff)
    (F : Fin 3 → Dist) (hF : ∀ i, ElasticityRegularity.LocalSobolev Ω s (F i)) :
    ∀ i, ElasticityRegularity.LocalSobolev Ω (s-1) (normSource z m n o F i) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · exact LocalSobolev.coeff (LocalSobolev.sub (LocalSobolev.divergence hF z)
      (LocalSobolev.smul (LocalSobolev.coeff (LocalSobolev.sum Finset.univ (fun i _ =>
        LocalSobolev.coeff ((hF i).mono (by linarith)) (dc i m))) n) 2)) o
  · exact LocalSobolev.coeff ((hF i).mono (by linarith)) n

end ElasticityDistribution

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Solvability
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! The Hahn--Banach / Riesz step used by the physical solvability argument.
This proves the functional-analytic implication, rather than postulating
existence of a right inverse. The physical test estimate is proved separately. -/

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

open MeasureTheory Complex SchwartzMap
open scoped BigOperators SchwartzMap LineDeriv
open scoped SchwartzMap LineDeriv BigOperators
open MeasureTheory Complex SchwartzMap
open scoped BigOperators SchwartzMap LineDeriv

open scoped BigOperators

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BigOperators
namespace ElasticityDistribution
open ElasticityAugmented ElasticityRegularity ElasticityCoeffBounds
open ElasticityPhysicalAlgebra (phase)
open ElasticityPhysicalDual

lemma lp_local_zero (Ω : Set X) (u : Lp ℂ 2 (volume : Measure X)) :
    ElasticityRegularity.LocalSobolev Ω 0 (u : Dist) :=
  ElasticityRegularity.MemSobolev.local_zero (memSobolev_zero_iff.mpr ⟨u,rfl⟩) Ω
end ElasticityDistribution

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_CGO
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityDistribution
open MeasureTheory TemperedDistribution

open scoped SchwartzMap LineDeriv Laplacian BigOperators ENNReal
open ElasticityAugmented ElasticityRegularity
lemma complex_zero_dist (u : Dist) : (0 : ℂ) • u=0 := zero_smul ℂ u
lemma complex_smul_dist_zero (c : ℂ) : c • (0 : Dist)=0 := @smul_zero ℂ Dist _ _ c

lemma divZeroCLM_apply (f : H3) : divZeroCLM f=divd 0 (fun j => (f j : Dist)) := by
  simp only [divZeroCLM,sum_apply,ContinuousLinearMap.comp_apply,lpProj,
    ContinuousLinearMap.proj_apply,Lp.toTemperedDistributionCLM_apply,
    divd,sd_apply,Pi.zero_apply,complex_zero_dist,add_zero,dd_apply,LineDeriv.lineDerivOpCLM_apply]
lemma divd_affine (z : Fin 3 → ℂ) (U : Fin 3 → Dist) :
    divd z U=divd 0 U+∑ i, z i • U i := by
  simp only [divd,sd_apply,Pi.zero_apply,complex_zero_dist,add_zero,Finset.sum_add_distrib]

/-- The source of the actual normalized system is also H^-1, with a uniform
polynomial phase bound depending on the fixed coefficients and cutoff only. -/
theorem normSource_cutoff_bound_oai {η : X → ℂ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hcη : HasCompactSupport η) (m n o : Coeff) :
    ∃ C : ℝ, 0<C ∧ ∀ (z : Fin 3 → ℂ) (f : H3),
      ∃ q : HV, (∀ i, sobolevInjection (-1) (q i)=smulLeftCLM ℂ η
        (normSource z m n o (fun j => (f j : Dist)) i)) ∧
        ‖q‖ ≤ C*(1+∑ d, ‖z d‖)^2*‖f‖ := by
  let T₀ : H3 →L[ℂ] Dist := (smulLeftCLM ℂ (eval o)).comp
    (divZeroCLM-(2 : ℂ) • (smulLeftCLM ℂ (eval n)).comp
      (∑ i, (smulLeftCLM ℂ (eval (dc i m))).comp (lpProj i)))
  let T₁ (i : Fin 3) : H3 →L[ℂ] Dist := (smulLeftCLM ℂ (eval o)).comp (lpProj i)
  have hT₀ (f : H3) : T₀ f=normSource 0 m n o (fun j => (f j : Dist)) 0 := by
    simp only [T₀,ContinuousLinearMap.comp_apply,sub_apply,smul_apply,sum_apply,
      divZeroCLM_apply,lpProj,ContinuousLinearMap.proj_apply,Lp.toTemperedDistributionCLM_apply,
      normSource,Fin.cons_zero,smul_def]
  have hT₁ (i : Fin 3) (f : H3) : T₁ i f=o • (f i : Dist) := rfl
  have hf (f : H3) (i : Fin 3) := lp_local_zero Set.univ (f i)
  obtain ⟨D,hD,hbD⟩ := affine_cutoff_bound (-1) T₀ T₁
    (fun f => by rw [hT₀]; simpa only [zero_sub] using normSource_local 0 m n o _ (hf f) 0 η hη hcη (Set.subset_univ _))
    (fun i f => ((LocalSobolev.coeff (hf f i) o) η hη hcη (Set.subset_univ _)).mono (by norm_num))
  have hc (i : Fin 3) := affine_cutoff_bound (-1)
    ((smulLeftCLM ℂ (eval n)).comp (lpProj i)) (fun _ => 0)
    (fun f => ((LocalSobolev.coeff (hf f i) n) η hη hcη (Set.subset_univ _)).mono (by norm_num))
    (fun _ _ => by simp only [zero_apply,map_zero]; exact memSobolev_fun_zero X ℂ _ _)
  choose B hB hb using hc
  let C := D+∑ i, B i
  have hs : 0≤∑ i, B i := Finset.sum_nonneg (fun i _ => (hB i).le)
  refine ⟨C,by dsimp [C]; positivity,fun z f => ?_⟩
  obtain ⟨q₀,hq₀,hn₀⟩ := hbD z f
  have hv (i : Fin 3) := hb i z f
  choose q hq hn using hv
  refine ⟨Fin.cons q₀ q,?_,?_⟩
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [Fin.cons_zero,hq₀,hT₀]
      congr 1
      simp only [normSource,Fin.cons_zero,hT₁]
      rw [divd_affine z]
      simp only [smul_def,map_sub,map_add,map_sum,map_smul]
      abel
    · simpa only [Fin.cons_succ,zero_apply,complex_smul_dist_zero,Finset.sum_const_zero,add_zero,lpProj,
        ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,
        Lp.toTemperedDistributionCLM_apply,normSource,smul_def] using hq i
  · apply (pi_norm_le_iff_of_nonneg (by dsimp [C]; positivity)).mpr
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · apply hn₀.trans
      gcongr
      exact le_add_of_nonneg_right hs
    · apply (hn i).trans
      gcongr
      have hh : B i≤∑ j, B j := Finset.single_le_sum (fun j _ => (hB j).le) (Finset.mem_univ i)
      exact hh.trans (le_add_of_nonneg_left hD.le)
end ElasticityDistribution

end

end OAI
end

theorem solution : type_of% @OAI.ElasticityDistribution.normSource_cutoff_bound_oai := @OAI.ElasticityDistribution.normSource_cutoff_bound_oai
