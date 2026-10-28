-- Prove2me | solution 1 for OAI.ElasticityDistribution.affine_cutoff_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:15:01.765141+00:00
-- url     : https://prove2.me/submissions/6acd0c57-cadf-457a-bf15-9fd994db1c59

import Mathlib
import Definitions.Def_OAIQ6El003
import Definitions.Def_OAIQ6El004

section
-- module Solutions.OAIQ6_Elast.Elasticity_LocalRegularity
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal BigOperators
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal
namespace ElasticityRegularity


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma LocalEqual.lp_ae {Ω : Set E} (hΩ : IsOpen Ω)
    (u v : Lp ℂ 2 (volume : Measure E))
    (h : LocalEqual Ω (u : 𝓢'(E,ℂ)) (v : 𝓢'(E,ℂ))) :
    ∀ᵐ x ∂(volume : Measure E), x ∈ Ω → u x=v x := by
  have hu : LocallyIntegrable (u : E → ℂ) (volume : Measure E) := (Lp.memLp u).locallyIntegrable (by norm_num)
  have hv : LocallyIntegrable (v : E → ℂ) (volume : Measure E) := (Lp.memLp v).locallyIntegrable (by norm_num)
  have he : ∀ᵐ x ∂(volume : Measure E), x ∈ Ω → (u x-v x)=0 := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((hu.sub hv).locallyIntegrableOn Ω) ?_
  · filter_upwards [he] with x hx
    intro hxΩ
    exact sub_eq_zero.mp (hx hxΩ)
  intro g hg hc hs
  let f : E → ℂ := fun x => (g x : ℂ)
  have hfc : HasCompactSupport f :=
    show HasCompactSupport (Complex.ofReal ∘ g) from hc.comp_left Complex.ofReal_zero
  have hfg : ContDiff ℝ (⊤ : ℕ∞) f :=
    (Complex.ofRealCLM.contDiff : ContDiff ℝ (⊤ : ℕ∞) Complex.ofReal).comp hg
  let φ : 𝓢(E,ℂ) := hfc.toSchwartzMap hfg
  have hfs : tsupport (φ : E → ℂ) ⊆ Ω := by
    change closure (Function.support f) ⊆ Ω
    apply Set.Subset.trans (closure_mono ?_) hs
    intro x hx hzero
    apply hx
    change (g x : ℂ)=0
    rw [hzero,Complex.ofReal_zero]
  have hh := h φ hfc hfs
  simp only [Lp.toTemperedDistribution_apply] at hh
  have hiu := hu.integrable_smul_left_of_hasCompactSupport hg.continuous hc
  have hiv := hv.integrable_smul_left_of_hasCompactSupport hg.continuous hc
  simp only [smul_sub]
  rw [integral_sub hiu hiv,sub_eq_zero]
  simp only [show (φ : E → ℂ)=f from rfl,f,Complex.real_smul,smul_eq_mul] at hh ⊢
  convert hh using 1
  all_goals try with_reducible_and_instances rfl

end ElasticityRegularity

open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Planar
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv
namespace ElasticityRegularity

/-- The closed graph argument supplies norms for genuine distribution operators,
not additional quantitative regularity assumptions. -/
theorem exists_continuous_lift
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z] [T2Space Z]
    (J : Y →L[ℂ] Z) (hJ : Function.Injective J) (T : X →L[ℂ] Z)
    (hT : ∀ x, ∃ y, J y=T x) :
    ∃ L : X →L[ℂ] Y, ∀ x, J (L x)=T x := by
  choose l hl using hT
  let L : X →ₗ[ℂ] Y := {
    toFun := l
    map_add' := fun x y => hJ (by rw [map_add,hl,hl,hl,map_add])
    map_smul' := fun c x => hJ (by rw [map_smul,hl,hl,map_smul]; rfl) }
  have hc : IsClosed (L.graph : Set (X × Y)) := by
    have he : (L.graph : Set (X × Y))={p | T p.1=J p.2} := by
      ext p
      change p.2=L p.1 ↔ T p.1=J p.2
      constructor
      · intro h
        rw [h]
        exact (hl p.1).symm
      · intro h
        apply hJ
        exact h.symm.trans (hl p.1).symm
    rw [he]
    exact isClosed_eq (T.continuous.comp continuous_fst) (J.continuous.comp continuous_snd)
  exact ⟨⟨L,L.continuous_of_isClosed_graph hc⟩,hl⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma lp_distribution_injective : Function.Injective
    (fun u : Lp ℂ 2 (volume : Measure E) => (u : 𝓢'(E,ℂ))) := by
  intro u v huv
  apply Lp.ext
  have h : LocalEqual Set.univ (u : 𝓢'(E,ℂ)) (v : 𝓢'(E,ℂ)) :=
    fun _ _ _ => congrArg (fun T : 𝓢'(E,ℂ) => T _) huv
  filter_upwards [h.lp_ae isOpen_univ u v] with x hx
  exact hx (Set.mem_univ x)

lemma sobolevInjection_injective (s : ℝ) :
    Function.Injective (sobolevInjection (E := E) s) := by
  intro u v huv
  have h := congrArg (besselPotential E ℂ s) huv
  have hh : (u : 𝓢'(E,ℂ))=(v : 𝓢'(E,ℂ)) := by
    simpa only [sobolevInjection,ContinuousLinearMap.comp_apply,
      besselPotential_besselPotential_apply,neg_add_cancel,besselPotential_zero,
      ContinuousLinearMap.id_apply,Lp.toTemperedDistributionCLM_apply] using h
  exact lp_distribution_injective hh

lemma sobolevInjection_mem (s : ℝ) (f : Lp ℂ 2 (volume : Measure E)) :
    MemSobolev s 2 (sobolevInjection s f) := by
  refine ⟨f,?_⟩
  simp only [sobolevInjection,ContinuousLinearMap.comp_apply,
    besselPotential_besselPotential_apply,neg_add_cancel,besselPotential_zero,
    ContinuousLinearMap.id_apply,Lp.toTemperedDistributionCLM_apply]

lemma memSobolev_iff_range (s : ℝ) (u : 𝓢'(E,ℂ)) :
    MemSobolev s 2 u ↔ ∃ f : Lp ℂ 2 (volume : Measure E), sobolevInjection s f=u := by
  constructor
  · rintro ⟨f,hf⟩
    refine ⟨f,?_⟩
    change besselPotential E ℂ (-s) (f : 𝓢'(E,ℂ))=u
    exact (besselPotential_neg_apply_eq_iff s (f : 𝓢'(E,ℂ)) u).mpr hf
  · rintro ⟨f,rfl⟩
    exact sobolevInjection_mem s f

end ElasticityRegularity

end

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

section
open scoped BigOperators
namespace ElasticityRegularity
/-- The precise polynomial loss for the shifted scalar-principal system. -/
theorem quadratic_parameter_norm {W ι : Type*} [NormedAddCommGroup W]
    [NormedSpace ℂ W] [Fintype ι] (R₀ R₂ : W) (R₁ : ι → W) :
    ∃ C : ℝ, 0<C ∧ ∀ z : ι → ℂ,
      ‖R₀+(∑ i, z i • R₁ i)+(∑ i, z i*z i) • R₂‖ ≤ C*(1+∑ i, ‖z i‖)^2 := by
  classical
  let S := ∑ i, ‖R₁ i‖
  refine ⟨‖R₀‖+S+‖R₂‖+1,by dsimp [S]; positivity,fun z => ?_⟩
  let Z := ∑ i, ‖z i‖
  have hZ : 0≤Z := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hS : 0≤S := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hz (i : ι) : ‖z i‖≤Z := Finset.single_le_sum (fun j _ => norm_nonneg (z j)) (Finset.mem_univ i)
  have hr (i : ι) : ‖R₁ i‖≤S := Finset.single_le_sum (fun j _ => norm_nonneg (R₁ j)) (Finset.mem_univ i)
  have hlin : ‖∑ i, z i • R₁ i‖ ≤ Z*S := by
    calc
      ‖∑ i, z i • R₁ i‖ ≤ ∑ i, ‖z i • R₁ i‖ := norm_sum_le _ _
      _ = ∑ i, ‖z i‖*‖R₁ i‖ := by simp only [norm_smul]
      _ ≤ ∑ i, ‖z i‖*S := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hr i) (norm_nonneg _))
      _ = Z*S := (Finset.sum_mul _ _ _).symm
  have hquad : ‖∑ i, z i*z i‖ ≤ Z^2 := by
    calc
      ‖∑ i, z i*z i‖ ≤ ∑ i, ‖z i*z i‖ := norm_sum_le _ _
      _ = ∑ i, ‖z i‖*‖z i‖ := by simp only [norm_mul]
      _ ≤ ∑ i, ‖z i‖*Z := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hz i) (norm_nonneg _))
      _ = Z^2 := by rw [← Finset.sum_mul]; change Z*Z=Z^2; ring
  have hn : ‖R₀+(∑ i, z i • R₁ i)+(∑ i, z i*z i) • R₂‖ ≤ ‖R₀‖+Z*S+Z^2*‖R₂‖ := by
    calc
      _ ≤ ‖R₀+(∑ i, z i • R₁ i)‖+‖(∑ i, z i*z i) • R₂‖ := norm_add_le _ _
      _ ≤ ‖R₀‖+Z*S+Z^2*‖R₂‖ := by
        rw [norm_smul]
        exact add_le_add ((norm_add_le _ _).trans (add_le_add_right hlin _))
          (mul_le_mul_of_nonneg_right hquad (norm_nonneg _))
  apply hn.trans
  change ‖R₀‖+Z*S+Z^2*‖R₂‖ ≤ (‖R₀‖+S+‖R₂‖+1)*(1+Z)^2
  have hW : 1 ≤ (1+Z)^2 := by nlinarith
  have hL : Z ≤ (1+Z)^2 := by nlinarith
  have hQ : Z^2 ≤ (1+Z)^2 := by nlinarith
  calc
    _ ≤ ‖R₀‖*(1+Z)^2+S*(1+Z)^2+‖R₂‖*(1+Z)^2 := by
      have h₀ := mul_le_mul_of_nonneg_left hW (norm_nonneg R₀)
      have h₁ := mul_le_mul_of_nonneg_left hL hS
      have h₂ := mul_le_mul_of_nonneg_left hQ (norm_nonneg R₂)
      nlinarith
    _ ≤ _ := by nlinarith [sq_nonneg (1+Z)]
end ElasticityRegularity

end
namespace ElasticityDistribution
open MeasureTheory TemperedDistribution

open scoped SchwartzMap LineDeriv Laplacian BigOperators ENNReal
open ElasticityAugmented ElasticityRegularity

/-- A bounded Sobolev realization of an actual affine distribution family. All
mapping properties are proved in the concrete applications below. -/
theorem affine_cutoff_bound_oai (s : ℝ) {η : X → ℂ}
    (T₀ : H3 →L[ℂ] Dist) (T₁ : Fin 3 → H3 →L[ℂ] Dist)
    (h₀ : ∀ f, MemSobolev s 2 (smulLeftCLM ℂ η (T₀ f)))
    (h₁ : ∀ d f, MemSobolev s 2 (smulLeftCLM ℂ η (T₁ d f))) :
    ∃ C : ℝ, 0<C ∧ ∀ (z : Fin 3 → ℂ) (f : H3),
      ∃ q : ElasticityDistribution.H,
        sobolevInjection s q=smulLeftCLM ℂ η (T₀ f+∑ d, z d • T₁ d f) ∧
        ‖q‖ ≤ C*(1+∑ d, ‖z d‖)^2*‖f‖ := by
  obtain ⟨L₀,hL₀⟩ := exists_continuous_lift (sobolevInjection s) (sobolevInjection_injective s)
    ((smulLeftCLM ℂ η).comp T₀) (fun f => (memSobolev_iff_range s _).mp (h₀ f))
  have hL₁ (d : Fin 3) := exists_continuous_lift (sobolevInjection s) (sobolevInjection_injective s)
    ((smulLeftCLM ℂ η).comp (T₁ d)) (fun f => (memSobolev_iff_range s _).mp (h₁ d f))
  choose L₁ hL₁ using hL₁
  obtain ⟨C,hC,hb⟩ := quadratic_parameter_norm L₀ (0 : H3 →L[ℂ] ElasticityDistribution.H) L₁
  refine ⟨C,hC,fun z f => ⟨(L₀+∑ d, z d • L₁ d) f,?_,?_⟩⟩
  · simp only [add_apply,sum_apply,smul_apply,map_add,map_sum,map_smul,hL₀,hL₁,
      ContinuousLinearMap.comp_apply]
  · have hh := hb z
    simp only [smul_zero,add_zero] at hh
    exact ((L₀+∑ d, z d • L₁ d).le_opNorm f).trans
      (mul_le_mul_of_nonneg_right hh (norm_nonneg f))

end ElasticityDistribution

end

end OAI
end

theorem solution : type_of% @OAI.ElasticityDistribution.affine_cutoff_bound_oai := @OAI.ElasticityDistribution.affine_cutoff_bound_oai
