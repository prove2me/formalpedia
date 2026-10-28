-- Prove2me | solution 1 for OAI.ElasticityCGO.physical_cgo_from_recursion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:29:40.459538+00:00
-- url     : https://prove2.me/submissions/294c64f1-325e-4759-a7e8-45f0220717eb

import Mathlib
import Definitions.Def_OAIQ6El006
import Theorems.Thm_OAI_ElasticityCGO_cut_truncation_residual
import Theorems.Thm_OAI_ElasticityDistribution_classical_quantitative_correction

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
open scoped ENNReal SchwartzMap BigOperators
open ElasticityAugmented ElasticityRegularity ElasticityCoeffBounds
open ElasticityPhysicalAlgebra (phase physical)
open ElasticityPhysicalDual (embed)

lemma finiteResidual_bound (h : ℝ) (hh : 0≤h) (h1 : h≤1) (f₀ f₁ : Fin 3 → S) :
    ‖embed (finiteResidual h f₀ f₁)‖ ≤ h^7*(‖embed f₀‖+‖embed f₁‖) := by
  have hp : h^8≤h^7 := by nlinarith [pow_nonneg hh 7]
  calc
    ‖embed (finiteResidual h f₀ f₁)‖ ≤ ‖(h : ℂ)^8 • embed f₀‖+‖(h : ℂ)^7 • embed f₁‖ := by
      simpa only [finiteResidual,map_add,map_smul] using
        norm_add_le ((h : ℂ)^8 • embed f₀) ((h : ℂ)^7 • embed f₁)
    _ = h^8*‖embed f₀‖+h^7*‖embed f₁‖ := by
      simp only [norm_smul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hh]
    _ ≤ h^7*(‖embed f₀‖+‖embed f₁‖) := by nlinarith [norm_nonneg (embed f₀)]

/-- Finite physical CGO residuals have a classical correction whose full
physical-divergence H1 error tends to zero at an explicit linear rate. -/
theorem finite_classical_correction (R : ℝ) (hR : 1≤R)
    (Ω Ω' : Set X) (hΩ : Ω ⊆ Metric.closedBall 0 R) (hΩ' : IsOpen Ω') (hsub : Ω' ⊆ Ω)
    (α β : X) (hα : α ≠ 0)
    (lam m : Smooth) (hl : ExteriorConstant lam) (hm : ExteriorConstant m)
    (hrl : ∀ x, star ((lam : X → ℂ) x)=(lam : X → ℂ) x)
    (hrm : ∀ x, star ((m : X → ℂ) x)=(m : X → ℂ) x)
    (hm0 : ∀ x, (m : X → ℂ) x ≠ 0)
    (he0 : ∀ x, ((lam+m+m : Smooth) : X → ℂ) x ≠ 0)
    (χ : Fin 5 → X → ℂ) (hχ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (χ i))
    (hcχ : ∀ i, HasCompactSupport (χ i))
    (hnest : ∀ i : Fin 4, Set.EqOn (χ i.succ) 1 (tsupport (χ i.castSucc)))
    (hs : ∀ i, tsupport (χ i) ⊆ Ω) (h1 : Set.EqOn (χ 0) 1 Ω')
    (f₀ f₁ : Fin 3 → S) :
    ∃ C h₀ : ℝ, 0<C ∧ 0<h₀ ∧ ∀ h : ℝ, 0<h → h≤h₀ →
      ∃ w : ElasticityPhysicalDual.H, ∃ q : HV, ∃ v : Fin 3 → S,
        (∀ i, ∀ᵐ x ∂(volume : Measure X), x ∈ Ω' → w i x=v i x) ∧
        (∀ i, Set.EqOn (physical (phase h α β) (eval (exteriorCoeff lam hl))
          (eval (exteriorCoeff m hm)) v i : X → ℂ) (finiteResidual h f₀ f₁ i : X → ℂ) Ω') ∧
        (∀ i, sobolevInjection 1 (q i)=smulLeftCLM ℂ (χ 0)
          ((Fin.cons (divd (phase h α β) (fun j => (w j : Dist)))
            (fun j => (w j : Dist)) : Fin 4 → Dist) i)) ∧
        ‖w‖ ≤ C*h^7 ∧ ‖q‖ ≤ C*h := by
  obtain ⟨A,h₀,hA,hh₀,hsol⟩ := classical_quantitative_correction R hR Ω Ω' hΩ hΩ' hsub
    α β hα lam m hl hm hrl hrm hm0 he0 χ hχ hcχ hnest hs h1
  let K := ‖embed f₀‖+‖embed f₁‖
  let C := A*(K+1)
  have hK : 0≤K := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hC : 0<C := mul_pos hA (by linarith)
  refine ⟨C,min h₀ 1,hC,lt_min hh₀ zero_lt_one,fun h hh hsmall => ?_⟩
  obtain ⟨w,q,v,hv,hphys,hq,hw,hqn⟩ := hsol h hh (hsmall.trans (min_le_left _ _))
    (finiteResidual h f₀ f₁)
  have hf := finiteResidual_bound h hh.le (hsmall.trans (min_le_right _ _)) f₀ f₁
  have hAK : A*K≤C := by dsimp [C]; nlinarith
  refine ⟨w,q,v,hv,hphys,hq,?_,?_⟩
  · calc
      ‖w‖ ≤ A*(h^7*K) := hw.trans (mul_le_mul_of_nonneg_left hf hA.le)
      _ ≤ C*h^7 := by nlinarith [pow_nonneg hh.le 7]
  · calc
      ‖q‖ ≤ A*h⁻¹^6*(h^7*K) := hqn.trans (mul_le_mul_of_nonneg_left hf (by positivity))
      _ = (A*K)*h := by field_simp
      _ ≤ C*h := mul_le_mul_of_nonneg_right hAK hh.le

lemma correction_cancels_residual (Ω : Set X) (z : Fin 3 → ℂ) (lam m : X → ℂ)
    (u v f : Fin 3 → S)
    (hu : ∀ i, Set.EqOn (physical z lam m u i : X → ℂ) (f i : X → ℂ) Ω)
    (hv : ∀ i, Set.EqOn (physical z lam m v i : X → ℂ) (f i : X → ℂ) Ω) :
    ∀ i, Set.EqOn (physical z lam m (u-v) i : X → ℂ) 0 Ω := by
  have he := (ElasticityPhysicalDual.physicalLM z lam m).map_sub u v
  change physical z lam m (u-v)=physical z lam m u-physical z lam m v at he
  intro i x hx
  rw [he]
  change physical z lam m u i x-physical z lam m v i x=0
  rw [hu i hx,hv i hx,sub_self]
end ElasticityDistribution

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Transfer
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped BigOperators SchwartzMap
namespace ElasticityCGO
open ElasticityAugmented
open ElasticityPhysicalAlgebra (toSmooth toSmooth_apply physical phase)
open ElasticityDistribution (finiteResidual)

lemma phase_eq (h : ℝ) (α β : X) :
    phase h α β=(h : ℂ)⁻¹ • (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) := by
  funext i
  simp only [phase,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]
end ElasticityCGO

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_PhysicalCGO
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityCGO

section
open MeasureTheory Set TemperedDistribution
open scoped SchwartzMap ENNReal BigOperators
open ElasticityAugmented
open ElasticityCoeffBounds (ExteriorConstant)
open ElasticityRegularity (sobolevInjection)
open ElasticityPhysicalAlgebra (phase physical)
open ElasticityDistribution (HV Dist divd)

/-- A genuinely compatible finite amplitude series gives exact smooth physical
CGO fields. The correction is the same estimated L2 solution, and its full
physical divergence is H1-small. Neither a physical-solvability statement nor
convergence of a formal infinite series is assumed. -/
theorem physical_cgo_from_recursion_oai (R : ℝ) (hR : 1≤R)
    (Ω U : Set X) (hΩ : Ω⊆Metric.closedBall 0 R) (hU : IsOpen U) (hsub : U⊆Ω)
    (α β : X) (hα : α≠0)
    (hθ : ∑ i,((α i : ℂ)+Complex.I*(β i : ℂ))*((α i : ℂ)+Complex.I*(β i : ℂ))=0)
    (lam m : Smooth) (hl : ExteriorConstant lam) (hm : ExteriorConstant m)
    (hrl : ∀ x,star ((lam : X → ℂ) x)=(lam : X → ℂ) x)
    (hrm : ∀ x,star ((m : X → ℂ) x)=(m : X → ℂ) x)
    (hm0 : ∀ x,(m : X → ℂ) x≠0)
    (he0 : ∀ x,((lam+m+m : Smooth) : X → ℂ) x≠0)
    (χ : Fin 5 → X → ℂ) (hχ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (χ i))
    (hcχ : ∀ i,HasCompactSupport (χ i))
    (hnest : ∀ i : Fin 4,EqOn (χ i.succ) 1 (tsupport (χ i.castSucc)))
    (hs : ∀ i,tsupport (χ i)⊆Ω) (h1 : EqOn (χ 0) 1 U)
    (a : ℕ → Amplitude Smooth)
    (hR₀ : leadingR (localCoord hU) (fun i => (α i : ℂ)+Complex.I*(β i : ℂ))
      (restrictSmooth U lam) (restrictSmooth U m) (localAmp U (a 0)).1 (localAmp U (a 0)).2=0)
    (hn₀ : normal (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) (a 0).1=0)
    (hrec : ∀ j<8,RecursOn hU (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) lam m (a j) (a (j+1))) :
    ∃ C h₀ : ℝ, 0<C ∧ 0<h₀ ∧ ∀ h : ℝ,0<h → h≤h₀ →
      ∃ w : ElasticityPhysicalDual.H,∃ q : HV,∃ v : Fin 3 → S,
        (∀ i,∀ᵐ x ∂(volume : Measure X),x∈U → w i x=v i x) ∧
        (∀ i,EqOn (physical (phase h α β) lam m
          ((fun j => cut ⟨χ 0,hχ 0⟩ (hcχ 0) ((truncation (h : ℂ) 8 a).1 j))-v) i : X → ℂ) 0 U) ∧
        (∀ i,sobolevInjection 1 (q i)=smulLeftCLM ℂ (χ 0)
          ((Fin.cons (divd (phase h α β) (fun j => (w j : Dist)))
            (fun j => (w j : Dist)) : Fin 4 → Dist) i)) ∧
        ‖w‖≤C*h^7 ∧ ‖q‖≤C*h := by
  let θ : Fin 3 → ℂ := fun i => (α i : ℂ)+Complex.I*(β i : ℂ)
  let f₀ : Fin 3 → S := fun i => cut ⟨χ 0,hχ 0⟩ (hcχ 0) (residual0 lam m (a 8) i)
  let f₁ : Fin 3 → S := fun i => cut ⟨χ 0,hχ 0⟩ (hcχ 0) (residual1 θ lam m (a 8) i)
  obtain ⟨C,h₀,hC,hh₀,hsol⟩ := ElasticityDistribution.finite_classical_correction R hR Ω U hΩ hU hsub
    α β hα lam m hl hm hrl hrm hm0 he0 χ hχ hcχ hnest hs h1 f₀ f₁
  refine ⟨C,h₀,hC,hh₀,fun h hh hsmall => ?_⟩
  obtain ⟨w,q,v,hv,hphys,hq,hw,hqn⟩ := hsol h hh hsmall
  refine ⟨w,q,v,hv,?_,hq,hw,hqn⟩
  apply ElasticityDistribution.correction_cancels_residual U (phase h α β) lam m
    (fun j => cut ⟨χ 0,hχ 0⟩ (hcχ 0) ((truncation (h : ℂ) 8 a).1 j)) v
    (ElasticityDistribution.finiteResidual h f₀ f₁) _ hphys
  intro i
  rw [phase_eq]
  exact cut_truncation_residual hU θ hθ lam m ⟨χ 0,hχ 0⟩ hl.growth hm.growth
    (hcχ 0) h1 h (ne_of_gt hh) a hR₀ hn₀ hrec i
end
open Set
open ElasticityAugmented
open ElasticityNegativeOrder (cutoff)

end ElasticityCGO

end

end OAI
end

theorem solution : type_of% @OAI.ElasticityCGO.physical_cgo_from_recursion_oai := @OAI.ElasticityCGO.physical_cgo_from_recursion_oai
