-- Prove2me | solution 1 for OAI.ElasticityDistribution.physical_quantitative_correction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:36:43.734343+00:00
-- url     : https://prove2.me/submissions/a678ef6f-660a-45c8-98b5-4af0e9b14ed5

import Mathlib
import Definitions.Def_OAIQ6El006
import Theorems.Thm_OAI_ElasticityDistribution_physical_quantitative_H1
import Theorems.Thm_OAI_ElasticityDistribution_weak_smooth_solvability

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
namespace ElasticityCoeffBounds
open ElasticityAugmented ElasticityPhysicalEstimate

lemma ExteriorConstant.add {f g : Smooth} (hf : ExteriorConstant f) (hg : ExteriorConstant g) :
    ExteriorConstant (f+g) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨d, hd⟩ := hg
  refine ⟨c+d, ?_⟩
  have he : (fun x => ((f+g : Smooth) : X → ℂ) x - (c+d)) =
      (fun x => (f : X → ℂ) x-c) + (fun x => (g : X → ℂ) x-d) := by
    funext x
    change (f : X → ℂ) x + (g : X → ℂ) x - (c+d) = _
    dsimp
    ring
  rw [he]
  exact hc.add hd

lemma reciprocal_mul (f : Smooth) (hf : ∀ x, (f : X → ℂ) x ≠ 0) :
    reciprocal f hf * f = 1 := by
  apply Subtype.ext
  funext x
  exact inv_mul_cancel₀ (hf x)

open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder
open ElasticityPhysicalAlgebra (physical phase)

end ElasticityCoeffBounds

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BigOperators
namespace ElasticityDistribution
open ElasticityAugmented ElasticityRegularity ElasticityCoeffBounds
open ElasticityPhysicalAlgebra (phase)
open ElasticityPhysicalDual

lemma inverseCoeff_mul (f : Smooth) (hf : ExteriorConstant f) (hn : ∀ x, (f : X → ℂ) x ≠ 0) :
    inverseCoeff f hf hn*exteriorCoeff f hf=1 := by
  apply Subtype.ext
  exact reciprocal_mul f hn

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
open scoped ENNReal SchwartzMap BigOperators
open ElasticityAugmented ElasticityRegularity ElasticityCoeffBounds

section
open ElasticityPhysicalAlgebra (phase)

lemma norm_ofLp_le (u : ElasticityPhysicalDual.H) : ‖(fun i => u i : H3)‖ ≤ ‖u‖ := by
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr (fun i => PiLp.norm_apply_le u i)

lemma phase_envelope (α β : X) {h : ℝ} (hh : 0<h) (h1 : h≤1) :
    1+∑ i, ‖phase h α β i‖ ≤ h⁻¹*(1+∑ i, ‖(α i : ℂ)+Complex.I*(β i : ℂ)‖) := by
  have hi : 1≤h⁻¹ := (one_le_inv₀ hh).mpr h1
  simp only [phase]
  simp only [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hh]
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  nlinarith

/-- Actual physical correction with a proved polynomial interior bound. This
uses the uniform physical inverse and two true interior elliptic gains; taking
more terms in the finite CGO expansion absorbs its fixed sixth-power loss. -/
theorem physical_quantitative_correction_oai (R : ℝ) (hR : 1≤R)
    (Ω : Set X) (hΩ : Ω ⊆ Metric.closedBall 0 R) (α β : X) (hα : α ≠ 0)
    (lam m : Smooth) (hl : ExteriorConstant lam) (hm : ExteriorConstant m)
    (hrl : ∀ x, star ((lam : X → ℂ) x)=(lam : X → ℂ) x)
    (hrm : ∀ x, star ((m : X → ℂ) x)=(m : X → ℂ) x)
    (hm0 : ∀ x, (m : X → ℂ) x ≠ 0)
    (he0 : ∀ x, ((lam+m+m : Smooth) : X → ℂ) x ≠ 0)
    (χ : Fin 5 → X → ℂ) (hχ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (χ i))
    (hcχ : ∀ i, HasCompactSupport (χ i))
    (hnest : ∀ i : Fin 4, Set.EqOn (χ i.succ) 1 (tsupport (χ i.castSucc)))
    (hs : ∀ i, tsupport (χ i) ⊆ Ω) :
    ∃ C h₀ : ℝ, 0<C ∧ 0<h₀ ∧ ∀ h : ℝ, 0<h → h≤h₀ →
      ∀ f : Fin 3 → S, ∃ w : ElasticityPhysicalDual.H, ∃ q : HV,
        (∀ i, LocalEq Ω (phys (phase h α β) (exteriorCoeff lam hl) (exteriorCoeff m hm)
          (fun j => (w j : Dist)) i) (f i : Dist)) ∧
        (∀ i, sobolevInjection 1 (q i)=smulLeftCLM ℂ (χ 0)
          ((Fin.cons (divd (phase h α β) (fun j => (w j : Dist)))
            (fun j => (w j : Dist)) : Fin 4 → Dist) i)) ∧
        ‖w‖ ≤ C*‖ElasticityPhysicalDual.embed f‖ ∧
        ‖q‖ ≤ C*h⁻¹^6*‖ElasticityPhysicalDual.embed f‖ := by
  obtain ⟨A,h₀,hA,hh₀,hsol⟩ := weak_smooth_solvability R hR Ω hΩ α β hα lam m hl hm hrl hrm hm0 he0
  let n := inverseCoeff m hm hm0
  let o := inverseCoeff (lam+m+m) ((hl.add hm).add hm) he0
  have hn : n*exteriorCoeff m hm=1 := inverseCoeff_mul m hm hm0
  have ho : o*(exteriorCoeff lam hl+exteriorCoeff m hm+exteriorCoeff m hm)=1 := by
    apply Subtype.ext
    exact reciprocal_mul (lam+m+m) he0
  obtain ⟨B,hB,hest⟩ := physical_quantitative_H1 χ hχ hcχ hnest hs
    (exteriorCoeff lam hl) (exteriorCoeff m hm) n o hn ho
  let K := 1+∑ i, ‖(α i : ℂ)+Complex.I*(β i : ℂ)‖
  let C := A+B*K^6*(A+1)
  have hK : 0<K := by dsimp [K]; positivity
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,min h₀ 1,hC,lt_min hh₀ zero_lt_one,fun h hh hsmall f => ?_⟩
  obtain ⟨w,hw,heq,_⟩ := hsol h hh (hsmall.trans (min_le_left _ _)) f
  let ff : H3 := fun i => ElasticityBessel.L2 (f i)
  have hfeq (i : Fin 3) : (ff i : Dist)=(f i : Dist) := by
    simp only [ff,ElasticityBessel.L2,SchwartzMap.toLpCLM_apply,Lp.toTemperedDistribution_toLp_eq]
  have heq' : ∀ i, LocalEq Ω (phys (phase h α β) (exteriorCoeff lam hl) (exteriorCoeff m hm)
      (fun j => (w j : Dist)) i) (ff i : Dist) := by simpa only [hfeq] using heq
  obtain ⟨q,hq,hqn⟩ := hest (phase h α β) (fun i => w i) ff heq'
  have hf : ‖ff‖≤‖ElasticityPhysicalDual.embed f‖ := by
    exact norm_ofLp_le (ElasticityPhysicalDual.embed f)
  have hr : ‖(fun i => w i : H3)‖≤A*‖ElasticityPhysicalDual.embed f‖ :=
    (norm_ofLp_le w).trans hw
  have hph : 1+∑ i, ‖phase h α β i‖ ≤ h⁻¹*K := phase_envelope α β hh (hsmall.trans (min_le_right _ _))
  have hB' : B*K^6*(A+1)≤C := le_add_of_nonneg_left hA.le
  have hA' : A≤C := le_add_of_nonneg_right (by positivity)
  refine ⟨w,q,heq,hq,hw.trans (mul_le_mul_of_nonneg_right hA' (norm_nonneg _)),?_⟩
  calc
    ‖q‖ ≤ B*(1+∑ i, ‖phase h α β i‖)^6*(‖(fun i => w i : H3)‖+‖ff‖) := hqn
    _ ≤ B*(h⁻¹*K)^6*(A*‖ElasticityPhysicalDual.embed f‖+‖ElasticityPhysicalDual.embed f‖) := by gcongr
    _ = (B*K^6*(A+1))*h⁻¹^6*‖ElasticityPhysicalDual.embed f‖ := by ring
    _ ≤ C*h⁻¹^6*‖ElasticityPhysicalDual.embed f‖ := by gcongr
end
open ElasticityPhysicalAlgebra (phase physical)

end ElasticityDistribution

end

end OAI
end

theorem solution : type_of% @OAI.ElasticityDistribution.physical_quantitative_correction_oai := @OAI.ElasticityDistribution.physical_quantitative_correction_oai
