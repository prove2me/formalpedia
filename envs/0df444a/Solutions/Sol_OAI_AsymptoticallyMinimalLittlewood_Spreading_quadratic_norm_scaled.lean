-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Spreading.quadratic_norm_scaled
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:32:52.879849+00:00
-- url     : https://prove2.me/submissions/5feeba8d-ceed-40ef-ae1e-90f40d64bbb5

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Spreading.lean:L19-L48
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Spreading.quadratic_norm_scaled. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_uniform_quadratic_integration

-- ---- from OAI.Analysis.Littlewood.Spreading ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement).
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
namespace OAI

universe uI uE uJ uK

namespace AsymptoticallyMinimalLittlewood
namespace Spreading
noncomputable section
open QuadraticTail MeasureTheory Filter Topology Complex
open scoped BigOperators ContDiff FourierTransform SchwartzMap

/-- The uniform stationary-phase bound in the squared, scale-invariant form
needed for every retained spread Fourier coefficient. -/
lemma quadratic_norm_scaled {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) (hg1 : ∀ x, ‖g x‖≤1)
    {β : ℝ} (hβ : β≠0) :
    ∃ C : ℝ, 0≤C ∧ ∀ T, 0<T → ∀ u : ℝ,
      T*|β| *‖∫ x : ℝ, g x*phase (T*β) u x‖^2 ≤ (1+C/T)^2 := by
  let C := Real.pi / |β| * (∫ ξ : ℝ, ξ^2 * ‖(𝓕⁻ (hg.toSchwartzMap hgs) : 𝓢(ℝ,ℂ)) ξ‖)
  have hC : 0≤C := mul_nonneg (div_nonneg Real.pi_pos.le (abs_nonneg _))
    (integral_nonneg (fun ξ ↦ mul_nonneg (sq_nonneg _) (norm_nonneg _)))
  refine ⟨C,hC,?_⟩
  intro T hT u
  obtain ⟨E,hE,he⟩ := uniform_quadratic_integration g hg hgs hβ hT u
  change ‖E‖≤C/T at hE
  change (∫ x : ℝ, g x*phase (T*β) u x) = _ at he
  have hphase : ‖realPhase (2*Real.pi*(Real.sign β/8-u^2/(2*T*β)))‖ = 1 := by
    exact norm_realPhase _
  have hsqrt : 0<Real.sqrt (T*|β|) := Real.sqrt_pos.mpr (mul_pos hT (abs_pos.mpr hβ))
  have hn : ‖g (u/(T*β))+E‖≤1+C/T :=
    (norm_add_le _ _).trans (add_le_add (hg1 _) hE)
  have hnorm : ‖∫ x : ℝ, g x*phase (T*β) u x‖ =
      ‖g (u/(T*β))+E‖/Real.sqrt (T*|β|) := by
    rw [he,norm_mul,norm_div,hphase,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hsqrt]
    ring
  rw [hnorm,div_pow,Real.sq_sqrt (mul_pos hT (abs_pos.mpr hβ)).le]
  have hc : 0≤1+C/T := by positivity
  have hn2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  calc
    _ = ‖g (u/(T*β))+E‖^2 := by field_simp
    _ ≤ _ := hn2

variable {I : Type uI} [Fintype I] [DecidableEq I]

end
end Spreading
end AsymptoticallyMinimalLittlewood

namespace AsymptoticallyMinimalLittlewood
namespace Auxiliary
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Finset UnitAddTorus Complex

end
end Auxiliary
end AsymptoticallyMinimalLittlewood

namespace AsymptoticallyMinimalLittlewood.Auxiliary
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Finset UnitAddTorus Complex QuadraticTail Spreading

end
end AsymptoticallyMinimalLittlewood.Auxiliary

namespace AsymptoticallyMinimalLittlewood.Auxiliary
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Finset UnitAddTorus Complex QuadraticTail Spreading

end
end AsymptoticallyMinimalLittlewood.Auxiliary

namespace AsymptoticallyMinimalLittlewood.Auxiliary
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Finset UnitAddTorus Complex QuadraticTail Spreading

attribute [instance] FinitePacket.fintypeI FinitePacket.fintypeJ FinitePacket.nonemptyI

end
end AsymptoticallyMinimalLittlewood.Auxiliary

namespace AsymptoticallyMinimalLittlewood.Auxiliary
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Finset UnitAddTorus Complex QuadraticTail Spreading

end
end AsymptoticallyMinimalLittlewood.Auxiliary

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Spreading
open QuadraticTail MeasureTheory Filter Topology Complex
open scoped BigOperators ContDiff FourierTransform SchwartzMap


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Spreading.quadratic_norm_scaled := @_root_.OAI.AsymptoticallyMinimalLittlewood.Spreading.quadratic_norm_scaled
