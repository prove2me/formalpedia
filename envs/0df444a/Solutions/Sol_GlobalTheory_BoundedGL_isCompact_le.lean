-- Prove2me | solution 1 for GlobalTheory.BoundedGL.isCompact_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:02:42.784197+00:00
-- url     : https://prove2.me/submissions/b50b924d-3ffe-4826-9873-6a6cde448ac0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicIntegersCompact_IsCompactAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCompactGLBoundedEntriesCompletionFinitePlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
noncomputable section
open GlobalTheory GlobalTheory.BoundedGL
variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
namespace GlobalTheory.BoundedGL
theorem _root_.solution (c : WithZero (Multiplicative ℤ)) :
    IsCompact {x : w.adicCompletion E | Valued.v x ≤ c} := by
  by_cases hc : c = 0
  · have e : {x : w.adicCompletion E | Valued.v x ≤ c} = {0} := by
      ext x
      simp [hc]
    rw [e]
    exact isCompact_singleton
  · obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer E
    set u : w.adicCompletion E := ((π ^ (-WithZero.log c) : E) : w.adicCompletion E) with hu
    have hvu : Valued.v u = c := by
      rw [hu, valuedAdicCompletion_eq_valuation', map_zpow₀, hπ, ← WithZero.exp_zsmul]
      simp [WithZero.exp_log hc]
    have hu0 : u ≠ 0 := by
      intro h
      rw [h, map_zero] at hvu
      exact hc hvu.symm
    have hO : IsCompact {x : w.adicCompletion E | Valued.v x ≤ 1} := by
      have := PI.IntAdCpctOpenWork.isCompact_adicCompletionIntegers w
      convert this using 1
      ext x
      simp [mem_adicCompletionIntegers]
    have e : {x : w.adicCompletion E | Valued.v x ≤ c} = (fun y => u * y) '' {x | Valued.v x ≤ 1} := by
      ext x
      constructor
      · intro hx
        refine ⟨u⁻¹ * x, ?_, by simp [hu0]⟩
        show Valued.v (u⁻¹ * x) ≤ 1
        rw [map_mul, map_inv₀, hvu]
        exact inv_mul_le_one_of_le₀ hx zero_le'
      · rintro ⟨y, hy, rfl⟩
        show Valued.v (u * y) ≤ c
        rw [map_mul, hvu]
        exact mul_le_of_le_one_right' hy
    rw [e]
    exact hO.image (continuous_mul_left u)
end GlobalTheory.BoundedGL
