-- Prove2me | solution 1 for GlobalTheory.LevelChars.exists_finset_close
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:44:44.431692+00:00
-- url     : https://prove2.me/submissions/577607ef-59e8-46fe-b647-6018259e61c2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FiniteChars
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HCFFromRecipA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicIntegersCompact_IsCompactAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayClassGroupIdelicFiniteIndex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField
open GlobalTheory GlobalTheory.LevelChars
namespace GlobalTheory.LevelChars
theorem _root_.solution (L : Type) [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) (N : ℕ) :
    ∃ F : Finset (v.adicCompletion L), ∀ x : v.adicCompletion L, Valued.v x ≤ 1 →
      ∃ f ∈ F, Valued.v (x - f) ≤ WithZero.exp (-(N : ℤ)) := by
  classical
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer L v
  set s : v.adicCompletion L := ((π ^ N : L) : v.adicCompletion L) with hsdef
  have hs : Valued.v s = WithZero.exp (-(N : ℤ)) := by
    rw [hsdef, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_pow, hπ, ← WithZero.exp_nsmul]
    congr 1
    simp
  have hball : IsOpen {y : v.adicCompletion L | Valued.v y < Valued.v s} := by
    have h := Valued.isOpen_ball (v.adicCompletion L) (Valued.v.restrict s)
    simpa [Valuation.restrict_lt_iff] using h
  obtain ⟨t, -, ht⟩ := (PI.IntAdCpctOpenWork.isCompact_adicCompletionIntegers (F := L) v).elim_nhds_subcover
    (fun x => {y | Valued.v (y - x) < Valued.v s})
    (fun x _ => (hball.preimage (continuous_id.sub continuous_const)).mem_nhds (by
      show Valued.v (x - x) < Valued.v s
      rw [sub_self, map_zero, hs]
      exact zero_lt_iff.2 WithZero.exp_ne_zero))
  refine ⟨t, fun x hx => ?_⟩
  have hxO : x ∈ (v.adicCompletionIntegers L : Set (v.adicCompletion L)) :=
    by rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]; exact hx
  obtain ⟨f, hf, hxf⟩ := Set.mem_iUnion₂.1 (ht hxO)
  exact ⟨f, hf, le_of_lt (hs ▸ hxf)⟩
end GlobalTheory.LevelChars
