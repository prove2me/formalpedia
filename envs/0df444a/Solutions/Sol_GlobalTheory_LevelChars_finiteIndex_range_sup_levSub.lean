-- Prove2me | solution 1 for GlobalTheory.LevelChars.finiteIndex_range_sup_levSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:13:12.656237+00:00
-- url     : https://prove2.me/submissions/4c8b1c11-7778-422e-95d6-3942bd56d3b6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FiniteChars
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HCFFromRecipA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicIntegersCompact_IsCompactAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayClassGroupIdelicFiniteIndex
import Theorems.Thm_GlobalTheory_LevelChars_relIndex_levSub_ne_zero
import Theorems.Thm_GlobalTheory_LevelChars_levSub_le_levSub_empty
import Theorems.Thm_GlobalTheory_LevelChars_finiteIndex_range_sup_levSub_empty

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
theorem _root_.solution (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ)
    (hS : S.Finite) :
    ((Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range ⊔ levSub L S N).FiniteIndex := by
  set R := (Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range
  have hle := levSub_le_levSub_empty L S N
  haveI := finiteIndex_range_sup_levSub_empty L
  have hT : R ⊔ levSub L S N ≤ R ⊔ levSub L ∅ 0 := sup_le_sup_left hle _
  have h1 : (R ⊔ levSub L S N).relIndex (levSub L ∅ 0) ≠ 0 := by
    intro h0
    have hd : (R ⊔ levSub L S N).relIndex (levSub L ∅ 0) ∣ (levSub L S N).relIndex (levSub L ∅ 0) :=
      Subgroup.relIndex_dvd_of_le_left (levSub L ∅ 0) le_sup_right
    rw [h0] at hd
    exact relIndex_levSub_ne_zero L S N hS (Nat.eq_zero_of_zero_dvd hd)
  have h2 : R ⊔ levSub L S N ⊔ levSub L ∅ 0 = R ⊔ levSub L ∅ 0 := by
    rw [sup_assoc, sup_eq_right.2 hle]
  have h3 : (R ⊔ levSub L S N).relIndex (R ⊔ levSub L ∅ 0) ≠ 0 := by
    rw [← h2, Subgroup.relIndex_sup_left]; exact h1
  rw [Subgroup.finiteIndex_iff, ← Subgroup.relIndex_mul_index hT]
  exact mul_ne_zero h3 (Subgroup.FiniteIndex.index_ne_zero)
end GlobalTheory.LevelChars
