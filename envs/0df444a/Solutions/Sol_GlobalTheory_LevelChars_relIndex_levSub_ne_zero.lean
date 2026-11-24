-- Prove2me | solution 1 for GlobalTheory.LevelChars.relIndex_levSub_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:53:07.818621+00:00
-- url     : https://prove2.me/submissions/cb5488e3-4e8c-4440-bfbd-df2734cbcc74

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FiniteChars
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HCFFromRecipA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicIntegersCompact_IsCompactAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayClassGroupIdelicFiniteIndex
import Theorems.Thm_GlobalTheory_LevelChars_exists_finset_close

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
    (hS : S.Finite) : (levSub L S N).relIndex (levSub L ∅ 0) ≠ 0 := by
  classical
  haveI : Finite S := hS.to_subtype
  choose F hF using fun v : S => exists_finset_close L v.1 N
  have hint : ∀ a : levSub L ∅ 0, ∀ v, Valued.v (compAt L v (a : (AdeleRing (𝓞 L) L)ˣ)) ≤ 1 :=
    fun a v => le_of_eq (a.2 v).1
  choose g hg hg' using fun (a : levSub L ∅ 0) (v : S) => hF v (compAt L v.1 a) (hint a v.1)
  let φ : levSub L ∅ 0 ⧸ (levSub L S N).subgroupOf (levSub L ∅ 0) → ((v : S) → (F v : Set (v.1.adicCompletion L))) :=
    fun q v => ⟨g q.out v, hg q.out v⟩
  have hφ : Function.Injective φ := by
    intro q q' hqq
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq, Subgroup.mem_subgroupOf]
    intro w
    refine ⟨((q.out⁻¹ * q'.out).2 w).1, fun hw => ?_⟩
    have e1 : g q.out ⟨w, hw⟩ = g q'.out ⟨w, hw⟩ := congrArg Subtype.val (congrFun hqq ⟨w, hw⟩)
    have h1 := hg' q.out ⟨w, hw⟩
    have h2 := hg' q'.out ⟨w, hw⟩
    rw [e1] at h1
    set a : (AdeleRing (𝓞 L) L)ˣ := (q.out : (AdeleRing (𝓞 L) L)ˣ)
    set b : (AdeleRing (𝓞 L) L)ˣ := (q'.out : (AdeleRing (𝓞 L) L)ˣ)
    have hinv : Valued.v (compAt L w a⁻¹) = 1 := ((q.out⁻¹).2 w).1
    have hc : compAt L w a⁻¹ * compAt L w a = 1 := by rw [← compAt_mul, inv_mul_cancel, compAt_one]
    have e2 : compAt L w ((q.out⁻¹ * q'.out : levSub L ∅ 0) : (AdeleRing (𝓞 L) L)ˣ) - 1 =
        compAt L w a⁻¹ * ((compAt L w b - g q'.out ⟨w, hw⟩) - (compAt L w a - g q'.out ⟨w, hw⟩)) := by
      have : ((q.out⁻¹ * q'.out : levSub L ∅ 0) : (AdeleRing (𝓞 L) L)ˣ) = a⁻¹ * b := rfl
      rw [this, compAt_mul]
      linear_combination hc
    rw [e2, map_mul, hinv, one_mul]
    exact (Valuation.map_sub _ _ _).trans (max_le h2 h1)
  haveI : Finite (levSub L ∅ 0 ⧸ (levSub L S N).subgroupOf (levSub L ∅ 0)) := Finite.of_injective φ hφ
  exact Subgroup.index_ne_zero_of_finite
end GlobalTheory.LevelChars
