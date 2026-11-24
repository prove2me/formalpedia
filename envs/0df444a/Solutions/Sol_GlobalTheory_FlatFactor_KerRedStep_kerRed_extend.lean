-- Prove2me | solution 1 for GlobalTheory.FlatFactor.KerRedStep.kerRed_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:40:34.013428+00:00
-- url     : https://prove2.me/submissions/f4c76377-3fb8-4809-b7cf-8a7f6b165983

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsRead
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousCharactersLocallyConstantNonarchLocalF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LinearMapKillingPartialEvalIntegralKernelTranslaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LinearMapKillsPartialEvalIntegralKernelOfLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_KernelReductionExtendEvaluatedIntegrated
import Theorems.Thm_GlobalTheory_FlatFactor_KerRedStep_mul_sum_law
import Theorems.Thm_GlobalTheory_FlatFactor_KerRedStep_trans_sum_law
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_T_linearMap_killing_partialEvalIntegralKernel_translation_invariant
import Theorems.Thm_GlobalTheory_T_linearMap_kills_partialEvalIntegralKernel_of_laws
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open GlobalTheory GlobalTheory.FlatFactor GlobalTheory.FlatFactor.KerRedStep
namespace GlobalTheory.FlatFactor.KerRedStep
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (m m' : Type) [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m'] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB (Matrix m m' k) →ₗ[ℂ] M) (β : Matrix m m' k) (ev it ev' it' : Finset (m × m')), ev ⊆ ev' → it ⊆ it' → Disjoint ev' it' → GlobalTheory.FlatFactor.KerRed ν ev it β l → (∀ e ∈ ev', e ∉ ev → ∀ (b : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = (ψ (b * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Θ.1 t) → l Θ' = l Θ) → (∀ e ∈ it', e ∉ it → ∀ (a : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = Θ.1 (t + Matrix.single e.1 e.2 a)) → l Θ' = l Θ) → GlobalTheory.FlatFactor.KerRed ν ev' it' β l := by
  intro k _ _ _ _ _ _ ψ ν hψc hψ1 hν m m' _ _ _ _ M _ _ l β ev it ev' it' hev hit hd hK hmul htr
  have hd0 : Disjoint ev it := Finset.disjoint_of_subset_left hev (Finset.disjoint_of_subset_right hit hd)
  have L1 : (∀ e ∈ ev, ∀ (b : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = (ψ (b * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Θ.1 t) → l Θ' = l Θ) := by
    intro e he b Θ Θ' h
    have he' : e ∉ it := Finset.disjoint_left.mp hd0 he
    have h0 : l (Θ' - Θ) = 0 := hK _ fun t => by
      unfold GlobalTheory.FlatFactor.red
      have hz : ∀ a, (Θ' - Θ).1 (GlobalTheory.FlatFactor.fill ev it β t a) = 0 := by
        intro a
        have hf : GlobalTheory.FlatFactor.fill ev it β t a e.1 e.2 = β e.1 e.2 := by
          simp [GlobalTheory.FlatFactor.fill, he, he']
        simp [h, hf]
      simp [hz]
    rwa [map_sub, sub_eq_zero] at h0
  have hM : (∀ e ∈ ev', ∀ (b : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = (ψ (b * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Θ.1 t) → l Θ' = l Θ) := by
    intro e he
    by_cases h : e ∈ ev
    · exact L1 e h
    · exact hmul e he h
  have hT : (∀ e ∈ it', ∀ (a : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = Θ.1 (t + Matrix.single e.1 e.2 a)) → l Θ' = l Θ) := by
    intro e he
    by_cases h : e ∈ it
    · exact GlobalTheory.T.linearMap_killing_partialEvalIntegralKernel_translation_invariant k ψ ν hψc hψ1 hν m m' M l β ev it hd0 hK e h
    · exact htr e he h
  exact GlobalTheory.T.linearMap_kills_partialEvalIntegralKernel_of_laws k ψ ν hψc hψ1 hν m m' M l β ev' it' hd
    (mul_sum_law k ψ ν hψc hψ1 hν m m' M l β ev' hM) (trans_sum_law k ψ ν hψc hψ1 hν m m' M l β it' hT)
end GlobalTheory.FlatFactor.KerRedStep
