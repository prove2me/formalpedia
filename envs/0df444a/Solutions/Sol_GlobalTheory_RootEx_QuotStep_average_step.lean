-- Prove2me | solution 1 for GlobalTheory.RootEx.QuotStep.average_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:19:02.028133+00:00
-- url     : https://prove2.me/submissions/f122dfaa-b3d9-4a35-9ebb-9cca1c6c6aa9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreservingTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicIntersection
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_integral_comp_mp
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_integral_swap_three
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_continuous_chart
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_chartN_mem
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_continuous_embX
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_proper_chart
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_integral_volN
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_mul
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.QuotStep
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
namespace GlobalTheory.RootEx.QuotStep
theorem _root_.solution {p q : ℕ} {E : (n → k) → GL (n ⊕ Fin c) k} (hE : IsSplit ν p q E)
    (μX : Measure (GL n k)) [μX.IsHaarMeasure] {F : GL (n ⊕ Fin c) k → ℂ} (hF : F ∈ SB (GL (n ⊕ Fin c) k))
    (h : GL (n ⊕ Fin c) k) :
    ∫ β, ∫ x, ∫ e, F (embX c x * chartB p e * (E β * h)) ∂(Measure.pi fun _ => ν) ∂μX ∂(Measure.pi fun _ => ν) =
      ∫ x, (∫ u : N k n c q, F (embX c x * (u : GL (n ⊕ Fin c) k) * h) ∂(volN ν n c q)) ∂μX := by
  haveI := secondCountable k
  haveI := t2Space k
  obtain ⟨T, hT, hT'⟩ := hE
  let a : GL n k × ({rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev q rs.1 < lev q rs.2} → k) → ℂ :=
    fun t => F (embX c t.1 * chartN q t.2 * h)
  have ha : Continuous a := hF.1.continuous.comp (((continuous_embX.comp continuous_fst).mul
    ((continuous_chart _).comp continuous_snd)).mul continuous_const)
  obtain ⟨D, hD, hD'⟩ := proper_chart _ (chartN_mem (k := k) (n := n) (c := c) q) _
    (hF.2.isCompact.image (continuous_mul_right h⁻¹))
  have hs : HasCompactSupport a :=
    HasCompactSupport.of_support_subset_isCompact hD fun t ht => hD' t ⟨_, subset_tsupport _ ht, by simp⟩
  have hi := ((MeasurePreserving.id μX).prod hT).integrable_comp_of_integrable
    (ha.integrable_of_hasCompactSupport hs)
  have h3 := integral_swap_three μX _ _ _ hi
  simp only [Function.comp_apply, Prod.map, id, a, hT', mul_assoc] at h3
  simp only [mul_assoc]
  rw [← h3]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [integral_volN ν q fun u => F (embX c x * (u * h)), ← integral_comp_mp hT
    (f := fun e => F (embX c x * (chartN q e * h))) (hF.1.continuous.comp (continuous_const.mul
      ((continuous_chart _).mul continuous_const))).aestronglyMeasurable]
  simp only [hT', mul_assoc]
end GlobalTheory.RootEx.QuotStep
