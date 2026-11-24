-- Prove2me | solution 1 for GlobalTheory.RootEx.QuotLinear.integrable_average
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:18:49.405916+00:00
-- url     : https://prove2.me/submissions/8820668f-bde8-420a-be09-a49f82c031f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotientIntegralLinear
import Theorems.Thm_GlobalTheory_RootEx_QuotLinear_isClosed_N
import Theorems.Thm_GlobalTheory_RootEx_QuotLinear_continuous_embX
import Theorems.Thm_GlobalTheory_RootEx_QuotLinear_exists_compact_prod
import Theorems.Thm_GlobalTheory_RootEx_QuotLinear_finiteOnCompacts_volN
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx Topology
open scoped Pointwise
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.QuotLinear
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}
variable [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.RootEx.QuotLinear
theorem _root_.solution (ν : Measure k) [ν.IsAddHaarMeasure] (μX : Measure (GL n k)) [μX.IsHaarMeasure]
    {F : GL (n ⊕ Fin c) k → ℂ} (hF : F ∈ SB (GL (n ⊕ Fin c) k)) (h : GL (n ⊕ Fin c) k) :
    (∀ x : GL n k, Integrable (fun u : N k n c p => F (embX c x * (u : GL (n ⊕ Fin c) k) * h)) (volN ν n c p)) ∧
    Integrable (fun x : GL n k =>
      ∫ u : N k n c p, F (embX c x * (u : GL (n ⊕ Fin c) k) * h) ∂(volN ν n c p)) μX := by
  haveI := finiteOnCompacts_volN (n := n) (c := c) (p := p) ν
  haveI : LocallyCompactSpace (N k n c p) :=
    (isClosed_N (k := k) (n := n) (c := c) (p := p)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (N k n c p) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : IsLocallyFiniteMeasure (volN ν n c p) := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : SigmaFinite (volN ν n c p) := sigmaFinite_of_locallyFinite
  have hK : IsCompact ((fun g => g * h⁻¹) '' tsupport F) := hF.2.isCompact.image (by fun_prop)
  obtain ⟨A, B, hA, hB, hAB⟩ := exists_compact_prod (p := p) hK
  have hz : ∀ (x : GL n k) (u : N k n c p), ¬ (x ∈ A ∧ u ∈ B) →
      F (embX c x * (u : GL (n ⊕ Fin c) k) * h) = 0 := fun x u hn => by
    by_contra h0
    exact hn (hAB x u ⟨_, subset_tsupport _ h0, by simp⟩)
  have hc : Continuous fun z : GL n k × N k n c p => F (embX c z.1 * (z.2 : GL (n ⊕ Fin c) k) * h) :=
    hF.1.continuous.comp (((continuous_embX.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)).mul continuous_const)
  refine ⟨fun x => ?_, ?_⟩
  · exact (hc.comp (Continuous.prodMk_right x)).integrable_of_hasCompactSupport
      (HasCompactSupport.intro hB fun u hu => hz x u fun h => hu h.2)
  · have hi : Integrable (fun z : GL n k × N k n c p => F (embX c z.1 * (z.2 : GL (n ⊕ Fin c) k) * h))
        (μX.prod (volN ν n c p)) :=
      hc.integrable_of_hasCompactSupport (HasCompactSupport.intro (hA.prod hB) fun z hz' => hz z.1 z.2 hz')
    exact hi.integral_prod_left
end GlobalTheory.RootEx.QuotLinear
