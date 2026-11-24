-- Prove2me | solution 1 for GlobalTheory.PosOne.RrLin.exists_open_translations
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:23:16.698344+00:00
-- url     : https://prove2.me/submissions/95f5a2f0-03ea-4be9-90dc-65b214a77be0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ToOneSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotientIntegralParabolicUnfolding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SecondCountableLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OpEOmTargetUnipotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotientIntegralLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsLinearIsQuotIntTInt
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_FourierJacobiAverage_app_coe
import Theorems.Thm_GlobalTheory_StepData_IntM_add
import Theorems.Thm_GlobalTheory_StepData_MaxM_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app app_coe)
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.PosOne GlobalTheory.PosOne.RrLin
namespace GlobalTheory.PosOne.RrLin
theorem _root_.solution {M : Type*} [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] {Φ : M → ℂ} (hΦ : Φ ∈ SB M) :
    ∃ Λ : AddSubgroup M, IsOpen (Λ : Set M) ∧ ∀ x, ∀ y ∈ Λ, Φ (x + y) = Φ x := by
  let Λ : AddSubgroup M :=
    { carrier := {y | ∀ x, Φ (x + y) = Φ x}
      zero_mem' := fun x => by simp
      add_mem' := fun {y z} hy hz x => by rw [← add_assoc, hz, hy]
      neg_mem' := fun {y} hy x => by rw [← hy (x + -y)]; simp }
  refine ⟨Λ, Λ.isOpen_of_mem_nhds (g := 0) ?_, fun x y hy => hy x⟩
  have h1 : ∀ᶠ y in 𝓝 (0 : M), ∀ x ∈ tsupport Φ, Φ (x + y) = Φ x := by
    refine IsCompact.eventually_forall_of_forall_eventually hΦ.2 fun x _ => ?_
    have h2 : IsLocallyConstant fun q : M × M => (Φ (q.2 + q.1), Φ q.2) :=
      (hΦ.1.comp_continuous (continuous_snd.add continuous_fst)).prodMk
        (hΦ.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (0, x)] with q hq
    simp only [Prod.mk.injEq, add_zero] at hq
    rw [hq.1, hq.2]
  have h2 : ∀ᶠ y in 𝓝 (0 : M), ∀ x ∈ tsupport Φ, Φ (x + -y) = Φ x := by
    have ht : Filter.Tendsto (fun y : M => -y) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_neg (G := M)).tendsto 0
    exact ht.eventually h1
  filter_upwards [h1, h2] with y hs hs' x
  by_cases hx : x ∈ tsupport Φ
  · exact hs x hx
  by_cases hx' : x + y ∈ tsupport Φ
  · rw [← hs' _ hx']; simp
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']
end GlobalTheory.PosOne.RrLin
