-- Prove2me | solution 1 for GlobalTheory.InertSupp.Unram.valuation_det_KO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:54:45.428431+00:00
-- url     : https://prove2.me/submissions/aa293ad6-ee74-497c-8068-d819bc0aa329

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviEmbMulSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NoUnramTwistOfNoInert

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces ValuativeRel Matrix MeasureTheory
open GlobalTheory GlobalTheory.InertSupp GlobalTheory.InertSupp.Unram
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
open ValuativeRel Matrix MeasureTheory
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.InertSupp.Unram
namespace _root_.GlobalTheory.InertSupp.Unram
theorem _root_.solution {m : Type} [Fintype m] [DecidableEq m] {g : GL m k}
    (hg : g ∈ _root_.GlobalTheory.SplitWeil.KO k m) :
    valuation k (GeneralLinearGroup.det g : k) = 1 := by
  unfold _root_.GlobalTheory.SplitWeil.KO at hg
  obtain ⟨h, rfl⟩ := hg
  have hdet : (GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap (𝒪[k]) k) h) : k)
      = algebraMap (𝒪[k]) k (GeneralLinearGroup.det h : 𝒪[k]) := by
    simp [GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rw [hdet]
  exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)
end _root_.GlobalTheory.InertSupp.Unram
end GlobalTheory.InertSupp.Unram
