-- Prove2me | solution 1 for GlobalTheory.OpenStratumMaps.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:02:35.298614+00:00
-- url     : https://prove2.me/submissions/693ac8fd-2f1f-4bc1-b727-54c0fd1b2563

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_WeilTensorLiftConclusion
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_BoundaryVanishingPullback
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_OpenClosedSequences
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DeterminedOnOpenStratum
import Theorems.Thm_GlobalTheory_OpenStratumMaps_exists_factor
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
open scoped TensorProduct
open GlobalTheory GlobalTheory.OpenStratumMaps
variable {F G H V W U : Type} [Field F] [Group G] [Group H] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup U] [Module F U]
namespace GlobalTheory.OpenStratumMaps
theorem _root_.solution {ρ : Representation F G V} {σ : Representation F G W} {τ : Representation F G U}
    (S T : Subrepresentation ρ) (e : (subQuot S T).Equiv σ)
    (h : ∀ f : σ.IntertwiningMap τ, ∀ w, f w = 0) (q : ρ.IntertwiningMap τ)
    (hq : ∀ v ∈ T.toSubmodule, q v = 0) : ∀ v ∈ S.toSubmodule, q v = 0 := by
  let p : S.toRepresentation.IntertwiningMap (subQuot S T) :=
    ⟨Submodule.mkQ _, fun g => LinearMap.ext fun v => rfl⟩
  let qS : S.toRepresentation.IntertwiningMap τ :=
    ⟨q.toLinearMap ∘ₗ S.toSubmodule.subtype, fun g => LinearMap.ext fun v => q.isIntertwining _ _ g v⟩
  obtain ⟨q', hq'⟩ := exists_factor (e.toIntertwiningMap.comp p)
    (e.toLinearEquiv.surjective.comp (Submodule.mkQ_surjective _)) qS (fun v hv => by
      have h1 : e.toLinearEquiv (Submodule.Quotient.mk v) = 0 := hv
      rw [LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero] at h1
      exact hq _ h1)
  intro v hv
  exact (hq' ⟨v, hv⟩).symm.trans (h q' _)
end GlobalTheory.OpenStratumMaps
