-- Prove2me | solution 1 for GlobalTheory.LevelUnfold.gluedS_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:41:36.578686+00:00
-- url     : https://prove2.me/submissions/ea4ffdc2-4032-4f71-8ba9-beaf88489036

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FlagVolumeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemSmulOfMemFlagSubOne
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise ENNReal
noncomputable section
open GlobalTheory GlobalTheory.LevelUnfold
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} {c : ℕ} {q : Unif k}
open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise ENNReal
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} {c : ℕ} {q : _root_.GlobalTheory.LatPair.Unif k}
namespace GlobalTheory.LevelUnfold
namespace _root_.GlobalTheory.LevelUnfold
theorem _root_.solution {L : Submodule 𝒪[k] (n → k)} {f : n → k}
    {M : Submodule 𝒪[k] (n ⊕ Fin c → k)} :
    _root_.GlobalTheory.LatPair.gluedS q c L f ≤ M ↔ (∀ y ∈ L, _root_.GlobalTheory.LatPair.inX k n c y ∈ M) ∧
      q.inv • _root_.GlobalTheory.LatPair.avec k n c 1 +
          _root_.GlobalTheory.LatPair.inX k n c f ∈ M ∧
      ∀ i : Fin c, 0 < i.val →
        q.inv • _root_.GlobalTheory.LatPair.avec k n c (i.val + 1) ∈ M := by
  unfold _root_.GlobalTheory.LatPair.gluedS
  rw [sup_le_iff, sup_le_iff, Submodule.map_le_iff_le_comap, Submodule.span_singleton_le_iff_mem,
    Submodule.span_le, and_assoc]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · intro h i hi
    exact h ⟨i.val + 1, by omega, by omega, rfl⟩
  · rintro h y ⟨j, hj2, hjc, rfl⟩
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    exact h ⟨m, by omega⟩ (by simp only; omega)
end _root_.GlobalTheory.LevelUnfold
end GlobalTheory.LevelUnfold
