-- Prove2me | solution 1 for GlobalTheory.LocFlat.flat_SB_onto
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:49:58.427153+00:00
-- url     : https://prove2.me/submissions/f38cd371-6a3f-4903-8122-656db25c4b64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective
import Theorems.Thm_GlobalTheory_LocFlat_flatSB_generic
import Theorems.Thm_GlobalTheory_LocFlat_flatOnto_generic
import Theorems.Thm_GlobalTheory_LocFlat_continuous_restOf
import Theorems.Thm_GlobalTheory_LocFlat_continuous_glue
import Theorems.Thm_GlobalTheory_LocFlat_glue_restOf
import Theorems.Thm_GlobalTheory_LocFlat_continuous_readCol
import Theorems.Thm_GlobalTheory_LocFlat_continuous_extCol
import Theorems.Thm_GlobalTheory_LocFlat_extCol_readCol
import Theorems.Thm_GlobalTheory_LocFlat_readCol_ptCol
import Theorems.Thm_GlobalTheory_LocFlat_restOf_ptCol
import Theorems.Thm_GlobalTheory_LocFlat_continuous_readRow
import Theorems.Thm_GlobalTheory_LocFlat_continuous_extRow
import Theorems.Thm_GlobalTheory_LocFlat_extRow_readRow
import Theorems.Thm_GlobalTheory_LocFlat_readRow_ptRow
import Theorems.Thm_GlobalTheory_LocFlat_restOf_ptRow
import Theorems.Thm_GlobalTheory_LocFlat_continuous_ptCol
import Theorems.Thm_GlobalTheory_LocFlat_continuous_ptRow
import Theorems.Thm_GlobalTheory_LocFlat_flCol_eq_integral
import Theorems.Thm_GlobalTheory_LocFlat_flRow_eq_integral
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.LocFlat
namespace GlobalTheory.LocFlat
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ), 1 ≤ p → (p ≤ c + 1 → (∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), GlobalTheory.LocFlat.flCol ψ ν p Φ ∈ SB _) ∧ ∀ Ψ ∈ SB (Matrix n (n' ⊕ Unit) k), ∃ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), GlobalTheory.LocFlat.flCol ψ ν p Φ = Ψ) ∧ (p ≤ c → (∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), GlobalTheory.LocFlat.flRow ψ ν p Φ ∈ SB _) ∧ ∀ Ψ ∈ SB (Matrix (n ⊕ Unit) n' k), ∃ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), GlobalTheory.LocFlat.flRow ψ ν p Φ = Ψ) := by
  intro k _ _ _ _ _ _ ψ ν hψ hν n n' _ _ _ _ c p hp1
  haveI := GlobalTheory.SplitWeil.t2Space k
  refine ⟨fun hpc => ?_, fun hpc => ?_⟩
  · have hp : p - 1 < c + 1 := by omega
    refine ⟨fun Φ hΦ => ?_, fun Ψ hΨ => ?_⟩
    · rw [flCol_eq_integral]
      exact flatSB_generic ψ ν p (ptCol p) (continuous_ptCol p) (readCol p hp) (continuous_readCol p hp)
        (restOf (rdCol p)) (continuous_restOf _) (readCol_ptCol p hp1 hp) (restOf_ptCol p) Φ hΦ
    · obtain ⟨Φ, hΦ, h⟩ := flatOnto_generic ψ hψ ν hν p (ptCol p) (readCol p hp) (continuous_readCol p hp)
        (restOf (rdCol p)) (continuous_restOf _) (glue (rdCol p) extCol) (continuous_glue _ continuous_extCol)
        (glue_restOf _ _ _ (extCol_readCol p hp)) (readCol_ptCol p hp1 hp) (restOf_ptCol p) Ψ hΨ
      exact ⟨Φ, hΦ, by rw [flCol_eq_integral]; exact funext h⟩
  · have hp : p - 1 < c := by omega
    refine ⟨fun Φ hΦ => ?_, fun Ψ hΨ => ?_⟩
    · rw [flRow_eq_integral]
      exact flatSB_generic ψ ν p (ptRow p) (continuous_ptRow p) (readRow p hp) (continuous_readRow p hp)
        (restOf (rdRow p)) (continuous_restOf _) (readRow_ptRow p hp1 hp) (restOf_ptRow p) Φ hΦ
    · obtain ⟨Φ, hΦ, h⟩ := flatOnto_generic ψ hψ ν hν p (ptRow p) (readRow p hp) (continuous_readRow p hp)
        (restOf (rdRow p)) (continuous_restOf _) (glue (rdRow p) extRow) (continuous_glue _ continuous_extRow)
        (glue_restOf _ _ _ (extRow_readRow p hp)) (readRow_ptRow p hp1 hp) (restOf_ptRow p) Ψ hΨ
      exact ⟨Φ, hΦ, by rw [flRow_eq_integral]; exact funext h⟩
end GlobalTheory.LocFlat
