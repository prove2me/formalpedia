-- Prove2me | solution 1 for GlobalTheory.LocFlat.exists_clopen_ch_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:30:28.997664+00:00
-- url     : https://prove2.me/submissions/1df30256-b587-4ff3-8085-15f1f6c31ca8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective
import Theorems.Thm_GlobalTheory_SplitWeil_exists_cball_subset
import Theorems.Thm_GlobalTheory_SplitWeil_isCompact_cball
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_cball
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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
namespace GlobalTheory.LocFlat
theorem _root_.solution (ψ : AddChar k Circle) (hψ : Continuous ψ) :
    ∃ W : Set (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), IsClopen W ∧ IsCompact W ∧
      (0 : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) ∈ W ∧
      ∀ z ∈ W, ‖((ψ (-ch z) : Circle) : ℂ) - 1‖ < 1 / 2 := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  have hU : {y : k | ‖((ψ (-y) : Circle) : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 (0 : k) := by
    refine (isOpen_lt ?_ continuous_const).mem_nhds ?_
    · exact (continuous_subtype_val.comp (hψ.comp continuous_neg)).sub continuous_const |>.norm
    · simp
  obtain ⟨s₀, hs₀⟩ := exists_cball_subset hU
  let W : Set (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :=
    Set.univ.pi fun _ => Set.univ.pi fun _ => cball s₀
  have hWc : IsCompact W := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_cball s₀
  have hWo : IsOpen W :=
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => isOpen_cball s₀
  refine ⟨W, ⟨hWc.isClosed, hWo⟩, hWc, ?_, ?_⟩
  · intro r _ s _
    simp [cball]
  · intro z hz
    apply hs₀
    show valuation k (ch z) ≤ valuation k (s₀ : k)
    exact Valuation.map_sum_le _ fun i _ => hz _ (Set.mem_univ _) _ (Set.mem_univ _)
end GlobalTheory.LocFlat
