-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.StdLattice.ind_mem_SB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:06:30.170209+00:00
-- url     : https://prove2.me/submissions/5dac141e-5092-483a-9fc4-ec788d27fce7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_SchrodingerModelSelfDualLatticeStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsStd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.StdLattice
variable {R : Type} [CommRing R] {κ : Type} [Fintype κ]
variable [TopologicalSpace R]
namespace GlobalTheory.CompanionTheory.StdLattice
theorem _root_.solution [T2Space R] {O : Subring R} (hc : IsCompact (O : Set R)) (ho : IsOpen (O : Set R)) :
    ind O κ ∈ SB (κ → R) := by
  have hO : IsClosed (O : Set R) := hc.isClosed
  have hset : {x : κ → R | ∀ i, x i ∈ O} = Set.univ.pi (fun _ => (O : Set R)) := by
    ext x
    simp [Set.mem_pi]
  have hS : IsOpen {x : κ → R | ∀ i, x i ∈ O} := by
    rw [hset]
    exact isOpen_set_pi Set.finite_univ (fun _ _ => ho)
  have hS' : IsClosed {x : κ → R | ∀ i, x i ∈ O} := by
    rw [hset]
    exact isClosed_set_pi (fun _ _ => hO)
  show IsLocallyConstant (ind O κ) ∧ HasCompactSupport (ind O κ)
  refine ⟨fun t => ?_, ?_⟩
  · show IsOpen (Set.indicator {x : κ → R | ∀ i, x i ∈ O} (fun _ => (1 : ℂ)) ⁻¹' t)
    rw [Set.indicator_preimage]
    exact ((IsLocallyConstant.const (1 : ℂ) t).inter hS).union
      ((IsLocallyConstant.const (0 : ℂ) t).sdiff hS')
  · exact HasCompactSupport.of_support_subset_isCompact
      (by rw [hset]; exact isCompact_univ_pi fun _ => hc) Set.support_indicator_subset
end GlobalTheory.CompanionTheory.StdLattice
