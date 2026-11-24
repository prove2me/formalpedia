-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LGroupSection.exists_subgroup_seq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:42:09.130255+00:00
-- url     : https://prove2.me/submissions/9626d340-649d-4e06-bd92-7d85fe2d0c86

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsContinuousSectionQuotient
import Theorems.Thm_GroundTheory_Automorphic_exists_openSubgroup_isCompact_subset


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter Set
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LGroupSection
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace GlobalTheory.CompanionTheory.LGroupSection
theorem _root_.solution [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [FirstCountableTopology G] :
    ∃ K : ℕ → Subgroup G, K 0 = ⊤ ∧ (∀ n, K (n + 1) ≤ K n) ∧ (∀ n, IsOpen (K n : Set G)) ∧
      (∀ n, IsCompact (K (n + 1) : Set G)) ∧ ∀ W ∈ 𝓝 (1 : G), ∃ n, (K n : Set G) ⊆ W := by
  obtain ⟨U, hU⟩ := (𝓝 (1 : G)).exists_antitone_basis
  choose L hLc hLU using fun n =>
    GroundTheory.Automorphic.exists_openSubgroup_isCompact_subset (hU.1.mem_of_mem (i := n) trivial)
  obtain ⟨K, hK0, hsucc⟩ : ∃ K : ℕ → Subgroup G, K 0 = ⊤ ∧
      ∀ n, K (n + 1) = K n ⊓ (L n : Subgroup G) :=
    ⟨fun n => Nat.rec (motive := fun _ => Subgroup G) ⊤
      (fun n S => S ⊓ (L n : Subgroup G)) n, rfl, fun _ => rfl⟩
  have hopen : ∀ n, IsOpen (K n : Set G) := by
    intro n
    induction n with
    | zero =>
      rw [hK0]
      exact isOpen_univ
    | succ n ih =>
      rw [hsucc, Subgroup.coe_inf]
      exact ih.inter (L n).isOpen
  have hle : ∀ n, K (n + 1) ≤ L n := fun n => by
    rw [hsucc]
    exact inf_le_right
  refine ⟨K, hK0, fun n => by rw [hsucc]; exact inf_le_left, hopen, fun n => ?_, fun W hW => ?_⟩
  · have hclosed : IsClosed (K (n + 1) : Set G) :=
      (⟨K (n + 1), hopen (n + 1)⟩ : OpenSubgroup G).isClosed
    exact (hLc n).of_isClosed_subset hclosed (hle n)
  · obtain ⟨n, -, hn⟩ := hU.1.mem_iff.1 hW
    exact ⟨n + 1, fun g hg => hn (hLU n (hle n hg))⟩
end GlobalTheory.CompanionTheory.LGroupSection
