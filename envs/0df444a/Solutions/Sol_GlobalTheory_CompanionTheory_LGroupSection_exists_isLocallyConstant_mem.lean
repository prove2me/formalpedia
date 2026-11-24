-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LGroupSection.exists_isLocallyConstant_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:48:17.633814+00:00
-- url     : https://prove2.me/submissions/a8cfbba3-7ccd-448e-86f8-80ef29c75265

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsContinuousSectionQuotient

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
theorem _root_.solution {X : Type*} [TopologicalSpace X] (V : ℕ → Set X)
    (hV : ∀ n, IsClopen (V n)) (hcov : ∀ x, ∃ n, x ∈ V n) :
    ∃ f : X → ℕ, IsLocallyConstant f ∧ ∀ x, x ∈ V (f x) := by
  classical
  refine ⟨fun x => Nat.find (hcov x), ?_, fun x => Nat.find_spec (hcov x)⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨V (Nat.find (hcov x)) ∩ ⋂ j ∈ Finset.range (Nat.find (hcov x)), (V j)ᶜ,
    (hV _).isOpen.inter (isOpen_biInter_finset fun j _ => (hV j).compl.isOpen), ?_, ?_⟩
  · refine ⟨Nat.find_spec (hcov x), ?_⟩
    simp only [mem_iInter, Finset.mem_range]
    exact fun j hj => Nat.find_min (hcov x) hj
  · rintro y ⟨hy1, hy2⟩
    simp only [mem_iInter, Finset.mem_range] at hy2
    refine le_antisymm (Nat.find_min' _ hy1) ?_
    by_contra hlt
    exact hy2 _ (not_le.1 hlt) (Nat.find_spec (hcov y))
end GlobalTheory.CompanionTheory.LGroupSection
