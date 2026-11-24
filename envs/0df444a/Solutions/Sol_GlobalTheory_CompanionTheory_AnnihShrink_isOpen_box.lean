-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AnnihShrink.isOpen_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:17:21.064739+00:00
-- url     : https://prove2.me/submissions/b3f94352-518a-4f5b-9fe8-5646d9cdd033

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticeAnnihilatorWithinNhds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix ValuativeRel
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AnnihShrink
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.CompanionTheory.AnnihShrink
theorem _root_.solution (n : ℕ) (b : k) (hb : b ≠ 0) : IsOpen (box n b : Set (Fin n → k)) := by
  have hvb : valuation k b ≠ 0 := (Valuation.ne_zero_iff _).2 hb
  have hU : Set.univ.pi (fun _ : Fin n => {y : k | valuation k y < valuation k b}) ∈
      nhds (0 : Fin n → k) :=
    set_pi_mem_nhds Set.finite_univ fun j _ =>
      (IsValuativeTopology.hasBasis_nhds_zero' k).mem_of_mem hvb
  refine (box n b).isOpen_of_mem_nhds (g := 0) (Filter.mem_of_superset hU ?_)
  intro x hx j
  exact (hx j (Set.mem_univ j)).le
end GlobalTheory.CompanionTheory.AnnihShrink
