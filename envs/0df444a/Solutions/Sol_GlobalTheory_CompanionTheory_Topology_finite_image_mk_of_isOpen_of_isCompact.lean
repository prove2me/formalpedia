-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Topology.finite_image_mk_of_isOpen_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:37:28.091464+00:00
-- url     : https://prove2.me/submissions/5fb13790-d213-4a93-8c30-1645dfbffea5

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteImageCompactOpenQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Topology
namespace GlobalTheory.CompanionTheory.Topology
theorem _root_.solution :
    ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
      (H : AddSubgroup G) (K : Set G), IsOpen (H : Set G) → IsCompact K →
      (QuotientAddGroup.mk '' K : Set (G ⧸ H)).Finite := by
  intro G _ _ _ H K hH hK
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : G => (fun y => x + y) '' (H : Set G))
    (fun x => (Homeomorph.addLeft x).isOpenMap _ hH)
    (fun x _ => Set.mem_iUnion.2 ⟨x, 0, H.zero_mem, add_zero x⟩)
  refine (t.finite_toSet.image (QuotientAddGroup.mk : G → G ⧸ H)).subset ?_
  rintro _ ⟨k, hk, rfl⟩
  obtain ⟨x, hx, hxk⟩ := Set.mem_iUnion₂.1 (ht hk)
  obtain ⟨h, hh, rfl⟩ := hxk
  refine ⟨x, hx, ?_⟩
  exact QuotientAddGroup.eq.2 (by simpa using hh)
end GlobalTheory.CompanionTheory.Topology
