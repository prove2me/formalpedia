-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LGroupSection.exists_refine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:03:25.098824+00:00
-- url     : https://prove2.me/submissions/a927651d-41c5-48f4-8484-4a45000d5d17

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsContinuousSectionQuotient
import Theorems.Thm_GlobalTheory_CompanionTheory_LGroupSection_isClopen_cosetImage
import Theorems.Thm_GlobalTheory_CompanionTheory_LGroupSection_exists_isLocallyConstant_mem

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
theorem _root_.solution [SecondCountableTopology G] (H K L : Subgroup G) [IsClosed (H : Set G)]
    (hLK : L ≤ K) (hLo : IsOpen (L : Set G)) (hLc : IsCompact (L : Set G))
    (t : G ⧸ H → G) (ht : IsLocallyConstant t) (h : ∀ x, x ∈ cosetImage H K (t x)) :
    ∃ t' : G ⧸ H → G, IsLocallyConstant t' ∧ (∀ x, x ∈ cosetImage H L (t' x)) ∧
      ∀ x, (t x)⁻¹ * t' x ∈ K := by
  let e : ℕ → G := TopologicalSpace.denseSeq G
  have he : DenseRange e := TopologicalSpace.denseRange_denseSeq G
  let V : ℕ → Set (G ⧸ H) := fun n =>
    (t ⁻¹' {g | g⁻¹ * e n ∈ K}) ∩ cosetImage H L (e n)
  have hV : ∀ n, IsClopen (V n) := fun n =>
    IsClopen.inter ⟨isOpen_compl_iff.1 (ht _ᶜ), ht _⟩ (isClopen_cosetImage H L hLo hLc (e n))
  have hcov : ∀ x, ∃ n, x ∈ V n := by
    intro x
    obtain ⟨k, hk, hkx⟩ := h x
    have hopen : IsOpen ((fun l : G => t x * k * l) '' (L : Set G)) :=
      (Homeomorph.mulLeft (t x * k)).isOpenMap _ hLo
    obtain ⟨n, l, hl, hn⟩ := he.exists_mem_open hopen ⟨t x * k * 1, 1, L.one_mem, rfl⟩
    refine ⟨n, ?_, l⁻¹, L.inv_mem hl, ?_⟩
    · simp only [mem_preimage, mem_setOf_eq, ← hn]
      have : (t x)⁻¹ * (t x * k * l) = k * l := by group
      rw [this]
      exact K.mul_mem hk (hLK hl)
    · rw [← hn, mul_inv_cancel_right]
      exact hkx
  obtain ⟨f, hf, hfV⟩ := exists_isLocallyConstant_mem V hV hcov
  exact ⟨fun x => e (f x), hf.comp e, fun x => (hfV x).2, fun x => (hfV x).1⟩
end GlobalTheory.CompanionTheory.LGroupSection
