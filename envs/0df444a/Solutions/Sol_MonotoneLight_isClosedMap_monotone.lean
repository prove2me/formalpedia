-- Prove2me | solution 1 for MonotoneLight.isClosedMap_monotone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:41:46.353222+00:00
-- url     : https://prove2.me/submissions/d5055d9a-6585-47cc-8eec-379cac2a98f8

module
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Homeomorph.Lemmas
public import Definitions.Def_MonotoneLight_Solution
public import Theorems.Thm_MonotoneLight_isClosed_fiberRel
public import Theorems.Thm_MonotoneLight_monotone_eq_iff

set_option autoImplicit true
@[expose] public section
public section
open Set Function Topology
universe u v
open MonotoneLight
variable {X : Type u} {Y : Type v} [_tX : TopologicalSpace X] [_tY : TopologicalSpace Y]
namespace MonotoneLight
theorem _root_.solution [_cX : CompactSpace X] [_hX : T2Space X] [_hY : T2Space Y]
    {f : X → Y} (hf : Continuous f) : IsClosedMap (monotone f) := by
  intro s hs
  apply isQuotientMap_quotient_mk'.isCoinducing.isClosed_preimage.mp
  have hc : IsClosed {p : X × X | FiberRel f p.1 p.2 ∧ p.2 ∈ s} :=
    (isClosed_fiberRel hf).inter (hs.preimage continuous_snd)
  have he : monotone f ⁻¹' (monotone f '' s) =
      Prod.fst '' {p : X × X | FiberRel f p.1 p.2 ∧ p.2 ∈ s} := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact ⟨(x, y), ⟨monotone_eq_iff.mp hxy.symm, hy⟩, rfl⟩
    · rintro ⟨⟨z, y⟩, ⟨hzy, hy⟩, rfl⟩
      exact ⟨y, hy, (monotone_eq_iff.mpr hzy).symm⟩
  change IsClosed (monotone f ⁻¹' (monotone f '' s))
  rw [he]
  exact (hc.isCompact.image continuous_fst).isClosed
end MonotoneLight
