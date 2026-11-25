-- Prove2me | solution 1 for MonotoneLight.totallyDisconnected_light_fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:51:58.835781+00:00
-- url     : https://prove2.me/submissions/f2e46139-8ca0-463e-ad07-56fdd211b74c

module
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Homeomorph.Lemmas
public import Definitions.Def_MonotoneLight_Solution
public import Theorems.Thm_MonotoneLight_monotone_eq_iff
public import Theorems.Thm_MonotoneLight_surjective_monotone
public import Theorems.Thm_MonotoneLight_middle_t2Space
public import Theorems.Thm_MonotoneLight_continuous_light
public import Theorems.Thm_MonotoneLight_connected_monotone_fiber

set_option autoImplicit true
@[expose] public section
public section
open Set Function Topology
universe u v
open MonotoneLight
variable {X : Type u} {Y : Type v} [_tX : TopologicalSpace X] [_tY : TopologicalSpace Y]
namespace MonotoneLight
theorem _root_.solution [_cX : CompactSpace X] [_hX : T2Space X] [_hY : T2Space Y]
    {f : X → Y} (hf : Continuous f) (y : Y) :
    IsTotallyDisconnected (light f ⁻¹' {y}) := by
  have : T2Space (Middle f) := middle_t2Space hf
  intro t ht htc q hq r hr
  have hcl : closure t ⊆ light f ⁻¹' {y} :=
    closure_minimal ht (isClosed_singleton.preimage (continuous_light hf))
  have hconn : IsConnected (closure t) := ⟨⟨q, subset_closure hq⟩, htc.closure⟩
  have hpre : IsConnected (monotone f ⁻¹' closure t) :=
    isQuotientMap_quotient_mk'.isCoinducing.isConnected_preimage_of_isClosed
      (connected_monotone_fiber f) isClosed_closure hconn
  obtain ⟨a, rfl⟩ := surjective_monotone f q
  obtain ⟨b, rfl⟩ := surjective_monotone f r
  have ha : a ∈ monotone f ⁻¹' closure t := subset_closure hq
  have hb : b ∈ monotone f ⁻¹' closure t := subset_closure hr
  have hsub : monotone f ⁻¹' closure t ⊆ f ⁻¹' {f a} := by
    intro z hz
    have hzY : f z = y := hcl hz
    have haY : f a = y := hcl ha
    exact hzY.trans haY.symm
  exact monotone_eq_iff.mpr (hpre.2.subset_connectedComponentIn ha hsub hb)
end MonotoneLight
