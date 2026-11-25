-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.mem_of_forall_fiber
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:13:33.489441+00:00
-- url     : https://prove2.me/submissions/ec986914-7b7c-49b1-98aa-ccb9b95ece08

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_isCompact_support
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_indicator_mul_mem
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_isClopen_mem_disjoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology
variable {X : Type*} [TopologicalSpace X]
variable [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
omit [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {Y : Type*} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    [TotallyDisconnectedSpace Y] {U C : Set X} (hC : IsClosed C) {p : X → Y}
    (hp : Continuous p) {W : Submodule ℂ (X → ℂ)}
    (hWK : supportedIn U ⊓ vanishingOn C ≤ W)
    (hWmul : ∀ V : Set Y, IsClopen V → ∀ w ∈ W, (fun x => (p ⁻¹' V).indicator 1 x * w x) ∈ W)
    {g : X → ℂ} (hg : g ∈ supportedIn U)
    (hfib : ∀ y, g ∈ W ⊔ (supportedIn U ⊓ vanishingOn (C ∩ p ⁻¹' {y}))) : g ∈ W := by
  classical

  let good : Set Y → Prop := fun V => (fun x => (p ⁻¹' V).indicator 1 x * g x) ∈ W
  have hloc : ∀ y, ∃ V : Set Y, IsClopen V ∧ y ∈ V ∧ good V := by
    intro y
    obtain ⟨c, hcW, k, hk, hck⟩ := Submodule.mem_sup.1 (hfib y)
    have hQ : IsCompact (p '' (C ∩ Function.support k)) :=
      ((isCompact_support hk.1.1).inter_left hC).image hp
    have hyQ : y ∉ p '' (C ∩ Function.support k) := by
      rintro ⟨x, ⟨hxC, hxk⟩, hxy⟩
      exact hxk (hk.2 x ⟨hxC, hxy⟩)
    obtain ⟨V, hV, hyV, hVQ⟩ := exists_isClopen_mem_disjoint hQ hyQ
    refine ⟨V, hV, hyV, ?_⟩
    have hsplit : (fun x => (p ⁻¹' V).indicator 1 x * g x) =
        (fun x => (p ⁻¹' V).indicator 1 x * c x) + (fun x => (p ⁻¹' V).indicator 1 x * k x) := by
      funext x
      simp only [Pi.add_apply, ← mul_add, ← hck]
    show _ ∈ W
    rw [hsplit]
    refine W.add_mem (hWmul V hV c hcW) (hWK ⟨indicator_mul_mem (hV.preimage hp) hk.1, ?_⟩)
    intro x hxC
    by_cases hxV : x ∈ p ⁻¹' V
    · have : k x = 0 := by
        by_contra hkx
        exact Set.disjoint_left.1 hVQ hxV ⟨x, ⟨hxC, hkx⟩, rfl⟩
      simp [this]
    · simp [Set.indicator_of_notMem hxV]
  choose V hVc hyV hVg using hloc

  have hQ : IsCompact (p '' (C ∩ Function.support g)) :=
    ((isCompact_support hg.1).inter_left hC).image hp
  obtain ⟨s, hs⟩ := hQ.elim_finite_subcover V (fun y => (hVc y).isOpen)
    (fun y _ => mem_iUnion.2 ⟨y, hyV y⟩)

  have hunion : ∀ t : Finset Y, IsClopen (⋃ y ∈ t, V y) ∧ good (⋃ y ∈ t, V y) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      refine ⟨by simp [isClopen_empty], ?_⟩
      show _ ∈ W
      simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, preimage_empty,
        Set.indicator_empty, zero_mul]
      exact W.zero_mem
    | insert a t hat ih =>
      obtain ⟨ht, hgt⟩ := ih
      have hcl : IsClopen (V a ∪ ⋃ y ∈ t, V y) := (hVc a).union ht
      refine ⟨by simpa [Finset.set_biUnion_insert] using hcl, ?_⟩
      show _ ∈ W
      have hmul := hWmul (V a) (hVc a) _ hgt
      have e : (fun x => (p ⁻¹' ⋃ y ∈ insert a t, V y).indicator 1 x * g x) =
          (fun x => (p ⁻¹' V a).indicator 1 x * g x) +
            (fun x => (p ⁻¹' ⋃ y ∈ t, V y).indicator 1 x * g x) -
            (fun x => (p ⁻¹' V a).indicator 1 x *
              ((p ⁻¹' ⋃ y ∈ t, V y).indicator 1 x * g x)) := by
        funext x
        simp only [Finset.set_biUnion_insert, Pi.add_apply, Pi.sub_apply, preimage_union]
        by_cases h1 : x ∈ p ⁻¹' V a <;> by_cases h2 : x ∈ p ⁻¹' ⋃ y ∈ t, V y <;>
          simp_all [Set.indicator_of_mem, Set.indicator_of_notMem]
      rw [e]
      exact W.sub_mem (W.add_mem (hVg a) hgt) hmul
  obtain ⟨-, hgood⟩ := hunion s
  have hrest : (g - fun x => (p ⁻¹' ⋃ y ∈ s, V y).indicator 1 x * g x) ∈ W := by
    refine hWK ⟨(supportedIn U).sub_mem hg
      (indicator_mul_mem ((hunion s).1.preimage hp) hg), ?_⟩
    intro x hxC
    by_cases hgx : g x = 0
    · simp [hgx]
    · have hx : x ∈ p ⁻¹' ⋃ y ∈ s, V y := hs ⟨x, ⟨hxC, hgx⟩, rfl⟩
      simp only [Pi.sub_apply]
      rw [Set.indicator_of_mem hx, Pi.one_apply, one_mul, sub_self]
  have := W.add_mem hrest hgood
  simpa using this
end GroundTheory.Automorphic.Whittaker
