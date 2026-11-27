-- Prove2me | solution 1 for GlobalTheory.exists_oLat_of_fg_ringOfIntegers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:37:23.189346+00:00
-- url     : https://prove2.me/submissions/97e9cd0d-c0b1-4a57-ad49-701c511bd706

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsCombOfMemClosureFinset
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open Formalism.BasicNotions NumberField
open GlobalTheory
open NumberField
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : ∀ (O K : Type) [CommRing O] [Field K] [NumberField K] (o : O →+* K) (e : K →+* ℂ) (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (W : Type) [AddCommGroup W] [Module ℂ W] (j : V →ₛₗ[e] W) (N : Submodule (𝓞 K) V), (∀ z, IsIntegral ℤ (o z)) → N.FG → Submodule.span ℂ (j '' (N : Set V)) = ⊤ → ∃ L : _root_.Formalism.BasicNotions.Rows.OLat O (e.comp o) W, L.carrier = j '' (N : Set V) ∧ (∀ v ∈ L.gen, v ∈ j '' (N : Set V)) ∧ (∀ y, (∃ c : W → 𝓞 K, y = ∑ v ∈ L.gen, e (c v : K) • v) ↔ y ∈ j '' (N : Set V)) ∧ ∀ (a : 𝓞 K), ∀ y ∈ L.carrier, e (a : K) • y ∈ L.carrier := by
  intro O K _ _ _ o e V _ _ _ _ W _ _ j N ho hN hspan
  have hNZ : (N.restrictScalars ℤ).FG := hN.restrictScalars
  obtain ⟨S, hS⟩ := hNZ.map j.toAddMonoidHom.toIntLinearMap
  have hmem : ∀ y, y ∈ Submodule.span ℤ (S : Set W) ↔ y ∈ j '' (N : Set V) := by
    intro y
    rw [hS, Submodule.mem_map]
    rfl
  have hsmul : ∀ (a : 𝓞 K) (y : W), y ∈ j '' (N : Set V) → e (a : K) • y ∈ j '' (N : Set V) := by
    rintro a _ ⟨n, hn, rfl⟩
    refine ⟨a • n, N.smul_mem a hn, ?_⟩
    rw [← algebraMap_smul K a n, j.map_smulₛₗ]
  have hcomb : ∀ c : W → 𝓞 K, ∑ v ∈ S, e (c v : K) • v ∈ j '' (N : Set V) := by
    intro c
    refine Finset.sum_induction _ (fun y => y ∈ j '' (N : Set V)) ?_ ⟨0, N.zero_mem, map_zero j⟩ ?_
    · rintro _ _ ⟨n₁, hn₁, rfl⟩ ⟨n₂, hn₂, rfl⟩
      exact ⟨n₁ + n₂, N.add_mem hn₁ hn₂, map_add j n₁ n₂⟩
    · intro v hv
      exact hsmul (c v) v ((hmem v).1 (Submodule.subset_span hv))
  have hint : ∀ y ∈ j '' (N : Set V), ∃ f : W → ℤ, y = ∑ v ∈ S, (f v : ℂ) • v := by
    intro y hy
    obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.1 ((hmem y).2 hy)
    refine ⟨f, ?_⟩
    rw [← hf]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Int.cast_smul_eq_zsmul]
  have hsub : j '' (N : Set V) ⊆ Submodule.span ℂ (S : Set W) := fun y hy =>
    Submodule.span_le_restrictScalars ℤ ℂ (S : Set W) ((hmem y).2 hy)
  let L : _root_.Formalism.BasicNotions.Rows.OLat O (e.comp o) W :=
    ⟨S, eq_top_iff.2 (hspan ▸ Submodule.span_le.2 hsub)⟩
  have hcarrier : L.carrier = j '' (N : Set V) := by
    unfold _root_.Formalism.BasicNotions.Rows.OLat.carrier
    ext y
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨c, rfl⟩
      exact hcomb fun v => ⟨o (c v), ho (c v)⟩
    · intro hy
      obtain ⟨f, rfl⟩ := hint y hy
      exact ⟨fun v => (f v : O), by simp [L]⟩
  refine ⟨L, hcarrier, fun v hv => (hmem v).1 (Submodule.subset_span hv), fun y => ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨c, rfl⟩
    exact hcomb c
  · intro hy
    obtain ⟨f, rfl⟩ := hint y hy
    exact ⟨fun v => (f v : 𝓞 K), by simp [L]⟩
  · intro a y hy
    rw [hcarrier] at hy ⊢
    exact hsmul a y hy
end _root_.GlobalTheory
end GlobalTheory
