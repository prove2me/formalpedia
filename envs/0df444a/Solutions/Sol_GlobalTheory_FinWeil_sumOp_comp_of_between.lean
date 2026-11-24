-- Prove2me | solution 1 for GlobalTheory.FinWeil.sumOp_comp_of_between
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:07:55.729721+00:00
-- url     : https://prove2.me/submissions/db548228-3e0d-4fb8-8751-e46224322b63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HeisenbergIntertwiningSumCompOfIntermediateLatti
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_comp_of_mem
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_iso
import Theorems.Thm_GlobalTheory_FinWeil_sumOp_transversal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.FinWeil
namespace GlobalTheory.FinWeil
theorem _root_.solution : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ (A B C : Submodule R X), SelfDual γ A → SelfDual γ B → SelfDual γ C → idx A B ≠ 0 → idx B C ≠ 0 → B ≤ (B ⊓ A) ⊔ (B ⊓ C) → idx A C = idx A B * idx B C ∧ ∀ v, Fixes W A v → sumOp W B C (sumOp W A B v) = sumOp W A C v := by
  intro R X M _ _ _ _ _ σ w γ W h A B C hA hB hC hAB hBC hle
  have hdec : ∀ b ∈ B, ∃ c, c ∈ B ∧ c ∈ C ∧ b - c ∈ A := by
    intro b hb
    obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.1 (hle hb)
    exact ⟨c, hc.1, hc.2, by simpa using ha.2⟩
  have hAC : ∀ x, x ∈ A → x ∈ C → x ∈ B := by
    intro x hxA hxC
    refine (hB x).2 fun b hb => ?_
    obtain ⟨c, -, hcC, hcA⟩ := hdec b hb
    have e : b = (b - c) + c := by abel
    rw [e, h.add_right, h.iso hA hxA hcA, h.iso hC hxC hcC, one_mul]
  obtain ⟨tAB, tAB2, -⟩ := GlobalTheory.FinWeil.sumOp_transversal h A B hB
  obtain ⟨tBC, tBC2, -⟩ := GlobalTheory.FinWeil.sumOp_transversal h B C hC
  obtain ⟨tAC, -, -⟩ := GlobalTheory.FinWeil.sumOp_transversal h A C hC
  obtain ⟨⟨n, f0, hf0B, hf0⟩, hfix, -⟩ := tAB2 hAB
  obtain ⟨⟨m, g, hgC, hg⟩, -, -⟩ := tBC2 hBC
  choose f hfB hfC hfA using fun i => hdec (f0 i) (hf0B i)
  have hf : ∀ b ∈ B, ∃! i, b - f i ∈ A := by
    intro b hb
    have key : ∀ i, b - f i ∈ A ↔ b - f0 i ∈ A := by
      intro i
      have e : b - f i = (b - f0 i) + (f0 i - f i) := by abel
      rw [e]
      exact A.add_mem_iff_left (hfA i)
    simp only [key]
    exact hf0 b hb
  have hkC : ∀ p : Fin m × Fin n, g p.1 + f p.2 ∈ C := fun p => C.add_mem (hgC _) (hfC _)
  have hk : ∀ x ∈ C, ∃! p : Fin m × Fin n, x - (g p.1 + f p.2) ∈ A := by
    intro x hx
    obtain ⟨j, hj, hju⟩ := hg x hx
    obtain ⟨i, hi, hiu⟩ := hf _ hj
    refine ⟨(j, i), by simpa [sub_add_eq_sub_sub] using hi, ?_⟩
    rintro ⟨j', i'⟩ hp
    have hp' : x - (g j' + f i') ∈ A := hp
    have h1 : x - (g j' + f i') ∈ B := hAC _ hp' (C.sub_mem hx (hkC (j', i')))
    have h2 : x - g j' ∈ B := by
      have e : x - g j' = (x - (g j' + f i')) + f i' := by abel
      rw [e]
      exact B.add_mem h1 (hfB i')
    obtain rfl : j' = j := hju j' h2
    obtain rfl : i' = i := hiu i' (by simpa [sub_add_eq_sub_sub] using hp')
    rfl
  have z : ∀ D : Submodule R X, Fixes W D 0 := fun D a _ => map_zero _
  refine ⟨?_, fun v hv => ?_⟩
  · rw [(tAC 0 (z A) _ (fun p : Fin m × Fin n => g p.1 + f p.2) hkC hk).2, (tAB 0 (z A) _ f hfB hf).2,
      (tBC 0 (z B) _ g hgC hg).2, Fintype.card_prod, mul_comm]
  · rw [(tBC _ (hfix v hv) _ g hgC hg).1, (tAB v hv _ f hfB hf).1,
      (tAC v hv _ (fun p : Fin m × Fin n => g p.1 + f p.2) hkC hk).1, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => h.comp_of_mem hC (hgC j) (hfC i) v
end GlobalTheory.FinWeil
