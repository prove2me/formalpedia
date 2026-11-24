-- Prove2me | solution 1 for GlobalTheory.CoeffSubring.exists_coeffSubring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:47:20.565654+00:00
-- url     : https://prove2.me/submissions/998ff644-56d0-43c3-a35b-9b34ab7f1ab7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DvdOfForallSubMulMem
import Theorems.Thm_GlobalTheory_CoeffSubring_mem_level_of_sub_mem
import Theorems.Thm_GlobalTheory_CoeffSubring_level_antitone
import Theorems.Thm_GlobalTheory_CoeffSubring_exists_level_sub_mem
import Theorems.Thm_GlobalTheory_CoeffSubring_exists_iInf_sub_mem
import Theorems.Thm_GlobalTheory_CoeffSubring_exists_sub_mul_mem
import Theorems.Thm_GlobalTheory_CoeffSubring_exists_mem_pow_of_mul_mem
import Theorems.Thm_GlobalTheory_CoeffSubring_dvd_of_forall_sub_mul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CoeffSubring
variable {S : Type} [CommRing S] [IsLocalRing S] (p : ℕ) (L : Set S)
variable {p L}
namespace GlobalTheory.CoeffSubring
theorem _root_.solution [IsDomain S] [IsNoetherianRing S] [IsAdicComplete (maximalIdeal S) S]
    (hp : p.Prime) (hp0 : (p : S) ≠ 0) (h0 : (p : S) ∈ maximalIdeal S) {B : Set (ResidueField S)}
    (hB : Subring.closure (Set.range (fun x : ResidueField S => x ^ p) ∪ B) = ⊤)
    (hB' : ∀ (Q : Type) [CommRing Q] (f : ResidueField S →+* Q) (g : ResidueField S → Q),
      (∀ b ∈ B, g b ^ p = f b) →
      ∃ σ : ResidueField S →+* Q, (∀ x, σ (x ^ p) = f x) ∧ ∀ b ∈ B, σ b = g b) :
    ∃ Λ : Subring S, (∀ s : S, ∃ a ∈ Λ, s - a ∈ maximalIdeal S) ∧
      (∀ a : Λ, (a : S) ∈ maximalIdeal S → (p : Λ) ∣ a) ∧
      (∀ s : S, (∀ n : ℕ, ∃ a ∈ Λ, s - a ∈ maximalIdeal S ^ n) → s ∈ Λ) := by
  choose l hl using residue_surjective (R := S)
  have hL : residue S '' (l '' B) = B := by simp [Set.image_image, hl]
  have hinj : Set.InjOn (residue S) (l '' B) := by
    rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩ h
    rw [hl, hl] at h
    rw [h]
  rw [← hL] at hB hB'
  have hs := exists_level_sub_mem hp h0 hB
  refine ⟨⨅ n, level p (l '' B) n, exists_iInf_sub_mem h0 hs, fun a ha => ?_, fun s h => ?_⟩
  · choose t ht ht' using fun n =>
      exists_sub_mul_mem hp h0 hinj hB' hs n (Subring.mem_iInf.1 a.2 n) ha
    obtain ⟨s, hs'⟩ := dvd_of_forall_sub_mul_mem fun n =>
      ⟨t n, Ideal.pow_le_pow_right n.le_succ (ht' n)⟩
    obtain ⟨c, hc⟩ := exists_mem_pow_of_mul_mem (maximalIdeal S) hp0
    refine ⟨⟨s, Subring.mem_iInf.2 fun n => ?_⟩, Subtype.ext (by simpa using hs')⟩
    refine mem_level_of_sub_mem (level_antitone (Nat.le_add_right n c) (ht (n + c))) (hc _ _ ?_)
    rw [mul_sub, ← hs', add_right_comm]
    exact ht' _
  · refine Subring.mem_iInf.2 fun n => ?_
    obtain ⟨a, ha, h'⟩ := h (n + 1)
    exact mem_level_of_sub_mem (Subring.mem_iInf.1 ha n) h'
end GlobalTheory.CoeffSubring
