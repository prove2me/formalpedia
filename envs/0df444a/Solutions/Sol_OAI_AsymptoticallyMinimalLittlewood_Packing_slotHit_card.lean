-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Packing.slotHit_card
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:16:42.814048+00:00
-- url     : https://prove2.me/submissions/4dd3b583-03f4-4038-8b4e-7c466a0b0160

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Chunks.lean:L464-L480
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Packing.slotHit_card. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
import Definitions.Def_OAI_Analysis_Littlewood_Chunks
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_signedSite_injective
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_siteCenter_chunk

-- ---- from OAI.Analysis.Littlewood.Chunks ----
namespace OAI

universe uJ

namespace AsymptoticallyMinimalLittlewood
namespace Packing
noncomputable section
open scoped BigOperators
open Finset

variable {r : ℕ}
lemma prefix_add_length_le (L : Fin r → ℕ) (i : Fin r) :
    slotPrefix L i+L i ≤ periodLength L := by
  classical
  have hi : i∉Finset.Iio i := by simp
  dsimp [slotPrefix,periodLength]
  rw [add_comm,← Finset.sum_insert hi]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

lemma slotLeft_bounds (L : Fin r → ℕ) (R : ℕ) {shift chunk period : ℕ}
    (hs : shift<periodLength L) (hp : period+1<R) (i : Fin r) :
    chunk*(R*periodLength L) ≤ slotLeft L R shift chunk period i ∧
    slotLeft L R shift chunk period i+L i < (chunk+1)*(R*periodLength L) := by
  have hi := prefix_add_length_le L i
  have hp' : (period+2)*periodLength L ≤ R*periodLength L :=
    Nat.mul_le_mul_right _ (by omega)
  dsimp [slotLeft]
  constructor
  · omega
  · simp only [Nat.add_mul] at hp' ⊢
    omega

lemma periodLength_pos (d : Fin r → ℕ) (i : Fin r) : 0<periodLength (oddLengths d) := by
  have h := prefix_add_length_le (oddLengths d) i
  dsimp [oddLengths] at h
  omega

lemma siteCenter_bounds (d : Fin r → ℕ) {R shift chunk period : ℕ}
    (hs : shift<periodLength (oddLengths d)) (hp : period+1<R) (i : Fin r) :
    chunk*(R*periodLength (oddLengths d)) < siteCenter d R shift chunk period i ∧
    siteCenter d R shift chunk period i < (chunk+1)*(R*periodLength (oddLengths d)) := by
  obtain ⟨hlo,hhi⟩ := slotLeft_bounds (oddLengths d) R (chunk := chunk) hs hp i
  dsimp [siteCenter,oddLengths] at *
  omega

end
end Packing
end AsymptoticallyMinimalLittlewood

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset
variable {r : ℕ}

lemma actual_centers_injective (d : Fin r → ℕ) (R K q : ℕ) (i : Fin r)
    (hq : 2*(K*(R*periodLength (oddLengths d)))<q) (ω : SlotChoices d K) :
    Function.Injective (fun c : Fin K × Fin (R-1) ↦
      signedSite q (ω c.1).2 (siteCenter d R (ω c.1).1 c.1 c.2 i)) := by
  intro c e h
  have hc : (c.2 : ℕ)+1<R := by have := c.2.isLt; omega
  have he : (e.2 : ℕ)+1<R := by have := e.2.isLt; omega
  have hcb := siteCenter_bounds d (R := R) (chunk := (c.1 : ℕ)) (ω c.1).1.isLt hc i
  have heb := siteCenter_bounds d (R := R) (chunk := (e.1 : ℕ)) (ω e.1).1.isLt he i
  have hcB : siteCenter d R (ω c.1).1 c.1 c.2 i≤K*(R*periodLength (oddLengths d)) :=
    hcb.2.le.trans (Nat.mul_le_mul_right _ (by have := c.1.isLt; omega))
  have heB : siteCenter d R (ω e.1).1 e.1 e.2 i≤K*(R*periodLength (oddLengths d)) :=
    heb.2.le.trans (Nat.mul_le_mul_right _ (by have := e.1.isLt; omega))
  have hs := ((signedSite_injective hq (by omega) hcB (by omega) heB _ _).mp h).2
  have hk : c.1=e.1 := by
    apply Fin.ext
    have hh := congrArg (fun n ↦ n/(R*periodLength (oddLengths d))) hs
    simpa only [siteCenter_chunk d (ω c.1).1.isLt hc i,
      siteCenter_chunk d (ω e.1).1.isLt he i] using hh
  have hp : c.2=e.2 := by
    apply Fin.ext
    rw [hk] at hs
    dsimp [siteCenter,slotLeft] at hs
    have hmul : (c.2 : ℕ)*periodLength (oddLengths d)=
        (e.2 : ℕ)*periodLength (oddLengths d) := by omega
    exact Nat.eq_of_mul_eq_mul_right (periodLength_pos d i) hmul
  exact Prod.ext hk hp

attribute [local instance] Classical.propDecidable

lemma slotHit_card (d : Fin r → ℕ) (R K q : ℕ) [NeZero q] (i : Fin r)
    (hq : 2*(K*(R*periodLength (oddLengths d)))<q) (ω : SlotChoices d K) :
    (Finset.univ.filter (fun t : ZMod q ↦ slotHit d R K q i ω t)).card=K*(R-1) := by
  classical
  have he : (Finset.univ.filter (fun t : ZMod q ↦ slotHit d R K q i ω t))=
      Finset.univ.image (fun c : Fin K × Fin (R-1) ↦
        signedSite q (ω c.1).2 (siteCenter d R (ω c.1).1 c.1 c.2 i)) := by
    apply Finset.ext
    intro t

    rw [Finset.mem_filter]
    simp only [Finset.mem_univ,true_and,Finset.mem_image,slotHit]
    constructor
    · rintro ⟨k,p,h⟩; exact ⟨(k,p),h.symm⟩
    · rintro ⟨⟨k,p⟩,h⟩; exact ⟨k,p,h.symm⟩
  rw [he,Finset.card_image_of_injective _ (actual_centers_injective d R K q i hq ω)]
  simp

end
end AsymptoticallyMinimalLittlewood.Packing

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Packing
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.slotHit_card := @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.slotHit_card
