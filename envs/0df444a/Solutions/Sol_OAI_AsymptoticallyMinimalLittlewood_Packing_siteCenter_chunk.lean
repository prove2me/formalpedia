-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Packing.siteCenter_chunk
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:11:11.489845+00:00
-- url     : https://prove2.me/submissions/a0b28473-e336-4dff-bab9-939aedc3b226

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Chunks.lean:L150-L163
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Packing.siteCenter_chunk. The node keeps its source
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

lemma siteCenter_chunk (d : Fin r → ℕ) {R shift chunk period : ℕ}
    (hs : shift<periodLength (oddLengths d)) (hp : period+1<R) (i : Fin r) :
    siteCenter d R shift chunk period i / (R*periodLength (oddLengths d)) = chunk := by
  have hR : 0<R := by omega
  have hL := periodLength_pos d i
  have hc := (siteCenter_bounds d (chunk := 0) hs hp i).2
  dsimp [siteCenter,slotLeft] at hc ⊢
  simp only [Nat.zero_mul,Nat.zero_add,Nat.zero_add,Nat.one_mul] at hc
  have he : chunk*(R*periodLength (oddLengths d))+period*periodLength (oddLengths d)+shift+
      slotPrefix (oddLengths d) i+d i+1 =
      (period*periodLength (oddLengths d)+shift+slotPrefix (oddLengths d) i+d i+1)+
      chunk*(R*periodLength (oddLengths d)) := by omega
  rw [he,Nat.add_mul_div_right _ _ (mul_pos hR hL),Nat.div_eq_of_lt hc]
  simp

end
end Packing
end AsymptoticallyMinimalLittlewood

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset
variable {r : ℕ}

attribute [local instance] Classical.propDecidable

end
end AsymptoticallyMinimalLittlewood.Packing

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Packing
open scoped BigOperators
open Finset


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.siteCenter_chunk := @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.siteCenter_chunk
