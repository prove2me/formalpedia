-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Packing.interior_center_exists
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:12:47.476986+00:00
-- url     : https://prove2.me/submissions/0fcafd87-74f4-4a86-ad2e-d530397544e7

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Chunks.lean:L165-L193
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Packing.interior_center_exists. The node keeps its source
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

lemma periodLength_pos (d : Fin r → ℕ) (i : Fin r) : 0<periodLength (oddLengths d) := by
  have h := prefix_add_length_le (oddLengths d) i
  dsimp [oddLengths] at h
  omega

lemma centerOffset_bounds (d : Fin r → ℕ) (i : Fin r) :
    0<slotPrefix (oddLengths d) i+d i+1 ∧
    slotPrefix (oddLengths d) i+d i+1≤periodLength (oddLengths d) := by
  have h := prefix_add_length_le (oddLengths d) i
  dsimp [oddLengths] at h
  omega

lemma interior_center_exists (d : Fin r → ℕ) {R t : ℕ}
    (ht : t<(R-2)*periodLength (oddLengths d)) (i : Fin r) :
    ∃ p s : ℕ, p+1<R ∧ s<periodLength (oddLengths d) ∧
      p*periodLength (oddLengths d)+s+slotPrefix (oddLengths d) i+d i+1 =
        periodLength (oddLengths d)+1+t := by
  let L := periodLength (oddLengths d)
  let c := slotPrefix (oddLengths d) i+d i+1
  have hL : 0<L := periodLength_pos d i
  have hc := centerOffset_bounds d i
  change 0<c ∧ c≤L at hc
  let u := L+1+t-c
  have hR : 2<R := by
    by_contra h
    have he : R-2=0 := by omega
    rw [he,Nat.zero_mul] at ht
    omega
  have hu : u<(R-1)*L := by
    have he : (R-1)*L=(R-2)*L+L := by
      rw [show R-1=(R-2)+1 by omega,Nat.add_mul,Nat.one_mul]
    dsimp [u,L] at *
    omega
  refine ⟨u/L,u%L,?_,Nat.mod_lt _ hL,?_⟩
  · have hh := (Nat.div_lt_iff_lt_mul hL).mpr hu
    omega
  · have he := Nat.mod_add_div u L
    rw [Nat.mul_comm L] at he
    have hcu : c≤L+1+t := by omega
    dsimp [u,c,L] at *
    omega

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


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.interior_center_exists := @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.interior_center_exists
