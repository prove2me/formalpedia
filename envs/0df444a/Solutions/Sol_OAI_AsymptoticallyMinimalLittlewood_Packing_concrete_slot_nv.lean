-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Packing.concrete_slot_nv
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:34:10.862647+00:00
-- url     : https://prove2.me/submissions/555a55ef-9c47-4bbf-9486-180c153ff302

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/SlotParameters.lean:L252-L268
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Packing.concrete_slot_nv. The node keeps its source
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
import Definitions.Def_OAI_Analysis_Littlewood_DependentMoments
import Definitions.Def_OAI_Analysis_Littlewood_SlotGraph
import Definitions.Def_OAI_Analysis_Littlewood_SlotParameters
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_slotHit_card

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

-- ---- from OAI.Analysis.Littlewood.SlotGraph ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uI uK uV uJ

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset
open Nibble
section SlotGraph
variable {I : Type uI} {K : Type uK} {V : Type uV} [Fintype I] [DecidableEq I] [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]

omit [DecidableEq I] [Field K] [DecidableEq K] in
lemma slotVertices_card (hit : I → K → Prop) [∀ i t, Decidable (hit i t)] :
    (slotVertices hit).card=∑ i, (Finset.univ.filter (hit i)).card := by
  classical
  simp only [slotVertices,Finset.card_filter,Fintype.sum_prod_type]

end SlotGraph
end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset Nibble
section RandomMatching
variable {I : Type} [Fintype I] [DecidableEq I]

end RandomMatching
end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset Nibble
attribute [local instance] Classical.propDecidable

lemma concrete_slot_vertices_card {r q : ℕ} [Fact q.Prime] (d : Fin r → ℕ)
    (R K : ℕ) (hq : 2*(K*(R*periodLength (oddLengths d)))<q) (ω : SlotChoices d K) :
    (slotVertices (fun i t ↦ slotHit d R K q i ω t)).card=r*K*(R-1) := by
  rw [slotVertices_card]
  simp only [slotHit_card d R K q _ hq ω,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul, Nat.cast_id]
  ring

end
end AsymptoticallyMinimalLittlewood.Packing

end OAI

-- ---- from OAI.Analysis.Littlewood.SlotParameters ----
namespace OAI

universe uV

/-! Parameter choices for the concrete signed-slot packing. The chunk
length is chosen first and remains fixed while the prime modulus grows. -/
namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open Filter Topology
open scoped BigOperators

lemma chunkCount_bounds {B q : ℕ} (hB : 0<B) (hq : 0<q) :
    B*chunkCount B q<q ∧ q≤B*(chunkCount B q+1) := by
  have hm := Nat.mod_lt (q-1) hB
  have he := Nat.mod_add_div (q-1) B
  dsimp [chunkCount]
  constructor
  · have hd := Nat.mul_div_le (q-1) B
    omega
  · nlinarith only [hm,he,show q-1+1=q by omega]

end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset Nibble Filter Topology
attribute [local instance] Classical.propDecidable

lemma concrete_slot_nv {r q R : ℕ} [Fact q.Prime]
    (d : Fin r → ℕ) (i₀ : Fin r) (hR : 1≤R)
    (ω : SlotChoices d (chunkCount (2*R*periodLength (oddLengths d)) q)) :
    ((slotVertices (fun i t ↦ slotHit d R
      (chunkCount (2*R*periodLength (oddLengths d)) q) q i ω t)).card : ℝ)=
      (q : ℝ)*packingNV r (periodLength (oddLengths d)) R q := by
  have hL := periodLength_pos d i₀
  have hq0 := (Fact.out : q.Prime).pos
  have hq : 2*(chunkCount (2*R*periodLength (oddLengths d)) q*
      (R*periodLength (oddLengths d)))<q := by
    have h := (chunkCount_bounds (show 0<2*R*periodLength (oddLengths d) by positivity) hq0).1
    nlinarith only [h]
  rw [concrete_slot_vertices_card d R _ hq]
  simp only [Nat.cast_mul,Nat.cast_sub hR,Nat.cast_one]
  unfold packingNV
  have hqne : (q : ℝ)≠0 := by exact_mod_cast hq0.ne'
  field_simp

end
end AsymptoticallyMinimalLittlewood.Packing

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Packing
open scoped BigOperators
open Finset Nibble Filter Topology
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.concrete_slot_nv := @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.concrete_slot_nv
