-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Packing.signedSite_injective
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:08:59.882935+00:00
-- url     : https://prove2.me/submissions/fa2974f6-fd5b-4aea-8f77-1ce05e6af692

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Chunks.lean:L110-L123
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Packing.signedSite_injective. The node keeps its source
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
lemma signedSite_injective {q A x y : ℕ} (hq : 2*A<q)
    (hx : 0<x) (hxA : x≤A) (hy : 0<y) (hyA : y≤A) (e f : Bool) :
    signedSite q e x=signedSite q f y ↔ e=f ∧ x=y := by
  have hxy : x+y<q := by omega
  have hn : (x : ZMod q)≠-(y : ZMod q) := by
    intro h
    have hz : ((x+y : ℕ) : ZMod q)=0 := by push_cast; rw [h]; simp
    have hd := (ZMod.natCast_eq_zero_iff _ _).mp hz
    have he := Nat.eq_zero_of_dvd_of_lt hd hxy
    omega
  have heq : (x : ZMod q)=(y : ZMod q) ↔ x=y := by
    rw [ZMod.natCast_eq_natCast_iff']
    rw [Nat.mod_eq_of_lt (by omega : x<q),Nat.mod_eq_of_lt (by omega : y<q)]
  cases e <;> cases f <;> simp [signedSite,heq,hn, neg_eq_iff_eq_neg]

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


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.signedSite_injective := @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.signedSite_injective
