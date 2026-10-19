-- Prove2me | solution 1 for OAI.FiniteCircle.residue_representative
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:44:19.706568+00:00
-- url     : https://prove2.me/submissions/e594b02f-eb4b-4ecc-9b48-f954cd5b5259

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/Translations.lean:L266-L280
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.residue_representative. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Primes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Fourier
import Definitions.Def_OAI_Combinatorics_FiniteCircle_DyadicShifts
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TreeBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Translations

-- ---- from OAI.Combinatorics.FiniteCircle.Translations ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

 theorem residue_representative {h : ℕ} (p : Fin h → ℕ)
    (hn : ∀ k, 0 < p k) (hp : Pairwise (fun i j => Nat.Coprime (p i) (p j)))
    (z : ∀ k, ZMod (p k)) : ∃ q : ℕ, q < ∏ k, p k ∧ ∀ k, (q : ZMod (p k)) = z k := by
  classical
  let a := fun k => (z k).val
  have hs : ∀ k ∈ (Finset.univ : Finset (Fin h)), p k ≠ 0 := fun k _ => (hn k).ne'
  have hpp : Set.Pairwise (Finset.univ : Finset (Fin h)) (fun i j => Nat.Coprime (p i) (p j)) :=
    fun i _ j _ hij => hp hij
  let q := Nat.chineseRemainderOfFinset a p Finset.univ hs hpp
  refine ⟨q.val, Nat.chineseRemainderOfFinset_lt_prod a p hs hpp, ?_⟩
  intro k
  let : NeZero (p k) := ⟨(hn k).ne'⟩
  have ht := q.property k (Finset.mem_univ k)
  have he := (ZMod.natCast_eq_natCast_iff q.val (a k) (p k)).mpr ht
  exact he.trans (ZMod.natCast_zmod_val (z k))

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module


theorem solution : type_of% @_root_.OAI.FiniteCircle.residue_representative := @_root_.OAI.FiniteCircle.residue_representative
