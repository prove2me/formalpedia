-- Prove2me | solution 1 for OAI.FiniteCircle.WordMatching.block_after_card_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T16:23:08.446532+00:00
-- url     : https://prove2.me/submissions/f62fa906-f720-444a-98ac-30ef024d383c

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/AnchorRecovery.lean:L142-L155
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.WordMatching.block_after_card_le. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Distortion
import Definitions.Def_OAI_Combinatorics_FiniteCircle_BlockMatching

-- ---- from OAI.Combinatorics.FiniteCircle.BlockMatching ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

theorem mod_strictMono_on_block (A : WordMatching x y q) {w i : ℕ}
    {k l : Fin q} (hk : k ∈ A.sourceBlock w i) (hl : l ∈ A.sourceBlock w i)
    (hkl : k < l) : (A.left k).val % w < (A.left l).val % w := by
  have hm : (A.left k).val < (A.left l).val := A.left.strictMono hkl
  have h1 := Nat.mod_add_div (A.left k).val w
  have h2 := Nat.mod_add_div (A.left l).val w
  rw [(A.mem_sourceBlock w i k).mp hk] at h1
  rw [(A.mem_sourceBlock w i l).mp hl] at h2
  omega

end WordMatching

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.AnchorRecovery ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

namespace WordMatching
variable {α : Type*} {x y : List α} {w q : ℕ} {c : α → Fin w → Bool}

end WordMatching

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

theorem mod_injectiveOn (A : WordMatching x y q) {w i : ℕ} :
    Set.InjOn (fun k : Fin q => (A.left k).val%w) (↑(A.sourceBlock w i) : Set (Fin q)) := by
  intro k hk l hl he
  change (A.left k).val%w = (A.left l).val%w at he
  apply A.left.injective
  apply Fin.ext
  have h1 := Nat.mod_add_div (A.left k).val w
  have h2 := Nat.mod_add_div (A.left l).val w
  rw [(A.mem_sourceBlock w i k).mp hk, he] at h1
  rw [(A.mem_sourceBlock w i l).mp hl] at h2
  omega

theorem block_after_card_le (A : WordMatching x y q) {w i : ℕ} (hw : 0 < w)
    {k : Fin q} (hk : k ∈ A.sourceBlock w i) :
    ((A.sourceBlock w i).filter (fun l => k < l)).card ≤ w - (A.left k).val%w - 1 := by
  let T := (A.sourceBlock w i).filter (fun l => k < l)
  let f := fun l : Fin q => (A.left l).val%w
  have hinj : Set.InjOn f (↑T : Set (Fin q)) := A.mod_injectiveOn.mono (by
    intro l hl; exact (Finset.mem_filter.mp hl).1)
  have hsub : T.image f ⊆ Finset.Ioo ((A.left k).val%w) w := by
    intro j hj
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hl, hlt⟩ := Finset.mem_filter.mp hl
    exact Finset.mem_Ioo.mpr ⟨A.mod_strictMono_on_block hk hl hlt, Nat.mod_lt _ hw⟩
  rw [← Finset.card_image_of_injOn hinj]
  simpa only [Nat.card_Ioo] using Finset.card_le_card hsub

end WordMatching

namespace WordMatching
variable {α : Type*} {x y : List α} {w q : ℕ} {c : α → Fin w → Bool}

end WordMatching

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle OAI.FiniteCircle.WordMatching
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module


theorem solution : type_of% @_root_.OAI.FiniteCircle.WordMatching.block_after_card_le := @_root_.OAI.FiniteCircle.WordMatching.block_after_card_le
