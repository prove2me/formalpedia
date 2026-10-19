-- Prove2me | solution 1 for OAI.FiniteCircle.distortion_upper
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:45:58.297583+00:00
-- url     : https://prove2.me/submissions/d0878b3a-14ad-41c4-bfd3-a3487254c554

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/Distortion.lean:L100-L131
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.distortion_upper. The node keeps its source
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

-- ---- from OAI.Combinatorics.FiniteCircle.Distortion ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

 theorem distortion_upper {α X : Type*} [Nontrivial X]
    (word : X → List α) (hw : Function.Injective word)
    (f : X → RealL1) (A B : ℝ) (hA : 0≤A)
    (hu : ∀ x y, ‖f x-f y‖ ≤ A*(editDistance (word x) (word y):ℝ))
    (hl : ∀ x y, (editDistance (word x) (word y):ℝ) ≤ B*‖f x-f y‖) :
    Function.Injective f ∧ distortion word f ≤ A*B := by
  have hf : Function.Injective f := by
    intro x y he
    have hwxy := hl x y
    rw [he,sub_self,norm_zero,mul_zero] at hwxy
    have ht : editDistance (word x) (word y)=0 := by exact_mod_cast (le_antisymm hwxy (by positivity))
    exact hw (editDistance_eq_zero.mp ht)
  refine ⟨hf,?_⟩
  obtain ⟨x,y,hxy⟩ := exists_pair_ne X
  have hune : (upperRates word f).Nonempty := ⟨_,x,y,hxy,rfl⟩
  have hlne : (lowerRates word f).Nonempty := ⟨_,x,y,hxy,rfl⟩
  have hU : sSup (upperRates word f) ≤ A := by
    apply csSup_le hune
    rintro r ⟨x,y,hxy,rfl⟩
    have hed : (0:ℝ)<editDistance (word x) (word y) := by
      exact_mod_cast Nat.pos_of_ne_zero (fun he => hxy (hw (editDistance_eq_zero.mp he)))
    exact (div_le_iff₀ hed).mpr (hu x y)
  have hL : sSup (lowerRates word f) ≤ B := by
    apply csSup_le hlne
    rintro r ⟨x,y,hxy,rfl⟩
    have hn : 0<‖f x-f y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (fun he => hxy (hf he)))
    exact (div_le_iff₀ hn).mpr (hl x y)
  apply mul_le_mul hU hL
  · apply Real.sSup_nonneg
    rintro r ⟨x,y,_,rfl⟩
    positivity
  · exact hA

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module


theorem solution : type_of% @_root_.OAI.FiniteCircle.distortion_upper := @_root_.OAI.FiniteCircle.distortion_upper
