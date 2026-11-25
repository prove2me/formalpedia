-- Prove2me | solution 1 for GlobalTheory.MoveFine.pair_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:25:51.766882+00:00
-- url     : https://prove2.me/submissions/818137a0-d731-4909-8800-26f48031eab1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerLatticeLocallyConstantDataStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsFineSubgroupMovesAtLattice
import Theorems.Thm_GlobalTheory_MoveFine_h_add_l
import Theorems.Thm_GlobalTheory_MoveFine_h_smul_l
import Theorems.Thm_GlobalTheory_MoveFine_h_zero_l
import Theorems.Thm_GlobalTheory_MoveFine_h_span_zero
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.MoveFine
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.MoveFine
theorem _root_.solution (g : Fin (r + 1) → S.V) (gs : Fin r → S.V)
    (hd : ∀ a j, S.h (g a) (gs j) = if a = j.castSucc then 1 else 0) (n : S.GLV) (hn : n ∈ S.Nof g)
    (j : Fin r) (y : S.V)
    (hy : y ∈ Submodule.span L.O ((fun b => n (g b)) '' {i | (i : ℕ) < j + 1})) :
    S.h y (gs j) ∈ L.O := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, hi, rfl⟩ := hy
    have hi' : (i : ℕ) < j + 1 := hi
    have hir : (i : ℕ) < r := by have := j.2; omega
    have h1 := (Subgroup.mem_iInf.1 hn.1.2 ⟨i, hir⟩).2 (g i)
      (Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩)
    have h2 : S.h (n (g i) - g i) (gs j) = 0 := by
      refine h_span_zero S _ {gs j} ?_ _ h1 _ (Submodule.subset_span rfl)
      rintro _ ⟨a, ha, rfl⟩ _ rfl
      have ha' : (a : ℕ) < i := ha
      rw [hd, if_neg]
      rintro rfl
      simp at ha'; omega
    have h3 : n (g i) = (n (g i) - g i) + g i := by abel
    show S.h (n (g i)) _ ∈ _
    rw [h3, h_add_l, h2, zero_add, hd]
    split_ifs
    exacts [L.O.one_mem, L.O.zero_mem]
  | zero => rw [h_zero_l]; exact L.O.zero_mem
  | add a b _ _ ha hb => rw [h_add_l]; exact L.O.add_mem ha hb
  | smul c a _ ha =>
    show S.h ((c : E) • a) _ ∈ _
    rw [h_smul_l]; exact L.O.mul_mem c.2 ha
end GlobalTheory.MoveFine
