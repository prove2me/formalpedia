-- Prove2me | solution 1 for GlobalTheory.MoveFine.split_Mof
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:10:01.803822+00:00
-- url     : https://prove2.me/submissions/e60f5aed-dc22-4ecf-b1ec-5aab095f375c

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
import Theorems.Thm_GlobalTheory_MoveFine_smul_memO
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
theorem _root_.solution (Λ : Submodule L.O S.V) (X X' : Submodule E S.V) (g g' : Fin (r + 1) → S.V)
    (hg : ∀ i, g i ∈ Λ ∧ g i ∈ X) (hg' : ∀ i, g' i ∈ Λ ∧ g' i ∈ X') (h0 : S.th ≠ 0)
    (hth : algebraMap F E S.th ∈ L.O) (m : S.V) (hm : m ∈ S.Mof g g') :
    ∃ z z', z ∈ Λ ∧ z ∈ X ∧ z' ∈ Λ ∧ z' ∈ X' ∧ algebraMap F E S.th • m = z + z' := by
  induction hm using Submodule.span_induction with
  | mem y hy =>
    rcases hy with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact ⟨_, 0, smul_memO S hth (hg i).1, X.smul_mem _ (hg i).2, Λ.zero_mem, X'.zero_mem, (add_zero _).symm⟩
    · refine ⟨-g i, g' i, Λ.neg_mem (hg i).1, X.neg_mem (hg i).2, (hg' i).1, (hg' i).2, ?_⟩
      rw [← mul_smul, ← map_mul, mul_inv_cancel₀ h0, map_one, one_smul]; abel
  | zero => exact ⟨0, 0, Λ.zero_mem, X.zero_mem, Λ.zero_mem, X'.zero_mem, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨z, z', h1, h2, h3, h4, e⟩ := ha
    obtain ⟨y, y', k1, k2, k3, k4, e'⟩ := hb
    refine ⟨z + y, z' + y', Λ.add_mem h1 k1, X.add_mem h2 k2, Λ.add_mem h3 k3, X'.add_mem h4 k4, ?_⟩
    rw [smul_add, e, e']; abel
  | smul c a _ ha =>
    obtain ⟨z, z', h1, h2, h3, h4, e⟩ := ha
    refine ⟨(c : E) • z, (c : E) • z', smul_memO S c.2 h1, X.smul_mem _ h2, smul_memO S c.2 h3,
      X'.smul_mem _ h4, ?_⟩
    show _ • (c : E) • a = _
    rw [smul_comm, e, smul_add]
end GlobalTheory.MoveFine
