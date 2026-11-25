-- Prove2me | solution 1 for GlobalTheory.HL.MoveFacts.mem_span_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:50:42.541408+00:00
-- url     : https://prove2.me/submissions/e8cbb251-0f8e-40cb-9224-fcbe6313001a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFramesDatumMoveProperties
import Theorems.Thm_GlobalTheory_HL_TermBasic_sub_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.MoveFacts
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.MoveFacts
theorem _root_.solution (g : Fin (r + 1) → S.V) (n : S.GLV) (hn : n ∈ S.Nof g) (j : Fin r)
    (x : S.V) (hx : x ∈ S.spanTo g (j + 1)) :
    x ∈ Submodule.span E (Set.range fun b => n (g b)) := by
  have key : ∀ m : ℕ, m ≤ r → S.spanTo g m ≤ Submodule.span E (Set.range fun b => n (g b)) := by
    intro m
    induction m with
    | zero =>
      intro _
      unfold Frames.spanTo
      rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      exact absurd (show (i : ℕ) < 0 from hi) (Nat.not_lt_zero _)
    | succ m ih =>
      intro hm
      have hm' : m < r := by omega
      have h0 : n ∈ S.Nof g := hn
      unfold Frames.Nof at h0
      have hI := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp h0).1).2
      have hU : n ∈ unipOn (S.spanTo g (m + 1)) (S.spanTo g m) := Subgroup.mem_iInf.mp hI ⟨m, hm'⟩
      have hU' : (∀ v, n v ∈ S.spanTo g (m + 1) ↔ v ∈ S.spanTo g (m + 1)) ∧
          ∀ v ∈ S.spanTo g (m + 1), n v - v ∈ S.spanTo g m := hU
      have hsub : S.spanTo g (m + 1) ≤ Submodule.span E (Set.range fun b => n (g b)) := by
        unfold Frames.spanTo
        rw [Submodule.span_le]
        rintro _ ⟨i, hi, rfl⟩
        have hgi : g i ∈ S.spanTo g (m + 1) := Submodule.subset_span ⟨i, hi, rfl⟩
        have h2 := ih hm'.le (hU'.2 (g i) hgi)
        have h3 : n (g i) ∈ Submodule.span E (Set.range fun b => n (g b)) :=
          Submodule.subset_span ⟨i, rfl⟩
        have h4 := Submodule.sub_mem _ h3 h2
        rwa [sub_sub_cancel] at h4
      exact hsub
  exact key (j + 1) (Nat.succ_le_of_lt j.2) hx
end GlobalTheory.HL.MoveFacts
