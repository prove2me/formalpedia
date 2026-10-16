-- Prove2me | solution 1 for OAI.Problem346.SecondTransfer.update_label_eq_progress_rowSwap
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T18:12:00.912002+00:00
-- url     : https://prove2.me/submissions/3568d69a-5f89-4ebb-9f56-11f2ac612385

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/SecondSwap.lean:L13-L49
-- (upload_full_project.md Phase 4): solution for node OAI.Problem346.SecondTransfer.update_label_eq_progress_rowSwap. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FoulkesHowe
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Model
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DegreeOne
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Functoriality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_LinearCase
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PermanentPairing
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricLift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_AlgebraEvaluation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricDual
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_TensorPresentation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FiniteDimension
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MonomialMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Spanning
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Actions
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Naturality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DualEmbedding
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PairingConstruction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FoulkesMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_CanonicalMap
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Multiplication
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_VanishingInduction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DiagonalCoefficient
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstLabels
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FlattenedForm
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MultilinearPolynomial
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_BlockWeight
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstPolynomial
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PolynomialShift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstCounts
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SlotDerivative
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_TransferEndpoints
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SecondLabels
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SecondSwap

-- ---- from OAI.RepresentationTheory.FoulkesHowe.SecondSwap ----
namespace OAI

noncomputable section
namespace Problem346.SecondTransfer

/-- Changing any remaining source factor to the common block agrees with progressing
the prefix count, after a permutation internal to that row. -/
theorem update_label_eq_progress_rowSwap
    {r b : ℕ} (k : Fin r → ℕ) (i : Fin r) (hi : k i < b)
    (j : Fin b) (hj : k i ≤ j.val) (p : Fin (r+1) × Fin b) :
    Function.update (label k) (i.succ, j) none p =
      label (Function.update k i (k i+1))
        (p.1, rowFactorSwap i j ⟨k i, hi⟩ p.1 p.2) := by
  classical
  rcases p with ⟨a,l⟩
  refine Fin.cases ?_ (fun a => ?_) a
  · simp [Function.update, rowFactorSwap, label]
    intro h
    have hv := congrArg Fin.val h
    simp at hv
  · by_cases hai : a = i
    · subst a
      by_cases hlj : l = j
      · subst l
        simp [rowFactorSwap, label]
      · by_cases hlk : l = (⟨k i, hi⟩ : Fin b)
        · subst l
          have hjval : k i < j.val := by
            have hne : j.val ≠ k i := by
              intro he
              apply hlj
              exact Fin.ext he.symm
            omega
          simp [rowFactorSwap, label, hlj, Nat.not_lt.mpr (by omega : k i+1 ≤ j.val)]
        · have hval : l.val ≠ k i := by
            intro he
            apply hlk
            exact Fin.ext he
          have hlt : l.val < k i+1 ↔ l.val < k i := by omega
          simp [rowFactorSwap, label, hlj, hlt,
            Equiv.swap_apply_of_ne_of_ne hlj hlk]
    · simp [rowFactorSwap, label, hai]

end Problem346.SecondTransfer

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem346 OAI.Problem346.SecondTransfer


theorem solution : type_of% @_root_.OAI.Problem346.SecondTransfer.update_label_eq_progress_rowSwap := @_root_.OAI.Problem346.SecondTransfer.update_label_eq_progress_rowSwap
