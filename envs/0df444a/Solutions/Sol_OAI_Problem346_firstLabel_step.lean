-- Prove2me | solution 1 for OAI.Problem346.firstLabel_step
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T17:42:52.485607+00:00
-- url     : https://prove2.me/submissions/e74cb7a2-f210-4fa8-9356-8b3cc134b756

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/FirstCounts.lean:L100-L122
-- (upload_full_project.md Phase 4): solution for node OAI.Problem346.firstLabel_step. The node keeps its source
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

-- ---- from OAI.RepresentationTheory.FoulkesHowe.FirstCounts ----
namespace OAI

open scoped BigOperators

namespace Problem346

theorem firstLabel_step (r m k : ℕ) (hk : k < m) :
    firstLabel r m (k + 1) = Function.update (firstLabel r m k)
      (0, ⟨k, Nat.lt_of_lt_of_le hk (Nat.le_add_left m r)⟩) (some (some ⟨k, hk⟩)) := by
  classical
  funext p
  rcases p with ⟨i, j⟩
  by_cases hi : i = 0
  · subst i
    by_cases hj : j.val = k
    · have hjeq : j = (⟨k, Nat.lt_of_lt_of_le hk (Nat.le_add_left m r)⟩ : Fin (r + m)) := Fin.ext hj
      rw [hjeq]
      simp [firstLabel, hk]
    · have hp : ((0 : Fin (r + 1)), j) ≠ (0, (⟨k, Nat.lt_of_lt_of_le hk (Nat.le_add_left m r)⟩ : Fin (r + m))) := by
        intro h
        exact hj (congrArg (fun p : Fin (r + 1) × Fin (r + m) => p.2.val) h)
      rw [Function.update_of_ne hp]
      have hlt : j.val < k + 1 ↔ j.val < k := by omega
      simp only [firstLabel_zero, hlt]
  · have hp : (i, j) ≠ (0, (⟨k, Nat.lt_of_lt_of_le hk (Nat.le_add_left m r)⟩ : Fin (r + m))) := by
      intro h
      exact hi (congrArg Prod.fst h)
    rw [Function.update_of_ne hp]
    simp [firstLabel, hi]

end Problem346

end OAI

-- ---- platform node ----
open OAI OAI.Problem346
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Problem346.firstLabel_step := @_root_.OAI.Problem346.firstLabel_step
