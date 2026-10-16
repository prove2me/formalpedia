-- Prove2me | solution 1 for OAI.Problem346.SecondTransfer.source_occurrences
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T18:10:15.605467+00:00
-- url     : https://prove2.me/submissions/5817695d-dc87-48a1-9e08-56211ec35f54

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/SecondCounts.lean:L51-L70
-- (upload_full_project.md Phase 4): solution for node OAI.Problem346.SecondTransfer.source_occurrences. The node keeps its source
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

-- ---- from OAI.RepresentationTheory.FoulkesHowe.SecondCounts ----
namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem346.SecondTransfer

/-- A source occurrence lies in exactly one nonzero row and beyond its
already-transferred prefix. -/
theorem label_eq_source_iff {r b : ℕ} (k : Fin r → ℕ)
    (i : Fin r) (p : Fin (r+1) × Fin b) :
    label k p = some i.succ ↔ p.1 = i.succ ∧ k i ≤ p.2.val := by
  rcases p with ⟨l,j⟩
  refine Fin.cases ?_ (fun l => ?_) l
  · simp [Ne.symm (Fin.succ_ne_zero i)]
  · by_cases h : l = i
    · subst l
      simp [not_lt]
    · simp [label_succ_row, Fin.succ_inj, h]

private theorem sum_fin_ite_lt (b k : ℕ) (hk : k ≤ b) :
    (∑ j : Fin b, if j.val < k then 1 else 0) = k := by
  classical
  by_cases h : k < b
  · let c : Fin b := ⟨k,h⟩
    have hs : Finset.univ.filter (fun j : Fin b => j.val < k) = Finset.Iio c := by
      ext j
      simp [c, Fin.lt_def]
    rw [← Finset.card_filter, hs, Fin.card_Iio]
  · have hkb : k = b := by omega
    subst k
    simp

private theorem sum_fin_ite_le (b k : ℕ) (hk : k ≤ b) :
    (∑ j : Fin b, if k ≤ j.val then 1 else 0) = b-k := by
  classical
  have h := sum_fin_ite_lt b k hk
  have hs : (∑ j : Fin b, if j.val < k then 1 else 0) +
      (∑ j : Fin b, if k ≤ j.val then 1 else 0) = b := by
    rw [← Finset.sum_add_distrib]
    have : ∀ j : Fin b, (if j.val < k then 1 else 0) +
        (if k ≤ j.val then 1 else 0) = (1 : ℕ) := by
      intro j
      split_ifs <;> omega
    simp_rw [this]
    simp
  omega

/-- Number of occurrences of the still-independent vector in row `i`. -/
theorem source_occurrences {r b : ℕ} (k : Fin r → ℕ)
    (hk : ∀ i, k i ≤ b) (i : Fin r) :
    (∑ p : Fin (r+1) × Fin b, if label k p = some i.succ then 1 else 0) = b-k i := by
  classical
  simp_rw [label_eq_source_iff]
  rw [Fintype.sum_prod_type]
  dsimp only
  simp only [ite_and]
  rw [Finset.sum_comm]
  calc
    _ = ∑ j : Fin b, if k i ≤ j.val then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_eq_single i.succ]
      · simp
      · intro l hl hli
        simp [hli]
      · simp
    _ = b-k i := sum_fin_ite_le b (k i) (hk i)

end Problem346.SecondTransfer

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem346 OAI.Problem346.SecondTransfer
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Problem346.SecondTransfer.source_occurrences := @_root_.OAI.Problem346.SecondTransfer.source_occurrences
