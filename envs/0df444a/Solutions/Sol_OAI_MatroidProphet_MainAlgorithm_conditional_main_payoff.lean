-- Prove2me | solution 1 for OAI.MatroidProphet.MainAlgorithm.conditional_main_payoff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:31:01.669899+00:00
-- url     : https://prove2.me/submissions/63e40633-a263-490d-a928-1edbd62a4e10

import Mathlib
import Definitions.Def_MatroidSecretary
import Definitions.Def_OAIW2MS000
import Theorems.Thm_OAI_MatroidProphet_MainAlgorithm_listedTransferGap_parity_expectation_le

section
-- module Solutions.OAIW2_MatroidSec.Compat
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_FiniteBits
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open Finset

variable {α : Type*} [DecidableEq α]

lemma bitsExpectation_mono (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (V : Finset α) {f g : Finset α → ℝ} (h : ∀ S ⊆ V, f S ≤ g S) :
    bitsExpectation q V f ≤ bitsExpectation q V g := by
  apply sum_le_sum
  intro S hS
  exact mul_le_mul_of_nonneg_left (h S (mem_powerset.1 hS)) (bitsWeight_nonneg q hq0 hq1 V S)

lemma bitsExpectation_congr (q : α → ℝ) (V : Finset α)
    {f g : Finset α → ℝ} (h : ∀ S ⊆ V, f S = g S) :
    bitsExpectation q V f = bitsExpectation q V g := by
  apply sum_congr rfl
  intro S hS
  rw [h S (mem_powerset.1 hS)]

lemma bitsExpectation_add (q : α → ℝ) (V : Finset α) (f g : Finset α → ℝ) :
    bitsExpectation q V (fun S => f S + g S) =
      bitsExpectation q V f + bitsExpectation q V g := by
  simp only [bitsExpectation, mul_add, sum_add_distrib]

lemma bitsExpectation_const (q : α → ℝ) (V : Finset α) (c : ℝ) :
    bitsExpectation q V (fun _ => c) = c := by
  have h := bitsExpectation_one q V
  simp only [bitsExpectation, mul_one] at h
  simp only [bitsExpectation, ← sum_mul, h, one_mul]

lemma bitsExpectation_nonneg (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (V : Finset α) {f : Finset α → ℝ} (h : ∀ S ⊆ V, 0 ≤ f S) :
    0 ≤ bitsExpectation q V f := by
  apply sum_nonneg
  intro S hS
  exact mul_nonneg (bitsWeight_nonneg q hq0 hq1 V S) (h S (mem_powerset.1 hS))

lemma bitsFailure_nonneg (cert : Finset α → Prop) [DecidablePred cert]
    (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (V I : Finset α) : 0 ≤ bitsFailure cert q V I := by
  apply bitsExpectation_nonneg q hq0 hq1
  intro S hS
  split_ifs <;> norm_num

lemma bitsFailure_le_one (cert : Finset α → Prop) [DecidablePred cert]
    (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (V I : Finset α) : bitsFailure cert q V I ≤ 1 := by
  rw [← bitsExpectation_one q V]
  apply bitsExpectation_mono q hq0 hq1
  intro S hS
  split_ifs <;> norm_num

lemma bitsFailure_forced_antitone (cert : Finset α → Prop) [DecidablePred cert]
    (hcert : Monotone cert) (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (V : Finset α) {I J : Finset α} (hIJ : I ⊆ J) :
    bitsFailure cert q V J ≤ bitsFailure cert q V I := by
  apply bitsExpectation_mono q hq0 hq1
  intro S hS
  have himp : cert (I ∪ S) → cert (J ∪ S) := hcert (union_subset_union hIJ Subset.rfl)
  by_cases hi : cert (I ∪ S)
  · simp [hi, himp hi]
  · split_ifs <;> norm_num

lemma bitsFailure_certifies (cert : Finset α → Prop) [DecidablePred cert]
    (hcert : Monotone cert) (q : α → ℝ) (V I : Finset α) (hI : cert I) :
    bitsFailure cert q V I = 0 := by
  unfold bitsFailure bitsExpectation
  apply sum_eq_zero
  intro S hS
  have hIS : cert (I ∪ S) := hcert subset_union_left hI
  simp [hIS]

lemma bitsFailure_insert (cert : Finset α → Prop) [DecidablePred cert]
    (q : α → ℝ) (V I : Finset α) (e : α) (he : e ∉ V) :
    bitsFailure cert q (insert e V) I =
      (1 - q e) * bitsFailure cert q V I + q e * bitsFailure cert q V (insert e I) := by
  unfold bitsFailure
  rw [bitsExpectation_insert q V e he]
  congr 2
  apply bitsExpectation_congr
  intro S hS
  simp only [union_insert, insert_union]

lemma bitsFailure_split (cert : Finset α → Prop) [DecidablePred cert]
    (q : α → ℝ) (V I : Finset α) (e : α) (he : e ∈ V) :
    bitsFailure cert q V I = (1 - q e) * bitsFailure cert q (V.erase e) I +
      q e * bitsFailure cert q (V.erase e) (insert e I) := by
  have h := bitsFailure_insert cert q (V.erase e) I e (notMem_erase e V)
  simpa only [insert_erase he] using h

lemma bitsFailure_antitone (cert : Finset α → Prop) [DecidablePred cert]
    (hcert : Monotone cert) (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (I : Finset α) : Antitone (fun V => bitsFailure cert q V I) := by
  apply Finset.antitone_iff_forall_insert_le.2
  intro V e he
  rw [bitsFailure_insert cert q V I e he]
  have h := bitsFailure_forced_antitone cert hcert q hq0 hq1 V (subset_insert e I)
  have hmul := mul_le_mul_of_nonneg_left h (hq0 e)
  nlinarith

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_AdaptiveResampling
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α β : Type*} [DecidableEq α]

lemma bitsExpectation_mul_left (q : α → ℝ) (V : Finset α) (c : ℝ) (f : Finset α → ℝ) :
    bitsExpectation q V (fun S => c * f S) = c * bitsExpectation q V f := by
  simp only [bitsExpectation, mul_sum]
  apply sum_congr rfl
  intro S hS
  ring

lemma bitsExpectation_mul_right (q : α → ℝ) (V : Finset α) (c : ℝ) (f : Finset α → ℝ) :
    bitsExpectation q V (fun S => f S * c) = bitsExpectation q V f * c := by
  simp only [bitsExpectation, sum_mul]
  apply sum_congr rfl
  intro S hS
  ring

lemma RevealTree.queried_subset (tree : RevealTree α β) (V S : Finset α) (fresh : tree.Fresh V) :
    tree.queried S ⊆ V := by
  induction tree generalizing V S with
  | leaf value => exact empty_subset V
  | query e no yes ihn ihy =>
    rcases fresh with ⟨he, hn, hy⟩
    apply insert_subset he
    by_cases heS : e ∈ S
    · simpa [queried, heS] using (ihy (V.erase e) (S.erase e) hy).trans (erase_subset e V)
    · simpa [queried, heS] using (ihn (V.erase e) (S.erase e) hn).trans (erase_subset e V)

lemma RevealTree.run_query_no (e : α) (no yes : RevealTree α β) (S : Finset α) (he : e ∉ S) :
    (RevealTree.query e no yes).run S = no.run S := by simp [run, he]

lemma RevealTree.run_query_yes (e : α) (no yes : RevealTree α β) (S : Finset α) (he : e ∉ S) :
    (RevealTree.query e no yes).run (insert e S) = yes.run S := by simp [run, he]

lemma RevealTree.hybrid_query (e : α) (no yes : RevealTree α β) (S T : Finset α)
    (heS : e ∉ S) (heT : e ∉ T) :
    (RevealTree.query e no yes).hybrid S T = no.hybrid S T ∧
    (RevealTree.query e no yes).hybrid S (insert e T) = insert e (no.hybrid S T) ∧
    (RevealTree.query e no yes).hybrid (insert e S) T = yes.hybrid S T ∧
    (RevealTree.query e no yes).hybrid (insert e S) (insert e T) = insert e (yes.hybrid S T) := by
  simp [hybrid, heS, heT]

lemma RevealTree.mean_run_query (q : α → ℝ) (V : Finset α) (e : α)
    (no yes : RevealTree α β) (φ : β → ℝ) (he : e ∈ V) :
    bitsExpectation q V (fun S => φ ((RevealTree.query e no yes).run S)) =
      (1-q e) * bitsExpectation q (V.erase e) (fun S => φ (no.run S)) +
        q e * bitsExpectation q (V.erase e) (fun S => φ (yes.run S)) := by
  have hs := bitsExpectation_insert q (V.erase e) e (notMem_erase e V)
    (fun S => φ ((RevealTree.query e no yes).run S))
  rw [insert_erase he] at hs
  rw [hs]
  congr 1
  · congr 1
    apply bitsExpectation_congr
    intro S hS
    rw [run_query_no _ _ _ _ (fun heS => notMem_erase e V (hS heS))]
  · congr 1
    apply bitsExpectation_congr
    intro S hS
    rw [run_query_yes _ _ _ _ (fun heS => notMem_erase e V (hS heS))]

theorem RevealTree.hybrid_independent (tree : RevealTree α β)
    (q : α → ℝ) (V : Finset α) (fresh : tree.Fresh V)
    (φ : β → ℝ) (ψ : Finset α → ℝ) :
    bitsExpectation q V (fun S => bitsExpectation q V (fun T => φ (tree.run S) * ψ (tree.hybrid S T))) =
      bitsExpectation q V (fun S => φ (tree.run S)) * bitsExpectation q V ψ := by
  induction tree generalizing V ψ with
  | leaf value =>
    simp only [run, hybrid, bitsExpectation_const]
    exact bitsExpectation_mul_left q V (φ value) ψ
  | query e no yes ihn ihy =>
    rcases fresh with ⟨he, hn, hy⟩
    let W := V.erase e
    have heW : e ∉ W := notMem_erase e V
    have hWV : insert e W = V := insert_erase he
    have hsplit (S : Finset α) := bitsExpectation_insert q W e heW
      (fun T => φ ((RevealTree.query e no yes).run S) * ψ ((RevealTree.query e no yes).hybrid S T))
    have hNo : bitsExpectation q W (fun S => bitsExpectation q V
        (fun T => φ ((RevealTree.query e no yes).run S) * ψ ((RevealTree.query e no yes).hybrid S T))) =
        (1-q e) * bitsExpectation q W (fun S => bitsExpectation q W
          (fun T => φ (no.run S) * ψ (no.hybrid S T))) +
        q e * bitsExpectation q W (fun S => bitsExpectation q W
          (fun T => φ (no.run S) * ψ (insert e (no.hybrid S T)))) := by
      rw [← bitsExpectation_mul_left, ← bitsExpectation_mul_left, ← bitsExpectation_add]
      apply bitsExpectation_congr
      intro S hS
      have heS : e ∉ S := fun hs => heW (hS hs)
      have h := hsplit S
      rw [hWV] at h
      rw [h]
      congr 1
      · congr 1
        apply bitsExpectation_congr
        intro T hT
        have heT : e ∉ T := fun ht => heW (hT ht)
        rw [run_query_no _ _ _ _ heS, (hybrid_query e no yes S T heS heT).1]
      · congr 1
        apply bitsExpectation_congr
        intro T hT
        have heT : e ∉ T := fun ht => heW (hT ht)
        rw [run_query_no _ _ _ _ heS, (hybrid_query e no yes S T heS heT).2.1]
    have hYes : bitsExpectation q W (fun S => bitsExpectation q V
        (fun T => φ ((RevealTree.query e no yes).run (insert e S)) *
          ψ ((RevealTree.query e no yes).hybrid (insert e S) T))) =
        (1-q e) * bitsExpectation q W (fun S => bitsExpectation q W
          (fun T => φ (yes.run S) * ψ (yes.hybrid S T))) +
        q e * bitsExpectation q W (fun S => bitsExpectation q W
          (fun T => φ (yes.run S) * ψ (insert e (yes.hybrid S T)))) := by
      rw [← bitsExpectation_mul_left, ← bitsExpectation_mul_left, ← bitsExpectation_add]
      apply bitsExpectation_congr
      intro S hS
      have heS : e ∉ S := fun hs => heW (hS hs)
      have h := hsplit (insert e S)
      rw [hWV] at h
      rw [h]
      congr 1
      · congr 1
        apply bitsExpectation_congr
        intro T hT
        have heT : e ∉ T := fun ht => heW (hT ht)
        rw [run_query_yes _ _ _ _ heS, (hybrid_query e no yes S T heS heT).2.2.1]
      · congr 1
        apply bitsExpectation_congr
        intro T hT
        have heT : e ∉ T := fun ht => heW (hT ht)
        rw [run_query_yes _ _ _ _ heS, (hybrid_query e no yes S T heS heT).2.2.2]
    have hOuter := bitsExpectation_insert q W e heW
      (fun S => bitsExpectation q V (fun T => φ ((RevealTree.query e no yes).run S) *
        ψ ((RevealTree.query e no yes).hybrid S T)))
    rw [hWV, hNo, hYes] at hOuter
    rw [hOuter, ihn W hn ψ, ihn W hn (fun S => ψ (insert e S)),
      ihy W hy ψ, ihy W hy (fun S => ψ (insert e S)), mean_run_query q V e no yes φ he]
    have hPsi := bitsExpectation_insert q W e heW ψ
    rw [hWV] at hPsi
    rw [hPsi]
    ring

lemma RevealTree.hybrid_eq_resample (tree : RevealTree α β) (V S T : Finset α)
    (fresh : tree.Fresh V) (hS : S ⊆ V) (hT : T ⊆ V) :
    tree.hybrid S T = (S \ tree.queried S) ∪ (T ∩ tree.queried S) := by
  induction tree generalizing V S T with
  | leaf value => simp [hybrid, queried]
  | query e no yes ihn ihy =>
    rcases fresh with ⟨he, hn, hy⟩
    have hSerase : S.erase e ⊆ V.erase e := erase_subset_erase e hS
    have hTerase : T.erase e ⊆ V.erase e := erase_subset_erase e hT
    by_cases heS : e ∈ S
    · have hq := yes.queried_subset (V.erase e) (S.erase e) hy
      have heq : e ∉ yes.queried (S.erase e) := fun h => notMem_erase e V (hq h)
      have hi := ihy (V.erase e) (S.erase e) (T.erase e) hy hSerase hTerase
      simp only [hybrid, queried, ite_eq_left heS, hi]
      by_cases heT : e ∈ T
      · rw [ite_eq_left heT]
        ext x
        by_cases hxe : x = e
        · subst x; simp [heS, heT, heq]
        · simp [hxe]
      · rw [ite_eq_right heT]
        ext x
        by_cases hxe : x = e
        · subst x; simp [heS, heT, heq]
        · simp [hxe]
    · have hq := no.queried_subset (V.erase e) (S.erase e) hn
      have heq : e ∉ no.queried (S.erase e) := fun h => notMem_erase e V (hq h)
      have hi := ihn (V.erase e) (S.erase e) (T.erase e) hn hSerase hTerase
      simp only [hybrid, queried, ite_eq_right heS, hi]
      by_cases heT : e ∈ T
      · rw [ite_eq_left heT]
        ext x
        by_cases hxe : x = e
        · subst x; simp [heS, heT]
        · simp [hxe]
      · rw [ite_eq_right heT]
        ext x
        by_cases hxe : x = e
        · subst x; simp [heS, heT]
        · simp [hxe]

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Density_Basic
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set

variable {α : Type*} [Fintype α]

lemma natRank_mono (M : Matroid α) {X Y : Set α} (h : X ⊆ Y) :
    natRank M X ≤ natRank M Y :=
  ENat.toNat_le_toNat (M.eRk_mono h) (rank_ne_top M Y)

lemma densityExpansion_flat (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D P : Set α) : M.IsFlat (densityExpansion M hE κ D P) :=
  (densityExpansion_spec M hE κ D P).1.1

lemma densityExpansion_mono (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D : Set α) {P P' : Set α} (hPP' : P ⊆ P') :
    densityExpansion M hE κ D P ⊆ densityExpansion M hE κ D P' := by
  let Q := densityExpansion M hE κ D P
  let Q' := densityExpansion M hE κ D P'
  have hQ : IsDensityMax M κ D P Q := (densityExpansion_spec M hE κ D P).1
  have hQ' : IsDensityMax M κ D P' Q' := (densityExpansion_spec M hE κ D P').1
  have hPint : P ⊆ Q ∩ Q' := subset_inter hQ.2.1 (hPP'.trans hQ'.2.1)
  have hP'cl : P' ⊆ M.closure (Q ∪ Q') :=
    hQ'.2.1.trans (subset_union_right.trans (M.subset_closure _ (by simp [hE])))
  have hInt := hQ.2.2 (Q ∩ Q') (flat_inter M hQ.1 hQ'.1) hPint
  have hSup := densityObjective_supermod M hE κ D Q Q'
  have hjoin : IsDensityMax M κ D P' (M.closure (Q ∪ Q')) := by
    refine ⟨Matroid.isFlat_closure (M := M) _, hP'cl, ?_⟩
    intro Z hZ hPZ
    have hm := hQ'.2.2 Z hZ hPZ
    omega
  exact (subset_union_left.trans (M.subset_closure _ (by simp [hE]))).trans
    ((densityExpansion_spec M hE κ D P').2 _ hjoin)

omit [Fintype α] in
lemma natRank_eq_ncard_of_basis (M : Matroid α) {I X : Set α}
    (hI : M.IsBasis I X) : natRank M X = I.ncard := by
  rw [natRank, ← hI.encard_eq_eRk, Set.ncard_def]

lemma closure_eq_of_subset_of_natRank_le (M : Matroid α) {X Y : Set α}
    (hXY : X ⊆ Y) (hr : natRank M Y ≤ natRank M X) : M.closure X = M.closure Y := by
  apply (M.isRkFinite_set X).closure_eq_closure_of_subset_of_eRk_ge_eRk hXY
  have hcast : (natRank M Y : ℕ∞) ≤ (natRank M X : ℕ∞) := by exact_mod_cast hr
  simpa only [natRank, ENat.natCast_toNat (rank_ne_top M _)] using hcast

lemma densityExpansion_generated (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (hκ : 0 < κ) (D P : Set α) :
    let Q := densityExpansion M hE κ D P
    M.closure (P ∪ (D ∩ Q)) = Q := by
  dsimp only
  let Q := densityExpansion M hE κ D P
  let A := M.closure (P ∪ (D ∩ Q))
  have hQ : IsDensityMax M κ D P Q := (densityExpansion_spec M hE κ D P).1
  have hAQ : A ⊆ Q := by
    exact (M.closure_subset_closure (union_subset hQ.2.1 inter_subset_right)).trans_eq hQ.1.closure
  have hPA : P ⊆ A := subset_union_left.trans (M.subset_closure _ (by simp [hE]))
  have hDA : D ∩ A = D ∩ Q := by
    apply Subset.antisymm (inter_subset_inter_right D hAQ)
    exact fun e he => ⟨he.1, M.subset_closure _ (by simp [hE]) (Or.inr he)⟩
  have hm := hQ.2.2 A (Matroid.isFlat_closure (M := M) _) hPA
  have hr : natRank M Q ≤ natRank M A := by
    dsimp [densityObjective] at hm
    rw [hDA] at hm
    have hm' : (κ : ℤ) * natRank M Q ≤ (κ : ℤ) * natRank M A := by omega
    have hk' : (0 : ℤ) < κ := by exact_mod_cast hκ
    exact_mod_cast (le_of_mul_le_mul_left hm' hk')
  have heq := closure_eq_of_subset_of_natRank_le M hAQ hr
  simpa only [A, M.closure_closure, hQ.1.closure] using heq

lemma exists_extension_generators (M : Matroid α) (hE : M.E = univ)
    (R D Q : Set α) (_hR : M.IsFlat R) (hgen : M.closure (R ∪ D) = Q) :
    ∃ K : Set α, K ⊆ D \ R ∧ M.closure (R ∪ K) = Q ∧
      K.ncard + natRank M R = natRank M Q := by
  obtain ⟨I, hI, hIR⟩ := M.exists_isBasis_union_inter_isBasis D R
    (by simp [hE]) (by simp [hE])
  refine ⟨I \ R, ?_, ?_, ?_⟩
  · intro e he
    refine ⟨?_, he.2⟩
    rcases hI.subset he.1 with hD | hr
    · exact hD
    · exact (he.2 hr).elim
  · apply Subset.antisymm
    · have hsub : R ∪ (I \ R) ⊆ R ∪ D := by
        intro e he
        rcases he with hr | hi
        · exact Or.inl hr
        · rcases hI.subset hi.1 with hd | hr
          · exact Or.inr hd
          · exact Or.inl hr
      exact (M.closure_subset_closure hsub).trans_eq hgen
    · have hIsub : I ⊆ R ∪ (I \ R) := by intro e he; by_cases hr : e ∈ R <;> simp_all
      calc
        Q = M.closure (D ∪ R) := by rw [union_comm D R, hgen]
        _ = M.closure I := hI.closure_eq_closure.symm
        _ ⊆ M.closure (R ∪ (I \ R)) := M.closure_subset_closure hIsub
  · have hiRank : natRank M Q = I.ncard := by
      rw [← hgen, natRank_closure, union_comm R D]
      exact natRank_eq_ncard_of_basis M hI
    rw [natRank_eq_ncard_of_basis M hIR, hiRank]
    simpa only [add_comm] using Set.ncard_inter_add_ncard_sdiff_eq_ncard I R

lemma densityExpansion_generator_step (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (hκ : 0 < κ) (D P R : Set α) (hR : M.IsFlat R)
    (hPR : P ⊆ R) (hRQ : R ⊆ densityExpansion M hE κ D P) :
    ∃ K : Set α,
      K ⊆ (D ∩ densityExpansion M hE κ D P) \ R ∧
      M.closure (R ∪ K) = densityExpansion M hE κ D P ∧
      κ * K.ncard + (D ∩ R).ncard ≤
        (D ∩ densityExpansion M hE κ D P).ncard := by
  let Q := densityExpansion M hE κ D P
  have hQ : IsDensityMax M κ D P Q := (densityExpansion_spec M hE κ D P).1
  have hgen : M.closure (R ∪ (D ∩ Q)) = Q := by
    apply Subset.antisymm
    · exact (M.closure_subset_closure (union_subset hRQ inter_subset_right)).trans_eq hQ.1.closure
    · calc
        Q = M.closure (P ∪ (D ∩ Q)) := (densityExpansion_generated M hE κ hκ D P).symm
        _ ⊆ M.closure (R ∪ (D ∩ Q)) :=
          M.closure_subset_closure (union_subset_union hPR Subset.rfl)
  obtain ⟨K, hK, hKgen, hKcard⟩ := exists_extension_generators M hE R (D ∩ Q) Q hR hgen
  refine ⟨K, hK, hKgen, ?_⟩
  have hm := hQ.2.2 R hR hPR
  dsimp [densityObjective] at hm
  have hmul := congrArg (fun x : ℕ => κ * x) hKcard
  rw [Nat.mul_add] at hmul
  exact_mod_cast (show (κ : ℤ) * K.ncard + (D ∩ R).ncard ≤ (D ∩ Q).ncard by
    have hmul' : (κ : ℤ) * K.ncard + (κ : ℤ) * natRank M R =
        (κ : ℤ) * natRank M Q := by exact_mod_cast hmul
    omega)

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Density_Path
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set

variable {α : Type*} [Fintype α]

private lemma densityPath_prefix (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (hκ : 0 < κ) (D : Set α) (P : ℕ → Set α) (hP : Monotone P) (N : ℕ) :
    ∃ J : ℕ → Set α, Monotone J ∧ (∀ k, J k ⊆ D) ∧
      (∀ k ≤ N, M.closure (P k ∪ J k) = densityExpansion M hE κ D (P k)) ∧
      κ * (J N).ncard ≤ (D ∩ densityExpansion M hE κ D (P N)).ncard ∧
      (∀ k, N ≤ k → J k = J N) := by
  induction N with
  | zero =>
    have hPQ : M.closure (P 0) ⊆ densityExpansion M hE κ D (P 0) := by
      exact (M.closure_subset_closure (densityExpansion_extensive M hE κ D (P 0))).trans_eq
        (densityExpansion_flat M hE κ D (P 0)).closure
    obtain ⟨K, hK, hgen, hcard⟩ := densityExpansion_generator_step M hE κ hκ D (P 0)
      (M.closure (P 0)) (Matroid.isFlat_closure (M := M) _)
      (M.subset_closure _ (by simp [hE])) hPQ
    refine ⟨fun _ => K, fun _ _ _ => Subset.rfl, ?_, ?_, ?_, ?_⟩
    · exact fun _ _ he => (hK he).1.1
    · intro k hk
      have hk0 : k = 0 := by omega
      subst k
      simpa only [M.closure_union_closure_left_eq] using hgen
    · dsimp only
      omega
    · exact fun _ _ => rfl
  | succ N ih =>
    obtain ⟨J, hJmono, hJD, hJgen, hJcard, hJsat⟩ := ih
    let Q := densityExpansion M hE κ D (P N)
    let Q' := densityExpansion M hE κ D (P (N + 1))
    let R := M.closure (P (N + 1) ∪ Q)
    have hQQ' : Q ⊆ Q' := densityExpansion_mono M hE κ D (hP (Nat.le_succ N))
    have hRflat : M.IsFlat R := Matroid.isFlat_closure (M := M) _
    have hPR : P (N + 1) ⊆ R :=
      subset_union_left.trans (M.subset_closure _ (by simp [hE]))
    have hQR : Q ⊆ R := subset_union_right.trans (M.subset_closure _ (by simp [hE]))
    have hRQ' : R ⊆ Q' := by
      exact (M.closure_subset_closure
        (union_subset (densityExpansion_extensive M hE κ D _) hQQ')).trans_eq
        (densityExpansion_flat M hE κ D _).closure
    obtain ⟨K, hK, hKgen, hKcard⟩ :=
      densityExpansion_generator_step M hE κ hκ D (P (N + 1)) R hRflat hPR hRQ'
    have hJNQ : J N ⊆ Q := by
      change J N ⊆ densityExpansion M hE κ D (P N)
      rw [← hJgen N le_rfl]
      exact subset_union_right.trans (M.subset_closure _ (by simp [hE]))
    have hJNR : J N ⊆ R := hJNQ.trans hQR
    have hdisj : Disjoint (J N) K := by
      rw [Set.disjoint_left]
      intro e heJ heK
      exact (hK heK).2 (hJNR heJ)
    have hRgen : M.closure (P (N + 1) ∪ J N) = R := by
      apply Subset.antisymm
      · exact M.closure_subset_closure (union_subset_union Subset.rfl hJNQ)
      · apply Matroid.closure_subset_closure_of_subset_closure
        apply union_subset
        · exact subset_union_left.trans (M.subset_closure _ (by simp [hE]))
        · change densityExpansion M hE κ D (P N) ⊆ _
          rw [← hJgen N le_rfl]
          exact M.closure_subset_closure (union_subset_union (hP (Nat.le_succ N)) Subset.rfl)
    have hnewgen : M.closure (P (N + 1) ∪ (J N ∪ K)) = Q' := by
      calc
        M.closure (P (N + 1) ∪ (J N ∪ K)) =
            M.closure ((P (N + 1) ∪ J N) ∪ K) := by rw [union_assoc]
        _ = M.closure (M.closure (P (N + 1) ∪ J N) ∪ K) :=
          (M.closure_union_closure_left_eq _ _).symm
        _ = M.closure (R ∪ K) := by rw [hRgen]
        _ = Q' := hKgen
    have hnewcard : κ * (J N ∪ K).ncard ≤ (D ∩ Q').ncard := by
      rw [Set.ncard_union_eq hdisj, Nat.mul_add]
      have hm := Set.ncard_mono (inter_subset_inter_right D hQR)
      change κ * K.ncard + (D ∩ R).ncard ≤ (D ∩ Q').ncard at hKcard
      change κ * (J N).ncard ≤ (D ∩ Q).ncard at hJcard
      omega
    let J' : ℕ → Set α := fun k => if k ≤ N then J k else J N ∪ K
    have hJ'last : J' (N + 1) = J N ∪ K := by simp [J']
    refine ⟨J', ?_, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      by_cases hi : i ≤ N
      · by_cases hj : j ≤ N
        · simpa [J', hi, hj] using hJmono hij
        · change (if i ≤ N then J i else J N ∪ K) ⊆ _
          rw [ite_eq_left hi]
          simpa only [J', ite_eq_right hj] using (hJmono hi).trans subset_union_left
      · have hj : ¬j ≤ N := by omega
        simp only [J', ite_eq_right hi, ite_eq_right hj]
        exact Subset.rfl
    · intro k e he
      by_cases hk : k ≤ N
      · exact hJD k (by simpa [J', hk] using he)
      · have he' : e ∈ J N ∪ K := by simpa [J', hk] using he
        rcases he' with heJ | heK
        · exact hJD N heJ
        · exact (hK heK).1.1
    · intro k hk
      by_cases hk' : k ≤ N
      · simpa [J', hk'] using hJgen k hk'
      · have heq : k = N + 1 := by omega
        subst k
        rw [hJ'last]
        exact hnewgen
    · rw [hJ'last]
      exact hnewcard
    · intro k hk
      have hk' : ¬ k ≤ N := by omega
      rw [hJ'last]
      simp [J', hk']

lemma densityPath_generators (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (hκ : 0 < κ) (D : Set α) (P : ℕ → Set α) (hP : Monotone P) (N : ℕ) :
    ∃ Jtotal : Set α, Jtotal ⊆ D ∧ κ * Jtotal.ncard ≤ D.ncard ∧
      ∃ J : ℕ → Set α, Monotone J ∧ (∀ k ≤ N, J k ⊆ Jtotal) ∧
        (∀ k ≤ N, M.closure (P k ∪ J k) = densityExpansion M hE κ D (P k)) := by
  obtain ⟨J, hmono, hD, hgen, hcard, _⟩ := densityPath_prefix M hE κ hκ D P hP N
  refine ⟨J N, hD N, ?_, J, hmono, ?_, hgen⟩
  · exact hcard.trans (Set.ncard_mono inter_subset_left)
  · exact fun k hk => hmono hk

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Density_Guarded
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set
variable {α : Type*} [Fintype α]

lemma densityEnabled_flat (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D : Set α) (a k : ℤ) {P : Set α} (hP : M.IsFlat P) :
    M.IsFlat (densityEnabled M hE κ D a k P) := by
  by_cases hak : a ≤ k
  · simpa only [densityEnabled, ite_eq_left hak] using densityExpansion_flat M hE κ D P
  · simpa only [densityEnabled, ite_eq_right hak] using hP

lemma densityEnabled_mono (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D : Set α) (a : ℤ) {k k' : ℤ} {P P' : Set α}
    (hkk' : k ≤ k') (hPP' : P ⊆ P') :
    densityEnabled M hE κ D a k P ⊆ densityEnabled M hE κ D a k' P' := by
  by_cases hak : a ≤ k
  · have hak' := hak.trans hkk'
    simpa only [densityEnabled, ite_eq_left hak, ite_eq_left hak'] using
      densityExpansion_mono M hE κ D hPP'
  · by_cases hak' : a ≤ k'
    · simpa only [densityEnabled, ite_eq_right hak, ite_eq_left hak'] using
        hPP'.trans (densityExpansion_extensive M hE κ D P')
    · simpa only [densityEnabled, ite_eq_right hak, ite_eq_right hak'] using hPP'

lemma guardedPath_succ (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (k : ℤ) :
    guardedPath M hE κ D C (h+1) k =
      M.closure (nominalPath M hE κ D C h k ∪ (C h ∩ nominalPath M hE κ D C h (k+1))) := rfl

lemma guardedPath_mono (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) : Monotone (guardedPath M hE κ D C h) := by
  induction h with
  | zero =>
    intro i j hij
    by_cases hi : i < 0
    · by_cases hj : j < 0
      · simp only [guardedPath, ite_eq_left hi, ite_eq_left hj, Subset.rfl]
      · simp only [guardedPath, ite_eq_left hi, ite_eq_right hj, subset_univ]
    · have hj : ¬ j < 0 := by omega
      simp only [guardedPath, ite_eq_right hi, ite_eq_right hj, Subset.rfl]
  | succ h ih =>
    intro i j hij
    apply M.closure_subset_closure
    exact union_subset_union (densityEnabled_mono M hE κ (D h) (activation h) hij (ih hij))
      (inter_subset_inter_right (C h)
        (densityEnabled_mono M hE κ (D h) (activation h) (by omega) (ih (by omega))))

lemma nominalPath_mono (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) : Monotone (nominalPath M hE κ D C h) := by
  intro i j hij
  exact densityEnabled_mono M hE κ (D h) (activation h) hij
    (guardedPath_mono M hE κ D C h hij)

lemma guarded_subset_nominal (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (k : ℤ) :
    guardedPath M hE κ D C h k ⊆ nominalPath M hE κ D C h k :=
  densityEnabled_extensive M hE κ (D h) (activation h) k _

lemma nominal_subset_guarded (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (k : ℤ) :
    nominalPath M hE κ D C h k ⊆ guardedPath M hE κ D C (h+1) k :=
  subset_union_left.trans (M.subset_closure _ (by simp [hE]))

lemma guardedPath_early (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) {k : ℤ} (hk : k < -3 * (h : ℤ) - 1) :
    guardedPath M hE κ D C h k = M.closure ∅ := by
  induction h generalizing k with
  | zero =>
    have hk' : k < 0 := by omega
    simp [guardedPath, hk']
  | succ h ih =>
    have hka : ¬ activation h ≤ k := by dsimp [activation]; push_cast at hk; omega
    have hk'a : ¬ activation h ≤ k+1 := by dsimp [activation]; push_cast at hk; omega
    have hkold : k < -3 * (h : ℤ) - 1 := by push_cast at hk; omega
    have hk'old : k+1 < -3 * (h : ℤ) - 1 := by omega
    rw [guardedPath, densityEnabled, densityEnabled, ite_eq_right hka, ite_eq_right hk'a,
      ih hkold, ih hk'old]
    rw [union_eq_self_of_subset_right inter_subset_right, M.closure_closure]

lemma nominalPath_early (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) {k : ℤ} (hk : k < activation h) :
    nominalPath M hE κ D C h k = M.closure ∅ := by
  rw [nominalPath, densityEnabled, ite_eq_right (not_le_of_gt hk)]
  apply guardedPath_early
  dsimp [activation] at hk
  omega

lemma nominalPath_baseline (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) :
    nominalPath M hE κ D C h (activation h) =
      densityExpansion M hE κ (D h) (M.closure ∅) := by
  rw [nominalPath, densityEnabled, ite_eq_left le_rfl, guardedPath_early]
  dsimp [activation]
  omega

lemma nominalPath_baseline_gap (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) :
    nominalPath M hE κ D C h (activation h + 1) =
      nominalPath M hE κ D C h (activation h) := by
  rw [nominalPath_baseline, nominalPath, densityEnabled, ite_eq_left (by omega), guardedPath_early]
  dsimp [activation]
  omega

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Density_Birth
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set
variable {α : Type*} [Fintype α]
attribute [local instance] Classical.propDecidable

lemma nominalBirth_mem (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (e : α) :
    e ∈ nominalPath M hE κ D C h (nominalBirth M hE κ D C h e) :=
  Nat.find_spec (exists_nominal_member M hE κ D C h e)

lemma nominalBirth_bounds (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (e : α) :
    activation h ≤ nominalBirth M hE κ D C h e ∧ nominalBirth M hE κ D C h e ≤ 0 := by
  have hmem : e ∈ nominalPath M hE κ D C h (activation h + (pathHorizon h : ℤ)) := by
    rw [activation_add_horizon, nominalPath_nonnegative M hE κ D C h (by omega)]
    trivial
  have hle := Nat.find_min' (exists_nominal_member M hE κ D C h e) hmem
  have hi : (Nat.find (exists_nominal_member M hE κ D C h e) : ℤ) ≤ pathHorizon h := by
    exact_mod_cast hle
  have hh := activation_add_horizon h
  dsimp only [nominalBirth]
  omega

lemma nominalBirth_not_activation_succ (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (e : α) :
    nominalBirth M hE κ D C h e ≠ activation h + 1 := by
  intro heq
  have hm := nominalBirth_mem M hE κ D C h e
  rw [heq, nominalPath_baseline_gap] at hm
  have hm0 : e ∈ nominalPath M hE κ D C h (activation h + (0 : ℕ)) := by simpa using hm
  have hj := Nat.find_min' (exists_nominal_member M hE κ D C h e) hm0
  have hj0 : Nat.find (exists_nominal_member M hE κ D C h e) = 0 := Nat.eq_zero_of_le_zero hj
  dsimp only [nominalBirth] at heq
  rw [hj0] at heq
  omega

lemma not_mem_nominal_before_birth (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (e : α) (he : e ∉ M.closure ∅)
    {k : ℤ} (hk : k < nominalBirth M hE κ D C h e) :
    e ∉ nominalPath M hE κ D C h k := by
  by_cases hka : k < activation h
  · rwa [nominalPath_early M hE κ D C h hka]
  · intro hm
    have heq : activation h + ((k - activation h).toNat : ℤ) = k := by
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    have hm' : e ∈ nominalPath M hE κ D C h
        (activation h + ((k - activation h).toNat : ℤ)) := by rwa [heq]
    have hf := Nat.find_min' (exists_nominal_member M hE κ D C h e) hm'
    have hfi : (Nat.find (exists_nominal_member M hE κ D C h e) : ℤ) ≤
        ((k - activation h).toNat : ℤ) := by exact_mod_cast hf
    dsimp only [nominalBirth] at hk
    omega

lemma mem_nominal_iff_birth_le (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (e : α) (he : e ∉ M.closure ∅) (k : ℤ) :
    e ∈ nominalPath M hE κ D C h k ↔ nominalBirth M hE κ D C h e ≤ k := by
  constructor
  · intro hm
    by_contra hn
    exact not_mem_nominal_before_birth M hE κ D C h e he (by omega) hm
  · intro hk
    exact nominalPath_mono M hE κ D C h hk (nominalBirth_mem M hE κ D C h e)

lemma nominalPath_generators (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (hκ : 0 < κ) (D C : ℕ → Set α) (h : ℕ) :
    ∃ Jtotal : Set α, Jtotal ⊆ D h ∧ κ * Jtotal.ncard ≤ (D h).ncard ∧
      ∃ J : ℕ → Set α, Monotone J ∧ (∀ j ≤ pathHorizon h, J j ⊆ Jtotal) ∧
        (∀ j ≤ pathHorizon h,
          M.closure (guardedPath M hE κ D C h (activation h + j) ∪ J j) =
            nominalPath M hE κ D C h (activation h + j)) := by
  have hmono : Monotone (fun j : ℕ => guardedPath M hE κ D C h (activation h + j)) := by
    intro i j hij
    apply guardedPath_mono M hE κ D C h
    have hi : (i : ℤ) ≤ j := by exact_mod_cast hij
    omega
  obtain ⟨Jtotal, hJD, hcard, J, hJmono, hJJ, hgen⟩ :=
    densityPath_generators M hE κ hκ (D h)
      (fun j : ℕ => guardedPath M hE κ D C h (activation h + j)) hmono (pathHorizon h)
  refine ⟨Jtotal, hJD, hcard, J, hJmono, hJJ, ?_⟩
  intro j hj
  rw [nominalPath, densityEnabled, ite_eq_left (by omega)]
  exact hgen j hj

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_RankAccounting
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open Set Finset

variable {α : Type*} [Fintype α]

lemma conditionalRank_add_base (M : Matroid α) (S P : Set α) :
    conditionalRank M S P + natRank M P = natRank M (S ∪ P) := by
  exact Nat.sub_add_cancel (natRank_mono M subset_union_right)

lemma conditionalRank_antitone (M : Matroid α) (S : Set α)
    {P Q : Set α} (hPQ : P ⊆ Q) :
    conditionalRank M S Q ≤ conditionalRank M S P := by
  have hsub := natRank_submod M (S ∪ P) Q
  have hi := natRank_mono M (show P ⊆ (S ∪ P) ∩ Q from
    fun x hx => ⟨Or.inr hx, hPQ hx⟩)
  have hu : (S ∪ P) ∪ Q = S ∪ Q := by
    ext x
    simp only [mem_union]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (hPQ h)
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
  rw [hu] at hsub
  have hP := conditionalRank_add_base M S P
  have hQ := conditionalRank_add_base M S Q
  omega

lemma conditionalRank_exchange (M : Matroid α) (S J A : Set α) :
    conditionalRank M S A + conditionalRank M J (A ∪ S) =
      conditionalRank M J A + conditionalRank M S (A ∪ J) := by
  have hSA := conditionalRank_add_base M S A
  have hJA := conditionalRank_add_base M J A
  have hJAS := conditionalRank_add_base M J (A ∪ S)
  have hSAJ := conditionalRank_add_base M S (A ∪ J)
  have hUS : S ∪ A = A ∪ S := union_comm _ _
  have hUJ : J ∪ A = A ∪ J := union_comm _ _
  have hU : J ∪ (A ∪ S) = S ∪ (A ∪ J) := by
    ext x
    simp only [mem_union]
    tauto
  rw [hUS] at hSA
  rw [hUJ] at hJA
  rw [hU] at hJAS
  omega

omit [Fintype α] in
lemma conditionalRank_closure (M : Matroid α) (S P : Set α) :
    conditionalRank M S (M.closure P) = conditionalRank M S P := by
  simp only [conditionalRank, natRank, M.eRk_union_closure_right_eq,
    M.eRk_closure_eq]

lemma conditionalRank_le_rank (M : Matroid α) (J A : Set α) :
    conditionalRank M J A ≤ natRank M J := by
  have h := conditionalRank_antitone M J (empty_subset A)
  simpa [conditionalRank] using h

lemma rankCost_step (M : Matroid α) (J S A B X Y : Set α)
    (hXA : X ⊆ A) (hAB : A ⊆ B)
    (hB : B ⊆ M.closure (A ∪ J)) (hY : A ∪ S ⊆ Y) :
    conditionalRank M S A - conditionalRank M S B ≤
      conditionalRank M J X - conditionalRank M J Y := by
  have hSJ := conditionalRank_antitone M S hB
  rw [conditionalRank_closure] at hSJ
  have hSA := conditionalRank_antitone M S hAB
  have hJA := conditionalRank_antitone M J hXA
  have hJY := conditionalRank_antitone M J hY
  have heq := conditionalRank_exchange M S J A
  omega

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_LayerGreedy
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set Finset
variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
lemma layerGreedy_subset (M : Matroid α) (E : Finset α)
    (base : ℤ → Set α) (layer : α → ℤ) (time : α → ℕ) :
    layerGreedy M E base layer time ⊆ E := by
  classical
  exact filter_subset _ _

lemma layerGreedy_spans_prefix (M : Matroid α) (E : Finset α)
    (base : ℤ → Set α) (layer : α → ℤ) (time : α → ℕ)
    (hE : M.E = Set.univ) (e : α) (he : e ∈ E) :
    e ∈ M.closure (base (layer e) ∪
      {f | f ∈ layerGreedy M E base layer time ∧ layer f = layer e ∧ time f ≤ time e}) := by
  have aux : ∀ k, ∀ e ∈ E, time e = k →
      e ∈ M.closure (base (layer e) ∪
        {f | f ∈ layerGreedy M E base layer time ∧ layer f = layer e ∧ time f ≤ k}) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro e he htime
      by_cases hkeep : e ∈ layerGreedy M E base layer time
      · exact M.mem_closure_of_mem' (Or.inr ⟨hkeep, rfl, htime.le⟩) (by simp [hE])
      have hdep : e ∈ M.closure (base (layer e) ∪ layerPrior E layer time (layer e) (time e)) := by
        simpa only [layerGreedy, mem_filter, he, true_and, not_not] using hkeep
      apply M.closure_subset_closure_of_subset_closure ?_ hdep
      rintro f (hf | ⟨hf, hl, ht⟩)
      · exact M.mem_closure_of_mem' (Or.inl hf) (by simp [hE])
      · have hfk : time f < k := by simpa [htime] using ht
        have hrec := ih (time f) hfk f hf rfl
        apply M.closure_subset_closure ?_ hrec
        rintro g (hg | ⟨hg, hgl, hgt⟩)
        · exact Or.inl (by simpa [hl] using hg)
        · exact Or.inr ⟨hg, hgl.trans hl, hgt.trans hfk.le⟩
  exact aux (time e) e he rfl

lemma layerGreedy_spans (M : Matroid α) (E : Finset α)
    (base : ℤ → Set α) (layer : α → ℤ) (time : α → ℕ)
    (hE : M.E = Set.univ) (b : ℤ) :
    {e | e ∈ E ∧ layer e = b} ⊆
      M.closure (base b ∪ {e | e ∈ layerGreedy M E base layer time ∧ layer e = b}) := by
  rintro e ⟨he, hb⟩
  have h := layerGreedy_spans_prefix M E base layer time hE e he
  apply M.closure_subset_closure ?_ h
  rintro f (hf | ⟨hf, hfb, _⟩)
  · exact Or.inl (by simpa [hb] using hf)
  · exact Or.inr ⟨hf, hfb.trans hb⟩

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Constants
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

noncomputable section

theorem constants_positive : 0 < weightBase ∧ 0 < densityThreshold ∧
    0 < thinningRate ∧ 0 < exitThreshold ∧ 0 < retainedFraction := by
  norm_num [weightBase, densityThreshold, thinningRate, exitThreshold, retainedFraction]

theorem error_constant :
    ((2 : ℝ) ^ 23)⁻¹ + thinningRate * densityThreshold +
      (1 + thinningRate * densityThreshold) / (weightBase - 1) < ((2 : ℝ) ^ 21)⁻¹ := by
  norm_num [thinningRate, densityThreshold, weightBase]

end

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Algorithm_Feasible
attribute [-instance] _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set Finset

lemma assigned_some_of_eligible {n : ℕ} {K : Type*}
    (assign : Fin n → K → Option ℤ) (v : Fin n → K) (e : Fin n)
    (he : e ∈ assignedEligible assign v) :
    assign e (v e) = some (assignedLayer assign v e) := by
  classical
  cases h : assign e (v e) <;> simp_all [assignedEligible, assignedLayer]

namespace MainAlgorithm
variable {n : ℕ}

lemma assign_spec (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (seen : Fin n → Option ℤ) (e : Fin n) (w : Option ℤ) (b : ℤ) :
    assign M hE d seen e w = some b ↔
      ∃ i, w = some i ∧ eligible M hE d seen e i ∧ birth M hE d seen e i = b := by
  classical
  cases w with
  | none => simp [assign]
  | some i =>
    by_cases h : eligible M hE d seen e i <;> simp [assign, h]

end MainAlgorithm
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Groups
attribute [-instance] _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.MainAlgorithm

open Finset

variable {n : ℕ}

lemma groups_nodup (M : Matroid (Fin n)) (d : MainMasks n)
    (seen : Fin n → Option ℤ) : (groups M d seen).Nodup :=
  Finset.sort_nodup _ _

lemma groups_sorted (M : Matroid (Fin n)) (d : MainMasks n)
    (seen : Fin n → Option ℤ) : (groups M d seen).SortedLT :=
  Finset.sortedLT_sort _

lemma groups_get?_idxOf (M : Matroid (Fin n)) (d : MainMasks n)
    (seen : Fin n → Option ℤ) (i : ℤ) (hi : i ∈ groups M d seen) :
    (groups M d seen)[(groups M d seen).idxOf i]? = some i :=
  List.getElem?_idxOf hi

lemma groups_idxOf_lt_iff (M : Matroid (Fin n)) (d : MainMasks n)
    (seen : Fin n → Option ℤ) (i j : ℤ)
    (hi : i ∈ groups M d seen) (hj : j ∈ groups M d seen) :
    (groups M d seen).idxOf i < (groups M d seen).idxOf j ↔ i < j := by
  have hii := List.idxOf_lt_length_of_mem hi
  have hjj := List.idxOf_lt_length_of_mem hj
  have h := (groups_sorted M d seen).getElem_lt_getElem_iff (hi := hii) (hj := hjj)
  simpa using h.symm

lemma groups_earlier_key (M : Matroid (Fin n)) (d : MainMasks n)
    (seen : Fin n → Option ℤ) {j h : ℕ} {i : ℤ}
    (hh : (groups M d seen)[h]? = some i) (hjh : j < h) :
    ∃ k, (groups M d seen)[j]? = some k ∧ k < i := by
  obtain ⟨hh', hi⟩ := List.getElem?_eq_some_iff.mp hh
  have hj : j < (groups M d seen).length := hjh.trans hh'
  refine ⟨(groups M d seen)[j], List.getElem?_eq_getElem hj, ?_⟩
  rw [← hi]
  exact (groups_sorted M d seen).getElem_lt_getElem_of_lt hjh

end MatroidProphet.MainAlgorithm

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Residual_Generators
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open Set

variable {α : Type*} [Fintype α]

lemma monotone_set_timing
    {α : Type u_1} [Fintype α] (J : ℕ → Set α) (hJ : Monotone J) (N : ℕ) :
    ∃ τ : α → ℕ, ∀ j ≤ N, J j = {g | g ∈ J N ∧ τ g ≤ j} := by
  classical
  let hex := fun g (hg : g ∈ J N) => show ∃ j, g ∈ J j from ⟨N, hg⟩
  let τ := fun g => if hg : g ∈ J N then Nat.find (hex g hg) else 0
  refine ⟨τ, ?_⟩
  intro j hj
  ext g
  constructor
  · intro hg
    have hgN := hJ hj hg
    refine ⟨hgN, ?_⟩
    simpa [τ, hgN] using Nat.find_min' (hex g hgN) hg
  · rintro ⟨hgN, hτ⟩
    have hfind : Nat.find (hex g hgN) ≤ j := by simpa [τ, hgN] using hτ
    exact hJ hfind (Nat.find_spec (hex g hgN))

lemma nominalPath_timed_generators (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (hκ : 0 < κ) (D C : ℕ → Set α) (h : ℕ) :
    ∃ G : Set α, G ⊆ D h ∧ κ * G.ncard ≤ (D h).ncard ∧ ∃ τ : α → ℕ,
      (∀ g ∈ G, τ g ≤ pathHorizon h) ∧
      (∀ j ≤ pathHorizon h,
        M.closure (guardedPath M hE κ D C h (activation h + j) ∪
          {g | g ∈ G ∧ τ g ≤ j}) = nominalPath M hE κ D C h (activation h + j)) := by
  obtain ⟨G, hGD, hGcard, J, hJmono, hJG, hgen⟩ := nominalPath_generators M hE κ hκ D C h
  obtain ⟨τ, hτ⟩ := monotone_set_timing J hJmono (pathHorizon h)
  refine ⟨J (pathHorizon h), (hJG _ le_rfl).trans hGD, ?_, τ, ?_, ?_⟩
  · exact (Nat.mul_le_mul_left κ (Set.ncard_mono (hJG _ le_rfl))).trans hGcard
  · intro g hg
    exact ((Set.ext_iff.mp (hτ _ le_rfl) g).mp hg).2
  · intro j hj
    rw [← hτ j hj]
    exact hgen j hj

lemma nominalPath_all_time_generators (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (hκ : 0 < κ) (D C : ℕ → Set α) (h : ℕ) :
    ∃ G : Set α, G ⊆ D h ∧ κ * G.ncard ≤ (D h).ncard ∧ ∃ τ : α → ℕ,
      (∀ g ∈ G, τ g ≤ pathHorizon h) ∧ ∀ k : ℤ,
        nominalPath M hE κ D C h k =
          M.closure (guardedPath M hE κ D C h k ∪ timedGeneratorSet G τ (activation h) k) := by
  obtain ⟨G, hGD, hGcard, τ, hbound, hgen⟩ := nominalPath_timed_generators M hE κ hκ D C h
  refine ⟨G, hGD, hGcard, τ, hbound, ?_⟩
  intro k
  by_cases hka : k < activation h
  · have hearly : k < -3 * (h : ℤ) - 1 := by
      dsimp [activation] at hka
      omega
    have hempty : timedGeneratorSet G τ (activation h) k = ∅ := by
      ext g
      simp only [timedGeneratorSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _ htime
      omega
    rw [nominalPath_early M hE κ D C h hka, guardedPath_early M hE κ D C h hearly,
      hempty, union_empty, M.closure_closure]
  · by_cases hk0 : 0 ≤ k
    · rw [nominalPath_nonnegative M hE κ D C h hk0, guardedPath_nonnegative M hE κ D C h hk0]
      simp [M.closure_univ, hE]
    · let j := (k - activation h).toNat
      have hjcast : (j : ℤ) = k - activation h := Int.toNat_of_nonneg (by omega)
      have hj : j ≤ pathHorizon h := by
        have hhor := activation_add_horizon h
        omega
      have hkj : activation h + (j : ℤ) = k := by omega
      have hsets : {g | g ∈ G ∧ τ g ≤ j} = timedGeneratorSet G τ (activation h) k := by
        ext g
        simp only [timedGeneratorSet, Set.mem_ofPred_eq]
        constructor <;> rintro ⟨hg, ht⟩ <;> exact ⟨hg, by omega⟩
      have h := hgen j hj
      rw [hkj, hsets] at h
      exact h.symm

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_CommonBudget
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set Finset
variable {α : Type*} [Fintype α]

omit [Fintype α] in
lemma commonPathGenerators_cost (κ : ℕ) (C D J : ℕ → Set α) (h t : ℕ)
    (hJ : ∀ j, κ * (J j).ncard ≤ (D j).ncard) :
    κ * (commonPathGenerators C J h t).ncard ≤ κ * (C h).ncard +
      ∑ j ∈ range t, (κ * (C (h+1+j)).ncard + (D (h+1+j)).ncard) := by
  induction t with
  | zero => simp [commonPathGenerators]
  | succ t ih =>
    have hcard := ncard_union_le (commonPathGenerators C J h t ∪ C (h+1+t)) (J (h+1+t))
    have hcard' := ncard_union_le (commonPathGenerators C J h t) (C (h+1+t))
    have hc : (commonPathGenerators C J h (t+1)).ncard ≤
        (commonPathGenerators C J h t).ncard + (C (h+1+t)).ncard + (J (h+1+t)).ncard := by
      exact hcard.trans (Nat.add_le_add_right hcard' _)
    have hm := Nat.mul_le_mul_left κ hc
    simp only [Nat.mul_add] at hm
    rw [sum_range_succ]
    have hj := hJ (h+1+t)
    omega

lemma commonPathGenerators_spans (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C J : ℕ → Set α) (h t : ℕ)
    (hJ : ∀ j k, nominalPath M hE κ D C j k ⊆
      M.closure (guardedPath M hE κ D C j k ∪ J j)) (k : ℤ) :
    guardedPath M hE κ D C (h+1+t) k ⊆
      M.closure (nominalPath M hE κ D C h k ∪ commonPathGenerators C J h t) := by
  induction t with
  | zero =>
    simp only [Nat.add_zero, commonPathGenerators, guardedPath_succ]
    exact M.closure_subset_closure (union_subset_union_right _ inter_subset_left)
  | succ t ih =>
    have hidx : h+1+(t+1) = (h+1+t)+1 := by omega
    rw [hidx, guardedPath_succ]
    apply M.closure_subset_closure_of_subset_closure
    apply Set.union_subset
    · apply (hJ (h+1+t) k).trans
      apply M.closure_subset_closure_of_subset_closure
      apply Set.union_subset
      · exact ih.trans (M.closure_subset_closure (by
          intro e he
          rcases he with he | he
          · exact Or.inl he
          · exact Or.inr (Or.inl (Or.inl he))))
      · intro e he
        exact M.mem_closure_of_mem (Or.inr (Or.inr he)) (by simp [hE])
    · intro e he
      exact M.mem_closure_of_mem (Or.inr (Or.inl (Or.inr he.1))) (by simp [hE])

theorem exists_commonPathBudget (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D C : ℕ → Set α) (h t : ℕ) :
    ∃ Jtotal : Set α,
      κ * Jtotal.ncard ≤ κ * (C h).ncard +
        ∑ j ∈ range t, (κ * (C (h+1+j)).ncard + (D (h+1+j)).ncard) ∧
      ∀ k, guardedPath M hE κ D C (h+1+t) k ⊆
        M.closure (nominalPath M hE κ D C h k ∪ Jtotal) := by
  choose J hJD hcard τ htime hgen using
    (fun j => nominalPath_all_time_generators M hE κ hκ D C j)
  refine ⟨commonPathGenerators C J h t, commonPathGenerators_cost κ C D J h t hcard, ?_⟩
  intro k
  apply commonPathGenerators_spans M hE κ D C J h t _ k
  intro j l
  rw [hgen j l]
  apply M.closure_subset_closure
  exact union_subset_union_right _ (fun _ he => he.1)

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_LayerRank
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set Finset
variable {α : Type*} [Fintype α]

lemma natRank_le_ncard (M : Matroid α) (S : Set α) : natRank M S ≤ S.ncard := by
  have h := ENat.toNat_le_toNat (M.eRk_le_encard S) (Set.toFinite S).encard_lt_top.ne
  simpa only [natRank, Set.ncard_def] using h

lemma conditionalRank_mono_left (M : Matroid α) (P : Set α)
    {S T : Set α} (hST : S ⊆ T) : conditionalRank M S P ≤ conditionalRank M T P := by
  exact Nat.sub_le_sub_right (natRank_mono M (union_subset_union_left P hST)) _

lemma conditionalRank_spanned (M : Matroid α) (hE : M.E = Set.univ)
    (S P H : Set α) (hspan : S ⊆ M.closure (P ∪ H)) :
    conditionalRank M S P ≤ H.ncard := by
  have hP : P ⊆ M.closure (P ∪ H) :=
    subset_union_left.trans (M.subset_closure _ (by simp [hE]))
  have hr := natRank_mono M (union_subset hspan hP)
  rw [natRank_closure] at hr
  have ht : conditionalRank M S P ≤ conditionalRank M H P := by
    unfold conditionalRank
    rw [union_comm H P]
    exact Nat.sub_le_sub_right hr _
  exact ht.trans ((conditionalRank_le_rank M H P).trans (natRank_le_ncard M H))

theorem layerGreedy_rank_lower (M : Matroid α) (hE : M.E = Set.univ)
    (E : Finset α) (base : ℤ → Set α) (layer : α → ℤ) (time : α → ℕ)
    (b : ℤ) (S K : Set α) (high : α → Prop) [DecidablePred high]
    (hS : S \ base b ⊆ {e | e ∈ E ∧ layer e = b})
    (hK : ∀ e ∈ layerGreedy M E base layer time, layer e = b → ¬ high e → e ∈ K) :
    conditionalRank M S (base b ∪ K) ≤
      ((layerGreedy M E base layer time).filter (fun e => layer e = b ∧ high e)).card := by
  classical
  let H := (layerGreedy M E base layer time).filter (fun e => layer e = b ∧ high e)
  have hspan : S ⊆ M.closure ((base b ∪ K) ∪ (H : Set α)) := by
    intro e he
    by_cases heF : e ∈ base b
    · exact M.mem_closure_of_mem (Or.inl (Or.inl heF)) (by simp [hE])
    have hel := hS ⟨he, heF⟩
    have hs := layerGreedy_spans M E base layer time hE b hel
    apply M.closure_subset_closure ?_ hs
    rintro f (hf | ⟨hf, hb⟩)
    · exact Or.inl (Or.inl hf)
    · by_cases hh : high f
      · exact Or.inr (mem_filter.mpr ⟨hf, hb, hh⟩)
      · exact Or.inl (Or.inr (hK f hf hb hh))
  have hc := conditionalRank_spanned M hE S (base b ∪ K) (H : Set α) hspan
  simpa only [Set.ncard_coe_finset, H] using hc

theorem layerGreedy_sum_rank_lower [DecidableEq α]
    (M : Matroid α) (hE : M.E = Set.univ)
    (E : Finset α) (base : ℤ → Set α) (layer : α → ℤ) (time : α → ℕ)
    (points : Finset ℤ) (S K : ℤ → Set α) (high : α → Prop) [DecidablePred high]
    (hS : ∀ b ∈ points, S b \ base b ⊆ {e | e ∈ E ∧ layer e = b})
    (hK : ∀ b ∈ points, ∀ e ∈ layerGreedy M E base layer time,
      layer e = b → ¬ high e → e ∈ K b) :
    (∑ b ∈ points, conditionalRank M (S b) (base b ∪ K b)) ≤
      ((layerGreedy M E base layer time).filter high).card := by
  classical
  let A := layerGreedy M E base layer time
  calc
    _ ≤ ∑ b ∈ points, (A.filter (fun e => layer e = b ∧ high e)).card := by
      exact Finset.sum_le_sum fun b hb =>
        layerGreedy_rank_lower M hE E base layer time b (S b) (K b) high (hS b hb) (hK b hb)
    _ = ∑ b ∈ points, ((A.filter high).filter (fun e => layer e = b)).card := by
      apply Finset.sum_congr rfl
      intro b hb
      congr 1
      ext e
      simp only [Finset.mem_filter]
      tauto
    _ = ((A.filter high).filter (fun e => layer e ∈ points)).card :=
      Finset.sum_card_fiberwise_eq_card_filter (A.filter high) points layer
    _ ≤ (A.filter high).card := Finset.card_filter_le _ _

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Reverse_Paths
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set
variable {α : Type*} [Fintype α]

lemma reversePrefix_succ (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C S : ℕ → Set α) (k : ℤ) (h : ℕ) :
    reversePrefix M hE κ D C S k (h+1) =
      M.closure (reverseNominal M hE κ D C S k h ∪ (C h ∩ S h)) := rfl

lemma reversePrefix_agrees (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (k : ℤ) (h : ℕ) :
    reversePrefix M hE κ D C (fun j => nominalPath M hE κ D C j (k+1)) k h =
      guardedPath M hE κ D C h k := by
  induction h with
  | zero => rfl
  | succ h ih =>
    rw [reversePrefix, ih]
    rfl

lemma reverseNominal_agrees (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (k : ℤ) (h : ℕ) :
    reverseNominal M hE κ D C (fun j => nominalPath M hE κ D C j (k+1)) k h =
      nominalPath M hE κ D C h k := by
  rw [reverseNominal, reversePrefix_agrees]
  rfl

lemma reversePrefix_mono (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C C' S S' : ℕ → Set α) {k k' : ℤ} (hkk' : k ≤ k')
    (hC : ∀ j, C j ⊆ C' j) (hS : ∀ j, S j ⊆ S' j) (h : ℕ) :
    reversePrefix M hE κ D C S k h ⊆ reversePrefix M hE κ D C' S' k' h := by
  induction h with
  | zero => exact guardedPath_mono M hE κ D C 0 hkk'
  | succ h ih =>
    exact M.closure_subset_closure
      (union_subset_union (densityEnabled_mono M hE κ (D h) (activation h) hkk' ih)
        (inter_subset_inter (hC h) (hS h)))

lemma reverseNominal_mono (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C C' S S' : ℕ → Set α) {k k' : ℤ} (hkk' : k ≤ k')
    (hC : ∀ j, C j ⊆ C' j) (hS : ∀ j, S j ⊆ S' j) (h : ℕ) :
    reverseNominal M hE κ D C S k h ⊆ reverseNominal M hE κ D C' S' k' h :=
  densityEnabled_mono M hE κ (D h) (activation h) hkk'
    (reversePrefix_mono M hE κ D C C' S S' hkk' hC hS h)

lemma reversePrefix_congr_before (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C C' S S' : ℕ → Set α) (k : ℤ) (h : ℕ)
    (hC : ∀ j < h, C j = C' j) (hS : ∀ j < h, S j = S' j) :
    reversePrefix M hE κ D C S k h = reversePrefix M hE κ D C' S' k h := by
  induction h with
  | zero => rfl
  | succ h ih =>
    rw [reversePrefix, reversePrefix, ih (fun j hj => hC j (by omega))
      (fun j hj => hS j (by omega)), hC h (by omega), hS h (by omega)]

lemma reverseNominal_congr_before (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C C' S S' : ℕ → Set α) (k : ℤ) (h : ℕ)
    (hC : ∀ j < h, C j = C' j) (hS : ∀ j < h, S j = S' j) :
    reverseNominal M hE κ D C S k h = reverseNominal M hE κ D C' S' k h := by
  rw [reverseNominal, reverseNominal, reversePrefix_congr_before M hE κ D C C' S S' k h hC hS]

lemma reversePrefix_subset_succ (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C S : ℕ → Set α) (k : ℤ) (h : ℕ) :
    reversePrefix M hE κ D C S k h ⊆ reversePrefix M hE κ D C S k (h+1) :=
  (densityEnabled_extensive M hE κ (D h) (activation h) k _).trans
    (subset_union_left.trans (M.subset_closure _ (by simp [hE])))

omit [Fintype α] in
lemma union_inter_sdiff (N C S : Set α) : N ∪ (C ∩ (S \ N)) = N ∪ (C ∩ S) := by
  ext e
  change (e ∈ N ∨ (e ∈ C ∧ e ∈ S ∧ e ∉ N)) ↔ (e ∈ N ∨ (e ∈ C ∧ e ∈ S))
  tauto

lemma reversePrefix_departing_only (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C S : ℕ → Set α) (k : ℤ) (h : ℕ) :
    reversePrefix M hE κ D (departingGuards M hE κ D C S k) S k h =
      reversePrefix M hE κ D C S k h := by
  induction h with
  | zero => rfl
  | succ h ih =>
    rw [reversePrefix, reversePrefix, ih]
    change M.closure (reverseNominal M hE κ D C S k h ∪
        ((C h ∩ (S h \ reverseNominal M hE κ D C S k h)) ∩ S h)) = _
    have hi : (C h ∩ (S h \ reverseNominal M hE κ D C S k h)) ∩ S h =
        C h ∩ (S h \ reverseNominal M hE κ D C S k h) := inter_eq_self_of_subset_left (fun _ he => he.2.1)
    rw [hi, union_inter_sdiff]
    rfl

lemma reverseNominal_departing_only (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C S : ℕ → Set α) (k : ℤ) (h : ℕ) :
    reverseNominal M hE κ D (departingGuards M hE κ D C S k) S k h =
      reverseNominal M hE κ D C S k h := by
  rw [reverseNominal, reverseNominal, reversePrefix_departing_only]

lemma hybridPrefix_contains (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C T : ℕ → Set α) (b : ℤ) (h : ℕ) :
    guardedPath M hE κ D C h (b-2) ∪ lowerCompetition M hE κ D C T b h ⊆
      reversePrefix M hE κ D (hybridGuards M hE κ D C T b)
        (fun j => nominalPath M hE κ D C j b) (b-1) h := by
  induction h with
  | zero =>
    exact union_subset (guardedPath_mono M hE κ D C 0 (by omega)) (empty_subset _)
  | succ h ih =>
    let A := reversePrefix M hE κ D (hybridGuards M hE κ D C T b)
      (fun j => nominalPath M hE κ D C j b) (b-1) h
    let N := reverseNominal M hE κ D (hybridGuards M hE κ D C T b)
      (fun j => nominalPath M hE κ D C j b) (b-1) h
    have hFn : nominalPath M hE κ D C h (b-2) ⊆ N :=
      densityEnabled_mono M hE κ (D h) (activation h) (by omega)
        (subset_union_left.trans ih)
    have hguards : C h ∩ nominalPath M hE κ D C h (b-1) ⊆
        hybridGuards M hE κ D C T b h ∩ nominalPath M hE κ D C h b := by
      intro e he
      exact ⟨Or.inl he, nominalPath_mono M hE κ D C h (by omega) he.2⟩
    have hF : guardedPath M hE κ D C (h+1) (b-2) ⊆
        reversePrefix M hE κ D (hybridGuards M hE κ D C T b)
          (fun j => nominalPath M hE κ D C j b) (b-1) (h+1) := by
      rw [guardedPath_succ, reversePrefix_succ]
      have ht : b-2+1 = b-1 := by omega
      rw [ht]
      exact M.closure_subset_closure (union_subset_union hFn hguards)
    apply union_subset hF
    change lowerCompetition M hE κ D C T b h ∪ _ ⊆ _
    apply union_subset
    · exact (subset_union_right.trans ih).trans
        (reversePrefix_subset_succ M hE κ D (hybridGuards M hE κ D C T b)
          (fun j => nominalPath M hE κ D C j b) (b-1) h)
    · intro e he
      apply M.subset_closure _ (by simp [hE])
      exact Or.inr ⟨Or.inr he, he.2.1⟩

lemma hybrid_containment (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C T : ℕ → Set α) (b : ℤ) (h : ℕ) (henabled : activation h ≤ b-1) :
    densityExpansion M hE κ (D h)
      (guardedPath M hE κ D C h (b-2) ∪ lowerCompetition M hE κ D C T b h) ⊆
      reverseNominal M hE κ D (hybridGuards M hE κ D C T b)
        (fun j => nominalPath M hE κ D C j b) (b-1) h := by
  rw [reverseNominal, densityEnabled, ite_eq_left henabled]
  exact densityExpansion_mono M hE κ (D h) (hybridPrefix_contains M hE κ D C T b h)

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_PathRankCost
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set Finset
variable {α : Type*} [Fintype α]

lemma lowerCompetition_subset_guarded (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (b : ℤ) (h : ℕ) :
    lowerCompetition M hE κ D C T b h ⊆ guardedPath M hE κ D C h b := by
  induction h with
  | zero => exact Set.empty_subset _
  | succ h ih =>
    apply Set.union_subset
    · exact ih.trans ((guarded_subset_nominal M hE κ D C h b).trans
        (nominal_subset_guarded M hE κ D C h b))
    · exact fun _ he => nominal_subset_guarded M hE κ D C h b he.2.1

lemma unobservedBirthRegion_subset (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (G O : Set α) (h : ℕ) (b : ℤ) :
    unobservedBirthRegion M hE κ D C G O h b ⊆ nominalPath M hE κ D C h b := by
  unfold unobservedBirthRegion
  split_ifs
  · exact fun _ he => he.1.2.1
  · exact Set.empty_subset _

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Algorithm_LayerRank
attribute [-instance] _root_.OAI.MatroidProphet.Secretary.uniformArrivalLaw_probability _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set Finset
variable {α : Type*} [Fintype α]

lemma mem_nominal_difference_iff (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (e : α) (he : e ∉ M.closure ∅) (b : ℤ) :
    e ∈ nominalPath M hE κ D C h b \ nominalPath M hE κ D C h (b-1) ↔
      nominalBirth M hE κ D C h e = b := by
  simp only [Set.mem_sdiff, mem_nominal_iff_birth_le M hE κ D C h e he]
  omega

lemma lowerCompetition_member (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (b : ℤ) {j h : ℕ} (hj : j < h)
    {e : α} (he : e ∈ T j ∩ (nominalPath M hE κ D C j b \
      nominalPath M hE κ D C j (b-1))) :
    e ∈ lowerCompetition M hE κ D C T b h := by
  induction h with
  | zero => omega
  | succ h ih =>
    change e ∈ lowerCompetition M hE κ D C T b h ∪
      (T h ∩ (nominalPath M hE κ D C h b \ nominalPath M hE κ D C h (b-1)))
    by_cases heq : j = h
    · exact Or.inr (heq ▸ he)
    · exact Or.inl (ih (by omega))

namespace MainAlgorithm
variable {n : ℕ}

lemma candidate_nonloop (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (e : Fin n) (v : Option ℤ)
    (he : candidate M d w e v) : e ∉ M.closure ∅ :=
  fun hx => he.2.2 (M.closure_subset_closure (Set.empty_subset _) hx)

lemma groups_index_of_get (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) {h : ℕ} {i : ℤ} (hi : (groups M d w)[h]? = some i) :
    i ∈ groups M d w ∧ (groups M d w).idxOf i = h := by
  obtain ⟨hh, rfl⟩ := List.getElem?_eq_some_iff.mp hi
  exact ⟨List.getElem_mem hh, (groups_nodup M d w).idxOf_getElem h hh⟩

lemma groupBirthRegion_eligible (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (h : ℕ) (b : ℤ)
    (hb : b % 2 = (if d.odd then 1 else 0)) {e : Fin n}
    (he : e ∈ groupBirthRegion M hE d w h b ∩ (d.T : Set (Fin n)))
    (hf : e ∉ finalPath M hE d w (b-2)) :
    e ∈ assignedEligible (assign M hE d w) w ∧
      assignedLayer (assign M hE d w) w e = b := by
  classical
  have ht := he.2
  have hr := he.1
  unfold groupBirthRegion unobservedBirthRegion at hr
  split_ifs at hr with ha
  · obtain ⟨⟨⟨_, hc, hg⟩, hX⟩, hO⟩ := hr
    obtain ⟨i, hwi⟩ : ∃ i, w e = some i := Option.ne_none_iff_exists'.mp hc.1
    have hget : (groups M d w)[h]? = some i := hg.symm.trans hwi
    obtain ⟨hi, hidx⟩ := groups_index_of_get M d w hget
    have hbirth : birth M hE d w e i = b := by
      unfold birth
      rw [hidx]
      exact (mem_nominal_difference_iff M hE (2^100) _ _ h e
        (candidate_nonloop M d w e _ hc) b).mp hX
    have hel : eligible M hE d w e i := by
      refine ⟨hO, ?_, hi, ht, ?_, ?_, ?_⟩
      · rwa [← hwi]
      · rwa [hidx, hbirth]
      · rwa [hbirth]
      · rwa [hbirth]
    have has : assign M hE d w e (w e) = some b :=
      (assign_spec M hE d w e _ b).mpr ⟨i, hwi, hel, hbirth⟩
    constructor
    · simp [assignedEligible, has]
    · simp [assignedLayer, has]
  · exact False.elim hr

lemma selection_low_mem_competition (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (π : ArrivalOrder n)
    (h : ℕ) (b : ℤ) {e : Fin n} (he : e ∈ selection M hE d w π)
    (hb : assignedLayer (assign M hE d w) w e = b)
    (hlow : ¬ ∃ i, w e = some i ∧ h ≤ (groups M d w).idxOf i) :
    e ∈ competition M hE d w h b := by
  have hel := layerGreedy_subset M _ _ _ _ he
  obtain ⟨i, hwi, hi, hbi⟩ := (assign_spec M hE d w e _ _).mp
    (assigned_some_of_eligible (assign M hE d w) w e hel)
  have hidx : (groups M d w).idxOf i < h := by
    by_contra hn
    exact hlow ⟨i, hwi, by omega⟩
  apply lowerCompetition_member M hE (2^100) _ _ _ b hidx
  constructor
  · exact ⟨hi.2.2.2.1, by simpa only [hwi] using hi.2.1, hwi.trans (groups_get?_idxOf M d w i hi.2.2.1).symm⟩
  · apply (mem_nominal_difference_iff M hE (2^100) _ _ _ e
      (candidate_nonloop M d w e _ hi.2.1) b).mpr
    exact hbi.trans hb

theorem selection_cumulative_rank (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (π : ArrivalOrder n)
    (h : ℕ) (L : Finset ℤ) (hL : ∀ b ∈ L, b % 2 = (if d.odd then 1 else 0)) :
    (∑ b ∈ L, conditionalRank M
      (groupBirthRegion M hE d w h b ∩ (d.T : Set (Fin n)))
      (finalPath M hE d w (b-2) ∪ competition M hE d w h b)) ≤
      ((selection M hE d w π).filter (fun e =>
        ∃ i, w e = some i ∧ h ≤ (groups M d w).idxOf i)).card := by
  classical
  exact layerGreedy_sum_rank_lower M hE _ _ _ _ L _ _ _
    (fun b hb e he => groupBirthRegion_eligible M hE d w h b (hL b hb) he.1 he.2)
    (fun b _ e he hb hn => selection_low_mem_competition M hE d w π h b he hb hn)

end MainAlgorithm
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_ProductRestriction
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [DecidableEq α]

theorem bitsExpectation_restrict (q : α → ℝ) (W V : Finset α) (hV : V ⊆ W)
    (f : Finset α → ℝ)
    (hf : ∀ S S', (∀ e ∈ V, e ∈ S ↔ e ∈ S') → f S = f S') :
    bitsExpectation q W f = bitsExpectation q V f := by
  induction W using Finset.strongInductionOn with
  | _ W ih =>
    by_cases hW : W ⊆ V
    · rw [subset_antisymm hW hV]
    · obtain ⟨e, heW, heV⟩ := Finset.not_subset.mp hW
      have hVerase : V ⊆ W.erase e := by
        intro x hx
        exact mem_erase.mpr ⟨fun h => heV (h ▸ hx), hV hx⟩
      have heq : bitsExpectation q (W.erase e) (fun S => f (insert e S)) =
          bitsExpectation q (W.erase e) f := by
        apply bitsExpectation_congr
        intro S _
        apply hf
        intro x hx
        have hxe : x ≠ e := fun h => heV (h ▸ hx)
        simp [hxe]
      have hs := bitsExpectation_insert q (W.erase e) e (notMem_erase e W) f
      rw [insert_erase heW, heq, ih (W.erase e) (erase_ssubset heW) hVerase] at hs
      linarith

lemma bitsExpectation_sum {ι : Type*} (q : α → ℝ) (V : Finset α) (I : Finset ι)
    (f : ι → Finset α → ℝ) :
    bitsExpectation q V (fun S => ∑ e ∈ I, f e S) = ∑ e ∈ I, bitsExpectation q V (f e) := by
  simp only [bitsExpectation, mul_sum]
  rw [sum_comm]

lemma bitsExpectation_mem (q : α → ℝ) (V : Finset α) (e : α) (he : e ∈ V) :
    bitsExpectation q V (fun S => if e ∈ S then 1 else 0) = q e := by
  rw [bitsExpectation_restrict q V {e} (singleton_subset_iff.mpr he)
    (fun S => if e ∈ S then 1 else 0) (by
      intro S S' h
      simp only [h e (mem_singleton_self e)])]
  rw [show ({e} : Finset α) = insert e ∅ from rfl,
    bitsExpectation_insert q ∅ e (notMem_empty e)]
  simp [bitsExpectation_empty]

lemma bitsExpectation_card_inter (q : α → ℝ) (V K : Finset α) (hKV : K ⊆ V) :
    bitsExpectation q V (fun S => ((K ∩ S).card : ℝ)) = ∑ e ∈ K, q e := by
  have hsum (S : Finset α) : ((K ∩ S).card : ℝ) =
      ∑ e ∈ K, if e ∈ S then (1 : ℝ) else 0 := by
    simp
  simp_rw [hsum]
  rw [bitsExpectation_sum]
  exact sum_congr rfl (fun e he => bitsExpectation_mem q V e (hKV he))

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_ProductSplit
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

lemma bitsExpectation_disjoint_union (q : α → ℝ) (U V : Finset α) (hUV : Disjoint U V)
    (f : Finset α → ℝ) :
    bitsExpectation q (U ∪ V) f =
      bitsExpectation q U (fun S => bitsExpectation q V (fun T => f (S ∪ T))) := by
  induction U using Finset.induction_on generalizing f with
  | empty => simp only [empty_union, bitsExpectation_empty]
  | @insert e U he ih =>
    have heV : e ∉ V := fun hx => (Finset.disjoint_left.mp hUV (mem_insert_self e U) hx)
    have hU : Disjoint U V := hUV.mono_left (subset_insert e U)
    rw [insert_union, bitsExpectation_insert q (U ∪ V) e (by simp [he, heV]),
      bitsExpectation_insert q U e he, ih hU f, ih hU (fun S => f (insert e S))]
    simp only [insert_union]

lemma bitsExpectation_split (q : α → ℝ) (V U : Finset α) (hU : U ⊆ V)
    (f : Finset α → ℝ) :
    bitsExpectation q V f =
      bitsExpectation q (V \ U) (fun S => bitsExpectation q U (fun T => f (S ∪ T))) := by
  have heq : (V \ U) ∪ U = V := sdiff_union_of_subset hU
  rw [← bitsExpectation_disjoint_union q (V \ U) U sdiff_disjoint f, heq]

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Thinning
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set Finset
variable {α : Type*} [Fintype α]

lemma conditionalRank_union_chain (M : Matroid α) (A B P : Set α) :
    conditionalRank M (A ∪ B) P =
      conditionalRank M A P + conditionalRank M B (P ∪ A) := by
  have hA := conditionalRank_add_base M A P
  have hB := conditionalRank_add_base M B (P ∪ A)
  have hAB := conditionalRank_add_base M (A ∪ B) P
  have heq : B ∪ (P ∪ A) = (A ∪ B) ∪ P := by ext x; simp only [Set.mem_union]; tauto
  rw [heq] at hB
  rw [union_comm A P] at hA
  omega

lemma conditionalRank_subset_witness (M : Matroid α) (K P A : Set α)
    (hK : conditionalRank M K P = K.ncard) (hAK : A ⊆ K) :
    conditionalRank M A P = A.ncard := by
  have hu : A ∪ (K \ A) = K := by
    ext e
    constructor
    · rintro (he | he)
      · exact hAK he
      · exact he.1
    · intro he
      by_cases ha : e ∈ A
      · exact Or.inl ha
      · exact Or.inr ⟨he, ha⟩
  have hc := conditionalRank_union_chain M A (K \ A) P
  rw [hu, hK] at hc
  have hd := (conditionalRank_le_rank M (K \ A) (P ∪ A)).trans (natRank_le_ncard M (K \ A))
  have ha := (conditionalRank_le_rank M A P).trans (natRank_le_ncard M A)
  have hn := Set.ncard_sdiff_add_ncard_of_subset hAK
  omega

lemma exists_conditionalRank_witness (M : Matroid α) (hE : M.E = Set.univ) (S P : Set α) :
    ∃ K : Set α, K ⊆ S ∧ conditionalRank M K P = K.ncard ∧
      K.ncard = conditionalRank M S P := by
  obtain ⟨K, hK, hgen, hcard⟩ := exists_extension_generators M hE (M.closure P) S
    (M.closure (M.closure P ∪ S)) (Matroid.isFlat_closure (M := M) P) rfl
  have hrS : K.ncard + natRank M P = natRank M (S ∪ P) := by
    simpa only [natRank, M.eRk_closure_eq, M.eRk_union_closure_left_eq, union_comm P S] using hcard
  have hrK : natRank M (K ∪ P) = natRank M (S ∪ P) := by
    have hh := congrArg (natRank M) hgen
    simpa only [natRank, M.eRk_closure_eq, M.eRk_union_closure_left_eq, union_comm P K,
      union_comm P S] using hh
  refine ⟨K, fun _ he => (hK he).1, ?_, ?_⟩ <;> unfold conditionalRank <;> omega

theorem independent_thinning_rank [DecidableEq α] (M : Matroid α) (hE : M.E = Set.univ)
    (V S : Finset α) (hSV : S ⊆ V) (P : Set α) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * (conditionalRank M (S : Set α) P : ℝ) ≤
      bitsExpectation (fun _ => t) V (fun T => (conditionalRank M ((S ∩ T : Finset α) : Set α) P : ℝ)) := by
  classical
  obtain ⟨K, hKS, hKrank, hKcard⟩ := exists_conditionalRank_witness M hE (S : Set α) P
  let KF := K.toFinset
  have hKF : KF ⊆ V := fun e he => hSV (hKS (by simpa [KF] using he))
  have hpoint (T : Finset α) : ((KF ∩ T).card : ℝ) ≤
      (conditionalRank M ((S ∩ T : Finset α) : Set α) P : ℝ) := by
    have hw := conditionalRank_subset_witness M K P ((KF ∩ T : Finset α) : Set α) hKrank
      (by intro e he; exact (by simpa [KF] using (mem_inter.mp he).1))
    have hm := conditionalRank_mono_left M P
      (show ((KF ∩ T : Finset α) : Set α) ⊆ ((S ∩ T : Finset α) : Set α) from by
        intro e he
        rcases mem_inter.mp he with ⟨heK, heT⟩
        exact mem_inter.mpr ⟨hKS (by simpa [KF] using heK), heT⟩)
    rw [hw, Set.ncard_coe_finset] at hm
    exact_mod_cast hm
  have hm := bitsExpectation_mono (fun _ : α => t) (fun _ => ht0) (fun _ => ht1)
    V (fun T _ => hpoint T)
  rw [bitsExpectation_card_inter _ V KF hKF] at hm
  have hcardKF : KF.card = conditionalRank M (S : Set α) P := by
    change K.toFinset.card = _
    rw [← Set.ncard_eq_toFinset_card', hKcard]
  simpa only [sum_const, nsmul_eq_mul, hcardKF, mul_comm] using hm

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_ConditionalThinning
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set Finset
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem conditionally_independent_thinning_rank
    (M : Matroid α) (hE : M.E = Set.univ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (V G : Finset α) (hG : G ⊆ V) (S : Set α) (hS : S ⊆ (G : Set α))
    (P : Finset α → Set α)
    (hP : ∀ A B : Finset α, B ⊆ G → P (A ∪ B) = P A) :
    t * bitsExpectation (fun _ => t) V (fun T => (conditionalRank M S (P T) : ℝ)) ≤
      bitsExpectation (fun _ => t) V
        (fun T => (conditionalRank M (S ∩ (T : Set α)) (P T) : ℝ)) := by
  classical
  have heq : bitsExpectation (fun _ => t) V (fun T => (conditionalRank M S (P T) : ℝ)) =
      bitsExpectation (fun _ => t) (V \ G) (fun A => (conditionalRank M S (P A) : ℝ)) := by
    rw [bitsExpectation_split (fun _ => t) V G hG]
    apply bitsExpectation_congr
    intro A hA
    calc
      _ = bitsExpectation (fun _ => t) G (fun _ => (conditionalRank M S (P A) : ℝ)) := by
        apply bitsExpectation_congr
        intro B hB
        rw [hP A B hB]
      _ = _ := bitsExpectation_const _ _ _
  rw [heq, ← bitsExpectation_mul_left, bitsExpectation_split (fun _ => t) V G hG]
  apply bitsExpectation_mono _ (fun _ => ht0) (fun _ => ht1)
  intro A hA
  have hdis : S ∩ (A : Set α) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro e ⟨heS, heA⟩
    exact (Finset.mem_sdiff.mp (hA heA)).2 (hS heS)
  have hb := independent_thinning_rank M hE G S.toFinset
    (fun e he => hS (by simpa only [Set.mem_toFinset] using he)) (P A) t ht0 ht1
  calc
    _ ≤ bitsExpectation (fun _ => t) G
        (fun B => (conditionalRank M (S ∩ (B : Set α)) (P A) : ℝ)) := by simpa only [Finset.coe_inter, Set.coe_toFinset] using hb
    _ = _ := by
      apply bitsExpectation_congr
      intro B hB
      rw [hP A B hB]
      have hset : S ∩ ((A ∪ B : Finset α) : Set α) = S ∩ (B : Set α) := by
        rw [Finset.coe_union, Set.inter_union_distrib_left, hdis, Set.empty_union]
      rw [hset]

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Pivots_GreedyScan
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
namespace Pivots

open Set Finset

variable {α β : Type*} [Fintype β] [DecidableEq β]

private lemma indep_image_of_notMem_prior
    {α : Type u_1} {β : Type u_2} [Fintype β] [DecidableEq β] (M : Matroid α) (label : β → α)
    (time : β → ℕ) (htime : Function.Injective time) (s : Finset β)
    (hground : ∀ o ∈ s, label o ∈ M.E)
    (hprior : ∀ o ∈ s, label o ∉ M.closure (label '' {p | p ∈ s ∧ time p < time o})) :
    M.Indep (label '' (s : Set β)) := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hs : s = ∅
    · simp [hs]
    obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image s time (Finset.nonempty_iff_ne_empty.mpr hs)
    have hI := ih (s.erase p) (Finset.erase_ssubset hp)
      (fun o ho => hground o (Finset.mem_of_mem_erase ho)) (by
        intro o ho hmem
        apply hprior o (Finset.mem_of_mem_erase ho)
        apply M.closure_subset_closure ?_ hmem
        rintro _ ⟨q, ⟨hq, hqt⟩, rfl⟩
        exact ⟨q, ⟨Finset.mem_of_mem_erase hq, hqt⟩, rfl⟩)
    have hnot : label p ∉ M.closure (label '' (s.erase p : Set β)) := by
      intro hmem
      apply hprior p hp
      apply M.closure_subset_closure ?_ hmem
      rintro _ ⟨q, hq, rfl⟩
      refine ⟨q, ⟨Finset.mem_of_mem_erase hq, ?_⟩, rfl⟩
      apply lt_of_le_of_ne (hmax q (Finset.mem_of_mem_erase hq))
      intro htimeeq
      exact (Finset.ne_of_mem_erase hq) (htime htimeeq)
    have hins := hI.insert_indep_iff.mpr (Or.inl ⟨hground p hp, hnot⟩)
    have hset : insert (label p) (label '' (s.erase p : Set β)) = label '' (s : Set β) := by
      rw [← Set.image_insert_eq, ← Finset.coe_insert, Finset.insert_erase hp]
    rwa [hset] at hins

lemma keptOccurrences_indep (M : Matroid α) (label : β → α) (time : β → ℕ)
    (hground : ∀ o, label o ∈ M.E) (htime : Function.Injective time) :
    M.Indep (label '' (keptOccurrences M label time : Set β)) := by
  classical
  apply indep_image_of_notMem_prior M label time htime
  · intro o _
    exact hground o
  · intro o ho hmem
    have hn := (Finset.mem_filter.mp ho).2
    apply hn
    apply M.closure_subset_closure ?_ hmem
    rintro _ ⟨p, ⟨_, hpt⟩, rfl⟩
    exact ⟨p, hpt, rfl⟩

end Pivots
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_RankCost
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set Finset

lemma sum_spaced_potential_drop (p : ℤ → ℕ) (hp : Antitone p)
    (L : Finset ℤ) (lo hi : ℤ) (hlohi : lo ≤ hi)
    (hlo : ∀ b ∈ L, lo + 2 ≤ b) (hhi : ∀ b ∈ L, b ≤ hi)
    (hgap : ∀ b ∈ L, ∀ c ∈ L, b < c → b + 2 ≤ c) :
    (∑ b ∈ L, (p (b-2) - p b)) + p hi ≤ p lo := by
  induction L using Finset.induction_on_max generalizing lo hi with
  | empty => simpa using hp hlohi
  | @insert a L hmax ih =>
    have ha : a ∉ L := fun hm => (lt_irrefl a) (hmax a hm)
    have hla : lo ≤ a-2 := by have := hlo a (mem_insert_self a L); omega
    have harest : ∀ b ∈ L, b ≤ a-2 := by
      intro b hb
      have hb' := hmax b hb
      have hg := hgap b (mem_insert_of_mem hb) a (mem_insert_self a L) hb'
      omega
    have hrec := ih lo (a-2) hla
      (fun b hb => hlo b (mem_insert_of_mem hb)) harest
      (fun b hb c hc hbc => hgap b (mem_insert_of_mem hb) c (mem_insert_of_mem hc) hbc)
    have hahi := hhi a (mem_insert_self a L)
    have hphi := hp hahi
    have hpaa := hp (show a-2 ≤ a by omega)
    rw [sum_insert ha]
    omega

variable {α : Type*} [Fintype α]

theorem rankCost_spaced (M : Matroid α) (J : Set α) (L : Finset ℤ)
    (lo hi : ℤ) (hlohi : lo ≤ hi)
    (hlo : ∀ b ∈ L, lo+2 ≤ b) (hhi : ∀ b ∈ L, b ≤ hi)
    (hgap : ∀ b ∈ L, ∀ c ∈ L, b < c → b+2 ≤ c)
    (X A B S : ℤ → Set α) (hX : Monotone X)
    (hXA : ∀ b ∈ L, X (b-2) ⊆ A b)
    (hAB : ∀ b ∈ L, A b ⊆ B b)
    (hB : ∀ b ∈ L, B b ⊆ M.closure (A b ∪ J))
    (hY : ∀ b ∈ L, A b ∪ S b ⊆ X b) :
    (∑ b ∈ L, conditionalRank M (S b) (A b)) ≤
      (∑ b ∈ L, conditionalRank M (S b) (B b)) + natRank M J := by
  have hp : Antitone (fun b => conditionalRank M J (X b)) :=
    fun _ _ hab => conditionalRank_antitone M J (hX hab)
  have hd := sum_spaced_potential_drop _ hp L lo hi hlohi hlo hhi hgap
  have hs : (∑ b ∈ L, conditionalRank M (S b) (A b)) ≤
      ∑ b ∈ L, (conditionalRank M (S b) (B b) +
        (conditionalRank M J (X (b-2)) - conditionalRank M J (X b))) := by
    apply sum_le_sum
    intro b hb
    have hc := rankCost_step M J (S b) (A b) (B b) (X (b-2)) (X b)
      (hXA b hb) (hAB b hb) (hB b hb) (hY b hb)
    have hm := conditionalRank_antitone M (S b) (hAB b hb)
    omega
  rw [sum_add_distrib] at hs
  have hb := conditionalRank_le_rank M J (X lo)
  omega

theorem actual_path_rank_cost_finset (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D C T : ℕ → Set α) (h later : ℕ)
    (L : Finset ℤ) (lo hi : ℤ) (hlohi : lo ≤ hi)
    (hlo : ∀ b ∈ L, lo+2 ≤ b) (hhi : ∀ b ∈ L, b ≤ hi)
    (hgap : ∀ b ∈ L, ∀ c ∈ L, b < c → b+2 ≤ c)
    (S : ℤ → Set α) (hS : ∀ b, S b ⊆ nominalPath M hE κ D C h b) :
    κ * (∑ b ∈ L, conditionalRank M (S b)
      (nominalPath M hE κ D C h (b-2) ∪ lowerCompetition M hE κ D C T b h)) ≤
    κ * (∑ b ∈ L, conditionalRank M (S b)
      (guardedPath M hE κ D C (h+1+later) (b-2) ∪ lowerCompetition M hE κ D C T b h)) +
      κ * (C h).ncard +
        ∑ j ∈ range later, (κ * (C (h+1+j)).ncard + (D (h+1+j)).ncard) := by
  obtain ⟨J, hJcost, hJ⟩ := exists_commonPathBudget M hE κ hκ D C h later
  have hXfinal (b : ℤ) : nominalPath M hE κ D C h b ⊆
      guardedPath M hE κ D C (h+1+later) b := by
    apply (nominal_subset_guarded M hE κ D C h b).trans
    have hm : Monotone (fun j => guardedPath M hE κ D C j b) :=
      monotone_nat_of_le_succ (fun j => (guarded_subset_nominal M hE κ D C j b).trans
        (nominal_subset_guarded M hE κ D C j b))
    exact hm (by omega)
  have hr := rankCost_spaced M J L lo hi hlohi hlo hhi hgap
    (nominalPath M hE κ D C h)
    (fun b => nominalPath M hE κ D C h (b-2) ∪ lowerCompetition M hE κ D C T b h)
    (fun b => guardedPath M hE κ D C (h+1+later) (b-2) ∪ lowerCompetition M hE κ D C T b h)
    S (nominalPath_mono M hE κ D C h)
    (fun _ _ => Set.subset_union_left)
    (fun b _ => Set.union_subset_union_left _ (hXfinal _))
    (by
      intro b hb
      apply Set.union_subset
      · exact (hJ _).trans (M.closure_subset_closure (by
          intro e he
          rcases he with he | he
          · exact Or.inl (Or.inl he)
          · exact Or.inr he))
      · intro e he
        exact M.mem_closure_of_mem (Or.inl (Or.inr he)) (by simp [hE]))
    (by
      intro b hb
      apply Set.union_subset
      · apply Set.union_subset
        · exact nominalPath_mono M hE κ D C h (by omega)
        · exact (lowerCompetition_subset_guarded M hE κ D C T _ h).trans
            (guarded_subset_nominal M hE κ D C h _)
      · exact hS _)
  have hmul := Nat.mul_le_mul_left κ hr
  rw [Nat.mul_add] at hmul
  have hcard := natRank_le_ncard M J
  have hbound := (Nat.mul_le_mul_left κ hcard).trans hJcost
  omega

lemma mem_parityPoints (a : ℤ) (ε : Fin 2) (b : ℤ) :
    b ∈ parityPoints a ε ↔ a-2 ≤ b ∧ b ≤ 1 ∧ b % 2 = (ε.val : ℤ) := by
  classical
  constructor
  · intro hb
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hb
    exact ⟨c.val.property.1, c.val.property.2, c.property⟩
  · rintro ⟨hl, hr, hm⟩
    exact Finset.mem_image.mpr ⟨⟨⟨b, ⟨hl, hr⟩⟩, hm⟩, Finset.mem_univ _, rfl⟩

lemma sum_parityPoints {β : Type*} [AddCommMonoid β] (a : ℤ) (ε : Fin 2) (f : ℤ → β) :
    (∑ b ∈ parityPoints a ε, f b) = ∑ b : Pivots.ParityWindow a ε, f b.val.val := by
  classical
  apply Finset.sum_image
  intro x _ y _ hxy
  exact Subtype.ext (Subtype.ext hxy)

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Residual_Constants
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

theorem residual_error_constant : densityThreshold⁻¹ + 2 * residualDelta ≤ ((2 : ℝ)^23)⁻¹ := by
  norm_num [densityThreshold, residualDelta]

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Residual_Probability
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open Finset

variable {α : Type*} [DecidableEq α]

lemma bitsExpectation_mul_const (q : α → ℝ) (V : Finset α) (c : ℝ) (f : Finset α → ℝ) :
    bitsExpectation q V (fun S => c * f S) = c * bitsExpectation q V f := by
  simp only [bitsExpectation, mul_sum]
  apply sum_congr rfl
  intro S hS
  ring

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Residual_Transfer
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [DecidableEq α]

lemma tripleMaskExpectation_mono (p q r : α → ℝ)
    (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (hr0 : ∀ e, 0 ≤ r e) (hr1 : ∀ e, r e ≤ 1)
    (V : Finset α) {f g : Finset α → Finset α → Finset α → ℝ}
    (h : ∀ D ⊆ V, ∀ C ⊆ V, ∀ T ⊆ V, f D C T ≤ g D C T) :
    tripleMaskExpectation p q r V f ≤ tripleMaskExpectation p q r V g := by
  apply bitsExpectation_mono p hp0 hp1
  intro D hD
  apply bitsExpectation_mono q hq0 hq1
  intro C hC
  exact bitsExpectation_mono r hr0 hr1 V (fun T hT => h D hD C hC T hT)

lemma tripleMaskExpectation_add (p q r : α → ℝ) (V : Finset α)
    (f g : Finset α → Finset α → Finset α → ℝ) :
    tripleMaskExpectation p q r V (fun D C T => f D C T + g D C T) =
      tripleMaskExpectation p q r V f + tripleMaskExpectation p q r V g := by
  simp only [tripleMaskExpectation, bitsExpectation_add]

lemma tripleMaskExpectation_mul (p q r : α → ℝ) (V : Finset α) (c : ℝ)
    (f : Finset α → Finset α → Finset α → ℝ) :
    tripleMaskExpectation p q r V (fun D C T => c * f D C T) =
      c * tripleMaskExpectation p q r V f := by
  simp only [tripleMaskExpectation, bitsExpectation_mul_const]

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Residual_Statistics
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set Finset Pivots
variable {α : Type*} [Fintype α]

lemma boolParity_val (parity : Bool) : ((boolParity parity).val : ℤ) = (if parity then 1 else 0) := by
  cases parity <;> rfl

lemma nominalLayerSet_subset (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (U : Set α) (ε : Fin 2)
    (b : ParityWindow (activation h) ε) : nominalLayerSet M hE κ D C h U ε b ⊆ U :=
  fun _ he => he.1

lemma nominalLayerSet_disjoint (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (U : Set α) (ε : Fin 2) :
    Pairwise (fun b c => Disjoint (nominalLayerSet M hE κ D C h U ε b)
      (nominalLayerSet M hE κ D C h U ε c)) := by
  intro b c hbc
  apply Set.disjoint_left.mpr
  intro e hb hc
  have hval : b.val.val ≠ c.val.val := by
    intro heq
    exact hbc (Subtype.ext (Subtype.ext heq))
  rcases lt_or_gt_of_ne hval with hlt | hlt
  · exact hc.2.2.2.2 (nominalPath_mono M hE κ D C h (by omega) hb.2.2.2.1)
  · exact hb.2.2.2.2 (nominalPath_mono M hE κ D C h (by omega) hc.2.2.2.1)

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_PathStatistics
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set Finset Pivots
variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
lemma lowerCompetition_congr_test_before (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T T' : ℕ → Set α) (b : ℤ) (h : ℕ)
    (hT : ∀ j < h, T j = T' j) :
    lowerCompetition M hE κ D C T b h = lowerCompetition M hE κ D C T' b h := by
  induction h with
  | zero => rfl
  | succ h ih =>
    simp only [lowerCompetition]
    rw [ih (fun j hj => hT j (by omega)), hT h (by omega)]

lemma lowerCompetition_ignore_focal (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (b : ℤ) (h : ℕ)
    (A B : Finset α) (hB : B ⊆ G h) :
    lowerCompetition M hE κ D C (fun j => ((A ∪ B : Finset α) : Set α) ∩ (G j : Set α)) b h =
      lowerCompetition M hE κ D C (fun j => (A : Set α) ∩ (G j : Set α)) b h := by
  apply lowerCompetition_congr_test_before
  intro j hj
  ext e
  have hd := Finset.disjoint_left.mp (hG (show h ≠ j by omega))
  simp only [Finset.coe_union, Set.mem_inter_iff, Set.mem_union, Finset.mem_coe]
  constructor
  · rintro ⟨ha | hb, hg⟩
    · exact ⟨ha, hg⟩
    · exact False.elim (hd (hB hb) hg)
  · rintro ⟨ha, hg⟩
    exact ⟨Or.inl ha, hg⟩

omit [DecidableEq α] in
lemma unobservedBirthRegion_eq_nominalLayer (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (U O : Set α) (ε : Fin 2)
    (b : ParityWindow (activation h) ε) :
    unobservedBirthRegion M hE κ D C U O h b.val.val =
      nominalLayerSet M hE κ D C h U ε b \ O := by
  classical
  ext e
  unfold unobservedBirthRegion nominalLayerSet
  by_cases ha : activation h+2 ≤ b.val.val
  · rw [ite_eq_left ha]
    constructor
    · rintro ⟨⟨hu, hx, hn⟩, ho⟩
      have hb : b.val.val ≤ 0 := by
        by_contra hb
        have heq := nominalPath_nonnegative M hE κ D C h (show 0 ≤ b.val.val-1 by omega)
        rw [heq] at hn
        exact hn (Set.mem_univ e)
      exact ⟨⟨hu, ha, hb, hx, hn⟩, ho⟩
    · rintro ⟨⟨hu, _, _, hx, hn⟩, ho⟩
      exact ⟨⟨hu, hx, hn⟩, ho⟩
  · rw [ite_eq_right ha]
    simp only [Set.mem_empty_iff_false, Set.mem_sdiff, Set.mem_ofPred_eq, false_iff,
      not_and]
    intro he
    exact (ha he.2.1).elim

theorem testRankStatistic_le_final_cost
    {α : Type u_1} [Fintype α] [DecidableEq α] (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D C T : ℕ → Set α) (h later : ℕ)
    (U O test : Set α) (ε : Fin 2) :
    κ * testRankStatistic M hE κ D C T h U O test ε ≤
      κ * finalRankStatistic M hE κ D C T h (h+1+later) U O test ε +
        κ * (C h).ncard +
          ∑ j ∈ range later, (κ * (C (h+1+j)).ncard + (D (h+1+j)).ncard) := by
  let S : ℤ → Set α := fun b => unobservedBirthRegion M hE κ D C U O h b ∩ test
  have hc := actual_path_rank_cost_finset M hE κ hκ D C T h later
    (parityPoints (activation h) ε) (activation h-4) 1
    (by dsimp [activation]; omega)
    (by intro b hb; have := (mem_parityPoints _ _ _).mp hb; omega)
    (by intro b hb; exact ((mem_parityPoints _ _ _).mp hb).2.1)
    (by
      intro b hb c hc hbc
      have hbm := ((mem_parityPoints _ _ _).mp hb).2.2
      have hcm := ((mem_parityPoints _ _ _).mp hc).2.2
      omega)
    S (fun b e he => unobservedBirthRegion_subset M hE κ D C U O h b he.1)
  rw [sum_parityPoints, sum_parityPoints] at hc
  have hS (b : ParityWindow (activation h) ε) : S b.val.val =
      (nominalLayerSet M hE κ D C h U ε b \ O) ∩ test := by
    dsimp [S]
    rw [unobservedBirthRegion_eq_nominalLayer M hE κ D C h U O ε b]
  simp_rw [hS] at hc
  exact hc

theorem thinning_finalRankStatistic (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (h final : ℕ) (O : Set α) (ε : Fin 2) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * bitsExpectation (fun _ : α => t) univ (fun T =>
      (finalRankStatistic M hE κ D C (fun j => (T : Set α) ∩ (G j : Set α)) h final
        (G h) O Set.univ ε : ℝ)) ≤
    bitsExpectation (fun _ : α => t) univ (fun T =>
      (finalRankStatistic M hE κ D C (fun j => (T : Set α) ∩ (G j : Set α)) h final
        (G h) O (T : Set α) ε : ℝ)) := by
  simp only [finalRankStatistic, Set.inter_univ, Nat.cast_sum, bitsExpectation_sum, mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  apply conditionally_independent_thinning_rank M hE t ht0 ht1 univ (G h) (subset_univ _)
  · exact fun e he => (nominalLayerSet_subset M hE κ D C h (G h) ε b he.1)
  · intro A B hB
    rw [lowerCompetition_ignore_focal M hE κ D C G hG b.val.val h A B hB]

theorem expected_nominal_to_final (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D C : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (h later : ℕ) (O : Set α) (ε : Fin 2) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (κ:ℝ) * t * bitsExpectation (fun _ : α => t) univ (fun T =>
      (nominalRankStatistic M hE κ D C (fun j => (T : Set α) ∩ (G j : Set α)) h (G h) O ε : ℝ)) ≤
    (κ:ℝ) * bitsExpectation (fun _ : α => t) univ (fun T =>
      (finalRankStatistic M hE κ D C (fun j => (T : Set α) ∩ (G j : Set α)) h
        (h+1+later) (G h) O (T : Set α) ε : ℝ)) +
      t * (κ * (C h).ncard + ∑ j ∈ range later,
        (κ * (C (h+1+j)).ncard + (D (h+1+j)).ncard) : ℕ) := by
  have ht := thinning_finalRankStatistic M hE κ D C G hG h (h+1+later) O ε t ht0 ht1
  have hp (T : Finset α) :
      (κ:ℝ) * (nominalRankStatistic M hE κ D C (fun j => (T : Set α) ∩ (G j : Set α))
        h (G h) O ε : ℝ) ≤
      (κ:ℝ) * (finalRankStatistic M hE κ D C (fun j => (T : Set α) ∩ (G j : Set α))
        h (h+1+later) (G h) O Set.univ ε : ℝ) +
        (κ * (C h).ncard + ∑ j ∈ range later,
          (κ * (C (h+1+j)).ncard + (D (h+1+j)).ncard) : ℕ) := by
    have hn := testRankStatistic_le_final_cost M hE κ hκ D C
      (fun j => (T : Set α) ∩ (G j : Set α)) h later (G h) O Set.univ ε
    have htest : testRankStatistic M hE κ D C (fun j => (T : Set α) ∩ (G j : Set α))
        h (G h) O Set.univ ε = nominalRankStatistic M hE κ D C
        (fun j => (T : Set α) ∩ (G j : Set α)) h (G h) O ε := by
      simp only [testRankStatistic, nominalRankStatistic, Set.inter_univ]
    rw [htest, Nat.add_assoc] at hn
    exact_mod_cast hn
  have hm := bitsExpectation_mono (fun _ : α => t) (fun _ => ht0) (fun _ => ht1)
    univ (fun T _ => hp T)
  simp only [bitsExpectation_add, bitsExpectation_mul_left, bitsExpectation_const] at hm
  have hs := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg κ : (0:ℝ) ≤ κ)
  have hc := mul_le_mul_of_nonneg_left hm ht0
  nlinarith

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Algorithm_Statistics
attribute [-instance] _root_.OAI.MatroidProphet.Secretary.uniformArrivalLaw_probability _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.MainAlgorithm
open Set Finset Pivots
variable {n : ℕ}

lemma pathGroups_coe (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (h : ℕ) :
    (pathGroups M d w h : Set (Fin n)) = groupMask M d w univ h := by
  classical
  exact Set.coe_toFinset _

lemma groupMask_eq_inter (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (mask : Finset (Fin n)) (h : ℕ) :
    groupMask M d w mask h = (mask : Set (Fin n)) ∩ (pathGroups M d w h : Set (Fin n)) := by
  classical
  rw [pathGroups_coe]
  ext e
  simp [groupMask]

lemma pathGroups_disjoint (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) : Pairwise (fun i j => Disjoint (pathGroups M d w i) (pathGroups M d w j)) := by
  classical
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro e hei hej
  have heI : e ∈ groupMask M d w univ i := by simpa only [pathGroups, Set.mem_toFinset] using hei
  have heJ : e ∈ groupMask M d w univ j := by simpa only [pathGroups, Set.mem_toFinset] using hej
  obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp heI.2.1.1
  have hi := (groups_index_of_get M d w (heI.2.2.symm.trans hk)).2
  have hj := (groups_index_of_get M d w (heJ.2.2.symm.trans hk)).2
  exact hij (hi.symm.trans hj)

theorem listedLambda_le_count (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (π : ArrivalOrder n) (h : ℕ) :
    listedLambda M hE d w h ≤
      ((selection M hE d w π).filter (fun e =>
        ∃ i, w e = some i ∧ h ≤ (groups M d w).idxOf i)).card := by
  classical
  have hc := selection_cumulative_rank M hE d w π h
    (parityPoints (activation h) (boolParity d.odd)) (by
      intro b hb
      have hm := ((mem_parityPoints _ _ _).mp hb).2.2
      rwa [boolParity_val] at hm)
  rw [sum_parityPoints] at hc
  have hreg (b : ParityWindow (activation h) (boolParity d.odd)) :
      groupBirthRegion M hE d w h b.val.val =
        nominalLayerSet M hE (2^100) (groupMask M d w d.D) (groupMask M d w d.C)
          h (groupMask M d w univ h) (boolParity d.odd) b \
          ((d.H ∪ d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) :=
    unobservedBirthRegion_eq_nominalLayer M hE (2^100) _ _ h _ _ _ b
  simp_rw [hreg] at hc
  exact hc

theorem trueLambda_le_count (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (π : ArrivalOrder n) (i : ℤ) :
    trueLambda M hE d w i ≤
      ((selection M hE d w π).filter (fun e => ∃ j, w e = some j ∧ i ≤ j)).card := by
  classical
  unfold trueLambda
  split_ifs with hi
  · apply (listedLambda_le_count M hE d w π _).trans
    apply Finset.card_le_card
    intro e he
    obtain ⟨hea, j, hwj, hij⟩ := Finset.mem_filter.mp he
    refine Finset.mem_filter.mpr ⟨hea, j, hwj, ?_⟩
    have hel := layerGreedy_subset M _ _ _ _ hea
    obtain ⟨k, hwk, hek, _⟩ := (assign_spec M hE d w e _ _).mp
      (assigned_some_of_eligible (assign M hE d w) w e hel)
    have hjk : j = k := Option.some.inj (hwj.symm.trans hwk)
    have hj : j ∈ groups M d w := hjk ▸ hek.2.2.1
    by_contra hn
    have hlt := (groups_idxOf_lt_iff M d w j i hj hi).mpr (by omega)
    omega
  · exact Nat.zero_le _

end MatroidProphet.MainAlgorithm

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Algorithm_Expectation
attribute [-instance] _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.MainAlgorithm
open Set Finset
variable {n : ℕ}

lemma groupMask_function_eq_inter (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (mask : Finset (Fin n)) :
    groupMask M d w mask = fun j => (mask : Set (Fin n)) ∩ (pathGroups M d w j : Set (Fin n)) := by
  funext j
  exact groupMask_eq_inter M d w mask j

lemma listedZ_update_T (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (h : ℕ) (T : Finset (Fin n)) :
    listedZ M hE {d with T := T} w h =
      nominalRankStatistic M hE (2^100) (groupMask M d w d.D) (groupMask M d w d.C)
        (fun j => (T : Set (Fin n)) ∩ (pathGroups M d w j : Set (Fin n))) h (pathGroups M d w h)
        ((d.H ∪ d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) (boolParity d.odd) := by
  unfold listedZ
  change nominalRankStatistic M hE (2^100) (groupMask M d w d.D) (groupMask M d w d.C)
    (groupMask M d w T) h (groupMask M d w univ h)
      ((d.H ∪ d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) (boolParity d.odd) = _
  rw [groupMask_function_eq_inter M d w T, ← pathGroups_coe]

lemma listedLambda_update_T (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (h : ℕ) (T : Finset (Fin n)) :
    listedLambda M hE {d with T := T} w h =
      finalRankStatistic M hE (2^100) (groupMask M d w d.D) (groupMask M d w d.C)
        (fun j => (T : Set (Fin n)) ∩ (pathGroups M d w j : Set (Fin n))) h (groups M d w).length
        (pathGroups M d w h) ((d.H ∪ d.D ∪ d.C : Finset (Fin n)) : Set (Fin n))
        (T : Set (Fin n)) (boolParity d.odd) := by
  unfold listedLambda
  change finalRankStatistic M hE (2^100) (groupMask M d w d.D) (groupMask M d w d.C)
    (groupMask M d w T) h (groups M d w).length (groupMask M d w univ h)
      ((d.H ∪ d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) (T : Set (Fin n)) (boolParity d.odd) = _
  rw [groupMask_function_eq_inter M d w T, ← pathGroups_coe]

theorem listed_expected_nominal_to_final (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (h : ℕ) (hh : h < (groups M d w).length)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    densityThreshold * t * bitsExpectation (fun _ : Fin n => t) univ (fun T =>
      (listedZ M hE {d with T := T} w h : ℝ)) ≤
    densityThreshold * bitsExpectation (fun _ : Fin n => t) univ (fun T =>
      (listedLambda M hE {d with T := T} w h : ℝ)) +
      t * ((2^100) * (groupMask M d w d.C h).ncard +
        ∑ j ∈ range ((groups M d w).length-(h+1)),
          ((2^100) * (groupMask M d w d.C (h+1+j)).ncard +
            (groupMask M d w d.D (h+1+j)).ncard) : ℕ) := by
  have hc := expected_nominal_to_final M hE (2^100) (by positivity)
    (groupMask M d w d.D) (groupMask M d w d.C) (pathGroups M d w)
    (pathGroups_disjoint M d w) h ((groups M d w).length-(h+1))
    ((d.H ∪ d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) (boolParity d.odd) t ht0 ht1
  have hlen : h+1+((groups M d w).length-(h+1)) = (groups M d w).length := by omega
  rw [hlen] at hc
  simp only [listedZ_update_T, listedLambda_update_T]
  convert hc using 1 <;> norm_num [densityThreshold]

end MatroidProphet.MainAlgorithm

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Candidates
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Finset Set

namespace MatroidProphet
namespace Candidates

variable {n : ℕ}

lemma prior_mono (time : Fin n → ℕ) {H V : Finset (Fin n)} (h : H ⊆ V)
    (e : Fin n) : prior time H e ⊆ prior time V e :=
  fun _ hf => ⟨h hf.1, hf.2⟩

lemma greedy_indep (M : Matroid (Fin n)) (time : Fin n → ℕ)
    (ht : Function.Injective time) (H : Finset (Fin n))
    (hground : ∀ e ∈ H, e ∈ M.E) : M.Indep (greedy M time H : Set (Fin n)) := by
  classical
  let label : H → Fin n := Subtype.val
  let arrival : H → ℕ := fun e => time e.val
  have htime : Function.Injective arrival := fun _ _ h => Subtype.ext (ht h)
  have hp (e : H) : label '' {p : H | arrival p < arrival e} = prior time H e.val := by
    ext f
    simp [label, arrival, prior, and_comm]
  have hi := Pivots.keptOccurrences_indep M label arrival (fun e => hground e.val e.property) htime
  have heq : label '' (Pivots.keptOccurrences M label arrival : Set H) =
      (greedy M time H : Set (Fin n)) := by
    ext e
    simp only [Set.mem_image, Finset.mem_coe, Pivots.keptOccurrences, Finset.mem_filter,
      Finset.mem_univ, true_and, greedy]
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact ⟨f.property, by simpa only [hp] using hf⟩
    · rintro ⟨he, hp'⟩
      refine ⟨⟨e, he⟩, ?_, rfl⟩
      simpa only [hp] using hp'
  rwa [heq] at hi

lemma greedy_sdiff_subset_candidates (M : Matroid (Fin n)) (time : Fin n → ℕ)
    (V H : Finset (Fin n)) (hHV : H ⊆ V) :
    greedy M time V \ H ⊆ candidates M time V H := by
  classical
  intro e he
  rcases Finset.mem_sdiff.mp he with ⟨heG, heH⟩
  rcases Finset.mem_filter.mp heG with ⟨heV, hecl⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_sdiff.mpr ⟨heV, heH⟩, ?_⟩
  exact fun h => hecl (M.closure_subset_closure (prior_mono time hHV e) h)

end Candidates
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Priority
attribute [-instance] _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

namespace Priority

open Finset Set

variable {n : ℕ}

lemma time_lt_iff_higher (a : Fin n → Option ℤ) (e f : Fin n) :
    time a e < time a f ↔ Higher a e f := by
  constructor
  · intro h
    by_cases hef : e = f
    · subst f
      exact False.elim (Nat.lt_irrefl _ h)
    · rcases higher_total a hef with hh | hh
      · exact hh
      · exact False.elim ((time_lt_of_higher a hh).not_gt h)
  · exact time_lt_of_higher a

lemma main_higher_iff (a : Fin n → Option ℤ) (e f : Fin n) (hf : a f ≠ none) :
    MainAlgorithm.higher e (a e) f (a f) ↔ Higher a e f := by
  cases heq : a e with
  | none => cases hfq : a f <;> simp_all [MainAlgorithm.higher, Higher, Maximum.higher]
  | some i => cases hfq : a f <;> simp_all [MainAlgorithm.higher, Higher, Maximum.higher, eq_comm]

lemma main_higher_iff_time (a : Fin n → Option ℤ) (e f : Fin n) (hf : a f ≠ none) :
    MainAlgorithm.higher e (a e) f (a f) ↔ time a e < time a f :=
  (main_higher_iff a e f hf).trans (time_lt_iff_higher a e f).symm

end Priority
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_CandidateFilter
attribute [-instance] _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.MainAlgorithm

open Finset Set

variable {n : ℕ}

lemma candidateSet_eq_filter (M : Matroid (Fin n)) (d : MainMasks n)
    (a : Fin n → Option ℤ) :
    candidateSet M d a =
      (Candidates.candidates M (Priority.time a) Finset.univ d.H).filter (fun e => a e ≠ none) := by
  classical
  ext e
  by_cases ha : a e = none
  · constructor
    · intro he
      exact False.elim (((Finset.mem_filter.mp he).2).1 ha)
    · intro he
      exact False.elim ((Finset.mem_filter.mp he).2 ha)
  · have hs : {f | f ∈ d.H ∧ higher f (a f) e (a e)} =
        Candidates.prior (Priority.time a) d.H e := by
      ext f
      simp only [Candidates.prior, Set.mem_ofPred_eq, Priority.main_higher_iff_time a f e ha]
    simp [candidateSet, candidate, Candidates.candidates, ha, hs, and_comm, and_left_comm]

lemma positiveGreedy_indep (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (a : Fin n → Option ℤ) : M.Indep (positiveGreedy M a : Set (Fin n)) := by
  apply (Candidates.greedy_indep M (Priority.time a) (Priority.time_injective a)
    Finset.univ (fun e _ => by simp [hE])).subset
  exact Finset.filter_subset _ _

lemma positiveGreedy_survivors_subset (M : Matroid (Fin n)) (a : Fin n → Option ℤ)
    (H : Finset (Fin n)) : positiveGreedy M a \ H ⊆ candidateLabels M a H := by
  classical
  intro e he
  obtain ⟨heG, heH⟩ := Finset.mem_sdiff.mp he
  obtain ⟨heFull, hea⟩ := Finset.mem_filter.mp heG
  have heC := Candidates.greedy_sdiff_subset_candidates M (Priority.time a) Finset.univ H
    (Finset.subset_univ H) (Finset.mem_sdiff.mpr ⟨heFull, heH⟩)
  rw [candidateLabels, candidateSet_eq_filter]
  exact Finset.mem_filter.mpr ⟨heC, hea⟩

lemma positiveGreedy_survivors_indep (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (a : Fin n → Option ℤ) (H : Finset (Fin n)) :
    M.Indep ((positiveGreedy M a \ H : Finset (Fin n)) : Set (Fin n)) :=
  (positiveGreedy_indep M hE a).subset (fun _ he => (Finset.mem_sdiff.mp he).1)

end MatroidProphet.MainAlgorithm

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Algorithm_Cost
attribute [-instance] _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.MainAlgorithm
open Set Finset
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

lemma sum_groupMask_card_le {ι : Type*} (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (J : Finset ι) (idx : ι → ℕ) (hinj : Set.InjOn idx (J : Set ι))
    (mask target : Finset (Fin n))
    (hsub : ∀ j ∈ J, groupMask M d w mask (idx j) ⊆ (target : Set (Fin n))) :
    (∑ j ∈ J, (groupMask M d w mask (idx j)).ncard) ≤ target.card := by
  classical
  let f : ι → Finset (Fin n) := fun j => (groupMask M d w mask (idx j)).toFinset
  have hf (j : ι) : f j ⊆ pathGroups M d w (idx j) := by
    intro e he
    have hx : e ∈ groupMask M d w mask (idx j) := by simpa [f] using he
    have hg : e ∈ groupMask M d w univ (idx j) := ⟨mem_univ _, hx.2⟩
    simpa [pathGroups] using hg
  have hd : (J : Set ι).PairwiseDisjoint f := by
    intro i hi j hj hij
    have hij' : idx i ≠ idx j := fun heq => hij (hinj hi hj heq)
    exact (pathGroups_disjoint M d w hij').mono (hf i) (hf j)
  have hs : J.biUnion f ⊆ target := by
    intro e he
    obtain ⟨j, hj, hej⟩ := mem_biUnion.mp he
    exact hsub j hj (by simpa [f] using hej)
  have hcard := Finset.card_le_card hs
  rw [card_biUnion hd] at hcard
  simpa only [f, ← Set.ncard_eq_toFinset_card'] using hcard

lemma groupMask_eq_focal (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (mask : Finset (Fin n)) {h : ℕ} {i : ℤ}
    (hi : (groups M d w)[h]? = some i) :
    (groupMask M d w mask h).toFinset =
      mask ∩ ((candidateLabels M w d.H).filter (fun e => w e = some i)) := by
  classical
  ext e
  simp only [Set.mem_toFinset, Finset.mem_inter, mem_filter, candidateLabels, candidateSet, Finset.mem_univ, true_and]
  change (e ∈ mask ∧ candidate M d w e (w e) ∧ w e = (groups M d w)[h]?) ↔
    (e ∈ mask ∧ candidate M d w e (w e) ∧ w e = some i)
  simp only [hi]

lemma groupMask_later_subset (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (mask : Finset (Fin n)) {h j : ℕ} {i : ℤ}
    (hi : (groups M d w)[h]? = some i) (hj : j < (groups M d w).length) (hhj : h < j) :
    groupMask M d w mask j ⊆
      (mask ∩ ((candidateLabels M w d.H).filter (fun e => ∃ k, w e = some k ∧ i < k)) :
        Finset (Fin n)) := by
  intro e he
  have hjget : (groups M d w)[j]? = some ((groups M d w)[j]) := List.getElem?_eq_getElem hj
  obtain ⟨k, hk, hkj⟩ := groups_earlier_key M d w hjget hhj
  have hki : k = i := Option.some.inj (hk.symm.trans hi)
  subst k
  exact Finset.mem_inter.mpr ⟨he.1, mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, he.2.1⟩,
    _, he.2.2.trans hjget, hkj⟩⟩

theorem listed_cost_le_true_counts (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) {h : ℕ} {i : ℤ} (hi : (groups M d w)[h]? = some i) (κ : ℕ) :
    κ * (groupMask M d w d.C h).ncard +
      ∑ j ∈ range ((groups M d w).length-(h+1)),
        (κ * (groupMask M d w d.C (h+1+j)).ncard +
          (groupMask M d w d.D (h+1+j)).ncard) ≤
    κ * (d.C ∩ ((candidateLabels M w d.H).filter (fun e => w e = some i))).card +
      κ * (d.C ∩ ((candidateLabels M w d.H).filter (fun e => ∃ k, w e = some k ∧ i < k))).card +
        ((candidateLabels M w d.H).filter (fun e => ∃ k, w e = some k ∧ i < k)).card := by
  classical
  let J := range ((groups M d w).length-(h+1))
  let high := (candidateLabels M w d.H).filter (fun e => ∃ k, w e = some k ∧ i < k)
  have hh := (List.getElem?_eq_some_iff.mp hi).1
  have hc : (∑ j ∈ J, (groupMask M d w d.C (h+1+j)).ncard) ≤ (d.C ∩ high).card := by
    apply sum_groupMask_card_le M d w J (fun j => h+1+j) (by intro a _ b _ hab; change h+1+a = h+1+b at hab; omega)
    intro j hj
    exact groupMask_later_subset M d w d.C hi (by have := mem_range.mp hj; omega) (by omega)
  have hd : (∑ j ∈ J, (groupMask M d w d.D (h+1+j)).ncard) ≤ high.card := by
    apply sum_groupMask_card_le M d w J (fun j => h+1+j) (by intro a _ b _ hab; change h+1+a = h+1+b at hab; omega)
    intro j hj e he
    have hm := groupMask_later_subset M d w d.D hi
      (by have := mem_range.mp hj; omega) (by omega) he
    exact (Finset.mem_inter.mp hm).2
  have hf : (groupMask M d w d.C h).ncard =
      (d.C ∩ ((candidateLabels M w d.H).filter (fun e => w e = some i))).card := by
    rw [Set.ncard_eq_toFinset_card', groupMask_eq_focal M d w d.C hi]
  rw [hf, sum_add_distrib, ← mul_sum]
  have hm := Nat.mul_le_mul_left κ hc
  change _ ≤ _ at hd
  dsimp [J, high] at hm hd
  omega

end MatroidProphet.MainAlgorithm

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_GroupConditioning
attribute [-instance] _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.MainAlgorithm
open Finset
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

lemma mem_listed_iff (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) :
    i ∈ listed M d s ↔ ∃ e ∈ d.D, e ∈ trueGroup M d s i := by
  simp only [listed, mem_biUnion, mem_trueGroup]
  constructor
  · rintro ⟨e, he, hi⟩
    by_cases hc : candidate M d s e (s e)
    · simp only [ite_eq_left hc, Option.mem_toFinset] at hi
      exact ⟨e, he, hc, hi⟩
    · simp only [ite_eq_right hc, Finset.notMem_empty] at hi
  · rintro ⟨e, he, hc, hi⟩
    exact ⟨e, he, by rw [ite_eq_left hc]; simp [hi]⟩

lemma groupMask_at_key (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (mask : Finset (Fin n)) (h : ℕ) (i : ℤ)
    (hi : (groups M d s)[h]? = some i) :
    groupMask M d s mask h = ((mask ∩ trueGroup M d s i : Finset (Fin n)) : Set (Fin n)) := by
  ext e
  simp only [groupMask, Set.mem_ofPred_eq, Finset.mem_coe, mem_inter, mem_trueGroup, hi]

end MatroidProphet.MainAlgorithm

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Baseline
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set
variable {α : Type*} [Fintype α]

omit [Fintype α] in
lemma natRank_eq_ncard_of_indep (M : Matroid α) {I : Set α} (hI : M.Indep I) :
    natRank M I = I.ncard := by
  simp only [natRank, hI.eRk_eq_encard, Set.ncard_def]

lemma baseline_density_rank (M : Matroid α) (hE : M.E = Set.univ) (κ : ℕ) (D : Set α) :
    κ * natRank M (densityExpansion M hE κ D (M.closure ∅)) ≤ D.ncard := by
  let Q := densityExpansion M hE κ D (M.closure ∅)
  have hmax := (densityExpansion_spec M hE κ D (M.closure ∅)).1.2.2
    (M.closure ∅) (Matroid.isFlat_closure (M := M) ∅) Set.Subset.rfl
  have hcount := Set.ncard_mono (show D ∩ Q ⊆ D from inter_subset_left)
  have hnn : (0 : ℤ) ≤ (D ∩ M.closure ∅).ncard := by exact_mod_cast Nat.zero_le _
  have hcount' : ((D ∩ Q).ncard : ℤ) ≤ D.ncard := by exact_mod_cast hcount
  have hmax' : (κ : ℤ) * natRank M Q ≤ D.ncard := by
    dsimp only [densityObjective] at hmax
    rw [natRank_closure, natRank_empty] at hmax
    change _ ≤ (D ∩ Q).ncard - (κ : ℤ) * natRank M Q at hmax
    omega
  exact_mod_cast hmax'

lemma baseline_independent_count (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D I : Set α) (hI : M.Indep I) :
    κ * (I ∩ densityExpansion M hE κ D (M.closure ∅)).ncard ≤ D.ncard := by
  have hi := natRank_eq_ncard_of_indep M
    (hI.subset (show I ∩ densityExpansion M hE κ D (M.closure ∅) ⊆ I from inter_subset_left))
  have hr := natRank_mono M (show I ∩ densityExpansion M hE κ D (M.closure ∅) ⊆
      densityExpansion M hE κ D (M.closure ∅) from inter_subset_right)
  rw [hi] at hr
  exact (Nat.mul_le_mul_left κ hr).trans (baseline_density_rank M hE κ D)

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_BatchReveal
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α β γ : Type*} [DecidableEq α]

lemma RevealTree.fresh_map (tree : RevealTree α β) (f : β → γ) (V : Finset α) :
    (tree.map f).Fresh V ↔ tree.Fresh V := by
  induction tree generalizing V with
  | leaf b => rfl
  | query e no yes ihn ihy => simp only [map, Fresh, ihn, ihy]

lemma RevealTree.run_map (tree : RevealTree α β) (f : β → γ) (S : Finset α) :
    (tree.map f).run S = f (tree.run S) := by
  induction tree generalizing S with
  | leaf b => rfl
  | query e no yes ihn ihy =>
    simp only [map, run]
    split_ifs <;> simp_all

lemma erase_sdiff_eq_sdiff_insert (S X : Finset α) (e : α) :
    S.erase e \ X = S \ insert e X := by
  ext x
  simp only [mem_sdiff, mem_erase, mem_insert]
  tauto

lemma revealBatch_fresh (xs : List α) (hxs : xs.Nodup)
    (cont : Finset α → RevealTree α β) (V : Finset α)
    (hXV : xs.toFinset ⊆ V)
    (hcont : ∀ I ⊆ xs.toFinset, (cont I).Fresh (V \ xs.toFinset)) :
    (revealBatch xs cont).Fresh V := by
  induction xs generalizing cont V with
  | nil => simpa [revealBatch] using hcont ∅ (empty_subset _)
  | cons e xs ih =>
    have heX : e ∉ xs.toFinset := by simpa using (List.nodup_cons.mp hxs).1
    have heV : e ∈ V := hXV (by simp)
    have hsub : xs.toFinset ⊆ V.erase e := by
      intro x hx
      refine mem_erase.mpr ⟨?_, hXV (by simp [hx])⟩
      intro h; subst x; exact heX hx
    have htail := (List.nodup_cons.mp hxs).2
    refine ⟨heV, ih htail cont (V.erase e) hsub ?_,
      ih htail (fun I => cont (insert e I)) (V.erase e) hsub ?_⟩
    · intro I hI
      rw [erase_sdiff_eq_sdiff_insert]
      simpa only [List.toFinset_cons] using hcont I (by simpa using hI.trans (subset_insert e xs.toFinset))
    · intro I hI
      rw [erase_sdiff_eq_sdiff_insert]
      simpa only [List.toFinset_cons] using hcont (insert e I) (by simpa using insert_subset_insert e hI)

lemma revealBatch_run (xs : List α) (hxs : xs.Nodup)
    (cont : Finset α → RevealTree α β) (S : Finset α) :
    (revealBatch xs cont).run S = (cont (S ∩ xs.toFinset)).run (S \ xs.toFinset) := by
  induction xs generalizing cont S with
  | nil => simp [revealBatch]
  | cons e xs ih =>
    have heX : e ∉ xs.toFinset := by simpa using (List.nodup_cons.mp hxs).1
    have htail := (List.nodup_cons.mp hxs).2
    have hinter : S.erase e ∩ xs.toFinset = S ∩ xs.toFinset := by
      ext x
      by_cases hx : x = e
      · subst x; simp [heX]
      · simp [hx]
    by_cases heS : e ∈ S
    · rw [revealBatch, RevealTree.run, ite_eq_left heS, ih htail,
        hinter, erase_sdiff_eq_sdiff_insert]
      have hins : insert e (S ∩ xs.toFinset) = S ∩ insert e xs.toFinset := by
        ext x
        by_cases hx : x = e
        · subst x; simp [heS]
        · simp [hx]
      simp only [List.toFinset_cons, hins]
    · rw [revealBatch, RevealTree.run, ite_eq_right heS, ih htail,
        hinter, erase_sdiff_eq_sdiff_insert]
      have hins : S ∩ xs.toFinset = S ∩ insert e xs.toFinset := by
        ext x
        by_cases hx : x = e
        · subst x; simp [heS]
        · simp [hx]
      simp only [List.toFinset_cons, hins]

lemma revealBatch_queried (xs : List α) (hxs : xs.Nodup)
    (cont : Finset α → RevealTree α β) (S : Finset α) :
    (revealBatch xs cont).queried S =
      xs.toFinset ∪ (cont (S ∩ xs.toFinset)).queried (S \ xs.toFinset) := by
  induction xs generalizing cont S with
  | nil => simp [revealBatch]
  | cons e xs ih =>
    have heX : e ∉ xs.toFinset := by simpa using (List.nodup_cons.mp hxs).1
    have htail := (List.nodup_cons.mp hxs).2
    have hinter : S.erase e ∩ xs.toFinset = S ∩ xs.toFinset := by
      ext x
      by_cases hx : x = e
      · subst x; simp [heX]
      · simp [hx]
    by_cases heS : e ∈ S
    · rw [revealBatch, RevealTree.queried, ite_eq_left heS, ih htail,
        hinter, erase_sdiff_eq_sdiff_insert]
      have hins : insert e (S ∩ xs.toFinset) = S ∩ insert e xs.toFinset := by
        ext x
        by_cases hx : x = e
        · subst x; simp [heS]
        · simp [hx]
      simp only [List.toFinset_cons, hins, insert_union]
    · rw [revealBatch, RevealTree.queried, ite_eq_right heS, ih htail,
        hinter, erase_sdiff_eq_sdiff_insert]
      have hins : S ∩ xs.toFinset = S ∩ insert e xs.toFinset := by
        ext x
        by_cases hx : x = e
        · subst x; simp [heS]
        · simp [hx]
      simp only [List.toFinset_cons, hins, insert_union]

lemma RevealTree.queried_map (tree : RevealTree α β) (f : β → γ) (S : Finset α) :
    (tree.map f).queried S = tree.queried S := by
  induction tree generalizing S with
  | leaf b => rfl
  | query e no yes ihn ihy =>
    simp only [map, queried]
    split_ifs <;> simp_all

lemma RevealTree.record_fresh (tree : RevealTree α β) (V : Finset α) :
    tree.record.Fresh V ↔ tree.Fresh V := by
  induction tree generalizing V with
  | leaf b => rfl
  | query e no yes ihn ihy => simp only [record, Fresh, fresh_map, ihn, ihy]

lemma RevealTree.record_run (tree : RevealTree α β) (S : Finset α) :
    tree.record.run S = ⟨tree.run S, tree.queried S, S ∩ tree.queried S⟩ := by
  induction tree generalizing S with
  | leaf b => simp [record, run, queried]
  | query e no yes ihn ihy =>
    by_cases heS : e ∈ S
    · simp only [record, run, queried, ite_eq_left heS, run_map, ihy]
      congr 1
      ext x
      by_cases hxe : x = e
      · subst x; simp [heS]
      · simp [hxe]
    · simp only [record, run, queried, ite_eq_right heS, run_map, ihn]
      congr 1
      ext x
      by_cases hxe : x = e
      · subst x; simp [heS]
      · simp [hxe]

lemma RevealTree.record_queried (tree : RevealTree α β) (S : Finset α) :
    tree.record.queried S = tree.queried S := by
  induction tree generalizing S with
  | leaf b => rfl
  | query e no yes ihn ihy => simp only [record, queried, queried_map, ihn, ihy]

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_RevealContinuation
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α β : Type*} [DecidableEq α]

theorem RevealTree.continuation_expectation (tree : RevealTree α β)
    (q : α → ℝ) (V : Finset α) (fresh : tree.Fresh V)
    (f : β → Finset α → ℝ) :
    bitsExpectation q V (fun S => f (tree.run S) (S \ tree.queried S)) =
      bitsExpectation q V (fun S => bitsExpectation q (V \ tree.queried S)
        (fun T => f (tree.run S) T)) := by
  induction tree generalizing V with
  | leaf b => simp only [run, queried, sdiff_empty, bitsExpectation_const]
  | query e no yes ihn ihy =>
    rcases fresh with ⟨he, hn, hy⟩
    let W := V.erase e
    have heW : e ∉ W := notMem_erase e V
    have hWV : insert e W = V := insert_erase he
    have leftSplit := bitsExpectation_insert q W e heW
      (fun S => f ((RevealTree.query e no yes).run S)
        (S \ (RevealTree.query e no yes).queried S))
    rw [hWV] at leftSplit
    have rightSplit := bitsExpectation_insert q W e heW
      (fun S => bitsExpectation q (V \ (RevealTree.query e no yes).queried S)
        (fun T => f ((RevealTree.query e no yes).run S) T))
    rw [hWV] at rightSplit
    have hSD (S Q : Finset α) (hS : S ⊆ W) :
        S \ insert e Q = S \ Q ∧ insert e S \ insert e Q = S \ Q := by
      have heS : e ∉ S := fun h => heW (hS h)
      constructor <;> ext x <;> by_cases hxe : x = e
      · subst x; simp [heS]
      · simp [hxe]
      · subst x; simp [heS]
      · simp [hxe]
    have hnoLeft : bitsExpectation q W (fun S => f ((RevealTree.query e no yes).run S)
        (S \ (RevealTree.query e no yes).queried S)) =
        bitsExpectation q W (fun S => f (no.run S) (S \ no.queried S)) := by
      apply bitsExpectation_congr
      intro S hS
      have heS : e ∉ S := fun h => heW (hS h)
      simp only [run, queried, ite_eq_right heS, erase_eq_of_notMem heS, (hSD S _ hS).1]
    have hyesLeft : bitsExpectation q W (fun S => f ((RevealTree.query e no yes).run (insert e S))
        (insert e S \ (RevealTree.query e no yes).queried (insert e S))) =
        bitsExpectation q W (fun S => f (yes.run S) (S \ yes.queried S)) := by
      apply bitsExpectation_congr
      intro S hS
      have heS : e ∉ S := fun h => heW (hS h)
      simp only [run, queried, mem_insert_self, ite_true, erase_insert heS, (hSD S _ hS).2]
    have hnoRight : bitsExpectation q W (fun S =>
        bitsExpectation q (V \ (RevealTree.query e no yes).queried S)
          (fun T => f ((RevealTree.query e no yes).run S) T)) =
        bitsExpectation q W (fun S => bitsExpectation q (W \ no.queried S)
          (fun T => f (no.run S) T)) := by
      apply bitsExpectation_congr
      intro S hS
      have heS : e ∉ S := fun h => heW (hS h)
      simp only [run, queried, ite_eq_right heS, erase_eq_of_notMem heS,
        ← erase_sdiff_eq_sdiff_insert, W]
    have hyesRight : bitsExpectation q W (fun S =>
        bitsExpectation q (V \ (RevealTree.query e no yes).queried (insert e S))
          (fun T => f ((RevealTree.query e no yes).run (insert e S)) T)) =
        bitsExpectation q W (fun S => bitsExpectation q (W \ yes.queried S)
          (fun T => f (yes.run S) T)) := by
      apply bitsExpectation_congr
      intro S hS
      have heS : e ∉ S := fun h => heW (hS h)
      simp only [run, queried, mem_insert_self, ite_true, erase_insert heS,
        ← erase_sdiff_eq_sdiff_insert, W]
    rw [leftSplit, rightSplit, hnoLeft, hyesLeft, hnoRight, hyesRight, ihn W hn, ihy W hy]

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Certificates_Budget
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open Finset

variable {α : Type*} [DecidableEq α]

lemma ratio_resource {p p' a : ℝ} (hp : 0 < p) (hpp' : p ≤ p')
    (ha : 0 ≤ a) (hap : a ≤ p) :
    a / p - a / p' ≤ Real.log p' - Real.log p := by
  have hp' : 0 < p' := lt_of_lt_of_le hp hpp'
  have hz : a / p ≤ 1 := (div_le_one hp).2 hap
  have hz0 : 0 ≤ a / p := div_nonneg ha hp.le
  have hx0 : 0 ≤ 1 - p / p' := by
    have h := (div_le_one hp').2 hpp'
    linarith
  have hm := mul_le_mul_of_nonneg_right hz hx0
  have heq : a / p - a / p' = (a / p) * (1 - p / p') := by
    field_simp
  rw [heq]
  calc
    a / p * (1 - p / p') ≤ 1 - p / p' := by simpa using hm
    _ ≤ Real.log (p' / p) := by
      simpa using Real.one_sub_inv_le_log_of_pos (div_pos hp' hp)
    _ = Real.log p' - Real.log p := Real.log_div hp'.ne' hp.ne'

theorem certificate_budget_of_failure_identities
    (cert : Finset α → Prop) [DecidablePred cert] (q : α → ℝ)
    (q_nonneg : ∀ e, 0 ≤ q e) (q_le_one : ∀ e, q e ≤ 1)
    (failure : Finset α → Finset α → ℝ)
    (positive : ∀ V, 0 < failure V ∅)
    (bounded : ∀ V I, 0 ≤ failure V I ∧ failure V I ≤ failure V ∅)
    (at_most_one : ∀ V, failure V ∅ ≤ 1)
    (depleted : ∀ V e, e ∈ V → failure V ∅ ≤ failure (V.erase e) ∅)
    (split : ∀ V I e, e ∈ V → failure V I =
      (1 - q e) * failure (V.erase e) I + q e * failure (V.erase e) (insert e I))
    (certifies : ∀ V I, cert I → failure V I = 0)
    (prog : QueryProgram α) (V I : Finset α) (fresh : prog.Fresh V) :
    prog.expected cert q I ≤ -Real.log (failure V ∅) + 1 - failure V I / failure V ∅ := by
  induction prog generalizing V I with
  | stop =>
    dsimp [QueryProgram.expected]
    have hlog : Real.log (failure V ∅) ≤ 0 :=
      Real.log_nonpos (positive V).le (at_most_one V)
    have hratio : failure V I / failure V ∅ ≤ 1 :=
      (div_le_one (positive V)).2 (bounded V I).2
    linarith
  | finish rest ih =>
    dsimp [QueryProgram.Fresh] at fresh
    have hr := ih V ∅ fresh
    have hp := positive V
    rw [div_self hp.ne'] at hr
    dsimp [QueryProgram.expected]
    split_ifs with hcert
    · rw [certifies V I hcert, zero_div]
      linarith
    · have hratio : failure V I / failure V ∅ ≤ 1 :=
        (div_le_one hp).2 (bounded V I).2
      linarith
  | query e no yes ihn ihy =>
    rcases fresh with ⟨he, hn, hy⟩
    have hno := ihn (V.erase e) I hn
    have hyes := ihy (V.erase e) (insert e I) hy
    have hqn : 0 ≤ 1 - q e := sub_nonneg.2 (q_le_one e)
    have h0 := mul_le_mul_of_nonneg_left hno hqn
    have h1 := mul_le_mul_of_nonneg_left hyes (q_nonneg e)
    have hp := positive V
    have hp' := positive (V.erase e)
    have hs := split V I e he
    have hresource := ratio_resource hp (depleted V e he) (bounded V I).1 (bounded V I).2
    have hmix : (1 - q e) *
        (-Real.log (failure (V.erase e) ∅) + 1 - failure (V.erase e) I / failure (V.erase e) ∅) +
        q e * (-Real.log (failure (V.erase e) ∅) + 1 -
          failure (V.erase e) (insert e I) / failure (V.erase e) ∅) =
        -Real.log (failure (V.erase e) ∅) + 1 - failure V I / failure (V.erase e) ∅ := by
      rw [hs]
      ring
    dsimp [QueryProgram.expected]
    linarith

theorem disjoint_query_certificates [Fintype α]
    (cert : Finset α → Prop) [DecidablePred cert] (hcert : Monotone cert)
    (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (hδ : 0 < bitsFailure cert q univ ∅)
    (prog : QueryProgram α) (fresh : prog.Fresh univ) :
    prog.expected cert q ∅ ≤ Real.log (1 / bitsFailure cert q univ ∅) := by
  have hp (V : Finset α) : 0 < bitsFailure cert q V ∅ :=
    lt_of_lt_of_le hδ (bitsFailure_antitone cert hcert q hq0 hq1 ∅ (subset_univ V))
  have h := certificate_budget_of_failure_identities cert q hq0 hq1
    (bitsFailure cert q) hp
    (fun V I => ⟨bitsFailure_nonneg cert q hq0 hq1 V I,
      bitsFailure_forced_antitone cert hcert q hq0 hq1 V (empty_subset I)⟩)
    (fun V => bitsFailure_le_one cert q hq0 hq1 V ∅)
    (fun V e _ => bitsFailure_antitone cert hcert q hq0 hq1 ∅ (erase_subset e V))
    (bitsFailure_split cert q)
    (bitsFailure_certifies cert hcert q) prog univ ∅ fresh
  simpa [div_self hδ.ne'] using h

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Certificates_Execution
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open Finset

variable {α : Type*} [DecidableEq α]

lemma QueryProgram.run_congr (cert : Finset α → Prop) [DecidablePred cert]
    (prog : QueryProgram α) (V I S S' : Finset α) (fresh : prog.Fresh V)
    (agree : ∀ e ∈ V, (e ∈ S ↔ e ∈ S')) :
    prog.run cert S I = prog.run cert S' I := by
  induction prog generalizing V I with
  | stop => rfl
  | finish rest ih =>
    simp only [run]
    rw [ih V ∅ fresh agree]
  | query e no yes ihn ihy =>
    rcases fresh with ⟨he, hn, hy⟩
    have ha := agree e he
    have har : ∀ x ∈ V.erase e, (x ∈ S ↔ x ∈ S') :=
      fun x hx => agree x (mem_of_mem_erase hx)
    by_cases h : e ∈ S
    · simp only [run, ite_eq_left h, ite_eq_left (ha.mp h)]
      exact ihy (V.erase e) (insert e I) hy har
    · have h' : e ∉ S' := fun hx => h (ha.mpr hx)
      simp only [run, ite_eq_right h, ite_eq_right h']
      exact ihn (V.erase e) I hn har

lemma QueryProgram.expected_eq_product (cert : Finset α → Prop) [DecidablePred cert]
    (q : α → ℝ) (prog : QueryProgram α) (V I : Finset α) (fresh : prog.Fresh V) :
    bitsExpectation q V (fun S => prog.run cert S I) = prog.expected cert q I := by
  induction prog generalizing V I with
  | stop => simp only [run, expected, bitsExpectation_const]
  | finish rest ih =>
    simp only [run, expected, bitsExpectation_add, bitsExpectation_const]
    rw [ih V ∅ fresh]
  | query e no yes ihn ihy =>
    rcases fresh with ⟨he, hn, hy⟩
    have hsplit := bitsExpectation_insert q (V.erase e) e (notMem_erase e V)
      (fun S => (QueryProgram.query e no yes).run cert S I)
    rw [insert_erase he] at hsplit
    have hno : bitsExpectation q (V.erase e)
        (fun S => (QueryProgram.query e no yes).run cert S I) =
        bitsExpectation q (V.erase e) (fun S => no.run cert S I) := by
      apply bitsExpectation_congr
      intro S hS
      have heS : e ∉ S := fun hx => (notMem_erase e V) (hS hx)
      simp only [run, ite_eq_right heS]
    have hyes : bitsExpectation q (V.erase e)
        (fun S => (QueryProgram.query e no yes).run cert (insert e S) I) =
        bitsExpectation q (V.erase e) (fun S => yes.run cert S (insert e I)) := by
      apply bitsExpectation_congr
      intro S hS
      simp only [run, mem_insert_self, ite_true]
      apply yes.run_congr cert (V.erase e) (insert e I) (insert e S) S hy
      intro x hx
      have hxe : x ≠ e := (mem_erase.1 hx).1
      simp only [mem_insert, hxe, false_or]
    rw [hsplit, hno, hyes, ihn (V.erase e) I hn, ihy (V.erase e) (insert e I) hy]
    rfl

theorem disjoint_query_certificates_product [Fintype α]
    (cert : Finset α → Prop) [DecidablePred cert] (hcert : Monotone cert)
    (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (hδ : 0 < bitsFailure cert q univ ∅)
    (prog : QueryProgram α) (fresh : prog.Fresh univ) :
    bitsExpectation q univ (fun S => prog.run cert S ∅) ≤
      Real.log (1 / bitsFailure cert q univ ∅) := by
  rw [prog.expected_eq_product cert q univ ∅ fresh]
  exact disjoint_query_certificates cert hcert q hq0 hq1 hδ prog fresh

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_RevealComposition
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α β γ : Type*} [DecidableEq α]

lemma RevealTree.run_bind (tree : RevealTree α β) (cont : β → RevealTree α γ) (S : Finset α) :
    (tree.bind cont).run S = (cont (tree.run S)).run (S \ tree.queried S) := by
  induction tree generalizing S with
  | leaf b => simp [bind, run, queried]
  | query e no yes ihn ihy =>
    by_cases heS : e ∈ S
    · simp only [bind, run, queried, ite_eq_left heS, ihy, erase_sdiff_eq_sdiff_insert]
    · simp only [bind, run, queried, ite_eq_right heS, ihn, erase_sdiff_eq_sdiff_insert]

lemma RevealTree.queried_bind (tree : RevealTree α β) (cont : β → RevealTree α γ) (S : Finset α) :
    (tree.bind cont).queried S =
      tree.queried S ∪ (cont (tree.run S)).queried (S \ tree.queried S) := by
  induction tree generalizing S with
  | leaf b => simp [bind, run, queried]
  | query e no yes ihn ihy =>
    by_cases heS : e ∈ S
    · simp only [bind, run, queried, ite_eq_left heS, ihy, erase_sdiff_eq_sdiff_insert, insert_union]
    · simp only [bind, run, queried, ite_eq_right heS, ihn, erase_sdiff_eq_sdiff_insert, insert_union]

lemma RevealTree.fresh_bind (tree : RevealTree α β) (cont : β → RevealTree α γ)
    (V : Finset α) (fresh : tree.Fresh V)
    (hcont : ∀ S ⊆ V, (cont (tree.run S)).Fresh (V \ tree.queried S)) :
    (tree.bind cont).Fresh V := by
  induction tree generalizing V with
  | leaf b => simpa [bind, run, queried] using hcont ∅ (empty_subset V)
  | query e no yes ihn ihy =>
    rcases fresh with ⟨he, hn, hy⟩
    refine ⟨he, ihn (V.erase e) hn ?_, ihy (V.erase e) hy ?_⟩
    · intro S hS
      have heS : e ∉ S := fun hs => notMem_erase e V (hS hs)
      have hc := hcont S (hS.trans (erase_subset e V))
      simpa only [run, queried, ite_eq_right heS, erase_eq_of_notMem heS,
        erase_sdiff_eq_sdiff_insert] using hc
    · intro S hS
      have heS : e ∉ S := fun hs => notMem_erase e V (hS hs)
      have hc := hcont (insert e S) (insert_subset he (hS.trans (erase_subset e V)))
      simpa only [run, queried, mem_insert_self, ite_true, erase_insert heS,
        erase_eq_of_notMem heS, erase_sdiff_eq_sdiff_insert] using hc

lemma RevealTree.run_congr (tree : RevealTree α β) (V S S' : Finset α)
    (fresh : tree.Fresh V) (agree : ∀ e ∈ V, (e ∈ S ↔ e ∈ S')) :
    tree.run S = tree.run S' := by
  induction tree generalizing V S S' with
  | leaf b => rfl
  | query e no yes ihn ihy =>
    rcases fresh with ⟨he, hn, hy⟩
    have ha := agree e he
    have har : ∀ x ∈ V.erase e, (x ∈ S.erase e ↔ x ∈ S'.erase e) := by
      intro x hx
      simp only [mem_erase, agree x (mem_of_mem_erase hx)]
    by_cases heS : e ∈ S
    · simp only [run, ite_eq_left heS, ite_eq_left (ha.mp heS)]
      exact ihy _ _ _ hy har
    · have heS' : e ∉ S' := fun h => heS (ha.mpr h)
      simp only [run, ite_eq_right heS, ite_eq_right heS']
      exact ihn _ _ _ hn har

lemma RevealTree.queried_congr (tree : RevealTree α β) (V S S' : Finset α)
    (fresh : tree.Fresh V) (agree : ∀ e ∈ V, (e ∈ S ↔ e ∈ S')) :
    tree.queried S = tree.queried S' := by
  induction tree generalizing V S S' with
  | leaf b => rfl
  | query e no yes ihn ihy =>
    rcases fresh with ⟨he, hn, hy⟩
    have ha := agree e he
    have har : ∀ x ∈ V.erase e, (x ∈ S.erase e ↔ x ∈ S'.erase e) := by
      intro x hx
      simp only [mem_erase, agree x (mem_of_mem_erase hx)]
    by_cases heS : e ∈ S
    · simp only [queried, ite_eq_left heS, ite_eq_left (ha.mp heS)]
      rw [ihy _ _ _ hy har]
    · have heS' : e ∉ S' := fun h => heS (ha.mpr h)
      simp only [queried, ite_eq_right heS, ite_eq_right heS']
      rw [ihn _ _ _ hn har]

lemma RevealTree.transaction_fresh (tree : RevealTree α β) (cont : β → QueryProgram α)
    (V : Finset α) (fresh : tree.Fresh V)
    (hcont : ∀ S ⊆ V, (cont (tree.run S)).Fresh (V \ tree.queried S)) :
    (tree.transaction cont).Fresh V := by
  induction tree generalizing V with
  | leaf b => simpa [transaction, QueryProgram.Fresh, run, queried] using hcont ∅ (empty_subset V)
  | query e no yes ihn ihy =>
    rcases fresh with ⟨he, hn, hy⟩
    refine ⟨he, ihn (V.erase e) hn ?_, ihy (V.erase e) hy ?_⟩
    · intro S hS
      have heS : e ∉ S := fun hs => notMem_erase e V (hS hs)
      have hc := hcont S (hS.trans (erase_subset e V))
      simpa only [run, queried, ite_eq_right heS, erase_eq_of_notMem heS,
        erase_sdiff_eq_sdiff_insert] using hc
    · intro S hS
      have heS : e ∉ S := fun hs => notMem_erase e V (hS hs)
      have hc := hcont (insert e S) (insert_subset he (hS.trans (erase_subset e V)))
      simpa only [run, queried, mem_insert_self, ite_true, erase_insert heS,
        erase_eq_of_notMem heS, erase_sdiff_eq_sdiff_insert] using hc

lemma RevealTree.transaction_run (tree : RevealTree α β) (cont : β → QueryProgram α)
    (V : Finset α) (fresh : tree.Fresh V) (cert : Finset α → Prop) [DecidablePred cert]
    (S I : Finset α) :
    (tree.transaction cont).run cert S I =
      (if cert (I ∪ (S ∩ tree.queried S)) then 1 else 0) + (cont (tree.run S)).run cert S ∅ := by
  induction tree generalizing V I with
  | leaf b => simp [transaction, QueryProgram.run, run, queried]
  | query e no yes ihn ihy =>
    rcases fresh with ⟨he, hn, hy⟩
    have ha : ∀ x ∈ V.erase e, (x ∈ S ↔ x ∈ S.erase e) := by
      intro x hx
      simp only [mem_erase]
      exact ⟨fun hs => ⟨(mem_erase.mp hx).1, hs⟩, fun hs => hs.2⟩
    by_cases heS : e ∈ S
    · rw [transaction, QueryProgram.run, ite_eq_left heS, ihy _ hy]
      rw [yes.run_congr _ S (S.erase e) hy ha, yes.queried_congr _ S (S.erase e) hy ha]
      simp only [run, queried, ite_eq_left heS]
      have heq : insert e I ∪ S ∩ yes.queried (S.erase e) =
          I ∪ S ∩ insert e (yes.queried (S.erase e)) := by
        ext x
        by_cases hxe : x = e
        · subst x; simp [heS]
        · simp [hxe]
      rw [heq]
    · rw [transaction, QueryProgram.run, ite_eq_right heS, ihn _ hn]
      rw [no.run_congr _ S (S.erase e) hn ha, no.queried_congr _ S (S.erase e) hn ha]
      simp only [run, queried, ite_eq_right heS]
      have heq : I ∪ S ∩ no.queried (S.erase e) =
          I ∪ S ∩ insert e (no.queried (S.erase e)) := by
        ext x
        by_cases hxe : x = e
        · subst x; simp [heS]
        · simp [hxe]
      rw [heq]

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Reverse_Exposure
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

lemma layerUpdate_eq_batch (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (L : ReverseLayer α) (A : Set α) (C : Finset α) :
    layerUpdate M hE κ k L A C =
      M.closure (layerNominal M hE κ k L A ∪ (C ∩ layerBatch M hE κ k L A : Finset α)) := by
  unfold layerUpdate
  congr 1
  ext e
  simp only [layerBatch, Set.mem_union, Set.mem_inter_iff, mem_coe, mem_inter, mem_filter]
  tauto

lemma reverseExposureTree_fresh (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (Ls : List (ReverseLayer α))
    (hdisj : Ls.Pairwise (fun L L' => Disjoint L.group L'.group))
    (V : Finset α) (hV : ∀ L ∈ Ls, (L.group.filter (fun e => e ∈ L.state)) ⊆ V) (A : Set α) :
    (reverseExposureTree M hE κ k Ls A).Fresh V := by
  induction Ls generalizing V A with
  | nil => trivial
  | cons L Ls ih =>
    rw [List.pairwise_cons] at hdisj
    apply revealBatch_fresh _ (nodup_toList _) _ V
    · simp only [toList_toFinset]
      intro e he
      exact hV L (by simp) (mem_filter.mpr ⟨(mem_filter.mp he).1, (mem_filter.mp he).2.1⟩)
    · intro I hI
      simp only [toList_toFinset]
      apply ih hdisj.2
      intro L' hL' e he
      refine mem_sdiff.mpr ⟨hV L' (by simp [hL']) he, ?_⟩
      intro hb
      have heL := (mem_filter.mp hb).1
      exact Finset.disjoint_left.mp (hdisj.1 L' hL') heL (mem_filter.mp he).1

lemma layerUpdate_congr (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (L : ReverseLayer α) (A : Set α) (C C' : Finset α)
    (hC : ∀ e ∈ L.group, (e ∈ C ↔ e ∈ C')) :
    layerUpdate M hE κ k L A C = layerUpdate M hE κ k L A C' := by
  unfold layerUpdate
  congr 1
  ext e
  by_cases heG : e ∈ L.group
  · simp only [Set.mem_union, Set.mem_inter_iff, mem_coe, hC e heG]
  · simp [heG]

lemma runReverseLayers_congr (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (Ls : List (ReverseLayer α)) (A : Set α) (C C' : Finset α)
    (hC : ∀ L ∈ Ls, ∀ e ∈ L.group, (e ∈ C ↔ e ∈ C')) :
    runReverseLayers M hE κ k Ls A C = runReverseLayers M hE κ k Ls A C' := by
  induction Ls generalizing A with
  | nil => rfl
  | cons L Ls ih =>
    rw [runReverseLayers, runReverseLayers, layerUpdate_congr M hE κ k L A C C' (hC L (by simp))]
    exact ih _ (fun L' hL' => hC L' (by simp [hL']))

lemma reverseExposureTree_run (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (Ls : List (ReverseLayer α))
    (hdisj : Ls.Pairwise (fun L L' => Disjoint L.group L'.group))
    (A : Set α) (C : Finset α) :
    (reverseExposureTree M hE κ k Ls A).run C = runReverseLayers M hE κ k Ls A C := by
  induction Ls generalizing A C with
  | nil => rfl
  | cons L Ls ih =>
    rw [List.pairwise_cons] at hdisj
    rw [reverseExposureTree, revealBatch_run _ (nodup_toList _)]
    simp only [toList_toFinset]
    rw [ih hdisj.2, ← layerUpdate_eq_batch, runReverseLayers]
    apply runReverseLayers_congr
    intro L' hL' e he
    have heB : e ∉ layerBatch M hE κ k L A := by
      intro hb
      exact Finset.disjoint_left.mp (hdisj.1 L' hL') (mem_filter.mp hb).1 he
    simp [heB]

theorem reverseExposure_hybrid_independent (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (Ls : List (ReverseLayer α))
    (hdisj : Ls.Pairwise (fun L L' => Disjoint L.group L'.group))
    (V : Finset α) (hV : ∀ L ∈ Ls, (L.group.filter (fun e => e ∈ L.state)) ⊆ V) (A : Set α)
    (q : α → ℝ) (φ : Set α → ℝ) (ψ : Finset α → ℝ) :
    bitsExpectation q V (fun C => bitsExpectation q V (fun T =>
      φ (runReverseLayers M hE κ k Ls A C) *
        ψ ((reverseExposureTree M hE κ k Ls A).hybrid C T))) =
      bitsExpectation q V (fun C => φ (runReverseLayers M hE κ k Ls A C)) *
        bitsExpectation q V ψ := by
  have h := (reverseExposureTree M hE κ k Ls A).hybrid_independent q V
    (reverseExposureTree_fresh M hE κ k Ls hdisj V hV A) φ ψ
  simpa only [reverseExposureTree_run M hE κ k Ls hdisj] using h

omit [DecidableEq α] in
lemma runReverseLayers_append (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (Ls Ls' : List (ReverseLayer α)) (A : Set α) (C : Finset α) :
    runReverseLayers M hE κ k (Ls ++ Ls') A C =
      runReverseLayers M hE κ k Ls' (runReverseLayers M hE κ k Ls A C) C := by
  induction Ls generalizing A with
  | nil => rfl
  | cons L Ls ih => exact ih _

omit [Fintype α] [DecidableEq α] in
lemma sourceLayers_pairwise (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) :
    (sourceLayers D S G n).Pairwise (fun L L' => Disjoint L.group L'.group) := by
  rw [sourceLayers, List.pairwise_map]
  exact (List.nodup_range (n := n)).pairwise_of_forall_ne (fun _ _ _ _ hij => hG hij)

omit [DecidableEq α] in
lemma runReverseLayers_source (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (C : Finset α) :
    runReverseLayers M hE κ k (sourceLayers D S G n)
      (if k < 0 then M.closure ∅ else Set.univ) C =
      reversePrefix M hE κ D (fun j => (C : Set α) ∩ (G j : Set α)) S k n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sourceLayers, List.range_succ, List.map_append, List.map_cons, List.map_nil,
      runReverseLayers_append]
    change layerUpdate M hE κ k (sourceLayer D S G n)
      (runReverseLayers M hE κ k (sourceLayers D S G n)
        (if k < 0 then M.closure ∅ else Set.univ) C) C = _
    rw [ih]
    rfl

theorem source_reverse_hybrid_independent (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (V : Finset α) (hV : ∀ j < n, (G j).filter (fun e => e ∈ S j) ⊆ V)
    (q : α → ℝ) (φ : Set α → ℝ) (ψ : Finset α → ℝ) :
    let tree := reverseExposureTree M hE κ k (sourceLayers D S G n)
      (if k < 0 then M.closure ∅ else Set.univ)
    bitsExpectation q V (fun C => bitsExpectation q V (fun T =>
      φ (reversePrefix M hE κ D (fun j => (C : Set α) ∩ (G j : Set α)) S k n) *
        ψ (tree.hybrid C T))) =
      bitsExpectation q V (fun C =>
        φ (reversePrefix M hE κ D (fun j => (C : Set α) ∩ (G j : Set α)) S k n)) *
          bitsExpectation q V ψ := by
  dsimp only
  have hv : ∀ L ∈ sourceLayers D S G n, L.group.filter (fun e => e ∈ L.state) ⊆ V := by
    intro L hL
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hL
    exact hV j (List.mem_range.mp hj)
  have h := reverseExposure_hybrid_independent M hE κ k (sourceLayers D S G n)
    (sourceLayers_pairwise D S G n hG) V hv
      (if k < 0 then M.closure ∅ else Set.univ) q φ ψ
  simpa only [runReverseLayers_source] using h

lemma queriedReverseLayers_congr (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (Ls : List (ReverseLayer α)) (A : Set α) (C C' : Finset α)
    (hC : ∀ L ∈ Ls, ∀ e ∈ L.group, (e ∈ C ↔ e ∈ C')) :
    queriedReverseLayers M hE κ k Ls A C = queriedReverseLayers M hE κ k Ls A C' := by
  induction Ls generalizing A with
  | nil => rfl
  | cons L Ls ih =>
    rw [queriedReverseLayers, queriedReverseLayers,
      layerUpdate_congr M hE κ k L A C C' (hC L (by simp))]
    congr 1
    exact ih _ (fun L' hL' => hC L' (by simp [hL']))

lemma reverseExposureTree_queried (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (Ls : List (ReverseLayer α))
    (hdisj : Ls.Pairwise (fun L L' => Disjoint L.group L'.group))
    (A : Set α) (C : Finset α) :
    (reverseExposureTree M hE κ k Ls A).queried C = queriedReverseLayers M hE κ k Ls A C := by
  induction Ls generalizing A C with
  | nil => rfl
  | cons L Ls ih =>
    rw [List.pairwise_cons] at hdisj
    rw [reverseExposureTree, revealBatch_queried _ (nodup_toList _)]
    simp only [toList_toFinset]
    rw [ih hdisj.2, ← layerUpdate_eq_batch, queriedReverseLayers]
    congr 1
    apply queriedReverseLayers_congr
    intro L' hL' e he
    have heB : e ∉ layerBatch M hE κ k L A := by
      intro hb
      exact Finset.disjoint_left.mp (hdisj.1 L' hL') (mem_filter.mp hb).1 he
    simp [heB]

lemma queriedReverseLayers_append (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (Ls Ls' : List (ReverseLayer α)) (A : Set α) (C : Finset α) :
    queriedReverseLayers M hE κ k (Ls ++ Ls') A C = queriedReverseLayers M hE κ k Ls A C ∪
      queriedReverseLayers M hE κ k Ls' (runReverseLayers M hE κ k Ls A C) C := by
  induction Ls generalizing A with
  | nil => simp [queriedReverseLayers, runReverseLayers]
  | cons L Ls ih =>
    simp only [List.cons_append, queriedReverseLayers, runReverseLayers, ih, union_assoc]

lemma queriedReverseLayers_source (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (C : Finset α) :
    queriedReverseLayers M hE κ k (sourceLayers D S G n)
      (if k < 0 then M.closure ∅ else Set.univ) C =
      (Finset.range n).biUnion (fun j => (G j).filter (fun e => e ∈ S j ∧
        e ∉ reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k j)) := by
  induction n with
  | zero => simp [sourceLayers, queriedReverseLayers]
  | succ n ih =>
    simp only [sourceLayers, List.range_succ, List.map_append, List.map_cons, List.map_nil,
      queriedReverseLayers_append]
    change queriedReverseLayers M hE κ k (sourceLayers D S G n)
        (if k < 0 then M.closure ∅ else Set.univ) C ∪
      (layerBatch M hE κ k (sourceLayer D S G n)
        (runReverseLayers M hE κ k (sourceLayers D S G n)
          (if k < 0 then M.closure ∅ else Set.univ) C) ∪ ∅) = _
    rw [ih, runReverseLayers_source]
    simp only [union_empty, Finset.range_add_one, biUnion_insert]
    rw [union_comm]
    rfl

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Reverse_Hybrid
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

lemma sourceReverseTree_fresh (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (V : Finset α) (hV : ∀ j < n, (G j).filter (fun e => e ∈ S j) ⊆ V) :
    (sourceReverseTree M hE κ k D S G n).Fresh V := by
  apply reverseExposureTree_fresh M hE κ k _ (sourceLayers_pairwise D S G n hG)
  intro L hL
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hL
  exact hV j (List.mem_range.mp hj)

lemma sourceReverseTree_queried (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (C : Finset α) :
    (sourceReverseTree M hE κ k D S G n).queried C =
      (Finset.range n).biUnion (fun j => (G j).filter (fun e => e ∈ S j ∧
        e ∉ reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k j)) := by
  rw [sourceReverseTree, reverseExposureTree_queried M hE κ k _
    (sourceLayers_pairwise D S G n hG), queriedReverseLayers_source]

lemma sourceReverseTree_queried_coordinate (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (C : Finset α)
    {j : ℕ} (hj : j < n) {e : α} (heG : e ∈ G j) (heS : e ∈ S j) :
    e ∈ (sourceReverseTree M hE κ k D S G n).queried C ↔
      e ∉ reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k j := by
  rw [sourceReverseTree_queried M hE κ k D S G n hG, mem_biUnion]
  constructor
  · rintro ⟨i, hi, he⟩
    by_cases hij : i = j
    · subst i; exact (mem_filter.mp he).2.2
    · exact (Finset.disjoint_left.mp (hG hij) (mem_filter.mp he).1 heG).elim
  · intro he
    exact ⟨j, mem_range.mpr hj, mem_filter.mpr ⟨heG, heS, he⟩⟩

lemma sourceReverseTree_hybrid_coordinate (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (V : Finset α) (hV : ∀ j < n, (G j).filter (fun e => e ∈ S j) ⊆ V)
    (C T : Finset α) (hC : C ⊆ V) (hT : T ⊆ V)
    {j : ℕ} (hj : j < n) {e : α} (heG : e ∈ G j) (heS : e ∈ S j) :
    e ∈ (sourceReverseTree M hE κ k D S G n).hybrid C T ↔
      (e ∈ C ∧ e ∈ reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k j) ∨
      (e ∈ T ∧ e ∉ reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k j) := by
  rw [(sourceReverseTree M hE κ k D S G n).hybrid_eq_resample V C T
    (sourceReverseTree_fresh M hE κ k D S G n hG V hV) hC hT]
  simp only [mem_union, mem_sdiff, mem_inter,
    sourceReverseTree_queried_coordinate M hE κ k D S G n hG C hj heG heS, not_not]

lemma sourceReverseTree_hybrid_guard (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (V : Finset α) (hV : ∀ j < n, (G j).filter (fun e => e ∈ S j) ⊆ V)
    (C T : Finset α) (hC : C ⊆ V) (hT : T ⊆ V) {j : ℕ} (hj : j < n) :
    (((sourceReverseTree M hE κ k D S G n).hybrid C T : Set α) ∩ (G j : Set α)) ∩ S j =
      transitionHybrid M hE κ k D S G C T j ∩ S j := by
  ext e
  by_cases heG : e ∈ G j
  · by_cases heS : e ∈ S j
    · have hh := sourceReverseTree_hybrid_coordinate M hE κ k D S G n hG V hV C T hC hT hj heG heS
      simp only [transitionHybrid, Set.mem_inter_iff, Set.mem_union, Set.mem_sdiff,
        mem_coe, heG, heS, and_true, true_and]
      exact hh
    · simp [transitionHybrid, heS]
  · simp [transitionHybrid, heG]

omit [DecidableEq α] in
lemma reversePrefix_congr_guard_inter (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C C' S : ℕ → Set α) (k : ℤ) (n : ℕ)
    (hC : ∀ j < n, C j ∩ S j = C' j ∩ S j) :
    reversePrefix M hE κ D C S k n = reversePrefix M hE κ D C' S k n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [reversePrefix, reversePrefix, ih (fun j hj => hC j (by omega)), hC n (by omega)]

lemma sourceReverseTree_hybrid_output (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (V : Finset α) (hV : ∀ j < n, (G j).filter (fun e => e ∈ S j) ⊆ V)
    (C T : Finset α) (hC : C ⊆ V) (hT : T ⊆ V) :
    reverseNominal M hE κ D
      (fun j => (((sourceReverseTree M hE κ k D S G n).hybrid C T : Set α) ∩ (G j : Set α))) S k n =
    reverseNominal M hE κ D (transitionHybrid M hE κ k D S G C T) S k n := by
  unfold reverseNominal
  congr 1
  exact reversePrefix_congr_guard_inter M hE κ D _ _ S k n
    (fun j hj => sourceReverseTree_hybrid_guard M hE κ k D S G n hG V hV C T hC hT hj)

theorem reverse_double_exit (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (V : Finset α) (hV : ∀ j < n, (G j).filter (fun e => e ∈ S j) ⊆ V)
    (q : α → ℝ) (d : α) :
    bitsExpectation q V (fun C => bitsExpectation q V (fun T =>
      (if d ∉ reverseNominal M hE κ D (fun j => (C : Set α) ∩ (G j : Set α)) S k n then 1 else 0) *
      (if d ∉ reverseNominal M hE κ D (transitionHybrid M hE κ k D S G C T) S k n then 1 else 0))) =
      (bitsExpectation q V (fun C =>
        if d ∉ reverseNominal M hE κ D (fun j => (C : Set α) ∩ (G j : Set α)) S k n then 1 else 0)) ^ 2 := by
  let φ : Set α → ℝ := fun A => if d ∉ densityEnabled M hE κ (D n) (activation n) k A then 1 else 0
  let ψ : Finset α → ℝ := fun C =>
    if d ∉ reverseNominal M hE κ D (fun j => (C : Set α) ∩ (G j : Set α)) S k n then 1 else 0
  have hi := source_reverse_hybrid_independent M hE κ k D S G n hG V hV q φ ψ
  change bitsExpectation q V (fun C => bitsExpectation q V (fun T =>
    ψ C * (if d ∉ reverseNominal M hE κ D (transitionHybrid M hE κ k D S G C T) S k n then 1 else 0))) =
      (bitsExpectation q V ψ)^2
  have heq : bitsExpectation q V (fun C => bitsExpectation q V (fun T =>
      ψ C * (if d ∉ reverseNominal M hE κ D (transitionHybrid M hE κ k D S G C T) S k n then 1 else 0))) =
      bitsExpectation q V (fun C => bitsExpectation q V (fun T =>
        ψ C * ψ ((sourceReverseTree M hE κ k D S G n).hybrid C T))) := by
    apply bitsExpectation_congr
    intro C hC
    apply bitsExpectation_congr
    intro T hT
    dsimp only [ψ]
    rw [sourceReverseTree_hybrid_output M hE κ k D S G n hG V hV C T hC hT]
  rw [heq]
  change bitsExpectation q V (fun C => bitsExpectation q V (fun T =>
    φ (reversePrefix M hE κ D (fun j => (C : Set α) ∩ (G j : Set α)) S k n) *
      ψ ((sourceReverseTree M hE κ k D S G n).hybrid C T))) = _
  unfold sourceReverseTree
  rw [hi]
  change bitsExpectation q V ψ * bitsExpectation q V ψ = _
  ring

lemma sourceReverseTree_queried_coordinate_full (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (C : Finset α)
    {j : ℕ} (hj : j < n) {e : α} (heG : e ∈ G j) :
    e ∈ (sourceReverseTree M hE κ k D S G n).queried C ↔
      e ∈ S j ∧ e ∉ reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k j := by
  rw [sourceReverseTree_queried M hE κ k D S G n hG, mem_biUnion]
  constructor
  · rintro ⟨i, hi, he⟩
    by_cases hij : i = j
    · subst i; exact (mem_filter.mp he).2
    · exact (Finset.disjoint_left.mp (hG hij) (mem_filter.mp he).1 heG).elim
  · intro he
    exact ⟨j, mem_range.mpr hj, mem_filter.mpr ⟨heG, he⟩⟩

lemma sourceReverseTree_positive_guards (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (C : Finset α)
    {j : ℕ} (hj : j < n) :
    ((C ∩ (sourceReverseTree M hE κ k D S G n).queried C : Finset α) : Set α) ∩ (G j : Set α) =
      departingGuards M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k j := by
  ext e
  by_cases heG : e ∈ G j
  · have hq := sourceReverseTree_queried_coordinate_full M hE κ k D S G n hG C hj heG
    simp only [departingGuards, Set.mem_inter_iff, Set.mem_sdiff, mem_coe, mem_inter, heG, and_true]
    rw [hq]
  · simp [departingGuards, heG]

lemma sourceReverseTree_positive_nominal (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (C : Finset α)
    {j : ℕ} (hj : j ≤ n) :
    reverseNominal M hE κ D
      (fun i => ((C ∩ (sourceReverseTree M hE κ k D S G n).queried C : Finset α) : Set α) ∩ (G i : Set α))
      S k j = reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k j := by
  calc
    _ = reverseNominal M hE κ D
        (departingGuards M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k) S k j := by
      apply reverseNominal_congr_before
      · intro i hi
        exact sourceReverseTree_positive_guards M hE κ k D S G n hG C (by omega)
      · exact fun _ _ => rfl
    _ = _ := reverseNominal_departing_only M hE κ D _ S k j

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Reverse_Iteration
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

omit [DecidableEq α] in
lemma reversePrefix_flat (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C S : ℕ → Set α) (k : ℤ) (j : ℕ) :
    M.IsFlat (reversePrefix M hE κ D C S k j) := by
  cases j with
  | zero =>
    by_cases hk : k < 0
    · simpa only [reversePrefix, ite_eq_left hk] using Matroid.isFlat_closure (M := M) ∅
    · simpa only [reversePrefix, ite_eq_right hk, ← hE] using M.ground_isFlat
  | succ j => exact Matroid.isFlat_closure (M := M) _

omit [DecidableEq α] in
lemma reverseNominal_flat (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C S : ℕ → Set α) (k : ℤ) (j : ℕ) :
    M.IsFlat (reverseNominal M hE κ D C S k j) :=
  densityEnabled_flat M hE κ (D j) (activation j) k (reversePrefix_flat M hE κ D C S k j)

omit [DecidableEq α] in

lemma reversePrefix_into_output (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C B S : ℕ → Set α) {l k : ℤ} (hlk : l ≤ k) (j : ℕ) :
    reversePrefix M hE κ D B (fun i => reverseNominal M hE κ D C S k i) l j ⊆
      reversePrefix M hE κ D C S k j := by
  induction j with
  | zero => exact guardedPath_mono M hE κ D C 0 hlk
  | succ j ih =>
    have hn := densityEnabled_mono M hE κ (D j) (activation j) hlk ih
    have hs : reversePrefix M hE κ D B (fun i => reverseNominal M hE κ D C S k i) l (j+1) ⊆
        reverseNominal M hE κ D C S k j := by
      exact (M.closure_subset_closure (Set.union_subset hn Set.inter_subset_right)).trans_eq
        (reverseNominal_flat M hE κ D C S k j).closure
    exact hs.trans (Set.subset_union_left.trans (M.subset_closure _ (by simp [hE])))

omit [DecidableEq α] in
lemma reverseNominal_into_output (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C B S : ℕ → Set α) {l k : ℤ} (hlk : l ≤ k) (j : ℕ) :
    reverseNominal M hE κ D B (fun i => reverseNominal M hE κ D C S k i) l j ⊆
      reverseNominal M hE κ D C S k j :=
  densityEnabled_mono M hE κ (D j) (activation j) hlk
    (reversePrefix_into_output M hE κ D C B S hlk j)

omit [DecidableEq α] in
lemma reverseClosed_univ (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (k : ℤ) :
    ReverseClosed M hE κ D k (fun _ => Set.univ) := fun _ _ => Set.subset_univ _

lemma reverseStepTree_run (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (C : Finset α) :
    (reverseStepTree M hE κ k D S G n).run C =
      (fun j => reverseNominal M hE κ D
        (fun i => ((C ∩ (sourceReverseTree M hE κ k D S G n).queried C : Finset α) : Set α) ∩ (G i : Set α)) S k j) := by
  rw [reverseStepTree, RevealTree.run_map, RevealTree.record_run]

lemma reverseStepTree_run_coordinate (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (C : Finset α) {j : ℕ} (hj : j ≤ n) :
    (reverseStepTree M hE κ k D S G n).run C j =
      reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k j := by
  rw [reverseStepTree_run]
  exact sourceReverseTree_positive_nominal M hE κ k D S G n hG C hj

lemma reverseStepTree_fresh (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (V : Finset α) (hV : ∀ j < n, (G j).filter (fun e => e ∈ S j) ⊆ V) :
    (reverseStepTree M hE κ k D S G n).Fresh V := by
  rw [reverseStepTree, RevealTree.fresh_map, RevealTree.record_fresh]
  exact sourceReverseTree_fresh M hE κ k D S G n hG V hV

lemma reverseStepTree_queried (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (C : Finset α) :
    (reverseStepTree M hE κ k D S G n).queried C =
      (sourceReverseTree M hE κ k D S G n).queried C := by
  rw [reverseStepTree, RevealTree.queried_map, RevealTree.record_queried]

lemma reverseStepTree_closed (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (C : Finset α) :
    ReverseClosed M hE κ D (k-1) ((reverseStepTree M hE κ k D S G n).run C) := by
  rw [reverseStepTree_run]
  intro B j
  exact reverseNominal_into_output M hE κ D _ B S (by omega) j

lemma reverseStepTree_remaining (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (V : Finset α) (hV : ∀ j < n, (G j).filter (fun e => e ∈ S j) ⊆ V)
    (closed : ReverseClosed M hE κ D k S) (C : Finset α) :
    ∀ j < n, (G j).filter (fun e => e ∈ (reverseStepTree M hE κ k D S G n).run C j) ⊆
      V \ (reverseStepTree M hE κ k D S G n).queried C := by
  intro j hj e he
  rcases mem_filter.mp he with ⟨heG, heN⟩
  rw [reverseStepTree_run_coordinate M hE κ k D S G n hG C hj.le] at heN
  refine mem_sdiff.mpr ⟨hV j hj (mem_filter.mpr ⟨heG, closed _ j heN⟩), ?_⟩
  rw [reverseStepTree_queried,
    sourceReverseTree_queried_coordinate_full M hE κ k D S G n hG C hj heG]
  exact fun h => h.2 heN

lemma reverseTransactions_fresh (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (stop : ℤ → (ℕ → Set α) → Prop) (m : ℕ) (k : ℤ) (S : ℕ → Set α)
    (V : Finset α) (hV : ∀ j < n, (G j).filter (fun e => e ∈ S j) ⊆ V)
    (closed : ReverseClosed M hE κ D k S) :
    (reverseTransactions M hE κ D G n stop m k S).Fresh V := by
  induction m generalizing k S V with
  | zero => trivial
  | succ m ih =>
    rw [reverseTransactions]
    split_ifs with hs
    · trivial
    · apply RevealTree.transaction_fresh _ _ V (reverseStepTree_fresh M hE κ k D S G n hG V hV)
      intro C hC
      exact ih (k-1) _ _ (reverseStepTree_remaining M hE κ k D S G n hG V hV closed C)
        (reverseStepTree_closed M hE κ k D S G n C)

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Reverse_Certificates
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

lemma reverseStepTree_contracts (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (closed : ReverseClosed M hE κ D k S) (C : Finset α) (j : ℕ) :
    (reverseStepTree M hE κ k D S G n).run C j ⊆ S j := by
  rw [reverseStepTree_run]
  exact closed _ j

omit [DecidableEq α] in
lemma reverseStayEvent_mono (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D S : ℕ → Set α) (G : ℕ → Finset α) (k : ℤ) (d : α) (h : ℕ) :
    Monotone (reverseStayEvent M hE κ D S G k d h) := by
  intro C C' hCC' he
  exact reverseNominal_mono M hE κ D _ _ S S le_rfl
    (fun j => Set.inter_subset_inter_left _ hCC') (fun _ => Set.Subset.rfl) h he

lemma reverseStepTree_nonexit_certificate (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D S S₀ : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    {k k₀ : ℤ} (hk : k ≤ k₀) (hS : ∀ j, S j ⊆ S₀ j)
    (C : Finset α) (d : α) (h : ℕ)
    (he : d ∈ (reverseStepTree M hE κ k D S G n).run C h) :
    reverseStayEvent M hE κ D S₀ G k₀ d h
      (C ∩ (reverseStepTree M hE κ k D S G n).queried C) := by
  rw [reverseStepTree_run] at he
  rw [reverseStepTree_queried]
  exact reverseNominal_mono M hE κ D _ _ S S₀ hk
    (fun _ => Set.Subset.rfl) hS h he

lemma reverseNonexitCount_le_transactions (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (stop : ℤ → (ℕ → Set α) → Prop) (d : α) (h : ℕ)
    (S₀ : ℕ → Set α) (k₀ : ℤ) (m : ℕ) (k : ℤ) (S : ℕ → Set α)
    (hk : k ≤ k₀) (hS : ∀ j, S j ⊆ S₀ j) (closed : ReverseClosed M hE κ D k S)
    (C : Finset α) :
    reverseNonexitCount M hE κ D G n stop d h m k S C ≤
      (reverseTransactions M hE κ D G n stop m k S).run
        (reverseStayEvent M hE κ D S₀ G k₀ d h) C ∅ := by
  induction m generalizing k S with
  | zero => simp [reverseNonexitCount, reverseTransactions, QueryProgram.run]
  | succ m ih =>
    rw [reverseNonexitCount, reverseTransactions]
    by_cases hs : stop k S
    · simp only [ite_eq_left hs, QueryProgram.run, le_refl]
    · simp only [ite_eq_right hs]
      rw [RevealTree.transaction_run _ _ univ
        (reverseStepTree_fresh M hE κ k D S G n hG univ (fun _ _ => subset_univ _))]
      simp only [empty_union]
      apply add_le_add
      · by_cases he : d ∈ (reverseStepTree M hE κ k D S G n).run C h
        · rw [ite_eq_left he, ite_eq_left (reverseStepTree_nonexit_certificate M hE κ D S S₀ G n hk hS C d h he)]
        · rw [ite_eq_right he]
          split_ifs <;> norm_num
      · exact ih (k-1) _ (by omega)
          (fun j => (reverseStepTree_contracts M hE κ k D S G n closed C j).trans (hS j))
          (reverseStepTree_closed M hE κ k D S G n C)

theorem reverse_nonexit_budget (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (stop : ℤ → (ℕ → Set α) → Prop) (d : α) (h : ℕ)
    (m : ℕ) (k₀ : ℤ) (S₀ : ℕ → Set α) (closed : ReverseClosed M hE κ D k₀ S₀)
    (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (hδ : 0 < bitsFailure (reverseStayEvent M hE κ D S₀ G k₀ d h) q univ ∅) :
    bitsExpectation q univ (reverseNonexitCount M hE κ D G n stop d h m k₀ S₀) ≤
      Real.log (1 / bitsFailure (reverseStayEvent M hE κ D S₀ G k₀ d h) q univ ∅) := by
  apply le_trans (bitsExpectation_mono q hq0 hq1 univ
    (fun C _ => reverseNonexitCount_le_transactions M hE κ D G n hG stop d h S₀ k₀ m k₀ S₀
      le_rfl (fun _ => Set.Subset.rfl) closed C))
  exact disjoint_query_certificates_product _ (reverseStayEvent_mono M hE κ D S₀ G k₀ d h)
    q hq0 hq1 hδ _ (reverseTransactions_fresh M hE κ D G n hG stop m k₀ S₀ univ
      (fun _ _ => subset_univ _) closed)

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Reverse_Cost
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

lemma reverseCost_congr (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (cost : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S)
    (C C' : Finset α)
    (agree : ∀ j < n, ∀ e ∈ G j, e ∈ S j → (e ∈ C ↔ e ∈ C')) :
    reverseCost M hE κ D G n cost m k S C = reverseCost M hE κ D G n cost m k S C' := by
  induction m generalizing k S with
  | zero => rfl
  | succ m ih =>
    let V := (range n).biUnion (fun j => (G j).filter (fun e => e ∈ S j))
    have hV : ∀ j < n, (G j).filter (fun e => e ∈ S j) ⊆ V := by
      intro j hj e he
      exact mem_biUnion.mpr ⟨j, mem_range.mpr hj, he⟩
    have ha : ∀ e ∈ V, (e ∈ C ↔ e ∈ C') := by
      intro e he
      obtain ⟨j, hj, hje⟩ := mem_biUnion.mp he
      exact agree j (mem_range.mp hj) e (mem_filter.mp hje).1 (mem_filter.mp hje).2
    have hs := (reverseStepTree M hE κ k D S G n).run_congr V C C'
      (reverseStepTree_fresh M hE κ k D S G n hG V hV) ha
    simp only [reverseCost, hs]
    congr 1
    apply ih (k-1) _ (reverseStepTree_closed M hE κ k D S G n C')
    intro j hj e heG heS
    exact agree j hj e heG (reverseStepTree_contracts M hE κ k D S G n closed C' j heS)

lemma reverseCost_add (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (f g : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (C : Finset α) :
    reverseCost M hE κ D G n (fun k S S' => f k S S' + g k S S') m k S C =
      reverseCost M hE κ D G n f m k S C + reverseCost M hE κ D G n g m k S C := by
  induction m generalizing k S with
  | zero => simp [reverseCost]
  | succ m ih => simp only [reverseCost, ih]; ring

lemma reverseCost_mul (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (f : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ) (a : ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (C : Finset α) :
    reverseCost M hE κ D G n (fun k S S' => a * f k S S') m k S C =
      a * reverseCost M hE κ D G n f m k S C := by
  induction m generalizing k S with
  | zero => simp [reverseCost]
  | succ m ih => simp only [reverseCost, ih]; ring

lemma reverseCost_mono (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (f g : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (hfg : ∀ k S S', f k S S' ≤ g k S S')
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (C : Finset α) :
    reverseCost M hE κ D G n f m k S C ≤ reverseCost M hE κ D G n g m k S C := by
  induction m generalizing k S with
  | zero => exact le_rfl
  | succ m ih => exact add_le_add (hfg _ _ _) (ih _ _)

lemma reverseCost_erase_step (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (cost : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) (C : Finset α) :
    reverseCost M hE κ D G n cost m (k-1) ((reverseStepTree M hE κ k D S G n).run C) C =
      reverseCost M hE κ D G n cost m (k-1) ((reverseStepTree M hE κ k D S G n).run C)
        (C \ (reverseStepTree M hE κ k D S G n).queried C) := by
  apply reverseCost_congr M hE κ D G n hG cost m (k-1) _
    (reverseStepTree_closed M hE κ k D S G n C)
  intro j hj e heG heS
  have he := reverseStepTree_remaining M hE κ k D S G n hG univ
    (fun _ _ => subset_univ _) closed C j hj (mem_filter.mpr ⟨heG, heS⟩)
  simp only [mem_sdiff, (mem_sdiff.mp he).2, not_false_eq_true, and_true]

theorem reverseMeanCost_succ (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (cost : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) :
    reverseMeanCost M hE κ D G n q cost (m+1) k S =
      bitsExpectation q univ (fun C => cost k S ((reverseStepTree M hE κ k D S G n).run C) +
        reverseMeanCost M hE κ D G n q cost m (k-1) ((reverseStepTree M hE κ k D S G n).run C)) := by
  let tree := reverseStepTree M hE κ k D S G n
  let f := fun (S' : ℕ → Set α) (C : Finset α) => reverseCost M hE κ D G n cost m (k-1) S' C
  have hfresh : tree.Fresh univ := reverseStepTree_fresh M hE κ k D S G n hG univ
    (fun _ _ => subset_univ _)
  have herase : bitsExpectation q univ (fun C => f (tree.run C) C) =
      bitsExpectation q univ (fun C => f (tree.run C) (C \ tree.queried C)) := by
    apply bitsExpectation_congr
    intro C hC
    exact reverseCost_erase_step M hE κ D G n hG cost m k S closed C
  have hrestrict : bitsExpectation q univ (fun C => bitsExpectation q (univ \ tree.queried C)
      (f (tree.run C))) = bitsExpectation q univ (fun C => bitsExpectation q univ (f (tree.run C))) := by
    apply bitsExpectation_congr
    intro C hC
    symm
    apply bitsExpectation_restrict q univ _ (subset_univ _) (f (tree.run C))
    intro T T' hT
    apply reverseCost_congr M hE κ D G n hG cost m (k-1) _
      (reverseStepTree_closed M hE κ k D S G n C)
    intro j hj e heG heS
    exact hT e (reverseStepTree_remaining M hE κ k D S G n hG univ
      (fun _ _ => subset_univ _) closed C j hj (mem_filter.mpr ⟨heG, heS⟩))
  have htower := tree.continuation_expectation q univ hfresh f
  change bitsExpectation q univ (fun C => cost k S (tree.run C) + f (tree.run C) C) =
    bitsExpectation q univ (fun C => cost k S (tree.run C) + bitsExpectation q univ (f (tree.run C)))
  rw [bitsExpectation_add, bitsExpectation_add, herase, htower, hrestrict]

@[simp] lemma reverseMeanCost_zero (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ)
    (cost : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ) (k : ℤ) (S : ℕ → Set α) :
    reverseMeanCost M hE κ D G n q cost 0 k S = 0 := by
  simp only [reverseMeanCost, reverseCost, bitsExpectation_const]

lemma reverseMeanCost_add (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ)
    (f g : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) :
    reverseMeanCost M hE κ D G n q (fun k S S' => f k S S' + g k S S') m k S =
      reverseMeanCost M hE κ D G n q f m k S + reverseMeanCost M hE κ D G n q g m k S := by
  unfold reverseMeanCost
  rw [← bitsExpectation_add]
  exact bitsExpectation_congr q univ (fun C _ => reverseCost_add M hE κ D G n f g m k S C)

lemma reverseMeanCost_mul (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ)
    (f : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ) (a : ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) :
    reverseMeanCost M hE κ D G n q (fun k S S' => a * f k S S') m k S =
      a * reverseMeanCost M hE κ D G n q f m k S := by
  unfold reverseMeanCost
  rw [← bitsExpectation_mul_left]
  exact bitsExpectation_congr q univ (fun C _ => reverseCost_mul M hE κ D G n f a m k S C)

theorem reverseMeanCost_le_of_step (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (f g : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (hfg : ∀ k S, ReverseClosed M hE κ D k S →
      bitsExpectation q univ (fun C => f k S ((reverseStepTree M hE κ k D S G n).run C)) ≤
      bitsExpectation q univ (fun C => g k S ((reverseStepTree M hE κ k D S G n).run C)))
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) :
    reverseMeanCost M hE κ D G n q f m k S ≤ reverseMeanCost M hE κ D G n q g m k S := by
  induction m generalizing k S with
  | zero => simp only [reverseMeanCost_zero, le_refl]
  | succ m ih =>
    rw [reverseMeanCost_succ M hE κ D G n hG q f m k S closed,
      reverseMeanCost_succ M hE κ D G n hG q g m k S closed,
      bitsExpectation_add, bitsExpectation_add]
    apply add_le_add (hfg k S closed)
    apply bitsExpectation_mono q hq0 hq1
    intro C hC
    exact ih (k-1) _ (reverseStepTree_closed M hE κ k D S G n C)

theorem reverseMeanCost_eq_of_step (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (f g : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (hfg : ∀ k S, ReverseClosed M hE κ D k S →
      bitsExpectation q univ (fun C => f k S ((reverseStepTree M hE κ k D S G n).run C)) =
      bitsExpectation q univ (fun C => g k S ((reverseStepTree M hE κ k D S G n).run C)))
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) :
    reverseMeanCost M hE κ D G n q f m k S = reverseMeanCost M hE κ D G n q g m k S :=
  le_antisymm (reverseMeanCost_le_of_step M hE κ D G n hG q hq0 hq1 f g
    (fun k S hS => (hfg k S hS).le) m k S closed)
    (reverseMeanCost_le_of_step M hE κ D G n hG q hq0 hq1 g f
    (fun k S hS => (hfg k S hS).ge) m k S closed)

lemma reverseCost_sum {ι : Type*} (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (I : Finset ι) (f : ι → ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (C : Finset α) :
    reverseCost M hE κ D G n (fun k S S' => ∑ i ∈ I, f i k S S') m k S C =
      ∑ i ∈ I, reverseCost M hE κ D G n (f i) m k S C := by
  induction m generalizing k S with
  | zero => simp only [reverseCost, sum_const_zero]
  | succ m ih => simp only [reverseCost, ih, sum_add_distrib]

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Reverse_Hazard
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

lemma reverseHazard_eq (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ) (d : α) (h : ℕ)
    (k : ℤ) (S : ℕ → Set α) :
    reverseHazard M hE κ D G q d h k S = bitsExpectation q univ (fun C =>
      if d ∉ reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k h then 1 else 0) := by
  unfold reverseHazard bitsFailure reverseStayEvent
  apply bitsExpectation_congr
  intro C hC
  simp only [empty_union]
  split_ifs <;> simp_all

lemma reverseHazard_nonneg (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) (d : α) (h : ℕ)
    (k : ℤ) (S : ℕ → Set α) : 0 ≤ reverseHazard M hE κ D G q d h k S :=
  bitsFailure_nonneg _ q hq0 hq1 _ _

lemma reverseHazard_mono (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) (d : α) (h : ℕ)
    {k l : ℤ} (hlk : l ≤ k) (S S' : ℕ → Set α) (hS : ∀ j, S' j ⊆ S j) :
    reverseHazard M hE κ D G q d h k S ≤ reverseHazard M hE κ D G q d h l S' := by
  rw [reverseHazard_eq, reverseHazard_eq]
  apply bitsExpectation_mono q hq0 hq1
  intro C hC
  have hn := reverseNominal_mono M hE κ D
    (fun i => (C : Set α) ∩ (G i : Set α)) _ S' S hlk (fun _ => Set.Subset.rfl) hS h
  by_cases he : d ∈ reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S' l h
  · simp [he, hn he]
  · simp [he]
    split_ifs <;> norm_num

lemma reverseHazard_step_mono (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) (d : α) (h : ℕ)
    (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) (C : Finset α) :
    reverseHazard M hE κ D G q d h k S ≤
      reverseHazard M hE κ D G q d h (k-1) ((reverseStepTree M hE κ k D S G n).run C) :=
  reverseHazard_mono M hE κ D G q hq0 hq1 d h (by omega) S _
    (reverseStepTree_contracts M hE κ k D S G n closed C)

lemma reverseHazard_eq_step (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ) (d : α) (h : ℕ) (hh : h ≤ n)
    (k : ℤ) (S : ℕ → Set α) :
    reverseHazard M hE κ D G q d h k S = bitsExpectation q univ (fun C =>
      if d ∉ (reverseStepTree M hE κ k D S G n).run C h then 1 else 0) := by
  rw [reverseHazard_eq]
  apply bitsExpectation_congr
  intro C hC
  rw [reverseStepTree_run_coordinate M hE κ k D S G n hG C hh]

lemma bandNonexitCost_zero_above (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) (d : α) (h : ℕ) (p₀ upper : ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S)
    (hu : upper ≤ reverseHazard M hE κ D G q d h k S) (C : Finset α) :
    reverseCost M hE κ D G n (bandNonexitCost M hE κ D G q d h p₀ upper) m k S C = 0 := by
  induction m generalizing k S with
  | zero => rfl
  | succ m ih =>
    rw [reverseCost, bandNonexitCost, ite_eq_right (fun hc => (not_lt_of_ge hu) hc.2.1)]
    have hm := reverseHazard_step_mono M hE κ D G n q hq0 hq1 d h k S closed C
    rw [ih (k-1) _ (reverseStepTree_closed M hE κ k D S G n C) (hu.trans hm)]
    exact zero_add 0

lemma bandNonexitCost_eq_count (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) (d : α) (h : ℕ) (p₀ upper : ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S)
    (hl : p₀ ≤ reverseHazard M hE κ D G q d h k S) (C : Finset α) :
    reverseCost M hE κ D G n (bandNonexitCost M hE κ D G q d h p₀ upper) m k S C =
      reverseNonexitCount M hE κ D G n
        (fun k S => upper ≤ reverseHazard M hE κ D G q d h k S) d h m k S C := by
  induction m generalizing k S with
  | zero => rfl
  | succ m ih =>
    by_cases hu : upper ≤ reverseHazard M hE κ D G q d h k S
    · rw [bandNonexitCost_zero_above M hE κ D G n q hq0 hq1 d h p₀ upper (m+1) k S closed hu C,
        reverseNonexitCount, ite_eq_left hu]
    · have hlt := lt_of_not_ge hu
      rw [reverseCost, reverseNonexitCount, ite_eq_right hu]
      simp only [bandNonexitCost, hl, hlt, true_and]
      congr 1
      exact ih (k-1) _ (reverseStepTree_closed M hE κ k D S G n C)
        (hl.trans (reverseHazard_step_mono M hE κ D G n q hq0 hq1 d h k S closed C))

theorem bandNonexitCost_budget_after_entry (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) (d : α) (h : ℕ) (p₀ upper : ℝ)
    (hp : 0 < p₀) (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S)
    (hl : p₀ ≤ reverseHazard M hE κ D G q d h k S) :
    reverseMeanCost M hE κ D G n q (bandNonexitCost M hE κ D G q d h p₀ upper) m k S ≤
      Real.log (1 / p₀) := by
  unfold reverseMeanCost
  have heq : bitsExpectation q univ
      (reverseCost M hE κ D G n (bandNonexitCost M hE κ D G q d h p₀ upper) m k S) =
      bitsExpectation q univ (reverseNonexitCount M hE κ D G n
        (fun k S => upper ≤ reverseHazard M hE κ D G q d h k S) d h m k S) := by
    apply bitsExpectation_congr
    intro C hC
    exact bandNonexitCost_eq_count M hE κ D G n q hq0 hq1 d h p₀ upper m k S closed hl C
  rw [heq]
  apply (reverse_nonexit_budget M hE κ D G n hG _ d h m k S closed q hq0 hq1 (hp.trans_le hl)).trans
  apply Real.log_le_log
  · exact one_div_pos.mpr (hp.trans_le hl)
  · exact one_div_le_one_div_of_le hp hl

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Reverse_Trace
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

lemma reverseCost_le_of_trace (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (f g : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (C : Finset α)
    (hfg : ∀ t ∈ reverseTrace M hE κ D G n m k S C,
      f t.time t.before t.after ≤ g t.time t.before t.after) :
    reverseCost M hE κ D G n f m k S C ≤ reverseCost M hE κ D G n g m k S C := by
  induction m generalizing k S with
  | zero => exact le_rfl
  | succ m ih =>
    rw [reverseCost, reverseCost]
    apply add_le_add (hfg ⟨k, S, (reverseStepTree M hE κ k D S G n).run C⟩ (by simp [reverseTrace]))
    exact ih _ _ (fun t ht => hfg t (by simp only [reverseTrace, List.mem_cons]; exact Or.inr ht))

lemma mem_traceHazards (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ) (d : α) (h : ℕ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (C : Finset α) (t : ReverseTransition α)
    (ht : t ∈ reverseTrace M hE κ D G n m k S C) :
    reverseHazard M hE κ D G q d h t.time t.before ∈ traceHazards M hE κ D G n q d h m k S := by
  exact mem_biUnion.mpr ⟨C, mem_univ C, List.mem_toFinset.mpr (List.mem_map.mpr ⟨t, ht, rfl⟩)⟩

lemma reverseStepTree_path (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (k : ℤ) (S : ℕ → Set α) (C : Finset α)
    (hS : ∀ j ≤ n, S j = nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j (k+1))
    {j : ℕ} (hj : j ≤ n) :
    (reverseStepTree M hE κ k D S G n).run C j =
      nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j k := by
  rw [reverseStepTree_run_coordinate M hE κ k D S G n hG C hj]
  calc
    _ = reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α))
        (fun i => nominalPath M hE κ D (fun l => (C : Set α) ∩ (G l : Set α)) i (k+1)) k j := by
      apply reverseNominal_congr_before
      · intro i hi; rfl
      · intro i hi; exact hS i (by omega)
    _ = _ := reverseNominal_agrees M hE κ D _ k j

lemma reverseFinal_path (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (C : Finset α)
    (hS : ∀ j ≤ n, S j = nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j (k+1))
    {j : ℕ} (hj : j ≤ n) :
    reverseFinal M hE κ D G n m k S C j =
      nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j (k+1-m) := by
  induction m generalizing k S with
  | zero => simpa only [reverseFinal, Nat.cast_zero, sub_zero] using hS j hj
  | succ m ih =>
    rw [reverseFinal]
    have hs' : ∀ i ≤ n, (reverseStepTree M hE κ k D S G n).run C i =
        nominalPath M hE κ D (fun l => (C : Set α) ∩ (G l : Set α)) i (k-1+1) := by
      intro i hi
      simpa only [sub_add_cancel] using reverseStepTree_path M hE κ D G n hG k S C hS hi
    rw [ih (k-1) _ hs']
    congr 1
    omega

lemma reverseFinal_from_univ (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (h : ℕ) (hh : h ≤ n) (C : Finset α) :
    reverseFinal M hE κ D G n (pathHorizon h + 1) (-1) (fun _ => Set.univ) C h = M.closure ∅ := by
  rw [reverseFinal_path M hE κ D G n hG (pathHorizon h+1) (-1) (fun _ => Set.univ) C
    (fun j hj => by simpa only [neg_add_cancel] using
      (nominalPath_nonnegative M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j (by omega : (0:ℤ) ≤ -1+1)).symm) hh]
  apply nominalPath_early
  unfold pathHorizon activation
  omega

lemma reverseCost_exit_telescope (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (d : α) (h : ℕ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) (C : Finset α) :
    reverseCost M hE κ D G n (exitCost d h) m k S C =
      (if d ∈ S h then 1 else 0) - (if d ∈ reverseFinal M hE κ D G n m k S C h then 1 else 0) := by
  induction m generalizing k S with
  | zero => by_cases hs : d ∈ S h <;> simp [reverseCost, reverseFinal, hs]
  | succ m ih =>
    rw [reverseCost, reverseFinal, ih (k-1) _ (reverseStepTree_closed M hE κ k D S G n C)]
    have hc := reverseStepTree_contracts M hE κ k D S G n closed C h
    by_cases hs : d ∈ S h <;> by_cases hn : d ∈ (reverseStepTree M hE κ k D S G n).run C h
    · simp [exitCost, hs, hn]
    · simp [exitCost, hs, hn]; ring
    · exact (hs (hc hn)).elim
    · simp [exitCost, hs, hn]

lemma reverse_exit_total_one (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (d : α) (hd : d ∉ M.closure ∅) (h : ℕ) (hh : h ≤ n) :
    reverseMeanCost M hE κ D G n q (exitCost d h) (pathHorizon h+1) (-1) (fun _ => Set.univ) = 1 := by
  unfold reverseMeanCost
  have hp : ∀ C : Finset α, reverseCost M hE κ D G n (exitCost d h)
      (pathHorizon h+1) (-1) (fun _ => Set.univ) C = 1 := by
    intro C
    rw [reverseCost_exit_telescope M hE κ D G n d h (pathHorizon h+1) (-1) _
      (reverseClosed_univ M hE κ D (-1)) C, reverseFinal_from_univ M hE κ D G n hG h hh C]
    simp [hd]
  exact (bitsExpectation_congr q univ (fun C _ => hp C)).trans (bitsExpectation_const q univ 1)

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Reverse_PrefixTree
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

lemma reversePrefixTree_fresh (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (V : Finset α)
    (hV : ∀ j < n, (G j).filter (fun e => e ∈ S j) ⊆ V)
    (closed : ReverseClosed M hE κ D k S) :
    (reversePrefixTree M hE κ D G n m k S).Fresh V := by
  induction m generalizing k S V with
  | zero => trivial
  | succ m ih =>
    apply RevealTree.fresh_bind _ _ V (reverseStepTree_fresh M hE κ k D S G n hG V hV)
    intro C hC
    exact ih (k-1) _ _ (reverseStepTree_remaining M hE κ k D S G n hG V hV closed C)
      (reverseStepTree_closed M hE κ k D S G n C)

lemma reversePrefixTree_remaining (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (V : Finset α)
    (hV : ∀ j < n, (G j).filter (fun e => e ∈ S j) ⊆ V)
    (closed : ReverseClosed M hE κ D k S) (C : Finset α) :
    ∀ j < n, (G j).filter (fun e => e ∈ (reversePrefixTree M hE κ D G n m k S).run C j) ⊆
      V \ (reversePrefixTree M hE κ D G n m k S).queried C := by
  induction m generalizing k S V C with
  | zero => simpa only [reversePrefixTree, RevealTree.run, RevealTree.queried, sdiff_empty] using hV
  | succ m ih =>
    rw [reversePrefixTree, RevealTree.run_bind, RevealTree.queried_bind]
    have hr := ih (k-1) _ _
      (reverseStepTree_remaining M hE κ k D S G n hG V hV closed C)
      (reverseStepTree_closed M hE κ k D S G n C)
      (C \ (reverseStepTree M hE κ k D S G n).queried C)
    intro j hj e he
    have hx := mem_sdiff.mp (hr j hj he)
    have hy := mem_sdiff.mp hx.1
    exact mem_sdiff.mpr ⟨hy.1, fun hm => (mem_union.mp hm).elim hy.2 hx.2⟩

lemma reversePrefixTree_run (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) (C : Finset α) :
    (reversePrefixTree M hE κ D G n m k S).run C = reverseFinal M hE κ D G n m k S C := by
  induction m generalizing k S C with
  | zero => rfl
  | succ m ih =>
    rw [reversePrefixTree, RevealTree.run_bind, reverseFinal]
    let W := univ \ (reverseStepTree M hE κ k D S G n).queried C
    have hW := reverseStepTree_remaining M hE κ k D S G n hG univ
      (fun _ _ => subset_univ _) closed C
    have hc := reverseStepTree_closed M hE κ k D S G n C
    have hcongr := (reversePrefixTree M hE κ D G n m (k-1)
      ((reverseStepTree M hE κ k D S G n).run C)).run_congr W
      (C \ (reverseStepTree M hE κ k D S G n).queried C) C
      (reversePrefixTree_fresh M hE κ D G n hG m (k-1) _ W hW hc)
      (fun e he => by
        have hne := (mem_sdiff.mp he).2
        simp only [mem_sdiff, hne, not_false_eq_true, and_true])
    rw [hcongr, ih (k-1) _ hc C]

theorem reversePrefixTree_tower (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) (q : α → ℝ)
    (f : (ℕ → Set α) → Finset α → ℝ)
    (hf : ∀ R C C', (∀ j < n, ∀ e ∈ G j, e ∈ R j → (e ∈ C ↔ e ∈ C')) → f R C = f R C') :
    bitsExpectation q univ (fun C => f ((reversePrefixTree M hE κ D G n m k S).run C) C) =
      bitsExpectation q univ (fun C => bitsExpectation q univ
        (f ((reversePrefixTree M hE κ D G n m k S).run C))) := by
  let tree := reversePrefixTree M hE κ D G n m k S
  have hrem := reversePrefixTree_remaining M hE κ D G n hG m k S univ
    (fun _ _ => subset_univ _) closed
  have he : bitsExpectation q univ (fun C => f (tree.run C) C) =
      bitsExpectation q univ (fun C => f (tree.run C) (C \ tree.queried C)) := by
    apply bitsExpectation_congr
    intro C hC
    apply hf
    intro j hj e heG heR
    have hx := (mem_sdiff.mp (hrem C j hj (mem_filter.mpr ⟨heG, heR⟩))).2
    change e ∉ tree.queried C at hx
    simp only [mem_sdiff, hx, not_false_eq_true, and_true]
  rw [he, tree.continuation_expectation q univ
    (reversePrefixTree_fresh M hE κ D G n hG m k S univ (fun _ _ => subset_univ _) closed)]
  apply bitsExpectation_congr
  intro C hC
  symm
  apply bitsExpectation_restrict q univ _ (subset_univ _) (f (tree.run C))
  intro T T' hTT'
  apply hf
  intro j hj e heG heR
  exact hTT' e (hrem C j hj (mem_filter.mpr ⟨heG, heR⟩))

lemma reverseNominal_mask_congr (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D S : ℕ → Set α) (G : ℕ → Finset α) (k : ℤ) (n : ℕ)
    (C C' : Finset α)
    (hC : ∀ j < n, ∀ e ∈ G j, e ∈ S j → (e ∈ C ↔ e ∈ C')) :
    reverseNominal M hE κ D (fun j => (C : Set α) ∩ (G j : Set α)) S k n =
      reverseNominal M hE κ D (fun j => (C' : Set α) ∩ (G j : Set α)) S k n := by
  unfold reverseNominal
  congr 1
  apply reversePrefix_congr_guard_inter
  intro j hj
  ext e
  by_cases heG : e ∈ G j
  · by_cases heS : e ∈ S j
    · simp only [Set.mem_inter_iff, mem_coe, heG, heS, and_true, hC j hj e heG heS]
    · simp [heS]
  · simp [heG]

lemma reverseHybrid_mask_congr (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D S : ℕ → Set α) (G : ℕ → Finset α) (k : ℤ) (n : ℕ)
    (C C' T : Finset α)
    (hC : ∀ j < n, ∀ e ∈ G j, e ∈ S j → (e ∈ C ↔ e ∈ C')) :
    reverseNominal M hE κ D (transitionHybrid M hE κ k D S G C T) S k n =
      reverseNominal M hE κ D (transitionHybrid M hE κ k D S G C' T) S k n := by
  unfold reverseNominal
  congr 1
  apply reversePrefix_congr_guard_inter
  intro j hj
  have hn := reverseNominal_mask_congr M hE κ D S G k j C C'
    (fun i hi => hC i (by omega))
  ext e
  by_cases heG : e ∈ G j
  · by_cases heS : e ∈ S j
    · simp only [transitionHybrid, hn, Set.mem_inter_iff, Set.mem_union, Set.mem_sdiff,
        mem_coe, heG, heS, true_and, and_true, hC j hj e heG heS]
    · simp [heS]
  · simp [transitionHybrid, heG]

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_ExitNumerics
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open Finset

lemma hazardTailPotential_nonneg (l : ℕ) : 0 ≤ hazardTailPotential l := by
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hl : 0 ≤ (l : ℝ) + 2 := by positivity
  exact div_nonneg (mul_nonneg (by norm_num)
    (add_nonneg (mul_nonneg hl hlog) (by norm_num))) (pow_nonneg (by norm_num) _)

lemma hazardTailPotential_step (l : ℕ) :
    hazardTailPotential l = hazardBandBound l + hazardTailPotential (l + 1) := by
  unfold hazardTailPotential hazardBandBound
  push_cast
  rw [pow_succ]
  field_simp
  ring

lemma hazardBandBound_sum (start length : ℕ) :
    (∑ k ∈ range length, hazardBandBound (start + k)) +
      hazardTailPotential (start + length) = hazardTailPotential start := by
  induction length with
  | zero => simp
  | succ length ih =>
    rw [sum_range_succ]
    have h := hazardTailPotential_step (start + length)
    rw [Nat.add_succ]
    linarith

lemma hazardTailPotential_twelve : hazardTailPotential 12 < (1 : ℝ) / 2 := by
  have hlog : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  unfold hazardTailPotential
  norm_num
  linarith

theorem hazardBandBound_sum_lt_half (length : ℕ) :
    (∑ k ∈ range length, hazardBandBound (12 + k)) < (1 : ℝ) / 2 := by
  have h := hazardBandBound_sum 12 length
  have hn := hazardTailPotential_nonneg (12 + length)
  have hu := hazardTailPotential_twelve
  linarith

lemma hazardBandBound_eq_certificate_bound (l : ℕ) :
    2 * (((2 : ℝ) ^ (l + 1))⁻¹) *
      (Real.log (1 / (((2 : ℝ) ^ (l + 1))⁻¹)) + 1) = hazardBandBound l := by
  rw [one_div, inv_inv, Real.log_pow]
  unfold hazardBandBound
  push_cast
  rw [pow_succ]
  field_simp

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_HazardCover
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset

lemma exists_hazard_band {p : ℝ} (hp : 0 < p) (hsmall : p < ((2 : ℝ)^12)⁻¹) :
    ∃ l : ℕ, 12 ≤ l ∧ inHazardBand p l := by
  have hex : ∃ n : ℕ, ((1/2 : ℝ)^n) ≤ p := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hp (by norm_num : (1/2 : ℝ) < 1)
    exact ⟨n, hn.le⟩
  let n := Nat.find hex
  have hn : (1/2 : ℝ)^n ≤ p := Nat.find_spec hex
  have hn12 : 12 < n := by
    by_contra h
    have hle : n ≤ 12 := by omega
    have hpow := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ) ≤ 1) hle
    have hsmall' : p < (1/2 : ℝ)^12 := by simpa [one_div, inv_pow] using hsmall
    linarith
  refine ⟨n-1, by omega, ?_⟩
  have hpred : p < (1/2 : ℝ)^(n-1) :=
    lt_of_not_ge (Nat.find_min hex (by dsimp only [n]; omega))
  unfold inHazardBand
  have hsucc : n-1+1 = n := by omega
  rw [hsucc]
  simpa only [one_div, inv_pow] using And.intro hn hpred

theorem finite_hazard_cover {ι : Type*} [Fintype ι] (p : ι → ℝ) :
    ∃ length : ℕ, ∀ i, 0 < p i → p i < ((2 : ℝ)^12)⁻¹ →
      ∃ k ∈ range length, inHazardBand (p i) (12+k) := by
  classical
  let band : ι → ℕ := fun i => if h : 0 < p i ∧ p i < ((2 : ℝ)^12)⁻¹
    then (exists_hazard_band h.1 h.2).choose else 12
  let length := (univ : Finset ι).sup band + 1
  refine ⟨length, ?_⟩
  intro i hi hs
  have hband : 12 ≤ band i ∧ inHazardBand (p i) (band i) := by
    dsimp only [band]
    rw [dite_eq_left ⟨hi, hs⟩]
    exact (exists_hazard_band hi hs).choose_spec
  refine ⟨band i-12, mem_range.mpr ?_, ?_⟩
  · have hb := le_sup (f := band) (mem_univ i)
    dsimp only [length]
    omega
  · have heq : 12 + (band i-12) = band i := by omega
    rw [heq]
    exact hband.2

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Reverse_Bands
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

theorem bandNonexitCost_budget (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) (d : α) (h : ℕ) (p₀ upper : ℝ)
    (hp : 0 < p₀) (hp1 : p₀ ≤ 1) (m : ℕ) (k : ℤ) (S : ℕ → Set α)
    (closed : ReverseClosed M hE κ D k S) :
    reverseMeanCost M hE κ D G n q (bandNonexitCost M hE κ D G q d h p₀ upper) m k S ≤
      Real.log (1 / p₀) := by
  have hlog : 0 ≤ Real.log (1 / p₀) := Real.log_nonneg ((one_le_div hp).mpr hp1)
  induction m generalizing k S with
  | zero => simpa only [reverseMeanCost_zero] using hlog
  | succ m ih =>
    by_cases hl : p₀ ≤ reverseHazard M hE κ D G q d h k S
    · exact bandNonexitCost_budget_after_entry M hE κ D G n hG q hq0 hq1 d h p₀ upper hp (m+1) k S closed hl
    · rw [reverseMeanCost_succ M hE κ D G n hG q _ m k S closed]
      calc
        _ ≤ bitsExpectation q univ (fun _ => Real.log (1 / p₀)) := by
          apply bitsExpectation_mono q hq0 hq1
          intro C hC
          simp only [bandNonexitCost, hl, false_and, ↓reduceIte, zero_add]
          exact ih (k-1) _ (reverseStepTree_closed M hE κ k D S G n C)
        _ = _ := bitsExpectation_const q univ _

lemma bandCountCost_step_split (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ)
    (d : α) (h : ℕ) (p₀ upper : ℝ) (k : ℤ) (S : ℕ → Set α)
    (closed : ReverseClosed M hE κ D k S) (C : Finset α) :
    bandCountCost M hE κ D G q d h p₀ upper k S ((reverseStepTree M hE κ k D S G n).run C) =
      bandNonexitCost M hE κ D G q d h p₀ upper k S ((reverseStepTree M hE κ k D S G n).run C) +
      bandExitCost M hE κ D G q d h p₀ upper k S ((reverseStepTree M hE κ k D S G n).run C) := by
  have hc := reverseStepTree_contracts M hE κ k D S G n closed C h
  unfold bandCountCost bandNonexitCost bandExitCost
  by_cases hS : d ∈ S h <;> by_cases hN : d ∈ (reverseStepTree M hE κ k D S G n).run C h
  · simp [hS, hN]
  · simp [hS, hN]
  · exact (hS (hc hN)).elim
  · simp [hS, hN]

lemma bandCountCost_mean_split (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ)
    (d : α) (h : ℕ) (p₀ upper : ℝ) (m : ℕ) (k : ℤ) (S : ℕ → Set α)
    (closed : ReverseClosed M hE κ D k S) :
    reverseMeanCost M hE κ D G n q (bandCountCost M hE κ D G q d h p₀ upper) m k S =
      reverseMeanCost M hE κ D G n q (bandNonexitCost M hE κ D G q d h p₀ upper) m k S +
      reverseMeanCost M hE κ D G n q (bandExitCost M hE κ D G q d h p₀ upper) m k S := by
  have hpoint (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) (C : Finset α) :
      reverseCost M hE κ D G n (bandCountCost M hE κ D G q d h p₀ upper) m k S C =
        reverseCost M hE κ D G n (bandNonexitCost M hE κ D G q d h p₀ upper) m k S C +
        reverseCost M hE κ D G n (bandExitCost M hE κ D G q d h p₀ upper) m k S C := by
    induction m generalizing k S with
    | zero => simp only [reverseCost, add_zero]
    | succ m ih =>
      rw [reverseCost, reverseCost, reverseCost, bandCountCost_step_split M hE κ D G n q d h p₀ upper k S closed C,
        ih (k-1) _ (reverseStepTree_closed M hE κ k D S G n C)]
      ring
  unfold reverseMeanCost
  rw [← bitsExpectation_add]
  exact bitsExpectation_congr q univ (fun C _ => hpoint m k S closed C)

lemma bandExitCost_count_le_one (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ)
    (d : α) (h : ℕ) (p₀ upper : ℝ) (m : ℕ) (k : ℤ) (S : ℕ → Set α)
    (closed : ReverseClosed M hE κ D k S) (C : Finset α) :
    reverseCost M hE κ D G n (bandExitCost M hE κ D G q d h p₀ upper) m k S C ≤
      if d ∈ S h then 1 else 0 := by
  induction m generalizing k S with
  | zero => simp only [reverseCost]; split_ifs <;> norm_num
  | succ m ih =>
    have hi := ih (k-1) _ (reverseStepTree_closed M hE κ k D S G n C)
    have hc := reverseStepTree_contracts M hE κ k D S G n closed C h
    rw [reverseCost]
    by_cases hS : d ∈ S h <;> by_cases hN : d ∈ (reverseStepTree M hE κ k D S G n).run C h
    · simpa [bandExitCost, hS, hN] using hi
    · simp only [hN, ite_false] at hi
      have hb : bandExitCost M hE κ D G q d h p₀ upper k S ((reverseStepTree M hE κ k D S G n).run C) ≤ 1 := by
        unfold bandExitCost
        split_ifs <;> norm_num
      simpa only [hS, ite_true, add_zero] using add_le_add hb hi
    · exact (hS (hc hN)).elim
    · simpa [bandExitCost, hS, hN] using hi

lemma bandExitCost_mean_le_one (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (d : α) (h : ℕ) (p₀ upper : ℝ) (m : ℕ) (k : ℤ) (S : ℕ → Set α)
    (closed : ReverseClosed M hE κ D k S) :
    reverseMeanCost M hE κ D G n q (bandExitCost M hE κ D G q d h p₀ upper) m k S ≤ 1 := by
  unfold reverseMeanCost
  calc
    _ ≤ bitsExpectation q univ (fun _ => 1) := by
      apply bitsExpectation_mono q hq0 hq1
      intro C hC
      apply (bandExitCost_count_le_one M hE κ D G n q d h p₀ upper m k S closed C).trans
      split_ifs <;> norm_num
    _ = 1 := bitsExpectation_one q univ

lemma bandExitCost_le_upper_count (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (d : α) (h : ℕ) (hh : h ≤ n) (p₀ upper : ℝ) (m : ℕ) (k : ℤ) (S : ℕ → Set α)
    (closed : ReverseClosed M hE κ D k S) :
    reverseMeanCost M hE κ D G n q (bandExitCost M hE κ D G q d h p₀ upper) m k S ≤
      upper * reverseMeanCost M hE κ D G n q (bandCountCost M hE κ D G q d h p₀ upper) m k S := by
  rw [← reverseMeanCost_mul]
  apply reverseMeanCost_le_of_step M hE κ D G n hG q hq0 hq1
  · intro l R hR
    by_cases hb : p₀ ≤ reverseHazard M hE κ D G q d h l R ∧
        reverseHazard M hE κ D G q d h l R < upper ∧ d ∈ R h
    · have heq : bitsExpectation q univ (fun C => bandExitCost M hE κ D G q d h p₀ upper l R
          ((reverseStepTree M hE κ l D R G n).run C)) = reverseHazard M hE κ D G q d h l R := by
        rw [reverseHazard_eq_step M hE κ D G n hG q d h hh]
        apply bitsExpectation_congr
        intro C hC
        simp only [bandExitCost, hb.1, hb.2.1, hb.2.2, true_and]
      rw [heq]
      simpa only [bandCountCost, hb.1, hb.2.1, hb.2.2, true_and, ite_true, mul_one, bitsExpectation_const] using hb.2.1.le
    · have hz : ∀ C, bandExitCost M hE κ D G q d h p₀ upper l R
          ((reverseStepTree M hE κ l D R G n).run C) = 0 := by
        intro C
        unfold bandExitCost
        apply ite_eq_right
        intro hc
        exact hb ⟨hc.1, hc.2.1, hc.2.2.1⟩
      simp only [hz, bandCountCost, hb, ite_false, mul_zero, bitsExpectation_const, le_refl]
  · exact closed

theorem reverse_exit_band_bound (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (d : α) (h : ℕ) (hh : h ≤ n) (p₀ upper : ℝ) (hp : 0 < p₀) (hp1 : p₀ ≤ 1) (hu : 0 ≤ upper)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) :
    reverseMeanCost M hE κ D G n q (bandExitCost M hE κ D G q d h p₀ upper) m k S ≤
      upper * (Real.log (1 / p₀) + 1) := by
  have he := bandExitCost_le_upper_count M hE κ D G n hG q hq0 hq1 d h hh p₀ upper m k S closed
  rw [bandCountCost_mean_split M hE κ D G n q d h p₀ upper m k S closed] at he
  apply he.trans
  apply mul_le_mul_of_nonneg_left _ hu
  exact add_le_add (bandNonexitCost_budget M hE κ D G n hG q hq0 hq1 d h p₀ upper hp hp1 m k S closed)
    (bandExitCost_mean_le_one M hE κ D G n q hq0 hq1 d h p₀ upper m k S closed)

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Reverse_LowHazard
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

lemma bandHazardCost_mean_eq_exit (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (d : α) (h : ℕ) (hh : h ≤ n) (p₀ upper : ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) :
    reverseMeanCost M hE κ D G n q (bandHazardCost M hE κ D G q d h p₀ upper) m k S =
      reverseMeanCost M hE κ D G n q (bandExitCost M hE κ D G q d h p₀ upper) m k S := by
  apply reverseMeanCost_eq_of_step M hE κ D G n hG q hq0 hq1
  · intro l R hR
    by_cases hb : p₀ ≤ reverseHazard M hE κ D G q d h l R ∧
        reverseHazard M hE κ D G q d h l R < upper ∧ d ∈ R h
    · simp only [bandHazardCost, hb, bitsExpectation_const]
      rw [reverseHazard_eq_step M hE κ D G n hG q d h hh]
      apply bitsExpectation_congr
      intro C hC
      simp only [bandExitCost, hb.1, hb.2.1, hb.2.2, true_and]
    · have hz : ∀ C, bandExitCost M hE κ D G q d h p₀ upper l R
          ((reverseStepTree M hE κ l D R G n).run C) = 0 := by
        intro C
        unfold bandExitCost
        apply ite_eq_right
        intro hc
        exact hb ⟨hc.1, hc.2.1, hc.2.2.1⟩
      simp only [bandHazardCost, hb, ite_false, hz, bitsExpectation_const]
  · exact closed

lemma dyadic_band_hazard_bound (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (d : α) (h : ℕ) (hh : h ≤ n) (l : ℕ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) :
    reverseMeanCost M hE κ D G n q
      (bandHazardCost M hE κ D G q d h (((2:ℝ)^(l+1))⁻¹) (((2:ℝ)^l)⁻¹)) m k S ≤
        hazardBandBound l := by
  rw [bandHazardCost_mean_eq_exit M hE κ D G n hG q hq0 hq1 d h hh _ _ m k S closed]
  have hp : 0 < ((2:ℝ)^(l+1))⁻¹ := by positivity
  have hp1 : ((2:ℝ)^(l+1))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hu : 0 ≤ ((2:ℝ)^l)⁻¹ := by positivity
  have hb := reverse_exit_band_bound M hE κ D G n hG q hq0 hq1 d h hh
    (((2:ℝ)^(l+1))⁻¹) (((2:ℝ)^l)⁻¹) hp hp1 hu m k S closed
  have heq : ((2:ℝ)^l)⁻¹ = 2 * ((2:ℝ)^(l+1))⁻¹ := by
    rw [pow_succ]
    field_simp
  rw [heq, hazardBandBound_eq_certificate_bound] at hb
  simpa only [← heq] using hb

theorem reverse_low_hazard_lt_half (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (d : α) (h : ℕ) (hh : h ≤ n)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) :
    reverseMeanCost M hE κ D G n q
      (lowHazardCost M hE κ D G q d h (((2:ℝ)^12)⁻¹)) m k S < (1:ℝ)/2 := by
  let R := traceHazards M hE κ D G n q d h m k S
  obtain ⟨L, hL⟩ := finite_hazard_cover (fun p : {p : ℝ // p ∈ R} => p.val)
  let B : ℕ → ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ := fun i =>
    bandHazardCost M hE κ D G q d h (((2:ℝ)^(12+i+1))⁻¹) (((2:ℝ)^(12+i))⁻¹)
  have hb0 (i : ℕ) (t : ReverseTransition α) : 0 ≤ B i t.time t.before t.after := by
    dsimp only [B, bandHazardCost]
    split_ifs
    · exact reverseHazard_nonneg M hE κ D G q hq0 hq1 d h _ _
    · exact le_rfl
  have hpoint (C : Finset α) :
      reverseCost M hE κ D G n (lowHazardCost M hE κ D G q d h (((2:ℝ)^12)⁻¹)) m k S C ≤
        ∑ i ∈ range L, reverseCost M hE κ D G n (B i) m k S C := by
    rw [← reverseCost_sum]
    apply reverseCost_le_of_trace
    intro t ht
    dsimp only [lowHazardCost]
    by_cases hs : d ∈ t.before h ∧ reverseHazard M hE κ D G q d h t.time t.before < ((2:ℝ)^12)⁻¹
    · rw [ite_eq_left hs]
      have hp0 := reverseHazard_nonneg M hE κ D G q hq0 hq1 d h t.time t.before
      by_cases hz : reverseHazard M hE κ D G q d h t.time t.before = 0
      · rw [hz]
        exact sum_nonneg (fun i hi => hb0 i t)
      · have hp : 0 < reverseHazard M hE κ D G q d h t.time t.before := lt_of_le_of_ne hp0 (Ne.symm hz)
        have hmem : reverseHazard M hE κ D G q d h t.time t.before ∈ R :=
          mem_traceHazards M hE κ D G n q d h m k S C t ht
        obtain ⟨i, hi, hband⟩ := hL ⟨_, hmem⟩ hp hs.2
        have heq : B i t.time t.before t.after = reverseHazard M hE κ D G q d h t.time t.before := by
          simp only [B, bandHazardCost, hband.1, hband.2, hs.1, true_and, ite_true]
        rw [← heq]
        exact single_le_sum (fun j hj => hb0 j t) hi
    · rw [ite_eq_right hs]
      exact sum_nonneg (fun i hi => hb0 i t)
  have hmean : reverseMeanCost M hE κ D G n q
      (lowHazardCost M hE κ D G q d h (((2:ℝ)^12)⁻¹)) m k S ≤
        ∑ i ∈ range L, reverseMeanCost M hE κ D G n q (B i) m k S := by
    unfold reverseMeanCost
    rw [← bitsExpectation_sum]
    exact bitsExpectation_mono q hq0 hq1 univ (fun C _ => hpoint C)
  apply lt_of_le_of_lt hmean
  apply lt_of_le_of_lt _ (hazardBandBound_sum_lt_half L)
  apply sum_le_sum
  intro i hi
  exact dyadic_band_hazard_bound M hE κ D G n hG q hq0 hq1 d h hh (12+i) m k S closed

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Reverse_Squared
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

lemma exitHazardCost_mean_eq_exit (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (d : α) (h : ℕ) (hh : h ≤ n) (m : ℕ) (k : ℤ) (S : ℕ → Set α)
    (closed : ReverseClosed M hE κ D k S) :
    reverseMeanCost M hE κ D G n q (exitHazardCost M hE κ D G q d h) m k S =
      reverseMeanCost M hE κ D G n q (exitCost d h) m k S := by
  apply reverseMeanCost_eq_of_step M hE κ D G n hG q hq0 hq1
  · intro l R hR
    by_cases hd : d ∈ R h
    · simp only [exitHazardCost, hd, ite_true, bitsExpectation_const, exitCost, true_and]
      exact reverseHazard_eq_step M hE κ D G n hG q d h hh l R
    · simp only [exitHazardCost, hd, ite_false, bitsExpectation_const, exitCost, false_and]
  · exact closed

theorem reverse_squared_exit_mass (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (d : α) (hd : d ∉ M.closure ∅) (h : ℕ) (hh : h ≤ n) :
    (((2:ℝ)^12)⁻¹) / 2 ≤
      reverseMeanCost M hE κ D G n q (squareHazardCost M hE κ D G q d h)
        (pathHorizon h+1) (-1) (fun _ => Set.univ) := by
  let η : ℝ := ((2:ℝ)^12)⁻¹
  have hη : 0 ≤ η := by dsimp only [η]; positivity
  have hpoint (k : ℤ) (S S' : ℕ → Set α) :
      η * exitHazardCost M hE κ D G q d h k S S' ≤
        squareHazardCost M hE κ D G q d h k S S' + η * lowHazardCost M hE κ D G q d h η k S S' := by
    by_cases hs : d ∈ S h
    · by_cases hp : reverseHazard M hE κ D G q d h k S < η
      · simp only [exitHazardCost, squareHazardCost, lowHazardCost, hs, hp, true_and, ite_true]
        nlinarith [sq_nonneg (reverseHazard M hE κ D G q d h k S)]
      · have hp' : η ≤ reverseHazard M hE κ D G q d h k S := le_of_not_gt hp
        have hp0 := reverseHazard_nonneg M hE κ D G q hq0 hq1 d h k S
        simp only [exitHazardCost, squareHazardCost, lowHazardCost, hs, hp, true_and, ite_true, ite_false, mul_zero, add_zero]
        nlinarith
    · simp [exitHazardCost, squareHazardCost, lowHazardCost, hs]
  have hmean :
      η * reverseMeanCost M hE κ D G n q (exitHazardCost M hE κ D G q d h) (pathHorizon h+1) (-1) (fun _ => Set.univ) ≤
      reverseMeanCost M hE κ D G n q (squareHazardCost M hE κ D G q d h) (pathHorizon h+1) (-1) (fun _ => Set.univ) +
      η * reverseMeanCost M hE κ D G n q (lowHazardCost M hE κ D G q d h η) (pathHorizon h+1) (-1) (fun _ => Set.univ) := by
    rw [← reverseMeanCost_mul, ← reverseMeanCost_mul, ← reverseMeanCost_add]
    unfold reverseMeanCost
    apply bitsExpectation_mono q hq0 hq1
    intro C hC
    exact reverseCost_mono M hE κ D G n _ _ hpoint _ _ _ C
  rw [exitHazardCost_mean_eq_exit M hE κ D G n hG q hq0 hq1 d h hh _ _ _
    (reverseClosed_univ M hE κ D (-1)), reverse_exit_total_one M hE κ D G n hG q d hd h hh,
    mul_one] at hmean
  have hlow := reverse_low_hazard_lt_half M hE κ D G n hG q hq0 hq1 d h hh
    (pathHorizon h+1) (-1) (fun _ => Set.univ) (reverseClosed_univ M hE κ D (-1))
  change η / 2 ≤ reverseMeanCost M hE κ D G n q _ _ _ _
  change reverseMeanCost M hE κ D G n q (lowHazardCost M hE κ D G q d h η) _ _ _ < _ at hlow
  have hmul := mul_le_mul_of_nonneg_left hlow.le hη
  have hsub := (sub_le_iff_le_add).mpr (hmean.trans (add_le_add le_rfl hmul))
  calc
    η / 2 = η - η * (1 / 2) := by ring
    _ ≤ _ := hsub

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Reverse_BirthSafety
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

lemma reverseDoubleExit_mask_congr (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D S : ℕ → Set α) (G : ℕ → Finset α) (k : ℤ) (h : ℕ) (d : α)
    (C C' T : Finset α)
    (hC : ∀ j < h, ∀ e ∈ G j, e ∈ S j → (e ∈ C ↔ e ∈ C')) :
    reverseDoubleExit M hE κ D S G k h d C T = reverseDoubleExit M hE κ D S G k h d C' T := by
  unfold reverseDoubleExit
  rw [reverseNominal_mask_congr M hE κ D S G k h C C' hC,
    reverseHybrid_mask_congr M hE κ D S G k h C C' T hC]

lemma reverseDoubleExit_expectation (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D S : ℕ → Set α) (G : ℕ → Finset α) (k : ℤ) (h : ℕ) (d : α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ) :
    bitsExpectation q univ (fun C => bitsExpectation q univ (reverseDoubleExit M hE κ D S G k h d C)) =
      if d ∈ S h then (reverseHazard M hE κ D G q d h k S)^2 else 0 := by
  change bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
    reverseDoubleExit M hE κ D S G k h d C T)) = _
  by_cases hd : d ∈ S h
  · simp only [reverseDoubleExit, hd, ite_true]
    rw [reverse_double_exit M hE κ k D S G h hG univ (fun _ _ => subset_univ _) q d,
      reverseHazard_eq]
  · simp only [reverseDoubleExit, hd, ite_false, bitsExpectation_const]

theorem reverseDoubleExit_after_prefix (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (d : α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) (l : ℤ) :
    bitsExpectation q univ (fun C => bitsExpectation q univ
      (reverseDoubleExit M hE κ D ((reversePrefixTree M hE κ D G h m k S).run C) G l h d C)) =
      bitsExpectation q univ (fun C => if d ∈ (reversePrefixTree M hE κ D G h m k S).run C h then
        (reverseHazard M hE κ D G q d h l ((reversePrefixTree M hE κ D G h m k S).run C))^2 else 0) := by
  let f := fun R C => bitsExpectation q univ (reverseDoubleExit M hE κ D R G l h d C)
  have ht := reversePrefixTree_tower M hE κ D G h hG m k S closed q f (by
    intro R C C' hC
    apply bitsExpectation_congr
    intro T hT
    exact reverseDoubleExit_mask_congr M hE κ D R G l h d C C' T hC)
  apply ht.trans
  apply bitsExpectation_congr
  intro C hC
  exact reverseDoubleExit_expectation M hE κ D _ G l h d hG q

lemma reversePrefixTree_from_univ_path (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (m : ℕ) (C : Finset α)
    {j : ℕ} (hj : j ≤ n) :
    (reversePrefixTree M hE κ D G n m (-1) (fun _ => Set.univ)).run C j =
      nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j (-(m:ℤ)) := by
  rw [reversePrefixTree_run M hE κ D G n hG m (-1) _ (reverseClosed_univ M hE κ D (-1)) C]
  have hS : ∀ i ≤ n, (fun _ => Set.univ) i =
      nominalPath M hE κ D (fun l => (C : Set α) ∩ (G l : Set α)) i (-1+1) := by
    intro i hi
    exact (nominalPath_nonnegative M hE κ D _ i (by omega)).symm
  simpa only [neg_add_cancel, zero_sub] using reverseFinal_path M hE κ D G n hG m (-1) _ C hS hj

omit [DecidableEq α] in
lemma reverseNominal_actual_state (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D S : ℕ → Set α) (G : ℕ → Finset α) (C : Finset α) (b : ℤ) (h : ℕ)
    (hS : ∀ j ≤ h, S j = nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j b) :
    reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S (b-1) h =
      nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h (b-1) := by
  calc
    _ = reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α))
        (fun j => nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j (b-1+1)) (b-1) h := by
      apply reverseNominal_congr_before
      · intro j hj; rfl
      · intro j hj; simpa only [sub_add_cancel] using hS j (by omega)
    _ = _ := reverseNominal_agrees M hE κ D _ (b-1) h

omit [DecidableEq α] in
lemma hybrid_actual_containment (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D S : ℕ → Set α) (G : ℕ → Finset α) (C T : Finset α) (b : ℤ) (h : ℕ)
    (hS : ∀ j ≤ h, S j = nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j b)
    (hb : activation h ≤ b-1) :
    densityExpansion M hE κ (D h)
      (guardedPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h (b-2) ∪
        lowerCompetition M hE κ D (fun i => (C : Set α) ∩ (G i : Set α))
          (fun i => (T : Set α) ∩ (G i : Set α)) b h) ⊆
      reverseNominal M hE κ D (transitionHybrid M hE κ (b-1) D S G C T) S (b-1) h := by
  have heq : reverseNominal M hE κ D (transitionHybrid M hE κ (b-1) D S G C T) S (b-1) h =
      reverseNominal M hE κ D
        (hybridGuards M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) (fun i => (T : Set α) ∩ (G i : Set α)) b)
        (fun j => nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j b) (b-1) h := by
    apply reverseNominal_congr_before
    · intro j hj
      unfold transitionHybrid hybridGuards
      rw [reverseNominal_actual_state M hE κ D S G C b j (fun i hi => hS i (by omega)), hS j (by omega)]
    · intro j hj; exact hS j (by omega)
  rw [heq]
  exact hybrid_containment M hE κ D _ _ b h hb

omit [DecidableEq α] in
lemma doubleExit_le_safeBirth (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D S : ℕ → Set α) (G : ℕ → Finset α) (C T : Finset α) (b : ℤ) (h : ℕ)
    (d : α) (hd : d ∉ M.closure ∅)
    (hS : ∀ j ≤ h, S j = nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j b)
    (hb : activation h ≤ b-1) :
    reverseDoubleExit M hE κ D S G (b-1) h d C T ≤ if safeBirthEvent M hE κ D G h d b C T then 1 else 0 := by
  unfold reverseDoubleExit
  by_cases hs : d ∈ S h
  · rw [ite_eq_left hs]
    by_cases hn : d ∉ reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S (b-1) h
    · rw [ite_eq_left hn, one_mul]
      by_cases hh : d ∉ reverseNominal M hE κ D (transitionHybrid M hE κ (b-1) D S G C T) S (b-1) h
      · rw [ite_eq_left hh]
        have hbirth : nominalBirth M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h d = b := by
          rw [hS h le_rfl, mem_nominal_iff_birth_le M hE κ D _ h d hd b] at hs
          rw [reverseNominal_actual_state M hE κ D S G C b h hS,
            mem_nominal_iff_birth_le M hE κ D _ h d hd (b-1)] at hn
          omega
        have hsafe : safeBirthEvent M hE κ D G h d b C T :=
          ⟨hbirth, fun he => hh (hybrid_actual_containment M hE κ D S G C T b h hS hb he)⟩
        simp only [ite_eq_left hsafe, le_refl]
      · simp only [ite_eq_right hh]
        split_ifs <;> norm_num
    · simp only [ite_eq_right hn, zero_mul]
      split_ifs <;> norm_num
  · simp only [ite_eq_right hs]
    split_ifs <;> norm_num

lemma reverseHazard_state_congr (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D S S' : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ) (k : ℤ) (h : ℕ) (d : α)
    (hS : ∀ j < h, S j = S' j) :
    reverseHazard M hE κ D G q d h k S = reverseHazard M hE κ D G q d h k S' := by
  rw [reverseHazard_eq, reverseHazard_eq]
  apply bitsExpectation_congr
  intro C hC
  rw [reverseNominal_congr_before M hE κ D _ _ S S' k h (fun _ _ => rfl) hS]

theorem safeBirth_probability (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (h : ℕ) (d : α) (hd : d ∉ M.closure ∅) (m : ℕ) (hb : activation h + 2 ≤ -(m:ℤ)) :
    bitsExpectation q univ (fun C =>
      if d ∈ nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h (-(m:ℤ)) then
        (reverseHazard M hE κ D G q d h (-(m:ℤ)-1)
          (fun j => nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j (-(m:ℤ))))^2 else 0) ≤
    bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
      if safeBirthEvent M hE κ D G h d (-(m:ℤ)) C T then 1 else 0)) := by
  let P := reversePrefixTree M hE κ D G h m (-1) (fun _ => Set.univ)
  have hP (C : Finset α) (j : ℕ) (hj : j ≤ h) : P.run C j =
      nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j (-(m:ℤ)) :=
    reversePrefixTree_from_univ_path M hE κ D G h hG m C hj
  have hid := reverseDoubleExit_after_prefix M hE κ D G h d hG q m (-1) (fun _ => Set.univ)
    (reverseClosed_univ M hE κ D (-1)) (-(m:ℤ)-1)
  have heq : bitsExpectation q univ (fun C =>
      if d ∈ nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h (-(m:ℤ)) then
        (reverseHazard M hE κ D G q d h (-(m:ℤ)-1)
          (fun j => nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j (-(m:ℤ))))^2 else 0) =
      bitsExpectation q univ (fun C => if d ∈ P.run C h then
        (reverseHazard M hE κ D G q d h (-(m:ℤ)-1) (P.run C))^2 else 0) := by
    apply bitsExpectation_congr
    intro C hC
    rw [hP C h le_rfl, reverseHazard_state_congr M hE κ D (P.run C) _ G q _ h d
      (fun j hj => hP C j hj.le)]
  rw [heq, ← hid]
  apply bitsExpectation_mono q hq0 hq1
  intro C hC
  apply bitsExpectation_mono q hq0 hq1
  intro T hT
  exact doubleExit_le_safeBirth M hE κ D (P.run C) G C T (-(m:ℤ)) h d hd (hP C) (by omega)

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Reverse_SquareSum
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

lemma reverseCost_add_steps (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (cost : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (m r : ℕ) (k : ℤ) (S : ℕ → Set α) (C : Finset α) :
    reverseCost M hE κ D G n cost (m+r) k S C =
      reverseCost M hE κ D G n cost m k S C +
        reverseCost M hE κ D G n cost r (k-m) (reverseFinal M hE κ D G n m k S C) C := by
  induction m generalizing k S with
  | zero => simp only [reverseCost, reverseFinal, Nat.cast_zero, sub_zero, zero_add]
  | succ m ih =>
    rw [Nat.succ_add, reverseCost, reverseCost, reverseFinal, ih]
    have ht : k - 1 - (m:ℤ) = k - ((m+1:ℕ):ℤ) := by omega
    rw [ht]
    ring

lemma reverseCost_eq_sum (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (cost : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (C : Finset α) :
    reverseCost M hE κ D G n cost m k S C =
      ∑ i ∈ range m, cost (k-i) (reverseFinal M hE κ D G n i k S C)
        ((reverseStepTree M hE κ (k-i) D (reverseFinal M hE κ D G n i k S C) G n).run C) := by
  induction m with
  | zero => simp only [reverseCost, range_zero, sum_empty]
  | succ m ih =>
    rw [reverseCost_add_steps M hE κ D G n cost m 1, ih, sum_range_succ]
    simp only [reverseCost, add_zero]

lemma reverse_square_eq_path_sum (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (d : α) (h : ℕ) (hh : h ≤ n) (m : ℕ) :
    reverseMeanCost M hE κ D G n q (squareHazardCost M hE κ D G q d h) m (-1) (fun _ => Set.univ) =
      ∑ i ∈ range m, bitsExpectation q univ (pathExitSquare M hE κ D G q d h i) := by
  unfold reverseMeanCost
  rw [← bitsExpectation_sum]
  apply bitsExpectation_congr
  intro C hC
  rw [reverseCost_eq_sum]
  apply sum_congr rfl
  intro i hi
  have hS : ∀ j ≤ n, (fun _ => Set.univ) j =
      nominalPath M hE κ D (fun l => (C : Set α) ∩ (G l : Set α)) j (-1+1) := by
    intro j hj
    exact (nominalPath_nonnegative M hE κ D _ j (by omega)).symm
  have hf (j : ℕ) (hj : j ≤ n) : reverseFinal M hE κ D G n i (-1) (fun _ => Set.univ) C j =
      nominalPath M hE κ D (fun l => (C : Set α) ∩ (G l : Set α)) j (-(i:ℤ)) := by
    simpa only [neg_add_cancel, zero_sub] using reverseFinal_path M hE κ D G n hG i (-1) _ C hS hj
  have ht : (-1:ℤ) - i = -(i:ℤ)-1 := by omega
  simp only [squareHazardCost, pathExitSquare, ht, hf h hh]
  rw [reverseHazard_state_congr M hE κ D _ _ G q _ h d (fun j hj => hf j (by omega))]

theorem path_squared_exit_mass (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (d : α) (hd : d ∉ M.closure ∅) (h : ℕ) :
    (((2:ℝ)^12)⁻¹) / 2 ≤
      ∑ i ∈ range (pathHorizon h+1), bitsExpectation q univ (pathExitSquare M hE κ D G q d h i) := by
  rw [← reverse_square_eq_path_sum M hE κ D G h hG q d h le_rfl]
  exact reverse_squared_exit_mass M hE κ D G h hG q hq0 hq1 d hd h le_rfl

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Reverse_BirthLoss
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

lemma pathExitSquare_eq_doubleExit (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (h : ℕ) (d : α) (m : ℕ) :
    bitsExpectation q univ (pathExitSquare M hE κ D G q d h m) =
      bitsExpectation q univ (fun C => bitsExpectation q univ
        (reverseDoubleExit M hE κ D ((reversePrefixTree M hE κ D G h m (-1) (fun _ => Set.univ)).run C)
          G (-(m:ℤ)-1) h d C)) := by
  rw [reverseDoubleExit_after_prefix M hE κ D G h d hG q m (-1) _ (reverseClosed_univ M hE κ D (-1))]
  apply bitsExpectation_congr
  intro C hC
  have hp (j : ℕ) (hj : j ≤ h) := reversePrefixTree_from_univ_path M hE κ D G h hG m C hj
  rw [hp h le_rfl, reverseHazard_state_congr M hE κ D _ _ G q _ h d (fun j hj => hp j hj.le)]
  rfl

omit [DecidableEq α] in
lemma doubleExit_le_birth (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D S : ℕ → Set α) (G : ℕ → Finset α) (C T : Finset α) (b : ℤ) (h : ℕ)
    (d : α) (hd : d ∉ M.closure ∅)
    (hS : ∀ j ≤ h, S j = nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j b) :
    reverseDoubleExit M hE κ D S G (b-1) h d C T ≤
      if nominalBirth M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h d = b then 1 else 0 := by
  unfold reverseDoubleExit
  by_cases hs : d ∈ S h
  · rw [ite_eq_left hs]
    by_cases hn : d ∉ reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S (b-1) h
    · rw [ite_eq_left hn, one_mul]
      have hbirth : nominalBirth M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h d = b := by
        rw [hS h le_rfl, mem_nominal_iff_birth_le M hE κ D _ h d hd b] at hs
        rw [reverseNominal_actual_state M hE κ D S G C b h hS,
          mem_nominal_iff_birth_le M hE κ D _ h d hd (b-1)] at hn
        omega
      rw [ite_eq_left hbirth]
      split_ifs <;> norm_num
    · simp only [ite_eq_right hn, zero_mul]
      split_ifs <;> norm_num
  · simp only [ite_eq_right hs]
    split_ifs <;> norm_num

theorem pathExitSquare_le_birth_probability (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (h : ℕ) (d : α) (hd : d ∉ M.closure ∅) (m : ℕ) :
    bitsExpectation q univ (pathExitSquare M hE κ D G q d h m) ≤
      bitsExpectation q univ (fun C =>
        if nominalBirth M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h d = -(m:ℤ) then 1 else 0) := by
  rw [pathExitSquare_eq_doubleExit M hE κ D G hG q h d m]
  apply bitsExpectation_mono q hq0 hq1
  intro C hC
  rw [← bitsExpectation_const q univ (if nominalBirth M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h d = -(m:ℤ) then 1 else 0)]
  apply bitsExpectation_mono q hq0 hq1
  intro T hT
  exact doubleExit_le_birth M hE κ D _ G C T (-(m:ℤ)) h d hd
    (fun j hj => reversePrefixTree_from_univ_path M hE κ D G h hG m C hj)

omit [DecidableEq α] in
lemma nominalBirth_baseline_iff (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (d : α) (hd : d ∉ M.closure ∅) :
    nominalBirth M hE κ D C h d = activation h ↔ d ∈ densityExpansion M hE κ (D h) (M.closure ∅) := by
  have hm := mem_nominal_iff_birth_le M hE κ D C h d hd (activation h)
  rw [nominalPath_baseline] at hm
  have hb := (nominalBirth_bounds M hE κ D C h d).1
  exact ⟨fun he => hm.mpr he.le, fun he => le_antisymm (hm.mp he) hb⟩

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_SafeSamples
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

lemma pathHorizon_pos (h : ℕ) : 0 < pathHorizon h := by unfold pathHorizon; omega

theorem safeEndpointCount_lower (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (h : ℕ) (d : α) (hd : d ∉ M.closure ∅) :
    (((2:ℝ)^12)⁻¹) / 2 ≤
      bitsExpectation q univ (fun C => bitsExpectation q univ (safeEndpointCount M hE κ D G h d C)) +
        if d ∈ densityExpansion M hE κ (D h) (M.closure ∅) then 1 else 0 := by
  let H := pathHorizon h
  let f := fun i => bitsExpectation q univ (pathExitSquare M hE κ D G q d h i)
  let g : ℕ → ℝ := fun i => bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
    if safeBirthEvent M hE κ D G h d (-(i:ℤ)) C T then 1 else 0))
  have hH : 1 ≤ H := pathHorizon_pos h
  have htime : activation h = -(H:ℤ) := by have ht := activation_add_horizon h; omega
  have hvalid : ∀ i ∈ range (H-1), f i ≤ g i := by
    intro i hi
    exact safeBirth_probability M hE κ D G hG q hq0 hq1 h d hd i (by
      have hi' := mem_range.mp hi
      rw [htime]
      omega)
  have hgap : f (H-1) ≤ 0 := by
    have hb := pathExitSquare_le_birth_probability M hE κ D G hG q hq0 hq1 h d hd (H-1)
    have ht : -((H-1:ℕ):ℤ) = activation h + 1 := by omega
    have hz : bitsExpectation q univ (fun C =>
        if nominalBirth M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h d = -((H-1:ℕ):ℤ)
          then 1 else 0) = 0 := by
      rw [ht]
      simp only [nominalBirth_not_activation_succ, ite_false, bitsExpectation_const]
    exact hb.trans_eq hz
  have hbase : f H ≤ if d ∈ densityExpansion M hE κ (D h) (M.closure ∅) then 1 else 0 := by
    have hb := pathExitSquare_le_birth_probability M hE κ D G hG q hq0 hq1 h d hd H
    have heq : bitsExpectation q univ (fun C =>
        if nominalBirth M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h d = -(H:ℤ)
          then 1 else 0) = if d ∈ densityExpansion M hE κ (D h) (M.closure ∅) then 1 else 0 := by
      rw [← htime]
      simp only [nominalBirth_baseline_iff M hE κ D _ h d hd, bitsExpectation_const]
    exact hb.trans_eq heq
  have hsplit : (∑ i ∈ range (H+1), f i) = (∑ i ∈ range (H-1), f i) + f (H-1) + f H := by
    have hn : H+1 = (H-1+1)+1 := by omega
    rw [hn, sum_range_succ, sum_range_succ, Nat.sub_add_cancel hH]
  have hsum := path_squared_exit_mass M hE κ D G hG q hq0 hq1 d hd h
  change (((2:ℝ)^12)⁻¹)/2 ≤ ∑ i ∈ range (H+1), f i at hsum
  rw [hsplit] at hsum
  have hfg := sum_le_sum (fun i hi => hvalid i hi)
  have heq : bitsExpectation q univ (fun C => bitsExpectation q univ (safeEndpointCount M hE κ D G h d C)) =
      ∑ i ∈ range (H-1), g i := by
    change bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
      ∑ i ∈ range (H-1), if safeBirthEvent M hE κ D G h d (-(i:ℤ)) C T then 1 else 0)) = _
    simp_rw [bitsExpectation_sum]
    rfl
  rw [heq]
  linarith

omit [Fintype α] [DecidableEq α] in
lemma indep_not_loop (M : Matroid α) (I : Finset α) (hI : M.Indep (I : Set α))
    {d : α} (hd : d ∈ I) : d ∉ M.closure ∅ := by
  intro he
  exact hI.notMem_closure_sdiff_of_mem hd (M.closure_subset_closure (Set.empty_subset _) he)

theorem safeCountBeforeParity_lower (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (h : ℕ) (I : Finset α) (hI : M.Indep (I : Set α)) :
    (((2:ℝ)^12)⁻¹) / 2 * I.card - (D h).ncard / (κ:ℝ) ≤
      bitsExpectation q univ (fun C => bitsExpectation q univ (safeCountBeforeParity M hE κ D G h I C)) := by
  let Q := densityExpansion M hE κ (D h) (M.closure ∅)
  have hsum := sum_le_sum (fun d hd => safeEndpointCount_lower M hE κ D G hG q hq0 hq1 h d (indep_not_loop M I hI hd))
  have hpre : bitsExpectation q univ (fun C => bitsExpectation q univ (safeCountBeforeParity M hE κ D G h I C)) =
      ∑ d ∈ I, bitsExpectation q univ (fun C => bitsExpectation q univ (safeEndpointCount M hE κ D G h d C)) := by
    change bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
      ∑ d ∈ I, safeEndpointCount M hE κ D G h d C T)) = _
    simp_rw [bitsExpectation_sum]
  have hcount : (∑ d ∈ I, if d ∈ Q then (1:ℝ) else 0) = ((I.filter (fun d => d ∈ Q)).card : ℝ) := by
    simp
  have hset : ((I.filter (fun d => d ∈ Q) : Finset α) : Set α) = (I : Set α) ∩ Q := by
    ext d
    simp
  have hb := baseline_independent_count M hE κ (D h) (I : Set α) hI
  change κ * ((I : Set α) ∩ Q).ncard ≤ (D h).ncard at hb
  rw [← hset, Set.ncard_coe_finset] at hb
  have hb' : (κ:ℝ) * ((I.filter (fun d => d ∈ Q)).card : ℝ) ≤ ((D h).ncard:ℝ) := by exact_mod_cast hb
  have hκ' : (0:ℝ) < κ := by exact_mod_cast hκ
  have hb'' : ((I.filter (fun d => d ∈ Q)).card : ℝ) ≤ (D h).ncard / (κ:ℝ) := (le_div_iff₀ hκ').mpr (by simpa [mul_comm] using hb')
  rw [sum_add_distrib] at hsum
  change (∑ _ ∈ I, (((2:ℝ)^12)⁻¹)/2) ≤
    (∑ d ∈ I, bitsExpectation q univ (fun C => bitsExpectation q univ (safeEndpointCount M hE κ D G h d C))) +
      ∑ d ∈ I, if d ∈ Q then (1:ℝ) else 0 at hsum
  rw [hcount, ← hpre] at hsum
  simp only [sum_const, nsmul_eq_mul] at hsum
  linarith

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_SafeParity
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

omit [DecidableEq α] in
lemma safeSampleCount_parity_split (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (I C T : Finset α) :
    safeSampleCount M hE κ D G h I C T false + safeSampleCount M hE κ D G h I C T true =
      safeCountBeforeParity M hE κ D G h I C T := by
  unfold safeSampleCount safeCountBeforeParity
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  unfold safeEndpointParityCount safeEndpointCount
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  have hm0 := Int.emod_nonneg (-(i:ℤ)) (by norm_num : (2:ℤ) ≠ 0)
  have hm1 := Int.emod_lt_of_pos (-(i:ℤ)) (by norm_num : (0:ℤ) < 2)
  have hm : (-(i:ℤ)) % 2 = 0 ∨ (-(i:ℤ)) % 2 = 1 := by omega
  by_cases hs : safeBirthEvent M hE κ D G h d (-(i:ℤ)) C T
  · rcases hm with hm | hm <;> simp [hs, hm]
  · simp [hs]

omit [DecidableEq α] in
lemma safeSampleCount_fair_parity (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (I C T : Finset α) :
    fairParityExpectation (safeSampleCount M hE κ D G h I C T) =
      safeCountBeforeParity M hE κ D G h I C T / 2 := by
  unfold fairParityExpectation
  rw [safeSampleCount_parity_split]

theorem safeSampleCount_lower (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (h : ℕ) (I : Finset α) (hI : M.Indep (I : Set α)) :
    (((2:ℝ)^12)⁻¹) / 4 * I.card - (D h).ncard / (κ:ℝ) ≤
      bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
        fairParityExpectation (safeSampleCount M hE κ D G h I C T))) := by
  have hpre := safeCountBeforeParity_lower M hE κ hκ D G hG q hq0 hq1 h I hI
  have heq : bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
        fairParityExpectation (safeSampleCount M hE κ D G h I C T))) =
      (bitsExpectation q univ (fun C => bitsExpectation q univ (safeCountBeforeParity M hE κ D G h I C))) / 2 := by
    simp only [safeSampleCount_fair_parity, div_eq_mul_inv]
    rw [show bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
      safeCountBeforeParity M hE κ D G h I C T * (2:ℝ)⁻¹)) =
        bitsExpectation q univ (fun C => bitsExpectation q univ (safeCountBeforeParity M hE κ D G h I C) * (2:ℝ)⁻¹) from by
          apply bitsExpectation_congr; intro C hC; exact bitsExpectation_mul_right q univ _ _]
    exact bitsExpectation_mul_right q univ _ _
  rw [heq]
  have hnonneg : 0 ≤ (D h).ncard / (κ:ℝ) := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  linarith

omit [Fintype α] [DecidableEq α] in
lemma sum_unique_indicators {ι : Type*} (J : Finset ι) (p : ι → Prop) [DecidablePred p]
    (huniq : ∀ i ∈ J, ∀ j ∈ J, p i → p j → i = j) :
    (∑ i ∈ J, if p i then (1:ℝ) else 0) = if ∃ i ∈ J, p i then 1 else 0 := by
  classical
  by_cases hex : ∃ i ∈ J, p i
  · obtain ⟨i, hi, hp⟩ := hex
    rw [ite_eq_left ⟨i, hi, hp⟩]
    calc
      _ = if p i then (1:ℝ) else 0 := by
        apply sum_eq_single i
        · intro j hj hji
          exact ite_eq_right (fun hjp => hji (huniq j hj i hi hjp hp))
        · intro hnot
          exact (hnot hi).elim
      _ = 1 := ite_eq_left hp
  · rw [ite_eq_right hex]
    apply sum_eq_zero
    intro i hi
    exact ite_eq_right (fun hp => hex ⟨i, hi, hp⟩)

omit [DecidableEq α] in
lemma isSafeSample_iff_endpoint (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (d : α) (C T : Finset α) (parity : Bool) :
    IsSafeSample M hE κ D G h d C T parity ↔ ∃ i ∈ range (pathHorizon h-1),
      safeBirthEvent M hE κ D G h d (-(i:ℤ)) C T ∧ (-(i:ℤ)) % 2 = (if parity then 1 else 0) := by
  let b := nominalBirth M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h d
  have ht := activation_add_horizon h
  have hH := pathHorizon_pos h
  constructor
  · rintro ⟨hlo, hhi, hp, hs⟩
    have hi0 : 0 ≤ -b := by omega
    have hieq : -(((-b).toNat:ℕ):ℤ) = b := by rw [Int.toNat_of_nonneg hi0]; omega
    refine ⟨(-b).toNat, mem_range.mpr ?_, ?_, ?_⟩
    · have hiNat := Int.toNat_of_nonneg hi0
      change activation h + 2 ≤ b at hlo
      omega
    · rw [hieq]
      exact ⟨rfl, hs⟩
    · simpa only [hieq] using hp
  · rintro ⟨i, hi, hs, hp⟩
    have hbirth := hs.1
    have hbound := mem_range.mp hi
    change _ ∧ _ ∧ _ ∧ _
    rw [hbirth]
    exact ⟨by omega, by omega, hp, hs.2⟩

omit [DecidableEq α] in

lemma safeSampleCount_eq_card (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (I C T : Finset α) (parity : Bool) :
    safeSampleCount M hE κ D G h I C T parity = (safeSampleSet M hE κ D G h I C T parity).card := by
  unfold safeSampleCount safeSampleSet
  have hpoint (d : α) : safeEndpointParityCount M hE κ D G h d C T parity =
      if IsSafeSample M hE κ D G h d C T parity then 1 else 0 := by
    unfold safeEndpointParityCount
    rw [sum_unique_indicators]
    · simp only [← isSafeSample_iff_endpoint]
    · intro i hi j hj hsi hsj
      have hbi := hsi.1.1
      have hbj := hsj.1.1
      omega
  simp_rw [hpoint]
  simp

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Residual_Global
attribute [-instance] _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [DecidableEq α]

lemma tripleMaskExpectation_const (p q r : α → ℝ) (V : Finset α) (c : ℝ) :
    tripleMaskExpectation p q r V (fun _ _ _ => c) = c := by
  simp only [tripleMaskExpectation, bitsExpectation_const]

lemma tripleMaskExpectation_congr (p q r : α → ℝ) (V : Finset α)
    {f g : Finset α → Finset α → Finset α → ℝ}
    (h : ∀ D ⊆ V, ∀ C ⊆ V, ∀ T ⊆ V, f D C T = g D C T) :
    tripleMaskExpectation p q r V f = tripleMaskExpectation p q r V g := by
  apply bitsExpectation_congr
  intro D hD
  apply bitsExpectation_congr
  intro C hC
  exact bitsExpectation_congr r V (fun T hT => h D hD C hC T hT)

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Algorithm_Mean
attribute [-instance] _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset

lemma fairParityExpectation_mono {f g : Bool → ℝ} (h : ∀ p, f p ≤ g p) :
    fairParityExpectation f ≤ fairParityExpectation g := by
  have h0 := h false
  have h1 := h true
  unfold fairParityExpectation
  linarith

lemma fairParityExpectation_const (c : ℝ) : fairParityExpectation (fun _ => c) = c := by
  unfold fairParityExpectation
  ring

lemma fairParityExpectation_add (f g : Bool → ℝ) :
    fairParityExpectation (fun p => f p + g p) = fairParityExpectation f + fairParityExpectation g := by
  unfold fairParityExpectation
  ring

lemma fairParityExpectation_mul (c : ℝ) (f : Bool → ℝ) :
    fairParityExpectation (fun p => c * f p) = c * fairParityExpectation f := by
  unfold fairParityExpectation
  ring

lemma bitsExpectation_fairParity {α : Type*} [DecidableEq α] (q : α → ℝ)
    (V : Finset α) (f : Finset α → Bool → ℝ) :
    bitsExpectation q V (fun T => fairParityExpectation (f T)) =
      fairParityExpectation (fun p => bitsExpectation q V (fun T => f T p)) := by
  simp only [fairParityExpectation, div_eq_mul_inv]
  rw [bitsExpectation_mul_right, bitsExpectation_add]

namespace MainAlgorithm
variable {n : ℕ}

lemma mainMean_mono (d : MainMasks n) {f g : MainMasks n → ℝ}
    (h : ∀ d', d'.H = d.H → f d' ≤ g d') : mainMean d f ≤ mainMean d g := by
  apply tripleMaskExpectation_mono _ _ _ (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => constants_positive.2.2.1.le) (fun _ => by norm_num [thinningRate])
    (fun _ => constants_positive.2.2.1.le) (fun _ => by norm_num [thinningRate])
  intro D hD C hC T hT
  exact fairParityExpectation_mono (fun p => h _ rfl)

lemma mainMean_const (d : MainMasks n) (c : ℝ) : mainMean d (fun _ => c) = c := by
  simp only [mainMean, fairParityExpectation_const, tripleMaskExpectation_const]

lemma mainMean_add (d : MainMasks n) (f g : MainMasks n → ℝ) :
    mainMean d (fun d' => f d' + g d') = mainMean d f + mainMean d g := by
  simp only [mainMean, fairParityExpectation_add, tripleMaskExpectation_add]

lemma mainMean_mul (d : MainMasks n) (c : ℝ) (f : MainMasks n → ℝ) :
    mainMean d (fun d' => c * f d') = c * mainMean d f := by
  simp only [mainMean, fairParityExpectation_mul, tripleMaskExpectation_mul]

lemma mainMean_guard_count (d : MainMasks n) (K : Finset (Fin n)) :
    mainMean d (fun d' => ((d'.C ∩ K).card : ℝ)) = thinningRate * K.card := by
  unfold mainMean tripleMaskExpectation MainAlgorithm.withMasks
  simp only [fairParityExpectation_const, bitsExpectation_const]
  have hc : bitsExpectation (fun _ : Fin n => thinningRate) univ
      (fun C => ((C ∩ K).card : ℝ)) = thinningRate * K.card := by
    simp_rw [Finset.inter_comm _ K]
    rw [bitsExpectation_card_inter _ univ K (subset_univ _)]
    simp [mul_comm]
  rw [hc]

end MainAlgorithm
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_WeightedAccounting
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset

lemma sum_zpow_lt_upper (B : ℝ) (hB : 1 < B) (s : Finset ℤ) (l : ℤ)
    (hsl : ∀ i ∈ s, i < l) :
    (∑ i ∈ s, B ^ i) < B ^ l / (B - 1) := by
  classical
  induction s using Finset.strongInductionOn generalizing l with
  | _ s ih =>
    by_cases hs : s.Nonempty
    · let m := s.max' hs
      have hm : m ∈ s := s.max'_mem hs
      have hrest : ∀ i ∈ s.erase m, i < m := by
        intro i hi
        exact lt_of_le_of_ne (s.le_max' i (mem_of_mem_erase hi)) (ne_of_mem_erase hi)
      have hsum := ih (s.erase m) (erase_ssubset hm) m hrest
      have hml : m + 1 ≤ l := by have := hsl m hm; omega
      have hp : B ^ (m + 1) ≤ B ^ l := zpow_le_zpow_right₀ hB.le hml
      have hden : 0 < B - 1 := sub_pos.mpr hB
      have heq : B ^ m / (B - 1) + B ^ m = B ^ (m + 1) / (B - 1) := by
        rw [zpow_add_one₀ (ne_of_gt (zero_lt_one.trans hB))]
        field_simp
        ring
      calc
        (∑ i ∈ s, B ^ i) = (∑ i ∈ s.erase m, B ^ i) + B ^ m :=
          (sum_erase_add _ _ hm).symm
        _ < B ^ m / (B - 1) + B ^ m := by linarith
        _ = B ^ (m + 1) / (B - 1) := heq
        _ ≤ B ^ l / (B - 1) := div_le_div_of_nonneg_right hp hden.le
    · have he : s = ∅ := not_nonempty_iff_eq_empty.mp hs
      simp only [he, sum_empty]
      exact div_pos (zpow_pos (zero_lt_one.trans hB) _) (sub_pos.mpr hB)

lemma sum_zpow_le_two (B : ℝ) (hB : 2 ≤ B) (s : Finset ℤ) (l : ℤ)
    (hsl : ∀ i ∈ s, i ≤ l) :
    (∑ i ∈ s, B ^ i) ≤ 2 * B ^ l := by
  have hB1 : 1 < B := lt_of_lt_of_le (by norm_num) hB
  have hs := sum_zpow_lt_upper B hB1 s (l+1) (fun i hi => by have := hsl i hi; omega)
  have hp : 0 < B ^ l := zpow_pos (by linarith) _
  have hden : 0 < B - 1 := by linarith
  have hratio : B / (B - 1) ≤ 2 := (div_le_iff₀ hden).mpr (by linarith)
  rw [zpow_add_one₀ (ne_of_gt (zero_lt_one.trans hB1)), mul_div_assoc] at hs
  nlinarith

theorem higher_weight_cost (B : ℝ) (hB : 1 < B) (levels analyzed : Finset ℤ)
    (n : ℤ → ℝ) (hn : ∀ i ∈ levels, 0 ≤ n i) :
    (∑ i ∈ analyzed, B ^ i * ∑ l ∈ levels with i < l, n l) ≤
      (∑ l ∈ levels, B ^ l * n l) / (B - 1) := by
  classical
  have heq : (∑ i ∈ analyzed, B ^ i * ∑ l ∈ levels with i < l, n l) =
      ∑ l ∈ levels, (∑ i ∈ analyzed with i < l, B ^ i) * n l := by
    simp only [sum_filter, mul_sum, sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro l hl
    apply sum_congr rfl
    intro i hi
    split_ifs <;> simp_all
  rw [heq, sum_div]
  apply sum_le_sum
  intro l hl
  have hs := sum_zpow_lt_upper B hB (analyzed.filter (· < l)) l
    (fun i hi => (mem_filter.mp hi).2)
  have hm := mul_le_mul_of_nonneg_right hs.le (hn l hl)
  simpa [div_mul_eq_mul_div] using hm

theorem cumulative_weight_bound {α : Type*} [DecidableEq α]
    (B : ℝ) (hB : 2 ≤ B) (A : Finset α) (level : α → ℤ) (analyzed : Finset ℤ) :
    (∑ i ∈ analyzed, B ^ i * ((A.filter (fun e => i ≤ level e)).card : ℝ)) ≤
      2 * ∑ e ∈ A, B ^ level e := by
  classical
  have heq : (∑ i ∈ analyzed, B ^ i * ((A.filter (fun e => i ≤ level e)).card : ℝ)) =
      ∑ e ∈ A, ∑ i ∈ analyzed with i ≤ level e, B ^ i := by
    simp_rw [sum_filter]
    conv_rhs => rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    rw [← sum_filter]
    simp [mul_comm]
  rw [heq, mul_sum]
  exact sum_le_sum fun e _ => sum_zpow_le_two B hB _ _
    (fun i hi => (mem_filter.mp hi).2)

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Algorithm_Worst
attribute [-instance] _root_.OAI.MatroidProphet.Secretary.uniformArrivalLaw_probability _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset

lemma cumulative_option_weight_bound {α : Type*} [DecidableEq α]
    (B : ℝ) (hB : 2 ≤ B) (A : Finset α) (level : α → Option ℤ) (analyzed : Finset ℤ) :
    (∑ i ∈ analyzed, B ^ i * ((A.filter (fun e => ∃ j, level e = some j ∧ i ≤ j)).card : ℝ)) ≤
      2 * ∑ e ∈ A, levelWeight B (level e) := by
  classical
  let P := A.filter (fun e => level e ≠ none)
  have hfilter (i : ℤ) : P.filter (fun e => i ≤ (level e).getD 0) =
      A.filter (fun e => ∃ j, level e = some j ∧ i ≤ j) := by
    ext e
    cases he : level e <;> simp [P, he]
  have hsum : (∑ e ∈ P, B ^ (level e).getD 0) = ∑ e ∈ A, levelWeight B (level e) := by
    unfold P
    rw [sum_filter]
    apply sum_congr rfl
    intro e he
    cases level e <;> simp [levelWeight]
  have hc := cumulative_weight_bound B hB P (fun e => (level e).getD 0) analyzed
  simpa only [hfilter, hsum] using hc

namespace MainAlgorithm
variable {n : ℕ}

lemma weighted_trueLambda_le_selection (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (analyzed : Finset ℤ) (π : ArrivalOrder n) :
    (1/2 : ℝ) * ∑ i ∈ analyzed, weightBase ^ i * (trueLambda M hE d w i : ℝ) ≤
      ∑ e ∈ selection M hE d w π, levelWeight weightBase (w e) := by
  have hc := cumulative_option_weight_bound weightBase (by norm_num [weightBase])
    (selection M hE d w π) w analyzed
  have hr : (∑ i ∈ analyzed, weightBase ^ i * (trueLambda M hE d w i : ℝ)) ≤
      ∑ i ∈ analyzed, weightBase ^ i *
        (((selection M hE d w π).filter (fun e => ∃ j, w e = some j ∧ i ≤ j)).card : ℝ) := by
    apply sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_left _ (zpow_pos (by norm_num [weightBase]) i).le
    exact_mod_cast trueLambda_le_count M hE d w π i
  linarith

lemma weighted_trueLambda_le_mainWorstRounded (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (analyzed : Finset ℤ) :
    (1/2 : ℝ) * ∑ i ∈ analyzed, weightBase ^ i * (trueLambda M hE d w i : ℝ) ≤
      mainWorstRounded M hE d w := by
  classical
  apply le_inf'
  intro π hπ
  exact weighted_trueLambda_le_selection M hE d w analyzed π

lemma mainMean_sum {β : Type*} (d : MainMasks n) (I : Finset β) (f : β → MainMasks n → ℝ) :
    mainMean d (fun d' => ∑ i ∈ I, f i d') = ∑ i ∈ I, mainMean d (f i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp only [sum_empty, mainMean_const]
  | @insert a I ha ih => simp only [sum_insert ha, mainMean_add, ih]

lemma weighted_mean_trueLambda_le_mainWorstRounded (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (analyzed : Finset ℤ) :
    (1/2 : ℝ) * ∑ i ∈ analyzed, weightBase ^ i * mainMean d (fun d' => (trueLambda M hE d' w i : ℝ)) ≤
      mainMean d (fun d' => mainWorstRounded M hE d' w) := by
  have hh := mainMean_mono d (fun d' _ => weighted_trueLambda_le_mainWorstRounded M hE d' w analyzed)
  simpa only [mainMean_mul, mainMean_sum] using hh

end MainAlgorithm
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_WeightGroups
attribute [-instance] _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open Finset

variable {n : ℕ}

lemma mem_weightLevels (a : Fin n → Option ℤ) (U : Finset (Fin n)) (i : ℤ) :
    i ∈ weightLevels a U ↔ ∃ e ∈ U, a e = some i := by
  classical
  simp [weightLevels]

lemma sum_weightGroups (a : Fin n → Option ℤ) (U : Finset (Fin n))
    (levels : Finset ℤ) (hlevels : weightLevels a U ⊆ levels)
    (f : ℤ → ℝ) :
    (∑ i ∈ levels, f i * ((U.filter fun e => a e = some i).card : ℝ)) =
      ∑ e ∈ U, (a e).elim 0 f := by
  classical
  have heq (i : ℤ) : f i * ((U.filter fun e => a e = some i).card : ℝ) =
      ∑ e ∈ U, if a e = some i then f i else 0 := by
    rw [← Finset.sum_filter]
    simp [mul_comm]
  simp_rw [heq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  cases ha : a e with
  | none => simp
  | some i =>
    have hi : i ∈ levels := hlevels ((mem_weightLevels a U i).2 ⟨e, he, ha⟩)
    simp [hi]

lemma sum_weightGroups_mass (a : Fin n → Option ℤ) (U : Finset (Fin n))
    (levels : Finset ℤ) (hlevels : weightLevels a U ⊆ levels) (B : ℝ) :
    (∑ i ∈ levels, B ^ i * ((U.filter fun e => a e = some i).card : ℝ)) =
      ∑ e ∈ U, levelWeight B (a e) := by
  rw [sum_weightGroups a U levels hlevels]
  apply Finset.sum_congr rfl
  intro e _
  cases a e <;> rfl

lemma highGroup_card (a : Fin n → Option ℤ) (U : Finset (Fin n))
    (levels : Finset ℤ) (hlevels : weightLevels a U ⊆ levels) (i : ℤ) :
    (((U.filter fun e => ∃ j, a e = some j ∧ i < j).card) : ℝ) =
      ∑ j ∈ levels with i < j, ((U.filter fun e => a e = some j).card : ℝ) := by
  classical
  have hs := sum_weightGroups a U levels hlevels (fun j => if i < j then 1 else 0)
  rw [Finset.sum_filter]
  have hleft : (∑ j ∈ levels, (if i < j then 1 else 0) *
      ((U.filter fun e => a e = some j).card : ℝ)) =
      ∑ j ∈ levels, if i < j then ((U.filter fun e => a e = some j).card : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  rw [hleft] at hs
  rw [hs]
  have hcount : (((U.filter fun e => ∃ j, a e = some j ∧ i < j).card) : ℝ) =
      ∑ e ∈ U, if (∃ j, a e = some j ∧ i < j) then 1 else 0 := by simp
  rw [hcount]
  apply Finset.sum_congr rfl
  intro e _
  cases a e <;> simp

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_WeightedPayoff
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open Finset

lemma weighted_group_payoff (B t κ γ a b ε : ℝ)
    (hB : 1 < B) (ht : 0 ≤ t) (hκ : 0 < κ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (herr : a + b / (B - 1) ≤ ε)
    (levels analyzed : Finset ℤ) (hsub : analyzed ⊆ levels)
    (N Y Λ : ℤ → ℝ) (hN : ∀ i ∈ levels, 0 ≤ N i)
    (hgroup : ∀ i ∈ analyzed,
      t / κ * (γ * Y i - a * N i - b * ∑ l ∈ levels with i < l, N l) ≤ Λ i) :
    t / (2 * κ) * (γ * ∑ i ∈ analyzed, B ^ i * Y i - ε * ∑ i ∈ levels, B ^ i * N i) ≤
      (1 / 2 : ℝ) * ∑ i ∈ analyzed, B ^ i * Λ i := by
  have hB0 : 0 < B := zero_lt_one.trans hB
  have htotal : 0 ≤ ∑ i ∈ levels, B ^ i * N i :=
    Finset.sum_nonneg fun i hi => mul_nonneg (zpow_pos hB0 i).le (hN i hi)
  have hNsum : (∑ i ∈ analyzed, B ^ i * N i) ≤ ∑ i ∈ levels, B ^ i * N i :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ =>
      mul_nonneg (zpow_pos hB0 i).le (hN i hi))
  have hcost := higher_weight_cost B hB levels analyzed N hN
  have herrors : a * (∑ i ∈ analyzed, B ^ i * N i) +
      b * (∑ i ∈ analyzed, B ^ i * ∑ l ∈ levels with i < l, N l) ≤
      ε * ∑ i ∈ levels, B ^ i * N i := by
    calc
      _ ≤ a * (∑ i ∈ levels, B ^ i * N i) +
          b * ((∑ i ∈ levels, B ^ i * N i) / (B - 1)) :=
        add_le_add (mul_le_mul_of_nonneg_left hNsum ha) (mul_le_mul_of_nonneg_left hcost hb)
      _ = (a + b / (B - 1)) * ∑ i ∈ levels, B ^ i * N i := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right herr htotal
  have hsum : (∑ i ∈ analyzed,
      B ^ i * (t / κ * (γ * Y i - a * N i - b * ∑ l ∈ levels with i < l, N l))) ≤
      ∑ i ∈ analyzed, B ^ i * Λ i :=
    Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hgroup i hi) (zpow_pos hB0 i).le
  have heq : (∑ i ∈ analyzed,
      B ^ i * (t / κ * (γ * Y i - a * N i - b * ∑ l ∈ levels with i < l, N l))) =
      t / κ * (γ * (∑ i ∈ analyzed, B ^ i * Y i) -
        (a * (∑ i ∈ analyzed, B ^ i * N i) +
          b * (∑ i ∈ analyzed, B ^ i * ∑ l ∈ levels with i < l, N l))) := by
    have hi (i : ℤ) : B ^ i * (t / κ * (γ * Y i - a * N i -
        b * ∑ l ∈ levels with i < l, N l)) =
        (t / κ * γ) * (B ^ i * Y i) - (t / κ * a) * (B ^ i * N i) -
          (t / κ * b) * (B ^ i * ∑ l ∈ levels with i < l, N l) := by ring
    simp_rw [hi]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  rw [heq] at hsum
  have hbudget := mul_le_mul_of_nonneg_left
    (sub_le_sub_left herrors (γ * ∑ i ∈ analyzed, B ^ i * Y i)) (div_nonneg ht hκ.le)
  have hresult := hbudget.trans hsum
  calc
    _ = (1 / 2 : ℝ) * (t / κ *
        (γ * ∑ i ∈ analyzed, B ^ i * Y i - ε * ∑ i ∈ levels, B ^ i * N i)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hresult (by norm_num)

lemma source_weighted_group_payoff (levels analyzed : Finset ℤ) (hsub : analyzed ⊆ levels)
    (N Y Λ : ℤ → ℝ) (hN : ∀ i ∈ levels, 0 ≤ N i)
    (hgroup : ∀ i ∈ analyzed,
      thinningRate / densityThreshold *
        (retainedFraction * Y i - (((2 : ℝ) ^ 23)⁻¹ + thinningRate * densityThreshold) * N i -
          (1 + thinningRate * densityThreshold) * ∑ l ∈ levels with i < l, N l) ≤ Λ i) :
    thinningRate / (2 * densityThreshold) *
      (retainedFraction * ∑ i ∈ analyzed, weightBase ^ i * Y i -
        ((2 : ℝ) ^ 21)⁻¹ * ∑ i ∈ levels, weightBase ^ i * N i) ≤
      (1 / 2 : ℝ) * ∑ i ∈ analyzed, weightBase ^ i * Λ i := by
  apply weighted_group_payoff weightBase thinningRate densityThreshold retainedFraction
    (((2 : ℝ) ^ 23)⁻¹ + thinningRate * densityThreshold) (1 + thinningRate * densityThreshold)
    (((2 : ℝ) ^ 21)⁻¹) (by norm_num [weightBase])
    constants_positive.2.2.1.le constants_positive.2.1
  · norm_num [thinningRate, densityThreshold]
  · norm_num [thinningRate, densityThreshold]
  · exact error_constant.le
  · exact hsub
  · exact hN
  · exact hgroup

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_SafeStatistics
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset Pivots
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

omit [DecidableEq α] in
lemma nominalBirth_eq_iff_departure (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (d : α) (hd : d ∉ M.closure ∅) (b : ℤ) :
    nominalBirth M hE κ D C h d = b ↔
      d ∈ nominalPath M hE κ D C h b ∧ d ∉ nominalPath M hE κ D C h (b-1) := by
  rw [mem_nominal_iff_birth_le M hE κ D C h d hd b,
    mem_nominal_iff_birth_le M hE κ D C h d hd (b-1)]
  omega

omit [DecidableEq α] in
lemma isSafeSample_iff_window (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (U : Set α) (I C T : Finset α)
    (hIU : (I : Set α) ⊆ U) (d : α) (hdI : d ∈ I) (hd : d ∉ M.closure ∅) (parity : Bool) :
    IsSafeSample M hE κ D G h d C T parity ↔
      ∃ b : ParityWindow (activation h) (boolParity parity),
        d ∈ safeLayerSet M hE κ D (fun i => (C : Set α) ∩ (G i : Set α))
          (fun i => (T : Set α) ∩ (G i : Set α)) h U (I : Set α) (boolParity parity) b := by
  constructor
  · intro hs
    obtain ⟨hlo, hhi, hp, hex⟩ := hs
    let birth := nominalBirth M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h d
    have hbwin : birth ∈ Set.Icc (activation h-2) 1 := by
      change activation h+2 ≤ birth at hlo
      change birth ≤ 0 at hhi
      constructor <;> omega
    have hbpar : birth % 2 = ((boolParity parity).val : ℤ) := by
      rw [boolParity_val]
      exact hp
    refine ⟨⟨⟨birth, hbwin⟩, hbpar⟩, ?_⟩
    have hdep := (nominalBirth_eq_iff_departure M hE κ D _ h d hd birth).mp rfl
    exact ⟨⟨hdI, hIU hdI, hlo, hhi, hdep.1, hdep.2⟩, hex⟩
  · rintro ⟨b, hb⟩
    rcases hb with ⟨⟨_, _, hlo, hhi, hmem, hnot⟩, hex⟩
    have hbirth := (nominalBirth_eq_iff_departure M hE κ D _ h d hd b.val.val).mpr ⟨hmem, hnot⟩
    unfold IsSafeSample
    rw [hbirth]
    have hp := b.property.trans (boolParity_val parity)
    exact ⟨hlo, hhi, hp, hex⟩

theorem safeSampleCount_eq_layerStatistic
    {α : Type u_1} [Fintype α] [DecidableEq α] (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (U : Set α) (I C T : Finset α)
    (hIU : (I : Set α) ⊆ U) (hIL : ∀ d ∈ I, d ∉ M.closure ∅) (parity : Bool) :
    safeSampleCount M hE κ D G h I C T parity =
      (safeLayerStatistic M hE κ D (fun i => (C : Set α) ∩ (G i : Set α))
        (fun i => (T : Set α) ∩ (G i : Set α)) h U (I : Set α) (boolParity parity) : ℝ) := by
  let W := ParityWindow (activation h) (boolParity parity)
  let L : W → Set α := safeLayerSet M hE κ D (fun i => (C : Set α) ∩ (G i : Set α))
    (fun i => (T : Set α) ∩ (G i : Set α)) h U (I : Set α) (boolParity parity)
  have hcount (b : W) : (L b).ncard = (I.filter (fun d => d ∈ L b)).card := by
    have hs : L b = ((I.filter (fun d => d ∈ L b) : Finset α) : Set α) := by
      ext d
      constructor
      · intro hd
        exact mem_filter.mpr ⟨hd.1.1, hd⟩
      · intro hd
        exact (mem_filter.mp hd).2
    exact (congrArg Set.ncard hs).trans (Set.ncard_coe_finset _)
  have hlabel (d : α) (hd : d ∈ I) :
      (∑ b : W, if d ∈ L b then (1:ℝ) else 0) = if IsSafeSample M hE κ D G h d C T parity then 1 else 0 := by
    rw [sum_unique_indicators]
    · have he : (∃ b ∈ (univ : Finset W), d ∈ L b) ↔ IsSafeSample M hE κ D G h d C T parity := by
        simp only [mem_univ, true_and]
        exact (isSafeSample_iff_window M hE κ D G h U I C T hIU d hd (hIL d hd) parity).symm
      simp only [he]
    · intro b hb c hc hdb hdc
      by_contra hbc
      have hdisj := nominalLayerSet_disjoint M hE κ D (fun i => (C : Set α) ∩ (G i : Set α))
        h U (boolParity parity) hbc
      exact Set.disjoint_left.mp hdisj hdb.1.2 hdc.1.2
  calc
    safeSampleCount M hE κ D G h I C T parity =
        ∑ d ∈ I, if IsSafeSample M hE κ D G h d C T parity then (1:ℝ) else 0 := by
      rw [safeSampleCount_eq_card]
      simp [safeSampleSet]
    _ = ∑ d ∈ I, ∑ b : W, if d ∈ L b then (1:ℝ) else 0 :=
      sum_congr rfl (fun d hd => (hlabel d hd).symm)
    _ = ∑ b : W, ∑ d ∈ I, if d ∈ L b then (1:ℝ) else 0 := sum_comm
    _ = ∑ b : W, ((L b).ncard : ℝ) := by
      apply sum_congr rfl
      intro b hb
      rw [hcount]
      simp
    _ = _ := by simp only [safeLayerStatistic, Nat.cast_sum]; rfl

theorem safeLayerStatistic_lower (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (h : ℕ) (U I : Set α) (hIU : I ⊆ U) (hI : M.Indep I) :
    (((2:ℝ)^12)⁻¹) / 4 * I.ncard - (D h).ncard / (κ:ℝ) ≤
      bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
        fairParityExpectation (fun parity => (safeLayerStatistic M hE κ D
          (fun i => (C : Set α) ∩ (G i : Set α)) (fun i => (T : Set α) ∩ (G i : Set α))
          h U I (boolParity parity) : ℝ)))) := by
  let J := I.toFinset
  have hJI : (J : Set α) = I := by simp [J]
  have hJcard : J.card = I.ncard := by rw [← Set.ncard_coe_finset, hJI]
  have hJ : M.Indep (J : Set α) := hJI.symm ▸ hI
  have hJU : (J : Set α) ⊆ U := hJI.symm ▸ hIU
  have hl := safeSampleCount_lower M hE κ hκ D G hG q hq0 hq1 h J hJ
  rw [hJcard] at hl
  have heq : bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
      fairParityExpectation (safeSampleCount M hE κ D G h J C T))) =
      bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
        fairParityExpectation (fun parity => (safeLayerStatistic M hE κ D
          (fun i => (C : Set α) ∩ (G i : Set α)) (fun i => (T : Set α) ∩ (G i : Set α))
          h U I (boolParity parity) : ℝ)))) := by
    apply bitsExpectation_congr
    intro C hC
    apply bitsExpectation_congr
    intro T hT
    congr 1
    funext parity
    rw [safeSampleCount_eq_layerStatistic M hE κ D G h U J C T hJU
      (fun d hd => indep_not_loop M J hJ hd) parity, hJI]
  exact hl.trans_eq heq

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_GroupSafety
attribute [-instance] _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.MainAlgorithm
open Finset
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

lemma mem_groupGround (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (j : ℕ) (e : Fin n) :
    e ∈ groupGround M d s j ↔ candidate M d s e (s e) ∧ s e = (groups M d s)[j]? := by
  rw [groupGround, Set.mem_toFinset]
  simp [groupMask]

lemma groupGround_disjoint (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) : Pairwise (fun i j => Disjoint (groupGround M d s i) (groupGround M d s j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro e hei hej
  obtain ⟨hc, hei⟩ := (mem_groupGround M d s i e).mp hei
  obtain ⟨_, hej⟩ := (mem_groupGround M d s j e).mp hej
  have hi : i < (groups M d s).length := by
    by_contra hi
    exact hc.1 (hei.trans (List.getElem?_eq_none (by omega)))
  exact hij ((List.getElem?_inj hi (groups_nodup M d s)).mp (hei.symm.trans hej))

lemma groupMask_eq_inter_ground (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (A : Finset (Fin n)) (j : ℕ) :
    groupMask M d s A j = (A : Set (Fin n)) ∩ (groupGround M d s j : Set (Fin n)) := by
  ext e
  simp only [groupMask, Set.mem_ofPred_eq, Set.mem_inter_iff, Finset.mem_coe, mem_groupGround]

lemma listedSafeStatistic_guards (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (Y : Set (Fin n)) (ε : Fin 2) (C T : Finset (Fin n))
    (hi : i ∈ groups M d s) :
    listedSafeStatistic M hE κ (withMasks d d.D C T) s i Y ε =
      safeLayerStatistic M hE κ (groupMask M d s d.D)
        (fun j => (C : Set (Fin n)) ∩ (groupGround M d s j : Set (Fin n)))
        (fun j => (T : Set (Fin n)) ∩ (groupGround M d s j : Set (Fin n)))
        ((groups M d s).idxOf i) (trueGroup M d s i : Set (Fin n))
        ((d.D : Set (Fin n)) ∩ Y) ε := by
  change (if i ∈ groups M d s then _ else _) = _
  rw [ite_eq_left hi]
  change safeLayerStatistic M hE κ (groupMask M d s d.D)
    (groupMask M d s C) (groupMask M d s T) ((groups M d s).idxOf i)
    (trueGroup M d s i : Set (Fin n)) ((d.D : Set (Fin n)) ∩ Y) ε = _
  congr 1
  · funext j
    exact groupMask_eq_inter_ground M d s C j
  · funext j
    exact groupMask_eq_inter_ground M d s T j

lemma unlisted_density_inter_empty (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) (hi : i ∉ groups M d s)
    (Y : Set (Fin n)) (hY : Y ⊆ (trueGroup M d s i : Set (Fin n))) :
    (d.D : Set (Fin n)) ∩ Y = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro e ⟨heD, heY⟩
  exact hi ((mem_groups M d s i).mpr ((mem_listed_iff M d s i).mpr ⟨e, heD, hY heY⟩))

theorem listedSafeStatistic_fixed_density (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (Y : Set (Fin n)) (hY : Y ⊆ (trueGroup M d s i : Set (Fin n))) (hI : M.Indep Y)
    (q : Fin n → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) :
    (((2:ℝ)^12)⁻¹) / 4 * ((d.D : Set (Fin n)) ∩ Y).ncard -
        (trueGroup M d s i).card / (κ:ℝ) ≤
      bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
        fairParityExpectation (fun p =>
          (listedSafeStatistic M hE κ (withMasks d d.D C T) s i Y (boolParity p) : ℝ)))) := by
  by_cases hi : i ∈ groups M d s
  · have hsafe := safeLayerStatistic_lower M hE κ hκ (groupMask M d s d.D)
      (groupGround M d s) (groupGround_disjoint M d s) q hq0 hq1
      ((groups M d s).idxOf i) (trueGroup M d s i : Set (Fin n))
      ((d.D : Set (Fin n)) ∩ Y) (Set.inter_subset_right.trans hY) (hI.subset Set.inter_subset_right)
    have hcard : (groupMask M d s d.D ((groups M d s).idxOf i)).ncard ≤ (trueGroup M d s i).card := by
      rw [groupMask_at_key M d s d.D _ i (groups_get?_idxOf M d s i hi), Set.ncard_coe_finset]
      exact card_le_card inter_subset_right
    have hdiv : ((groupMask M d s d.D ((groups M d s).idxOf i)).ncard : ℝ) / (κ:ℝ) ≤
        (trueGroup M d s i).card / (κ:ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hcard) (Nat.cast_nonneg κ)
    have heq : bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
        fairParityExpectation (fun p =>
          (listedSafeStatistic M hE κ (withMasks d d.D C T) s i Y (boolParity p) : ℝ)))) =
        bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
          fairParityExpectation (fun p => (safeLayerStatistic M hE κ (groupMask M d s d.D)
            (fun j => (C : Set (Fin n)) ∩ (groupGround M d s j : Set (Fin n)))
            (fun j => (T : Set (Fin n)) ∩ (groupGround M d s j : Set (Fin n)))
            ((groups M d s).idxOf i) (trueGroup M d s i : Set (Fin n))
            ((d.D : Set (Fin n)) ∩ Y) (boolParity p) : ℝ)))) := by
      apply bitsExpectation_congr
      intro C hC
      apply bitsExpectation_congr
      intro T hT
      congr 1
      funext p
      rw [listedSafeStatistic_guards M hE κ d s i Y (boolParity p) C T hi]
    rw [heq]
    exact (sub_le_sub_left hdiv _).trans hsafe
  · have hempty := unlisted_density_inter_empty M d s i hi Y hY
    have hzero (C T : Finset (Fin n)) (p : Bool) :
        listedSafeStatistic M hE κ (withMasks d d.D C T) s i Y (boolParity p) = 0 := by
      change (if i ∈ groups M d s then _ else 0) = 0
      rw [ite_eq_right hi]
    simp only [hempty, Set.ncard_empty, Nat.cast_zero, mul_zero, zero_sub, hzero,
      fairParityExpectation, zero_add, zero_div, bitsExpectation_const]
    exact neg_nonpos.mpr (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

theorem listedSafeStatistic_lower (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (Y : Set (Fin n)) (hY : Y ⊆ (trueGroup M d s i : Set (Fin n))) (hI : M.Indep Y)
    (q : Fin n → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) :
    retainedFraction * Y.ncard - (trueGroup M d s i).card / (κ:ℝ) ≤
      tripleMaskExpectation (fun _ => (1:ℝ)/4) q q univ (fun D C T =>
        fairParityExpectation (fun p =>
          (listedSafeStatistic M hE κ (withMasks d D C T) s i Y (boolParity p) : ℝ))) := by
  have hfixed (D : Finset (Fin n)) :
      (((2:ℝ)^12)⁻¹) / 4 * ((D : Set (Fin n)) ∩ Y).ncard -
          (trueGroup M d s i).card / (κ:ℝ) ≤
        bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
          fairParityExpectation (fun p =>
            (listedSafeStatistic M hE κ (withMasks d D C T) s i Y (boolParity p) : ℝ)))) :=
    listedSafeStatistic_fixed_density M hE κ hκ (withMasks d D ∅ ∅) s i Y hY hI q hq0 hq1
  have hmean := bitsExpectation_mono (fun _ : Fin n => (1:ℝ)/4) (by intro e; norm_num)
    (by intro e; norm_num) univ (fun D _ => hfixed D)
  have hcard : bitsExpectation (fun _ : Fin n => (1:ℝ)/4) univ
      (fun D => (((D : Set (Fin n)) ∩ Y).ncard : ℝ)) = Y.ncard / 4 := by
    have hset (D : Finset (Fin n)) : (D : Set (Fin n)) ∩ Y =
        ((Y.toFinset ∩ D : Finset (Fin n)) : Set (Fin n)) := by
      ext e
      simp only [Set.mem_inter_iff, Finset.mem_coe, mem_inter, Set.mem_toFinset]
      exact and_comm
    simp only [hset, Set.ncard_coe_finset]
    rw [bitsExpectation_card_inter (fun _ : Fin n => (1:ℝ)/4) univ Y.toFinset (subset_univ _)]
    simp only [sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card']
    ring
  have hnum : (((2:ℝ)^12)⁻¹) / 4 / 4 = retainedFraction := by
    norm_num [retainedFraction]
  have heq : bitsExpectation (fun _ : Fin n => (1:ℝ)/4) univ
      (fun D => (((2:ℝ)^12)⁻¹) / 4 * ((D : Set (Fin n)) ∩ Y).ncard -
        (trueGroup M d s i).card / (κ:ℝ)) =
      retainedFraction * Y.ncard - (trueGroup M d s i).card / (κ:ℝ) := by
    simp only [sub_eq_add_neg, bitsExpectation_add, bitsExpectation_mul_const,
      bitsExpectation_const, hcard]
    congr 1
    calc
      (((2:ℝ)^12)⁻¹) / 4 * (Y.ncard / 4) =
        ((((2:ℝ)^12)⁻¹) / 4 / 4) * Y.ncard := by ring
      _ = retainedFraction * Y.ncard := by rw [hnum]
  rw [heq] at hmean
  exact hmean

end MatroidProphet.MainAlgorithm

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_GroupTransfer
attribute [-instance] _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.MainAlgorithm
open Finset
variable {n : ℕ}

lemma listedSafe_le_rank_gap (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (Y : Set (Fin n)) (ε : Fin 2) :
    (listedSafeStatistic M hE κ d s i Y ε : ℝ) ≤
      (κ : ℝ) * listedRankStatistic M hE κ d s i ε + listedTransferGap M hE κ d s i Y ε := by
  unfold listedTransferGap
  have hh := le_max_left ((listedSafeStatistic M hE κ d s i Y ε : ℝ) -
    (κ : ℝ) * listedRankStatistic M hE κ d s i ε) 0
  linarith

theorem listedRankStatistic_lower (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ) (Y : Set (Fin n))
    (hY : Y ⊆ (trueGroup M d s i : Set (Fin n))) (hI : M.Indep Y)
    (hn : densityThreshold ≤ ((trueGroup M d s i).card : ℝ)) :
    (retainedFraction * Y.ncard - ((2:ℝ)^23)⁻¹ * (trueGroup M d s i).card) / densityThreshold ≤
      tripleMaskExpectation (fun _ => (1:ℝ)/4) (fun _ => thinningRate) (fun _ => thinningRate)
        univ (fun D C T => fairParityExpectation (fun p =>
          (listedRankStatistic M hE (2^100) (withMasks d D C T) s i (boolParity p) : ℝ))) := by
  have ht0 : 0 ≤ thinningRate := constants_positive.2.2.1.le
  have ht1 : thinningRate ≤ 1 := by norm_num [thinningRate]
  have hsafe := listedSafeStatistic_lower M hE (2^100) (by positivity) d s i Y hY hI
    (fun _ => thinningRate) (fun _ => ht0) (fun _ => ht1)
  have herr := listedTransferGap_parity_expectation_le M hE d s i Y hY hn
  have hkcast : ((2^100 : ℕ) : ℝ) = densityThreshold := by
    simp only [Nat.cast_pow, Nat.cast_ofNat, densityThreshold]
  rw [hkcast] at hsafe
  have hdet (D C T : Finset (Fin n)) :
      fairParityExpectation (fun p => (listedSafeStatistic M hE (2^100)
        (withMasks d D C T) s i Y (boolParity p) : ℝ)) ≤
      densityThreshold * fairParityExpectation (fun p => (listedRankStatistic M hE (2^100)
        (withMasks d D C T) s i (boolParity p) : ℝ)) +
      fairParityExpectation (fun p => listedTransferGap M hE (2^100)
        (withMasks d D C T) s i Y (boolParity p)) := by
    have h0 := listedSafe_le_rank_gap M hE (2^100) (withMasks d D C T) s i Y (boolParity false)
    have h1 := listedSafe_le_rank_gap M hE (2^100) (withMasks d D C T) s i Y (boolParity true)
    rw [hkcast] at h0 h1
    dsimp only [fairParityExpectation]
    calc
      _ ≤ _ := div_le_div_of_nonneg_right (add_le_add h0 h1) (by norm_num : (0:ℝ) ≤ 2)
      _ = _ := by ring
  have hmean := tripleMaskExpectation_mono (fun _ : Fin n => (1:ℝ)/4)
    (fun _ => thinningRate) (fun _ => thinningRate) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => ht0) (fun _ => ht1) (fun _ => ht0) (fun _ => ht1) univ
    (fun D _ C _ T _ => hdet D C T)
  rw [tripleMaskExpectation_add, tripleMaskExpectation_mul] at hmean
  have hc := mul_le_mul_of_nonneg_right residual_error_constant
    (Nat.cast_nonneg (trueGroup M d s i).card)
  apply (div_le_iff₀ constants_positive.2.1).2
  rw [div_eq_mul_inv] at hsafe
  nlinarith

end MatroidProphet.MainAlgorithm

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_GroupPayoff
attribute [-instance] _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.MainAlgorithm
open Finset
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

lemma trueGroup_eq_candidate_filter (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (i : ℤ) :
    trueGroup M d w i = (candidateLabels M w d.H).filter (fun e => w e = some i) := by
  unfold trueGroup candidateLabels candidateSet
  ext e
  simp only [mem_filter, mem_univ, true_and]
  rfl

lemma trueZ_eq_listedRankStatistic (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (i : ℤ) :
    trueZ M hE d w i = listedRankStatistic M hE (2^100) d w i (boolParity d.odd) := by
  unfold trueZ listedRankStatistic
  split_ifs with hi
  · unfold listedZ
    rw [groupMask_at_key M d w univ _ i (groups_get?_idxOf M d w i hi), univ_inter]
  · rfl

lemma mainMean_trueZ (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (i : ℤ) :
    mainMean d (fun d' => (trueZ M hE d' w i : ℝ)) =
      tripleMaskExpectation (fun _ => (1:ℝ)/4) (fun _ => thinningRate) (fun _ => thinningRate)
        univ (fun D C T => fairParityExpectation (fun p =>
          (listedRankStatistic M hE (2^100) (withMasks d D C T) w i (boolParity p) : ℝ))) := by
  unfold mainMean
  apply tripleMaskExpectation_congr
  intro D hD C hC T hT
  congr 1
  funext p
  dsimp only
  rw [trueZ_eq_listedRankStatistic]
  rfl

theorem mainMean_trueZ_lower (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (i : ℤ)
    (Y : Set (Fin n)) (hY : Y ⊆ (trueGroup M d w i : Set (Fin n))) (hI : M.Indep Y)
    (hn : densityThreshold ≤ ((trueGroup M d w i).card : ℝ)) :
    (retainedFraction * Y.ncard - ((2:ℝ)^23)⁻¹ * (trueGroup M d w i).card) / densityThreshold ≤
      mainMean d (fun d' => (trueZ M hE d' w i : ℝ)) := by
  rw [mainMean_trueZ]
  exact listedRankStatistic_lower M hE d w i Y hY hI hn

lemma true_expected_nominal_to_final (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (i : ℤ)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    densityThreshold * t * bitsExpectation (fun _ : Fin n => t) univ (fun T =>
      (trueZ M hE {d with T := T} w i : ℝ)) ≤
    densityThreshold * bitsExpectation (fun _ : Fin n => t) univ (fun T =>
      (trueLambda M hE {d with T := T} w i : ℝ)) +
      t * (densityThreshold * (d.C ∩ trueGroup M d w i).card +
        densityThreshold * (d.C ∩ higherTrueGroups M d w i).card +
          (higherTrueGroups M d w i).card) := by
  by_cases hi : i ∈ groups M d w
  · have hh : (groups M d w).idxOf i < (groups M d w).length := List.idxOf_lt_length_of_mem hi
    have hl := listed_expected_nominal_to_final M hE d w _ hh t ht0 ht1
    have hc := listed_cost_le_true_counts M d w (groups_get?_idxOf M d w i hi) (2^100)
    rw [← trueGroup_eq_candidate_filter M d w i] at hc
    have hc' : (((2^100) * (groupMask M d w d.C ((groups M d w).idxOf i)).ncard +
        ∑ j ∈ range ((groups M d w).length-((groups M d w).idxOf i+1)),
          ((2^100) * (groupMask M d w d.C ((groups M d w).idxOf i+1+j)).ncard +
            (groupMask M d w d.D ((groups M d w).idxOf i+1+j)).ncard) : ℕ) : ℝ) ≤
        densityThreshold * (d.C ∩ trueGroup M d w i).card +
          densityThreshold * (d.C ∩ higherTrueGroups M d w i).card +
            (higherTrueGroups M d w i).card := by
      calc
        _ ≤ (((2^100) * (d.C ∩ trueGroup M d w i).card +
          (2^100) * (d.C ∩ higherTrueGroups M d w i).card +
          (higherTrueGroups M d w i).card : ℕ) : ℝ) := by exact_mod_cast hc
        _ = _ := by norm_num [densityThreshold]
    have hz (T : Finset (Fin n)) : trueZ M hE {d with T := T} w i =
        listedZ M hE {d with T := T} w ((groups M d w).idxOf i) := by
      change (if i ∈ groups M d w then _ else 0) = _
      rw [ite_eq_left hi]
      rfl
    have hLam (T : Finset (Fin n)) : trueLambda M hE {d with T := T} w i =
        listedLambda M hE {d with T := T} w ((groups M d w).idxOf i) := by
      change (if i ∈ groups M d w then _ else 0) = _
      rw [ite_eq_left hi]
      rfl
    simp only [hz, hLam]
    exact hl.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hc' ht0))
  · have hz (T : Finset (Fin n)) : trueZ M hE {d with T := T} w i = 0 := by
      change (if i ∈ groups M d w then _ else 0) = _
      rw [ite_eq_right hi]
    have hLam (T : Finset (Fin n)) : trueLambda M hE {d with T := T} w i = 0 := by
      change (if i ∈ groups M d w then _ else 0) = _
      rw [ite_eq_right hi]
    simp only [hz, hLam, Nat.cast_zero, bitsExpectation_const, mul_zero, zero_add]
    apply mul_nonneg ht0
    exact add_nonneg (add_nonneg
      (mul_nonneg constants_positive.2.1.le (Nat.cast_nonneg _))
      (mul_nonneg constants_positive.2.1.le (Nat.cast_nonneg _))) (Nat.cast_nonneg _)

lemma trueGroup_eq_of_H_eq (M : Matroid (Fin n)) (d d' : MainMasks n)
    (w : Fin n → Option ℤ) (i : ℤ) (hH : d'.H = d.H) :
    trueGroup M d' w i = trueGroup M d w i := by
  rw [trueGroup_eq_candidate_filter, trueGroup_eq_candidate_filter, hH]

lemma higherTrueGroups_eq_of_H_eq (M : Matroid (Fin n)) (d d' : MainMasks n)
    (w : Fin n → Option ℤ) (i : ℤ) (hH : d'.H = d.H) :
    higherTrueGroups M d' w i = higherTrueGroups M d w i := by
  simp only [higherTrueGroups, hH]

lemma mainMean_resample_test (d : MainMasks n) (f : MainMasks n → ℝ) :
    mainMean d (fun d' => bitsExpectation (fun _ : Fin n => thinningRate) univ
      (fun T => f {d' with T := T})) = mainMean d f := by
  unfold mainMean tripleMaskExpectation
  apply bitsExpectation_congr
  intro D hD
  apply bitsExpectation_congr
  intro C hC
  change bitsExpectation (fun _ : Fin n => thinningRate) univ (fun _ =>
      fairParityExpectation (fun p => bitsExpectation (fun _ : Fin n => thinningRate) univ
        (fun T => f {withMasks d D C T with odd := p}))) = _
  rw [bitsExpectation_const, ← bitsExpectation_fairParity]

theorem mainMean_nominal_to_final (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (i : ℤ) :
    densityThreshold * thinningRate * mainMean d (fun d' => (trueZ M hE d' w i : ℝ)) ≤
      densityThreshold * mainMean d (fun d' => (trueLambda M hE d' w i : ℝ)) +
        thinningRate * (densityThreshold * thinningRate * (trueGroup M d w i).card +
          densityThreshold * thinningRate * (higherTrueGroups M d w i).card +
            (higherTrueGroups M d w i).card) := by
  have hmean : mainMean d (fun d' => densityThreshold * thinningRate *
      bitsExpectation (fun _ : Fin n => thinningRate) univ (fun T =>
        (trueZ M hE {d' with T := T} w i : ℝ))) ≤
      mainMean d (fun d' => densityThreshold *
        bitsExpectation (fun _ : Fin n => thinningRate) univ (fun T =>
          (trueLambda M hE {d' with T := T} w i : ℝ)) +
        thinningRate * (densityThreshold * (d'.C ∩ trueGroup M d w i).card +
          densityThreshold * (d'.C ∩ higherTrueGroups M d w i).card +
            (higherTrueGroups M d w i).card)) := by
    apply mainMean_mono
    intro d' hH
    have hp := true_expected_nominal_to_final M hE d' w i thinningRate
      constants_positive.2.2.1.le (by norm_num [thinningRate])
    rwa [trueGroup_eq_of_H_eq M d d' w i hH,
      higherTrueGroups_eq_of_H_eq M d d' w i hH] at hp
  simp only [mainMean_add, mainMean_mul, mainMean_const, mainMean_guard_count] at hmean
  rw [mainMean_resample_test d (fun d' => (trueZ M hE d' w i : ℝ)),
    mainMean_resample_test d (fun d' => (trueLambda M hE d' w i : ℝ))] at hmean
  simpa only [mul_assoc] using hmean

theorem true_group_payoff (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (i : ℤ)
    (Y : Set (Fin n)) (hY : Y ⊆ (trueGroup M d w i : Set (Fin n))) (hI : M.Indep Y)
    (hn : densityThreshold ≤ ((trueGroup M d w i).card : ℝ)) :
    thinningRate / densityThreshold *
        (retainedFraction * Y.ncard -
          (((2:ℝ)^23)⁻¹ + thinningRate * densityThreshold) * (trueGroup M d w i).card -
          (1 + thinningRate * densityThreshold) * (higherTrueGroups M d w i).card) ≤
      mainMean d (fun d' => (trueLambda M hE d' w i : ℝ)) := by
  have hZ := mainMean_trueZ_lower M hE d w i Y hY hI hn
  have hcost := mainMean_nominal_to_final M hE d w i
  have hk : 0 < densityThreshold := constants_positive.2.1
  have ht : 0 ≤ thinningRate := constants_positive.2.2.1.le
  have hmul := mul_le_mul_of_nonneg_left hZ (mul_nonneg hk.le ht)
  have hcancel : densityThreshold * thinningRate *
      ((retainedFraction * Y.ncard - ((2:ℝ)^23)⁻¹ * (trueGroup M d w i).card) / densityThreshold) =
      thinningRate * (retainedFraction * Y.ncard - ((2:ℝ)^23)⁻¹ * (trueGroup M d w i).card) := by
    field_simp
  rw [hcancel] at hmul
  have hboth := hmul.trans hcost
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hk).mpr
  nlinarith [hboth]

end MatroidProphet.MainAlgorithm

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Algorithm_WeightedPayoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.MainAlgorithm
open Finset
variable {n : ℕ}

lemma higherTrueGroups_card_eq_sum (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (i : ℤ) :
    ((higherTrueGroups M d w i).card : ℝ) =
      ∑ j ∈ trueLevels M w d.H with i < j, ((trueGroup M d w j).card : ℝ) := by
  simp only [trueGroup_eq_candidate_filter, higherTrueGroups]
  exact highGroup_card w (candidateLabels M w d.H) (trueLevels M w d.H) Subset.rfl i

theorem conditional_main_payoff_oai (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) :
    thinningRate / (2 * densityThreshold) *
      (retainedFraction * analyzedComparisonMass M w d.H - ((2:ℝ)^21)⁻¹ *
        ∑ e ∈ candidateLabels M w d.H, levelWeight weightBase (w e)) ≤
      mainMean d (fun d' => mainWorstRounded M hE d' w) := by
  classical
  let J := positiveGreedy M w \ d.H
  let Y : ℤ → Finset (Fin n) := fun i => J.filter (fun e => w e = some i)
  have hY (i : ℤ) : (Y i : Set (Fin n)) ⊆ (trueGroup M d w i : Set (Fin n)) := by
    rw [trueGroup_eq_candidate_filter]
    intro e he
    obtain ⟨heJ, hew⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨positiveGreedy_survivors_subset M w d.H heJ, hew⟩
  have hI (i : ℤ) : M.Indep (Y i : Set (Fin n)) :=
    (positiveGreedy_survivors_indep M hE w d.H).subset (filter_subset _ _)
  have hgroup (i : ℤ) (hi : i ∈ analyzedLevels M w d.H) :
      thinningRate / densityThreshold *
        (retainedFraction * (Y i).card -
          (((2:ℝ)^23)⁻¹ + thinningRate * densityThreshold) * (trueGroup M d w i).card -
          (1 + thinningRate * densityThreshold) *
            ∑ l ∈ trueLevels M w d.H with i < l, ((trueGroup M d w l).card : ℝ)) ≤
        mainMean d (fun d' => (trueLambda M hE d' w i : ℝ)) := by
    have hn : densityThreshold ≤ ((trueGroup M d w i).card : ℝ) := by
      rw [trueGroup_eq_candidate_filter]
      exact (mem_filter.mp hi).2
    have hp := true_group_payoff M hE d w i (Y i : Set (Fin n)) (hY i) (hI i) hn
    simpa only [Set.ncard_coe_finset, higherTrueGroups_card_eq_sum] using hp
  have hpaid := source_weighted_group_payoff (trueLevels M w d.H) (analyzedLevels M w d.H)
    (filter_subset _ _) (fun i => ((trueGroup M d w i).card : ℝ))
    (fun i => ((Y i).card : ℝ)) (fun i => mainMean d (fun d' => (trueLambda M hE d' w i : ℝ)))
    (fun i hi => Nat.cast_nonneg _) hgroup
  have hmass : (∑ i ∈ trueLevels M w d.H, weightBase ^ i * ((trueGroup M d w i).card : ℝ)) =
      ∑ e ∈ candidateLabels M w d.H, levelWeight weightBase (w e) := by
    simp only [trueGroup_eq_candidate_filter]
    exact sum_weightGroups_mass w (candidateLabels M w d.H) (trueLevels M w d.H) Subset.rfl weightBase
  rw [hmass] at hpaid
  exact hpaid.trans (weighted_mean_trueLambda_le_mainWorstRounded M hE d w (analyzedLevels M w d.H))

end MatroidProphet.MainAlgorithm

end OAI
end

theorem solution : type_of% @OAI.MatroidProphet.MainAlgorithm.conditional_main_payoff_oai := @OAI.MatroidProphet.MainAlgorithm.conditional_main_payoff_oai
