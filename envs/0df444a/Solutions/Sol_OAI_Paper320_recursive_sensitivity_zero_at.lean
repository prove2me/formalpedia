-- Prove2me | solution 1 for OAI.Paper320.recursive_sensitivity_zero_at
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:31:42.167742+00:00
-- url     : https://prove2.me/submissions/c194c3a2-8ccf-430b-b019-178838a7f3e1

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/RecursiveZero.lean:L12-L107
-- (upload_full_project.md Phase 4): solution for node OAI.Paper320.recursive_sensitivity_zero_at. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_SensitivitySeparation
import Definitions.Def_OAI_Combinatorics_Sensitivity_HammingBase
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_Basic
import Definitions.Def_OAI_Combinatorics_Sensitivity_InitialPredicates
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tournament
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveDefinitions
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveBlocks
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveSets
import Definitions.Def_OAI_Combinatorics_Sensitivity_TournamentCounts
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveFailures
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveCandidates
import Theorems.Thm_OAI_Paper320_Tournament_card_le_three_of_outdegree_le_one
import Theorems.Thm_OAI_Paper320_rowClause_repair_cases

-- ---- from OAI.Combinatorics.Sensitivity.RecursiveProfiles ----
namespace OAI

/-! The side and joint profiles count literal flips of the same raw input. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem NestedFamily.rejects_of_le {h : ℕ} {I : Type}
    {F : Fin h → (I → Bool) → Bool} (hF : NestedFamily F)
    {q q' : Fin h} {x} (hqq : q ≤ q') (hx : F q x = false) :
    F q' x = false := by
  cases h' : F q' x
  · rfl
  · have := hF.accepts_of_le hqq h'
    simp [hx] at this

theorem sensitivityAt_le_sideSensitivity {h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (b : Bool) (q : Fin h) (x : I → Bool)
    (hx : F q x = b) : sensitivityAt (F q) x ≤ sideSensitivity F b := by
  apply Finset.le_sup_of_le (Finset.mem_univ q)
  apply Finset.le_sup_of_le (Finset.mem_univ x)
  simp [hx]

theorem jointSensitivityAt_le_jointSensitivity {h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (b : Bool) (q q' : Fin h) (x : I → Bool)
    (hqq : q < q') (hx : F q x = b) (hx' : F q' x = b) :
    jointSensitivityAt (F q) (F q') x ≤ jointSensitivity F b := by
  apply Finset.le_sup_of_le (Finset.mem_univ q)
  apply Finset.le_sup_of_le (Finset.mem_univ q')
  apply Finset.le_sup_of_le (Finset.mem_univ x)
  simp [hqq, hx, hx']

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.Tournament ----
namespace OAI

/-! Finite tournaments and the target-constant labeling condition. -/

noncomputable section
open scoped Classical

namespace Paper320

namespace Tournament
variable {k : ℕ} (T : Tournament k)

theorem adj_or_reverse {i j : Fin k} (h : i ≠ j) : T.Adj i j ∨ T.Adj j i := by
  by_cases hh : T.Adj j i
  · exact Or.inr hh
  · exact Or.inl ((T.edge_compl h).mpr hh)

theorem internal_sink_unique {I : Finset (Fin k)} {i j : Fin k}
    (hi : i ∈ I) (hj : j ∈ I)
    (hsi : ∀ v ∈ I, ¬ T.Adj i v) (hsj : ∀ v ∈ I, ¬ T.Adj j v) : i = j := by
  by_contra h
  rcases T.adj_or_reverse h with hh | hh
  · exact hsi j hj hh
  · exact hsj i hi hh

end Tournament

namespace GoodLabeling
variable {k r : ℕ} {T : Tournament k} (A : GoodLabeling T r)

theorem good_implies_card_lt_sixteen (I : Finset (Fin k)) (m : Fin k → Fin r)
    (h : ∀ i ∈ I, ∀ j ∈ I, T.Adj i j → A.label i j = m j) : I.card < 16 := by
  by_contra hn
  obtain ⟨J, hJI, hJ⟩ := Finset.exists_subset_card_eq (show 16 ≤ I.card by omega)
  obtain ⟨i, hi, j, hj, hij, hne⟩ := A.good J hJ m
  exact hne (h i (hJI hi) j (hJI hj) hij)

end GoodLabeling
end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.RecursiveDefinitions ----
namespace OAI

/-! The literal target-row and labeled-gate construction. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem gateIndex_lt_last {h : ℕ} (q : Fin h) : gateIndex q < Fin.last h :=
  Fin.castSucc_lt_last _

theorem recursiveFamily_eq_true_iff {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) :
    recursiveFamily T label F q x = true ↔ ∃ i, rowClause T label F q x i = true := by
  simp only [recursiveFamily, decide_eq_true_eq]

theorem recursiveFamily_eq_false_iff {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) :
    recursiveFamily T label F q x = false ↔ ∀ i, rowClause T label F q x i = false := by
  simp [recursiveFamily]

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.RecursiveSets ----
namespace OAI

/-! Finite sets of changing raw coordinates inside an individual child. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem card_biUnion_le_mul {J I : Type} [DecidableEq I] (A : Finset J) (B : J → Finset I) (n : ℕ)
    (hn : ∀ j ∈ A, (B j).card ≤ n) : (A.biUnion B).card ≤ A.card * n := by
  calc
    (A.biUnion B).card ≤ ∑ j ∈ A, (B j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ A, n := Finset.sum_le_sum hn
    _ = A.card * n := by simp

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.RecursiveFailures ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

/-! Fixed initial-input lists of clauses with exactly one failed condition. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem targetFailures_empty_iff {k r h : ℕ} {I : Type}
    (F : Fin (h + 1) → (I → Bool) → Bool)
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) :
    targetFailures F x i = ∅ ↔ ∀ c, F (Fin.last h) (recursiveChild x i c) = true := by
  simp [targetFailures, Finset.filter_eq_empty_iff]

theorem gateFailures_empty_iff {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) :
    gateFailures T label F q x i = ∅ ↔
      ∀ j, T.Adj i j → F (gateIndex q) (recursiveChild x j (label i j)) = false := by
  simp [gateFailures, Finset.filter_eq_empty_iff]

theorem targetFailures_singleton {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) (i : Fin k)
    (hi : i ∈ targetCandidates T label F q x) :
    targetFailures F x i = {targetWitness F x hr i} := by
  have hc := (Finset.mem_filter.mp hi).2.1
  obtain ⟨c, hc'⟩ := Finset.card_eq_one.mp hc
  have hne : (targetFailures F x i).Nonempty := hc' ▸ Finset.singleton_nonempty c
  have hm : targetWitness F x hr i ∈ targetFailures F x i := by
    simp only [targetWitness, dite_eq_left hne]
    exact hne.choose_spec
  rw [hc', Finset.mem_singleton] at hm
  simpa [hm] using hc'

theorem gateFailures_singleton {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k)
    (hi : i ∈ gateCandidates T label F q x) :
    gateFailures T label F q x i = {gateWitness T label F q x i} := by
  have hc := (Finset.mem_filter.mp hi).2.2
  obtain ⟨j, hc'⟩ := Finset.card_eq_one.mp hc
  have hne : (gateFailures T label F q x i).Nonempty := hc' ▸ Finset.singleton_nonempty j
  have hm : gateWitness T label F q x i ∈ gateFailures T label F q x i := by
    simp only [gateWitness, dite_eq_left hne]
    exact hne.choose_spec
  rw [hc', Finset.mem_singleton] at hm
  simpa [hm] using hc'

theorem targetCandidates_card {k r h : ℕ} {I : Type} (T : Tournament k)
    (A : GoodLabeling T r) (F : Fin (h + 1) → (I → Bool) → Bool) (hF : NestedFamily F)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) :
    (targetCandidates T A.label F q x).card < 16 := by
  apply A.good_implies_card_lt_sixteen _ (targetWitness F x hr)
  intro i hi j hj hij
  have hgate := (gateFailures_empty_iff T A.label F q x i).mp (Finset.mem_filter.mp hi).2.2
  have hz := hF.rejects_of_le (gateIndex_lt_last q).le (hgate j hij)
  have hm : A.label i j ∈ targetFailures F x j := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩
  rw [targetFailures_singleton T A.label F q x hr j hj, Finset.mem_singleton] at hm
  exact hm

theorem gateCandidates_neighbor {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (hF : NestedFamily F) (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool)
    (i j : Fin k) (hi : i ∈ gateCandidates T label F q x)
    (hj : j ∈ gateCandidates T label F q x) (hij : T.Adj i j) :
    j = gateWitness T label F q x i := by
  have ht := (targetFailures_empty_iff F x j).mp (Finset.mem_filter.mp hj).2.1
  have hon := hF.accepts_of_le (gateIndex_lt_last q).le (ht (label i j))
  have hm : j ∈ gateFailures T label F q x i := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij, hon⟩
  rwa [gateFailures_singleton T label F q x i hi, Finset.mem_singleton] at hm

theorem gateCandidates_card {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (hF : NestedFamily F) (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) :
    (gateCandidates T label F q x).card ≤ 3 := by
  apply T.card_le_three_of_outdegree_le_one
  intro i hi
  apply le_trans (Finset.card_le_card (t := {gateWitness T label F q x i}) ?_)
    (by simp)
  intro j hj
  have h := Finset.mem_filter.mp hj
  exact Finset.mem_singleton.mpr (gateCandidates_neighbor T label F hF q x i j hi h.1 h.2)

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.RecursiveCandidates ----
namespace OAI

/-! Unique failed children and the unique possible sink of the gate-clause list. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem targetWitness_false {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) (i : Fin k)
    (hi : i ∈ targetCandidates T label F q x) :
    F (Fin.last h) (recursiveChild x i (targetWitness F x hr i)) = false := by
  have hm : targetWitness F x hr i ∈ targetFailures F x i := by
    rw [targetFailures_singleton T label F q x hr i hi]
    exact Finset.mem_singleton_self _
  exact (Finset.mem_filter.mp hm).2

theorem targetWitness_unique {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) (i : Fin k)
    (hi : i ∈ targetCandidates T label F q x) (c : Fin r)
    (hc : F (Fin.last h) (recursiveChild x i c) = false) : c = targetWitness F x hr i := by
  have hm : c ∈ targetFailures F x i := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
  rwa [targetFailures_singleton T label F q x hr i hi, Finset.mem_singleton] at hm

theorem gateWitness_spec {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k)
    (hi : i ∈ gateCandidates T label F q x) :
    T.Adj i (gateWitness T label F q x i) ∧
      F (gateIndex q) (recursiveChild x (gateWitness T label F q x i)
        (label i (gateWitness T label F q x i))) = true := by
  have hm : gateWitness T label F q x i ∈ gateFailures T label F q x i := by
    rw [gateFailures_singleton T label F q x i hi]
    exact Finset.mem_singleton_self _
  exact (Finset.mem_filter.mp hm).2

theorem gateWitness_unique {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k)
    (hi : i ∈ gateCandidates T label F q x) (j : Fin k) (hij : T.Adj i j)
    (hj : F (gateIndex q) (recursiveChild x j (label i j)) = true) :
    j = gateWitness T label F q x i := by
  have hm : j ∈ gateFailures T label F q x i := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij, hj⟩
  rwa [gateFailures_singleton T label F q x i hi, Finset.mem_singleton] at hm

theorem gateSinks_card {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) :
    (gateSinks T label F q x).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  exact T.internal_sink_unique (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

theorem nonsink_gateWitness_mem {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (hF : NestedFamily F) (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool)
    (i : Fin k) (hi : i ∈ gateCandidates T label F q x)
    (hs : i ∉ gateSinks T label F q x) :
    gateWitness T label F q x i ∈ gateCandidates T label F q x := by
  have he : ∃ j ∈ gateCandidates T label F q x, T.Adj i j := by
    by_contra hn
    apply hs
    apply Finset.mem_filter.mpr
    refine ⟨hi, ?_⟩
    intro j hj hij
    exact hn ⟨j, hj, hij⟩
  obtain ⟨j, hj, hij⟩ := he
  rwa [← gateCandidates_neighbor T label F hF q x i j hi hj hij]

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.RecursiveZero ----
namespace OAI

/-! The zero-side recurrence separates the unique possible gate-list sink. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem recursive_sensitivity_zero_at {k r h : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (A : GoodLabeling T r)
    (F : Fin (h + 1) → (I → Bool) → Bool) (hF : NestedFamily F) (hr : 0 < r)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool)
    (hx : recursiveFamily T A.label F q x = false) :
    sensitivityAt (recursiveFamily T A.label F q) x ≤
      16 * sideSensitivity F false + sideSensitivity F true + 3 * jointSensitivity F true := by
  let TC := targetCandidates T A.label F q x
  let GC := gateCandidates T A.label F q x
  let SC := gateSinks T A.label F q x
  let NC := GC \ SC
  let w := gateWitness T A.label F q x
  let U := TC.biUnion fun i => childChanges F (Fin.last h) x i (targetWitness F x hr i)
  let V := NC.biUnion fun i => childJointChanges F (gateIndex q) (Fin.last h) x (w i) (A.label i (w i))
  let W := SC.biUnion fun i => childChanges F (gateIndex q) x (w i) (A.label i (w i))
  have hsub : (Finset.univ.filter fun p =>
      recursiveFamily T A.label F q (flip x {p}) ≠ recursiveFamily T A.label F q x) ⊆ U ∪ (V ∪ W) := by
    rintro ⟨⟨j, c⟩, a⟩ hp
    have hchange := (Finset.mem_filter.mp hp).2
    have hon : recursiveFamily T A.label F q (flip x {((j, c), a)}) = true := by
      cases hy : recursiveFamily T A.label F q (flip x {((j, c), a)})
      · exact False.elim (hchange (hy.trans hx.symm))
      · rfl
    obtain ⟨i, hi⟩ := (recursiveFamily_eq_true_iff T A.label F q _).mp hon
    have hioff := (recursiveFamily_eq_false_iff T A.label F q x).mp hx i
    rcases rowClause_repair_cases T A.label F q x i j c a hioff hi with
      ⟨hit, hji, htoff, hton⟩ | ⟨hig, hij, rfl, hgon, hgoff⟩
    · subst j
      have hc := targetWitness_unique T A.label F q x hr i hit c htoff
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨i, hit, ?_⟩
      have hn : F (Fin.last h) (flip (recursiveChild x i c) {a}) ≠
          F (Fin.last h) (recursiveChild x i c) := by simp [hton, htoff]
      simpa [childChanges, hc] using hn
    · have hj := gateWitness_unique T A.label F q x i hig j hij hgon
      apply Finset.mem_union_right
      by_cases hs : i ∈ SC
      · apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        refine ⟨i, hs, ?_⟩
        have hn : F (gateIndex q) (flip (recursiveChild x j (A.label i j)) {a}) ≠
            F (gateIndex q) (recursiveChild x j (A.label i j)) := by simp [hgon, hgoff]
        simpa [childChanges, w, hj] using hn
      · have hwg := nonsink_gateWitness_mem T A.label F hF q x i hig hs
        have hjg : j ∈ gateCandidates T A.label F q x := by simpa [hj] using hwg
        have hton := (targetFailures_empty_iff F x j).mp (Finset.mem_filter.mp hjg).2.1 (A.label i j)
        have htoff := hF.rejects_of_le (gateIndex_lt_last q).le hgoff
        apply Finset.mem_union_left
        apply Finset.mem_biUnion.mpr
        refine ⟨i, Finset.mem_sdiff.mpr ⟨hig, hs⟩, ?_⟩
        have hn :
            F (gateIndex q) (flip (recursiveChild x j (A.label i j)) {a}) ≠
              F (gateIndex q) (recursiveChild x j (A.label i j)) ∧
            F (Fin.last h) (flip (recursiveChild x j (A.label i j)) {a}) ≠
              F (Fin.last h) (recursiveChild x j (A.label i j)) := by
          simp [hgon, hgoff, hton, htoff]
        simpa [childJointChanges, w, hj] using hn
  have hU : U.card ≤ 16 * sideSensitivity F false := by
    calc
      U.card ≤ TC.card * sideSensitivity F false :=
        card_biUnion_le_mul TC _ _ (fun i hi => by
          rw [childChanges_card]
          exact sensitivityAt_le_sideSensitivity F false _ _
            (targetWitness_false T A.label F q x hr i hi))
      _ ≤ 16 * sideSensitivity F false := Nat.mul_le_mul_right _
        (Nat.le_of_lt (targetCandidates_card T A F hF q x hr))
  have hV : V.card ≤ 3 * jointSensitivity F true := by
    calc
      V.card ≤ NC.card * jointSensitivity F true :=
        card_biUnion_le_mul NC _ _ (fun i hi => by
          have hg := Finset.mem_sdiff.mp hi
          have hw := nonsink_gateWitness_mem T A.label F hF q x i hg.1 hg.2
          have hgate := (gateWitness_spec T A.label F q x i hg.1).2
          have htarget := (targetFailures_empty_iff F x _).mp (Finset.mem_filter.mp hw).2.1
            (A.label i (w i))
          rw [childJointChanges_card]
          exact jointSensitivityAt_le_jointSensitivity F true _ _ _ (gateIndex_lt_last q) hgate htarget)
      _ ≤ GC.card * jointSensitivity F true := Nat.mul_le_mul_right _ (Finset.card_le_card Finset.sdiff_subset)
      _ ≤ 3 * jointSensitivity F true := Nat.mul_le_mul_right _ (gateCandidates_card T A.label F hF q x)
  have hW : W.card ≤ sideSensitivity F true := by
    calc
      W.card ≤ SC.card * sideSensitivity F true :=
        card_biUnion_le_mul SC _ _ (fun i hi => by
          rw [childChanges_card]
          exact sensitivityAt_le_sideSensitivity F true _ _
            (gateWitness_spec T A.label F q x i (Finset.mem_filter.mp hi).1).2)
      _ ≤ 1 * sideSensitivity F true := Nat.mul_le_mul_right _ (gateSinks_card T A.label F q x)
      _ = _ := Nat.one_mul _
  calc
    sensitivityAt (recursiveFamily T A.label F q) x ≤ (U ∪ (V ∪ W)).card := Finset.card_le_card hsub
    _ ≤ U.card + (V ∪ W).card := Finset.card_union_le _ _
    _ ≤ U.card + (V.card + W.card) := Nat.add_le_add_left (Finset.card_union_le _ _) _
    _ ≤ 16 * sideSensitivity F false + (3 * jointSensitivity F true + sideSensitivity F true) :=
      Nat.add_le_add hU (Nat.add_le_add hV hW)
    _ = _ := by omega

end Paper320

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper320
open scoped Classical

theorem solution {k r h : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (A : GoodLabeling T r)
    (F : Fin (h + 1) → (I → Bool) → Bool) (hF : NestedFamily F) (hr : 0 < r)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool)
    (hx : recursiveFamily T A.label F q x = false) :
    sensitivityAt (recursiveFamily T A.label F q) x ≤
      16 * sideSensitivity F false + sideSensitivity F true + 3 * jointSensitivity F true := by
  first
    | exact OAI.Paper320.recursive_sensitivity_zero_at T A F hF hr q x hx
    | exact OAI.Paper320.recursive_sensitivity_zero_at
    | (apply OAI.Paper320.recursive_sensitivity_zero_at <;> assumption)
    | (intros; apply OAI.Paper320.recursive_sensitivity_zero_at <;> assumption)
