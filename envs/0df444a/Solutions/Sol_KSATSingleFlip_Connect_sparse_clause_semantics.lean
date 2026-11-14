-- Prove2me | solution 1 for KSATSingleFlip.Connect.sparse_clause_semantics
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:25:20.991199+00:00
-- url     : https://prove2.me/submissions/8c05c9e1-d7e2-4f5b-98ba-12fe3df93f7f

import Definitions.Def_KSATSingleFlip_Connect_SparseFlip

open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

theorem audit_sparse_clause_at {n k : ℕ} (C : SparseClause n k) (i : Fin k) :
    C.toClause (C.index i) = some (C.sign i) := by
  unfold SparseClause.toClause
  have h : ∃ j, C.index j = C.index i := ⟨i, rfl⟩
  rw [dif_pos h]
  have hchoice : Classical.choose h = i := C.index.injective (Classical.choose_spec h)
  rw [hchoice]

theorem audit_sparse_scope {n k : ℕ} (C : SparseClause n k) :
    vbl C.toClause = Finset.univ.image C.index := by
  ext v
  simp only [vbl, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro hv
    unfold SparseClause.toClause at hv
    split at hv
    · rename_i h
      exact ⟨Classical.choose h, Classical.choose_spec h⟩
    · simp at hv
  · rintro ⟨i, _, rfl⟩
    rw [audit_sparse_clause_at]
    rfl

theorem audit_sparse_scope_card {n k : ℕ} (C : SparseClause n k) :
    (vbl C.toClause).card = k := by
  rw [audit_sparse_scope, Finset.card_image_iff.mpr C.index.injective.injOn]
  simp

theorem audit_sparse_clause_sat {n k : ℕ} (C : SparseClause n k) (x : Fin n → Bool) :
    ClauseSat x C.toClause ↔ C.Sat x := by
  constructor
  · rintro ⟨v, hv⟩
    unfold SparseClause.toClause at hv
    split at hv
    · rename_i h
      refine ⟨Classical.choose h, ?_⟩
      have he := Option.some.inj hv
      simpa [Classical.choose_spec h] using he
    · simp at hv
  · rintro ⟨i, hi⟩
    exact ⟨C.index i, by rw [audit_sparse_clause_at, hi]⟩

theorem audit_sparse_input_linear (n k m c : ℕ) (hm : m ≤ c * n) :
    sparseFlipInputWords n k m ≤ 4 + (2 * k * c + 1) * n := by
  unfold sparseFlipInputWords
  nlinarith

theorem audit_flip_path_word_count {n : ℕ} (p : FlipListPath n) :
    p.wordCount = n + 1 + p.flips.length := rfl

end KSATSingleFlip.Connect

namespace KSATSingleFlip.Connect
open OAI.FixedClauseThreshold

/-- Every proper option-valued k-clause has a sparse representation. -/
theorem audit_sparse_represents_clause {n k : ℕ} (D : ProperClause n k) :
    ∃ C : SparseClause n k, C.toClause = D.val := by
  let S : Finset (Fin n) := vbl D.val
  have hcard : S.card = k := D.property
  let e : Fin k ≃ {v // v ∈ S} := (Finset.equivFinOfCardEq hcard).symm
  let C : SparseClause n k :=
    { index := e.toEmbedding.trans (Function.Embedding.subtype (· ∈ S))
      sign := fun i => (D.val (e i).1).getD false }
  refine ⟨C, ?_⟩
  funext v
  by_cases hv : v ∈ S
  · let i : Fin k := e.symm ⟨v, hv⟩
    have hi : C.index i = v := by simp [C, i]
    calc
      C.toClause v = C.toClause (C.index i) := by rw [hi]
      _ = some (C.sign i) := audit_sparse_clause_at C i
      _ = D.val v := by
        have hs : (D.val v).isSome := (Finset.mem_filter.mp hv).2
        have he : (e i).1 = v := by simpa [C] using hi
        dsimp [C]
        rw [he]
        cases hval : D.val v <;> simp_all
  · have hnone : D.val v = none := by
      have hs : ¬(D.val v).isSome := by
        simpa [S, vbl] using hv
      cases hval : D.val v <;> simp_all
    have hnindex : ¬∃ i, C.index i = v := by
      rintro ⟨i, hi⟩
      apply hv
      have he : (e i).1 = v := by simpa [C] using hi
      exact he ▸ (e i).property
    simp [SparseClause.toClause, hnindex, hnone]

end KSATSingleFlip.Connect

namespace KSATSingleFlip.Connect
open OAI.FixedClauseThreshold

/-- Every ordered formula has an order- and multiplicity-preserving sparse encoding. -/
theorem audit_sparse_represents_formula {n k m : ℕ} (F : Formula n k m) :
    ∃ G : SparseFormula n k m, sparseFormulaSemantics G = ofFormula F := by
  let G : SparseFormula n k m := fun j => Classical.choose (audit_sparse_represents_clause (F j))
  refine ⟨G, ?_⟩
  unfold sparseFormulaSemantics ofFormula
  apply congrArg List.ofFn
  funext j
  exact Classical.choose_spec (audit_sparse_represents_clause (F j))

end KSATSingleFlip.Connect

open KSATSingleFlip.Connect OAI.FixedClauseThreshold

theorem solution (n k m : ℕ) :
    (∀ C : SparseClause n k, (vbl C.toClause).card = k) ∧
    (∀ (C : SparseClause n k) (x : Fin n → Bool), ClauseSat x C.toClause ↔ C.Sat x) ∧
    (∀ D : ProperClause n k, ∃ C : SparseClause n k, C.toClause = D.val) ∧
    (∀ F : Formula n k m, ∃ G : SparseFormula n k m, sparseFormulaSemantics G = ofFormula F) := by
  exact ⟨audit_sparse_scope_card, audit_sparse_clause_sat, audit_sparse_represents_clause,
    audit_sparse_represents_formula⟩

#print axioms solution
