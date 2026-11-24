-- Prove2me | solution 1 for GlobalTheory.FunObj.DiagLattice.exists_unip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:47:11.386332+00:00
-- url     : https://prove2.me/submissions/ddfce22b-1663-4276-9d7f-25eea480c30d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsKOOfDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.DiagLattice
namespace GlobalTheory.FunObj.DiagLattice
theorem _root_.solution {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (p : ℕ)
    (v : Fin c → n ⊕ Fin c → k) (h1 : ∀ i, v i (Sum.inr i) = 1) (h2 : ∀ i l, i < l → v i (Sum.inr l) = 0)
    (h3 : ∀ i : Fin c, i.val < p → ∀ r, v i (Sum.inl r) = 0) :
    ∃ u ∈ N k n c p, (∀ r i, u.val r (Sum.inr i) = v i r) ∧
      ∀ r s, u.val r (Sum.inl s) = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (Sum.inl s) := by
  refine ⟨(Model.mkNel p fun rs => Sum.elim (fun _ => (0 : k)) (fun i => v i rs.1.1) rs.1.2).1,
    Subtype.property _, ?_, ?_⟩
  · intro r i
    show Model.mkN p (fun rs => Sum.elim (fun _ => (0 : k)) (fun i => v i rs.1.1) rs.1.2) r (Sum.inr i) = _
    simp only [Model.mkN, of_apply, Sum.elim_inr]
    split_ifs with h
    · rfl
    · rcases r with r | r
      · rw [h3 i (by simp [lev] at h; omega)]; simp
      · simp only [lev, Sum.elim_inr] at h
        rcases eq_or_lt_of_le (show i ≤ r by rw [Fin.le_def]; omega) with e | e
        · subst e; simp [h1]
        · rw [h2 i r e, Matrix.one_apply_ne]
          simpa using e.ne'
  · intro r s
    show Model.mkN p (fun rs => Sum.elim (fun _ => (0 : k)) (fun i => v i rs.1.1) rs.1.2) r (Sum.inl s) = _
    simp only [Model.mkN, of_apply, Sum.elim_inl]
    split_ifs with h
    · rw [Matrix.one_apply_ne]
      rintro rfl; exact lt_irrefl _ h
    · rfl
end GlobalTheory.FunObj.DiagLattice
