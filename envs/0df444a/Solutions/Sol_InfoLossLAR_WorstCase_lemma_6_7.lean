-- Prove2me | solution 1 for InfoLossLAR.WorstCase.lemma_6_7
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T23:20:29.511886+00:00
-- url     : https://prove2.me/submissions/dd5dc1b3-144f-4be5-8977-58bf16be509d

import Mathlib
import Definitions.Def_InfoLossLAR_WorstCase_FixedT
import Theorems.Thm_InfoLossLAR_WorstCase_lemma_6_2
set_option autoImplicit false
open scoped BigOperators
open InfoLossLAR.WorstCase
namespace TreeDetProof
variable {d : ℕ} (T : OrientedTree d) (σ : T.G.edgeSet ⊕ Unit ≃ Fin d)
private def extM (v : Fin d → ℤ) := (T.extended v).submatrix id σ.symm
private theorem coordinates (v : Fin d → ℤ) (a : Fin d → ℤ) :
    (extM T σ v).mulVec a =
      T.incidence.mulVec (fun e => a (σ (.inl e))) + a (σ (.inr ())) • v := by
  classical
  funext i
  change (∑ j : Fin d, (T.extended v i (σ.symm j)) * a j) = _
  rw [← Equiv.sum_comp σ (fun j => T.extended v i (σ.symm j) * a j)]
  simp [Fintype.sum_sum_type,OrientedTree.extended,Matrix.mulVec,dotProduct,mul_comm]
private theorem decomposed (r : Fin d) (v : Fin d → ℤ) :
    ∃ k : T.G.edgeSet → ℤ, T.incidence.mulVec k = v - (∑ i, v i) • Pi.single r 1 := by
  classical
  have h : v - (∑ i, v i) • Pi.single r 1 ∈ zeroSumLattice d := by
    change (∑ i, (v i - (∑ j, v j) * (Pi.single r 1 : Fin d → ℤ) i)) = 0
    simp [Finset.sum_sub_distrib, ← Finset.mul_sum, Pi.single_apply]
  rw [← (lemma_6_2 d T).2.2.2.1] at h
  exact h
end TreeDetProof
open TreeDetProof
theorem solution (d : ℕ) (T : OrientedTree d) (v : Fin d → ℤ)
    (σ : T.G.edgeSet ⊕ Unit ≃ Fin d) :
    |((T.extended v).submatrix id σ.symm).det| = |∑ i, v i| := by
  classical
  let r := σ (.inr ())
  let u : Fin d → ℤ := Pi.single r 1
  let A := extM T σ u
  have hpre (y : Fin d → ℤ) : ∃ a : Fin d → ℤ, A.mulVec a = y ∧ a r = ∑ i, y i := by
    obtain ⟨k,hk⟩ := decomposed T r y
    let a : Fin d → ℤ := fun j => Sum.elim k (fun _ => ∑ i, y i) (σ.symm j)
    refine ⟨a, ?_, by simp [a,r]⟩
    rw [coordinates]
    simpa [a,u,hk] using add_sub_cancel_right (T.incidence.mulVec k) ((∑ i, y i) • u)
  have hu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).1
      (Matrix.mulVec_surjective_iff_isUnit.1 (fun y => (hpre y).imp fun _ h => h.1))
  obtain ⟨a,ha,har⟩ := hpre v
  have hmat : (T.extended v).submatrix id σ.symm = A.updateCol r (fun i => ∑ j, a j • A i j) := by
    ext i j
    obtain ⟨c,rfl⟩ := σ.surjective j
    cases c with
    | inl e => simp [Matrix.updateCol_apply,extM,A,r,OrientedTree.extended,Function.update]
    | inr x =>
      cases x
      simpa [A,extM,r,OrientedTree.extended,Matrix.updateCol_apply,Matrix.mulVec,dotProduct,mul_comm] using (congrFun ha i).symm
  rw [hmat,Matrix.det_updateCol_sum,har,smul_eq_mul,abs_mul]
  rcases Int.isUnit_iff.mp hu with hp|hp <;> simp [hp]
