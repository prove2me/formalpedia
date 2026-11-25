-- Prove2me | solution 1 for GroundTheory.Automorphic.exists_linearIndependent_pow_apply_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:03:06.512943+00:00
-- url     : https://prove2.me/submissions/e00999a6-5178-49ef-92fc-eadec51cb6ee

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjCyclic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Polynomial Module Matrix
variable {K W : Type*} [Field K] [IsAlgClosed K] [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]
namespace GroundTheory.Automorphic
theorem _root_.solution (f : Module.End K W)
    (hf : f.charpoly.Separable) :
    ∃ w : W, LinearIndependent K (fun k : Fin (finrank K W) => (f ^ (k : ℕ)) w) := by
  set n := finrank K W
  have hdeg : f.charpoly.natDegree = n := LinearMap.charpoly_natDegree f
  have hnd := nodup_roots hf
  let s : Finset K := ⟨f.charpoly.roots, hnd⟩
  have hs : s.card = n := by
    change f.charpoly.roots.card = n
    rw [IsAlgClosed.card_roots_eq_natDegree, hdeg]
  let e : Fin n ≃ s := (s.equivFin.trans (finCongr hs)).symm
  let μ : Fin n → K := fun j => (e j : K)
  have hμ : Function.Injective μ := Subtype.coe_injective.comp e.injective
  have hroot : ∀ j, f.charpoly.IsRoot (μ j) := fun j =>
    (mem_roots hf.ne_zero).1 (e j).2
  have hev : ∀ j, f.HasEigenvalue (μ j) := fun j =>
    (Module.End.hasEigenvalue_iff_isRoot_charpoly f _).2 (hroot j)
  choose w hw using fun j => (hev j).exists_hasEigenvector
  have hli : LinearIndependent K w := f.eigenvectors_linearIndependent' μ hμ w hw
  have hpow : ∀ (k : ℕ) j, (f ^ k) (w j) = μ j ^ k • w j := by
    intro k j
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, (hw j).apply_eq_smul, smul_smul,
        pow_succ]
  refine ⟨∑ j, w j, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hsum : ∀ j, ∑ k : Fin n, c k * μ j ^ (k : ℕ) = 0 := by
    have h2 : ∑ j, (∑ k : Fin n, c k * μ j ^ (k : ℕ)) • w j = 0 := by
      rw [← hc]
      simp only [map_sum, hpow, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    exact fun j => (Fintype.linearIndependent_iff.1 hli) _ h2 j
  have hV : Matrix.vandermonde μ *ᵥ c = 0 := by
    ext j
    simp only [Matrix.mulVec, dotProduct, Matrix.vandermonde_apply, Pi.zero_apply]
    rw [← hsum j]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hdet : (Matrix.vandermonde μ).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.2 hμ
  exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet hV)
end GroundTheory.Automorphic
