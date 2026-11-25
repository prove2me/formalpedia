-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.exists_isSymm_of_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:48:43.348246+00:00
-- url     : https://prove2.me/submissions/9a471ea1-bc11-4fb0-b7d9-4bc50fcfdcc1

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ContragredientTranspose
open Polynomial
universe u
open scoped Matrix
variable {F : Type u} [Field F] {n : ℕ}
namespace GroundTheory.Automorphic.ContragredientTranspose
theorem _root_.solution (A : Matrix (Fin n) (Fin n) F) (B : (Fin n → F) → (Fin n → F) → F)
    (hBsymm : ∀ v w, B v w = B w v) (hBaddl : ∀ v v' w, B (v + v') w = B v w + B v' w)
    (hBsmull : ∀ (c : F) v w, B (c • v) w = c * B v w)
    (hBA : ∀ v w, B (A.mulVec v) w = B v (A.mulVec w))
    (hBnd : ∀ w, (∀ v, B v w = 0) → w = 0) :
    ∃ S : GL (Fin n) F, (S : Matrix (Fin n) (Fin n) F).IsSymm ∧
      (S : Matrix (Fin n) (Fin n) F) * A = Aᵀ * S := by
  classical
  have hBaddr : ∀ v w w', B v (w + w') = B v w + B v w' := fun v w w' => by
    rw [hBsymm, hBaddl, hBsymm w, hBsymm w']
  have hBsmulr : ∀ (c : F) v w, B v (c • w) = c * B v w := fun c v w => by
    rw [hBsymm, hBsmull, hBsymm]
  have hexp : ∀ v w, B v w = ∑ l, w l * B v (Pi.single l 1) := by
    intro v w
    have hsum : ∀ s : Finset (Fin n), B v (∑ l ∈ s, w l • Pi.single l (1 : F)) =
        ∑ l ∈ s, w l * B v (Pi.single l 1) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        simp only [Finset.sum_empty]
        have := hBsmulr 0 v 0
        simpa using this
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, hBaddr, ih, hBsmulr]
    have hw : ∑ l, w l • Pi.single l (1 : F) = w := by
      have := (Pi.basisFun F (Fin n)).sum_repr w
      simpa using this
    rw [← hsum Finset.univ, hw]
  have hexpl : ∀ v w, B v w = ∑ l, v l * B (Pi.single l 1) w := by
    intro v w
    rw [hBsymm, hexp]
    simp only [hBsymm w]
  have hcol : ∀ k, A.mulVec (Pi.single k 1) = fun l => A l k := by
    intro k
    rw [Matrix.mulVec_single_one]
    rfl
  let S : Matrix (Fin n) (Fin n) F := Matrix.of fun j k => B (Pi.single j 1) (Pi.single k 1)
  have hS : ∀ j k, S j k = B (Pi.single j 1) (Pi.single k 1) := fun _ _ => rfl
  have hdet : S.det ≠ 0 := by
    intro h0
    obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hw0
    apply hBnd
    intro v
    rw [hexpl]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hj := congrFun hw j
    simp only [Matrix.mulVec, dotProduct, hS, Pi.zero_apply] at hj
    rw [hexp, Finset.sum_congr rfl fun l _ => mul_comm _ _, hj, mul_zero]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero S hdet, ?_, ?_⟩
  · refine Matrix.IsSymm.ext fun j k => ?_
    show S k j = S j k
    rw [hS, hS, hBsymm]
  · show S * A = Aᵀ * S
    ext j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    have h1 : ∑ l, S j l * A l k = B (Pi.single j 1) (A.mulVec (Pi.single k 1)) := by
      rw [hexp, hcol]
      exact Finset.sum_congr rfl fun l _ => by rw [hS, mul_comm]
    have h2 : ∑ l, A l j * S l k = B (A.mulVec (Pi.single j 1)) (Pi.single k 1) := by
      rw [hexpl, hcol]
      exact Finset.sum_congr rfl fun l _ => by rw [hS]
    rw [h1, h2, hBA]
end GroundTheory.Automorphic.ContragredientTranspose
