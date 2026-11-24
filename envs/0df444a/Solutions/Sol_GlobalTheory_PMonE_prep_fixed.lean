-- Prove2me | solution 1 for GlobalTheory.PMonE.prep_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:32:41.230416+00:00
-- url     : https://prove2.me/submissions/d0cb8016-8d08-45ab-88f8-1aa1811dd774

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemPreparationNormalFormOne
import Theorems.Thm_GlobalTheory_PMonE_PrepBd_add
import Theorems.Thm_GlobalTheory_PMonE_PrepBd_neg
import Theorems.Thm_GlobalTheory_PMonE_PrepBd_mono
import Theorems.Thm_GlobalTheory_PMonE_PrepBd_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset
variable {F : Type} [NormedField F] {m : Type} [Fintype m]
variable [IsUltrametricDist F]
namespace GlobalTheory.PMonE
theorem _root_.solution [CompleteSpace F] {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ < 1) (M0 : Matrix m m F) (h0 : PrepBd 1 M0)
    (W : Matrix m m F → Matrix m m F) (hW : ∀ A, PrepBd 1 A → PrepBd δ (W A))
    (hW2 : ∀ A B ε, 0 ≤ ε → PrepBd 1 A → PrepBd 1 B → PrepBd ε (A - B) → PrepBd (δ * ε) (W A - W B)) :
    ∃ A, PrepBd 1 A ∧ A = -M0 - W A * A := by
  let s : Set (m → m → F) := {A | ∀ i j, ‖A i j‖ ≤ 1}
  let f : (m → m → F) → (m → m → F) := fun A => fun i j => (-M0 - W (Matrix.of A) * (Matrix.of A)) i j
  have hs : IsClosed s := by
    simp only [s, Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_le (by fun_prop) continuous_const
  have hf : Set.MapsTo f s s := by
    intro A hA
    have hA' : PrepBd 1 (Matrix.of A) := hA
    have : PrepBd 1 (-M0 - W (Matrix.of A) * (Matrix.of A)) := by
      rw [sub_eq_add_neg]
      refine h0.neg.add (PrepBd.neg ?_)
      exact (PrepBd.mul hδ zero_le_one (hW _ hA') hA').mono (by simpa using hδ1.le)
    exact this
  have hc : ContractingWith ⟨δ, hδ⟩ (hf.restrict f s s) := by
    refine ⟨hδ1, LipschitzWith.of_dist_le_mul fun A B => ?_⟩
    have hA' : PrepBd 1 (Matrix.of A.1) := A.2
    have hB' : PrepBd 1 (Matrix.of B.1) := B.2
    have hε : 0 ≤ dist A B := dist_nonneg
    have hAB : PrepBd (dist A B) (Matrix.of A.1 - Matrix.of B.1) := by
      intro i j
      rw [Matrix.sub_apply, Matrix.of_apply, Matrix.of_apply, ← dist_eq_norm, Subtype.dist_eq]
      exact (dist_le_pi_dist _ _ j).trans (dist_le_pi_dist A.1 B.1 i)
    have key : PrepBd (δ * dist A B) ((-M0 - W (Matrix.of A.1) * (Matrix.of A.1)) -
        (-M0 - W (Matrix.of B.1) * (Matrix.of B.1))) := by
      have e1 : (-M0 - W (Matrix.of A.1) * (Matrix.of A.1)) - (-M0 - W (Matrix.of B.1) * (Matrix.of B.1)) =
          -((W (Matrix.of A.1) - W (Matrix.of B.1)) * (Matrix.of A.1) +
            W (Matrix.of B.1) * (Matrix.of A.1 - Matrix.of B.1)) := by
        rw [Matrix.sub_mul, Matrix.mul_sub]; abel
      rw [e1]
      refine PrepBd.neg (PrepBd.add ?_ ?_)
      · simpa using PrepBd.mul (mul_nonneg hδ hε) zero_le_one (hW2 _ _ _ hε hA' hB' hAB) hA'
      · exact PrepBd.mul hδ hε (hW _ hB') hAB
    change dist (f A.1) (f B.1) ≤ δ * dist A B
    refine (dist_pi_le_iff (mul_nonneg hδ hε)).2 fun i => (dist_pi_le_iff (mul_nonneg hδ hε)).2 fun j => ?_
    rw [dist_eq_norm]
    exact key i j
  obtain ⟨y, hy, hfix, -⟩ := hc.exists_fixedPoint' hs.isComplete hf (x := 0) (by intro i j; simp) (edist_ne_top _ _)
  refine ⟨Matrix.of y, hy, ?_⟩
  ext i j
  exact (congrFun (congrFun hfix i) j).symm
end GlobalTheory.PMonE
