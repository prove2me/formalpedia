-- Prove2me | solution 1 for GlobalTheory.MinorGerm.lead_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:51:15.02021+00:00
-- url     : https://prove2.me/submissions/47a76348-4cf1-47b6-b70d-1b105f473790

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdFactorialDiag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
noncomputable section
open GlobalTheory GlobalTheory.MinorGerm
variable {C : Type} [Field C] {σ : Type}
variable {p : σ → Prop} [DecidablePred p]
namespace GlobalTheory.MinorGerm
theorem _root_.solution {k : ℕ} (w : Fin k → Fin k → σ) (hw : ∀ b c, p (w b c) ↔ b = c) :
    Lead p (∑ b, Finsupp.single (w b b) 1)
      (Matrix.of fun b c : Fin k => (MvPolynomial.X (w b c) : MvPolynomial σ C)).det := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · rw [AlgHom.map_det]
    have hM : (kill p).mapMatrix (Matrix.of fun b c : Fin k => (MvPolynomial.X (w b c) : MvPolynomial σ C)) =
        Matrix.diagonal fun b => MvPolynomial.X (w b b) := by
      ext b c
      simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.diagonal_apply, kill,
        MvPolynomial.aeval_X]
      by_cases hbc : b = c
      · subst hbc
        simp [(hw b b).2 rfl]
      · simp [hbc, (hw b c).not.2 hbc]
    rw [hM, Matrix.det_diagonal, MvPolynomial.monomial_sum_one]
    rfl
  · have hdeg : (∑ b : Fin k, Finsupp.single (w b b) 1).degree = k := by
      rw [map_sum]
      simp [Finsupp.degree_single]
    rw [hdeg, Matrix.det_apply]
    apply MvPolynomial.IsHomogeneous.sum
    intro s _
    have hprod : MvPolynomial.IsHomogeneous (∏ i, (Matrix.of fun b c : Fin k =>
        (MvPolynomial.X (w b c) : MvPolynomial σ C)) (s i) i) k := by
      have h := MvPolynomial.IsHomogeneous.prod Finset.univ
        (fun i => (Matrix.of fun b c : Fin k => (MvPolynomial.X (w b c) : MvPolynomial σ C)) (s i) i)
        (fun _ => 1) (fun i _ => MvPolynomial.isHomogeneous_X _ _)
      simpa using h
    rcases Int.units_eq_one_or (Equiv.Perm.sign s) with h | h
    · rw [h, one_smul]
      exact hprod
    · rw [h, Units.neg_smul, one_smul]
      exact hprod.neg
  · intro x hx
    obtain ⟨b, -, hb⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hx)
    have hx' := Finsupp.support_single_subset hb
    rw [Finset.mem_singleton] at hx'
    rw [hx']
    exact (hw b b).2 rfl
end GlobalTheory.MinorGerm
