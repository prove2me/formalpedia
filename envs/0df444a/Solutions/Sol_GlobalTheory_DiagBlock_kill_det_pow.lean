-- Prove2me | solution 1 for GlobalTheory.DiagBlock.kill_det_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:59:57.299798+00:00
-- url     : https://prove2.me/submissions/5432aec2-a0c2-4af4-b6b6-8e6dd39517de

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict
import Theorems.Thm_GlobalTheory_DiagBlock_kill_X
import Theorems.Thm_GlobalTheory_DiagBlock_det_diag_rows

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.DiagBlock
namespace GlobalTheory.DiagBlock
theorem _root_.solution {R : Type} [CommRing R] {σ : Type} (S : σ → Prop) [DecidablePred S]
    {n0 n : ℕ} (hn : n0 ≤ n) (f : Fin n → Fin n → σ)
    (hf : ∀ ρ c, S (f ρ c) ↔ n0 ≤ ρ.val ∧ c ≠ ρ) (Y : ℕ) :
    kill S ((Matrix.of fun b c : Fin n => (MvPolynomial.X (f b c) : MvPolynomial σ R)).det ^ Y) =
      (Matrix.of fun b c : Fin n0 =>
        (MvPolynomial.X (f (Fin.castLE hn b) (Fin.castLE hn c)) : MvPolynomial σ R)).det ^ Y *
      MvPolynomial.monomial
        (∑ ρ ∈ (Finset.univ : Finset (Fin n)).filter (fun ρ => n0 ≤ ρ.val),
          Finsupp.single (f ρ ρ) Y) 1 := by
  rw [map_pow, AlgHom.map_det]
  have hM : (kill (R := R) S).mapMatrix (Matrix.of fun b c : Fin n => (MvPolynomial.X (f b c) : MvPolynomial σ R)) =
      Matrix.of fun b c : Fin n => if S (f b c) then 0 else MvPolynomial.X (f b c) := by
    ext b c
    simp [AlgHom.mapMatrix_apply, kill_X]
  rw [hM, det_diag_rows hn _ (by
    intro ρ c hρ hc
    simp [(hf ρ c).2 ⟨hρ, hc⟩])]
  have hsub : (Matrix.of fun b c : Fin n => if S (f b c) then (0 : MvPolynomial σ R) else MvPolynomial.X (f b c)).submatrix
      (Fin.castLE hn) (Fin.castLE hn) =
      Matrix.of fun b c : Fin n0 => (MvPolynomial.X (f (Fin.castLE hn b) (Fin.castLE hn c)) : MvPolynomial σ R) := by
    ext b c
    simp [hf, not_le.2 b.isLt]
  have hdiag : ∀ ρ : Fin n, (Matrix.of fun b c : Fin n =>
      if S (f b c) then (0 : MvPolynomial σ R) else MvPolynomial.X (f b c)) ρ ρ = MvPolynomial.X (f ρ ρ) := by
    intro ρ
    simp [hf]
  rw [hsub, Finset.prod_congr rfl (fun ρ _ => hdiag ρ), mul_pow, ← Finset.prod_pow,
    MvPolynomial.monomial_sum_one]
  congr 1
  refine Finset.prod_congr rfl fun ρ _ => ?_
  rw [MvPolynomial.X_pow_eq_monomial]
end GlobalTheory.DiagBlock
