-- Prove2me | solution 1 for GlobalTheory.BlockThInhab.poly_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:00:55.860097+00:00
-- url     : https://prove2.me/submissions/66e3b25c-29f4-402b-87ad-a59ab4d9ccca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_IsBlockProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NotIsBlockProdZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BlockThInhab
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.BlockTh
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) (n : ℕ)
namespace GlobalTheory.BlockThInhab
theorem _root_.solution (K : Type) [Field K] (B : Bk Dw n) : B.poly K ≠ 0 := by
  classical
  unfold Bk.poly
  refine pow_ne_zero _ ?_
  intro h
  let v : LtN Dw n → K := fun l => if ∃ a : Fin B.i, l = ⟨B.τ, Fin.castLE B.hi a, B.col a⟩ then 1 else 0
  have h2 := congrArg (MvPolynomial.eval v) h
  rw [RingHom.map_det, map_zero] at h2
  have : (MvPolynomial.eval v).mapMatrix (Matrix.of fun a b : Fin B.i => MvPolynomial.X (⟨B.τ, Fin.castLE B.hi a, B.col b⟩ : LtN Dw n)) = 1 := by
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.eval_X, v, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab; rw [if_pos ⟨a, rfl⟩, if_pos rfl]
    · rw [if_neg hab, if_neg]
      rintro ⟨d, hd⟩
      simp only [Sigma.mk.injEq, heq_eq_eq, true_and, Prod.mk.injEq] at hd
      have h1 : a = d := Fin.castLE_injective _ hd.1
      have h3 : b = d := B.col_inj hd.2
      exact hab (h1.trans h3.symm)
  rw [this, Matrix.det_one] at h2
  exact one_ne_zero h2
end GlobalTheory.BlockThInhab
