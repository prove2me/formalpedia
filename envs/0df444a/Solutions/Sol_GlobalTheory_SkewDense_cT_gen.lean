-- Prove2me | solution 1 for GlobalTheory.SkewDense.cT_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:12:52.722191+00:00
-- url     : https://prove2.me/submissions/4b71b3cc-1c48-4e1a-ab26-4927d1f186bf

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MvPolynomialEqZeroOfVanishSkewHermitian

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
open NumberField
open GlobalTheory GlobalTheory.SkewDense
namespace GlobalTheory.SkewDense
theorem _root_.solution {E : Type} [CommRing E] (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (u v : Fin n) (x : E) :
    Formalism.UG.cT σ (gen σ u v x) = -gen σ u v x := by
  ext i j
  simp only [Formalism.UG.cT, gen, Matrix.transpose_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.neg_apply,
    Matrix.single_apply, map_sub, apply_ite σ, map_zero, hσ, neg_sub, and_comm]
end GlobalTheory.SkewDense
