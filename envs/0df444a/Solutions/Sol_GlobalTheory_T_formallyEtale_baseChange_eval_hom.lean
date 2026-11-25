-- Prove2me | solution 1 for GlobalTheory.T.formallyEtale_baseChange_eval_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:20:13.569055+00:00
-- url     : https://prove2.me/submissions/c4b00cec-33fb-4431-a211-b52ab47351c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FormallyEtaleBaseChangeEvalHom
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FormallyEtaleBaseChangeEvalHomStatement
import Theorems.Thm_P2M_GlobalTheory_formallyEtale_mvPolynomial_eval__tensor_865e95252550


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {k R B : Type} [CommRing k] [CommRing R] [CommRing B] [Algebra k R] [Algebra k B] {r : ℕ} (τ : Fin r → B),
  (MvPolynomial.eval₂Hom (algebraMap k B) τ).FormallyEtale →
  (MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[k] B)
      (fun i => (1 : R) ⊗ₜ[k] τ i)).FormallyEtale := by
  first | exact @GlobalTheory.formallyEtale_mvPolynomial_eval₂_tensor | exact GlobalTheory.formallyEtale_mvPolynomial_eval₂_tensor | (intros; apply GlobalTheory.formallyEtale_mvPolynomial_eval₂_tensor <;> assumption)
end _root_.GlobalTheory.T
