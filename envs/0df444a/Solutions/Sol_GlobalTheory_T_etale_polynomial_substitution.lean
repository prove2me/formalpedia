-- Prove2me | solution 1 for GlobalTheory.T.etale_polynomial_substitution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:16:39.616346+00:00
-- url     : https://prove2.me/submissions/51bb0685-88f1-4739-bc97-36132a54df3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtalePolynomialSubstitution
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtalePolynomialSubstitutionStatement
import Theorems.Thm_P2M_GlobalTheory_etale_eval_Hom_option_of_bijective_fb0a4cde01c9


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {k A R N : Type} [CommRing k] [CommRing A] [CommRing R] (α : k →+* A) (t : A) (f : A →+* R) (n : N → R) {d : ℕ} (e : Fin (d + 1) ≃ Option N), (MvPolynomial.eval₂Hom α (fun _ : Fin 1 => t)).Etale → Function.Bijective (MvPolynomial.eval₂Hom f n) → (MvPolynomial.eval₂Hom (f.comp α) (fun j => (e j).elim (f t) n)).Etale := by
  first | exact @GlobalTheory.etale_eval₂Hom_option_of_bijective | exact GlobalTheory.etale_eval₂Hom_option_of_bijective | (intros; apply GlobalTheory.etale_eval₂Hom_option_of_bijective <;> assumption)
end _root_.GlobalTheory.T
