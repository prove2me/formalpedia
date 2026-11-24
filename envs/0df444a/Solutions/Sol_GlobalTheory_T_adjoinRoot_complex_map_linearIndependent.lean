-- Prove2me | solution 1 for GlobalTheory.T.adjoinRoot_complex_map_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:30:30.099669+00:00
-- url     : https://prove2.me/submissions/0d8e08ca-050c-4e5c-a758-b9abe1d99135

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdjoinRootMapComplexLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdjoinRootMapComplexLinearIndependentStatement
import Theorems.Thm_GlobalTheory_adjoinRoot_map_complex_linearIndependent


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (D : ℕ) (P : Polynomial (MvPolynomial (Fin D) ℚ)), P.Monic → ∃ τ : AdjoinRoot P →+* AdjoinRoot (P.map (MvPolynomial.map (algebraMap ℚ ℂ))), (∀ i, τ (AdjoinRoot.of P (MvPolynomial.X i)) = AdjoinRoot.of _ (MvPolynomial.X i)) ∧ (∀ (q : ℚ) u, τ (q • u) = (q : ℂ) • τ u) ∧ ∀ (J : Type) (e : J → AdjoinRoot P), LinearIndependent ℚ e → LinearIndependent ℂ (fun j => τ (e j)) := by
  first | exact @GlobalTheory.adjoinRoot_map_complex_linearIndependent | exact GlobalTheory.adjoinRoot_map_complex_linearIndependent | (intros; apply GlobalTheory.adjoinRoot_map_complex_linearIndependent <;> assumption)
end _root_.GlobalTheory.T
