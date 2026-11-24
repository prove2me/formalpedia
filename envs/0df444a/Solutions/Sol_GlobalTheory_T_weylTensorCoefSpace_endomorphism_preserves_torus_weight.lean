-- Prove2me | solution 1 for GlobalTheory.T.weylTensorCoefSpace_endomorphism_preserves_torus_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:25:58.623798+00:00
-- url     : https://prove2.me/submissions/0f6d7e8b-f263-4e98-8545-ad1347791d2c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeylTensorCoefSpaceEndomorphismPreservesTorusWei
import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeylTensorCoefSpaceEndomorphismPreservesTorusWeiStatement
import Theorems.Thm_GlobalTheory_CoefTorusWeight_weight_preserved


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
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [CharZero K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (g : Module.End K (VV K lam)), (∀ (h : ι → GL (Fin n) K) v, g (rhoK lam h v) = rhoK lam h (g v)) → ∀ v : VV K lam, (∀ m ∈ (v : Pol K ι n).support, ∀ τ a, ∑ s : Fin n, m (τ, a, s) = (lam τ).natW a) → ∀ m ∈ ((g v : VV K lam) : Pol K ι n).support, ∀ τ a, ∑ s : Fin n, m (τ, a, s) = (lam τ).natW a := by
  first | exact @GlobalTheory.CoefTorusWeight.weight_preserved | exact GlobalTheory.CoefTorusWeight.weight_preserved | (intros; apply GlobalTheory.CoefTorusWeight.weight_preserved <;> assumption)
end _root_.GlobalTheory.T
