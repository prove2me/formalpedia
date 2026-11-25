-- Prove2me | solution 1 for GlobalTheory.T.finprod_localDifferentIdealNorm_eq_discr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:23:05.186005+00:00
-- url     : https://prove2.me/submissions/25af8276-c228-4fa6-b70f-fd10c7f3fb29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FinprodLocalDifferentIdealNormEqDiscr
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_LocalDualIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FinprodLocalDifferentIdealNormEqDiscrStatement
import Theorems.Thm_GlobalTheory_LocalDifferentProduct_prod_normDifferentV


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : E, star x = σ x) → Formalism.HermitianLatticesTheory.IsCMUnram E → (Function.mulSupport (normDifferentV F)).Finite ∧ ((∏ᶠ v, normDifferentV F v : ℕ) : ℝ) = absDiscr F ∧ absDiscr F = (2 * Formalism.HermitianLatticesTheory.vInv E) ^ Formalism.HermitianLatticesTheory.fDeg E := by
  first | exact @GlobalTheory.LocalDifferentProduct.prod_normDifferentV | exact GlobalTheory.LocalDifferentProduct.prod_normDifferentV | (intros; apply GlobalTheory.LocalDifferentProduct.prod_normDifferentV <;> assumption)
end _root_.GlobalTheory.T
