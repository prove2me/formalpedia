-- Prove2me | solution 1 for GlobalTheory.T.fractionalIdealNorm_pow_six_mul_discriminant_class_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:17:29.268996+00:00
-- url     : https://prove2.me/submissions/3cb275a2-b31b-413e-9752-90b688ad8010

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FractionalIdealNormPowSixMulDiscriminantClassInv
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_LatticeNormTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FractionalIdealNormPowSixMulDiscriminantClassInvStatement
import Theorems.Thm_GlobalTheory_DiscClass_nrm_pow_mul_norm_latDisc_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {K : Type} [Field K] [NumberField K] (φK : K →+* ℂ), Module.finrank ℚ K = 2 → (starRingEnd ℂ).comp φK ≠ φK → ∀ (𝔞 𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (Λa Λb : PeriodPair), IsLatOf φK (𝔞 : FractionalIdeal (𝓞 K)⁰ K) Λa → IsLatOf φK (𝔟 : FractionalIdeal (𝓞 K)⁰ K) Λb → ClassGroup.mk K 𝔞 = ClassGroup.mk K 𝔟 → nrm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) ^ 6 * ‖latDisc Λa‖ = nrm (𝔟 : FractionalIdeal (𝓞 K)⁰ K) ^ 6 * ‖latDisc Λb‖ := by
  first | exact @GlobalTheory.DiscClass.nrm_pow_mul_norm_latDisc_eq | exact GlobalTheory.DiscClass.nrm_pow_mul_norm_latDisc_eq | (intros; apply GlobalTheory.DiscClass.nrm_pow_mul_norm_latDisc_eq <;> assumption)
end _root_.GlobalTheory.T
