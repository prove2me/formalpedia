-- Prove2me | solution 1 for GlobalTheory.QFam.isIntegral_value_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:48:34.478973+00:00
-- url     : https://prove2.me/submissions/15a169d1-74d8-4226-8823-0ddc81ae7362

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModJTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EsymmPowTwelveDivDiscriminantMemSubringStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralOfEsymmMemSubringStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralModularFamilyValueDivPeriodPow
import Theorems.Thm_GlobalTheory_T_esymm_pow_twelve_div_discriminant_mem_subring
import Theorems.Thm_GlobalTheory_T_isIntegral_of_esymm_mem_subring


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open GlobalTheory GlobalTheory.QFam
namespace GlobalTheory.QFam
theorem _root_.solution (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (w N : ℕ)
    (f : ι → ℍ → ℂ) (R : Subring ℂ) (τ₀ : ℍ) (Ω : ℂ) (hN : 0 < N) (hact : ActBij act)
    (hf : IsFam act w f) (hq : ∀ i, QAll (· ∈ R) N (f i)) (hj : IsIntegral R (jT τ₀))
    (hΩ : Ω ^ 12 = DD τ₀) (i : ι) : IsIntegral R (f i τ₀ / Ω ^ w) := by
  have hq' : ∀ i, QAll (· ∈ (integralClosure R ℂ).toSubring) N (f i) := fun i => by
    obtain ⟨a, ha, haR⟩ := hq i
    exact ⟨a, ha, fun n => (integralClosure R ℂ).algebraMap_mem ⟨a n, haR n⟩⟩
  have hs := GlobalTheory.T.esymm_pow_twelve_div_discriminant_mem_subring ι act w N f (integralClosure R ℂ).toSubring τ₀ hN hact hf hq' hj
  have h1 : IsIntegral (integralClosure R ℂ) (f i τ₀ ^ 12 / DD τ₀ ^ w) :=
    GlobalTheory.T.isIntegral_of_esymm_mem_subring ι (integralClosure R ℂ).toSubring (fun i => f i τ₀ ^ 12 / DD τ₀ ^ w) hs i
  have h2 : IsIntegral R (f i τ₀ ^ 12 / DD τ₀ ^ w) := isIntegral_trans _ h1
  have h3 : (f i τ₀ / Ω ^ w) ^ 12 = f i τ₀ ^ 12 / DD τ₀ ^ w := by
    rw [div_pow, ← hΩ, ← pow_mul, ← pow_mul, mul_comm]
  exact IsIntegral.of_pow (n := 12) (by norm_num) (h3 ▸ h2)
end GlobalTheory.QFam
