-- Prove2me | solution 1 for GlobalTheory.T.exists_radical_locally_eq_span_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:05:10.029969+00:00
-- url     : https://prove2.me/submissions/f99a3386-81cf-477e-9a8a-c250dc790ebd

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_RegularSystemOfParametersLocalRing
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_RegularSystemOfParametersLocalRingStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_BdRad_exists_den_prod_params


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (m e : ℕ) (I Dc : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ) (r : Fin e → MvPolynomial (Fin m) ℂ) (Jf : Finset (Fin e)), I ≤ Dc → (∀ h ∈ I, eval t h = 0) → IsRegularLocalRing (locRing I t) → ringKrullDim (locRing I t) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) = Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) → (∀ 𝔮 : Ideal (MvPolynomial (Fin m) ℂ), 𝔮.IsPrime → I ≤ 𝔮 → 𝔮 ≤ ptIdeal t → (Dc ≤ 𝔮 ↔ ∃ i ∈ Jf, r i ∈ 𝔮)) → ∃ h : MvPolynomial (Fin m) ℂ, eval t h ≠ 0 ∧ h * ∏ l ∈ Jf, r l ∈ Dc.radical ∧ ∀ g ∈ Dc.radical, h * g ∈ Ideal.span {∏ l ∈ Jf, r l} ⊔ I := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.BdRad.exists_den_prod_params | exact GlobalTheory.CompanionTheory.Ar.Cmp.BdRad.exists_den_prod_params | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.BdRad.exists_den_prod_params <;> assumption)
end _root_.GlobalTheory.T
