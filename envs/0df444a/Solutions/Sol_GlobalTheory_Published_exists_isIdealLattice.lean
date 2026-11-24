-- Prove2me | solution 1 for GlobalTheory.Published.exists_isIdealLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:14:58.796016+00:00
-- url     : https://prove2.me/submissions/762c1bbf-7390-4948-bad5-0f08df68bd79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_ComplexMultiplicationJPremises
import Theorems.Thm_GlobalTheory_QuadraticZeta_exists_periodPair


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors IntermediateField
open GlobalTheory GlobalTheory.Published
variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]
open NumberField
open scoped nonZeroDivisors IntermediateField
variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]
namespace GlobalTheory.Published
namespace _root_.GlobalTheory.Published
theorem _root_.solution [IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2)
    (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ∃ L, _root_.GlobalTheory.Published.IsIdealLattice 𝔞 L := by
  have hc : InfinitePlace.nrComplexPlaces K = 1 := by
    have := IsTotallyComplex.finrank (K := K)
    omega
  have hs := sign_discr K
  rw [hc, pow_one, Int.sign_eq_neg_one_iff_neg] at hs
  have hd : discr K = -((-discr K).toNat : ℤ) := by omega
  obtain ⟨L, hL⟩ := _root_.GlobalTheory.QuadraticZeta.exists_periodPair h2 hd (algebraMap K ℂ) 𝔞
  exact ⟨L, hL⟩
end _root_.GlobalTheory.Published
end GlobalTheory.Published
