-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.BdRad.radical_span_prod_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:31:53.065936+00:00
-- url     : https://prove2.me/submissions/abe25940-32cf-424a-8bca-dbef6ae6b7a4

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsMulMemOfAlgebraMapLocRingEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_RegDom
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_RegularSystemOfParametersLocalRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.BdRad
open MvPolynomial ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
variable {m : ℕ}
namespace GlobalTheory.CompanionTheory.Ar.Cmp.BdRad
theorem _root_.solution {O ι : Type*} [CommRing O] [IsDomain O] (R : ι → O) (J : Finset ι)
    (hpr : ∀ i, Prime (R i)) (hna : ∀ i j, i ≠ j → ¬ Associated (R i) (R j)) :
    (Ideal.span {∏ i ∈ J, R i}).radical = Ideal.span {∏ i ∈ J, R i} := by
  classical
  apply le_antisymm _ Ideal.le_radical
  rintro g ⟨n, hn⟩
  rw [Ideal.mem_span_singleton] at hn ⊢
  have hdiv : ∀ i ∈ J, R i ∣ g := fun i hi =>
    (hpr i).dvd_of_dvd_pow ((Finset.dvd_prod_of_mem R hi).trans hn)
  clear hn
  induction J using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    obtain ⟨c, rfl⟩ := ih fun i hi => hdiv i (Finset.mem_insert_of_mem hi)
    have hac := hdiv a (Finset.mem_insert_self _ _)
    rcases (hpr a).dvd_or_dvd hac with h | h
    · exfalso
      obtain ⟨j, hj, hd⟩ := (Prime.exists_mem_finset_dvd (hpr a) h)
      have hne : a ≠ j := fun e => ha (e ▸ hj)
      exact hna a j hne (((hpr a).dvd_prime_iff_associated (hpr j)).mp hd)
    · obtain ⟨d, rfl⟩ := h
      exact ⟨d, by ring⟩
end GlobalTheory.CompanionTheory.Ar.Cmp.BdRad
