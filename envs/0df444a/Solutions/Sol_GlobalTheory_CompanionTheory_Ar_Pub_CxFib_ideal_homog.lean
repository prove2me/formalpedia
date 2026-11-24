-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Pub.CxFib.ideal_homog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:36:03.828741+00:00
-- url     : https://prove2.me/submissions/2c603a4a-142f-4c7e-9a62-5c28d3fec20c

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Metrics__PoincareLelong_e61d89ea90cf58ae
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Metrics__SheetDensityEqSetSheetDensity_cb85824e9bfdd8ba
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_CxPosDens
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_CxSimple
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SetFibreFiniteOfGoodProj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Pub.CxFib
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt
open ReciprocityTheory.AnForm.R (conePts)
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
private lemma weight_blkW_lemma [DecidableEq K] (d : (Σ k, ι k) →₀ ℕ) (a : K → ℕ)
    (h : ∀ k, ∑ i, d ⟨k, i⟩ = a k) : Finsupp.weight (blkW ι) d = a := by
  funext k
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  swap
  · intro p
    exact zero_smul _ _
  rw [Finset.sum_apply, Fintype.sum_sigma]
  simp only [blkW, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single k]
  · simp [h k]
  · intro b _ hb
    simp [Ne.symm hb]
  · simp
private lemma multiHomog_weighted_lemma_2 [DecidableEq K] {f : MRingOver ℂ ι} {a : K → ℕ}
    (ha : IsMultiHomog f a) : f ∈ weightedHomogeneousSubmodule ℂ (blkW ι) a := by
  rw [mem_weightedHomogeneousSubmodule]
  intro d hd
  exact weight_blkW_lemma d a (ha d (MvPolynomial.mem_support_iff.mpr hd))
variable {e : ℕ}
end GlobalTheory.CompanionTheory.Ar.Pub.CxFib
end
end

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Pub GlobalTheory.CompanionTheory.Ar.Pub.CxFib
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt
open ReciprocityTheory.AnForm.R (conePts)
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace GlobalTheory.CompanionTheory.Ar.Pub.CxFib
theorem _root_.solution [DecidableEq K] {Q : Ideal (MRingOver ℂ ι)} (hQ : IsMultiHomogIdeal Q) :
    Q.IsHomogeneous (weightedHomogeneousSubmodule ℂ (blkW ι)) := by
  obtain ⟨S, hS, rfl⟩ := hQ
  apply Ideal.homogeneous_span
  intro f hf
  obtain ⟨a, ha⟩ := hS f hf
  exact ⟨a, multiHomog_weighted_lemma_2 ha⟩
end GlobalTheory.CompanionTheory.Ar.Pub.CxFib
