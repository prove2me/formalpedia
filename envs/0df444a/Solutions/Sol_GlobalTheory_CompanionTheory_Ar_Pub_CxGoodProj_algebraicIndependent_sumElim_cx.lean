-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Pub.CxGoodProj.algebraicIndependent_sumElim_cx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:46:51.226264+00:00
-- url     : https://prove2.me/submissions/e9b4deb7-b54a-4471-87e2-d57770a6fbde

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
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_SegreChartProjObjects
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MemChartComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreCoordGoodProj
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemConePtsIffChartIdeal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ExistsGoodProjFirstCoordinate
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Pub_CxGoodProj_ideal_isHomogeneous
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Pub_CxGoodProj_segMonC_isWeightedHomogeneous
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Pub_CxGoodProj_component_aeval_cx
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Pub_CxGoodProj_aeval_sumElim_factor_cx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Pub GlobalTheory.CompanionTheory.Ar.Pub.CxGoodProj
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GlobalTheory.CompanionTheory.Ar.Pub.CxGoodProj
theorem _root_.solution (Q : Ideal (MRingOver ℂ ι)) [Q.IsPrime]
    (hhom : IsMultiHomogIdeal Q) (k0 : K) (i0 : (k : K) → ι k)
    (hi0 : ∀ k, (X ⟨k, i0 k⟩ : MRingOver ℂ ι) ∉ Q) {r : ℕ} (L : Fin r → ((k : K) → ι k) → ℂ)
    (hind : AlgebraicIndependent ℂ (forms (segC Q) L)) :
    AlgebraicIndependent ℂ (Sum.elim (forms (segC Q) L)
      (fun k' : {k // k ≠ k0} => Ideal.Quotient.mk Q (X ⟨k'.1, i0 k'.1⟩))) := by
  set xs : {k // k ≠ k0} → MRingOver ℂ ι ⧸ Q :=
    fun k' => Ideal.Quotient.mk Q (X ⟨k'.1, i0 k'.1⟩) with hxs
  let π := Ideal.Quotient.mkₐ ℂ Q
  let yt : Fin r ⊕ {k // k ≠ k0} → MRingOver ℂ ι :=
    Sum.elim (fun j => ∑ i, L j i • segMonC i) (fun k' => X ⟨k'.1, i0 k'.1⟩)
  have hyt : ∀ e, IsWeightedHomogeneous (blkWt (ι := ι)) (yt e) (sWt k0 r e) := by
    rintro (j | k')
    · refine IsWeightedHomogeneous.sum _ _ _ fun i _ => ?_
      rw [smul_eq_C_mul]
      exact (segMonC_isWeightedHomogeneous i).C_mul _
    · exact isWeightedHomogeneous_X ℂ _ _
  have hπy : (fun e => π (yt e)) = Sum.elim (forms (segC Q) L) xs := by
    funext e
    rcases e with j | k'
    · simp [yt, π, forms, segC, map_sum]
    · rfl
  have hcomp : ∀ G : MvPolynomial (Fin r ⊕ {k // k ≠ k0}) ℂ,
      Ideal.Quotient.mk Q (aeval yt G) = aeval (Sum.elim (forms (segC Q) L) xs) G := by
    intro G
    rw [← hπy, ← MvPolynomial.comp_aeval]
    rfl
  have hx0 : ∀ k', xs k' ≠ 0 := by
    intro k' h
    rw [hxs, Ideal.Quotient.eq_zero_iff_mem] at h
    exact hi0 k'.1 h
  rw [algebraicIndependent_iff]
  intro H hH0
  by_contra hne
  obtain ⟨n0, hn0⟩ := support_nonempty.mpr hne
  set δ := Finsupp.weight (sWt k0 r) n0
  set H' := weightedHomogeneousComponent (sWt k0 r) δ H
  have hH'hom : IsWeightedHomogeneous (sWt k0 r) H' δ :=
    weightedHomogeneousComponent_isWeightedHomogeneous δ H
  have hn0' : n0 ∈ H'.support := by
    rw [mem_support_iff, coeff_weightedHomogeneousComponent, if_pos rfl]
    exact mem_support_iff.mp hn0
  have hmem : aeval yt H ∈ Q := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, hcomp]
    exact hH0
  have hmem' : aeval yt H' ∈ Q := by
    rw [← component_aeval_cx (sWt k0 r) yt hyt H δ]
    exact weightedHomogeneousComponent_mem_of_mem ℂ blkWt (ideal_isHomogeneous Q hhom) hmem δ
  have hzero : aeval (Sum.elim (forms (segC Q) L) xs) H' = 0 := by
    rw [← hcomp]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem'
  rw [aeval_sumElim_factor_cx k0 hH'hom hn0'] at hzero
  have hprod : (∏ k', xs k' ^ n0 (Sum.inr k')) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k' _ => pow_ne_zero _ (hx0 k')
  have h1 : aeval (Sum.elim (forms (segC Q) L) 1) H' = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hprod
  let G : MvPolynomial (Fin r) ℂ := aeval (Sum.elim X 1) H'
  have hG : ∀ {S : Type} [CommRing S] [Algebra ℂ S] (a : Fin r → S),
      aeval a G = aeval (Sum.elim a 1) H' := by
    intro S _ _ a
    simp only [G]
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    exact congrArg (fun f => aeval f H') (funext fun e => by rcases e with j | k' <;> simp)
  have hG0 : G = 0 := (algebraicIndependent_iff.mp hind) G (by rw [hG]; exact h1)
  have hH'0 : H' * ∏ k', X (Sum.inr k') = 0 := by
    apply MvPolynomial.funext
    intro z
    rw [map_mul, map_zero, map_prod]
    by_cases hz : ∀ k', z (Sum.inr k') ≠ 0
    · have := aeval_sumElim_factor_cx k0 hH'hom hn0' (S := ℂ) (z ∘ Sum.inl) (z ∘ Sum.inr)
      have hzz : Sum.elim (z ∘ Sum.inl) (z ∘ Sum.inr) = z := by
        funext e; rcases e with j | k' <;> rfl
      rw [hzz, ← hG, hG0, map_zero, mul_zero] at this
      rw [← coe_aeval_eq_eval]
      simp only [AlgHom.coe_toRingHom] at this ⊢
      rw [this, zero_mul]
    · push Not at hz
      obtain ⟨k', hk'⟩ := hz
      rw [Finset.prod_eq_zero (Finset.mem_univ k') (by simp [hk']), mul_zero]
  have hH'z : H' = 0 := by
    rcases mul_eq_zero.mp hH'0 with h | h
    · exact h
    · exact absurd h (Finset.prod_ne_zero_iff.mpr fun k' _ => X_ne_zero _)
  rw [hH'z] at hn0'
  simp at hn0'
end GlobalTheory.CompanionTheory.Ar.Pub.CxGoodProj
