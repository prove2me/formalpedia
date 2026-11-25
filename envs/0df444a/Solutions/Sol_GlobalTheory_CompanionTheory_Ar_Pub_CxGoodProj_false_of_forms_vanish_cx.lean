-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Pub.CxGoodProj.false_of_forms_vanish_cx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:45:56.679203+00:00
-- url     : https://prove2.me/submissions/0eeedbb7-4517-40ae-8254-d030534053d6

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
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Pub_CxGoodProj_evC_segC
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Pub_CxGoodProj_evC_forms
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Pub_CxGoodProj_mem_conePts
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegreCoordGoodProj_segre_scaleBlock_124690bb4980
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_mono


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
theorem _root_.solution (Q : Ideal (MRingOver ℂ ι)) (hhom : IsMultiHomogIdeal Q) (k0 : K)
    {r : ℕ} (L : Fin r → ((k : K) → ι k) → ℂ) (hL : ∀ t, IntOver ℂ (forms (segC Q) L) (segC Q t))
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ conePts Q) (hV : ∀ j, ∑ t, L j t * segre z t = 0) : False := by
  choose i1 hi1 using hz.1
  have hs : segre z i1 ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hi1 k
  obtain ⟨p, hpm, hp⟩ := hL i1
  let g0 : MvPolynomial (Fin r) ℂ →+* ℂ := eval₂Hom (RingHom.id ℂ) 0
  have key : ∀ c : ℂ, c ≠ 0 → Polynomial.eval (c * segre z i1) (p.map g0) = 0 := by
    intro c hc
    have hzc := mem_conePts Q hhom k0 hc hz
    have hcomp : ((evC Q _ hzc : (MRingOver ℂ ι ⧸ Q) →+* ℂ)).comp
        ((aeval (forms (segC Q) L) : MvPolynomial (Fin r) ℂ →ₐ[ℂ] _) : MvPolynomial (Fin r) ℂ →+* _) =
        g0 := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [g0]
      · intro j
        have h1 : ∑ t, L j t * (c * segre z t) = c * ∑ t, L j t * segre z t := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun t _ => by ring
        simp [g0, evC_forms, GroundTheory.Heights₂.Heights.SegreCoordGoodProj.segre_scaleBlock, h1, hV j]
    have := congrArg (evC Q _ hzc : (MRingOver ℂ ι ⧸ Q) →+* ℂ) hp
    rw [Polynomial.hom_eval₂, hcomp] at this
    simp only [RingHom.coe_coe, evC_segC, GroundTheory.Heights₂.Heights.SegreCoordGoodProj.segre_scaleBlock,
      map_zero] at this
    rw [Polynomial.eval_map]
    exact this
  have hinf : {x : ℂ | (p.map g0).IsRoot x}.Infinite := by
    refine Set.Infinite.mono ?_ (Set.finite_singleton (0 : ℂ)).infinite_compl
    intro x hx
    have hx0 : x ≠ 0 := hx
    have := key (x / segre z i1) (div_ne_zero hx0 hs)
    rw [div_mul_cancel₀ x hs] at this
    exact this
  exact (hpm.map g0).ne_zero (Polynomial.eq_zero_of_infinite_isRoot _ hinf)
end GlobalTheory.CompanionTheory.Ar.Pub.CxGoodProj
