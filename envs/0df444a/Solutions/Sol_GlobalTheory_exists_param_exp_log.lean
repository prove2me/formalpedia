-- Prove2me | solution 1 for GlobalTheory.exists_param_exp_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:51:16.445358+00:00
-- url     : https://prove2.me/submissions/6868bd12-35bd-42ff-889b-a22966eceff6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsLocalHomeomorphAddMonoidHomOfEventuallyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOpenPartialHomeomorphAnalytic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAnalyticParamInverse
import Theorems.Thm_GlobalTheory_exists_analytic_param_inverse
import Theorems.Thm_GlobalTheory_eventually_eq_zero_of_slices
import Theorems.Thm_GlobalTheory_analyticAt_param_doublingLog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Metric Set Filter Asymptotics
open scoped Topology
variable {B V : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B] [FiniteDimensional ℂ B]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
namespace GlobalTheory
theorem _root_.solution {b₀ : B} {M : B × V × V → V} (hM : AnalyticAt ℂ M (b₀, 0, 0))
    (hu : ∀ᶠ q : B × V in 𝓝 (b₀, 0), M (q.1, q.2, 0) = q.2)
    (hc : ∀ᶠ q : B × V × V in 𝓝 (b₀, 0, 0), M (q.1, q.2.1, q.2.2) = M (q.1, q.2.2, q.2.1))
    (hs : ∀ᶠ q : B × V × V × V in 𝓝 (b₀, 0, 0, 0),
      M (q.1, M (q.1, q.2.1, q.2.2.1), q.2.2.2) = M (q.1, q.2.1, M (q.1, q.2.2.1, q.2.2.2))) :
    ∃ E L : B × V → V, AnalyticAt ℂ E (b₀, 0) ∧ AnalyticAt ℂ L (b₀, 0) ∧
      (∀ᶠ b in 𝓝 b₀, E (b, 0) = 0 ∧
        HasFDerivAt (fun v => E (b, v)) (ContinuousLinearMap.id ℂ V) 0) ∧
      (∀ᶠ q : B × V in 𝓝 (b₀, 0), L (q.1, E q) = q.2 ∧ E (q.1, L q) = q.2) ∧
      ∀ᶠ q : B × V × V in 𝓝 (b₀, 0, 0),
        E (q.1, q.2.1 + q.2.2) = M (q.1, E (q.1, q.2.1), E (q.1, q.2.2)) := by
  have : CompleteSpace V := FiniteDimensional.complete ℂ V
  have hlaw : ∀ᶠ b in 𝓝 b₀, IsLocalCommGroupLaw fun p : V × V => M (b, p) := by
    filter_upwards [hM.eventually_analyticAt.curry_nhds, hu.curry_nhds, hc.curry_nhds,
      hs.curry_nhds] with b h1 h2 h3 h4
    exact IsLocalCommGroupLaw.of_unit
      (AnalyticAt.comp (f := fun p : V × V => (b, p)) h1.self_of_nhds
        (analyticAt_const.prod analyticAt_id)) h2 h3 h4
  have h₀ := hlaw.self_of_nhds
  have hM0 : M (b₀, 0, 0) = 0 := h₀.map_zero
  obtain ⟨ε, hεa, -, hε⟩ := exists_analytic_param_inverse
    (F := fun q : B × V => M (q.1, q.2, q.2)) (b₀ := b₀)
    (AnalyticAt.comp (f := fun q : B × V => (q.1, q.2, q.2)) hM
      (analyticAt_fst.prod (analyticAt_snd.prod analyticAt_snd))) hM0
    h₀.hasFDerivAt_doubling (IsLocalCommGroupLaw.twoEquiv V).injective
  have hε' : ∀ᶠ b in 𝓝 b₀, ∀ᶠ x in 𝓝 (0 : V), ε (b, M (b, x, x)) = x :=
    (hε.mono fun q hq => hq.1).curry_nhds
  set L : B × V → V := fun q => doublingLog (fun x => ε (q.1, x)) q.2 with hL
  have hLa : AnalyticAt ℂ L (b₀, 0) := analyticAt_param_doublingLog hεa (by
    filter_upwards [hlaw, hε'] with b h1 h2
    exact h1.isBigO_inverse (ε := fun x => ε (b, x)) h2)
  have hLb : ∀ᶠ b in 𝓝 b₀, L (b, 0) = 0 ∧
      HasFDerivAt (fun x => L (b, x)) (ContinuousLinearMap.id ℂ V) 0 ∧
      ∀ᶠ p in 𝓝 (0 : V × V), L (b, M (b, p)) - (L (b, p.1) + L (b, p.2)) = 0 := by
    filter_upwards [hlaw, hε'] with b h1 h2
    exact ⟨h1.doublingLog_zero (ε := fun x => ε (b, x)) h2,
      h1.hasFDerivAt_doublingLog (ε := fun x => ε (b, x)) h2,
      (h1.doublingLog_law (ε := fun x => ε (b, x)) h2).mono fun p hp => sub_eq_zero.mpr hp⟩
  have hadd : ∀ᶠ q : B × V × V in 𝓝 (b₀, 0),
      L (q.1, M q) - (L (q.1, q.2.1) + L (q.1, q.2.2)) = 0 := by
    refine eventually_eq_zero_of_slices
      (F := fun q : B × V × V => L (q.1, M q) - (L (q.1, q.2.1) + L (q.1, q.2.2))) ?_
      (hLb.mono fun b hb => hb.2.2)
    refine AnalyticAt.sub ?_ (AnalyticAt.add ?_ ?_)
    · exact AnalyticAt.comp_of_eq (f := fun q : B × V × V => (q.1, M q)) hLa
        (analyticAt_fst.prod hM) (Prod.ext rfl hM0)
    · exact AnalyticAt.comp_of_eq (f := fun q : B × V × V => (q.1, q.2.1)) hLa
        (analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd)) rfl
    · exact AnalyticAt.comp_of_eq (f := fun q : B × V × V => (q.1, q.2.2)) hLa
        (analyticAt_fst.prod (analyticAt_snd.comp analyticAt_snd)) rfl
  obtain ⟨E, hEa, hE0, hE⟩ := exists_analytic_param_inverse hLa hLb.self_of_nhds.1
    hLb.self_of_nhds.2.1 Function.injective_id
  refine ⟨E, L, hEa, hLa, ?_, hE.mono fun q hq => hq.symm, ?_⟩
  · filter_upwards [hLb, hE.curry_nhds, hEa.eventually_analyticAt.curry_nhds] with b h1 h2 h3
    have h4 : E (b, 0) = 0 := by simpa [h1.1] using h2.self_of_nhds.1
    refine ⟨h4, ?_⟩
    have h5 : HasFDerivAt (fun v => E (b, v)) (fderiv ℂ (fun v => E (b, v)) 0) 0 :=
      (DifferentiableAt.comp (f := fun v : V => (b, v)) 0 h3.self_of_nhds.differentiableAt
        (by fun_prop)).hasFDerivAt
    have h6 := HasFDerivAt.comp (g := fun x => L (b, x)) (f := fun v => E (b, v)) 0
      (by simpa only [h4] using h1.2.1) h5
    have h7 := h6.unique ((hasFDerivAt_id (0 : V)).congr_of_eventuallyEq
      (h2.mono fun v hv => hv.2))
    rw [ContinuousLinearMap.id_comp] at h7
    rwa [h7] at h5
  · have tE : Tendsto E (𝓝 (b₀, 0)) (𝓝 0) := by
      simpa only [hE0] using hEa.continuousAt.tendsto
    have tM : Tendsto M (𝓝 (b₀, 0, 0)) (𝓝 0) := by
      simpa only [hM0] using hM.continuousAt.tendsto
    have t0 : Tendsto (fun q : B × V × V => q.1) (𝓝 (b₀, 0, 0)) (𝓝 b₀) :=
      continuous_fst.tendsto' _ _ rfl
    have t1 : Tendsto (fun q : B × V × V => (q.1, q.2.1)) (𝓝 (b₀, 0, 0)) (𝓝 (b₀, 0)) :=
      Continuous.tendsto' (by fun_prop) _ _ rfl
    have t2 : Tendsto (fun q : B × V × V => (q.1, q.2.2)) (𝓝 (b₀, 0, 0)) (𝓝 (b₀, 0)) :=
      Continuous.tendsto' (by fun_prop) _ _ rfl
    have t3 := t0.prodMk_nhds ((tE.comp t1).prodMk_nhds (tE.comp t2))
    filter_upwards [t3.eventually hadd, t1.eventually hE, t2.eventually hE,
      (t3.eventually (((continuous_fst.tendsto' _ _ rfl).prodMk_nhds tM).eventually hE))]
      with q h1 h2 h3 h4
    simp only [Function.comp] at h1 h2 h3 h4
    rw [sub_eq_zero, h2.2, h3.2] at h1
    rw [← h1, h4.1]
end GlobalTheory
