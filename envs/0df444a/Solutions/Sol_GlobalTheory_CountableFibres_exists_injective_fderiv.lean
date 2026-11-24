-- Prove2me | solution 1 for GlobalTheory.CountableFibres.exists_injective_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:01:28.82408+00:00
-- url     : https://prove2.me/submissions/19fc14fa-42e8-4fc3-9afd-728fcd716fb0

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MvPolynomialEqZeroOfEventually

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CountableFibres
open Filter Topology
namespace GlobalTheory.CountableFibres
namespace _root_.GlobalTheory.CountableFibres
theorem _root_.solution {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    {U : Set E} (hU : IsOpen U) (hne : U.Nonempty) {f : E → F}
    (hf : ∀ z ∈ U, ContDiffAt ℂ 1 f z) (hc : ∀ z ∈ U, {z' ∈ U | f z' = f z}.Countable) :
    ∃ z ∈ U, Function.Injective (fderiv ℂ f z) := by
  haveI := FiniteDimensional.complete ℂ E
  set rk : E → ℕ := fun z => Module.finrank ℂ (LinearMap.range (fderiv ℂ f z : E →ₗ[ℂ] F))
  have hbdd : BddAbove (rk '' U) := ⟨Module.finrank ℂ F, by
    rintro _ ⟨z, -, rfl⟩; exact Submodule.finrank_le _⟩
  obtain ⟨z₀, hz₀, hr⟩ : sSup (rk '' U) ∈ rk '' U := Nat.sSup_mem (hne.image _) hbdd
  have hmax : ∀ z ∈ U, rk z ≤ rk z₀ := fun z hz => hr ▸ le_csSup hbdd ⟨z, hz, rfl⟩
  refine ⟨z₀, hz₀, ?_⟩
  by_contra hinj
  set L := fderiv ℂ f z₀
  set W := LinearMap.range (L : E →ₗ[ℂ] F)
  haveI := FiniteDimensional.complete ℂ W
  obtain ⟨P₀, hP₀⟩ := LinearMap.exists_leftInverse_of_injective W.subtype W.ker_subtype
  set P : F →L[ℂ] W := LinearMap.toContinuousLinearMap P₀
  have hPL : ∀ x, P (L x) = ⟨L x, x, rfl⟩ := fun x => by
    have := congrArg (fun φ => φ ⟨L x, x, rfl⟩) hP₀
    simpa [P] using this
  have hsurj : LinearMap.range ((P.comp L : E →L[ℂ] W) : E →ₗ[ℂ] W) = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨w, x, rfl⟩
    exact ⟨x, by simp [hPL]⟩
  have hg : HasStrictFDerivAt (fun x => P (f x)) (P.comp L) z₀ :=
    P.hasStrictFDerivAt.comp z₀ ((hf z₀ hz₀).hasStrictFDerivAt one_ne_zero)

  obtain ⟨R₀, hR₀⟩ := LinearMap.exists_rightInverse_of_surjective _ hsurj
  set R : W →L[ℂ] E := LinearMap.toContinuousLinearMap R₀
  have hΦ : ContinuousAt (fun z => (P.comp (fderiv ℂ f z)).comp R) z₀ :=
    (continuousAt_const.clm_comp ((hf z₀ hz₀).continuousAt_fderiv one_ne_zero)).clm_comp
      continuousAt_const
  have hΦ₀ : (P.comp L).comp R = 1 := by
    ext1 w
    exact congrArg (fun φ => φ w) hR₀
  have hunit : ∀ᶠ z in 𝓝 z₀, IsUnit ((P.comp (fderiv ℂ f z)).comp R) :=
    hΦ.eventually (Units.isOpen.mem_nhds (by
      show IsUnit ((P.comp L).comp R)
      rw [hΦ₀]; exact isUnit_one))
  have hW : Module.finrank ℂ W = rk z₀ := rfl
  have hker : ∀ᶠ z in 𝓝 z₀, ∀ v, P (fderiv ℂ f z v) = 0 → fderiv ℂ f z v = 0 := by
    filter_upwards [hunit, hU.mem_nhds hz₀] with z hz hzU
    obtain ⟨b, hb⟩ := hz.exists_right_inv
    have hran : LinearMap.range ((P.comp (fderiv ℂ f z) : E →L[ℂ] W) : E →ₗ[ℂ] W) = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro w
      refine ⟨R (b w), ?_⟩
      have := congrArg (fun φ : W →L[ℂ] W => φ w) hb
      simpa using this
    have h1 := LinearMap.finrank_range_add_finrank_ker
      ((P.comp (fderiv ℂ f z) : E →L[ℂ] W) : E →ₗ[ℂ] W)
    have h2 := LinearMap.finrank_range_add_finrank_ker (fderiv ℂ f z : E →ₗ[ℂ] F)
    rw [hran, finrank_top, hW] at h1
    have h3 := hmax z hzU
    have hle : LinearMap.ker (fderiv ℂ f z : E →ₗ[ℂ] F) ≤
        LinearMap.ker ((P.comp (fderiv ℂ f z) : E →L[ℂ] W) : E →ₗ[ℂ] W) := fun v hv => by
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hv ⊢
      simp [hv]
    have heq := Submodule.eq_of_le_of_finrank_le hle (by simp only [rk] at h1 h3; omega)
    intro v hv
    have hv' : v ∈ LinearMap.ker ((P.comp (fderiv ℂ f z) : E →L[ℂ] W) : E →ₗ[ℂ] W) := by
      simpa using hv
    rw [← heq] at hv'
    simpa using hv'

  set K := LinearMap.ker ((P.comp L : E →L[ℂ] W) : E →ₗ[ℂ] W)
  haveI : Nontrivial K := by
    rw [Submodule.nontrivial_iff_ne_bot]
    intro hK
    apply hinj
    intro x y hxy
    have : x - y ∈ K := by
      simp only [K, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
        map_sub, hxy, sub_self, map_zero]
    rw [hK, Submodule.mem_bot, sub_eq_zero] at this
    exact this
  set Ψ := hg.implicitToOpenPartialHomeomorph _ _ hsurj
  set ψ : K → E := fun t => Ψ.symm (P (f z₀), t)
  have hψ0 : ψ 0 = z₀ := hg.implicitFunction_apply_image hsurj
  have hψc : ContinuousAt ψ 0 := (hg.to_implicitFunction hsurj).continuousAt
  have htend : Tendsto (fun t : K => (P (f z₀), t)) (𝓝 0) (𝓝 (P (f z₀), 0)) :=
    tendsto_const_nhds.prodMk_nhds tendsto_id
  have hlev : ∀ᶠ t in 𝓝 (0 : K), P (f (ψ t)) = P (f z₀) :=
    htend.eventually (hg.map_implicitFunction_eq hsurj)
  have hinv : ∀ᶠ t in 𝓝 (0 : K), (Ψ (ψ t)).2 = t := by
    have h := Ψ.open_target.mem_nhds (hg.mem_implicitToOpenPartialHomeomorph_target hsurj)
    filter_upwards [htend h] with t ht
    simp only [ψ]
    rw [Ψ.right_inv (by exact ht)]
  have hdiff : ∀ᶠ t in 𝓝 (0 : K), DifferentiableAt ℂ ψ t := by
    have hcc : K.ClosedComplemented :=
      ContinuousLinearMap.ker_closedComplemented_of_finiteDimensional_range (P.comp L)
    let D := hg.implicitFunctionDataOfComplemented _ _ hsurj hcc
    have hl : ContDiffAt ℂ 1 D.leftFun D.pt :=
      (P.contDiff.contDiffAt).comp z₀ (hf z₀ hz₀)
    have hr : ContDiffAt ℂ 1 D.rightFun D.pt := by
      show ContDiffAt ℂ 1 (fun x => (Classical.choose hcc) (x - z₀)) z₀
      exact ((Classical.choose hcc).contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt
    have hp : D.prodFun D.pt = (P (f z₀), 0) := by
      rw [ImplicitFunctionData.prodFun_apply]
      show (P (f z₀), (Classical.choose hcc) (z₀ - z₀)) = _
      rw [sub_self, map_zero]
    have hcd := (D.contDiffAt_implicitFunction hl hr one_ne_zero).eventually (by simp)
    rw [hp] at hcd
    filter_upwards [htend.eventually hcd] with t ht
    exact (ht.differentiableAt one_ne_zero).comp t
      ((differentiableAt_const _).prodMk differentiableAt_id)
  have hnear : ∀ᶠ t in 𝓝 (0 : K), ψ t ∈ U ∧
      (∀ v, P (fderiv ℂ f (ψ t) v) = 0 → fderiv ℂ f (ψ t) v = 0) := by
    have h := (hU.eventually_mem hz₀).and hker
    rw [← hψ0] at h
    exact hψc.eventually h
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hlev.and (hinv.and (hdiff.and hnear)))
  set S := Metric.ball (0 : K) ε
  have hderiv : ∀ t ∈ S, fderiv ℂ (fun s => f (ψ s)) t = 0 := by
    intro t ht
    obtain ⟨-, -, hdt, htU, hkt⟩ := hball t ht
    have hft : DifferentiableAt ℂ f (ψ t) := (hf _ htU).differentiableAt one_ne_zero
    have hloc : (fun s => P (f (ψ s))) =ᶠ[𝓝 t] fun _ => P (f z₀) :=
      Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds ht) fun s hs => (hball s hs).1
    have hcomp : HasFDerivAt (fun s => f (ψ s)) ((fderiv ℂ f (ψ t)).comp (fderiv ℂ ψ t)) t :=
      hft.hasFDerivAt.comp t hdt.hasFDerivAt
    have hcompP : HasFDerivAt (fun s => P (f (ψ s)))
        (P.comp ((fderiv ℂ f (ψ t)).comp (fderiv ℂ ψ t))) t := P.hasFDerivAt.comp t hcomp
    have hzero : HasFDerivAt (fun s => P (f (ψ s))) (0 : K →L[ℂ] W) t :=
      (hasFDerivAt_const (P (f z₀)) t).congr_of_eventuallyEq hloc
    have h0 := hcompP.unique hzero
    rw [hcomp.fderiv]
    ext1 v
    apply hkt
    have := congrArg (fun φ : K →L[ℂ] W => φ v) h0
    simpa using this
  have hconst : ∀ t ∈ S, f (ψ t) = f z₀ := by
    intro t ht
    have hdon : DifferentiableOn ℂ (fun s => f (ψ s)) S := fun s hs =>
      (((hf _ (hball s hs).2.2.2.1).differentiableAt one_ne_zero).comp s
        (hball s hs).2.2.1).differentiableWithinAt
    have := Metric.isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball (0 : K) ε).isPreconnected
      hdon (fun s hs => hderiv s hs) ht (Metric.mem_ball_self hε)
    rwa [hψ0] at this
  have hcount : S.Countable := by
    refine Set.MapsTo.countable_of_injOn (f := ψ) (t := {z' ∈ U | f z' = f z₀}) (fun t ht => ⟨(hball t ht).2.2.2.1, hconst t ht⟩)
      ?_ (hc z₀ hz₀)
    intro s hs t ht hst
    rw [← (hball s hs).2.1, ← (hball t ht).2.1]
    simp only [ψ] at hst ⊢
    rw [hst]
  obtain ⟨x, hx, hxS⟩ := (hcount.dense_compl ℂ).inter_open_nonempty S Metric.isOpen_ball
    ⟨0, Metric.mem_ball_self hε⟩
  exact hxS hx
end _root_.GlobalTheory.CountableFibres
end GlobalTheory.CountableFibres
