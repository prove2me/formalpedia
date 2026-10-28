-- Prove2me | solution 1 for OAI.StrictHotSpots.closedTraceSpace_local_rank
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T05:45:08.517188+00:00
-- url     : https://prove2.me/submissions/43104b1a-b060-40cd-8d20-a964f603af6e

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho004
import Theorems.Thm_OAI_StrictHotSpots_Conformal_ClosedDiskChart_eq_zero_of_boundary_closedGradient

section
-- module Solutions.OAIQ3_Hot.HotSpots_Eigenfunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ClosedEigenAlgebra

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace StrictHotSpots

lemma closedEigenJet_eq_zero_of_eqOn {Ω : Set Plane} (ho : IsOpen Ω)
    {v : Plane → ℝ} {Y : Plane → Plane} (hv : ContinuousOn v (closure Ω))
    (hY : ContinuousOn Y (closure Ω)) (he : EqOn (gradient v) Y Ω)
    (hz : EqOn v 0 Ω) : closedEigenJet Ω v Y = 0 := by
  have hzc := hz.of_subset_closure hv continuousOn_const subset_closure (Subset.refl _)
  have hgz : EqOn Y 0 Ω := by
    intro x hx
    rw [← he hx]
    unfold gradient
    rw [(show v =ᶠ[𝓝 x] 0 from eventually_of_mem (ho.mem_nhds hx) (fun y hy => hz hy)).fderiv_eq]
    simp
  have hgc := hgz.of_subset_closure hY continuousOn_const subset_closure (Subset.refl _)
  exact Prod.ext (funext fun x => hzc x.property) (funext fun x => hgc x.property)


end StrictHotSpots
end
end ClosedEigenAlgebra

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Multiplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ClosedBoundaryZeroJet

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff InnerProductSpace
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)
include c




theorem hasFDerivWithinAt_zero_of_closedGradient_zero {v : Plane → ℝ}
    (hv : ContDiffOn ℝ ∞ v Ω) (hvc : ContinuousOn v (closure Ω))
    {Y : Plane → Plane} (hY : ContinuousOn Y (closure Ω)) (he : EqOn (gradient v) Y Ω)
    {p : Plane} (hp : p ∈ closure Ω) (hz : Y p = 0) :
    HasFDerivWithinAt v (0 : Plane →L[ℝ] ℝ) (closure Ω) p := by
  have hGp := c.inverse_maps_closed hp
  have hYG : Tendsto (fun z => Y (c.F z)) (𝓝[disk] (c.G p)) (𝓝 (0 : Plane)) := by
    have hc := (hY.comp c.continuous_closed c.maps_closed (c.G p) hGp).mono subset_closure
    change Tendsto (Y ∘ c.F) (𝓝[disk] c.G p) (𝓝 (Y (c.F (c.G p)))) at hc
    rw [c.right_inverse p hp,hz] at hc
    exact hc
  have hlim : Tendsto (fun z => fderiv ℝ (c.pullDatum v) z)
      (𝓝[disk] (c.G p)) (𝓝 (0 : Plane →L[ℝ] ℝ)) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (g := fun z => c.bound * ‖Y (c.F z)‖) (Eventually.of_forall fun _ => norm_nonneg _)
    · filter_upwards [self_mem_nhdsWithin] with z hzD
      have hn : ‖fderiv ℝ (c.pullDatum v) z‖ = ‖gradient (c.pullDatum v) z‖ := by
        simp only [gradient,LinearIsometryEquiv.norm_map]
      rw [hn,c.pullDatum_grad_norm (hv.differentiableOn (by simp)) hzD,
        he (c.diskMap.map_source hzD),c.diskMap_agrees hzD]
      exact mul_le_mul_of_nonneg_right (c.bounded_deriv z (c.source_eq.symm ▸ hzD)) (norm_nonneg _)
    · simpa only [norm_zero,mul_zero] using tendsto_const_nhds.mul hYG.norm
  have hD : HasFDerivWithinAt (c.pullDatum v) (0 : Plane →L[ℝ] ℝ)
      (closure disk) (c.G p) :=
    hasFDerivWithinAt_closure_of_tendsto_fderiv
      ((c.pullDatum_smooth hv).differentiableOn (by simp))
      (convex_ball (0:Plane) 1) diskOpen
      (fun z hzD => (c.pullDatum_continuous hvc z hzD).mono subset_closure) hlim
  have ht : Tendsto c.G (𝓝[closure Ω] p) (𝓝[closure disk] (c.G p)) :=
    c.inverse_lipschitz.continuous.continuousWithinAt.tendsto_nhdsWithin c.inverse_maps_closed
  have hsmall := (hasFDerivWithinAt_iff_isLittleO.mp hD).comp_tendsto ht
  have hbig : (fun x => c.G x-c.G p) =O[𝓝[closure Ω] p] (fun x => x-p) :=
    Asymptotics.IsBigO.of_bound c.InvLip (Eventually.of_forall (fun x => c.inverse_lipschitz.norm_sub_le x p))
  have hh := hsmall.trans_isBigO hbig
  apply hasFDerivWithinAt_iff_isLittleO.mpr
  apply hh.congr' _ (Filter.EventuallyEq.refl _ _)
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp only [Function.comp_apply,zero_apply,sub_zero,pullDatum,
    c.right_inverse x hx,c.right_inverse p hp]

end StrictHotSpots.Conformal.ClosedDiskChart
end
end ClosedBoundaryZeroJet


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Cauchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualBoundaryCauchySupport

section ActualBoundaryLocalConstLayer
noncomputable section
open Set Filter Metric Function
open scoped Topology ContDiff
namespace StrictHotSpots

lemma nonzero_real_functional_surjective (D : Plane →L[ℝ] ℝ) (hD : D ≠ 0) :
    D.range = ⊤ := by
  apply LinearMap.range_eq_top.mpr
  have hn : ∃ v, D v ≠ 0 := by
    by_contra hh
    apply hD
    ext v
    simpa using not_exists.mp hh v
  obtain ⟨v,hv⟩ := hn
  intro t
  refine ⟨(t / D v) • v,?_⟩
  simp [map_smul,div_mul_cancel₀ _ hv]

lemma frontier_level_zero {Ω U : Set Plane} {ρ : Plane → ℝ} {p : Plane}
    (ho : IsOpen Ω) (hU : IsOpen U) (hpU : p ∈ U) (hp : p ∈ frontier Ω)
    (hc : ContinuousAt ρ p)
    (he : Ω ∩ U = {x | ρ x < 0} ∩ U) : ρ p = 0 := by
  apply le_antisymm
  · by_contra hh
    have ht : ∀ᶠ x in 𝓝 p, x ∈ U ∧ 0 < ρ x :=
      (show ∀ᶠ x in 𝓝 p, x ∈ U from hU.mem_nhds hpU).and
        (hc (lt_mem_nhds (lt_of_not_ge hh)))
    obtain ⟨x,hx,hxU,hpx⟩ := (mem_closure_iff_frequently.mp hp.1).and_eventually ht |>.exists
    have hz : ρ x < 0 := (he ▸ (show x ∈ Ω ∩ U from ⟨hx,hxU⟩)).1
    exact (not_lt_of_ge hpx.le) hz
  · by_contra hh
    have hm : p ∈ Ω := ((he.symm ▸ (show p ∈ {x | ρ x < 0} ∩ U from
      ⟨lt_of_not_ge hh,hpU⟩)) : p ∈ Ω ∩ U).1
    exact hp.2 (ho.interior_eq.symm ▸ hm)

lemma regular_level_mem_frontier {Ω U : Set Plane} {ρ : Plane → ℝ} {p : Plane}
    (ho : IsOpen Ω) (hU : IsOpen U) (hpU : p ∈ U)
    (hc : DifferentiableAt ℝ ρ p) (hD : fderiv ℝ ρ p ≠ 0) (hpρ : ρ p = 0)
    (he : Ω ∩ U = {x | ρ x < 0} ∩ U) : p ∈ frontier Ω := by
  obtain ⟨v,hv⟩ : ∃ v, fderiv ℝ ρ p v = -1 :=
    LinearMap.range_eq_top.mp (nonzero_real_functional_surjective _ hD) (-1)
  have ht : Tendsto (fun t : ℝ => p+t•v) (𝓝[>] 0) (𝓝 p) := by
    simpa using tendsto_const_nhds.add
      ((tendsto_id'.mpr (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)).smul_const v)
  have hm : ∀ᶠ t in 𝓝[>] (0 : ℝ), p+t•v ∈ Ω := by
    filter_upwards [HasFDerivAt.eventually_lt_along_ray hc.hasFDerivAt
      (show fderiv ℝ ρ p v < 0 by rw [hv]; norm_num),ht (hU.mem_nhds hpU)] with t hneg htU
    exact ((he.symm ▸ (show p+t•v ∈ {x | ρ x < 0} ∩ U from
      ⟨by change ρ (p+t•v) < 0; simpa only [hpρ] using hneg,htU⟩)) : p+t•v ∈ Ω ∩ U).1
  refine ⟨mem_closure_of_tendsto ht hm,?_⟩
  rw [ho.interior_eq]
  intro hh
  have hz : ρ p < 0 := (he ▸ (show p ∈ Ω ∩ U from ⟨hh,hpU⟩)).1
  simp only [hpρ,lt_self_iff_false] at hz





theorem SmoothBoundary.locally_const_of_boundary_zero_jet
    {Ω O : Set Plane} {u : Plane → ℝ} (hs : SmoothBoundary Ω) (ho : IsOpen Ω)
    {p : Plane} (hp : p ∈ frontier Ω)
    (hO : IsOpen O) (hpO : p ∈ O)
    (hz : ∀ x ∈ O ∩ frontier Ω, HasFDerivWithinAt u (0 : Plane →L[ℝ] ℝ) (closure Ω) x) :
    ∃ V : Set Plane, IsOpen V ∧ p ∈ V ∧ ∀ x ∈ V ∩ frontier Ω, u x = u p := by
  obtain ⟨U,ρ,hU,hpU,hρ,hD,hpρ,he⟩ := hs p hp
  have hρat : ContDiffAt ℝ ∞ ρ p := (hρ p hpU).contDiffAt (hU.mem_nhds hpU)
  let D := fderiv ℝ ρ p
  let hker := D.ker_closedComplemented_of_finiteDimensional_range
  let φ := HasStrictFDerivAt.implicitFunctionDataOfComplemented ρ D
    (hρat.hasStrictFDerivAt (by simp)) (nonzero_real_functional_surjective D hD) hker
  have hφp : φ.prodFun p = (0,0) := by
    simp [φ,ImplicitFunctionData.prodFun,hpρ]
  have hr : ContDiff ℝ ∞ φ.rightFun := by
    change ContDiff ℝ ∞ (fun x => Classical.choose hker (x-p))
    fun_prop
  have hcunc : ContDiffAt ℝ 1 φ.implicitFunction.uncurry (0,0) := by
    rw [← hφp]
    exact φ.contDiffAt_implicitFunction (hρat.of_le (by simp))
      (hr.contDiffAt.of_le (by simp)) (by simp)
  let c : D.ker → Plane := φ.implicitFunction 0
  have hc : ContDiffAt ℝ 1 c 0 := by
    exact hcunc.comp 0 (contDiffAt_const.prodMk contDiffAt_id)
  have hcp : c 0 = p := by
    have hh := φ.toOpenPartialHomeomorph.left_inv φ.pt_mem_toOpenPartialHomeomorph_source
    change φ.implicitFunction (φ.prodFun p).1 (φ.prodFun p).2 = p at hh
    simpa only [hφp] using hh
  have ht : Tendsto (fun y : D.ker => (0,y)) (𝓝 0) (𝓝 (φ.prodFun p)) := by
    rw [hφp]
    exact tendsto_const_nhds.prodMk_nhds tendsto_id
  have hcρ : ∀ᶠ y in 𝓝 (0 : D.ker), ρ (c y) = 0 := ht φ.leftFun_implicitFunction
  have hct : Tendsto c (𝓝 (0 : D.ker)) (𝓝 p) := hcp ▸ hc.continuousAt.tendsto
  have hdn := hct ((hρat.continuousAt_fderiv (by simp)).eventually_ne hD)
  have hgood : ∀ᶠ y in 𝓝 (0 : D.ker), DifferentiableAt ℝ c y ∧ c y ∈ O ∩ frontier Ω := by
    filter_upwards [hc.eventually (by simp),hcρ,hdn,hct (hU.mem_nhds hpU),
      hct (hO.mem_nhds hpO)] with y hcy hρy hdy hyU hyO
    refine ⟨hcy.differentiableAt (by simp),hyO,?_⟩
    exact regular_level_mem_frontier ho hU hyU
      (((hρ (c y) hyU).contDiffAt (hU.mem_nhds hyU)).differentiableAt (by simp))
      hdy hρy he
  obtain ⟨ε,hε,hεgood⟩ := Metric.eventually_nhds_iff.mp hgood
  have hfzero (y : D.ker) (hy : y ∈ ball 0 ε) : HasFDerivAt (u ∘ c) (0 : D.ker →L[ℝ] ℝ) y := by
    have hygood := hεgood hy
    have hdu := hz (c y) hygood.2
    have hmaps : ∀ᶠ z in 𝓝 y, c z ∈ closure Ω := by
      filter_upwards [isOpen_ball.mem_nhds hy] with z hz
      exact (hεgood hz).2.2.1
    simpa only [ContinuousLinearMap.zero_comp] using
      hdu.comp_hasFDerivAt y hygood.1.hasFDerivAt hmaps
  have hconst (y : D.ker) (hy : y ∈ ball 0 ε) : u (c y) = u p := by
    have hh := (convex_ball (0 : D.ker) ε).is_const_of_fderivWithin_eq_zero
      (fun z hz => (hfzero z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hfzero z hz).hasFDerivWithinAt.fderivWithin
        (isOpen_ball.uniqueDiffOn z hz)) hy (mem_ball_self hε)
    exact hh.trans (congrArg u hcp)
  have hright0 : φ.rightFun p = 0 := congrArg Prod.snd hφp
  have hry : ∀ᶠ x in 𝓝 p, φ.rightFun x ∈ ball 0 ε := by
    exact hr.continuous.continuousAt.tendsto
      (hright0.symm ▸ (isOpen_ball.mem_nhds (mem_ball_self hε)))
  have hloc : ∀ᶠ x in 𝓝 p, x ∈ frontier Ω → u x = u p := by
    filter_upwards [hU.mem_nhds hpU,hry,φ.implicitFunction_apply_image] with x hxU hxy hix
    intro hxf
    have hzρ := frontier_level_zero ho hU hxU hxf
      ((hρ x hxU).continuousWithinAt.continuousAt (hU.mem_nhds hxU)) he
    have hic : c (φ.rightFun x) = x := by
      change φ.implicitFunction 0 (φ.rightFun x) = x
      change φ.implicitFunction (ρ x) (φ.rightFun x) = x at hix
      simpa only [hzρ] using hix
    exact hic ▸ hconst _ hxy
  obtain ⟨V,hV,hVo,hpV⟩ := _root_.mem_nhds_iff.mp hloc
  exact ⟨V,hVo,hpV,fun x hx => hV hx.1 hx.2⟩

end StrictHotSpots

end
end ActualBoundaryLocalConstLayer
end ActualBoundaryCauchySupport

section ClosedEigenLocalRank

noncomputable section
open Set Filter Metric Function
open scoped Topology ContDiff InnerProductSpace
namespace StrictHotSpots

lemma closedPatchEval_injective {Ω O : Set Plane} (c : Conformal.ClosedDiskChart Ω)
    (hΩ : AdmissibleDomain Ω) {p : Plane} (hp : p ∈ frontier Ω) (hO : IsOpen O) (hpO : p ∈ O) :
    Injective (closedPatchEval (O := O) hΩ hp) := by
  have hzero (J : closedPatchEigenSpace Ω O hΩ) (hJ : closedPatchEval hΩ hp J = 0) : J = 0 := by
    obtain ⟨v,Y,hv,hvc,hY,he,hjet⟩ := J.property.1
    have hz (x : Plane) (hx : x ∈ O ∩ frontier Ω) : Y x = 0 := by
      have h := J.property.2 ⟨x,hx.2.1⟩ hx
      rw [← hjet] at h
      exact h
    have hd (x : Plane) (hx : x ∈ O ∩ frontier Ω) :
        HasFDerivWithinAt v (0 : Plane →L[ℝ] ℝ) (closure Ω) x :=
      c.hasFDerivWithinAt_zero_of_closedGradient_zero hv.1 hvc hY he hx.2.1 (hz x hx)
    obtain ⟨V,hV,hpV,hconst⟩ := hΩ.2.2.2.2.locally_const_of_boundary_zero_jet hΩ.2.1 hp hO hpO hd
    have hvp : v p = 0 := by
      change J.val.1 ⟨p,hp.1⟩ = 0 at hJ
      rw [← hjet] at hJ
      exact hJ
    have hv0 : EqOn v 0 Ω := c.eq_zero_of_boundary_closedGradient hΩ hv hvc hY he hp
      (hV.inter hO) ⟨hpV,hpO⟩
      (fun x hx => ⟨(hconst x ⟨hx.1.1,hx.2⟩).trans hvp,hz x ⟨hx.1.2,hx.2⟩⟩)
    apply Subtype.ext
    exact hjet.symm.trans (closedEigenJet_eq_zero_of_eqOn hΩ.2.1 hvc hY he hv0)
  intro J K hJK
  apply sub_eq_zero.mp
  apply hzero (J-K)
  change J.val.1 ⟨p,hp.1⟩ - K.val.1 ⟨p,hp.1⟩ = 0
  exact sub_eq_zero.mpr hJK


theorem closedPatchEigenSpace_finrank_le_one {Ω O : Set Plane} (c : Conformal.ClosedDiskChart Ω)
    (hΩ : AdmissibleDomain Ω) {p : Plane} (hp : p ∈ frontier Ω) (hO : IsOpen O) (hpO : p ∈ O) :
    Module.Finite ℝ (closedPatchEigenSpace Ω O hΩ) ∧
      Module.finrank ℝ (closedPatchEigenSpace Ω O hΩ) ≤ 1 := by
  have hi := closedPatchEval_injective c hΩ hp hO hpO
  have hf := Module.Finite.of_injective (closedPatchEval (O := O) hΩ hp) hi
  let : Module.Finite ℝ (closedPatchEigenSpace Ω O hΩ) := hf
  exact ⟨hf,by simpa using LinearMap.finrank_le_finrank_of_injective hi⟩
end StrictHotSpots
end
end ClosedEigenLocalRank



end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_TraceRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ClosedTraceRank

noncomputable section
open Set Function Module
open scoped Topology
namespace StrictHotSpots
open HilbertMultipliers


lemma closedTraceSpace_local_rank_oai {Ω : Set Plane} (c : Conformal.ClosedDiskChart Ω)
    (hΩ : AdmissibleDomain Ω) {U : Set Circle} (hU : IsOpen U) (hne : U.Nonempty) :
    finrank ℝ (vanishingOn (closedTraceSpace c hΩ) U) ≤ 1 := by
  classical
  obtain ⟨O,hO,hOU⟩ := isOpen_induced_iff.mp (c.circleBoundaryHomeomorph.isOpenMap U hU)
  have hmem (s : Circle) : s ∈ U ↔ (c.circleBoundaryHomeomorph s : Plane) ∈ O := by
    have hh : c.circleBoundaryHomeomorph s ∈ c.circleBoundaryHomeomorph '' U ↔ s ∈ U :=
      c.circleBoundaryHomeomorph.injective.mem_set_image
    rw [← hOU] at hh
    exact hh.symm
  obtain ⟨s,hs⟩ := hne
  obtain ⟨hf,hr⟩ := closedPatchEigenSpace_finrank_le_one c hΩ
    (c.circleBoundaryHomeomorph s).property hO ((hmem s).mp hs)
  let : Module.Finite ℝ (closedPatchEigenSpace Ω O hΩ) := hf
  let E := closedEigenSpace Ω hΩ.2.1 hΩ.2.2.1
  let P := closedPatchEigenSpace Ω O hΩ
  let inc : P →ₗ[ℝ] E := Submodule.inclusion (fun _ h => h.1)
  let L := (closedGradientTrace c hΩ).comp inc
  have heq : L.range = vanishingOn (closedTraceSpace c hΩ) U := by
    ext g
    constructor
    · rintro ⟨J,rfl⟩
      refine ⟨⟨inc J,rfl⟩,?_⟩
      intro t ht
      exact J.property.2 _ ⟨(hmem t).mp ht,(c.circleBoundaryHomeomorph t).property⟩
    · rintro ⟨⟨J,hJ⟩,hz⟩
      have hpatch : J.val ∈ P := by
        refine ⟨J.property,?_⟩
        intro x hx
        let t := c.circleBoundaryHomeomorph.symm ⟨x,hx.2⟩
        have ht : (c.circleBoundaryHomeomorph t : Plane) = x :=
          congrArg Subtype.val (c.circleBoundaryHomeomorph.apply_symm_apply ⟨x,hx.2⟩)
        have htU : t ∈ U := (hmem t).mpr (ht ▸ hx.1)
        have hh := hz t htU
        rw [← hJ] at hh
        change J.val.2 ⟨c.circleBoundaryHomeomorph t,_⟩ = 0 at hh
        convert hh using 1
        exact congrArg J.val.2 (Subtype.ext ht.symm)
      refine ⟨⟨J.val,hpatch⟩,?_⟩
      exact hJ
  rw [← heq]
  exact (LinearMap.finrank_range_le L).trans hr
end StrictHotSpots
end
end ClosedTraceRank



end OAI
end

theorem solution : type_of% @OAI.StrictHotSpots.closedTraceSpace_local_rank_oai := @OAI.StrictHotSpots.closedTraceSpace_local_rank_oai
