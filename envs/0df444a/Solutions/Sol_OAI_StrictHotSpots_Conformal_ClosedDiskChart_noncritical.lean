-- Prove2me | solution 1 for OAI.StrictHotSpots.Conformal.ClosedDiskChart.noncritical
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T05:37:26.31239+00:00
-- url     : https://prove2.me/submissions/7e7db57b-646f-4e20-83e5-a89391e50c6b

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho004
import Theorems.Thm_OAI_StrictHotSpots_Conformal_ClosedDiskChart_coordinate_null_trace
import Theorems.Thm_OAI_StrictHotSpots_Conformal_ClosedDiskChart_subcritical
import Theorems.Thm_OAI_StrictHotSpots_InteriorBoundarySign_exists_boundary_neg
import Theorems.Thm_OAI_StrictHotSpots_InteriorBoundarySign_exists_boundary_pos
import Theorems.Thm_OAI_StrictHotSpots_PlaneGreen_full_boundary_hilbert_embedding
import Theorems.Thm_OAI_StrictHotSpots_closedTraceSpace_local_rank
import Theorems.Thm_OAI_StrictHotSpots_closedTraceSpace_rank

section
-- module Solutions.OAIQ3_Hot.HotSpots_Multiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section LipschitzMultiplierKernel

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal Topology
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen Hodge
variable {Ω : Set Plane} (c : ClosedDiskChart Ω) (hΩ : AdmissibleDomain Ω)
variable {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u)
variable (hμ : 0 < firstPositiveNeumannValue Ω)
variable {L : ℝ} (hl : firstPositiveNeumannValue Ω < L)
  (hD : ∀ j : H10 hΩ.2.1, L*‖H10.value hΩ.2.1 j‖^2 ≤ ‖H10.grad hΩ.2.1 j‖^2)

include hΩ hu in
lemma closedGradient_trace_continuous :
    Continuous (fun s : Boundary => closedGradient Ω u (c.F s)) := by
  apply (closedGradient_continuous hΩ.2.1 hΩ.2.2.2.2 hu.1).comp_continuous
    (c.lipschitz.continuous.comp continuous_subtype_val)
  intro s
  exact c.maps_closed (boundary_mem_closed s)

end StrictHotSpots.Conformal.ClosedDiskChart
end
end LipschitzMultiplierKernel

section HilbertMultiplierSum

noncomputable section
open Set MeasureTheory Metric Function
open scoped InnerProductSpace Topology
namespace StrictHotSpots.HilbertMultipliers

lemma orthonormal_countable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [TopologicalSpace.SeparableSpace H] {e : ι → H} (he : Orthonormal ℝ e) : Countable ι := by
  have hp : Pairwise (Disjoint on fun i => ball (e i) (1/2:ℝ)) := by
    intro i j hij
    apply disjoint_left.mpr
    intro x hxi hxj
    have hd : dist (e i) (e j) < 1 := by
      have h := dist_triangle (e i) x (e j)
      have hi : dist (e i) x < 1/2 := by simpa [dist_comm] using hxi
      have hj : dist x (e j) < 1/2 := hxj
      linarith
    have hn : ‖e i-e j‖^2 = 2 := by
      rw [norm_sub_sq_real,he.1 i,he.1 j,he.2 hij]
      norm_num
    rw [dist_eq_norm] at hd
    nlinarith [norm_nonneg (e i-e j)]
  exact hp.countable_of_isOpen_disjoint (fun _ => isOpen_ball)
    (fun i => ⟨e i,mem_ball_self (by norm_num)⟩)

end StrictHotSpots.HilbertMultipliers
end
end HilbertMultiplierSum


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Eigenfunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualInteriorEigenSupport



noncomputable section
open Set MeasureTheory Filter Metric
open scoped ContDiff Laplacian Topology


section WeakEigenRegularityActualInteriorLayer
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped ContDiff Topology
namespace StrictHotSpots



lemma InFirstNeumannEigenspace.interior {Ω : Set Plane} {u : Plane → ℝ}
    (hu : InFirstNeumannEigenspace Ω u) : InInteriorNeumannEigenspace Ω u :=
  ⟨hu.1.mono subset_closure,hu.2⟩



end StrictHotSpots
end
end WeakEigenRegularityActualInteriorLayer


end
end ActualInteriorEigenSupport

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



end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_TraceRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualHilbertContradiction


section

noncomputable section
open Set Function
open scoped InnerProductSpace Topology
namespace StrictHotSpots.CircleGeometry

lemma continuous_exists_eq_antipodal (f : Circle → ℝ) (hf : Continuous f) :
    ∃ s, f s = f (-s) := by
  let h : Circle → ℝ := fun s => f s-f (-s)
  have hc : Continuous h := hf.sub (hf.comp continuous_neg)
  have hn (s : Circle) : h (-s) = -h s := by simp only [h,neg_neg]; ring
  have hx : 0 ∈ Set.range h := by
    apply mem_range_of_exists_le_of_exists_ge hc
    · by_cases hh : h 1 ≤ 0
      · exact ⟨1,hh⟩
      · exact ⟨-1,by rw [hn]; linarith⟩
    · by_cases hh : 0 ≤ h 1
      · exact ⟨1,hh⟩
      · exact ⟨-1,by rw [hn]; linarith⟩
  obtain ⟨s,hs⟩ := hx
  exact ⟨s,sub_eq_zero.mp hs⟩

lemma not_continuous_injective_to_real {f : Circle → ℝ} (hf : Continuous f) :
    ¬Injective f := by
  intro hi
  obtain ⟨s,hs⟩ := continuous_exists_eq_antipodal f hf
  exact Circle.neg_ne_self s (hi hs).symm


theorem not_subset_affine_line {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {b : Circle → H} (hb : Continuous b) (hi : Injective b) (a v : H) :
    ¬(∀ s, ∃ t : ℝ, b s = a+t•v) := by
  intro hline
  have hn : v ≠ 0 := by
    intro hz
    apply Circle.neg_ne_self (1 : Circle)
    apply hi
    obtain ⟨c,hc⟩ := hline (-1)
    obtain ⟨d,hd⟩ := hline 1
    simp only [hz,smul_zero,add_zero] at hc hd
    exact hc.trans hd.symm
  let f : Circle → ℝ := fun s => inner ℝ v (b s-a)
  apply not_continuous_injective_to_real (show Continuous f by fun_prop)
  intro s t hst
  obtain ⟨r,hr⟩ := hline s
  obtain ⟨q,hq⟩ := hline t
  have hne : inner ℝ v v ≠ 0 := inner_self_ne_zero.mpr hn
  have he : r=q := by
    change inner ℝ v (b s-a) = inner ℝ v (b t-a) at hst
    rw [hr,hq,add_sub_cancel_left,add_sub_cancel_left,real_inner_smul_right,
      real_inner_smul_right] at hst
    exact mul_right_cancel₀ hne hst
  apply hi
  rw [hr,hq,he]

end StrictHotSpots.CircleGeometry

end

section

noncomputable section
open Set Function Module
open scoped InnerProductSpace Topology
namespace StrictHotSpots.HilbertMultipliers

variable {S E H ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

local instance instNontrivialCircle_solutions : Nontrivial Circle := ⟨⟨-1,1,Circle.neg_ne_self 1⟩⟩

lemma coordinate_separates (e : HilbertBasis ι ℝ H) {x y : H} (h : x ≠ y) :
    ∃ i, inner ℝ (e i) x ≠ inner ℝ (e i) y := by
  by_contra! hh
  apply h
  apply e.repr.injective
  ext i
  simpa only [e.repr_apply_apply] using hh i

lemma pair_independent (T : Submodule ℝ (S → E)) (g : T) (a : S → ℝ)
    (ha : (fun s => a s • g.val s) ∈ T) {s t : S}
    (hs : g.val s ≠ 0) (ht : g.val t ≠ 0) (hst : a s ≠ a t) :
    LinearIndependent ℝ ![(⟨fun s => a s • g.val s,ha⟩ : T),g] := by
  rw [linearIndependent_fin2]
  constructor
  · intro hz
    exact hs (congrArg (fun f : T => f.val s) hz)
  · intro c hc
    have hcs := congrArg (fun f : T => f.val s) hc
    have hct := congrArg (fun f : T => f.val t) hc
    change c • g.val s = a s • g.val s at hcs
    change c • g.val t = a t • g.val t at hct
    exact hst ((smul_left_injective ℝ hs hcs).symm.trans (smul_left_injective ℝ ht hct))

lemma rank_two_spanning {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] {f g : V} (hr : finrank ℝ V ≤ 2)
    (hi : LinearIndependent ℝ ![f,g]) (v : V) : ∃ a c : ℝ, a • f+c • g=v := by
  have hn : Fintype.card (Fin 2) = finrank ℝ V := by
    have hh := hi.fintype_card_le_finrank
    simpa using (le_antisymm hh hr)
  have htop := hi.span_eq_top_of_card_eq_finrank' hn
  apply Submodule.mem_span_pair.mp
  have he : Set.range ![f,g] = ({f,g} : Set V) := by simp [Set.pair_comm]
  rw [← he,htop]
  trivial

lemma scalar_affine_elimination {A B C D P Q z : ℝ} (hne : P ≠ Q)
    (hA : A=C*P+D) (hB : B=C*Q+D) :
    C*z+D = A+((z-P)/(Q-P))*(B-A) := by
  have hd : Q-P ≠ 0 := sub_ne_zero.mpr hne.symm
  rw [hA,hB]
  field_simp
  ring




theorem rank_two_affine_support (e : HilbertBasis ι ℝ H) (b : S → H)
    (T : Submodule ℝ (S → E)) [FiniteDimensional ℝ T] (hr : finrank ℝ T ≤ 2)
    (g : T) (hmem : ∀ i, (fun s => inner ℝ (e i) (b s) • g.val s) ∈ T)
    {s t : S} (hs : g.val s ≠ 0) (ht : g.val t ≠ 0) (hb : b s ≠ b t) :
    ∃ j, inner ℝ (e j) (b s) ≠ inner ℝ (e j) (b t) ∧
      ∀ x, g.val x ≠ 0 → b x = b s +
        ((inner ℝ (e j) (b x)-inner ℝ (e j) (b s)) /
          (inner ℝ (e j) (b t)-inner ℝ (e j) (b s))) • (b t-b s) := by
  obtain ⟨j,hj⟩ := coordinate_separates e hb
  let f : T := ⟨fun x => inner ℝ (e j) (b x) • g.val x,hmem j⟩
  have hi : LinearIndependent ℝ ![f,g] := pair_independent T g _ (hmem j) hs ht hj
  refine ⟨j,hj,?_⟩
  intro x hx
  apply e.repr.injective
  ext i
  simp only [e.repr_apply_apply,inner_add_right,real_inner_smul_right,inner_sub_right]
  obtain ⟨a,c,hac⟩ := rank_two_spanning hr hi (⟨fun y => inner ℝ (e i) (b y) • g.val y,hmem i⟩ : T)
  have he (y : S) (hy : g.val y ≠ 0) : inner ℝ (e i) (b y) = a*inner ℝ (e j) (b y)+c := by
    have hh := congrArg (fun f : T => f.val y) hac
    change a • (inner ℝ (e j) (b y) • g.val y)+c • g.val y =
      inner ℝ (e i) (b y) • g.val y at hh
    rw [smul_smul,← add_smul] at hh
    exact (smul_left_injective ℝ hy hh).symm
  rw [he x hx]
  exact scalar_affine_elimination hj (he s hs) (he t ht)

lemma nonempty_open_two_points {S : Type*} [TopologicalSpace S] [PerfectSpace S]
    {U : Set S} (hu : IsOpen U) (hne : U.Nonempty) :
    ∃ s ∈ U, ∃ t ∈ U, s ≠ t := by
  obtain ⟨s,hs⟩ := hne
  obtain ⟨t,ht,hst⟩ := preperfect_iff_nhds.mp PerfectSpace.univ_preperfect
    s (mem_univ s) U (hu.mem_nhds hs)
  exact ⟨s,hs,t,ht.1,hst.symm⟩



theorem not_dense_support_of_rank_two (e : HilbertBasis ι ℝ H)
    {b : Circle → H} (hb : Continuous b) (hi : Injective b)
    (T : Submodule ℝ (Circle → E)) [FiniteDimensional ℝ T] (hr : finrank ℝ T ≤ 2)
    (g : T) (hg : Continuous g.val)
    (hmem : ∀ i, (fun s => inner ℝ (e i) (b s) • g.val s) ∈ T) :
    ¬Dense {s | g.val s ≠ 0} := by
  intro hd
  have ho : IsOpen {s | g.val s ≠ 0} := isOpen_ne_fun hg continuous_const
  obtain ⟨s,hs,t,ht,hst⟩ := nonempty_open_two_points ho hd.nonempty
  obtain ⟨j,hj,hline⟩ := rank_two_affine_support e b T hr g hmem hs ht (hi.ne hst)
  have hall : b = fun x => b s +
      ((inner ℝ (e j) (b x)-inner ℝ (e j) (b s)) /
        (inner ℝ (e j) (b t)-inner ℝ (e j) (b s))) • (b t-b s) :=
    Continuous.ext_on hd hb (by fun_prop) hline
  apply CircleGeometry.not_subset_affine_line hb hi (b s) (b t-b s)
  intro x
  exact ⟨_,congrFun hall x⟩



theorem no_nonzero_multiplier_in_rank_one (e : HilbertBasis ι ℝ H)
    {b : Circle → H} (hi : Injective b)
    (T : Submodule ℝ (Circle → E)) [FiniteDimensional ℝ T] (hr : finrank ℝ T ≤ 1)
    (g : T) (hg : Continuous g.val)
    (hmem : ∀ i, (fun s => inner ℝ (e i) (b s) • g.val s) ∈ T) : g = 0 := by
  by_contra hz
  have hne : {s | g.val s ≠ 0}.Nonempty := by
    by_contra hh
    apply hz
    apply Subtype.ext
    funext s
    exact not_ne_iff.mp (fun hs => hh ⟨s,hs⟩)
  obtain ⟨s,hs,t,ht,hst⟩ := nonempty_open_two_points (isOpen_ne_fun hg continuous_const) hne
  obtain ⟨j,hj⟩ := coordinate_separates e (hi.ne hst)
  have hlin := pair_independent T g _ (hmem j) hs ht hj
  have hn := hlin.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hn
  omega

end StrictHotSpots.HilbertMultipliers

end

section

noncomputable section
open Set Function Module
open scoped InnerProductSpace Topology
namespace StrictHotSpots.HilbertMultipliers

variable {S E H ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]


lemma vanishingOn_le (T : Submodule ℝ (S → E)) (U : Set S) : vanishingOn T U ≤ T :=
  fun _ hf => hf.1

instance instFiniteDimensionalRealSubtypeForallMemSubmoduleVanishingOn (T : Submodule ℝ (S → E)) [FiniteDimensional ℝ T] (U : Set S) :
    FiniteDimensional ℝ (vanishingOn T U) :=
  FiniteDimensional.of_injective (Submodule.inclusion (vanishingOn_le T U))
    (Submodule.inclusion_injective (vanishingOn_le T U))




theorem multiplier_contradiction (e : HilbertBasis ι ℝ H)
    {b : Circle → H} (hb : Continuous b) (hi : Injective b)
    (T : Submodule ℝ (Circle → E)) [FiniteDimensional ℝ T]
    (hr : finrank ℝ T ≤ 2)
    (hloc : ∀ U : Set Circle, IsOpen U → U.Nonempty → finrank ℝ (vanishingOn T U) ≤ 1)
    (g : T) (hg : Continuous g.val)
    (hmem : ∀ i, (fun s => inner ℝ (e i) (b s) • g.val s) ∈ T) : g = 0 := by
  have hnd := not_dense_support_of_rank_two e hb hi T hr g hg hmem
  let U : Set Circle := (closure {s | g.val s ≠ 0})ᶜ
  have hU : IsOpen U := isClosed_closure.isOpen_compl
  have hne : U.Nonempty := by
    rw [dense_iff_closure_eq] at hnd
    exact Set.nonempty_compl.mpr hnd
  have hz (s : Circle) (hs : s ∈ U) : g.val s = 0 := by
    by_contra hn
    exact hs (subset_closure hn)
  let f : vanishingOn T U := ⟨g.val,g.property,hz⟩
  have hm (i : ι) : (fun s => inner ℝ (e i) (b s) • f.val s) ∈ vanishingOn T U := by
    refine ⟨hmem i,?_⟩
    intro s hs
    change inner ℝ (e i) (b s) • g.val s = 0
    rw [hz s hs,smul_zero]
  have hf := no_nonzero_multiplier_in_rank_one e hi (vanishingOn T U) (hloc U hU hne) f hg hm
  exact Subtype.ext (congrArg (fun w : vanishingOn T U => w.val) hf)

end StrictHotSpots.HilbertMultipliers

end
end
end
end
end ActualHilbertContradiction

section ClosedTraceNonzero

noncomputable section
open Set Filter Metric Function
open scoped Topology ContDiff InnerProductSpace
namespace StrictHotSpots.Conformal.ClosedDiskChart
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)
include c




theorem boundary_gradient_not_zero (hΩ : AdmissibleDomain Ω)
    {v : Plane → ℝ} (hv : InInteriorNeumannEigenspace Ω v)
    (hvc : ContinuousOn v (closure Ω)) {Y : Plane → Plane}
    (hY : ContinuousOn Y (closure Ω)) (he : EqOn (gradient v) Y Ω)
    (hne : ∃ x ∈ Ω, v x ≠ 0) : ¬ (∀ x ∈ frontier Ω, Y x = 0) := by
  intro hz
  have hd (x : Plane) (hx : x ∈ frontier Ω) :
      HasFDerivWithinAt v (0 : Plane →L[ℝ] ℝ) (closure Ω) x :=
    c.hasFDerivWithinAt_zero_of_closedGradient_zero hv.1 hvc hY he hx.1 (hz x hx)
  let f : Circle → ℝ := fun s => v (c.circleBoundaryHomeomorph s)
  have hmap : Continuous (fun s : Circle => (c.circleBoundaryHomeomorph s : Plane)) :=
    continuous_subtype_val.comp c.circleBoundaryHomeomorph.continuous
  have hc : IsLocallyConstant f := by
    apply (IsLocallyConstant.iff_exists_open f).mpr
    intro s
    obtain ⟨V,hV,hsV,hconst⟩ := hΩ.2.2.2.2.locally_const_of_boundary_zero_jet hΩ.2.1
      (c.circleBoundaryHomeomorph s).property isOpen_univ (mem_univ _)
      (fun x hx => hd x hx.2)
    refine ⟨(fun s : Circle => (c.circleBoundaryHomeomorph s : Plane)) ⁻¹' V,
      hV.preimage hmap,hsV,?_⟩
    intro t ht
    exact hconst _ ⟨ht,(c.circleBoundaryHomeomorph t).property⟩
  obtain ⟨x,hx,hvx⟩ := InteriorBoundarySign.exists_boundary_pos hΩ.2.1 hΩ.2.2.1 hv hvc hne
  obtain ⟨y,hy,hvy⟩ := InteriorBoundarySign.exists_boundary_neg hΩ.2.1 hΩ.2.2.1 hv hvc hne
  have heq := hc.apply_eq_of_preconnectedSpace
    (c.circleBoundaryHomeomorph.symm ⟨x,hx⟩) (c.circleBoundaryHomeomorph.symm ⟨y,hy⟩)
  change v (c.circleBoundaryHomeomorph (c.circleBoundaryHomeomorph.symm ⟨x,hx⟩)) =
    v (c.circleBoundaryHomeomorph (c.circleBoundaryHomeomorph.symm ⟨y,hy⟩)) at heq
  simp only [Homeomorph.apply_symm_apply] at heq
  linarith
end StrictHotSpots.Conformal.ClosedDiskChart
end
end ClosedTraceNonzero



end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualNoncritical

noncomputable section
open Set MeasureTheory Filter Metric Function Module
open scoped ENNReal NNReal Topology InnerProductSpace
namespace StrictHotSpots.Conformal.ClosedDiskChart
open PlaneGreen DiskH10 HilbertMultipliers
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)




theorem noncritical_at_disk (hΩ : AdmissibleDomain Ω)
    {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u) (hne : ∃ x ∈ Ω, u x ≠ 0)
    (p : disk) : gradient u (c.F p) ≠ 0 := by
  intro hz
  let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
  have hμ := firstPositiveNeumannValue_pos_of_eigenfunction hΩ hu hne
  obtain ⟨d,hd,hd1,hsub⟩ := c.subcritical hΩ.2.2.1 hΩ.1 hμ
  obtain ⟨H,hN,hI,hC,hS,b,B,hinj,hb,hid⟩ := full_boundary_hilbert_embedding
    c.densityBound_ne_top (c.density_bound hμ.le) hd.le hd1 hsub p
  let := hN
  let := hI
  let := hC
  let := hS
  obtain ⟨I,e,_he⟩ := exists_hilbertBasis ℝ H
  let : Countable I := orthonormal_countable e.orthonormal
  have hnull := c.coordinate_null_trace hΩ hu hne p hz e hb hid
  have hY : ContinuousOn (closedGradient Ω u) (closure Ω) :=
    closedGradient_continuous hΩ.2.1 hΩ.2.2.2.2 hu.1
  have he : EqOn (gradient u) (closedGradient Ω u) Ω := fun _ hx => (closedGradient_eq hΩ.2.1 hx).symm
  let J : closedEigenSpace Ω hΩ.2.1 hΩ.2.2.1 :=
    ⟨closedEigenJet Ω u (closedGradient Ω u),u,closedGradient Ω u,hu.interior,hu.1.continuousOn,hY,he,rfl⟩
  let T := closedTraceSpace c hΩ
  let g : T := ⟨closedGradientTrace c hΩ J,J,rfl⟩
  have hgv (s : Circle) : g.val s = closedGradient Ω u (c.F (circleBoundary s)) := rfl
  obtain ⟨hf,hr⟩ := closedTraceSpace_rank c hΩ
  let : Module.Finite ℝ T := hf
  have hmem (i : I) : (fun s => inner ℝ (e i) (b (circleBoundary s)) • g.val s) ∈ T := by
    obtain ⟨v,Y,hv,hvc,hY,hvY,ht⟩ := hnull i
    let K : closedEigenSpace Ω hΩ.2.1 hΩ.2.2.1 :=
      ⟨closedEigenJet Ω v Y,v,Y,hv,hvc,hY,hvY,rfl⟩
    refine ⟨K,?_⟩
    funext s
    exact ht (circleBoundary s)
  have h0 := multiplier_contradiction e (hb.continuous.comp circleBoundary.continuous)
    (hinj.comp circleBoundary.injective) T hr (fun U hU hne => closedTraceSpace_local_rank c hΩ hU hne)
    g ((c.closedGradient_trace_continuous hΩ hu).comp circleBoundary.continuous) hmem
  apply c.boundary_gradient_not_zero hΩ hu.interior hu.1.continuousOn hY he hne
  intro x hx
  have hh := congrArg (fun f : T => f.val (c.circleBoundaryHomeomorph.symm ⟨x,hx⟩)) h0
  change closedGradient Ω u
    (c.circleBoundaryHomeomorph (c.circleBoundaryHomeomorph.symm ⟨x,hx⟩)) = 0 at hh
  simpa only [Homeomorph.apply_symm_apply] using hh

include c


theorem noncritical_oai (hΩ : AdmissibleDomain Ω)
    {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u) (hne : ∃ x ∈ Ω, u x ≠ 0) :
    ∀ x ∈ Ω, gradient u x ≠ 0 := by
  intro x hx
  have hp : c.G x ∈ disk := by
    have hh := c.diskMap.map_target hx
    change c.diskMap.symm x ∈ disk at hh
    rwa [c.diskMap_inverse_agrees hx] at hh
  have hh := c.noncritical_at_disk hΩ hu hne ⟨c.G x,hp⟩
  simpa only [c.right_inverse x (subset_closure hx)] using hh
end StrictHotSpots.Conformal.ClosedDiskChart

end
end ActualNoncritical


end OAI
end

theorem solution : type_of% @OAI.StrictHotSpots.Conformal.ClosedDiskChart.noncritical_oai := @OAI.StrictHotSpots.Conformal.ClosedDiskChart.noncritical_oai
