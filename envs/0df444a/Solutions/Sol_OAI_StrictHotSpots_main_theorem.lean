-- Prove2me | solution 1 for OAI.StrictHotSpots.main_theorem
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T05:18:48.097164+00:00
-- url     : https://prove2.me/submissions/d9b7a840-e12b-423d-82be-63367fc3db2a

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho003
import Theorems.Thm_OAI_StrictHotSpots_Conformal_ClosedDiskChart_noncritical

section
-- module Solutions.OAIQ3_Hot.HotSpots_Variational
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section MainVariationalCombinedLayer
open Set MeasureTheory Filter
open scoped Topology InnerProductSpace ContDiff
namespace StrictHotSpots






lemma strict_boundary_extrema_of_noncritical {Ω : Set Plane} {u : Plane → ℝ}
    (hne : Ω.Nonempty) (hopen : IsOpen Ω) (hbound : Bornology.IsBounded Ω)
    (hu : ContinuousOn u (closure Ω))
    (hnocrit : ∀ x ∈ Ω, gradient u x ≠ 0) : MainConclusion Ω u := by
  have hnotmin (x : Plane) (hx : x ∈ Ω) : ¬IsMinOn u (closure Ω) x := by
    intro hm
    have hl := hm.isLocalMin (Filter.mem_of_superset (hopen.mem_nhds hx) subset_closure)
    apply hnocrit x hx
    simp [gradient, hl.fderiv_eq_zero]
  have hnotmax (x : Plane) (hx : x ∈ Ω) : ¬IsMaxOn u (closure Ω) x := by
    intro hm
    have hl := hm.isLocalMax (Filter.mem_of_superset (hopen.mem_nhds hx) subset_closure)
    apply hnocrit x hx
    simp [gradient, hl.fderiv_eq_zero]
  obtain ⟨a, ha, hmin⟩ := hbound.isCompact_closure.exists_isMinOn hne.closure hu
  obtain ⟨b, hb, hmax⟩ := hbound.isCompact_closure.exists_isMaxOn hne.closure hu
  have hfa : a ∈ frontier Ω := by
    rw [frontier, hopen.interior_eq]
    exact ⟨ha, fun hx => hnotmin a hx hmin⟩
  have hfb : b ∈ frontier Ω := by
    rw [frontier, hopen.interior_eq]
    exact ⟨hb, fun hx => hnotmax b hx hmax⟩
  have hleast : IsLeast (u '' frontier Ω) (u a) := by
    refine ⟨⟨a, hfa, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hmin (frontier_subset_closure hy)
  have hgreatest : IsGreatest (u '' frontier Ω) (u b) := by
    refine ⟨⟨b, hfb, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hmax (frontier_subset_closure hy)
  refine ⟨hnocrit, ?_⟩
  intro x hx
  rw [hleast.csInf_eq, hgreatest.csSup_eq]
  constructor
  · by_contra hlt
    apply hnotmin x hx
    intro y hy
    exact (le_of_not_gt hlt).trans (hmin hy)
  · by_contra hlt
    apply hnotmax x hx
    intro y hy
    exact (hmax hy).trans (le_of_not_gt hlt)


end StrictHotSpots
end MainVariationalCombinedLayer


end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Conformal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ConformalCoordinates


noncomputable section
open Set MeasureTheory _root_.Complex ComplexConjugate InnerProductSpace
open scoped InnerProductSpace Topology ContDiff
namespace StrictHotSpots.Conformal

lemma planeChart_source (e : OpenPartialHomeomorph ℂ ℂ) :
    (planeChart e).source = coordinate.symm ⁻¹' e.source := by
  ext x
  simp [planeChart]

lemma planeChart_target (e : OpenPartialHomeomorph ℂ ℂ) :
    (planeChart e).target = coordinate.symm ⁻¹' e.target := by
  ext x
  simp [planeChart]

end StrictHotSpots.Conformal
end
end ConformalCoordinates


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Riemann
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section RiemannBiholomorphic





noncomputable section
open Set Filter Metric _root_.Complex Function
open scoped Topology
namespace Complex
open scoped _root_.Complex












/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

The following conformal embedding declarations are adapted from Mathlib.Analysis.Complex.RiemannMapping.
Source: https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Analysis/Complex/RiemannMapping.lean

This code has been modified.
-/

theorem exists_injective_not_dense_image_deriv_ne_zero {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) (hU : U ≠ univ) :
    ∃ f : ℂ → ℂ, Injective f ∧ ¬Dense (f '' U) ∧ ∀ z ∈ U, deriv f z ≠ 0 := by

  wlog hU₀ : 0 ∉ U
  · rw [ne_univ_iff_exists_notMem] at hU
    rcases hU with ⟨a, ha⟩
    specialize this (hUo.vadd (-a)) (by simpa) (by simp [hU])
      (by simpa [mem_vadd_set_iff_neg_vadd_mem])
    rcases this with ⟨f, hf_inj, hf_dense, hdf⟩
    refine ⟨f ∘ (-a + ·), hf_inj.comp (add_right_injective (-a)), ?_, fun z hz ↦ ?_⟩
    · simpa only [← image_vadd, Set.image_image] using! hf_dense
    · simpa [Function.comp_def, deriv_comp_const_add] using hdf (-a + z) (mapsTo_image _ _ hz)


  rcases _root_.Complex.exists_continuousOn_pow_eq hUc hUo continuousOn_id (by rwa [image_id]) two_ne_zero
    with ⟨f, hfc, hf_inv⟩
  replace hf_inv : LeftInverse (· ^ 2) f := hf_inv

  have hf₀ : ∀ z ∈ U, f z ≠ 0 := by
    intro z hz hfz
    simpa [hfz, (ne_of_mem_of_not_mem hz hU₀).symm] using hf_inv z


  have hdf : ∀ z ∈ U, HasStrictDerivAt f (2 * f z)⁻¹ z := by
    intro z hz
    apply HasStrictDerivAt.of_local_left_inverse
    · exact hfc.continuousAt <| hUo.mem_nhds hz
    · simpa using hasStrictDerivAt_pow 2 (f z)
    · simpa using hf₀ z hz
    · exact .of_forall hf_inv

  refine ⟨f, hf_inv.injective, ?_, fun z hz ↦ ?_⟩
  ·
    simp only [Dense, not_forall, mem_closure_iff_frequently, not_frequently]
    rcases hUc.nonempty with ⟨x, hx⟩

    use -f x


    have : f '' U ∈ 𝓝 (f x) := by
      rw [← (hdf x hx).map_nhds_eq (by simpa using hf₀ x hx)]
      exact Filter.image_mem_map <| hUo.mem_nhds hx

    rw [nhds_neg, eventually_neg]



    filter_upwards [this]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    obtain rfl : a = b := by
      rw [← hf_inv b, hab]
      simp [hf_inv a]
    refine hf₀ a ha ?_
    linear_combination hab / 2
  · simpa [(hdf z hz).hasDerivAt.deriv] using hf₀ z hz













lemma exists_mapsTo_unitBall_injOn_deriv_ne_zero {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) (hU : U ≠ univ) :
    ∃ f : ℂ → ℂ, MapsTo f U (ball 0 1) ∧ InjOn f U ∧ ∀ z ∈ U, deriv f z ≠ 0 := by


  rcases exists_injective_not_dense_image_deriv_ne_zero hUo hUc hU with ⟨f, hf_inj, hfd, hdf⟩

  obtain ⟨x, ε, hε₀, hε⟩ : ∃ (x : ℂ) (ε : ℝ), 0 < ε ∧ ∀ a ∈ U, ε < dist (f a) x := by
    simpa [Dense, mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall] using hfd
  have hfx : ∀ z ∈ U, f z ≠ x := fun z hz ↦ by simpa using hε₀.trans (hε z hz)

  use fun z ↦ ε / (f z - x)
  refine ⟨?mapsTo, ?injOn, ?deriv⟩
  case mapsTo =>
    intro z hz
    rw [mem_ball_zero_iff, norm_div, _root_.Complex.norm_real, Real.norm_of_nonneg hε₀.le, div_lt_one₀]
    · simpa [dist_eq_norm] using hε z hz
    · simpa [sub_eq_zero] using hfx z hz
  case injOn =>
    intro z hz w hw heq
    simpa [div_eq_mul_inv, hε₀.ne', hf_inj.eq_iff] using heq
  case deriv =>
    intro z hz
    have hdz : DifferentiableAt ℂ f z := differentiableAt_of_deriv_ne_zero (hdf z hz)
    rw [(hasDerivAt_const _ _).fun_div (hdz.hasDerivAt.sub_const _) _ |>.deriv] <;>
      simp [*, ne_of_gt, sub_eq_zero]

end Complex

namespace StrictHotSpots.Riemann

variable {U : Set ℂ}


lemma extend_eq (f : C(U,ℂ)) {z : ℂ} (hz : z ∈ U) : extend f z=f ⟨z,hz⟩ := by
  simp [extend,hz]

lemma tendsto_extend {ι : Type*} {l : Filter ι} [LocallyCompactSpace U]
    {F : ι → C(U,ℂ)} {f : C(U,ℂ)} (h : Tendsto F l (𝓝 f)) :
    TendstoLocallyUniformlyOn (fun i => extend (F i)) (extend f) l U := by
  rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
  simpa only [Function.comp_def,extend_coe] using
    (ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp h)

lemma holomorphicBall_isClosed (ho : IsOpen U) : IsClosed (holomorphicBall U) := by
  let : LocallyCompactSpace U := ho.locallyCompactSpace
  rw [isClosed_iff_forall_filter]
  intro f l hl hF hf
  let := hl
  have hF : ∀ᶠ g in l, g ∈ holomorphicBall U := le_principal_iff.mp hF
  refine ⟨(tendsto_extend (show Tendsto id l (𝓝 f) from hf)).differentiableOn (hF.mono fun _ hi => hi.1) ho,?_⟩
  intro z
  have hh : Tendsto (fun i => ‖i z‖) l (𝓝 ‖f z‖) :=
    by simpa only [extend_coe,id] using
      ((tendsto_extend (show Tendsto id l (𝓝 f) from hf)).tendsto_at z.property).norm
  exact le_of_tendsto hh (hF.mono fun _ hi => hi.2 z)

lemma holomorphicBall_dist_bound (_ho : IsOpen U) {f : C(U,ℂ)}
    (hf : f ∈ holomorphicBall U) {x : U} {r : ℝ} (_hr : 0 < r)
    (hball : ball (x:ℂ) r ⊆ U) {y : U} (hy : dist (y:ℂ) x < r) :
    dist (f x) (f y) ≤ (2/r)*dist (x:ℂ) y := by
  have hm : MapsTo (extend f) (ball (x:ℂ) r) (closedBall (extend f x) 2) := by
    intro z hz
    have hzu := hball hz
    rw [mem_closedBall,dist_eq_norm]
    calc
      ‖extend f z-extend f x‖ ≤ ‖extend f z‖+‖extend f x‖ := norm_sub_le _ _
      _ ≤ 1+1 := add_le_add (by simpa only [extend_eq f hzu] using hf.2 ⟨z,hzu⟩)
        (by simpa only [extend_coe,id] using hf.2 x)
      _ = 2 := by norm_num
  have hh := Complex.dist_le_div_mul_dist_of_mapsTo_ball (hf.1.mono hball) hm
    (show (y:ℂ) ∈ ball (x:ℂ) r from hy)
  simpa only [extend_coe,dist_comm] using hh

lemma holomorphicBall_equicontinuous (ho : IsOpen U) :
    Equicontinuous (fun f : holomorphicBall U => (f.val : U → ℂ)) := by
  intro x
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨r,hr,hru⟩ := Metric.isOpen_iff.mp ho (x:ℂ) x.property
  refine ⟨min r (ε*r/2),lt_min hr (by positivity),?_⟩
  intro y hy f
  have hyr : dist (y:ℂ) x < r := lt_of_lt_of_le hy (min_le_left _ _)
  have hye : dist (y:ℂ) x < ε*r/2 := lt_of_lt_of_le hy (min_le_right _ _)
  apply (holomorphicBall_dist_bound ho f.property hr hru hyr).trans_lt
  rw [dist_comm]
  exact (mul_lt_mul_of_pos_left hye (div_pos (by norm_num) hr)).trans_eq (by field_simp)

lemma holomorphicBall_isCompact (ho : IsOpen U) : IsCompact (holomorphicBall U) := by
  let : LocallyCompactSpace U := ho.locallyCompactSpace
  have : T2Space (UniformOnFun U ℂ {K : Set U | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (by
      rw [sUnion_eq_univ_iff]
      intro x
      exact ⟨{x},isCompact_singleton,mem_singleton x⟩)
  have hc : IsCompact (closure (holomorphicBall U)) :=
    ArzelaAscoli.isCompact_closure_of_isClosedEmbedding (fun _ h => h)
      ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
      (fun K _ => (holomorphicBall_equicontinuous ho).equicontinuousOn K)
      (fun K _ x _ => ⟨closedBall (0:ℂ) 1,isCompact_closedBall _ _,fun f hf => by
        simpa only [mem_closedBall,dist_zero_right] using hf.2 x⟩)
  simpa only [(holomorphicBall_isClosed ho).closure_eq] using hc

lemma deriv_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] (ho : IsOpen U)
    {F : ι → C(U,ℂ)} {f : C(U,ℂ)} (hF : ∀ᶠ i in l, F i ∈ holomorphicBall U)
    (hf : Tendsto F l (𝓝 f)) (z : U) :
    Tendsto (fun i => deriv (extend (F i)) z) l (𝓝 (deriv (extend f) z)) := by
  let : LocallyCompactSpace U := ho.locallyCompactSpace
  exact ((tendsto_extend hf).deriv (hF.mono fun _ hi => hi.1) ho).tendsto_at z.property

end StrictHotSpots.Riemann




noncomputable section
open Set Filter Metric Complex Function
open scoped Topology
namespace StrictHotSpots.Riemann

lemma hurwitz_locally_zero {ι : Type*} {l : Filter ι} [l.NeBot]
    {U : Set ℂ} (ho : IsOpen U) {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hconv : TendstoLocallyUniformlyOn F f l U)
    (hF : ∀ᶠ i in l, DifferentiableOn ℂ (F i) U ∧ ∀ z ∈ U, F i z ≠ 0)
    {z : ℂ} (hz : z ∈ U) (hfz : f z = 0) : ∀ᶠ w in 𝓝 z, f w = 0 := by
  have hfd := hconv.differentiableOn (hF.mono fun _ hi => hi.1) ho
  rcases (hfd.analyticOnNhd ho z hz).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact h
  obtain ⟨R,hR,hRU⟩ := Metric.isOpen_iff.mp ho z hz
  obtain ⟨δ,hδ,hδf⟩ := Metric.mem_nhdsWithin_iff.mp h
  let r := min R δ / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : r < R := by dsimp [r]; linarith [min_le_left R δ]
  have hrδ : r < δ := by dsimp [r]; linarith [min_le_right R δ]
  have hcl : closedBall z r ⊆ U := (closedBall_subset_ball hrR).trans hRU
  have hs : sphere z r ⊆ U := sphere_subset_closedBall.trans hcl
  have hfs : ∀ w ∈ sphere z r, f w ≠ 0 := by
    intro w hw
    apply hδf
    refine ⟨?_,?_⟩
    · rw [mem_ball,mem_sphere.mp hw]; exact hrδ
    · simpa only [mem_compl_iff,mem_singleton_iff] using (ne_of_mem_sphere hw hr.ne')
  obtain ⟨v,hv,hvm⟩ := (isCompact_sphere z r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr.le) (hfd.continuousOn.mono hs).norm
  let m := ‖f v‖
  have hm : 0 < m := norm_pos_iff.mpr (hfs v hv)
  have he : ∀ᶠ i in l, ∀ w ∈ sphere z r, dist (f w) (F i w) < m/2 :=
    Metric.tendstoUniformlyOn_iff.mp
      ((tendstoLocallyUniformlyOn_iff_forall_isCompact ho).mp hconv
        _ hs (isCompact_sphere z r)) _ (by positivity)
  have hbound : ∀ᶠ i in l, 1 ≤ (2/m)*‖F i z‖ := by
    filter_upwards [hF,he] with i hi hei
    have hiinv := hi.1.inv hi.2
    have hnorm : ‖(F i z)⁻¹‖ ≤ 2/m :=
      Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball)
        (hiinv.diffContOnCl_ball hcl) (fun w hw => by
          rw [frontier_ball z hr.ne'] at hw
          have hmin : m ≤ ‖f w‖ := hvm hw
          have hd := norm_sub_norm_le (f w) (F i w)
          have hew := hei w hw
          rw [dist_eq_norm] at hew
          have hlow : m/2 ≤ ‖F i w‖ := by linarith
          rw [Pi.inv_apply,norm_inv,inv_eq_one_div]
          calc
            1/‖F i w‖ ≤ 1/(m/2) := one_div_le_one_div_of_le (by positivity) hlow
            _ = 2/m := by field_simp)
        (by rw [closure_ball z hr.ne']; exact mem_closedBall_self hr.le)
    rw [norm_inv,inv_eq_one_div,div_le_iff₀ (norm_pos_iff.mpr (hi.2 z hz))] at hnorm
    exact hnorm
  have ht : Tendsto (fun i => (2/m)*‖F i z‖) l (𝓝 0) := by
    simpa only [hfz,norm_zero,mul_zero] using (hconv.tendsto_at hz).norm.const_mul (2/m)
  have hcontra : (1:ℝ) ≤ 0 := ge_of_tendsto ht hbound
  norm_num at hcontra

lemma hurwitz_injective {ι : Type*} {l : Filter ι} [l.NeBot]
    {U : Set ℂ} (ho : IsOpen U) (hc : IsPreconnected U)
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hconv : TendstoLocallyUniformlyOn F f l U)
    (hF : ∀ᶠ i in l, DifferentiableOn ℂ (F i) U ∧ InjOn (F i) U)
    (hf : ∃ a ∈ U, ∃ b ∈ U, f a ≠ f b) : InjOn f U := by
  intro x hx y hy hxy
  by_contra hne
  have hfd := hconv.differentiableOn (hF.mono fun _ hi => hi.1) ho
  have hcst : TendstoLocallyUniformlyOn (fun i (_ : ℂ) => F i x) (fun _ => f x) l U :=
    (hconv.tendsto_at hx).tendstoUniformlyOn_const U |>.tendstoLocallyUniformlyOn
  have hsub : TendstoLocallyUniformlyOn (fun i z => F i z-F i x)
      (fun z => f z-f x) l (U \ {x}) := (hconv.sub hcst).mono sdiff_subset
  have hloc : ∀ᶠ w in 𝓝 y, f w-f x=0 := hurwitz_locally_zero
      (ho.sdiff isClosed_singleton) hsub
      (hF.mono fun i hi => ⟨(hi.1.sub_const _).mono sdiff_subset,by
        intro z hz
        exact sub_ne_zero.mpr (fun hh => hz.2 (hi.2 hz.1 hx hh))⟩)
      ⟨hy,fun hyx => hne (Eq.symm (mem_singleton_iff.mp hyx))⟩ (sub_eq_zero.mpr hxy.symm)
  have he : EqOn (fun z => f z-f x) 0 U :=
    ((hfd.sub_const _).analyticOnNhd ho).eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hy hloc
  obtain ⟨a,ha,b,hb,hab⟩ := hf
  exact hab ((sub_eq_zero.mp (he ha)).trans (sub_eq_zero.mp (he hb)).symm)

end StrictHotSpots.Riemann

namespace StrictHotSpots.Riemann

lemma normalizedMaps_isClosed {U : Set ℂ} (ho : IsOpen U)
    (hc : IsPreconnected U) (a : U) : IsClosed (normalizedMaps a) := by
  let : LocallyCompactSpace U := ho.locallyCompactSpace
  rw [isClosed_iff_forall_filter]
  intro f l hl hF hf
  let := hl
  have hF : ∀ᶠ g in l, g ∈ normalizedMaps a := le_principal_iff.mp hF
  have ht : TendstoLocallyUniformlyOn (fun g => extend g) (extend f) l U := tendsto_extend hf
  have hfa : f a=0 := by
    apply isClosed_singleton.mem_of_tendsto (by simpa only [extend_coe] using ht.tendsto_at a.property)
    exact hF.mono fun _ hg => hg.2.1
  refine ⟨(holomorphicBall_isClosed ho).mem_of_tendsto hf (hF.mono fun _ hg => hg.1),hfa,?_⟩
  by_cases hfzero : f=0
  · exact Or.inr hfzero
  left
  obtain ⟨b,hb⟩ : ∃ b : U, f b≠0 := by
    by_contra hh
    simp only [not_exists,not_not] at hh
    exact hfzero (ContinuousMap.ext hh)
  have hFb : ∀ᶠ g in l, g b≠0 := by
    exact (show Tendsto (fun g : C(U,ℂ) => g b) l (𝓝 (f b)) from
      by simpa only [extend_coe] using ht.tendsto_at b.property).eventually
        (show ∀ᶠ z in 𝓝 (f b), z ≠ 0 from isOpen_compl_singleton.mem_nhds hb)
  have hin : InjOn (extend f) U := hurwitz_injective ho hc ht
    (by
      filter_upwards [hF,hFb] with g hg hgb
      refine ⟨hg.1.1,?_⟩
      have hgInj : Injective g := hg.2.2.resolve_right (by intro hg0; simp [hg0] at hgb)
      intro x hx y hy hxy
      exact congrArg Subtype.val (hgInj (by simpa only [extend_eq g hx,extend_eq g hy] using hxy)))
    ⟨b,b.property,a,a.property,by simpa only [extend_coe,hfa] using hb⟩
  intro x y hxy
  exact Subtype.ext (hin x.property y.property (by simpa only [extend_coe] using hxy))

lemma normalizedMaps_isCompact {U : Set ℂ} (ho : IsOpen U)
    (hc : IsPreconnected U) (a : U) : IsCompact (normalizedMaps a) :=
  (holomorphicBall_isCompact ho).of_isClosed_subset (normalizedMaps_isClosed ho hc a)
    (fun _ hf => hf.1)

lemma deriv_continuousOn {U : Set ℂ} (ho : IsOpen U) (a : U) :
    ContinuousOn (fun f : C(U,ℂ) => deriv (extend f) a) (holomorphicBall U) := by
  rw [continuousOn_iff_continuous_domRestrict,continuous_iff_continuousAt]
  intro f
  exact deriv_tendsto ho (Eventually.of_forall fun g : holomorphicBall U => g.property)
    continuous_subtype_val.continuousAt a

lemma exists_extremal {U : Set ℂ} (ho : IsOpen U) (hc : IsPreconnected U) (a : U)
    {g : C(U,ℂ)} (hg : g ∈ normalizedMaps a) (hgd : deriv (extend g) a ≠ 0) :
    ∃ f ∈ normalizedMaps a, 0 < ‖deriv (extend f) a‖ ∧
      ∀ h ∈ normalizedMaps a, ‖deriv (extend h) a‖ ≤ ‖deriv (extend f) a‖ := by
  obtain ⟨f,hf,hmax⟩ := (normalizedMaps_isCompact ho hc a).exists_isMaxOn ⟨g,hg⟩
    ((deriv_continuousOn ho a).mono (fun _ hh => hh.1)).norm
  exact ⟨f,hf,(norm_pos_iff.mpr hgd).trans_le (hmax hg),hmax⟩


lemma extend_eventuallyEq {U : Set ℂ} (ho : IsOpen U) (g : C(U,ℂ))
    {f : ℂ → ℂ} (hf : ∀ z : U, g z=f z) (a : U) :
    extend g =ᶠ[𝓝 (a:ℂ)] f := by
  filter_upwards [ho.mem_nhds a.property] with z hz
  rw [extend_eq g hz]
  exact hf ⟨z,hz⟩

lemma normalized_initial {U : Set ℂ} (ho : IsOpen U) (hs : IsSimplyConnected U)
    (hU : U ≠ univ) (a : U) :
    ∃ g ∈ normalizedMaps a, deriv (extend g) a ≠ 0 := by
  obtain ⟨f,hfmap,hfinj,hfderiv⟩ := Complex.exists_mapsTo_unitBall_injOn_deriv_ne_zero ho hs hU
  have hfd : DifferentiableOn ℂ f U := fun z hz =>
    (differentiableAt_of_deriv_ne_zero (hfderiv z hz)).differentiableWithinAt
  let g : C(U,ℂ) := ⟨fun z => (f z-f a)/2,
    hfd.continuousOn.domRestrict.sub continuous_const |>.div_const 2⟩
  have heq : ∀ z ∈ U, extend g z = (f z-f a)/2 := fun z hz => extend_eq g hz
  refine ⟨g,⟨⟨((hfd.sub_const _).div_const 2).congr heq,?_⟩,?_,Or.inl ?_⟩,?_⟩
  · intro z
    change ‖(f z-f a)/2‖ ≤ 1
    rw [norm_div,Complex.norm_ofNat,div_le_one₀ (by norm_num : (0:ℝ)<2)]
    exact (norm_sub_le _ _).trans (by
      have hz : ‖f z‖ < 1 := mem_ball_zero_iff.mp (hfmap z.property)
      have ha : ‖f a‖ < 1 := mem_ball_zero_iff.mp (hfmap a.property)
      linarith)
  · change (f a-f a)/2=0
    simp
  · intro x y hxy
    apply Subtype.ext
    apply hfinj x.property y.property
    change (f x-f a)/2=(f y-f a)/2 at hxy
    have h2 : f x-f a=f y-f a := (div_left_inj' (by norm_num : (2:ℂ)≠0)).mp hxy
    linear_combination h2
  · rw [(extend_eventuallyEq ho g (f := fun z => (f z-f a)/2) (fun _ => rfl) a).deriv_eq,deriv_div_const,
      deriv_sub_const]
    exact div_ne_zero (hfderiv a a.property) (by norm_num)

lemma exists_nonzero_extremal {U : Set ℂ} (ho : IsOpen U) (hs : IsSimplyConnected U)
    (hU : U ≠ univ) (a : U) :
    ∃ f ∈ normalizedMaps a, 0 < ‖deriv (extend f) a‖ ∧
      ∀ h ∈ normalizedMaps a, ‖deriv (extend h) a‖ ≤ ‖deriv (extend f) a‖ := by
  obtain ⟨g,hg,hgd⟩ := normalized_initial ho hs hU a
  have hc : IsPreconnected U := hs.isPathConnected.isConnected.isPreconnected
  exact exists_extremal ho hc a hg hgd

lemma normalized_norm_lt {U : Set ℂ} (ho : IsOpen U) (hc : IsPreconnected U)
    (a : U) {f : C(U,ℂ)} (hf : f ∈ normalizedMaps a) (z : U) : ‖f z‖ < 1 := by
  by_contra hle
  have heq : ‖f z‖=1 := le_antisymm (hf.1.2 z) (not_lt.mp hle)
  have hmax : IsMaxOn (norm ∘ extend f) U (z:ℂ) := by
    intro w hw
    change ‖extend f w‖ ≤ ‖extend f z‖
    rw [extend_eq f hw,extend_coe,heq]
    exact hf.1.2 ⟨w,hw⟩
  have hh := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hc ho hf.1.1 z.property hmax a.property
  simp only [extend_coe,Function.const_apply,hf.2.1] at hh
  rw [← hh,norm_zero] at heq
  norm_num at heq

end StrictHotSpots.Riemann




noncomputable section
open Set Filter Metric Complex Function
open scoped Topology ComplexConjugate
namespace StrictHotSpots.Riemann

lemma mobius_denom_ne {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    1-conj a*z ≠ 0 := by
  apply sub_ne_zero.mpr
  intro he
  have hh : ‖conj a*z‖ < 1 := by
    rw [norm_mul,norm_conj]
    nlinarith [norm_nonneg a,norm_nonneg z]
  rw [← he,norm_one] at hh
  exact lt_irrefl _ hh

lemma mobius_norm_identity (a z : ℂ) :
    ‖1-conj a*z‖^2-‖z-a‖^2=(1-‖a‖^2)*(1-‖z‖^2) := by
  simp only [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,sub_re,sub_im,
    one_re,one_im,mul_re,mul_im,conj_re,conj_im]
  ring

lemma norm_mobius_lt {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    ‖mobius a z‖ < 1 := by
  have hden : 0 < ‖1-conj a*z‖ := norm_pos_iff.mpr (mobius_denom_ne ha hz)
  rw [mobius,norm_div,div_lt_one₀ hden]
  have hpos : 0 < (1-‖a‖^2)*(1-‖z‖^2) := mul_pos
    (by nlinarith [norm_nonneg a]) (by nlinarith [norm_nonneg z])
  have hh := mobius_norm_identity a z
  nlinarith [norm_nonneg (z-a)]

lemma mobius_injOn {a : ℂ} (ha : ‖a‖ < 1) : InjOn (mobius a) (ball 0 1) := by
  intro x hx y hy he
  have hx' := mobius_denom_ne ha (mem_ball_zero_iff.mp hx)
  have hy' := mobius_denom_ne ha (mem_ball_zero_iff.mp hy)
  have haa := mobius_denom_ne ha ha
  have hcross := (div_eq_div_iff hx' hy').mp he
  have hmul : (x-y)*(1-conj a*a)=0 := by linear_combination hcross
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right haa)

lemma hasDerivAt_mobius {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    HasDerivAt (mobius a) ((1-conj a*a)/(1-conj a*z)^2) z := by
  have hh := ((hasDerivAt_id z).sub_const a).div
    ((hasDerivAt_const z 1).sub ((hasDerivAt_id z).const_mul (conj a))) (mobius_denom_ne ha hz)
  change HasDerivAt (fun w => (w-a)/(1-conj a*w))
    ((1*(1-conj a*z)-(z-a)*(0-conj a*1))/(1-conj a*z)^2) z at hh
  have he : 1*(1-conj a*z)-(z-a)*(0-conj a*1)=1-conj a*a := by ring
  rw [he] at hh
  exact hh

lemma hasDerivAt_mobius_zero {a : ℂ} (ha : ‖a‖ < 1) :
    HasDerivAt (mobius a) (1-conj a*a) 0 := by
  simpa using hasDerivAt_mobius ha (by simp : ‖(0:ℂ)‖<1)

lemma norm_mobius_self_deriv {a : ℂ} (ha : ‖a‖ < 1) :
    ‖(1-conj a*a)/(1-conj a*a)^2‖=1/(1-‖a‖^2) := by
  have hh : 0 < 1-‖a‖^2 := by nlinarith [norm_nonneg a]
  rw [← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
  norm_cast
  rw [norm_div,norm_pow,Real.norm_of_nonneg hh.le]
  field_simp

lemma norm_mobius_zero_deriv {a : ℂ} (ha : ‖a‖ < 1) :
    ‖1-conj a*a‖=1-‖a‖^2 := by
  rw [← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
  norm_cast
  exact Real.norm_of_nonneg (by nlinarith [norm_nonneg a])

lemma hasDerivAt_continuous_square_root {r h : ℂ → ℂ} {a d : ℂ}
    (hrc : ContinuousAt r a) (hr : r a ≠ 0) (he : ∀ z, r z^2=h z)
    (hh : HasDerivAt h d a) : HasDerivAt r ((2*r a)⁻¹*d) a := by
  have hq : HasStrictDerivAt (fun z : ℂ => z^2) (2*r a) (r a) := by
    simpa using hasStrictDerivAt_pow 2 (r a)
  have hqne : 2*r a ≠ 0 := mul_ne_zero (by norm_num) hr
  let k := hq.localInverse (fun z : ℂ => z^2) (2*r a) (r a) hqne
  have hk : HasDerivAt k (2*r a)⁻¹ (h a) := by
    rw [← he a]
    exact (hq.to_localInverse hqne).hasDerivAt
  have hke : (fun z => k (h z)) =ᶠ[𝓝 a] r := by
    have hev := hrc.eventually (hq.eventually_left_inverse hqne)
    filter_upwards [hev] with z hz
    simpa only [he] using hz
  exact (hk.comp a hh).congr_of_eventuallyEq hke.symm


lemma root_improvement_inequality {r d : ℝ} (hr : 0 < r) (hr1 : r < 1) (hd : 0 < d) :
    d < (1/(1-r^2)) * ((2*r)⁻¹*((1-(r^2)^2)*d)) := by
  have hp : 0 < 1-r^2 := by nlinarith
  have he : (1/(1-r^2)) * ((2*r)⁻¹*((1-(r^2)^2)*d)) =
      (1+r^2)/(2*r)*d := by
    field_simp
    ring
  rw [he]
  have hh : 1 < (1+r^2)/(2*r) := (lt_div_iff₀ (by positivity)).mpr (by nlinarith [sq_pos_of_pos (sub_pos.mpr hr1)])
  simpa using mul_lt_mul_of_pos_right hh hd




lemma exists_root_improvement {U : Set ℂ} (ho : IsOpen U) (hs : IsSimplyConnected U)
    {a : ℂ} (ha : a ∈ U) {f : ℂ → ℂ} (hfd : DifferentiableOn ℂ f U)
    (hfi : InjOn f U) (hfm : ∀ z ∈ U, ‖f z‖ < 1) (hfa : f a = 0)
    (hdf : 0 < ‖deriv f a‖) {c : ℂ} (hc : ‖c‖ < 1) (hcf : c ∉ f '' U) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ InjOn g U ∧
      (∀ z ∈ U, ‖g z‖ < 1) ∧ g a=0 ∧ ‖deriv f a‖ < ‖deriv g a‖ := by
  have hdc (z : ℂ) (hz : z ∈ U) : HasDerivAt (fun w => mobius c (f w))
      (((1-conj c*c)/(1-conj c*f z)^2)*deriv f z) z :=
    (hasDerivAt_mobius hc (hfm z hz)).comp z ((hfd z hz).differentiableAt (ho.mem_nhds hz)).hasDerivAt
  have hcn (z : ℂ) (hz : z ∈ U) : mobius c (f z) ≠ 0 := by
    rw [mobius,div_ne_zero_iff]
    exact ⟨sub_ne_zero.mpr (by intro he; exact hcf ⟨z,hz,he⟩),mobius_denom_ne hc (hfm z hz)⟩
  obtain ⟨r,hrc,hreq⟩ := Complex.exists_continuousOn_pow_eq hs ho
    (show ContinuousOn (fun z => mobius c (f z)) U from fun z hz => (hdc z hz).continuousAt.continuousWithinAt)
    (by rintro ⟨z,hz,he⟩; exact hcn z hz he) two_ne_zero
  have hrn (z : ℂ) (hz : z ∈ U) : r z ≠ 0 := by
    intro he
    have hh := hreq z
    rw [he,zero_pow two_ne_zero] at hh
    exact hcn z hz hh.symm
  have hrm (z : ℂ) (hz : z ∈ U) : ‖r z‖ < 1 := by
    have hh := congrArg norm (hreq z)
    rw [norm_pow] at hh
    have hlt := norm_mobius_lt hc (hfm z hz)
    nlinarith [norm_nonneg (r z)]
  have hrd (z : ℂ) (hz : z ∈ U) : HasDerivAt r
      ((2*r z)⁻¹ * (((1-conj c*c)/(1-conj c*f z)^2)*deriv f z)) z :=
    hasDerivAt_continuous_square_root (hrc.continuousAt (ho.mem_nhds hz)) (hrn z hz) hreq (hdc z hz)
  have hri : InjOn r U := by
    intro x hx y hy he
    apply hfi hx hy
    apply mobius_injOn hc (mem_ball_zero_iff.mpr (hfm x hx)) (mem_ball_zero_iff.mpr (hfm y hy))
    rw [← hreq x,← hreq y,he]
  let g : ℂ → ℂ := fun z => mobius (r a) (r z)
  have hgd (z : ℂ) (hz : z ∈ U) : HasDerivAt g
      (((1-conj (r a)*r a)/(1-conj (r a)*r z)^2)*
        ((2*r z)⁻¹ * (((1-conj c*c)/(1-conj c*f z)^2)*deriv f z))) z :=
    (hasDerivAt_mobius (hrm a ha) (hrm z hz)).comp z (hrd z hz)
  refine ⟨g,(fun z hz => (hgd z hz).differentiableAt.differentiableWithinAt),?_,?_,?_,?_⟩
  · intro x hx y hy he
    exact hri hx hy (mobius_injOn (hrm a ha) (mem_ball_zero_iff.mpr (hrm x hx))
      (mem_ball_zero_iff.mpr (hrm y hy)) he)
  · intro z hz
    exact norm_mobius_lt (hrm a ha) (hrm z hz)
  · exact mobius_self _
  · have hnorm : ‖c‖=‖r a‖^2 := by
      have hh := congrArg norm (hreq a)
      simpa only [hfa,mobius_zero,norm_pow,norm_neg] using hh.symm
    rw [(hgd a ha).deriv,norm_mul,norm_mobius_self_deriv (hrm a ha),norm_mul,
      norm_inv,norm_mul,Complex.norm_ofNat,norm_mul,hfa]
    simp only [mul_zero,sub_zero,one_pow,div_one]
    rw [norm_mobius_zero_deriv hc,hnorm]
    exact root_improvement_inequality (norm_pos_iff.mpr (hrn a ha)) (hrm a ha) hdf

end StrictHotSpots.Riemann

namespace StrictHotSpots.Riemann


lemma exists_normalized_bijective {U : Set ℂ} (ho : IsOpen U) (hs : IsSimplyConnected U)
    (hU : U ≠ univ) (a : U) :
    ∃ f : ℂ → ℂ, f a=0 ∧ BijOn f U (ball 0 1) ∧ DifferentiableOn ℂ f U ∧
      0 < ‖deriv f a‖ := by
  obtain ⟨f,hf,hd,hmax⟩ := exists_nonzero_extremal ho hs hU a
  have hfinj : Injective f := hf.2.2.resolve_right (by
    intro he
    subst f
    have hezero : extend (0:C(U,ℂ))=0 := by ext z; simp [extend]
    rw [hezero] at hd
    simp at hd)
  have hfi : InjOn (extend f) U := by
    intro x hx y hy he
    exact congrArg Subtype.val (hfinj (by simpa only [extend_eq f hx,extend_eq f hy] using he))
  have hfm : ∀ z ∈ U, ‖extend f z‖ < 1 := by
    intro z hz
    rw [extend_eq f hz]
    exact normalized_norm_lt ho hs.isPathConnected.isConnected.isPreconnected a hf ⟨z,hz⟩
  have hfa : extend f a=0 := by simpa only [extend_coe] using hf.2.1
  refine ⟨extend f,hfa,⟨(fun z hz => mem_ball_zero_iff.mpr (hfm z hz)),hfi,?_⟩,hf.1.1,hd⟩
  intro c hc
  by_contra hcf
  obtain ⟨g,hgd,hgi,hgm,hga,hbetter⟩ := exists_root_improvement ho hs a.property hf.1.1 hfi hfm hfa hd
    (mem_ball_zero_iff.mp hc) hcf
  let G : C(U,ℂ) := ⟨U.domRestrict g,hgd.continuousOn.domRestrict⟩
  have hG : G ∈ normalizedMaps a := by
    refine ⟨⟨hgd.congr (fun z hz => extend_eq G hz),?_⟩,hga,Or.inl ?_⟩
    · intro z
      exact (hgm z z.property).le
    · intro x y he
      exact Subtype.ext (hgi x.property y.property he)
  have hh := hmax G hG
  rw [(extend_eventuallyEq ho G (f:=g) (fun _ => rfl) a).deriv_eq] at hh
  exact (not_lt_of_ge hh) hbetter

end StrictHotSpots.Riemann





noncomputable section
open Set Filter Metric Complex Function
open scoped Topology
namespace StrictHotSpots.Riemann

lemma analytic_inverse_openPartialHomeomorph (e : OpenPartialHomeomorph ℂ ℂ)
    (hc : IsPreconnected e.source) (hd : DifferentiableOn ℂ e e.source)
    {a : ℂ} (ha : a ∈ e.source) (hda : deriv e a ≠ 0) :
    DifferentiableOn ℂ e.symm e.target ∧ ∀ x ∈ e.source, deriv e x ≠ 0 := by
  have han := hd.analyticOnNhd e.open_source
  have hinv (x : ℂ) (hx : x ∈ e.source) : AnalyticAt ℂ e.symm (e x) := by
    have hdn : ∀ᶠ z in 𝓝[≠] x, deriv e z ≠ 0 := by
      rcases (han.deriv x hx).eventually_eq_zero_or_eventually_ne_zero with he | he
      · have hzero := han.deriv.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hc hx he
        exact (hda (hzero ha)).elim
      · exact he
    have ht : Tendsto e.symm (𝓝[≠] e x) (𝓝[≠] x) := by
      have ht0 : Tendsto e.symm (𝓝[≠] e x) (𝓝[≠] e.symm (e x)) :=
        tendsto_nhdsWithin_iff.mpr ⟨(e.continuousAt_symm (e.map_source hx)).tendsto.mono_left nhdsWithin_le_nhds,
          e.symm.eventually_ne_nhdsWithin (e.map_source hx)⟩
      simpa only [e.left_inv hx] using ht0
    apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      ?_ (e.continuousAt_symm (e.map_source hx))
    filter_upwards [ht.eventually hdn,eventually_nhdsWithin_of_eventually_nhds
      (e.open_target.mem_nhds (e.map_source hx))] with y hdy hy
    exact (e.hasDerivAt_symm hy hdy
      ((hd (e.symm y) (e.map_target hy)).differentiableAt
        (e.open_source.mem_nhds (e.map_target hy))).hasDerivAt).differentiableAt
  refine ⟨?_,?_⟩
  · intro y hy
    have hh := hinv (e.symm y) (e.map_target hy)
    rw [e.right_inv hy] at hh
    exact hh.differentiableAt.differentiableWithinAt
  · intro x hx
    have hcomp := (hinv x hx).differentiableAt.hasDerivAt.comp x
      ((hd x hx).differentiableAt (e.open_source.mem_nhds hx)).hasDerivAt
    have heq : deriv e.symm (e x) * deriv e x = 1 :=
      hcomp.unique ((hasDerivAt_id x).congr_of_eventuallyEq (e.eventually_left_inverse hx))
    intro he
    rw [he,mul_zero] at heq
    exact zero_ne_one heq

lemma exists_biholomorphic_inverse {U V : Set ℂ} (ho : IsOpen U)
    (hc : IsPreconnected U) {f : ℂ → ℂ} (hfd : DifferentiableOn ℂ f U)
    (hfb : BijOn f U V) {a : ℂ} (ha : a ∈ U) (hda : deriv f a ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, (e : ℂ → ℂ)=f ∧ e.source=U ∧ e.target=V ∧
      DifferentiableOn ℂ e.symm V ∧ (∀ x ∈ U, deriv f x ≠ 0) := by
  have hop : ∀ s ⊆ U, IsOpen s → IsOpen (f '' s) := by
    rcases (hfd.analyticOnNhd ho).is_constant_or_isOpen hc with h | h
    · obtain ⟨c,he⟩ := h
      have hg : f =ᶠ[𝓝 a] fun _ => c := by
        filter_upwards [ho.mem_nhds ha] with z hz
        exact he z hz
      exact (hda (by rw [hg.deriv_eq,deriv_const])).elim
    · exact h
  have hrestrict : IsOpenMap (U.domRestrict f) := by
    intro s hs
    have hsub : Subtype.val '' s ⊆ U := by rintro _ ⟨x,_,rfl⟩; exact x.property
    change IsOpen ((fun x : U => f x) '' s)
    simpa only [image_image,comp_def] using hop (Subtype.val '' s) hsub (ho.isOpenMap_subtype_val s hs)
  let e := OpenPartialHomeomorph.ofContinuousOpenRestrict (hfb.toPartialEquiv f U V)
    hfd.continuousOn hrestrict ho
  have he : (e : ℂ → ℂ)=f := rfl
  have hes : e.source=U := rfl
  have het : e.target=V := rfl
  have hh := analytic_inverse_openPartialHomeomorph e hc hfd ha hda
  exact ⟨e,he,hes,het,hh.1,hh.2⟩

end StrictHotSpots.Riemann


namespace StrictHotSpots.Riemann



theorem exists_disk_biholomorphism {U : Set ℂ} (ho : IsOpen U)
    (hs : IsSimplyConnected U) (hne : U.Nonempty) (hU : U ≠ univ) :
    ∃ Φ : OpenPartialHomeomorph ℂ ℂ, Φ.source = ball 0 1 ∧ Φ.target = U ∧
      DifferentiableOn ℂ Φ (ball 0 1) ∧ DifferentiableOn ℂ Φ.symm U ∧
      (∀ z ∈ ball (0:ℂ) 1, deriv Φ z ≠ 0) ∧
      (∀ w ∈ U, deriv Φ.symm w ≠ 0) := by
  obtain ⟨a,ha⟩ := hne
  obtain ⟨f,_,hfb,hfd,hda⟩ := exists_normalized_bijective ho hs hU ⟨a,ha⟩
  obtain ⟨e,he,hes,het,hdi,hen⟩ := exists_biholomorphic_inverse ho
    hs.isPathConnected.isConnected.isPreconnected hfd hfb ha
    (norm_pos_iff.mp hda)
  refine ⟨e.symm,het,hes,hdi,?_,?_,?_⟩
  · simpa only [e.symm_symm,he] using hfd
  · intro z hz
    have hzt : z ∈ e.target := het.symm ▸ hz
    have hw : e.symm z ∈ U := hes ▸ e.map_target hzt
    have hd : HasDerivAt e (deriv f (e.symm z)) (e.symm z) := by
      rw [he]
      exact ((hfd _ hw).differentiableAt (ho.mem_nhds hw)).hasDerivAt
    have hd' := e.hasDerivAt_symm hzt (hen _ hw) hd
    rw [hd'.deriv]
    exact inv_ne_zero (hen _ hw)
  · simpa only [e.symm_symm,he] using hen

end StrictHotSpots.Riemann
end
end
end
end
end RiemannBiholomorphic

section RiemannDomain





noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
namespace StrictHotSpots.Conformal

lemma conjugate_contDiffOn {f : ℂ → ℂ} {U : Set ℂ}
    (ho : IsOpen U) (hd : DifferentiableOn ℂ f U) :
    ContDiffOn ℝ ∞ (fun x : Plane => coordinate (f (coordinate.symm x)))
      (coordinate.symm ⁻¹' U) := by
  exact coordinate.contDiff.comp_contDiffOn
    (((hd.contDiffOn ho).restrict_scalars ℝ).comp coordinate.symm.contDiff.contDiffOn
      (fun _ hx => hx))

lemma conjugate_hasFDerivAt {f : ℂ → ℂ} {x : Plane}
    (hd : DifferentiableAt ℂ f (coordinate.symm x)) :
    HasFDerivAt (fun y : Plane => coordinate (f (coordinate.symm y)))
      (planeMul (deriv f (coordinate.symm x))) x :=
  coordinate.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp x
    ((hd.hasDerivAt.hasFDerivAt.restrictScalars ℝ).comp x
      coordinate.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt)



end StrictHotSpots.Conformal
end
end RiemannDomain

section RiemannSchwarz

noncomputable section
open Set Filter Metric _root_.OAI.Complex Function
open scoped Topology ComplexConjugate
namespace StrictHotSpots.Riemann

lemma mobius_neg_zero (z : ℂ) : mobius (-z) 0 = z := by simp


theorem schwarz_mobius_ball {f : ℂ → ℂ} {c x : ℂ} {r : ℝ}
    (hd : DifferentiableOn ℂ f (ball c r))
    (hm : MapsTo f (ball c r) (ball 0 1)) (hx : x ∈ ball c r) :
    ‖mobius (f c) (f x)‖ ≤ dist x c / r := by
  have hr : 0 < r := nonempty_ball.mp ⟨x,hx⟩
  have hc : c ∈ ball c r := mem_ball_self hr
  have hfc : ‖f c‖ < 1 := mem_ball_zero_iff.mp (hm hc)
  let g : ℂ → ℂ := fun y => mobius (f c) (f y)
  have hg0 : g c = 0 := mobius_self _
  have hgd : DifferentiableOn ℂ g (ball c r) := by
    intro y hy
    exact ((hasDerivAt_mobius hfc (mem_ball_zero_iff.mp (hm hy))).differentiableAt.comp y
      ((hd y hy).differentiableAt (isOpen_ball.mem_nhds hy))).differentiableWithinAt
  have hgm : MapsTo g (ball c r) (closedBall (g c) 1) := by
    intro y hy
    rw [hg0,mem_closedBall_zero_iff]
    exact (norm_mobius_lt hfc (mem_ball_zero_iff.mp (hm hy))).le
  have H := Complex.dist_le_div_mul_dist_of_mapsTo_ball hgd hgm hx
  simpa only [g,hg0,dist_zero_right,one_div,div_eq_mul_inv,mul_comm,mul_one] using H



theorem schwarz_pick_deriv {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1))
    (hm : MapsTo f (ball 0 1) (ball 0 1)) {z : ℂ} (hz : z ∈ ball 0 1) :
    ‖deriv f z‖ * (1-‖z‖^2) ≤ 1-‖f z‖^2 := by
  have hz' : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hfz : ‖f z‖ < 1 := mem_ball_zero_iff.mp (hm hz)
  have hneg : ‖-z‖ < 1 := by simpa only [norm_neg] using hz'
  let g : ℂ → ℂ := fun w => mobius (f z) (f (mobius (-z) w))
  have hg0 : g 0 = 0 := by simp [g]
  have hgd (w : ℂ) (hw : w ∈ ball 0 1) : DifferentiableAt ℂ g w := by
    have hw' : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
    have hmw : mobius (-z) w ∈ ball 0 1 := mem_ball_zero_iff.mpr (norm_mobius_lt hneg hw')
    exact ((hasDerivAt_mobius hfz (mem_ball_zero_iff.mp (hm hmw))).differentiableAt.comp w
      (((hd _ hmw).differentiableAt (isOpen_ball.mem_nhds hmw)).comp _
        (hasDerivAt_mobius hneg hw').differentiableAt))
  have hgm : MapsTo g (ball 0 1) (closedBall (g 0) 1) := by
    intro w hw
    rw [hg0,mem_closedBall_zero_iff]
    exact (norm_mobius_lt hfz (mem_ball_zero_iff.mp
      (hm (mem_ball_zero_iff.mpr (norm_mobius_lt hneg (mem_ball_zero_iff.mp hw)))))).le
  have hle := Complex.norm_deriv_le_one_of_mapsTo_ball
    (fun w hw => (hgd w hw).differentiableWithinAt) hgm (by norm_num : (0:ℝ)<1)
  have hdf : HasDerivAt f (deriv f z) (mobius (-z) (0:ℂ)) := by
    simpa only [mobius_neg_zero] using
      ((hd z hz).differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have hinner : HasDerivAt (fun w : ℂ => f (mobius (-z) w))
      (deriv f z * (1-conj (-z)*(-z))) (0:ℂ) := by
    exact hdf.comp (0:ℂ) (hasDerivAt_mobius_zero hneg)
  have houter : HasDerivAt (mobius (f z))
      ((1-conj (f z)*f z)/(1-conj (f z)*f z)^2) (f (mobius (-z) (0:ℂ))) := by
    simpa only [mobius_neg_zero] using hasDerivAt_mobius hfz hfz
  have hd0 := houter.comp (0:ℂ) hinner
  change HasDerivAt g
    (((1-conj (f z)*f z)/(1-conj (f z)*f z)^2)*
      (deriv f z*(1-conj (-z)*(-z)))) 0 at hd0
  rw [hd0.deriv,norm_mul,norm_mul,norm_mobius_self_deriv hfz,
    norm_mobius_zero_deriv hneg,norm_neg] at hle
  have hpos : 0 < 1-‖f z‖^2 := by nlinarith [norm_nonneg (f z)]
  have hh : (‖deriv f z‖*(1-‖z‖^2))/(1-‖f z‖^2) ≤ 1 := by
    simpa only [one_div,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using hle
  exact (div_le_one hpos).mp hh

lemma mobius_deficit_identity {a y : ℂ} (ha : ‖a‖ < 1) (hy : ‖y‖ < 1) :
    (1-‖mobius a y‖^2)*‖1-conj a*y‖^2 = (1-‖a‖^2)*(1-‖y‖^2) := by
  have hn : ‖1-conj a*y‖ ≠ 0 := norm_ne_zero_iff.mpr (mobius_denom_ne ha hy)
  rw [mobius,norm_div,div_pow]
  calc
    _ = ‖1-conj a*y‖^2-‖y-a‖^2 := by rw [sub_mul,one_mul,div_mul_cancel₀ _ (pow_ne_zero _ hn)]
    _ = _ := mobius_norm_identity a y



lemma mobius_boundary_deficit {a y : ℂ} {m t : ℝ}
    (hm : m < 1) (ha : ‖a‖ ≤ m) (hy : ‖y‖ < 1)
    (ht : t < 1) (hmt : ‖mobius a y‖ ≤ t) :
    (1-m)^2*(1-t) ≤ 2*(1-‖y‖) := by
  have ha' : ‖a‖ < 1 := ha.trans_lt hm
  have ht0 : 0 ≤ t := (norm_nonneg _).trans hmt
  have hm0 : 0 ≤ m := (norm_nonneg _).trans ha
  have hmul : ‖a‖*‖y‖ ≤ m :=
    (mul_le_of_le_one_right (norm_nonneg _) hy.le).trans ha
  have hden : 1-m ≤ ‖1-conj a*y‖ := by
    have hh := norm_sub_norm_le (1:ℂ) (conj a*y)
    simp only [norm_one,norm_mul,_root_.Complex.norm_conj] at hh
    linarith
  have hden2 : (1-m)^2 ≤ ‖1-conj a*y‖^2 :=
    pow_le_pow_left₀ (by linarith) hden 2
  have hmt2 : ‖mobius a y‖^2 ≤ t := by
    have hh := pow_le_pow_left₀ (norm_nonneg _) hmt 2
    nlinarith
  have hn : 0 ≤ 1-‖mobius a y‖^2 := by nlinarith
  calc
    _ ≤ ‖1-conj a*y‖^2*(1-‖mobius a y‖^2) :=
      mul_le_mul hden2 (by linarith) (by linarith) (sq_nonneg _)
    _ = (1-‖a‖^2)*(1-‖y‖^2) :=
      (mul_comm _ _).trans (mobius_deficit_identity ha' hy)
    _ ≤ 1-‖y‖^2 := mul_le_of_le_one_left
      (by nlinarith [norm_nonneg y]) (by nlinarith [sq_nonneg ‖a‖])
    _ ≤ 2*(1-‖y‖) := by nlinarith [sq_nonneg (1-‖y‖)]



theorem disk_distance_from_interior_ball {f : ℂ → ℂ} {c x : ℂ} {r m : ℝ}
    (hd : DifferentiableOn ℂ f (ball c r))
    (hf : MapsTo f (ball c r) (ball 0 1)) (hx : x ∈ ball c r)
    (hm : m < 1) (hfc : ‖f c‖ ≤ m) :
    (1-m)^2*(r-dist x c) ≤ 2*r*(1-‖f x‖) := by
  have hr : 0 < r := nonempty_ball.mp ⟨x,hx⟩
  have ht : dist x c/r < 1 := (div_lt_one hr).mpr hx
  have H := mobius_boundary_deficit hm hfc (mem_ball_zero_iff.mp (hf hx)) ht
    (schwarz_mobius_ball hd hf hx)
  have H' := mul_le_mul_of_nonneg_left H hr.le
  have hcancel : r*((1-m)^2*(1-dist x c/r)) = (1-m)^2*(r-dist x c) := by
    field_simp
  rw [hcancel] at H'
  nlinarith only [H']

end StrictHotSpots.Riemann
end
end RiemannSchwarz


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_ClosedChart
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section RollingBallTaylor




noncomputable section
open Set Metric Filter
open scoped Topology NNReal
namespace StrictHotSpots.Rolling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma taylor_quadratic {f : E → ℝ} {U : Set E} {K : ℝ≥0}
    (hU : Convex ℝ U) (hd : ∀ x ∈ U, DifferentiableAt ℝ f x)
    (hL : LipschitzOnWith K (fderiv ℝ f) U) {p x : E} (hp : p ∈ U) (hx : x ∈ U) :
    ‖f x-f p-fderiv ℝ f p (x-p)‖ ≤ (K:ℝ)*‖x-p‖^2 := by
  have hs : segment ℝ p x ⊆ U := hU.segment_subset hp hx
  have H := (convex_segment p x).norm_image_sub_le_of_norm_fderiv_le'
    (fun y hy => hd y (hs hy))
    (φ := fderiv ℝ f p) (C := (K:ℝ)*‖x-p‖)
    (fun y hy => (hL.norm_sub_le (hs hy) hp).trans
      (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hy) K.coe_nonneg))
    (left_mem_segment ℝ p x) (right_mem_segment ℝ p x)
  simpa only [pow_two,mul_assoc] using H

lemma norm_sub_smul_sq (y n : E) (r : ℝ) :
    ‖y-r•n‖^2 = ‖y‖^2 - 2*r*inner ℝ y n + r^2*‖n‖^2 := by
  rw [norm_sub_sq_real,real_inner_smul_right,norm_smul,Real.norm_eq_abs,
    mul_pow,sq_abs]
  ring

lemma tangent_ball_linear {p n x : E} {r : ℝ} (hn : ‖n‖ = 1) (hr : 0 < r)
    (hx : x ∈ ball (p+r•n) r) :
    ‖x-p‖^2 < 2*r*inner ℝ (x-p) n := by
  have hh : ‖(x-p)-r•n‖ < r := by
    simpa only [mem_ball,dist_eq_norm,sub_add_eq_sub_sub] using hx
  have hh2 := (sq_lt_sq₀ (norm_nonneg _) hr.le).mpr hh
  rw [norm_sub_smul_sq,hn,one_pow,mul_one] at hh2
  linarith



lemma balls_of_taylor {f : E → ℝ} {p n : E} {U : Set E} {a K r : ℝ}
    (hn : ‖n‖ = 1) (ha : 0 < a) (hr : 0 < r)
    (hsmall : 2*r*K ≤ a) (hzero : f p = 0)
    (hD : ∀ v, fderiv ℝ f p v = a*inner ℝ n v)
    (hB : ball p (2*r) ⊆ U)
    (hT : ∀ x ∈ U, ‖f x-f p-fderiv ℝ f p (x-p)‖ ≤ K*‖x-p‖^2) :
    ball (p-r•n) r ⊆ {x | f x < 0} ∧
    ball (p+r•n) r ⊆ {x | 0 < f x} := by
  have hside (N : E) (hN : ‖N‖ = 1) (x : E) (hx : x ∈ ball (p+r•N) r) :
      x ∈ U ∧ ‖x-p‖^2 < 2*r*inner ℝ (x-p) N := by
    refine ⟨hB ?_,tangent_ball_linear hN hr hx⟩
    have hd : dist (p+r•N) p = r := by
      simp [dist_eq_norm,norm_smul,hN,abs_of_pos hr]
    calc
      dist x p ≤ dist x (p+r•N)+dist (p+r•N) p := dist_triangle _ _ _
      _ < r+r := add_lt_add_of_lt_of_le hx (le_of_eq hd)
      _ = 2*r := by ring
  constructor
  · intro x hx
    have hx' : x ∈ ball (p+r•(-n)) r := by simpa [smul_neg,sub_eq_add_neg] using hx
    obtain ⟨hxU,hx2⟩ := hside (-n) (by simpa using hn) x hx'
    rw [inner_neg_right,real_inner_comm n (x-p)] at hx2
    have ht := hT x hxU
    rw [hzero,sub_zero,hD,Real.norm_eq_abs] at ht
    have he := (le_abs_self (f x-a*inner ℝ n (x-p))).trans ht
    have hk := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖x-p‖)
    have hstrict := mul_lt_mul_of_pos_left hx2 ha
    have hmul := mul_le_mul_of_nonneg_left he (mul_pos (by norm_num : (0:ℝ)<2) hr).le
    change f x < 0
    nlinarith only [hmul,hstrict,hk,hr]
  · intro x hx
    obtain ⟨hxU,hx2⟩ := hside n hn x hx
    rw [real_inner_comm n (x-p)] at hx2
    have ht := hT x hxU
    rw [hzero,sub_zero,hD,Real.norm_eq_abs] at ht
    have he' : -(K*‖x-p‖^2) ≤ f x-a*inner ℝ n (x-p) := by
      have hh := neg_abs_le (f x-a*inner ℝ n (x-p))
      linarith [ht]
    have hk := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖x-p‖)
    have hstrict := mul_lt_mul_of_pos_left hx2 ha
    have hmul := mul_le_mul_of_nonneg_left he' (mul_pos (by norm_num : (0:ℝ)<2) hr).le
    change 0 < f x
    nlinarith only [hmul,hstrict,hk,hr]

end StrictHotSpots.Rolling
end
end RollingBallTaylor

section RollingBallMetric

noncomputable section
open Set Metric Filter
open scoped Topology
namespace StrictHotSpots.Rolling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma tangent_ball_mono {p n : E} {s r : ℝ} (hn : ‖n‖ = 1)
    (hsr : s ≤ r) : ball (p+s•n) s ⊆ ball (p+r•n) r := by
  intro x hx
  have hd : dist (p+s•n) (p+r•n) = r-s := by
    rw [dist_eq_norm,show (p+s•n)-(p+r•n) = (s-r)•n by module,norm_smul,hn,mul_one,
      Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hsr)]
    ring
  calc
    dist x (p+r•n) ≤ dist x (p+s•n)+dist (p+s•n) (p+r•n) := dist_triangle _ _ _
    _ < s+(r-s) := add_lt_add_of_lt_of_le hx (le_of_eq hd)
    _ = r := by ring




lemma nearest_normal_of_balls {Ω : Set E} {x p n : E} {r : ℝ}
    (hn : ‖n‖ = 1) (hr : 0 < r) (hxp : x ≠ p)
    (hin : ball x (dist x p) ⊆ Ω)
    (hout : ball (p+r•n) r ⊆ Ωᶜ) : x = p-dist x p • n := by
  let δ := dist x p
  have hδ : 0 < δ := dist_pos.mpr hxp
  have hdisj : Disjoint (ball x δ) (ball (p+r•n) r) := by
    refine disjoint_left.mpr (fun y hy₁ hy₂ => ?_)
    exact hout hy₂ (hin hy₁)
  have hd : δ+r ≤ ‖(x-p)-r•n‖ := by
    simpa only [dist_eq_norm,sub_add_eq_sub_sub] using
      (disjoint_ball_ball_iff hδ hr).mp hdisj
  have hnorm : ‖x-p‖ = δ := (dist_eq_norm _ _).symm
  have hd2 := (sq_le_sq₀ (by positivity : 0 ≤ δ+r) (norm_nonneg _)).mpr hd
  rw [norm_sub_smul_sq,hn,one_pow,mul_one,hnorm] at hd2
  have hi : inner ℝ (x-p) n ≤ -δ := by nlinarith only [hd2,hr]
  have hi' := mul_le_mul_of_nonneg_left hi hδ.le
  have he : ‖(x-p)+δ•n‖^2 = 0 := by
    have hnn := sq_nonneg ‖(x-p)+δ•n‖
    rw [norm_add_sq_real,hnorm,real_inner_smul_right,norm_smul,
      Real.norm_eq_abs,abs_of_pos hδ,hn,mul_one] at hnn ⊢
    nlinarith only [hi',hnn]
  have hz : (x-p)+δ•n = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp he)
  dsimp [δ] at hz
  calc
    x = (x-p)+p := by abel
    _ = -(dist x p•n)+p := congrArg (fun a => a+p) (eq_neg_of_add_eq_zero_left hz)
    _ = p-dist x p•n := by abel

lemma near_interior_ball {Ω : Set E} {x p n : E} {r : ℝ}
    (hn : ‖n‖ = 1) (hr : 0 < r) (hxp : x ≠ p)
    (hin : ball x (dist x p) ⊆ Ω) (hout : ball (p+r•n) r ⊆ Ωᶜ)
    (hnear : dist x p < r) :
    dist x (p-r•n) = r-dist x p ∧ x ∈ ball (p-r•n) r := by
  have he := nearest_normal_of_balls hn hr hxp hin hout
  have heq : x-(p-r•n) = (r-dist x p) • n := by
    calc
      _ = (p-dist x p•n)-(p-r•n) := congrArg (fun a => a-(p-r•n)) he
      _ = _ := by module
  have hd : dist x (p-r•n) = r-dist x p := by
    rw [dist_eq_norm,heq,norm_smul,hn,mul_one,Real.norm_eq_abs,
      abs_of_pos (sub_pos.mpr hnear)]
  refine ⟨hd,?_⟩
  change dist x (p-r•n) < r
  rw [hd]
  linarith [dist_pos.mpr hxp]

end StrictHotSpots.Rolling
end
end RollingBallMetric

section RollingBallNormals

noncomputable section
open Set Metric
open scoped Topology
namespace StrictHotSpots.Rolling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]



lemma normals_bound {U : Set E} {p q n m : E} {r : ℝ} (hr : 0 < r)
    (hn : ‖n‖ = 1) (hm : ‖m‖ = 1)
    (hip : ball (p-r•n) r ⊆ U) (hop : ball (p+r•n) r ⊆ Uᶜ)
    (hiq : ball (q-r•m) r ⊆ U) (hoq : ball (q+r•m) r ⊆ Uᶜ) :
    r*‖n-m‖ ≤ dist p q := by
  have hd₁ : Disjoint (ball (p-r•n) r) (ball (q+r•m) r) :=
    disjoint_left.mpr (fun x h₁ h₂ => hoq h₂ (hip h₁))
  have hd₂ : Disjoint (ball (p+r•n) r) (ball (q-r•m) r) :=
    disjoint_left.mpr (fun x h₁ h₂ => hop h₁ (hiq h₂))
  have h₁ : 2*r ≤ ‖(p-q)-r•(n+m)‖ := by
    have h := (disjoint_ball_ball_iff hr hr).mp hd₁
    simpa only [dist_eq_norm,show (p-r•n)-(q+r•m)=(p-q)-r•(n+m) by module,two_mul] using h
  have h₂ : 2*r ≤ ‖(p-q)+r•(n+m)‖ := by
    have h := (disjoint_ball_ball_iff hr hr).mp hd₂
    simpa only [dist_eq_norm,show (p+r•n)-(q-r•m)=(p-q)+r•(n+m) by module,two_mul] using h
  have h₁sq := (sq_le_sq₀ (by positivity : 0 ≤ 2*r) (norm_nonneg _)).mpr h₁
  have h₂sq := (sq_le_sq₀ (by positivity : 0 ≤ 2*r) (norm_nonneg _)).mpr h₂
  have hp := parallelogram_law_with_norm ℝ (p-q) (r•(n+m))
  have hn' := parallelogram_law_with_norm ℝ n m
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr] at hp
  rw [hn,hm] at hn'
  have hsq : (r*‖n-m‖)^2 ≤ ‖p-q‖^2 := by
    nlinarith only [h₁sq,h₂sq,hp,hn',sq_nonneg r]
  rw [dist_eq_norm]
  exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp hsq

lemma interior_centers_bound {U : Set E} {p q n m : E} {r : ℝ} (hr : 0 < r)
    (hn : ‖n‖ = 1) (hm : ‖m‖ = 1)
    (hip : ball (p-r•n) r ⊆ U) (hop : ball (p+r•n) r ⊆ Uᶜ)
    (hiq : ball (q-r•m) r ⊆ U) (hoq : ball (q+r•m) r ⊆ Uᶜ) :
    dist (p-r•n) (q-r•m) ≤ 2*dist p q := by
  have H := normals_bound hr hn hm hip hop hiq hoq
  rw [dist_eq_norm,show (p-r•n)-(q-r•m)=(p-q)-r•(n-m) by module]
  calc
    _ ≤ ‖p-q‖+‖r•(n-m)‖ := norm_sub_le _ _
    _ = dist p q+r*‖n-m‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,dist_eq_norm]
    _ ≤ 2*dist p q := by linarith
end StrictHotSpots.Rolling
end
end RollingBallNormals

section RiemannBoundaryCompatible

noncomputable section


section SmoothRollingBallsCompatibleLayer

open Set Metric Filter
open scoped Topology ContDiff NNReal
namespace StrictHotSpots

lemma boundary_level_zero {Ω U : Set Plane} {ρ : Plane → ℝ} {q : Plane}
    (ho : IsOpen Ω) (hU : IsOpen U) (hq : q ∈ frontier Ω) (hqU : q ∈ U)
    (hc : ContinuousAt ρ q) (hlevel : Ω ∩ U = {x | ρ x < 0} ∩ U) : ρ q = 0 := by
  have hnonneg : 0 ≤ ρ q := by
    by_contra hh
    have hmem : q ∈ Ω ∩ U := hlevel ▸ ⟨lt_of_not_ge hh,hqU⟩
    exact hq.2 (ho.interior_eq.symm ▸ hmem.1)
  apply le_antisymm _ hnonneg
  by_contra hh
  have hp : 0 < ρ q := lt_of_not_ge hh
  have hnh : U ∩ ρ ⁻¹' Ioi 0 ∈ 𝓝 q :=
    inter_mem (hU.mem_nhds hqU) (hc.preimage_mem_nhds (Ioi_mem_nhds hp))
  obtain ⟨x,⟨hxU,hxρ⟩,hxΩ⟩ := mem_closure_iff_nhds.mp hq.1 _ hnh
  have hx : x ∈ {x | ρ x < 0} ∩ U := hlevel ▸ ⟨hxΩ,hxU⟩
  exact lt_asymm (show ρ x < 0 from hx.1) (show 0 < ρ x from hxρ)




lemma SmoothBoundary.local_rolling_balls {Ω : Set Plane} (hs : SmoothBoundary Ω)
    (ho : IsOpen Ω) {p : Plane} (hp : p ∈ frontier Ω) :
    ∃ (V : Set Plane), IsOpen V ∧ p ∈ V ∧ ∃ r > 0,
      ∀ q ∈ frontier Ω ∩ V, ∃ n : Plane, ‖n‖ = 1 ∧
        ball (q-r•n) r ⊆ Ω ∧ ball (q+r•n) r ⊆ Ωᶜ := by
  obtain ⟨U,ρ,hU,hpU,hρ,hD,hpρ,hlevel⟩ := hs p hp
  have hc : ContDiffAt ℝ ∞ ρ p := (hρ p hpU).contDiffAt (hU.mem_nhds hpU)
  have hdc : ContDiffAt ℝ 1 (fderiv ℝ ρ) p := hc.fderiv_right (by exact WithTop.coe_le_coe.mpr le_top)
  obtain ⟨K,A,hA,hL⟩ := hdc.exists_lipschitzOnWith
  let a : ℝ := ‖fderiv ℝ ρ p‖/2
  have ha : 0 < a := half_pos (norm_pos_iff.mpr hD)
  have han : a < ‖fderiv ℝ ρ p‖ := by dsimp [a]; linarith [norm_pos_iff.mpr hD]
  have hAn : {x | a < ‖fderiv ℝ ρ x‖} ∈ 𝓝 p :=
    hdc.continuousAt.norm.preimage_mem_nhds (Ioi_mem_nhds han)
  obtain ⟨R,hR,hsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hU.mem_nhds hpU) (inter_mem hA hAn))
  let r : ℝ := min (R/8) (a/(4*((K:ℝ)+1)))
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrR : 2*r ≤ R/4 := by have := min_le_left (R/8) (a/(4*((K:ℝ)+1))); dsimp [r]; linarith
  have hrK : 2*r*(K:ℝ) ≤ a := by
    have hh : r ≤ a/(4*((K:ℝ)+1)) := min_le_right _ _
    have hc' : 0 < 4*((K:ℝ)+1) := by positivity
    have hh' := (le_div_iff₀ hc').mp hh
    nlinarith [K.coe_nonneg]
  refine ⟨ball p (R/4),isOpen_ball,mem_ball_self (by positivity),r,hr,?_⟩
  intro q hq
  have hqR : q ∈ ball p R := ball_subset_ball (by linarith : R/4 ≤ R) hq.2
  have hqU := (hsub hqR).1
  have hqρ : ρ q = 0 := boundary_level_zero ho hU hq.1 hqU
    ((hρ q hqU).contDiffAt (hU.mem_nhds hqU)).continuousAt hlevel
  let g := gradient ρ q
  have hg : ‖g‖ = ‖fderiv ℝ ρ q‖ := by simp [g,gradient]
  have hga : a < ‖g‖ := by rw [hg]; exact (hsub hqR).2.2
  have hgpos : 0 < ‖g‖ := ha.trans hga
  let n : Plane := ‖g‖⁻¹ • g
  have hn : ‖n‖ = 1 := by simp [n,norm_smul,ne_of_gt hgpos]
  have hDq (v : Plane) : fderiv ℝ ρ q v = ‖g‖*inner ℝ n v := by
    rw [show n = ‖g‖⁻¹ • g from rfl,real_inner_smul_left,
      ← mul_assoc,mul_inv_cancel₀ hgpos.ne',one_mul]
    exact inner_gradient_left.symm
  have hball : ball q (2*r) ⊆ ball p R := by
    intro x hx
    calc
      dist x p ≤ dist x q + dist q p := dist_triangle _ _ _
      _ < 2*r+R/4 := add_lt_add hx hq.2
      _ < R := by linarith
  have hT (x : Plane) (hx : x ∈ ball p R) :
      ‖ρ x-ρ q-fderiv ℝ ρ q (x-q)‖ ≤ (K:ℝ)*‖x-q‖^2 :=
    Rolling.taylor_quadratic (convex_ball p R)
      (fun y hy => ((hρ y (hsub hy).1).contDiffAt
        (hU.mem_nhds (hsub hy).1)).differentiableAt (by simp))
      (hL.mono (fun _ hy => (hsub hy).2.1)) hqR hx
  obtain ⟨hin,hout⟩ := Rolling.balls_of_taylor hn hgpos hr
    (hrK.trans hga.le) hqρ hDq hball hT
  refine ⟨n,hn,?_,?_⟩
  · intro x hx
    have hxR : x ∈ ball p R := hball (by
      have hh : dist x q < 2*r := by
        have hd : dist (q-r•n) q = r := by
          simp [norm_smul,hn,abs_of_pos hr]
        calc
          dist x q ≤ dist x (q-r•n)+dist (q-r•n) q := dist_triangle _ _ _
          _ < r+r := add_lt_add_of_lt_of_le hx (le_of_eq hd)
          _ = 2*r := by ring
      exact hh)
    have hh : x ∈ Ω ∩ U := hlevel ▸ ⟨hin hx,(hsub hxR).1⟩
    exact hh.1
  · intro x hx hxΩ
    have hxU : x ∈ U := (hsub (hball (by
      have hd : dist (q+r•n) q = r := by
        simp [dist_eq_norm,norm_smul,hn,abs_of_pos hr]
      calc
        dist x q ≤ dist x (q+r•n)+dist (q+r•n) q := dist_triangle _ _ _
        _ < r+r := add_lt_add_of_lt_of_le hx (le_of_eq hd)
        _ = 2*r := by ring))).1
    have hh : x ∈ {x | ρ x < 0} ∩ U := hlevel ▸ ⟨hxΩ,hxU⟩
    exact lt_asymm (show 0 < ρ x from hout hx) (show ρ x < 0 from hh.1)

end StrictHotSpots
end SmoothRollingBallsCompatibleLayer


section UniformRollingBallsCompatibleLayer
open Set Metric Filter
open scoped Topology
namespace StrictHotSpots

lemma finite_positive_lower {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf : ∀ a ∈ s, 0 < f a) : ∃ r > 0, ∀ a ∈ s, r ≤ f a := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert a s hmem ih =>
    obtain ⟨r,hr,hR⟩ := ih (fun b hb => hf b (Finset.mem_insert_of_mem hb))
    refine ⟨min r (f a),lt_min hr (hf a (Finset.mem_insert_self _ _)),?_⟩
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hR b hb)




theorem SmoothBoundary.uniform_rolling_balls {Ω : Set Plane} (hs : SmoothBoundary Ω)
    (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    ∃ r > 0, ∀ p ∈ frontier Ω, ∃ n : Plane, ‖n‖ = 1 ∧
      ball (p-r•n) r ⊆ Ω ∧ ball (p+r•n) r ⊆ Ωᶜ := by
  classical
  have hlocal (p : frontier Ω) := hs.local_rolling_balls ho p.property
  choose V hVo hpV r hr hballs using hlocal
  have hc : IsCompact (frontier Ω) :=
    hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hcover : frontier Ω ⊆ ⋃ p : frontier Ω, V p := by
    intro p hp
    exact mem_iUnion.mpr ⟨⟨p,hp⟩,hpV ⟨p,hp⟩⟩
  obtain ⟨s,hcov⟩ := hc.elim_finite_subcover V hVo hcover
  obtain ⟨R,hR,hRs⟩ := finite_positive_lower s r (fun p _ => hr p)
  refine ⟨R,hR,?_⟩
  intro p hp
  obtain ⟨q,hq⟩ := mem_iUnion.mp (hcov hp)
  obtain ⟨hqs,hpV⟩ := mem_iUnion.mp hq
  obtain ⟨n,hn,hin,hout⟩ := hballs q p ⟨hp,hpV⟩
  refine ⟨n,hn,?_,?_⟩
  · have hmono := Rolling.tangent_ball_mono (p := p) (n := -n)
      (by simpa only [norm_neg] using hn) (hRs q hqs)
    have hmono' : ball (p-R•n) R ⊆ ball (p-r q•n) (r q) := by
      simpa only [smul_neg,← sub_eq_add_neg] using hmono
    exact hmono'.trans hin
  · exact (Rolling.tangent_ball_mono hn (hRs q hqs)).trans hout

end StrictHotSpots
end UniformRollingBallsCompatibleLayer


section RiemannBoundaryGeometryCompatibleLayer
open Set Metric Filter
open scoped Topology
namespace StrictHotSpots


theorem SmoothBoundary.complex_rolling_balls {Ω : Set Plane} (hs : SmoothBoundary Ω)
    (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    ∃ r > 0, ∀ p ∈ frontier (Conformal.coordinate ⁻¹' Ω), ∃ n : ℂ, ‖n‖ = 1 ∧
      ball (p-r•n) r ⊆ Conformal.coordinate ⁻¹' Ω ∧
      ball (p+r•n) r ⊆ (Conformal.coordinate ⁻¹' Ω)ᶜ := by
  obtain ⟨r,hr,hR⟩ := hs.uniform_rolling_balls ho hb
  refine ⟨r,hr,?_⟩
  intro p hp
  have hp' : Conformal.coordinate p ∈ frontier Ω := by
    change p ∈ Conformal.coordinate.toHomeomorph ⁻¹' frontier Ω
    rw [Conformal.coordinate.toHomeomorph.preimage_frontier]
    exact hp
  obtain ⟨n,hn,hin,hout⟩ := hR _ hp'
  refine ⟨Conformal.coordinate.symm n,by simpa using hn,?_,?_⟩
  · intro x hx
    apply hin
    simpa only [mem_ball,← Conformal.coordinate.dist_map x (p-r•Conformal.coordinate.symm n),
      map_sub,map_smul,LinearIsometryEquiv.apply_symm_apply] using hx
  · intro x hx
    apply hout
    simpa only [mem_ball,← Conformal.coordinate.dist_map x (p+r•Conformal.coordinate.symm n),
      map_add,map_smul,LinearIsometryEquiv.apply_symm_apply] using hx

namespace Riemann
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

omit [NormedSpace ℝ E] [ProperSpace E] in
lemma boundary_distance_pos {U : Set E} (ho : IsOpen U) (hc : Uᶜ.Nonempty)
    {x : E} (hx : x ∈ U) : 0 < infDist x Uᶜ := by
  apply (infDist_pos_iff_notMem_closure hc).mp
  rwa [ho.isClosed_compl.closure_eq,mem_compl_iff,not_not]



lemma nearest_frontier {U : Set E} (ho : IsOpen U) (hc : Uᶜ.Nonempty)
    {x : E} (hx : x ∈ U) :
    ∃ p ∈ frontier U, dist x p = infDist x Uᶜ ∧ x ≠ p ∧
      ball x (dist x p) ⊆ U := by
  obtain ⟨p,hp,he⟩ := ho.isClosed_compl.exists_infDist_eq_dist hc x
  have hδ := boundary_distance_pos ho hc hx
  have hball : ball x (dist x p) ⊆ U := by
    rw [← he]
    exact ball_infDist_compl_subset
  have hpcl : p ∈ closure U := by
    have hpc : p ∈ closedBall x (dist x p) := by simp [dist_comm]
    rw [← closure_ball x (by linarith : dist x p ≠ 0)] at hpc
    exact closure_mono hball hpc
  refine ⟨p,?_,he.symm,?_,hball⟩
  · rw [frontier_eq_closure_inter_closure,ho.isClosed_compl.closure_eq]
    exact ⟨hpcl,hp⟩
  · exact dist_ne_zero.mp (by linarith)

omit [NormedSpace ℝ E] in


lemma compact_core {U : Set E} (hb : Bornology.IsBounded U) {r : ℝ} (hr : 0 < r) :
    IsCompact {x | x ∈ closure U ∧ r ≤ infDist x Uᶜ} ∧
      {x | x ∈ closure U ∧ r ≤ infDist x Uᶜ} ⊆ U := by
  have hclosed : IsClosed {x : E | r ≤ infDist x Uᶜ} :=
    isClosed_le continuous_const (continuous_infDist_pt Uᶜ)
  refine ⟨hb.isCompact_closure.inter_right hclosed,?_⟩
  intro x hx
  by_contra hnot
  have hz : infDist x Uᶜ = 0 := infDist_zero_of_mem hnot
  linarith [hx.2]

end Riemann
end StrictHotSpots
end RiemannBoundaryGeometryCompatibleLayer


section RiemannBoundaryDistanceCompatibleLayer
open Set Metric Filter
open scoped Topology
namespace StrictHotSpots.Riemann

lemma compact_disk_separation {U K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U)
    {f : ℂ → ℂ} (hf : ContinuousOn f U) (hm : MapsTo f U (ball 0 1)) :
    ∃ m : ℝ, 0 ≤ m ∧ m < 1 ∧ ∀ x ∈ K, ‖f x‖ ≤ m := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0,le_rfl,by norm_num,by simp⟩
  obtain ⟨a,ha,hmax⟩ := hK.exists_isMaxOn hne (hf.norm.mono hKU)
  exact ⟨‖f a‖,norm_nonneg _,mem_ball_zero_iff.mp (hm (hKU ha)),hmax⟩

lemma core_of_ball_subset {U : Set ℂ} (hc : Uᶜ.Nonempty) {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hin : ball c r ⊆ U) :
    c ∈ {x | x ∈ closure U ∧ r ≤ infDist x Uᶜ} := by
  refine ⟨subset_closure (hin (mem_ball_self hr)),(le_infDist hc).mpr ?_⟩
  intro y hy
  by_contra h
  exact hy (hin (by simpa only [mem_ball,dist_comm] using lt_of_not_ge h))




theorem domain_distance_le_disk_distance {U : Set ℂ} (ho : IsOpen U)
    (hb : Bornology.IsBounded U) (hc : Uᶜ.Nonempty)
    {r : ℝ} (hr : 0 < r)
    (hroll : ∀ p ∈ frontier U, ∃ n : ℂ, ‖n‖ = 1 ∧
      ball (p-r•n) r ⊆ U ∧ ball (p+r•n) r ⊆ Uᶜ)
    {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f U) (hm : MapsTo f U (ball 0 1)) :
    ∃ C > 0, ∀ x ∈ U, infDist x Uᶜ ≤ C*(1-‖f x‖) := by
  let K : Set ℂ := {x | x ∈ closure U ∧ r ≤ infDist x Uᶜ}
  have hK := compact_core hb hr
  obtain ⟨m,hm0,hm1,hfm⟩ := compact_disk_separation hK.1 hK.2 hd.continuousOn hm
  obtain ⟨M,hM⟩ := (hb.isCompact_closure.image (continuous_infDist_pt Uᶜ)).bddAbove
  let C := max (2*r/(1-m)^2) ((|M|+1)/(1-m))
  have hp : 0 < 1-m := sub_pos.mpr hm1
  have hpp : 0 < (1-m)^2 := sq_pos_of_pos hp
  have hC : 0 < C := lt_of_lt_of_le (by positivity : 0 < 2*r/(1-m)^2) (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro x hx
  have hfx : 0 < 1-‖f x‖ := sub_pos.mpr (mem_ball_zero_iff.mp (hm hx))
  by_cases hnear : infDist x Uᶜ < r
  · obtain ⟨p,hpfr,hpd,hxp,hball⟩ := nearest_frontier ho hc hx
    obtain ⟨n,hn,hin,hout⟩ := hroll p hpfr
    obtain ⟨hdist,hxin⟩ := Rolling.near_interior_ball hn hr hxp hball hout (by rwa [hpd])
    have hcenter : p-r•n ∈ K := core_of_ball_subset hc hr hin
    have hh := disk_distance_from_interior_ball (hd.mono hin) (hm.mono_left hin)
      hxin hm1 (hfm _ hcenter)
    rw [hdist] at hh
    have hh' : infDist x Uᶜ ≤ (2*r/(1-m)^2)*(1-‖f x‖) := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hpp).mpr
      nlinarith only [hh,hpd]
    exact hh'.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hfx.le)
  · have hxK : x ∈ K := ⟨subset_closure hx,le_of_not_gt hnear⟩
    have hnorm := hfm x hxK
    have hxm : infDist x Uᶜ ≤ M := hM ⟨x,subset_closure hx,rfl⟩
    have hxm' : infDist x Uᶜ ≤ |M|+1 := hxm.trans (by linarith [le_abs_self M])
    have hh : infDist x Uᶜ ≤ ((|M|+1)/(1-m))*(1-‖f x‖) := by
      calc
        _ ≤ |M|+1 := hxm'
        _ = ((|M|+1)/(1-m))*(1-m) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hfx.le)

end StrictHotSpots.Riemann
end RiemannBoundaryDistanceCompatibleLayer


section RiemannDerivativeBoundCompatibleLayer
open Set Metric Filter _root_.Complex _root_.OAI.Complex
open scoped Topology
namespace StrictHotSpots.Riemann

lemma exterior_ball_distance {U : Set ℂ} (ho : IsOpen U) (hc : Uᶜ.Nonempty)
    {r : ℝ} (hr : 0 < r) {b y : ℂ} (hout : ball b r ⊆ Uᶜ) (hy : y ∈ U) :
    r+infDist y Uᶜ ≤ dist y b := by
  have hδ := boundary_distance_pos ho hc hy
  have hdisj : Disjoint (ball y (infDist y Uᶜ)) (ball b r) := by
    refine disjoint_left.mpr (fun a ha ha' => ?_)
    exact hout ha' (ball_infDist_compl_subset ha)
  simpa only [add_comm] using (disjoint_ball_ball_iff hδ hr).mp hdisj


theorem schwarz_exterior_ball {F : ℂ → ℂ} (hd : DifferentiableOn ℂ F (ball 0 1))
    {b : ℂ} {r : ℝ} (hr : 0 < r)
    (hout : ∀ z ∈ ball (0:ℂ) 1, r < dist (F z) b)
    {z : ℂ} (hz : z ∈ ball (0:ℂ) 1) :
    r*‖deriv F z‖*(1-‖z‖^2) ≤ dist (F z) b ^2-r^2 := by
  let f : ℂ → ℂ := fun w => (r:ℂ)/(F w-b)
  have hne (w : ℂ) (hw : w ∈ ball (0:ℂ) 1) : F w-b ≠ 0 := by
    apply norm_ne_zero_iff.mp
    have hh := hout w hw
    rw [dist_eq_norm] at hh
    linarith
  have hf (w : ℂ) (hw : w ∈ ball (0:ℂ) 1) :
      HasDerivAt f (-(r:ℂ)*deriv F w/(F w-b)^2) w := by
    simpa only [f,zero_mul,zero_sub,neg_mul] using
      (hasDerivAt_const w (r:ℂ)).fun_div
        (((hd w hw).differentiableAt (isOpen_ball.mem_nhds hw)).hasDerivAt.sub_const b) (hne w hw)
  have hm : MapsTo f (ball 0 1) (ball 0 1) := by
    intro w hw
    rw [mem_ball_zero_iff]
    dsimp [f]
    rw [norm_div,norm_real,Real.norm_of_nonneg hr.le]
    exact (div_lt_one (by simpa only [dist_eq_norm] using hr.trans (hout w hw))).mpr
      (by simpa only [dist_eq_norm] using hout w hw)
  have hh := schwarz_pick_deriv (fun w hw => (hf w hw).differentiableAt.differentiableWithinAt) hm hz
  rw [(hf z hz).deriv,norm_div,norm_mul,norm_neg,norm_real,Real.norm_of_nonneg hr.le,
    norm_pow] at hh
  have he : ‖f z‖ = r/dist (F z) b := by
    dsimp [f]
    rw [norm_div,norm_real,Real.norm_of_nonneg hr.le,dist_eq_norm]
  rw [he,← dist_eq_norm,div_pow] at hh
  have hp : 0 < dist (F z) b ^2 := sq_pos_of_pos (hr.trans (hout z hz))
  have hh' := mul_le_mul_of_nonneg_right hh hp.le
  have hc₁ : (r*‖deriv F z‖/dist (F z) b ^2*(1-‖z‖^2))*dist (F z) b ^2 =
      r*‖deriv F z‖*(1-‖z‖^2) := by field_simp [(hr.trans (hout z hz)).ne']
  have hc₂ : (1-r^2/dist (F z) b ^2)*dist (F z) b ^2 = dist (F z) b ^2-r^2 := by field_simp [(hr.trans (hout z hz)).ne']
  rwa [hc₁,hc₂] at hh'



theorem bounded_deriv_of_rolling_balls (e : OpenPartialHomeomorph ℂ ℂ)
    (hes : e.source = ball 0 1)
    (hd : DifferentiableOn ℂ e (ball 0 1))
    (hdi : DifferentiableOn ℂ e.symm e.target)
    (hb : Bornology.IsBounded e.target)
    (hc : e.targetᶜ.Nonempty)
    {r : ℝ} (hr : 0 < r)
    (hroll : ∀ p ∈ frontier e.target, ∃ n : ℂ, ‖n‖ = 1 ∧
      ball (p-r•n) r ⊆ e.target ∧ ball (p+r•n) r ⊆ e.targetᶜ) :
    ∃ B > 0, ∀ z ∈ ball (0:ℂ) 1, ‖deriv e z‖ ≤ B := by
  have hmi : MapsTo e.symm e.target (ball 0 1) := by simpa only [← hes] using e.mapsTo_symm
  obtain ⟨C,hC,hδ⟩ := domain_distance_le_disk_distance e.open_target hb hc hr hroll hdi hmi
  obtain ⟨M,hM⟩ := (hb.isCompact_closure.image (continuous_infDist_pt e.targetᶜ)).bddAbove
  let L := 2*r+|M|+1
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨C*L/r,by positivity,?_⟩
  intro z hz
  have hzs : z ∈ e.source := hes.symm ▸ hz
  have hx : e z ∈ e.target := e.map_source hzs
  have hδz : infDist (e z) e.targetᶜ ≤ C*(1-‖z‖) := by
    simpa only [e.left_inv hzs] using hδ (e z) hx
  have hδM : infDist (e z) e.targetᶜ ≤ M := hM ⟨e z,subset_closure hx,rfl⟩
  obtain ⟨p,hp,hpd,hxp,hball⟩ := nearest_frontier e.open_target hc hx
  obtain ⟨n,hn,hin,hout⟩ := hroll p hp
  have hnormal := Rolling.nearest_normal_of_balls hn hr hxp hball hout
  have hdist : dist (e z) (p+r•n) = r+infDist (e z) e.targetᶜ := by
    rw [dist_eq_norm,show e z-(p+r•n) = -(r+dist (e z) p)•n by
      calc
        _ = (p-dist (e z) p•n)-(p+r•n) := congrArg (fun a => a-(p+r•n)) hnormal
        _ = _ := by module,
      norm_smul,hn,mul_one,Real.norm_eq_abs,abs_neg,abs_of_pos (by positivity),hpd]
  have hbound := schwarz_exterior_ball hd hr (fun w hw =>
    lt_of_lt_of_le (by linarith [boundary_distance_pos e.open_target hc (e.map_source (hes.symm ▸ hw))] :
        r < r+infDist (e w) e.targetᶜ)
      (exterior_ball_distance e.open_target hc hr hout (e.map_source (hes.symm ▸ hw)))) hz
  rw [hdist] at hbound
  have hleft : r*‖deriv e z‖*(1-‖z‖) ≤ r*‖deriv e z‖*(1-‖z‖^2) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hz' := mem_ball_zero_iff.mp hz
    nlinarith [norm_nonneg z]
  have hright : (r+infDist (e z) e.targetᶜ)^2-r^2 ≤ L*(C*(1-‖z‖)) := by
    calc
      _ = (2*r+infDist (e z) e.targetᶜ)*infDist (e z) e.targetᶜ := by ring
      _ ≤ L*(C*(1-‖z‖)) := mul_le_mul (by dsimp [L]; linarith [le_abs_self M]) hδz
        infDist_nonneg hL.le
  have hzz : 0 < 1-‖z‖ := sub_pos.mpr (mem_ball_zero_iff.mp hz)
  have hh : r*‖deriv e z‖ ≤ L*C := (mul_le_mul_iff_left₀ hzz).mp (by
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hleft.trans (hbound.trans hright))
  apply (le_div_iff₀ hr).mpr
  nlinarith only [hh]

end StrictHotSpots.Riemann
end RiemannDerivativeBoundCompatibleLayer


section RiemannInverseBoundCompatibleLayer
open Set Metric Filter _root_.Complex _root_.OAI.Complex
open scoped Topology ComplexConjugate
namespace StrictHotSpots.Riemann

lemma schwarz_pick_center {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hd : DifferentiableOn ℂ f (ball c r)) (hm : MapsTo f (ball c r) (ball 0 1)) :
    r*‖deriv f c‖ ≤ 1-‖f c‖^2 := by
  have hc : c ∈ ball c r := mem_ball_self hr
  have hfc : ‖f c‖ < 1 := mem_ball_zero_iff.mp (hm hc)
  let g := fun y => mobius (f c) (f y)
  have hg0 : g c = 0 := mobius_self _
  have hgd : DifferentiableOn ℂ g (ball c r) := by
    intro y hy
    exact ((hasDerivAt_mobius hfc (mem_ball_zero_iff.mp (hm hy))).differentiableAt.comp y
      ((hd y hy).differentiableAt (isOpen_ball.mem_nhds hy))).differentiableWithinAt
  have hgm : MapsTo g (ball c r) (closedBall (g c) 1) := by
    intro y hy
    rw [hg0,mem_closedBall_zero_iff]
    exact (norm_mobius_lt hfc (mem_ball_zero_iff.mp (hm hy))).le
  have hle := Complex.norm_deriv_le_div_of_mapsTo_ball hgd hgm hr
  have hder := (hasDerivAt_mobius hfc hfc).comp c
    ((hd c hc).differentiableAt (isOpen_ball.mem_nhds hc)).hasDerivAt
  change HasDerivAt g (((1-conj (f c)*f c)/(1-conj (f c)*f c)^2)*deriv f c) c at hder
  rw [hder.deriv,norm_mul,norm_mobius_self_deriv hfc] at hle
  have hpos : 0 < 1-‖f c‖^2 := by nlinarith [norm_nonneg (f c)]
  have hh : ‖deriv f c‖/(1-‖f c‖^2) ≤ 1/r := by simpa only [one_div,div_eq_mul_inv,mul_comm,one_mul] using hle
  have hh' := (div_le_div_iff₀ hpos hr).mp hh
  nlinarith only [hh']



theorem disk_distance_le_domain_distance (e : OpenPartialHomeomorph ℂ ℂ)
    (hes : e.source = ball 0 1) (hd : DifferentiableOn ℂ e (ball 0 1))
    (hc : e.targetᶜ.Nonempty) {r : ℝ} (hr : 0 < r)
    (hroll : ∀ p ∈ frontier e.target, ∃ n : ℂ, ‖n‖ = 1 ∧
      ball (p-r•n) r ⊆ e.target ∧ ball (p+r•n) r ⊆ e.targetᶜ) :
    ∃ A > 0, ∀ z ∈ ball (0:ℂ) 1, 1-‖z‖ ≤ A*infDist (e z) e.targetᶜ := by
  have h0 : (0:ℂ) ∈ e.source := by rw [hes]; exact mem_ball_self (by norm_num)
  have hδ0 := boundary_distance_pos e.open_target hc (e.map_source h0)
  let m := r/(r+infDist (e 0) e.targetᶜ)
  have hm : m < 1 := (div_lt_one (by positivity)).mpr (by linarith only [hδ0])
  have hpos : 0 < (1-m)^2 := sq_pos_of_pos (sub_pos.mpr hm)
  refine ⟨2/(r*(1-m)^2),by positivity,?_⟩
  intro z hz
  have hzs : z ∈ e.source := hes.symm ▸ hz
  have hx := e.map_source hzs
  have hδ := boundary_distance_pos e.open_target hc hx
  obtain ⟨p,hp,hpd,hxp,hball⟩ := nearest_frontier e.open_target hc hx
  obtain ⟨n,hn,hin,hout⟩ := hroll p hp
  let b := p+r•n
  have hnormal := Rolling.nearest_normal_of_balls hn hr hxp hball hout
  have hdist : dist (e z) b = r+infDist (e z) e.targetᶜ := by
    rw [dist_eq_norm,show e z-b = -(r+dist (e z) p)•n by
      calc
        _ = (p-dist (e z) p•n)-(p+r•n) := congrArg (fun a => a-(p+r•n)) hnormal
        _ = _ := by module,
      norm_smul,hn,mul_one,Real.norm_eq_abs,abs_neg,abs_of_pos (by positivity),hpd]
  have hsep (w : ℂ) (hw : w ∈ ball (0:ℂ) 1) : r < dist (e w) b := by
    have hδw := boundary_distance_pos e.open_target hc (e.map_source (hes.symm ▸ hw))
    exact lt_of_lt_of_le (by linarith) (exterior_ball_distance e.open_target hc hr hout
      (e.map_source (hes.symm ▸ hw)))
  let f := fun w : ℂ => (r:ℂ)/(e w-b)
  have hf : DifferentiableOn ℂ f (ball 0 1) := by
    intro w hw
    apply DifferentiableWithinAt.fun_div (differentiableWithinAt_const (r:ℂ)) ((hd w hw).sub_const b)
    apply norm_ne_zero_iff.mp
    have h := hr.trans (hsep w hw)
    simpa only [dist_eq_norm] using h.ne'
  have hnorm (w : ℂ) : ‖f w‖ = r/dist (e w) b := by
    dsimp [f]
    rw [norm_div,norm_real,Real.norm_of_nonneg hr.le,dist_eq_norm]
  have hfm : MapsTo f (ball 0 1) (ball 0 1) := by
    intro w hw
    rw [mem_ball_zero_iff,hnorm]
    exact (div_lt_one (hr.trans (hsep w hw))).mpr (hsep w hw)
  have hfc : ‖f 0‖ ≤ m := by
    rw [hnorm]
    exact div_le_div_of_nonneg_left hr.le (by positivity)
      (exterior_ball_distance e.open_target hc hr hout (e.map_source h0))
  have hh := disk_distance_from_interior_ball hf hfm hz hm hfc
  rw [dist_zero_right,hnorm,hdist] at hh
  have hright : r*(1-r/(r+infDist (e z) e.targetᶜ)) ≤ infDist (e z) e.targetᶜ := by
    have hsum : 0 < r+infDist (e z) e.targetᶜ := by positivity
    apply (mul_le_mul_iff_left₀ hsum).mp
    field_simp
    nlinarith [sq_nonneg (infDist (e z) e.targetᶜ)]
  have hh' := mul_le_mul_of_nonneg_left hh hr.le
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (mul_pos hr hpos)).mpr
  nlinarith only [hh',hright]



theorem bounded_inverse_deriv_of_rolling_balls (e : OpenPartialHomeomorph ℂ ℂ)
    (hes : e.source = ball 0 1) (hd : DifferentiableOn ℂ e (ball 0 1))
    (hdi : DifferentiableOn ℂ e.symm e.target)
    (hc : e.targetᶜ.Nonempty) {r : ℝ} (hr : 0 < r)
    (hroll : ∀ p ∈ frontier e.target, ∃ n : ℂ, ‖n‖ = 1 ∧
      ball (p-r•n) r ⊆ e.target ∧ ball (p+r•n) r ⊆ e.targetᶜ) :
    ∃ B > 0, ∀ x ∈ e.target, ‖deriv e.symm x‖ ≤ B := by
  obtain ⟨A,hA,hδ⟩ := disk_distance_le_domain_distance e hes hd hc hr hroll
  refine ⟨2*A,by positivity,?_⟩
  intro x hx
  have hδx := boundary_distance_pos e.open_target hc hx
  have hin : ball x (infDist x e.targetᶜ) ⊆ e.target := ball_infDist_compl_subset
  have hmi : MapsTo e.symm e.target (ball 0 1) := by
    simpa only [← hes] using e.mapsTo_symm
  have hh := schwarz_pick_center hδx (hdi.mono hin) (hmi.mono_left hin)
  have hz : e.symm x ∈ ball (0:ℂ) 1 := hmi hx
  have H : 1-‖e.symm x‖ ≤ A*infDist x e.targetᶜ := by
    simpa only [e.right_inv hx] using hδ (e.symm x) hz
  have H' : 1-‖e.symm x‖^2 ≤ 2*(A*infDist x e.targetᶜ) := by
    have hsq := sq_nonneg (1-‖e.symm x‖)
    nlinarith only [hsq,H]
  exact (mul_le_mul_iff_right₀ hδx).mp (by
    simpa only [mul_comm,mul_left_comm,mul_assoc] using hh.trans H')

end StrictHotSpots.Riemann
end RiemannInverseBoundCompatibleLayer


section RiemannClosedExtensionCompatibleLayer
open Set Metric Filter _root_.Complex _root_.OAI.Complex
open scoped Topology NNReal
namespace StrictHotSpots.Riemann

lemma complex_lipschitz_extension {f : ℂ → ℂ} {U : Set ℂ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f U) :
    ∃ (F : ℂ → ℂ) (B : ℝ≥0), LipschitzWith B F ∧ EqOn f F U := by
  obtain ⟨a,ha,hea⟩ := (Complex.reCLM.lipschitz.comp_lipschitzOnWith hf).extend_real
  obtain ⟨b,hb,heb⟩ := (Complex.imCLM.lipschitz.comp_lipschitzOnWith hf).extend_real
  let F : ℂ → ℂ := fun z => (a z:ℂ)+(b z:ℂ)*I
  refine ⟨F,‖Complex.reCLM‖₊*K+‖Complex.imCLM‖₊*K,?_,?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    have h₁ := ha.dist_le_mul x y
    have h₂ := hb.dist_le_mul x y
    have hh := norm_le_abs_re_add_abs_im (F x-F y)
    have hre : |(F x-F y).re| = dist (a x) (a y) := by simp [F,Real.dist_eq]
    have him : |(F x-F y).im| = dist (b x) (b y) := by simp [F,Real.dist_eq]
    rw [hre,him] at hh
    simpa only [dist_eq_norm,NNReal.coe_add,NNReal.coe_mul,add_mul,mul_assoc] using
      hh.trans (add_le_add h₁ h₂)
  · intro x hx
    apply Complex.ext
    · simpa [F] using hea hx
    · simpa [F] using heb hx



theorem closed_disk_extension (e : OpenPartialHomeomorph ℂ ℂ)
    (hes : e.source = ball 0 1) (hd : DifferentiableOn ℂ e (ball 0 1))
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ z ∈ ball (0:ℂ) 1, ‖deriv e z‖ ≤ B) :
    ∃ (F : ℂ → ℂ) (L : ℝ≥0), LipschitzWith L F ∧ EqOn e F (ball 0 1) ∧
      F '' closedBall 0 1 = closure e.target := by
  have hLip : LipschitzOnWith ⟨B,hB⟩ e (ball 0 1) :=
    (convex_ball (0:ℂ) 1).lipschitzOnWith_of_nnnorm_deriv_le
      (fun z hz => (hd z hz).differentiableAt (isOpen_ball.mem_nhds hz)) hbound
  obtain ⟨F,L,hF,he⟩ := complex_lipschitz_extension hLip
  have him : F '' ball (0:ℂ) 1 = e.target := by
    calc
      F '' ball (0:ℂ) 1 = e '' ball (0:ℂ) 1 := image_congr he.symm
      _ = e.target := by rw [← hes,e.image_source_eq_target]
  refine ⟨F,L,hF,he,?_⟩
  apply Subset.antisymm
  · rw [← closure_ball (0:ℂ) (by norm_num : (1:ℝ) ≠ 0)]
    simpa only [him] using image_closure_subset_closure_image (s := ball (0:ℂ) 1) hF.continuous
  · have hclosed : IsClosed (F '' closedBall (0:ℂ) 1) :=
      ((isCompact_closedBall (0:ℂ) 1).image hF.continuous).isClosed
    apply closure_minimal _ hclosed
    rw [← him]
    exact image_mono ball_subset_closedBall

end StrictHotSpots.Riemann
end RiemannClosedExtensionCompatibleLayer


section RiemannGlobalInverseCompatibleLayer
open Set Metric Filter _root_.Complex _root_.OAI.Complex
open scoped Topology NNReal
namespace StrictHotSpots.Riemann

lemma dist_image_le_on_ball {U : Set ℂ} (ho : IsOpen U) {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f U) {B : ℝ} (hB : ∀ z ∈ U, ‖deriv f z‖ ≤ B)
    {c : ℂ} {r : ℝ} (hin : ball c r ⊆ U) {x y : ℂ}
    (hx : x ∈ ball c r) (hy : y ∈ ball c r) :
    dist (f x) (f y) ≤ B*dist x y := by
  simpa only [dist_eq_norm] using (convex_ball c r).norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (hd z (hin hz)).differentiableAt (ho.mem_nhds (hin hz)))
    (fun z hz => hB z (hin hz)) hy hx




theorem lipschitz_of_rolling_balls {U : Set ℂ} (ho : IsOpen U) (hc : Uᶜ.Nonempty)
    {r : ℝ} (hr : 0 < r)
    (hroll : ∀ p ∈ frontier U, ∃ n : ℂ, ‖n‖ = 1 ∧
      ball (p-r•n) r ⊆ U ∧ ball (p+r•n) r ⊆ Uᶜ)
    {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f U)
    (hm : MapsTo f U (ball 0 1)) {B : ℝ} (hB : 0 < B)
    (hbound : ∀ x ∈ U, ‖deriv f x‖ ≤ B) :
    ∃ L : ℝ≥0, LipschitzOnWith L f U := by
  let L : ℝ := 40*B+40/r
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨⟨L,hL.le⟩,LipschitzOnWith.of_dist_le_mul ?_⟩
  intro x hx y hy
  change dist (f x) (f y) ≤ L*dist x y
  have hδx := boundary_distance_pos ho hc hx
  have hδy := boundary_distance_pos ho hc hy
  have hLB : B ≤ L := by
    dsimp [L]
    have := div_pos (by norm_num : (0:ℝ)<40) hr
    linarith
  by_cases hdirect : dist x y < infDist x Uᶜ
  · have hh := dist_image_le_on_ball ho hd hbound (ball_infDist_compl_subset (s := U) (x := x))
      (mem_ball_self hδx) (by simpa only [mem_ball,dist_comm] using hdirect)
    exact hh.trans (mul_le_mul_of_nonneg_right hLB dist_nonneg)
  by_cases hnear : dist x y < r/10
  · let d := dist x y
    have hd0 : 0 < d := hδx.trans_le (le_of_not_gt hdirect)
    have hdx : infDist x Uᶜ ≤ d := le_of_not_gt hdirect
    have hdy : infDist y Uᶜ ≤ 2*d := by
      have hh : infDist y Uᶜ ≤ infDist x Uᶜ+dist y x := infDist_le_infDist_add_dist
      rw [dist_comm y x] at hh
      linarith
    obtain ⟨p,hp,hpx,hxp,hballx⟩ := nearest_frontier ho hc hx
    obtain ⟨q,hq,hqy,hyq,hbally⟩ := nearest_frontier ho hc hy
    obtain ⟨n,hn,hip,hop⟩ := hroll p hp
    obtain ⟨m,hnm,hiq,hoq⟩ := hroll q hq
    have hxpball : x ∈ ball (p-r•n) r :=
      (Rolling.near_interior_ball hn hr hxp hballx hop (by rw [hpx]; dsimp [d] at hdx; linarith)).2
    have hyqball : y ∈ ball (q-r•m) r :=
      (Rolling.near_interior_ball hnm hr hyq hbally hoq (by rw [hqy]; dsimp [d] at hdy; linarith)).2
    have hpq : dist p q ≤ 4*d := by
      have hh := dist_triangle4 p x y q
      rw [dist_comm p x,hpx,hqy] at hh
      dsimp [d] at *
      linarith
    have hcc : dist (p-r•n) (q-r•m) ≤ 8*d :=
      (Rolling.interior_centers_bound hr hn hnm hip hop hiq hoq).trans (by linarith)
    let a := p-(9*d)•n
    have ht : 9*d < r := by dsimp [d]; linarith
    have hap : dist a p = 9*d := by
      simp [a,hn,abs_of_pos hd0]
    have hac : dist a (p-r•n) = r-9*d := by
      rw [dist_eq_norm,show a-(p-r•n)=(r-9*d)•n by
        dsimp only [a]
        rw [sub_smul]
        abel,
        norm_smul,hn,mul_one,Real.norm_eq_abs,abs_of_pos (sub_pos.mpr ht)]
    have ha₁ : a ∈ ball (p-r•n) r := by rw [mem_ball,hac]; linarith
    have ha₂ : a ∈ ball (q-r•m) r := by
      have hh := dist_triangle a (p-r•n) (q-r•m)
      rw [hac] at hh
      change dist a (q-r•m) < r
      linarith
    have hxa : dist x a ≤ 10*d := by
      have hh := dist_triangle x p a
      rw [hpx,dist_comm p a,hap] at hh
      linarith
    have hay : dist a y ≤ 11*d := by
      have hh := dist_triangle a x y
      rw [dist_comm a x] at hh
      dsimp [d] at *
      linarith
    have h₁ := dist_image_le_on_ball ho hd hbound hip hxpball ha₁
    have h₂ := dist_image_le_on_ball ho hd hbound hiq ha₂ hyqball
    calc
      _ ≤ dist (f x) (f a)+dist (f a) (f y) := dist_triangle _ _ _
      _ ≤ B*(dist x a+dist a y) := by nlinarith only [h₁,h₂]
      _ ≤ B*(21*d) := mul_le_mul_of_nonneg_left (by linarith) hB.le
      _ ≤ L*d := by dsimp [L]; nlinarith [div_pos (by norm_num : (0:ℝ)<40) hr]
  · have hfar : r/10 ≤ dist x y := le_of_not_gt hnear
    have hdist : dist (f x) (f y) ≤ 2 := by
      have hh := dist_triangle (f x) 0 (f y)
      rw [dist_zero_right,dist_zero_left] at hh
      linarith [mem_ball_zero_iff.mp (hm hx),mem_ball_zero_iff.mp (hm hy)]
    apply hdist.trans
    have hpos := div_mul_cancel₀ (40:ℝ) hr.ne'
    have hh := mul_le_mul_of_nonneg_left hfar (show 0 ≤ 40/r by positivity)
    dsimp [L]
    nlinarith [mul_nonneg hB.le (dist_nonneg (x:=x) (y:=y))]

end StrictHotSpots.Riemann
end RiemannGlobalInverseCompatibleLayer


section RiemannClosedBiholomorphicCompatibleLayer
open Set Metric Filter _root_.Complex _root_.OAI.Complex
open scoped Topology NNReal
namespace StrictHotSpots.Riemann



theorem closed_bilipschitz_extension (e : OpenPartialHomeomorph ℂ ℂ)
    (hes : e.source = ball 0 1) (hd : DifferentiableOn ℂ e (ball 0 1))
    (hdi : DifferentiableOn ℂ e.symm e.target)
    (hb : Bornology.IsBounded e.target) (hc : e.targetᶜ.Nonempty)
    {r : ℝ} (hr : 0 < r)
    (hroll : ∀ p ∈ frontier e.target, ∃ n : ℂ, ‖n‖ = 1 ∧
      ball (p-r•n) r ⊆ e.target ∧ ball (p+r•n) r ⊆ e.targetᶜ) :
    ∃ (F G : ℂ → ℂ) (L M : ℝ≥0),
      LipschitzWith L F ∧ LipschitzWith M G ∧
      EqOn e F (ball 0 1) ∧ EqOn e.symm G e.target ∧
      F '' closedBall 0 1 = closure e.target ∧
      G '' closure e.target = closedBall 0 1 ∧
      (∀ z ∈ closedBall 0 1, G (F z) = z) ∧
      (∀ x ∈ closure e.target, F (G x) = x) := by
  obtain ⟨B,hB,hbound⟩ := bounded_deriv_of_rolling_balls e hes hd hdi hb hc hr hroll
  obtain ⟨F,L,hF,he,himage⟩ := closed_disk_extension e hes hd hB.le hbound
  obtain ⟨C,hC,hcbound⟩ := bounded_inverse_deriv_of_rolling_balls e hes hd hdi hc hr hroll
  have hmi : MapsTo e.symm e.target (ball 0 1) := by simpa only [← hes] using e.mapsTo_symm
  obtain ⟨K,hK⟩ := lipschitz_of_rolling_balls e.open_target hc hr hroll hdi hmi hC hcbound
  obtain ⟨G,M,hG,hi⟩ := complex_lipschitz_extension hK
  have hleft₀ : EqOn (G ∘ F) id (ball (0:ℂ) 1) := by
    intro z hz
    change G (F z) = z
    rw [← he hz,← hi (e.map_source (hes.symm ▸ hz)),e.left_inv (hes.symm ▸ hz)]
  have hleft : ∀ z ∈ closedBall (0:ℂ) 1, G (F z) = z := by
    have hh := hleft₀.closure (hG.continuous.comp hF.continuous) continuous_id
    rwa [closure_ball (0:ℂ) (by norm_num : (1:ℝ) ≠ 0)] at hh
  have hright₀ : EqOn (F ∘ G) id e.target := by
    intro x hx
    change F (G x) = x
    rw [← hi hx,← he (hmi hx),e.right_inv hx]
  have hright : ∀ x ∈ closure e.target, F (G x) = x :=
    hright₀.closure (hF.continuous.comp hG.continuous) continuous_id
  refine ⟨F,G,L,M,hF,hG,he,hi,himage,?_,hleft,hright⟩
  rw [← himage,image_image]
  exact image_congr hleft |>.trans (image_id _)



end StrictHotSpots.Riemann
end RiemannClosedBiholomorphicCompatibleLayer
end
end RiemannBoundaryCompatible

section ActualClosedConformal

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal
namespace StrictHotSpots.Conformal



theorem exists_closed_disk_chart {Ω : Set Plane} (hΩ : AdmissibleDomain Ω) :
    Nonempty (ClosedDiskChart Ω) := by
  let U : Set ℂ := coordinate ⁻¹' Ω
  have ho : IsOpen U := hΩ.2.1.preimage coordinate.continuous
  have hs : IsSimplyConnected U := coordinate.toHomeomorph.isSimplyConnected_preimage.mpr hΩ.2.2.2.1
  have hne : U.Nonempty := by
    obtain ⟨x,hx⟩ := hΩ.1
    exact ⟨coordinate.symm x,by simpa [U] using hx⟩
  have hb : Bornology.IsBounded U := by
    have he : U = coordinate.symm '' Ω := by
      ext z
      constructor
      · intro hz
        exact ⟨coordinate z,hz,coordinate.symm_apply_apply z⟩
      · rintro ⟨x,hx,rfl⟩
        simpa [U] using hx
    rw [he]
    exact coordinate.symm.lipschitz.isBounded_image hΩ.2.2.1
  have hproper : U ≠ univ := fun hh => NormedSpace.unbounded_univ ℝ ℂ (hh ▸ hb)
  have hc : Uᶜ.Nonempty := nonempty_compl.mpr hproper
  obtain ⟨Φ,hΦs,hΦt,hΦ,hΦi,hn,hn'⟩ := Riemann.exists_disk_biholomorphism ho hs hne hproper
  obtain ⟨r,hr,hroll⟩ := hΩ.2.2.2.2.complex_rolling_balls hΩ.2.1 hΩ.2.2.1
  have hroll' : ∀ p ∈ frontier Φ.target, ∃ n : ℂ, ‖n‖=1 ∧
      ball (p-r•n) r ⊆ Φ.target ∧ ball (p+r•n) r ⊆ Φ.targetᶜ := by
    simpa only [hΦt] using hroll
  have hb' : Bornology.IsBounded Φ.target := hΦt.symm ▸ hb
  have hc' : Φ.targetᶜ.Nonempty := hΦt.symm ▸ hc
  obtain ⟨B,hB,hbd⟩ := Riemann.bounded_deriv_of_rolling_balls Φ hΦs hΦ
    (hΦt.symm ▸ hΦi) hb' hc' hr hroll'
  obtain ⟨C,hC,hcd⟩ := Riemann.bounded_inverse_deriv_of_rolling_balls Φ hΦs hΦ
    (hΦt.symm ▸ hΦi) hc' hr hroll'
  obtain ⟨F,G,L,M,hF,hG,he,hi,himage,himage',hl,hright⟩ :=
    Riemann.closed_bilipschitz_extension Φ hΦs hΦ (hΦt.symm ▸ hΦi) hb' hc' hr hroll'
  let e := planeChart Φ
  have hes : e.source = DiskH10.disk := by
    rw [planeChart_source,hΦs]
    ext x
    simp only [mem_preimage,mem_ball,dist_zero_right,coordinate.symm.norm_map,DiskH10.disk]
  have het : e.target = Ω := by
    rw [planeChart_target,hΦt]
    ext x
    simp [U]
  have hsrc (x : Plane) (hx : x ∈ e.source) : coordinate.symm x ∈ ball (0:ℂ) 1 := by
    rwa [planeChart_source,hΦs] at hx
  have htgt (x : Plane) (hx : x ∈ e.target) : coordinate.symm x ∈ U := by
    rwa [planeChart_target,hΦt] at hx
  have hsrccl (x : Plane) (hx : x ∈ closure e.source) : coordinate.symm x ∈ closedBall (0:ℂ) 1 := by
    have hsball : e.source = ball (0:Plane) 1 := by
      rw [hes]
      rfl
    rw [hsball,closure_ball (0:Plane) (by norm_num : (1:ℝ) ≠ 0)] at hx
    simpa only [mem_closedBall_zero_iff,coordinate.symm.norm_map] using hx
  have htgtcl (x : Plane) (hx : x ∈ closure Ω) : coordinate.symm x ∈ closure Φ.target := by
    rw [hΦt]
    change coordinate.symm x ∈ closure (coordinate.toHomeomorph ⁻¹' Ω)
    rw [← coordinate.toHomeomorph.preimage_closure]
    simpa using hx
  let f : Plane → Plane := fun x => coordinate (F (coordinate.symm x))
  let g : Plane → Plane := fun x => coordinate (G (coordinate.symm x))
  have hf : LipschitzWith L f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [f,coordinate.dist_map,coordinate.symm.dist_map] using hF.dist_le_mul (coordinate.symm x) (coordinate.symm y)
  have hg : LipschitzWith M g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [g,coordinate.dist_map,coordinate.symm.dist_map] using hG.dist_le_mul (coordinate.symm x) (coordinate.symm y)
  refine ⟨{
    e := e
    d := fun x => deriv Φ (coordinate.symm x)
    d' := fun x => deriv Φ.symm (coordinate.symm x)
    source_eq := hes
    target_eq := het
    smooth := ?_
    inverse_smooth := ?_
    deriv := ?_
    inverse_deriv := ?_
    nonzero := ?_
    inverse_nonzero := ?_
    bound := B
    inverse_bound := C
    bound_pos := hB
    inverse_bound_pos := hC
    bounded_deriv := ?_
    bounded_inverse_deriv := ?_
    F := f
    G := g
    Lip := L
    InvLip := M
    lipschitz := hf
    inverse_lipschitz := hg
    agrees := ?_
    inverse_agrees := ?_
    maps_closure := ?_
    inverse_maps_closure := ?_
    left_inverse := ?_
    right_inverse := ?_ }⟩
  · change ContDiffOn ℝ ∞ (fun x => coordinate (Φ (coordinate.symm x))) _
    rw [planeChart_source,hΦs]
    exact conjugate_contDiffOn isOpen_ball hΦ
  · change ContDiffOn ℝ ∞ (fun x => coordinate (Φ.symm (coordinate.symm x))) _
    rw [planeChart_target,hΦt]
    exact conjugate_contDiffOn ho hΦi
  · intro x hx
    exact conjugate_hasFDerivAt ((hΦ _ (hsrc x hx)).differentiableAt (isOpen_ball.mem_nhds (hsrc x hx)))
  · intro x hx
    exact conjugate_hasFDerivAt ((hΦi _ (htgt x hx)).differentiableAt (ho.mem_nhds (htgt x hx)))
  · intro x hx
    exact hn _ (hsrc x hx)
  · intro x hx
    exact hn' _ (htgt x hx)
  · intro x hx
    exact hbd _ (hsrc x hx)
  · intro x hx
    exact hcd _ (hΦt.symm ▸ htgt x hx)
  · intro x hx
    exact congrArg coordinate (he (hsrc x hx))
  · intro x hx
    change coordinate (Φ.symm (coordinate.symm x)) = coordinate (G (coordinate.symm x))
    have hm : coordinate.symm x ∈ Φ.target := by rw [hΦt]; exact htgt x hx
    exact congrArg coordinate (hi hm)
  · intro x hx
    have hh : F (coordinate.symm x) ∈ closure Φ.target := himage ▸ mem_image_of_mem F (hsrccl x hx)
    rw [hΦt] at hh
    change coordinate (F (coordinate.symm x)) ∈ closure Ω
    change F (coordinate.symm x) ∈ closure (coordinate.toHomeomorph ⁻¹' Ω) at hh
    rwa [← coordinate.toHomeomorph.preimage_closure] at hh
  · intro x hx
    have hh : G (coordinate.symm x) ∈ closedBall (0:ℂ) 1 := himage' ▸ mem_image_of_mem G (htgtcl x hx)
    have hsball : e.source = ball (0:Plane) 1 := by rw [hes]; rfl
    rw [hsball,closure_ball (0:Plane) (by norm_num : (1:ℝ) ≠ 0)]
    simpa only [g,mem_closedBall_zero_iff,coordinate.norm_map] using hh
  · intro x hx
    simpa only [f,g,coordinate.symm_apply_apply,coordinate.apply_symm_apply] using congrArg coordinate (hl _ (hsrccl x hx))
  · intro x hx
    simpa only [f,g,coordinate.symm_apply_apply,coordinate.apply_symm_apply] using congrArg coordinate (hright _ (htgtcl x hx))

end StrictHotSpots.Conformal
end
end ActualClosedConformal

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

namespace StrictHotSpots


theorem main_theorem_oai (Ω : Set Plane) (hΩ : AdmissibleDomain Ω)
    (u : Plane → ℝ) (hu : InFirstNeumannEigenspace Ω u)
    (hne : ∃ x ∈ Ω, u x ≠ 0) : MainConclusion Ω u := by
  obtain ⟨c⟩ := Conformal.exists_closed_disk_chart hΩ
  exact strict_boundary_extrema_of_noncritical hΩ.1 hΩ.2.1 hΩ.2.2.1 hu.1.continuousOn
    (c.noncritical hΩ hu hne)
end StrictHotSpots
end
end ActualNoncritical


end OAI
end

theorem solution : type_of% @OAI.StrictHotSpots.main_theorem_oai := @OAI.StrictHotSpots.main_theorem_oai
