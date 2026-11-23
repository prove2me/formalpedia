-- Prove2me | solution 1 for NoHair.future_timelike_cones_in_chart
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T09:24:01.620877+00:00
-- url     : https://prove2.me/submissions/2b3b769a-2be5-400e-b35c-60b3a4cec8ef

import Definitions.Def_NoHair_spacetime

open NoHair Set Filter
open scoped ContDiff Manifold BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
private abbrev I4 := 𝓘(ℝ,E4)

private theorem chart_eval {G : E4 →L[ℝ] E4 →L[ℝ] ℝ} (L : E4 →L[ℝ] E4) (v w : E4) :
    G (L v) (L w) = ∑ i, ∑ j, v i * (w j * G (L (coordBasis i)) (L (coordBasis j))) := by
  have bases (z : E4) : ∑ i, z i • coordBasis i = z := by ext i; fin_cases i <;> simp [Fin.sum_univ_four,coordBasis]
  have repr (z : E4) : L z = ∑ i, z i • L (coordBasis i) := by
    calc
      _ = L (∑ i, z i • coordBasis i) := congrArg L (bases z).symm
      _ = _ := by simp only [map_sum,map_smul]
  rw [repr v,repr w]
  simp only [map_sum,map_smul,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    smul_eq_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem future_cross {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    {g : BilinField M} {T : VecField M} (hg : IsLorentzian g) {x : M}
    (hT : g x (T x) (T x) < 0) {v w : TangentSpace I4 x}
    (hv : IsFutureTimelike g T x v) (hw : IsFutureTimelike g T x w) :
    g x v w < 0 ∧ g x w v = g x v w := by
  let G : E4 →L[ℝ] E4 →L[ℝ] ℝ := g x
  obtain ⟨b,hb⟩ := hg x
  let t := fun u : E4 => (b.repr u) 0
  have form (u z : E4) : G u z = ∑ i, ∑ j, b.repr u i * (b.repr z j * minkowski i j) := by
    conv_lhs => rw [← b.sum_repr u,← b.sum_repr z]
    change (g x) _ _ = _
    simp only [map_sum,map_smul,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
      smul_eq_mul,hb,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have symm (u z : E4) : G z u = G u z := by
    rw [form,form]
    simp [Fin.sum_univ_four,minkowski]
    <;> ring
  have spatial (u : E4) (h : t u = 0) : 0 ≤ G u u := by
    rw [form]
    change b.repr u 0 = 0 at h
    simp [Fin.sum_univ_four,minkowski,h]
    <;> nlinarith only [sq_nonneg (b.repr u 1),sq_nonneg (b.repr u 2),sq_nonneg (b.repr u 3)]
  have pair (u z : E4) (hu : G u u < 0) (hz : G z z < 0) : G u z * (t u * t z) < 0 := by
    have h0 : t u ≠ 0 := fun h => (not_lt_of_ge (spatial u h)) hu
    have hk := spatial ((t z) • u - (t u) • z) (by simp [t,smul_eq_mul,mul_comm])
    simp only [map_sub,map_smul,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
      smul_eq_mul,symm u z] at hk
    nlinarith only [hk,mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (t z)) hu.le,
      mul_neg_of_pos_of_neg (sq_pos_iff.mpr h0) hz]
  have sign (u : E4) (hu : IsFutureTimelike g T x u) : 0 < t u * t (T x) := by
    have h := pair u (T x) hu.1 hT
    by_contra! hn
    exact (not_lt_of_ge (mul_nonneg_of_nonpos_of_nonpos hu.2.le hn)) h
  have hcommon : 0 < t v * t w := by
    rcases mul_pos_iff.mp (sign v hv) with h|h <;> rcases mul_pos_iff.mp (sign w hw) with h'|h'
    · exact mul_pos h.1 h'.1
    · linarith [h.2,h'.2]
    · linarith [h.2,h'.2]
    · exact mul_pos_of_neg_of_neg h.1 h'.1
  refine ⟨?_,symm v w⟩
  by_contra! hn
  exact (not_lt_of_ge (mul_nonneg hn hcommon.le)) (pair v w hv.1 hw.1)

theorem solution {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ,E4) ∞ M] (g : BilinField M) (T : VecField M)
    (hg : IsLorentzian g) (hs : IsSmoothBilinField g) (hT : IsTimeOrientation g T) (p : M) :
    let e := chartAt E4 p
    let K := {z : E4 × E4 | z.1 ∈ e.target ∧
      IsFutureTimelike g T (e.symm z.1) ((mfderiv 𝓘(ℝ,E4) 𝓘(ℝ,E4) e.symm z.1) z.2)}
    IsOpen K ∧ ∀ y ∈ e.target, Convex ℝ {v : E4 | (y,v) ∈ K} := by
  let e := chartAt E4 p
  let L : E4 → E4 →L[ℝ] E4 := fun y => mfderiv I4 I4 e.symm y
  let W : E4 → E4 := fun y => (mfderiv I4 I4 e (e.symm y) : E4 →L[ℝ] E4) (T (e.symm y))
  let C := pullbackCoeffs g e.symm
  let H := fun (y u v : E4) => ∑ i, ∑ j, u i * (v j * C y i j)
  have eval (y u v : E4) : g (e.symm y) (L y u) (L y v) = H y u v :=
    chart_eval (L y) u v
  have de : ContMDiffOn I4 I4 ∞ e e.source := contMDiffOn_chart
  have ds : ContMDiffOn I4 I4 ∞ e.symm e.target := contMDiffOn_chart_symm
  have hW : ContinuousOn W e.target := by
    let V := fun y => (⟨e.symm y,T (e.symm y)⟩ : TangentBundle I4 M)
    have hV : ContinuousOn V e.target := hT.1.comp_continuousOn e.continuousOn_symm
    have hmap := (de.continuousOn_tangentMapWithin (by simp) e.open_source.uniqueMDiffOn).comp hV
      (fun y hy => e.map_target hy)
    have hc := (contMDiff_snd_tangentBundle_modelSpace E4 I4 (n := 1)).continuous.comp_continuousOn hmap
    apply hc.congr
    intro y hy
    change (mfderiv I4 I4 e (e.symm y) : E4 →L[ℝ] E4) _ = (mfderivWithin I4 I4 e e.source (e.symm y) : E4 →L[ℝ] E4) _
    rw [mfderivWithin_of_isOpen e.open_source (e.map_target hy)]
  have inv (y : E4) (hy : y ∈ e.target) : L y (W y) = T (e.symm y) := by
    let x := e.symm y
    have hx : x ∈ e.source := e.map_target hy
    have hr : e x = y := e.right_inv hy
    have comp := mfderiv_comp (I' := I4) x
      ((ds _ (e.map_source hx)).contMDiffAt (e.open_target.mem_nhds (e.map_source hx)) |>.mdifferentiableAt (by simp))
      ((de _ hx).contMDiffAt (e.open_source.mem_nhds hx) |>.mdifferentiableAt (by simp))
    have germ : e.symm ∘ e =ᶠ[𝓝 x] id :=
      Filter.eventuallyEq_of_mem (e.open_source.mem_nhds hx) (fun z hz => e.left_inv hz)
    rw [germ.mfderiv_eq,mfderiv_id,hr] at comp
    exact (congrArg (fun A : E4 →L[ℝ] E4 => A (T x)) comp).symm
  let K := {z : E4 × E4 | z.1 ∈ e.target ∧ IsFutureTimelike g T (e.symm z.1) (L z.1 z.2)}
  change IsOpen K ∧ ∀ y ∈ e.target, Convex ℝ {v : E4 | (y,v) ∈ K}
  constructor
  · apply isOpen_iff_mem_nhds.mpr
    rintro ⟨y,v⟩ ⟨hy,hqq,hqT⟩
    change g (e.symm y) (L y v) (L y v) < 0 at hqq
    change g (e.symm y) (L y v) (T (e.symm y)) < 0 at hqT
    rw [eval] at hqq
    rw [←inv y hy,eval] at hqT
    have coeff (i j : Fin 4) : ContinuousAt (fun z : E4 × E4 => C z.1 i j) (y,v) :=
      ((hs e (chart_mem_atlas E4 p) i j).continuousOn.continuousAt (e.open_target.mem_nhds hy)).comp continuous_fst.continuousAt
    have wcont : ContinuousAt (fun z : E4 × E4 => W z.1) (y,v) :=
      (hW.continuousAt (e.open_target.mem_nhds hy)).comp continuous_fst.continuousAt
    have vx (i : Fin 4) : ContinuousAt (fun z : E4 × E4 => z.2 i) (y,v) :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.continuousAt.comp continuous_snd.continuousAt
    have wx (i : Fin 4) : ContinuousAt (fun z : E4 × E4 => W z.1 i) (y,v) :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.continuousAt.comp wcont
    have cq : ContinuousAt (fun z : E4 × E4 => H z.1 z.2 z.2) (y,v) := by
      simp only [H,Fin.sum_univ_four]
      repeat' apply ContinuousAt.add
      all_goals exact (vx _).mul ((vx _).mul (coeff _ _))
    have ct : ContinuousAt (fun z : E4 × E4 => H z.1 z.2 (W z.1)) (y,v) := by
      simp only [H,Fin.sum_univ_four]
      repeat' apply ContinuousAt.add
      all_goals exact (vx _).mul ((wx _).mul (coeff _ _))
    have hy' : ∀ᶠ z : E4 × E4 in 𝓝 (y,v), z.1 ∈ e.target :=
      continuous_fst.continuousAt (e.open_target.mem_nhds hy)
    filter_upwards [hy',cq.eventually_lt continuousAt_const hqq,ct.eventually_lt continuousAt_const hqT] with z hz hq ht
    refine ⟨hz,?_,?_⟩
    · change g (e.symm z.1) (L z.1 z.2) (L z.1 z.2) < 0
      rwa [eval]
    · change g (e.symm z.1) (L z.1 z.2) (T (e.symm z.1)) < 0
      rwa [←inv z.1 hz,eval]
  · intro y hy u hu v hv a b ha hb hab
    obtain ⟨huq,hut⟩ := hu.2
    obtain ⟨hvq,hvt⟩ := hv.2
    let G : E4 →L[ℝ] E4 →L[ℝ] ℝ := g (e.symm y)
    change G (L y u) (L y u) < 0 at huq
    change G (L y v) (L y v) < 0 at hvq
    change G (L y u) (T (e.symm y)) < 0 at hut
    change G (L y v) (T (e.symm y)) < 0 at hvt
    obtain ⟨hc,hsym⟩ := future_cross hg (hT.2 (e.symm y)) hu.2 hv.2
    change G (L y u) (L y v) < 0 at hc
    change G (L y v) (L y u) = G (L y u) (L y v) at hsym
    refine ⟨hy,?_,?_⟩
    · change G (L y (a • u + b • v)) (L y (a • u + b • v)) < 0
      simp only [map_add,map_smul,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,hsym]
      have hm := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ha hb) hc.le
      rcases eq_or_lt_of_le ha with he | he
      · have hb1 : b = 1 := by linarith
        simpa [←he,hb1] using hvq
      · nlinarith only [hm,mul_neg_of_pos_of_neg (sq_pos_of_pos he) huq,
          mul_nonpos_of_nonneg_of_nonpos (sq_nonneg b) hvq.le]
    · change G (L y (a • u + b • v)) (T (e.symm y)) < 0
      simp only [map_add,map_smul,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
      rcases eq_or_lt_of_le ha with he | he
      · have hb1 : b = 1 := by linarith
        simpa [←he,hb1] using hvt
      · exact add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg he hut) (mul_nonpos_of_nonneg_of_nonpos hb hvt.le)
