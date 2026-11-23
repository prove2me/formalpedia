-- Prove2me | solution 1 for NoHair.stationary_end_pullback_metric
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T09:43:13.223009+00:00
-- url     : https://prove2.me/submissions/2f17b40b-9406-4176-b6cd-62291b8a5458

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

private lemma open_region (R : ℝ) : IsOpen (exteriorRegion R) := by
  apply isOpen_lt continuous_const
  unfold spatialRadius
  fun_prop

private lemma orbit_in_chart {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold I4 ∞ M] {g F : BilinField M} {φ : ℝ → M → M}
    (E : AsymptoticallyFlatEnd g F φ) (y : E4) (hy : y ∈ exteriorRegion E.R) :
    flowGenerator φ (E.ψ y) = mfderiv I4 I4 E.ψ y (coordBasis 0) := by
  let l (s : ℝ) := y + s • coordBasis 0
  have hl : HasDerivAt l (coordBasis 0) 0 := by
    simpa [l] using (((hasDerivAt_id (0:ℝ)).smul_const (coordBasis 0)).const_add y)
  have h0 : l 0 = y := by simp [l]
  obtain ⟨χ,_,_,_,_,hψ,_⟩ := E.diffeo
  have hmd := ((hψ y hy).contMDiffAt ((open_region E.R).mem_nhds hy)).mdifferentiableAt (by simp)
  have hd : MDifferentiableAt I4 I4 E.ψ (l 0) := h0 ▸ hmd
  have he : (fun s => φ s (E.ψ y)) = E.ψ ∘ l := funext (fun s => (E.equivariant s y hy).symm)
  unfold flowGenerator
  rw [he, mfderiv_comp (I' := I4) 0 hd hl.differentiableAt.mdifferentiableAt]
  change mfderiv I4 I4 E.ψ (l 0) (mfderiv 𝓘(ℝ,ℝ) I4 l 0 1) = _
  rw [h0, mfderiv_eq_fderiv]
  exact congrArg (mfderiv I4 I4 E.ψ y) hl.deriv

section EndChart
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M] [IsManifold I4 ∞ M]
variable {g F : BilinField M} {φ : ℝ → M → M}

private theorem coordinate_continuous (E : AsymptoticallyFlatEnd g F φ) (hs : IsSmoothBilinField g) :
    ContinuousOn (fun z : E4 × (E4 × E4) => g (E.ψ z.1) (mfderiv I4 I4 E.ψ z.1 z.2.1)
      (mfderiv I4 I4 E.ψ z.1 z.2.2)) (exteriorRegion E.R ×ˢ Set.univ) := by
  rintro z hz
  obtain ⟨χ,_,_,_,_,hψ,_⟩ := E.diffeo
  have hψs (y) (hy : y ∈ exteriorRegion E.R) :=
    (hψ y hy).contMDiffAt ((open_region E.R).mem_nhds hy)
  let e := chartAt E4 (E.ψ z.1)
  let f := e ∘ E.ψ
  have de : ContMDiffOn I4 I4 ∞ e e.source := contMDiffOn_chart
  have di : ContMDiffOn I4 I4 ∞ e.symm e.target := contMDiffOn_chart_symm
  have hx : E.ψ z.1 ∈ e.source := mem_chart_source _ _
  have fs (y) (hy : y ∈ exteriorRegion E.R) (he : E.ψ y ∈ e.source) : ContDiffAt ℝ ∞ f y :=
    (((de _ he).contMDiffAt (e.open_source.mem_nhds he)).comp y (hψs y hy)).contDiffAt
  have hfs := fs z.1 hz.1 hx
  let V := fun (z : E4 × (E4 × E4)) => fderiv ℝ f z.1 z.2.1
  let W := fun (z : E4 × (E4 × E4)) => fderiv ℝ f z.1 z.2.2
  have hD : ContinuousAt (fun z : E4 × (E4 × E4) => fderiv ℝ f z.1) z :=
    (hfs.continuousAt_fderiv (by simp)).comp continuous_fst.continuousAt
  have hV : ContinuousAt V z := hD.clm_apply (continuous_fst.comp continuous_snd).continuousAt
  have hW : ContinuousAt W z := hD.clm_apply (continuous_snd.comp continuous_snd).continuousAt
  have v (i : Fin 4) := (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.continuousAt.comp hV
  have w (j : Fin 4) := (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.continuousAt.comp hW
  let C := pullbackCoeffs g e.symm
  have coeff (i j : Fin 4) : ContinuousAt (fun z : E4 × (E4 × E4) => C (f z.1) i j) z :=
    ((hs e (chart_mem_atlas _ _) i j).continuousOn.continuousAt (e.open_target.mem_nhds (e.map_source hx))).comp (f := fun q : E4 × (E4 × E4) => f q.1)
      (hfs.continuousAt.comp continuous_fst.continuousAt)
  let H := fun z : E4 × (E4 × E4) => ∑ i, ∑ j, V z i * (W z j * C (f z.1) i j)
  have hH : ContinuousAt H z := by
    simp only [H,Fin.sum_univ_four]
    repeat' apply ContinuousAt.add
    all_goals exact (v _).mul ((w _).mul (coeff _ _))
  have reg : ∀ᶠ q : E4 × (E4 × E4) in 𝓝 z, q.1 ∈ exteriorRegion E.R :=
    continuous_fst.continuousAt ((open_region E.R).mem_nhds hz.1)
  have hc : ∀ᶠ q : E4 × (E4 × E4) in 𝓝 z, E.ψ q.1 ∈ e.source :=
    ((hψs _ hz.1).continuousAt.comp continuous_fst.continuousAt) (e.open_source.mem_nhds hx)
  apply ContinuousAt.continuousWithinAt
  apply hH.congr_of_eventuallyEq
  filter_upwards [reg,hc] with q hq hsrc
  let y := q.1
  have germ : e.symm ∘ f =ᶠ[𝓝 y] E.ψ := by
    filter_upwards [(hψs y hq).continuousAt (e.open_source.mem_nhds hsrc)] with u hu
    exact e.left_inv hu
  have comp := mfderiv_comp (I' := I4) y
    (((di _ (e.map_source hsrc)).contMDiffAt (e.open_target.mem_nhds (e.map_source hsrc))).mdifferentiableAt (by simp))
    ((fs y hq hsrc).differentiableAt (by simp)).mdifferentiableAt
  rw [germ.mfderiv_eq,mfderiv_eq_fderiv (f := f)] at comp
  let L := mfderiv I4 I4 e.symm (f y)
  have factors (u : E4) : mfderiv I4 I4 E.ψ y u = L (fderiv ℝ f y u) :=
    congrArg (fun A : E4 →L[ℝ] E4 => A u) comp
  have hbase : e.symm (f y) = E.ψ y := e.left_inv hsrc
  change g (E.ψ y) (mfderiv I4 I4 E.ψ y q.2.1) (mfderiv I4 I4 E.ψ y q.2.2) = _
  rw [factors,factors]
  let G : E4 →L[ℝ] E4 →L[ℝ] ℝ := g (e.symm (f y))
  let gm : M → (E4 →L[ℝ] E4 →L[ℝ] ℝ) := fun p => g p
  have hgxy : (g (E.ψ y) : E4 →L[ℝ] E4 →L[ℝ] ℝ) = G := congrArg gm hbase.symm
  rw [hgxy]
  exact chart_eval (G := G) L (V q) (W q)

private theorem shifted_radius (y : E4) (s : ℝ) : spatialRadius (y+s • coordBasis 0) = spatialRadius y := by
  simp [spatialRadius,coordBasis]

private theorem translate_metric (E : AsymptoticallyFlatEnd g F φ) (hφ : IsSymmetryFlow g F φ)
    (y : E4) (hy : y ∈ exteriorRegion E.R) (s : ℝ) (u v : E4) :
    g (E.ψ (y+s • coordBasis 0)) (mfderiv I4 I4 E.ψ (y+s • coordBasis 0) u)
      (mfderiv I4 I4 E.ψ (y+s • coordBasis 0) v) =
    g (E.ψ y) (mfderiv I4 I4 E.ψ y u) (mfderiv I4 I4 E.ψ y v) := by
  let τ := fun z : E4 => z+s • coordBasis 0
  have hy' : τ y ∈ exteriorRegion E.R := by change E.R < spatialRadius (y+s • coordBasis 0); rwa [shifted_radius]
  obtain ⟨χ,_,_,_,_,hψ,_⟩ := E.diffeo
  have d (z) (hz : z ∈ exteriorRegion E.R) := ((hψ z hz).contMDiffAt ((open_region E.R).mem_nhds hz)).mdifferentiableAt (by simp)
  have hτ : HasFDerivAt τ (ContinuousLinearMap.id ℝ E4) y := (hasFDerivAt_id y).add_const _
  have hp : ContMDiff I4 I4 ∞ (φ s) := hφ.2.2.1.comp (contMDiff_const.prodMk contMDiff_id)
  have eq : E.ψ ∘ τ =ᶠ[𝓝 y] φ s ∘ E.ψ :=
    Filter.eventuallyEq_of_mem ((open_region E.R).mem_nhds hy) (fun z hz => E.equivariant s z hz)
  have eqD := eq.mfderiv_eq (I := I4) (I' := I4)
  rw [mfderiv_comp y (d _ hy') hτ.differentiableAt.mdifferentiableAt,
    mfderiv_comp y ((hp _).mdifferentiableAt (by simp)) (d _ hy),
    mfderiv_eq_fderiv (f := τ),hτ.fderiv] at eqD
  have du (a : E4) : (mfderiv I4 I4 E.ψ (τ y) : E4 →L[ℝ] E4) a =
      (mfderiv I4 I4 (φ s) (E.ψ y) : E4 →L[ℝ] E4) (mfderiv I4 I4 E.ψ y a) :=
    congrArg (fun A : E4 →L[ℝ] E4 => A a) eqD
  change g (E.ψ (τ y)) (mfderiv I4 I4 E.ψ (τ y) u) (mfderiv I4 I4 E.ψ (τ y) v) = _
  rw [du,du]
  let gm : M → (E4 →L[ℝ] E4 →L[ℝ] ℝ) := fun p => g p
  have hb : (g (E.ψ (τ y)) : E4 →L[ℝ] E4 →L[ℝ] ℝ) = g (φ s (E.ψ y)) :=
    congrArg gm (E.equivariant s y hy)
  rw [hb]
  exact hφ.2.2.2.1 s _ _ _
end EndChart

theorem solution {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ, E4) ∞ M] {g F : BilinField M} {φ : ℝ → M → M}
    (E : AsymptoticallyFlatEnd g F φ) (hs : IsSmoothBilinField g) (hφ : IsSymmetryFlow g F φ) :
    let L := fun y => mfderiv 𝓘(ℝ,E4) 𝓘(ℝ,E4) E.ψ y
    let B := fun (y v w : E4) => g (E.ψ y) (L y v) (L y w)
    ContinuousOn (fun z : E4 × (E4 × E4) => B z.1 z.2.1 z.2.2) (exteriorRegion E.R ×ˢ Set.univ) ∧
    (∀ y ∈ exteriorRegion E.R, ∀ (s : ℝ) (v w : E4), B (y+s • coordBasis 0) v w = B y v w) ∧
    ∀ y ∈ exteriorRegion E.R, flowGenerator φ (E.ψ y) = L y (coordBasis 0) := by
  exact ⟨coordinate_continuous E hs,translate_metric E hφ,orbit_in_chart E⟩
