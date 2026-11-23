-- Prove2me | solution 1 for NoHair.euclidean_chart_from_static_completion
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T10:17:11.565309+00:00
-- url     : https://prove2.me/submissions/518bc10b-a732-4749-9912-3a7639d3bbc3


import Definitions.Def_NoHair_staticConformalCompletion

open NoHair Set Filter
open scoped ContDiff Manifold Topology

noncomputable section

open scoped Bundle

private abbrev X := ADMPoint
private abbrev I := 𝓘(ℝ,ADMPoint)

private lemma euclid_flux (f : X → ℝ) (x : X) :
    staticWeightedLapseDivergence (fun _ => 1) f x =
    ∑ i : Fin 3, fderiv ℝ (fun y => (2/(1+f y))^2 * fderiv ℝ f y (EuclideanSpace.single i (1:ℝ)))
      x (EuclideanSpace.single i (1:ℝ)) := by
  have e (i : Fin 3) (y : X) : (∑ j : Fin 3, (1 : Matrix (Fin 3) (Fin 3) ℝ) i j * spatialADMPartial j f y) =
      spatialADMPartial i f y := by simp [Matrix.one_apply]
  simp only [staticWeightedLapseDivergence,Matrix.det_one,Real.sqrt_one,one_mul,inv_one]
  simp_rw [e]
  rfl

set_option maxHeartbeats 700000 in
theorem solution (Ω : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (d : StaticConformalCompletion Ω N h) (hrigidity : ThreeDimensionalZeroMassRigidity) :
    ∃ (V : ADMPoint → ℝ) (p : ADMPoint), HasStaticSpatialDoubleChart Ω N h V ∧
      ContDiffOn ℝ 2 V ({0}ᶜ) ∧ (∀ x, x ≠ 0 → -1 < V x) ∧
      (∀ ε : ℝ, 0 < ε → ∃ L : ℝ, ∀ x, L < ‖x‖ → |V x - 1| ≤ ε) ∧
      p ≠ 0 ∧ V p = 0 ∧ (∀ x : ADMPoint, x ≠ 0 → V x ≠ 0 →
        ∑ i : Fin 3, fderiv ℝ
          (fun y => (2 / (1 + V y))^2 * fderiv ℝ V y (EuclideanSpace.single i (1:ℝ)))
          x (EuclideanSpace.single i (1:ℝ)) = 0) := by
  classical
  obtain ⟨F,cf,ci,ipF⟩ := hrigidity d.carrier d.zeroMassEnd
  let a := F d.pole
  let J : X ≃ᵢ d.carrier := (IsometryEquiv.addRight a).trans F.symm
  let e := J.toHomeomorph.toOpenPartialHomeomorph
  let V := d.lapse ∘ J
  have jp (x : X) : J x = F.symm (x+a) := rfl
  have js (q : d.carrier) : J.symm q = F q + (-a) := rfl
  have j0 : J 0 = d.pole := by rw [jp,zero_add]; exact F.symm_apply_apply _
  have np (x : X) : J x ≠ d.pole ↔ x≠0 := by rw [←j0]; exact J.injective.ne_iff
  have cj : ContMDiff I I ∞ J := ci.comp (contMDiff_iff_contDiff.mpr
    (contDiff_id.add contDiff_const : ContDiff ℝ ∞ (fun x : X => x+a)))
  have cs : ContMDiff I I ∞ J.symm := (contMDiff_iff_contDiff.mpr
    (contDiff_id.add contDiff_const : ContDiff ℝ ∞ (fun x : X => x+(-a)))).comp cf
  have se : e.source=univ := rfl
  have te : e.target=univ := rfl
  have fully (x v : X) : mfderiv I I F (J x) (mfderiv I I J x v) = v := by
    have comp := mfderiv_comp (I':=I) x (cf.contMDiffAt.mdifferentiableAt (by simp)) (cj.contMDiffAt.mdifferentiableAt (by simp))
    have fa : (F ∘ J) = (fun y : X => y+a) := by funext y; exact F.apply_symm_apply _
    have der : fderiv ℝ (F ∘ J) x = ContinuousLinearMap.id ℝ X := by
      rw [fa]; exact ((hasFDerivAt_id x).add_const a).fderiv
    have c0 := congrArg (fun L : X →L[ℝ] X => L v) comp
    change mfderiv I I (F ∘ J) x v = _ at c0
    rw [mfderiv_eq_fderiv,der] at c0
    exact c0.symm
  have ip (x v w : X) : inner ℝ (mfderiv I I J x v) (mfderiv I I J x w) = inner ℝ v w := by
    have h := ipF (J x) (mfderiv I I J x v) (mfderiv I I J x w)
    exact h.symm.trans (congrArg₂ (fun u t : X => inner ℝ u t) (fully x v) (fully x w))
  have metric (y : X) : riemannianEndCoeffs e y = 1 := by
    ext i j
    change inner ℝ (mfderiv I I J y (EuclideanSpace.single i (1:ℝ))) (mfderiv I I J y (EuclideanSpace.single j (1:ℝ))) = _
    rw [ip]
    simp [EuclideanSpace.inner_single_left,PiLp.single_apply,Matrix.one_apply,eq_comm]
  let σ := e.trans d.physical
  have sσ : σ.source=J ⁻¹' d.physical.source := by
    change (e.trans d.physical).source = _
    rw [OpenPartialHomeomorph.trans_source,se,univ_inter]
    rfl
  have tσ : σ.target=d.physical.target := by
    change (e.trans d.physical).target = _
    rw [OpenPartialHomeomorph.trans_target,te,preimage_univ,inter_univ]
  have phys {x : X} (hx : x∈σ.source) : J x∈ d.physical.source := by change x ∈ J ⁻¹' d.physical.source; rwa [←sσ]
  have dom : σ.source={x | x≠0 ∧ 0<V x} := by
    rw [sσ,d.source]; ext x
    exact and_congr_left (fun _ => np x)
  have isochart : HasStaticSpatialDoubleChart Ω N h V := by
    refine ⟨σ,dom,tσ.trans d.target,?_,?_,?_⟩
    · apply contMDiffOn_iff_contDiffOn.mp
      change ContMDiffOn I I ∞ (d.physical ∘ J) σ.source
      exact d.smoothPhysical.comp cj.contMDiffOn (fun _ hx => phys hx)
    · apply contMDiffOn_iff_contDiffOn.mp
      change ContMDiffOn I I ∞ (J.symm ∘ d.physical.symm) σ.target
      exact cs.comp_contMDiffOn (tσ ▸ d.smoothInverse)
    · intro x hx
      have m := d.physicalMetric (J x) (phys hx)
      refine ⟨m.1,?_⟩
      intro v w
      have diff := (d.smoothPhysical.contMDiffAt (d.physical.open_source.mem_nhds (phys hx))).mdifferentiableAt (by simp)
      have H := mfderiv_comp (I':=I) x diff (cj.contMDiffAt.mdifferentiableAt (by simp))
      have row (v : X) : fderiv ℝ σ x v = mfderiv I I d.physical (J x) (mfderiv I I J x v) := by
        have H' := congrArg (fun L : X →L[ℝ] X => L v) H
        change (mfderiv I I (d.physical ∘ J) x) v = _ at H'
        rw [mfderiv_eq_fderiv] at H'
        exact H'
      change (∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric N h (d.physical (J x)) i j *
        (fderiv ℝ σ x v) i * (fderiv ℝ σ x w) j) = inner ℝ v w
      rw [row v,row w]
      exact (m.2 _ _).trans (ip x v w)
  obtain ⟨b,bne,bz⟩ := d.horizon
  refine ⟨V,J.symm b,isochart,?_,fun x hx => d.lower _ ((np x).mpr hx),?_,?_,?_,?_⟩
  · apply contMDiffOn_iff_contDiffOn.mp
    exact d.smoothLapse.comp (cj.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contMDiffOn (fun x hx => (np x).mpr hx)
  · intro ε he
    obtain ⟨K,hK,decay⟩ := d.asymptote ε he
    obtain ⟨R,hR⟩ := (hK.image J.symm.continuous).isBounded.subset_closedBall (0:X)
    refine ⟨R,fun x hx => decay (J x) ?_⟩
    intro hk
    have inside := hR (show x ∈ J.symm '' K from ⟨J x,hk,J.symm_apply_apply x⟩)
    exact hx.not_ge (by simpa only [Metric.mem_closedBall,dist_zero_right] using inside)
  · apply (np _).mp
    simpa only [J.apply_symm_apply] using bne
  · change d.lapse (J (J.symm b))=0
    rwa [J.apply_symm_apply]
  · intro x nx vx
    have law := d.lapseEquation e cj.contMDiffOn cs.contMDiffOn x (se ▸ mem_univ x) ((np x).mpr nx) vx
    have mat : riemannianEndCoeffs e = (fun _ => 1) := funext metric
    change staticWeightedLapseDivergence (riemannianEndCoeffs e) V x = 0 at law
    rwa [mat,euclid_flux] at law
