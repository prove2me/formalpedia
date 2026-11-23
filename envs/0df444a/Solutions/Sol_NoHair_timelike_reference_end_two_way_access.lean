-- Prove2me | solution 1 for NoHair.timelike_reference_end_two_way_access
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T09:44:04.227291+00:00
-- url     : https://prove2.me/submissions/1a10eb39-44c8-4612-b2db-b41f275f1659

import Theorems.Thm_NoHair_stationary_end_pullback_metric
import Definitions.Def_NoHair_chronologyAtInfinity

open NoHair Set Filter
open scoped ContDiff Manifold BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
private abbrev I4 := 𝓘(ℝ,E4)
private abbrev I1 := 𝓘(ℝ,ℝ)

private theorem exterior_open (R : ℝ) : IsOpen (exteriorRegion R) :=
  isOpen_lt continuous_const (by unfold spatialRadius; fun_prop)

private theorem radius_sq (z : E4) : spatialRadius z ^ 2 = z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 :=
  Real.sq_sqrt (by positivity)

private def bend (y : E4) (s : ℝ) : E4 :=
  y + ((if 0 ≤ y 1 then 1 else -1 : ℝ)*s^2) • coordBasis 1

private theorem time_radius (y : E4) (s : ℝ) : spatialRadius (y+s • coordBasis 0) = spatialRadius y := by
  simp [spatialRadius,coordBasis]

private theorem bend_geometry (y : E4) (s : ℝ) :
    spatialRadius y ≤ spatialRadius (bend y s) ∧ s^2 ≤ spatialRadius (bend y s) := by
  let e : ℝ := if 0 ≤ y 1 then 1 else -1
  have c1 : bend y s 1 = y 1 + e*s^2 := by by_cases h : 0 ≤ y 1 <;> simp [bend,e,h,coordBasis]
  have c2 : bend y s 2 = y 2 := by by_cases h : 0 ≤ y 1 <;> simp [bend,h,coordBasis]
  have c3 : bend y s 3 = y 3 := by by_cases h : 0 ≤ y 1 <;> simp [bend,h,coordBasis]
  have hsq := radius_sq (bend y s)
  rw [c1,c2,c3] at hsq
  have h₁ : |y 1| ≤ |y 1 + e*s^2| ∧ s^2 ≤ |y 1 + e*s^2| := by
    by_cases h : 0 ≤ y 1
    · simp only [e,if_pos h,one_mul,abs_of_nonneg h,abs_of_nonneg (add_nonneg h (sq_nonneg s))]
      constructor <;> linarith [sq_nonneg s]
    · have hsum : y 1 + (-1)*s^2 ≤ 0 := by linarith [sq_nonneg s]
      simp only [e,if_neg h,abs_of_nonpos (le_of_not_ge h),abs_of_nonpos hsum]
      constructor <;> linarith [sq_nonneg s]
  constructor
  · apply (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mp
    have hs := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr h₁.1
    rw [sq_abs,sq_abs] at hs
    change spatialRadius y ^ 2 ≤ spatialRadius (bend y s) ^ 2
    linarith [radius_sq y]
  · apply h₁.2.trans
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs]
    change (y 1 + e*s^2)^2 ≤ spatialRadius (bend y s)^2
    linarith [sq_nonneg (y 2),sq_nonneg (y 3)]

section Manifold
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M] [IsManifold I4 ∞ M]
variable {g F : BilinField M} {φ : ℝ → M → M}

private theorem inverse_vector (E : AsymptoticallyFlatEnd g F φ) (T : VecField M)
    (hT : IsTimeOrientation g T) (c : ℝ → E4) (hc : ∀ t, c t ∈ exteriorRegion E.R)
    (hγ : Continuous (E.ψ ∘ c)) :
    ∃ W : ℝ → E4, Continuous W ∧ ∀ t,
      (mfderiv I4 I4 E.ψ (c t)) (W t) = T (E.ψ (c t)) := by
  obtain ⟨χ,hmap,_,hl,hr,hψ,hχ⟩ := E.diffeo
  let z := E.ψ ∘ c
  let V := fun t => (⟨z t,T (z t)⟩ : TangentBundle I4 M)
  have hV : Continuous V := hT.1.comp hγ
  have ht := hχ.continuousOn_tangentMapWithin (by simp) E.isOpen_image.uniqueMDiffOn
  have hmapV : Continuous ((tangentMapWithin I4 I4 χ E.region) ∘ V) :=
    ht.comp_continuous hV (fun t => hmap (hc t))
  let W := fun t => (tangentMapWithin I4 I4 χ E.region (V t)).2
  have hW : Continuous W :=
    (contMDiff_snd_tangentBundle_modelSpace E4 I4 (n := 1)).continuous.comp hmapV
  refine ⟨W,hW,?_⟩
  intro t
  have him : z t ∈ E.region := hmap (hc t)
  have hinv : χ (z t) = c t := hl (hc t)
  have hψd := ((hψ (c t) (hc t)).contMDiffAt ((exterior_open E.R).mem_nhds (hc t))).mdifferentiableAt (by simp)
  have hχd := ((hχ (z t) him).contMDiffAt (E.isOpen_image.mem_nhds him)).mdifferentiableAt (by simp)
  have hψd' : MDifferentiableAt I4 I4 E.ψ (χ (z t)) := hinv.symm ▸ hψd
  have comp := mfderiv_comp (I' := I4) (z t) hψd' hχd
  have germ : E.ψ ∘ χ =ᶠ[𝓝 (z t)] id :=
    Filter.eventuallyEq_of_mem (E.isOpen_image.mem_nhds him) (fun x hx => hr hx)
  rw [germ.mfderiv_eq,mfderiv_id,hinv] at comp
  change (mfderiv I4 I4 E.ψ (c t) : E4 →L[ℝ] E4) ((mfderivWithin I4 I4 χ E.region (z t) : E4 →L[ℝ] E4) (T (z t))) = T (z t)
  have hnh : E.region ∈ 𝓝 (z t) := E.isOpen_image.mem_nhds him
  rw [mfderivWithin_of_mem_nhds hnh]
  exact (congrArg (fun L : E4 →L[ℝ] E4 => L (T (z t))) comp).symm

private theorem signal_segment (T : VecField M) (γ : ℝ → M) (hγ : ContMDiff I1 I4 1 γ)
    (p q : ℝ) (hp : p ∈ Icc (-1:ℝ) 1) (hq : q ∈ Icc (-1:ℝ) 1)
    (hne : q-p ≠ 0) (hneg : ∀ u ∈ Icc (-1:ℝ) 1, g (γ u) (velocity γ u) (velocity γ u) < 0)
    (hdir : ∀ u ∈ Icc (-1:ℝ) 1, (q-p) * g (γ u) (velocity γ u) (T (γ u)) < 0) :
    γ q ∈ chronoFuture g T univ (γ p) := by
  let l := fun t : ℝ => p+(q-p)*t
  have hl (t : ℝ) : HasDerivAt l (q-p) t := by
    simpa [l] using (((hasDerivAt_id t).const_mul (q-p)).const_add p)
  have hs : ContMDiff I1 I1 1 l := (show ContDiff ℝ 1 l by unfold l; fun_prop).contMDiff
  refine ⟨γ ∘ l,⟨hγ.comp hs,?_⟩,by simp [l],by simp [l]⟩
  intro t ht
  have hseg : l t ∈ Icc (-1:ℝ) 1 := by
    change -1 ≤ p+(q-p)*t ∧ p+(q-p)*t ≤ 1
    constructor
    · nlinarith only [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hp.1),mul_nonneg ht.1 (sub_nonneg.mpr hq.1)]
    · nlinarith only [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hp.2),mul_nonneg ht.1 (sub_nonneg.mpr hq.2)]
  refine ⟨mem_univ _,?_⟩
  have hd : (mfderiv I1 I1 l t : ℝ →L[ℝ] ℝ) 1 = q-p := by
    rw [mfderiv_eq_fderiv]
    exact (hl t).deriv
  have hv : velocity (γ ∘ l) t = (q-p) • velocity γ (l t) := by
    unfold velocity
    rw [mfderiv_comp (I' := I1) t ((hγ (l t)).mdifferentiableAt (by simp)) ((hs t).mdifferentiableAt (by simp))]
    change mfderiv I1 I4 γ (l t) ((mfderiv I1 I1 l t) 1) = _
    rw [hd]
    simpa only [smul_eq_mul,mul_one] using (mfderiv I1 I4 γ (l t)).map_smul (q-p) (1:ℝ)
  rw [hv]
  change g (γ (l t)) ((q-p) • velocity γ (l t)) ((q-p) • velocity γ (l t)) < 0 ∧
    g (γ (l t)) ((q-p) • velocity γ (l t)) (T (γ (l t))) < 0
  simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
  exact ⟨by nlinarith only [mul_neg_of_pos_of_neg (sq_pos_iff.mpr hne) (hneg (l t) hseg)],hdir (l t) hseg⟩

private theorem timelike_inner_ne {g : BilinField M} (hg : IsLorentzian g) {x : M}
    {v w : TangentSpace I4 x} (hv : g x v v < 0) (hw : g x w w < 0) : g x v w ≠ 0 := by
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
  intro h
  have hzero : G v w = 0 := h
  simpa [hzero] using (pair v w hv hw)

end Manifold

theorem solution {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ, E4) ∞ M] {g F : BilinField M} {φ : ℝ → M → M}
    (E : AsymptoticallyFlatEnd g F φ) (hg : IsLorentzian g) (hs : IsSmoothBilinField g)
    (T : VecField M) (hT : IsTimeOrientation g T) (hφ : IsSymmetryFlow g F φ)
    (hK : ∀ x ∈ E.region, g x (flowGenerator φ x) (flowGenerator φ x) < 0) :
    E.region ⊆ domainOfOuterCommunicationsAtInfinity g T (fun R => E.ψ '' exteriorRegion R) E.R := by
  obtain ⟨hB,htime,hgen⟩ := stationary_end_pullback_metric E hs hφ
  let L := fun z => (mfderiv I4 I4 E.ψ z : E4 →L[ℝ] E4)
  let B := fun (z v w : E4) => g (E.ψ z) (L z v) (L z w)
  change ContinuousOn (fun z : E4 × (E4 × E4) => B z.1 z.2.1 z.2.2) (exteriorRegion E.R ×ˢ univ) at hB
  change ∀ z ∈ exteriorRegion E.R, ∀ (s : ℝ) (v w : E4), B (z+s • coordBasis 0) v w = B z v w at htime
  rintro _ ⟨y,hy,rfl⟩
  let e : ℝ := if 0 ≤ y 1 then 1 else -1
  have access (R : ℝ) : E.ψ y ∈ chronoFutureSet g T (E.ψ '' exteriorRegion R) ∧
      E.ψ y ∈ chronoPastSet g T (E.ψ '' exteriorRegion R) := by
    let N := |R|+2
    have hN : 0 < N := by dsimp [N]; positivity
    have hRN : R < N^2 := by
      have h1 : 1 < N := by dsimp [N]; linarith [abs_nonneg R]
      have h2 : R < N := by dsimp [N]; linarith [le_abs_self R]
      nlinarith only [h1,h2,mul_nonneg hN.le (sub_nonneg.mpr h1.le)]
    let b := fun t : ℝ => bend y (N*t)
    let k := fun t : ℝ => 2*e*N^2*t
    let V := fun d t : ℝ => coordBasis 0 + (d*k t) • coordBasis 1
    have bh (t : ℝ) : b t ∈ exteriorRegion E.R :=
      lt_of_lt_of_le hy (bend_geometry y (N*t)).1
    have bc : Continuous b := by unfold b bend; fun_prop
    let X := fun z : ℝ × ℝ => (b z.2,V z.1 z.2,V z.1 z.2)
    have xc : Continuous X := by dsimp [X,V,k]; fun_prop
    have cform : Continuous (fun z : ℝ × ℝ => B (b z.2) (V z.1 z.2) (V z.1 z.2)) :=
      hB.comp_continuous xc (fun z => ⟨bh z.2,mem_univ _⟩)
    have small : ∀ᶠ d : ℝ in 𝓝 0, ∀ t ∈ Icc (-1:ℝ) 1, B (b t) (V d t) (V d t) < 0 := by
      apply isCompact_Icc.eventually_forall_of_forall_eventually
      intro t _
      have neg := hK (E.ψ (b t)) ⟨_,bh t,rfl⟩
      rw [hgen _ (bh t)] at neg
      have at0 : B (b t) (V 0 t) (V 0 t) < 0 := by simpa [V,B,L] using neg
      exact (cform.continuousAt (x := ((0:ℝ),t))).eventually_lt continuousAt_const at0
    obtain ⟨ε,hε,heps⟩ := Metric.eventually_nhds_iff.mp small
    let d := ε/2
    have hd : 0 < d := by dsimp [d]; positivity
    have hclose : dist d 0 < ε := by rw [Real.dist_eq,sub_zero,abs_of_pos hd]; dsimp [d]; linarith
    have q0 := heps hclose
    let c := fun t : ℝ => b t + (d⁻¹*t) • coordBasis 0
    let v := fun t : ℝ => d⁻¹ • V d t
    let γ := E.ψ ∘ c
    have hrad (t : ℝ) : spatialRadius (c t) = spatialRadius (b t) := time_radius _ _
    have hc (t : ℝ) : c t ∈ exteriorRegion E.R := by change E.R < spatialRadius (c t); rw [hrad]; exact bh t
    have cd : ContDiff ℝ 1 c := by dsimp [c,b,bend]; fun_prop
    obtain ⟨χ,_,_,_,_,hψ,_⟩ := E.diffeo
    have ps (t : ℝ) := (hψ (c t) (hc t)).contMDiffAt ((exterior_open E.R).mem_nhds (hc t))
    have hγ : ContMDiff I1 I4 1 γ := fun t => ((ps t).of_le (by simp)).comp t (cd.contMDiff t)
    have jet (t : ℝ) : HasDerivAt c (v t) t := by
      have ns : HasDerivAt (fun s : ℝ => N*s) N t := by simpa using (hasDerivAt_id t).const_mul N
      have sq : HasDerivAt (fun s : ℝ => e*(N*s)^2) (k t) t := by
        exact ((ns.pow 2).const_mul e).congr_deriv (by dsimp [k]; ring)
      have tt : HasDerivAt (fun s : ℝ => d⁻¹*s) d⁻¹ t := by simpa using (hasDerivAt_id t).const_mul d⁻¹
      have h := (((sq.smul_const (coordBasis 1)).const_add y).add (tt.smul_const (coordBasis 0)))
      apply h.congr_deriv
      simp [v,V,smul_add,smul_smul,←mul_assoc,hd.ne',add_comm]
    have vel (t : ℝ) : velocity γ t = L (c t) (v t) := by
      unfold velocity
      rw [show γ = E.ψ ∘ c from rfl,mfderiv_comp (I' := I4) t ((ps t).mdifferentiableAt (by simp)) (jet t).differentiableAt.mdifferentiableAt]
      change L (c t) ((mfderiv I1 I4 c t : ℝ →L[ℝ] E4) 1) = L (c t) (v t)
      rw [mfderiv_eq_fderiv]
      exact congrArg _ (jet t).deriv
    have hneg (t : ℝ) (ht : t ∈ Icc (-1:ℝ) 1) : g (γ t) (velocity γ t) (velocity γ t) < 0 := by
      rw [vel]
      change B (b t + (d⁻¹*t) • coordBasis 0) (v t) (v t) < 0
      rw [htime _ (bh t)]
      have hh : 0 < d⁻¹ := inv_pos.mpr hd
      change g (E.ψ (b t)) (L (b t) (d⁻¹ • V d t)) (L (b t) (d⁻¹ • V d t)) < 0
      simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
      exact mul_neg_of_pos_of_neg hh (mul_neg_of_pos_of_neg hh (q0 t ht))
    obtain ⟨W,hW,hinv⟩ := inverse_vector E T hT c hc hγ.continuous
    let f := fun t => g (γ t) (velocity γ t) (T (γ t))
    have vc : Continuous v := by dsimp [v,V,k]; fun_prop
    have fc : Continuous f := by
      have cW : Continuous (fun t => (c t,v t,W t)) := cd.continuous.prodMk (vc.prodMk hW)
      have hcomp := hB.comp_continuous cW (fun t => ⟨hc t,mem_univ _⟩)
      apply hcomp.congr
      intro t
      change B (c t) (v t) (W t) = f t
      unfold f B
      rw [vel,show L (c t) (W t) = T (γ t) from hinv t]
      rfl
    have hn (t : ℝ) (ht : t ∈ Icc (-1:ℝ) 1) : f t ≠ 0 := timelike_inner_ne hg (hneg t ht) (hT.2 (γ t))
    have signs := isPreconnected_Icc.mapsTo_Ioi_or_Iio fc.continuousOn hn
    have zero : γ 0 = E.ψ y := by simp [γ,c,b,bend]
    have plus : γ 1 ∈ E.ψ '' exteriorRegion R := by
      refine ⟨c 1,?_,rfl⟩
      change R < spatialRadius (c 1)
      rw [hrad]
      simpa [b] using hRN.trans_le (bend_geometry y N).2
    have minus : γ (-1) ∈ E.ψ '' exteriorRegion R := by
      refine ⟨c (-1),?_,rfl⟩
      change R < spatialRadius (c (-1))
      rw [hrad]
      have h : N^2 ≤ spatialRadius (bend y (-N)) := by simpa using (bend_geometry y (-N)).2
      simpa [b] using hRN.trans_le h
    rw [←zero]
    rcases signs with hpos | hnegdir
    · exact ⟨mem_iUnion₂.mpr ⟨_,plus,signal_segment T γ hγ 1 0 (by norm_num) (by norm_num) (by norm_num) hneg
          (fun t ht => mul_neg_of_neg_of_pos (by norm_num) (hpos ht))⟩,
        mem_iUnion₂.mpr ⟨_,minus,signal_segment T γ hγ 0 (-1) (by norm_num) (by norm_num) (by norm_num) hneg
          (fun t ht => mul_neg_of_neg_of_pos (by norm_num) (hpos ht))⟩⟩
    · exact ⟨mem_iUnion₂.mpr ⟨_,minus,signal_segment T γ hγ (-1) 0 (by norm_num) (by norm_num) (by norm_num) hneg
          (fun t ht => mul_neg_of_pos_of_neg (by norm_num) (hnegdir ht))⟩,
        mem_iUnion₂.mpr ⟨_,plus,signal_segment T γ hγ 0 1 (by norm_num) (by norm_num) (by norm_num) hneg
          (fun t ht => mul_neg_of_pos_of_neg (by norm_num) (hnegdir ht))⟩⟩
  exact ⟨fun R _ => (access R).1,fun R _ => (access R).2⟩
