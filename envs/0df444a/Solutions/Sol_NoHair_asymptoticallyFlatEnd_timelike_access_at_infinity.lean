-- Prove2me | solution 1 for NoHair.asymptoticallyFlatEnd_timelike_access_at_infinity
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T09:14:34.366962+00:00
-- url     : https://prove2.me/submissions/715cc25e-dc23-4040-b939-570d1a1223f1

import Theorems.Thm_NoHair_asymptoticallyFlatEnd_coordinate_cones
import Definitions.Def_NoHair_chronologyAtInfinity

open NoHair Set Filter
open scoped ContDiff Manifold BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
private abbrev I4 := 𝓘(ℝ,E4)
private abbrev I1 := 𝓘(ℝ,ℝ)

private theorem exterior_open (R : ℝ) : IsOpen (exteriorRegion R) :=
  isOpen_lt continuous_const (by unfold spatialRadius; fun_prop)

private theorem radius_sq (z : E4) : spatialRadius z ^ 2 = z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- A path with the same large spatial displacement in both parameter directions. -/
private def bend (y : E4) (s : ℝ) : E4 :=
  y + (4*s+4*s^3/3) • coordBasis 0 + ((if 0 ≤ y 1 then 1 else -1 : ℝ)*s^2) • coordBasis 1

private def bendVel (y : E4) (s : ℝ) : E4 :=
  (4*(1+s^2)) • coordBasis 0 + (2*(if 0 ≤ y 1 then 1 else -1 : ℝ)*s) • coordBasis 1

private theorem bend_deriv (y : E4) (s : ℝ) : HasDerivAt (bend y) (bendVel y s) s := by
  let e : ℝ := if 0 ≤ y 1 then 1 else -1
  have ht : HasDerivAt (fun u : ℝ => 4*u+4*u^3/3) (4*(1+s^2)) s := by
    have h := ((hasDerivAt_id s).const_mul 4).add (((hasDerivAt_pow 3 s).const_mul 4).div_const 3)
    exact h.congr_deriv (by norm_num <;> ring)
  have hr : HasDerivAt (fun u : ℝ => e*u^2) (2*e*s) s := by
    exact ((hasDerivAt_pow 2 s).const_mul e).congr_deriv (by norm_num <;> ring)
  exact ((ht.smul_const (coordBasis 0)).const_add y).add (hr.smul_const (coordBasis 1))

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
    (p q : ℝ) (hne : q-p ≠ 0) (hneg : ∀ u, g (γ u) (velocity γ u) (velocity γ u) < 0)
    (hdir : ∀ u, (q-p) * g (γ u) (velocity γ u) (T (γ u)) < 0) :
    γ q ∈ chronoFuture g T univ (γ p) := by
  let l := fun t : ℝ => p+(q-p)*t
  have hl (t : ℝ) : HasDerivAt l (q-p) t := by
    simpa [l] using (((hasDerivAt_id t).const_mul (q-p)).const_add p)
  have hs : ContMDiff I1 I1 1 l := (show ContDiff ℝ 1 l by unfold l; fun_prop).contMDiff
  refine ⟨γ ∘ l,⟨hγ.comp hs,?_⟩,by simp [l],by simp [l]⟩
  intro t _
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
  exact ⟨by nlinarith only [mul_neg_of_pos_of_neg (sq_pos_iff.mpr hne) (hneg (l t))],hdir (l t)⟩
end Manifold

theorem solution {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ, E4) ∞ M] {g F : BilinField M} {φ : ℝ → M → M}
    (E : AsymptoticallyFlatEnd g F φ)
    (hg : IsLorentzian g) (T : VecField M) (hT : IsTimeOrientation g T)
    (R₀ : ℝ) (hR : E.R ≤ R₀) (hC : 16 * |E.C| ≤ R₀) :
    let A := fun R : ℝ => E.ψ '' exteriorRegion R
    A R₀ ⊆ domainOfOuterCommunicationsAtInfinity g T A R₀ := by
  change E.ψ '' exteriorRegion R₀ ⊆ domainOfOuterCommunicationsAtInfinity g T
    (fun R => E.ψ '' exteriorRegion R) R₀
  rintro _ ⟨y,hy,rfl⟩
  let c := bend y
  let γ := E.ψ ∘ c
  let v := bendVel y
  let L := fun t => (mfderiv I4 I4 E.ψ (c t) : E4 →L[ℝ] E4)
  have hcR (t : ℝ) : R₀ < spatialRadius (c t) := lt_of_lt_of_le hy (bend_geometry y t).1
  have hc (t : ℝ) : c t ∈ exteriorRegion E.R := lt_of_le_of_lt hR (hcR t)
  have hfar (t : ℝ) : 16 * |E.C| ≤ spatialRadius (c t) := hC.trans (hcR t).le
  obtain ⟨χ,_,_,_,_,hψ,_⟩ := E.diffeo
  have hcd : ContDiff ℝ 1 c := by
    change ContDiff ℝ 1 (bend y)
    unfold bend
    fun_prop
  have hψs (t : ℝ) : ContMDiffAt I4 I4 ∞ E.ψ (c t) :=
    (hψ (c t) (hc t)).contMDiffAt ((exterior_open E.R).mem_nhds (hc t))
  have hγ : ContMDiff I1 I4 1 γ := fun t =>
    ((hψs t).of_le (by simp)).comp t (hcd.contMDiff t)
  have hv (t : ℝ) : velocity γ t = L t (v t) := by
    unfold velocity
    rw [show γ = E.ψ ∘ c from rfl, mfderiv_comp (I' := I4) t
      ((hψs t).mdifferentiableAt (by simp)) (bend_deriv y t).differentiableAt.mdifferentiableAt]
    change L t ((mfderiv I1 I4 c t : ℝ →L[ℝ] E4) 1) = L t (v t)
    rw [mfderiv_eq_fderiv]
    exact congrArg (L t) (bend_deriv y t).deriv
  have v0 (t : ℝ) : 0 < v t 0 := by
    have h : v t 0 = 4*(1+t^2) := by by_cases hh : 0 ≤ y 1 <;> simp [v,bendVel,coordBasis,hh]
    rw [h]
    positivity
  have hneg (t : ℝ) : g (γ t) (velocity γ t) (velocity γ t) < 0 := by
    rw [hv]
    have h := (asymptoticallyFlatEnd_coordinate_cones E hg (c t) (hc t) (hfar t)).2.1
    apply h (4*(1+t^2)) (2*(if 0 ≤ y 1 then 1 else -1 : ℝ)*t) (by positivity)
    have he : |(if 0 ≤ y 1 then 1 else -1 : ℝ)| = 1 := by split <;> norm_num
    rw [abs_mul,abs_mul,he]
    norm_num
    nlinarith only [sq_nonneg (|t| - 1),sq_abs t,sq_nonneg t]
  obtain ⟨W,hW,hInv⟩ := inverse_vector E T hT c hc hγ.continuous
  have htim (t : ℝ) : g (γ t) (L t (W t)) (L t (W t)) < 0 := by
    rw [show L t (W t) = T (γ t) from hInv t]
    exact hT.2 _
  have W0 (t : ℝ) : W t 0 ≠ 0 := by
    intro hz
    exact (not_lt_of_ge ((asymptoticallyFlatEnd_coordinate_cones E hg (c t) (hc t) (hfar t)).1 (W t) hz)) (htim t)
  have cross (t : ℝ) : g (γ t) (velocity γ t) (T (γ t)) * ((v t 0)*(W t 0)) < 0 := by
    have hnv : g (γ t) (L t (v t)) (L t (v t)) < 0 := by rw [←hv]; exact hneg t
    have h := (asymptoticallyFlatEnd_coordinate_cones E hg (c t) (hc t) (hfar t)).2.2
      (v t) (W t) hnv (htim t)
    change g (γ t) (L t (v t)) (L t (W t)) * (v t 0) * (W t 0) < 0 at h
    rwa [←hv t,show L t (W t) = T (γ t) from hInv t,mul_assoc] at h
  have hW0 : Continuous (fun t => W t 0) := by fun_prop
  have hsign : (∀ t, g (γ t) (velocity γ t) (T (γ t)) < 0) ∨
      (∀ t, 0 < g (γ t) (velocity γ t) (T (γ t))) := by
    rcases isPreconnected_univ.mapsTo_Ioi_or_Iio hW0.continuousOn (fun t _ => W0 t) with h | h
    · left
      intro t
      have hw : 0 < W t 0 := h (mem_univ t)
      by_contra! hn
      exact (not_lt_of_ge (mul_nonneg hn (mul_pos (v0 t) hw).le)) (cross t)
    · right
      intro t
      have hw : W t 0 < 0 := h (mem_univ t)
      by_contra! hn
      exact (not_lt_of_ge (mul_nonneg_of_nonpos_of_nonpos hn (mul_neg_of_pos_of_neg (v0 t) hw).le)) (cross t)
  have hzero : γ 0 = E.ψ y := by simp [γ,c,bend]
  have access (R : ℝ) :
      γ 0 ∈ chronoFutureSet g T (E.ψ '' exteriorRegion R) ∧
      γ 0 ∈ chronoPastSet g T (E.ψ '' exteriorRegion R) := by
    let N := |R| + 2
    have hN : 0 < N := by dsimp [N]; positivity
    have hRN : R < N^2 := by
      have h1 : 1 < N := by dsimp [N]; linarith [abs_nonneg R]
      have h2 : R < N := by dsimp [N]; linarith [le_abs_self R]
      nlinarith only [h1,h2,mul_nonneg hN.le (sub_nonneg.mpr h1.le)]
    have hplus : γ N ∈ E.ψ '' exteriorRegion R := ⟨c N,hRN.trans_le (bend_geometry y N).2,rfl⟩
    have hminus : γ (-N) ∈ E.ψ '' exteriorRegion R :=
      ⟨c (-N),hRN.trans_le (by simpa using (bend_geometry y (-N)).2),rfl⟩
    rcases hsign with hf | hf
    · have hp : 0 < 0-(-N) := by linarith
      have hq : 0 < N-0 := by linarith
      exact ⟨mem_iUnion₂.mpr ⟨_,hminus,signal_segment T γ hγ (-N) 0 hp.ne' hneg (fun t => mul_neg_of_pos_of_neg hp (hf t))⟩,
        mem_iUnion₂.mpr ⟨_,hplus,signal_segment T γ hγ 0 N hq.ne' hneg (fun t => mul_neg_of_pos_of_neg hq (hf t))⟩⟩
    · have hp : 0-N < 0 := by linarith
      have hq : -N-0 < 0 := by linarith
      exact ⟨mem_iUnion₂.mpr ⟨_,hplus,signal_segment T γ hγ N 0 hp.ne hneg (fun t => mul_neg_of_neg_of_pos hp (hf t))⟩,
        mem_iUnion₂.mpr ⟨_,hminus,signal_segment T γ hγ 0 (-N) hq.ne hneg (fun t => mul_neg_of_neg_of_pos hq (hf t))⟩⟩
  rw [←hzero]
  exact ⟨fun R _ => (access R).1,fun R _ => (access R).2⟩
