-- Prove2me | solution 1 for NoHair.smooth_scalar_flat_atlas_on_one_point_static_completion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T12:51:36.859357+00:00
-- url     : https://prove2.me/submissions/c25da449-b0be-4a9a-9304-e0f5579353dc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_smooth_isometric_extension_of_static_double_metric_and_equations
import Theorems.Thm_NoHair_positive_static_end_chart_realizes_zero_adm_end
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Geometry.Manifold.Instances.Icc
import Definitions.Def_NoHair_staticReflectionAndCap

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

noncomputable section

open UniformSpace Metric
private abbrev X := ADMPoint
private abbrev A := Fin 3
private abbrev I := 𝓘(ℝ,X)
private noncomputable abbrev frameVec (i:A) : X := EuclideanSpace.single i 1

private lemma inner_in_chart {Q:Type} [MetricSpace Q] [ChartedSpace X Q] [IsManifold I ∞ Q]
    [RiemannianBundle (fun q : Q => TangentSpace I q)] (F:X→Q) (x v w:X) :
    (∑ i:A, ∑ j:A, riemannianEndCoeffs F x i j*v i*w j) =
      inner ℝ (mfderiv I I F x v) (mfderiv I I F x w) := by
  let D := mfderiv I I F x
  have rep (v:X) : (∑ i : A, v i • frameVec i)=v := by
    rw [Fin.sum_univ_three]; ext j
    fin_cases j <;> simp +decide [frameVec,EuclideanSpace.single,PiLp.single_apply]
  have dr (v:X) : D v = ∑ i:A, v i • D (frameVec i) := by
    let P : X →ₗ[ℝ] TangentSpace I (F x) := D.toLinearMap
    change P v = ∑ i:A, v i • P (frameVec i)
    calc _ = P (∑ i:A, v i • frameVec i) := congrArg P (rep v).symm
         _ = _ := by simp only [map_sum,map_smul]
  change _ = inner ℝ (D v) (D w)
  rw [dr v,dr w]
  simp only [sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [riemannianEndCoeffs,D,frameVec]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem solution (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h)
    (d : ReflectedStaticDouble Ω N h) (a : StaticMinusPointChart Ω N h)
    (hpositiveEnd : ∃ R : ℝ, 0 < R ∧
      (∀ x : ADMPoint, R < ‖x‖ → ∀ v : ADMPoint, ‖v‖^2 / 4 ≤
        ∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric N h x i j * v i * v j) ∧
      ∀ (γ : ℝ → ADMPoint) (a b : ℝ), a ≤ b → ContDiff ℝ 1 γ →
        (∀ t ∈ Set.Icc a b, R < ‖γ t‖) →
        ‖γ b - γ a‖ ≤ 2 * ∫ t in a..b, Real.sqrt
          (∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric N h (γ t) i j * deriv γ t i * deriv γ t j))
    (hmass : Tendsto (staticADMFlux (staticPositiveMetric N h)) atTop (𝓝 0))
    (p : UniformSpace.Completion d.carrier) (off : ∀ q:d.carrier, (q : UniformSpace.Completion d.carrier) ≠ p)
    (exhaust : ∀ w : UniformSpace.Completion d.carrier, w=p ∨ ∃ q:d.carrier, (q : UniformSpace.Completion d.carrier)=w)
    (e : OpenPartialHomeomorph ADMPoint (UniformSpace.Completion d.carrier))
    (ball : e.source=Metric.ball 0 a.radius) (center : e 0=p)
    (agrees : ∀ y ∈ a.change.source, e y=((d.side false).symm (a.change y) : UniformSpace.Completion d.carrier))
    (compactEnd : ∃ R : ℝ, 0 < R ∧ ∀ t : ℝ, R ≤ t → IsCompact
      (((fun x : ADMPoint => ((d.side true).symm x : UniformSpace.Completion d.carrier)) '' {x : ADMPoint | t < ‖x‖})ᶜ))
    (L : C(UniformSpace.Completion d.carrier, ℝ)) (f : OpenPartialHomeomorph (UniformSpace.Completion d.carrier) ADMPoint)
    (extension : (∀ q : d.carrier, L (q : UniformSpace.Completion d.carrier) = d.lapse q)) (atPole : L p = -1)
    (source : f.source = {z | z ≠ p ∧ 0 < L z}) (target : f.target=Ω)
    (inverse : (∀ x ∈ Ω, f.symm x = ((d.side true).symm x : UniformSpace.Completion d.carrier))) :
    ∃ ch : ChartedSpace ADMPoint (UniformSpace.Completion d.carrier), letI := ch
      ∃ sm : IsManifold 𝓘(ℝ,ADMPoint) ∞ (UniformSpace.Completion d.carrier), letI := sm
      ∃ rb : RiemannianBundle (fun q : (UniformSpace.Completion d.carrier) => TangentSpace 𝓘(ℝ,ADMPoint) q), letI := rb
      IsContMDiffRiemannianBundle 𝓘(ℝ,ADMPoint) ∞ ADMPoint (fun q : (UniformSpace.Completion d.carrier) => TangentSpace 𝓘(ℝ,ADMPoint) q) ∧
      IsRiemannianManifold 𝓘(ℝ,ADMPoint) (UniformSpace.Completion d.carrier) ∧
      HasScalarFlatZeroADMEnd (UniformSpace.Completion d.carrier) ∧ ContMDiffOn 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ℝ) 2 L ({p}ᶜ) ∧
      ContMDiffOn 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ f f.source ∧
      ContMDiffOn 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ f.symm f.target ∧
      (∀ q ∈ f.source, ∀ v w : TangentSpace 𝓘(ℝ,ADMPoint) q, (∑ i : Fin 3, ∑ j : Fin 3,
      staticPositiveMetric N h (f q) i j *
        (fun z : ADMPoint => z i) (mfderiv 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) f q v) *
        (fun z : ADMPoint => z j) (mfderiv 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) f q w)) = inner ℝ v w) ∧
      (∀ e : OpenPartialHomeomorph ADMPoint (UniformSpace.Completion d.carrier),
    ContMDiffOn 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ e e.source →
    ContMDiffOn 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ e.symm e.target →
    ∀ x ∈ e.source, e x ≠ p → L (e x) ≠ 0 →
      staticWeightedLapseDivergence (riemannianEndCoeffs e) (L ∘ e) x = 0) := by
  classical
  obtain ⟨ch,sm,rb,sr,rm,sflat,sl,sf,si,cf,eq⟩ :=
    smooth_isometric_extension_of_static_double_metric_and_equations Ω W N h c d a hpositiveEnd hmass p off exhaust e ball center agrees compactEnd
      L f extension atPole source target inverse
  letI := ch
  letI := sm
  letI := rb
  letI := sr
  letI := rm
  have tails : ∃ A:ℝ, 0<A ∧ ∀ t:ℝ, A≤t → IsCompact (f.symm '' {x:X | t<‖x‖})ᶜ := by
    obtain ⟨R,rp,ck⟩ := compactEnd
    obtain ⟨B,hB⟩ := c.compactComplement.isBounded.exists_norm_le
    refine ⟨max R B,rp.trans_le (le_max_left _ _),?_⟩
    intro t ht
    have ev : EqOn (f.symm : X → Completion d.carrier) (fun x:X => ((d.side true).symm x : Completion d.carrier)) {x:X | t<‖x‖} := by
      intro x hx
      apply inverse x
      by_contra bad
      exact (((le_max_right R B).trans ht).trans_lt hx).not_ge (hB x bad)
    rw [ev.image_eq]
    exact ck t ((le_max_left _ _).trans ht)
  have ed := positive_static_end_chart_realizes_zero_adm_end Ω W N h c (Completion d.carrier)
    f target sf si cf sflat tails hmass
  refine ⟨ch,sm,rb,sr,rm,ed,sl,sf,si,?_,eq⟩
  intro q hq v w
  have fq := f.map_source hq
  have ox : f q ∈ Ω := (Set.ext_iff.mp target (f q)).mp fq
  have fd := (sf.contMDiffAt (f.open_source.mem_nhds hq)).mdifferentiableAt (by simp : (∞:ℕ∞ω)≠0)
  have id' := (si.contMDiffAt (f.open_target.mem_nhds fq)).mdifferentiableAt (by simp : (∞:ℕ∞ω)≠0)
  have de := mfderiv_comp (I':=I) q id' fd
  have loc : (f.symm ∘ f) =ᶠ[𝓝 q] id :=
    (show ∀ᶠ z in 𝓝 q, z∈f.source from f.open_source.mem_nhds hq).mono (fun z hz => f.left_inv hz)
  rw [loc.mfderiv_eq,mfderiv_id] at de
  have back (v : TangentSpace I q) : mfderiv I I f.symm (f q) (mfderiv I I f q v) = v :=
    congrArg (fun H : X →L[ℝ] X => H v) de.symm
  rw [←cf (f q) ox,inner_in_chart,back,back]
  first
  | rw [f.left_inv hq]
  | exact congrArg (fun z : Completion d.carrier => @inner ℝ (TangentSpace I z) (by infer_instance) v w) (f.left_inv hq)
