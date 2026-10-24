-- Prove2me | solution 1 for OAI.SplitTangent.RationalFamily.integrable_both_of_submersive
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T19:38:32.340519+00:00
-- url     : https://prove2.me/submissions/34fafd9f-3c43-4869-8199-803cfa918d41

import Mathlib
import Definitions.Def_SplitTangentIntegrability
import Definitions.Def_OAIQWST002
import Theorems.Thm_OAI_SplitTangent_TangentSplitting_exists_projective_tangent_box

section
-- module Solutions.OAIQW_SplitTangent.BracketIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bracket Integrability. -/

noncomputable section
open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle

universe u
namespace SplitTangent
section

attribute [instance] ComplexManifold.topology ComplexManifold.charts
  ComplexManifold.holomorphicAtlas ComplexManifold.hausdorff
  ComplexManifold.secondCountable

open Filter Topology
namespace TangentSplitting
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)



theorem integrable_first_of_bracketTensor_eq_zero
    (hB : ∀ x, S.bracketTensor x = 0) : Integrable X S.first := by
  intro U hU V W hV hW hPV hPW x hx
  have hV' := (hV x hx).contMDiffAt (hU.mem_nhds hx)
  have hW' := (hW x hx).contMDiffAt (hU.mem_nhds hx)
  have he := S.bracketTensor_apply (hV'.mdifferentiableAt (by simp))
    (hW'.mdifferentiableAt (by simp))
  rw [hB x] at he
  have hEV : S.projectField V =ᶠ[nhds x] V :=
    Filter.eventually_of_mem (hU.mem_nhds hx) (fun y hy => (S.mem_first_iff y _).mp (hPV y hy))
  have hEW : S.projectField W =ᶠ[nhds x] W :=
    Filter.eventually_of_mem (hU.mem_nhds hx) (fun y hy => (S.mem_first_iff y _).mp (hPW y hy))
  have hb := hEV.mlieBracketWithin_vectorField_eq_nhds (I := ModelWithCorners X)
    (s := Set.univ) hEW
  rw [VectorField.mlieBracketWithin_univ, VectorField.mlieBracketWithin_univ] at hb
  rw [mem_first_iff_complement_eq_zero, VectorField.mlieBracketWithin_of_isOpen hU hx]
  simpa only [bracketOperation, hb, zero_apply] using he.symm



end TangentSplitting

namespace AnalyticContinuation

variable {M E F : Type*} [TopologicalSpace M] [PreconnectedSpace M]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

 

theorem eq_univ_of_local_analytic_zero_locus {Z : Set M}
    (hlocal : ∀ x : M, ∃ e : OpenPartialHomeomorph M E, x ∈ e.source ∧
      ∃ f : E → F, AnalyticOnNhd ℂ f e.target ∧
        ∀ y ∈ e.source, y ∈ Z ↔ f (e y) = 0)
    (hne : (interior Z).Nonempty) : Z = univ := by
  have hc : IsClosed (interior Z) := by
    apply isClosed_of_closure_subset
    intro x hx
    obtain ⟨e, hxe, f, hf, he⟩ := hlocal x
    obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp e.open_target (e x) (e.map_source hxe)
    let U := e.source ∩ e ⁻¹' Metric.ball (e x) r
    have hU : IsOpen U := e.isOpen_inter_preimage Metric.isOpen_ball
    have hxU : x ∈ U := ⟨hxe, Metric.mem_ball_self hr⟩
    obtain ⟨y, hyU, hyI⟩ := mem_closure_iff.mp hx U hU hxU
    have hyE : e y ∈ Metric.ball (e x) r := hyU.2
    have him : IsOpen (e '' (U ∩ interior Z)) :=
      e.isOpen_image_of_subset_source (hU.inter isOpen_interior)
        (fun z hz => hz.1.1)
    have hey : e y ∈ e '' (U ∩ interior Z) := ⟨y,⟨hyU,hyI⟩,rfl⟩
    have hzero : f =ᶠ[nhds (e y)] 0 := by
      apply Filter.eventually_of_mem (him.mem_nhds hey)
      rintro z ⟨a,⟨haU,haI⟩,rfl⟩
      exact (he a haU.1).mp (interior_subset haI)
    have hball := (hf.mono hrsub).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (e x) r).isPreconnected hyE hzero
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset (hU.mem_nhds hxU)
    intro z hz
    exact (he z hz.1).mpr (hball hz.2)
  have hI : interior Z = univ := (show IsClopen (interior Z) from ⟨hc,isOpen_interior⟩).eq_univ hne
  exact univ_subset_iff.mp (hI ▸ (interior_subset : interior Z ⊆ Z))

end AnalyticContinuation

namespace TangentSplitting
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

 

theorem bracketTensor_local_analytic_zero_locus (x : X.Carrier) :
    ∃ e : OpenPartialHomeomorph X.Carrier (Model X), x ∈ e.source ∧
      ∃ f : Model X → (Fin X.dim → Fin X.dim → Model X),
        AnalyticOnNhd ℂ f e.target ∧
        ∀ y ∈ e.source, S.bracketTensor y = 0 ↔ f (e y) = 0 := by
  let t := trivializationAt (Model X) (Tangent X) x
  let b := Pi.basisFun ℂ (Fin X.dim)
  let c := chartAt (Model X) x
  let e := c.restr t.baseSet
  let H := fun (y : X.Carrier) (i j : Fin X.dim) =>
    (t ⟨y,S.bracketTensor y (t.localFrame b i y) (t.localFrame b j y)⟩).2
  have hframe (i : Fin X.dim) : HolomorphicSectionOn X (t.localFrame b i) t.baseSet :=
    t.contMDiffOn_localFrame_baseSet ω b i
  have hH (i j : Fin X.dim) : ContMDiffOn (ModelWithCorners X) 𝓘(ℂ, Model X) ω
      (fun y => H y i j) t.baseSet :=
    t.contMDiffOn_section_baseSet_iff.mp
      (S.holomorphicSectionOn_bracketTensor_apply t.open_baseSet (hframe i) (hframe j))
  have hsrc : e.source = c.source ∩ t.baseSet := c.restr_source' _ t.open_baseSet
  have htarg : e.target = c.target ∩ c.symm ⁻¹' t.baseSet := by
    rw [OpenPartialHomeomorph.restr_target, t.open_baseSet.interior_eq]
  refine ⟨e, ?_, (fun z => H (c.symm z)), ?_, ?_⟩
  · rw [hsrc]
    exact ⟨mem_chart_source (Model X) x, FiberBundle.mem_baseSet_trivializationAt' x⟩
  · intro z hz
    rw [htarg] at hz
    apply AnalyticAt.pi
    intro i
    apply AnalyticAt.pi
    intro j
    have hc : ContMDiffAt 𝓘(ℂ,Model X) (ModelWithCorners X) ω c.symm z :=
      contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) x) hz.1
    exact ((hH i j).contMDiffAt (t.open_baseSet.mem_nhds hz.2) |>.comp z hc).contDiffAt.analyticAt
  · intro y hy
    rw [hsrc] at hy
    change S.bracketTensor y = 0 ↔ H (c.symm (c y)) = 0
    rw [c.left_inv hy.1]
    have hHval (i j : Fin X.dim) :
        H y i j = t.linearEquivAt ℂ y hy.2
          (S.bracketTensor y ((t.basisAt b hy.2) i) ((t.basisAt b hy.2) j)) := by
      simp only [H, Bundle.Trivialization.localFrame_apply_of_mem_baseSet t b hy.2,
        Bundle.Trivialization.linearEquivAt_apply]
    constructor
    · intro hz
      funext i j
      rw [hHval, hz]
      change (t.linearEquivAt ℂ y hy.2) 0 = 0
      exact map_zero _
    · intro hz
      apply ContinuousLinearMap.coe_injective
      apply (t.basisAt b hy.2).ext
      intro i
      apply ContinuousLinearMap.coe_injective
      apply (t.basisAt b hy.2).ext
      intro j
      have h := congrFun (congrFun hz i) j
      rw [hHval] at h
      apply (t.linearEquivAt ℂ y hy.2).injective
      change (t.linearEquivAt ℂ y hy.2) _ = (t.linearEquivAt ℂ y hy.2) 0
      rw [map_zero]
      exact h

 
theorem bracketTensor_eq_zero_of_open [ConnectedSpace X.Carrier]
    {U : Set X.Carrier} (hU : IsOpen U) (hne : U.Nonempty)
    (hB : ∀ x ∈ U, S.bracketTensor x = 0) : ∀ x, S.bracketTensor x = 0 := by
  have hne' : (interior {x | S.bracketTensor x = 0}).Nonempty := by
    obtain ⟨x,hx⟩ := hne
    exact ⟨x, interior_maximal hB hU hx⟩
  have heq := AnalyticContinuation.eq_univ_of_local_analytic_zero_locus
    (S.bracketTensor_local_analytic_zero_locus) hne'
  intro x
  exact (Set.eq_univ_iff_forall.mp heq) x

end TangentSplitting
end

section



namespace RationalFamily
variable {X T : ComplexManifold.{u}} (G : RationalFamily X T)

lemma twoPointEvaluation_derivative (a b : ℂ) (τ : T.Carrier) (v : Tangent T τ) :
    mfderiv (ModelWithCorners T) ((ModelWithCorners X).prod (ModelWithCorners X))
      (G.twoPointEvaluation a b) τ v =
      ((G.derivativeSection τ v).finite a, (G.derivativeSection τ v).finite b) := by
  change (mfderiv (ModelWithCorners T) ((ModelWithCorners X).prod (ModelWithCorners X))
    (fun t => (G.finite (a,t), G.finite (b,t))) τ) v =
    (parameterDerivative G.finite τ v a, parameterDerivative G.finite τ v b)
  have h (z : ℂ) : MDifferentiableAt (ModelWithCorners T) (ModelWithCorners X)
      (fun t => G.finite (z,t)) τ :=
    (G.finite_holomorphic.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable (by simp) τ
  rw [mfderiv_prodMk (h a) (h b)]
  rfl

 

theorem exists_section_endpoints {a b : ℂ} {τ : T.Carrier}
    (hs : Function.Surjective (mfderiv (ModelWithCorners T)
      ((ModelWithCorners X).prod (ModelWithCorners X)) (G.twoPointEvaluation a b) τ))
    (v : Tangent X (G.finite (a,τ))) (w : Tangent X (G.finite (b,τ))) :
    ∃ σ : CurveTangentSection (G.curve τ), σ.finite a = v ∧ σ.finite b = w := by
  obtain ⟨u,hu⟩ := hs (v,w)
  rw [G.twoPointEvaluation_derivative] at hu
  exact ⟨G.derivativeSection τ u, congrArg Prod.fst hu, congrArg Prod.snd hu⟩

end RationalFamily

open Filter

 
theorem twoChart_holomorphic_constant {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {f k : ℂ → V} (hf : Differentiable ℂ f) (hk : ContinuousAt k 0)
    (he : ∀ z : ℂ, z ≠ 0 → f z = k z⁻¹) (z w : ℂ) : f z = f w := by
  have ht : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (nhds 0) := by
    simpa only [Metric.cobounded_eq_cocompact] using
      (tendsto_inv₀_cobounded : Tendsto (fun z : ℂ => z⁻¹) (Bornology.cobounded ℂ) (nhds 0))
  have hz : ∀ᶠ z : ℂ in cocompact ℂ, z ≠ 0 :=
    mem_cocompact.mpr ⟨{0},isCompact_singleton,by intro z hz; simpa using hz⟩
  have hlim : Tendsto f (cocompact ℂ) (nhds (k 0)) :=
    (hk.tendsto.comp ht).congr' (hz.mono fun z hz => (he z hz).symm)
  rw [hf.apply_eq_of_tendsto_cocompact z hlim,hf.apply_eq_of_tendsto_cocompact w hlim]

namespace CurveTangentSection
variable {X : ComplexManifold.{u}}
 
theorem constant_finite (x : X.Carrier) (σ : CurveTangentSection (RationalCurve.constant x))
    (z w : ℂ) : σ.finite z = σ.finite w := by
  let t := trivializationAt (Model X) (Tangent X) x
  have hx : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  let f := fun q : ℂ => (t ⟨x,σ.finite q⟩).2
  let k := fun q : ℂ => (t ⟨x,σ.infinity q⟩).2
  have hf : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,Model X) ω f := by
    intro q
    exact ((t.contMDiffAt_iff (f := fun q => (⟨x,σ.finite q⟩ :
      TangentBundle (ModelWithCorners X) X.Carrier)) (by simpa only [t.mem_source] using hx)).mp
      (σ.finite_holomorphic q)).2
  have hk : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,Model X) ω k := by
    intro q
    exact ((t.contMDiffAt_iff (f := fun q => (⟨x,σ.infinity q⟩ :
      TangentBundle (ModelWithCorners X) X.Carrier)) (by simpa only [t.mem_source] using hx)).mp
      (σ.infinity_holomorphic q)).2
  have he : ∀ q : ℂ, q ≠ 0 → f q = k q⁻¹ := by
    intro q hq
    exact congrArg (fun v : Tangent X x => (t ⟨x,v⟩).2) (σ.overlap q hq)
  apply (t.linearEquivAt ℂ x hx).injective
  exact twoChart_holomorphic_constant
    ((contMDiff_iff_contDiff.mp hf).differentiable (by simp)) hk.continuous.continuousAt he z w
end CurveTangentSection

namespace TangentSplitting
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

lemma bracketTensor_projectors (x : X.Carrier) (v w : Tangent X x) :
    S.bracketTensor x (S.projector x v) (S.projector x w) = S.bracketTensor x v w := by
  let V := FiberBundle.extend (Model X) v
  let W := FiberBundle.extend (Model X) w
  have hV := FiberBundle.mdifferentiableAt_extend (ModelWithCorners X) (Model X) v
  have hW := FiberBundle.mdifferentiableAt_extend (ModelWithCorners X) (Model X) w
  have h1 := S.bracketTensor_apply (S.mdifferentiableAt_projectField hV)
    (S.mdifferentiableAt_projectField hW)
  have h2 := S.bracketTensor_apply hV hW
  have he (U : Field (X := X)) : S.projectField (S.projectField U) = S.projectField U := by
    funext y
    exact S.idempotent y (U y)
  have h3 : S.bracketOperation x (S.projectField (FiberBundle.extend (Model X) v))
      (S.projectField (FiberBundle.extend (Model X) w)) =
      S.bracketOperation x (FiberBundle.extend (Model X) v) (FiberBundle.extend (Model X) w) := by
    simp only [bracketOperation,he]
  simpa [projectField] using h1.trans (h3.trans h2.symm)

lemma complementAt_bracketTensor (x : X.Carrier) (v w : Tangent X x) :
    S.complementAt x (S.bracketTensor x v w) = S.bracketTensor x v w := by
  have h := S.bracketTensor_apply
    (FiberBundle.mdifferentiableAt_extend (ModelWithCorners X) (Model X) v)
    (FiberBundle.mdifferentiableAt_extend (ModelWithCorners X) (Model X) w)
  simp only [FiberBundle.extend_apply_self] at h
  rw [h]
  simp [bracketOperation,complementAt_apply,map_sub,S.idempotent]

end TangentSplitting
end




namespace RationalFamily
variable {X T : ComplexManifold.{u}} (G : RationalFamily X T)

 

theorem bracketTensor_zero_of_transport (S : TangentSplitting X) {a b : ℂ} {τ : T.Carrier}
    (hs : Function.Surjective (mfderiv (ModelWithCorners T)
      ((ModelWithCorners X).prod (ModelWithCorners X)) (G.twoPointEvaluation a b) τ))
    (D : NormalizedFactorTransport S (G.curve τ) b) :
    S.bracketTensor (G.finite (b,τ)) = 0 := by
  ext v w
  obtain ⟨σ,haσ,hbσ⟩ := G.exists_section_endpoints hs 0 v
  obtain ⟨ζ,haζ,hbζ⟩ := G.exists_section_endpoints hs 0 w
  let σ' := D.firstMap.mapSection σ
  let ζ' := D.firstMap.mapSection ζ
  let β := CurveTangentSection.bracket S σ' ζ'
  let κ := D.secondMap.mapSection β
  have hk := CurveTangentSection.constant_finite ((G.curve τ).finite b) κ b a
  have hka : κ.finite a = 0 := by
    change D.secondMap.finite a (S.bracketTensor (D.factor.finite a)
      (D.firstMap.finite a (σ.finite a)) (D.firstMap.finite a (ζ.finite a))) = 0
    have hσ0 : D.firstMap.finite a (σ.finite a) = 0 :=
      (congrArg (D.firstMap.finite a) haσ).trans (map_zero _)
    have hζ0 : D.firstMap.finite a (ζ.finite a) = 0 :=
      (congrArg (D.firstMap.finite a) haζ).trans (map_zero _)
    rw [hσ0,hζ0]
    simp
  have hkb : κ.finite b = S.bracketTensor (G.finite (b,τ)) v w := by
    change D.secondMap.finite b (S.bracketTensor (D.factor.finite b)
      (D.firstMap.finite b (σ.finite b)) (D.firstMap.finite b (ζ.finite b))) = _
    rw [D.first_normalized,D.second_normalized,D.diagonal,hbσ,hbζ]
    change S.complementAt (G.finite (b,τ))
      (S.bracketTensor (G.finite (b,τ)) (S.projector (G.finite (b,τ)) v)
        (S.projector (G.finite (b,τ)) w)) = S.bracketTensor (G.finite (b,τ)) v w
    rw [S.bracketTensor_projectors,S.complementAt_bracketTensor]
  rw [hka,hkb] at hk
  exact hk

 

theorem integrable_first_of_transport [ConnectedSpace X.Carrier]
    (S : TangentSplitting X) {a b : ℂ}
    (hs : ∀ τ, Function.Surjective (mfderiv (ModelWithCorners T)
      ((ModelWithCorners X).prod (ModelWithCorners X)) (G.twoPointEvaluation a b) τ))
    (D : ∀ τ, NormalizedFactorTransport S (G.curve τ) b)
    {U : Set X.Carrier} (hU : IsOpen U) (hn : U.Nonempty)
    (himage : U ⊆ Set.range (fun τ => G.finite (b,τ))) : Integrable X S.first := by
  apply S.integrable_first_of_bracketTensor_eq_zero
  apply S.bracketTensor_eq_zero_of_open hU hn
  intro x hx
  obtain ⟨τ,rfl⟩ := himage hx
  exact G.bracketTensor_zero_of_transport S (hs τ) (D τ)

end RationalFamily
end SplitTangent

open scoped Topology
open Filter
namespace SplitTangent

 

lemma map_nhds_eq_of_surjective_mfderiv {T X : ComplexManifold.{u}}
    {f : T.Carrier → X.Carrier} {t : T.Carrier}
    (hf : ContMDiffAt (ModelWithCorners T) (ModelWithCorners X) ω f t)
    (hs : Function.Surjective (mfderiv (ModelWithCorners T) (ModelWithCorners X) f t)) :
    Filter.map f (𝓝 t) = 𝓝 (f t) := by
  let e := extChartAt (ModelWithCorners T) t
  let d := extChartAt (ModelWithCorners X) (f t)
  let W := d ∘ f ∘ e.symm
  have hw : ContDiffAt ℂ ω W (e t) := by
    simpa [W,e,d,ModelWithCorners,contDiffWithinAt_univ] using (contMDiffAt_iff.mp hf).2
  have hder : mfderiv (ModelWithCorners T) (ModelWithCorners X) f t =
      fderiv ℂ W (e t) := by
    simp [mfderiv,hf.mdifferentiableAt (by simp),writtenInExtChartAt,W,e,d,ModelWithCorners]
    rfl
  have hmap : Filter.map W (𝓝 (e t)) = 𝓝 (W (e t)) :=
    (hw.hasStrictFDerivAt (by simp)).map_nhds_eq_of_surj
      (LinearMap.range_eq_top.mpr (hder ▸ hs))
  have he : Filter.map e.symm (𝓝 (e t)) = 𝓝 t := by
    simpa [e,ModelWithCorners] using
      (map_extChartAt_symm_nhdsWithin_range (I := ModelWithCorners T) t)
  have hd : Filter.map d.symm (𝓝 (d (f t))) = 𝓝 (f t) := by
    simpa [d,ModelWithCorners] using
      (map_extChartAt_symm_nhdsWithin_range (I := ModelWithCorners X) (f t))
  have hwet : W (e t) = d (f t) := by
    simp [W,e]
  have heq : d.symm ∘ W =ᶠ[𝓝 (e t)] f ∘ e.symm := by
    have hct : ContinuousAt (f ∘ e.symm) (e t) := by
      have hc : ContinuousAt f (e.symm (e t)) := by simpa [e] using hf.continuousAt
      exact hc.comp (continuousAt_extChartAt_symm (I := ModelWithCorners T) t)
    have hm : ∀ᶠ z in 𝓝 (e t), f (e.symm z) ∈ d.source := by
      apply hct.eventually
      simpa [e,d] using extChartAt_source_mem_nhds (I := ModelWithCorners X) (f t)
    filter_upwards [hm] with z hz
    exact d.left_inv hz
  calc
    Filter.map f (𝓝 t) = Filter.map (f ∘ e.symm) (𝓝 (e t)) := by rw [← he,Filter.map_map]
    _ = Filter.map (d.symm ∘ W) (𝓝 (e t)) := Filter.map_congr heq.symm
    _ = 𝓝 (f t) := by rw [← Filter.map_map,hmap,hwet,hd]

namespace RationalFamily
variable {X T : ComplexManifold.{u}} (G : RationalFamily X T)

lemma endpoint_derivative_surjective {a b : ℂ} {τ : T.Carrier}
    (hs : Function.Surjective (mfderiv (ModelWithCorners T)
      ((ModelWithCorners X).prod (ModelWithCorners X)) (G.twoPointEvaluation a b) τ)) :
    Function.Surjective (mfderiv (ModelWithCorners T) (ModelWithCorners X)
      (fun t => G.finite (b,t)) τ) := by
  intro w
  obtain ⟨v,hv⟩ := hs (0,w)
  have hh := congrArg Prod.snd hv
  rw [G.twoPointEvaluation_derivative] at hh
  exact ⟨v,hh⟩

 
lemma endpoint_range_open {a b : ℂ}
    (hs : ∀ τ, Function.Surjective (mfderiv (ModelWithCorners T)
      ((ModelWithCorners X).prod (ModelWithCorners X)) (G.twoPointEvaluation a b) τ)) :
    IsOpen (Set.range (fun τ => G.finite (b,τ))) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨τ,rfl⟩ := hx
  have hf : ContMDiffAt (ModelWithCorners T) (ModelWithCorners X) ω
      (fun t => G.finite (b,t)) τ :=
    (G.finite_holomorphic.comp (contMDiff_const.prodMk contMDiff_id)).contMDiffAt
  have hm := map_nhds_eq_of_surjective_mfderiv hf (G.endpoint_derivative_surjective (hs τ))
  rw [← hm]
  exact Filter.mem_map.mpr (by simp)

 

theorem integrable_first_of_submersive_transport [ConnectedSpace X.Carrier]
    [Nonempty T.Carrier] (S : TangentSplitting X) {a b : ℂ}
    (hs : ∀ τ, Function.Surjective (mfderiv (ModelWithCorners T)
      ((ModelWithCorners X).prod (ModelWithCorners X)) (G.twoPointEvaluation a b) τ))
    (D : ∀ τ, NormalizedFactorTransport S (G.curve τ) b) : Integrable X S.first := by
  exact G.integrable_first_of_transport S hs D (G.endpoint_range_open hs)
    (Set.range_nonempty _) (fun _ h => h)

end RationalFamily
end SplitTangent

namespace SplitTangent.RationalFamily
variable {X T : ComplexManifold.{u}} (G : RationalFamily X T)
 

theorem integrable_both_of_submersive_transport [ConnectedSpace X.Carrier]
    [Nonempty T.Carrier] (S : TangentSplitting X) {a b : ℂ}
    (hs : ∀ τ, Function.Surjective (mfderiv (ModelWithCorners T)
      ((ModelWithCorners X).prod (ModelWithCorners X)) (G.twoPointEvaluation a b) τ))
    (D₁ : ∀ τ, NormalizedFactorTransport S (G.curve τ) b)
    (D₂ : ∀ τ, NormalizedFactorTransport S.swap (G.curve τ) b) :
    Integrable X S.first ∧ Integrable X S.second := by
  refine ⟨G.integrable_first_of_submersive_transport S hs D₁,?_⟩
  simpa only [TangentSplitting.swap_first] using
    G.integrable_first_of_submersive_transport S.swap hs D₂
end SplitTangent.RationalFamily

end

end OAI
end

section
-- module Solutions.OAIQW_SplitTangent.RationalTrivialization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Trivialization. -/

noncomputable section
universe u
open Filter Topology Set Bundle
open scoped ContDiff Manifold LinearAlgebra.Projectivization

open Filter Topology Set

open scoped Manifold LinearAlgebra.Projectivization
open Bundle

open Filter Topology

namespace SplitTangent
section
open Filter Topology Set

namespace TangentSplitting
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

theorem exists_rational_reverse_map (g : RationalCurve X)
    (hvf : ∀ z, S.projector (g.finite z)
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g.finite z (1 : ℂ))=0)
    (hvi : ∀ z, S.projector (g.infinity z)
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g.infinity z (1 : ℂ))=0)
    (a : ℂ) : ∃ B : CurveBundleMap g (RationalCurve.constant (g.finite a)),
      B.finite a=S.projector (g.finite a) := by
  obtain ⟨Lf⟩ := S.exists_local_chart_images g.finite_holomorphic
  obtain ⟨Li⟩ := S.exists_local_chart_images g.infinity_holomorphic
  exact ⟨S.rationalReverseMap g Lf Li hvf hvi a,Lf.continuationMap_self _ _ a⟩
end TangentSplitting
end

open Filter Topology Set



end SplitTangent

end

end OAI
end

section
-- module Solutions.OAIQW_SplitTangent.BoxTransportBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Box Transport Base. -/

noncomputable section
open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle
universe u

namespace SplitTangent.TangentBox
open Filter Topology Set
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} {g : RationalCurve X}
  (F : TangentBox S g)


lemma firstFactor_diagonal (b : ℂ) : (F.firstFactor b).finite b=g.finite b :=
  F.finite_diagonal b

lemma firstFactor_tangent (b z : ℂ) (c : Bool) :
    S.swap.projector (F.chart c false (z,b))
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) (fun w : ℂ => F.chart c false (w,b)) z (1 : ℂ))=0 := by
  have hd : HasFDerivAt (fun w : ℂ => (w,b))
      ((ContinuousLinearMap.id ℂ ℂ).prod 0) z :=
    hasFDerivAt_id z |>.prodMk (hasFDerivAt_const b z)
  have hm : MDifferentiableAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ × ℂ) (fun w : ℂ => (w,b)) z :=
    hd.differentiableAt.mdifferentiableAt
  have hchain := mfderiv_comp z ((F.holomorphic c false (z,b)).mdifferentiableAt (by simp)) hm
  change S.complementAt _ _=0
  apply (S.mem_first_iff_complement_eq_zero _ _).mp
  change (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) ((F.chart c false) ∘ (fun w : ℂ => (w,b))) z) (1 : ℂ) ∈ _
  rw [hchain,mfderiv_eq_fderiv,hd.fderiv]
  change mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) (F.chart c false) (z,b) (1,0) ∈ S.first (F.chart c false (z,b))
  exact (F.tangency c false (z,b)).1

 

theorem exists_normalized_second_map (b : ℂ) :
    ∃ B : CurveBundleMap (F.firstFactor b) (RationalCurve.constant (g.finite b)),
      B.finite b=S.complementAt (g.finite b) := by
  rw [← F.firstFactor_diagonal b]
  exact S.swap.exists_rational_reverse_map (F.firstFactor b)
    (fun z => F.firstFactor_tangent b z false) (fun z => F.firstFactor_tangent b z true) b

end SplitTangent.TangentBox

end

end OAI
end

section
-- module Solutions.OAIQW_SplitTangent.BoxFirstTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Box First Transport. -/

noncomputable section
open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle
universe u

namespace SplitTangent.TangentSplitting
open Filter Topology Set
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

lemma entireMap_self {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    (hv : ∀ z, S.projector (g z)
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g z (1 : ℂ))=0) (a : ℂ) :
    S.entireMap hg hv a a=S.projector (g a) :=
  (S.canonicalChartImages hg).continuationMap_self hg hv a

end SplitTangent.TangentSplitting

namespace SplitTangent.TangentBox
open Filter Topology Set TangentSplitting
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} {g : RationalCurve X}
  (F : TangentBox S g)

lemma chartTransport_self (a b : Bool) (s u : ℂ) :
    F.chartTransport a b s u u = S.projector (F.chart a b (s,u)) :=
  S.entireMap_self (F.vertical_holomorphic a b s) (F.vertical_tangent a b s) u

lemma firstMap_normalized (b : ℂ) : (F.firstMap b).finite b=S.projector (g.finite b) := by
  change F.chartTransport false false b b b = _
  rw [F.chartTransport_self]
  erw [F.finite_diagonal]

include F in
theorem exists_normalized_factor_transport (b : ℂ) :
    Nonempty (NormalizedFactorTransport S g b) := by
  obtain ⟨B,hB⟩ := F.exists_normalized_second_map b
  exact ⟨⟨F.firstFactor b,F.firstFactor_diagonal b,F.firstMap b,B,F.firstMap_normalized b,hB⟩⟩

end SplitTangent.TangentBox

end

end OAI
end

section
-- module Solutions.OAIQW_SplitTangent.RationalFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Families. -/

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold
universe u

open Set Filter Topology
open scoped ContDiff

open Set Filter Topology IsManifold
open scoped ContDiff Manifold

open Set Filter Topology
open scoped ContDiff

open Filter Topology Set
open scoped ContDiff

open Filter Topology Set

open scoped Manifold LinearAlgebra.Projectivization
open Bundle

open Filter Topology


open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle

open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle

open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle Filter Topology

open Set Filter Topology

open Filter Topology

open Filter Topology

open Filter Topology Metric Set

 

open MvPowerSeries

open Filter Topology Set Metric

 

open Set Filter Topology
open scoped ContDiff



open Set Filter Topology
open scoped ContDiff



open Set Filter Topology
open scoped ContDiff



open Set Filter Topology
open scoped ContDiff



open Set Filter Topology
open scoped ContDiff



open Set Filter Topology
open scoped ContDiff Manifold BigOperators



open Set Filter Topology
open scoped ContDiff Manifold



open Set Filter Topology
open scoped ContDiff Manifold

 

open Set Filter Topology
open scoped ContDiff Manifold BigOperators

 

open Set Filter Topology
open scoped ContDiff Manifold

 

open Set Filter Topology
open scoped ContDiff Manifold

 

open Set Filter Topology
open scoped ContDiff Manifold BigOperators

 

open Set Filter Topology
open scoped ContDiff Manifold

 

open Set Filter Topology
open scoped ContDiff


 

open Set Filter Topology
open scoped ContDiff




open Set Filter Topology
open scoped ContDiff



open Set Filter Topology
open scoped ContDiff ENNReal



open Set Filter Topology
open scoped ContDiff ENNReal



open Set Filter Topology IsManifold
open scoped ContDiff Manifold

 

open Set Filter Topology IsManifold
open scoped ContDiff Manifold

namespace SplitTangent.RationalFamily
variable {X T : ComplexManifold.{u}} (G : RationalFamily X T)
 

theorem integrable_both_of_submersive_oai [CompactSpace X.Carrier]
    [ConnectedSpace X.Carrier] [Nonempty T.Carrier]
    (e : ProjectiveEmbedding X) (S : TangentSplitting X) {a b : ℂ}
    (hs : ∀ τ, Function.Surjective (mfderiv (ModelWithCorners T)
      ((ModelWithCorners X).prod (ModelWithCorners X)) (G.twoPointEvaluation a b) τ)) :
    Integrable X S.first ∧ Integrable X S.second := by
  classical
  apply G.integrable_both_of_submersive_transport S hs
  · intro τ
    let F := Classical.choice (S.exists_projective_tangent_box e (G.curve τ))
    exact Classical.choice (F.exists_normalized_factor_transport b)
  · intro τ
    let F := Classical.choice (S.swap.exists_projective_tangent_box e (G.curve τ))
    exact Classical.choice (F.exists_normalized_factor_transport b)
end SplitTangent.RationalFamily

end

end OAI
end

theorem solution.{u} : type_of% @OAI.SplitTangent.RationalFamily.integrable_both_of_submersive_oai.{u} := @OAI.SplitTangent.RationalFamily.integrable_both_of_submersive_oai.{u}
