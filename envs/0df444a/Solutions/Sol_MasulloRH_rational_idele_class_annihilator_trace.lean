-- Prove2me | solution 1 for MasulloRH.rational_idele_class_annihilator_trace
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T02:52:51.264048+00:00
-- url     : https://prove2.me/submissions/52bab387-53c9-4738-b7ab-3996d270a85e

import Definitions.Def_MasulloRH_RationalClassThetaSpace
import Theorems.Thm_MasulloRH_rational_theta_test_factorization
import Theorems.Thm_MasulloRH_rational_theta_annihilator_jet_trace
import Theorems.Thm_MasulloGRH_nuclear_trace_hasSum_hilbertBasis
import Definitions.Def_MasulloRH_RationalThetaSpace
import Theorems.Thm_MasulloRH_rational_idele_class_spherical_coordinates

section StandaloneClassTraceRows

open NumberField IsDedekindDomain MeasureTheory Set
open MasulloRH.RationalClass MasulloRH.RationalFinite
open scoped Topology InnerProductSpace SchwartzMap

namespace MasulloRH.ClassTrace
noncomputable section

abbrev HR := Lp ℂ 2 (volume : Measure ℝ)

def realRow (p : ℝ) (g : 𝓢(ℝ,ℂ)) (x : ℝ) : ℂ :=
  (starRingEnd ℂ) ((((1+x^2)^(p/2):ℝ):ℂ)*((Real.exp (x/2):ℂ)*∑' n : ℤ, g ((n:ℝ)*Real.exp x)))

def realRows (p : ℝ) : Set HR := {v | ∃ g : 𝓢(ℝ,ℂ),
  g 0=0 ∧ (∫ x : ℝ, g x)=0 ∧ (v : ℝ→ℂ) =ᵐ[volume] realRow p g}

theorem realRow_continuous (p : ℝ) (g : 𝓢(ℝ,ℂ)) (h0 : g 0=0) (hI : (∫ x : ℝ, g x)=0) :
    Continuous (realRow p g) := by
  obtain ⟨T,hT,_⟩ := (rational_theta_test_factorization g h0 hI).2
  have he : realRow p g = fun x : ℝ => (starRingEnd ℂ) ((((1+x^2)^(p/2):ℝ):ℂ)*T x) := by
    funext x
    exact congrArg (fun z : ℂ => (starRingEnd ℂ) ((((1+x^2)^(p/2):ℝ):ℂ)*z)) (hT x).symm
  rw [he]
  have hr : Continuous (fun x : ℝ => (1+x^2)^(p/2)) :=
    (show Continuous (fun x : ℝ => 1+x^2) by fun_prop).rpow_const (fun x => Or.inl (by positivity))
  exact Complex.continuous_conj.comp ((Complex.continuous_ofReal.comp hr).mul T.continuous)

variable [MeasurableSpace Ad] [MeasurableSpace K] [MeasurableSpace C]
variable (μ : Measure Ad) (κ : Measure K) (ν : Measure C)

def ImageEquality : Prop :=
  {Φ : C → ℂ | ∃ F ∈ AdelicFourier.schwartzBruhat ℚ, F 0=0 ∧ (∫ a, F a ∂μ)=0 ∧
      Φ=sphericalTheta κ F} =
  {Φ : C → ℂ | ∃ g : 𝓢(ℝ,ℂ), g 0=0 ∧ (∫ x : ℝ, g x)=0 ∧
      ∀ z, Φ z = ∑' n : ℤ, g ((n:ℝ)*Real.exp (logNorm z))}

theorem rows_eq_image (p : ℝ) (himg : ImageEquality μ κ)
    (hl : MeasurePreserving logNorm ν (volume : Measure ℝ))
    (J : HR →ₗᵢ[ℂ] Lp ℂ 2 ν) (hJ : ∀ v, (J v : C→ℂ) =ᵐ[ν] fun z => v (logNorm z)) :
    rationalClassThetaRows μ κ ν p = J '' realRows p := by
  ext w
  constructor
  · rintro ⟨F,hF,h0,hI,hw⟩
    obtain ⟨g,hg0,hgI,he⟩ := (Set.ext_iff.mp himg (sphericalTheta κ F)).1 ⟨F,hF,h0,hI,rfl⟩
    have he' : (w : C→ℂ) =ᵐ[ν] (realRow p g ∘ logNorm) := by
      filter_upwards [hw] with z h
      simpa only [Function.comp_apply,realRow,he] using h
    have hm : MemLp (realRow p g ∘ logNorm) 2 ν := (memLp_congr_ae he').mp (Lp.memLp w)
    have hc := realRow_continuous p g hg0 hgI
    have hr : MemLp (realRow p g) 2 (volume : Measure ℝ) := by
      rw [← hl.map_eq]
      exact (memLp_map_measure_iff hc.aestronglyMeasurable hl.aemeasurable).mpr hm
    refine ⟨hr.toLp _,⟨g,hg0,hgI,hr.coeFn_toLp⟩,Lp.ext ?_⟩
    exact ((hJ _).trans (hl.quasiMeasurePreserving.ae_eq_comp hr.coeFn_toLp)).trans he'.symm
  · rintro ⟨v,⟨g,hg0,hgI,hv⟩,rfl⟩
    let Φ (z : C) := ∑' n : ℤ, g ((n:ℝ)*Real.exp (logNorm z))
    obtain ⟨F,hF,h0,hI,he⟩ := (Set.ext_iff.mp himg Φ).2 ⟨g,hg0,hgI,fun _ => rfl⟩
    refine ⟨F,hF,h0,hI,?_⟩
    have h := (hJ v).trans (hl.quasiMeasurePreserving.ae_eq_comp hv)
    filter_upwards [h] with z hz
    simpa only [Function.comp_apply,realRow,← he,Φ] using hz

theorem spherical_eq_range
    (J : HR →ₗᵢ[ℂ] Lp ℂ 2 ν)
    (h : ∀ v : Lp ℂ 2 ν, v ∈ J.toLinearMap.range ↔ ∀ᵐ z ∂ν, ∀ᵐ u ∂κ, v (z*finiteUnit u)=v z) :
    rationalClassSpherical κ ν = J.toLinearMap.range := by
  have he : {v : Lp ℂ 2 ν | ∀ᵐ z ∂ν, ∀ᵐ u ∂κ, v (z*finiteUnit u)=v z} =
      (J.toLinearMap.range : Set (Lp ℂ 2 ν)) := Set.ext fun z => (h z).symm
  rw [rationalClassSpherical,he,Submodule.span_eq]
  exact (show IsClosed (J.toLinearMap.range : Set (Lp ℂ 2 ν)) from J.isometry.isClosedEmbedding.isClosed_range).submodule_topologicalClosure_eq

end
end MasulloRH.ClassTrace

end StandaloneClassTraceRows

section StandaloneClassTraceUnitary

open NumberField IsDedekindDomain MeasureTheory Set
open MasulloRH.RationalClass MasulloRH.RationalFinite
open scoped Topology InnerProductSpace SchwartzMap
namespace MasulloRH.ClassTrace
noncomputable section

variable [MeasurableSpace Ad] [MeasurableSpace K] [MeasurableSpace C]
variable (μ : Measure Ad) (κ : Measure K) (ν : Measure C) (p : ℝ)

theorem annihilator_map (J : HR →ₗᵢ[ℂ] Lp ℂ 2 ν)
    (hS : rationalClassSpherical κ ν=J.toLinearMap.range)
    (hR : rationalClassThetaRows μ κ ν p = J '' realRows p) :
    (rationalThetaAnnihilator p).map J.toLinearMap = rationalClassThetaAnnihilator μ κ ν p := by
  change ((Submodule.span ℂ (realRows p))ᗮ).map J.toLinearMap = _
  rw [Submodule.map_orthogonal,Submodule.map_span,rationalClassThetaAnnihilator,hS,hR,inf_comm]
  rfl

theorem exists_annihilator_equiv (J : HR →ₗᵢ[ℂ] Lp ℂ 2 ν)
    (hE : (rationalThetaAnnihilator p).map J.toLinearMap = rationalClassThetaAnnihilator μ κ ν p) :
    ∃ E : rationalThetaAnnihilator p ≃ₗᵢ[ℂ] rationalClassThetaAnnihilator μ κ ν p,
      ∀ f, (E f : Lp ℂ 2 ν)=J f.val := by
  let X := rationalThetaAnnihilator p
  let S := J.submoduleMap X
  have hs : Function.Surjective S := by
    rintro ⟨_,x,hx,rfl⟩
    exact ⟨⟨x,hx⟩,rfl⟩
  let U := LinearIsometryEquiv.ofSurjective S hs
  exact ⟨U.trans (LinearIsometryEquiv.ofEq _ _ hE),fun _ => rfl⟩

private theorem cyclic_ClassTraceUnitary_family_image {ι : Type*} (f : ι → ℝ → ℂ) (hc : ∀ i, Continuous (f i))
    (hl : MeasurePreserving logNorm ν (volume : Measure ℝ))
    (J : HR →ₗᵢ[ℂ] Lp ℂ 2 ν) (hJ : ∀ v, (J v : C→ℂ) =ᵐ[ν] fun z => v (logNorm z)) :
    {v : Lp ℂ 2 ν | ∃ i, (v : C→ℂ) =ᵐ[ν] f i ∘ logNorm} =
      J '' {v : HR | ∃ i, (v : ℝ→ℂ) =ᵐ[volume] f i} := by
  ext w
  constructor
  · rintro ⟨i,hi⟩
    have hm := (memLp_congr_ae hi).mp (Lp.memLp w)
    have hr : MemLp (f i) 2 (volume : Measure ℝ) := by
      rw [← hl.map_eq]
      exact (memLp_map_measure_iff (hc i).aestronglyMeasurable hl.aemeasurable).mpr hm
    exact ⟨hr.toLp _,⟨i,hr.coeFn_toLp⟩,Lp.ext (((hJ _).trans
      (hl.quasiMeasurePreserving.ae_eq_comp hr.coeFn_toLp)).trans hi.symm)⟩
  · rintro ⟨v,⟨i,hi⟩,rfl⟩
    exact ⟨i,(hJ v).trans (hl.quasiMeasurePreserving.ae_eq_comp hi)⟩

abbrev Z := {z : ℂ // riemannZeta z=0 ∧ z.re=1/2}
def jet (p : ℝ) (z : Z) (r : ℕ) (x : ℝ) : ℂ :=
  ((1+x^2)^(-p/2) : ℝ)*((x:ℂ)^r * Complex.exp (↑(z.val.im*x)*Complex.I))
abbrev Jet (p : ℝ) := {j : Z × ℕ // j.2 < analyticOrderNatAt riemannZeta j.1.val ∧ (j.2:ℝ)+1/2 < p}

theorem jet_span (hp : 1/2<p) (hl : MeasurePreserving logNorm ν (volume : Measure ℝ))
    (J : HR →ₗᵢ[ℂ] Lp ℂ 2 ν) (hJ : ∀ v, (J v : C→ℂ) =ᵐ[ν] fun z => v (logNorm z))
    (hE : (rationalThetaAnnihilator p).map J.toLinearMap = rationalClassThetaAnnihilator μ κ ν p) :
    rationalClassThetaAnnihilator μ κ ν p =
      (Submodule.span ℂ {v : Lp ℂ 2 ν | ∃ (z : Z) (r : ℕ), r < analyticOrderNatAt riemannZeta z.val ∧
          (r:ℝ)+1/2<p ∧ (v : C→ℂ) =ᵐ[ν] fun q => jet p z r (logNorm q)}).topologicalClosure := by
  let S := {v : HR | ∃ j : Jet p, (v : ℝ→ℂ) =ᵐ[volume] jet p j.val.1 j.val.2}
  let U := {v : Lp ℂ 2 ν | ∃ j : Jet p, (v:C→ℂ) =ᵐ[ν] jet p j.val.1 j.val.2 ∘ logNorm}
  have hS : rationalThetaAnnihilator p = (Submodule.span ℂ S).topologicalClosure := by
    rw [(rational_theta_annihilator_jet_trace p hp).1]
    congr 2
    ext v
    constructor
    · rintro ⟨z,r,hr,hh,hv⟩
      exact ⟨⟨(z,r),hr,hh⟩,hv⟩
    · rintro ⟨⟨⟨z,r⟩,hr,hh⟩,hv⟩
      exact ⟨z,r,hr,hh,hv⟩
  have he : U = J '' S := by
    apply cyclic_ClassTraceUnitary_family_image ν _ _ hl J hJ
    intro j
    have hr : Continuous (fun x : ℝ => (1+x^2)^(-p/2)) :=
      (show Continuous (fun x : ℝ => 1+x^2) by fun_prop).rpow_const (fun x => Or.inl (by positivity))
    unfold jet
    fun_prop
  have hcl : ((Submodule.span ℂ S).topologicalClosure).map J.toLinearMap =
      ((Submodule.span ℂ S).map J.toLinearMap).topologicalClosure := by
    apply SetLike.coe_injective
    exact (J.isometry.isClosedEmbedding.closure_image_eq _).symm
  rw [←hE,hS,hcl,Submodule.map_span]
  change (Submodule.span ℂ (J '' S)).topologicalClosure = _
  rw [←he]
  congr 2
  ext v
  constructor
  · rintro ⟨⟨⟨z,r⟩,hr,hh⟩,hv⟩
    exact ⟨z,r,hr,hh,hv⟩
  · rintro ⟨z,r,hr,hh,hv⟩ 
    exact ⟨⟨(z,r),hr,hh⟩,hv⟩

end
end MasulloRH.ClassTrace

end StandaloneClassTraceUnitary

section StandaloneClassTraceNuclear

open MeasureTheory MasulloGRH
open scoped InnerProductSpace
namespace MasulloRH.RationalClass
noncomputable section

/-- An intertwining Hilbert isometry preserves nuclearity and the canonical Hilbert trace. -/
theorem nuclear_trace_transport {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (E : H ≃ₗᵢ[ℂ] F) (T : H →L[ℂ] H) (S : F →L[ℂ] F)
    (hS : ∀ u, S (E u) = E (T u)) (hT : IsNuclearOperator T) :
    IsNuclearOperator S ∧ operatorTrace S = operatorTrace T := by
  have hn : IsNuclearOperator S := by
    obtain ⟨x,y,hs,ht⟩ := hT
    refine ⟨fun n => E (x n),fun n => E (y n),by simpa using hs,?_⟩
    intro v
    obtain ⟨u,rfl⟩ := E.surjective v
    rw [hS]
    have ht' := (ht u).mapL E.toLinearIsometry.toContinuousLinearMap
    simpa only [LinearIsometry.coe_toContinuousLinearMap,LinearIsometryEquiv.coe_toLinearIsometry,
      E.inner_map_map,map_smul] using ht'
  refine ⟨hn,?_⟩
  let b := chosenHilbertBasis H
  let c : HilbertBasis (exists_hilbertBasis ℂ H).choose ℂ F :=
    ⟨E.symm.trans b.repr⟩
  have hc (i : (exists_hilbertBasis ℂ H).choose) : c i = E (b i) := rfl
  have hsd := (nuclear_trace_hasSum_hilbertBasis S hn c).2
  have htd := (nuclear_trace_hasSum_hilbertBasis T hT b).2
  simp only [hc,hS,E.inner_map_map] at hsd
  exact hsd.unique htd

/-- The weak identity determines its operator, since it tests against all of ambient L². -/
theorem convolution_unique [MeasurableSpace Ad] [MeasurableSpace RationalFinite.K]
    [MeasurableSpace C] (μ : Measure Ad) (κ : Measure RationalFinite.K) (ν : Measure C)
    (p : ℝ) (ray : ℝ → C) (φ : ℝ → ℂ)
    {T S : rationalClassThetaAnnihilator μ κ ν p →L[ℂ] rationalClassThetaAnnihilator μ κ ν p}
    (hT : IsRationalClassThetaConvolution μ κ ν p ray φ T)
    (hS : IsRationalClassThetaConvolution μ κ ν p ray φ S) : T = S := by
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  apply ext_inner_left ℂ
  intro g
  exact (hT u g).trans (hS u g).symm

end
end MasulloRH.RationalClass

end StandaloneClassTraceNuclear

section StandaloneClassTraceConvolution

open MeasureTheory Filter
open scoped InnerProductSpace
open MasulloRH.RationalFinite

namespace MasulloRH.RationalClass
noncomputable section

private def cyclic_ClassTraceConvolution_convWeight (p x : ℝ) := (1+x^2)^(-p/2)
private theorem cyclic_ClassTraceConvolution_convWeight_pos (p x : ℝ) : 0 < cyclic_ClassTraceConvolution_convWeight p x :=
  Real.rpow_pos_of_pos (by positivity) _
private theorem cyclic_ClassTraceConvolution_cont_convWeight (p : ℝ) : Continuous (cyclic_ClassTraceConvolution_convWeight p) := by
  exact Continuous.rpow_const (continuous_const.add (continuous_id.pow 2))
    (fun x => Or.inl (show 1+x^2 ≠ (0:ℝ) by positivity))

private theorem cyclic_ClassTraceConvolution_convRatio_bound (p : ℝ) (hp : 0 ≤ p) (y x : ℝ) :
    cyclic_ClassTraceConvolution_convWeight p x / cyclic_ClassTraceConvolution_convWeight p (x+y) ≤ (2+2*y^2)^(p/2) := by
  have hx : 0 < 1+x^2 := by positivity
  have hy : 0 < 2+2*y^2 := by positivity
  have hxy : 0 < 1+(x+y)^2 := by positivity
  have he : 1+(x+y)^2 ≤ (2+2*y^2)*(1+x^2) := by
    nlinarith [sq_nonneg (x-y), sq_nonneg (x*y), sq_nonneg y]
  simp only [cyclic_ClassTraceConvolution_convWeight,neg_div,Real.rpow_neg hx.le,Real.rpow_neg hxy.le,inv_div_inv]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hx (p/2))).mpr
  rw [← Real.mul_rpow hy.le hx.le]
  exact Real.rpow_le_rpow hxy.le he (by positivity)

private theorem cyclic_ClassTraceConvolution_shifted_representative (p : ℝ) (hp : 0 ≤ p) (y : ℝ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ∃ v : Lp ℂ 2 (volume : Measure ℝ), (v : ℝ → ℂ) =ᵐ[volume]
      fun x => ((cyclic_ClassTraceConvolution_convWeight p x / cyclic_ClassTraceConvolution_convWeight p (x+y) : ℝ) : ℂ) * f (x+y) := by
  have hf := (Lp.memLp f).comp_measurePreserving (measurePreserving_add_right volume y)
  let r (x : ℝ) : ℂ := (cyclic_ClassTraceConvolution_convWeight p x / cyclic_ClassTraceConvolution_convWeight p (x+y) : ℝ)
  have hr : Continuous r := Complex.continuous_ofReal.comp <| (cyclic_ClassTraceConvolution_cont_convWeight p).div
    ((cyclic_ClassTraceConvolution_cont_convWeight p).comp (continuous_id.add_const y)) (fun x => (cyclic_ClassTraceConvolution_convWeight_pos _ _).ne')
  have hv : MemLp (fun x : ℝ => r x * f (x+y)) 2 volume := by
    refine hf.of_le_mul (c := (2+2*y^2)^(p/2)) (hr.aestronglyMeasurable.mul hf.1) ?_
    apply ae_of_all
    intro x
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (Complex.norm_of_nonneg (div_nonneg (cyclic_ClassTraceConvolution_convWeight_pos p x).le (cyclic_ClassTraceConvolution_convWeight_pos p (x+y)).le)).le.trans
      (cyclic_ClassTraceConvolution_convRatio_bound p hp y x)
  exact ⟨hv.toLp _,hv.coeFn_toLp⟩

variable [MeasurableSpace Ad] [MeasurableSpace K] [MeasurableSpace C] [BorelSpace C]
  (μ : Measure Ad) (κ : Measure K) (ν : Measure C) [ν.IsMulRightInvariant]

/-- The weak formula transports to all quotient test vectors. The adjoint of the log-norm
pullback gives their fiber average, and equivariance identifies each translated integrand. -/
theorem convolution_of_transport (p : ℝ) (hp : 0 ≤ p) (ray : ℝ → C)
    (hray : ∀ z y, logNorm (z*ray y) = logNorm z + y)
    (hlog : Measure.QuasiMeasurePreserving logNorm ν volume)
    (J : Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp ℂ 2 ν)
    (hJ : ∀ f, (J f : C → ℂ) =ᵐ[ν] fun z => f (logNorm z))
    (E : rationalThetaAnnihilator p ≃ₗᵢ[ℂ] rationalClassThetaAnnihilator μ κ ν p)
    (hE : ∀ f, (E f : Lp ℂ 2 ν) = J f.val)
    (φ : ℝ → ℂ)
    (T : rationalThetaAnnihilator p →L[ℂ] rationalThetaAnnihilator p)
    (S : rationalClassThetaAnnihilator μ κ ν p →L[ℂ] rationalClassThetaAnnihilator μ κ ν p)
    (hS : ∀ f, S (E f) = E (T f)) (hT : IsRationalThetaConvolution p φ T) :
    IsRationalClassThetaConvolution μ κ ν p ray φ S := by
  intro u g
  obtain ⟨f,rfl⟩ := E.surjective u
  let adj := J.toContinuousLinearMap.adjoint
  have pair (v : Lp ℂ 2 (volume : Measure ℝ)) : ⟪g,J v⟫_ℂ = ⟪adj g,v⟫_ℂ :=
    (J.toContinuousLinearMap.adjoint_inner_left v g).symm
  rw [hS,hE,pair,hT]
  apply integral_congr_ae
  apply ae_of_all
  intro y
  apply congrArg (fun a : ℂ => φ (Real.exp y)*a)
  obtain ⟨v,hv⟩ := cyclic_ClassTraceConvolution_shifted_representative p hp y f.val
  have hfr := (measurePreserving_mul_right ν (ray y)).quasiMeasurePreserving.ae_eq_comp (hJ f.val)
  have hvr := hlog.ae_eq_comp hv
  calc
    _ = ⟪adj g,v⟫_ℂ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hv] with x hx
      rw [hx,RCLike.inner_apply,mul_comm]
      rfl
    _ = ⟪g,J v⟫_ℂ := (pair v).symm
    _ = _ := by
      rw [L2.inner_def,hE f]
      apply integral_congr_ae
      filter_upwards [hJ v,hvr,hfr] with z hz hvz hfz
      change v (logNorm z) = _ at hvz
      change J f.val (z*ray y) = f.val (logNorm (z*ray y)) at hfz
      rw [RCLike.inner_apply,hz,hvz,hfz,hray,mul_comm]
      rfl

end
end MasulloRH.RationalClass

end StandaloneClassTraceConvolution

section StandaloneClassTraceFinal

open NumberField IsDedekindDomain MeasureTheory Set
open MasulloGRH MasulloRH MasulloRH.RationalFinite MasulloRH.RationalClass
open scoped Topology InnerProductSpace SchwartzMap ENNReal

theorem solution [MeasurableSpace Ad] [BorelSpace Ad] (μ : Measure Ad) [μ.IsAddHaarMeasure]
    [MeasurableSpace K] [BorelSpace K] (κ : Measure K) [κ.IsMulLeftInvariant] [IsProbabilityMeasure κ]
    [MeasurableSpace C] [BorelSpace C] :
    ∃ (e : Multiplicative ℝ × K ≃ₜ* C) (ν : Measure C), ν.IsHaarMeasure ∧
      MeasurePreserving (fun v : ℝ × K => e (Multiplicative.ofAdd v.1,v.2)) ((volume : Measure ℝ).prod κ) ν ∧
      (∀ x u, logNorm (e (Multiplicative.ofAdd x,u))=x) ∧ (∀ u : K, finiteUnit u=e (1,u)) ∧
      ∀ p : ℝ, 1/2<p →
        let Z := {z : ℂ // riemannZeta z=0 ∧ z.re=1/2}
        let V := rationalClassThetaAnnihilator μ κ ν p
        (∃ E : rationalThetaAnnihilator p ≃ₗᵢ[ℂ] V, ∀ f,
          ((E f : Lp ℂ 2 ν) : C→ℂ) =ᵐ[ν] fun z => (f : Lp ℂ 2 (volume : Measure ℝ)) (logNorm z)) ∧
        V = (Submodule.span ℂ {v : Lp ℂ 2 ν | ∃ (z : Z) (r : ℕ),
          r<analyticOrderNatAt riemannZeta z.val ∧ (r:ℝ)+1/2<p ∧
          (v:C→ℂ) =ᵐ[ν] fun q =>
            ((1+(logNorm q)^2)^(-p/2):ℝ) * (((logNorm q:ℝ):ℂ)^r *
              Complex.exp (↑(z.val.im*logNorm q)*Complex.I))}).topologicalClosure ∧
        ∀ (φ : ℝ→ℂ), IsRationalTraceTest φ →
          ∃! T : V →L[ℂ] V,
            IsRationalClassThetaConvolution μ κ ν p (fun y => e (Multiplicative.ofAdd y,1)) φ T ∧
            IsNuclearOperator T ∧
            HasSum (fun z : Z => ((min (analyticOrderNatAt riemannZeta z.val) ⌈p-1/2⌉₊:ℕ):ℂ) *
              mellin φ (z.val-1/2)) (operatorTrace T) := by
  obtain ⟨_,_,_,e,he,hu,hk⟩ := rational_idele_class_spherical_coordinates μ
  obtain ⟨ν,hν,hm,hl,_,_,hi,J,hJ,_,hsect,_⟩ := hk κ
  let : ν.IsHaarMeasure := hν
  let : ν.IsMulRightInvariant := ⟨fun z => by
    have hlz := @Measure.IsMulLeftInvariant.map_mul_left_eq_self C _ _ ν hν.toIsMulLeftInvariant z
    simpa only [mul_comm z] using hlz⟩
  have heq (s : Multiplicative ℝ) (u : K) : logNorm (e (s,u))=s.toAdd := by
    obtain ⟨x,_,hx,hlog⟩ := he s u
    simpa only [hx] using hlog
  have hray (z : C) (y : ℝ) : logNorm (z*e (Multiplicative.ofAdd y,1))=logNorm z+y := by
    obtain ⟨⟨s,u⟩,rfl⟩ := e.surjective z
    have hh : e (s,u)*e (Multiplicative.ofAdd y,1)=e (s*Multiplicative.ofAdd y,u) := by
      rw [←map_mul]
      simp
    rw [hh,heq,heq]
    rfl
  refine ⟨e,ν,hν,hm,fun x u => heq _ _,hu,?_⟩
  intro p hp Z V
  have hS := ClassTrace.spherical_eq_range κ ν J hsect
  have hR := ClassTrace.rows_eq_image μ κ ν p hi hl J hJ
  have hA := ClassTrace.annihilator_map μ κ ν p J hS hR
  obtain ⟨E,hE⟩ := ClassTrace.exists_annihilator_equiv μ κ ν p J hA
  refine ⟨⟨E,fun f => (hE f) ▸ hJ f.val⟩,ClassTrace.jet_span μ κ ν p hp hl J hJ hA,?_⟩
  intro φ hφ
  obtain ⟨T,⟨hT,hn,hs⟩,_⟩ := (rational_theta_annihilator_jet_trace p hp).2 φ hφ
  let S := E.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (T.comp E.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  have heS (f : rationalThetaAnnihilator p) : S (E f) = E (T f) := by simp [S]
  have hW := convolution_of_transport μ κ ν p (by linarith) (fun y => e (Multiplicative.ofAdd y,1))
    hray hl.quasiMeasurePreserving J hJ E hE φ T S heS hT
  obtain ⟨hnS,htr⟩ := nuclear_trace_transport E T S heS hn
  exact ⟨S,⟨hW,hnS,htr.symm ▸ hs⟩,fun T h => convolution_unique μ κ ν p _ φ h.1 hW⟩

end StandaloneClassTraceFinal
