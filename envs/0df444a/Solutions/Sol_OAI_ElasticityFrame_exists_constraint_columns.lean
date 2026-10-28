-- Prove2me | solution 1 for OAI.ElasticityFrame.exists_constraint_columns
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:54:04.021926+00:00
-- url     : https://prove2.me/submissions/cbe9fd54-1443-4faa-afb2-a027db9f9b38

import Mathlib
import Definitions.Def_OAIQ6El002
import Definitions.Def_OAIQ6El003
import Theorems.Thm_OAI_ElasticityPlanar_spatial_frame_of_left_inverse

section
-- module Solutions.OAIQ6_Elast.Elasticity_Extension
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter Metric
open scoped Topology Manifold
namespace ElasticityBoundary
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma compact_smooth_cutoff {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K⊆U) :
    ∃ χ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ⊆U ∧
      (∀ᶠ x in 𝓝ˢ K, χ x=1) ∧ ∀ x, χ x∈Icc 0 1 := by
  obtain ⟨R,hR⟩ := hK.isBounded.subset_ball (0 : E)
  obtain ⟨V,hV,hKV,hVU⟩ := normal_exists_closure_subset hK.isClosed (hU.inter isOpen_ball)
    (show K⊆U∩ball (0 : E) R from fun x hx => ⟨hKU hx,hR hx⟩)
  obtain ⟨χ,hχ,hzero,hb⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ,E)) (n := (⊤ : ℕ∞)) hK.isClosed (by rwa [hV.interior_eq])
  have hs : tsupport (χ : E → ℝ)⊆closure V := by
    apply closure_mono
    intro x hx
    by_contra hn
    exact hx (hzero x hn)
  refine ⟨χ,χ.contMDiff.contDiff,?_,fun x hx => (hVU (hs hx)).1,hχ,hb⟩
  apply (isCompact_closedBall (0 : E) R).of_isClosed_subset (isClosed_tsupport χ)
  exact fun x hx => ball_subset_closedBall ((hVU (hs hx)).2)

end ElasticityBoundary

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Transport
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityPlanar
open Set Complex Module
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

section
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R] [FiniteDimensional ℂ R]
variable {n : Type*} [Fintype n]

/-- Actual frames on every compact physical region, with no coordinate,
cutoff, or planar-solvability existence hypothesis. -/
theorem exists_spatial_frame (J : ℂ →L[ℝ] E) (hJ : Function.Injective J)
    (q : Basis n ℂ R) (A : E → R) (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    {C : Set E} (hC : IsCompact C) :
    ∃ V : E → R, ContDiff ℝ (⊤ : ℕ∞) V ∧ (∀ x, IsUnit (V x)) ∧
      ∀ x∈C, fderiv ℝ V x (J 1)+I • fderiv ℝ V x (J I)=A x*V x := by
  obtain ⟨K,hK⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hJ
  obtain ⟨r,hr⟩ := (hC.image K.continuous).isBounded.subset_ball (0 : ℂ)
  have hbb : Metric.closedBall (0 : ℂ) r ⊆ Metric.ball 0 (r+1) := by
    intro z hz
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by linarith)
  obtain ⟨g,hg,hc,hs,h1,_⟩ := ElasticityBoundary.compact_smooth_cutoff
    (isCompact_closedBall (0 : ℂ) r) Metric.isOpen_ball hbb
  let g' : ℂ → ℂ := fun z => (g z : ℂ)
  have hg' : ContDiff ℝ (⊤ : ℕ∞) g' := Complex.ofRealCLM.contDiff.comp hg
  have hsupport : tsupport g'⊆tsupport g := by
    apply closure_mono
    intro z hz
    exact fun hh => hz (by simp only [g',hh,Complex.ofReal_zero])
  have hc' : HasCompactSupport g' := hc.of_isClosed_subset (isClosed_tsupport _) hsupport
  have h1' : Set.EqOn g' 1 (Metric.ball (0 : ℂ) r) := by
    intro z hz
    have hh := h1.self_of_nhdsSet z (Metric.ball_subset_closedBall hz)
    simp only [g',hh,Complex.ofReal_one,Pi.one_apply]
  obtain ⟨V,hV,hu,he⟩ := spatial_frame_of_left_inverse J K hK
    (isCompact_closedBall (0 : ℂ) (r+1)) Metric.ball_subset_closedBall Metric.isOpen_ball
    (Metric.ball_subset_ball (by linarith : r ≤ r+1)) q A hA hg' hc' (hsupport.trans hs) h1'
  exact ⟨V,hV,hu,fun x hx => he x (hr (Set.mem_image_of_mem K hx))⟩
end
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

/-- Genuine invertible transport frames on any finite dimensional complex
fiber, with arbitrary smooth coefficients. Applies to the rank-three physical
null hyperplane plus scalar fiber, without assuming a frame exists. -/
theorem exists_spatial_linear_frame (J : ℂ →L[ℝ] E) (hJ : Function.Injective J)
    (A : E → F →L[ℂ] F) (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    {C : Set E} (hC : IsCompact C) :
    ∃ V : E → F →L[ℂ] F, ContDiff ℝ (⊤ : ℕ∞) V ∧
      (∀ x, IsUnit (V x)) ∧
      ∀ x∈C, fderiv ℝ V x (J 1)+I • fderiv ℝ V x (J I)=A x*V x := by
  let : CompleteSpace F := FiniteDimensional.complete ℂ F
  exact exists_spatial_frame J hJ (Module.finBasis ℂ (F →L[ℂ] F)) A hA hC

end ElasticityPlanar
namespace ElasticityParameter
open scoped BigOperators InnerProductSpace

lemma real_complex_plane_injective {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : E) (ha : a≠0) (hb : b≠0) (hab : inner ℝ a b=0) :
    Function.Injective (Complex.reCLM.smulRight a+Complex.imCLM.smulRight b : ℂ →L[ℝ] E) := by
  let J : ℂ →L[ℝ] E := Complex.reCLM.smulRight a+Complex.imCLM.smulRight b
  suffices hn : ∀ z : ℂ, J z=0 → z=0 by
    intro z w h
    apply sub_eq_zero.mp
    apply hn
    rw [map_sub,h,sub_self]
  intro z hz
  have ha0 : inner ℝ a a≠0 := by
    intro h
    exact ha (inner_self_eq_zero.mp h)
  have hb0 : inner ℝ b b≠0 := by
    intro h
    exact hb (inner_self_eq_zero.mp h)
  have hba : inner ℝ b a=0 := by rwa [real_inner_comm]
  have hr := congrArg (fun v : E => inner ℝ a v) hz
  have hi := congrArg (fun v : E => inner ℝ b v) hz
  change inner ℝ a (z.re • a+z.im • b)=inner ℝ a 0 at hr
  change inner ℝ b (z.re • a+z.im • b)=inner ℝ b 0 at hi
  simp only [inner_add_right,inner_smul_right,hab,hba,mul_zero,zero_add,add_zero,inner_zero_right] at hr hi
  apply Complex.ext
  · exact (mul_eq_zero.mp hr).resolve_right ha0
  · exact (mul_eq_zero.mp hi).resolve_right hb0

lemma basis_sum_apply (v : Fin 3 → ℝ) (i : Fin 3) :
    (∑ r, v r • basis r : X) i=v i := by
  simp [basis,Pi.single_apply]

lemma null_re_im (θ : Fin 3 → ℂ) (hθ : ∑ i, θ i*θ i=0) :
    (∑ i, (θ i).re*(θ i).re)=(∑ i, (θ i).im*(θ i).im) ∧
      (∑ i, (θ i).re*(θ i).im)=0 := by
  have hr := congrArg Complex.re hθ
  have hi := congrArg Complex.im hθ
  simp only [Complex.re_sum,Complex.mul_re,Complex.zero_re,Finset.sum_sub_distrib] at hr
  simp only [Complex.im_sum,Complex.mul_im,Complex.zero_im,Finset.sum_add_distrib] at hi
  have he : (∑ i, (θ i).im*(θ i).re)=(∑ i, (θ i).re*(θ i).im) :=
    Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [he] at hi
  constructor
  · exact sub_eq_zero.mp hr
  · linarith

lemma null_plane_injective (θ : Fin 3 → ℂ) (hθ : ∑ i, θ i*θ i=0) (hne : θ≠0) :
    Function.Injective (characteristicPlane basis θ) := by
  obtain ⟨hre,him⟩ := null_re_im θ hθ
  let a : X := ∑ i, (θ i).re • basis i
  let b : X := ∑ i, (θ i).im • basis i
  have hai (i : Fin 3) : a i=(θ i).re := basis_sum_apply _ i
  have hbi (i : Fin 3) : b i=(θ i).im := basis_sum_apply _ i
  have haa : inner ℝ a a=∑ i, (θ i).re*(θ i).re := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,hai]
  have hbb : inner ℝ b b=∑ i, (θ i).im*(θ i).im := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,hbi]
  have hab : inner ℝ a b=0 := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,hai,hbi]
    simpa only [mul_comm] using him
  have he : inner ℝ a a=inner ℝ b b := by rw [haa,hbb,hre]
  have hboth : ¬ (a=0 ∧ b=0) := by
    rintro ⟨ha,hb⟩
    apply hne
    funext i
    apply Complex.ext
    · simpa only [ha,PiLp.zero_apply,Pi.zero_apply,Complex.zero_re] using (hai i).symm
    · simpa only [hb,PiLp.zero_apply,Pi.zero_apply,Complex.zero_im] using (hbi i).symm
  have ha : a≠0 := by
    intro hz
    apply hboth
    refine ⟨hz,(@inner_self_eq_zero ℝ X _ _ _).mp ?_⟩
    rw [← he,hz,inner_zero_left]
  have hb : b≠0 := by
    intro hz
    apply ha
    apply (@inner_self_eq_zero ℝ X _ _ _).mp
    rw [he,hz,inner_zero_left]
  exact real_complex_plane_injective a b ha hb hab
end ElasticityParameter
namespace ElasticityFrame
open Set Complex Module
open scoped BigOperators

lemma finrank_fiber (θ : Fin 3 → ℂ) (hne : θ≠0) : Module.finrank ℂ (Fiber θ)=3 := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hne
  change θ i≠0 at hi
  have hs : Function.Surjective (normal θ) := by
    intro c
    refine ⟨(Pi.single i (c/(θ i)),0),?_⟩
    change (∑ j,θ j*(Pi.single i (c/(θ i)) : Fin 3 → ℂ) j)=c
    simp [Pi.single_apply]
    field_simp [hi]
  have he := (normal θ).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs,finrank_top] at he
  change Module.finrank ℂ ℂ+Module.finrank ℂ (Fiber θ)=Module.finrank ℂ Amp at he
  simp only [Module.finrank_self,Module.finrank_prod,Module.finrank_pi,Fintype.card_fin] at he
  omega

lemma connection_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (t : E → ℂ) (q : Fin 3 → E → ℂ)
    (ht : ContDiff ℝ (⊤ : ℕ∞) t) (hq : ∀ i,ContDiff ℝ (⊤ : ℕ∞) (q i)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => connection θ hθ (t x) (fun i => q i x)) := by
  have hs (B : Fiber θ →L[ℂ] Fiber θ) {f : E → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
      ContDiff ℝ (⊤ : ℕ∞) (fun x => f x • B) := by
    exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := ℂ) (F := Fiber θ →L[ℂ] Fiber θ)
      (((ContinuousLinearMap.id ℂ ℂ).smulRight B).restrictScalars ℝ)).comp hf
  exact (contDiff_const.add (hs _ ht)).add (ContDiff.sum (fun i _ => hs _ (hq i)))

/-- The actual rank-three constrained transport admits a smooth invertible
frame on every compact physical region. The null-plane geometry and smooth
planar solvability are proved dependencies, not existence hypotheses. -/
theorem exists_constraint_frame (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (hne : θ≠0)
    (t : X → ℂ) (q : Fin 3 → X → ℂ)
    (ht : ContDiff ℝ (⊤ : ℕ∞) t) (hq : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (q i))
    {C : Set X} (hC : IsCompact C) :
    ∃ V : X → Fiber θ →L[ℂ] Fiber θ, ContDiff ℝ (⊤ : ℕ∞) V ∧
      (∀ x,IsUnit (V x)) ∧
      ∀ x∈C, fderiv ℝ V x (ElasticityParameter.characteristicPlane ElasticityParameter.basis θ 1)+
        I • fderiv ℝ V x (ElasticityParameter.characteristicPlane ElasticityParameter.basis θ I)=
        connection θ hθ (t x) (fun i => q i x)*V x := by
  exact ElasticityPlanar.exists_spatial_linear_frame
    (ElasticityParameter.characteristicPlane ElasticityParameter.basis θ)
    (ElasticityParameter.null_plane_injective θ hθ hne)
    (fun x => connection θ hθ (t x) (fun i => q i x)) (connection_smooth θ hθ t q ht hq) hC
end ElasticityFrame
section
open Set Complex Module
open scoped BigOperators
namespace ElasticityFrame

/-- Three genuine independent smooth columns for the null constrained system,
on an arbitrary compact physical region. -/
theorem exists_constraint_columns_oai (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (hne : θ≠0)
    (t : X → ℂ) (q : Fin 3 → X → ℂ)
    (ht : ContDiff ℝ (⊤ : ℕ∞) t) (hq : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (q i))
    {C : Set X} (hC : IsCompact C) :
    ∃ B : X → Basis (Fin 3) ℂ (Fiber θ),
      (∀ ν, ContDiff ℝ (⊤ : ℕ∞) (fun x => B x ν)) ∧
      ∀ ν x, x∈C →
        fderiv ℝ (fun x => B x ν) x (ElasticityParameter.characteristicPlane ElasticityParameter.basis θ 1)+
          I • fderiv ℝ (fun x => B x ν) x (ElasticityParameter.characteristicPlane ElasticityParameter.basis θ I)=
          connection θ hθ (t x) (fun i => q i x) (B x ν) := by
  obtain ⟨V,hV,hu,he⟩ := exists_constraint_frame θ hθ hne t q ht hq hC
  let : CompleteSpace (Fiber θ) := FiniteDimensional.complete ℂ (Fiber θ)
  let b := Module.finBasisOfFinrankEq ℂ (Fiber θ) (finrank_fiber θ hne)
  let B : X → Basis (Fin 3) ℂ (Fiber θ) := fun x =>
    b.map (LinearEquiv.ofBijective (V x).toLinearMap (ContinuousLinearMap.isUnit_iff_bijective.mp (hu x)))
  have hB (ν) : ContDiff ℝ (⊤ : ℕ∞) (fun x => B x ν) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun x => V x (b ν))
    exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := Fiber θ →L[ℂ] Fiber θ) (F := Fiber θ)
      ((ContinuousLinearMap.apply ℂ (Fiber θ) (b ν)).restrictScalars ℝ)).comp hV
  refine ⟨B,hB,fun ν x hx => ?_⟩
  have hd (v : X) : fderiv ℝ (fun x => B x ν) x v=fderiv ℝ V x v (b ν) := by
    have hh := ((ContinuousLinearMap.apply ℂ (Fiber θ) (b ν)).restrictScalars ℝ).hasFDerivAt.comp x
      ((hV.differentiable (by simp)) x).hasFDerivAt
    change HasFDerivAt (fun x => B x ν) _ x at hh
    rw [hh.fderiv]
    rfl
  rw [hd,hd]
  exact congrArg (fun L : Fiber θ →L[ℂ] Fiber θ => L (b ν)) (he x hx)

end ElasticityFrame

end

end

end OAI
end

theorem solution : type_of% @OAI.ElasticityFrame.exists_constraint_columns_oai := @OAI.ElasticityFrame.exists_constraint_columns_oai
