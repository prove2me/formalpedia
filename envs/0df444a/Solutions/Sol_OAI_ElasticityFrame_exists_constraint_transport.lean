-- Prove2me | solution 1 for OAI.ElasticityFrame.exists_constraint_transport
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:54:28.30722+00:00
-- url     : https://prove2.me/submissions/c82c4e20-6153-451c-aaf5-bc92e6363f4a

import Mathlib
import Definitions.Def_OAIQ6El002
import Definitions.Def_OAIQ6El003
import Theorems.Thm_OAI_ElasticityPlanar_exists_spatial_transport

section
-- module Solutions.OAIQ6_Elast.Elasticity_Transport
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

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

lemma connection_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (t : E → ℂ) (q : Fin 3 → E → ℂ)
    (ht : ContDiff ℝ (⊤ : ℕ∞) t) (hq : ∀ i,ContDiff ℝ (⊤ : ℕ∞) (q i)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => connection θ hθ (t x) (fun i => q i x)) := by
  have hs (B : Fiber θ →L[ℂ] Fiber θ) {f : E → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
      ContDiff ℝ (⊤ : ℕ∞) (fun x => f x • B) := by
    exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := ℂ) (F := Fiber θ →L[ℂ] Fiber θ)
      (((ContinuousLinearMap.id ℂ ℂ).smulRight B).restrictScalars ℝ)).comp hf
  exact (contDiff_const.add (hs _ ht)).add (ContDiff.sum (fun i _ => hs _ (hq i)))

end ElasticityFrame
namespace ElasticityPlanar
open Set Complex Module
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

/-- Inhomogeneous spatial transport on an actual finite-dimensional complex
fiber, not a postulated planar inverse. -/
theorem exists_spatial_linear_transport (J : ℂ →L[ℝ] E) (hJ : Function.Injective J)
    (A : E → F →L[ℂ] F) (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (f : E → F) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {C : Set E} (hC : IsCompact C) :
    ∃ u : E → F, ContDiff ℝ (⊤ : ℕ∞) u ∧
      ∀ x∈C, fderiv ℝ u x (J 1)+I • fderiv ℝ u x (J I)=A x (u x)+f x := by
  let q := Module.finBasis ℂ F
  let L : F ≃L[ℂ] (Fin (Module.finrank ℂ F) → ℂ) := q.equivFun.toContinuousLinearEquiv
  let c (i : Fin (Module.finrank ℂ F)) : F →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj i).comp L.toContinuousLinearMap
  let a := fun i j x => -c i (A x (q j))
  let g := fun i x => c i (f x)
  have ha (i j) : ContDiff ℝ (⊤ : ℕ∞) (a i j) :=
    (((c i).restrictScalars ℝ).contDiff.comp
      (((ContinuousLinearMap.apply ℂ F (q j)).restrictScalars ℝ).contDiff.comp hA)).neg
  have hg (i) : ContDiff ℝ (⊤ : ℕ∞) (g i) := ((c i).restrictScalars ℝ).contDiff.comp hf
  obtain ⟨v,hv,he⟩ := exists_spatial_transport J hJ a ha g hg hC
  let u : E → F := fun x => L.symm (fun i => v i x)
  have hu : ContDiff ℝ (⊤ : ℕ∞) u :=
    (L.symm.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp (contDiff_pi.mpr hv)
  have hcoord (i) : (fun x => c i (u x))=v i := by
    funext x
    change L (L.symm (fun i => v i x)) i=v i x
    rw [ContinuousLinearEquiv.apply_symm_apply]
  have hmat (x : E) (i) : c i (A x (u x))=∑ j,c i (A x (q j))*v j x := by
    have hex : u x=∑ j,L (u x) j • q j := (q.sum_equivFun _).symm
    conv_lhs => rw [hex]
    simp only [map_sum,map_smul,smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    have hc : L (u x) j=v j x := congrFun (hcoord j) x
    rw [hc,mul_comm]
  refine ⟨u,hu,fun x hx => ?_⟩
  apply L.injective
  ext i
  change c i (fderiv ℝ u x (J 1)+I • fderiv ℝ u x (J I))=c i (A x (u x)+f x)
  have hd (z : ℂ) : c i (fderiv ℝ u x (J z))=fderiv ℝ (v i) x (J z) := by
    have hh := ((c i).restrictScalars ℝ).hasFDerivAt.comp x ((hu.differentiable (by simp)) x).hasFDerivAt
    change HasFDerivAt (fun x => c i (u x)) _ x at hh
    rw [hcoord] at hh
    rw [hh.fderiv]
    rfl
  rw [map_add,map_smul,hd 1,hd I,map_add,hmat]
  have hh := he i x hx
  simp only [a,g,neg_mul,Finset.sum_neg_distrib] at hh
  change _+I*_=_+_
  linear_combination hh
end ElasticityPlanar
section
open Set Complex Module
open scoped BigOperators
namespace ElasticityFrame

/-- Inhomogeneous constrained transport has actual smooth solutions as well. -/
theorem exists_constraint_transport_oai (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (hne : θ≠0)
    (t : X → ℂ) (q : Fin 3 → X → ℂ)
    (ht : ContDiff ℝ (⊤ : ℕ∞) t) (hq : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (q i))
    (f : X → Fiber θ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {C : Set X} (hC : IsCompact C) :
    ∃ u : X → Fiber θ, ContDiff ℝ (⊤ : ℕ∞) u ∧
      ∀ x∈C, fderiv ℝ u x (ElasticityParameter.characteristicPlane ElasticityParameter.basis θ 1)+
        I • fderiv ℝ u x (ElasticityParameter.characteristicPlane ElasticityParameter.basis θ I)=
        connection θ hθ (t x) (fun i => q i x) (u x)+f x := by
  exact ElasticityPlanar.exists_spatial_linear_transport
    (ElasticityParameter.characteristicPlane ElasticityParameter.basis θ)
    (ElasticityParameter.null_plane_injective θ hθ hne)
    (fun x => connection θ hθ (t x) (fun i => q i x)) (connection_smooth θ hθ t q ht hq) f hf hC
end ElasticityFrame

end

end

end OAI
end

theorem solution : type_of% @OAI.ElasticityFrame.exists_constraint_transport_oai := @OAI.ElasticityFrame.exists_constraint_transport_oai
