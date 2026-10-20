-- Prove2me | solution 1 for OAI.Cotype.exists_paired_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T22:07:37.969283+00:00
-- url     : https://prove2.me/submissions/49aab28b-9158-4d93-9f2b-e5a921c14eb7

import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
import Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent
import Definitions.Def_OAI_Analysis_Cotype_SectorResolvent
import Definitions.Def_OAI_Analysis_Cotype_FiniteContour
import Definitions.Def_OAI_Analysis_Cotype_NoiseHypercontractivity
import Definitions.Def_OAI_Analysis_Cotype_QuadraticTypeTensor
import Definitions.Def_OAI_Analysis_Cotype_WalshAmplification
import Definitions.Def_OAI_Analysis_Cotype_FiniteL2Dual
import Definitions.Def_OAI_Analysis_Cotype_DualMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_FiniteSupDual
import Definitions.Def_OAI_Analysis_Cotype_PrimalMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_CotypeAmplification
import Definitions.Def_OAI_Analysis_Cotype_TypeCotypeDuality
import Definitions.Def_OAI_Analysis_Cotype_Rectangles
import Definitions.Def_OAI_Analysis_Cotype_BinaryRank
import Definitions.Def_OAI_Analysis_Cotype_BiasedFourier
import Definitions.Def_OAI_Analysis_Cotype_Damping
import Definitions.Def_OAI_Analysis_Cotype_WalshExactPairing
import Definitions.Def_OAI_Analysis_Cotype_WalshSymmetry
import Definitions.Def_OAI_Analysis_Cotype_CubeCoordinateProjections
import Definitions.Def_OAI_Analysis_Cotype_CubeFirstChaos

open OAI OAI.Cotype
open LinearMap
variable {𝕜 A K W E : Type*} [Field 𝕜]
  [AddCommGroup A] [Module 𝕜 A] [AddCommGroup K] [Module 𝕜 K]
  [AddCommGroup W] [Module 𝕜 W] [AddCommGroup E] [Module 𝕜 E]
/-- extend an isomorphism between images of injective maps to an iso of the ambient spaces -/
lemma h51_core {𝕜 B N N' : Type*} [Field 𝕜] [AddCommGroup B] [Module 𝕜 B]
    [AddCommGroup N] [Module 𝕜 N] [AddCommGroup N'] [Module 𝕜 N']
    [FiniteDimensional 𝕜 N] [FiniteDimensional 𝕜 N']
    (φ : B →ₗ[𝕜] N) (φ' : B →ₗ[𝕜] N') (hφ : Function.Injective φ) (hφ' : Function.Injective φ')
    (hdim : Module.finrank 𝕜 N = Module.finrank 𝕜 N') :
    ∃ T : N ≃ₗ[𝕜] N', ∀ b, T (φ b) = φ' b := by
  haveI : FiniteDimensional 𝕜 B := Module.Finite.of_injective φ hφ
  set S := LinearMap.range φ
  set S' := LinearMap.range φ'
  let e : B ≃ₗ[𝕜] S := LinearEquiv.ofInjective φ hφ
  let e' : B ≃ₗ[𝕜] S' := LinearEquiv.ofInjective φ' hφ'
  let σ : S ≃ₗ[𝕜] S' := e.symm.trans e'
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl S
  obtain ⟨C', hC'⟩ := Submodule.exists_isCompl S'
  have h1 := Submodule.finrank_add_eq_of_isCompl hC
  have h2 := Submodule.finrank_add_eq_of_isCompl hC'
  have h3 : Module.finrank 𝕜 S = Module.finrank 𝕜 S' := by
    rw [← e.finrank_eq, ← e'.finrank_eq]
  have hCC : Module.finrank 𝕜 C = Module.finrank 𝕜 C' := by omega
  let τ : C ≃ₗ[𝕜] C' := LinearEquiv.ofFinrankEq C C' hCC
  let T : N ≃ₗ[𝕜] N' := ((Submodule.prodEquivOfIsCompl S C hC).symm.trans (σ.prodCongr τ)).trans
    (Submodule.prodEquivOfIsCompl S' C' hC')
  refine ⟨T, fun b => ?_⟩
  have hb : (⟨φ b, LinearMap.mem_range_self φ b⟩ : S) = e b := rfl
  simp only [T, LinearEquiv.trans_apply]
  have : (Submodule.prodEquivOfIsCompl S C hC).symm (φ b) = (⟨φ b, LinearMap.mem_range_self φ b⟩, 0) :=
    Submodule.prodEquivOfIsCompl_symm_apply_left S C hC ⟨φ b, LinearMap.mem_range_self φ b⟩
  rw [this, hb]
  simp [σ, e']
  rfl

/-- factor a linear map through another one whose kernel is smaller -/
lemma h51_factor {𝕜 M E V : Type*} [Field 𝕜] [AddCommGroup M] [Module 𝕜 M]
    [AddCommGroup E] [Module 𝕜 E] [AddCommGroup V] [Module 𝕜 V]
    (Ψ : M →ₗ[𝕜] E) (Φ : M →ₗ[𝕜] V) (h : LinearMap.ker Ψ ≤ LinearMap.ker Φ) :
    ∃ L : E →ₗ[𝕜] V, ∀ x, L (Ψ x) = Φ x := by
  let L0 : LinearMap.range Ψ →ₗ[𝕜] V :=
    ((LinearMap.ker Ψ).liftQ Φ h).comp Ψ.quotKerEquivRange.symm.toLinearMap
  obtain ⟨L, hL⟩ := LinearMap.exists_extend L0
  refine ⟨L, fun x => ?_⟩
  have : L (Ψ x) = L0 ⟨Ψ x, LinearMap.mem_range_self Ψ x⟩ := by
    rw [← hL]; rfl
  rw [this]
  simp [L0]

theorem solution [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 W]
    (f f' : A →ₗ[𝕜] E) (p p' : E →ₗ[𝕜] W)
    (hf : Function.Injective f) (hf' : Function.Injective f')
    (hp : Function.Surjective p) (hp' : Function.Surjective p')
    (hpair : p.comp f = p'.comp f') :
    ∃ H : E ≃ₗ[𝕜] E, (∀ x, H (f x) = f' x) ∧ ∀ x, p' (H x) = p x := by
  classical
  have hdim : Module.finrank 𝕜 (LinearMap.ker p) = Module.finrank 𝕜 (LinearMap.ker p') := by
    have a1 := LinearMap.finrank_range_add_finrank_ker p
    have a2 := LinearMap.finrank_range_add_finrank_ker p'
    rw [LinearMap.range_eq_top.mpr hp, finrank_top] at a1
    rw [LinearMap.range_eq_top.mpr hp', finrank_top] at a2
    omega
  set N := LinearMap.ker p
  set N' := LinearMap.ker p'
  set A0 := LinearMap.ker (p.comp f)
  have hA0 : ∀ a : A0, p (f a) = 0 := fun a => a.2
  have hA0' : ∀ a : A0, p' (f' a) = 0 := fun a => by
    have h := hA0 a
    rw [← LinearMap.comp_apply, ← hpair, LinearMap.comp_apply]; exact h
  let φ : A0 →ₗ[𝕜] N := LinearMap.codRestrict N (f.comp A0.subtype) (fun a => hA0 a)
  let φ' : A0 →ₗ[𝕜] N' := LinearMap.codRestrict N' (f'.comp A0.subtype) (fun a => hA0' a)
  have hφ : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext; apply hf
    have := congrArg Subtype.val hab
    simp only [φ, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply] at this
    exact this
  have hφ' : Function.Injective φ' := by
    intro a b hab
    apply Subtype.ext; apply hf'
    have := congrArg Subtype.val hab
    simp only [φ', LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply] at this
    exact this
  obtain ⟨T, hT⟩ := h51_core φ φ' hφ hφ' hdim
  obtain ⟨s', hs'⟩ := LinearMap.exists_rightInverse_of_surjective p' (LinearMap.range_eq_top.mpr hp')
  have hs'x : ∀ w, p' (s' w) = w := fun w => by
    have := congrArg (fun g => g w) hs'; simpa using this
  let π' : E →ₗ[𝕜] N' := LinearMap.codRestrict N' (LinearMap.id - s'.comp p') (fun e => by
    show _ ∈ LinearMap.ker p'
    rw [LinearMap.mem_ker]; simp [hs'x])
  let Ψ : (A × N) →ₗ[𝕜] E := f.coprod N.subtype
  let Φ : (A × N) →ₗ[𝕜] N' := (π'.comp f').coprod T.toLinearMap
  have hker : LinearMap.ker Ψ ≤ LinearMap.ker Φ := by
    rintro ⟨a, k⟩ hx
    simp only [LinearMap.mem_ker, Ψ, LinearMap.coprod_apply, Submodule.subtype_apply] at hx
    have hpa : p (f a) = 0 := by
      have : p (f a + k) = 0 := by rw [hx, map_zero]
      rw [map_add, k.2, add_zero] at this; exact this
    have ha : a ∈ A0 := by simpa [A0] using hpa
    have hk : k = - φ ⟨a, ha⟩ := by
      apply Subtype.ext; simp [φ]; exact eq_neg_of_add_eq_zero_right hx
    simp only [LinearMap.mem_ker, Φ, LinearMap.coprod_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe]
    rw [hk, map_neg, hT]
    apply Subtype.ext
    have hp'a : p' (f' a) = 0 := hA0' ⟨a, ha⟩
    simp [π', φ', hp'a]
    show f' a + -(f' a) = 0
    simp
  obtain ⟨L, hL⟩ := h51_factor Ψ Φ hker
  let H0 : E →ₗ[𝕜] E := s'.comp p + N'.subtype.comp L
  have hH0p : ∀ x, p' (H0 x) = p x := by
    intro x
    simp only [H0, LinearMap.add_apply, LinearMap.comp_apply, map_add, hs'x, Submodule.subtype_apply]
    rw [(L x).2, add_zero]
  have hH0f : ∀ a, H0 (f a) = f' a := by
    intro a
    have h1 := hL (a, 0)
    simp only [Ψ, Φ, LinearMap.coprod_apply, map_zero, add_zero, LinearMap.comp_apply] at h1
    simp only [H0, LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply, h1]
    simp only [π', LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply]
    rw [show p (f a) = p' (f' a) by
      rw [← LinearMap.comp_apply, hpair, LinearMap.comp_apply]]
    abel
  have hinj : Function.Injective H0 := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hpx : p x = 0 := by rw [← hH0p, hx, map_zero]
    have hxN : x ∈ N := hpx
    have h1 := hL (0, ⟨x, hxN⟩)
    simp only [Ψ, Φ, LinearMap.coprod_apply, map_zero, zero_add, Submodule.subtype_apply,
      LinearEquiv.coe_coe] at h1
    have : H0 x = (T ⟨x, hxN⟩ : E) := by
      simp only [H0, LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply, hpx, map_zero,
        zero_add, h1]
    rw [hx] at this
    have hT0 : T ⟨x, hxN⟩ = 0 := Subtype.ext this.symm
    have := T.injective (hT0.trans (map_zero T).symm)
    simpa using congrArg Subtype.val this
  refine ⟨LinearEquiv.ofInjectiveEndo H0 hinj, fun x => ?_, fun x => ?_⟩
  · exact hH0f x
  · exact hH0p x

