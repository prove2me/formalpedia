-- Prove2me | solution 1 for OAI.Cotype.walsh_paired_frames_orbit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T22:13:22.668793+00:00
-- url     : https://prove2.me/submissions/e5bfdca4-f92b-4b28-90bc-80ea05e4bb9e

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
import Definitions.Def_OAI_Analysis_Cotype_FrameOrbit
import Definitions.Def_OAI_Analysis_Cotype_BinaryCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshFrameOrbit

open OAI OAI.Cotype
variable {n r s : ℕ}
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
lemma h51_pext {𝕜 A W E : Type*} [Field 𝕜]
    [AddCommGroup A] [Module 𝕜 A] [AddCommGroup W] [Module 𝕜 W] [AddCommGroup E] [Module 𝕜 E]
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 W]
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

lemma h51_evsurj {𝕜 κ E : Type*} [Field 𝕜] [Fintype κ] [DecidableEq κ] [AddCommGroup E] [Module 𝕜 E]
    [FiniteDimensional 𝕜 E] (V : κ → Module.Dual 𝕜 E) (hV : LinearIndependent 𝕜 V) :
    Function.Surjective (LinearMap.pi (fun j => V j) : E →ₗ[𝕜] (κ → 𝕜)) := by
  rw [← LinearMap.dualMap_injective_iff]
  rw [injective_iff_map_eq_zero]
  intro φ hφ
  have hsum : ∑ j, φ (Pi.single j 1) • V j = 0 := by
    ext x
    have := congrArg (fun ψ => ψ x) hφ
    simp only [LinearMap.dualMap_apply, LinearMap.zero_apply] at this
    have hx : (LinearMap.pi (fun j => V j) x : κ → 𝕜) = ∑ j, (V j x) • Pi.single j 1 := by
      ext i; simp [Finset.sum_apply, Pi.single_apply]
    rw [LinearMap.zero_apply, ← this, hx, map_sum]
    simp [mul_comm]
  have hz := (Fintype.linearIndependent_iff.mp hV) _ hsum
  ext i
  simpa using hz i
lemma h51_pfo {𝕜 : Type*} [Field 𝕜] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {E : Type*} [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
    (U U' : ι → E) (V V' : κ → Module.Dual 𝕜 E)
    (hU : LinearIndependent 𝕜 U) (hU' : LinearIndependent 𝕜 U')
    (hV : LinearIndependent 𝕜 V) (hV' : LinearIndependent 𝕜 V')
    (hpair : ∀ i j, V j (U i) = V' j (U' i)) :
    ∃ H : E ≃ₗ[𝕜] E, (∀ i, H (U i) = U' i) ∧ ∀ j x, V' j (H x) = V j x := by
  classical
  let f : (ι → 𝕜) →ₗ[𝕜] E := Fintype.linearCombination 𝕜 U
  let f' : (ι → 𝕜) →ₗ[𝕜] E := Fintype.linearCombination 𝕜 U'
  let p : E →ₗ[𝕜] (κ → 𝕜) := LinearMap.pi (fun j => V j)
  let p' : E →ₗ[𝕜] (κ → 𝕜) := LinearMap.pi (fun j => V' j)
  have hpair' : p.comp f = p'.comp f' := by
    ext a j
    simp [p, p', f, f', Fintype.linearCombination_apply, hpair]
  obtain ⟨H, hH1, hH2⟩ := h51_pext f f' p p' hU.fintypeLinearCombination_injective
    hU'.fintypeLinearCombination_injective (h51_evsurj V hV) (h51_evsurj V' hV') hpair'
  refine ⟨H, fun i => ?_, fun j x => ?_⟩
  · have := hH1 (Pi.single i 1)
    simpa [f, f', Fintype.linearCombination_apply, Pi.single_apply] using this
  · have := congrArg (fun y => y j) (hH2 x)
    simpa [p, p'] using this

lemma h51_bsign_inj (a b : ZMod 2) (h : binarySign a = binarySign b) : a = b := by
  rcases binary_eq_zero_or_one a with rfl | rfl <;> rcases binary_eq_zero_or_one b with rfl | rfl <;>
    simp_all <;> norm_num at h

theorem solution (U U' : Fin r → Cube n) (V V' : Fin s → Cube n)
    (hU : BinaryFrame U) (hU' : BinaryFrame U')
    (hV : BinaryFrame V) (hV' : BinaryFrame V')
    (hpair : ∀ i j, character (V j) (U i) = character (V' j) (U' i)) :
    ∃ g : WalshSymmetry n,
      (∀ i, primalSymmetry g (U i) = U' i) ∧ ∀ j, dualSymmetry g (V j) = V' j := by
  classical
  set β := cubeBinaryEquiv n
  let CD : BinarySpace n ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (BinarySpace n) := coordinateDual
  have hVd : LinearIndependent (ZMod 2) (fun j => CD (β (V j))) :=
    hV.map' CD.toLinearMap CD.ker
  have hVd' : LinearIndependent (ZMod 2) (fun j => CD (β (V' j))) :=
    hV'.map' CD.toLinearMap CD.ker
  have hpair' : ∀ i j, CD (β (V j)) (β (U i)) = CD (β (V' j)) (β (U' i)) := by
    intro i j
    apply h51_bsign_inj
    have := hpair i j
    rw [character_binary_dot, character_binary_dot] at this
    exact this
  obtain ⟨H, hH1, hH2⟩ := h51_pfo (fun i => β (U i)) (fun i => β (U' i))
    (fun j => CD (β (V j))) (fun j => CD (β (V' j))) hU hU' hVd hVd' hpair'
  let G : BinarySpace n ≃ BinarySpace n :=
    { toFun := fun v => CD.symm ((CD v).comp H.symm.toLinearMap)
      invFun := fun v => CD.symm ((CD v).comp H.toLinearMap)
      left_inv := fun v => by
        apply CD.injective
        simp only [LinearEquiv.apply_symm_apply]
        ext x; simp
      right_inv := fun v => by
        apply CD.injective
        simp only [LinearEquiv.apply_symm_apply]
        ext x; simp }
  have hG : ∀ u v, CD (G v) (H u) = CD v u := by
    intro u v
    simp [G]
  let g1 : Equiv.Perm (Cube n) := β.trans (H.toEquiv.trans β.symm)
  let g2 : Equiv.Perm (Cube n) := β.trans (G.trans β.symm)
  have hmem : (g1, g2) ∈ walshSymmetryGroup n := by
    intro u v
    show character (β.symm (G (β v))) (β.symm (H (β u))) = character v u
    rw [character_binary_dot, character_binary_dot, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact congrArg binarySign (hG (β u) (β v))
  refine ⟨⟨(g1, g2), hmem⟩, fun i => ?_, fun j => ?_⟩
  · show β.symm (H (β (U i))) = U' i
    rw [hH1 i]; simp
  · show β.symm (G (β (V j))) = V' j
    rw [Equiv.symm_apply_eq]
    apply CD.injective
    simp only [G, Equiv.coe_fn_mk, LinearEquiv.apply_symm_apply]
    refine LinearMap.ext (fun x => ?_)
    have := hH2 j (H.symm x)
    simp only [LinearEquiv.apply_symm_apply] at this
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    exact this.symm

