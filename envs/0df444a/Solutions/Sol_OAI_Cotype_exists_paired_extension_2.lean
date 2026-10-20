-- Prove2me | solution 2 for OAI.Cotype.exists_paired_extension
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:13:35.636092+00:00
-- url     : https://prove2.me/submissions/a6821088-64c4-4534-b400-a6e1ca40ca5d

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/PairedExtension.lean:L87-L125
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.exists_paired_extension. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

-- ---- from OAI.Analysis.Cotype.PairedExtension ----
namespace OAI

noncomputable section

namespace Cotype
open LinearMap
variable {𝕜 A K W E : Type*} [Field 𝕜]
  [AddCommGroup A] [Module 𝕜 A] [AddCommGroup K] [Module 𝕜 K]
  [AddCommGroup W] [Module 𝕜 W] [AddCommGroup E] [Module 𝕜 E]

theorem exists_factor_of_ker_le (b : A →ₗ[𝕜] W) (d : A →ₗ[𝕜] K)
    (h : ker b ≤ ker d) : ∃ L : W →ₗ[𝕜] K, L.comp b = d := by
  let q := (ker b).liftQ d h
  let f := q.comp b.quotKerEquivRange.symm.toLinearMap
  obtain ⟨L,hL⟩ := f.exists_extend
  refine ⟨L, ?_⟩
  ext x
  have hh := congrArg (fun z : range b →ₗ[𝕜] K => z ⟨b x, mem_range_self b x⟩) hL
  simpa [f, q] using hh

theorem exists_shear_extension [FiniteDimensional 𝕜 K]
    (a a' : A →ₗ[𝕜] K) (b : A →ₗ[𝕜] W)
    (ha : Function.Injective (a.prod b)) (ha' : Function.Injective (a'.prod b)) :
    ∃ (H : (K × W) ≃ₗ[𝕜] (K × W)),
      (∀ x, H (a x, b x) = (a' x, b x)) ∧ ∀ z, (H z).2 = z.2 := by
  let c := a.comp (ker b).subtype
  let c' := a'.comp (ker b).subtype
  have hc : Function.Injective c := by
    intro x y h
    apply Subtype.ext
    apply ha
    exact Prod.ext h (by simp)
  have hc' : Function.Injective c' := by
    intro x y h
    apply Subtype.ext
    apply ha'
    exact Prod.ext h (by simp)
  let e := (LinearEquiv.ofInjective c hc).symm.trans (LinearEquiv.ofInjective c' hc')
  obtain ⟨S,hS⟩ := Submodule.exists_linearEquiv_restrict_eq e
  have hSc (x : ker b) : S (a x) = a' x := by
    have hh := hS (LinearEquiv.ofInjective c hc x)
    simpa [e, c, c'] using hh.symm
  have hd : ker b ≤ ker (a' - S.toLinearMap.comp a) := by
    intro x hx
    change a' x - S (a x) = 0
    exact sub_eq_zero.mpr (hSc ⟨x,hx⟩).symm
  obtain ⟨L,hL⟩ := exists_factor_of_ker_le b (a' - S.toLinearMap.comp a) hd
  let H : (K × W) ≃ₗ[𝕜] (K × W) :=
    { toFun := fun z => (S z.1 + L z.2, z.2)
      invFun := fun z => (S.symm (z.1 - L z.2), z.2)
      left_inv := by intro z; simp
      right_inv := by intro z; simp
      map_add' := by intro x y; ext <;> simp [add_assoc, add_left_comm, add_comm]
      map_smul' := by intro t x; ext <;> simp [smul_add] }
  refine ⟨H, ?_, fun z => rfl⟩
  intro x
  apply Prod.ext
  · change S (a x) + L (b x) = a' x
    have hh := LinearMap.congr_fun hL x
    change L (b x) = a' x - S (a x) at hh
    rw [hh]; abel
  · rfl

theorem exists_surjection_split [FiniteDimensional 𝕜 W]
    (p : E →ₗ[𝕜] W) (hp : Function.Surjective p) :
    ∃ e : E ≃ₗ[𝕜] (ker p × W), ∀ x, (e x).2 = p x := by
  obtain ⟨s,hs⟩ := p.exists_rightInverse_of_surjective (range_eq_top.mpr hp)
  have hsx (w : W) : p (s w) = w := LinearMap.congr_fun hs w
  let e : E ≃ₗ[𝕜] (ker p × W) :=
    { toFun := fun x => (⟨x - s (p x), by simp [hsx]⟩, p x)
      invFun := fun z => z.1 + s z.2
      left_inv := by intro x; simp
      right_inv := by
        intro z
        apply Prod.ext
        · apply Subtype.ext; simp [map_add, hsx]
        · simp [map_add, hsx]
      map_add' := by intro x y; apply Prod.ext <;> simp [map_add, sub_add_sub_comm]
      map_smul' := by intro t x; apply Prod.ext <;> simp [map_smul, smul_sub] }
  exact ⟨e, fun x => rfl⟩

theorem exists_paired_extension [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 W]
    (f f' : A →ₗ[𝕜] E) (p p' : E →ₗ[𝕜] W)
    (hf : Function.Injective f) (hf' : Function.Injective f')
    (hp : Function.Surjective p) (hp' : Function.Surjective p')
    (hpair : p.comp f = p'.comp f') :
    ∃ H : E ≃ₗ[𝕜] E, (∀ x, H (f x) = f' x) ∧ ∀ x, p' (H x) = p x := by
  obtain ⟨e,he⟩ := exists_surjection_split p hp
  obtain ⟨e',he'⟩ := exists_surjection_split p' hp'
  have hdim : Module.finrank 𝕜 (ker p') = Module.finrank 𝕜 (ker p) := by
    have h := p.finrank_range_add_finrank_ker
    have h' := p'.finrank_range_add_finrank_ker
    rw [range_eq_top.mpr hp] at h
    rw [range_eq_top.mpr hp'] at h'
    omega
  let k : ker p' ≃ₗ[𝕜] ker p := LinearEquiv.ofFinrankEq _ _ hdim
  let t := e'.trans (k.prodCongr (LinearEquiv.refl 𝕜 W))
  have ht (x : E) : (t x).2 = p' x := he' x
  let a := (fst 𝕜 (ker p) W).comp (e.toLinearMap.comp f)
  let a' := (fst 𝕜 (ker p) W).comp (t.toLinearMap.comp f')
  let b := p.comp f
  have hb (x : A) : p (f x) = p' (f' x) := LinearMap.congr_fun hpair x
  have hab (x : A) : (a x, b x) = e (f x) := Prod.ext rfl (he _).symm
  have hab' (x : A) : (a' x, b x) = t (f' x) := Prod.ext rfl ((hb x).trans (ht _).symm)
  have ha : Function.Injective (a.prod b) := by
    intro x y h; apply hf; apply e.injective
    change (a x, b x) = (a y, b y) at h
    simpa only [hab] using h
  have ha' : Function.Injective (a'.prod b) := by
    intro x y h; apply hf'; apply t.injective
    change (a' x, b x) = (a' y, b y) at h
    simpa only [hab'] using h
  obtain ⟨S,hSf,hSp⟩ := exists_shear_extension a a' b ha ha'
  refine ⟨e.trans (S.trans t.symm), ?_, ?_⟩
  · intro x
    change t.symm (S (e (f x))) = f' x
    rw [← hab, hSf, hab', t.symm_apply_apply]
  · intro x
    change p' (t.symm (S (e x))) = p x
    rw [← ht, t.apply_symm_apply, hSp, he]

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open LinearMap


theorem solution : type_of% @_root_.OAI.Cotype.exists_paired_extension := @_root_.OAI.Cotype.exists_paired_extension
