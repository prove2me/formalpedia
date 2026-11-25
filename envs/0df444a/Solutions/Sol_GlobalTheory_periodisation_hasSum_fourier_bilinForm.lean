-- Prove2me | solution 1 for GlobalTheory.periodisation_hasSum_fourier_bilinForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:43:56.052702+00:00
-- url     : https://prove2.me/submissions/2305c62e-c47b-4e74-ad74-5fb2e9cb0ae6

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoisson
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeDualFourierExpansionSchwartz
import Theorems.Thm_GlobalTheory_schwartz_summable_norm_mul_one_add_pow
import Theorems.Thm_GroundTheory_Global_LatticePoisson_hasSum_smul_fourier
import Theorems.Thm_GroundTheory_Global_mem_dualLattice


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open scoped RealInnerProductSpace FourierTransform SchwartzMap
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (P : LinearMap.BilinForm ℝ V) (hP : P.Nondegenerate)
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (f : SchwartzMap V ℂ) :
    ∃ c : V → ℂ, (∀ N : ℕ, Summable (fun μ : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} =>
        ‖c μ‖ * (1 + ‖(μ : V)‖) ^ N)) ∧
      ∀ x : V, HasSum (fun μ : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} =>
        c μ * Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ))) (∑' l : Λ, f (x + l)) := by
  let E := EuclideanSpace ℝ (Fin (finrank ℝ V))
  let T : E ≃L[ℝ] V := (toEuclidean (E := V)).symm
  let A₀ : V ≃ₗ[ℝ] E := (P.flip.toDual hP.flip) ≪≫ₗ T.toLinearEquiv.dualMap ≪≫ₗ
    (LinearMap.BilinForm.toDual (innerₗ E) GroundTheory.Global.innerₗ_nondegenerate).symm
  let A : V ≃L[ℝ] E := A₀.toContinuousLinearEquiv
  have hA : ∀ μ y, ⟪A μ, y⟫ = P (T y) μ := by
    intro μ y
    have h := LinearMap.BilinForm.toDual_def (B := innerₗ E) GroundTheory.Global.innerₗ_nondegenerate
      (m := A₀ μ) (n := y)
    have h2 : ⟪A μ, y⟫ = (innerₗ E) (A₀ μ) y := rfl
    rw [h2, ← h]
    simp only [A₀, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rfl
  let L : Submodule ℤ E := ZLattice.comap ℝ Λ T.toLinearMap
  haveI : DiscreteTopology L := inferInstanceAs (DiscreteTopology (ZLattice.comap ℝ Λ T.toLinearMap))
  haveI : IsZLattice ℝ L := inferInstanceAs (IsZLattice ℝ (ZLattice.comap ℝ Λ T.toLinearMap))
  have hL : ∀ y, y ∈ L ↔ T y ∈ Λ := fun y => Iff.rfl
  let g : 𝓢(E, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ T f
  have hg : ∀ y, g y = f (T y) := fun y => rfl
  let Λ' : Submodule ℤ V := ZLattice.comap ℝ (GroundTheory.Global.dualLattice L) A.toLinearMap
  haveI : DiscreteTopology Λ' :=
    inferInstanceAs (DiscreteTopology (ZLattice.comap ℝ (GroundTheory.Global.dualLattice L) A.toLinearMap))
  have hmem : ∀ μ : V, (∀ l ∈ Λ, ∃ k : ℤ, P l μ = k) ↔ A μ ∈ GroundTheory.Global.dualLattice L := by
    intro μ
    rw [GroundTheory.Global.mem_dualLattice]
    constructor
    · intro h y hy
      rw [hA]
      exact h _ ((hL y).mp hy)
    · intro h l hl
      have := h (T.symm l) ((hL _).mpr (by simpa using hl))
      rwa [hA, T.apply_symm_apply] at this
  let h : 𝓢(V, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ A (𝓕 g)
  have hh : ∀ μ, h μ = 𝓕 (g : E → ℂ) (A μ) := fun μ => rfl
  refine ⟨fun μ => (ZLattice.covolume L)⁻¹ • h μ, fun N => ?_, fun x => ?_⟩
  · let e : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} ≃ Λ' := Equiv.subtypeEquivRight hmem
    have hs := (e.summable_iff.mpr
      (schwartz_summable_norm_mul_one_add_pow Λ' h N)).mul_left ‖(ZLattice.covolume L)⁻¹‖
    refine hs.congr fun μ => ?_
    rw [norm_smul, mul_assoc]
    rfl
  · let e : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} ≃ GroundTheory.Global.dualLattice L :=
      A.toEquiv.subtypeEquiv hmem
    let e' : L ≃ Λ := T.toEquiv.subtypeEquiv hL
    have hs := e.hasSum_iff.mpr
      (GroundTheory.Global.LatticePoisson.hasSum_smul_fourier (L := L) g (T.symm x))
    have hper : GroundTheory.Global.LatticePoisson.per L g (T.symm x) = ∑' l : Λ, f (x + l) := by
      rw [GroundTheory.Global.LatticePoisson.per, ← e'.tsum_eq]
      refine tsum_congr fun l => ?_
      rw [hg, map_add, T.apply_symm_apply]
      rfl
    rw [hper] at hs
    convert hs using 1
    funext μ
    have he : (e μ : E) = A μ := rfl
    simp only [Function.comp_apply, he, hA, T.apply_symm_apply, hh, Real.fourierChar_apply,
      smul_mul_assoc]
    congr 3
    push_cast
    ring
end GlobalTheory
