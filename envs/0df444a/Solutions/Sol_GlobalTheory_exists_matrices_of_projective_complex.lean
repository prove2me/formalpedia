-- Prove2me | solution 1 for GlobalTheory.exists_matrices_of_projective_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:38:10.237885+00:00
-- url     : https://prove2.me/submissions/50ff0e46-a9f0-4685-a3ed-9c565a53bc95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMatricesOfProjectiveComplex
import Theorems.Thm_GlobalTheory_projMatrix_abstract
import Theorems.Thm_GlobalTheory_projMatrix_mulVec
import Theorems.Thm_GlobalTheory_projMatrix_sum
import Theorems.Thm_GlobalTheory_GrSum_map_of
import Theorems.Thm_GlobalTheory_IsGradedMap_id
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GrSum.map_of
attribute [local simp] GlobalTheory.Wick.dividedContraction_one
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] (P₀ P₁ P₂ : Type) [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂] [Module.Finite R P₀] [Module.Projective R P₀] [Module.Finite R P₁] [Module.Projective R P₁] [Module.Finite R P₂] [Module.Projective R P₂] (d₀ : P₀ →ₗ[R] P₁) (d₁ : P₁ →ₗ[R] P₂), d₁ ∘ₗ d₀ = 0 → ∃ (a b c : ℕ) (D₀ : Matrix (Fin b) (Fin a) R) (D₁ : Matrix (Fin c) (Fin b) R) (u : Fin a → P₀), D₁ * D₀ = 0 ∧ ∀ (R' : Type) [CommRing R'] [Algebra R R'], Set.BijOn (fun v : Fin a → R' => ∑ k, v k ⊗ₜ[R] u k) {v | (D₀.map (algebraMap R R')).mulVec v = 0} (LinearMap.ker (d₀.baseChange R')) ∧ (Function.Exact (d₀.baseChange R') (d₁.baseChange R') → ∀ w : Fin b → R', (D₁.map (algebraMap R R')).mulVec w = 0 → ∃ v, (D₀.map (algebraMap R R')).mulVec v = w) := by
  intro R _ P₀ P₁ P₂ _ _ _ _ _ _ _ _ _ _ _ _ d₀ d₁ hd
  obtain ⟨n₀, p₀, s₀, -, -, h₀⟩ := Module.Finite.exists_comp_eq_id_of_projective R P₀
  obtain ⟨n₁, p₁, s₁, -, -, h₁⟩ := Module.Finite.exists_comp_eq_id_of_projective R P₁
  obtain ⟨n₂, p₂, s₂, -, -, h₂⟩ := Module.Finite.exists_comp_eq_id_of_projective R P₂
  have hE : ∀ n m : ℕ, Nonempty ((Fin (n + m) → R) ≃ₗ[R] (Fin n → R) × (Fin m → R)) :=
    fun n m => ⟨(LinearEquiv.funCongrLeft R R finSumFinEquiv).trans
      (LinearEquiv.sumArrowLequivProdArrow _ _ R R)⟩
  obtain ⟨E⟩ := hE n₁ n₀
  obtain ⟨E'⟩ := hE n₂ (n₁ + n₀)
  have h₀' : ∀ x, p₀ (s₀ x) = x := fun x => LinearMap.congr_fun h₀ x
  have h₁' : ∀ x, p₁ (s₁ x) = x := fun x => LinearMap.congr_fun h₁ x
  have h₂' : ∀ x, p₂ (s₂ x) = x := fun x => LinearMap.congr_fun h₂ x
  have hd' : ∀ x, d₁ (d₀ x) = 0 := fun x => LinearMap.congr_fun hd x
  let q₁ : (Fin (n₁ + n₀) → R) →ₗ[R] (Fin n₁ → R) := LinearMap.fst R _ _ ∘ₗ E.toLinearMap
  let q₀ : (Fin (n₁ + n₀) → R) →ₗ[R] (Fin n₀ → R) := LinearMap.snd R _ _ ∘ₗ E.toLinearMap
  let i₁ : (Fin n₁ → R) →ₗ[R] (Fin (n₁ + n₀) → R) := E.symm.toLinearMap ∘ₗ LinearMap.inl R _ _
  let i₀ : (Fin n₀ → R) →ₗ[R] (Fin (n₁ + n₀) → R) := E.symm.toLinearMap ∘ₗ LinearMap.inr R _ _
  let f₀ : (Fin n₀ → R) →ₗ[R] (Fin (n₁ + n₀) → R) :=
    E.symm.toLinearMap ∘ₗ LinearMap.prod (s₁ ∘ₗ d₀ ∘ₗ p₀) (LinearMap.id - s₀ ∘ₗ p₀)
  let f₁ : (Fin (n₁ + n₀) → R) →ₗ[R] (Fin (n₂ + (n₁ + n₀)) → R) :=
    E'.symm.toLinearMap ∘ₗ LinearMap.prod (s₂ ∘ₗ d₁ ∘ₗ p₁ ∘ₗ q₁)
      (E.symm.toLinearMap ∘ₗ LinearMap.prod (q₁ - s₁ ∘ₗ p₁ ∘ₗ q₁) (s₀ ∘ₗ p₀ ∘ₗ q₀))
  let r₂ : (Fin (n₂ + (n₁ + n₀)) → R) →ₗ[R] P₂ := p₂ ∘ₗ LinearMap.fst R _ _ ∘ₗ E'.toLinearMap
  let r₁ : (Fin (n₂ + (n₁ + n₀)) → R) →ₗ[R] (Fin n₁ → R) :=
    q₁ ∘ₗ LinearMap.snd R _ _ ∘ₗ E'.toLinearMap
  let r₀ : (Fin (n₂ + (n₁ + n₀)) → R) →ₗ[R] P₀ :=
    p₀ ∘ₗ q₀ ∘ₗ LinearMap.snd R _ _ ∘ₗ E'.toLinearMap
  have hq₁ : q₁ ∘ₗ f₀ = s₁ ∘ₗ d₀ ∘ₗ p₀ := LinearMap.ext fun x => by simp [q₁, f₀]
  have hq₀ : q₀ ∘ₗ f₀ = LinearMap.id - s₀ ∘ₗ p₀ := LinearMap.ext fun x => by simp [q₀, f₀]
  have hi : i₁ ∘ₗ q₁ + i₀ ∘ₗ q₀ = LinearMap.id := LinearMap.ext fun x => by
    simp [q₀, q₁, i₀, i₁, ← map_add]
  have hr₂ : r₂ ∘ₗ f₁ = d₁ ∘ₗ p₁ ∘ₗ q₁ := LinearMap.ext fun x => by simp [r₂, f₁, h₂']
  have hr₁ : r₁ ∘ₗ f₁ = q₁ - s₁ ∘ₗ p₁ ∘ₗ q₁ := LinearMap.ext fun x => by simp [r₁, f₁, q₁]
  have hr₀ : r₀ ∘ₗ f₁ = p₀ ∘ₗ q₀ := LinearMap.ext fun x => by simp [r₀, f₁, q₀, h₀']
  have hf : f₁ ∘ₗ f₀ = 0 := LinearMap.ext fun x => by
    have e₁ : q₁ (f₀ x) = s₁ (d₀ (p₀ x)) := LinearMap.congr_fun hq₁ x
    have e₀ : q₀ (f₀ x) = x - s₀ (p₀ x) := LinearMap.congr_fun hq₀ x
    simp [f₁, e₁, e₀, h₀', h₁', hd']
  refine ⟨n₀, n₁ + n₀, n₂ + (n₁ + n₀), LinearMap.toMatrix' f₀, LinearMap.toMatrix' f₁,
    fun k => p₀ (Pi.single k 1), ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, hf, map_zero]
  intro R' _ _
  obtain ⟨hB, hX⟩ := projMatrix_abstract (d₀.baseChange R') (d₁.baseChange R')
    (p₀.baseChange R') (s₀.baseChange R') (p₁.baseChange R') (s₁.baseChange R')
    (f₀.baseChange R') (f₁.baseChange R') (q₁.baseChange R') (q₀.baseChange R')
    (i₁.baseChange R') (i₀.baseChange R') (r₂.baseChange R') (r₁.baseChange R')
    (r₀.baseChange R')
    (by rw [← LinearMap.baseChange_comp, h₀, LinearMap.baseChange_id])
    (by rw [← LinearMap.baseChange_comp, h₁, LinearMap.baseChange_id])
    (by simp only [← LinearMap.baseChange_comp, hq₁])
    (by simp only [← LinearMap.baseChange_comp, hq₀, LinearMap.baseChange_sub,
      LinearMap.baseChange_id])
    (by simp only [← LinearMap.baseChange_comp, ← LinearMap.baseChange_add, hi,
      LinearMap.baseChange_id])
    (by simp only [← LinearMap.baseChange_comp, hr₂])
    (by simp only [← LinearMap.baseChange_comp, hr₁, LinearMap.baseChange_sub])
    (by simp only [← LinearMap.baseChange_comp, hr₀])
  constructor
  · let e := TensorProduct.piScalarRight R R' R' (Fin n₀)
    have hmem : ∀ x, (((LinearMap.toMatrix' f₀).map (algebraMap R R')).mulVec (e x) = 0) ↔
        f₀.baseChange R' x = 0 := fun x => by
      rw [projMatrix_mulVec, LinearEquiv.map_eq_zero_iff]
    refine ⟨fun v hv => ?_, fun v hv v' hv' h => ?_, fun y hy => ?_⟩
    · obtain ⟨x, rfl⟩ := e.surjective v
      have := hB.mapsTo ((hmem x).mp hv)
      rwa [← projMatrix_sum] at this
    · obtain ⟨x, rfl⟩ := e.surjective v
      obtain ⟨x', rfl⟩ := e.surjective v'
      congr 1
      refine hB.injOn ((hmem x).mp hv) ((hmem x').mp hv') ?_
      rw [← projMatrix_sum, ← projMatrix_sum]
      exact h
    · obtain ⟨x, hx, rfl⟩ := hB.surjOn hy
      exact ⟨e x, (hmem x).mpr hx, projMatrix_sum R' p₀ x⟩
  · intro hex w hw
    obtain ⟨x, rfl⟩ := (TensorProduct.piScalarRight R R' R' (Fin (n₁ + n₀))).surjective w
    rw [projMatrix_mulVec, LinearEquiv.map_eq_zero_iff] at hw
    obtain ⟨v, rfl⟩ := hX hex x hw
    exact ⟨_, projMatrix_mulVec R' f₀ v⟩
end GlobalTheory
