-- Prove2me | solution 1 for GlobalTheory.PrimitiveUnitProduct.unit_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:17:35.923328+00:00
-- url     : https://prove2.me/submissions/b870073f-23e4-4062-8df8-4e12d5388dc5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnitOnProductEqOne
import Theorems.Thm_GlobalTheory_PrimitiveUnitProduct_value_mem_range

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct CategoryTheory AlgebraicGeometry Limits
open GlobalTheory GlobalTheory.PrimitiveUnitProduct
namespace GlobalTheory.PrimitiveUnitProduct
theorem _root_.solution {K A : Type} [Field K] [CommRing A] [Algebra K A] [IsDomain A]
    (H : ∀ (L : Type) [Field L] [Algebra K L], IsDomain (L ⊗[K] A)) (ε : A →ₐ[K] K)
    (u : A ⊗[K] A) (hu : IsUnit u) (p₁ p₂ : A ⊗[K] A →+* A)
    (hp₁ : ∀ a b, p₁ (a ⊗ₜ b) = a * algebraMap K A (ε b))
    (hp₂ : ∀ a b, p₂ (a ⊗ₜ b) = algebraMap K A (ε a) * b)
    (h₁ : p₁ u = 1) (h₂ : p₂ u = 1) : u = 1 := by
  let Ω := AlgebraicClosure (FractionRing A)
  let ι : A →ₐ[K] Ω := IsScalarTower.toAlgHom K A Ω
  have hι : Function.Injective ι :=
    (algebraMap (FractionRing A) Ω).injective.comp (IsFractionRing.injective A (FractionRing A))
  have : IsDomain (Ω ⊗[K] A) := H Ω
  let F := FractionRing (Ω ⊗[K] A)
  let θ : A ⊗[K] A →ₐ[K] Ω ⊗[K] A := Algebra.TensorProduct.map ι (AlgHom.id K A)
  have hθ : Function.Injective θ :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := A) ι.toLinearMap hι
  let j : A →ₐ[K] F :=
    (IsScalarTower.toAlgHom K (Ω ⊗[K] A) F).comp Algebra.TensorProduct.includeRight
  let σ : A ⊗[K] A →ₐ[K] F ⊗[K] A := (Algebra.TensorProduct.map j (AlgHom.id K A)).comp
    (Algebra.TensorProduct.comm K A A).toAlgHom
  have hσ : ∀ a b, σ (a ⊗ₜ b) = j b ⊗ₜ a := fun _ _ => rfl
  have e₁ : ∀ t, Algebra.TensorProduct.lift (AlgHom.id K F)
      ((IsScalarTower.toAlgHom K Ω F).comp ι) (fun _ _ => Commute.all _ _) (σ t) =
      algebraMap (Ω ⊗[K] A) F (θ t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b =>
      have : algebraMap (Ω ⊗[K] A) F (θ (a ⊗ₜ b)) =
          algebraMap (Ω ⊗[K] A) F ((1 : Ω) ⊗ₜ[K] b) *
            algebraMap (Ω ⊗[K] A) F (algebraMap Ω (Ω ⊗[K] A) (ι a)) := by
        rw [← map_mul]
        congr 1
        simp [θ]
      rw [this, ← IsScalarTower.algebraMap_apply, hσ, Algebra.TensorProduct.lift_tmul]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have e₂ : ∀ t, Algebra.TensorProduct.lift (AlgHom.id K F)
      ((IsScalarTower.toAlgHom K Ω F).comp ((Algebra.ofId K Ω).comp ε))
        (fun _ _ => Commute.all _ _) (σ t) = j (p₂ t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b =>
      rw [hp₂, map_mul, j.commutes, mul_comm, hσ, Algebra.TensorProduct.lift_tmul,
        IsScalarTower.algebraMap_apply K Ω F]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  obtain ⟨c, hc⟩ := value_mem_range H ι ((Algebra.ofId K Ω).comp ε) (σ u) (hu.map σ)
    (by rw [e₂, h₂, map_one])
  rw [e₁] at hc
  have hc' : algebraMap Ω (Ω ⊗[K] A) c = θ u := by
    apply IsFractionRing.injective (Ω ⊗[K] A) F
    rw [← IsScalarTower.algebraMap_apply, hc]
  let q : Ω ⊗[K] A →ₐ[Ω] Ω :=
    Algebra.TensorProduct.lift (AlgHom.id Ω Ω) ((Algebra.ofId K Ω).comp ε)
      (fun _ _ => Commute.all _ _)
  have e₃ : ∀ t, q (θ t) = ι (p₁ t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b =>
      rw [hp₁, map_mul, ι.commutes]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have hc1 : c = 1 := by
    have := congrArg q hc'
    rwa [e₃, h₁, map_one, q.commutes] at this
  apply hθ
  rw [← hc', hc1, map_one, map_one]
end GlobalTheory.PrimitiveUnitProduct
