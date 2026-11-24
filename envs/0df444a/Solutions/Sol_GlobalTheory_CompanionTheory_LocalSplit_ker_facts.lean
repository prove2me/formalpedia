-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LocalSplit.ker_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:49:42.05583+00:00
-- url     : https://prove2.me/submissions/42227a96-4be8-4bef-ae3c-8c490901771f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalFreeKernelSplitting

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LocalSplit
namespace GlobalTheory.CompanionTheory.LocalSplit
theorem _root_.solution {A Q : Type} [CommRing A] [IsLocalRing A] [AddCommGroup Q] [Module A Q]
    [Module.Finite A Q] [Module.Free A Q] (s : ℕ)
    (f : (Fin s → A) →ₗ[A] Q) (p : Q →ₗ[A] (Fin s → A)) (h : p ∘ₗ f = LinearMap.id) :
    Module.Free A (LinearMap.ker p) ∧ Module.Finite A (LinearMap.ker p) ∧
      s + Module.finrank A (LinearMap.ker p) = Module.finrank A Q := by
  have hpf : ∀ y, p (f y) = y := fun y => LinearMap.congr_fun h y
  let e : Q ≃ₗ[A] (LinearMap.ker p) × (Fin s → A) := LinearEquiv.ofLinear
    (LinearMap.prod
      (LinearMap.codRestrict (LinearMap.ker p) (LinearMap.id - f ∘ₗ p)
        (fun x => by simp [hpf]))
      p)
    (LinearMap.coprod (LinearMap.ker p).subtype f)
    (by
      ext x <;> simp [hpf])
    (by
      ext x
      simp)
  have hproj : Module.Projective A ((LinearMap.ker p) × (Fin s → A)) :=
    Module.Projective.of_equiv e
  have hker : Module.Projective A (LinearMap.ker p) :=
    Module.Projective.of_split (LinearMap.inl A (LinearMap.ker p) (Fin s → A))
      (LinearMap.fst A (LinearMap.ker p) (Fin s → A)) (by ext; simp)
  have hfin : Module.Finite A (LinearMap.ker p) :=
    Module.Finite.of_surjective (LinearMap.fst A (LinearMap.ker p) (Fin s → A) ∘ₗ e.toLinearMap)
      (fun y => ⟨e.symm (y, 0), by simp⟩)
  have hfree : Module.Free A (LinearMap.ker p) := Module.free_of_flat_of_isLocalRing
  refine ⟨hfree, hfin, ?_⟩
  have := e.finrank_eq
  rw [Module.finrank_prod, Module.finrank_fin_fun] at this
  omega
end GlobalTheory.CompanionTheory.LocalSplit
