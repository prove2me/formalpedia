-- Prove2me | solution 1 for IsLocalRing.existsUnique_algHom_residue_eq_of_flat_of_map_maximalIdeal_eq_of_isNilpotent_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/6266a58d-b3fb-5877-827e-91b1af1141f3

import Mathlib
import Theorems.Thm_Algebra_Etale_quotient_tensorProduct_of_flat_of_map_maximalIdeal_eq_of_isSeparable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_existsUnique_algHom_residue_eq_of_flat_of_map_maximalIdeal_eq_of_isNilpotent_maximalIdeal

set_option autoImplicit false

open IsLocalRing TensorProduct

theorem solution
    (V : Type) [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    (D : Type) [CommRing D] [IsLocalRing D] [Algebra V D] [IsLocalHom (algebraMap V D)] [Module.Flat V D]
    (hVD : (maximalIdeal V).map (algebraMap V D) = maximalIdeal D)
    [Module.Finite (ResidueField V) (ResidueField D)] [Algebra.IsSeparable (ResidueField V) (ResidueField D)]
    (T : Type) [CommRing T] [IsLocalRing T] [Algebra V T] (hT : IsNilpotent (maximalIdeal T))
    (ι : ResidueField D →+* ResidueField T)
    (hι : ∀ v : V, ι (residue D (algebraMap V D v)) = residue T (algebraMap V T v)) :
    ∃! g : D →ₐ[V] T, ∀ d : D, residue T (g d) = ι (residue D d) := by
  classical

  obtain ⟨N, hN⟩ := hT
  let M : ℕ := N + 1
  have hM : 0 < M := Nat.succ_pos N
  have hTM : maximalIdeal T ^ M = ⊥ := by
    refine le_bot_iff.mp ?_
    calc maximalIdeal T ^ M ≤ maximalIdeal T ^ N := Ideal.pow_le_pow_right (Nat.le_succ N)
      _ = ⊥ := by rw [hN, Submodule.zero_eq_bot]

  have hloc : (maximalIdeal V).map (algebraMap V T) ≤ maximalIdeal T := by
    rw [Ideal.map_le_iff_le_comap]
    intro v hv
    rw [Ideal.mem_comap, ← residue_eq_zero_iff, ← hι]
    have hvD : algebraMap V D v ∈ maximalIdeal D := hVD.le (Ideal.mem_map_of_mem _ hv)
    rw [(residue_eq_zero_iff _).mpr hvD, map_zero]
  have hker : ∀ v ∈ maximalIdeal V ^ M, algebraMap V T v = 0 := by
    intro v hv
    have : algebraMap V T v ∈ (maximalIdeal T) ^ M := by
      have h1 : algebraMap V T v ∈ ((maximalIdeal V).map (algebraMap V T)) ^ M := by
        rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hv
      exact Ideal.pow_right_mono hloc M h1
    rwa [hTM, Ideal.mem_bot] at this

  let ψ : V ⧸ maximalIdeal V ^ M →+* T :=
    Ideal.Quotient.lift (maximalIdeal V ^ M) (algebraMap V T) hker
  letI algVMT : Algebra (V ⧸ maximalIdeal V ^ M) T := ψ.toAlgebra
  haveI towVT : IsScalarTower V (V ⧸ maximalIdeal V ^ M) T :=
    IsScalarTower.of_algebraMap_eq fun v => (Ideal.Quotient.lift_mk (maximalIdeal V ^ M) (algebraMap V T) hker).symm

  haveI hEt : Algebra.Etale (V ⧸ maximalIdeal V ^ M) ((V ⧸ maximalIdeal V ^ M) ⊗[V] D) :=
    Algebra.Etale.quotient_tensorProduct_of_flat_of_map_maximalIdeal_eq_of_isSeparable V D hVD M hM

  let j : D →ₐ[V] (V ⧸ maximalIdeal V ^ M) ⊗[V] D := Algebra.TensorProduct.includeRight
  let Φ : (D →ₐ[V] T) → ((V ⧸ maximalIdeal V ^ M) ⊗[V] D →ₐ[V ⧸ maximalIdeal V ^ M] T) := fun g =>
    Algebra.TensorProduct.lift (Algebra.ofId (V ⧸ maximalIdeal V ^ M) T) g (fun _ _ => Commute.all _ _)
  have hΦ : ∀ (g : D →ₐ[V] T) (d : D), Φ g (j d) = g d := by
    intro g d
    show Algebra.TensorProduct.lift _ g _ ((1 : V ⧸ maximalIdeal V ^ M) ⊗ₜ[V] d) = g d
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  have hΦ' : ∀ g : D →ₐ[V] T, ((Φ g).restrictScalars V).comp j = g :=
    fun g => AlgHom.ext fun d => hΦ g d

  let g₀ : D →ₐ[V] T ⧸ maximalIdeal T :=
    { toRingHom := ι.comp (residue D)
      commutes' := fun v => by
        show ι (residue D (algebraMap V D v)) = algebraMap V (T ⧸ maximalIdeal T) v
        rw [hι]; rfl }
  have hg₀ : ∀ d : D, g₀ d = ι (residue D d) := fun d => rfl

  let φ₀ : (V ⧸ maximalIdeal V ^ M) ⊗[V] D →ₐ[V ⧸ maximalIdeal V ^ M] T ⧸ maximalIdeal T :=
    Algebra.TensorProduct.lift (Algebra.ofId (V ⧸ maximalIdeal V ^ M) (T ⧸ maximalIdeal T)) g₀
      (fun _ _ => Commute.all _ _)
  have hnil : IsNilpotent (maximalIdeal T) := ⟨N, hN⟩
  let φ : (V ⧸ maximalIdeal V ^ M) ⊗[V] D →ₐ[V ⧸ maximalIdeal V ^ M] T :=
    Algebra.FormallySmooth.lift (maximalIdeal T) hnil φ₀
  have hφ : ∀ x, Ideal.Quotient.mk (maximalIdeal T) (φ x) = φ₀ x :=
    fun x => Algebra.FormallySmooth.mk_lift (maximalIdeal T) hnil φ₀ x
  let g : D →ₐ[V] T := (φ.restrictScalars V).comp j
  have hg : ∀ d : D, residue T (g d) = ι (residue D d) := by
    intro d
    show Ideal.Quotient.mk (maximalIdeal T) (φ (j d)) = ι (residue D d)
    rw [hφ]
    show Algebra.TensorProduct.lift _ g₀ _ ((1 : V ⧸ maximalIdeal V ^ M) ⊗ₜ[V] d) = ι (residue D d)
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul, hg₀]

  have huniq : ∀ g₁ g₂ : D →ₐ[V] T, (∀ d, residue T (g₁ d) = ι (residue D d)) →
      (∀ d, residue T (g₂ d) = ι (residue D d)) → g₁ = g₂ := by
    intro g₁ g₂ h₁ h₂
    have key : Φ g₁ = Φ g₂ := by
      refine Algebra.FormallyUnramified.lift_unique (maximalIdeal T) hnil _ _ ?_
      refine Algebra.TensorProduct.ext' fun a d => ?_
      show Ideal.Quotient.mk (maximalIdeal T) (Φ g₁ (a ⊗ₜ d)) = Ideal.Quotient.mk (maximalIdeal T) (Φ g₂ (a ⊗ₜ d))
      show Ideal.Quotient.mk (maximalIdeal T) (Algebra.TensorProduct.lift _ g₁ _ (a ⊗ₜ[V] d)) =
        Ideal.Quotient.mk (maximalIdeal T) (Algebra.TensorProduct.lift _ g₂ _ (a ⊗ₜ[V] d))
      rw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul, map_mul, map_mul]
      congr 1
      exact (h₁ d).trans (h₂ d).symm
    rw [← hΦ' g₁, ← hΦ' g₂, key]
  exact ⟨g, hg, fun g' hg' => huniq g' g hg' hg⟩

end S_IsLocalRing_existsUnique_algHom_residue_eq_of_flat_of_map_maximalIdeal_eq_of_isNilpotent_maximalIdeal
end P2MW
export P2MW.S_IsLocalRing_existsUnique_algHom_residue_eq_of_flat_of_map_maximalIdeal_eq_of_isNilpotent_maximalIdeal (solution)
