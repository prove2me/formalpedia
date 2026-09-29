-- Prove2me | solution 1 for HopfAlgebra.exists_signTwist_withConv_mulEquiv_of_linearEquiv_padicInt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/b2aa5b1b-a952-5c69-9c58-a2a23c11a450

import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_HopfAlgebra_exists_signTwist_withConv_equiv_formula_of_linearEquiv_padicInt
import Theorems.Thm_HopfAlgebra_withConv_mul_signTwist_of_formula_of_linearEquiv_padicInt
import Theorems.Thm_HopfAlgebra_signTwist_galois_of_formula_of_linearEquiv_padicInt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_signTwist_withConv_mulEquiv_of_linearEquiv_padicInt

open scoped NNReal

open scoped TensorProduct in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (d : ℚ_[p]) (hd : ‖d‖₊ = 1) (hd_nsq : ¬ IsSquare d)
    (s : AlgebraicClosure ℚ_[p]) (hs : s ^ 2 = algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) d)
    (d₀ : ℤ_[p]) (hd₀d : (d₀ : ℚ_[p]) = d) (hd₀ : IsUnit d₀)
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H]
    (hfin : Module.Finite ℤ_[p] H) (hflat : Module.Flat ℤ_[p] H)
    (hcocomm : Coalgebra.IsCocomm ℤ_[p] H)
    (H' : Type) [CommRing H'] [HopfAlgebra ℤ_[p] H']
    (hfin' : Module.Finite ℤ_[p] H') (hflat' : Module.Flat ℤ_[p] H')
    (hcocomm' : Coalgebra.IsCocomm ℤ_[p] H')
    (e : H' ≃ₗ[ℤ_[p]] H)
    (he1 : e 1 = 1)
    (hemul : let Pm : H →ₗ[ℤ_[p]] H :=
        Ring.inverse (2:ℤ_[p]) • (LinearMap.id - HopfAlgebra.antipode ℤ_[p])
      ∀ a b : H', e (a * b) = e a * e b + (d₀ - 1) • (Pm (e a) * Pm (e b)))
    (hecounit : ∀ a : H', (Coalgebra.counit (e a) : ℤ_[p]) = Coalgebra.counit a)
    (heant : ∀ a : H', e (HopfAlgebra.antipode ℤ_[p] a) = HopfAlgebra.antipode ℤ_[p] (e a))
    (hecomul : let Pm : H →ₗ[ℤ_[p]] H :=
        Ring.inverse (2:ℤ_[p]) • (LinearMap.id - HopfAlgebra.antipode ℤ_[p])
      ∀ a : H', (TensorProduct.map (e : H' →ₗ[ℤ_[p]] H) (e : H' →ₗ[ℤ_[p]] H))
                  (Coalgebra.comul a)
            = Coalgebra.comul (e a)
              + (Ring.inverse d₀ - 1) •
                  (TensorProduct.map Pm Pm) (Coalgebra.comul (e a))) :
    ∃ β : WithConv (H' →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃
          WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]),
      (∀ f' g', β (f' * g') = β f' * β g') ∧
      ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
        (f' g' : WithConv (H' →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]))
        (g : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
        (∀ h' : H', g' h' = σ (f' h')) →
        (∀ h : H, g h = σ ((β f') h)) →
          (σ s = s → β g' = g) ∧ (σ s ≠ s → β g' * g = 1) := by

  have hd' : ‖d‖ = 1 := by
    have h1 : ((‖d‖₊ : ℝ≥0) : ℝ) = ((1 : ℝ≥0) : ℝ) := by exact_mod_cast hd
    simpa [coe_nnnorm] using h1
  have hd_ne : d ≠ 0 := fun h => by simp [h] at hd'
  have hs0 : s ≠ 0 := by
    intro h
    apply hd_ne
    have h2 : algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) d = 0 := by
      rw [← hs, h, zero_pow two_ne_zero]
    exact (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])).injective
      (h2.trans (map_zero _).symm)

  have hd₀s : algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]) d₀ = s ^ 2 := by
    rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (AlgebraicClosure ℚ_[p]),
      show (algebraMap ℤ_[p] ℚ_[p]) d₀ = (d₀ : ℚ_[p]) from rfl, hd₀d, hs]

  obtain ⟨β, hβ⟩ :=
    HopfAlgebra.exists_signTwist_withConv_equiv_formula_of_linearEquiv_padicInt
      p hp2 s hs0 d₀ hd₀s H H' e he1 hemul heant
  refine ⟨β, ?_, ?_⟩
  ·
    exact HopfAlgebra.withConv_mul_signTwist_of_formula_of_linearEquiv_padicInt
      p hp2 s hs0 d₀ hd₀s hd₀ H hcocomm H' e hecomul β hβ
  ·
    exact HopfAlgebra.signTwist_galois_of_formula_of_linearEquiv_padicInt
      p hp2 d s hs0 hs H hcocomm H' e β hβ

end S_HopfAlgebra_exists_signTwist_withConv_mulEquiv_of_linearEquiv_padicInt
end P2MW
export P2MW.S_HopfAlgebra_exists_signTwist_withConv_mulEquiv_of_linearEquiv_padicInt (solution)
