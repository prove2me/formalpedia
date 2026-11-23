-- Prove2me | solution 1 for GlobalTheory.Mem.An.Model.mem_rayI_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:03:03.644851+00:00
-- url     : https://prove2.me/submissions/9cf4a47e-b766-4762-bf41-63e22b056799

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NormOneSevenOneTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.An GlobalTheory.Mem.An.Model
namespace GlobalTheory.Mem.An.Model
theorem _root_.solution {K : Type} [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)) (J : Ideal (𝓞 K)) :
    J ≠ 0 → J ⊔ 𝔮 = ⊤ → ∀ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ,
      (I : FractionalIdeal (𝓞 K)⁰ K) = (J : FractionalIdeal (𝓞 K)⁰ K) → I ∈ rayI 𝔮 := by
  induction J using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact absurd rfl h
  | h₂ u hu =>
    intro _ _ I hI
    rw [Ideal.isUnit_iff] at hu
    subst hu
    have hI1 : I = 1 := Units.ext (by rw [hI, FractionalIdeal.coeIdeal_top, Units.val_one])
    rw [hI1]
    exact one_mem _
  | h₃ a P ha hP ih =>
    intro _ hcop I hI
    have hP0 : P ≠ 0 := hP.ne_zero
    have hPq : ¬ P ∣ 𝔮 := by
      intro hd
      apply hP.not_isUnit
      rw [Ideal.isUnit_iff, eq_top_iff, ← hcop]
      exact sup_le Ideal.mul_le_left (Ideal.le_of_dvd hd)
    have hacop : a ⊔ 𝔮 = ⊤ := by
      rw [eq_top_iff, ← hcop]
      exact sup_le_sup_right Ideal.mul_le_right _
    have hPf : (P : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
      rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact hP0
    have haf : (a : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
      rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact ha
    have hI' : I = Units.mk0 _ hPf * Units.mk0 _ haf := Units.ext (by
      rw [hI, Units.val_mul, Units.val_mk0, Units.val_mk0, FractionalIdeal.coeIdeal_mul])
    have hu : Units.mk0 _ hPf ∈ rayI 𝔮 :=
      Subgroup.subset_closure ⟨⟨P, Ideal.isPrime_of_prime hP, hP0⟩, hPq, rfl⟩
    rw [hI']
    exact Subgroup.mul_mem _ hu (ih ha hacop _ rfl)
end GlobalTheory.Mem.An.Model
