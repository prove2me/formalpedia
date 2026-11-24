-- Prove2me | solution 1 for GlobalTheory.exists_algHom_lift_of_isStandardEtale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:25:54.425944+00:00
-- url     : https://prove2.me/submissions/56103694-750b-40d5-8710-11571c81ea8c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Theorems.Thm_GlobalTheory_isUnit_of_isUnit_map_of_henselian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial IsLocalRing
open scoped TensorProduct
variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]
namespace GlobalTheory
theorem _root_.solution [Algebra.IsStandardEtale R A] (I : Ideal B)
    [HenselianRing B I] (π : B →ₐ[R] C) (hπ : Function.Surjective π) (hI : ∀ b, b ∈ I ↔ π b = 0)
    (φ : A →ₐ[R] C) : ∃ ψ : A →ₐ[R] B, π.comp ψ = φ := by
  obtain ⟨P⟩ : Nonempty (StandardEtalePresentation R A) := inferInstance
  have h₀ : P.P.HasMap (φ P.x) := P.hasMap.map φ
  obtain ⟨t₀, ht₀⟩ := hπ (φ P.x)
  have hu : ∀ b, IsUnit (π b) → IsUnit b := fun b hb =>
    isUnit_of_isUnit_map_of_henselian I (π : B →+* C) hπ hI hb
  obtain ⟨t, ht, htt⟩ := HenselianRing.is_henselian (I := I)
    (P.f.map (algebraMap R B)) (P.monic_f.map _) t₀
    (by rw [hI, eval_map_algebraMap, ← aeval_algHom_apply, ht₀]; exact h₀.1)
    (by
      refine IsUnit.map _ (hu _ ?_)
      rw [derivative_map, eval_map_algebraMap, ← aeval_algHom_apply, ht₀]
      exact h₀.isUnit_derivative_f)
  have hπt : π t = φ P.x := by
    rw [hI, map_sub, sub_eq_zero] at htt
    rw [htt, ht₀]
  have h₁ : P.P.HasMap t :=
    ⟨by rwa [IsRoot.def, eval_map_algebraMap] at ht,
      hu _ (by rw [← aeval_algHom_apply, hπt]; exact h₀.2)⟩
  exact ⟨(P.P.lift t h₁).comp P.equivRing.toAlgHom, P.hom_ext (by simp [hπt])⟩
end GlobalTheory
