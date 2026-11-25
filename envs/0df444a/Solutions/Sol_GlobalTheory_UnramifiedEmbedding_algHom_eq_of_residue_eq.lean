-- Prove2me | solution 1 for GlobalTheory.UnramifiedEmbedding.algHom_eq_of_residue_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:21:51.23129+00:00
-- url     : https://prove2.me/submissions/e7a4268d-e191-49c7-826d-a8bda9507156

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GaloisOfPrimePowerDegree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RangeLeRangeOfIsUnramifiedAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial IsLocalRing NumberField
open GlobalTheory GlobalTheory.UnramifiedEmbedding
namespace GlobalTheory.UnramifiedEmbedding
theorem _root_.solution {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [IsLocalRing T] [Algebra R S] [Algebra R T] [Algebra.IsStandardEtale R S] {χ₁ χ₂ : S →ₐ[R] T}
    (h : ∀ s, residue T (χ₁ s) = residue T (χ₂ s)) : χ₁ = χ₂ := by
  obtain ⟨P⟩ : Nonempty (StandardEtalePresentation R S) := inferInstance
  refine P.hom_ext ?_
  have h₁ : P.P.HasMap (χ₁ P.x) := P.hasMap.map χ₁
  have h₂ : P.P.HasMap (χ₂ P.x) := P.hasMap.map χ₂
  set y := χ₁ P.x with hy
  set d := χ₂ P.x - y with hd
  have hdm : d ∈ maximalIdeal T := by
    rw [← residue_eq_zero_iff, hd, map_sub, hy, h, sub_self]
  obtain ⟨k, hk⟩ := binomExpansion (P.f.map (algebraMap R T)) y d
  have hu : IsUnit (aeval y (derivative P.f)) := h₁.isUnit_derivative_f
  rw [show y + d = χ₂ P.x by rw [hd]; ring, eval_map_algebraMap, eval_map_algebraMap,
    derivative_map, eval_map_algebraMap, h₂.1, h₁.1, zero_add] at hk
  have hu' : IsUnit (aeval y (derivative P.f) + k * d) := by
    by_contra hn
    have : aeval y (derivative P.f) + k * d - k * d ∈ maximalIdeal T :=
      Ideal.sub_mem _ ((mem_maximalIdeal _).2 hn) (Ideal.mul_mem_left _ _ hdm)
    rw [add_sub_cancel_right] at this
    exact (mem_maximalIdeal _).1 this hu
  have h0 : d * (aeval y (derivative P.f) + k * d) = 0 := by
    rw [hk]; ring
  have : d = 0 := (hu'.mul_left_eq_zero).1 h0
  rw [hd, sub_eq_zero] at this
  exact this.symm
end GlobalTheory.UnramifiedEmbedding
