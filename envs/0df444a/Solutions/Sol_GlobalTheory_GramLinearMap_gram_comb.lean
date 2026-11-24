-- Prove2me | solution 1 for GlobalTheory.GramLinearMap.gram_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:53:51.829254+00:00
-- url     : https://prove2.me/submissions/0b451044-34a7-45ef-babd-8b3ed103f44d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsLinearMapOfGram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.GramLinearMap
namespace GlobalTheory.GramLinearMap
theorem _root_.solution {P : Type} [AddCommGroup P] [Module ℂ P] {B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ}
    {P' : Type} [AddCommGroup P'] [Module ℂ P'] {B' : P' →ₗ⋆[ℂ] P' →ₗ[ℂ] ℂ} {U : Type}
    (f : U → P) (f' : U → P') {c d : ℂ}
    (h : ∀ u v : U, B (f u) (f v) * c = d * B' (f' u) (f' v)) (x y : U →₀ ℂ) :
    B (Finsupp.linearCombination ℂ f x) (Finsupp.linearCombination ℂ f y) * c =
      d * B' (Finsupp.linearCombination ℂ f' x) (Finsupp.linearCombination ℂ f' y) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x₁ x₂ h₁ h₂ =>
    simp only [map_add, LinearMap.add_apply, add_mul, mul_add, h₁, h₂]
  | single u a =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y₁ y₂ h₁ h₂ =>
      simp only [map_add, add_mul, mul_add, h₁, h₂]
    | single v b =>
      simp only [Finsupp.linearCombination_single, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
        smul_eq_mul, RingHom.id_apply]
      linear_combination (b * (starRingEnd ℂ) a) * h u v
end GlobalTheory.GramLinearMap
