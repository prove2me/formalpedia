-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Orbit.adjoin_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:19:25.399427+00:00
-- url     : https://prove2.me/submissions/0bbfcb35-bcaf-4162-819b-a105cc590bf9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit
open GlobalTheory.UnitLemma Polynomial IsLocalRing ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
variable {K : UQ}
namespace GlobalTheory.UnitLemma.Orbit
theorem _root_.solution (B : InvAlg K) (hu : B.g * B.σ B.g = 1) (hi : IsIntegral K.O B.g) {y : B.A}
    (hy : y ∈ Algebra.adjoin K.O ({B.g} : Set B.A)) : B.σ y ∈ Algebra.adjoin K.O ({B.g} : Set B.A) := by
  have hO : ∀ a : K.O, ∃ b : K.O, B.σ (algebraMap K.O B.A a) = algebraMap K.O B.A b := by
    intro a
    obtain ⟨b, hb⟩ := K.c_int a
    exact ⟨b, by rw [IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg, hb, ← IsScalarTower.algebraMap_apply]⟩
  have hσi : IsIntegral K.O (B.σ B.g) := by
    have hinj : Function.Injective (algebraMap K.O K.E) := IsFractionRing.injective _ _
    choose τ' hτ' using K.c_int
    let cO : K.O →+* K.O :=
      { toFun := τ'
        map_one' := hinj (by rw [← hτ']; simp)
        map_mul' := fun a b => hinj (by simp [← hτ'])
        map_zero' := hinj (by rw [← hτ']; simp)
        map_add' := fun a b => hinj (by simp [← hτ']) }
    refine IsIntegral.map_of_comp_eq cO (B.σ : B.A →+* B.A) ?_ hi
    ext a
    change algebraMap K.O B.A (τ' a) = B.σ (algebraMap K.O B.A a)
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A a, B.σ_alg, hτ', ← IsScalarTower.algebraMap_apply]
  have hg : B.σ B.g ∈ Algebra.adjoin K.O ({B.g} : Set B.A) := by
    obtain ⟨p, hp, h0⟩ := hσi
    let i : Invertible (B.σ B.g) := ⟨B.g, hu, by rw [mul_comm, hu]⟩
    have h1 : eval₂ (algebraMap K.O B.A) B.g p.reverse = 0 :=
      (eval₂_reverse_eq_zero_iff (algebraMap K.O B.A) (B.σ B.g) p).2 h0
    rw [← X_mul_divX_add p.reverse, coeff_zero_reverse, hp.leadingCoeff, ← aeval_def] at h1
    simp only [map_add, map_mul, aeval_X, map_one] at h1
    have h2 : B.σ B.g = -aeval B.g p.reverse.divX := by
      linear_combination B.σ B.g * h1 - aeval B.g p.reverse.divX * hu
    rw [h2]
    exact neg_mem (aeval_mem_adjoin_singleton _ _)
  induction hy using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact hg
  | algebraMap a => obtain ⟨b, hb⟩ := hO a; rw [hb]; exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
end GlobalTheory.UnitLemma.Orbit
