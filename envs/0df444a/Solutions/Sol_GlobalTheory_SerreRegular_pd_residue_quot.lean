-- Prove2me | solution 1 for GlobalTheory.SerreRegular.pd_residue_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:23:27.117218+00:00
-- url     : https://prove2.me/submissions/34431c6a-171b-4932-bb8d-18705afe5275

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ProjectionSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsHasProjectiveDimensionLEOfResidueField
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_LocDim
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Theorems.Thm_GlobalTheory_SerreRegular_map_maximalIdeal_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing GlobalTheory.Pat CategoryTheory TensorProduct
open GlobalTheory
open GlobalTheory.SerreRegular
namespace GlobalTheory.SerreRegular
theorem _root_.solution {A : Type} [CommRing A] [IsLocalRing A] {x : A}
    (hm : x ∈ maximalIdeal A) (hm2 : x ∉ maximalIdeal A ^ 2) [IsLocalRing (A ⧸ Ideal.span {x})]
    (n : ℕ) (h : HasProjectiveDimensionLE
      (ModuleCat.of (A ⧸ Ideal.span {x}) ((A ⧸ Ideal.span {x}) ⊗[A] maximalIdeal A)) n) :
    HasProjectiveDimensionLE (ModuleCat.of (A ⧸ Ideal.span {x})
      ((A ⧸ Ideal.span {x}) ⧸ maximalIdeal (A ⧸ Ideal.span {x}))) n := by
  have hmap := map_maximalIdeal_eq (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
  have hx0 : Ideal.Quotient.mk (Ideal.span {x}) x = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x)
  set B := A ⧸ Ideal.span {x} with hB
  have hv0 : (maximalIdeal A).toCotangent ⟨x, hm⟩ ≠ 0 := by
    rw [Ne, Ideal.toCotangent_eq_zero]
    exact hm2
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one (ResidueField A) (V := CotangentSpace A) hv0
  let j : ResidueField A →ₗ[A] B ⧸ maximalIdeal B :=
    Submodule.liftQ (maximalIdeal A) (Algebra.linearMap A (B ⧸ maximalIdeal B)) (by
      intro a ha
      rw [LinearMap.mem_ker]
      change Ideal.Quotient.mk (maximalIdeal B) (Ideal.Quotient.mk (Ideal.span {x}) a) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, ← hmap]
      exact Ideal.mem_map_of_mem _ ha)
  have hj : j 1 = 1 := map_one (algebraMap A (B ⧸ maximalIdeal B))
  let r0 : maximalIdeal A →ₗ[A] B ⧸ maximalIdeal B :=
    j ∘ₗ (l.restrictScalars A) ∘ₗ (maximalIdeal A).toCotangent
  have hr0 : r0 ⟨x, hm⟩ = 1 := by
    change j (l ((maximalIdeal A).toCotangent ⟨x, hm⟩)) = 1
    rw [hl, hj]
  let r : B ⊗[A] maximalIdeal A →ₗ[B] B ⧸ maximalIdeal B := r0.liftBaseChange B
  let i : (B ⧸ maximalIdeal B) →ₗ[B] B ⊗[A] maximalIdeal A :=
    Submodule.liftQ (maximalIdeal B) (LinearMap.toSpanSingleton B _ ((1 : B) ⊗ₜ[A] ⟨x, hm⟩)) (by
      intro b hb
      rw [← hmap, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hb
      obtain ⟨a, ha, rfl⟩ := hb
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      have e : a • (⟨x, hm⟩ : maximalIdeal A) = x • (⟨a, ha⟩ : maximalIdeal A) :=
        Subtype.ext (mul_comm a x)
      change algebraMap A B a • _ = 0
      rw [algebraMap_smul, ← TensorProduct.tmul_smul, e, TensorProduct.tmul_smul,
        ← algebraMap_smul B x]
      change Ideal.Quotient.mk (Ideal.span {x}) x • _ = 0
      rw [hx0, zero_smul])
  have hri : r ∘ₗ i = LinearMap.id := by
    apply Submodule.linearMap_qext
    apply LinearMap.ext_ring
    change r (LinearMap.toSpanSingleton B _ ((1 : B) ⊗ₜ[A] (⟨x, hm⟩ : maximalIdeal A)) 1) = 1
    rw [LinearMap.toSpanSingleton_apply, one_smul, LinearMap.liftBaseChange_tmul, hr0, one_smul]
  let ret : Retract (ModuleCat.of B (B ⧸ maximalIdeal B)) (ModuleCat.of B (B ⊗[A] maximalIdeal A)) :=
    ⟨ModuleCat.ofHom i, ModuleCat.ofHom r, by
      rw [← ModuleCat.ofHom_comp, hri]; rfl⟩
  exact ret.hasProjectiveDimensionLT _
end GlobalTheory.SerreRegular
