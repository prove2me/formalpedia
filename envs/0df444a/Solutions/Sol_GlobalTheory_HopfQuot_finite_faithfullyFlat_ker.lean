-- Prove2me | solution 1 for GlobalTheory.HopfQuot.finite_faithfullyFlat_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:50:24.793901+00:00
-- url     : https://prove2.me/submissions/4886ce78-53f9-455b-a24d-6ce6adf8a763

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteFaithfullyFlatKer
import Theorems.Thm_GlobalTheory_HopfQuot_ev_tmul
import Theorems.Thm_GlobalTheory_HopfQuot_exists_dual_family
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HopfQuot.ev_tmul

set_option autoImplicit false
open GlobalTheory GlobalTheory.HopfQuot
open TensorProduct
variable {R Λ B : Type*} [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [CommRing B] [Algebra R B]
  (ρ : B →ₐ[R] B ⊗[R] Λ)
namespace GlobalTheory.HopfQuot
theorem _root_.solution [Module.Finite R Λ] [Module.Projective R Λ]
    (hassoc : ∀ b, TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ (ρ b)) =
      (Coalgebra.comul (R := R) (A := Λ)).lTensor B (ρ b))
    (hcounit : ∀ b, TensorProduct.rid R B
      ((Coalgebra.counit (R := R) (A := Λ)).lTensor B (ρ b)) = b)
    (hsurj : Function.Surjective (Algebra.TensorProduct.productMap
      (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ) ρ)) :
    Module.Finite (AlgHom.equalizer ρ
      (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ)) B ∧
    Module.Projective (AlgHom.equalizer ρ
      (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ)) B ∧
    Module.FaithfullyFlat (AlgHom.equalizer ρ
      (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ)) B ∧
    RingHom.ker (Algebra.TensorProduct.productMap
        (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ) ρ) =
      Ideal.span {z | ∃ b ∈ AlgHom.equalizer ρ
        (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ),
        z = b ⊗ₜ[R] (1 : B) - (1 : B) ⊗ₜ[R] b} := by
  classical
  obtain ⟨ι, _, a, L, hL, ha⟩ := exists_dual_family ρ hassoc hcounit hsurj
  set B₀ := AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ) with hB₀
  let s : B →ₗ[B₀] (ι → B₀) :=
    { toFun := fun u j => ⟨L j (ρ u), hL j u⟩
      map_add' := fun u v => by
        ext j
        simp
      map_smul' := fun t u => by
        ext j
        have ht : ρ t = (t : B) ⊗ₜ 1 := t.2
        change L j (ρ (t * u)) = t * L j (ρ u)
        rw [map_mul, ht, ← smul_eq_mul (t : B), ← map_smul, Algebra.smul_def]
        rfl }
  let p : (ι → B₀) →ₗ[B₀] B := Fintype.linearCombination B₀ a
  have hps : p ∘ₗ s = LinearMap.id := by
    refine LinearMap.ext fun u => ?_
    exact ha u
  have hfin : Module.Finite B₀ B :=
    Module.Finite.of_surjective p fun u => ⟨s u, LinearMap.congr_fun hps u⟩
  have hproj : Module.Projective B₀ B := Module.Projective.of_split s p hps
  refine ⟨hfin, hproj,
    .of_comap_surjective (Algebra.IsIntegral.comap_surjective B₀ B), le_antisymm ?_ ?_⟩
  · set I := Ideal.span {z | ∃ b ∈ B₀, z = b ⊗ₜ[R] (1 : B) - (1 : B) ⊗ₜ[R] b}
    have key : ∀ z : B ⊗[R] B, (∑ j, L j (Algebra.TensorProduct.productMap
        (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ) ρ z) ⊗ₜ[R] a j) - z ∈ I := by
      intro z
      induction z with
      | zero => simp
      | add u v hu hv =>
        simp only [map_add, add_tmul, Finset.sum_add_distrib]
        rw [add_sub_add_comm]
        exact I.add_mem hu hv
      | tmul x y =>
        have : x ⊗ₜ[R] y = ∑ j, x ⊗ₜ[R] (L j (ρ y) * a j) := by rw [← tmul_sum, ha]
        rw [Algebra.TensorProduct.productMap_apply_tmul, this, ← Finset.sum_sub_distrib]
        refine I.sum_mem fun j _ => ?_
        have h1 : L j ((Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ) x * ρ y) =
            x * L j (ρ y) := by
          rw [← smul_eq_mul x, ← map_smul, Algebra.smul_def]
          rfl
        have h2 : (x * L j (ρ y)) ⊗ₜ[R] a j - x ⊗ₜ[R] (L j (ρ y) * a j) =
            (x ⊗ₜ[R] a j) * (L j (ρ y) ⊗ₜ[R] (1 : B) - (1 : B) ⊗ₜ[R] L j (ρ y)) := by
          simp [mul_sub, mul_comm]
        rw [h1, h2]
        exact I.mul_mem_left _ (Ideal.subset_span ⟨_, hL j y, rfl⟩)
    intro z hz
    have := key z
    rw [RingHom.mem_ker] at hz
    simp only [hz, map_zero, zero_tmul, Finset.sum_const_zero, zero_sub] at this
    exact neg_mem_iff.1 this
  · rw [Ideal.span_le]
    rintro _ ⟨b, hb, rfl⟩
    have hb' : ρ b = b ⊗ₜ 1 := hb
    simp [RingHom.mem_ker, hb']
end GlobalTheory.HopfQuot
