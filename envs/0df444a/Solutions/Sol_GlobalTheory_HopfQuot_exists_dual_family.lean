-- Prove2me | solution 1 for GlobalTheory.HopfQuot.exists_dual_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:31:13.593802+00:00
-- url     : https://prove2.me/submissions/9dcf6654-7255-491a-b332-f17428f3e518

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteFaithfullyFlatKer
import Theorems.Thm_GlobalTheory_HopfQuot_ev_tmul
import Theorems.Thm_GlobalTheory_HopfQuot_exists_integrals
import Theorems.Thm_GlobalTheory_HopfQuot_ev_mem_equalizer
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
    ∃ (ι : Type) (_ : Fintype ι) (a : ι → B) (L : ι → B ⊗[R] Λ →ₗ[B] B),
      (∀ j u, L j (ρ u) ∈ AlgHom.equalizer ρ
        (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ)) ∧
      ∀ u, ∑ j, L j (ρ u) * a j = u := by
  obtain ⟨n, l, T, hl, hT⟩ := exists_integrals R Λ
  choose z hz using fun k => hsurj (1 ⊗ₜ T k)
  choose m x y hxy using fun k => TensorProduct.exists_sum_tmul_eq (z k)
  refine ⟨Σ k, Fin (m k), inferInstance, fun j => x j.1 j.2,
    fun j => ev B (l j.1) ∘ₗ LinearMap.mulLeft B (ρ (y j.1 j.2)), fun j u => ?_, fun u => ?_⟩
  · rw [LinearMap.comp_apply, LinearMap.mulLeft_apply, ← map_mul]
    exact ev_mem_equalizer ρ hassoc _ (hl _) _
  · rw [Fintype.sum_sigma]
    have h1 : ∀ k, ∑ i, ev B (l k) (ρ (y k i) * ρ u) * x k i = ev B (l k) (1 ⊗ₜ T k * ρ u) := by
      intro k
      rw [← hz, hxy, map_sum, Finset.sum_mul, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm, ← smul_eq_mul, ← map_smul, Algebra.TensorProduct.productMap_apply_tmul,
        mul_assoc, Algebra.smul_def]
      rfl
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, h1]
    conv_rhs => rw [← hcounit u]
    generalize ρ u = w
    induction w with
    | zero => simp
    | add u v hu hv => simp only [map_add, mul_add, Finset.sum_add_distrib, hu, hv]
    | tmul u v => simp [← Finset.sum_smul, hT]
end GlobalTheory.HopfQuot
