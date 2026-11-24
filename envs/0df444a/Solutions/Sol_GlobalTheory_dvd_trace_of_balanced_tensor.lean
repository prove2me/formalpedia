-- Prove2me | solution 1 for GlobalTheory.dvd_trace_of_balanced_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:46:58.700746+00:00
-- url     : https://prove2.me/submissions/a656700f-2971-43c7-99ec-59353e536a53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdTraceOfBalancedTensor
import Theorems.Thm_GlobalTheory_sum_contractRight_coord_tmul
import Theorems.Thm_GlobalTheory_contractRight_trace
import Theorems.Thm_GlobalTheory_eq_zero_of_lTensor_eq_zero_of_balanced

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (O H : Type) [CommRing O] [IsLocalRing O] [CommRing H] [Algebra O H] [Module.Free O H] [Module.Finite O H] (Θ : H ⊗[O] H) (c : O), ((∀ h : H, (h ⊗ₜ[O] (1 : H)) * Θ = ((1 : H) ⊗ₜ[O] h) * Θ) ∧ Algebra.TensorProduct.lmul' O Θ = algebraMap O H c ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra O K], (∀ a ∈ IsLocalRing.maximalIdeal O, algebraMap O K a = 0) → ∀ ga : H →ₐ[O] K, Algebra.TensorProduct.map (AlgHom.id O H) ga Θ ≠ 0) → ∀ h : H, c ∣ Algebra.trace O H h := by
  intro O H _ _ _ _ _ _ Θ c ⟨hΘ, hc, hK⟩ h
  classical
  let b := Module.Free.chooseBasis O H
  let K := AlgebraicClosure (IsLocalRing.ResidueField O)
  have hm : ∀ a ∈ IsLocalRing.maximalIdeal O, algebraMap O K a = 0 := by
    intro a ha
    rw [IsScalarTower.algebraMap_apply O (IsLocalRing.ResidueField O) K,
      IsLocalRing.ResidueField.algebraMap_eq, (IsLocalRing.residue_eq_zero_iff a).2 ha, map_zero]
  have hdet : IsUnit (LinearMap.toMatrix b.dualBasis b (contractRight Θ)).det := by
    by_contra hnu
    have h0 := hm _ ((IsLocalRing.mem_maximalIdeal _).2 hnu)
    rw [RingHom.map_det] at h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hv0
    have : b.constr O v = 0 := by
      apply eq_zero_of_lTensor_eq_zero_of_balanced Θ hΘ K (hK K hm)
      have hv' : ∀ i, ∑ j, b.repr (contractRight Θ (b.coord j)) i • v j = 0 := by
        intro i
        have := congrFun hv i
        simpa [Matrix.mulVec, dotProduct, LinearMap.toMatrix_apply, Algebra.smul_def,
          Module.Basis.coe_dualBasis] using this
      have e : LinearMap.lTensor H (b.constr O v) Θ
          = ∑ j, contractRight Θ (b.coord j) ⊗ₜ[O] v j := by
        conv_lhs => rw [← sum_contractRight_coord_tmul b Θ]
        simp [map_sum]
      rw [e]
      calc ∑ j, contractRight Θ (b.coord j) ⊗ₜ[O] v j
          = ∑ j, ∑ i, b i ⊗ₜ[O] (b.repr (contractRight Θ (b.coord j)) i • v j) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            conv_lhs => rw [← b.sum_repr (contractRight Θ (b.coord j))]
            simp only [TensorProduct.sum_tmul, TensorProduct.smul_tmul]
        _ = 0 := by
            rw [Finset.sum_comm]
            simp only [← TensorProduct.tmul_sum, hv', TensorProduct.tmul_zero,
              Finset.sum_const_zero]
    exact (b.constr O).injective (by rw [this, map_zero])
  let e := LinearEquiv.ofIsUnitDet hdet
  have he : ∀ a, e a = contractRight Θ a := fun a => rfl
  have : Algebra.trace O H = c • e.symm 1 := by
    apply e.injective
    rw [map_smul, e.apply_symm_apply, he, contractRight_trace b Θ hΘ, hc, Algebra.algebraMap_eq_smul_one]
  rw [this]
  exact Dvd.intro _ rfl
end GlobalTheory
