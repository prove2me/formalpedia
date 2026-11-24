-- Prove2me | solution 1 for GlobalTheory.PrimitiveUnitProduct.exists_primitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:30:54.786457+00:00
-- url     : https://prove2.me/submissions/fa8466cd-d747-41f6-b58e-21de21c7cd53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnitOnProductEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct CategoryTheory AlgebraicGeometry Limits
open GlobalTheory GlobalTheory.PrimitiveUnitProduct
variable {K A O F : Type} [Field K] [CommRing A] [Algebra K A] [CommRing O] [IsDomain O]
  [ValuationRing O] [Field F] [Algebra O F] [IsFractionRing O F] [Algebra K O] [Algebra K F]
  [IsScalarTower K O F]
namespace GlobalTheory.PrimitiveUnitProduct
theorem _root_.solution (t : F ⊗[K] A) (ht : t ≠ 0) :
    ∃ (c : F) (t' : O ⊗[K] A),
      t = (c ⊗ₜ[K] (1 : A)) *
        Algebra.TensorProduct.map (IsScalarTower.toAlgHom K O F) (AlgHom.id K A) t' ∧
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom K O (IsLocalRing.ResidueField O))
        (AlgHom.id K A) t' ≠ 0 := by
  classical
  let b := Module.Basis.ofVectorSpace K A
  let bF := Algebra.TensorProduct.basis F b
  let bk := Algebra.TensorProduct.basis (IsLocalRing.ResidueField O) b
  let x := bF.repr t
  have hx : x.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    intro h
    exact ht (bF.repr.map_eq_zero_iff.mp h)
  obtain ⟨i₀, hi₀, hmax⟩ := x.support.exists_max_image
    (fun i => ValuationRing.valuation O F (x i)) hx
  have hc : x i₀ ≠ 0 := Finsupp.mem_support_iff.mp hi₀
  have hg : ∀ i, ∃ a : O, i ∈ x.support → algebraMap O F a = x i / x i₀ := by
    intro i
    by_cases hi : i ∈ x.support
    · have : x i / x i₀ ∈ (ValuationRing.valuation O F).integer := by
        rw [Valuation.mem_integer_iff, map_div₀]
        exact div_le_one_of_le₀ (hmax i hi) zero_le
      obtain ⟨a, ha⟩ := (ValuationRing.mem_integer_iff O F _).mp this
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h => (hi h).elim⟩
  choose g hg using hg
  refine ⟨x i₀, ∑ i ∈ x.support, g i ⊗ₜ[K] b i, ?_, ?_⟩
  · rw [map_sum, Finset.mul_sum]
    conv_lhs => rw [← bF.linearCombination_repr t, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Algebra.TensorProduct.map_tmul, IsScalarTower.coe_toAlgHom', hg i hi,
      AlgHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, bF,
      Algebra.TensorProduct.basis_apply, smul_tmul', smul_eq_mul, mul_one]
    rw [mul_div_cancel₀ _ hc]
  · intro h
    have h1 : g i₀ = 1 := by
      apply IsFractionRing.injective O F
      rw [hg i₀ hi₀, div_self hc, map_one]
    have h2 := congrArg (fun z => bk.repr z i₀) h
    simp only [map_sum, Algebra.TensorProduct.map_tmul, IsScalarTower.coe_toAlgHom',
      AlgHom.id_apply, map_zero, Finsupp.coe_zero, Pi.zero_apply, bk,
      Algebra.TensorProduct.basis_repr_tmul, Module.Basis.repr_self, Finsupp.coe_finset_sum,
      Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply, Finsupp.mapRange_apply,
      Finsupp.single_apply] at h2
    rw [Finset.sum_eq_single i₀] at h2
    · simp [h1] at h2
    · intro j _ hj
      simp [hj]
    · intro h; exact (h hi₀).elim
end GlobalTheory.PrimitiveUnitProduct
