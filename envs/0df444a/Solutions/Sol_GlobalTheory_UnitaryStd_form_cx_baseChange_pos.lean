-- Prove2me | solution 1 for GlobalTheory.UnitaryStd.form_cx_baseChange_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:36:59.350558+00:00
-- url     : https://prove2.me/submissions/7b133df8-d1d9-4655-8672-5282be455455

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BasisApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryStandardLatticeFormComplexStructureBaseCh
import Theorems.Thm_GlobalTheory_UnitaryStd_form_cx_basis
import Theorems.Thm_GlobalTheory_UnitaryStd_basis_apply
import Theorems.Thm_GlobalTheory_UnitaryStd_smul_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped TensorProduct
open GlobalTheory GlobalTheory.UnitaryStd
variable {E : Type} [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) (g : ℕ)
namespace GlobalTheory.UnitaryStd
theorem _root_.solution (S : Matrix (Fin r) (Fin r) ℤ) (hS : (S.map (Int.cast : ℤ → ℝ)).PosDef)
    (x : ℝ ⊗[ℤ] Lat ρ g) (hx : x ≠ 0) :
    0 < (form ρ g S).baseChange ℝ ((cx ρ g).baseChange ℝ x) x := by
  set b := Algebra.TensorProduct.basis ℝ (basis ρ g) with hb
  set c := b.repr x with hc
  have hx' : x = ∑ p, c p • b p := (b.sum_repr x).symm
  have key : (form ρ g S).baseChange ℝ ((cx ρ g).baseChange ℝ x) x =
      ∑ q, ∑ p, c p * c q * (((if p.2 = q.2 then S p.1 q.1 else 0 : ℤ)) : ℝ) := by
    conv_lhs => rw [hx']
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hb,
      Algebra.TensorProduct.basis_apply, LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul,
      form_cx_basis, mul_one, zsmul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    ring
  set v : (Fin g ⊕ Fin g) → Fin r → ℝ := fun α i => c (i, α) with hv
  have key2 : (form ρ g S).baseChange ℝ ((cx ρ g).baseChange ℝ x) x =
      ∑ α, v α ⬝ᵥ ((S.map (Int.cast : ℤ → ℝ)).mulVec (v α)) := by
    rw [key, Finset.sum_comm]
    simp only [Fintype.sum_prod_type, Int.cast_ite, Int.cast_zero, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, dotProduct, Matrix.mulVec,
      Matrix.map_apply, Finset.mul_sum, hv]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [key2]
  have hnn : ∀ α, 0 ≤ v α ⬝ᵥ ((S.map (Int.cast : ℤ → ℝ)).mulVec (v α)) := by
    intro α
    by_cases h0 : v α = 0
    · simp [h0]
    · simpa using (hS.dotProduct_mulVec_pos h0).le
  have hne : c ≠ 0 := by
    intro h; apply hx; rw [hx']; simp [h]
  obtain ⟨⟨i, α⟩, hp⟩ : ∃ p, c p ≠ 0 := by
    by_contra h; push_neg at h; exact hne (Finsupp.ext h)
  have hα : v α ≠ 0 := fun h => hp (by simpa [hv] using congrFun h i)
  have hpos : 0 < v α ⬝ᵥ ((S.map (Int.cast : ℤ → ℝ)).mulVec (v α)) := by
    simpa using hS.dotProduct_mulVec_pos hα
  exact lt_of_lt_of_le hpos (Finset.single_le_sum (fun β _ => hnn β) (Finset.mem_univ α))
end GlobalTheory.UnitaryStd
