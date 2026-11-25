-- Prove2me | solution 1 for GlobalTheory.UnitRigidity.exists_normalised
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:25:31.565981+00:00
-- url     : https://prove2.me/submissions/0cef265c-396c-413f-8a5c-de83b0488abf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnitOnProductEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedOfIsPullbackOfSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.UnitRigidity
namespace GlobalTheory.UnitRigidity
theorem _root_.solution {K L B ι : Type*} [Field K] [Field L] [Algebra K L] [CommRing B] [Algebra K B]
    (b : Module.Basis ι K B) (O : ValuationSubring L) [Algebra K O] [IsScalarTower K O L]
    (w : L ⊗[K] B) (hw : w ≠ 0) :
    ∃ (a : L) (w' : O ⊗[K] B), a ≠ 0 ∧
      w = a • Algebra.TensorProduct.map (IsScalarTower.toAlgHom K O L) (AlgHom.id K B) w' ∧
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom K O (IsLocalRing.ResidueField O))
        (AlgHom.id K B) w' ≠ 0 ∧
      ∀ i, ∃ c : O, (Algebra.TensorProduct.basis L b).repr w i = a * c := by
  classical
  set c := (Algebra.TensorProduct.basis L b).repr w with hc
  have hne : c.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    simpa [hc] using hw
  obtain ⟨i₀, hi₀, hmax⟩ := c.support.exists_max_image (fun i => O.valuation (c i)) hne
  have h0 : c i₀ ≠ 0 := Finsupp.mem_support_iff.mp hi₀
  have hmem : ∀ i, c i / c i₀ ∈ O := by
    intro i
    rw [← O.valuation_le_one_iff, map_div₀, div_le_one₀ (by simpa [pos_iff_ne_zero] using h0)]
    by_cases hi : i ∈ c.support
    · exact hmax i hi
    · simp [Finsupp.notMem_support_iff.mp hi]
  refine ⟨c i₀, ∑ i ∈ c.support, (⟨_, hmem i⟩ : O) ⊗ₜ b i, h0, ?_, ?_, fun i => ⟨⟨_, hmem i⟩, ?_⟩⟩
  · rw [map_sum, Finset.smul_sum]
    conv_lhs => rw [← (Algebra.TensorProduct.basis L b).linearCombination_repr w, ← hc,
      Finsupp.linearCombination_apply, Finsupp.sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', mul_div_cancel₀ _ h0]
  · intro h
    have := congrArg (fun z => (Algebra.TensorProduct.basis (IsLocalRing.ResidueField O) b).repr z i₀) h
    simp only [map_sum, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id,
      Algebra.TensorProduct.basis_repr_tmul, Finsupp.coe_finset_sum, Finset.sum_apply, map_zero,
      Module.Basis.repr_self, Finsupp.coe_zero, Pi.zero_apply] at this
    rw [Finset.sum_eq_single i₀] at this
    · have e : (⟨_, hmem i₀⟩ : O) = 1 := Subtype.ext (div_self h0)
      rw [e] at this
      simp at this
    · intro i _ hi
      simp [hi]
    · exact fun h => (h hi₀).elim
  · simp [mul_div_cancel₀ _ h0]
end GlobalTheory.UnitRigidity
