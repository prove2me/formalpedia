-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.isClosed_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:57:12.721028+00:00
-- url     : https://prove2.me/submissions/cb41081b-9dee-4934-9e9d-4efdaf0ebb00

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Degree
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ClosedSubgroups
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_DegreeDecomposition
import Theorems.Thm_GroundTheory_Global_Cyclotomic_isOpen_stabilizer_ringOfIntegers
import Theorems.Thm_GroundTheory_Global_Cyclotomic_padicEquiv_apply
import Theorems.Thm_GroundTheory_Global_Cyclotomic_padicEquiv_symm_apply
import Theorems.Thm_GroundTheory_Global_Cyclotomic_val_unitsPadicEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.Cyclotomic.padicEquiv_apply
attribute [local simp] GroundTheory.Global.Cyclotomic.padicEquiv_symm_apply
attribute [local simp] GroundTheory.Global.Cyclotomic.val_unitsPadicEquiv_apply



set_option autoImplicit false
open NumberField IntermediateField Filter Topology
open scoped GroundTheory.LocalField.Abstract Pointwise
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
open GroundTheory.LocalField.Abstract
local notation "ℚ̄" => AlgebraicClosure ℚ
namespace GroundTheory.Global.Cyclotomic
theorem _root_.solution (P : Ideal (𝓞 ℚ̄)) :
    IsClosed (MulAction.stabilizer Gal(ℚ̄/ℚ) P : Set Gal(ℚ̄/ℚ)) := by
  let _ : TopologicalSpace (𝓞 ℚ̄) := ⊥
  have : DiscreteTopology (𝓞 ℚ̄) := ⟨rfl⟩
  have : ContinuousSMul Gal(ℚ̄/ℚ) (𝓞 ℚ̄) :=
    continuousSMul_iff_stabilizer_isOpen.2 isOpen_stabilizer_ringOfIntegers
  have hset : (MulAction.stabilizer Gal(ℚ̄/ℚ) P : Set Gal(ℚ̄/ℚ)) =
      (⋂ x ∈ P, (fun σ : Gal(ℚ̄/ℚ) => σ • x) ⁻¹' (P : Set (𝓞 ℚ̄))) ∩
        ⋂ x ∈ P, (fun σ : Gal(ℚ̄/ℚ) => σ⁻¹ • x) ⁻¹' (P : Set (𝓞 ℚ̄)) := by
    ext σ
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_preimage]
    constructor
    · intro h
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · rw [← h]
        exact Ideal.smul_mem_pointwise_smul_iff.2 hx
      · rw [← Ideal.mem_pointwise_smul_iff_inv_smul_mem, h]
        exact hx
    · rintro ⟨h1, h2⟩
      apply le_antisymm
      · intro y hy
        rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
        have := h1 _ hy
        rwa [smul_inv_smul] at this
      · intro y hy
        rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
        exact h2 y hy
  rw [hset]
  refine (isClosed_biInter fun x _ => ?_).inter (isClosed_biInter fun x _ => ?_)
  · exact (isClosed_discrete (P : Set (𝓞 ℚ̄))).preimage (continuous_id.smul continuous_const)
  · exact (isClosed_discrete (P : Set (𝓞 ℚ̄))).preimage (continuous_inv.smul continuous_const)
end GroundTheory.Global.Cyclotomic
