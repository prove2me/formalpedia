-- Prove2me | solution 1 for GlobalTheory.sum_exp_pair_mul_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:41:17.543724+00:00
-- url     : https://prove2.me/submissions/4de53933-3114-4ccf-9602-42177e67f7f1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HasSumLocallyUniformlyOnIteratedFDerivRiemannThe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareDetA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FromBlocksMapIntCastMemSymplecticGroup
import Theorems.Thm_GlobalTheory_intCast_mulVec_complex
import Theorems.Thm_GlobalTheory_intCast_dotProduct_complex
import Theorems.Thm_GlobalTheory_fromBlocks_map_intCast_mem_symplecticGroup
import Theorems.Thm_GlobalTheory_symplectic_fromBlocks_inv_relations
import Theorems.Thm_GlobalTheory_isUnit_det_map_intCast
import Theorems.Thm_GlobalTheory_IsSiegel_mk
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_zero
import Theorems.Thm_GlobalTheory_mem_siegelUpperCoords
import Theorems.Thm_GlobalTheory_ratCircleChar_pairQuadraticForm_mk
import Theorems.Thm_GlobalTheory_riemannThetaJointForm_apply
import Theorems.Thm_GlobalTheory_symm_coprime_of_mem_symplecticGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.lineDerivList_nil
attribute [local simp] GlobalTheory.lineDerivList_zero
attribute [local simp] GlobalTheory.mem_siegelUpperCoords
attribute [local simp] GlobalTheory.riemannThetaJointForm_apply



set_option autoImplicit false
open Complex Matrix
open scoped Real
noncomputable section
open GlobalTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {a b c d : Matrix ι ι ℤ}
namespace GlobalTheory
theorem _root_.solution (h : fromBlocks a b c d ∈ symplecticGroup ι ℤ) (hd : d.det ≠ 0)
    (hb : ∀ μ, Even (μ ⬝ᵥ (dᵀ * b) *ᵥ μ)) (hc : ∀ μ, Even (μ ⬝ᵥ (aᵀ * c) *ᵥ μ))
    {κ : Type*} [Fintype κ] (r : κ → ι → ℤ)
    (hr : Function.Bijective fun k =>
      (Submodule.Quotient.mk (r k) : (ι → ℤ) ⧸ LinearMap.range d.mulVecLin)) (m : ι → ℤ) :
    ∑ k, cexp (π * I * ((fun i => (r k i : ℂ)) ⬝ᵥ
        (b.map ((↑) : ℤ → ℂ) * (d.map ((↑) : ℤ → ℂ))⁻¹) *ᵥ fun i => (r k i : ℂ))) *
      cexp (2 * π * I * ((fun i => (m i : ℂ)) ⬝ᵥ
        (d.map ((↑) : ℤ → ℂ))⁻¹ *ᵥ fun i => (r k i : ℂ))) =
    (∑ k, cexp (π * I * ((fun i => (r k i : ℂ)) ⬝ᵥ
        (b.map ((↑) : ℤ → ℂ) * (d.map ((↑) : ℤ → ℂ))⁻¹) *ᵥ fun i => (r k i : ℂ)))) *
      cexp (π * I * ((fun i => (m i : ℂ)) ⬝ᵥ
        ((d.map ((↑) : ℤ → ℂ))⁻¹ * c.map ((↑) : ℤ → ℂ)) *ᵥ fun i => (m i : ℂ))) := by
  have hs := (symm_coprime_of_mem_symplecticGroup h).1
  obtain ⟨h1, -, h3⟩ := symplectic_fromBlocks_inv_relations
    (fromBlocks_map_intCast_mem_symplecticGroup ℂ h) (isUnit_det_map_intCast ℂ hd)
  let := Fintype.ofBijective _ hr
  set Φ := fun x => ratCircleChar (pairQuadraticForm hd hs hb x) with hΦ
  have e1 : ∑ k, Φ (Submodule.Quotient.mk (r k)) =
      ∑ k, Φ (Submodule.Quotient.mk (r k - c *ᵥ m)) := by
    rw [Fintype.sum_bijective _ hr _ Φ fun _ => rfl]
    exact (Fintype.sum_bijective _
      ((Equiv.subRight (Submodule.Quotient.mk (c *ᵥ m))).bijective.comp hr) _ Φ fun _ => rfl).symm
  simp only [hΦ, ratCircleChar_pairQuadraticForm_mk] at e1
  rw [e1, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  obtain ⟨t, ht⟩ := hc m
  have ht' := congrArg ((↑) : ℤ → ℂ) ht
  rw [← mulVec_mulVec, intCast_dotProduct_complex, intCast_mulVec_complex, intCast_mulVec_complex,
    transpose_map] at ht'
  have hu := intCast_dotProduct_complex m (aᵀ *ᵥ r k)
  rw [intCast_mulVec_complex, transpose_map] at hu
  have e2 : (fun i => ((r k - c *ᵥ m) i : ℂ)) =
      (fun i => (r k i : ℂ)) - c.map ((↑) : ℤ → ℂ) *ᵥ fun i => (m i : ℂ) := by
    rw [← intCast_mulVec_complex]
    ext i
    simp
  have e3 (v : ι → ℂ) : (c.map ((↑) : ℤ → ℂ) *ᵥ fun i => (m i : ℂ)) ⬝ᵥ
      (b.map ((↑) : ℤ → ℂ) * (d.map ((↑) : ℤ → ℂ))⁻¹) *ᵥ v =
      (fun i => (m i : ℂ)) ⬝ᵥ (a.map ((↑) : ℤ → ℂ))ᵀ *ᵥ v -
        (fun i => (m i : ℂ)) ⬝ᵥ (d.map ((↑) : ℤ → ℂ))⁻¹ *ᵥ v := by
    rw [← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, h3, sub_mulVec, dotProduct_sub]
  rw [← Complex.exp_add, ← Complex.exp_add, e2, mulVec_sub, sub_dotProduct, dotProduct_sub,
    dotProduct_sub, dotProduct_mulVec_comm_of_isSymm h1 _ (c.map _ *ᵥ _), e3, e3, ← hu, ht',
    ← mulVec_mulVec (fun i => (m i : ℂ))]
  refine Complex.exp_eq_exp_iff_exists_int.2 ⟨m ⬝ᵥ aᵀ *ᵥ r k - t, ?_⟩
  push_cast
  ring
end GlobalTheory
