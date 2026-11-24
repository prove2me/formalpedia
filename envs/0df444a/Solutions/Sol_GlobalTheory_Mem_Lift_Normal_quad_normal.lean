-- Prove2me | solution 1 for GlobalTheory.Mem.Lift.Normal.quad_normal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:32:54.473993+00:00
-- url     : https://prove2.me/submissions/c83ee7db-6fc2-4302-8252-3cb80a78f592

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionUnitaryGroupHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeisenbergSmoothOfWeakDerivativeClosedSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HeisenbergSmoothVectorDerivativeCalculus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfNormal
import Theorems.Thm_GlobalTheory_Mem_Lift_dH_add
import Theorems.Thm_GlobalTheory_Mem_Lift_dH_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology
noncomputable section
namespace GlobalTheory.Mem.Lift.Normal
variable {ι : Type}
variable [Fintype ι] [DecidableEq ι]
private theorem sm_add' {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    {ρ : (ι → ℂ) → B →L[ℂ] B} {f g : B} (hf : Sm ρ f) (hg : Sm ρ g) : Sm ρ (f + g) := by
  unfold Sm at *
  simp only [map_add]
  exact hf.add hg
private theorem sm_smul' {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    {ρ : (ι → ℂ) → B →L[ℂ] B} {f : B} (a : ℂ) (hf : Sm ρ f) : Sm ρ (a • f) := by
  unfold Sm at *
  simp only [map_smul]
  exact hf.const_smul a
end GlobalTheory.Mem.Lift.Normal
end
end

set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Lift GlobalTheory.Mem.Lift.Normal
variable {ι : Type}
variable [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.Mem.Lift.Normal
theorem _root_.solution (H X : Matrix ι ι ℂ) {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    (ρ : (ι → ℂ) → B →L[ℂ] B) (f : B) (hs : ∀ v, Sm ρ (dH ρ v f)) :
    quad ρ (nC X) nP (nQ H) f = nOp ρ H X f := by
  have hy : ∀ j : ι, Sm ρ (dH ρ (H⁻¹ *ᵥ Pi.single j 1) f) := fun j => hs _
  have hIy : ∀ j : ι, Sm ρ (dH ρ (I • H⁻¹ *ᵥ Pi.single j 1) f) := fun j => hs _

  have hexp : ∀ (u : ι → ℂ) (j : ι), dH ρ u (dOp ρ H j f) = (-(1 / (4 * π)) : ℂ) •
      (dH ρ u (dH ρ (H⁻¹ *ᵥ Pi.single j 1) f) + I • dH ρ u (dH ρ (I • H⁻¹ *ᵥ Pi.single j 1) f)) := by
    intro u j
    unfold dOp
    rw [dH_smul u _ (sm_add' (hy j) (sm_smul' I (hIy j))),
      dH_add u (hy j) (sm_smul' I (hIy j)), dH_smul u I (hIy j)]
  unfold quad nOp xOp
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [nC, nP, nQ, Bool.false_eq_true, ↓reduceIte, hexp]
  module
end GlobalTheory.Mem.Lift.Normal
