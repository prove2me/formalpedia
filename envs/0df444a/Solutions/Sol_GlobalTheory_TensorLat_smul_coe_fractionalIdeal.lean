-- Prove2me | solution 1 for GlobalTheory.TensorLat.smul_coe_fractionalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:11:30.617185+00:00
-- url     : https://prove2.me/submissions/40315626-4400-41fe-9757-48615f96926e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NsmulApplyMemOfMemTensorLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemOfMemSpanFraction
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsIntSmulMemSpan
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCE
import Definitions.Def_ReciprocityTheory_DualLattices_WedgeNeZeroOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsCoeEqSpanDetOfIntVecLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TensorLat
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)
open scoped nonZeroDivisors
open ReciprocityTheory.MultiplicativeHeights.SemiDegIdx ReciprocityTheory.PGsh
variable {K : Type} [Field K] [NumberField K] {n : ℕ}
namespace GlobalTheory.TensorLat
theorem _root_.solution (𝔫 : Ideal (𝓞 K)) (J : FractionalIdeal (𝓞 K)⁰ K) :
    𝔫 • (J : Submodule (𝓞 K) K) =
      (((𝔫 : FractionalIdeal (𝓞 K)⁰ K) * J : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
  rw [FractionalIdeal.coe_mul]
  refine le_antisymm (Submodule.smul_le.2 fun a ha x hx => ?_)
    (Submodule.mul_le.2 fun a ha x hx => ?_)
  · rw [Algebra.smul_def]
    exact Submodule.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ ha) hx
  · obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ha
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem_smul hb hx
end GlobalTheory.TensorLat
