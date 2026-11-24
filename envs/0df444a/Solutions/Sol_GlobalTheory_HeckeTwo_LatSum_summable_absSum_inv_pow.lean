-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.LatSum.summable_absSum_inv_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:21:58.311012+00:00
-- url     : https://prove2.me/submissions/dd3917b4-ff5b-414c-be60-de3619c9131b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableHeckeBalancedLatticeDoubleSum
import Theorems.Thm_GlobalTheory_HeckeTwo_LatSum_absSum_nonneg
import Theorems.Thm_GlobalTheory_HeckeTwo_LatSum_norm_mixedEmbedding_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.LatSum
variable {F : Type} [Field F] [NumberField F]
variable [IsTotallyReal F]
open scoped Classical
namespace GlobalTheory.HeckeTwo.LatSum
theorem _root_.solution (I : Frac F) {k : ℕ} (hk : Module.finrank ℚ F < k) :
    Summable (fun x : NZ (I : FractionalIdeal (𝓞 F)⁰ F) => ((absSum x.1) ^ k)⁻¹) := by
  let L := mixedEmbedding.idealLattice F I
  have hL := ZLattice.summable_norm_rpow L (-(k : ℝ)) (by
    rw [ZLattice.rank ℝ L, mixedEmbedding.finrank F]
    have : (Module.finrank ℚ F : ℝ) < k := by exact_mod_cast hk
    linarith)
  let j : NZ (I : FractionalIdeal (𝓞 F)⁰ F) → L := fun x =>
    ⟨mixedEmbedding F x.1, (mixedEmbedding.mem_idealLattice F I).2 ⟨x.1, x.2.1, rfl⟩⟩
  have hj : Function.Injective j := fun x y h =>
    Subtype.ext ((mixedEmbedding F).injective (congrArg Subtype.val h))
  refine (hL.comp_injective hj).of_nonneg_of_le (fun x => inv_nonneg.2 (pow_nonneg (absSum_nonneg _) _))
    (fun x => ?_)
  have hpos : 0 < ‖mixedEmbedding F x.1‖ := norm_pos_iff.2 fun h =>
    x.2.2 ((mixedEmbedding F).injective (h.trans (map_zero _).symm))
  show ((absSum x.1) ^ k)⁻¹ ≤ ‖mixedEmbedding F x.1‖ ^ (-(k : ℝ))
  rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast]
  exact inv_anti₀ (pow_pos hpos k) (pow_le_pow_left₀ hpos.le (norm_mixedEmbedding_le x.1) k)
end GlobalTheory.HeckeTwo.LatSum
