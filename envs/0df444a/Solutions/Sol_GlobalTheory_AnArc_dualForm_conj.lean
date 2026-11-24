-- Prove2me | solution 1 for GlobalTheory.AnArc.dualForm_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:36:15.838646+00:00
-- url     : https://prove2.me/submissions/3101184c-c7ee-4eb3-a975-3051a51967bf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Theorems.Thm_GlobalTheory_AnArc_Bw_symm
import Theorems.Thm_GlobalTheory_AnArc_BwMat_apply
import Theorems.Thm_GlobalTheory_AnArc_dualForm_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open Matrix
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution (w : ℂ) (r r' : A.X →+ ℂ) : starRingEnd ℂ (A.dualForm w r r') = A.dualForm w r' r := by
  classical
  have hC : (A.BwMat w).IsHermitian := by
    ext i j; simp [BwMat_apply, A.Bw_symm w (Module.Free.chooseBasis ℤ A.X i)]
  have h : ∀ i k, (A.BwMat w)⁻¹ i k = (A.BwMat w)⁻¹ k i := fun i k => by simpa using hC.inv.apply k i
  simp only [dualForm_apply, dotProduct, mulVec, map_sum, map_mul, Finset.mul_sum, Pi.star_apply,
    RCLike.star_def, Complex.conj_conj, Matrix.map_apply, Complex.conj_ofReal]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by rw [h k i]; ring
end GlobalTheory.AnArc
