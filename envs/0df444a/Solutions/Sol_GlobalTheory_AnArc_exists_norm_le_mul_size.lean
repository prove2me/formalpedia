-- Prove2me | solution 1 for GlobalTheory.AnArc.exists_norm_le_mul_size
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:07:29.815639+00:00
-- url     : https://prove2.me/submissions/5087e462-070f-471e-b1b4-1afcc70fc82c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SummableExpNegSumAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HasSumLocallyUniformlyOnTerm
import Theorems.Thm_GlobalTheory_AnArc_norm_le_mul_size

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution {E : Type*} [SeminormedAddCommGroup E] (f : A.X →+ E) :
    ∃ C, 0 ≤ C ∧ ∀ μ, ‖f μ‖ ≤ C * A.size μ :=
  ⟨∑ i, ‖f (Module.Free.chooseBasis ℤ A.X i)‖, Finset.sum_nonneg fun _ _ => norm_nonneg _,
    A.norm_le_mul_size f fun i => Finset.single_le_sum
      (f := fun i => ‖f (Module.Free.chooseBasis ℤ A.X i)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)⟩
end GlobalTheory.AnArc
