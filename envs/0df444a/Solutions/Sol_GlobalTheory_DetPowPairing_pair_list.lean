-- Prove2me | solution 1 for GlobalTheory.DetPowPairing.pair_list
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:56:16.58088+00:00
-- url     : https://prove2.me/submissions/5e8730a3-f9fe-47f8-b9e7-ad38bae890ba

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Theorems.Thm_GlobalTheory_DetPowPairing_pair_X_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
noncomputable section
open GlobalTheory GlobalTheory.DetPowPairing
open MvPolynomial
variable {σ : Type} {C : Type} [CommRing C]
namespace GlobalTheory.DetPowPairing
theorem _root_.solution {ι : Type} (f : ι → σ) (l : List ι) (P Q : MvPolynomial σ C) :
    pair (P * (l.map fun j => X (f j)).prod) Q =
      pair P (((l.map fun j => ((pderiv (f j) : Derivation C _ _) :
        MvPolynomial σ C →ₗ[C] MvPolynomial σ C)).prod : Module.End C (MvPolynomial σ C)) Q) := by
  induction l generalizing P with
  | nil => simp
  | cons j l ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, ← mul_assoc, ih, pair_X_mul]
    rfl
end GlobalTheory.DetPowPairing
