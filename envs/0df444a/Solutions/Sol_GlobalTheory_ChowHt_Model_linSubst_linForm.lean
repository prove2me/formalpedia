-- Prove2me | solution 1 for GlobalTheory.ChowHt.Model.linSubst_linForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:10:43.514954+00:00
-- url     : https://prove2.me/submissions/f927516f-ba3c-4a80-8f90-8cffedbee192

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsHomogeneousOfEquivariant
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BlockSphereMeanLinForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial NumberField
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.ChowHt.Model
namespace GlobalTheory.ChowHt.Model
theorem _root_.solution {R : Type} [CommRing R] {N n : ℕ} (M : Matrix (Fin N) (Fin n) R)
    (c : Fin N → R) : linSubst M (linForm c) = linForm (fun k => ∑ j, M j k * c j) := by
  simp only [linSubst, linForm, map_sum, map_mul, aeval_C, aeval_X, algebraMap_eq, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
end GlobalTheory.ChowHt.Model
