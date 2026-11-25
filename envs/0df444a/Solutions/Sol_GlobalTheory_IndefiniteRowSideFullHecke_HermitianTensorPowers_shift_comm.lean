-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.HermitianTensorPowers.shift_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:51:08.597099+00:00
-- url     : https://prove2.me/submissions/538aa027-740f-4091-b8ed-98323d5f9661

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_HermitianTensorPowers
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_HermitianTensorPowers_herm_add_left
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_HermitianTensorPowers_herm_swap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianTensorPowers
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.IndefiniteRowSideFullHecke.HermitianTensorPowers
theorem _root_.solution {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) (k : ℕ) (v w : Fin g → ℂ)
    (θ : (Fin g → ℂ) → ℂ) (z : Fin g → ℂ) :
    shift Hm k v (shift Hm k w θ) z = commVal Hm k v w * shift Hm k w (shift Hm k v θ) z := by
  have h1 : herm Hm v w - herm Hm w v = 2 * ((herm Hm v w).im : ℂ) * Complex.I := by
    rw [herm_swap h v w, Complex.sub_conj]; push_cast; ring
  simp only [shift, commVal, Units.val_mk0, herm_add_left]
  rw [add_right_comm z w v, ← _root_.mul_assoc (Complex.exp _) (Complex.exp _) (θ _), ← _root_.mul_assoc (Complex.exp _) (Complex.exp _) (θ _),
    ← _root_.mul_assoc (Complex.exp _) _ (θ _), ← Complex.exp_add, ← Complex.exp_add,
    ← Complex.exp_add]
  refine congrArg (fun t => Complex.exp t * θ (z + v + w)) ?_
  linear_combination (-(k : ℂ) * Real.pi) * h1
end GlobalTheory.IndefiniteRowSideFullHecke.HermitianTensorPowers
