-- Prove2me | solution 1 for GlobalTheory.ThetaUnifCompare.chi_eq_one_or_of_sym
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:26:07.461527+00:00
-- url     : https://prove2.me/submissions/f9b10e46-dfcd-4c78-9a53-2e8a87466e1b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_HermitianTensorPowers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ConstOfNormPeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ChiEqOneOrOfSym
import Theorems.Thm_GlobalTheory_ThetaUnifCompare_chi_neg_of_sym
import Theorems.Thm_GlobalTheory_EigenNorm_hermForm_conj
import Theorems.Thm_GlobalTheory_FrameValue_chi_add
import Theorems.Thm_GlobalTheory_FrameValue_chi_zero
import Theorems.Thm_GlobalTheory_FrameValue_hermForm_neg_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.ThetaUnifCompare
open GlobalTheory.FrameValue GlobalTheory.IndefiniteRowSideFullHecke.HermitianTensorPowers CubeValues SymmetricSemicharacter EigenNorm
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g}
  {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
namespace GlobalTheory.ThetaUnifCompare
theorem _root_.solution (hL : L.IsLB) (hs : Out.Sym A L) (h : u.IsAH Hm χ) (l : u.Λ) : χ l = 1 ∨ χ l = -1 := by
  have e := chi_add hL h l (-l)
  have hi : (hermForm Hm l l).im = 0 := Complex.conj_eq_iff_im.1 (hermForm_conj Hm h.1 l l).symm
  rw [add_neg_cancel, chi_zero hL h, chi_neg_of_sym hL hs h, Submodule.coe_neg, hermForm_neg_right, Complex.neg_im,
    hi] at e
  exact mul_self_eq_one_iff.1 (by simpa using e.symm)
end GlobalTheory.ThetaUnifCompare
