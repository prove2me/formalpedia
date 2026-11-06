-- Prove2me | solution 1 for OAI.SevenEighths.HeckeTheta.latticeL_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:48:35.396603+00:00
-- url     : https://prove2.me/submissions/ebf2b1cf-354f-449e-a2c7-9ea13dc6f1b7

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Theta
import Definitions.Def_OAI_NumberTheory_DirichletL_LatticeSummability
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_ThetaSeries
import Theorems.Thm_OAI_SevenEighths_HeckeTheta_completed_hasSum

set_option autoImplicit false
open OAI
noncomputable section
open MeasureTheory Set
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.HeckeTheta
open EisensteinTheta LatticeSummability
namespace OAI.SevenEighths.HeckeTheta
theorem _root_.solution {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℤ × ℤ => periodicCoeff w n / (normForm n.1 n.2 : ℂ) ^ s)
      (latticeL w s) := by
  have hΓ := Complex.Gamma_ne_zero_of_re_pos (by linarith : 0 < s.re)
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpow : (Real.pi : ℂ) ^ s ≠ 0 := fun h => hπ ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have h := (completed_hasSum w hs).mul_left ((Real.pi : ℂ) ^ s * (Complex.Gamma s)⁻¹)
  change HasSum _ ((Real.pi : ℂ) ^ s * (Complex.Gamma s)⁻¹ * completed w s)
  convert h using 1 <;> try rfl
  funext n
  rw [Complex.cpow_neg]
  field_simp
end OAI.SevenEighths.HeckeTheta
