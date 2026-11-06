-- Prove2me | solution 1 for OAI.SevenEighths.HeckeTheta.norm_periodicCoeff_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:44:11.364499+00:00
-- url     : https://prove2.me/submissions/6e682c7a-f0f1-429e-95f4-d836182549f1

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Theta
import Definitions.Def_OAI_NumberTheory_DirichletL_LatticeSummability
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_ThetaSeries

set_option autoImplicit false
open OAI
noncomputable section
open MeasureTheory Set
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.HeckeTheta
open EisensteinTheta LatticeSummability
namespace OAI.SevenEighths.HeckeTheta
theorem _root_.solution {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    (n : ℤ × ℤ) : ‖periodicCoeff w n‖ ≤ ∑ a, ‖w a‖ := by
  unfold periodicCoeff
  exact Finset.single_le_sum (fun a _ => norm_nonneg (w a)) (Finset.mem_univ _)
end OAI.SevenEighths.HeckeTheta
