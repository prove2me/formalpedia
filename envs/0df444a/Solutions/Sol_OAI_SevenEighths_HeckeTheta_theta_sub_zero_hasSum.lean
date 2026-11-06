-- Prove2me | solution 1 for OAI.SevenEighths.HeckeTheta.theta_sub_zero_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:44:56.054358+00:00
-- url     : https://prove2.me/submissions/bd463d7f-0218-4123-9166-b9ce051899db

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Theta
import Definitions.Def_OAI_NumberTheory_DirichletL_LatticeSummability
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_ThetaSeries
import Theorems.Thm_OAI_SevenEighths_HeckeTheta_periodicCoeff_zero
import Theorems.Thm_OAI_SevenEighths_EisensteinTheta_parityPair_k
import Theorems.Thm_OAI_SevenEighths_HeckeTheta_pair_k
import Theorems.Thm_OAI_SevenEighths_HeckeTheta_theta_hasSum
import Theorems.Thm_OAI_SevenEighths_LatticeSummability_normForm_eq_zero_iff
import Theorems.Thm_OAI_SevenEighths_ThetaProduct_rectangularPair_k
import Theorems.Thm_P2M_OAI_SevenEighths_HeckeTheta_pair_f__4d2050f76d8c
attribute [local simp] OAI.SevenEighths.EisensteinTheta.parityPair_k
attribute [local simp] OAI.SevenEighths.HeckeTheta.pair_k
attribute [local simp] OAI.SevenEighths.ThetaProduct.rectangularPair_k


attribute [local simp] OAI.SevenEighths.HeckeTheta.periodicCoeff_zero
section
namespace OAI
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace SevenEighths.HeckeTheta
open EisensteinTheta LatticeSummability
private theorem normForm_coordinates_eq_zero (n : ℤ × ℤ) :
    normForm n.1 n.2 = 0 ↔ n = (0, 0) := by
  rw [normForm_eq_zero_iff]
  simp only [Int.cast_eq_zero, Prod.ext_iff]
end SevenEighths.HeckeTheta
end
end OAI
end

set_option autoImplicit false
open OAI
noncomputable section
open MeasureTheory Set
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.HeckeTheta
open EisensteinTheta LatticeSummability
namespace OAI.SevenEighths.HeckeTheta
theorem _root_.solution {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ × ℤ => if normForm n.1 n.2 = 0 then 0 else
      periodicCoeff w n * (Real.exp (-Real.pi * normForm n.1 n.2 * t) : ℂ))
      ((pair w).f t - (pair w).f₀) := by
  have h := (theta_hasSum w ht).sub (hasSum_ite_eq (0, 0) (w (0, 0)))
  rw [pair_f₀]
  convert h using 1 <;> try rfl
  funext n
  simp only [normForm_coordinates_eq_zero]
  by_cases hn : n = (0, 0)
  · subst n
    simp [normForm]
  · simp [hn]
end OAI.SevenEighths.HeckeTheta
