-- Prove2me | solution 1 for OAI.PoissonChildCRT.mask_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:19:44.79632+00:00
-- url     : https://prove2.me/submissions/2918fd92-730a-4e5d-9698-4c6d631eb737

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open OAI.PoissonChildCRT
open scoped Classical
variable (n : ℕ) (χ : MulChar (ZMod n) ℂ)
namespace OAI.PoissonChildCRT
theorem _root_.solution (n a b : ℕ) :
    mask n (a * b) = mask n a * mask n b := by
  classical
  simp only [mask]
  by_cases hab : n.Coprime (a * b)
  · have ha : n.Coprime a := (Nat.coprime_mul_iff_right.mp hab).1
    have hb : n.Coprime b := (Nat.coprime_mul_iff_right.mp hab).2
    rw [if_pos hab, if_pos ha, if_pos hb]
    norm_num
  · have hna_or_hnb : ¬ n.Coprime a ∨ ¬ n.Coprime b := by
      by_contra h
      exact hab (Nat.coprime_mul_iff_right.mpr ⟨not_not.mp (not_or.mp h).1,
        not_not.mp (not_or.mp h).2⟩)
    rcases hna_or_hnb with hna | hnb
    · rw [if_neg hab, if_neg hna]
      simp
    · rw [if_neg hab, if_neg hnb]
      simp
end OAI.PoissonChildCRT
