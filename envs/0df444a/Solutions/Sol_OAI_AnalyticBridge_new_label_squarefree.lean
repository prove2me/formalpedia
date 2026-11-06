-- Prove2me | solution 1 for OAI.AnalyticBridge.new_label_squarefree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:04:23.105228+00:00
-- url     : https://prove2.me/submissions/0f468161-cfc8-41fd-af08-d4960c838bfe

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open OAI.AnalyticBridge
variable {Ω : Type*}
namespace OAI.AnalyticBridge
theorem _root_.solution
    (J C g e v : ℕ)
    (hJ : Squarefree J) (hC : Squarefree C)
    (he : Squarefree e) (hv : Squarefree v)
    (hCJ : C.Coprime J)
    (hg : g.Coprime (C * J))
    (hvold : v.Coprime (g * C * J))
    (he_g : e ∣ g) : Squarefree (J * C * e * v) := by
  have hJC : J.Coprime C := hCJ.symm
  have hJCe : (J * C).Coprime e := by
    have h := Nat.Coprime.of_dvd_left he_g hg
    simpa [mul_comm] using h.symm
  have hdiv : J * C * e ∣ g * C * J := by
    have h := Nat.mul_dvd_mul_left (J * C) he_g
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hJCev : (J * C * e).Coprime v :=
    (Nat.Coprime.of_dvd_right hdiv hvold).symm
  apply Nat.squarefree_mul_iff.mpr
  refine ⟨hJCev, ?_, hv⟩
  apply Nat.squarefree_mul_iff.mpr
  refine ⟨hJCe, ?_, he⟩
  exact Nat.squarefree_mul_iff.mpr ⟨hJC, hJ, hC⟩
end OAI.AnalyticBridge
