-- Prove2me | solution 1 for GlobalTheory.Mem.An.Model.zmult_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:00:36.517771+00:00
-- url     : https://prove2.me/submissions/483c8b77-fad6-4537-978a-490dab8c7d17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NormOneSevenOneTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.An GlobalTheory.Mem.An.Model
namespace GlobalTheory.Mem.An.Model
theorem _root_.solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ρ : ℂ)
    (h : DirichletCharacter.LFunction χ ρ = 0) : 0 < zmult χ ρ := by
  have hd := DirichletCharacter.differentiable_LFunction hχ
  have htop : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ ⊤ := by
    intro ht
    rw [analyticOrderAt_eq_top] at ht
    have han : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) Set.univ := fun z _ => hd.analyticAt z
    have hz := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ ρ) ht
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ) (s := 2) (Or.inl hχ)
      (by norm_num) (hz (Set.mem_univ 2))
  have h0 : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ 0 :=
    (hd.analyticAt ρ).analyticOrderAt_ne_zero.mpr h
  show 0 < analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ
  rw [Nat.pos_iff_ne_zero]
  intro h'
  apply h0
  rw [← Nat.cast_analyticOrderNatAt htop, h', Nat.cast_zero]
end GlobalTheory.Mem.An.Model
