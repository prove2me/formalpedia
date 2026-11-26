-- Prove2me | solution 1 for LowRankUnivariateSOS.peelingSchedule_of_factors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:01:25.401885+00:00
-- url     : https://prove2.me/submissions/9c2fb8b9-da75-4c4e-900a-5f38b30aa392

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_FactoredCase
import Definitions.Def_LowRankUnivariateSOS_PeelingStep
import Theorems.Thm_LowRankUnivariateSOS_A_scalePair_left
import Theorems.Thm_LowRankUnivariateSOS_A_self_eq_sigma2
import Theorems.Thm_LowRankUnivariateSOS_A_smul_right
import Theorems.Thm_LowRankUnivariateSOS_dot_add_left
import Theorems.Thm_LowRankUnivariateSOS_dot_add_right
import Theorems.Thm_LowRankUnivariateSOS_dot_neg_left
import Theorems.Thm_LowRankUnivariateSOS_dot_neg_right
import Theorems.Thm_LowRankUnivariateSOS_dot_smul_left
import Theorems.Thm_LowRankUnivariateSOS_dot_smul_right
import Theorems.Thm_LowRankUnivariateSOS_dot_zero_left
import Theorems.Thm_LowRankUnivariateSOS_dot_zero_right
import Theorems.Thm_LowRankUnivariateSOS_perpPair_fst
import Theorems.Thm_LowRankUnivariateSOS_perpPair_snd
import Theorems.Thm_LowRankUnivariateSOS_scalePair_fst
import Theorems.Thm_LowRankUnivariateSOS_scalePair_snd
import Theorems.Thm_LowRankUnivariateSOS_sigma2_perpPair
import Theorems.Thm_LowRankUnivariateSOS_sigma2_scalePair
import Theorems.Thm_LowRankUnivariateSOS_sigma2_smul
import Theorems.Thm_LowRankUnivariateSOS_smul_fst
import Theorems.Thm_LowRankUnivariateSOS_smul_snd
attribute [local simp] LowRankUnivariateSOS.A_scalePair_left
attribute [local simp] LowRankUnivariateSOS.A_self_eq_sigma2
attribute [local simp] LowRankUnivariateSOS.A_smul_right
attribute [local simp] LowRankUnivariateSOS.dot_add_left
attribute [local simp] LowRankUnivariateSOS.dot_add_right
attribute [local simp] LowRankUnivariateSOS.dot_neg_left
attribute [local simp] LowRankUnivariateSOS.dot_neg_right
attribute [local simp] LowRankUnivariateSOS.dot_smul_left
attribute [local simp] LowRankUnivariateSOS.dot_smul_right
attribute [local simp] LowRankUnivariateSOS.dot_zero_left
attribute [local simp] LowRankUnivariateSOS.dot_zero_right
attribute [local simp] LowRankUnivariateSOS.perpPair_fst
attribute [local simp] LowRankUnivariateSOS.perpPair_snd
attribute [local simp] LowRankUnivariateSOS.scalePair_fst
attribute [local simp] LowRankUnivariateSOS.scalePair_snd
attribute [local simp] LowRankUnivariateSOS.sigma2_perpPair
attribute [local simp] LowRankUnivariateSOS.sigma2_scalePair
attribute [local simp] LowRankUnivariateSOS.sigma2_smul
attribute [local simp] LowRankUnivariateSOS.smul_fst
attribute [local simp] LowRankUnivariateSOS.smul_snd



set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
namespace LowRankUnivariateSOS
theorem _root_.solution {u u0 : UPair} {gBase : Poly} {rs : List Poly}
    (hrs : ∀ r ∈ rs, r ∣ sigma2 u0)
    (hstep :
      ∀ {gStart gNext : Poly}, QuadraticFactorStep u0 gStart gNext →
        HasPeelingWitness u (scalePair gStart u0) (scalePair gNext u0)) :
    PeelingSchedule u u0 (gBase * rs.prod) (peelTerminalScale gBase rs) := by
  revert gBase
  induction rs with
  | nil =>
      intro gBase
      simpa [peelTerminalScale] using (PeelingSchedule.done (u := u) (u0 := u0) gBase)
  | cons r rs ih =>
      intro gBase
      have hr_sigma : r ∣ sigma2 u0 := hrs r (by simp)
      have hrs_tail : ∀ r' ∈ rs, r' ∣ sigma2 u0 := by
        intro r' hr'
        exact hrs r' (by simp [hr'])
      have hfg :
          QuadraticFactorStep u0 (gBase * (r :: rs).prod)
            (((Polynomial.X ^ 2) * gBase) * rs.prod) :=
        { r := r
          r_dvd_sigma := hr_sigma
          r_dvd_scale := by
            refine ⟨gBase * rs.prod, ?_⟩
            simp [List.prod_cons, mul_left_comm]
          peel_eq := by
            simp [List.prod_cons, mul_assoc, mul_left_comm, mul_comm] }
      have hschedTail :
          PeelingSchedule u u0 (((Polynomial.X ^ 2) * gBase) * rs.prod)
            (peelTerminalScale ((Polynomial.X ^ 2) * gBase) rs) :=
        ih hrs_tail (gBase := (Polynomial.X ^ 2) * gBase)
      exact PeelingSchedule.peel (hstep hfg) hschedTail
end LowRankUnivariateSOS
