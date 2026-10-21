-- Prove2me | solution 1 for IntMul.Kappa.jain_round7_framework
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-20T23:25:17.590762+00:00
-- url     : https://prove2.me/submissions/ef3b107a-9a1a-4d86-9481-bf7a1439a5c1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_MultitapeModel
import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_KappaJainData
import Definitions.Def_IntMul_Kappa_RG_Defs
import Theorems.Thm_IntMul_Kappa_R6_kappa_finalG_at
import Theorems.Thm_IntMul_Kappa_R6_IL3H_p14NeedG_all
import Theorems.Thm_IntMul_Kappa_R6_rG_normalize
import Theorems.Thm_IntMul_Kappa_R6_rat_eps
import Theorems.Thm_IntMul_Kappa_R6_setupNeed6
import Theorems.Thm_IntMul_Kappa_R6_crtNeed6
import Theorems.Thm_IntMul_Kappa_R6_Leaf_fineNeed6_all
import Theorems.Thm_IntMul_Kappa_R6_Leaf_lineNeed6_all
import Theorems.Thm_IntMul_Kappa_R6_Leaf_p18IL6_all
import Theorems.Thm_IntMul_Kappa_R6_Bit_bitNetR7_mom
import Theorems.Thm_IntMul_Kappa_R6_Cx_cxNetR6G

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# Jain's round seven from the parametric round-six machine

Round seven keeps the round-six complex network (`Jain.cxR6`, proved as `Cx.cxNetR6G`) and
replaces the bit network by the round-seven one (`Jain.bitR7`, `108516254` roles, width `529`).
The parametric assembly `kappa_finalG_at` turns the crude-guard assembly into `KappaBound κ`.
-/

namespace IntMul.Kappa.R7Sk

open IntMul.Kappa IntMul.Kappa.R6

theorem histMomentR7_nonneg (h : List (ℕ × ℕ)) (m : ℕ) (τ : ℝ) : 0 ≤ histMoment h m τ := by
  unfold histMoment
  apply List.sum_nonneg
  intro y hy
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hy
  positivity

theorem histMomentR7_append (h₁ h₂ : List (ℕ × ℕ)) (m : ℕ) (τ : ℝ) :
    histMoment (h₁ ++ h₂) m τ = histMoment h₁ m τ + histMoment h₂ m τ := by
  unfold histMoment; simp [List.map_append, List.sum_append]

/-- For a nonpositive exponent, a term with `0 < w ≤ m` is at least `n_w`. -/
theorem termR7_ge (w n m : ℕ) (τ : ℝ) (hw : 0 < w) (hwm : w ≤ m) (hτ : τ ≤ 0) :
    (n : ℝ) ≤ (n : ℝ) * ((w : ℝ) / m) ^ τ := by
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  have hm' : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le hw hwm)
  have h1 : ((w : ℝ) / m) ≤ 1 := by
    rw [div_le_one hm']; exact_mod_cast hwm
  have := Real.one_le_rpow_of_pos_of_le_one_of_nonpos (div_pos hw' hm') h1 hτ
  have hn : (0 : ℝ) ≤ n := by positivity
  nlinarith

theorem bitR7_tau_pos (τ : ℝ) (h : histMoment Jain.bitR7 529 τ < 108516254) : 0 < τ := by
  by_contra hτ
  push Not at hτ
  have e : Jain.bitR7 = [(1, 1690297301)] ++ Jain.bitR7.tail := rfl
  rw [e, histMomentR7_append] at h
  have h2 := histMomentR7_nonneg Jain.bitR7.tail 529 τ
  have h1 := termR7_ge 1 1690297301 529 τ (by norm_num) (by norm_num) hτ
  simp only [histMoment, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero] at h h2
  push_cast at h1 h
  linarith

theorem cxR6_sigma_posR7 (σ : ℝ) (h : histMoment Jain.cxR6 576 σ < 207387136) : 0 < σ := by
  by_contra hσ
  push Not at hσ
  have e : Jain.cxR6 = [(1, 184811440), (2, 107199136)] ++ Jain.cxR6.tail.tail := rfl
  rw [e, histMomentR7_append] at h
  have h3 := histMomentR7_nonneg Jain.cxR6.tail.tail 576 σ
  have h1 := termR7_ge 1 184811440 576 σ (by norm_num) (by norm_num) hσ
  have h2 := termR7_ge 2 107199136 576 σ (by norm_num) (by norm_num) hσ
  simp only [histMoment, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero] at h h3
  push_cast at h1 h2 h
  linarith

theorem cxR6_boundsR7 : ∀ p ∈ Jain.cxR6, 1 ≤ p.1 ∧ p.1 ≤ 552 := by
  intro p hp
  simp only [Jain.cxR6, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

set_option exponentiation.threshold 2000 in
theorem cxR6_numR7 : 2 * ((Jain.cxR6.map Prod.snd).sum * 1105 ^ 600) ≤ 1152 ^ 600 := by
  norm_num [Jain.cxR6]

theorem cxR6_momR7 (e : ℕ) (he : 600 ≤ e) :
    2 * ((Jain.cxR6.map Prod.snd).sum * (2 * 552 + 1) ^ e) ≤ (2 * 576) ^ e := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le he
  rw [pow_add, pow_add]
  have a : 1105 ^ k ≤ 1152 ^ k := Nat.pow_le_pow_left (by norm_num) k
  calc 2 * ((Jain.cxR6.map Prod.snd).sum * (1105 ^ 600 * 1105 ^ k))
      = (2 * ((Jain.cxR6.map Prod.snd).sum * 1105 ^ 600)) * 1105 ^ k := by ring
    _ ≤ 1152 ^ 600 * 1152 ^ k := Nat.mul_le_mul cxR6_numR7 a

theorem cxR6_rankR7 : 8 ≤ histRankSum Jain.cxR6 := by
  norm_num [histRankSum, Jain.cxR6]

theorem cxR6_p0R7 : ((600 : ℕ) : ℝ) ≤ 2 + (576 : ℕ) * Real.log (histRankSum Jain.cxR6) := by
  have hR8 : (8 : ℝ) ≤ (histRankSum Jain.cxR6 : ℝ) := by exact_mod_cast cxR6_rankR7
  have hl8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have hl2 := Real.log_two_gt_d9
  have hlog : Real.log 8 ≤ Real.log (histRankSum Jain.cxR6) := Real.log_le_log (by norm_num) hR8
  push_cast
  linarith

theorem round7_sol_aux (ab ac ε x C₁ κ : ℝ) (hab : 0 ≤ ab) (hac : 0 ≤ ac)
    (hbit : histMoment Jain.bitR7 529 (1 - ab) < 108516254)
    (hcx : histMoment Jain.cxR6 576 (1 - ac) < 207387136)
    (hasm : CrudeAssembly ab ac (1 / 1000) ε x C₁ κ 576 (histRankSum Jain.cxR6)) :
    KappaBound κ := by
  have hτ : 0 < 1 - ab := bitR7_tau_pos _ hbit
  have hσ : 0 < 1 - ac := cxR6_sigma_posR7 _ hcx
  obtain ⟨P, hP, hκ, hPτ, hPσ, hC1⟩ :=
    rG_normalize 576 (histRankSum Jain.cxR6) ab ac ε x C₁ κ hτ hσ hab hac hasm
  obtain ⟨q, hP', hκ'⟩ := rat_eps P hP κ hκ
  have hJb : histMoment Jain.bitR7 529 ({ P with ε := (q : ℝ) } : Prm).τ < 108516254 := by
    show histMoment Jain.bitR7 529 P.τ < 108516254
    rw [hPτ]; exact hbit
  have hJc : histMoment Jain.cxR6 576 ({ P with ε := (q : ℝ) } : Prm).σ < 207387136 := by
    show histMoment Jain.cxR6 576 P.σ < 207387136
    rw [hPσ]; exact hcx
  have hC1' : 2 + (576 : ℕ) * Real.log (histRankSum Jain.cxR6) ≤
      (({ P with ε := (q : ℝ) } : Prm).C1 : ℝ) := hC1
  exact kappa_finalG_at 108516254 529 207387136 576 Jain.bitR7 Jain.cxR6 (by norm_num)
    _ hP' ⟨q, rfl⟩ κ hκ' (setupNeed6 _ hP') (crtNeed6 _ hP') (Leaf.fineNeed6_all _ hP')
    (Leaf.lineNeed6_all _ hP')
    (IL3H.p14NeedG_all 207387136 576 552 600 Jain.cxR6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) cxR6_boundsR7 cxR6_momR7 cxR6_p0R7 (by norm_num) _ hP')
    (Leaf.p18IL6_all _ hP') (by exact_mod_cast hJb) (by exact_mod_cast hJc) hC1'
    Bit.bitNetR7_mom Cx.cxNetR6G

end IntMul.Kappa.R7Sk

theorem solution : type_of% @IntMul.Kappa.R7Sk.round7_sol_aux := @IntMul.Kappa.R7Sk.round7_sol_aux
