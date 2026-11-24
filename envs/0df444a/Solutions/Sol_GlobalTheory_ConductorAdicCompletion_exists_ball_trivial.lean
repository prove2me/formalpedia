-- Prove2me | solution 1 for GlobalTheory.ConductorAdicCompletion.exists_ball_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:58:37.626312+00:00
-- url     : https://prove2.me/submissions/0db33bfa-077e-41cd-b9bc-92ca9b0991d5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsConductorAdicCompletion
import Theorems.Thm_GlobalTheory_ConductorAdicCompletion_eq_one_of_pow_near_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ConductorAdicCompletion
namespace GlobalTheory.ConductorAdicCompletion
theorem _root_.solution {K : Type*} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
    (ψ : AddChar K ℂ) (hc : Continuous ψ) :
    ∃ m : ℤ, ∀ x : K, Valued.v x ≤ WithZero.exp m → ψ x = 1 := by
  have hmem : {x : K | ‖ψ x - 1‖ < 1 / 2} ∈ nhds (0 : K) := by
    apply IsOpen.mem_nhds
    · exact isOpen_lt (by fun_prop) continuous_const
    · simp
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hmem
  set g : WithZero (Multiplicative ℤ) := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hg
  have hg0 : g ≠ 0 := by
    rw [hg]
    exact (map_ne_zero _).mpr γ.ne_zero
  refine ⟨WithZero.log g - 1, fun x hx => ?_⟩
  have hlt : WithZero.exp (WithZero.log g - 1) < g :=
    (WithZero.lt_log_iff_exp_lt hg0).mp (by omega)
  apply eq_one_of_pow_near_one
  intro k
  rw [← AddChar.map_nsmul_eq_pow]
  have hk : Valued.v (k • x) ≤ WithZero.exp (WithZero.log g - 1) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [succ_nsmul]
      exact Valuation.map_add_le _ ih hx
  have : k • x ∈ {x : K | ‖ψ x - 1‖ < 1 / 2} := by
    apply hγ
    exact (Valuation.restrict_lt_iff_lt_embedding _).mpr (hk.trans_lt hlt)
  exact le_of_lt this
end GlobalTheory.ConductorAdicCompletion
