-- Prove2me | solution 1 for OAI.KervaireRibbon.sameCycle_erase
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T17:57:19.602393+00:00
-- url     : https://prove2.me/submissions/c3543444-7fd4-45fe-ab29-34e43fd36364

import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression

open OAI OAI.KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]
theorem solution (σ : Equiv.Perm D) {x d e : D} (hx : σ x ≠ x)
    (hd : d ≠ x) (he : e ≠ x) :
    (erase σ x).SameCycle d e ↔ σ.SameCycle d e := by
  constructor
  · intro h
    have hle : SameCycle.setoid (erase σ x) ≤ SameCycle.setoid σ := by
      apply cycle_le_of_step
      intro u
      change σ.SameCycle (erase σ x u) u
      by_cases hu : u = x
      · subst hu; rw [erase_fixed]
      · rw [erase_apply σ x u hu]
        split_ifs with h'
        · rw [← h']
          exact (SameCycle.rfl.apply_right.apply_right).symm
        · exact SameCycle.rfl.apply_left
    exact hle h
  · intro h
    have key : ∀ n : ℕ, (σ ^ n) d ≠ x → (erase σ x).SameCycle d ((σ ^ n) d) := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro hn
        rcases n with _ | n
        · rw [pow_zero, Perm.one_apply]
        · rw [pow_succ', Perm.mul_apply] at hn ⊢
          by_cases hu : (σ ^ n) d = x
          · rcases n with _ | m
            · simp at hu; exact absurd hu hd
            · rw [pow_succ', Perm.mul_apply] at hu
              have hw : (σ ^ m) d ≠ x := fun hw => hx (by rw [hw] at hu; exact hu)
              have := ih m (by omega) hw
              have hstep : erase σ x ((σ ^ m) d) = σ ((σ ^ (m + 1)) d) := by
                rw [erase_apply σ x _ hw, if_pos hu, pow_succ', Perm.mul_apply, hu]
              rw [pow_succ', Perm.mul_apply] at hstep ⊢
              rw [← hstep]
              exact this.trans (SameCycle.rfl.apply_right)
          · have := ih n (by omega) hu
            have hstep : erase σ x ((σ ^ n) d) = σ ((σ ^ n) d) := by
              rw [erase_apply σ x _ hu, if_neg hn]
            rw [← hstep]
            exact this.trans (SameCycle.rfl.apply_right)
    obtain ⟨n, _, _, hn⟩ := h.exists_pow_eq σ
    rw [← hn] at he ⊢
    exact key n he
