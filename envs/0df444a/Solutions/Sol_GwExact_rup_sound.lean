-- Prove2me | solution 1 for GwExact.rup_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:20:01.355726+00:00
-- url     : https://prove2.me/submissions/5d511ebb-5aa5-485f-8c52-c00052a4d8b2

module
public import Definitions.Def_GwExact_Check
public import Theorems.Thm_GwExact_eq_of_land_pred
public import Theorems.Thm_GwExact_testBit_rem
public import Theorems.Thm_GwExact_beq_false
public import Theorems.Thm_GwExact_beq_true

set_option autoImplicit true
@[expose] public section
public section
open GwExact
namespace GwExact
theorem _root_.solution {σ : Nat → Bool} {src : Nat → Option Cls} {w wm : Nat}
    (hsrc : ∀ h c, src h = some c → c.Holds σ) :
    ∀ cnt code t f, rup src w wm cnt code t f = true →
      (∀ v, t.testBit v = true → σ v = true) → (∀ v, f.testBit v = true → σ v = false) → False := by
  intro cnt
  induction cnt with
  | zero => intro code t f h; simp [rup] at h
  | succ cnt ih =>
    intro code t f h ht hf
    simp only [rup] at h
    split at h
    · simp at h
    · rename_i cl hcl
      obtain ⟨v, hv⟩ := hsrc _ _ hcl
      have hrp : ∀ u, (Nat.xor cl.p (Nat.land cl.p f)).testBit u = (cl.p.testBit u && !f.testBit u) :=
        fun u => testBit_rem _ _ u
      have hrn : ∀ u, (Nat.xor cl.n (Nat.land cl.n t)).testBit u = (cl.n.testBit u && !t.testBit u) :=
        fun u => testBit_rem _ _ u
      -- the true literal of the hint clause is not falsified
      have hlive : (Nat.xor cl.p (Nat.land cl.p f)).testBit v = true ∨
          (Nat.xor cl.n (Nat.land cl.n t)).testBit v = true := by
        rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left; rw [hrp, h1]
          cases hfv : f.testBit v
          · rfl
          · have := hf v hfv; rw [h2] at this; exact absurd this (by simp)
        · right; rw [hrn, h1]
          cases htv : t.testBit v
          · rfl
          · have := ht v htv; rw [h2] at this; exact absurd this (by simp)
      generalize hRP : Nat.xor cl.p (Nat.land cl.p f) = rp at h hrp hlive
      generalize hRN : Nat.xor cl.n (Nat.land cl.n t) = rn at h hrn hlive
      by_cases hp0 : rp = 0
      · subst hp0
        have hlive' : rn.testBit v = true := by simpa using hlive
        by_cases hn0 : rn = 0
        · subst hn0; simp at hlive'
        · have hb : Nat.beq rn 0 = false := beq_false hn0
          simp only [Nat.beq_refl, Bool.cond_true, hb, Bool.cond_false] at h
          by_cases hpow : Nat.land rn (rn - 1) = 0
          · have hb2 : Nat.beq (Nat.land rn (Nat.sub rn 1)) 0 = true := beq_true hpow
            rw [hb2, Bool.cond_true] at h
            refine ih _ _ _ h ht ?_
            intro u hu
            have hu' : (f ||| rn).testBit u = true := hu
            rw [Nat.testBit_or] at hu'
            rcases Bool.or_eq_true_iff.mp hu' with hu1 | hu1
            · exact hf u hu1
            · have := eq_of_land_pred rn hpow u v hu1 hlive'
              subst this
              have := (hrn u).symm.trans hu1
              rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · -- v is a positive literal of cl; rp = 0 forces f v
                exfalso
                have hz : (0 : Nat).testBit u = (cl.p.testBit u && !f.testBit u) := hrp u
                rw [h1] at hz
                cases hfu : f.testBit u
                · rw [hfu] at hz; simp at hz
                · have := hf u hfu; rw [h2] at this; exact absurd this (by simp)
              · exact h2
          · have hb2 : Nat.beq (Nat.land rn (Nat.sub rn 1)) 0 = false := beq_false hpow
            rw [hb2, Bool.cond_false] at h
            simp at h
      · have hb : Nat.beq rp 0 = false := beq_false hp0
        simp only [hb, Bool.cond_false] at h
        by_cases hn0 : rn = 0
        · subst hn0
          have hlive' : rp.testBit v = true := by simpa using hlive
          by_cases hpow : Nat.land rp (rp - 1) = 0
          · have hb2 : (Nat.beq 0 0 && Nat.beq (Nat.land rp (Nat.sub rp 1)) 0) = true := by
              rw [Nat.beq_refl, show Nat.beq (Nat.land rp (Nat.sub rp 1)) 0 = true from beq_true hpow]; rfl
            rw [hb2, Bool.cond_true] at h
            refine ih _ _ _ h ?_ hf
            intro u hu
            have hu' : (t ||| rp).testBit u = true := hu
            rw [Nat.testBit_or] at hu'
            rcases Bool.or_eq_true_iff.mp hu' with hu1 | hu1
            · exact ht u hu1
            · have := eq_of_land_pred rp hpow u v hu1 hlive'
              subst this
              rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · exact h2
              · exfalso
                have hz : (0 : Nat).testBit u = (cl.n.testBit u && !t.testBit u) := hrn u
                rw [h1] at hz
                cases htu : t.testBit u
                · rw [htu] at hz; simp at hz
                · have := ht u htu; rw [h2] at this; exact absurd this (by simp)
          · have hb2 : (Nat.beq 0 0 && Nat.beq (Nat.land rp (Nat.sub rp 1)) 0) = false := by
              rw [Nat.beq_refl, show Nat.beq (Nat.land rp (Nat.sub rp 1)) 0 = false from beq_false hpow]; rfl
            rw [hb2, Bool.cond_false] at h
            simp at h
        · have hb2 : Nat.beq rn 0 = false := beq_false hn0
          rw [hb2, Bool.false_and, Bool.cond_false] at h
          simp at h
end GwExact
