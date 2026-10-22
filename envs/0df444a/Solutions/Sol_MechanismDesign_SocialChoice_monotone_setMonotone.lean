-- Prove2me | solution 1 for MechanismDesign.SocialChoice.monotone_setMonotone
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:23:40.108359+00:00
-- url     : https://prove2.me/submissions/d9eb0fa5-96b4-4cd0-b049-70e3def9ad8c

import Mathlib
import Definitions.Def_MechanismDesign_SocialChoice_Model

set_option autoImplicit false
open MechanismDesign.SocialChoice

/-- a linear preference from an injective ranking key -/
def prefOfKey {A : Type*} (key : A → ℕ) (hinj : Function.Injective key) : LinPref A where
  rel p q := key p ≤ key q
  total p q := le_total _ _
  trans p q r h1 h2 := le_trans h1 h2
  antisymm p q h1 h2 := hinj (le_antisymm h1 h2)

/-- ranking key: `x` first, `y` second, the rest ordered by `e` -/
def rkey {A : Type*} [DecidableEq A] (e : A → ℕ) (x y p : A) : ℕ :=
  if p = x then 0 else if p = y then 1 else 2 + e p

theorem rkey_inj {A : Type*} [DecidableEq A] (e : A → ℕ) (he : Function.Injective e) (x y : A)
    (hxy : x ≠ y) : Function.Injective (rkey e x y) := by
  intro p q h
  unfold rkey at h
  split_ifs at h with h1 h2 h3 h4 h5 h6 h7 h8 <;> first
    | omega
    | (subst_vars; rfl)
    | (exact absurd (h1.symm.trans h3) (by tauto))
    | (exact he (by omega))
    | skip

theorem solution {ι A : Type*} [Fintype ι] [Fintype A]
    (f : DirectMechanism ι A) (hf : IsMonotone f) : IsSetMonotone f := by
  classical
  intro R R' B hB hagree
  by_contra hc
  obtain ⟨a, ha⟩ : ∃ a, f R = a := ⟨_, rfl⟩
  obtain ⟨c, hc'⟩ : ∃ c, f R' = c := ⟨_, rfl⟩
  rw [hc'] at hc
  rw [ha] at hB
  have hac : a ≠ c := fun h => hc (h ▸ hB)
  let e : A → ℕ := fun p => (Fintype.equivFin A p : ℕ)
  have he : Function.Injective e := fun p q h => (Fintype.equivFin A).injective (Fin.ext h)
  let R'' : ι → LinPref A := fun i =>
    if (R i).rel a c then prefOfKey (rkey e a c) (rkey_inj e he a c hac)
    else prefOfKey (rkey e c a) (rkey_inj e he c a hac.symm)
  have h1 : f R'' = a := by
    refine hf R R'' a ha ?_
    intro i b hb
    by_cases h : (R i).rel a c
    · simp only [R'', if_pos h]
      show rkey e a c a ≤ rkey e a c b
      simp [rkey]
    · simp only [R'', if_neg h]
      show rkey e c a a ≤ rkey e c a b
      by_cases hbc : b = c
      · subst hbc; exact absurd hb h
      · unfold rkey
        simp only [hac, hbc, if_false, if_true]
        split_ifs <;> omega
  have h2 : f R'' = c := by
    refine hf R' R'' c hc' ?_
    intro i b hb
    have hiff : (R' i).rel a c ↔ (R i).rel a c := hagree i a c (Or.inr hc)
    by_cases h : (R i).rel a c
    · simp only [R'', if_pos h]
      show rkey e a c c ≤ rkey e a c b
      have hba : b ≠ a := by
        rintro rfl
        exact hac ((R' i).antisymm _ _ (hiff.2 h) hb)
      unfold rkey
      simp only [hac.symm, if_false, if_true, hba]
      split_ifs <;> omega
    · simp only [R'', if_neg h]
      show rkey e c a c ≤ rkey e c a b
      simp [rkey]
  exact hac (h1.symm.trans h2)
