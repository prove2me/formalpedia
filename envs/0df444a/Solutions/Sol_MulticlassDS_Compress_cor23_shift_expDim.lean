-- Prove2me | solution 1 for MulticlassDS.Compress.cor23_shift_expDim
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T00:11:10.378868+00:00
-- url     : https://prove2.me/submissions/df1f6fbb-a037-45bb-9d54-f37f589f1090

import Mathlib
import Definitions.Def_MulticlassDS_Compress_Shifting

open MulticlassDS.Compress

noncomputable def solE {n p : ℕ} (H : Set (Fin n → Fin p)) (i : Fin n) (v : Fin n → Fin p) :
    Finset (Fin n → Fin p) := by
  classical
  exact Finset.univ.filter (fun u => u ∈ H ∧ AgreeOff i u v)

theorem solE_mem {n p : ℕ} (H : Set (Fin n → Fin p)) (i : Fin n) (v u : Fin n → Fin p) :
    u ∈ solE H i v ↔ u ∈ H ∧ AgreeOff i u v := by
  unfold solE
  simp

theorem solE_ncard {n p : ℕ} (H : Set (Fin n → Fin p)) (i : Fin n) (v : Fin n → Fin p) :
    {u ∈ H | AgreeOff i u v}.ncard = (solE H i v).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext u
  simp [solE_mem]

def solCands {n p k : ℕ} (H : Set (Fin n → Fin p)) (i : Fin n) (S : Fin k → Fin n)
    (x : Fin k → Fin p) : Set (Fin n → Fin p) :=
  {v | v ∈ H ∧ ∀ j, S j ≠ i → v (S j) = x j}

noncomputable def solBest {n p : ℕ} (H : Set (Fin n → Fin p)) (i : Fin n)
    (C : Set (Fin n → Fin p)) : Option (Fin n → Fin p) := by
  classical
  exact if h : ∃ v ∈ C, ∀ u ∈ C, (solE H i u).card ≤ (solE H i v).card then some h.choose
    else none

theorem solBest_spec {n p : ℕ} (H : Set (Fin n → Fin p)) (i : Fin n)
    (C : Set (Fin n → Fin p)) (hne : C.Nonempty) :
    ∃ b, solBest H i C = some b ∧ b ∈ C ∧ ∀ u ∈ C, (solE H i u).card ≤ (solE H i b).card := by
  have h : ∃ v ∈ C, ∀ u ∈ C, (solE H i u).card ≤ (solE H i v).card :=
    Set.exists_max_image C (fun u => (solE H i u).card) (Set.toFinite C) hne
  refine ⟨h.choose, ?_, h.choose_spec.1, h.choose_spec.2⟩
  unfold solBest
  rw [dif_pos h]

noncomputable def solF {n p k : ℕ} (H : Set (Fin n → Fin p)) (i : Fin n) (S : Fin k → Fin n)
    (j0 : Fin k) (x : Fin k → Fin p) : Fin k → Fin p :=
  match solBest H i (solCands H i S x) with
  | none => x
  | some b => if ht : (x j0 : ℕ) < (solE H i b).card then
      (((solE H i b).equivFin.symm ⟨x j0, ht⟩).1) ∘ S else x

theorem solF_eq {n p k : ℕ} (H : Set (Fin n → Fin p)) (i : Fin n) (S : Fin k → Fin n)
    (j0 : Fin k) (x : Fin k → Fin p) (b : Fin n → Fin p)
    (hb : solBest H i (solCands H i S x) = some b) (ht : (x j0 : ℕ) < (solE H i b).card) :
    solF H i S j0 x = (((solE H i b).equivFin.symm ⟨x j0, ht⟩).1) ∘ S := by
  unfold solF
  rw [hb]
  dsimp only
  rw [dif_pos ht]

theorem sol_claim22 {n p : ℕ} (H : Set (Fin n → Fin p)) (i : Fin n) (k : ℕ)
    (S : Fin k → Fin n) :
    (proj (shift i H) S).encard ≤ (proj H S).encard := by
  classical
  by_cases hi : ∃ j0, S j0 = i
  swap
  · push_neg at hi
    apply Set.encard_le_encard
    rintro x ⟨g, ⟨v, hv, hag, -⟩, hgx⟩
    refine ⟨v, hv, ?_⟩
    rw [← hgx]
    funext j
    exact (hag (S j) (hi j)).symm
  obtain ⟨j0, hj0⟩ := hi
  have hstruct : ∀ x ∈ proj (shift i H) S, (∀ j, S j = i → x j = x j0) ∧
      ∃ b, solBest H i (solCands H i S x) = some b ∧ b ∈ solCands H i S x ∧
        (x j0 : ℕ) < (solE H i b).card := by
    rintro x ⟨g, ⟨v, hv, hag, hlt⟩, hgx⟩
    have hx : ∀ j, x j = g (S j) := fun j => by rw [← hgx]; rfl
    refine ⟨fun j hj => by rw [hx j, hx j0, hj, hj0], ?_⟩
    have hvC : v ∈ solCands H i S x := ⟨hv, fun j hj => by rw [hx j]; exact (hag (S j) hj).symm⟩
    obtain ⟨b, hb, hbC, hmax⟩ := solBest_spec H i (solCands H i S x) ⟨v, hvC⟩
    refine ⟨b, hb, hbC, ?_⟩
    rw [solE_ncard] at hlt
    have := hmax v hvC
    rw [hx j0, hj0]
    omega
  apply Set.encard_le_encard_of_injOn (f := solF H i S j0)
  · intro x hx
    obtain ⟨-, b, hb, -, ht⟩ := hstruct x hx
    rw [solF_eq H i S j0 x b hb ht]
    exact ⟨_, ((solE_mem H i b _).mp ((solE H i b).equivFin.symm ⟨x j0, ht⟩).2).1, rfl⟩
  · intro x hx y hy hxy
    obtain ⟨hxi, bx, hbx, hbxC, htx⟩ := hstruct x hx
    obtain ⟨hyi, b2, hby, hbyC, hty⟩ := hstruct y hy
    rw [solF_eq H i S j0 x bx hbx htx, solF_eq H i S j0 y b2 hby hty] at hxy
    set ex := (solE H i bx).equivFin.symm ⟨x j0, htx⟩ with hex
    set ey := (solE H i b2).equivFin.symm ⟨y j0, hty⟩ with hey
    have hexm := (solE_mem H i bx _).mp ex.2
    have heym := (solE_mem H i b2 _).mp ey.2
    have hoff : ∀ j, S j ≠ i → x j = y j := by
      intro j hj
      have h1 := congrFun hxy j
      simp only [Function.comp] at h1
      rw [← hbxC.2 j hj, ← hbyC.2 j hj, ← hexm.2 (S j) hj, ← heym.2 (S j) hj]
      exact h1
    have hC : solCands H i S x = solCands H i S y := by
      ext v
      simp only [solCands, Set.mem_setOf_eq]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun j hj => (h2 j hj).trans (hoff j hj)⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun j hj => (h2 j hj).trans (hoff j hj).symm⟩
    rw [hC, hby] at hbx
    obtain rfl : b2 = bx := Option.some.inj hbx
    have hi_eq : ex.1 i = ey.1 i := by
      have h1 := congrFun hxy j0
      simp only [Function.comp, hj0] at h1
      exact h1
    have hfun : ex.1 = ey.1 := by
      funext m
      by_cases hm : m = i
      · rw [hm]; exact hi_eq
      · rw [hexm.2 m hm, heym.2 m hm]
    have hsub : ex = ey := Subtype.ext hfun
    have hfin := (solE H i b2).equivFin.symm.injective hsub
    have hval : ((x j0 : ℕ)) = y j0 := Fin.mk.inj_iff.mp hfin
    have hj : x j0 = y j0 := Fin.ext hval
    funext j
    by_cases hSj : S j = i
    · rw [hxi j hSj, hyi j hSj, hj]
    · exact hoff j hSj

theorem solution {n p : ℕ} (H : Set (Fin n → Fin p)) (i : Fin n) :
    expDim (shift i H) ≤ expDim H := by
  unfold expDim
  refine iSup_le fun k => iSup_le fun S => iSup_le fun hk => ?_
  exact le_iSup_of_le k (le_iSup_of_le S
    (le_iSup_of_le (hk.trans (sol_claim22 H i k S)) le_rfl))
