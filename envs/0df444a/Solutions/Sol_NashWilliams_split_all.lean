-- Prove2me | solution 1 for NashWilliams.split_all
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:33:24.463856+00:00
-- url     : https://prove2.me/submissions/c167b7b7-c41f-4531-963f-b9bd28e3b735

module
public import Definitions.Def_NashWilliamsLib_Mader
public import Definitions.Def_NashWilliamsLib_Splitting
public import Definitions.Def_NashWilliamsLib_Orientation
public import Theorems.Thm_NashWilliams_lv_split
public import Theorems.Thm_NashWilliams_lv_split_eq
public import Theorems.Thm_NashWilliams_outCutF_split
public import Theorems.Thm_NashWilliams_mem_erase_of_joins
public import Theorems.Thm_NashWilliams_cr_singleton_of_joins
public import Theorems.Thm_NashWilliams_cutF_split
public import Theorems.Thm_NashWilliams_exists_split


set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]
omit [DecidableEq ι]
namespace NashWilliams
theorem _root_.solution {K : ℕ} (hK : 2 ≤ K) {T : Finset V} {s : V} :
    ∀ (m : ℕ) (ends : ι → V × V) (F : Finset ι), Inside T ends F → Req K (T.erase s) ends F →
      cutF ends F {s} = 2 * m →
      ∃ (ends' : ι → V × V) (F' : Finset ι), F'.card + m = F.card ∧ Inside T ends' F' ∧
        Req K (T.erase s) ends' F' ∧ cutF ends' F' {s} = 0 ∧
        ∀ o' : ι → Bool, ∃ o : ι → Bool, (∀ S, outCutF ends' o' F' S ≤ outCutF ends o F S) ∧
          m ≤ outCutF ends o F {s} ∧ m ≤ outCutF ends o F (T.erase s) := by
  classical
  intro m
  induction m with
  | zero =>
    intro ends F hin hreq hcut
    exact ⟨ends, F, by simp, hin, hreq, by simpa using hcut,
      fun o' => ⟨o', fun S => le_rfl, Nat.zero_le _, Nat.zero_le _⟩⟩
  | succ m ih =>
    intro ends F hin hreq hcut
    obtain ⟨i, hi, j, hj, u, v, hij, hJi, hJj, hreq1⟩ :=
      exists_split hK hin hreq ⟨m + 1, by omega⟩ (by omega)
    have huT := mem_erase_of_joins hin hi hJi
    have hvT := mem_erase_of_joins hin hj hJj
    have hin1 : Inside T (Function.update ends i (u, v)) (F.erase j) := by
      intro l hl
      by_cases hli : l = i
      · subst hli
        simp only [Function.update_self]
        exact ⟨mem_of_mem_erase huT, mem_of_mem_erase hvT⟩
      · rw [Function.update_of_ne hli]
        exact hin l (mem_of_mem_erase hl)
    have hcut1 : cutF (Function.update ends i (u, v)) (F.erase j) {s} = 2 * m := by
      have e := cutF_split hi hj hij u v {s} (ends := ends)
      rw [cr_singleton_of_joins hJi, cr_singleton_of_joins hJj] at e
      have hu : u ≠ s := (mem_erase.1 huT).1
      have hv : v ≠ s := (mem_erase.1 hvT).1
      simp [cr, hu, hv] at e
      omega
    obtain ⟨ends', F', hcard, hin', hreq', hcut', htrans⟩ := ih _ _ hin1 hreq1 hcut1
    refine ⟨ends', F', ?_, hin', hreq', hcut', fun o' => ?_⟩
    · have := card_erase_of_mem hj
      have := card_pos.2 ⟨j, hj⟩
      omega
    obtain ⟨o1, ha, hb1, hb2⟩ := htrans o'
    have hli : liftO s ends o1 i j i = if (ends i).2 = s then o1 i else !o1 i := by
      simp [liftO]
    have hlj : liftO s ends o1 i j j = if (ends j).1 = s then o1 i else !o1 i := by
      simp [liftO, Ne.symm hij]
    refine ⟨liftO s ends o1 i j, fun S => ?_, ?_, ?_⟩
    · have e := outCutF_split (s := s) (u := u) (v := v) (ends := ends) hi hj hij o1 S
      have := lv_split hJi hJj (o1 i) S
      rw [hli, hlj] at e
      have := ha S
      omega
    · have e := outCutF_split (s := s) (u := u) (v := v) (ends := ends) hi hj hij o1 {s}
      have := lv_split_eq hJi hJj (o1 i) (X := {s})
        (Or.inl ⟨mem_singleton_self s, by simpa using (mem_erase.1 huT).1,
          by simpa using (mem_erase.1 hvT).1⟩)
      rw [hli, hlj] at e
      omega
    · have e := outCutF_split (s := s) (u := u) (v := v) (ends := ends) hi hj hij o1 (T.erase s)
      have := lv_split_eq hJi hJj (o1 i) (X := T.erase s)
        (Or.inr ⟨by simp, huT, hvT⟩)
      rw [hli, hlj] at e
      omega
end NashWilliams
