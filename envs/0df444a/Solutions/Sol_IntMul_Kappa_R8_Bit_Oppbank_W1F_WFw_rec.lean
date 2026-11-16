-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.W1F_WFw_rec
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T07:53:07.898785+00:00
-- url     : https://prove2.me/submissions/c1f2aad6-b72d-4305-b44c-40d0a77b4c71

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRec
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_W1F_wires_lt_NL_rec
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open IntMul.Kappa.R8.Bit.Oppbank.NB
open IntMul.Kappa.R8.Bit.Oppbank

/-- `mk c el` puts both endpoints of every XOR pair into the touched-wire list. -/
private theorem mk_gates_touch (c : ℕ) (el : List (ℕ × ℕ)) :
    ∀ p ∈ (mk c el).2.2, p.1 ∈ (mk c el).2.1 ∧ p.2 ∈ (mk c el).2.1 := by
  intro p hp
  dsimp [mk, touch] at hp ⊢
  refine ⟨List.mem_flatMap.2 ⟨p, hp, ?_⟩, List.mem_flatMap.2 ⟨p, hp, ?_⟩⟩
  · simp
  · simp

private theorem wf_map_mk {α : Type*} (L : List α) (code : α → ℕ) (el : α → List (ℕ × ℕ)) :
    ∀ i ∈ L.map (fun x => mk (code x) (el x)),
      ∀ p ∈ i.2.2, p.1 ∈ i.2.1 ∧ p.2 ∈ i.2.1 := by
  intro i hi p hp
  obtain ⟨x, _, rfl⟩ := List.mem_map.1 hi
  exact mk_gates_touch (code x) (el x) p hp

private theorem wf_append {W W' : List LInstr}
    (hW : ∀ i ∈ W, ∀ p ∈ i.2.2, p.1 ∈ i.2.1 ∧ p.2 ∈ i.2.1)
    (hW' : ∀ i ∈ W', ∀ p ∈ i.2.2, p.1 ∈ i.2.1 ∧ p.2 ∈ i.2.1) :
    ∀ i ∈ W ++ W', ∀ p ∈ i.2.2, p.1 ∈ i.2.1 ∧ p.2 ∈ i.2.1 := by
  intro i hi p hp
  rcases List.mem_append.1 hi with h | h
  · exact hW i h p hp
  · exact hW' i h p hp

private theorem wf_sweep {a n f : ℕ} :
    ∀ i ∈ sweepR a (a + n) f, ∀ p ∈ i.2.2, p.1 ∈ i.2.1 ∧ p.2 ∈ i.2.1 := by
  intro i hi p hp
  simp only [sweepR, List.mem_map] at hi
  obtain ⟨q, _, rfl⟩ := hi
  cases hp

/-- `sweepR a b f` with `a ≤ b` is `sweepR a (a + (b - a)) f`. -/
private theorem sweepR_eq {a b f : ℕ} (h : a ≤ b) :
    sweepR a b f = sweepR a (a + (b - a)) f := by
  simp [sweepR, Nat.add_sub_cancel' h]

private theorem wf_sweep_le {a b f : ℕ} (h : a ≤ b) :
    ∀ i ∈ sweepR a b f, ∀ p ∈ i.2.2, p.1 ∈ i.2.1 ∧ p.2 ∈ i.2.1 := by
  intro i hi
  have := wf_sweep (a := a) (n := b - a) (f := f)
  rw [← sweepR_eq h] at this
  exact this i hi

private theorem wf_mixF (code : ℕ → ℕ) :
    ∀ i ∈ mixF code, ∀ p ∈ i.2.2, p.1 ∈ i.2.1 ∧ p.2 ∈ i.2.1 :=
  wf_map_mk recs (fun r => code r.1) recEl

private theorem wf_mixI (code : ℕ → ℕ) :
    ∀ i ∈ mixI code, ∀ p ∈ i.2.2, p.1 ∈ i.2.1 ∧ p.2 ∈ i.2.1 :=
  wf_map_mk recs.reverse (fun r => code r.1) (fun r => (recEl r).reverse)

private theorem wf_mixFB (a b : ℕ) (code : ℕ → ℕ) :
    ∀ i ∈ mixFB a b code, ∀ p ∈ i.2.2, p.1 ∈ i.2.1 ∧ p.2 ∈ i.2.1 :=
  wf_map_mk (blkRecs a b) (fun r => code r.1) recEl

private theorem wf_scat (rd : ℕ → ℕ) (code : ℕ → ℕ) :
    ∀ i ∈ scat rd code, ∀ p ∈ i.2.2, p.1 ∈ i.2.1 ∧ p.2 ∈ i.2.1 :=
  wf_map_mk (List.range v) code (fun T => scatEl rd T)

private theorem wf_injo (code : ℕ → ℕ) :
    ∀ i ∈ injo code, ∀ p ∈ i.2.2, p.1 ∈ i.2.1 ∧ p.2 ∈ i.2.1 :=
  wf_map_mk (List.range v) code (fun T => [0, 1, 2].map fun k => (wY T, wS (injS T k)))

private theorem wf_copyo (code : ℕ → ℕ) :
    ∀ i ∈ copyo code, ∀ p ∈ i.2.2, p.1 ∈ i.2.1 ∧ p.2 ∈ i.2.1 :=
  wf_map_mk (List.range v) code (fun t => [(wS (srcS t), wX t)])

private theorem wf_tcopy :
    ∀ i ∈ tcopy, ∀ p ∈ i.2.2, p.1 ∈ i.2.1 ∧ p.2 ∈ i.2.1 :=
  wf_map_mk (List.range 23) (fun c => cND (retN c)) (fun c => [(wT c, wS (retS c))])

private theorem wf_scatT :
    ∀ i ∈ scatT, ∀ p ∈ i.2.2, p.1 ∈ i.2.1 ∧ p.2 ∈ i.2.1 :=
  wf_append wf_tcopy (wf_scat wT (fun _ => cLOW))

private theorem W1F_gates_touch :
    ∀ i ∈ W1F, ∀ p ∈ i.2.2, p.1 ∈ i.2.1 ∧ p.2 ∈ i.2.1 := by
  unfold W1F
  repeat apply wf_append
  · exact wf_mixF _
  · exact wf_scat _ _
  · exact wf_injo _
  · exact wf_mixI _
  · exact wf_copyo _
  · exact wf_mixFB _ _ _
  · exact wf_mixFB _ _ _
  · exact wf_mixFB _ _ _
  · exact wf_mixFB _ _ _
  · exact wf_mixFB _ _ _
  · exact wf_mixFB _ _ _
  · exact wf_mixFB _ _ _
  · exact wf_scatT
  · exact wf_injo _
  · exact wf_sweep_le (by decide)
  · exact wf_sweep_le (by decide)
  · exact wf_mixI _
  · exact wf_copyo _

theorem solution :
    ∀ i ∈ W1F,
      (∀ w ∈ i.2.1, w < NL) ∧ ∀ p ∈ i.2.2, p.1 ∈ i.2.1 ∧ p.2 ∈ i.2.1 := by
  intro i hi
  refine ⟨?_, W1F_gates_touch i hi⟩
  intro w hw
  exact net0O2_W1F_wires_lt_NL_rec w ⟨i, hi, Or.inl hw⟩
