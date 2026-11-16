-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_blk2_filter_eq_entI_filter
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T06:04:25.053494+00:00
-- url     : https://prove2.me/submissions/dfd2e23f-3a1e-4e26-a52b-75a314f68a5f

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_blk2_after_entI_width_ne_484
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd

private abbrev headW484 : Edge 529 → Bool :=
  fun e => decide ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0 = 484)

private noncomputable abbrev blk2_tail (a : ℕ) : List NB.NI :=
  NB.chunkProg (NB.ι2 a) ((toNB ch0O).e2 a) NB.cs2 ++
    (List.range v).flatMap (NB.corrI (toNB ch0O) a)

private theorem filterMap_flatMap_ind {α β γ : Type*} (f : α → List β) (g : β → Option γ) :
    ∀ l : List α,
      (l.flatMap f).filterMap g = l.flatMap fun a => (f a).filterMap g
  | [] => by simp [List.flatMap]
  | a :: as => by
    have ih := filterMap_flatMap_ind f g as
    change ((f a ++ as.flatMap f).filterMap g) =
      (f a).filterMap g ++ as.flatMap fun x => (f x).filterMap g
    rw [List.filterMap_append, ih]

private theorem filter_flatMap_ind {α β : Type*} (f : α → List β) (p : β → Bool) :
    ∀ l : List α, (l.flatMap f).filter p = l.flatMap fun a => (f a).filter p
  | [] => by simp [List.flatMap]
  | a :: as => by
    have ih := filter_flatMap_ind f p as
    change ((f a ++ as.flatMap f).filter p) = (f a).filter p ++ as.flatMap fun x => (f x).filter p
    rw [List.filter_append, ih]

private theorem filter_append_right_nil {α : Type*} (p : α → Bool) (X Y : List α)
    (hY : Y.filter p = []) : (X ++ Y).filter p = X.filter p := by
  rw [List.filter_append, hY, List.append_nil]

private theorem filter_flatMap_append_left {α β : Type*} (X Y : α → List β) (p : β → Bool)
    (l : List α) (hY : ∀ a ∈ l, (Y a).filter p = []) :
    (l.flatMap fun a => X a ++ Y a).filter p = (l.flatMap X).filter p := by
  induction l with
  | nil => simp [List.flatMap]
  | cons a as ih =>
    have hYa : (Y a).filter p = [] := hY a (by simp)
    have hYas : ∀ x ∈ as, (Y x).filter p = [] := fun x hx => hY x (by simp [hx])
    change ((X a ++ Y a) ++ as.flatMap fun x => X x ++ Y x).filter p =
      (X a ++ as.flatMap X).filter p
    rw [List.filter_append, filter_append_right_nil p (X a) (Y a) hYa, ih hYas, List.filter_append]

private theorem mem_flatMap_nil {α β : Type*} {f : α → List β} {l : List α}
    (h : l.flatMap f = []) : ∀ a ∈ l, f a = [] := by
  induction l with
  | nil => intro _ h; cases h
  | cons a as ih =>
    intro x hx
    simp only [List.flatMap_cons, List.append_eq_nil_iff] at h
    rcases h with ⟨ha, has⟩
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ha
    · exact ih has x hx

theorem solution :
    (List.filter headW484
      (((List.range v).flatMap (NB.blk2 (toNB ch0O))).filterMap Instr.edgeOf)) =
    (List.filter headW484
      (((List.range v).flatMap (NB.entI (toNB ch0O))).filterMap Instr.edgeOf)) := by
  have htail_global := net0O2_blk2_after_entI_width_ne_484
  rw [filterMap_flatMap_ind (NB.blk2 (toNB ch0O)) Instr.edgeOf (List.range v)]
  rw [filterMap_flatMap_ind (NB.entI (toNB ch0O)) Instr.edgeOf (List.range v)]
  have hsplit :
      (fun a => (NB.blk2 (toNB ch0O) a).filterMap Instr.edgeOf) =
        fun a =>
          (NB.entI (toNB ch0O) a).filterMap Instr.edgeOf ++
            (blk2_tail a).filterMap Instr.edgeOf := by
    funext a
    change ((NB.entI (toNB ch0O) a ++ blk2_tail a).filterMap Instr.edgeOf) = _
    rw [List.filterMap_append]
  have hY : ∀ a ∈ List.range v,
      ((blk2_tail a).filterMap Instr.edgeOf).filter headW484 = [] := by
    have hfm :
        ((List.range v).flatMap blk2_tail).filterMap Instr.edgeOf =
          (List.range v).flatMap fun a => (blk2_tail a).filterMap Instr.edgeOf :=
      filterMap_flatMap_ind blk2_tail Instr.edgeOf (List.range v)
    have h := htail_global
    change
        (List.filter headW484
          (((List.range v).flatMap blk2_tail).filterMap Instr.edgeOf)) = [] at h
    rw [hfm, filter_flatMap_ind (fun a => (blk2_tail a).filterMap Instr.edgeOf) headW484
      (List.range v)] at h
    exact mem_flatMap_nil h
  rw [hsplit]
  exact filter_flatMap_append_left
    (fun a => (NB.entI (toNB ch0O) a).filterMap Instr.edgeOf)
    (fun a => (blk2_tail a).filterMap Instr.edgeOf)
    headW484 (List.range v) hY
