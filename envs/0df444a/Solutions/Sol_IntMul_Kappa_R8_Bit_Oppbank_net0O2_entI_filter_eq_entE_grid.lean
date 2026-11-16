-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_entI_filter_eq_entE_grid
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T06:07:10.777847+00:00
-- url     : https://prove2.me/submissions/e6acda3d-3383-438f-9b60-2160c105df89
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_entE_width484
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_ei_PE
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_pickE_oneRun_headW
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix

private abbrev headW484 : Edge 529 → Bool :=
  fun e => decide ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0 = 484)

private theorem filterMap_map_edge (ι : ℕ → NB.Wr) (E : ℕ → Edge 529) :
    ∀ l : List ℕ,
      (l.map fun w => (Instr.edge (ι w) (E w) : Instr NB.Wr (ZMod 2) 529)).filterMap
          Instr.edgeOf =
        l.map E
  | [] => by simp
  | w :: ws => by
    simp only [List.map_cons, List.filterMap_cons, Instr.edgeOf]
    exact congrArg (fun t => E w :: t) (filterMap_map_edge ι E ws)

private theorem entI_edges (a : ℕ) :
    (NB.entI (toNB ch0O) a).filterMap Instr.edgeOf =
      (List.range wAuxEnd).map fun w => NB.entE (toNB ch0O) a w := by
  change
      ((List.range wAuxEnd).map fun w =>
          (Instr.edge (NB.ι2 a w) (NB.entE (toNB ch0O) a w) :
            Instr NB.Wr (ZMod 2) 529)).filterMap Instr.edgeOf =
        (List.range wAuxEnd).map fun w => NB.entE (toNB ch0O) a w
  exact filterMap_map_edge (NB.ι2 a) (NB.entE (toNB ch0O) a) (List.range wAuxEnd)

private theorem range_wAuxEnd_split :
    List.range wAuxEnd =
      List.range wEnt ++ (List.range NR).map (fun i => wEnt + i) := by
  have h : wAuxEnd = wEnt + NR := rfl
  rw [h]
  exact @List.range_add wEnt NR

private theorem entE_of_ge_wEnt (a w : ℕ) (hw : wEnt ≤ w) :
    NB.entE (toNB ch0O) a w = (toNB ch0O).ei a := by
  unfold NB.entE
  have hv : ¬ w < v := by
    intro hwv
    exact Nat.not_le_of_gt (Nat.lt_trans hwv (by decide : v < wEnt)) hw
  have hw' : ¬ w < wEnt := Nat.not_lt.2 hw
  simp [hv, hw']

private theorem ei_eq_pickE (a : ℕ) (ha : a < v) :
    (toNB ch0O).ei a =
      OneRunNet2.pickE (OneRunNet2.PE (K S0 Si0 (1 - Pl a) 1) (oneRun 22)) := by
  simp [toNB, ch0O, ha]

private theorem ei_headW_ne_484 (a : ℕ) (ha : a < v) :
    headW484 ((toNB ch0O).ei a) = false := by
  have hPE := net0O2_ei_PE a ha
  have hw := pickE_oneRun_headW (K S0 Si0 (1 - Pl a) 1) 22 hPE
  rw [ei_eq_pickE a ha]
  change decide
      ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2)
          (OneRunNet2.pickE (OneRunNet2.PE (K S0 Si0 (1 - Pl a) 1) (oneRun 22))).runs.head?).getD
          0 =
        484) =
      false
  rw [hw]
  decide

private theorem filter_map_ei_nil (a : ℕ) (ha : a < v) :
    ∀ l : List ℕ, (l.map fun _ => (toNB ch0O).ei a).filter headW484 = []
  | [] => by simp
  | _ :: ws => by
    simp only [List.map_cons, List.filter_cons, ei_headW_ne_484 a ha,
      Bool.false_eq_true, ↓reduceIte]
    exact filter_map_ei_nil a ha ws

private theorem filter_grid_id (a : ℕ) (ha : a < v) :
    ((List.range wEnt).map fun w => NB.entE (toNB ch0O) a w).filter headW484 =
      (List.range wEnt).map fun w => NB.entE (toNB ch0O) a w := by
  refine List.filter_eq_self.2 ?_
  intro e he
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 he
  exact decide_eq_true
    (net0O2_entE_width484 a w (List.mem_range.1 (List.mem_range.2 ha)) (List.mem_range.1 hw))

private theorem entI_filter_one (a : ℕ) (ha : a < v) :
    ((NB.entI (toNB ch0O) a).filterMap Instr.edgeOf).filter headW484 =
      (List.range wEnt).map fun w => NB.entE (toNB ch0O) a w := by
  rw [entI_edges, range_wAuxEnd_split, List.map_append, List.filter_append,
    filter_grid_id a ha]
  have htail :
      (((List.range NR).map fun i => wEnt + i).map fun w => NB.entE (toNB ch0O) a w) =
        (List.range NR).map fun _ => (toNB ch0O).ei a := by
    simp only [List.map_map]
    refine List.map_congr_left ?_
    intro i _hi
    exact entE_of_ge_wEnt a (wEnt + i) (Nat.le_add_right _ _)
  rw [htail, filter_map_ei_nil a ha, List.append_nil]

private theorem filter_flatMap_ind {α β : Type*} (f : α → List β) (p : β → Bool) :
    ∀ l : List α, (l.flatMap f).filter p = l.flatMap fun a => (f a).filter p
  | [] => by simp [List.flatMap]
  | a :: as => by
    have ih := filter_flatMap_ind f p as
    change ((f a ++ as.flatMap f).filter p) = (f a).filter p ++ as.flatMap fun x => (f x).filter p
    rw [List.filter_append, ih]

theorem solution :
    ((List.range v).flatMap fun a =>
        (NB.entI (toNB ch0O) a).filterMap Instr.edgeOf).filter
      (fun e : Edge 529 =>
        decide ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0 = 484)) =
      ((List.range v).flatMap fun a =>
        (List.range wEnt).map fun w => NB.entE (toNB ch0O) a w) := by
  change
      ((List.range v).flatMap fun a =>
          (NB.entI (toNB ch0O) a).filterMap Instr.edgeOf).filter headW484 =
        ((List.range v).flatMap fun a =>
          (List.range wEnt).map fun w => NB.entE (toNB ch0O) a w)
  rw [filter_flatMap_ind (fun a => (NB.entI (toNB ch0O) a).filterMap Instr.edgeOf) headW484
    (List.range v)]
  refine List.flatMap_congr ?_
  intro a ha
  exact entI_filter_one a (List.mem_range.1 ha)
