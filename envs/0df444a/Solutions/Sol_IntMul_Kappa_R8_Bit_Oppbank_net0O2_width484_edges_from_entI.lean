-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_width484_edges_from_entI
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T06:12:03.795339+00:00
-- url     : https://prove2.me/submissions/b853cbf8-6650-449e-8bb5-513282f58d1c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_blk1_edges_width_ne_484
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_entI_filter_eq_entE_grid
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_blk2_filter_eq_entI_filter
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd

/-- Prefer blk1 ++ blk2 order (not global entI ++ tail). -/
private theorem edges_blk12 :
    net0O.edges =
      ((List.range v).flatMap (NB.blk1 (toNB ch0O))).filterMap Instr.edgeOf ++
        ((List.range v).flatMap (NB.blk2 (toNB ch0O))).filterMap Instr.edgeOf := by
  change (NB.net (toNB ch0O)).edges = _
  simp only [NB.net, QHNet.edges, progEdges, NB.prog]
  rw [List.filterMap_append]

private theorem filterMap_flatMap_ind {α β γ : Type*} (f : α → List β) (g : β → Option γ) :
    ∀ l : List α,
      (l.flatMap f).filterMap g = l.flatMap fun a => (f a).filterMap g
  | [] => by simp [List.flatMap]
  | a :: as => by
    have ih := filterMap_flatMap_ind f g as
    -- flatMap f (a::as) = f a ++ flatMap f as
    change ((f a ++ as.flatMap f).filterMap g) = (f a).filterMap g ++ as.flatMap fun x => (f x).filterMap g
    rw [List.filterMap_append, ih]

private theorem entI_filterMap_flat :
    ((List.range v).flatMap (NB.entI (toNB ch0O))).filterMap Instr.edgeOf =
      (List.range v).flatMap fun a =>
        (NB.entI (toNB ch0O) a).filterMap Instr.edgeOf :=
  filterMap_flatMap_ind (NB.entI (toNB ch0O)) Instr.edgeOf (List.range v)

theorem solution :
    (net0O.edges.filter
        (fun e : Edge 529 =>
          decide ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0 = 484))) =
      ((List.range v).flatMap fun a =>
        (List.range wEnt).map fun w => NB.entE (toNB ch0O) a w) := by
  have hblk1 := net0O2_blk1_edges_width_ne_484
  have hblk2 := net0O2_blk2_filter_eq_entI_filter
  have hentI := net0O2_entI_filter_eq_entE_grid
  rw [edges_blk12, List.filter_append, hblk1, List.nil_append, hblk2, entI_filterMap_flat]
  exact hentI
