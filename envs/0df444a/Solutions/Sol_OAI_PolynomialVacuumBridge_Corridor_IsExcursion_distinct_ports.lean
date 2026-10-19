-- Prove2me | solution 1 for OAI.PolynomialVacuumBridge.Corridor.IsExcursion.distinct_ports
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:29:24.608437+00:00
-- url     : https://prove2.me/submissions/34c1f71e-3638-454e-bcbc-f63c9ec85167

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/Excursions.lean:L403-L420
-- (upload_full_project.md Phase 4): solution for node OAI.PolynomialVacuumBridge.Corridor.IsExcursion.distinct_ports. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_HoneycombBridgeFiniteness
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Basic
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Excursions

-- ---- from OAI.Combinatorics.HoneycombCorridor.Excursions ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem IsExcursion.distinct_ports {D : Finset Vertex} {e : Germ × List Bool}
    (he : IsExcursion D e) : reverseGerm (terminalGerm e.1 e.2) ≠ e.1 := by
  intro hp
  obtain ⟨b,w,hw⟩ := List.exists_cons_of_ne_nil he.nonempty
  have hN := (stopped_traced D e.1 e.2 he.2.2.1).1
  rw [hw,traced,List.nodup_cons] at hN
  cases w with
  | nil =>
      have hk := congrArg Prod.snd hp
      simp only [hw,terminalGerm,reverseGerm,advance] at hk
      rcases e.1 with ⟨v,k⟩
      fin_cases k <;> cases b <;> simp [outgoingSlot] at hk
  | cons c w =>
      apply hN.1
      have hm := reverse_first_mem (advance e.1 b) (c :: w) (by simp)
      have hx : (reverseGerm (terminalGerm (advance e.1 b) (c :: w))).1 = e.1.1 :=
        congrArg Prod.fst (by simpa only [hw,terminalGerm] using hp)
      exact hx ▸ hm

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- platform node ----
open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor


theorem solution : type_of% @_root_.OAI.PolynomialVacuumBridge.Corridor.IsExcursion.distinct_ports := @_root_.OAI.PolynomialVacuumBridge.Corridor.IsExcursion.distinct_ports
