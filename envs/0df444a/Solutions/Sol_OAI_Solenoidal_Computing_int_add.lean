-- Prove2me | solution 1 for OAI.Solenoidal.Computing.int_add
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:37:50.15524+00:00
-- url     : https://prove2.me/submissions/50b90805-a606-4fe7-b3ff-4fe491a89cd3

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/Computing.lean:L88-L103
-- (upload_full_project.md Phase 4): solution for node OAI.Solenoidal.Computing.int_add. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SolenoidalSheetPrograms
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_DirectForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Profiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Clocks
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Differential
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ScheduledForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ClassicalRegularity
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_EnergyIdentities
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RectangleGeometry
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Trajectories
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Pulses
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Localization
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ShearCore
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Routing
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_JetCalculus
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_JetProfiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_BoxJets
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RationalFormula
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_FormulaProfiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RationalBalls
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Computing

-- ---- from OAI.MathematicalPhysics.SheetFlows.Computing ----
namespace OAI

/-! SheetFlows computing. -/

section
open Encodable
namespace Solenoidal.Computing

theorem int_ofNat : Primrec Int.ofNat :=
  Primrec.encode_iff.mp (Primrec.nat_mul.comp (.const 2) .id)

theorem int_negSucc : Primrec Int.negSucc :=
  Primrec.encode_iff.mp (Primrec.nat_add.comp (Primrec.nat_mul.comp (.const 2) .id) (.const 1))

theorem int_subNatNat : Primrec₂ Int.subNatNat := by
  refine (Primrec.ite Primrec.nat_le
    (Primrec.nat_casesOn (Primrec.nat_sub.comp .snd .fst) (.const 0)
      (int_negSucc.comp .snd).to₂)
    (int_ofNat.comp (Primrec.nat_sub.comp .fst .snd))).of_eq ?_
  intro p
  simp only [Int.subNatNat]
  split <;> rename_i h
  · split <;> simp_all
  · split <;> simp_all; omega

theorem int_add : Primrec₂ ((·+·) : ℤ → ℤ → ℤ) := by
  let f : ℤ×ℤ → ℤ := fun p => Int.casesOn p.1
    (fun n => Int.casesOn p.2 (fun m => Int.ofNat (n+m))
      (fun m => Int.subNatNat n (m+1)))
    (fun n => Int.casesOn p.2 (fun m => Int.subNatNat m (n+1))
      (fun m => Int.negSucc (n+m+1)))
  have h : Primrec f := by
    apply int_cases .fst
    · apply int_cases (Primrec.snd.comp .fst)
      · exact int_ofNat.comp (Primrec.nat_add.comp (Primrec.snd.comp .fst) .snd)
      · exact int_subNatNat.comp (Primrec.snd.comp .fst) (Primrec.succ.comp .snd)
    · apply int_cases (Primrec.snd.comp .fst)
      · exact int_subNatNat.comp .snd (Primrec.succ.comp (Primrec.snd.comp .fst))
      · exact int_negSucc.comp (Primrec.succ.comp
          (Primrec.nat_add.comp (Primrec.snd.comp .fst) .snd))
  exact h.of_eq (fun ⟨a,b⟩ => by cases a <;> cases b <;> rfl)

end Solenoidal.Computing
end

section
open Encodable
open scoped BigOperators
namespace Solenoidal.Computing

end Solenoidal.Computing
end

end OAI

-- ---- platform node ----
open OAI OAI.Solenoidal OAI.Solenoidal.Computing
open Encodable


theorem solution : type_of% @_root_.OAI.Solenoidal.Computing.int_add := @_root_.OAI.Solenoidal.Computing.int_add
