-- Prove2me | solution 1 for OAI.Solenoidal.Computing.int_mul
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:39:18.811195+00:00
-- url     : https://prove2.me/submissions/f86553a0-42fb-4497-a043-44a35b4b2979

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/Computing.lean:L105-L122
-- (upload_full_project.md Phase 4): solution for node OAI.Solenoidal.Computing.int_mul. The node keeps its source
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

theorem int_neg : Primrec ((- ·) : ℤ → ℤ) := by
  have h : Primrec (fun z : ℤ => Int.casesOn (motive := fun _ => ℤ) z
      (fun n => Nat.casesOn n (0 : ℤ) Int.negSucc) (fun n => Int.ofNat (n+1))) := by
    exact int_cases .id
      (Primrec.nat_casesOn .snd (.const 0) (int_negSucc.comp .snd).to₂)
      (int_ofNat.comp (Primrec.succ.comp .snd))
  exact h.of_eq (fun z => by cases z with
    | ofNat n => cases n <;> rfl
    | negSucc n => rfl)

theorem int_mul : Primrec₂ ((·*·) : ℤ → ℤ → ℤ) := by
  let f : ℤ×ℤ → ℤ := fun p => Int.casesOn p.1
    (fun n => Int.casesOn p.2 (fun m => Int.ofNat (n*m))
      (fun m => -(Int.ofNat (n*(m+1)))))
    (fun n => Int.casesOn p.2 (fun m => -(Int.ofNat ((n+1)*m)))
      (fun m => Int.ofNat ((n+1)*(m+1))))
  have h : Primrec f := by
    apply int_cases .fst
    · apply int_cases (Primrec.snd.comp .fst)
      · exact int_ofNat.comp (Primrec.nat_mul.comp (Primrec.snd.comp .fst) .snd)
      · exact int_neg.comp (int_ofNat.comp (Primrec.nat_mul.comp
          (Primrec.snd.comp .fst) (Primrec.succ.comp .snd)))
    · apply int_cases (Primrec.snd.comp .fst)
      · exact int_neg.comp (int_ofNat.comp (Primrec.nat_mul.comp
          (Primrec.succ.comp (Primrec.snd.comp .fst)) .snd))
      · exact int_ofNat.comp (Primrec.nat_mul.comp
          (Primrec.succ.comp (Primrec.snd.comp .fst)) (Primrec.succ.comp .snd))
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


theorem solution : type_of% @_root_.OAI.Solenoidal.Computing.int_mul := @_root_.OAI.Solenoidal.Computing.int_mul
