-- Prove2me | solution 1 for OAI.Solenoidal.Computing.rat_inv
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:40:48.547765+00:00
-- url     : https://prove2.me/submissions/6a5b0d4b-cdf7-4b32-8c48-649d2af9b285

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/Computing.lean:L236-L248
-- (upload_full_project.md Phase 4): solution for node OAI.Solenoidal.Computing.rat_inv. The node keeps its source
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
import Theorems.Thm_OAI_Solenoidal_Computing_int_add

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

theorem int_edivNat : Primrec₂ (fun (z : ℤ) (n : ℕ) => z / (n:ℤ)) := by
  let f : ℤ×ℕ → ℤ := fun p => Int.casesOn p.1
    (fun m => Int.ofNat (m / p.2))
    (fun m => Nat.casesOn p.2 0 (fun n => Int.negSucc (m / (n+1))))
  have h : Primrec f := by
    apply int_cases .fst
    · exact int_ofNat.comp (Primrec.nat_div.comp .snd (Primrec.snd.comp .fst))
    · exact Primrec.nat_casesOn (Primrec.snd.comp .fst) (.const 0)
        (int_negSucc.comp (Primrec.nat_div.comp (Primrec.snd.comp .fst)
          (Primrec.succ.comp .snd))).to₂
  exact h.of_eq (fun ⟨a,b⟩ => by cases a <;> cases b <;> rfl)

theorem int_nonneg : PrimrecPred (fun z : ℤ => 0 ≤ z) := by
  refine ⟨inferInstance, ?_⟩
  refine (int_cases .id (Primrec₂.const true) (Primrec₂.const false)).of_eq ?_
  intro z
  cases z with
  | ofNat n => change true = decide (0 ≤ (n:ℤ)); simp
  | negSucc n => rfl

theorem int_le : PrimrecRel ((· ≤ ·) : ℤ → ℤ → Prop) :=
  (int_nonneg.comp (int_add.comp .snd (int_neg.comp .fst))).of_eq
    (fun p => by simp [← sub_eq_add_neg])

theorem int_lt : PrimrecRel ((· < ·) : ℤ → ℤ → Prop) :=
  ((int_le.comp .snd .fst).not).of_eq (fun _ => not_le)

theorem rat_num : Primrec Rat.num :=
  Primrec.fst.comp (Primrec.subtype_val.comp (Primrec.of_equiv (e := ratEquiv)))

theorem rat_den : Primrec Rat.den :=
  Primrec.snd.comp (Primrec.subtype_val.comp (Primrec.of_equiv (e := ratEquiv)))

theorem rat_mk_iff {α : Type*} [Primcodable α] {f : α → ℚ} :
    Primrec f ↔ Primrec (fun a => (f a).num) ∧ Primrec (fun a => (f a).den) := by
  refine ⟨fun h => ⟨rat_num.comp h,rat_den.comp h⟩, fun h => ?_⟩
  exact (Primrec.of_equiv_iff ratEquiv).mp
    ((Primrec.subtype_val_iff).mp (h.1.pair h.2))

theorem rat_mk : Primrec₂ mkRat := by
  apply rat_mk_iff.mpr
  constructor
  · exact (Primrec.ite (Primrec.eq.comp .snd (.const 0)) (.const 0)
      (int_edivNat.comp .fst (nat_gcd.comp .snd (int_natAbs.comp .fst)))).of_eq
        (fun p => (Rat.num_mkRat p.1 p.2).symm)
  · exact (Primrec.ite (Primrec.eq.comp .snd (.const 0)) (.const 1)
      (Primrec.nat_div.comp .snd (nat_gcd.comp .snd (int_natAbs.comp .fst)))).of_eq
        (fun p => (Rat.den_mkRat p.1 p.2).symm)

theorem rat_inv : Primrec (fun q : ℚ => q⁻¹) := by
  have h : Primrec (fun q : ℚ =>
      if q.num < 0 then mkRat (-(q.den:ℤ)) q.num.natAbs
      else mkRat (q.den:ℤ) q.num.natAbs) :=
    Primrec.ite (int_lt.comp rat_num (.const 0))
      (rat_mk.comp (int_neg.comp (int_ofNat.comp rat_den)) (int_natAbs.comp rat_num))
      (rat_mk.comp (int_ofNat.comp rat_den) (int_natAbs.comp rat_num))
  refine h.of_eq ?_
  intro q
  rw [Rat.inv_def]
  cases q.num with
  | ofNat numerator => simp [Rat.divInt]
  | negSucc numerator => simp [Rat.divInt,Rat.normalize_eq_mkRat]

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


theorem solution : type_of% @_root_.OAI.Solenoidal.Computing.rat_inv := @_root_.OAI.Solenoidal.Computing.rat_inv
