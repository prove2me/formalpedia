-- Prove2me | solution 1 for OAI.BalancedTransport.Effectivity.NumericOp.computable_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:39:49.778644+00:00
-- url     : https://prove2.me/submissions/f5f57dde-3b40-4dbf-a540-9a0281bb3dca

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/NumericPrograms.lean:L158-L201
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Effectivity.NumericOp.computable_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Work
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_TimeRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FieldBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompactFamilies
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ResidualRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RhoAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveLog
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericPrograms

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.RationalAlgorithms ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity

lemma primrec_nat_factorial : Primrec Nat.factorial := by
  have h : Primrec₂ (fun (_ : Unit) n => Nat.rec (motive := fun _ => ℕ) 1 (fun n r => (n + 1) * r) n) :=
    Primrec.nat_rec (Primrec.const 1)
      (Primrec.nat_mul.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd)).to₂
  refine (h.comp (Primrec.const ()) Primrec.id).of_eq ?_
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simpa [Nat.factorial_succ] using congrArg (fun k => (n + 1) * k) ih

end BalancedTransport.Effectivity
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.RhoAlgorithms ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open Polynomial
open scoped NNReal

lemma primrec_rhoCoeffStep : Primrec rhoCoeffStep := by
  have h : Primrec₂ (fun cs : List ℤ => fun j : ℕ =>
      cs.getD j 0 - (j + 1 : ℤ) * cs.getD (j + 1) 0) := by
    have h₁ : Primrec (fun p : List ℤ × ℕ => (p.2 + 1 : ℤ)) := by
      exact (primrec_int_ofNat.comp (Primrec.succ.comp Primrec.snd)).of_eq
        (fun _ => by simp)
    exact (primrec_int_add.comp (Primrec.list_getD 0)
      (primrec_int_neg.comp (primrec_int_mul.comp h₁
        ((Primrec.list_getD 0).comp Primrec.fst (Primrec.succ.comp Primrec.snd))))).of_eq
          (fun _ => (sub_eq_add_neg _ _).symm)
  exact Primrec.list_cons.comp (Primrec.const 0) (Primrec.list_cons.comp
    (Primrec.const 0) (Primrec.list_map (Primrec.list_range.comp Primrec.list_length) h))

lemma primrec_rhoCoeffs : Primrec rhoCoeffs := by
  have h : Primrec₂ (fun (_ : Unit) n => Nat.rec (motive := fun _ => List ℤ)
      [1] (fun _ cs => rhoCoeffStep cs) n) :=
    Primrec.nat_rec (Primrec.const [1])
      (primrec_rhoCoeffStep.comp (Primrec.snd.comp Primrec.snd)).to₂
  refine (h.comp (Primrec.const ()) Primrec.id).of_eq ?_
  intro n
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg rhoCoeffStep ih

lemma primrec_sum_range_nat {α : Type*} [Primcodable α]
    {f : α → ℕ → ℕ} (hf : Primrec₂ f) :
    Primrec₂ (fun a n => ∑ i ∈ Finset.range n, f a i) := by
  have hh : Primrec₂ (fun a n => Nat.rec (motive := fun _ => ℕ) 0
      (fun j r => r + f a j) n) :=
    Primrec.nat_rec (Primrec.const 0)
      (Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd)
        (hf.comp Primrec.fst (Primrec.fst.comp Primrec.snd))).to₂
  refine hh.of_eq ?_
  intro a n
  induction n with
  | zero => simp
  | succ n ih => simpa [Finset.sum_range_succ] using congrArg (fun r => r + f a n) ih

lemma primrec_rhoBound : Primrec₂ rhoBound := by
  have hh : Primrec₂ (fun p : ℕ × ℕ => fun j =>
      ((rhoCoeffs p.1).getD j 0).natAbs * (j + p.2).factorial) :=
    Primrec.nat_mul.comp
      (primrec_int_natAbs.comp ((Primrec.list_getD 0).comp
        (primrec_rhoCoeffs.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd))
      (primrec_nat_factorial.comp (Primrec.nat_add.comp Primrec.snd
        (Primrec.snd.comp Primrec.fst)))
  exact (primrec_sum_range_nat hh).comp Primrec.id
    (Primrec.list_length.comp (primrec_rhoCoeffs.comp Primrec.fst))

end BalancedTransport.Effectivity
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.NumericPrograms ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity

lemma computable_fin_cases {α β : Type*} [Primcodable α] [Primcodable β]
    [Inhabited β] {n : ℕ} {i : α → Fin n} {f : Fin n → α → β}
    (hi : Computable i) (hf : ∀ j, Computable (f j)) :
    Computable (fun a => f (i a) a) := by
  have hl : Computable (fun a => List.ofFn (fun j => f j a)) :=
    Computable.list_ofFn hf
  exact ((Primrec.list_getD default).to_comp.comp hl (Primrec.fin_val.to_comp.comp hi)).of_eq
    (fun a => by simp)

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp

lemma computable_bound : Computable (fun z : NumericOp × ℕ × List (ℕ × ℕ) =>
    bound z.1 z.2.1 z.2.2) := by
  have ha : Computable (fun z : NumericOp × ℕ × List (ℕ × ℕ) => z.1.left) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hb : Computable (fun z : NumericOp × ℕ × List (ℕ × ℕ) => z.1.right) :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hq : Computable (fun z : NumericOp × ℕ × List (ℕ × ℕ) => z.1.rat) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hs : Computable (fun z : NumericOp × ℕ × List (ℕ × ℕ) => z.2.2) :=
    Computable.snd.comp Computable.snd
  have hva := (Primrec.list_getD (0,0)).to_comp.comp hs ha
  have hvb := (Primrec.list_getD (0,0)).to_comp.comp hs hb
  have hA := Computable.fst.comp hva
  have hE := Computable.snd.comp hva
  have hB := Computable.fst.comp hvb
  have hF := Computable.snd.comp hvb
  have hadd := Primrec.nat_add.to_comp
  have hmul := Primrec.nat_mul.to_comp
  have hpow : Computable₂ (fun a b : ℕ => a ^ b) := by
    exact (((Primrec.nat_iff.mpr Nat.Primrec.pow).comp Primrec.encode).of_eq
      (fun p => by rcases p with ⟨a,b⟩; change (Nat.unpair (Nat.pair a b)).1 ^ (Nat.unpair (Nat.pair a b)).2 = a ^ b; rw [Nat.unpair_pair])).to_comp
  have hn := primrec_int_natAbs.to_comp.comp (computable_rat_num.comp hq)
  have hc (j : Fin 9) : Computable (fun z : NumericOp × ℕ × List (ℕ × ℕ) =>
      boundCase j z.1 z.2.1 z.2.2) := by
    fin_cases j <;> dsimp only [boundCase, rat, left, right]
    · simpa only [left, right, rat] using hn.pair (Computable.const 0)
    · simpa only [left, right, rat] using (Computable.fst.comp Computable.snd).pair (Computable.const 0)
    · simpa only [left, right, rat] using (hadd.comp hA hB).pair (hadd.comp hE hF)
    · simpa only [left, right, rat] using (hmul.comp hA hB).pair
        (hadd.comp (hmul.comp (hadd.comp hA hE) hF) (hmul.comp hB hE))
    · simpa only [left, right, rat] using hva
    · simpa only [left, right, rat] using (Computable.succ.comp hb).pair
        (hmul.comp (hpow.comp (Computable.succ.comp hb) (Computable.const 2)) hE)
    · simpa only [left, right, rat] using (primrec_rhoBound.to_comp.comp ha (Computable.const 0)).pair
        (hadd.comp (Computable.const 1) (hmul.comp
          (primrec_rhoBound.to_comp.comp (Computable.succ.comp ha) (Computable.const 0)) hF))
    · simpa only [left, right, rat] using (hpow.comp (Computable.const 3) hA).pair
        (hadd.comp (Computable.const 1) (hmul.comp
          (hpow.comp (Computable.const 3) (hadd.comp hA hE)) hE))
    · simpa only [left, right, rat] using (hadd.comp hn (primrec_int_natAbs.to_comp.comp
        (computable_rat_num.comp (computable_rat_inv.comp hq)))).pair (Computable.const 1)
  have H := computable_fin_cases (i := fun z => z.1.tag)
    (Computable.fst.comp Computable.fst) hc
  simpa only [bound] using H

end BalancedTransport.Effectivity.NumericOp
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity OAI.BalancedTransport.Effectivity.NumericOp


theorem solution : type_of% @_root_.OAI.BalancedTransport.Effectivity.NumericOp.computable_bound := @_root_.OAI.BalancedTransport.Effectivity.NumericOp.computable_bound
