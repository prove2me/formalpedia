-- Prove2me | solution 1 for OAI.BalancedTransport.Effectivity.NumericOp.computable_rational
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:37:52.684099+00:00
-- url     : https://prove2.me/submissions/62c72cbb-d3b5-4d78-a57c-af51e6114206

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/NumericPrograms.lean:L121-L156
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Effectivity.NumericOp.computable_rational. The node keeps its source
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
import Theorems.Thm_OAI_BalancedTransport_Effectivity_computable_rat_le
import Theorems.Thm_OAI_BalancedTransport_Effectivity_computable_rat_pow
import Theorems.Thm_OAI_BalancedTransport_Effectivity_computable_sum_range

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.RationalAlgorithms ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity

lemma computable_rat_abs : Computable (fun q : ℚ => |q|) := by
  exact (computable_ite (computable_rat_le.comp (Computable.const 0) Computable.id)
    Computable.id computable_rat_neg).of_eq (fun q => by
      split_ifs with h
      · exact (abs_of_nonneg h).symm
      · exact (abs_of_neg (lt_of_not_ge h)).symm)

lemma computable_rat_sub : Computable₂ ((· - ·) : ℚ → ℚ → ℚ) := by
  exact (computable_rat_add.comp Computable.fst (computable_rat_neg.comp Computable.snd)).of_eq
    (fun _ => (sub_eq_add_neg _ _).symm)

lemma computable_rat_natCast : Computable (fun n : ℕ => (n : ℚ)) := by
  exact (computable_rat_of_parts primrec_int_ofNat.to_comp (Computable.const 1)
    (fun _ => by decide)).of_eq (fun n => by norm_cast; simp)

lemma computable_rat_intCast : Computable (fun n : ℤ => (n : ℚ)) := by
  exact (computable_rat_of_parts Computable.id (Computable.const 1)
    (fun _ => by decide)).of_eq (fun n => by norm_num)

lemma computable_rat_div : Computable₂ ((· / ·) : ℚ → ℚ → ℚ) := by
  exact (computable_rat_mul.comp Computable.fst (computable_rat_inv.comp Computable.snd)).of_eq
    (fun _ => (div_eq_mul_inv _ _).symm)

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

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.EffectiveExp ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open Filter
open scoped Topology

lemma computable_decide_and {α : Type*} [Primcodable α]
    {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (hp : Computable fun a => decide (p a)) (hq : Computable fun a => decide (q a)) :
    Computable (fun a => decide (p a ∧ q a)) := by
  exact (Computable.cond hp hq (Computable.const false)).of_eq (fun a => by
    by_cases h : p a <;> simp [h])

lemma computable_expAccurate :
    Computable₂ (fun p : ℚ × ℕ => fun k => decide (expAccurate p.1 p.2 k)) := by
  have hq : Computable (fun p : (ℚ × ℕ) × ℕ => |p.1.1|) :=
    computable_rat_abs.comp (Computable.fst.comp Computable.fst)
  have hr : Computable (fun p : (ℚ × ℕ) × ℕ => |p.1.1| / ((p.2 + 1 : ℕ) : ℚ)) :=
    computable_rat_div.comp hq (computable_rat_natCast.comp (Computable.succ.comp Computable.snd))
  have ha : Computable (fun p : (ℚ × ℕ) × ℕ =>
      |p.1.1| ^ p.2 / (p.2.factorial : ℚ) * 2) :=
    computable_rat_mul.comp (computable_rat_div.comp (computable_rat_pow.comp hq Computable.snd)
      (computable_rat_natCast.comp (primrec_nat_factorial.to_comp.comp Computable.snd)))
      (Computable.const 2)
  exact computable_decide_and
    (computable_rat_le.comp hr (Computable.const (1 / 2)))
    (computable_rat_le.comp ha (computable_rat_pow.comp (Computable.const (1 / 2))
      (Computable.snd.comp Computable.fst)))

lemma computable_expCutoff : Computable₂ expCutoff :=
  computable_find computable_expAccurate (fun p => exists_expAccurate p.1 p.2)

lemma computable_expApprox : Computable₂ expApprox := by
  have hs : Computable₂ (fun q : ℚ => fun n : ℕ =>
      ∑ k ∈ Finset.range n, q ^ k / (k.factorial : ℚ)) :=
    computable_sum_range (computable_rat_div.comp computable_rat_pow
      (computable_rat_natCast.comp (primrec_nat_factorial.to_comp.comp Computable.snd)))
  exact hs.comp Computable.fst computable_expCutoff

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

lemma computable_rhoPolyValue : Computable₂ rhoPolyValue := by
  have hh : Computable₂ (fun p : ℕ × ℚ => fun j =>
      ((rhoCoeffs p.1).getD j 0 : ℚ) * p.2 ^ j) :=
    computable_rat_mul.comp
      (computable_rat_intCast.comp ((Primrec.list_getD 0).to_comp.comp
        (primrec_rhoCoeffs.to_comp.comp (Computable.fst.comp Computable.fst)) Computable.snd))
      (computable_rat_pow.comp (Computable.snd.comp Computable.fst) Computable.snd)
  exact (computable_sum_range hh).comp Computable.id
    (Primrec.list_length.to_comp.comp (primrec_rhoCoeffs.to_comp.comp Computable.fst))

lemma computable_rhoApprox : Computable (fun s : ℕ × ℚ × ℕ => rhoApprox s.1 s.2.1 s.2.2) := by
  have hq : Computable (fun s : ℕ × ℚ × ℕ => s.2.1⁻¹) :=
    computable_rat_inv.comp (Computable.fst.comp Computable.snd)
  have hv : Computable (fun s : ℕ × ℚ × ℕ => rhoPolyValue s.1 s.2.1⁻¹) :=
    computable_rhoPolyValue.comp Computable.fst hq
  exact computable_ite (computable_rat_le.comp (Computable.fst.comp Computable.snd)
    (Computable.const 0)) (Computable.const 0)
    (computable_rat_mul.comp hv (computable_expApprox.comp (computable_rat_neg.comp hq)
      (Primrec.nat_add.to_comp.comp (Computable.snd.comp Computable.snd)
        (primrec_int_natAbs.to_comp.comp (computable_rat_num.comp hv)))))

end BalancedTransport.Effectivity
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.EffectiveLog ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open Filter
open scoped Topology

lemma computable_rat_lt : Computable₂ (fun a b : ℚ => decide (a < b)) := by
  exact (Computable.cond (computable_rat_le.comp Computable.snd Computable.fst)
    (Computable.const false) (Computable.const true)).of_eq
      (fun p => by
        by_cases h : p.2 ≤ p.1
        · simp [h, not_lt.mpr h]
        · simp [h, lt_of_not_ge h])

lemma computable_logBracket :
    Computable₂ (fun p : ℚ × ℕ => fun c => decide (logBracket p.1 p.2 c)) := by
  have hr : Computable (fun p : (ℚ × ℕ) × ℕ => Denumerable.ofNat ℚ p.2.unpair.1) :=
    (Computable.ofNat ℚ).comp (Computable.fst.comp (Primrec.unpair.to_comp.comp Computable.snd))
  have hk : Computable (fun p : (ℚ × ℕ) × ℕ => p.2.unpair.2) :=
    Computable.snd.comp (Primrec.unpair.to_comp.comp Computable.snd)
  have he : Computable (fun p : (ℚ × ℕ) × ℕ => (1 / 2 : ℚ) ^ p.1.2) :=
    computable_rat_pow.comp (Computable.const (1 / 2)) (Computable.snd.comp Computable.fst)
  have hd : Computable (fun p : (ℚ × ℕ) × ℕ => (1 / 2 : ℚ) ^ p.2.unpair.2) :=
    computable_rat_pow.comp (Computable.const (1 / 2)) hk
  exact computable_decide_and
    (computable_rat_lt.comp
      (computable_rat_add.comp (computable_expApprox.comp (computable_rat_sub.comp hr he) hk) hd)
      (Computable.fst.comp Computable.fst))
    (computable_rat_lt.comp (Computable.fst.comp Computable.fst)
      (computable_rat_sub.comp (computable_expApprox.comp (computable_rat_add.comp hr he) hk) hd))

lemma computable_logCutoff : Computable logCutoff := by
  apply computable_find (hex := exists_logSearchPredicate)
  exact (Computable.cond (computable_rat_lt.comp (Computable.const 0)
    (Computable.fst.comp Computable.fst)) computable_logBracket (Computable.const true)).of_eq
      (fun p => by by_cases hq : 0 < p.1.1 <;> simp [logSearchPredicate, hq])

lemma computable_logApprox : Computable₂ logApprox := by
  exact computable_ite (computable_rat_lt.comp (Computable.const 0) Computable.fst)
    ((Computable.ofNat ℚ).comp (Computable.fst.comp
      (Primrec.unpair.to_comp.comp computable_logCutoff))) (Computable.const 0)

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

lemma computable_rational (d : ℕ) [NeZero d] :
    Computable (fun z : NumericOp × (Fin d → ℚ) × ℕ × List ℚ =>
      rational d z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  have ha : Computable (fun z : NumericOp × (Fin d → ℚ) × ℕ × List ℚ => z.1.left) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hb : Computable (fun z : NumericOp × (Fin d → ℚ) × ℕ × List ℚ => z.1.right) :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hq : Computable (fun z : NumericOp × (Fin d → ℚ) × ℕ × List ℚ => z.1.rat) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hs : Computable (fun z : NumericOp × (Fin d → ℚ) × ℕ × List ℚ => z.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have hp : Computable (fun z : NumericOp × (Fin d → ℚ) × ℕ × List ℚ => z.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hva := (Primrec.list_getD (0 : ℚ)).to_comp.comp hs ha
  have hvb := (Primrec.list_getD (0 : ℚ)).to_comp.comp hs hb
  have hi : Primrec (fun a : ℕ => Fin.ofNat d a) :=
    Primrec.fin_val_iff.mp (Primrec.nat_mod.comp Primrec.id (Primrec.const d))
  have hmax : Computable₂ (fun a b : ℚ => max a b) := by
    exact (computable_ite computable_rat_le Computable.snd Computable.fst).of_eq
      (fun p => by split_ifs with h <;> simp [max_def, h])
  have hc (j : Fin 9) : Computable (fun z : NumericOp × (Fin d → ℚ) × ℕ × List ℚ =>
      rationalCase d j z.1 z.2.1 z.2.2.1 z.2.2.2) := by
    fin_cases j <;> dsimp only [rationalCase, rat, left, right]
    · simpa only [left, right, rat] using hq
    · simpa only [left, right, rat, id_eq] using Computable.fin_app.comp (Computable.fst.comp Computable.snd) (hi.to_comp.comp ha)
    · simpa only [left, right, rat] using computable_rat_add.comp hva hvb
    · simpa only [left, right, rat] using computable_rat_mul.comp hva hvb
    · simpa only [left, right, rat] using computable_rat_neg.comp hva
    · simpa only [left, right, rat] using computable_rat_inv.comp (hmax.comp
        (computable_rat_inv.comp (computable_rat_natCast.comp (Computable.succ.comp hb))) hva)
    · simpa only [left, right, rat] using computable_rhoApprox.comp (ha.pair (hvb.pair hp))
    · simpa only [left, right, rat] using computable_expApprox.comp hva hp
    · simpa only [left, right, rat] using computable_logApprox.comp hq hp
  have H := computable_fin_cases (i := fun z => z.1.tag)
    (Computable.fst.comp Computable.fst) hc
  simpa only [rational] using H

end BalancedTransport.Effectivity.NumericOp
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity OAI.BalancedTransport.Effectivity.NumericOp


theorem solution : type_of% @_root_.OAI.BalancedTransport.Effectivity.NumericOp.computable_rational := @_root_.OAI.BalancedTransport.Effectivity.NumericOp.computable_rational
