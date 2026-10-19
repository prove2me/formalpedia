-- Prove2me | solution 1 for OAI.BalancedTransport.Effectivity.computable_rat_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:06:38.394223+00:00
-- url     : https://prove2.me/submissions/c06cc6c7-d141-4cc7-bed8-f601bc277263

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/RationalAlgorithms.lean:L28-L41
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Effectivity.computable_rat_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.RationalAlgorithms ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity

lemma primrec_int_nonneg : PrimrecPred (fun z : ℤ => 0 ≤ z) := by
  refine ⟨inferInstance, (primrec_int_cases Primrec.id (Primrec.const true).to₂
    (Primrec.const false).to₂).of_eq ?_⟩
  intro z
  cases z with
  | ofNat n => cases n <;> rfl
  | negSucc n => rfl

lemma primrec_int_le : PrimrecRel ((· ≤ ·) : ℤ → ℤ → Prop) := by
  exact (primrec_int_nonneg.comp
    (primrec_int_add.comp Primrec.snd (primrec_int_neg.comp Primrec.fst))).of_eq
    (fun p => by simp only [← sub_eq_add_neg, sub_nonneg])

lemma computable_rat_le : Computable₂ (fun a b : ℚ => decide (a ≤ b)) := by
  have ha : Computable (fun p : ℚ × ℚ => p.1.num * (p.2.den : ℤ)) :=
    primrec_int_mul.to_comp.comp (computable_rat_num.comp Computable.fst)
      ((primrec_int_ofNat.to_comp.comp computable_rat_den).comp Computable.snd)
  have hb : Computable (fun p : ℚ × ℚ => p.2.num * (p.1.den : ℤ)) :=
    primrec_int_mul.to_comp.comp (computable_rat_num.comp Computable.snd)
      ((primrec_int_ofNat.to_comp.comp computable_rat_den).comp Computable.fst)
  refine ((primrec_int_le.decide.to_comp).comp ha hb).of_eq ?_
  intro ⟨a,b⟩
  have he : a.num * (b.den : ℤ) ≤ b.num * (a.den : ℤ) ↔ a ≤ b := by
    simpa only [Rat.num_divInt_den] using
      (Rat.divInt_le_divInt (a := a.num) (c := b.num) (by exact_mod_cast a.pos : (0 : ℤ) < a.den)
        (by exact_mod_cast b.pos : (0 : ℤ) < b.den)).symm
  simp only [he]

end BalancedTransport.Effectivity
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity


theorem solution : type_of% @_root_.OAI.BalancedTransport.Effectivity.computable_rat_le := @_root_.OAI.BalancedTransport.Effectivity.computable_rat_le
