-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval716_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:48:42.380076+00:00
-- url     : https://prove2.me/submissions/80feec81-ad61-4e74-9aec-98806f076495

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E122
import Definitions.Def_OAIQ106E136
import Definitions.Def_OAIQ106E137
import Definitions.Def_OAIQ106E139

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_CompareMerge
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse collection needs only a computable comparison, not order axioms.
The comparison changes the representation but never its real evaluation. -/
namespace MUB6.Certificate.Integer.Sparse

variable {ι : Type*} [DecidableEq ι]

theorem eval_mergeByFuel (less : ι → ι → Bool) (fuel : ℕ)
    (a b : Sparse ι) (x : ι → ℝ) :
    eval (mergeByFuel less fuel a b) x = eval a x + eval b x := by
  induction fuel generalizing a b with
  | zero => simp [mergeByFuel]
  | succ fuel ih =>
    cases a with
    | nil => simp [mergeByFuel]
    | cons a as =>
      cases b with
      | nil => simp [mergeByFuel]
      | cons b bs =>
        simp only [mergeByFuel]
        split_ifs with hlt heq hz
        · simp only [eval_cons, ih]
          ring
        · simp only [ih, eval_cons]
          have hc : (a.2 : ℝ) + (b.2 : ℝ) = 0 := by exact_mod_cast hz
          have hcx := congrArg (fun z : ℝ => z * x b.1) hc
          simp only [add_mul, zero_mul] at hcx
          rw [heq]
          linarith
        · simp only [eval_cons, ih, Int.cast_add]
          rw [heq]
          ring
        · simp only [eval_cons, ih]
          ring

@[simp] theorem eval_mergeBy (less : ι → ι → Bool) (a b : Sparse ι) (x : ι → ℝ) :
    eval (mergeBy less a b) x = eval a x + eval b x := eval_mergeByFuel _ _ _ _ _

end MUB6.Certificate.Integer.Sparse

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node640 node640Labels = Sparse.eval nodeValue640 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 640) = mixedMoment B node640 node640Labels := rfl
  simpa [nodeValue640, Sparse.eval] using hc.symm

theorem sound641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node641 node641Labels = Sparse.eval nodeValue641 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 641) = mixedMoment B node641 node641Labels := rfl
  simpa [nodeValue641, Sparse.eval] using hc.symm

theorem sound642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node642 node642Labels = Sparse.eval nodeValue642 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 642) = mixedMoment B node642 node642Labels := rfl
  simpa [nodeValue642, Sparse.eval] using hc.symm

theorem sound643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node643 node643Labels = Sparse.eval nodeValue643 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 643) = mixedMoment B node643 node643Labels := rfl
  simpa [nodeValue643, Sparse.eval] using hc.symm

theorem sound653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node653 node653Labels = Sparse.eval nodeValue653 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 653) = mixedMoment B node653 node653Labels := rfl
  simpa [nodeValue653, Sparse.eval] using hc.symm

theorem sound654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node654 node654Labels = Sparse.eval nodeValue654 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 654) = mixedMoment B node654 node654Labels := rfl
  simpa [nodeValue654, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node909 node909Labels = Sparse.eval nodeValue909 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 909) = mixedMoment B node909 node909Labels := rfl
  simpa [nodeValue909, Sparse.eval] using hc.symm

theorem sound911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node911 node911Labels = Sparse.eval nodeValue911 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 911) = mixedMoment B node911 node911Labels := rfl
  simpa [nodeValue911, Sparse.eval] using hc.symm

theorem sound914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node914 node914Labels = Sparse.eval nodeValue914 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 914) = mixedMoment B node914 node914Labels := rfl
  simpa [nodeValue914, Sparse.eval] using hc.symm

theorem sound922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node922 node922Labels = Sparse.eval nodeValue922 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 922) = mixedMoment B node922 node922Labels := rfl
  simpa [nodeValue922, Sparse.eval] using hc.symm

theorem sound929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node929 node929Labels = Sparse.eval nodeValue929 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 929) = mixedMoment B node929 node929Labels := rfl
  simpa [nodeValue929, Sparse.eval] using hc.symm

theorem sound930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node930 node930Labels = Sparse.eval nodeValue930 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 930) = mixedMoment B node930 node930Labels := rfl
  simpa [nodeValue930, Sparse.eval] using hc.symm

theorem sound931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node931 node931Labels = Sparse.eval nodeValue931 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 931) = mixedMoment B node931 node931Labels := rfl
  simpa [nodeValue931, Sparse.eval] using hc.symm

theorem sound932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node932 node932Labels = Sparse.eval nodeValue932 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 932) = mixedMoment B node932 node932Labels := rfl
  simpa [nodeValue932, Sparse.eval] using hc.symm

theorem sound933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node933 node933Labels = Sparse.eval nodeValue933 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 933) = mixedMoment B node933 node933Labels := rfl
  simpa [nodeValue933, Sparse.eval] using hc.symm

theorem sound934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node934 node934Labels = Sparse.eval nodeValue934 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 934) = mixedMoment B node934 node934Labels := rfl
  simpa [nodeValue934, Sparse.eval] using hc.symm

theorem sound936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node936 node936Labels = Sparse.eval nodeValue936 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 936) = mixedMoment B node936 node936Labels := rfl
  simpa [nodeValue936, Sparse.eval] using hc.symm

theorem sound937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node937 node937Labels = Sparse.eval nodeValue937 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 937) = mixedMoment B node937 node937Labels := rfl
  simpa [nodeValue937, Sparse.eval] using hc.symm

theorem sound939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node939 node939Labels = Sparse.eval nodeValue939 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 939) = mixedMoment B node939 node939Labels := rfl
  simpa [nodeValue939, Sparse.eval] using hc.symm

theorem sound940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node940 node940Labels = Sparse.eval nodeValue940 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 940) = mixedMoment B node940 node940Labels := rfl
  simpa [nodeValue940, Sparse.eval] using hc.symm

theorem sound944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node944 node944Labels = Sparse.eval nodeValue944 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 944) = mixedMoment B node944 node944Labels := rfl
  simpa [nodeValue944, Sparse.eval] using hc.symm

theorem sound945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node945 node945Labels = Sparse.eval nodeValue945 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 945) = mixedMoment B node945 node945Labels := rfl
  simpa [nodeValue945, Sparse.eval] using hc.symm

theorem sound946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node946 node946Labels = Sparse.eval nodeValue946 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 946) = mixedMoment B node946 node946Labels := rfl
  simpa [nodeValue946, Sparse.eval] using hc.symm

theorem sound949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node949 node949Labels = Sparse.eval nodeValue949 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 949) = mixedMoment B node949 node949Labels := rfl
  simpa [nodeValue949, Sparse.eval] using hc.symm

theorem sound950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node950 node950Labels = Sparse.eval nodeValue950 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 950) = mixedMoment B node950 node950Labels := rfl
  simpa [nodeValue950, Sparse.eval] using hc.symm

theorem sound951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node951 node951Labels = Sparse.eval nodeValue951 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 951) = mixedMoment B node951 node951Labels := rfl
  simpa [nodeValue951, Sparse.eval] using hc.symm

theorem sound952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node952 node952Labels = Sparse.eval nodeValue952 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 952) = mixedMoment B node952 node952Labels := rfl
  simpa [nodeValue952, Sparse.eval] using hc.symm

theorem sound953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node953 node953Labels = Sparse.eval nodeValue953 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 953) = mixedMoment B node953 node953Labels := rfl
  simpa [nodeValue953, Sparse.eval] using hc.symm

theorem sound954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node954 node954Labels = Sparse.eval nodeValue954 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 954) = mixedMoment B node954 node954Labels := rfl
  simpa [nodeValue954, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1024 node1024Labels = Sparse.eval nodeValue1024 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1024) = mixedMoment B node1024 node1024Labels := rfl
  simpa [nodeValue1024, Sparse.eval] using hc.symm

theorem sound1027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1027 node1027Labels = Sparse.eval nodeValue1027 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1027) = mixedMoment B node1027 node1027Labels := rfl
  simpa [nodeValue1027, Sparse.eval] using hc.symm

theorem sound1039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1039 node1039Labels = Sparse.eval nodeValue1039 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1039) = mixedMoment B node1039 node1039Labels := rfl
  simpa [nodeValue1039, Sparse.eval] using hc.symm

theorem sound1041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1041 node1041Labels = Sparse.eval nodeValue1041 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1041) = mixedMoment B node1041 node1041Labels := rfl
  simpa [nodeValue1041, Sparse.eval] using hc.symm

theorem sound1044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1044 node1044Labels = Sparse.eval nodeValue1044 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1044) = mixedMoment B node1044 node1044Labels := rfl
  simpa [nodeValue1044, Sparse.eval] using hc.symm

theorem sound1046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1046 node1046Labels = Sparse.eval nodeValue1046 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1046) = mixedMoment B node1046 node1046Labels := rfl
  simpa [nodeValue1046, Sparse.eval] using hc.symm

theorem sound1047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1047 node1047Labels = Sparse.eval nodeValue1047 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1047) = mixedMoment B node1047 node1047Labels := rfl
  simpa [nodeValue1047, Sparse.eval] using hc.symm

theorem sound1049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1049 node1049Labels = Sparse.eval nodeValue1049 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1049) = mixedMoment B node1049 node1049Labels := rfl
  simpa [nodeValue1049, Sparse.eval] using hc.symm

theorem sound1050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1050 node1050Labels = Sparse.eval nodeValue1050 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1050) = mixedMoment B node1050 node1050Labels := rfl
  simpa [nodeValue1050, Sparse.eval] using hc.symm

theorem sound1051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1051 node1051Labels = Sparse.eval nodeValue1051 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1051) = mixedMoment B node1051 node1051Labels := rfl
  simpa [nodeValue1051, Sparse.eval] using hc.symm

theorem sound1058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1058 node1058Labels = Sparse.eval nodeValue1058 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1058) = mixedMoment B node1058 node1058Labels := rfl
  simpa [nodeValue1058, Sparse.eval] using hc.symm

theorem sound1061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1061 node1061Labels = Sparse.eval nodeValue1061 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1061) = mixedMoment B node1061 node1061Labels := rfl
  simpa [nodeValue1061, Sparse.eval] using hc.symm

theorem sound1063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1063 node1063Labels = Sparse.eval nodeValue1063 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1063) = mixedMoment B node1063 node1063Labels := rfl
  simpa [nodeValue1063, Sparse.eval] using hc.symm

theorem sound1064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1064 node1064Labels = Sparse.eval nodeValue1064 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1064) = mixedMoment B node1064 node1064Labels := rfl
  simpa [nodeValue1064, Sparse.eval] using hc.symm

theorem sound1087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1087 node1087Labels = Sparse.eval nodeValue1087 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1087) = mixedMoment B node1087 node1087Labels := rfl
  simpa [nodeValue1087, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1091 node1091Labels = Sparse.eval nodeValue1091 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1091) = mixedMoment B node1091 node1091Labels := rfl
  simpa [nodeValue1091, Sparse.eval] using hc.symm

theorem sound1094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1094 node1094Labels = Sparse.eval nodeValue1094 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1094) = mixedMoment B node1094 node1094Labels := rfl
  simpa [nodeValue1094, Sparse.eval] using hc.symm

theorem sound1111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1111 node1111Labels = Sparse.eval nodeValue1111 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1111) = mixedMoment B node1111 node1111Labels := rfl
  simpa [nodeValue1111, Sparse.eval] using hc.symm

theorem sound1112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1112 node1112Labels = Sparse.eval nodeValue1112 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1112) = mixedMoment B node1112 node1112Labels := rfl
  simpa [nodeValue1112, Sparse.eval] using hc.symm

theorem sound1113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1113 node1113Labels = Sparse.eval nodeValue1113 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1113) = mixedMoment B node1113 node1113Labels := rfl
  simpa [nodeValue1113, Sparse.eval] using hc.symm

theorem sound1115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1115 node1115Labels = Sparse.eval nodeValue1115 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1115) = mixedMoment B node1115 node1115Labels := rfl
  simpa [nodeValue1115, Sparse.eval] using hc.symm

theorem sound1116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1116 node1116Labels = Sparse.eval nodeValue1116 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1116) = mixedMoment B node1116 node1116Labels := rfl
  simpa [nodeValue1116, Sparse.eval] using hc.symm

theorem sound1117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1117 node1117Labels = Sparse.eval nodeValue1117 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1117) = mixedMoment B node1117 node1117Labels := rfl
  simpa [nodeValue1117, Sparse.eval] using hc.symm

theorem sound1118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1118 node1118Labels = Sparse.eval nodeValue1118 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1118) = mixedMoment B node1118 node1118Labels := rfl
  simpa [nodeValue1118, Sparse.eval] using hc.symm

theorem sound1119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1119 node1119Labels = Sparse.eval nodeValue1119 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1119) = mixedMoment B node1119 node1119Labels := rfl
  simpa [nodeValue1119, Sparse.eval] using hc.symm

theorem sound1120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1120 node1120Labels = Sparse.eval nodeValue1120 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1120) = mixedMoment B node1120 node1120Labels := rfl
  simpa [nodeValue1120, Sparse.eval] using hc.symm

theorem sound1121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1121 node1121Labels = Sparse.eval nodeValue1121 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1121) = mixedMoment B node1121 node1121Labels := rfl
  simpa [nodeValue1121, Sparse.eval] using hc.symm

theorem sound1125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1125 node1125Labels = Sparse.eval nodeValue1125 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1125) = mixedMoment B node1125 node1125Labels := rfl
  simpa [nodeValue1125, Sparse.eval] using hc.symm

theorem sound1126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1126 node1126Labels = Sparse.eval nodeValue1126 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1126) = mixedMoment B node1126 node1126Labels := rfl
  simpa [nodeValue1126, Sparse.eval] using hc.symm

theorem sound1128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1128 node1128Labels = Sparse.eval nodeValue1128 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1128) = mixedMoment B node1128 node1128Labels := rfl
  simpa [nodeValue1128, Sparse.eval] using hc.symm

theorem sound1129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1129 node1129Labels = Sparse.eval nodeValue1129 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1129) = mixedMoment B node1129 node1129Labels := rfl
  simpa [nodeValue1129, Sparse.eval] using hc.symm

theorem sound1130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1130 node1130Labels = Sparse.eval nodeValue1130 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1130) = mixedMoment B node1130 node1130Labels := rfl
  simpa [nodeValue1130, Sparse.eval] using hc.symm

theorem sound1131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1131 node1131Labels = Sparse.eval nodeValue1131 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1131) = mixedMoment B node1131 node1131Labels := rfl
  simpa [nodeValue1131, Sparse.eval] using hc.symm

theorem sound1132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1132 node1132Labels = Sparse.eval nodeValue1132 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1132) = mixedMoment B node1132 node1132Labels := rfl
  simpa [nodeValue1132, Sparse.eval] using hc.symm

theorem sound1133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1133 node1133Labels = Sparse.eval nodeValue1133 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1133) = mixedMoment B node1133 node1133Labels := rfl
  simpa [nodeValue1133, Sparse.eval] using hc.symm

theorem sound1134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1134 node1134Labels = Sparse.eval nodeValue1134 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1134) = mixedMoment B node1134 node1134Labels := rfl
  simpa [nodeValue1134, Sparse.eval] using hc.symm

theorem sound1135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1135 node1135Labels = Sparse.eval nodeValue1135 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1135) = mixedMoment B node1135 node1135Labels := rfl
  simpa [nodeValue1135, Sparse.eval] using hc.symm

theorem sound1137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1137 node1137Labels = Sparse.eval nodeValue1137 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1137) = mixedMoment B node1137 node1137Labels := rfl
  simpa [nodeValue1137, Sparse.eval] using hc.symm

theorem sound1138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1138 node1138Labels = Sparse.eval nodeValue1138 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1138) = mixedMoment B node1138 node1138Labels := rfl
  simpa [nodeValue1138, Sparse.eval] using hc.symm

theorem sound1139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1139 node1139Labels = Sparse.eval nodeValue1139 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1139) = mixedMoment B node1139 node1139Labels := rfl
  simpa [nodeValue1139, Sparse.eval] using hc.symm

theorem sound1140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1140 node1140Labels = Sparse.eval nodeValue1140 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1140) = mixedMoment B node1140 node1140Labels := rfl
  simpa [nodeValue1140, Sparse.eval] using hc.symm

theorem sound1141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1141 node1141Labels = Sparse.eval nodeValue1141 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1141) = mixedMoment B node1141 node1141Labels := rfl
  simpa [nodeValue1141, Sparse.eval] using hc.symm

theorem sound1142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1142 node1142Labels = Sparse.eval nodeValue1142 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1142) = mixedMoment B node1142 node1142Labels := rfl
  simpa [nodeValue1142, Sparse.eval] using hc.symm

theorem sound1143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1143 node1143Labels = Sparse.eval nodeValue1143 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1143) = mixedMoment B node1143 node1143Labels := rfl
  simpa [nodeValue1143, Sparse.eval] using hc.symm

theorem sound1144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1144 node1144Labels = Sparse.eval nodeValue1144 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1144) = mixedMoment B node1144 node1144Labels := rfl
  simpa [nodeValue1144, Sparse.eval] using hc.symm

theorem sound1145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1145 node1145Labels = Sparse.eval nodeValue1145 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1145) = mixedMoment B node1145 node1145Labels := rfl
  simpa [nodeValue1145, Sparse.eval] using hc.symm

theorem sound1146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1146 node1146Labels = Sparse.eval nodeValue1146 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1146) = mixedMoment B node1146 node1146Labels := rfl
  simpa [nodeValue1146, Sparse.eval] using hc.symm

theorem sound1148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1148 node1148Labels = Sparse.eval nodeValue1148 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1148) = mixedMoment B node1148 node1148Labels := rfl
  simpa [nodeValue1148, Sparse.eval] using hc.symm

theorem sound1149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1149 node1149Labels = Sparse.eval nodeValue1149 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1149) = mixedMoment B node1149 node1149Labels := rfl
  simpa [nodeValue1149, Sparse.eval] using hc.symm

theorem sound1150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1150 node1150Labels = Sparse.eval nodeValue1150 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1150) = mixedMoment B node1150 node1150Labels := rfl
  simpa [nodeValue1150, Sparse.eval] using hc.symm

theorem sound1151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1151 node1151Labels = Sparse.eval nodeValue1151 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1151) = mixedMoment B node1151 node1151Labels := rfl
  simpa [nodeValue1151, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1153 node1153Labels = Sparse.eval nodeValue1153 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1153) = mixedMoment B node1153 node1153Labels := rfl
  simpa [nodeValue1153, Sparse.eval] using hc.symm

theorem sound1155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1155 node1155Labels = Sparse.eval nodeValue1155 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1155) = mixedMoment B node1155 node1155Labels := rfl
  simpa [nodeValue1155, Sparse.eval] using hc.symm

theorem sound1156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1156 node1156Labels = Sparse.eval nodeValue1156 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1156) = mixedMoment B node1156 node1156Labels := rfl
  simpa [nodeValue1156, Sparse.eval] using hc.symm

theorem sound1159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1159 node1159Labels = Sparse.eval nodeValue1159 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1159) = mixedMoment B node1159 node1159Labels := rfl
  simpa [nodeValue1159, Sparse.eval] using hc.symm

theorem sound1160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1160 node1160Labels = Sparse.eval nodeValue1160 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1160) = mixedMoment B node1160 node1160Labels := rfl
  simpa [nodeValue1160, Sparse.eval] using hc.symm

theorem sound1169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1169 node1169Labels = Sparse.eval nodeValue1169 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1169) = mixedMoment B node1169 node1169Labels := rfl
  simpa [nodeValue1169, Sparse.eval] using hc.symm

theorem sound1171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1171 node1171Labels = Sparse.eval nodeValue1171 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1171) = mixedMoment B node1171 node1171Labels := rfl
  simpa [nodeValue1171, Sparse.eval] using hc.symm

theorem sound1174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1174 node1174Labels = Sparse.eval nodeValue1174 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1174) = mixedMoment B node1174 node1174Labels := rfl
  simpa [nodeValue1174, Sparse.eval] using hc.symm

theorem sound1212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1212 node1212Labels = Sparse.eval nodeValue1212 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1212) = mixedMoment B node1212 node1212Labels := rfl
  simpa [nodeValue1212, Sparse.eval] using hc.symm

theorem sound1215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1215 node1215Labels = Sparse.eval nodeValue1215 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1215) = mixedMoment B node1215 node1215Labels := rfl
  simpa [nodeValue1215, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1216 node1216Labels = Sparse.eval nodeValue1216 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1216) = mixedMoment B node1216 node1216Labels := rfl
  simpa [nodeValue1216, Sparse.eval] using hc.symm

theorem sound1217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1217 node1217Labels = Sparse.eval nodeValue1217 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1217) = mixedMoment B node1217 node1217Labels := rfl
  simpa [nodeValue1217, Sparse.eval] using hc.symm

theorem sound1219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1219 node1219Labels = Sparse.eval nodeValue1219 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1219) = mixedMoment B node1219 node1219Labels := rfl
  simpa [nodeValue1219, Sparse.eval] using hc.symm

theorem sound1221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1221 node1221Labels = Sparse.eval nodeValue1221 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1221) = mixedMoment B node1221 node1221Labels := rfl
  simpa [nodeValue1221, Sparse.eval] using hc.symm

theorem sound1233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1233 node1233Labels = Sparse.eval nodeValue1233 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1233) = mixedMoment B node1233 node1233Labels := rfl
  simpa [nodeValue1233, Sparse.eval] using hc.symm

theorem sound1234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1234 node1234Labels = Sparse.eval nodeValue1234 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1234) = mixedMoment B node1234 node1234Labels := rfl
  simpa [nodeValue1234, Sparse.eval] using hc.symm

theorem sound1235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1235 node1235Labels = Sparse.eval nodeValue1235 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1235) = mixedMoment B node1235 node1235Labels := rfl
  simpa [nodeValue1235, Sparse.eval] using hc.symm

theorem sound1236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1236 node1236Labels = Sparse.eval nodeValue1236 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1236) = mixedMoment B node1236 node1236Labels := rfl
  simpa [nodeValue1236, Sparse.eval] using hc.symm

theorem sound1237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1237 node1237Labels = Sparse.eval nodeValue1237 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1237) = mixedMoment B node1237 node1237Labels := rfl
  simpa [nodeValue1237, Sparse.eval] using hc.symm

theorem sound1239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1239 node1239Labels = Sparse.eval nodeValue1239 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1239) = mixedMoment B node1239 node1239Labels := rfl
  simpa [nodeValue1239, Sparse.eval] using hc.symm

theorem sound1240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1240 node1240Labels = Sparse.eval nodeValue1240 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1240) = mixedMoment B node1240 node1240Labels := rfl
  simpa [nodeValue1240, Sparse.eval] using hc.symm

theorem sound1241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1241 node1241Labels = Sparse.eval nodeValue1241 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1241) = mixedMoment B node1241 node1241Labels := rfl
  simpa [nodeValue1241, Sparse.eval] using hc.symm

theorem sound1242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1242 node1242Labels = Sparse.eval nodeValue1242 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1242) = mixedMoment B node1242 node1242Labels := rfl
  simpa [nodeValue1242, Sparse.eval] using hc.symm

theorem sound1243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1243 node1243Labels = Sparse.eval nodeValue1243 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1243) = mixedMoment B node1243 node1243Labels := rfl
  simpa [nodeValue1243, Sparse.eval] using hc.symm

theorem sound1245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1245 node1245Labels = Sparse.eval nodeValue1245 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1245) = mixedMoment B node1245 node1245Labels := rfl
  simpa [nodeValue1245, Sparse.eval] using hc.symm

theorem sound1246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1246 node1246Labels = Sparse.eval nodeValue1246 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1246) = mixedMoment B node1246 node1246Labels := rfl
  simpa [nodeValue1246, Sparse.eval] using hc.symm

theorem sound1260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1260 node1260Labels = Sparse.eval nodeValue1260 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1260) = mixedMoment B node1260 node1260Labels := rfl
  simpa [nodeValue1260, Sparse.eval] using hc.symm

theorem sound1261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1261 node1261Labels = Sparse.eval nodeValue1261 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1261) = mixedMoment B node1261 node1261Labels := rfl
  simpa [nodeValue1261, Sparse.eval] using hc.symm

theorem sound1262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1262 node1262Labels = Sparse.eval nodeValue1262 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1262) = mixedMoment B node1262 node1262Labels := rfl
  simpa [nodeValue1262, Sparse.eval] using hc.symm

theorem sound1264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1264 node1264Labels = Sparse.eval nodeValue1264 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1264) = mixedMoment B node1264 node1264Labels := rfl
  simpa [nodeValue1264, Sparse.eval] using hc.symm

theorem sound1270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1270 node1270Labels = Sparse.eval nodeValue1270 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1270) = mixedMoment B node1270 node1270Labels := rfl
  simpa [nodeValue1270, Sparse.eval] using hc.symm

theorem sound1273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1273 node1273Labels = Sparse.eval nodeValue1273 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1273) = mixedMoment B node1273 node1273Labels := rfl
  simpa [nodeValue1273, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1291 node1291Labels = Sparse.eval nodeValue1291 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1291) = mixedMoment B node1291 node1291Labels := rfl
  simpa [nodeValue1291, Sparse.eval] using hc.symm

theorem sound1292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1292 node1292Labels = Sparse.eval nodeValue1292 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1292) = mixedMoment B node1292 node1292Labels := rfl
  simpa [nodeValue1292, Sparse.eval] using hc.symm

theorem sound1293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1293 node1293Labels = Sparse.eval nodeValue1293 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1293) = mixedMoment B node1293 node1293Labels := rfl
  simpa [nodeValue1293, Sparse.eval] using hc.symm

theorem sound1294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1294 node1294Labels = Sparse.eval nodeValue1294 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1294) = mixedMoment B node1294 node1294Labels := rfl
  simpa [nodeValue1294, Sparse.eval] using hc.symm

theorem sound1295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1295 node1295Labels = Sparse.eval nodeValue1295 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1295) = mixedMoment B node1295 node1295Labels := rfl
  simpa [nodeValue1295, Sparse.eval] using hc.symm

theorem sound1297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1297 node1297Labels = Sparse.eval nodeValue1297 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1297) = mixedMoment B node1297 node1297Labels := rfl
  simpa [nodeValue1297, Sparse.eval] using hc.symm

theorem sound1306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1306 node1306Labels = Sparse.eval nodeValue1306 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1306) = mixedMoment B node1306 node1306Labels := rfl
  simpa [nodeValue1306, Sparse.eval] using hc.symm

theorem sound1310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1310 node1310Labels = Sparse.eval nodeValue1310 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1310) = mixedMoment B node1310 node1310Labels := rfl
  simpa [nodeValue1310, Sparse.eval] using hc.symm

theorem sound1314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1314 node1314Labels = Sparse.eval nodeValue1314 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1314) = mixedMoment B node1314 node1314Labels := rfl
  simpa [nodeValue1314, Sparse.eval] using hc.symm

theorem sound1315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1315 node1315Labels = Sparse.eval nodeValue1315 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1315) = mixedMoment B node1315 node1315Labels := rfl
  simpa [nodeValue1315, Sparse.eval] using hc.symm

theorem sound1316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1316 node1316Labels = Sparse.eval nodeValue1316 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1316) = mixedMoment B node1316 node1316Labels := rfl
  simpa [nodeValue1316, Sparse.eval] using hc.symm

theorem sound1317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1317 node1317Labels = Sparse.eval nodeValue1317 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1317) = mixedMoment B node1317 node1317Labels := rfl
  simpa [nodeValue1317, Sparse.eval] using hc.symm

theorem sound1318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1318 node1318Labels = Sparse.eval nodeValue1318 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1318) = mixedMoment B node1318 node1318Labels := rfl
  simpa [nodeValue1318, Sparse.eval] using hc.symm

theorem sound1319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1319 node1319Labels = Sparse.eval nodeValue1319 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1319) = mixedMoment B node1319 node1319Labels := rfl
  simpa [nodeValue1319, Sparse.eval] using hc.symm

theorem sound1320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1320 node1320Labels = Sparse.eval nodeValue1320 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1320) = mixedMoment B node1320 node1320Labels := rfl
  simpa [nodeValue1320, Sparse.eval] using hc.symm

theorem sound1321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1321 node1321Labels = Sparse.eval nodeValue1321 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1321) = mixedMoment B node1321 node1321Labels := rfl
  simpa [nodeValue1321, Sparse.eval] using hc.symm

theorem sound1322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1322 node1322Labels = Sparse.eval nodeValue1322 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1322) = mixedMoment B node1322 node1322Labels := rfl
  simpa [nodeValue1322, Sparse.eval] using hc.symm

theorem sound1323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1323 node1323Labels = Sparse.eval nodeValue1323 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1323) = mixedMoment B node1323 node1323Labels := rfl
  simpa [nodeValue1323, Sparse.eval] using hc.symm

theorem sound1324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1324 node1324Labels = Sparse.eval nodeValue1324 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1324) = mixedMoment B node1324 node1324Labels := rfl
  simpa [nodeValue1324, Sparse.eval] using hc.symm

theorem sound1325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1325 node1325Labels = Sparse.eval nodeValue1325 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1325) = mixedMoment B node1325 node1325Labels := rfl
  simpa [nodeValue1325, Sparse.eval] using hc.symm

theorem sound1326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1326 node1326Labels = Sparse.eval nodeValue1326 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1326) = mixedMoment B node1326 node1326Labels := rfl
  simpa [nodeValue1326, Sparse.eval] using hc.symm

theorem sound1327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1327 node1327Labels = Sparse.eval nodeValue1327 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1327) = mixedMoment B node1327 node1327Labels := rfl
  simpa [nodeValue1327, Sparse.eval] using hc.symm

theorem sound1328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1328 node1328Labels = Sparse.eval nodeValue1328 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1328) = mixedMoment B node1328 node1328Labels := rfl
  simpa [nodeValue1328, Sparse.eval] using hc.symm

theorem sound1330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1330 node1330Labels = Sparse.eval nodeValue1330 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1330) = mixedMoment B node1330 node1330Labels := rfl
  simpa [nodeValue1330, Sparse.eval] using hc.symm

theorem sound1332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1332 node1332Labels = Sparse.eval nodeValue1332 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1332) = mixedMoment B node1332 node1332Labels := rfl
  simpa [nodeValue1332, Sparse.eval] using hc.symm

theorem sound1333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1333 node1333Labels = Sparse.eval nodeValue1333 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1333) = mixedMoment B node1333 node1333Labels := rfl
  simpa [nodeValue1333, Sparse.eval] using hc.symm

theorem sound1334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1334 node1334Labels = Sparse.eval nodeValue1334 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1334) = mixedMoment B node1334 node1334Labels := rfl
  simpa [nodeValue1334, Sparse.eval] using hc.symm

theorem sound1335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1335 node1335Labels = Sparse.eval nodeValue1335 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1335) = mixedMoment B node1335 node1335Labels := rfl
  simpa [nodeValue1335, Sparse.eval] using hc.symm

theorem sound1336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1336 node1336Labels = Sparse.eval nodeValue1336 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1336) = mixedMoment B node1336 node1336Labels := rfl
  simpa [nodeValue1336, Sparse.eval] using hc.symm

theorem sound1337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1337 node1337Labels = Sparse.eval nodeValue1337 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1337) = mixedMoment B node1337 node1337Labels := rfl
  simpa [nodeValue1337, Sparse.eval] using hc.symm

theorem sound1338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1338 node1338Labels = Sparse.eval nodeValue1338 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1338) = mixedMoment B node1338 node1338Labels := rfl
  simpa [nodeValue1338, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1348 node1348Labels = Sparse.eval nodeValue1348 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1348) = mixedMoment B node1348 node1348Labels := rfl
  simpa [nodeValue1348, Sparse.eval] using hc.symm

theorem sound1366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1366 node1366Labels = Sparse.eval nodeValue1366 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1366) = mixedMoment B node1366 node1366Labels := rfl
  simpa [nodeValue1366, Sparse.eval] using hc.symm

theorem sound1367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1367 node1367Labels = Sparse.eval nodeValue1367 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1367) = mixedMoment B node1367 node1367Labels := rfl
  simpa [nodeValue1367, Sparse.eval] using hc.symm

theorem sound1369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1369 node1369Labels = Sparse.eval nodeValue1369 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1369) = mixedMoment B node1369 node1369Labels := rfl
  simpa [nodeValue1369, Sparse.eval] using hc.symm

theorem sound1370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1370 node1370Labels = Sparse.eval nodeValue1370 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1370) = mixedMoment B node1370 node1370Labels := rfl
  simpa [nodeValue1370, Sparse.eval] using hc.symm

theorem sound1372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1372 node1372Labels = Sparse.eval nodeValue1372 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1372) = mixedMoment B node1372 node1372Labels := rfl
  simpa [nodeValue1372, Sparse.eval] using hc.symm

theorem sound1375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1375 node1375Labels = Sparse.eval nodeValue1375 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1375) = mixedMoment B node1375 node1375Labels := rfl
  simpa [nodeValue1375, Sparse.eval] using hc.symm

theorem sound1383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1383 node1383Labels = Sparse.eval nodeValue1383 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1383) = mixedMoment B node1383 node1383Labels := rfl
  simpa [nodeValue1383, Sparse.eval] using hc.symm

theorem sound1385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1385 node1385Labels = Sparse.eval nodeValue1385 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1385) = mixedMoment B node1385 node1385Labels := rfl
  simpa [nodeValue1385, Sparse.eval] using hc.symm

theorem sound1388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1388 node1388Labels = Sparse.eval nodeValue1388 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1388) = mixedMoment B node1388 node1388Labels := rfl
  simpa [nodeValue1388, Sparse.eval] using hc.symm

theorem sound1391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1391 node1391Labels = Sparse.eval nodeValue1391 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1391) = mixedMoment B node1391 node1391Labels := rfl
  simpa [nodeValue1391, Sparse.eval] using hc.symm

theorem sound1406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1406 node1406Labels = Sparse.eval nodeValue1406 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1406) = mixedMoment B node1406 node1406Labels := rfl
  simpa [nodeValue1406, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1408 node1408Labels = Sparse.eval nodeValue1408 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1408) = mixedMoment B node1408 node1408Labels := rfl
  simpa [nodeValue1408, Sparse.eval] using hc.symm

theorem sound1435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1435 node1435Labels = Sparse.eval nodeValue1435 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1435) = mixedMoment B node1435 node1435Labels := rfl
  simpa [nodeValue1435, Sparse.eval] using hc.symm

theorem sound1436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1436 node1436Labels = Sparse.eval nodeValue1436 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1436) = mixedMoment B node1436 node1436Labels := rfl
  simpa [nodeValue1436, Sparse.eval] using hc.symm

theorem sound1438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1438 node1438Labels = Sparse.eval nodeValue1438 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1438) = mixedMoment B node1438 node1438Labels := rfl
  simpa [nodeValue1438, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1501 node1501Labels = Sparse.eval nodeValue1501 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1501) = mixedMoment B node1501 node1501Labels := rfl
  simpa [nodeValue1501, Sparse.eval] using hc.symm

theorem sound1502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1502 node1502Labels = Sparse.eval nodeValue1502 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1502) = mixedMoment B node1502 node1502Labels := rfl
  simpa [nodeValue1502, Sparse.eval] using hc.symm

theorem sound1504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1504 node1504Labels = Sparse.eval nodeValue1504 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1504) = mixedMoment B node1504 node1504Labels := rfl
  simpa [nodeValue1504, Sparse.eval] using hc.symm

theorem sound1505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1505 node1505Labels = Sparse.eval nodeValue1505 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1505) = mixedMoment B node1505 node1505Labels := rfl
  simpa [nodeValue1505, Sparse.eval] using hc.symm

theorem sound1508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1508 node1508Labels = Sparse.eval nodeValue1508 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1508) = mixedMoment B node1508 node1508Labels := rfl
  simpa [nodeValue1508, Sparse.eval] using hc.symm

theorem sound1510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1510 node1510Labels = Sparse.eval nodeValue1510 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1510) = mixedMoment B node1510 node1510Labels := rfl
  simpa [nodeValue1510, Sparse.eval] using hc.symm

theorem sound1511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1511 node1511Labels = Sparse.eval nodeValue1511 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1511) = mixedMoment B node1511 node1511Labels := rfl
  simpa [nodeValue1511, Sparse.eval] using hc.symm

theorem sound1512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1512 node1512Labels = Sparse.eval nodeValue1512 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1512) = mixedMoment B node1512 node1512Labels := rfl
  simpa [nodeValue1512, Sparse.eval] using hc.symm

theorem sound1513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1513 node1513Labels = Sparse.eval nodeValue1513 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1513) = mixedMoment B node1513 node1513Labels := rfl
  simpa [nodeValue1513, Sparse.eval] using hc.symm

theorem sound1514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1514 node1514Labels = Sparse.eval nodeValue1514 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1514) = mixedMoment B node1514 node1514Labels := rfl
  simpa [nodeValue1514, Sparse.eval] using hc.symm

theorem sound1515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1515 node1515Labels = Sparse.eval nodeValue1515 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1515) = mixedMoment B node1515 node1515Labels := rfl
  simpa [nodeValue1515, Sparse.eval] using hc.symm

theorem sound1516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1516 node1516Labels = Sparse.eval nodeValue1516 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1516) = mixedMoment B node1516 node1516Labels := rfl
  simpa [nodeValue1516, Sparse.eval] using hc.symm

theorem sound1520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1520 node1520Labels = Sparse.eval nodeValue1520 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1520) = mixedMoment B node1520 node1520Labels := rfl
  simpa [nodeValue1520, Sparse.eval] using hc.symm

theorem sound1522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1522 node1522Labels = Sparse.eval nodeValue1522 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1522) = mixedMoment B node1522 node1522Labels := rfl
  simpa [nodeValue1522, Sparse.eval] using hc.symm

theorem sound1523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1523 node1523Labels = Sparse.eval nodeValue1523 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1523) = mixedMoment B node1523 node1523Labels := rfl
  simpa [nodeValue1523, Sparse.eval] using hc.symm

theorem sound1526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1526 node1526Labels = Sparse.eval nodeValue1526 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1526) = mixedMoment B node1526 node1526Labels := rfl
  simpa [nodeValue1526, Sparse.eval] using hc.symm

theorem sound1528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1528 node1528Labels = Sparse.eval nodeValue1528 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1528) = mixedMoment B node1528 node1528Labels := rfl
  simpa [nodeValue1528, Sparse.eval] using hc.symm

theorem sound1529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1529 node1529Labels = Sparse.eval nodeValue1529 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1529) = mixedMoment B node1529 node1529Labels := rfl
  simpa [nodeValue1529, Sparse.eval] using hc.symm

theorem sound1530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1530 node1530Labels = Sparse.eval nodeValue1530 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1530) = mixedMoment B node1530 node1530Labels := rfl
  simpa [nodeValue1530, Sparse.eval] using hc.symm

theorem sound1531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1531 node1531Labels = Sparse.eval nodeValue1531 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1531) = mixedMoment B node1531 node1531Labels := rfl
  simpa [nodeValue1531, Sparse.eval] using hc.symm

theorem sound1532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1532 node1532Labels = Sparse.eval nodeValue1532 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1532) = mixedMoment B node1532 node1532Labels := rfl
  simpa [nodeValue1532, Sparse.eval] using hc.symm

theorem sound1533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1533 node1533Labels = Sparse.eval nodeValue1533 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1533) = mixedMoment B node1533 node1533Labels := rfl
  simpa [nodeValue1533, Sparse.eval] using hc.symm

theorem sound1534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1534 node1534Labels = Sparse.eval nodeValue1534 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1534) = mixedMoment B node1534 node1534Labels := rfl
  simpa [nodeValue1534, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1540 node1540Labels = Sparse.eval nodeValue1540 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1540) = mixedMoment B node1540 node1540Labels := rfl
  simpa [nodeValue1540, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1667 node1667Labels = Sparse.eval nodeValue1667 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1667) = mixedMoment B node1667 node1667Labels := rfl
  simpa [nodeValue1667, Sparse.eval] using hc.symm

theorem sound1668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1668 node1668Labels = Sparse.eval nodeValue1668 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1668) = mixedMoment B node1668 node1668Labels := rfl
  simpa [nodeValue1668, Sparse.eval] using hc.symm

theorem sound1670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1670 node1670Labels = Sparse.eval nodeValue1670 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1670) = mixedMoment B node1670 node1670Labels := rfl
  simpa [nodeValue1670, Sparse.eval] using hc.symm

theorem sound1672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1672 node1672Labels = Sparse.eval nodeValue1672 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1672) = mixedMoment B node1672 node1672Labels := rfl
  simpa [nodeValue1672, Sparse.eval] using hc.symm

theorem sound1676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1676 node1676Labels = Sparse.eval nodeValue1676 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1676) = mixedMoment B node1676 node1676Labels := rfl
  simpa [nodeValue1676, Sparse.eval] using hc.symm

theorem sound1678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1678 node1678Labels = Sparse.eval nodeValue1678 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1678) = mixedMoment B node1678 node1678Labels := rfl
  simpa [nodeValue1678, Sparse.eval] using hc.symm

theorem sound1679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1679 node1679Labels = Sparse.eval nodeValue1679 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1679) = mixedMoment B node1679 node1679Labels := rfl
  simpa [nodeValue1679, Sparse.eval] using hc.symm

theorem sound1682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1682 node1682Labels = Sparse.eval nodeValue1682 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1682) = mixedMoment B node1682 node1682Labels := rfl
  simpa [nodeValue1682, Sparse.eval] using hc.symm

theorem sound1684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1684 node1684Labels = Sparse.eval nodeValue1684 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1684) = mixedMoment B node1684 node1684Labels := rfl
  simpa [nodeValue1684, Sparse.eval] using hc.symm

theorem sound1685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1685 node1685Labels = Sparse.eval nodeValue1685 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1685) = mixedMoment B node1685 node1685Labels := rfl
  simpa [nodeValue1685, Sparse.eval] using hc.symm

theorem sound1686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1686 node1686Labels = Sparse.eval nodeValue1686 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1686) = mixedMoment B node1686 node1686Labels := rfl
  simpa [nodeValue1686, Sparse.eval] using hc.symm

theorem sound1687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1687 node1687Labels = Sparse.eval nodeValue1687 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1687) = mixedMoment B node1687 node1687Labels := rfl
  simpa [nodeValue1687, Sparse.eval] using hc.symm

theorem sound1688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1688 node1688Labels = Sparse.eval nodeValue1688 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1688) = mixedMoment B node1688 node1688Labels := rfl
  simpa [nodeValue1688, Sparse.eval] using hc.symm

theorem sound1689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1689 node1689Labels = Sparse.eval nodeValue1689 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1689) = mixedMoment B node1689 node1689Labels := rfl
  simpa [nodeValue1689, Sparse.eval] using hc.symm

theorem sound1695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1695 node1695Labels = Sparse.eval nodeValue1695 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1695) = mixedMoment B node1695 node1695Labels := rfl
  simpa [nodeValue1695, Sparse.eval] using hc.symm

theorem sound1697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1697 node1697Labels = Sparse.eval nodeValue1697 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1697) = mixedMoment B node1697 node1697Labels := rfl
  simpa [nodeValue1697, Sparse.eval] using hc.symm

theorem sound1699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1699 node1699Labels = Sparse.eval nodeValue1699 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1699) = mixedMoment B node1699 node1699Labels := rfl
  simpa [nodeValue1699, Sparse.eval] using hc.symm

theorem sound1700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1700 node1700Labels = Sparse.eval nodeValue1700 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1700) = mixedMoment B node1700 node1700Labels := rfl
  simpa [nodeValue1700, Sparse.eval] using hc.symm

theorem sound1703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1703 node1703Labels = Sparse.eval nodeValue1703 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1703) = mixedMoment B node1703 node1703Labels := rfl
  simpa [nodeValue1703, Sparse.eval] using hc.symm

theorem sound1704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1704 node1704Labels = Sparse.eval nodeValue1704 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1704) = mixedMoment B node1704 node1704Labels := rfl
  simpa [nodeValue1704, Sparse.eval] using hc.symm

theorem sound1709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1709 node1709Labels = Sparse.eval nodeValue1709 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1709) = mixedMoment B node1709 node1709Labels := rfl
  simpa [nodeValue1709, Sparse.eval] using hc.symm

theorem sound1711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1711 node1711Labels = Sparse.eval nodeValue1711 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1711) = mixedMoment B node1711 node1711Labels := rfl
  simpa [nodeValue1711, Sparse.eval] using hc.symm

theorem sound1712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1712 node1712Labels = Sparse.eval nodeValue1712 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1712) = mixedMoment B node1712 node1712Labels := rfl
  simpa [nodeValue1712, Sparse.eval] using hc.symm

theorem sound1713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1713 node1713Labels = Sparse.eval nodeValue1713 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1713) = mixedMoment B node1713 node1713Labels := rfl
  simpa [nodeValue1713, Sparse.eval] using hc.symm

theorem sound1714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1714 node1714Labels = Sparse.eval nodeValue1714 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1714) = mixedMoment B node1714 node1714Labels := rfl
  simpa [nodeValue1714, Sparse.eval] using hc.symm

theorem sound1715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1715 node1715Labels = Sparse.eval nodeValue1715 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1715) = mixedMoment B node1715 node1715Labels := rfl
  simpa [nodeValue1715, Sparse.eval] using hc.symm

theorem sound1716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1716 node1716Labels = Sparse.eval nodeValue1716 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1716) = mixedMoment B node1716 node1716Labels := rfl
  simpa [nodeValue1716, Sparse.eval] using hc.symm

theorem sound1720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1720 node1720Labels = Sparse.eval nodeValue1720 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1720) = mixedMoment B node1720 node1720Labels := rfl
  simpa [nodeValue1720, Sparse.eval] using hc.symm

theorem sound1721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1721 node1721Labels = Sparse.eval nodeValue1721 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1721) = mixedMoment B node1721 node1721Labels := rfl
  simpa [nodeValue1721, Sparse.eval] using hc.symm

theorem sound1722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1722 node1722Labels = Sparse.eval nodeValue1722 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1722) = mixedMoment B node1722 node1722Labels := rfl
  simpa [nodeValue1722, Sparse.eval] using hc.symm

theorem sound1723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1723 node1723Labels = Sparse.eval nodeValue1723 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1723) = mixedMoment B node1723 node1723Labels := rfl
  simpa [nodeValue1723, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1729 node1729Labels = Sparse.eval nodeValue1729 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1729) = mixedMoment B node1729 node1729Labels := rfl
  simpa [nodeValue1729, Sparse.eval] using hc.symm

theorem sound1734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1734 node1734Labels = Sparse.eval nodeValue1734 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1734) = mixedMoment B node1734 node1734Labels := rfl
  simpa [nodeValue1734, Sparse.eval] using hc.symm

theorem sound1735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1735 node1735Labels = Sparse.eval nodeValue1735 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1735) = mixedMoment B node1735 node1735Labels := rfl
  simpa [nodeValue1735, Sparse.eval] using hc.symm

theorem sound1736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1736 node1736Labels = Sparse.eval nodeValue1736 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1736) = mixedMoment B node1736 node1736Labels := rfl
  simpa [nodeValue1736, Sparse.eval] using hc.symm

theorem sound1740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1740 node1740Labels = Sparse.eval nodeValue1740 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1740) = mixedMoment B node1740 node1740Labels := rfl
  simpa [nodeValue1740, Sparse.eval] using hc.symm

theorem sound1742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1742 node1742Labels = Sparse.eval nodeValue1742 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1742) = mixedMoment B node1742 node1742Labels := rfl
  simpa [nodeValue1742, Sparse.eval] using hc.symm

theorem sound1743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1743 node1743Labels = Sparse.eval nodeValue1743 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1743) = mixedMoment B node1743 node1743Labels := rfl
  simpa [nodeValue1743, Sparse.eval] using hc.symm

theorem sound1744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1744 node1744Labels = Sparse.eval nodeValue1744 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1744) = mixedMoment B node1744 node1744Labels := rfl
  simpa [nodeValue1744, Sparse.eval] using hc.symm

theorem sound1745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1745 node1745Labels = Sparse.eval nodeValue1745 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1745) = mixedMoment B node1745 node1745Labels := rfl
  simpa [nodeValue1745, Sparse.eval] using hc.symm

theorem sound1746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1746 node1746Labels = Sparse.eval nodeValue1746 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1746) = mixedMoment B node1746 node1746Labels := rfl
  simpa [nodeValue1746, Sparse.eval] using hc.symm

theorem sound1747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1747 node1747Labels = Sparse.eval nodeValue1747 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1747) = mixedMoment B node1747 node1747Labels := rfl
  simpa [nodeValue1747, Sparse.eval] using hc.symm

theorem sound1748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1748 node1748Labels = Sparse.eval nodeValue1748 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1748) = mixedMoment B node1748 node1748Labels := rfl
  simpa [nodeValue1748, Sparse.eval] using hc.symm

theorem sound1749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1749 node1749Labels = Sparse.eval nodeValue1749 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1749) = mixedMoment B node1749 node1749Labels := rfl
  simpa [nodeValue1749, Sparse.eval] using hc.symm

theorem sound1757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1757 node1757Labels = Sparse.eval nodeValue1757 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1757) = mixedMoment B node1757 node1757Labels := rfl
  simpa [nodeValue1757, Sparse.eval] using hc.symm

theorem sound1789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1789 node1789Labels = Sparse.eval nodeValue1789 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1789) = mixedMoment B node1789 node1789Labels := rfl
  simpa [nodeValue1789, Sparse.eval] using hc.symm

theorem sound1790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1790 node1790Labels = Sparse.eval nodeValue1790 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1790) = mixedMoment B node1790 node1790Labels := rfl
  simpa [nodeValue1790, Sparse.eval] using hc.symm

theorem sound1791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1791 node1791Labels = Sparse.eval nodeValue1791 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1791) = mixedMoment B node1791 node1791Labels := rfl
  simpa [nodeValue1791, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1792 node1792Labels = Sparse.eval nodeValue1792 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1792) = mixedMoment B node1792 node1792Labels := rfl
  simpa [nodeValue1792, Sparse.eval] using hc.symm

theorem sound1793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1793 node1793Labels = Sparse.eval nodeValue1793 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1793) = mixedMoment B node1793 node1793Labels := rfl
  simpa [nodeValue1793, Sparse.eval] using hc.symm

theorem sound1794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1794 node1794Labels = Sparse.eval nodeValue1794 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1794) = mixedMoment B node1794 node1794Labels := rfl
  simpa [nodeValue1794, Sparse.eval] using hc.symm

theorem sound1795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1795 node1795Labels = Sparse.eval nodeValue1795 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1795) = mixedMoment B node1795 node1795Labels := rfl
  simpa [nodeValue1795, Sparse.eval] using hc.symm

theorem sound1796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1796 node1796Labels = Sparse.eval nodeValue1796 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1796) = mixedMoment B node1796 node1796Labels := rfl
  simpa [nodeValue1796, Sparse.eval] using hc.symm

theorem sound1797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1797 node1797Labels = Sparse.eval nodeValue1797 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1797) = mixedMoment B node1797 node1797Labels := rfl
  simpa [nodeValue1797, Sparse.eval] using hc.symm

theorem sound1802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1802 node1802Labels = Sparse.eval nodeValue1802 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1802) = mixedMoment B node1802 node1802Labels := rfl
  simpa [nodeValue1802, Sparse.eval] using hc.symm

theorem sound1803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1803 node1803Labels = Sparse.eval nodeValue1803 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1803) = mixedMoment B node1803 node1803Labels := rfl
  simpa [nodeValue1803, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node639 node639Labels = Sparse.eval nodeValue639 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 639) = mixedMoment B node639 node639Labels := rfl
  simpa [nodeValue639, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic479 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm479 x = (-3501219910680576000000 : ℝ) * Sparse.eval nodeValue639 x := by
  norm_num [reducedTerm479, nodeValue639, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic480 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm480 x = (-5023829814312960000000 : ℝ) * Sparse.eval nodeValue640 x := by
  norm_num [reducedTerm480, nodeValue640, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic481 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm481 x = (2600840819146752000000 : ℝ) * Sparse.eval nodeValue641 x := by
  norm_num [reducedTerm481, nodeValue641, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic482 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm482 x = (-7838560195140648960000 : ℝ) * Sparse.eval nodeValue642 x := by
  norm_num [reducedTerm482, nodeValue642, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic483 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm483 x = (3501219910680576000000 : ℝ) * Sparse.eval nodeValue643 x := by
  norm_num [reducedTerm483, nodeValue643, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic484 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm484 x = (892167378500321280000 : ℝ) * Sparse.eval nodeValue653 x := by
  norm_num [reducedTerm484, nodeValue653, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic485 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm485 x = (315973519843000320000 : ℝ) * Sparse.eval nodeValue654 x := by
  norm_num [reducedTerm485, nodeValue654, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic486 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm486 x = (8659257895151861760000 : ℝ) * Sparse.eval nodeValue909 x := by
  norm_num [reducedTerm486, nodeValue909, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic487 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm487 x = (7407336363717427200000 : ℝ) * Sparse.eval nodeValue911 x := by
  norm_num [reducedTerm487, nodeValue911, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic488 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm488 x = (8137792988223897600000 : ℝ) * Sparse.eval nodeValue914 x := by
  norm_num [reducedTerm488, nodeValue914, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic489 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm489 x = (842806262366208000000 : ℝ) * Sparse.eval nodeValue922 x := by
  norm_num [reducedTerm489, nodeValue922, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic490 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm490 x = (-941481721225543680000 : ℝ) * Sparse.eval nodeValue929 x := by
  norm_num [reducedTerm490, nodeValue929, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic491 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm491 x = (-4522163694065418240000 : ℝ) * Sparse.eval nodeValue930 x := by
  norm_num [reducedTerm491, nodeValue930, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic492 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm492 x = (862331180804997120000 : ℝ) * Sparse.eval nodeValue931 x := by
  norm_num [reducedTerm492, nodeValue931, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic493 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm493 x = (-2281209943794647040000 : ℝ) * Sparse.eval nodeValue932 x := by
  norm_num [reducedTerm493, nodeValue932, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic494 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm494 x = (-842806262366208000000 : ℝ) * Sparse.eval nodeValue933 x := by
  norm_num [reducedTerm494, nodeValue933, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic495 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm495 x = (1048155974782156800000 : ℝ) * Sparse.eval nodeValue934 x := by
  norm_num [reducedTerm495, nodeValue934, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic496 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm496 x = (-3501622812129361920000 : ℝ) * Sparse.eval nodeValue936 x := by
  norm_num [reducedTerm496, nodeValue936, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic497 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm497 x = (-690110044530278400000 : ℝ) * Sparse.eval nodeValue937 x := by
  norm_num [reducedTerm497, nodeValue937, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic498 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm498 x = (-5644648033344552960000 : ℝ) * Sparse.eval nodeValue939 x := by
  norm_num [reducedTerm498, nodeValue939, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic499 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm499 x = (-3110224913045913600000 : ℝ) * Sparse.eval nodeValue940 x := by
  norm_num [reducedTerm499, nodeValue940, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic500 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm500 x = (5755499567677440000000 : ℝ) * Sparse.eval nodeValue944 x := by
  norm_num [reducedTerm500, nodeValue944, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic501 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm501 x = (5755499567677440000000 : ℝ) * Sparse.eval nodeValue945 x := by
  norm_num [reducedTerm501, nodeValue945, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic502 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm502 x = (4959624732475392000000 : ℝ) * Sparse.eval nodeValue946 x := by
  norm_num [reducedTerm502, nodeValue946, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic503 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm503 x = (-7458564352880148480000 : ℝ) * Sparse.eval nodeValue949 x := by
  norm_num [reducedTerm503, nodeValue949, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic504 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm504 x = (-5755499567677440000000 : ℝ) * Sparse.eval nodeValue950 x := by
  norm_num [reducedTerm504, nodeValue950, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic505 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm505 x = (7458564352880148480000 : ℝ) * Sparse.eval nodeValue951 x := by
  norm_num [reducedTerm505, nodeValue951, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic506 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm506 x = (-4959624732475392000000 : ℝ) * Sparse.eval nodeValue952 x := by
  norm_num [reducedTerm506, nodeValue952, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic507 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm507 x = (-5755499567677440000000 : ℝ) * Sparse.eval nodeValue953 x := by
  norm_num [reducedTerm507, nodeValue953, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic508 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm508 x = (-3501219910680576000000 : ℝ) * Sparse.eval nodeValue954 x := by
  norm_num [reducedTerm508, nodeValue954, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic509 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm509 x = (-2976678613712240640000 : ℝ) * Sparse.eval nodeValue1024 x := by
  norm_num [reducedTerm509, nodeValue1024, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic510 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm510 x = (-4206296272205905920000 : ℝ) * Sparse.eval nodeValue1027 x := by
  norm_num [reducedTerm510, nodeValue1027, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic511 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm511 x = (84218592777338880000 : ℝ) * Sparse.eval nodeValue1039 x := by
  norm_num [reducedTerm511, nodeValue1039, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic512 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm512 x = (-1011243447920885760000 : ℝ) * Sparse.eval nodeValue1041 x := by
  norm_num [reducedTerm512, nodeValue1041, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic513 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm513 x = (-2007773678972436480000 : ℝ) * Sparse.eval nodeValue1044 x := by
  norm_num [reducedTerm513, nodeValue1044, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic514 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm514 x = (10725266364412723200000 : ℝ) * Sparse.eval nodeValue1046 x := by
  norm_num [reducedTerm514, nodeValue1046, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic515 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm515 x = (-13781464017158799360000 : ℝ) * Sparse.eval nodeValue1047 x := by
  norm_num [reducedTerm515, nodeValue1047, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic516 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm516 x = (1567784528782295040000 : ℝ) * Sparse.eval nodeValue1049 x := by
  norm_num [reducedTerm516, nodeValue1049, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic517 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm517 x = (927024855143546880000 : ℝ) * Sparse.eval nodeValue1050 x := by
  norm_num [reducedTerm517, nodeValue1050, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic518 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm518 x = (1191593947134689280000 : ℝ) * Sparse.eval nodeValue1051 x := by
  norm_num [reducedTerm518, nodeValue1051, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic519 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm519 x = (6300739362226176000000 : ℝ) * Sparse.eval nodeValue1058 x := by
  norm_num [reducedTerm519, nodeValue1058, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic520 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm520 x = (-3750701327642787840000 : ℝ) * Sparse.eval nodeValue1061 x := by
  norm_num [reducedTerm520, nodeValue1061, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic521 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm521 x = (-6300739362226176000000 : ℝ) * Sparse.eval nodeValue1063 x := by
  norm_num [reducedTerm521, nodeValue1063, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic522 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm522 x = (3750701327642787840000 : ℝ) * Sparse.eval nodeValue1064 x := by
  norm_num [reducedTerm522, nodeValue1064, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic523 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm523 x = (-8631272678361661440000 : ℝ) * Sparse.eval nodeValue1087 x := by
  norm_num [reducedTerm523, nodeValue1087, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic524 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm524 x = (7331333818189086720000 : ℝ) * Sparse.eval nodeValue1091 x := by
  norm_num [reducedTerm524, nodeValue1091, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic525 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm525 x = (-2107338916154572800000 : ℝ) * Sparse.eval nodeValue1094 x := by
  norm_num [reducedTerm525, nodeValue1094, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic526 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm526 x = (94866766992506880000 : ℝ) * Sparse.eval nodeValue1111 x := by
  norm_num [reducedTerm526, nodeValue1111, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic527 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm527 x = (-26389657073487052800000 : ℝ) * Sparse.eval nodeValue1112 x := by
  norm_num [reducedTerm527, nodeValue1112, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic528 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm528 x = (-8810814575497052160000 : ℝ) * Sparse.eval nodeValue1113 x := by
  norm_num [reducedTerm528, nodeValue1113, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic529 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm529 x = (-1573216023167631360000 : ℝ) * Sparse.eval nodeValue1115 x := by
  norm_num [reducedTerm529, nodeValue1115, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic530 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm530 x = (-1126879414384066560000 : ℝ) * Sparse.eval nodeValue1116 x := by
  norm_num [reducedTerm530, nodeValue1116, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic531 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm531 x = (-250586732209766400000 : ℝ) * Sparse.eval nodeValue1117 x := by
  norm_num [reducedTerm531, nodeValue1117, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic532 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm532 x = (4772950974038016000000 : ℝ) * Sparse.eval nodeValue1118 x := by
  norm_num [reducedTerm532, nodeValue1118, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic533 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm533 x = (-1307377367220879360000 : ℝ) * Sparse.eval nodeValue1119 x := by
  norm_num [reducedTerm533, nodeValue1119, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic534 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm534 x = (6812136157446144000000 : ℝ) * Sparse.eval nodeValue1120 x := by
  norm_num [reducedTerm534, nodeValue1120, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic535 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm535 x = (-8762782347893145600000 : ℝ) * Sparse.eval nodeValue1121 x := by
  norm_num [reducedTerm535, nodeValue1121, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic536 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm536 x = (416003421044736000000 : ℝ) * Sparse.eval nodeValue1125 x := by
  norm_num [reducedTerm536, nodeValue1125, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic537 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm537 x = (3128439995443445760000 : ℝ) * Sparse.eval nodeValue1126 x := by
  norm_num [reducedTerm537, nodeValue1126, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic538 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm538 x = (331078441437757440000 : ℝ) * Sparse.eval nodeValue1128 x := by
  norm_num [reducedTerm538, nodeValue1128, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic539 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm539 x = (19378969510926090240000 : ℝ) * Sparse.eval nodeValue1129 x := by
  norm_num [reducedTerm539, nodeValue1129, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic540 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm540 x = (-9464678117613895680000 : ℝ) * Sparse.eval nodeValue1130 x := by
  norm_num [reducedTerm540, nodeValue1130, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic541 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm541 x = (5641023726228602880000 : ℝ) * Sparse.eval nodeValue1131 x := by
  norm_num [reducedTerm541, nodeValue1131, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic542 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm542 x = (-1759585423361310720000 : ℝ) * Sparse.eval nodeValue1132 x := by
  norm_num [reducedTerm542, nodeValue1132, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic543 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm543 x = (1307514346489774080000 : ℝ) * Sparse.eval nodeValue1133 x := by
  norm_num [reducedTerm543, nodeValue1133, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic544 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm544 x = (3771399734927032320000 : ℝ) * Sparse.eval nodeValue1134 x := by
  norm_num [reducedTerm544, nodeValue1134, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic545 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm545 x = (-4459227814998835200000 : ℝ) * Sparse.eval nodeValue1135 x := by
  norm_num [reducedTerm545, nodeValue1135, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic546 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm546 x = (467378502645841920000 : ℝ) * Sparse.eval nodeValue1137 x := by
  norm_num [reducedTerm546, nodeValue1137, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic547 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm547 x = (-19215558570607902720000 : ℝ) * Sparse.eval nodeValue1138 x := by
  norm_num [reducedTerm547, nodeValue1138, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic548 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm548 x = (-10083993537718517760000 : ℝ) * Sparse.eval nodeValue1139 x := by
  norm_num [reducedTerm548, nodeValue1139, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic549 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm549 x = (5594674980160143360000 : ℝ) * Sparse.eval nodeValue1140 x := by
  norm_num [reducedTerm549, nodeValue1140, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic550 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm550 x = (871459791106867200000 : ℝ) * Sparse.eval nodeValue1141 x := by
  norm_num [reducedTerm550, nodeValue1141, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic551 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm551 x = (5137435020224102400000 : ℝ) * Sparse.eval nodeValue1142 x := by
  norm_num [reducedTerm551, nodeValue1142, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic552 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm552 x = (-5549518414241464320000 : ℝ) * Sparse.eval nodeValue1143 x := by
  norm_num [reducedTerm552, nodeValue1143, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic553 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm553 x = (-2210692257679933440000 : ℝ) * Sparse.eval nodeValue1144 x := by
  norm_num [reducedTerm553, nodeValue1144, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic554 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm554 x = (2991047260449669120000 : ℝ) * Sparse.eval nodeValue1145 x := by
  norm_num [reducedTerm554, nodeValue1145, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic555 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm555 x = (167779287760896000000 : ℝ) * Sparse.eval nodeValue1146 x := by
  norm_num [reducedTerm555, nodeValue1146, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic556 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm556 x = (-54778388874854400000 : ℝ) * Sparse.eval nodeValue1148 x := by
  norm_num [reducedTerm556, nodeValue1148, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic557 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm557 x = (54778388874854400000 : ℝ) * Sparse.eval nodeValue1149 x := by
  norm_num [reducedTerm557, nodeValue1149, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic558 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm558 x = (598839592845312000000 : ℝ) * Sparse.eval nodeValue1150 x := by
  norm_num [reducedTerm558, nodeValue1150, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic559 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm559 x = (-3796503149893386240000 : ℝ) * Sparse.eval nodeValue1151 x := by
  norm_num [reducedTerm559, nodeValue1151, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic560 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm560 x = (-2713512723987824640000 : ℝ) * Sparse.eval nodeValue1153 x := by
  norm_num [reducedTerm560, nodeValue1153, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic561 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm561 x = (3773107777016954880000 : ℝ) * Sparse.eval nodeValue1155 x := by
  norm_num [reducedTerm561, nodeValue1155, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic562 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm562 x = (-4033883256599347200000 : ℝ) * Sparse.eval nodeValue1156 x := by
  norm_num [reducedTerm562, nodeValue1156, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic563 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm563 x = (-1465158899028787200000 : ℝ) * Sparse.eval nodeValue1159 x := by
  norm_num [reducedTerm563, nodeValue1159, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic564 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm564 x = (5499042155628134400000 : ℝ) * Sparse.eval nodeValue1160 x := by
  norm_num [reducedTerm564, nodeValue1160, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic565 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm565 x = (4433171053215744000000 : ℝ) * Sparse.eval nodeValue1169 x := by
  norm_num [reducedTerm565, nodeValue1169, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic566 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm566 x = (6851070957020774400000 : ℝ) * Sparse.eval nodeValue1171 x := by
  norm_num [reducedTerm566, nodeValue1171, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic567 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm567 x = (606438917347737600000 : ℝ) * Sparse.eval nodeValue1174 x := by
  norm_num [reducedTerm567, nodeValue1174, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic568 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm568 x = (934778270036459520000 : ℝ) * Sparse.eval nodeValue1212 x := by
  norm_num [reducedTerm568, nodeValue1212, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic569 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm569 x = (-1029645037028966400000 : ℝ) * Sparse.eval nodeValue1215 x := by
  norm_num [reducedTerm569, nodeValue1215, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic570 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm570 x = (250586732209766400000 : ℝ) * Sparse.eval nodeValue1216 x := by
  norm_num [reducedTerm570, nodeValue1216, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic571 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm571 x = (18978681323195596800000 : ℝ) * Sparse.eval nodeValue1217 x := by
  norm_num [reducedTerm571, nodeValue1217, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic572 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm572 x = (11351689807634104320000 : ℝ) * Sparse.eval nodeValue1219 x := by
  norm_num [reducedTerm572, nodeValue1219, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic573 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm573 x = (972527074748006400000 : ℝ) * Sparse.eval nodeValue1221 x := by
  norm_num [reducedTerm573, nodeValue1221, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic574 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm574 x = (-6722247552986972160000 : ℝ) * Sparse.eval nodeValue1233 x := by
  norm_num [reducedTerm574, nodeValue1233, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic575 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm575 x = (-416003421044736000000 : ℝ) * Sparse.eval nodeValue1234 x := by
  norm_num [reducedTerm575, nodeValue1234, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic576 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm576 x = (3252202435368714240000 : ℝ) * Sparse.eval nodeValue1235 x := by
  norm_num [reducedTerm576, nodeValue1235, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic577 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm577 x = (12119156027369717760000 : ℝ) * Sparse.eval nodeValue1236 x := by
  norm_num [reducedTerm577, nodeValue1236, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic578 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm578 x = (6722247552986972160000 : ℝ) * Sparse.eval nodeValue1237 x := by
  norm_num [reducedTerm578, nodeValue1237, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic579 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm579 x = (-2570828363354603520000 : ℝ) * Sparse.eval nodeValue1239 x := by
  norm_num [reducedTerm579, nodeValue1239, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic580 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm580 x = (-12547178408576286720000 : ℝ) * Sparse.eval nodeValue1240 x := by
  norm_num [reducedTerm580, nodeValue1240, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic581 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm581 x = (8753467817805742080000 : ℝ) * Sparse.eval nodeValue1241 x := by
  norm_num [reducedTerm581, nodeValue1241, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic582 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm582 x = (-3100873301337047040000 : ℝ) * Sparse.eval nodeValue1242 x := by
  norm_num [reducedTerm582, nodeValue1242, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic583 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm583 x = (-2614211302075269120000 : ℝ) * Sparse.eval nodeValue1243 x := by
  norm_num [reducedTerm583, nodeValue1243, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic584 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm584 x = (7725885129934110720000 : ℝ) * Sparse.eval nodeValue1245 x := by
  norm_num [reducedTerm584, nodeValue1245, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic585 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm585 x = (-19348453924951818240000 : ℝ) * Sparse.eval nodeValue1246 x := by
  norm_num [reducedTerm585, nodeValue1246, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic586 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm586 x = (-7062722889655910400000 : ℝ) * Sparse.eval nodeValue1260 x := by
  norm_num [reducedTerm586, nodeValue1260, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic587 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm587 x = (-9103216750304624640000 : ℝ) * Sparse.eval nodeValue1261 x := by
  norm_num [reducedTerm587, nodeValue1261, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic588 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm588 x = (7062722889655910400000 : ℝ) * Sparse.eval nodeValue1262 x := by
  norm_num [reducedTerm588, nodeValue1262, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic589 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm589 x = (8502527801884999680000 : ℝ) * Sparse.eval nodeValue1264 x := by
  norm_num [reducedTerm589, nodeValue1264, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic590 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm590 x = (-8079242612869693440000 : ℝ) * Sparse.eval nodeValue1270 x := by
  norm_num [reducedTerm590, nodeValue1270, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic591 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm591 x = (-5076859302087229440000 : ℝ) * Sparse.eval nodeValue1273 x := by
  norm_num [reducedTerm591, nodeValue1273, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic592 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm592 x = (-2206050538624450560000 : ℝ) * Sparse.eval nodeValue1291 x := by
  norm_num [reducedTerm592, nodeValue1291, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic593 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm593 x = (2219882239269273600000 : ℝ) * Sparse.eval nodeValue1292 x := by
  norm_num [reducedTerm593, nodeValue1292, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic594 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm594 x = (4459227814998835200000 : ℝ) * Sparse.eval nodeValue1293 x := by
  norm_num [reducedTerm594, nodeValue1293, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic595 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm595 x = (11729049453615513600000 : ℝ) * Sparse.eval nodeValue1294 x := by
  norm_num [reducedTerm595, nodeValue1294, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic596 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm596 x = (2206050538624450560000 : ℝ) * Sparse.eval nodeValue1295 x := by
  norm_num [reducedTerm596, nodeValue1295, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic597 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm597 x = (5575466278860226560000 : ℝ) * Sparse.eval nodeValue1297 x := by
  norm_num [reducedTerm597, nodeValue1297, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic598 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm598 x = (-6047328798324817920000 : ℝ) * Sparse.eval nodeValue1306 x := by
  norm_num [reducedTerm598, nodeValue1306, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic599 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm599 x = (-626180907745935360000 : ℝ) * Sparse.eval nodeValue1310 x := by
  norm_num [reducedTerm599, nodeValue1310, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic600 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm600 x = (5977466481711513600000 : ℝ) * Sparse.eval nodeValue1314 x := by
  norm_num [reducedTerm600, nodeValue1314, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic601 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm601 x = (3501622812129361920000 : ℝ) * Sparse.eval nodeValue1315 x := by
  norm_num [reducedTerm601, nodeValue1315, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic602 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm602 x = (-9579839035999518720000 : ℝ) * Sparse.eval nodeValue1316 x := by
  norm_num [reducedTerm602, nodeValue1316, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic603 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm603 x = (7341542882196848640000 : ℝ) * Sparse.eval nodeValue1317 x := by
  norm_num [reducedTerm603, nodeValue1317, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic604 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm604 x = (-4432587559454638080000 : ℝ) * Sparse.eval nodeValue1318 x := by
  norm_num [reducedTerm604, nodeValue1318, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic605 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm605 x = (-3032742142629642240000 : ℝ) * Sparse.eval nodeValue1319 x := by
  norm_num [reducedTerm605, nodeValue1319, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic606 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm606 x = (11886766950399344640000 : ℝ) * Sparse.eval nodeValue1320 x := by
  norm_num [reducedTerm606, nodeValue1320, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic607 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm607 x = (-10548491592982855680000 : ℝ) * Sparse.eval nodeValue1321 x := by
  norm_num [reducedTerm607, nodeValue1321, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic608 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm608 x = (9579839035999518720000 : ℝ) * Sparse.eval nodeValue1322 x := by
  norm_num [reducedTerm608, nodeValue1322, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic609 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm609 x = (-4933072605979607040000 : ℝ) * Sparse.eval nodeValue1323 x := by
  norm_num [reducedTerm609, nodeValue1323, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic610 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm610 x = (-8886421804453724160000 : ℝ) * Sparse.eval nodeValue1324 x := by
  norm_num [reducedTerm610, nodeValue1324, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic611 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm611 x = (-8635312347795947520000 : ℝ) * Sparse.eval nodeValue1325 x := by
  norm_num [reducedTerm611, nodeValue1325, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic612 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm612 x = (277114839928012800000 : ℝ) * Sparse.eval nodeValue1326 x := by
  norm_num [reducedTerm612, nodeValue1326, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic613 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm613 x = (-5341116330562682880000 : ℝ) * Sparse.eval nodeValue1327 x := by
  norm_num [reducedTerm613, nodeValue1327, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic614 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm614 x = (-2299907207666073600000 : ℝ) * Sparse.eval nodeValue1328 x := by
  norm_num [reducedTerm614, nodeValue1328, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic615 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm615 x = (-819339736118722560000 : ℝ) * Sparse.eval nodeValue1330 x := by
  norm_num [reducedTerm615, nodeValue1330, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic616 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm616 x = (-3493413807980544000000 : ℝ) * Sparse.eval nodeValue1332 x := by
  norm_num [reducedTerm616, nodeValue1332, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic617 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm617 x = (7641023538228756480000 : ℝ) * Sparse.eval nodeValue1333 x := by
  norm_num [reducedTerm617, nodeValue1333, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic618 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm618 x = (8698253102854963200000 : ℝ) * Sparse.eval nodeValue1334 x := by
  norm_num [reducedTerm618, nodeValue1334, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic619 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm619 x = (7361272231133184000000 : ℝ) * Sparse.eval nodeValue1335 x := by
  norm_num [reducedTerm619, nodeValue1335, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic620 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm620 x = (3435031202884485120000 : ℝ) * Sparse.eval nodeValue1336 x := by
  norm_num [reducedTerm620, nodeValue1336, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic621 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm621 x = (-1895122181062656000000 : ℝ) * Sparse.eval nodeValue1337 x := by
  norm_num [reducedTerm621, nodeValue1337, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic622 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm622 x = (4158977745420288000000 : ℝ) * Sparse.eval nodeValue1338 x := by
  norm_num [reducedTerm622, nodeValue1338, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic623 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm623 x = (1542086242739159040000 : ℝ) * Sparse.eval nodeValue1348 x := by
  norm_num [reducedTerm623, nodeValue1348, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic624 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm624 x = (-1899117244195799040000 : ℝ) * Sparse.eval nodeValue1366 x := by
  norm_num [reducedTerm624, nodeValue1366, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic625 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm625 x = (2667259420956426240000 : ℝ) * Sparse.eval nodeValue1367 x := by
  norm_num [reducedTerm625, nodeValue1367, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic626 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm626 x = (-3750701327642787840000 : ℝ) * Sparse.eval nodeValue1369 x := by
  norm_num [reducedTerm626, nodeValue1369, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic627 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm627 x = (1899117244195799040000 : ℝ) * Sparse.eval nodeValue1370 x := by
  norm_num [reducedTerm627, nodeValue1370, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic628 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm628 x = (8859486641663508480000 : ℝ) * Sparse.eval nodeValue1372 x := by
  norm_num [reducedTerm628, nodeValue1372, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic629 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm629 x = (-11526746062619934720000 : ℝ) * Sparse.eval nodeValue1375 x := by
  norm_num [reducedTerm629, nodeValue1375, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic630 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm630 x = (4656026210537963520000 : ℝ) * Sparse.eval nodeValue1383 x := by
  norm_num [reducedTerm630, nodeValue1383, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic631 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm631 x = (-3478154931439534080000 : ℝ) * Sparse.eval nodeValue1385 x := by
  norm_num [reducedTerm631, nodeValue1385, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic632 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm632 x = (-2299907207666073600000 : ℝ) * Sparse.eval nodeValue1388 x := by
  norm_num [reducedTerm632, nodeValue1388, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic633 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm633 x = (-2356119002871889920000 : ℝ) * Sparse.eval nodeValue1391 x := by
  norm_num [reducedTerm633, nodeValue1391, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic634 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm634 x = (-22276992136265072640000 : ℝ) * Sparse.eval nodeValue1406 x := by
  norm_num [reducedTerm634, nodeValue1406, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic635 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm635 x = (-17269758213677383680000 : ℝ) * Sparse.eval nodeValue1408 x := by
  norm_num [reducedTerm635, nodeValue1408, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic636 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm636 x = (847409560407244800000 : ℝ) * Sparse.eval nodeValue1435 x := by
  norm_num [reducedTerm636, nodeValue1435, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic637 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm637 x = (-3245969833485926400000 : ℝ) * Sparse.eval nodeValue1436 x := by
  norm_num [reducedTerm637, nodeValue1436, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic638 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm638 x = (39708998817546240000 : ℝ) * Sparse.eval nodeValue1438 x := by
  norm_num [reducedTerm638, nodeValue1438, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic639 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm639 x = (-1056230257065984000000 : ℝ) * Sparse.eval nodeValue1501 x := by
  norm_num [reducedTerm639, nodeValue1501, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic640 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm640 x = (-1423280520010137600000 : ℝ) * Sparse.eval nodeValue1502 x := by
  norm_num [reducedTerm640, nodeValue1502, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic641 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm641 x = (-1951341470849433600000 : ℝ) * Sparse.eval nodeValue1504 x := by
  norm_num [reducedTerm641, nodeValue1504, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic642 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm642 x = (1056230257065984000000 : ℝ) * Sparse.eval nodeValue1505 x := by
  norm_num [reducedTerm642, nodeValue1505, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic643 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm643 x = (1423280520010137600000 : ℝ) * Sparse.eval nodeValue1508 x := by
  norm_num [reducedTerm643, nodeValue1508, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic644 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm644 x = (-2210913934743306240000 : ℝ) * Sparse.eval nodeValue1510 x := by
  norm_num [reducedTerm644, nodeValue1510, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic645 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm645 x = (-2862630613510520832000 : ℝ) * Sparse.eval nodeValue1511 x := by
  norm_num [reducedTerm645, nodeValue1511, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic646 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm646 x = (-1812234680041734144000 : ℝ) * Sparse.eval nodeValue1512 x := by
  norm_num [reducedTerm646, nodeValue1512, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic647 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm647 x = (807931683631005696000 : ℝ) * Sparse.eval nodeValue1513 x := by
  norm_num [reducedTerm647, nodeValue1513, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic648 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm648 x = (279082176459964416000 : ℝ) * Sparse.eval nodeValue1514 x := by
  norm_num [reducedTerm648, nodeValue1514, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic649 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm649 x = (1951341470849433600000 : ℝ) * Sparse.eval nodeValue1515 x := by
  norm_num [reducedTerm649, nodeValue1515, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic650 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm650 x = (1532149313286832128000 : ℝ) * Sparse.eval nodeValue1516 x := by
  norm_num [reducedTerm650, nodeValue1516, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic651 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm651 x = (3125626258862112768000 : ℝ) * Sparse.eval nodeValue1520 x := by
  norm_num [reducedTerm651, nodeValue1520, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic652 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm652 x = (1398340775856439296000 : ℝ) * Sparse.eval nodeValue1522 x := by
  norm_num [reducedTerm652, nodeValue1522, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic653 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm653 x = (1978196107527585792000 : ℝ) * Sparse.eval nodeValue1523 x := by
  norm_num [reducedTerm653, nodeValue1523, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic654 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm654 x = (3237439447258103808000 : ℝ) * Sparse.eval nodeValue1526 x := by
  norm_num [reducedTerm654, nodeValue1526, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic655 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm655 x = (-115736953684230144000 : ℝ) * Sparse.eval nodeValue1528 x := by
  norm_num [reducedTerm655, nodeValue1528, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic656 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm656 x = (-190397481621258240000 : ℝ) * Sparse.eval nodeValue1529 x := by
  norm_num [reducedTerm656, nodeValue1529, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic657 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm657 x = (-179029231679176704000 : ℝ) * Sparse.eval nodeValue1530 x := by
  norm_num [reducedTerm657, nodeValue1530, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic658 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm658 x = (-24315273996926976000 : ℝ) * Sparse.eval nodeValue1531 x := by
  norm_num [reducedTerm658, nodeValue1531, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic659 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm659 x = (513372727945986048000 : ℝ) * Sparse.eval nodeValue1532 x := by
  norm_num [reducedTerm659, nodeValue1532, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic660 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm660 x = (3726326584597413888000 : ℝ) * Sparse.eval nodeValue1533 x := by
  norm_num [reducedTerm660, nodeValue1533, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic661 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm661 x = (92042023309737984000 : ℝ) * Sparse.eval nodeValue1534 x := by
  norm_num [reducedTerm661, nodeValue1534, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic662 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm662 x = (299269579737268224000 : ℝ) * Sparse.eval nodeValue1540 x := by
  norm_num [reducedTerm662, nodeValue1540, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic663 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm663 x = (-1090667657931522048000 : ℝ) * Sparse.eval nodeValue1667 x := by
  norm_num [reducedTerm663, nodeValue1667, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic664 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm664 x = (-1101980502152183808000 : ℝ) * Sparse.eval nodeValue1668 x := by
  norm_num [reducedTerm664, nodeValue1668, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic665 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm665 x = (-735052166107693056000 : ℝ) * Sparse.eval nodeValue1670 x := by
  norm_num [reducedTerm665, nodeValue1670, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic666 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm666 x = (-615325865037004800000 : ℝ) * Sparse.eval nodeValue1672 x := by
  norm_num [reducedTerm666, nodeValue1672, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic667 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm667 x = (441343231347916800000 : ℝ) * Sparse.eval nodeValue1676 x := by
  norm_num [reducedTerm667, nodeValue1676, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic668 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm668 x = (2798915153550114816000 : ℝ) * Sparse.eval nodeValue1678 x := by
  norm_num [reducedTerm668, nodeValue1678, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic669 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm669 x = (4204277593279561728000 : ℝ) * Sparse.eval nodeValue1679 x := by
  norm_num [reducedTerm669, nodeValue1679, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic670 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm670 x = (4390161007521300480000 : ℝ) * Sparse.eval nodeValue1682 x := by
  norm_num [reducedTerm670, nodeValue1682, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic671 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm671 x = (604529641244196864000 : ℝ) * Sparse.eval nodeValue1684 x := by
  norm_num [reducedTerm671, nodeValue1684, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic672 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm672 x = (910860777696264192000 : ℝ) * Sparse.eval nodeValue1685 x := by
  norm_num [reducedTerm672, nodeValue1685, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic673 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm673 x = (789405404560883712000 : ℝ) * Sparse.eval nodeValue1686 x := by
  norm_num [reducedTerm673, nodeValue1686, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic674 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm674 x = (-120789168095232000000 : ℝ) * Sparse.eval nodeValue1687 x := by
  norm_num [reducedTerm674, nodeValue1687, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic675 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm675 x = (1305313133883752448000 : ℝ) * Sparse.eval nodeValue1688 x := by
  norm_num [reducedTerm675, nodeValue1688, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic676 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm676 x = (3666193326655340544000 : ℝ) * Sparse.eval nodeValue1689 x := by
  norm_num [reducedTerm676, nodeValue1689, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic677 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm677 x = (888021087364841472000 : ℝ) * Sparse.eval nodeValue1695 x := by
  norm_num [reducedTerm677, nodeValue1695, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic678 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm678 x = (550098197290156032000 : ℝ) * Sparse.eval nodeValue1697 x := by
  norm_num [reducedTerm678, nodeValue1697, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic679 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm679 x = (-902368496446341120000 : ℝ) * Sparse.eval nodeValue1699 x := by
  norm_num [reducedTerm679, nodeValue1699, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic680 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm680 x = (-1069052130648391680000 : ℝ) * Sparse.eval nodeValue1700 x := by
  norm_num [reducedTerm680, nodeValue1700, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic681 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm681 x = (2007627038014832640000 : ℝ) * Sparse.eval nodeValue1703 x := by
  norm_num [reducedTerm681, nodeValue1703, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic682 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm682 x = (583395049348005888000 : ℝ) * Sparse.eval nodeValue1704 x := by
  norm_num [reducedTerm682, nodeValue1704, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic683 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm683 x = (-2010373847085219840000 : ℝ) * Sparse.eval nodeValue1709 x := by
  norm_num [reducedTerm683, nodeValue1709, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic684 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm684 x = (-4752834733161381888000 : ℝ) * Sparse.eval nodeValue1711 x := by
  norm_num [reducedTerm684, nodeValue1711, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic685 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm685 x = (-4818691431020888064000 : ℝ) * Sparse.eval nodeValue1712 x := by
  norm_num [reducedTerm685, nodeValue1712, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic686 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm686 x = (-3378878307861331968000 : ℝ) * Sparse.eval nodeValue1713 x := by
  norm_num [reducedTerm686, nodeValue1713, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic687 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm687 x = (-6227807807028068352000 : ℝ) * Sparse.eval nodeValue1714 x := by
  norm_num [reducedTerm687, nodeValue1714, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic688 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm688 x = (-2138368756797407232000 : ℝ) * Sparse.eval nodeValue1715 x := by
  norm_num [reducedTerm688, nodeValue1715, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic689 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm689 x = (1926014843785052160000 : ℝ) * Sparse.eval nodeValue1716 x := by
  norm_num [reducedTerm689, nodeValue1716, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic690 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm690 x = (-1541521449311993856000 : ℝ) * Sparse.eval nodeValue1720 x := by
  norm_num [reducedTerm690, nodeValue1720, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic691 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm691 x = (1386207265990901760000 : ℝ) * Sparse.eval nodeValue1721 x := by
  norm_num [reducedTerm691, nodeValue1721, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic692 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm692 x = (1717512314662158336000 : ℝ) * Sparse.eval nodeValue1722 x := by
  norm_num [reducedTerm692, nodeValue1722, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic693 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm693 x = (-4810412754357977088000 : ℝ) * Sparse.eval nodeValue1723 x := by
  norm_num [reducedTerm693, nodeValue1723, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic694 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm694 x = (3751773612556419072000 : ℝ) * Sparse.eval nodeValue1729 x := by
  norm_num [reducedTerm694, nodeValue1729, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic695 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm695 x = (-95615204742070272000 : ℝ) * Sparse.eval nodeValue1734 x := by
  norm_num [reducedTerm695, nodeValue1734, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic696 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm696 x = (2302759193699155968000 : ℝ) * Sparse.eval nodeValue1735 x := by
  norm_num [reducedTerm696, nodeValue1735, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic697 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm697 x = (2459234748121546752000 : ℝ) * Sparse.eval nodeValue1736 x := by
  norm_num [reducedTerm697, nodeValue1736, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic698 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm698 x = (4524755554931834880000 : ℝ) * Sparse.eval nodeValue1740 x := by
  norm_num [reducedTerm698, nodeValue1740, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic699 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm699 x = (119212994511765504000 : ℝ) * Sparse.eval nodeValue1742 x := by
  norm_num [reducedTerm699, nodeValue1742, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic700 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm700 x = (-8626840581832704000 : ℝ) * Sparse.eval nodeValue1743 x := by
  norm_num [reducedTerm700, nodeValue1743, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic701 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm701 x = (-554123003977138176000 : ℝ) * Sparse.eval nodeValue1744 x := by
  norm_num [reducedTerm701, nodeValue1744, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic702 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm702 x = (-2769188286440669184000 : ℝ) * Sparse.eval nodeValue1745 x := by
  norm_num [reducedTerm702, nodeValue1745, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic703 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm703 x = (-3563661364114489344000 : ℝ) * Sparse.eval nodeValue1746 x := by
  norm_num [reducedTerm703, nodeValue1746, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic704 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm704 x = (-1117582666619682816000 : ℝ) * Sparse.eval nodeValue1747 x := by
  norm_num [reducedTerm704, nodeValue1747, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic705 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm705 x = (4393837063364345856000 : ℝ) * Sparse.eval nodeValue1748 x := by
  norm_num [reducedTerm705, nodeValue1748, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic706 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm706 x = (-722047208039055360000 : ℝ) * Sparse.eval nodeValue1749 x := by
  norm_num [reducedTerm706, nodeValue1749, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic707 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm707 x = (-474172475731476480000 : ℝ) * Sparse.eval nodeValue1757 x := by
  norm_num [reducedTerm707, nodeValue1757, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic708 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm708 x = (654308882759024640000 : ℝ) * Sparse.eval nodeValue1789 x := by
  norm_num [reducedTerm708, nodeValue1789, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic709 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm709 x = (-4566900924634890240000 : ℝ) * Sparse.eval nodeValue1790 x := by
  norm_num [reducedTerm709, nodeValue1790, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic710 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm710 x = (-6742174334468751360000 : ℝ) * Sparse.eval nodeValue1791 x := by
  norm_num [reducedTerm710, nodeValue1791, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic711 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm711 x = (2282493232765992960000 : ℝ) * Sparse.eval nodeValue1792 x := by
  norm_num [reducedTerm711, nodeValue1792, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic712 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm712 x = (3731415152240885760000 : ℝ) * Sparse.eval nodeValue1793 x := by
  norm_num [reducedTerm712, nodeValue1793, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic713 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm713 x = (673420605987225600000 : ℝ) * Sparse.eval nodeValue1794 x := by
  norm_num [reducedTerm713, nodeValue1794, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic714 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm714 x = (8275744746720460800000 : ℝ) * Sparse.eval nodeValue1795 x := by
  norm_num [reducedTerm714, nodeValue1795, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic715 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm715 x = (8393450481675141120000 : ℝ) * Sparse.eval nodeValue1796 x := by
  norm_num [reducedTerm715, nodeValue1796, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic716 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm716 x = (5418404332170117120000 : ℝ) * Sparse.eval nodeValue1797 x := by
  norm_num [reducedTerm716, nodeValue1797, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic717 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm717 x = (6265573704801976320000 : ℝ) * Sparse.eval nodeValue1802 x := by
  norm_num [reducedTerm717, nodeValue1802, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic718 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm718 x = (28541892592926720000 : ℝ) * Sparse.eval nodeValue1803 x := by
  norm_num [reducedTerm718, nodeValue1803, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge478Check : reducedMerge478 = Integer.Sparse.mergeBy masterLess reducedTerm480 reducedTerm481 := by decide +kernel

theorem reducedMerge479Check : reducedMerge479 = Integer.Sparse.mergeBy masterLess reducedTerm479 reducedMerge478 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge480Check : reducedMerge480 = Integer.Sparse.mergeBy masterLess reducedTerm482 reducedTerm483 := by decide +kernel

theorem reducedMerge481Check : reducedMerge481 = Integer.Sparse.mergeBy masterLess reducedTerm484 reducedTerm485 := by decide +kernel

theorem reducedMerge482Check : reducedMerge482 = Integer.Sparse.mergeBy masterLess reducedMerge480 reducedMerge481 := by decide +kernel

theorem reducedMerge483Check : reducedMerge483 = Integer.Sparse.mergeBy masterLess reducedMerge479 reducedMerge482 := by decide +kernel

theorem reducedMerge484Check : reducedMerge484 = Integer.Sparse.mergeBy masterLess reducedTerm486 reducedTerm487 := by decide +kernel

theorem reducedMerge485Check : reducedMerge485 = Integer.Sparse.mergeBy masterLess reducedTerm488 reducedTerm489 := by decide +kernel

theorem reducedMerge486Check : reducedMerge486 = Integer.Sparse.mergeBy masterLess reducedMerge484 reducedMerge485 := by decide +kernel

theorem reducedMerge487Check : reducedMerge487 = Integer.Sparse.mergeBy masterLess reducedTerm490 reducedTerm491 := by decide +kernel

theorem reducedMerge488Check : reducedMerge488 = Integer.Sparse.mergeBy masterLess reducedTerm492 reducedTerm493 := by decide +kernel

theorem reducedMerge489Check : reducedMerge489 = Integer.Sparse.mergeBy masterLess reducedMerge487 reducedMerge488 := by decide +kernel

theorem reducedMerge490Check : reducedMerge490 = Integer.Sparse.mergeBy masterLess reducedMerge486 reducedMerge489 := by decide +kernel

theorem reducedMerge491Check : reducedMerge491 = Integer.Sparse.mergeBy masterLess reducedMerge483 reducedMerge490 := by decide +kernel

theorem reducedMerge492Check : reducedMerge492 = Integer.Sparse.mergeBy masterLess reducedTerm495 reducedTerm496 := by decide +kernel

theorem reducedMerge493Check : reducedMerge493 = Integer.Sparse.mergeBy masterLess reducedTerm494 reducedMerge492 := by decide +kernel

theorem reducedMerge494Check : reducedMerge494 = Integer.Sparse.mergeBy masterLess reducedTerm497 reducedTerm498 := by decide +kernel

theorem reducedMerge495Check : reducedMerge495 = Integer.Sparse.mergeBy masterLess reducedTerm499 reducedTerm500 := by decide +kernel

theorem reducedMerge496Check : reducedMerge496 = Integer.Sparse.mergeBy masterLess reducedMerge494 reducedMerge495 := by decide +kernel

theorem reducedMerge497Check : reducedMerge497 = Integer.Sparse.mergeBy masterLess reducedMerge493 reducedMerge496 := by decide +kernel

theorem reducedMerge498Check : reducedMerge498 = Integer.Sparse.mergeBy masterLess reducedTerm501 reducedTerm502 := by decide +kernel

theorem reducedMerge499Check : reducedMerge499 = Integer.Sparse.mergeBy masterLess reducedTerm503 reducedTerm504 := by decide +kernel

theorem reducedMerge500Check : reducedMerge500 = Integer.Sparse.mergeBy masterLess reducedMerge498 reducedMerge499 := by decide +kernel

theorem reducedMerge501Check : reducedMerge501 = Integer.Sparse.mergeBy masterLess reducedTerm505 reducedTerm506 := by decide +kernel

theorem reducedMerge502Check : reducedMerge502 = Integer.Sparse.mergeBy masterLess reducedTerm507 reducedTerm508 := by decide +kernel

theorem reducedMerge503Check : reducedMerge503 = Integer.Sparse.mergeBy masterLess reducedMerge501 reducedMerge502 := by decide +kernel

theorem reducedMerge504Check : reducedMerge504 = Integer.Sparse.mergeBy masterLess reducedMerge500 reducedMerge503 := by decide +kernel

theorem reducedMerge505Check : reducedMerge505 = Integer.Sparse.mergeBy masterLess reducedMerge497 reducedMerge504 := by decide +kernel

theorem reducedMerge506Check : reducedMerge506 = Integer.Sparse.mergeBy masterLess reducedMerge491 reducedMerge505 := by decide +kernel

theorem reducedMerge507Check : reducedMerge507 = Integer.Sparse.mergeBy masterLess reducedTerm510 reducedTerm511 := by decide +kernel

theorem reducedMerge508Check : reducedMerge508 = Integer.Sparse.mergeBy masterLess reducedTerm509 reducedMerge507 := by decide +kernel

theorem reducedMerge509Check : reducedMerge509 = Integer.Sparse.mergeBy masterLess reducedTerm512 reducedTerm513 := by decide +kernel

theorem reducedMerge510Check : reducedMerge510 = Integer.Sparse.mergeBy masterLess reducedTerm514 reducedTerm515 := by decide +kernel

theorem reducedMerge511Check : reducedMerge511 = Integer.Sparse.mergeBy masterLess reducedMerge509 reducedMerge510 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge512Check : reducedMerge512 = Integer.Sparse.mergeBy masterLess reducedMerge508 reducedMerge511 := by decide +kernel

theorem reducedMerge513Check : reducedMerge513 = Integer.Sparse.mergeBy masterLess reducedTerm516 reducedTerm517 := by decide +kernel

theorem reducedMerge514Check : reducedMerge514 = Integer.Sparse.mergeBy masterLess reducedTerm518 reducedTerm519 := by decide +kernel

theorem reducedMerge515Check : reducedMerge515 = Integer.Sparse.mergeBy masterLess reducedMerge513 reducedMerge514 := by decide +kernel

theorem reducedMerge516Check : reducedMerge516 = Integer.Sparse.mergeBy masterLess reducedTerm520 reducedTerm521 := by decide +kernel

theorem reducedMerge517Check : reducedMerge517 = Integer.Sparse.mergeBy masterLess reducedTerm522 reducedTerm523 := by decide +kernel

theorem reducedMerge518Check : reducedMerge518 = Integer.Sparse.mergeBy masterLess reducedMerge516 reducedMerge517 := by decide +kernel

theorem reducedMerge519Check : reducedMerge519 = Integer.Sparse.mergeBy masterLess reducedMerge515 reducedMerge518 := by decide +kernel

theorem reducedMerge520Check : reducedMerge520 = Integer.Sparse.mergeBy masterLess reducedMerge512 reducedMerge519 := by decide +kernel

theorem reducedMerge521Check : reducedMerge521 = Integer.Sparse.mergeBy masterLess reducedTerm525 reducedTerm526 := by decide +kernel

theorem reducedMerge522Check : reducedMerge522 = Integer.Sparse.mergeBy masterLess reducedTerm524 reducedMerge521 := by decide +kernel

theorem reducedMerge523Check : reducedMerge523 = Integer.Sparse.mergeBy masterLess reducedTerm527 reducedTerm528 := by decide +kernel

theorem reducedMerge524Check : reducedMerge524 = Integer.Sparse.mergeBy masterLess reducedTerm529 reducedTerm530 := by decide +kernel

theorem reducedMerge525Check : reducedMerge525 = Integer.Sparse.mergeBy masterLess reducedMerge523 reducedMerge524 := by decide +kernel

theorem reducedMerge526Check : reducedMerge526 = Integer.Sparse.mergeBy masterLess reducedMerge522 reducedMerge525 := by decide +kernel

theorem reducedMerge527Check : reducedMerge527 = Integer.Sparse.mergeBy masterLess reducedTerm531 reducedTerm532 := by decide +kernel

theorem reducedMerge528Check : reducedMerge528 = Integer.Sparse.mergeBy masterLess reducedTerm533 reducedTerm534 := by decide +kernel

theorem reducedMerge529Check : reducedMerge529 = Integer.Sparse.mergeBy masterLess reducedMerge527 reducedMerge528 := by decide +kernel

theorem reducedMerge530Check : reducedMerge530 = Integer.Sparse.mergeBy masterLess reducedTerm535 reducedTerm536 := by decide +kernel

theorem reducedMerge531Check : reducedMerge531 = Integer.Sparse.mergeBy masterLess reducedTerm537 reducedTerm538 := by decide +kernel

theorem reducedMerge532Check : reducedMerge532 = Integer.Sparse.mergeBy masterLess reducedMerge530 reducedMerge531 := by decide +kernel

theorem reducedMerge533Check : reducedMerge533 = Integer.Sparse.mergeBy masterLess reducedMerge529 reducedMerge532 := by decide +kernel

theorem reducedMerge534Check : reducedMerge534 = Integer.Sparse.mergeBy masterLess reducedMerge526 reducedMerge533 := by decide +kernel

theorem reducedMerge535Check : reducedMerge535 = Integer.Sparse.mergeBy masterLess reducedMerge520 reducedMerge534 := by decide +kernel

theorem reducedMerge536Check : reducedMerge536 = Integer.Sparse.mergeBy masterLess reducedMerge506 reducedMerge535 := by decide +kernel

theorem reducedMerge537Check : reducedMerge537 = Integer.Sparse.mergeBy masterLess reducedTerm540 reducedTerm541 := by decide +kernel

theorem reducedMerge538Check : reducedMerge538 = Integer.Sparse.mergeBy masterLess reducedTerm539 reducedMerge537 := by decide +kernel

theorem reducedMerge539Check : reducedMerge539 = Integer.Sparse.mergeBy masterLess reducedTerm542 reducedTerm543 := by decide +kernel

theorem reducedMerge540Check : reducedMerge540 = Integer.Sparse.mergeBy masterLess reducedTerm544 reducedTerm545 := by decide +kernel

theorem reducedMerge541Check : reducedMerge541 = Integer.Sparse.mergeBy masterLess reducedMerge539 reducedMerge540 := by decide +kernel

theorem reducedMerge542Check : reducedMerge542 = Integer.Sparse.mergeBy masterLess reducedMerge538 reducedMerge541 := by decide +kernel

theorem reducedMerge543Check : reducedMerge543 = Integer.Sparse.mergeBy masterLess reducedTerm546 reducedTerm547 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge544Check : reducedMerge544 = Integer.Sparse.mergeBy masterLess reducedTerm548 reducedTerm549 := by decide +kernel

theorem reducedMerge545Check : reducedMerge545 = Integer.Sparse.mergeBy masterLess reducedMerge543 reducedMerge544 := by decide +kernel

theorem reducedMerge546Check : reducedMerge546 = Integer.Sparse.mergeBy masterLess reducedTerm550 reducedTerm551 := by decide +kernel

theorem reducedMerge547Check : reducedMerge547 = Integer.Sparse.mergeBy masterLess reducedTerm552 reducedTerm553 := by decide +kernel

theorem reducedMerge548Check : reducedMerge548 = Integer.Sparse.mergeBy masterLess reducedMerge546 reducedMerge547 := by decide +kernel

theorem reducedMerge549Check : reducedMerge549 = Integer.Sparse.mergeBy masterLess reducedMerge545 reducedMerge548 := by decide +kernel

theorem reducedMerge550Check : reducedMerge550 = Integer.Sparse.mergeBy masterLess reducedMerge542 reducedMerge549 := by decide +kernel

theorem reducedMerge551Check : reducedMerge551 = Integer.Sparse.mergeBy masterLess reducedTerm555 reducedTerm556 := by decide +kernel

theorem reducedMerge552Check : reducedMerge552 = Integer.Sparse.mergeBy masterLess reducedTerm554 reducedMerge551 := by decide +kernel

theorem reducedMerge553Check : reducedMerge553 = Integer.Sparse.mergeBy masterLess reducedTerm557 reducedTerm558 := by decide +kernel

theorem reducedMerge554Check : reducedMerge554 = Integer.Sparse.mergeBy masterLess reducedTerm559 reducedTerm560 := by decide +kernel

theorem reducedMerge555Check : reducedMerge555 = Integer.Sparse.mergeBy masterLess reducedMerge553 reducedMerge554 := by decide +kernel

theorem reducedMerge556Check : reducedMerge556 = Integer.Sparse.mergeBy masterLess reducedMerge552 reducedMerge555 := by decide +kernel

theorem reducedMerge557Check : reducedMerge557 = Integer.Sparse.mergeBy masterLess reducedTerm561 reducedTerm562 := by decide +kernel

theorem reducedMerge558Check : reducedMerge558 = Integer.Sparse.mergeBy masterLess reducedTerm563 reducedTerm564 := by decide +kernel

theorem reducedMerge559Check : reducedMerge559 = Integer.Sparse.mergeBy masterLess reducedMerge557 reducedMerge558 := by decide +kernel

theorem reducedMerge560Check : reducedMerge560 = Integer.Sparse.mergeBy masterLess reducedTerm565 reducedTerm566 := by decide +kernel

theorem reducedMerge561Check : reducedMerge561 = Integer.Sparse.mergeBy masterLess reducedTerm567 reducedTerm568 := by decide +kernel

theorem reducedMerge562Check : reducedMerge562 = Integer.Sparse.mergeBy masterLess reducedMerge560 reducedMerge561 := by decide +kernel

theorem reducedMerge563Check : reducedMerge563 = Integer.Sparse.mergeBy masterLess reducedMerge559 reducedMerge562 := by decide +kernel

theorem reducedMerge564Check : reducedMerge564 = Integer.Sparse.mergeBy masterLess reducedMerge556 reducedMerge563 := by decide +kernel

theorem reducedMerge565Check : reducedMerge565 = Integer.Sparse.mergeBy masterLess reducedMerge550 reducedMerge564 := by decide +kernel

theorem reducedMerge566Check : reducedMerge566 = Integer.Sparse.mergeBy masterLess reducedTerm570 reducedTerm571 := by decide +kernel

theorem reducedMerge567Check : reducedMerge567 = Integer.Sparse.mergeBy masterLess reducedTerm569 reducedMerge566 := by decide +kernel

theorem reducedMerge568Check : reducedMerge568 = Integer.Sparse.mergeBy masterLess reducedTerm572 reducedTerm573 := by decide +kernel

theorem reducedMerge569Check : reducedMerge569 = Integer.Sparse.mergeBy masterLess reducedTerm574 reducedTerm575 := by decide +kernel

theorem reducedMerge570Check : reducedMerge570 = Integer.Sparse.mergeBy masterLess reducedMerge568 reducedMerge569 := by decide +kernel

theorem reducedMerge571Check : reducedMerge571 = Integer.Sparse.mergeBy masterLess reducedMerge567 reducedMerge570 := by decide +kernel

theorem reducedMerge572Check : reducedMerge572 = Integer.Sparse.mergeBy masterLess reducedTerm576 reducedTerm577 := by decide +kernel

theorem reducedMerge573Check : reducedMerge573 = Integer.Sparse.mergeBy masterLess reducedTerm578 reducedTerm579 := by decide +kernel

theorem reducedMerge574Check : reducedMerge574 = Integer.Sparse.mergeBy masterLess reducedMerge572 reducedMerge573 := by decide +kernel

theorem reducedMerge575Check : reducedMerge575 = Integer.Sparse.mergeBy masterLess reducedTerm580 reducedTerm581 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge576Check : reducedMerge576 = Integer.Sparse.mergeBy masterLess reducedTerm582 reducedTerm583 := by decide +kernel

theorem reducedMerge577Check : reducedMerge577 = Integer.Sparse.mergeBy masterLess reducedMerge575 reducedMerge576 := by decide +kernel

theorem reducedMerge578Check : reducedMerge578 = Integer.Sparse.mergeBy masterLess reducedMerge574 reducedMerge577 := by decide +kernel

theorem reducedMerge579Check : reducedMerge579 = Integer.Sparse.mergeBy masterLess reducedMerge571 reducedMerge578 := by decide +kernel

theorem reducedMerge580Check : reducedMerge580 = Integer.Sparse.mergeBy masterLess reducedTerm585 reducedTerm586 := by decide +kernel

theorem reducedMerge581Check : reducedMerge581 = Integer.Sparse.mergeBy masterLess reducedTerm584 reducedMerge580 := by decide +kernel

theorem reducedMerge582Check : reducedMerge582 = Integer.Sparse.mergeBy masterLess reducedTerm587 reducedTerm588 := by decide +kernel

theorem reducedMerge583Check : reducedMerge583 = Integer.Sparse.mergeBy masterLess reducedTerm589 reducedTerm590 := by decide +kernel

theorem reducedMerge584Check : reducedMerge584 = Integer.Sparse.mergeBy masterLess reducedMerge582 reducedMerge583 := by decide +kernel

theorem reducedMerge585Check : reducedMerge585 = Integer.Sparse.mergeBy masterLess reducedMerge581 reducedMerge584 := by decide +kernel

theorem reducedMerge586Check : reducedMerge586 = Integer.Sparse.mergeBy masterLess reducedTerm591 reducedTerm592 := by decide +kernel

theorem reducedMerge587Check : reducedMerge587 = Integer.Sparse.mergeBy masterLess reducedTerm593 reducedTerm594 := by decide +kernel

theorem reducedMerge588Check : reducedMerge588 = Integer.Sparse.mergeBy masterLess reducedMerge586 reducedMerge587 := by decide +kernel

theorem reducedMerge589Check : reducedMerge589 = Integer.Sparse.mergeBy masterLess reducedTerm595 reducedTerm596 := by decide +kernel

theorem reducedMerge590Check : reducedMerge590 = Integer.Sparse.mergeBy masterLess reducedTerm597 reducedTerm598 := by decide +kernel

theorem reducedMerge591Check : reducedMerge591 = Integer.Sparse.mergeBy masterLess reducedMerge589 reducedMerge590 := by decide +kernel

theorem reducedMerge592Check : reducedMerge592 = Integer.Sparse.mergeBy masterLess reducedMerge588 reducedMerge591 := by decide +kernel

theorem reducedMerge593Check : reducedMerge593 = Integer.Sparse.mergeBy masterLess reducedMerge585 reducedMerge592 := by decide +kernel

theorem reducedMerge594Check : reducedMerge594 = Integer.Sparse.mergeBy masterLess reducedMerge579 reducedMerge593 := by decide +kernel

theorem reducedMerge595Check : reducedMerge595 = Integer.Sparse.mergeBy masterLess reducedMerge565 reducedMerge594 := by decide +kernel

theorem reducedMerge596Check : reducedMerge596 = Integer.Sparse.mergeBy masterLess reducedMerge536 reducedMerge595 := by decide +kernel

theorem reducedMerge597Check : reducedMerge597 = Integer.Sparse.mergeBy masterLess reducedTerm600 reducedTerm601 := by decide +kernel

theorem reducedMerge598Check : reducedMerge598 = Integer.Sparse.mergeBy masterLess reducedTerm599 reducedMerge597 := by decide +kernel

theorem reducedMerge599Check : reducedMerge599 = Integer.Sparse.mergeBy masterLess reducedTerm602 reducedTerm603 := by decide +kernel

theorem reducedMerge600Check : reducedMerge600 = Integer.Sparse.mergeBy masterLess reducedTerm604 reducedTerm605 := by decide +kernel

theorem reducedMerge601Check : reducedMerge601 = Integer.Sparse.mergeBy masterLess reducedMerge599 reducedMerge600 := by decide +kernel

theorem reducedMerge602Check : reducedMerge602 = Integer.Sparse.mergeBy masterLess reducedMerge598 reducedMerge601 := by decide +kernel

theorem reducedMerge603Check : reducedMerge603 = Integer.Sparse.mergeBy masterLess reducedTerm606 reducedTerm607 := by decide +kernel

theorem reducedMerge604Check : reducedMerge604 = Integer.Sparse.mergeBy masterLess reducedTerm608 reducedTerm609 := by decide +kernel

theorem reducedMerge605Check : reducedMerge605 = Integer.Sparse.mergeBy masterLess reducedMerge603 reducedMerge604 := by decide +kernel

theorem reducedMerge606Check : reducedMerge606 = Integer.Sparse.mergeBy masterLess reducedTerm610 reducedTerm611 := by decide +kernel

theorem reducedMerge607Check : reducedMerge607 = Integer.Sparse.mergeBy masterLess reducedTerm612 reducedTerm613 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge608Check : reducedMerge608 = Integer.Sparse.mergeBy masterLess reducedMerge606 reducedMerge607 := by decide +kernel

theorem reducedMerge609Check : reducedMerge609 = Integer.Sparse.mergeBy masterLess reducedMerge605 reducedMerge608 := by decide +kernel

theorem reducedMerge610Check : reducedMerge610 = Integer.Sparse.mergeBy masterLess reducedMerge602 reducedMerge609 := by decide +kernel

theorem reducedMerge611Check : reducedMerge611 = Integer.Sparse.mergeBy masterLess reducedTerm615 reducedTerm616 := by decide +kernel

theorem reducedMerge612Check : reducedMerge612 = Integer.Sparse.mergeBy masterLess reducedTerm614 reducedMerge611 := by decide +kernel

theorem reducedMerge613Check : reducedMerge613 = Integer.Sparse.mergeBy masterLess reducedTerm617 reducedTerm618 := by decide +kernel

theorem reducedMerge614Check : reducedMerge614 = Integer.Sparse.mergeBy masterLess reducedTerm619 reducedTerm620 := by decide +kernel

theorem reducedMerge615Check : reducedMerge615 = Integer.Sparse.mergeBy masterLess reducedMerge613 reducedMerge614 := by decide +kernel

theorem reducedMerge616Check : reducedMerge616 = Integer.Sparse.mergeBy masterLess reducedMerge612 reducedMerge615 := by decide +kernel

theorem reducedMerge617Check : reducedMerge617 = Integer.Sparse.mergeBy masterLess reducedTerm621 reducedTerm622 := by decide +kernel

theorem reducedMerge618Check : reducedMerge618 = Integer.Sparse.mergeBy masterLess reducedTerm623 reducedTerm624 := by decide +kernel

theorem reducedMerge619Check : reducedMerge619 = Integer.Sparse.mergeBy masterLess reducedMerge617 reducedMerge618 := by decide +kernel

theorem reducedMerge620Check : reducedMerge620 = Integer.Sparse.mergeBy masterLess reducedTerm625 reducedTerm626 := by decide +kernel

theorem reducedMerge621Check : reducedMerge621 = Integer.Sparse.mergeBy masterLess reducedTerm627 reducedTerm628 := by decide +kernel

theorem reducedMerge622Check : reducedMerge622 = Integer.Sparse.mergeBy masterLess reducedMerge620 reducedMerge621 := by decide +kernel

theorem reducedMerge623Check : reducedMerge623 = Integer.Sparse.mergeBy masterLess reducedMerge619 reducedMerge622 := by decide +kernel

theorem reducedMerge624Check : reducedMerge624 = Integer.Sparse.mergeBy masterLess reducedMerge616 reducedMerge623 := by decide +kernel

theorem reducedMerge625Check : reducedMerge625 = Integer.Sparse.mergeBy masterLess reducedMerge610 reducedMerge624 := by decide +kernel

theorem reducedMerge626Check : reducedMerge626 = Integer.Sparse.mergeBy masterLess reducedTerm630 reducedTerm631 := by decide +kernel

theorem reducedMerge627Check : reducedMerge627 = Integer.Sparse.mergeBy masterLess reducedTerm629 reducedMerge626 := by decide +kernel

theorem reducedMerge628Check : reducedMerge628 = Integer.Sparse.mergeBy masterLess reducedTerm632 reducedTerm633 := by decide +kernel

theorem reducedMerge629Check : reducedMerge629 = Integer.Sparse.mergeBy masterLess reducedTerm634 reducedTerm635 := by decide +kernel

theorem reducedMerge630Check : reducedMerge630 = Integer.Sparse.mergeBy masterLess reducedMerge628 reducedMerge629 := by decide +kernel

theorem reducedMerge631Check : reducedMerge631 = Integer.Sparse.mergeBy masterLess reducedMerge627 reducedMerge630 := by decide +kernel

theorem reducedMerge632Check : reducedMerge632 = Integer.Sparse.mergeBy masterLess reducedTerm636 reducedTerm637 := by decide +kernel

theorem reducedMerge633Check : reducedMerge633 = Integer.Sparse.mergeBy masterLess reducedTerm638 reducedTerm639 := by decide +kernel

theorem reducedMerge634Check : reducedMerge634 = Integer.Sparse.mergeBy masterLess reducedMerge632 reducedMerge633 := by decide +kernel

theorem reducedMerge635Check : reducedMerge635 = Integer.Sparse.mergeBy masterLess reducedTerm640 reducedTerm641 := by decide +kernel

theorem reducedMerge636Check : reducedMerge636 = Integer.Sparse.mergeBy masterLess reducedTerm642 reducedTerm643 := by decide +kernel

theorem reducedMerge637Check : reducedMerge637 = Integer.Sparse.mergeBy masterLess reducedMerge635 reducedMerge636 := by decide +kernel

theorem reducedMerge638Check : reducedMerge638 = Integer.Sparse.mergeBy masterLess reducedMerge634 reducedMerge637 := by decide +kernel

theorem reducedMerge639Check : reducedMerge639 = Integer.Sparse.mergeBy masterLess reducedMerge631 reducedMerge638 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge640Check : reducedMerge640 = Integer.Sparse.mergeBy masterLess reducedTerm645 reducedTerm646 := by decide +kernel

theorem reducedMerge641Check : reducedMerge641 = Integer.Sparse.mergeBy masterLess reducedTerm644 reducedMerge640 := by decide +kernel

theorem reducedMerge642Check : reducedMerge642 = Integer.Sparse.mergeBy masterLess reducedTerm647 reducedTerm648 := by decide +kernel

theorem reducedMerge643Check : reducedMerge643 = Integer.Sparse.mergeBy masterLess reducedTerm649 reducedTerm650 := by decide +kernel

theorem reducedMerge644Check : reducedMerge644 = Integer.Sparse.mergeBy masterLess reducedMerge642 reducedMerge643 := by decide +kernel

theorem reducedMerge645Check : reducedMerge645 = Integer.Sparse.mergeBy masterLess reducedMerge641 reducedMerge644 := by decide +kernel

theorem reducedMerge646Check : reducedMerge646 = Integer.Sparse.mergeBy masterLess reducedTerm651 reducedTerm652 := by decide +kernel

theorem reducedMerge647Check : reducedMerge647 = Integer.Sparse.mergeBy masterLess reducedTerm653 reducedTerm654 := by decide +kernel

theorem reducedMerge648Check : reducedMerge648 = Integer.Sparse.mergeBy masterLess reducedMerge646 reducedMerge647 := by decide +kernel

theorem reducedMerge649Check : reducedMerge649 = Integer.Sparse.mergeBy masterLess reducedTerm655 reducedTerm656 := by decide +kernel

theorem reducedMerge650Check : reducedMerge650 = Integer.Sparse.mergeBy masterLess reducedTerm657 reducedTerm658 := by decide +kernel

theorem reducedMerge651Check : reducedMerge651 = Integer.Sparse.mergeBy masterLess reducedMerge649 reducedMerge650 := by decide +kernel

theorem reducedMerge652Check : reducedMerge652 = Integer.Sparse.mergeBy masterLess reducedMerge648 reducedMerge651 := by decide +kernel

theorem reducedMerge653Check : reducedMerge653 = Integer.Sparse.mergeBy masterLess reducedMerge645 reducedMerge652 := by decide +kernel

theorem reducedMerge654Check : reducedMerge654 = Integer.Sparse.mergeBy masterLess reducedMerge639 reducedMerge653 := by decide +kernel

theorem reducedMerge655Check : reducedMerge655 = Integer.Sparse.mergeBy masterLess reducedMerge625 reducedMerge654 := by decide +kernel

theorem reducedMerge656Check : reducedMerge656 = Integer.Sparse.mergeBy masterLess reducedTerm660 reducedTerm661 := by decide +kernel

theorem reducedMerge657Check : reducedMerge657 = Integer.Sparse.mergeBy masterLess reducedTerm659 reducedMerge656 := by decide +kernel

theorem reducedMerge658Check : reducedMerge658 = Integer.Sparse.mergeBy masterLess reducedTerm662 reducedTerm663 := by decide +kernel

theorem reducedMerge659Check : reducedMerge659 = Integer.Sparse.mergeBy masterLess reducedTerm664 reducedTerm665 := by decide +kernel

theorem reducedMerge660Check : reducedMerge660 = Integer.Sparse.mergeBy masterLess reducedMerge658 reducedMerge659 := by decide +kernel

theorem reducedMerge661Check : reducedMerge661 = Integer.Sparse.mergeBy masterLess reducedMerge657 reducedMerge660 := by decide +kernel

theorem reducedMerge662Check : reducedMerge662 = Integer.Sparse.mergeBy masterLess reducedTerm666 reducedTerm667 := by decide +kernel

theorem reducedMerge663Check : reducedMerge663 = Integer.Sparse.mergeBy masterLess reducedTerm668 reducedTerm669 := by decide +kernel

theorem reducedMerge664Check : reducedMerge664 = Integer.Sparse.mergeBy masterLess reducedMerge662 reducedMerge663 := by decide +kernel

theorem reducedMerge665Check : reducedMerge665 = Integer.Sparse.mergeBy masterLess reducedTerm670 reducedTerm671 := by decide +kernel

theorem reducedMerge666Check : reducedMerge666 = Integer.Sparse.mergeBy masterLess reducedTerm672 reducedTerm673 := by decide +kernel

theorem reducedMerge667Check : reducedMerge667 = Integer.Sparse.mergeBy masterLess reducedMerge665 reducedMerge666 := by decide +kernel

theorem reducedMerge668Check : reducedMerge668 = Integer.Sparse.mergeBy masterLess reducedMerge664 reducedMerge667 := by decide +kernel

theorem reducedMerge669Check : reducedMerge669 = Integer.Sparse.mergeBy masterLess reducedMerge661 reducedMerge668 := by decide +kernel

theorem reducedMerge670Check : reducedMerge670 = Integer.Sparse.mergeBy masterLess reducedTerm675 reducedTerm676 := by decide +kernel

theorem reducedMerge671Check : reducedMerge671 = Integer.Sparse.mergeBy masterLess reducedTerm674 reducedMerge670 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge672Check : reducedMerge672 = Integer.Sparse.mergeBy masterLess reducedTerm677 reducedTerm678 := by decide +kernel

theorem reducedMerge673Check : reducedMerge673 = Integer.Sparse.mergeBy masterLess reducedTerm679 reducedTerm680 := by decide +kernel

theorem reducedMerge674Check : reducedMerge674 = Integer.Sparse.mergeBy masterLess reducedMerge672 reducedMerge673 := by decide +kernel

theorem reducedMerge675Check : reducedMerge675 = Integer.Sparse.mergeBy masterLess reducedMerge671 reducedMerge674 := by decide +kernel

theorem reducedMerge676Check : reducedMerge676 = Integer.Sparse.mergeBy masterLess reducedTerm681 reducedTerm682 := by decide +kernel

theorem reducedMerge677Check : reducedMerge677 = Integer.Sparse.mergeBy masterLess reducedTerm683 reducedTerm684 := by decide +kernel

theorem reducedMerge678Check : reducedMerge678 = Integer.Sparse.mergeBy masterLess reducedMerge676 reducedMerge677 := by decide +kernel

theorem reducedMerge679Check : reducedMerge679 = Integer.Sparse.mergeBy masterLess reducedTerm685 reducedTerm686 := by decide +kernel

theorem reducedMerge680Check : reducedMerge680 = Integer.Sparse.mergeBy masterLess reducedTerm687 reducedTerm688 := by decide +kernel

theorem reducedMerge681Check : reducedMerge681 = Integer.Sparse.mergeBy masterLess reducedMerge679 reducedMerge680 := by decide +kernel

theorem reducedMerge682Check : reducedMerge682 = Integer.Sparse.mergeBy masterLess reducedMerge678 reducedMerge681 := by decide +kernel

theorem reducedMerge683Check : reducedMerge683 = Integer.Sparse.mergeBy masterLess reducedMerge675 reducedMerge682 := by decide +kernel

theorem reducedMerge684Check : reducedMerge684 = Integer.Sparse.mergeBy masterLess reducedMerge669 reducedMerge683 := by decide +kernel

theorem reducedMerge685Check : reducedMerge685 = Integer.Sparse.mergeBy masterLess reducedTerm690 reducedTerm691 := by decide +kernel

theorem reducedMerge686Check : reducedMerge686 = Integer.Sparse.mergeBy masterLess reducedTerm689 reducedMerge685 := by decide +kernel

theorem reducedMerge687Check : reducedMerge687 = Integer.Sparse.mergeBy masterLess reducedTerm692 reducedTerm693 := by decide +kernel

theorem reducedMerge688Check : reducedMerge688 = Integer.Sparse.mergeBy masterLess reducedTerm694 reducedTerm695 := by decide +kernel

theorem reducedMerge689Check : reducedMerge689 = Integer.Sparse.mergeBy masterLess reducedMerge687 reducedMerge688 := by decide +kernel

theorem reducedMerge690Check : reducedMerge690 = Integer.Sparse.mergeBy masterLess reducedMerge686 reducedMerge689 := by decide +kernel

theorem reducedMerge691Check : reducedMerge691 = Integer.Sparse.mergeBy masterLess reducedTerm696 reducedTerm697 := by decide +kernel

theorem reducedMerge692Check : reducedMerge692 = Integer.Sparse.mergeBy masterLess reducedTerm698 reducedTerm699 := by decide +kernel

theorem reducedMerge693Check : reducedMerge693 = Integer.Sparse.mergeBy masterLess reducedMerge691 reducedMerge692 := by decide +kernel

theorem reducedMerge694Check : reducedMerge694 = Integer.Sparse.mergeBy masterLess reducedTerm700 reducedTerm701 := by decide +kernel

theorem reducedMerge695Check : reducedMerge695 = Integer.Sparse.mergeBy masterLess reducedTerm702 reducedTerm703 := by decide +kernel

theorem reducedMerge696Check : reducedMerge696 = Integer.Sparse.mergeBy masterLess reducedMerge694 reducedMerge695 := by decide +kernel

theorem reducedMerge697Check : reducedMerge697 = Integer.Sparse.mergeBy masterLess reducedMerge693 reducedMerge696 := by decide +kernel

theorem reducedMerge698Check : reducedMerge698 = Integer.Sparse.mergeBy masterLess reducedMerge690 reducedMerge697 := by decide +kernel

theorem reducedMerge699Check : reducedMerge699 = Integer.Sparse.mergeBy masterLess reducedTerm705 reducedTerm706 := by decide +kernel

theorem reducedMerge700Check : reducedMerge700 = Integer.Sparse.mergeBy masterLess reducedTerm704 reducedMerge699 := by decide +kernel

theorem reducedMerge701Check : reducedMerge701 = Integer.Sparse.mergeBy masterLess reducedTerm707 reducedTerm708 := by decide +kernel

theorem reducedMerge702Check : reducedMerge702 = Integer.Sparse.mergeBy masterLess reducedTerm709 reducedTerm710 := by decide +kernel

theorem reducedMerge703Check : reducedMerge703 = Integer.Sparse.mergeBy masterLess reducedMerge701 reducedMerge702 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge704Check : reducedMerge704 = Integer.Sparse.mergeBy masterLess reducedMerge700 reducedMerge703 := by decide +kernel

theorem reducedMerge705Check : reducedMerge705 = Integer.Sparse.mergeBy masterLess reducedTerm711 reducedTerm712 := by decide +kernel

theorem reducedMerge706Check : reducedMerge706 = Integer.Sparse.mergeBy masterLess reducedTerm713 reducedTerm714 := by decide +kernel

theorem reducedMerge707Check : reducedMerge707 = Integer.Sparse.mergeBy masterLess reducedMerge705 reducedMerge706 := by decide +kernel

theorem reducedMerge708Check : reducedMerge708 = Integer.Sparse.mergeBy masterLess reducedTerm715 reducedTerm716 := by decide +kernel

theorem reducedMerge709Check : reducedMerge709 = Integer.Sparse.mergeBy masterLess reducedTerm717 reducedTerm718 := by decide +kernel

theorem reducedMerge710Check : reducedMerge710 = Integer.Sparse.mergeBy masterLess reducedMerge708 reducedMerge709 := by decide +kernel

theorem reducedMerge711Check : reducedMerge711 = Integer.Sparse.mergeBy masterLess reducedMerge707 reducedMerge710 := by decide +kernel

theorem reducedMerge712Check : reducedMerge712 = Integer.Sparse.mergeBy masterLess reducedMerge704 reducedMerge711 := by decide +kernel

theorem reducedMerge713Check : reducedMerge713 = Integer.Sparse.mergeBy masterLess reducedMerge698 reducedMerge712 := by decide +kernel

theorem reducedMerge714Check : reducedMerge714 = Integer.Sparse.mergeBy masterLess reducedMerge684 reducedMerge713 := by decide +kernel

theorem reducedMerge715Check : reducedMerge715 = Integer.Sparse.mergeBy masterLess reducedMerge655 reducedMerge714 := by decide +kernel

theorem reducedMerge716Check : reducedMerge716 = Integer.Sparse.mergeBy masterLess reducedMerge596 reducedMerge715 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval479 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm479 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm479 (originalVector B) := by
  rw [reducedTermArithmetic479, ← sound639 B hB hF]
  change (-3501219910680576000000 : ℝ) * mixedMoment B node639 node639Labels =
    (37623398400 : ℝ) * (((-93059640000 : ℤ) : ℝ) * mixedMoment B node639 node639Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval480 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm480 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm480 (originalVector B) := by
  rw [reducedTermArithmetic480, ← sound640 B hB hF]
  change (-5023829814312960000000 : ℝ) * mixedMoment B node640 node640Labels =
    (37623398400 : ℝ) * (((-133529400000 : ℤ) : ℝ) * mixedMoment B node640 node640Labels + 0)
  ring

theorem reducedTermEval481 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm481 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm481 (originalVector B) := by
  rw [reducedTermArithmetic481, ← sound641 B hB hF]
  change (2600840819146752000000 : ℝ) * mixedMoment B node641 node641Labels =
    (37623398400 : ℝ) * ((69128280000 : ℝ) * mixedMoment B node641 node641Labels + 0)
  ring

theorem reducedTermEval482 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm482 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm482 (originalVector B) := by
  rw [reducedTermArithmetic482, ← sound642 B hB hF]
  change (-7838560195140648960000 : ℝ) * mixedMoment B node642 node642Labels =
    (37623398400 : ℝ) * (((-208342694400 : ℤ) : ℝ) * mixedMoment B node642 node642Labels + 0)
  ring

theorem reducedTermEval483 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm483 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm483 (originalVector B) := by
  rw [reducedTermArithmetic483, ← sound643 B hB hF]
  change (3501219910680576000000 : ℝ) * mixedMoment B node643 node643Labels =
    (37623398400 : ℝ) * ((93059640000 : ℝ) * mixedMoment B node643 node643Labels + 0)
  ring

theorem reducedTermEval484 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm484 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm484 (originalVector B) := by
  rw [reducedTermArithmetic484, ← sound653 B hB hF]
  change (892167378500321280000 : ℝ) * mixedMoment B node653 node653Labels =
    (37623398400 : ℝ) * ((23713099200 : ℝ) * mixedMoment B node653 node653Labels + 0)
  ring

theorem reducedTermEval485 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm485 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm485 (originalVector B) := by
  rw [reducedTermArithmetic485, ← sound654 B hB hF]
  change (315973519843000320000 : ℝ) * mixedMoment B node654 node654Labels =
    (37623398400 : ℝ) * ((8398324800 : ℝ) * mixedMoment B node654 node654Labels + 0)
  ring

theorem reducedTermEval486 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm486 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm486 (originalVector B) := by
  rw [reducedTermArithmetic486, ← sound909 B hB hF]
  change (8659257895151861760000 : ℝ) * mixedMoment B node909 node909Labels =
    (37623398400 : ℝ) * ((230156186400 : ℝ) * mixedMoment B node909 node909Labels + 0)
  ring

theorem reducedTermEval487 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm487 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm487 (originalVector B) := by
  rw [reducedTermArithmetic487, ← sound911 B hB hF]
  change (7407336363717427200000 : ℝ) * mixedMoment B node911 node911Labels =
    (37623398400 : ℝ) * ((196881108000 : ℝ) * mixedMoment B node911 node911Labels + 0)
  ring

theorem reducedTermEval488 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm488 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm488 (originalVector B) := by
  rw [reducedTermArithmetic488, ← sound914 B hB hF]
  change (8137792988223897600000 : ℝ) * mixedMoment B node914 node914Labels =
    (37623398400 : ℝ) * ((216296064000 : ℝ) * mixedMoment B node914 node914Labels + 0)
  ring

theorem reducedTermEval489 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm489 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm489 (originalVector B) := by
  rw [reducedTermArithmetic489, ← sound922 B hB hF]
  change (842806262366208000000 : ℝ) * mixedMoment B node922 node922Labels =
    (37623398400 : ℝ) * ((22401120000 : ℝ) * mixedMoment B node922 node922Labels + 0)
  ring

theorem reducedTermEval490 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm490 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm490 (originalVector B) := by
  rw [reducedTermArithmetic490, ← sound929 B hB hF]
  change (-941481721225543680000 : ℝ) * mixedMoment B node929 node929Labels =
    (37623398400 : ℝ) * (((-25023835200 : ℤ) : ℝ) * mixedMoment B node929 node929Labels + 0)
  ring

theorem reducedTermEval491 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm491 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm491 (originalVector B) := by
  rw [reducedTermArithmetic491, ← sound930 B hB hF]
  change (-4522163694065418240000 : ℝ) * mixedMoment B node930 node930Labels =
    (37623398400 : ℝ) * (((-120195513600 : ℤ) : ℝ) * mixedMoment B node930 node930Labels + 0)
  ring

theorem reducedTermEval492 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm492 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm492 (originalVector B) := by
  rw [reducedTermArithmetic492, ← sound931 B hB hF]
  change (862331180804997120000 : ℝ) * mixedMoment B node931 node931Labels =
    (37623398400 : ℝ) * ((22920076800 : ℝ) * mixedMoment B node931 node931Labels + 0)
  ring

theorem reducedTermEval493 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm493 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm493 (originalVector B) := by
  rw [reducedTermArithmetic493, ← sound932 B hB hF]
  change (-2281209943794647040000 : ℝ) * mixedMoment B node932 node932Labels =
    (37623398400 : ℝ) * (((-60632745600 : ℤ) : ℝ) * mixedMoment B node932 node932Labels + 0)
  ring

theorem reducedTermEval494 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm494 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm494 (originalVector B) := by
  rw [reducedTermArithmetic494, ← sound933 B hB hF]
  change (-842806262366208000000 : ℝ) * mixedMoment B node933 node933Labels =
    (37623398400 : ℝ) * (((-22401120000 : ℤ) : ℝ) * mixedMoment B node933 node933Labels + 0)
  ring

theorem reducedTermEval495 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm495 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm495 (originalVector B) := by
  rw [reducedTermArithmetic495, ← sound934 B hB hF]
  change (1048155974782156800000 : ℝ) * mixedMoment B node934 node934Labels =
    (37623398400 : ℝ) * ((27859152000 : ℝ) * mixedMoment B node934 node934Labels + 0)
  ring

theorem reducedTermEval496 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm496 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm496 (originalVector B) := by
  rw [reducedTermArithmetic496, ← sound936 B hB hF]
  change (-3501622812129361920000 : ℝ) * mixedMoment B node936 node936Labels =
    (37623398400 : ℝ) * (((-93070348800 : ℤ) : ℝ) * mixedMoment B node936 node936Labels + 0)
  ring

theorem reducedTermEval497 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm497 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm497 (originalVector B) := by
  rw [reducedTermArithmetic497, ← sound937 B hB hF]
  change (-690110044530278400000 : ℝ) * mixedMoment B node937 node937Labels =
    (37623398400 : ℝ) * (((-18342576000 : ℤ) : ℝ) * mixedMoment B node937 node937Labels + 0)
  ring

theorem reducedTermEval498 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm498 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm498 (originalVector B) := by
  rw [reducedTermArithmetic498, ← sound939 B hB hF]
  change (-5644648033344552960000 : ℝ) * mixedMoment B node939 node939Labels =
    (37623398400 : ℝ) * (((-150030254400 : ℤ) : ℝ) * mixedMoment B node939 node939Labels + 0)
  ring

theorem reducedTermEval499 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm499 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm499 (originalVector B) := by
  rw [reducedTermArithmetic499, ← sound940 B hB hF]
  change (-3110224913045913600000 : ℝ) * mixedMoment B node940 node940Labels =
    (37623398400 : ℝ) * (((-82667304000 : ℤ) : ℝ) * mixedMoment B node940 node940Labels + 0)
  ring

theorem reducedTermEval500 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm500 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm500 (originalVector B) := by
  rw [reducedTermArithmetic500, ← sound944 B hB hF]
  change (5755499567677440000000 : ℝ) * mixedMoment B node944 node944Labels =
    (37623398400 : ℝ) * ((152976600000 : ℝ) * mixedMoment B node944 node944Labels + 0)
  ring

theorem reducedTermEval501 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm501 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm501 (originalVector B) := by
  rw [reducedTermArithmetic501, ← sound945 B hB hF]
  change (5755499567677440000000 : ℝ) * mixedMoment B node945 node945Labels =
    (37623398400 : ℝ) * ((152976600000 : ℝ) * mixedMoment B node945 node945Labels + 0)
  ring

theorem reducedTermEval502 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm502 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm502 (originalVector B) := by
  rw [reducedTermArithmetic502, ← sound946 B hB hF]
  change (4959624732475392000000 : ℝ) * mixedMoment B node946 node946Labels =
    (37623398400 : ℝ) * ((131822880000 : ℝ) * mixedMoment B node946 node946Labels + 0)
  ring

theorem reducedTermEval503 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm503 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm503 (originalVector B) := by
  rw [reducedTermArithmetic503, ← sound949 B hB hF]
  change (-7458564352880148480000 : ℝ) * mixedMoment B node949 node949Labels =
    (37623398400 : ℝ) * (((-198242707200 : ℤ) : ℝ) * mixedMoment B node949 node949Labels + 0)
  ring

theorem reducedTermEval504 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm504 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm504 (originalVector B) := by
  rw [reducedTermArithmetic504, ← sound950 B hB hF]
  change (-5755499567677440000000 : ℝ) * mixedMoment B node950 node950Labels =
    (37623398400 : ℝ) * (((-152976600000 : ℤ) : ℝ) * mixedMoment B node950 node950Labels + 0)
  ring

theorem reducedTermEval505 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm505 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm505 (originalVector B) := by
  rw [reducedTermArithmetic505, ← sound951 B hB hF]
  change (7458564352880148480000 : ℝ) * mixedMoment B node951 node951Labels =
    (37623398400 : ℝ) * ((198242707200 : ℝ) * mixedMoment B node951 node951Labels + 0)
  ring

theorem reducedTermEval506 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm506 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm506 (originalVector B) := by
  rw [reducedTermArithmetic506, ← sound952 B hB hF]
  change (-4959624732475392000000 : ℝ) * mixedMoment B node952 node952Labels =
    (37623398400 : ℝ) * (((-131822880000 : ℤ) : ℝ) * mixedMoment B node952 node952Labels + 0)
  ring

theorem reducedTermEval507 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm507 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm507 (originalVector B) := by
  rw [reducedTermArithmetic507, ← sound953 B hB hF]
  change (-5755499567677440000000 : ℝ) * mixedMoment B node953 node953Labels =
    (37623398400 : ℝ) * (((-152976600000 : ℤ) : ℝ) * mixedMoment B node953 node953Labels + 0)
  ring

theorem reducedTermEval508 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm508 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm508 (originalVector B) := by
  rw [reducedTermArithmetic508, ← sound954 B hB hF]
  change (-3501219910680576000000 : ℝ) * mixedMoment B node954 node954Labels =
    (37623398400 : ℝ) * (((-93059640000 : ℤ) : ℝ) * mixedMoment B node954 node954Labels + 0)
  ring

theorem reducedTermEval509 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm509 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm509 (originalVector B) := by
  rw [reducedTermArithmetic509, ← sound1024 B hB hF]
  change (-2976678613712240640000 : ℝ) * mixedMoment B node1024 node1024Labels =
    (37623398400 : ℝ) * (((-79117749600 : ℤ) : ℝ) * mixedMoment B node1024 node1024Labels + 0)
  ring

theorem reducedTermEval510 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm510 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm510 (originalVector B) := by
  rw [reducedTermArithmetic510, ← sound1027 B hB hF]
  change (-4206296272205905920000 : ℝ) * mixedMoment B node1027 node1027Labels =
    (37623398400 : ℝ) * (((-111800008800 : ℤ) : ℝ) * mixedMoment B node1027 node1027Labels + 0)
  ring

theorem reducedTermEval511 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm511 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm511 (originalVector B) := by
  rw [reducedTermArithmetic511, ← sound1039 B hB hF]
  change (84218592777338880000 : ℝ) * mixedMoment B node1039 node1039Labels =
    (37623398400 : ℝ) * ((2238463200 : ℝ) * mixedMoment B node1039 node1039Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval478 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge478 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge478 (originalVector B) := by
  rw [reducedMerge478Check, Integer.Sparse.eval_mergeBy, reducedTermEval480 B hB hF, reducedTermEval481 B hB hF]
  rw [originalMerge478, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval479 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge479 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge479 (originalVector B) := by
  rw [reducedMerge479Check, Integer.Sparse.eval_mergeBy, reducedTermEval479 B hB hF, reducedMergeEval478 B hB hF]
  rw [originalMerge479, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval512 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm512 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm512 (originalVector B) := by
  rw [reducedTermArithmetic512, ← sound1041 B hB hF]
  change (-1011243447920885760000 : ℝ) * mixedMoment B node1041 node1041Labels =
    (37623398400 : ℝ) * (((-26878046400 : ℤ) : ℝ) * mixedMoment B node1041 node1041Labels + 0)
  ring

theorem reducedTermEval513 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm513 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm513 (originalVector B) := by
  rw [reducedTermArithmetic513, ← sound1044 B hB hF]
  change (-2007773678972436480000 : ℝ) * mixedMoment B node1044 node1044Labels =
    (37623398400 : ℝ) * (((-53365027200 : ℤ) : ℝ) * mixedMoment B node1044 node1044Labels + 0)
  ring

theorem reducedTermEval514 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm514 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm514 (originalVector B) := by
  rw [reducedTermArithmetic514, ← sound1046 B hB hF]
  change (10725266364412723200000 : ℝ) * mixedMoment B node1046 node1046Labels =
    (37623398400 : ℝ) * ((285069048000 : ℝ) * mixedMoment B node1046 node1046Labels + 0)
  ring

theorem reducedTermEval515 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm515 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm515 (originalVector B) := by
  rw [reducedTermArithmetic515, ← sound1047 B hB hF]
  change (-13781464017158799360000 : ℝ) * mixedMoment B node1047 node1047Labels =
    (37623398400 : ℝ) * (((-366300350400 : ℤ) : ℝ) * mixedMoment B node1047 node1047Labels + 0)
  ring

theorem reducedTermEval516 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm516 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm516 (originalVector B) := by
  rw [reducedTermArithmetic516, ← sound1049 B hB hF]
  change (1567784528782295040000 : ℝ) * mixedMoment B node1049 node1049Labels =
    (37623398400 : ℝ) * ((41670465600 : ℝ) * mixedMoment B node1049 node1049Labels + 0)
  ring

theorem reducedTermEval517 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm517 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm517 (originalVector B) := by
  rw [reducedTermArithmetic517, ← sound1050 B hB hF]
  change (927024855143546880000 : ℝ) * mixedMoment B node1050 node1050Labels =
    (37623398400 : ℝ) * ((24639583200 : ℝ) * mixedMoment B node1050 node1050Labels + 0)
  ring

theorem reducedTermEval518 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm518 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm518 (originalVector B) := by
  rw [reducedTermArithmetic518, ← sound1051 B hB hF]
  change (1191593947134689280000 : ℝ) * mixedMoment B node1051 node1051Labels =
    (37623398400 : ℝ) * ((31671619200 : ℝ) * mixedMoment B node1051 node1051Labels + 0)
  ring

theorem reducedTermEval519 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm519 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm519 (originalVector B) := by
  rw [reducedTermArithmetic519, ← sound1058 B hB hF]
  change (6300739362226176000000 : ℝ) * mixedMoment B node1058 node1058Labels =
    (37623398400 : ℝ) * ((167468640000 : ℝ) * mixedMoment B node1058 node1058Labels + 0)
  ring

theorem reducedTermEval520 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm520 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm520 (originalVector B) := by
  rw [reducedTermArithmetic520, ← sound1061 B hB hF]
  change (-3750701327642787840000 : ℝ) * mixedMoment B node1061 node1061Labels =
    (37623398400 : ℝ) * (((-99690657600 : ℤ) : ℝ) * mixedMoment B node1061 node1061Labels + 0)
  ring

theorem reducedTermEval521 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm521 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm521 (originalVector B) := by
  rw [reducedTermArithmetic521, ← sound1063 B hB hF]
  change (-6300739362226176000000 : ℝ) * mixedMoment B node1063 node1063Labels =
    (37623398400 : ℝ) * (((-167468640000 : ℤ) : ℝ) * mixedMoment B node1063 node1063Labels + 0)
  ring

theorem reducedTermEval522 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm522 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm522 (originalVector B) := by
  rw [reducedTermArithmetic522, ← sound1064 B hB hF]
  change (3750701327642787840000 : ℝ) * mixedMoment B node1064 node1064Labels =
    (37623398400 : ℝ) * ((99690657600 : ℝ) * mixedMoment B node1064 node1064Labels + 0)
  ring

theorem reducedTermEval523 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm523 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm523 (originalVector B) := by
  rw [reducedTermArithmetic523, ← sound1087 B hB hF]
  change (-8631272678361661440000 : ℝ) * mixedMoment B node1087 node1087Labels =
    (37623398400 : ℝ) * (((-229412361600 : ℤ) : ℝ) * mixedMoment B node1087 node1087Labels + 0)
  ring

theorem reducedTermEval524 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm524 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm524 (originalVector B) := by
  rw [reducedTermArithmetic524, ← sound1091 B hB hF]
  change (7331333818189086720000 : ℝ) * mixedMoment B node1091 node1091Labels =
    (37623398400 : ℝ) * ((194861020800 : ℝ) * mixedMoment B node1091 node1091Labels + 0)
  ring

theorem reducedTermEval525 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm525 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm525 (originalVector B) := by
  rw [reducedTermArithmetic525, ← sound1094 B hB hF]
  change (-2107338916154572800000 : ℝ) * mixedMoment B node1094 node1094Labels =
    (37623398400 : ℝ) * (((-56011392000 : ℤ) : ℝ) * mixedMoment B node1094 node1094Labels + 0)
  ring

theorem reducedTermEval526 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm526 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm526 (originalVector B) := by
  rw [reducedTermArithmetic526, ← sound1111 B hB hF]
  change (94866766992506880000 : ℝ) * mixedMoment B node1111 node1111Labels =
    (37623398400 : ℝ) * ((2521483200 : ℝ) * mixedMoment B node1111 node1111Labels + 0)
  ring

theorem reducedTermEval527 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm527 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm527 (originalVector B) := by
  rw [reducedTermArithmetic527, ← sound1112 B hB hF]
  change (-26389657073487052800000 : ℝ) * mixedMoment B node1112 node1112Labels =
    (37623398400 : ℝ) * (((-701416092000 : ℤ) : ℝ) * mixedMoment B node1112 node1112Labels + 0)
  ring

theorem reducedTermEval528 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm528 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm528 (originalVector B) := by
  rw [reducedTermArithmetic528, ← sound1113 B hB hF]
  change (-8810814575497052160000 : ℝ) * mixedMoment B node1113 node1113Labels =
    (37623398400 : ℝ) * (((-234184442400 : ℤ) : ℝ) * mixedMoment B node1113 node1113Labels + 0)
  ring

theorem reducedTermEval529 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm529 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm529 (originalVector B) := by
  rw [reducedTermArithmetic529, ← sound1115 B hB hF]
  change (-1573216023167631360000 : ℝ) * mixedMoment B node1115 node1115Labels =
    (37623398400 : ℝ) * (((-41814830400 : ℤ) : ℝ) * mixedMoment B node1115 node1115Labels + 0)
  ring

theorem reducedTermEval530 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm530 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm530 (originalVector B) := by
  rw [reducedTermArithmetic530, ← sound1116 B hB hF]
  change (-1126879414384066560000 : ℝ) * mixedMoment B node1116 node1116Labels =
    (37623398400 : ℝ) * (((-29951558400 : ℤ) : ℝ) * mixedMoment B node1116 node1116Labels + 0)
  ring

theorem reducedTermEval531 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm531 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm531 (originalVector B) := by
  rw [reducedTermArithmetic531, ← sound1117 B hB hF]
  change (-250586732209766400000 : ℝ) * mixedMoment B node1117 node1117Labels =
    (37623398400 : ℝ) * (((-6660396000 : ℤ) : ℝ) * mixedMoment B node1117 node1117Labels + 0)
  ring

theorem reducedTermEval532 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm532 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm532 (originalVector B) := by
  rw [reducedTermArithmetic532, ← sound1118 B hB hF]
  change (4772950974038016000000 : ℝ) * mixedMoment B node1118 node1118Labels =
    (37623398400 : ℝ) * ((126861240000 : ℝ) * mixedMoment B node1118 node1118Labels + 0)
  ring

theorem reducedTermEval533 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm533 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm533 (originalVector B) := by
  rw [reducedTermArithmetic533, ← sound1119 B hB hF]
  change (-1307377367220879360000 : ℝ) * mixedMoment B node1119 node1119Labels =
    (37623398400 : ℝ) * (((-34749050400 : ℤ) : ℝ) * mixedMoment B node1119 node1119Labels + 0)
  ring

theorem reducedTermEval534 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm534 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm534 (originalVector B) := by
  rw [reducedTermArithmetic534, ← sound1120 B hB hF]
  change (6812136157446144000000 : ℝ) * mixedMoment B node1120 node1120Labels =
    (37623398400 : ℝ) * ((181061160000 : ℝ) * mixedMoment B node1120 node1120Labels + 0)
  ring

theorem reducedTermEval535 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm535 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm535 (originalVector B) := by
  rw [reducedTermArithmetic535, ← sound1121 B hB hF]
  change (-8762782347893145600000 : ℝ) * mixedMoment B node1121 node1121Labels =
    (37623398400 : ℝ) * (((-232907784000 : ℤ) : ℝ) * mixedMoment B node1121 node1121Labels + 0)
  ring

theorem reducedTermEval536 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm536 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm536 (originalVector B) := by
  rw [reducedTermArithmetic536, ← sound1125 B hB hF]
  change (416003421044736000000 : ℝ) * mixedMoment B node1125 node1125Labels =
    (37623398400 : ℝ) * ((11057040000 : ℝ) * mixedMoment B node1125 node1125Labels + 0)
  ring

theorem reducedTermEval537 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm537 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm537 (originalVector B) := by
  rw [reducedTermArithmetic537, ← sound1126 B hB hF]
  change (3128439995443445760000 : ℝ) * mixedMoment B node1126 node1126Labels =
    (37623398400 : ℝ) * ((83151446400 : ℝ) * mixedMoment B node1126 node1126Labels + 0)
  ring

theorem reducedTermEval538 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm538 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm538 (originalVector B) := by
  rw [reducedTermArithmetic538, ← sound1128 B hB hF]
  change (331078441437757440000 : ℝ) * mixedMoment B node1128 node1128Labels =
    (37623398400 : ℝ) * ((8799801600 : ℝ) * mixedMoment B node1128 node1128Labels + 0)
  ring

theorem reducedTermEval539 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm539 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm539 (originalVector B) := by
  rw [reducedTermArithmetic539, ← sound1129 B hB hF]
  change (19378969510926090240000 : ℝ) * mixedMoment B node1129 node1129Labels =
    (37623398400 : ℝ) * ((515077593600 : ℝ) * mixedMoment B node1129 node1129Labels + 0)
  ring

theorem reducedTermEval540 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm540 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm540 (originalVector B) := by
  rw [reducedTermArithmetic540, ← sound1130 B hB hF]
  change (-9464678117613895680000 : ℝ) * mixedMoment B node1130 node1130Labels =
    (37623398400 : ℝ) * (((-251563615200 : ℤ) : ℝ) * mixedMoment B node1130 node1130Labels + 0)
  ring

theorem reducedTermEval541 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm541 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm541 (originalVector B) := by
  rw [reducedTermArithmetic541, ← sound1131 B hB hF]
  change (5641023726228602880000 : ℝ) * mixedMoment B node1131 node1131Labels =
    (37623398400 : ℝ) * ((149933923200 : ℝ) * mixedMoment B node1131 node1131Labels + 0)
  ring

theorem reducedTermEval542 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm542 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm542 (originalVector B) := by
  rw [reducedTermArithmetic542, ← sound1132 B hB hF]
  change (-1759585423361310720000 : ℝ) * mixedMoment B node1132 node1132Labels =
    (37623398400 : ℝ) * (((-46768380800 : ℤ) : ℝ) * mixedMoment B node1132 node1132Labels + 0)
  ring

theorem reducedTermEval543 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm543 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm543 (originalVector B) := by
  rw [reducedTermArithmetic543, ← sound1133 B hB hF]
  change (1307514346489774080000 : ℝ) * mixedMoment B node1133 node1133Labels =
    (37623398400 : ℝ) * ((34752691200 : ℝ) * mixedMoment B node1133 node1133Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval480 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge480 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge480 (originalVector B) := by
  rw [reducedMerge480Check, Integer.Sparse.eval_mergeBy, reducedTermEval482 B hB hF, reducedTermEval483 B hB hF]
  rw [originalMerge480, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval481 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge481 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge481 (originalVector B) := by
  rw [reducedMerge481Check, Integer.Sparse.eval_mergeBy, reducedTermEval484 B hB hF, reducedTermEval485 B hB hF]
  rw [originalMerge481, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval482 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge482 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge482 (originalVector B) := by
  rw [reducedMerge482Check, Integer.Sparse.eval_mergeBy, reducedMergeEval480 B hB hF, reducedMergeEval481 B hB hF]
  rw [originalMerge482, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval483 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge483 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge483 (originalVector B) := by
  rw [reducedMerge483Check, Integer.Sparse.eval_mergeBy, reducedMergeEval479 B hB hF, reducedMergeEval482 B hB hF]
  rw [originalMerge483, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval484 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge484 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge484 (originalVector B) := by
  rw [reducedMerge484Check, Integer.Sparse.eval_mergeBy, reducedTermEval486 B hB hF, reducedTermEval487 B hB hF]
  rw [originalMerge484, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval485 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge485 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge485 (originalVector B) := by
  rw [reducedMerge485Check, Integer.Sparse.eval_mergeBy, reducedTermEval488 B hB hF, reducedTermEval489 B hB hF]
  rw [originalMerge485, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval486 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge486 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge486 (originalVector B) := by
  rw [reducedMerge486Check, Integer.Sparse.eval_mergeBy, reducedMergeEval484 B hB hF, reducedMergeEval485 B hB hF]
  rw [originalMerge486, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval487 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge487 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge487 (originalVector B) := by
  rw [reducedMerge487Check, Integer.Sparse.eval_mergeBy, reducedTermEval490 B hB hF, reducedTermEval491 B hB hF]
  rw [originalMerge487, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval488 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge488 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge488 (originalVector B) := by
  rw [reducedMerge488Check, Integer.Sparse.eval_mergeBy, reducedTermEval492 B hB hF, reducedTermEval493 B hB hF]
  rw [originalMerge488, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval489 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge489 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge489 (originalVector B) := by
  rw [reducedMerge489Check, Integer.Sparse.eval_mergeBy, reducedMergeEval487 B hB hF, reducedMergeEval488 B hB hF]
  rw [originalMerge489, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval490 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge490 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge490 (originalVector B) := by
  rw [reducedMerge490Check, Integer.Sparse.eval_mergeBy, reducedMergeEval486 B hB hF, reducedMergeEval489 B hB hF]
  rw [originalMerge490, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval491 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge491 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge491 (originalVector B) := by
  rw [reducedMerge491Check, Integer.Sparse.eval_mergeBy, reducedMergeEval483 B hB hF, reducedMergeEval490 B hB hF]
  rw [originalMerge491, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval492 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge492 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge492 (originalVector B) := by
  rw [reducedMerge492Check, Integer.Sparse.eval_mergeBy, reducedTermEval495 B hB hF, reducedTermEval496 B hB hF]
  rw [originalMerge492, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval493 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge493 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge493 (originalVector B) := by
  rw [reducedMerge493Check, Integer.Sparse.eval_mergeBy, reducedTermEval494 B hB hF, reducedMergeEval492 B hB hF]
  rw [originalMerge493, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval494 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge494 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge494 (originalVector B) := by
  rw [reducedMerge494Check, Integer.Sparse.eval_mergeBy, reducedTermEval497 B hB hF, reducedTermEval498 B hB hF]
  rw [originalMerge494, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval495 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge495 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge495 (originalVector B) := by
  rw [reducedMerge495Check, Integer.Sparse.eval_mergeBy, reducedTermEval499 B hB hF, reducedTermEval500 B hB hF]
  rw [originalMerge495, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval496 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge496 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge496 (originalVector B) := by
  rw [reducedMerge496Check, Integer.Sparse.eval_mergeBy, reducedMergeEval494 B hB hF, reducedMergeEval495 B hB hF]
  rw [originalMerge496, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval497 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge497 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge497 (originalVector B) := by
  rw [reducedMerge497Check, Integer.Sparse.eval_mergeBy, reducedMergeEval493 B hB hF, reducedMergeEval496 B hB hF]
  rw [originalMerge497, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval498 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge498 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge498 (originalVector B) := by
  rw [reducedMerge498Check, Integer.Sparse.eval_mergeBy, reducedTermEval501 B hB hF, reducedTermEval502 B hB hF]
  rw [originalMerge498, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval499 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge499 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge499 (originalVector B) := by
  rw [reducedMerge499Check, Integer.Sparse.eval_mergeBy, reducedTermEval503 B hB hF, reducedTermEval504 B hB hF]
  rw [originalMerge499, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval500 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge500 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge500 (originalVector B) := by
  rw [reducedMerge500Check, Integer.Sparse.eval_mergeBy, reducedMergeEval498 B hB hF, reducedMergeEval499 B hB hF]
  rw [originalMerge500, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval501 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge501 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge501 (originalVector B) := by
  rw [reducedMerge501Check, Integer.Sparse.eval_mergeBy, reducedTermEval505 B hB hF, reducedTermEval506 B hB hF]
  rw [originalMerge501, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval502 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge502 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge502 (originalVector B) := by
  rw [reducedMerge502Check, Integer.Sparse.eval_mergeBy, reducedTermEval507 B hB hF, reducedTermEval508 B hB hF]
  rw [originalMerge502, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval503 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge503 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge503 (originalVector B) := by
  rw [reducedMerge503Check, Integer.Sparse.eval_mergeBy, reducedMergeEval501 B hB hF, reducedMergeEval502 B hB hF]
  rw [originalMerge503, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval504 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge504 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge504 (originalVector B) := by
  rw [reducedMerge504Check, Integer.Sparse.eval_mergeBy, reducedMergeEval500 B hB hF, reducedMergeEval503 B hB hF]
  rw [originalMerge504, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval505 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge505 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge505 (originalVector B) := by
  rw [reducedMerge505Check, Integer.Sparse.eval_mergeBy, reducedMergeEval497 B hB hF, reducedMergeEval504 B hB hF]
  rw [originalMerge505, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval506 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge506 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge506 (originalVector B) := by
  rw [reducedMerge506Check, Integer.Sparse.eval_mergeBy, reducedMergeEval491 B hB hF, reducedMergeEval505 B hB hF]
  rw [originalMerge506, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval507 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge507 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge507 (originalVector B) := by
  rw [reducedMerge507Check, Integer.Sparse.eval_mergeBy, reducedTermEval510 B hB hF, reducedTermEval511 B hB hF]
  rw [originalMerge507, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval508 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge508 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge508 (originalVector B) := by
  rw [reducedMerge508Check, Integer.Sparse.eval_mergeBy, reducedTermEval509 B hB hF, reducedMergeEval507 B hB hF]
  rw [originalMerge508, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval509 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge509 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge509 (originalVector B) := by
  rw [reducedMerge509Check, Integer.Sparse.eval_mergeBy, reducedTermEval512 B hB hF, reducedTermEval513 B hB hF]
  rw [originalMerge509, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval510 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge510 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge510 (originalVector B) := by
  rw [reducedMerge510Check, Integer.Sparse.eval_mergeBy, reducedTermEval514 B hB hF, reducedTermEval515 B hB hF]
  rw [originalMerge510, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval511 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge511 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge511 (originalVector B) := by
  rw [reducedMerge511Check, Integer.Sparse.eval_mergeBy, reducedMergeEval509 B hB hF, reducedMergeEval510 B hB hF]
  rw [originalMerge511, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval544 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm544 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm544 (originalVector B) := by
  rw [reducedTermArithmetic544, ← sound1134 B hB hF]
  change (3771399734927032320000 : ℝ) * mixedMoment B node1134 node1134Labels =
    (37623398400 : ℝ) * ((100240804800 : ℝ) * mixedMoment B node1134 node1134Labels + 0)
  ring

theorem reducedTermEval545 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm545 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm545 (originalVector B) := by
  rw [reducedTermArithmetic545, ← sound1135 B hB hF]
  change (-4459227814998835200000 : ℝ) * mixedMoment B node1135 node1135Labels =
    (37623398400 : ℝ) * (((-118522728000 : ℤ) : ℝ) * mixedMoment B node1135 node1135Labels + 0)
  ring

theorem reducedTermEval546 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm546 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm546 (originalVector B) := by
  rw [reducedTermArithmetic546, ← sound1137 B hB hF]
  change (467378502645841920000 : ℝ) * mixedMoment B node1137 node1137Labels =
    (37623398400 : ℝ) * ((12422548800 : ℝ) * mixedMoment B node1137 node1137Labels + 0)
  ring

theorem reducedTermEval547 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm547 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm547 (originalVector B) := by
  rw [reducedTermArithmetic547, ← sound1138 B hB hF]
  change (-19215558570607902720000 : ℝ) * mixedMoment B node1138 node1138Labels =
    (37623398400 : ℝ) * (((-510734260800 : ℤ) : ℝ) * mixedMoment B node1138 node1138Labels + 0)
  ring

theorem reducedTermEval548 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm548 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm548 (originalVector B) := by
  rw [reducedTermArithmetic548, ← sound1139 B hB hF]
  change (-10083993537718517760000 : ℝ) * mixedMoment B node1139 node1139Labels =
    (37623398400 : ℝ) * (((-268024526400 : ℤ) : ℝ) * mixedMoment B node1139 node1139Labels + 0)
  ring

theorem reducedTermEval549 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm549 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm549 (originalVector B) := by
  rw [reducedTermArithmetic549, ← sound1140 B hB hF]
  change (5594674980160143360000 : ℝ) * mixedMoment B node1140 node1140Labels =
    (37623398400 : ℝ) * ((148702010400 : ℝ) * mixedMoment B node1140 node1140Labels + 0)
  ring

theorem reducedTermEval550 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm550 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm550 (originalVector B) := by
  rw [reducedTermArithmetic550, ← sound1141 B hB hF]
  change (871459791106867200000 : ℝ) * mixedMoment B node1141 node1141Labels =
    (37623398400 : ℝ) * ((23162708000 : ℝ) * mixedMoment B node1141 node1141Labels + 0)
  ring

theorem reducedTermEval551 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm551 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm551 (originalVector B) := by
  rw [reducedTermArithmetic551, ← sound1142 B hB hF]
  change (5137435020224102400000 : ℝ) * mixedMoment B node1142 node1142Labels =
    (37623398400 : ℝ) * ((136548936000 : ℝ) * mixedMoment B node1142 node1142Labels + 0)
  ring

theorem reducedTermEval552 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm552 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm552 (originalVector B) := by
  rw [reducedTermArithmetic552, ← sound1143 B hB hF]
  change (-5549518414241464320000 : ℝ) * mixedMoment B node1143 node1143Labels =
    (37623398400 : ℝ) * (((-147501784800 : ℤ) : ℝ) * mixedMoment B node1143 node1143Labels + 0)
  ring

theorem reducedTermEval553 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm553 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm553 (originalVector B) := by
  rw [reducedTermArithmetic553, ← sound1144 B hB hF]
  change (-2210692257679933440000 : ℝ) * mixedMoment B node1144 node1144Labels =
    (37623398400 : ℝ) * (((-58758441600 : ℤ) : ℝ) * mixedMoment B node1144 node1144Labels + 0)
  ring

theorem reducedTermEval554 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm554 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm554 (originalVector B) := by
  rw [reducedTermArithmetic554, ← sound1145 B hB hF]
  change (2991047260449669120000 : ℝ) * mixedMoment B node1145 node1145Labels =
    (37623398400 : ℝ) * ((79499656800 : ℝ) * mixedMoment B node1145 node1145Labels + 0)
  ring

theorem reducedTermEval555 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm555 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm555 (originalVector B) := by
  rw [reducedTermArithmetic555, ← sound1146 B hB hF]
  change (167779287760896000000 : ℝ) * mixedMoment B node1146 node1146Labels =
    (37623398400 : ℝ) * ((4459440000 : ℝ) * mixedMoment B node1146 node1146Labels + 0)
  ring

theorem reducedTermEval556 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm556 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm556 (originalVector B) := by
  rw [reducedTermArithmetic556, ← sound1148 B hB hF]
  change (-54778388874854400000 : ℝ) * mixedMoment B node1148 node1148Labels =
    (37623398400 : ℝ) * (((-1455966000 : ℤ) : ℝ) * mixedMoment B node1148 node1148Labels + 0)
  ring

theorem reducedTermEval557 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm557 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm557 (originalVector B) := by
  rw [reducedTermArithmetic557, ← sound1149 B hB hF]
  change (54778388874854400000 : ℝ) * mixedMoment B node1149 node1149Labels =
    (37623398400 : ℝ) * ((1455966000 : ℝ) * mixedMoment B node1149 node1149Labels + 0)
  ring

theorem reducedTermEval558 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm558 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm558 (originalVector B) := by
  rw [reducedTermArithmetic558, ← sound1150 B hB hF]
  change (598839592845312000000 : ℝ) * mixedMoment B node1150 node1150Labels =
    (37623398400 : ℝ) * ((15916680000 : ℝ) * mixedMoment B node1150 node1150Labels + 0)
  ring

theorem reducedTermEval559 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm559 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm559 (originalVector B) := by
  rw [reducedTermArithmetic559, ← sound1151 B hB hF]
  change (-3796503149893386240000 : ℝ) * mixedMoment B node1151 node1151Labels =
    (37623398400 : ℝ) * (((-100908033600 : ℤ) : ℝ) * mixedMoment B node1151 node1151Labels + 0)
  ring

theorem reducedTermEval560 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm560 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm560 (originalVector B) := by
  rw [reducedTermArithmetic560, ← sound1153 B hB hF]
  change (-2713512723987824640000 : ℝ) * mixedMoment B node1153 node1153Labels =
    (37623398400 : ℝ) * (((-72123009600 : ℤ) : ℝ) * mixedMoment B node1153 node1153Labels + 0)
  ring

theorem reducedTermEval561 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm561 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm561 (originalVector B) := by
  rw [reducedTermArithmetic561, ← sound1155 B hB hF]
  change (3773107777016954880000 : ℝ) * mixedMoment B node1155 node1155Labels =
    (37623398400 : ℝ) * ((100286203200 : ℝ) * mixedMoment B node1155 node1155Labels + 0)
  ring

theorem reducedTermEval562 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm562 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm562 (originalVector B) := by
  rw [reducedTermArithmetic562, ← sound1156 B hB hF]
  change (-4033883256599347200000 : ℝ) * mixedMoment B node1156 node1156Labels =
    (37623398400 : ℝ) * (((-107217408000 : ℤ) : ℝ) * mixedMoment B node1156 node1156Labels + 0)
  ring

theorem reducedTermEval563 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm563 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm563 (originalVector B) := by
  rw [reducedTermArithmetic563, ← sound1159 B hB hF]
  change (-1465158899028787200000 : ℝ) * mixedMoment B node1159 node1159Labels =
    (37623398400 : ℝ) * (((-38942758000 : ℤ) : ℝ) * mixedMoment B node1159 node1159Labels + 0)
  ring

theorem reducedTermEval564 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm564 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm564 (originalVector B) := by
  rw [reducedTermArithmetic564, ← sound1160 B hB hF]
  change (5499042155628134400000 : ℝ) * mixedMoment B node1160 node1160Labels =
    (37623398400 : ℝ) * ((146160166000 : ℝ) * mixedMoment B node1160 node1160Labels + 0)
  ring

theorem reducedTermEval565 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm565 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm565 (originalVector B) := by
  rw [reducedTermArithmetic565, ← sound1169 B hB hF]
  change (4433171053215744000000 : ℝ) * mixedMoment B node1169 node1169Labels =
    (37623398400 : ℝ) * ((117830160000 : ℝ) * mixedMoment B node1169 node1169Labels + 0)
  ring

theorem reducedTermEval566 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm566 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm566 (originalVector B) := by
  rw [reducedTermArithmetic566, ← sound1171 B hB hF]
  change (6851070957020774400000 : ℝ) * mixedMoment B node1171 node1171Labels =
    (37623398400 : ℝ) * ((182096016000 : ℝ) * mixedMoment B node1171 node1171Labels + 0)
  ring

theorem reducedTermEval567 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm567 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm567 (originalVector B) := by
  rw [reducedTermArithmetic567, ← sound1174 B hB hF]
  change (606438917347737600000 : ℝ) * mixedMoment B node1174 node1174Labels =
    (37623398400 : ℝ) * ((16118664000 : ℝ) * mixedMoment B node1174 node1174Labels + 0)
  ring

theorem reducedTermEval568 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm568 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm568 (originalVector B) := by
  rw [reducedTermArithmetic568, ← sound1212 B hB hF]
  change (934778270036459520000 : ℝ) * mixedMoment B node1212 node1212Labels =
    (37623398400 : ℝ) * ((24845662800 : ℝ) * mixedMoment B node1212 node1212Labels + 0)
  ring

theorem reducedTermEval569 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm569 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm569 (originalVector B) := by
  rw [reducedTermArithmetic569, ← sound1215 B hB hF]
  change (-1029645037028966400000 : ℝ) * mixedMoment B node1215 node1215Labels =
    (37623398400 : ℝ) * (((-27367146000 : ℤ) : ℝ) * mixedMoment B node1215 node1215Labels + 0)
  ring

theorem reducedTermEval570 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm570 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm570 (originalVector B) := by
  rw [reducedTermArithmetic570, ← sound1216 B hB hF]
  change (250586732209766400000 : ℝ) * mixedMoment B node1216 node1216Labels =
    (37623398400 : ℝ) * ((6660396000 : ℝ) * mixedMoment B node1216 node1216Labels + 0)
  ring

theorem reducedTermEval571 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm571 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm571 (originalVector B) := by
  rw [reducedTermArithmetic571, ← sound1217 B hB hF]
  change (18978681323195596800000 : ℝ) * mixedMoment B node1217 node1217Labels =
    (37623398400 : ℝ) * ((504438252000 : ℝ) * mixedMoment B node1217 node1217Labels + 0)
  ring

theorem reducedTermEval572 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm572 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm572 (originalVector B) := by
  rw [reducedTermArithmetic572, ← sound1219 B hB hF]
  change (11351689807634104320000 : ℝ) * mixedMoment B node1219 node1219Labels =
    (37623398400 : ℝ) * ((301718884800 : ℝ) * mixedMoment B node1219 node1219Labels + 0)
  ring

theorem reducedTermEval573 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm573 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm573 (originalVector B) := by
  rw [reducedTermArithmetic573, ← sound1221 B hB hF]
  change (972527074748006400000 : ℝ) * mixedMoment B node1221 node1221Labels =
    (37623398400 : ℝ) * ((25848996000 : ℝ) * mixedMoment B node1221 node1221Labels + 0)
  ring

theorem reducedTermEval574 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm574 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm574 (originalVector B) := by
  rw [reducedTermArithmetic574, ← sound1233 B hB hF]
  change (-6722247552986972160000 : ℝ) * mixedMoment B node1233 node1233Labels =
    (37623398400 : ℝ) * (((-178671992400 : ℤ) : ℝ) * mixedMoment B node1233 node1233Labels + 0)
  ring

theorem reducedTermEval575 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm575 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm575 (originalVector B) := by
  rw [reducedTermArithmetic575, ← sound1234 B hB hF]
  change (-416003421044736000000 : ℝ) * mixedMoment B node1234 node1234Labels =
    (37623398400 : ℝ) * (((-11057040000 : ℤ) : ℝ) * mixedMoment B node1234 node1234Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval512 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge512 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge512 (originalVector B) := by
  rw [reducedMerge512Check, Integer.Sparse.eval_mergeBy, reducedMergeEval508 B hB hF, reducedMergeEval511 B hB hF]
  rw [originalMerge512, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval513 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge513 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge513 (originalVector B) := by
  rw [reducedMerge513Check, Integer.Sparse.eval_mergeBy, reducedTermEval516 B hB hF, reducedTermEval517 B hB hF]
  rw [originalMerge513, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval514 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge514 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge514 (originalVector B) := by
  rw [reducedMerge514Check, Integer.Sparse.eval_mergeBy, reducedTermEval518 B hB hF, reducedTermEval519 B hB hF]
  rw [originalMerge514, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval515 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge515 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge515 (originalVector B) := by
  rw [reducedMerge515Check, Integer.Sparse.eval_mergeBy, reducedMergeEval513 B hB hF, reducedMergeEval514 B hB hF]
  rw [originalMerge515, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval516 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge516 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge516 (originalVector B) := by
  rw [reducedMerge516Check, Integer.Sparse.eval_mergeBy, reducedTermEval520 B hB hF, reducedTermEval521 B hB hF]
  rw [originalMerge516, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval517 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge517 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge517 (originalVector B) := by
  rw [reducedMerge517Check, Integer.Sparse.eval_mergeBy, reducedTermEval522 B hB hF, reducedTermEval523 B hB hF]
  rw [originalMerge517, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval518 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge518 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge518 (originalVector B) := by
  rw [reducedMerge518Check, Integer.Sparse.eval_mergeBy, reducedMergeEval516 B hB hF, reducedMergeEval517 B hB hF]
  rw [originalMerge518, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval519 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge519 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge519 (originalVector B) := by
  rw [reducedMerge519Check, Integer.Sparse.eval_mergeBy, reducedMergeEval515 B hB hF, reducedMergeEval518 B hB hF]
  rw [originalMerge519, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval520 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge520 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge520 (originalVector B) := by
  rw [reducedMerge520Check, Integer.Sparse.eval_mergeBy, reducedMergeEval512 B hB hF, reducedMergeEval519 B hB hF]
  rw [originalMerge520, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval521 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge521 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge521 (originalVector B) := by
  rw [reducedMerge521Check, Integer.Sparse.eval_mergeBy, reducedTermEval525 B hB hF, reducedTermEval526 B hB hF]
  rw [originalMerge521, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval522 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge522 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge522 (originalVector B) := by
  rw [reducedMerge522Check, Integer.Sparse.eval_mergeBy, reducedTermEval524 B hB hF, reducedMergeEval521 B hB hF]
  rw [originalMerge522, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval523 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge523 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge523 (originalVector B) := by
  rw [reducedMerge523Check, Integer.Sparse.eval_mergeBy, reducedTermEval527 B hB hF, reducedTermEval528 B hB hF]
  rw [originalMerge523, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval524 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge524 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge524 (originalVector B) := by
  rw [reducedMerge524Check, Integer.Sparse.eval_mergeBy, reducedTermEval529 B hB hF, reducedTermEval530 B hB hF]
  rw [originalMerge524, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval525 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge525 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge525 (originalVector B) := by
  rw [reducedMerge525Check, Integer.Sparse.eval_mergeBy, reducedMergeEval523 B hB hF, reducedMergeEval524 B hB hF]
  rw [originalMerge525, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval526 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge526 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge526 (originalVector B) := by
  rw [reducedMerge526Check, Integer.Sparse.eval_mergeBy, reducedMergeEval522 B hB hF, reducedMergeEval525 B hB hF]
  rw [originalMerge526, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval527 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge527 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge527 (originalVector B) := by
  rw [reducedMerge527Check, Integer.Sparse.eval_mergeBy, reducedTermEval531 B hB hF, reducedTermEval532 B hB hF]
  rw [originalMerge527, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval528 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge528 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge528 (originalVector B) := by
  rw [reducedMerge528Check, Integer.Sparse.eval_mergeBy, reducedTermEval533 B hB hF, reducedTermEval534 B hB hF]
  rw [originalMerge528, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval529 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge529 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge529 (originalVector B) := by
  rw [reducedMerge529Check, Integer.Sparse.eval_mergeBy, reducedMergeEval527 B hB hF, reducedMergeEval528 B hB hF]
  rw [originalMerge529, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval530 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge530 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge530 (originalVector B) := by
  rw [reducedMerge530Check, Integer.Sparse.eval_mergeBy, reducedTermEval535 B hB hF, reducedTermEval536 B hB hF]
  rw [originalMerge530, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval531 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge531 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge531 (originalVector B) := by
  rw [reducedMerge531Check, Integer.Sparse.eval_mergeBy, reducedTermEval537 B hB hF, reducedTermEval538 B hB hF]
  rw [originalMerge531, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval532 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge532 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge532 (originalVector B) := by
  rw [reducedMerge532Check, Integer.Sparse.eval_mergeBy, reducedMergeEval530 B hB hF, reducedMergeEval531 B hB hF]
  rw [originalMerge532, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval533 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge533 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge533 (originalVector B) := by
  rw [reducedMerge533Check, Integer.Sparse.eval_mergeBy, reducedMergeEval529 B hB hF, reducedMergeEval532 B hB hF]
  rw [originalMerge533, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval534 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge534 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge534 (originalVector B) := by
  rw [reducedMerge534Check, Integer.Sparse.eval_mergeBy, reducedMergeEval526 B hB hF, reducedMergeEval533 B hB hF]
  rw [originalMerge534, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval535 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge535 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge535 (originalVector B) := by
  rw [reducedMerge535Check, Integer.Sparse.eval_mergeBy, reducedMergeEval520 B hB hF, reducedMergeEval534 B hB hF]
  rw [originalMerge535, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval536 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge536 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge536 (originalVector B) := by
  rw [reducedMerge536Check, Integer.Sparse.eval_mergeBy, reducedMergeEval506 B hB hF, reducedMergeEval535 B hB hF]
  rw [originalMerge536, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval537 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge537 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge537 (originalVector B) := by
  rw [reducedMerge537Check, Integer.Sparse.eval_mergeBy, reducedTermEval540 B hB hF, reducedTermEval541 B hB hF]
  rw [originalMerge537, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval538 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge538 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge538 (originalVector B) := by
  rw [reducedMerge538Check, Integer.Sparse.eval_mergeBy, reducedTermEval539 B hB hF, reducedMergeEval537 B hB hF]
  rw [originalMerge538, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval539 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge539 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge539 (originalVector B) := by
  rw [reducedMerge539Check, Integer.Sparse.eval_mergeBy, reducedTermEval542 B hB hF, reducedTermEval543 B hB hF]
  rw [originalMerge539, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval540 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge540 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge540 (originalVector B) := by
  rw [reducedMerge540Check, Integer.Sparse.eval_mergeBy, reducedTermEval544 B hB hF, reducedTermEval545 B hB hF]
  rw [originalMerge540, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval541 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge541 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge541 (originalVector B) := by
  rw [reducedMerge541Check, Integer.Sparse.eval_mergeBy, reducedMergeEval539 B hB hF, reducedMergeEval540 B hB hF]
  rw [originalMerge541, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval542 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge542 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge542 (originalVector B) := by
  rw [reducedMerge542Check, Integer.Sparse.eval_mergeBy, reducedMergeEval538 B hB hF, reducedMergeEval541 B hB hF]
  rw [originalMerge542, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval543 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge543 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge543 (originalVector B) := by
  rw [reducedMerge543Check, Integer.Sparse.eval_mergeBy, reducedTermEval546 B hB hF, reducedTermEval547 B hB hF]
  rw [originalMerge543, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval576 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm576 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm576 (originalVector B) := by
  rw [reducedTermArithmetic576, ← sound1235 B hB hF]
  change (3252202435368714240000 : ℝ) * mixedMoment B node1235 node1235Labels =
    (37623398400 : ℝ) * ((86440953600 : ℝ) * mixedMoment B node1235 node1235Labels + 0)
  ring

theorem reducedTermEval577 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm577 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm577 (originalVector B) := by
  rw [reducedTermArithmetic577, ← sound1236 B hB hF]
  change (12119156027369717760000 : ℝ) * mixedMoment B node1236 node1236Labels =
    (37623398400 : ℝ) * ((322117526400 : ℝ) * mixedMoment B node1236 node1236Labels + 0)
  ring

theorem reducedTermEval578 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm578 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm578 (originalVector B) := by
  rw [reducedTermArithmetic578, ← sound1237 B hB hF]
  change (6722247552986972160000 : ℝ) * mixedMoment B node1237 node1237Labels =
    (37623398400 : ℝ) * ((178671992400 : ℝ) * mixedMoment B node1237 node1237Labels + 0)
  ring

theorem reducedTermEval579 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm579 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm579 (originalVector B) := by
  rw [reducedTermArithmetic579, ← sound1239 B hB hF]
  change (-2570828363354603520000 : ℝ) * mixedMoment B node1239 node1239Labels =
    (37623398400 : ℝ) * (((-68330572800 : ℤ) : ℝ) * mixedMoment B node1239 node1239Labels + 0)
  ring

theorem reducedTermEval580 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm580 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm580 (originalVector B) := by
  rw [reducedTermArithmetic580, ← sound1240 B hB hF]
  change (-12547178408576286720000 : ℝ) * mixedMoment B node1240 node1240Labels =
    (37623398400 : ℝ) * (((-333494020800 : ℤ) : ℝ) * mixedMoment B node1240 node1240Labels + 0)
  ring

theorem reducedTermEval581 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm581 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm581 (originalVector B) := by
  rw [reducedTermArithmetic581, ← sound1241 B hB hF]
  change (8753467817805742080000 : ℝ) * mixedMoment B node1241 node1241Labels =
    (37623398400 : ℝ) * ((232660211200 : ℝ) * mixedMoment B node1241 node1241Labels + 0)
  ring

theorem reducedTermEval582 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm582 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm582 (originalVector B) := by
  rw [reducedTermArithmetic582, ← sound1242 B hB hF]
  change (-3100873301337047040000 : ℝ) * mixedMoment B node1242 node1242Labels =
    (37623398400 : ℝ) * (((-82418745600 : ℤ) : ℝ) * mixedMoment B node1242 node1242Labels + 0)
  ring

theorem reducedTermEval583 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm583 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm583 (originalVector B) := by
  rw [reducedTermArithmetic583, ← sound1243 B hB hF]
  change (-2614211302075269120000 : ℝ) * mixedMoment B node1243 node1243Labels =
    (37623398400 : ℝ) * (((-69483656800 : ℤ) : ℝ) * mixedMoment B node1243 node1243Labels + 0)
  ring

theorem reducedTermEval584 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm584 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm584 (originalVector B) := by
  rw [reducedTermArithmetic584, ← sound1245 B hB hF]
  change (7725885129934110720000 : ℝ) * mixedMoment B node1245 node1245Labels =
    (37623398400 : ℝ) * ((205347880800 : ℝ) * mixedMoment B node1245 node1245Labels + 0)
  ring

theorem reducedTermEval585 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm585 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm585 (originalVector B) := by
  rw [reducedTermArithmetic585, ← sound1246 B hB hF]
  change (-19348453924951818240000 : ℝ) * mixedMoment B node1246 node1246Labels =
    (37623398400 : ℝ) * (((-514266513600 : ℤ) : ℝ) * mixedMoment B node1246 node1246Labels + 0)
  ring

theorem reducedTermEval586 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm586 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm586 (originalVector B) := by
  rw [reducedTermArithmetic586, ← sound1260 B hB hF]
  change (-7062722889655910400000 : ℝ) * mixedMoment B node1260 node1260Labels =
    (37623398400 : ℝ) * (((-187721556000 : ℤ) : ℝ) * mixedMoment B node1260 node1260Labels + 0)
  ring

theorem reducedTermEval587 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm587 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm587 (originalVector B) := by
  rw [reducedTermArithmetic587, ← sound1261 B hB hF]
  change (-9103216750304624640000 : ℝ) * mixedMoment B node1261 node1261Labels =
    (37623398400 : ℝ) * (((-241956259600 : ℤ) : ℝ) * mixedMoment B node1261 node1261Labels + 0)
  ring

theorem reducedTermEval588 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm588 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm588 (originalVector B) := by
  rw [reducedTermArithmetic588, ← sound1262 B hB hF]
  change (7062722889655910400000 : ℝ) * mixedMoment B node1262 node1262Labels =
    (37623398400 : ℝ) * ((187721556000 : ℝ) * mixedMoment B node1262 node1262Labels + 0)
  ring

theorem reducedTermEval589 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm589 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm589 (originalVector B) := by
  rw [reducedTermArithmetic589, ← sound1264 B hB hF]
  change (8502527801884999680000 : ℝ) * mixedMoment B node1264 node1264Labels =
    (37623398400 : ℝ) * ((225990425200 : ℝ) * mixedMoment B node1264 node1264Labels + 0)
  ring

theorem reducedTermEval590 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm590 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm590 (originalVector B) := by
  rw [reducedTermArithmetic590, ← sound1270 B hB hF]
  change (-8079242612869693440000 : ℝ) * mixedMoment B node1270 node1270Labels =
    (37623398400 : ℝ) * (((-214739841600 : ℤ) : ℝ) * mixedMoment B node1270 node1270Labels + 0)
  ring

theorem reducedTermEval591 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm591 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm591 (originalVector B) := by
  rw [reducedTermArithmetic591, ← sound1273 B hB hF]
  change (-5076859302087229440000 : ℝ) * mixedMoment B node1273 node1273Labels =
    (37623398400 : ℝ) * (((-134938881600 : ℤ) : ℝ) * mixedMoment B node1273 node1273Labels + 0)
  ring

theorem reducedTermEval592 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm592 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm592 (originalVector B) := by
  rw [reducedTermArithmetic592, ← sound1291 B hB hF]
  change (-2206050538624450560000 : ℝ) * mixedMoment B node1291 node1291Labels =
    (37623398400 : ℝ) * (((-58635068400 : ℤ) : ℝ) * mixedMoment B node1291 node1291Labels + 0)
  ring

theorem reducedTermEval593 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm593 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm593 (originalVector B) := by
  rw [reducedTermArithmetic593, ← sound1292 B hB hF]
  change (2219882239269273600000 : ℝ) * mixedMoment B node1292 node1292Labels =
    (37623398400 : ℝ) * ((59002704000 : ℝ) * mixedMoment B node1292 node1292Labels + 0)
  ring

theorem reducedTermEval594 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm594 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm594 (originalVector B) := by
  rw [reducedTermArithmetic594, ← sound1293 B hB hF]
  change (4459227814998835200000 : ℝ) * mixedMoment B node1293 node1293Labels =
    (37623398400 : ℝ) * ((118522728000 : ℝ) * mixedMoment B node1293 node1293Labels + 0)
  ring

theorem reducedTermEval595 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm595 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm595 (originalVector B) := by
  rw [reducedTermArithmetic595, ← sound1294 B hB hF]
  change (11729049453615513600000 : ℝ) * mixedMoment B node1294 node1294Labels =
    (37623398400 : ℝ) * ((311748804000 : ℝ) * mixedMoment B node1294 node1294Labels + 0)
  ring

theorem reducedTermEval596 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm596 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm596 (originalVector B) := by
  rw [reducedTermArithmetic596, ← sound1295 B hB hF]
  change (2206050538624450560000 : ℝ) * mixedMoment B node1295 node1295Labels =
    (37623398400 : ℝ) * ((58635068400 : ℝ) * mixedMoment B node1295 node1295Labels + 0)
  ring

theorem reducedTermEval597 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm597 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm597 (originalVector B) := by
  rw [reducedTermArithmetic597, ← sound1297 B hB hF]
  change (5575466278860226560000 : ℝ) * mixedMoment B node1297 node1297Labels =
    (37623398400 : ℝ) * ((148191458400 : ℝ) * mixedMoment B node1297 node1297Labels + 0)
  ring

theorem reducedTermEval598 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm598 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm598 (originalVector B) := by
  rw [reducedTermArithmetic598, ← sound1306 B hB hF]
  change (-6047328798324817920000 : ℝ) * mixedMoment B node1306 node1306Labels =
    (37623398400 : ℝ) * (((-160733188800 : ℤ) : ℝ) * mixedMoment B node1306 node1306Labels + 0)
  ring

theorem reducedTermEval599 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm599 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm599 (originalVector B) := by
  rw [reducedTermArithmetic599, ← sound1310 B hB hF]
  change (-626180907745935360000 : ℝ) * mixedMoment B node1310 node1310Labels =
    (37623398400 : ℝ) * (((-16643390400 : ℤ) : ℝ) * mixedMoment B node1310 node1310Labels + 0)
  ring

theorem reducedTermEval600 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm600 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm600 (originalVector B) := by
  rw [reducedTermArithmetic600, ← sound1314 B hB hF]
  change (5977466481711513600000 : ℝ) * mixedMoment B node1314 node1314Labels =
    (37623398400 : ℝ) * ((158876304000 : ℝ) * mixedMoment B node1314 node1314Labels + 0)
  ring

theorem reducedTermEval601 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm601 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm601 (originalVector B) := by
  rw [reducedTermArithmetic601, ← sound1315 B hB hF]
  change (3501622812129361920000 : ℝ) * mixedMoment B node1315 node1315Labels =
    (37623398400 : ℝ) * ((93070348800 : ℝ) * mixedMoment B node1315 node1315Labels + 0)
  ring

theorem reducedTermEval602 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm602 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm602 (originalVector B) := by
  rw [reducedTermArithmetic602, ← sound1316 B hB hF]
  change (-9579839035999518720000 : ℝ) * mixedMoment B node1316 node1316Labels =
    (37623398400 : ℝ) * (((-254624500800 : ℤ) : ℝ) * mixedMoment B node1316 node1316Labels + 0)
  ring

theorem reducedTermEval603 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm603 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm603 (originalVector B) := by
  rw [reducedTermArithmetic603, ← sound1317 B hB hF]
  change (7341542882196848640000 : ℝ) * mixedMoment B node1317 node1317Labels =
    (37623398400 : ℝ) * ((195132369600 : ℝ) * mixedMoment B node1317 node1317Labels + 0)
  ring

theorem reducedTermEval604 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm604 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm604 (originalVector B) := by
  rw [reducedTermArithmetic604, ← sound1318 B hB hF]
  change (-4432587559454638080000 : ℝ) * mixedMoment B node1318 node1318Labels =
    (37623398400 : ℝ) * (((-117814651200 : ℤ) : ℝ) * mixedMoment B node1318 node1318Labels + 0)
  ring

theorem reducedTermEval605 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm605 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm605 (originalVector B) := by
  rw [reducedTermArithmetic605, ← sound1319 B hB hF]
  change (-3032742142629642240000 : ℝ) * mixedMoment B node1319 node1319Labels =
    (37623398400 : ℝ) * (((-80607873600 : ℤ) : ℝ) * mixedMoment B node1319 node1319Labels + 0)
  ring

theorem reducedTermEval606 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm606 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm606 (originalVector B) := by
  rw [reducedTermArithmetic606, ← sound1320 B hB hF]
  change (11886766950399344640000 : ℝ) * mixedMoment B node1320 node1320Labels =
    (37623398400 : ℝ) * ((315940809600 : ℝ) * mixedMoment B node1320 node1320Labels + 0)
  ring

theorem reducedTermEval607 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm607 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm607 (originalVector B) := by
  rw [reducedTermArithmetic607, ← sound1321 B hB hF]
  change (-10548491592982855680000 : ℝ) * mixedMoment B node1321 node1321Labels =
    (37623398400 : ℝ) * (((-280370515200 : ℤ) : ℝ) * mixedMoment B node1321 node1321Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval544 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge544 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge544 (originalVector B) := by
  rw [reducedMerge544Check, Integer.Sparse.eval_mergeBy, reducedTermEval548 B hB hF, reducedTermEval549 B hB hF]
  rw [originalMerge544, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval545 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge545 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge545 (originalVector B) := by
  rw [reducedMerge545Check, Integer.Sparse.eval_mergeBy, reducedMergeEval543 B hB hF, reducedMergeEval544 B hB hF]
  rw [originalMerge545, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval546 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge546 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge546 (originalVector B) := by
  rw [reducedMerge546Check, Integer.Sparse.eval_mergeBy, reducedTermEval550 B hB hF, reducedTermEval551 B hB hF]
  rw [originalMerge546, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval547 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge547 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge547 (originalVector B) := by
  rw [reducedMerge547Check, Integer.Sparse.eval_mergeBy, reducedTermEval552 B hB hF, reducedTermEval553 B hB hF]
  rw [originalMerge547, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval548 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge548 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge548 (originalVector B) := by
  rw [reducedMerge548Check, Integer.Sparse.eval_mergeBy, reducedMergeEval546 B hB hF, reducedMergeEval547 B hB hF]
  rw [originalMerge548, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval549 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge549 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge549 (originalVector B) := by
  rw [reducedMerge549Check, Integer.Sparse.eval_mergeBy, reducedMergeEval545 B hB hF, reducedMergeEval548 B hB hF]
  rw [originalMerge549, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval550 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge550 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge550 (originalVector B) := by
  rw [reducedMerge550Check, Integer.Sparse.eval_mergeBy, reducedMergeEval542 B hB hF, reducedMergeEval549 B hB hF]
  rw [originalMerge550, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval551 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge551 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge551 (originalVector B) := by
  rw [reducedMerge551Check, Integer.Sparse.eval_mergeBy, reducedTermEval555 B hB hF, reducedTermEval556 B hB hF]
  rw [originalMerge551, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval552 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge552 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge552 (originalVector B) := by
  rw [reducedMerge552Check, Integer.Sparse.eval_mergeBy, reducedTermEval554 B hB hF, reducedMergeEval551 B hB hF]
  rw [originalMerge552, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval553 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge553 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge553 (originalVector B) := by
  rw [reducedMerge553Check, Integer.Sparse.eval_mergeBy, reducedTermEval557 B hB hF, reducedTermEval558 B hB hF]
  rw [originalMerge553, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval554 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge554 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge554 (originalVector B) := by
  rw [reducedMerge554Check, Integer.Sparse.eval_mergeBy, reducedTermEval559 B hB hF, reducedTermEval560 B hB hF]
  rw [originalMerge554, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval555 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge555 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge555 (originalVector B) := by
  rw [reducedMerge555Check, Integer.Sparse.eval_mergeBy, reducedMergeEval553 B hB hF, reducedMergeEval554 B hB hF]
  rw [originalMerge555, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval556 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge556 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge556 (originalVector B) := by
  rw [reducedMerge556Check, Integer.Sparse.eval_mergeBy, reducedMergeEval552 B hB hF, reducedMergeEval555 B hB hF]
  rw [originalMerge556, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval557 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge557 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge557 (originalVector B) := by
  rw [reducedMerge557Check, Integer.Sparse.eval_mergeBy, reducedTermEval561 B hB hF, reducedTermEval562 B hB hF]
  rw [originalMerge557, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval558 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge558 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge558 (originalVector B) := by
  rw [reducedMerge558Check, Integer.Sparse.eval_mergeBy, reducedTermEval563 B hB hF, reducedTermEval564 B hB hF]
  rw [originalMerge558, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval559 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge559 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge559 (originalVector B) := by
  rw [reducedMerge559Check, Integer.Sparse.eval_mergeBy, reducedMergeEval557 B hB hF, reducedMergeEval558 B hB hF]
  rw [originalMerge559, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval560 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge560 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge560 (originalVector B) := by
  rw [reducedMerge560Check, Integer.Sparse.eval_mergeBy, reducedTermEval565 B hB hF, reducedTermEval566 B hB hF]
  rw [originalMerge560, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval561 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge561 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge561 (originalVector B) := by
  rw [reducedMerge561Check, Integer.Sparse.eval_mergeBy, reducedTermEval567 B hB hF, reducedTermEval568 B hB hF]
  rw [originalMerge561, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval562 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge562 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge562 (originalVector B) := by
  rw [reducedMerge562Check, Integer.Sparse.eval_mergeBy, reducedMergeEval560 B hB hF, reducedMergeEval561 B hB hF]
  rw [originalMerge562, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval563 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge563 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge563 (originalVector B) := by
  rw [reducedMerge563Check, Integer.Sparse.eval_mergeBy, reducedMergeEval559 B hB hF, reducedMergeEval562 B hB hF]
  rw [originalMerge563, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval564 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge564 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge564 (originalVector B) := by
  rw [reducedMerge564Check, Integer.Sparse.eval_mergeBy, reducedMergeEval556 B hB hF, reducedMergeEval563 B hB hF]
  rw [originalMerge564, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval565 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge565 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge565 (originalVector B) := by
  rw [reducedMerge565Check, Integer.Sparse.eval_mergeBy, reducedMergeEval550 B hB hF, reducedMergeEval564 B hB hF]
  rw [originalMerge565, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval566 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge566 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge566 (originalVector B) := by
  rw [reducedMerge566Check, Integer.Sparse.eval_mergeBy, reducedTermEval570 B hB hF, reducedTermEval571 B hB hF]
  rw [originalMerge566, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval567 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge567 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge567 (originalVector B) := by
  rw [reducedMerge567Check, Integer.Sparse.eval_mergeBy, reducedTermEval569 B hB hF, reducedMergeEval566 B hB hF]
  rw [originalMerge567, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval568 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge568 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge568 (originalVector B) := by
  rw [reducedMerge568Check, Integer.Sparse.eval_mergeBy, reducedTermEval572 B hB hF, reducedTermEval573 B hB hF]
  rw [originalMerge568, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval569 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge569 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge569 (originalVector B) := by
  rw [reducedMerge569Check, Integer.Sparse.eval_mergeBy, reducedTermEval574 B hB hF, reducedTermEval575 B hB hF]
  rw [originalMerge569, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval570 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge570 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge570 (originalVector B) := by
  rw [reducedMerge570Check, Integer.Sparse.eval_mergeBy, reducedMergeEval568 B hB hF, reducedMergeEval569 B hB hF]
  rw [originalMerge570, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval571 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge571 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge571 (originalVector B) := by
  rw [reducedMerge571Check, Integer.Sparse.eval_mergeBy, reducedMergeEval567 B hB hF, reducedMergeEval570 B hB hF]
  rw [originalMerge571, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval572 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge572 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge572 (originalVector B) := by
  rw [reducedMerge572Check, Integer.Sparse.eval_mergeBy, reducedTermEval576 B hB hF, reducedTermEval577 B hB hF]
  rw [originalMerge572, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval573 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge573 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge573 (originalVector B) := by
  rw [reducedMerge573Check, Integer.Sparse.eval_mergeBy, reducedTermEval578 B hB hF, reducedTermEval579 B hB hF]
  rw [originalMerge573, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval574 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge574 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge574 (originalVector B) := by
  rw [reducedMerge574Check, Integer.Sparse.eval_mergeBy, reducedMergeEval572 B hB hF, reducedMergeEval573 B hB hF]
  rw [originalMerge574, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval575 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge575 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge575 (originalVector B) := by
  rw [reducedMerge575Check, Integer.Sparse.eval_mergeBy, reducedTermEval580 B hB hF, reducedTermEval581 B hB hF]
  rw [originalMerge575, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval608 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm608 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm608 (originalVector B) := by
  rw [reducedTermArithmetic608, ← sound1322 B hB hF]
  change (9579839035999518720000 : ℝ) * mixedMoment B node1322 node1322Labels =
    (37623398400 : ℝ) * ((254624500800 : ℝ) * mixedMoment B node1322 node1322Labels + 0)
  ring

theorem reducedTermEval609 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm609 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm609 (originalVector B) := by
  rw [reducedTermArithmetic609, ← sound1323 B hB hF]
  change (-4933072605979607040000 : ℝ) * mixedMoment B node1323 node1323Labels =
    (37623398400 : ℝ) * (((-131117145600 : ℤ) : ℝ) * mixedMoment B node1323 node1323Labels + 0)
  ring

theorem reducedTermEval610 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm610 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm610 (originalVector B) := by
  rw [reducedTermArithmetic610, ← sound1324 B hB hF]
  change (-8886421804453724160000 : ℝ) * mixedMoment B node1324 node1324Labels =
    (37623398400 : ℝ) * (((-236194022400 : ℤ) : ℝ) * mixedMoment B node1324 node1324Labels + 0)
  ring

theorem reducedTermEval611 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm611 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm611 (originalVector B) := by
  rw [reducedTermArithmetic611, ← sound1325 B hB hF]
  change (-8635312347795947520000 : ℝ) * mixedMoment B node1325 node1325Labels =
    (37623398400 : ℝ) * (((-229519732800 : ℤ) : ℝ) * mixedMoment B node1325 node1325Labels + 0)
  ring

theorem reducedTermEval612 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm612 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm612 (originalVector B) := by
  rw [reducedTermArithmetic612, ← sound1326 B hB hF]
  change (277114839928012800000 : ℝ) * mixedMoment B node1326 node1326Labels =
    (37623398400 : ℝ) * ((7365492000 : ℝ) * mixedMoment B node1326 node1326Labels + 0)
  ring

theorem reducedTermEval613 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm613 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm613 (originalVector B) := by
  rw [reducedTermArithmetic613, ← sound1327 B hB hF]
  change (-5341116330562682880000 : ℝ) * mixedMoment B node1327 node1327Labels =
    (37623398400 : ℝ) * (((-141962623200 : ℤ) : ℝ) * mixedMoment B node1327 node1327Labels + 0)
  ring

theorem reducedTermEval614 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm614 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm614 (originalVector B) := by
  rw [reducedTermArithmetic614, ← sound1328 B hB hF]
  change (-2299907207666073600000 : ℝ) * mixedMoment B node1328 node1328Labels =
    (37623398400 : ℝ) * (((-61129704000 : ℤ) : ℝ) * mixedMoment B node1328 node1328Labels + 0)
  ring

theorem reducedTermEval615 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm615 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm615 (originalVector B) := by
  rw [reducedTermArithmetic615, ← sound1330 B hB hF]
  change (-819339736118722560000 : ℝ) * mixedMoment B node1330 node1330Labels =
    (37623398400 : ℝ) * (((-21777398400 : ℤ) : ℝ) * mixedMoment B node1330 node1330Labels + 0)
  ring

theorem reducedTermEval616 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm616 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm616 (originalVector B) := by
  rw [reducedTermArithmetic616, ← sound1332 B hB hF]
  change (-3493413807980544000000 : ℝ) * mixedMoment B node1332 node1332Labels =
    (37623398400 : ℝ) * (((-92852160000 : ℤ) : ℝ) * mixedMoment B node1332 node1332Labels + 0)
  ring

theorem reducedTermEval617 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm617 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm617 (originalVector B) := by
  rw [reducedTermArithmetic617, ← sound1333 B hB hF]
  change (7641023538228756480000 : ℝ) * mixedMoment B node1333 node1333Labels =
    (37623398400 : ℝ) * ((203092327200 : ℝ) * mixedMoment B node1333 node1333Labels + 0)
  ring

theorem reducedTermEval618 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm618 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm618 (originalVector B) := by
  rw [reducedTermArithmetic618, ← sound1334 B hB hF]
  change (8698253102854963200000 : ℝ) * mixedMoment B node1334 node1334Labels =
    (37623398400 : ℝ) * ((231192648000 : ℝ) * mixedMoment B node1334 node1334Labels + 0)
  ring

theorem reducedTermEval619 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm619 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm619 (originalVector B) := by
  rw [reducedTermArithmetic619, ← sound1335 B hB hF]
  change (7361272231133184000000 : ℝ) * mixedMoment B node1335 node1335Labels =
    (37623398400 : ℝ) * ((195656760000 : ℝ) * mixedMoment B node1335 node1335Labels + 0)
  ring

theorem reducedTermEval620 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm620 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm620 (originalVector B) := by
  rw [reducedTermArithmetic620, ← sound1336 B hB hF]
  change (3435031202884485120000 : ℝ) * mixedMoment B node1336 node1336Labels =
    (37623398400 : ℝ) * ((91300396800 : ℝ) * mixedMoment B node1336 node1336Labels + 0)
  ring

theorem reducedTermEval621 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm621 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm621 (originalVector B) := by
  rw [reducedTermArithmetic621, ← sound1337 B hB hF]
  change (-1895122181062656000000 : ℝ) * mixedMoment B node1337 node1337Labels =
    (37623398400 : ℝ) * (((-50370840000 : ℤ) : ℝ) * mixedMoment B node1337 node1337Labels + 0)
  ring

theorem reducedTermEval622 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm622 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm622 (originalVector B) := by
  rw [reducedTermArithmetic622, ← sound1338 B hB hF]
  change (4158977745420288000000 : ℝ) * mixedMoment B node1338 node1338Labels =
    (37623398400 : ℝ) * ((110542320000 : ℝ) * mixedMoment B node1338 node1338Labels + 0)
  ring

theorem reducedTermEval623 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm623 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm623 (originalVector B) := by
  rw [reducedTermArithmetic623, ← sound1348 B hB hF]
  change (1542086242739159040000 : ℝ) * mixedMoment B node1348 node1348Labels =
    (37623398400 : ℝ) * ((40987425600 : ℝ) * mixedMoment B node1348 node1348Labels + 0)
  ring

theorem reducedTermEval624 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm624 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm624 (originalVector B) := by
  rw [reducedTermArithmetic624, ← sound1366 B hB hF]
  change (-1899117244195799040000 : ℝ) * mixedMoment B node1366 node1366Labels =
    (37623398400 : ℝ) * (((-50477025600 : ℤ) : ℝ) * mixedMoment B node1366 node1366Labels + 0)
  ring

theorem reducedTermEval625 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm625 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm625 (originalVector B) := by
  rw [reducedTermArithmetic625, ← sound1367 B hB hF]
  change (2667259420956426240000 : ℝ) * mixedMoment B node1367 node1367Labels =
    (37623398400 : ℝ) * ((70893633600 : ℝ) * mixedMoment B node1367 node1367Labels + 0)
  ring

theorem reducedTermEval626 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm626 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm626 (originalVector B) := by
  rw [reducedTermArithmetic626, ← sound1369 B hB hF]
  change (-3750701327642787840000 : ℝ) * mixedMoment B node1369 node1369Labels =
    (37623398400 : ℝ) * (((-99690657600 : ℤ) : ℝ) * mixedMoment B node1369 node1369Labels + 0)
  ring

theorem reducedTermEval627 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm627 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm627 (originalVector B) := by
  rw [reducedTermArithmetic627, ← sound1370 B hB hF]
  change (1899117244195799040000 : ℝ) * mixedMoment B node1370 node1370Labels =
    (37623398400 : ℝ) * ((50477025600 : ℝ) * mixedMoment B node1370 node1370Labels + 0)
  ring

theorem reducedTermEval628 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm628 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm628 (originalVector B) := by
  rw [reducedTermArithmetic628, ← sound1372 B hB hF]
  change (8859486641663508480000 : ℝ) * mixedMoment B node1372 node1372Labels =
    (37623398400 : ℝ) * ((235478107200 : ℝ) * mixedMoment B node1372 node1372Labels + 0)
  ring

theorem reducedTermEval629 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm629 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm629 (originalVector B) := by
  rw [reducedTermArithmetic629, ← sound1375 B hB hF]
  change (-11526746062619934720000 : ℝ) * mixedMoment B node1375 node1375Labels =
    (37623398400 : ℝ) * (((-306371740800 : ℤ) : ℝ) * mixedMoment B node1375 node1375Labels + 0)
  ring

theorem reducedTermEval630 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm630 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm630 (originalVector B) := by
  rw [reducedTermArithmetic630, ← sound1383 B hB hF]
  change (4656026210537963520000 : ℝ) * mixedMoment B node1383 node1383Labels =
    (37623398400 : ℝ) * ((123753472800 : ℝ) * mixedMoment B node1383 node1383Labels + 0)
  ring

theorem reducedTermEval631 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm631 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm631 (originalVector B) := by
  rw [reducedTermArithmetic631, ← sound1385 B hB hF]
  change (-3478154931439534080000 : ℝ) * mixedMoment B node1385 node1385Labels =
    (37623398400 : ℝ) * (((-92446591200 : ℤ) : ℝ) * mixedMoment B node1385 node1385Labels + 0)
  ring

theorem reducedTermEval632 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm632 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm632 (originalVector B) := by
  rw [reducedTermArithmetic632, ← sound1388 B hB hF]
  change (-2299907207666073600000 : ℝ) * mixedMoment B node1388 node1388Labels =
    (37623398400 : ℝ) * (((-61129704000 : ℤ) : ℝ) * mixedMoment B node1388 node1388Labels + 0)
  ring

theorem reducedTermEval633 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm633 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm633 (originalVector B) := by
  rw [reducedTermArithmetic633, ← sound1391 B hB hF]
  change (-2356119002871889920000 : ℝ) * mixedMoment B node1391 node1391Labels =
    (37623398400 : ℝ) * (((-62623768800 : ℤ) : ℝ) * mixedMoment B node1391 node1391Labels + 0)
  ring

theorem reducedTermEval634 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm634 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm634 (originalVector B) := by
  rw [reducedTermArithmetic634, ← sound1406 B hB hF]
  change (-22276992136265072640000 : ℝ) * mixedMoment B node1406 node1406Labels =
    (37623398400 : ℝ) * (((-592104729600 : ℤ) : ℝ) * mixedMoment B node1406 node1406Labels + 0)
  ring

theorem reducedTermEval635 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm635 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm635 (originalVector B) := by
  rw [reducedTermArithmetic635, ← sound1408 B hB hF]
  change (-17269758213677383680000 : ℝ) * mixedMoment B node1408 node1408Labels =
    (37623398400 : ℝ) * (((-459016435200 : ℤ) : ℝ) * mixedMoment B node1408 node1408Labels + 0)
  ring

theorem reducedTermEval636 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm636 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm636 (originalVector B) := by
  rw [reducedTermArithmetic636, ← sound1435 B hB hF]
  change (847409560407244800000 : ℝ) * mixedMoment B node1435 node1435Labels =
    (37623398400 : ℝ) * ((22523472000 : ℝ) * mixedMoment B node1435 node1435Labels + 0)
  ring

theorem reducedTermEval637 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm637 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm637 (originalVector B) := by
  rw [reducedTermArithmetic637, ← sound1436 B hB hF]
  change (-3245969833485926400000 : ℝ) * mixedMoment B node1436 node1436Labels =
    (37623398400 : ℝ) * (((-86275296000 : ℤ) : ℝ) * mixedMoment B node1436 node1436Labels + 0)
  ring

theorem reducedTermEval638 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm638 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm638 (originalVector B) := by
  rw [reducedTermArithmetic638, ← sound1438 B hB hF]
  change (39708998817546240000 : ℝ) * mixedMoment B node1438 node1438Labels =
    (37623398400 : ℝ) * ((1055433600 : ℝ) * mixedMoment B node1438 node1438Labels + 0)
  ring

theorem reducedTermEval639 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm639 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm639 (originalVector B) := by
  rw [reducedTermArithmetic639, ← sound1501 B hB hF]
  change (-1056230257065984000000 : ℝ) * mixedMoment B node1501 node1501Labels =
    (37623398400 : ℝ) * (((-28073760000 : ℤ) : ℝ) * mixedMoment B node1501 node1501Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval576 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge576 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge576 (originalVector B) := by
  rw [reducedMerge576Check, Integer.Sparse.eval_mergeBy, reducedTermEval582 B hB hF, reducedTermEval583 B hB hF]
  rw [originalMerge576, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval577 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge577 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge577 (originalVector B) := by
  rw [reducedMerge577Check, Integer.Sparse.eval_mergeBy, reducedMergeEval575 B hB hF, reducedMergeEval576 B hB hF]
  rw [originalMerge577, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval578 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge578 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge578 (originalVector B) := by
  rw [reducedMerge578Check, Integer.Sparse.eval_mergeBy, reducedMergeEval574 B hB hF, reducedMergeEval577 B hB hF]
  rw [originalMerge578, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval579 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge579 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge579 (originalVector B) := by
  rw [reducedMerge579Check, Integer.Sparse.eval_mergeBy, reducedMergeEval571 B hB hF, reducedMergeEval578 B hB hF]
  rw [originalMerge579, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval580 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge580 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge580 (originalVector B) := by
  rw [reducedMerge580Check, Integer.Sparse.eval_mergeBy, reducedTermEval585 B hB hF, reducedTermEval586 B hB hF]
  rw [originalMerge580, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval581 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge581 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge581 (originalVector B) := by
  rw [reducedMerge581Check, Integer.Sparse.eval_mergeBy, reducedTermEval584 B hB hF, reducedMergeEval580 B hB hF]
  rw [originalMerge581, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval582 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge582 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge582 (originalVector B) := by
  rw [reducedMerge582Check, Integer.Sparse.eval_mergeBy, reducedTermEval587 B hB hF, reducedTermEval588 B hB hF]
  rw [originalMerge582, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval583 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge583 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge583 (originalVector B) := by
  rw [reducedMerge583Check, Integer.Sparse.eval_mergeBy, reducedTermEval589 B hB hF, reducedTermEval590 B hB hF]
  rw [originalMerge583, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval584 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge584 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge584 (originalVector B) := by
  rw [reducedMerge584Check, Integer.Sparse.eval_mergeBy, reducedMergeEval582 B hB hF, reducedMergeEval583 B hB hF]
  rw [originalMerge584, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval585 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge585 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge585 (originalVector B) := by
  rw [reducedMerge585Check, Integer.Sparse.eval_mergeBy, reducedMergeEval581 B hB hF, reducedMergeEval584 B hB hF]
  rw [originalMerge585, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval586 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge586 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge586 (originalVector B) := by
  rw [reducedMerge586Check, Integer.Sparse.eval_mergeBy, reducedTermEval591 B hB hF, reducedTermEval592 B hB hF]
  rw [originalMerge586, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval587 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge587 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge587 (originalVector B) := by
  rw [reducedMerge587Check, Integer.Sparse.eval_mergeBy, reducedTermEval593 B hB hF, reducedTermEval594 B hB hF]
  rw [originalMerge587, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval588 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge588 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge588 (originalVector B) := by
  rw [reducedMerge588Check, Integer.Sparse.eval_mergeBy, reducedMergeEval586 B hB hF, reducedMergeEval587 B hB hF]
  rw [originalMerge588, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval589 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge589 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge589 (originalVector B) := by
  rw [reducedMerge589Check, Integer.Sparse.eval_mergeBy, reducedTermEval595 B hB hF, reducedTermEval596 B hB hF]
  rw [originalMerge589, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval590 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge590 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge590 (originalVector B) := by
  rw [reducedMerge590Check, Integer.Sparse.eval_mergeBy, reducedTermEval597 B hB hF, reducedTermEval598 B hB hF]
  rw [originalMerge590, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval591 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge591 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge591 (originalVector B) := by
  rw [reducedMerge591Check, Integer.Sparse.eval_mergeBy, reducedMergeEval589 B hB hF, reducedMergeEval590 B hB hF]
  rw [originalMerge591, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval592 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge592 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge592 (originalVector B) := by
  rw [reducedMerge592Check, Integer.Sparse.eval_mergeBy, reducedMergeEval588 B hB hF, reducedMergeEval591 B hB hF]
  rw [originalMerge592, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval593 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge593 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge593 (originalVector B) := by
  rw [reducedMerge593Check, Integer.Sparse.eval_mergeBy, reducedMergeEval585 B hB hF, reducedMergeEval592 B hB hF]
  rw [originalMerge593, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval594 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge594 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge594 (originalVector B) := by
  rw [reducedMerge594Check, Integer.Sparse.eval_mergeBy, reducedMergeEval579 B hB hF, reducedMergeEval593 B hB hF]
  rw [originalMerge594, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval595 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge595 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge595 (originalVector B) := by
  rw [reducedMerge595Check, Integer.Sparse.eval_mergeBy, reducedMergeEval565 B hB hF, reducedMergeEval594 B hB hF]
  rw [originalMerge595, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval596 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge596 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge596 (originalVector B) := by
  rw [reducedMerge596Check, Integer.Sparse.eval_mergeBy, reducedMergeEval536 B hB hF, reducedMergeEval595 B hB hF]
  rw [originalMerge596, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval597 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge597 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge597 (originalVector B) := by
  rw [reducedMerge597Check, Integer.Sparse.eval_mergeBy, reducedTermEval600 B hB hF, reducedTermEval601 B hB hF]
  rw [originalMerge597, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval598 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge598 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge598 (originalVector B) := by
  rw [reducedMerge598Check, Integer.Sparse.eval_mergeBy, reducedTermEval599 B hB hF, reducedMergeEval597 B hB hF]
  rw [originalMerge598, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval599 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge599 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge599 (originalVector B) := by
  rw [reducedMerge599Check, Integer.Sparse.eval_mergeBy, reducedTermEval602 B hB hF, reducedTermEval603 B hB hF]
  rw [originalMerge599, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval600 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge600 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge600 (originalVector B) := by
  rw [reducedMerge600Check, Integer.Sparse.eval_mergeBy, reducedTermEval604 B hB hF, reducedTermEval605 B hB hF]
  rw [originalMerge600, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval601 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge601 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge601 (originalVector B) := by
  rw [reducedMerge601Check, Integer.Sparse.eval_mergeBy, reducedMergeEval599 B hB hF, reducedMergeEval600 B hB hF]
  rw [originalMerge601, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval602 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge602 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge602 (originalVector B) := by
  rw [reducedMerge602Check, Integer.Sparse.eval_mergeBy, reducedMergeEval598 B hB hF, reducedMergeEval601 B hB hF]
  rw [originalMerge602, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval603 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge603 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge603 (originalVector B) := by
  rw [reducedMerge603Check, Integer.Sparse.eval_mergeBy, reducedTermEval606 B hB hF, reducedTermEval607 B hB hF]
  rw [originalMerge603, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval604 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge604 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge604 (originalVector B) := by
  rw [reducedMerge604Check, Integer.Sparse.eval_mergeBy, reducedTermEval608 B hB hF, reducedTermEval609 B hB hF]
  rw [originalMerge604, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval605 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge605 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge605 (originalVector B) := by
  rw [reducedMerge605Check, Integer.Sparse.eval_mergeBy, reducedMergeEval603 B hB hF, reducedMergeEval604 B hB hF]
  rw [originalMerge605, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval606 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge606 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge606 (originalVector B) := by
  rw [reducedMerge606Check, Integer.Sparse.eval_mergeBy, reducedTermEval610 B hB hF, reducedTermEval611 B hB hF]
  rw [originalMerge606, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval607 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge607 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge607 (originalVector B) := by
  rw [reducedMerge607Check, Integer.Sparse.eval_mergeBy, reducedTermEval612 B hB hF, reducedTermEval613 B hB hF]
  rw [originalMerge607, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval640 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm640 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm640 (originalVector B) := by
  rw [reducedTermArithmetic640, ← sound1502 B hB hF]
  change (-1423280520010137600000 : ℝ) * mixedMoment B node1502 node1502Labels =
    (37623398400 : ℝ) * (((-37829664000 : ℤ) : ℝ) * mixedMoment B node1502 node1502Labels + 0)
  ring

theorem reducedTermEval641 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm641 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm641 (originalVector B) := by
  rw [reducedTermArithmetic641, ← sound1504 B hB hF]
  change (-1951341470849433600000 : ℝ) * mixedMoment B node1504 node1504Labels =
    (37623398400 : ℝ) * (((-51865104000 : ℤ) : ℝ) * mixedMoment B node1504 node1504Labels + 0)
  ring

theorem reducedTermEval642 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm642 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm642 (originalVector B) := by
  rw [reducedTermArithmetic642, ← sound1505 B hB hF]
  change (1056230257065984000000 : ℝ) * mixedMoment B node1505 node1505Labels =
    (37623398400 : ℝ) * ((28073760000 : ℝ) * mixedMoment B node1505 node1505Labels + 0)
  ring

theorem reducedTermEval643 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm643 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm643 (originalVector B) := by
  rw [reducedTermArithmetic643, ← sound1508 B hB hF]
  change (1423280520010137600000 : ℝ) * mixedMoment B node1508 node1508Labels =
    (37623398400 : ℝ) * ((37829664000 : ℝ) * mixedMoment B node1508 node1508Labels + 0)
  ring

theorem reducedTermEval644 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm644 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm644 (originalVector B) := by
  rw [reducedTermArithmetic644, ← sound1510 B hB hF]
  change (-2210913934743306240000 : ℝ) * mixedMoment B node1510 node1510Labels =
    (37623398400 : ℝ) * (((-58764333600 : ℤ) : ℝ) * mixedMoment B node1510 node1510Labels + 0)
  ring

theorem reducedTermEval645 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm645 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm645 (originalVector B) := by
  rw [reducedTermArithmetic645, ← sound1511 B hB hF]
  change (-2862630613510520832000 : ℝ) * mixedMoment B node1511 node1511Labels =
    (37623398400 : ℝ) * (((-76086444480 : ℤ) : ℝ) * mixedMoment B node1511 node1511Labels + 0)
  ring

theorem reducedTermEval646 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm646 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm646 (originalVector B) := by
  rw [reducedTermArithmetic646, ← sound1512 B hB hF]
  change (-1812234680041734144000 : ℝ) * mixedMoment B node1512 node1512Labels =
    (37623398400 : ℝ) * (((-48167756160 : ℤ) : ℝ) * mixedMoment B node1512 node1512Labels + 0)
  ring

theorem reducedTermEval647 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm647 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm647 (originalVector B) := by
  rw [reducedTermArithmetic647, ← sound1513 B hB hF]
  change (807931683631005696000 : ℝ) * mixedMoment B node1513 node1513Labels =
    (37623398400 : ℝ) * ((21474181440 : ℝ) * mixedMoment B node1513 node1513Labels + 0)
  ring

theorem reducedTermEval648 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm648 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm648 (originalVector B) := by
  rw [reducedTermArithmetic648, ← sound1514 B hB hF]
  change (279082176459964416000 : ℝ) * mixedMoment B node1514 node1514Labels =
    (37623398400 : ℝ) * ((7417782240 : ℝ) * mixedMoment B node1514 node1514Labels + 0)
  ring

theorem reducedTermEval649 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm649 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm649 (originalVector B) := by
  rw [reducedTermArithmetic649, ← sound1515 B hB hF]
  change (1951341470849433600000 : ℝ) * mixedMoment B node1515 node1515Labels =
    (37623398400 : ℝ) * ((51865104000 : ℝ) * mixedMoment B node1515 node1515Labels + 0)
  ring

theorem reducedTermEval650 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm650 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm650 (originalVector B) := by
  rw [reducedTermArithmetic650, ← sound1516 B hB hF]
  change (1532149313286832128000 : ℝ) * mixedMoment B node1516 node1516Labels =
    (37623398400 : ℝ) * ((40723309920 : ℝ) * mixedMoment B node1516 node1516Labels + 0)
  ring

theorem reducedTermEval651 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm651 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm651 (originalVector B) := by
  rw [reducedTermArithmetic651, ← sound1520 B hB hF]
  change (3125626258862112768000 : ℝ) * mixedMoment B node1520 node1520Labels =
    (37623398400 : ℝ) * ((83076659520 : ℝ) * mixedMoment B node1520 node1520Labels + 0)
  ring

theorem reducedTermEval652 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm652 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm652 (originalVector B) := by
  rw [reducedTermArithmetic652, ← sound1522 B hB hF]
  change (1398340775856439296000 : ℝ) * mixedMoment B node1522 node1522Labels =
    (37623398400 : ℝ) * ((37166785440 : ℝ) * mixedMoment B node1522 node1522Labels + 0)
  ring

theorem reducedTermEval653 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm653 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm653 (originalVector B) := by
  rw [reducedTermArithmetic653, ← sound1523 B hB hF]
  change (1978196107527585792000 : ℝ) * mixedMoment B node1523 node1523Labels =
    (37623398400 : ℝ) * ((52578878880 : ℝ) * mixedMoment B node1523 node1523Labels + 0)
  ring

theorem reducedTermEval654 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm654 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm654 (originalVector B) := by
  rw [reducedTermArithmetic654, ← sound1526 B hB hF]
  change (3237439447258103808000 : ℝ) * mixedMoment B node1526 node1526Labels =
    (37623398400 : ℝ) * ((86048565120 : ℝ) * mixedMoment B node1526 node1526Labels + 0)
  ring

theorem reducedTermEval655 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm655 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm655 (originalVector B) := by
  rw [reducedTermArithmetic655, ← sound1528 B hB hF]
  change (-115736953684230144000 : ℝ) * mixedMoment B node1528 node1528Labels =
    (37623398400 : ℝ) * (((-3076196160 : ℤ) : ℝ) * mixedMoment B node1528 node1528Labels + 0)
  ring

theorem reducedTermEval656 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm656 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm656 (originalVector B) := by
  rw [reducedTermArithmetic656, ← sound1529 B hB hF]
  change (-190397481621258240000 : ℝ) * mixedMoment B node1529 node1529Labels =
    (37623398400 : ℝ) * (((-5060613600 : ℤ) : ℝ) * mixedMoment B node1529 node1529Labels + 0)
  ring

theorem reducedTermEval657 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm657 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm657 (originalVector B) := by
  rw [reducedTermArithmetic657, ← sound1530 B hB hF]
  change (-179029231679176704000 : ℝ) * mixedMoment B node1530 node1530Labels =
    (37623398400 : ℝ) * (((-4758454560 : ℤ) : ℝ) * mixedMoment B node1530 node1530Labels + 0)
  ring

theorem reducedTermEval658 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm658 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm658 (originalVector B) := by
  rw [reducedTermArithmetic658, ← sound1531 B hB hF]
  change (-24315273996926976000 : ℝ) * mixedMoment B node1531 node1531Labels =
    (37623398400 : ℝ) * (((-646280640 : ℤ) : ℝ) * mixedMoment B node1531 node1531Labels + 0)
  ring

theorem reducedTermEval659 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm659 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm659 (originalVector B) := by
  rw [reducedTermArithmetic659, ← sound1532 B hB hF]
  change (513372727945986048000 : ℝ) * mixedMoment B node1532 node1532Labels =
    (37623398400 : ℝ) * ((13645038720 : ℝ) * mixedMoment B node1532 node1532Labels + 0)
  ring

theorem reducedTermEval660 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm660 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm660 (originalVector B) := by
  rw [reducedTermArithmetic660, ← sound1533 B hB hF]
  change (3726326584597413888000 : ℝ) * mixedMoment B node1533 node1533Labels =
    (37623398400 : ℝ) * ((99042796320 : ℝ) * mixedMoment B node1533 node1533Labels + 0)
  ring

theorem reducedTermEval661 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm661 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm661 (originalVector B) := by
  rw [reducedTermArithmetic661, ← sound1534 B hB hF]
  change (92042023309737984000 : ℝ) * mixedMoment B node1534 node1534Labels =
    (37623398400 : ℝ) * ((2446403760 : ℝ) * mixedMoment B node1534 node1534Labels + 0)
  ring

theorem reducedTermEval662 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm662 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm662 (originalVector B) := by
  rw [reducedTermArithmetic662, ← sound1540 B hB hF]
  change (299269579737268224000 : ℝ) * mixedMoment B node1540 node1540Labels =
    (37623398400 : ℝ) * ((7954347360 : ℝ) * mixedMoment B node1540 node1540Labels + 0)
  ring

theorem reducedTermEval663 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm663 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm663 (originalVector B) := by
  rw [reducedTermArithmetic663, ← sound1667 B hB hF]
  change (-1090667657931522048000 : ℝ) * mixedMoment B node1667 node1667Labels =
    (37623398400 : ℝ) * (((-28989078720 : ℤ) : ℝ) * mixedMoment B node1667 node1667Labels + 0)
  ring

theorem reducedTermEval664 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm664 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm664 (originalVector B) := by
  rw [reducedTermArithmetic664, ← sound1668 B hB hF]
  change (-1101980502152183808000 : ℝ) * mixedMoment B node1668 node1668Labels =
    (37623398400 : ℝ) * (((-29289765120 : ℤ) : ℝ) * mixedMoment B node1668 node1668Labels + 0)
  ring

theorem reducedTermEval665 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm665 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm665 (originalVector B) := by
  rw [reducedTermArithmetic665, ← sound1670 B hB hF]
  change (-735052166107693056000 : ℝ) * mixedMoment B node1670 node1670Labels =
    (37623398400 : ℝ) * (((-19537101840 : ℤ) : ℝ) * mixedMoment B node1670 node1670Labels + 0)
  ring

theorem reducedTermEval666 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm666 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm666 (originalVector B) := by
  rw [reducedTermArithmetic666, ← sound1672 B hB hF]
  change (-615325865037004800000 : ℝ) * mixedMoment B node1672 node1672Labels =
    (37623398400 : ℝ) * (((-16354872000 : ℤ) : ℝ) * mixedMoment B node1672 node1672Labels + 0)
  ring

theorem reducedTermEval667 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm667 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm667 (originalVector B) := by
  rw [reducedTermArithmetic667, ← sound1676 B hB hF]
  change (441343231347916800000 : ℝ) * mixedMoment B node1676 node1676Labels =
    (37623398400 : ℝ) * ((11730552000 : ℝ) * mixedMoment B node1676 node1676Labels + 0)
  ring

theorem reducedTermEval668 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm668 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm668 (originalVector B) := by
  rw [reducedTermArithmetic668, ← sound1678 B hB hF]
  change (2798915153550114816000 : ℝ) * mixedMoment B node1678 node1678Labels =
    (37623398400 : ℝ) * ((74392938240 : ℝ) * mixedMoment B node1678 node1678Labels + 0)
  ring

theorem reducedTermEval669 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm669 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm669 (originalVector B) := by
  rw [reducedTermArithmetic669, ← sound1679 B hB hF]
  change (4204277593279561728000 : ℝ) * mixedMoment B node1679 node1679Labels =
    (37623398400 : ℝ) * ((111746353920 : ℝ) * mixedMoment B node1679 node1679Labels + 0)
  ring

theorem reducedTermEval670 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm670 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm670 (originalVector B) := by
  rw [reducedTermArithmetic670, ← sound1682 B hB hF]
  change (4390161007521300480000 : ℝ) * mixedMoment B node1682 node1682Labels =
    (37623398400 : ℝ) * ((116686987200 : ℝ) * mixedMoment B node1682 node1682Labels + 0)
  ring

theorem reducedTermEval671 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm671 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm671 (originalVector B) := by
  rw [reducedTermArithmetic671, ← sound1684 B hB hF]
  change (604529641244196864000 : ℝ) * mixedMoment B node1684 node1684Labels =
    (37623398400 : ℝ) * ((16067916960 : ℝ) * mixedMoment B node1684 node1684Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval608 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge608 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge608 (originalVector B) := by
  rw [reducedMerge608Check, Integer.Sparse.eval_mergeBy, reducedMergeEval606 B hB hF, reducedMergeEval607 B hB hF]
  rw [originalMerge608, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval609 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge609 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge609 (originalVector B) := by
  rw [reducedMerge609Check, Integer.Sparse.eval_mergeBy, reducedMergeEval605 B hB hF, reducedMergeEval608 B hB hF]
  rw [originalMerge609, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval610 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge610 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge610 (originalVector B) := by
  rw [reducedMerge610Check, Integer.Sparse.eval_mergeBy, reducedMergeEval602 B hB hF, reducedMergeEval609 B hB hF]
  rw [originalMerge610, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval611 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge611 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge611 (originalVector B) := by
  rw [reducedMerge611Check, Integer.Sparse.eval_mergeBy, reducedTermEval615 B hB hF, reducedTermEval616 B hB hF]
  rw [originalMerge611, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval612 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge612 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge612 (originalVector B) := by
  rw [reducedMerge612Check, Integer.Sparse.eval_mergeBy, reducedTermEval614 B hB hF, reducedMergeEval611 B hB hF]
  rw [originalMerge612, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval613 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge613 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge613 (originalVector B) := by
  rw [reducedMerge613Check, Integer.Sparse.eval_mergeBy, reducedTermEval617 B hB hF, reducedTermEval618 B hB hF]
  rw [originalMerge613, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval614 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge614 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge614 (originalVector B) := by
  rw [reducedMerge614Check, Integer.Sparse.eval_mergeBy, reducedTermEval619 B hB hF, reducedTermEval620 B hB hF]
  rw [originalMerge614, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval615 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge615 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge615 (originalVector B) := by
  rw [reducedMerge615Check, Integer.Sparse.eval_mergeBy, reducedMergeEval613 B hB hF, reducedMergeEval614 B hB hF]
  rw [originalMerge615, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval616 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge616 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge616 (originalVector B) := by
  rw [reducedMerge616Check, Integer.Sparse.eval_mergeBy, reducedMergeEval612 B hB hF, reducedMergeEval615 B hB hF]
  rw [originalMerge616, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval617 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge617 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge617 (originalVector B) := by
  rw [reducedMerge617Check, Integer.Sparse.eval_mergeBy, reducedTermEval621 B hB hF, reducedTermEval622 B hB hF]
  rw [originalMerge617, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval618 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge618 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge618 (originalVector B) := by
  rw [reducedMerge618Check, Integer.Sparse.eval_mergeBy, reducedTermEval623 B hB hF, reducedTermEval624 B hB hF]
  rw [originalMerge618, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval619 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge619 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge619 (originalVector B) := by
  rw [reducedMerge619Check, Integer.Sparse.eval_mergeBy, reducedMergeEval617 B hB hF, reducedMergeEval618 B hB hF]
  rw [originalMerge619, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval620 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge620 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge620 (originalVector B) := by
  rw [reducedMerge620Check, Integer.Sparse.eval_mergeBy, reducedTermEval625 B hB hF, reducedTermEval626 B hB hF]
  rw [originalMerge620, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval621 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge621 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge621 (originalVector B) := by
  rw [reducedMerge621Check, Integer.Sparse.eval_mergeBy, reducedTermEval627 B hB hF, reducedTermEval628 B hB hF]
  rw [originalMerge621, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval622 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge622 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge622 (originalVector B) := by
  rw [reducedMerge622Check, Integer.Sparse.eval_mergeBy, reducedMergeEval620 B hB hF, reducedMergeEval621 B hB hF]
  rw [originalMerge622, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval623 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge623 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge623 (originalVector B) := by
  rw [reducedMerge623Check, Integer.Sparse.eval_mergeBy, reducedMergeEval619 B hB hF, reducedMergeEval622 B hB hF]
  rw [originalMerge623, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval624 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge624 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge624 (originalVector B) := by
  rw [reducedMerge624Check, Integer.Sparse.eval_mergeBy, reducedMergeEval616 B hB hF, reducedMergeEval623 B hB hF]
  rw [originalMerge624, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval625 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge625 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge625 (originalVector B) := by
  rw [reducedMerge625Check, Integer.Sparse.eval_mergeBy, reducedMergeEval610 B hB hF, reducedMergeEval624 B hB hF]
  rw [originalMerge625, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval626 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge626 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge626 (originalVector B) := by
  rw [reducedMerge626Check, Integer.Sparse.eval_mergeBy, reducedTermEval630 B hB hF, reducedTermEval631 B hB hF]
  rw [originalMerge626, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval627 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge627 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge627 (originalVector B) := by
  rw [reducedMerge627Check, Integer.Sparse.eval_mergeBy, reducedTermEval629 B hB hF, reducedMergeEval626 B hB hF]
  rw [originalMerge627, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval628 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge628 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge628 (originalVector B) := by
  rw [reducedMerge628Check, Integer.Sparse.eval_mergeBy, reducedTermEval632 B hB hF, reducedTermEval633 B hB hF]
  rw [originalMerge628, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval629 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge629 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge629 (originalVector B) := by
  rw [reducedMerge629Check, Integer.Sparse.eval_mergeBy, reducedTermEval634 B hB hF, reducedTermEval635 B hB hF]
  rw [originalMerge629, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval630 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge630 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge630 (originalVector B) := by
  rw [reducedMerge630Check, Integer.Sparse.eval_mergeBy, reducedMergeEval628 B hB hF, reducedMergeEval629 B hB hF]
  rw [originalMerge630, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval631 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge631 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge631 (originalVector B) := by
  rw [reducedMerge631Check, Integer.Sparse.eval_mergeBy, reducedMergeEval627 B hB hF, reducedMergeEval630 B hB hF]
  rw [originalMerge631, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval632 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge632 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge632 (originalVector B) := by
  rw [reducedMerge632Check, Integer.Sparse.eval_mergeBy, reducedTermEval636 B hB hF, reducedTermEval637 B hB hF]
  rw [originalMerge632, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval633 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge633 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge633 (originalVector B) := by
  rw [reducedMerge633Check, Integer.Sparse.eval_mergeBy, reducedTermEval638 B hB hF, reducedTermEval639 B hB hF]
  rw [originalMerge633, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval634 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge634 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge634 (originalVector B) := by
  rw [reducedMerge634Check, Integer.Sparse.eval_mergeBy, reducedMergeEval632 B hB hF, reducedMergeEval633 B hB hF]
  rw [originalMerge634, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval635 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge635 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge635 (originalVector B) := by
  rw [reducedMerge635Check, Integer.Sparse.eval_mergeBy, reducedTermEval640 B hB hF, reducedTermEval641 B hB hF]
  rw [originalMerge635, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval636 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge636 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge636 (originalVector B) := by
  rw [reducedMerge636Check, Integer.Sparse.eval_mergeBy, reducedTermEval642 B hB hF, reducedTermEval643 B hB hF]
  rw [originalMerge636, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval637 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge637 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge637 (originalVector B) := by
  rw [reducedMerge637Check, Integer.Sparse.eval_mergeBy, reducedMergeEval635 B hB hF, reducedMergeEval636 B hB hF]
  rw [originalMerge637, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval638 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge638 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge638 (originalVector B) := by
  rw [reducedMerge638Check, Integer.Sparse.eval_mergeBy, reducedMergeEval634 B hB hF, reducedMergeEval637 B hB hF]
  rw [originalMerge638, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval639 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge639 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge639 (originalVector B) := by
  rw [reducedMerge639Check, Integer.Sparse.eval_mergeBy, reducedMergeEval631 B hB hF, reducedMergeEval638 B hB hF]
  rw [originalMerge639, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval672 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm672 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm672 (originalVector B) := by
  rw [reducedTermArithmetic672, ← sound1685 B hB hF]
  change (910860777696264192000 : ℝ) * mixedMoment B node1685 node1685Labels =
    (37623398400 : ℝ) * ((24209954880 : ℝ) * mixedMoment B node1685 node1685Labels + 0)
  ring

theorem reducedTermEval673 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm673 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm673 (originalVector B) := by
  rw [reducedTermArithmetic673, ← sound1686 B hB hF]
  change (789405404560883712000 : ℝ) * mixedMoment B node1686 node1686Labels =
    (37623398400 : ℝ) * ((20981767680 : ℝ) * mixedMoment B node1686 node1686Labels + 0)
  ring

theorem reducedTermEval674 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm674 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm674 (originalVector B) := by
  rw [reducedTermArithmetic674, ← sound1687 B hB hF]
  change (-120789168095232000000 : ℝ) * mixedMoment B node1687 node1687Labels =
    (37623398400 : ℝ) * (((-3210480000 : ℤ) : ℝ) * mixedMoment B node1687 node1687Labels + 0)
  ring

theorem reducedTermEval675 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm675 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm675 (originalVector B) := by
  rw [reducedTermArithmetic675, ← sound1688 B hB hF]
  change (1305313133883752448000 : ℝ) * mixedMoment B node1688 node1688Labels =
    (37623398400 : ℝ) * ((34694184720 : ℝ) * mixedMoment B node1688 node1688Labels + 0)
  ring

theorem reducedTermEval676 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm676 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm676 (originalVector B) := by
  rw [reducedTermArithmetic676, ← sound1689 B hB hF]
  change (3666193326655340544000 : ℝ) * mixedMoment B node1689 node1689Labels =
    (37623398400 : ℝ) * ((97444502160 : ℝ) * mixedMoment B node1689 node1689Labels + 0)
  ring

theorem reducedTermEval677 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm677 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm677 (originalVector B) := by
  rw [reducedTermArithmetic677, ← sound1695 B hB hF]
  change (888021087364841472000 : ℝ) * mixedMoment B node1695 node1695Labels =
    (37623398400 : ℝ) * ((23602894080 : ℝ) * mixedMoment B node1695 node1695Labels + 0)
  ring

theorem reducedTermEval678 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm678 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm678 (originalVector B) := by
  rw [reducedTermArithmetic678, ← sound1697 B hB hF]
  change (550098197290156032000 : ℝ) * mixedMoment B node1697 node1697Labels =
    (37623398400 : ℝ) * ((14621172480 : ℝ) * mixedMoment B node1697 node1697Labels + 0)
  ring

theorem reducedTermEval679 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm679 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm679 (originalVector B) := by
  rw [reducedTermArithmetic679, ← sound1699 B hB hF]
  change (-902368496446341120000 : ℝ) * mixedMoment B node1699 node1699Labels =
    (37623398400 : ℝ) * (((-23984236800 : ℤ) : ℝ) * mixedMoment B node1699 node1699Labels + 0)
  ring

theorem reducedTermEval680 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm680 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm680 (originalVector B) := by
  rw [reducedTermArithmetic680, ← sound1700 B hB hF]
  change (-1069052130648391680000 : ℝ) * mixedMoment B node1700 node1700Labels =
    (37623398400 : ℝ) * (((-28414555200 : ℤ) : ℝ) * mixedMoment B node1700 node1700Labels + 0)
  ring

theorem reducedTermEval681 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm681 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm681 (originalVector B) := by
  rw [reducedTermArithmetic681, ← sound1703 B hB hF]
  change (2007627038014832640000 : ℝ) * mixedMoment B node1703 node1703Labels =
    (37623398400 : ℝ) * ((53361129600 : ℝ) * mixedMoment B node1703 node1703Labels + 0)
  ring

theorem reducedTermEval682 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm682 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm682 (originalVector B) := by
  rw [reducedTermArithmetic682, ← sound1704 B hB hF]
  change (583395049348005888000 : ℝ) * mixedMoment B node1704 node1704Labels =
    (37623398400 : ℝ) * ((15506176320 : ℝ) * mixedMoment B node1704 node1704Labels + 0)
  ring

theorem reducedTermEval683 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm683 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm683 (originalVector B) := by
  rw [reducedTermArithmetic683, ← sound1709 B hB hF]
  change (-2010373847085219840000 : ℝ) * mixedMoment B node1709 node1709Labels =
    (37623398400 : ℝ) * (((-53434137600 : ℤ) : ℝ) * mixedMoment B node1709 node1709Labels + 0)
  ring

theorem reducedTermEval684 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm684 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm684 (originalVector B) := by
  rw [reducedTermArithmetic684, ← sound1711 B hB hF]
  change (-4752834733161381888000 : ℝ) * mixedMoment B node1711 node1711Labels =
    (37623398400 : ℝ) * (((-126326566320 : ℤ) : ℝ) * mixedMoment B node1711 node1711Labels + 0)
  ring

theorem reducedTermEval685 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm685 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm685 (originalVector B) := by
  rw [reducedTermArithmetic685, ← sound1712 B hB hF]
  change (-4818691431020888064000 : ℝ) * mixedMoment B node1712 node1712Labels =
    (37623398400 : ℝ) * (((-128076984960 : ℤ) : ℝ) * mixedMoment B node1712 node1712Labels + 0)
  ring

theorem reducedTermEval686 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm686 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm686 (originalVector B) := by
  rw [reducedTermArithmetic686, ← sound1713 B hB hF]
  change (-3378878307861331968000 : ℝ) * mixedMoment B node1713 node1713Labels =
    (37623398400 : ℝ) * (((-89807897520 : ℤ) : ℝ) * mixedMoment B node1713 node1713Labels + 0)
  ring

theorem reducedTermEval687 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm687 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm687 (originalVector B) := by
  rw [reducedTermArithmetic687, ← sound1714 B hB hF]
  change (-6227807807028068352000 : ℝ) * mixedMoment B node1714 node1714Labels =
    (37623398400 : ℝ) * (((-165530177280 : ℤ) : ℝ) * mixedMoment B node1714 node1714Labels + 0)
  ring

theorem reducedTermEval688 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm688 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm688 (originalVector B) := by
  rw [reducedTermArithmetic688, ← sound1715 B hB hF]
  change (-2138368756797407232000 : ℝ) * mixedMoment B node1715 node1715Labels =
    (37623398400 : ℝ) * (((-56836140480 : ℤ) : ℝ) * mixedMoment B node1715 node1715Labels + 0)
  ring

theorem reducedTermEval689 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm689 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm689 (originalVector B) := by
  rw [reducedTermArithmetic689, ← sound1716 B hB hF]
  change (1926014843785052160000 : ℝ) * mixedMoment B node1716 node1716Labels =
    (37623398400 : ℝ) * ((51191942400 : ℝ) * mixedMoment B node1716 node1716Labels + 0)
  ring

theorem reducedTermEval690 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm690 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm690 (originalVector B) := by
  rw [reducedTermArithmetic690, ← sound1720 B hB hF]
  change (-1541521449311993856000 : ℝ) * mixedMoment B node1720 node1720Labels =
    (37623398400 : ℝ) * (((-40972413840 : ℤ) : ℝ) * mixedMoment B node1720 node1720Labels + 0)
  ring

theorem reducedTermEval691 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm691 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm691 (originalVector B) := by
  rw [reducedTermArithmetic691, ← sound1721 B hB hF]
  change (1386207265990901760000 : ℝ) * mixedMoment B node1721 node1721Labels =
    (37623398400 : ℝ) * ((36844286400 : ℝ) * mixedMoment B node1721 node1721Labels + 0)
  ring

theorem reducedTermEval692 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm692 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm692 (originalVector B) := by
  rw [reducedTermArithmetic692, ← sound1722 B hB hF]
  change (1717512314662158336000 : ℝ) * mixedMoment B node1722 node1722Labels =
    (37623398400 : ℝ) * ((45650111040 : ℝ) * mixedMoment B node1722 node1722Labels + 0)
  ring

theorem reducedTermEval693 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm693 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm693 (originalVector B) := by
  rw [reducedTermArithmetic693, ← sound1723 B hB hF]
  change (-4810412754357977088000 : ℝ) * mixedMoment B node1723 node1723Labels =
    (37623398400 : ℝ) * (((-127856944320 : ℤ) : ℝ) * mixedMoment B node1723 node1723Labels + 0)
  ring

theorem reducedTermEval694 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm694 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm694 (originalVector B) := by
  rw [reducedTermArithmetic694, ← sound1729 B hB hF]
  change (3751773612556419072000 : ℝ) * mixedMoment B node1729 node1729Labels =
    (37623398400 : ℝ) * ((99719158080 : ℝ) * mixedMoment B node1729 node1729Labels + 0)
  ring

theorem reducedTermEval695 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm695 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm695 (originalVector B) := by
  rw [reducedTermArithmetic695, ← sound1734 B hB hF]
  change (-95615204742070272000 : ℝ) * mixedMoment B node1734 node1734Labels =
    (37623398400 : ℝ) * (((-2541376080 : ℤ) : ℝ) * mixedMoment B node1734 node1734Labels + 0)
  ring

theorem reducedTermEval696 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm696 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm696 (originalVector B) := by
  rw [reducedTermArithmetic696, ← sound1735 B hB hF]
  change (2302759193699155968000 : ℝ) * mixedMoment B node1735 node1735Labels =
    (37623398400 : ℝ) * ((61205507520 : ℝ) * mixedMoment B node1735 node1735Labels + 0)
  ring

theorem reducedTermEval697 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm697 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm697 (originalVector B) := by
  rw [reducedTermArithmetic697, ← sound1736 B hB hF]
  change (2459234748121546752000 : ℝ) * mixedMoment B node1736 node1736Labels =
    (37623398400 : ℝ) * ((65364503280 : ℝ) * mixedMoment B node1736 node1736Labels + 0)
  ring

theorem reducedTermEval698 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm698 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm698 (originalVector B) := by
  rw [reducedTermArithmetic698, ← sound1740 B hB hF]
  change (4524755554931834880000 : ℝ) * mixedMoment B node1740 node1740Labels =
    (37623398400 : ℝ) * ((120264403200 : ℝ) * mixedMoment B node1740 node1740Labels + 0)
  ring

theorem reducedTermEval699 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm699 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm699 (originalVector B) := by
  rw [reducedTermArithmetic699, ← sound1742 B hB hF]
  change (119212994511765504000 : ℝ) * mixedMoment B node1742 node1742Labels =
    (37623398400 : ℝ) * ((3168586560 : ℝ) * mixedMoment B node1742 node1742Labels + 0)
  ring

theorem reducedTermEval700 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm700 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm700 (originalVector B) := by
  rw [reducedTermArithmetic700, ← sound1743 B hB hF]
  change (-8626840581832704000 : ℝ) * mixedMoment B node1743 node1743Labels =
    (37623398400 : ℝ) * (((-229294560 : ℤ) : ℝ) * mixedMoment B node1743 node1743Labels + 0)
  ring

theorem reducedTermEval701 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm701 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm701 (originalVector B) := by
  rw [reducedTermArithmetic701, ← sound1744 B hB hF]
  change (-554123003977138176000 : ℝ) * mixedMoment B node1744 node1744Labels =
    (37623398400 : ℝ) * (((-14728148640 : ℤ) : ℝ) * mixedMoment B node1744 node1744Labels + 0)
  ring

theorem reducedTermEval702 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm702 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm702 (originalVector B) := by
  rw [reducedTermArithmetic702, ← sound1745 B hB hF]
  change (-2769188286440669184000 : ℝ) * mixedMoment B node1745 node1745Labels =
    (37623398400 : ℝ) * (((-73602821760 : ℤ) : ℝ) * mixedMoment B node1745 node1745Labels + 0)
  ring

theorem reducedTermEval703 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm703 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm703 (originalVector B) := by
  rw [reducedTermArithmetic703, ← sound1746 B hB hF]
  change (-3563661364114489344000 : ℝ) * mixedMoment B node1746 node1746Labels =
    (37623398400 : ℝ) * (((-94719284160 : ℤ) : ℝ) * mixedMoment B node1746 node1746Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval640 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge640 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge640 (originalVector B) := by
  rw [reducedMerge640Check, Integer.Sparse.eval_mergeBy, reducedTermEval645 B hB hF, reducedTermEval646 B hB hF]
  rw [originalMerge640, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval641 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge641 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge641 (originalVector B) := by
  rw [reducedMerge641Check, Integer.Sparse.eval_mergeBy, reducedTermEval644 B hB hF, reducedMergeEval640 B hB hF]
  rw [originalMerge641, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval642 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge642 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge642 (originalVector B) := by
  rw [reducedMerge642Check, Integer.Sparse.eval_mergeBy, reducedTermEval647 B hB hF, reducedTermEval648 B hB hF]
  rw [originalMerge642, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval643 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge643 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge643 (originalVector B) := by
  rw [reducedMerge643Check, Integer.Sparse.eval_mergeBy, reducedTermEval649 B hB hF, reducedTermEval650 B hB hF]
  rw [originalMerge643, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval644 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge644 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge644 (originalVector B) := by
  rw [reducedMerge644Check, Integer.Sparse.eval_mergeBy, reducedMergeEval642 B hB hF, reducedMergeEval643 B hB hF]
  rw [originalMerge644, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval645 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge645 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge645 (originalVector B) := by
  rw [reducedMerge645Check, Integer.Sparse.eval_mergeBy, reducedMergeEval641 B hB hF, reducedMergeEval644 B hB hF]
  rw [originalMerge645, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval646 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge646 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge646 (originalVector B) := by
  rw [reducedMerge646Check, Integer.Sparse.eval_mergeBy, reducedTermEval651 B hB hF, reducedTermEval652 B hB hF]
  rw [originalMerge646, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval647 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge647 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge647 (originalVector B) := by
  rw [reducedMerge647Check, Integer.Sparse.eval_mergeBy, reducedTermEval653 B hB hF, reducedTermEval654 B hB hF]
  rw [originalMerge647, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval648 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge648 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge648 (originalVector B) := by
  rw [reducedMerge648Check, Integer.Sparse.eval_mergeBy, reducedMergeEval646 B hB hF, reducedMergeEval647 B hB hF]
  rw [originalMerge648, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval649 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge649 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge649 (originalVector B) := by
  rw [reducedMerge649Check, Integer.Sparse.eval_mergeBy, reducedTermEval655 B hB hF, reducedTermEval656 B hB hF]
  rw [originalMerge649, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval650 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge650 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge650 (originalVector B) := by
  rw [reducedMerge650Check, Integer.Sparse.eval_mergeBy, reducedTermEval657 B hB hF, reducedTermEval658 B hB hF]
  rw [originalMerge650, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval651 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge651 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge651 (originalVector B) := by
  rw [reducedMerge651Check, Integer.Sparse.eval_mergeBy, reducedMergeEval649 B hB hF, reducedMergeEval650 B hB hF]
  rw [originalMerge651, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval652 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge652 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge652 (originalVector B) := by
  rw [reducedMerge652Check, Integer.Sparse.eval_mergeBy, reducedMergeEval648 B hB hF, reducedMergeEval651 B hB hF]
  rw [originalMerge652, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval653 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge653 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge653 (originalVector B) := by
  rw [reducedMerge653Check, Integer.Sparse.eval_mergeBy, reducedMergeEval645 B hB hF, reducedMergeEval652 B hB hF]
  rw [originalMerge653, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval654 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge654 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge654 (originalVector B) := by
  rw [reducedMerge654Check, Integer.Sparse.eval_mergeBy, reducedMergeEval639 B hB hF, reducedMergeEval653 B hB hF]
  rw [originalMerge654, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval655 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge655 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge655 (originalVector B) := by
  rw [reducedMerge655Check, Integer.Sparse.eval_mergeBy, reducedMergeEval625 B hB hF, reducedMergeEval654 B hB hF]
  rw [originalMerge655, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval656 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge656 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge656 (originalVector B) := by
  rw [reducedMerge656Check, Integer.Sparse.eval_mergeBy, reducedTermEval660 B hB hF, reducedTermEval661 B hB hF]
  rw [originalMerge656, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval657 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge657 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge657 (originalVector B) := by
  rw [reducedMerge657Check, Integer.Sparse.eval_mergeBy, reducedTermEval659 B hB hF, reducedMergeEval656 B hB hF]
  rw [originalMerge657, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval658 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge658 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge658 (originalVector B) := by
  rw [reducedMerge658Check, Integer.Sparse.eval_mergeBy, reducedTermEval662 B hB hF, reducedTermEval663 B hB hF]
  rw [originalMerge658, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval659 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge659 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge659 (originalVector B) := by
  rw [reducedMerge659Check, Integer.Sparse.eval_mergeBy, reducedTermEval664 B hB hF, reducedTermEval665 B hB hF]
  rw [originalMerge659, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval660 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge660 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge660 (originalVector B) := by
  rw [reducedMerge660Check, Integer.Sparse.eval_mergeBy, reducedMergeEval658 B hB hF, reducedMergeEval659 B hB hF]
  rw [originalMerge660, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval661 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge661 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge661 (originalVector B) := by
  rw [reducedMerge661Check, Integer.Sparse.eval_mergeBy, reducedMergeEval657 B hB hF, reducedMergeEval660 B hB hF]
  rw [originalMerge661, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval662 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge662 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge662 (originalVector B) := by
  rw [reducedMerge662Check, Integer.Sparse.eval_mergeBy, reducedTermEval666 B hB hF, reducedTermEval667 B hB hF]
  rw [originalMerge662, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval663 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge663 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge663 (originalVector B) := by
  rw [reducedMerge663Check, Integer.Sparse.eval_mergeBy, reducedTermEval668 B hB hF, reducedTermEval669 B hB hF]
  rw [originalMerge663, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval664 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge664 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge664 (originalVector B) := by
  rw [reducedMerge664Check, Integer.Sparse.eval_mergeBy, reducedMergeEval662 B hB hF, reducedMergeEval663 B hB hF]
  rw [originalMerge664, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval665 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge665 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge665 (originalVector B) := by
  rw [reducedMerge665Check, Integer.Sparse.eval_mergeBy, reducedTermEval670 B hB hF, reducedTermEval671 B hB hF]
  rw [originalMerge665, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval666 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge666 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge666 (originalVector B) := by
  rw [reducedMerge666Check, Integer.Sparse.eval_mergeBy, reducedTermEval672 B hB hF, reducedTermEval673 B hB hF]
  rw [originalMerge666, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval667 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge667 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge667 (originalVector B) := by
  rw [reducedMerge667Check, Integer.Sparse.eval_mergeBy, reducedMergeEval665 B hB hF, reducedMergeEval666 B hB hF]
  rw [originalMerge667, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval668 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge668 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge668 (originalVector B) := by
  rw [reducedMerge668Check, Integer.Sparse.eval_mergeBy, reducedMergeEval664 B hB hF, reducedMergeEval667 B hB hF]
  rw [originalMerge668, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval669 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge669 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge669 (originalVector B) := by
  rw [reducedMerge669Check, Integer.Sparse.eval_mergeBy, reducedMergeEval661 B hB hF, reducedMergeEval668 B hB hF]
  rw [originalMerge669, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval670 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge670 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge670 (originalVector B) := by
  rw [reducedMerge670Check, Integer.Sparse.eval_mergeBy, reducedTermEval675 B hB hF, reducedTermEval676 B hB hF]
  rw [originalMerge670, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval671 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge671 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge671 (originalVector B) := by
  rw [reducedMerge671Check, Integer.Sparse.eval_mergeBy, reducedTermEval674 B hB hF, reducedMergeEval670 B hB hF]
  rw [originalMerge671, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval704 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm704 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm704 (originalVector B) := by
  rw [reducedTermArithmetic704, ← sound1747 B hB hF]
  change (-1117582666619682816000 : ℝ) * mixedMoment B node1747 node1747Labels =
    (37623398400 : ℝ) * (((-29704458240 : ℤ) : ℝ) * mixedMoment B node1747 node1747Labels + 0)
  ring

theorem reducedTermEval705 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm705 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm705 (originalVector B) := by
  rw [reducedTermArithmetic705, ← sound1748 B hB hF]
  change (4393837063364345856000 : ℝ) * mixedMoment B node1748 node1748Labels =
    (37623398400 : ℝ) * ((116784693840 : ℝ) * mixedMoment B node1748 node1748Labels + 0)
  ring

theorem reducedTermEval706 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm706 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm706 (originalVector B) := by
  rw [reducedTermArithmetic706, ← sound1749 B hB hF]
  change (-722047208039055360000 : ℝ) * mixedMoment B node1749 node1749Labels =
    (37623398400 : ℝ) * (((-19191440400 : ℤ) : ℝ) * mixedMoment B node1749 node1749Labels + 0)
  ring

theorem reducedTermEval707 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm707 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm707 (originalVector B) := by
  rw [reducedTermArithmetic707, ← sound1757 B hB hF]
  change (-474172475731476480000 : ℝ) * mixedMoment B node1757 node1757Labels =
    (37623398400 : ℝ) * (((-12603127200 : ℤ) : ℝ) * mixedMoment B node1757 node1757Labels + 0)
  ring

theorem reducedTermEval708 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm708 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm708 (originalVector B) := by
  rw [reducedTermArithmetic708, ← sound1789 B hB hF]
  change (654308882759024640000 : ℝ) * mixedMoment B node1789 node1789Labels =
    (37623398400 : ℝ) * ((17391009600 : ℝ) * mixedMoment B node1789 node1789Labels + 0)
  ring

theorem reducedTermEval709 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm709 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm709 (originalVector B) := by
  rw [reducedTermArithmetic709, ← sound1790 B hB hF]
  change (-4566900924634890240000 : ℝ) * mixedMoment B node1790 node1790Labels =
    (37623398400 : ℝ) * (((-121384593600 : ℤ) : ℝ) * mixedMoment B node1790 node1790Labels + 0)
  ring

theorem reducedTermEval710 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm710 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm710 (originalVector B) := by
  rw [reducedTermArithmetic710, ← sound1791 B hB hF]
  change (-6742174334468751360000 : ℝ) * mixedMoment B node1791 node1791Labels =
    (37623398400 : ℝ) * (((-179201630400 : ℤ) : ℝ) * mixedMoment B node1791 node1791Labels + 0)
  ring

theorem reducedTermEval711 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm711 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm711 (originalVector B) := by
  rw [reducedTermArithmetic711, ← sound1792 B hB hF]
  change (2282493232765992960000 : ℝ) * mixedMoment B node1792 node1792Labels =
    (37623398400 : ℝ) * ((60666854400 : ℝ) * mixedMoment B node1792 node1792Labels + 0)
  ring

theorem reducedTermEval712 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm712 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm712 (originalVector B) := by
  rw [reducedTermArithmetic712, ← sound1793 B hB hF]
  change (3731415152240885760000 : ℝ) * mixedMoment B node1793 node1793Labels =
    (37623398400 : ℝ) * ((99178046400 : ℝ) * mixedMoment B node1793 node1793Labels + 0)
  ring

theorem reducedTermEval713 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm713 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm713 (originalVector B) := by
  rw [reducedTermArithmetic713, ← sound1794 B hB hF]
  change (673420605987225600000 : ℝ) * mixedMoment B node1794 node1794Labels =
    (37623398400 : ℝ) * ((17898984000 : ℝ) * mixedMoment B node1794 node1794Labels + 0)
  ring

theorem reducedTermEval714 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm714 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm714 (originalVector B) := by
  rw [reducedTermArithmetic714, ← sound1795 B hB hF]
  change (8275744746720460800000 : ℝ) * mixedMoment B node1795 node1795Labels =
    (37623398400 : ℝ) * ((219962712000 : ℝ) * mixedMoment B node1795 node1795Labels + 0)
  ring

theorem reducedTermEval715 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm715 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm715 (originalVector B) := by
  rw [reducedTermArithmetic715, ← sound1796 B hB hF]
  change (8393450481675141120000 : ℝ) * mixedMoment B node1796 node1796Labels =
    (37623398400 : ℝ) * ((223091236800 : ℝ) * mixedMoment B node1796 node1796Labels + 0)
  ring

theorem reducedTermEval716 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm716 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm716 (originalVector B) := by
  rw [reducedTermArithmetic716, ← sound1797 B hB hF]
  change (5418404332170117120000 : ℝ) * mixedMoment B node1797 node1797Labels =
    (37623398400 : ℝ) * ((144016876800 : ℝ) * mixedMoment B node1797 node1797Labels + 0)
  ring

theorem reducedTermEval717 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm717 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm717 (originalVector B) := by
  rw [reducedTermArithmetic717, ← sound1802 B hB hF]
  change (6265573704801976320000 : ℝ) * mixedMoment B node1802 node1802Labels =
    (37623398400 : ℝ) * ((166533964800 : ℝ) * mixedMoment B node1802 node1802Labels + 0)
  ring

theorem reducedTermEval718 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm718 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm718 (originalVector B) := by
  rw [reducedTermArithmetic718, ← sound1803 B hB hF]
  change (28541892592926720000 : ℝ) * mixedMoment B node1803 node1803Labels =
    (37623398400 : ℝ) * ((758620800 : ℝ) * mixedMoment B node1803 node1803Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval672 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge672 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge672 (originalVector B) := by
  rw [reducedMerge672Check, Integer.Sparse.eval_mergeBy, reducedTermEval677 B hB hF, reducedTermEval678 B hB hF]
  rw [originalMerge672, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval673 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge673 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge673 (originalVector B) := by
  rw [reducedMerge673Check, Integer.Sparse.eval_mergeBy, reducedTermEval679 B hB hF, reducedTermEval680 B hB hF]
  rw [originalMerge673, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval674 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge674 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge674 (originalVector B) := by
  rw [reducedMerge674Check, Integer.Sparse.eval_mergeBy, reducedMergeEval672 B hB hF, reducedMergeEval673 B hB hF]
  rw [originalMerge674, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval675 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge675 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge675 (originalVector B) := by
  rw [reducedMerge675Check, Integer.Sparse.eval_mergeBy, reducedMergeEval671 B hB hF, reducedMergeEval674 B hB hF]
  rw [originalMerge675, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval676 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge676 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge676 (originalVector B) := by
  rw [reducedMerge676Check, Integer.Sparse.eval_mergeBy, reducedTermEval681 B hB hF, reducedTermEval682 B hB hF]
  rw [originalMerge676, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval677 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge677 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge677 (originalVector B) := by
  rw [reducedMerge677Check, Integer.Sparse.eval_mergeBy, reducedTermEval683 B hB hF, reducedTermEval684 B hB hF]
  rw [originalMerge677, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval678 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge678 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge678 (originalVector B) := by
  rw [reducedMerge678Check, Integer.Sparse.eval_mergeBy, reducedMergeEval676 B hB hF, reducedMergeEval677 B hB hF]
  rw [originalMerge678, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval679 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge679 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge679 (originalVector B) := by
  rw [reducedMerge679Check, Integer.Sparse.eval_mergeBy, reducedTermEval685 B hB hF, reducedTermEval686 B hB hF]
  rw [originalMerge679, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval680 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge680 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge680 (originalVector B) := by
  rw [reducedMerge680Check, Integer.Sparse.eval_mergeBy, reducedTermEval687 B hB hF, reducedTermEval688 B hB hF]
  rw [originalMerge680, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval681 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge681 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge681 (originalVector B) := by
  rw [reducedMerge681Check, Integer.Sparse.eval_mergeBy, reducedMergeEval679 B hB hF, reducedMergeEval680 B hB hF]
  rw [originalMerge681, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval682 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge682 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge682 (originalVector B) := by
  rw [reducedMerge682Check, Integer.Sparse.eval_mergeBy, reducedMergeEval678 B hB hF, reducedMergeEval681 B hB hF]
  rw [originalMerge682, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval683 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge683 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge683 (originalVector B) := by
  rw [reducedMerge683Check, Integer.Sparse.eval_mergeBy, reducedMergeEval675 B hB hF, reducedMergeEval682 B hB hF]
  rw [originalMerge683, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval684 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge684 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge684 (originalVector B) := by
  rw [reducedMerge684Check, Integer.Sparse.eval_mergeBy, reducedMergeEval669 B hB hF, reducedMergeEval683 B hB hF]
  rw [originalMerge684, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval685 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge685 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge685 (originalVector B) := by
  rw [reducedMerge685Check, Integer.Sparse.eval_mergeBy, reducedTermEval690 B hB hF, reducedTermEval691 B hB hF]
  rw [originalMerge685, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval686 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge686 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge686 (originalVector B) := by
  rw [reducedMerge686Check, Integer.Sparse.eval_mergeBy, reducedTermEval689 B hB hF, reducedMergeEval685 B hB hF]
  rw [originalMerge686, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval687 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge687 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge687 (originalVector B) := by
  rw [reducedMerge687Check, Integer.Sparse.eval_mergeBy, reducedTermEval692 B hB hF, reducedTermEval693 B hB hF]
  rw [originalMerge687, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval688 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge688 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge688 (originalVector B) := by
  rw [reducedMerge688Check, Integer.Sparse.eval_mergeBy, reducedTermEval694 B hB hF, reducedTermEval695 B hB hF]
  rw [originalMerge688, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval689 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge689 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge689 (originalVector B) := by
  rw [reducedMerge689Check, Integer.Sparse.eval_mergeBy, reducedMergeEval687 B hB hF, reducedMergeEval688 B hB hF]
  rw [originalMerge689, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval690 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge690 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge690 (originalVector B) := by
  rw [reducedMerge690Check, Integer.Sparse.eval_mergeBy, reducedMergeEval686 B hB hF, reducedMergeEval689 B hB hF]
  rw [originalMerge690, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval691 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge691 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge691 (originalVector B) := by
  rw [reducedMerge691Check, Integer.Sparse.eval_mergeBy, reducedTermEval696 B hB hF, reducedTermEval697 B hB hF]
  rw [originalMerge691, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval692 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge692 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge692 (originalVector B) := by
  rw [reducedMerge692Check, Integer.Sparse.eval_mergeBy, reducedTermEval698 B hB hF, reducedTermEval699 B hB hF]
  rw [originalMerge692, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval693 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge693 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge693 (originalVector B) := by
  rw [reducedMerge693Check, Integer.Sparse.eval_mergeBy, reducedMergeEval691 B hB hF, reducedMergeEval692 B hB hF]
  rw [originalMerge693, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval694 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge694 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge694 (originalVector B) := by
  rw [reducedMerge694Check, Integer.Sparse.eval_mergeBy, reducedTermEval700 B hB hF, reducedTermEval701 B hB hF]
  rw [originalMerge694, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval695 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge695 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge695 (originalVector B) := by
  rw [reducedMerge695Check, Integer.Sparse.eval_mergeBy, reducedTermEval702 B hB hF, reducedTermEval703 B hB hF]
  rw [originalMerge695, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval696 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge696 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge696 (originalVector B) := by
  rw [reducedMerge696Check, Integer.Sparse.eval_mergeBy, reducedMergeEval694 B hB hF, reducedMergeEval695 B hB hF]
  rw [originalMerge696, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval697 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge697 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge697 (originalVector B) := by
  rw [reducedMerge697Check, Integer.Sparse.eval_mergeBy, reducedMergeEval693 B hB hF, reducedMergeEval696 B hB hF]
  rw [originalMerge697, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval698 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge698 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge698 (originalVector B) := by
  rw [reducedMerge698Check, Integer.Sparse.eval_mergeBy, reducedMergeEval690 B hB hF, reducedMergeEval697 B hB hF]
  rw [originalMerge698, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval699 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge699 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge699 (originalVector B) := by
  rw [reducedMerge699Check, Integer.Sparse.eval_mergeBy, reducedTermEval705 B hB hF, reducedTermEval706 B hB hF]
  rw [originalMerge699, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval700 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge700 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge700 (originalVector B) := by
  rw [reducedMerge700Check, Integer.Sparse.eval_mergeBy, reducedTermEval704 B hB hF, reducedMergeEval699 B hB hF]
  rw [originalMerge700, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval701 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge701 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge701 (originalVector B) := by
  rw [reducedMerge701Check, Integer.Sparse.eval_mergeBy, reducedTermEval707 B hB hF, reducedTermEval708 B hB hF]
  rw [originalMerge701, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval702 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge702 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge702 (originalVector B) := by
  rw [reducedMerge702Check, Integer.Sparse.eval_mergeBy, reducedTermEval709 B hB hF, reducedTermEval710 B hB hF]
  rw [originalMerge702, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval703 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge703 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge703 (originalVector B) := by
  rw [reducedMerge703Check, Integer.Sparse.eval_mergeBy, reducedMergeEval701 B hB hF, reducedMergeEval702 B hB hF]
  rw [originalMerge703, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval704 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge704 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge704 (originalVector B) := by
  rw [reducedMerge704Check, Integer.Sparse.eval_mergeBy, reducedMergeEval700 B hB hF, reducedMergeEval703 B hB hF]
  rw [originalMerge704, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval705 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge705 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge705 (originalVector B) := by
  rw [reducedMerge705Check, Integer.Sparse.eval_mergeBy, reducedTermEval711 B hB hF, reducedTermEval712 B hB hF]
  rw [originalMerge705, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval706 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge706 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge706 (originalVector B) := by
  rw [reducedMerge706Check, Integer.Sparse.eval_mergeBy, reducedTermEval713 B hB hF, reducedTermEval714 B hB hF]
  rw [originalMerge706, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval707 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge707 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge707 (originalVector B) := by
  rw [reducedMerge707Check, Integer.Sparse.eval_mergeBy, reducedMergeEval705 B hB hF, reducedMergeEval706 B hB hF]
  rw [originalMerge707, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval708 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge708 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge708 (originalVector B) := by
  rw [reducedMerge708Check, Integer.Sparse.eval_mergeBy, reducedTermEval715 B hB hF, reducedTermEval716 B hB hF]
  rw [originalMerge708, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval709 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge709 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge709 (originalVector B) := by
  rw [reducedMerge709Check, Integer.Sparse.eval_mergeBy, reducedTermEval717 B hB hF, reducedTermEval718 B hB hF]
  rw [originalMerge709, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval710 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge710 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge710 (originalVector B) := by
  rw [reducedMerge710Check, Integer.Sparse.eval_mergeBy, reducedMergeEval708 B hB hF, reducedMergeEval709 B hB hF]
  rw [originalMerge710, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval711 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge711 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge711 (originalVector B) := by
  rw [reducedMerge711Check, Integer.Sparse.eval_mergeBy, reducedMergeEval707 B hB hF, reducedMergeEval710 B hB hF]
  rw [originalMerge711, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval712 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge712 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge712 (originalVector B) := by
  rw [reducedMerge712Check, Integer.Sparse.eval_mergeBy, reducedMergeEval704 B hB hF, reducedMergeEval711 B hB hF]
  rw [originalMerge712, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval713 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge713 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge713 (originalVector B) := by
  rw [reducedMerge713Check, Integer.Sparse.eval_mergeBy, reducedMergeEval698 B hB hF, reducedMergeEval712 B hB hF]
  rw [originalMerge713, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval714 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge714 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge714 (originalVector B) := by
  rw [reducedMerge714Check, Integer.Sparse.eval_mergeBy, reducedMergeEval684 B hB hF, reducedMergeEval713 B hB hF]
  rw [originalMerge714, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval715 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge715 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge715 (originalVector B) := by
  rw [reducedMerge715Check, Integer.Sparse.eval_mergeBy, reducedMergeEval655 B hB hF, reducedMergeEval714 B hB hF]
  rw [originalMerge715, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval716_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge716 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge716 (originalVector B) := by
  rw [reducedMerge716Check, Integer.Sparse.eval_mergeBy, reducedMergeEval596 B hB hF, reducedMergeEval715 B hB hF]
  rw [originalMerge716, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval716_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval716_e_oai
