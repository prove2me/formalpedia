-- Prove2me | solution 1 for OAI.BassTrace.RightProjective.bassTraceModules_vanishing_and_support
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T21:12:17.01577+00:00
-- url     : https://prove2.me/submissions/5c0b8bf1-be07-4810-ba5e-35478fdd49cb

import Mathlib
import Definitions.Def_BassTrace
import Definitions.Def_OAIQWBAS000
import Theorems.Thm_OAI_BassTrace_bassTrace

section
-- module Solutions.OAIQW_BassTrace.MatrixK0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section

namespace BassTrace.K0

section

open scoped Classical BigOperators

variable {G : Type*} [_root_.Group G]

lemma classTrace_apply (a : MonoidAlgebra ℂ G) (g : G) :
    classTrace a (ConjClasses.mk g)=classCoefficient g a := by
  unfold classTrace classCoefficient
  simp only [Finsupp.mapDomain,Finsupp.sum_apply,Finsupp.single_apply,
    ConjClasses.mk_eq_mk_iff_isConj]

lemma rawTrace_apply (z : FreeAbelianGroup (Idempotent (MonoidAlgebra ℂ G))) (g : G) :
    rawTrace z (ConjClasses.mk g)=rawCoefficient g z := by
  induction z using FreeAbelianGroup.induction_on with
  | zero => simp only [map_zero,Finsupp.zero_apply]
  | of e =>
    simp only [rawTrace,rawCoefficient,FreeAbelianGroup.lift_apply_of]
    exact classTrace_apply _ g
  | neg e he => simp only [map_neg,Finsupp.neg_apply,he]
  | add x y hx hy => simp only [map_add,Finsupp.add_apply,hx,hy]

lemma HattoriStallings_apply (x : Group (MonoidAlgebra ℂ G)) (g : G) :
    HattoriStallings x (ConjClasses.mk g)=hsCoefficient g x := by
  induction x using QuotientAddGroup.induction_on with | H z =>
    exact rawTrace_apply z g

end

open scoped Classical

theorem bassTraceK0 {G : Type*} [_root_.Group G]
    (x : Group (MonoidAlgebra ℂ G)) (g : G) (hg : ¬IsOfFinOrder g) :
    HattoriStallings x (ConjClasses.mk g)=0 := by
  rw [HattoriStallings_apply]
  induction x using QuotientAddGroup.induction_on with | H z =>
    change rawCoefficient g z=0
    induction z using FreeAbelianGroup.induction_on with
    | zero => exact map_zero _
    | of e =>
      simp only [rawCoefficient,FreeAbelianGroup.lift_apply_of]
      exact BassTrace.bassTrace e.matrix e.idem g hg
    | neg z hz => rw [map_neg,hz,neg_zero]
    | add z w hz hw => rw [map_add,hz,hw,add_zero]

theorem bassTraceK0_support {G : Type*} [_root_.Group G]
    (x : Group (MonoidAlgebra ℂ G)) :
    ↑(HattoriStallings x).support ⊆
      {c : ConjClasses G | ∃g : G,IsOfFinOrder g ∧ ConjClasses.mk g=c} := by
  intro c hc
  obtain ⟨g,rfl⟩ := ConjClasses.mk_surjective c
  refine ⟨g,?_,rfl⟩
  by_contra hg
  exact (Finsupp.mem_support_iff.mp hc) (bassTraceK0 x g hg)

end BassTrace.K0

end

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section

namespace BassTrace.RightProjective

universe u v

theorem bassTraceModules {G : Type u} [_root_.Group G]
    (x : ModuleK0.{u,v} (MonoidAlgebra ℂ G)) (g : G) (hg : ¬IsOfFinOrder g) :
    HattoriStallings x (ConjClasses.mk g)=0 :=
  K0.bassTraceK0 (presentation x) g hg

theorem bassTraceModules_support {G : Type u} [_root_.Group G]
    (x : ModuleK0.{u,v} (MonoidAlgebra ℂ G)) :
    ↑(HattoriStallings x).support ⊆ {c | ∃g : G,IsOfFinOrder g ∧ ConjClasses.mk g=c} :=
  K0.bassTraceK0_support (presentation x)

theorem bassTraceModules_vanishing_and_support_oai {G : Type u} [_root_.Group G]
    (x : ModuleK0.{u,v} (MonoidAlgebra ℂ G)) :
    (∀ g : G, ¬IsOfFinOrder g → HattoriStallings x (ConjClasses.mk g) = 0) ∧
      ↑(HattoriStallings x).support ⊆
        {c | ∃ g : G, IsOfFinOrder g ∧ ConjClasses.mk g = c} :=
  ⟨fun g hg => bassTraceModules x g hg, bassTraceModules_support x⟩

end BassTrace.RightProjective

end

end OAI
end

theorem solution.{u, v} : type_of% @OAI.BassTrace.RightProjective.bassTraceModules_vanishing_and_support_oai.{u, v} := @OAI.BassTrace.RightProjective.bassTraceModules_vanishing_and_support_oai.{u, v}
