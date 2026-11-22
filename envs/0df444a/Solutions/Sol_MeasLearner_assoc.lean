-- Prove2me | solution 1 for MeasLearner.assoc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:46:18.778691+00:00
-- url     : https://prove2.me/submissions/e7cd61a7-0383-4e32-a216-dc1647e3731d

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Closure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Monad

set_option autoImplicit true
@[expose] public section
public section
universe u
namespace MeasLearner
theorem _root_.solution
    {X : Type u} [MeasurableSpace X]
    (family : ℕ → MeasLearner X)
    [_hfam : UniformMeasurableBatchFamily (fun n => (family n).learner)]
    (sel : {m : ℕ} → (Fin m → X × Bool) → ℕ)
    {m : ℕ} (S : Fin m → X × Bool) (x : X) :
    (concatLearner (fun n => (family n).learner) sel).learn S x =
    (family (sel S)).learner.learn S x := by rfl
end MeasLearner
