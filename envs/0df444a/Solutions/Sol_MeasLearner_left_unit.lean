-- Prove2me | solution 1 for MeasLearner.left_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:46:13.901664+00:00
-- url     : https://prove2.me/submissions/e645771f-3512-48eb-b30d-5b43b83cade9

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
    (n : ℕ) {m : ℕ} (S : Fin m → X × Bool) (x : X) :
    (concatLearner (fun i => (family i).learner) (fun _ => n)).learn S x =
    (family n).learner.learn S x := by rfl
end MeasLearner
