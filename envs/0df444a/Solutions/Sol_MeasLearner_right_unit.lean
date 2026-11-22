-- Prove2me | solution 1 for MeasLearner.right_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:46:15.780777+00:00
-- url     : https://prove2.me/submissions/9bc78473-9b78-4a42-bb24-413e80d20116

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
    (L : MeasLearner X)
    (sel : {m : ℕ} → (Fin m → X × Bool) → ℕ)
    {m : ℕ} (S : Fin m → X × Bool) (x : X) :
    (concatLearner (fun _ => L.learner) sel).learn S x =
    L.learner.learn S x := by rfl
end MeasLearner
