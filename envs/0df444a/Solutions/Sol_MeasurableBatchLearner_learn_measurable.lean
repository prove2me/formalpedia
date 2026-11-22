-- Prove2me | solution 1 for MeasurableBatchLearner.learn_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:45:49.874388+00:00
-- url     : https://prove2.me/submissions/c5938e5b-6a95-4833-944c-d4720c2218c4

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Core
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Data.EReal.Inv
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Properties

set_option autoImplicit true
@[expose] public section
public section
universe u v
namespace MeasurableBatchLearner
theorem _root_.solution
    {X : Type u} [MeasurableSpace X]
    (L : BatchLearner X Bool) [h : MeasurableBatchLearner X L]
    {m : ℕ} (S : Fin m → X × Bool) :
    Measurable (L.learn S) :=
  (h.eval_measurable m).comp (Measurable.prodMk measurable_const measurable_id)
end MeasurableBatchLearner
