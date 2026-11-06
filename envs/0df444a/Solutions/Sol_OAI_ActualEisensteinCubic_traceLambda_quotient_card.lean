-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.traceLambda_quotient_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:17:05.41923+00:00
-- url     : https://prove2.me/submissions/f23df383-29a3-41e1-9bbb-e93d9546ee6d

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_LocalProductAssembly
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RamifiedTracePhase
section
namespace OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
namespace TraceLambdaPhase
open EisensteinEmbedding ConcreteTraceCRT Complex
open scoped ComplexConjugate
end TraceLambdaPhase
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE TraceLambdaPhase
private theorem traceLambda_span_eq_lambda :
    Ideal.span {traceLambda} = Ideal.span {lambda} := by
  rw [traceLambda_eq_unit_mul_lambda]
  exact Ideal.span_singleton_mul_left_unit neg_omega_isUnit lambda
end ActualEisensteinCubic
namespace PoissonFirstLocal
open scoped Classical
end PoissonFirstLocal
namespace ActualEisensteinCubic
section
open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE TraceLambdaPhase
end
end ActualEisensteinCubic
namespace AnalyticBridge
end AnalyticBridge
namespace ShortDraftCusp
variable {R : Type*} [CommRing R]
end ShortDraftCusp
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
end ActualEisensteinCubic
end
end OAI
end

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open OAI.ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE TraceLambdaPhase
namespace OAI.ActualEisensteinCubic
theorem _root_.solution :
    Nat.card (O ⧸ Ideal.span {traceLambda}) = 3 := by
  rw [traceLambda_span_eq_lambda]
  exact ActualEisensteinSieve.lambda_card
end OAI.ActualEisensteinCubic
