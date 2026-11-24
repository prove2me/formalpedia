-- Prove2me | solution 1 for GlobalTheory.CyclicNormCheck.norm_of_root
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:51:08.004193+00:00
-- url     : https://prove2.me/submissions/84ef0453-038b-4a3c-9199-bbb928dacc7e

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_CyclicNormPrinciple
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AdelicSplittingExamples_LocalConditionsOfGlobal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct
open GlobalTheory GlobalTheory.CyclicNormCheck
namespace GlobalTheory.CyclicNormCheck
theorem _root_.solution {F E K : Type} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K]
    [Module.Finite F E] {a r : K} (h : r ^ Module.finrank F E = a) :
    ∃ y : K ⊗[F] E, Algebra.norm K y = a :=
  ⟨algebraMap K _ r, by rw [Algebra.norm_algebraMap, Module.finrank_baseChange, h]⟩
end GlobalTheory.CyclicNormCheck
