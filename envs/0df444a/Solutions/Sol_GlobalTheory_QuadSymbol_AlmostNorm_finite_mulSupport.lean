-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.AlmostNorm.finite_mulSupport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:45:01.963801+00:00
-- url     : https://prove2.me/submissions/b17911e3-e19d-4617-a419-7456421381af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Theorems.Thm_GlobalTheory_QuadSymbol_eta_eq_one_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open GlobalTheory GlobalTheory.QuadSymbol
variable (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
open NumberField IsDedekindDomain
open scoped TensorProduct
variable (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
namespace GlobalTheory.QuadSymbol
namespace _root_.GlobalTheory.QuadSymbol.AlmostNorm
theorem _root_.solution
    {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L]
    {x : _root_.GlobalTheory.QuadSymbol.FinFam K} (h : _root_.GlobalTheory.QuadSymbol.AlmostNorm K L x) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) =>
      _root_.GlobalTheory.QuadSymbol.eta K L (v.adicCompletion K) (x v)).Finite := by
  refine h.subset fun v hv => ?_
  simp only [Function.mem_mulSupport] at hv
  exact fun hmem => hv (_root_.GlobalTheory.QuadSymbol.eta_eq_one_iff.mpr hmem)
end _root_.GlobalTheory.QuadSymbol.AlmostNorm
end GlobalTheory.QuadSymbol
