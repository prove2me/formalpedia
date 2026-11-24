-- Prove2me | solution 1 for GlobalTheory.InertiaAlmostAll.finite_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:11:34.092021+00:00
-- url     : https://prove2.me/submissions/7e69633b-ee47-4d3f-9cfd-4658c466a3e2

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinitePlacesInertiaNotFixingFiniteExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.InertiaAlmostAll
namespace GlobalTheory.InertiaAlmostAll
theorem _root_.solution (F : Type) [Field F] [NumberField F] {c : ℤ} (hc : c ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) | (c : 𝓞 F) ∈ v.asIdeal}.Finite := by
  have h : Ideal.span {(c : 𝓞 F)} ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using hc
  refine (Ideal.finite_factors h).subset fun v hv => ?_
  simpa [Ideal.dvd_span_singleton] using hv
end GlobalTheory.InertiaAlmostAll
