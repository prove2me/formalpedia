-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.eventually_codiscrete_ne_zero_of_nhdsNE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:37.433463+00:00
-- url     : https://prove2.me/submissions/0792fc37-db22-4865-9612-ae5974f2a561

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set Polynomial
open scoped PeriodPair
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {L : PeriodPair}
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {F : ℂ → ℂ} (hF : Meromorphic F)
    (h : ∀ᶠ z in 𝓝[≠] (0 : ℂ), F z ≠ 0) : ∀ᶠ z in codiscrete ℂ, F z ≠ 0 := by
  have h0 : meromorphicOrderAt F 0 ≠ ⊤ :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hF 0)).2 h
  have hall : ∀ u ∈ (univ : Set ℂ), meromorphicOrderAt F u ≠ ⊤ := fun u _ ↦
    (hF.meromorphicOn (s := univ)).meromorphicOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (mem_univ 0) (mem_univ u) h0
  exact MeromorphicAt.MeromorphicOn.codiscreteWithin_setOfPred_ne_zero
    (hF.meromorphicOn (s := univ)) hall
end GroundTheory.Global.Elliptic
