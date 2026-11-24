-- Prove2me | solution 1 for GlobalTheory.CoprimeBasis.isCoprime_of_mem_primeTo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:58:38.279941+00:00
-- url     : https://prove2.me/submissions/1f162635-fbaa-4ad7-a6cb-3f4f8b5952eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemLocDIffSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIndependentBasisCoprime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.CoprimeBasis
namespace GlobalTheory.CoprimeBasis
theorem _root_.solution {R : Type} [CommRing R] {s d : R}
    (hs : s ∈ GlobalTheory.Mass.primeTo d) : IsCoprime s d := by
  by_cases hI : Ideal.span {s, d} = ⊤
  · obtain ⟨a, b, h⟩ := Ideal.mem_span_pair.1 ((Ideal.eq_top_iff_one _).1 hI)
    exact ⟨a, b, h⟩
  · obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hI
    exact absurd (hle (Ideal.subset_span (by simp))) (hs P hP (hle (Ideal.subset_span (by simp))))
end GlobalTheory.CoprimeBasis
