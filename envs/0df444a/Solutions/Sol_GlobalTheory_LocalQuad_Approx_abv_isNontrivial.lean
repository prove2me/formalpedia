-- Prove2me | solution 1 for GlobalTheory.LocalQuad.Approx.abv_isNontrivial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:21:07.388718+00:00
-- url     : https://prove2.me/submissions/37fec4e7-48a4-4df8-be0b-07159d49f2a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsForallAbvSubLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open GlobalTheory GlobalTheory.LocalQuad GlobalTheory.LocalQuad.Approx
variable {F : Type} [Field F] [NumberField F]
open NumberField IsDedekindDomain
open scoped Matrix WithZero
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.LocalQuad.Approx
namespace _root_.GlobalTheory.LocalQuad.Approx
theorem _root_.solution (T : Finset (HeightOneSpectrum (𝓞 F)))
    (i : T ⊕ (F →+* ℝ)) : (_root_.GlobalTheory.LocalQuad.Approx.abv T i).IsNontrivial := by
  rcases i with v | σ
  · obtain ⟨r, hrv, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.1.ne_bot
    refine ⟨algebraMap (𝓞 F) F r, (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hr0, ?_⟩
    change NumberField.HeightOneSpectrum.adicAbv F v.1 _ ≠ 1
    rw [← FinitePlace.norm_embedding]
    exact ((FinitePlace.norm_lt_one_iff_mem F v.1 r).2 hrv).ne
  · exact (InfinitePlace.mk (Complex.ofRealHom.comp σ)).isNontrivial
end _root_.GlobalTheory.LocalQuad.Approx
end GlobalTheory.LocalQuad.Approx
