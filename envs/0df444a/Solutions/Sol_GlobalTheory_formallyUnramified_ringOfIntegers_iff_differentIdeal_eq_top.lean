-- Prove2me | solution 1 for GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:42.192086+00:00
-- url     : https://prove2.me/submissions/15223dca-5f7a-4896-a304-07ec207f5b53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FormallyUnramifiedRingOfIntegersIffDifferentIdea

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory
open NumberField
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution (F E : Type) [Field F]
    [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Algebra.FormallyUnramified (𝓞 F) (𝓞 E) ↔ differentIdeal (𝓞 F) (𝓞 E) = ⊤ := by
  rw [← Algebra.unramifiedLocus_eq_univ_iff, Set.eq_univ_iff_forall]
  constructor
  · intro h
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    exact (dvd_differentIdeal_iff (P := M)).1 (Ideal.dvd_iff_le.2 hle) (h ⟨M, hM.isPrime⟩)
  · intro h P
    show Algebra.IsUnramifiedAt _ P.asIdeal
    rw [← not_dvd_differentIdeal_iff, h, Ideal.dvd_iff_le, top_le_iff]
    exact P.isPrime.ne_top
end _root_.GlobalTheory
end GlobalTheory
