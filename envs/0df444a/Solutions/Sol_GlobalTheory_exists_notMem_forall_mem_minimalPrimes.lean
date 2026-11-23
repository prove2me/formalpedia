-- Prove2me | solution 1 for GlobalTheory.exists_notMem_forall_mem_minimalPrimes
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:48:10.887409+00:00
-- url     : https://prove2.me/submissions/fe1d14f1-ac63-49c1-a4e1-6d664a472069

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringLiftOfSpecialFibre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
universe u
namespace GlobalTheory
theorem _root_.solution {B : Type*} [CommRing B] [IsNoetherianRing B]
    (I p : Ideal B) [p.IsPrime] (hp : ∀ P ∈ I.minimalPrimes, P ≤ p → P = p) :
    ∃ s ∉ p, ∀ P ∈ I.minimalPrimes, P ≠ p → s ∈ P := by
  classical
  have hfin : (I.minimalPrimes \ {p}).Finite :=
    I.finite_minimalPrimes_of_isNoetherianRing.subset Set.sdiff_subset
  have : ¬ hfin.toFinset.inf id ≤ p := by
    rw [Ideal.IsPrime.inf_le' inferInstance]
    rintro ⟨P, hP, hle⟩
    rw [Set.Finite.mem_toFinset] at hP
    exact hP.2 (hp P hP.1 hle)
  obtain ⟨s, hs, hsp⟩ := SetLike.not_le_iff_exists.mp this
  refine ⟨s, hsp, fun P hP hne => ?_⟩
  exact (Finset.inf_le (f := id) (hfin.mem_toFinset.mpr ⟨hP, hne⟩) : _ ≤ P) hs
end GlobalTheory
