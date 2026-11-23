-- Prove2me | solution 1 for GlobalTheory.NormCompat.NormCont.exists_exp_le_intValuation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:22:53.144692+00:00
-- url     : https://prove2.me/submissions/c142c90d-5ad1-4008-a1b8-2a97c02c0828

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormCloseToOneOfCloseAbovePlace

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
open GlobalTheory GlobalTheory.NormCompat GlobalTheory.NormCompat.NormCont
namespace GlobalTheory.NormCompat.NormCont
theorem _root_.solution {R : Type} [CommRing R] [IsDedekindDomain R] {x : R} (hx : x ≠ 0) :
    ∃ k : ℕ, ∀ w : HeightOneSpectrum R, WithZero.exp (-(k : ℤ)) ≤ w.intValuation x := by
  classical
  have hI : Ideal.span {x} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hx
  set F := (Ideal.finite_factors hI).toFinset
  refine ⟨F.sup fun w => (w.intValuation x).log.natAbs, fun w => ?_⟩
  by_cases hw : w ∈ F
  · have h0 := w.intValuation_ne_zero x hx
    have hle : (w.intValuation x).log.natAbs ≤ F.sup fun w => (w.intValuation x).log.natAbs :=
      Finset.le_sup (f := fun w => (w.intValuation x).log.natAbs) hw
    calc WithZero.exp (-((F.sup fun w => (w.intValuation x).log.natAbs : ℕ) : ℤ))
        ≤ WithZero.exp ((w.intValuation x).log) := by
          rw [WithZero.exp_le_exp]; omega
      _ = w.intValuation x := WithZero.exp_log h0
  · have h1 : w.intValuation x = 1 := by
      refine le_antisymm (w.intValuation_le_one x) (not_lt.1 fun h => hw ?_)
      rw [Set.Finite.mem_toFinset]
      exact (w.intValuation_lt_one_iff_dvd x).1 h
    rw [h1, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
end GlobalTheory.NormCompat.NormCont
