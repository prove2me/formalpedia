-- Prove2me | solution 1 for GlobalTheory.SpanInfEq.span_inf_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:14:40.541416+00:00
-- url     : https://prove2.me/submissions/2e8c0b85-6b43-4185-8be6-1fe9a94f3787

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanInfEq
import Theorems.Thm_GlobalTheory_SpanInfEq_exists_smul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SpanInfEq
open NumberField
namespace GlobalTheory.SpanInfEq
theorem _root_.solution {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V]
    [Module K V] [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]
    (L : Submodule (RingOfIntegers K) V) (hL : Submodule.IsLattice K L) (T : Submodule K V) :
    Submodule.span K (↑(L ⊓ Submodule.restrictScalars (RingOfIntegers K) T) : Set V) = T := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact (Submodule.mem_inf.mp hx).2
  · intro v hv
    obtain ⟨d, hd, h⟩ := exists_smul_mem L hL v
    have hd' : algebraMap (RingOfIntegers K) K d ≠ 0 := by
      intro h0
      exact hd ((map_eq_zero_iff _ (IsFractionRing.injective (RingOfIntegers K) K)).mp h0)
    have hdT : d • v ∈ Submodule.restrictScalars (RingOfIntegers K) T := by
      rw [← algebraMap_smul K d v]
      exact T.smul_mem _ hv
    have hmem : d • v ∈ L ⊓ Submodule.restrictScalars (RingOfIntegers K) T :=
      Submodule.mem_inf.mpr ⟨h, hdT⟩
    have : v = (algebraMap (RingOfIntegers K) K d)⁻¹ • (d • v) := by
      rw [← algebraMap_smul K d v, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
end GlobalTheory.SpanInfEq
