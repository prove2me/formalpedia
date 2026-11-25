-- Prove2me | solution 1 for GroundTheory.Global.forall_valued_trace_le_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:09:53.224338+00:00
-- url     : https://prove2.me/submissions/b055c7ea-09da-4402-a6e0-bfaa7c04f6dd

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminant
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_NormTrace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Definitions.Def_GroundTheory_LocalFields_Different
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminantLocal
import Theorems.Thm_GroundTheory_Global_mem_inv_maximalIdeal_pow_iff
import Theorems.Thm_GroundTheory_Global_integers_valued
import Theorems.Thm_GroundTheory_Global_mem_valuationInteger_iff
import Theorems.Thm_GroundTheory_LocalField_differentIdeal_eq_maximalIdeal_pow
import Theorems.Thm_GroundTheory_LocalField_maximalIdeal_pow_dvd_pow_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel GroundTheory.LocalField
open scoped WithZero
open GroundTheory GroundTheory.Global
variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 M)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion M)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion M)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion M)]
namespace GroundTheory.Global
theorem _root_.solution (n : ℕ) :
    (∀ y : w.adicCompletion M, Valued.v y ≤ WithZero.exp (n : ℤ) →
      Valued.v (Algebra.trace (v.adicCompletion K) (w.adicCompletion M) y) ≤ 1) ↔
      n ≤ differentExponent (v.adicCompletion K) (w.adicCompletion M) := by
  have hI : (𝓂[w.adicCompletion M] ^ n) ≠ ⊥ :=
    pow_ne_zero _ (IsDiscreteValuationRing.not_a_field _)
  rw [← maximalIdeal_pow_dvd_pow_iff (R := 𝒪[w.adicCompletion M]),
    ← differentIdeal_eq_maximalIdeal_pow, Ideal.dvd_iff_le,
    differentialIdeal_le_iff (K := v.adicCompletion K) (L := w.adicCompletion M) hI,
    Submodule.map_le_iff_le_comap]
  constructor
  · intro h y hy
    have hy' := h y ((mem_inv_maximalIdeal_pow_iff w n y).1 hy)
    rw [Submodule.mem_comap]
    exact Submodule.mem_one.2 ⟨⟨_, (mem_valuationInteger_iff v _).2 hy'⟩, rfl⟩
  · intro h y hy
    obtain ⟨a, ha⟩ := Submodule.mem_one.1 (Submodule.mem_comap.1
      (h ((mem_inv_maximalIdeal_pow_iff w n y).2 hy)))
    change (a : v.adicCompletion K) = Algebra.trace (v.adicCompletion K) (w.adicCompletion M) y
      at ha
    rw [← ha]
    exact (integers_valued v).map_le_one a
end GroundTheory.Global
