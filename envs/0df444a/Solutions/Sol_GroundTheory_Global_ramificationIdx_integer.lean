-- Prove2me | solution 1 for GroundTheory.Global.ramificationIdx_integer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:17:20.882232+00:00
-- url     : https://prove2.me/submissions/73aa5f39-10d3-483d-9094-d0afed0f95ce

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Theorems.Thm_GroundTheory_Global_valued_of_irreducible_integer
import Theorems.Thm_GroundTheory_Global_mem_maximalIdeal_pow_iff
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk



set_option autoImplicit false
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel
open scoped WithZero
open GroundTheory GroundTheory.Global
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]
namespace GroundTheory.Global
theorem _root_.solution :
    𝓂[w.adicCompletion L].ramificationIdx 𝒪[v.adicCompletion K] =
      w.asIdeal.ramificationIdx (𝓞 K) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[v.adicCompletion K]
  have key : ∀ n : ℕ, Ideal.map (algebraMap 𝒪[v.adicCompletion K] 𝒪[w.adicCompletion L])
      𝓂[v.adicCompletion K] ≤ 𝓂[w.adicCompletion L] ^ n ↔
        n ≤ v.asIdeal.ramificationIdx' w.asIdeal := by
    intro n
    rw [hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem,
      mem_maximalIdeal_pow_iff, GroundTheory.LocalField.coe_algebraMap_integer,
      valued_algebraMap_adicCompletion', valued_of_irreducible_integer v hϖ,
      ← WithZero.exp_nsmul, WithZero.exp_le_exp]
    simp only [smul_neg, nsmul_eq_mul, mul_one, neg_le_neg_iff, Nat.cast_le]
  have h := Ideal.ramificationIdx'_spec ((key _).2 le_rfl)
    (fun h ↦ by simpa using (key _).1 h)
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx 𝓂[v.adicCompletion K] 𝓂[w.adicCompletion L]
    (IsDiscreteValuationRing.not_a_field _), h,
    Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot]
end GroundTheory.Global
