-- Prove2me | solution 1 for GroundTheory.Global.ramificationIdx_mul_inertiaDeg_integer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:16:19.860306+00:00
-- url     : https://prove2.me/submissions/e980a88c-061c-4e2c-8ea9-4e37aac9b137

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Theorems.Thm_GroundTheory_Global_finite_integer
import Theorems.Thm_GroundTheory_Global_free_integer
import Theorems.Thm_GroundTheory_Global_finrank_integer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
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
    𝓂[w.adicCompletion L].ramificationIdx 𝒪[v.adicCompletion K] *
        𝓂[w.adicCompletion L].inertiaDeg 𝒪[v.adicCompletion K] =
      Module.finrank (v.adicCompletion K) (w.adicCompletion L) := by
  have := finite_integer v w
  have := free_integer v w
  have hp0 : 𝓂[v.adicCompletion K] ≠ ⊥ := IsDiscreteValuationRing.not_a_field _
  have hset := IsLocalRing.primesOver_eq 𝒪[w.adicCompletion L] hp0
  have hmem : 𝓂[w.adicCompletion L] ∈ 𝓂[v.adicCompletion K].primesOver 𝒪[w.adicCompletion L] := by
    rw [hset]; rfl
  let : Unique (𝓂[v.adicCompletion K].primesOver 𝒪[w.adicCompletion L]) :=
    { default := ⟨_, hmem⟩
      uniq := fun q ↦ Subtype.ext ((Set.ext_iff.1 hset q).1 q.2) }
  have h := Ideal.sum_ramification_inertia_eq_finrank 𝓂[v.adicCompletion K] 𝒪[w.adicCompletion L]
  rw [Fintype.sum_unique, finrank_integer] at h
  exact h
end GroundTheory.Global
