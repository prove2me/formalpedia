-- Prove2me | solution 1 for GroundTheory.Global.SemiLocal.ramificationIdx_mul_inertiaDeg_le_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:52:54.640411+00:00
-- url     : https://prove2.me/submissions/ad460da8-7d31-40b0-a136-02b1b6f763cb

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_LocalDegree
import Theorems.Thm_GroundTheory_Global_SemiLocal_linearIndependent_uniformizer_pow_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField WithZero
noncomputable section
open GroundTheory.Global.SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]
variable {ι : Type*} [Fintype ι]
namespace GroundTheory.Global.SemiLocal
theorem _root_.solution :
    w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) ≤
      Module.finrank (v.adicCompletion K) (w.adicCompletion L) := by
  have := v.isMaximal
  have := w.isMaximal
  let := Ideal.Quotient.field v.asIdeal
  rw [Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal w.asIdeal]
  let b := Module.finBasis (𝓞 K ⧸ v.asIdeal) (𝓞 L ⧸ w.asIdeal)
  choose ω hω using fun j ↦ Ideal.Quotient.mk_surjective (b j)
  have hli : LinearIndependent (𝓞 K ⧸ v.asIdeal) (fun j ↦ Ideal.Quotient.mk w.asIdeal (ω j)) := by
    convert b.linearIndependent with j
    exact hω j
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer L
  have := (linearIndependent_uniformizer_pow_mul v w ω hli π hπ).fintype_card_le_finrank
  simpa using this
end GroundTheory.Global.SemiLocal
