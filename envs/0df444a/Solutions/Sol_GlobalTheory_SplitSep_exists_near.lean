-- Prove2me | solution 1 for GlobalTheory.SplitSep.exists_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:55:50.455854+00:00
-- url     : https://prove2.me/submissions/3849168d-a8d7-4e55-8b13-9fd6a61720e0

import Mathlib
import Definitions.Def_ReciprocityTheory_Automorphisms_Unitary
import Definitions.Def_ReciprocityTheory_Automorphisms_PlaceA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsIntegerUnitSplitPlaceConjugatePrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial
noncomputable section
open GlobalTheory GlobalTheory.SplitSep
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
local notation3 "L⁺" => NumberField.maximalRealSubfield L
local notation3 "cc" => IsCMField.complexConj L
namespace GlobalTheory.SplitSep
theorem _root_.solution (v : HeightOneSpectrum (𝓞 L⁺))
    (f : v.adicCompletion L⁺ → v.adicCompletion L⁺) (hf : Continuous f)
    (y₀ : v.adicCompletion L⁺) (hy₀ : Valued.v (f y₀) < 1) :
    ∃ a : L⁺, Valued.v (f (algebraMap L⁺ (v.adicCompletion L⁺) a)) < 1 := by
  have hU : IsOpen {z : v.adicCompletion L⁺ | Valued.v (f z) < 1} := by
    have h := (Valued.isOpen_ball (v.adicCompletion L⁺) 1).preimage hf
    convert h using 2 with z
    simp [Valuation.restrict_lt_iff_lt_embedding]
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 L⁺) (K := L⁺) v).exists_mem_open
    hU ⟨y₀, hy₀⟩
  exact ⟨k, hk⟩
end GlobalTheory.SplitSep
