-- Prove2me | solution 1 for GlobalTheory.SplitWeil.isSelfDual_iff_vol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:23:37.583382+00:00
-- url     : https://prove2.me/submissions/19c4c28a-a074-4d0a-b0ae-f8177a1a6f85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsSelfDualOfHasConductor
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_isLocallyConstant
import Theorems.Thm_GlobalTheory_SplitWeil_fourier_inversion
import Theorems.Thm_GlobalTheory_SplitWeil_isCompact_int
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_int
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} {c : kˣ}
namespace GlobalTheory.SplitWeil
theorem _root_.solution (h : HasConductor ψ c) (ν : Measure k) [ν.IsAddHaarMeasure] :
    IsSelfDual ψ ν ↔ (ν (𝒪[k] : Set k)).toReal ^ 2 * nabs k c = 1 := by
  have := t2Space k
  have hcl : IsClosed (𝒪[k] : Set k) := (isCompact_int k).isClosed
  have hclo : IsClopen (𝒪[k] : Set k) := ⟨hcl, isOpen_int k⟩
  set f : k → ℂ := (𝒪[k] : Set k).indicator 1 with hf
  have hfSB : f ∈ SB k := by
    refine ⟨?_, ?_⟩
    · have hlc := (LocallyConstant.charFn ℂ hclo).isLocallyConstant
      exact hlc
    · exact HasCompactSupport.intro' (isCompact_int k) hcl fun x hx => by simp [f, hx]
  have hf0 : f 0 = 1 := by simp [f]
  have hvol : ν.real (𝒪[k] : Set k) = (ν (𝒪[k] : Set k)).toReal := measureReal_def ν _
  constructor
  · rintro ⟨-, hsd⟩
    have e := (fourier_inversion ν h hfSB).symm.trans (hsd f hfSB)
    rw [hf0, mul_one] at e
    rw [← hvol]
    exact_mod_cast e
  · intro hC
    refine ⟨inferInstance, fun g hg => ?_⟩
    rw [fourier_inversion ν h hg, hvol, hC]
    simp
end GlobalTheory.SplitWeil
