-- Prove2me | solution 1 for OAI.SevenEighths.ProbeGauss.frequencyGauss_eq_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:10:19.390205+00:00
-- url     : https://prove2.me/submissions/d4ec9d44-7d1a-4e84-a904-c5c7c98d864d

import Mathlib.NumberTheory.GaussSum
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_Gauss

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.ProbeGauss
open scoped BigOperators Classical
noncomputable section
namespace OAI.SevenEighths.ProbeGauss
theorem _root_.solution {F : Type*} [Field F] [Fintype F]
    (ξ : MulChar F ℂ) (ψ : AddChar F ℂ) (h : F) :
    frequencyGauss ξ ψ h = gaussSum ξ (ψ.mulShift h) := rfl
end OAI.SevenEighths.ProbeGauss
