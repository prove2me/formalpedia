-- Prove2me | solution 1 for GlobalTheory.DedekindSmooth.smooth_of_isDedekindDomain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:44:28.160557+00:00
-- url     : https://prove2.me/submissions/18edeb7f-31bb-4565-a9f4-b2a43c7d92f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SmoothOfIsDedekindDomain
import Theorems.Thm_GlobalTheory_DedekindSmooth_isSmoothAt_bot
import Theorems.Thm_GlobalTheory_DedekindSmooth_isSmoothAt_of_ne_bot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DedekindSmooth
open Polynomial IsLocalRing
namespace GlobalTheory.DedekindSmooth
theorem _root_.solution :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B] [IsDedekindDomain B]
      [Algebra k B] [Algebra.FiniteType k B], Algebra.Smooth k B := by
  intro k _ _ B _ _ _ _
  have : Algebra.FinitePresentation k B :=
    (Algebra.FinitePresentation.of_finiteType (R := k) (A := B)).mp ‹_›
  refine ⟨Algebra.smoothLocus_eq_univ_iff.mp (Set.eq_univ_iff_forall.mpr fun q => ?_), ‹_›⟩
  obtain ⟨q, hq⟩ := q
  by_cases h : q = ⊥
  · subst h
    exact isSmoothAt_bot k B
  · exact isSmoothAt_of_ne_bot k B q h
end GlobalTheory.DedekindSmooth
