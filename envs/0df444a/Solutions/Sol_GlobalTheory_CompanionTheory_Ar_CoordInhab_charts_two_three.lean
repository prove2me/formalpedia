-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CoordInhab.charts_two_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:36:41.426458+00:00
-- url     : https://prove2.me/submissions/60acbb2f-0d60-48eb-a493-73455b7333ab

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_StalkClosedPointToToStalk
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordInhab_genPt_specializes
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordInhab_inChart_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordInhab_span_two_three

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
open AlgebraicGeometry CategoryTheory CptModel
open CoordInhab
open GlobalTheory.CompanionTheory.Ar.CoordInhab
namespace GlobalTheory.CompanionTheory.Ar.CoordInhab
theorem _root_.solution (c : Fin 2) :
    (∃ p, InChart (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))
      (fun j => algebraMap ℤ ℚ ((![2, 3] : Fin 2 → ℤ) j)) c p) ∧
    ∃ p, ¬ InChart (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))
      (fun j => algebraMap ℤ ℚ ((![2, 3] : Fin 2 → ℤ) j)) c p := by
  constructor
  · refine ⟨CptModel.self _, (inChart_iff _ span_two_three c _).2 ?_⟩
    intro hmem
    change _ ∈ (genPt (pt (algebraMap ℤ ℚ))).asIdeal at hmem
    rw [genPt_asIdeal, RingHom.mem_ker] at hmem
    fin_cases c <;> simp at hmem
  · fin_cases c
    · refine ⟨CptModel.two, fun hc => ?_⟩
      apply (inChart_iff _ span_two_three _ _).1 hc
      show _ ∈ Ideal.span {(2 : ℤ)}
      exact Ideal.subset_span (by simp)
    · refine ⟨⟨(⟨Ideal.span {3}, (Ideal.span_singleton_prime (by norm_num)).2 Int.prime_three⟩ :
          PrimeSpectrum ℤ), genPt_specializes _⟩, fun hc => ?_⟩
      apply (inChart_iff _ span_two_three _ _).1 hc
      show _ ∈ Ideal.span {(3 : ℤ)}
      exact Ideal.subset_span (by simp)
end GlobalTheory.CompanionTheory.Ar.CoordInhab
