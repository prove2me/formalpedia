-- Prove2me | solution 1 for GlobalTheory.UnitLemma.InvAlg.isIntegral_mk_comap_sigma_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:20:19.71596+00:00
-- url     : https://prove2.me/submissions/70f1ae9e-fcd8-4e09-bc9a-821f9a70437d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralResidueComapInvolutionIff
import Theorems.Thm_GlobalTheory_UnitLemma_SwapInt_isIntegral_map_semilinear
import Theorems.Thm_GlobalTheory_UnitLemma_SwapInt_sigma_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory.UnitLemma.SwapInt
namespace GlobalTheory.UnitLemma.InvAlg
theorem _root_.solution :
    ∀ (K : UQ) (B : InvAlg K) (m : MaximalSpectrum B.A) (x : B.A),
      IsIntegral K.O (Ideal.Quotient.mk (m.asIdeal.comap B.σ) x) ↔
        IsIntegral K.O (Ideal.Quotient.mk m.asIdeal (B.σ x)) := by
  intro K B m x
  let σr : B.A →+* B.A := B.σ
  let ψ := Ideal.quotientMap m.asIdeal σr (le_refl (m.asIdeal.comap σr))
  have hm : m.asIdeal ≤ (m.asIdeal.comap σr).comap σr := by
    intro y hy
    simp only [Ideal.mem_comap]
    show B.σ (B.σ y) ∈ m.asIdeal
    rw [B.σ_σ]; exact hy
  let φ := Ideal.quotientMap (m.asIdeal.comap σr) σr hm
  have key : ∀ o : K.O, σr (algebraMap K.O B.A o) = algebraMap K.O B.A (conjO K o) :=
    sigma_algebraMap B
  constructor
  · intro h
    have h' : IsIntegral K.O (Ideal.Quotient.mk (m.asIdeal.comap σr) x) := h
    have := isIntegral_map_semilinear (conjO K) ψ (fun o => by
      rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap]
      simp only [ψ]
      rw [Ideal.quotientMap_mk, key]) h'
    have e2 : ψ (Ideal.Quotient.mk (m.asIdeal.comap σr) x) = Ideal.Quotient.mk m.asIdeal (σr x) :=
      Ideal.quotientMap_mk
    rw [e2] at this
    exact this
  · intro h
    have h' : IsIntegral K.O (Ideal.Quotient.mk m.asIdeal (σr x)) := h
    have := isIntegral_map_semilinear (conjO K) φ (fun o => by
      rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap]
      simp only [φ]
      rw [Ideal.quotientMap_mk, key]) h'
    have e2 : φ (Ideal.Quotient.mk m.asIdeal (σr x)) = Ideal.Quotient.mk (m.asIdeal.comap σr) (σr (σr x)) :=
      Ideal.quotientMap_mk
    have e : σr (σr x) = x := B.σ_σ x
    rw [e2, e] at this
    exact this
end GlobalTheory.UnitLemma.InvAlg
