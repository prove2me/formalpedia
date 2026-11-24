-- Prove2me | solution 1 for GlobalTheory.QSA.exists_nrm_one_re_sq_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:45:09.181592+00:00
-- url     : https://prove2.me/submissions/65a2b884-1466-4dd6-b762-14fd4cfb318d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsQuaternionNormOneNearReSqNeOne
import Theorems.Thm_GlobalTheory_QSA_nrm_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology
open Filter
open GlobalTheory GlobalTheory.QSA
namespace GlobalTheory.QSA
theorem _root_.solution : ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K], (2 : K) ≠ 0 → (𝓝[≠] (0 : K)).NeBot → ∀ a b : K, a ≠ 0 → ∀ g : ℍ[K, a, b], nrm g = 1 → ∀ W : Set ℍ[K, a, b], W ∈ 𝓝 g → ∃ g' : ℍ[K, a, b], nrm g' = 1 ∧ g'.re ^ 2 ≠ 1 ∧ W ∈ 𝓝 g' := by
  intro K _ _ _ _ h2 hne a b ha g hg W hW
  by_cases hre : g.re ^ 2 = 1
  swap
  · exact ⟨g, hg, hre, hW⟩
  have hs0 : g.re ≠ 0 := by
    intro h
    rw [h] at hre
    simp at hre
  let X0 : K → K := fun τ => (1 + a * τ ^ 2) / (1 - a * τ ^ 2)
  let X1 : K → K := fun τ => 2 * τ / (1 - a * τ ^ 2)
  let x : K → ℍ[K, a, b] := fun τ => ⟨X0 τ, X1 τ, 0, 0⟩
  have hD : Tendsto (fun τ : K => 1 - a * τ ^ 2) (𝓝 0) (𝓝 1) := by
    have : Continuous (fun τ : K => 1 - a * τ ^ 2) := by fun_prop
    simpa using this.tendsto 0
  have hx0 : Tendsto X0 (𝓝 0) (𝓝 1) := by
    have h1 : Continuous (fun τ : K => 1 + a * τ ^ 2) := by fun_prop
    have := (h1.tendsto 0).div hD one_ne_zero
    simpa [Pi.div_def] using this
  have hx1 : Tendsto X1 (𝓝 0) (𝓝 0) := by
    have h1 : Continuous (fun τ : K => 2 * τ) := by fun_prop
    have := (h1.tendsto 0).div hD one_ne_zero
    simpa [Pi.div_def] using this
  have key : ∀ c d : K, Tendsto (fun τ => c * X0 τ + d * X1 τ) (𝓝 0) (𝓝 c) := by
    intro c d
    simpa using (hx0.const_mul c).add (hx1.const_mul d)
  have hf : Tendsto (fun τ => g * x τ) (𝓝 0) (𝓝 g) := by
    rw [(Topology.IsInducing.induced coords).tendsto_nhds_iff, tendsto_pi_nhds]
    intro i
    fin_cases i
    · refine (key g.re (a * g.imI)).congr fun τ => ?_
      simp [coords, x]
    · refine (key g.imI g.re).congr fun τ => ?_
      simp [coords, x, add_comm]
    · refine (key g.imJ (-(a * g.imK))).congr fun τ => ?_
      simp [coords, x, sub_eq_add_neg]
    · refine (key g.imK (-g.imJ)).congr fun τ => ?_
      simp [coords, x, add_comm]
  have e1 : ∀ᶠ τ in 𝓝[≠] (0 : K), τ ≠ 0 := self_mem_nhdsWithin
  have e2 : ∀ᶠ τ in 𝓝[≠] (0 : K), 1 - a * τ ^ 2 ≠ 0 :=
    (hD.eventually_ne one_ne_zero).filter_mono nhdsWithin_le_nhds
  have e3 : ∀ᶠ τ in 𝓝[≠] (0 : K), g.re + a * τ * g.imI ≠ 0 := by
    have h1 : Continuous (fun τ : K => g.re + a * τ * g.imI) := by fun_prop
    exact ((h1.tendsto 0).eventually_ne (by simpa using hs0)).filter_mono nhdsWithin_le_nhds
  have e4 : ∀ᶠ τ in 𝓝[≠] (0 : K), g.re * τ + g.imI ≠ 0 := by
    by_cases hI : g.imI = 0
    · filter_upwards [e1] with τ hτ
      simpa [hI] using ⟨hs0, hτ⟩
    · have h1 : Continuous (fun τ : K => g.re * τ + g.imI) := by fun_prop
      exact ((h1.tendsto 0).eventually_ne (by simpa using hI)).filter_mono nhdsWithin_le_nhds
  have e5 : ∀ᶠ τ in 𝓝[≠] (0 : K), g * x τ ∈ interior W :=
    (hf.eventually (interior_mem_nhds.2 hW)).filter_mono nhdsWithin_le_nhds
  obtain ⟨τ, h1, h2', h3, h4, h5⟩ := (e1.and (e2.and (e3.and (e4.and e5)))).exists
  refine ⟨g * x τ, ?_, ?_, mem_interior_iff_mem_nhds.1 h5⟩
  · rw [nrm_mul, hg, one_mul]
    simp only [nrm, x, X0, X1]
    field_simp
    ring
  · have hr : (g * x τ).re = g.re * X0 τ + a * g.imI * X1 τ := by simp [x]
    rw [hr]
    intro h
    have hm : g.re * X0 τ + a * g.imI * X1 τ - g.re
        = 2 * a * τ * (g.re * τ + g.imI) / (1 - a * τ ^ 2) := by
      simp only [X0, X1]
      field_simp
      ring
    have hp : g.re * X0 τ + a * g.imI * X1 τ + g.re
        = 2 * (g.re + a * τ * g.imI) / (1 - a * τ ^ 2) := by
      simp only [X0, X1]
      field_simp
      ring
    have hz : (g.re * X0 τ + a * g.imI * X1 τ - g.re) * (g.re * X0 τ + a * g.imI * X1 τ + g.re) = 0 := by
      linear_combination h - hre
    rw [hm, hp] at hz
    exact mul_ne_zero (div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h2 ha) h1) h4) h2')
      (div_ne_zero (mul_ne_zero h2 h3) h2') hz
end GlobalTheory.QSA
