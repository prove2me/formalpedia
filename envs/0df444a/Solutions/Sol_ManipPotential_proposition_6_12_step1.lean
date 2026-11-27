-- Prove2me | solution 1 for ManipPotential.proposition_6_12_step1
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:09:25.29337+00:00
-- url     : https://prove2.me/submissions/e3ea84c2-7d6e-4d3f-a66f-5e741205632b

import Mathlib
import Theorems.Thm_ManipPotential_proposition_6_11
import Theorems.Thm_ManipPotential_proposition_6_12_step1_curve
import Definitions.Def_ManipPotential_GAxioms
import Definitions.Def_ManipPotential_TransferVectors
import Definitions.Def_ManipPotential_ell
import Definitions.Def_ManipPotential_unitVec

open ManipPotential MeasureTheory
open scoped NNReal Pointwise

/-- Proposition 6.12, Step 1. -/
theorem solution {m : ℕ} [NeZero m] (hm : 3 ≤ m) (K : ℕ)
    (g : (Ranking m → ℚ) → Fin m) (hg : GAxioms K g) :
    ∃ T : Submodule ℝ (Ranking m → ℝ),
      Module.finrank ℝ T = m.factorial - m + 1 ∧
      ∀ i j : Fin m, i ≠ j → ∃ M : Set (Ranking m → ℝ),
        IsClosed M ∧ Convex ℝ M ∧ 0 ∈ M ∧
        (∀ ⦃a : ℝ⦄, 0 ≤ a → ∀ ⦃x : Ranking m → ℝ⦄, x ∈ M → a • x ∈ M) ∧
        (T : Set (Ranking m → ℝ)) ⊆ M ∧
        TransferVectors ((K : ℝ) + 1) i j ⊆ M ∧
        -(unitVec (ell i) - unitVec (ell j)) ∉ M := by
  classical
  obtain ⟨a, b, a₀, b₀, U, L, G, ha, hab, hU, hLip, hcoord, hJ, huniq, hpos, hrank⟩ :=
    proposition_6_11 hm K g hg
  have hUopen : IsOpen U := by
    rw [hU]
    exact (isOpen_set_pi Set.finite_univ fun s _ => isOpen_Ioo).prod isOpen_Ioo
  have hUne : U.Nonempty := by
    refine ⟨(fun s => (a s + b s) / 2, (a₀ + b₀) / 2), ?_⟩
    rw [hU]
    constructor
    · intro s hs
      exact ⟨by linarith [ha s], by linarith [ha s]⟩
    · exact ⟨by linarith, by linarith⟩
  haveI : (volume : Measure ((ExtRanking m → ℝ) × ℝ)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure volume volume
  have hae : ∀ᵐ z ∂(volume.restrict U), DifferentiableWithinAt ℝ G U z :=
    hLip.ae_differentiableWithinAt hUopen.measurableSet
  have hmem : ∀ᵐ z ∂(volume.restrict U), z ∈ U :=
    ae_restrict_mem hUopen.measurableSet
  haveI : (ae (volume.restrict U)).NeBot :=
    ae_restrict_neBot.mpr (hUopen.measure_ne_zero volume hUne)
  obtain ⟨z₀, hzd, hzU⟩ := (hae.and hmem).exists
  have hzdiff : DifferentiableAt ℝ G z₀ := hzd.differentiableAt (hUopen.mem_nhds hzU)
  let D : ((ExtRanking m → ℝ) × ℝ) →ₗ[ℝ] (Ranking m → ℝ) :=
    (fderiv ℝ G z₀).toLinearMap
  let T : Submodule ℝ (Ranking m → ℝ) := LinearMap.range D
  refine ⟨T, hrank z₀ hzU hzdiff, ?_⟩
  intro i j hij
  let C : Submodule ℝ≥0 (Ranking m → ℝ) :=
    Submodule.span ℝ≥0 (TransferVectors ((K : ℝ) + 1) i j)
  let A : Set (Ranking m → ℝ) := (C : Set (Ranking m → ℝ)) + (T : Set (Ranking m → ℝ))
  let M : Set (Ranking m → ℝ) := closure A
  have hA0 : (0 : Ranking m → ℝ) ∈ A := by
    have h := Set.add_mem_add C.zero_mem T.zero_mem
    simpa using h
  have hAconv : Convex ℝ A := by
    rintro x hx y hy p q hp hq hpq
    rcases hx with ⟨c₁, hc₁, t₁, ht₁, rfl⟩
    rcases hy with ⟨c₂, hc₂, t₂, ht₂, rfl⟩
    have hc : p • c₁ + q • c₂ ∈ C := by
      have h := C.add_mem (C.smul_mem ⟨p, hp⟩ hc₁) (C.smul_mem ⟨q, hq⟩ hc₂)
      exact (NNReal.smul_def ⟨p, hp⟩ c₁) ▸ (NNReal.smul_def ⟨q, hq⟩ c₂) ▸ h
    have ht : p • t₁ + q • t₂ ∈ T := T.add_mem (T.smul_mem p ht₁) (T.smul_mem q ht₂)
    have h := Set.add_mem_add hc ht
    convert h using 1 <;> module
  have hAscale : ∀ ⦃p : ℝ⦄, 0 ≤ p → ∀ ⦃x : Ranking m → ℝ⦄, x ∈ A → p • x ∈ A := by
    intro p hp x hx
    rcases hx with ⟨c, hc, t, ht, rfl⟩
    have hc' : p • c ∈ C := (NNReal.smul_def ⟨p, hp⟩ c) ▸ C.smul_mem ⟨p, hp⟩ hc
    have h := Set.add_mem_add hc' (T.smul_mem p ht)
    convert h using 1 <;> module
  have hM0 : (0 : Ranking m → ℝ) ∈ M := subset_closure hA0
  have hMscale : ∀ ⦃p : ℝ⦄, 0 ≤ p → ∀ ⦃x : Ranking m → ℝ⦄, x ∈ M → p • x ∈ M := by
    intro p hp x hx
    apply closure_minimal _ (isClosed_closure.preimage (continuous_const_smul p)) hx
    intro y hy
    exact subset_closure (hAscale hp hy)
  refine ⟨M, isClosed_closure, hAconv.closure, hM0, hMscale, ?_, ?_, ?_⟩
  · intro t ht
    apply subset_closure
    have h := Set.add_mem_add C.zero_mem ht
    simpa using h
  · intro u hu
    apply subset_closure
    have huC : u ∈ C := Submodule.subset_span hu
    have h := Set.add_mem_add huC T.zero_mem
    simpa using h
  · exact proposition_6_12_step1_curve hm K g hg G U hUopen z₀ hzU hzdiff hJ hpos i j hij
