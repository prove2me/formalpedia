-- Prove2me | solution 1 for HighDimStat.Rkhs.thm12_11_moore_aronszajn
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-14T02:24:59.587508+00:00
-- url     : https://prove2.me/submissions/617dfb98-d019-4ea1-acfb-b920cc5db65b

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Ring
import Definitions.Def_HighDimStat_Rkhs_Core

open scoped RealInnerProductSpace
open HighDimStat.Rkhs

/-- The Kronecker delta kernel on any type `X`, defined classically as `1` on the diagonal and
`0` off the diagonal. -/
private noncomputable def kroneckerKernel (X : Type*) (x y : X) : ℝ :=
  by
    classical
    exact if x = y then 1 else 0

private lemma isPSDKernel_kroneckerKernel (X : Type*) : IsPSDKernel (kroneckerKernel X) := by
  classical
  refine ⟨fun x y => ?_, fun n x α => ?_⟩
  · simp only [kroneckerKernel, eq_comm]
  · let s : Finset X := Finset.univ.image x
    have hdiag : ∀ i j : Fin n, kroneckerKernel X (x i) (x j) =
        ∑ z ∈ s, (if x i = z then (1 : ℝ) else 0) * (if x j = z then 1 else 0) := by
      intro i j
      simp only [kroneckerKernel]
      by_cases hij : x i = x j
      · have hmem : x i ∈ s := Finset.mem_image_of_mem x (Finset.mem_univ i)
        rw [if_pos hij, Finset.sum_eq_single (x i)]
        · simp [hij]
        · intro z _ hz
          rw [if_neg (Ne.symm hz), zero_mul]
        · intro hnot
          exact False.elim (hnot hmem)
      · rw [if_neg hij]
        symm
        refine Finset.sum_eq_zero fun z _ => ?_
        by_cases hiz : x i = z
        · subst hiz
          rw [if_neg (Ne.symm hij), mul_zero]
        · rw [if_neg hiz, zero_mul]
    have hsum : ∑ i : Fin n, ∑ j : Fin n, α i * α j * kroneckerKernel X (x i) (x j) =
        ∑ z ∈ s, (∑ i : Fin n, α i * if x i = z then (1 : ℝ) else 0) *
          (∑ j : Fin n, α j * if x j = z then (1 : ℝ) else 0) := by
      symm
      simp_rw [Finset.sum_mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hdiag i j, Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      ring
    rw [hsum]
    exact Finset.sum_nonneg fun z _ => mul_self_nonneg _

/-- For the Kronecker delta kernel, the reproducing property forces any RKHS feature map to be
injective. -/
private lemma feature_injective_of_kronecker {X H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {toFun : H →ₗ[ℝ] (X → ℝ)} {feature : X → H}
    (hR : IsRKHS (kroneckerKernel X) toFun feature) : Function.Injective feature := by
  classical
  intro x y hxy
  by_contra hne
  have h1 : ⟪feature y, feature x⟫ = kroneckerKernel X x y := by
    rw [hR.reproducing, hR.feature_eq]
  have h2 : ⟪feature y, feature y⟫ = kroneckerKernel X y y := by
    rw [hR.reproducing, hR.feature_eq]
  rw [hxy, h2] at h1
  simp only [kroneckerKernel, ↓reduceIte, if_neg hne] at h1
  exact one_ne_zero h1

/-- The type `Σ A : Type, Set A : Type 1` admits no injective map into any `H : Type 0`, since for
every `H : Type 0` it contains an embedded copy of `Set H`. -/
private lemma not_injective_sigma_set_to_type0 (H : Type)
    (f : (Σ A : Type, Set A) → H) : ¬ Function.Injective f := by
  intro hf
  let g : Set H → (Σ A : Type, Set A) := fun s => ⟨H, s⟩
  have hg : Function.Injective g := fun s₁ s₂ h => eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have hfg : Function.Injective (f ∘ g) := hf.comp hg
  let S : Set H := {h : H | ∃ s : Set H, f (g s) = h ∧ h ∉ s}
  by_cases hmem : f (g S) ∈ S
  · rcases hmem with ⟨s, hs_eq, hs_not⟩
    have hsS : s = S := hfg hs_eq
    rw [hsS] at hs_not
    exact hs_not ⟨S, rfl, hs_not⟩
  · exact hmem ⟨S, rfl, hmem⟩

theorem solution :
    ¬ (∀ {X : Type 1} (K : X → X → ℝ) (_hK : IsPSDKernel K),
      (∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H)
          (toFun : H →ₗ[ℝ] (X → ℝ)) (feature : X → H), IsRKHS K toFun feature) ∧
        (∀ (H₁ : Type) (_ : NormedAddCommGroup H₁) (_ : InnerProductSpace ℝ H₁)
            (_ : CompleteSpace H₁) (toFun₁ : H₁ →ₗ[ℝ] (X → ℝ)) (feature₁ : X → H₁),
            IsRKHS K toFun₁ feature₁ →
          ∀ (H₂ : Type) (_ : NormedAddCommGroup H₂) (_ : InnerProductSpace ℝ H₂)
            (_ : CompleteSpace H₂) (toFun₂ : H₂ →ₗ[ℝ] (X → ℝ)) (feature₂ : X → H₂),
            IsRKHS K toFun₂ feature₂ →
          ∃ e : H₁ ≃ₗᵢ[ℝ] H₂, ∀ f : H₁, toFun₂ (e f) = toFun₁ f)) := by
  intro h
  let X₁ : Type 1 := Σ A : Type, Set A
  obtain ⟨⟨H, _, _, _, toFun, feature, hR⟩, _⟩ :=
    @h X₁ (kroneckerKernel X₁) (isPSDKernel_kroneckerKernel X₁)
  exact not_injective_sigma_set_to_type0 H feature (feature_injective_of_kronecker hR)
