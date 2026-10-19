-- Prove2me | solution 1 for OAI.GaussianPropeller.Gram.exists_translation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:16:16.609689+00:00
-- url     : https://prove2.me/submissions/2596aa38-340c-43dc-a33d-a203c1c2a23a

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion

open OAI OAI.GaussianPropeller
universe uE uF uι
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
variable {ι : Type uι} {E : Type uE} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]


theorem solution [FiniteDimensional ℝ E] (z : ι → E)
    (hneg : Pairwise (fun i j => ⟪z i, z j⟫ < 0)) (hsum : ∑ i, z i = 0)
    (i : ι) : ∃ h ∈ Submodule.span ℝ (Set.range z),
      (∀ j, j ≠ i → ⟪h, z i - z j⟫ = 1) ∧
        ⟪h, z i⟫ = ((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ) := by
  classical
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  have hn0 : n ≠ 0 := by
    rw [hn]; exact_mod_cast (Fintype.card_pos_iff.mpr ⟨i⟩).ne'
  let f : (ι → ℝ) →ₗ[ℝ] E := Fintype.linearCombination ℝ z
  let g : (ι → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj i - n⁻¹ • (∑ j, LinearMap.proj j)
  have hg : ∀ c, g c = c i - n⁻¹ * ∑ j, c j := by
    intro c; simp [g]
  have hker : LinearMap.ker f ≤ LinearMap.ker g := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    rw [Fintype.linearCombination_apply] at hc
    obtain ⟨j0, -, hj0⟩ := Finset.exists_min_image Finset.univ c ⟨i, Finset.mem_univ _⟩
    have hd : ∑ j, (c j - c j0) • z j = 0 := by
      simp_rw [sub_smul]; rw [Finset.sum_sub_distrib, ← Finset.smul_sum, hc, hsum]; simp
    have hin : ∑ j, (c j - c j0) * ⟪z j, z j0⟫ = 0 := by
      have := congrArg (fun w => ⟪w, z j0⟫) hd
      simp only [sum_inner, inner_smul_left, inner_zero_left, RCLike.conj_to_real] at this
      exact this
    have hnp : ∀ j ∈ Finset.univ, (c j - c j0) * ⟪z j, z j0⟫ ≤ 0 := by
      intro j _
      by_cases hj : j = j0
      · subst hj; simp
      · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hj0 j (Finset.mem_univ _)))
          (hneg hj).le
    have hz0 := (Finset.sum_eq_zero_iff_of_nonpos hnp).mp hin
    have hall : ∀ j, c j = c j0 := by
      intro j
      by_cases hj : j = j0
      · rw [hj]
      · have := hz0 j (Finset.mem_univ _)
        rcases mul_eq_zero.mp this with h | h
        · linarith
        · exact absurd h (hneg hj).ne
    rw [hg]
    simp_rw [hall]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn]
    field_simp; ring
  let V := LinearMap.range f
  let φ : V →ₗ[ℝ] ℝ := (LinearMap.ker f).liftQ g hker ∘ₗ f.quotKerEquivRange.symm.toLinearMap
  have hφ : ∀ c, φ ⟨f c, LinearMap.mem_range_self f c⟩ = g c := by
    intro c
    simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  let h0 : V := (InnerProductSpace.toDual ℝ V).symm (LinearMap.toContinuousLinearMap φ)
  have hz : ∀ j, f (Pi.single j 1) = z j := by
    intro j; rw [Fintype.linearCombination_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  have hval : ∀ j, ⟪(h0 : E), z j⟫ = (if j = i then 1 else 0) - n⁻¹ := by
    intro j
    have e1 : ⟪(h0 : E), z j⟫ = ⟪h0, (⟨f (Pi.single j 1), LinearMap.mem_range_self f _⟩ : V)⟫ := by
      rw [Submodule.coe_inner]; simp only [hz]
    rw [e1, InnerProductSpace.toDual_symm_apply, LinearMap.coe_toContinuousLinearMap', hφ, hg]
    rw [Finset.sum_eq_single j]
    · simp [Pi.single_apply, eq_comm]
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  refine ⟨(h0 : E), ?_, ?_, ?_⟩
  · have := h0.2
    have hV : V = Submodule.span ℝ (Set.range z) := Fintype.range_linearCombination ℝ z
    exact hV ▸ this
  · intro j hj
    rw [inner_sub_right, hval, hval, if_pos rfl, if_neg hj]; ring
  · rw [hval, if_pos rfl]; field_simp

