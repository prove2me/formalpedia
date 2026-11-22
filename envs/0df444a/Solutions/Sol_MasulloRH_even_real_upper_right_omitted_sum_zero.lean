-- Prove2me | solution 1 for MasulloRH.even_real_upper_right_omitted_sum_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T17:18:52.819354+00:00
-- url     : https://prove2.me/submissions/d7097813-7364-4bc1-9825-1bb8d6151041
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MasulloRH_RationalTrace
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Compactness.Lindelof
import Theorems.Thm_MasulloRH_even_test_omitted_sum_eq_four_mul_upper_right
import Theorems.Thm_MasulloRH_even_real_upper_right_omitted_sum_zero_of_no_boundary_zero

open MasulloRH MeasureTheory Set Filter
open scoped Topology
set_option autoImplicit false

theorem solution
    (α : ℝ) (hα : 0 < α) (hα2 : α < 1 / 2)
    (ψ : ℝ → ℝ) (hψ : IsRationalTraceTest (fun t => (ψ t : ℂ)))
    (heven : ∀ t : ℝ, 0 < t → ψ t⁻¹ = ψ t) :
    ∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 1 / 2 + α ≤ ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im},
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) *
        (mellin (fun t => (ψ t : ℂ)) ((ρ : ℂ) - 1 / 2)).re = 0 := by
  classical
  let Z (β : ℝ) := {z : ℂ // riemannZeta z = 0 ∧
    1 / 2 + β ≤ z.re ∧ z.re < 1 ∧ 0 < z.im}
  let weight : ℂ → ℝ := fun z =>
    (analyticOrderNatAt riemannZeta z : ℝ) *
      (mellin (fun t => (ψ t : ℂ)) (z - 1 / 2)).re
  have hSummable : Summable (fun z : Z (α / 2) => weight z) :=
    (even_test_omitted_sum_eq_four_mul_upper_right (α / 2)
      (half_pos hα) ψ hψ heven).1
  let cut (β : ℝ) (z : Z (α / 2)) : ℝ :=
    if 1 / 2 + β ≤ (z : ℂ).re then weight z else 0
  have hSum (β : ℝ) (hβ : α / 2 ≤ β) :
      (∑' z : Z β, weight z) = ∑' z : Z (α / 2), cut β z := by
    let s : Set (Z (α / 2)) := {z | 1 / 2 + β ≤ (z : ℂ).re}
    let e : Z β ≃ s :=
      { toFun := fun z =>
          ⟨⟨z, z.property.1, (add_le_add_right hβ _).trans z.property.2.1,
            z.property.2.2⟩, z.property.2.1⟩
        invFun := fun z => ⟨z.val, z.val.property.1, z.property, z.val.property.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    calc
      (∑' z : Z β, weight z) = ∑' z : s, weight z.val :=
        e.tsum_eq (fun z : s => weight z.val)
      _ = ∑' z : Z (α / 2), cut β z := by
        simpa only [Set.indicator_apply, cut, s, Set.mem_ofPred_eq] using
          (tsum_subtype s (fun z : Z (α / 2) => weight z))

  let bad : Set ℝ := (fun z : ℂ => z.re - 1 / 2) '' riemannZetaZeros
  have hZeros : riemannZetaZeros.Countable :=
    (HereditarilyLindelofSpace.isLindelof riemannZetaZeros).countable_of_isDiscrete
      isDiscrete_riemannZetaZeros
  have hDense : Dense badᶜ := (hZeros.image _).dense_compl ℝ
  let good := Ioo (α / 2) α ∩ badᶜ
  have hClosure : α ∈ closure good := by
    rw [Real.mem_closure_iff]
    intro ε hε
    let lower := max (α / 2) (α - ε)
    have hLower : lower < α := max_lt (by linarith) (by linarith)
    obtain ⟨β, hβ, hNotBad⟩ :=
      hDense.inter_open_nonempty (Ioo lower α) isOpen_Ioo (nonempty_Ioo.mpr hLower)
    have hDist : |β - α| < ε := by
      have hLeft : α - ε < β := (le_max_right _ _).trans_lt hβ.1
      rw [abs_of_neg (sub_neg.mpr hβ.2)]
      linarith
    exact ⟨β, ⟨⟨(le_max_left _ _).trans_lt hβ.1, hβ.2⟩, hNotBad⟩, hDist⟩

  let F := 𝓝[good] α
  have : F.NeBot := mem_closure_iff_nhdsWithin_neBot.mp hClosure
  have hGood : ∀ᶠ β in F, β ∈ good := self_mem_nhdsWithin
  have hPointwise (z : Z (α / 2)) : Tendsto (fun β => cut β z) F (𝓝 (cut α z)) := by
    by_cases hz : 1 / 2 + α ≤ (z : ℂ).re
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hGood] with β hβ
      have hβz : 1 / 2 + β ≤ (z : ℂ).re :=
        (add_le_add_right hβ.1.2.le _).trans hz
      simp only [cut, hβz, hz, ↓reduceIte]
    · have hLt : (z : ℂ).re - 1 / 2 < α := by linarith [lt_of_not_ge hz]
      have hEventually : ∀ᶠ β in F, β ∈ Ioi ((z : ℂ).re - 1 / 2) :=
        nhdsWithin_le_nhds (Ioi_mem_nhds hLt)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hEventually] with β hβ
      have hβz : ¬ 1 / 2 + β ≤ (z : ℂ).re := by
        have : (z : ℂ).re - 1 / 2 < β := hβ
        linarith
      simp only [cut, hβz, hz, ↓reduceIte]
  have hLimit : Tendsto (fun β => ∑' z, cut β z) F (𝓝 (∑' z, cut α z)) := by
    apply tendsto_tsum_of_dominated_convergence hSummable.norm hPointwise
    exact Eventually.of_forall fun β z => by
      dsimp only [cut]
      by_cases hz : 1 / 2 + β ≤ (z : ℂ).re
      · rw [if_pos hz]
      · rw [if_neg hz, norm_zero]
        exact norm_nonneg _
  have hZero : (fun _ : ℝ => (0 : ℝ)) =ᶠ[F] (fun β => ∑' z, cut β z) := by
    filter_upwards [hGood] with β hβ
    rw [← hSum β hβ.1.1.le]
    symm
    apply even_real_upper_right_omitted_sum_zero_of_no_boundary_zero β
      ((half_pos hα).trans hβ.1.1) (hβ.1.2.trans hα2) ψ hψ heven
    intro z hz hRe _
    exact hβ.2 ⟨z, mem_riemannZetaZeros.mpr hz, by linarith⟩
  change (∑' z : Z α, weight z) = 0
  rw [hSum α (by linarith)]
  exact tendsto_nhds_unique hLimit (tendsto_const_nhds.congr' hZero)
