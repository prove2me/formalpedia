-- Prove2me | solution 1 for MeasureTheory.second_moment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:38:50.894359+00:00
-- url     : https://prove2.me/submissions/1e5b2dd5-fb49-4395-9a2b-289113cd65dd

module
public import Definitions.Def_AddUN_CantorMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_AddUN_SecondMoment
public import Theorems.Thm_MeasureTheory_cantorMeasure_real_inter_cylinderOn
public import Theorems.Thm_MeasureTheory_integrable_ind
public import Theorems.Thm_MeasureTheory_integral_ind
public import Theorems.Thm_MeasureTheory_integral_mul_aux
public import Theorems.Thm_MeasureTheory_Determined_inter
public import Theorems.Thm_MeasureTheory_Determined_mono
public import Theorems.Thm_MeasureTheory_IsUniversallyNull_mono
public import Theorems.Thm_MeasureTheory_determined_cylinderOn
public import Theorems.Thm_MeasureTheory_flip_apply_self
public import Theorems.Thm_MeasureTheory_flip_flip
public import Theorems.Thm_MeasureTheory_measurableSet_cylinderOn
attribute [local simp] MeasureTheory.flip_apply_self
attribute [local simp] MeasureTheory.flip_flip



set_option autoImplicit false
@[expose] public section
public section
open Set MeasureTheory
open MeasureTheory
namespace MeasureTheory
theorem _root_.solution {K : Set (ℕ → Bool)} (hK : MeasurableSet K) (J : Finset ℕ)
    (E : ℕ → Set (ℕ → Bool)) (B : ℕ → Finset ℕ) (v : ℕ → Bool) (L : ℕ) (s : Set ℕ) {θ : ℝ}
    (hθ : 0 < θ) (hE : ∀ k ∈ J, MeasurableSet (E k)) (hdet : ∀ k ∈ J, Determined s (E k))
    (hs : ∀ k ∈ J, Disjoint s (B k : Set ℕ))
    (hB : ∀ k ∈ J, ∀ k' ∈ J, k ≠ k' → Disjoint (B k) (B k')) (hL : ∀ k ∈ J, (B k).card = L)
    (hθK : ∀ k ∈ J, θ ≤ cantorMeasure.real (K ∩ E k))
    (hbad : ∀ k ∈ J, cantorMeasure.real (K ∩ E k ∩ cylinderOn (B k) v) ≤
      (1 / 2) ^ L / 2 * cantorMeasure.real (K ∩ E k)) :
    (J.card : ℝ) * (1 / 2) ^ L * θ ^ 2 ≤ 4 := by
  set ρ : ℝ := (1 / 2) ^ L with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  let R : ℕ → Set (ℕ → Bool) := fun k ↦ cylinderOn (B k) v
  have hR : ∀ k, MeasurableSet (R k) := fun k ↦ measurableSet_cylinderOn _ _
  let ξ : ℕ → (ℕ → Bool) → ℝ := fun k w ↦ ρ * ind (E k) w - ind (E k ∩ R k) w
  let ζ : ℕ → (ℕ → Bool) → ℝ := fun k w ↦ ρ * ind (K ∩ E k) w - ind (K ∩ E k ∩ R k) w
  -- The integral of `ζ k`.
  have hζi : ∀ k ∈ J, Integrable (ζ k) cantorMeasure := fun k hk ↦
    ((integrable_ind (hK.inter (hE k hk))).const_mul ρ).sub
      (integrable_ind ((hK.inter (hE k hk)).inter (hR k)))
  have hζ : ∀ k ∈ J, ∫ w, ζ k w ∂cantorMeasure =
      ρ * cantorMeasure.real (K ∩ E k) - cantorMeasure.real (K ∩ E k ∩ R k) := fun k hk ↦ by
    simp only [ζ]
    rw [integral_sub ((integrable_ind (hK.inter (hE k hk))).const_mul ρ)
      (integrable_ind ((hK.inter (hE k hk)).inter (hR k))), integral_const_mul,
      integral_ind (hK.inter (hE k hk)), integral_ind ((hK.inter (hE k hk)).inter (hR k))]
  -- The products `ξ k * ξ k'`: the cross terms vanish by independence.
  have hint : ∀ k ∈ J, ∀ k' ∈ J, Integrable (fun w ↦ ξ k w * ξ k' w) cantorMeasure :=
    fun k hk k' hk' ↦ (integral_mul_aux (hE k hk) (hE k' hk') (hR k) (hR k') ρ).1
  have hcross : ∀ k ∈ J, ∀ k' ∈ J, k ≠ k' → ∫ w, ξ k w * ξ k' w ∂cantorMeasure = 0 := by
    intro k hk k' hk' hne
    have hd : Determined s (E k ∩ E k') := (hdet k hk).inter (hdet k' hk')
    have i1 : cantorMeasure.real (E k ∩ E k' ∩ R k') = cantorMeasure.real (E k ∩ E k') * ρ := by
      rw [cantorMeasure_real_inter_cylinderOn (B k') v
        (hd.mono (hs k' hk').subset_compl_right), hL k' hk']
    have i2 : cantorMeasure.real (E k ∩ E k' ∩ R k) = cantorMeasure.real (E k ∩ E k') * ρ := by
      rw [cantorMeasure_real_inter_cylinderOn (B k) v
        (hd.mono (hs k hk).subset_compl_right), hL k hk]
    have i3 : cantorMeasure.real (E k ∩ E k' ∩ R k ∩ R k') =
        cantorMeasure.real (E k ∩ E k' ∩ R k) * ρ := by
      rw [cantorMeasure_real_inter_cylinderOn (B k') v
        ((hd.mono (hs k' hk').subset_compl_right).inter (determined_cylinderOn (B k) v
          (Finset.disjoint_coe.2 (hB k hk k' hk' hne)).subset_compl_right)), hL k' hk']
    rw [(integral_mul_aux (hE k hk) (hE k' hk') (hR k) (hR k') ρ).2, i3, i2, i1]
    ring
  have hdiag : ∀ k ∈ J, ∫ w, ξ k w * ξ k w ∂cantorMeasure ≤ ρ := by
    intro k hk
    have i1 : cantorMeasure.real (E k ∩ R k) = cantorMeasure.real (E k) * ρ := by
      rw [cantorMeasure_real_inter_cylinderOn (B k) v
        ((hdet k hk).mono (hs k hk).subset_compl_right), hL k hk]
    have hq0 : 0 ≤ cantorMeasure.real (E k) := measureReal_nonneg
    have hq1 : cantorMeasure.real (E k) ≤ 1 := measureReal_le_one
    rw [(integral_mul_aux (hE k hk) (hE k hk) (hR k) (hR k) ρ).2, inter_self, inter_assoc (E k),
      inter_self, i1]
    nlinarith [mul_nonneg hρ0 (sub_nonneg.2 hq1), mul_nonneg (mul_nonneg hq0 hρ0) hρ0]
  -- The second moment of the sum.
  have hsq : ∀ w, (∑ k ∈ J, ξ k w) ^ 2 = ∑ k ∈ J, ∑ k' ∈ J, ξ k w * ξ k' w := fun w ↦ by
    rw [sq, Finset.sum_mul_sum]
  have hsqi : Integrable (fun w ↦ (∑ k ∈ J, ξ k w) ^ 2) cantorMeasure := by
    simp_rw [hsq]
    exact integrable_finsetSum _ fun k hk ↦ integrable_finsetSum _ fun k' hk' ↦ hint k hk k' hk'
  have hmom : ∫ w, (∑ k ∈ J, ξ k w) ^ 2 ∂cantorMeasure ≤ J.card * ρ := by
    simp_rw [hsq]
    rw [integral_finsetSum _ fun k hk ↦ integrable_finsetSum _ fun k' hk' ↦ hint k hk k' hk']
    calc ∑ k ∈ J, ∫ w, ∑ k' ∈ J, ξ k w * ξ k' w ∂cantorMeasure
        = ∑ k ∈ J, ∫ w, ξ k w * ξ k w ∂cantorMeasure := Finset.sum_congr rfl fun k hk ↦ by
          rw [integral_finsetSum _ fun k' hk' ↦ hint k hk k' hk',
            Finset.sum_eq_single k (fun k' hk' hne ↦ hcross k hk k' hk' hne.symm)
              (fun h ↦ absurd hk h)]
      _ ≤ ∑ _k ∈ J, ρ := Finset.sum_le_sum hdiag
      _ = J.card * ρ := by simp
  -- A pointwise bound, integrated.
  have ht : 0 < 2 / θ := by positivity
  have hpt : ∀ w, ∑ k ∈ J, ζ k w ≤ 2 / θ / 2 + (∑ k ∈ J, ξ k w) ^ 2 / (2 * (2 / θ)) := by
    intro w
    by_cases hw : w ∈ K
    · have e : ∀ k, ζ k w = ξ k w := fun k ↦ by
        by_cases h1 : w ∈ E k <;> by_cases h2 : w ∈ R k <;> simp [ζ, ξ, ind, hw, h1, h2]
      simp_rw [e]
      have h0 : 0 ≤ (∑ k ∈ J, ξ k w - 2 / θ) ^ 2 / (2 * (2 / θ)) := by positivity
      have e2 : (∑ k ∈ J, ξ k w - 2 / θ) ^ 2 / (2 * (2 / θ)) =
          2 / θ / 2 + (∑ k ∈ J, ξ k w) ^ 2 / (2 * (2 / θ)) - ∑ k ∈ J, ξ k w := by
        field_simp
        ring
      linarith
    · have e : ∀ k, ζ k w = 0 := fun k ↦ by
        simp [ζ, ind, hw]
      simp_rw [e]
      simp only [Finset.sum_const_zero]
      positivity
  have hgi : Integrable (fun w ↦ 2 / θ / 2 + (∑ k ∈ J, ξ k w) ^ 2 / (2 * (2 / θ)))
      cantorMeasure := (integrable_const (2 / θ / 2)).add (hsqi.div_const (2 * (2 / θ)))
  have hmono := integral_mono (integrable_finsetSum _ hζi) hgi hpt
  rw [integral_finsetSum _ hζi, integral_add (f := fun _ ↦ 2 / θ / 2)
    (g := fun w ↦ (∑ k ∈ J, ξ k w) ^ 2 / (2 * (2 / θ))) (integrable_const _)
    (hsqi.div_const _), integral_const, integral_div] at hmono
  have hlow : (J.card : ℝ) * (ρ / 2 * θ) ≤ ∑ k ∈ J, ∫ w, ζ k w ∂cantorMeasure := by
    calc (J.card : ℝ) * (ρ / 2 * θ) = ∑ _k ∈ J, ρ / 2 * θ := by simp
      _ ≤ ∑ k ∈ J, ∫ w, ζ k w ∂cantorMeasure := Finset.sum_le_sum fun k hk ↦ by
        rw [hζ k hk]
        have h1 := hbad k hk
        have h2 : ρ / 2 * θ ≤ ρ / 2 * cantorMeasure.real (K ∩ E k) :=
          mul_le_mul_of_nonneg_left (hθK k hk) (by positivity)
        linarith
  have h5 : (∫ w, (∑ k ∈ J, ξ k w) ^ 2 ∂cantorMeasure) / (2 * (2 / θ)) ≤
      J.card * ρ / (2 * (2 / θ)) := div_le_div_of_nonneg_right hmom (by positivity)
  have h6 : 2 / θ / 2 = 1 / θ := by field_simp
  have h7 : (J.card : ℝ) * ρ / (2 * (2 / θ)) = J.card * ρ * θ / 4 := by
    field_simp
    ring
  simp only [probReal_univ, smul_eq_mul, one_mul] at hmono
  have h8 : (J.card : ℝ) * ρ * θ / 4 ≤ 1 / θ := by linarith
  rw [le_div_iff₀ hθ] at h8
  linarith
end MeasureTheory
