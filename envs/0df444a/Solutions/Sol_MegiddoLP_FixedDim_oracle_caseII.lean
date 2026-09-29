-- Prove2me | solution 1 for MegiddoLP.FixedDim.oracle_caseII
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:41:31.286617+00:00
-- url     : https://prove2.me/submissions/81a5a406-ac44-4299-ac16-c37e8496101b

import Mathlib
import Definitions.Def_Polyhedron
import Definitions.Def_MegiddoLP_FixedDim_Infeasibility

open Matrix LinearOptimization

namespace MegiddoLP.FixedDim

theorem aux_mcII_le {n d : ℕ} (A : Matrix (Fin (n + 1)) (Fin d) ℝ)
    (b : Fin (n + 1) → ℝ) (x : Fin d → ℝ) (i : Fin (n + 1)) :
    b i - A i ⬝ᵥ x ≤ infeas A b x := by
  unfold infeas
  exact Finset.le_sup' (fun i => b i - A i ⬝ᵥ x) (Finset.mem_univ i)

theorem aux_mcII_lt_iff {n d : ℕ} (A : Matrix (Fin (n + 1)) (Fin d) ℝ)
    (b : Fin (n + 1) → ℝ) (x : Fin d → ℝ) (c : ℝ) :
    infeas A b x < c ↔ ∀ i, b i - A i ⬝ᵥ x < c := by
  unfold infeas
  rw [Finset.sup'_lt_iff]
  simp

theorem aux_mcII_le_iff {n d : ℕ} (A : Matrix (Fin (n + 1)) (Fin d) ℝ)
    (b : Fin (n + 1) → ℝ) (x : Fin d → ℝ) (c : ℝ) :
    infeas A b x ≤ c ↔ ∀ i, b i - A i ⬝ᵥ x ≤ c := by
  unfold infeas
  rw [Finset.sup'_le_iff]
  simp

theorem aux_mcII_key {n d : ℕ} (A : Matrix (Fin (n + 1)) (Fin (d + 1)) ℝ)
    (b : Fin (n + 1) → ℝ) (x' : Fin (d + 1) → ℝ)
    (hx' : x' (Fin.last d) = 0)
    (hmin : ∀ w : Fin (d + 1) → ℝ, w (Fin.last d) = 0 → infeas A b x' ≤ infeas A b w)
    (y : Fin (d + 1) → ℝ) (hy : ∀ i, infeas A b x' = b i - A i ⬝ᵥ x' → 0 ≤ A i ⬝ᵥ y)
    (w : Fin (d + 1) → ℝ) (hw : infeas A b w < infeas A b x')
    (hyw : y (Fin.last d) * w (Fin.last d) < 0) : False := by
  set c := infeas A b x' with hc
  set yd := y (Fin.last d) with hyd
  set wd := w (Fin.last d) with hwd
  have hyd0 : yd ≠ 0 := by
    intro h; rw [h, zero_mul] at hyw; exact lt_irrefl _ hyw
  set α : ℝ := -wd / yd with hα
  have hαpos : 0 ≤ α := by
    have : α = -(yd * wd) / (yd ^ 2) := by
      rw [hα]; field_simp
    rw [this]
    apply div_nonneg (by linarith) (by positivity)
  set v : Fin (d + 1) → ℝ := (w - x') + α • y with hv
  set K : Fin (n + 1) → ℝ := fun i => A i ⬝ᵥ v with hK
  set r : Fin (n + 1) → ℝ := fun i => b i - A i ⬝ᵥ x' with hr
  have hKpos : ∀ i, c = r i → 0 < K i := by
    intro i hi
    have h1 := aux_mcII_le A b w i
    have h2 := hy i hi
    have : K i = (A i ⬝ᵥ w - A i ⬝ᵥ x') + α * (A i ⬝ᵥ y) := by
      simp only [hK, hv, dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    rw [this]
    have h3 : 0 ≤ α * (A i ⬝ᵥ y) := mul_nonneg hαpos h2
    simp only [hr] at hi
    linarith
  have hev : ∀ i, ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), r i - s * K i < c := by
    intro i
    rcases (aux_mcII_le A b x' i).lt_or_eq with h | h
    · have ht : Filter.Tendsto (fun s : ℝ => r i - s * K i) (nhds 0) (nhds (r i)) := by
        have h0 : Filter.Tendsto (fun s : ℝ => r i - s * K i) (nhds 0) (nhds (r i - 0 * K i)) :=
          tendsto_const_nhds.sub (Filter.tendsto_id.mul tendsto_const_nhds)
        rwa [zero_mul, sub_zero] at h0
      exact nhdsWithin_le_nhds (ht.eventually (gt_mem_nhds h))
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have : 0 < s * K i := mul_pos hs (hKpos i h.symm)
      linarith
  have hall := (Filter.eventually_all.2 hev).and self_mem_nhdsWithin
  obtain ⟨s, hs, _⟩ := hall.exists
  set q : Fin (d + 1) → ℝ := x' + s • v with hq
  have hqd : q (Fin.last d) = 0 := by
    simp only [hq, hv, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hx']
    rw [← hwd, ← hyd, hα]
    field_simp
    ring
  have hlt : infeas A b q < c := by
    rw [aux_mcII_lt_iff]
    intro i
    have := hs i
    have e : b i - A i ⬝ᵥ q = r i - s * K i := by
      simp only [hq, hr, hK, dotProduct_add, dotProduct_smul, smul_eq_mul]
      ring
    rw [e]; exact this
  have := hmin q hqd
  linarith

end MegiddoLP.FixedDim

open Matrix LinearOptimization
open MegiddoLP.FixedDim

theorem solution {n d : ℕ} (A : Matrix (Fin (n + 1)) (Fin (d + 1)) ℝ)
    (b : Fin (n + 1) → ℝ) (x' : Fin (d + 1) → ℝ)
    (hinf : polyhedron A b ∩ {x | x (Fin.last d) = 0} = ∅)
    (hx' : x' (Fin.last d) = 0)
    (hmin : ∀ w : Fin (d + 1) → ℝ, w (Fin.last d) = 0 → infeas A b x' ≤ infeas A b w) :
    ((∃ y : Fin (d + 1) → ℝ, y (Fin.last d) = 1 ∧
        ∀ i, infeas A b x' = b i - A i ⬝ᵥ x' → 0 ≤ A i ⬝ᵥ y) →
      ∀ w, infeas A b w < infeas A b x' → 0 < w (Fin.last d)) ∧
    ((∃ z : Fin (d + 1) → ℝ, z (Fin.last d) = -1 ∧
        ∀ i, infeas A b x' = b i - A i ⬝ᵥ x' → 0 ≤ A i ⬝ᵥ z) →
      ∀ w, infeas A b w < infeas A b x' → w (Fin.last d) < 0) ∧
    (((∃ y : Fin (d + 1) → ℝ, y (Fin.last d) = 1 ∧
        ∀ i, infeas A b x' = b i - A i ⬝ᵥ x' → 0 ≤ A i ⬝ᵥ y) ↔
      (∃ z : Fin (d + 1) → ℝ, z (Fin.last d) = -1 ∧
        ∀ i, infeas A b x' = b i - A i ⬝ᵥ x' → 0 ≤ A i ⬝ᵥ z)) →
      (∀ w, infeas A b x' ≤ infeas A b w) ∧ polyhedron A b = ∅) := by
  -- positivity of the infeasibility at x'
  have hcpos : 0 < infeas A b x' := by
    by_contra h
    push Not at h
    have hmem : x' ∈ polyhedron A b := by
      intro i
      have := aux_mcII_le A b x' i
      show b i ≤ A i ⬝ᵥ x'
      linarith
    have : x' ∈ polyhedron A b ∩ {x | x (Fin.last d) = 0} := ⟨hmem, hx'⟩
    rw [hinf] at this
    exact this
  have h1 : (∃ y : Fin (d + 1) → ℝ, y (Fin.last d) = 1 ∧
        ∀ i, infeas A b x' = b i - A i ⬝ᵥ x' → 0 ≤ A i ⬝ᵥ y) →
      ∀ w, infeas A b w < infeas A b x' → 0 < w (Fin.last d) := by
    rintro ⟨y, hyd, hy⟩ w hw
    by_contra h
    push Not at h
    rcases h.lt_or_eq with h | h
    · exact aux_mcII_key A b x' hx' hmin y hy w hw (by rw [hyd]; linarith)
    · have := hmin w h
      linarith
  have h2 : (∃ z : Fin (d + 1) → ℝ, z (Fin.last d) = -1 ∧
        ∀ i, infeas A b x' = b i - A i ⬝ᵥ x' → 0 ≤ A i ⬝ᵥ z) →
      ∀ w, infeas A b w < infeas A b x' → w (Fin.last d) < 0 := by
    rintro ⟨z, hzd, hz⟩ w hw
    by_contra h
    push Not at h
    rcases h.lt_or_eq with h | h
    · exact aux_mcII_key A b x' hx' hmin z hz w hw (by rw [hzd]; linarith)
    · have := hmin w h.symm
      linarith
  refine ⟨h1, h2, ?_⟩
  intro hiff
  have hall : ∀ w, infeas A b x' ≤ infeas A b w := by
    intro w
    by_contra hw
    push Not at hw
    have hact : ∀ i, infeas A b x' = b i - A i ⬝ᵥ x' → 0 ≤ A i ⬝ᵥ (w - x') := by
      intro i hi
      have := aux_mcII_le A b w i
      rw [dotProduct_sub]
      linarith
    rcases lt_trichotomy (w (Fin.last d)) 0 with h | h | h
    · have hz : ∃ z : Fin (d + 1) → ℝ, z (Fin.last d) = -1 ∧
          ∀ i, infeas A b x' = b i - A i ⬝ᵥ x' → 0 ≤ A i ⬝ᵥ z := by
        refine ⟨(1 / (-w (Fin.last d))) • (w - x'), ?_, ?_⟩
        · have hne : w (Fin.last d) ≠ 0 := h.ne
          simp only [Pi.smul_apply, Pi.sub_apply, hx', smul_eq_mul, sub_zero]
          rw [one_div, inv_neg, neg_mul, inv_mul_cancel₀ hne]
        · intro i hi
          rw [dotProduct_smul, smul_eq_mul]
          apply mul_nonneg _ (hact i hi)
          apply div_nonneg zero_le_one
          linarith
      have := h1 (hiff.2 hz) w hw
      linarith
    · have := hmin w h
      linarith
    · have hy : ∃ y : Fin (d + 1) → ℝ, y (Fin.last d) = 1 ∧
          ∀ i, infeas A b x' = b i - A i ⬝ᵥ x' → 0 ≤ A i ⬝ᵥ y := by
        refine ⟨(1 / (w (Fin.last d))) • (w - x'), ?_, ?_⟩
        · simp only [Pi.smul_apply, Pi.sub_apply, hx', smul_eq_mul, sub_zero]
          field_simp
        · intro i hi
          rw [dotProduct_smul, smul_eq_mul]
          apply mul_nonneg _ (hact i hi)
          apply div_nonneg zero_le_one
          linarith
      have := h2 (hiff.1 hy) w hw
      linarith
  refine ⟨hall, ?_⟩
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  have hle : infeas A b x ≤ 0 := by
    rw [aux_mcII_le_iff]
    intro i
    have : b i ≤ A i ⬝ᵥ x := hx i
    linarith
  have := hall x
  linarith
