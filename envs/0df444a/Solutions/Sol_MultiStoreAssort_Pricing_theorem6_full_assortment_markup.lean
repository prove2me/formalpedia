-- Prove2me | solution 1 for MultiStoreAssort.Pricing.theorem6_full_assortment_markup
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:32:33.947868+00:00
-- url     : https://prove2.me/submissions/e088fd31-afd5-4fda-a505-d2676070000e

import Mathlib
import Definitions.Def_MultiStoreAssort_Pricing_Model

set_option autoImplicit false
open Finset MultiStoreAssort.Pricing

lemma yb_key (a b p θ : ℝ) (hb : 0 < b) :
    (p - θ) * Real.exp (a - b * p) ≤ Real.exp ((a - Real.log b - 1) - b * θ) := by
  have e : (a - Real.log b - 1) - b * θ = (a - b * p) + (b * (p - θ) - 1) + (-Real.log b) := by ring
  rw [e, Real.exp_add, Real.exp_add, Real.exp_neg, Real.exp_log hb]
  have h1 : b * (p - θ) ≤ Real.exp (b * (p - θ) - 1) := by
    have := Real.add_one_le_exp (b * (p - θ) - 1); linarith
  have hE : 0 < Real.exp (a - b * p) := Real.exp_pos _
  have h2 : Real.exp (a - b * p) * (b * (p - θ)) * b⁻¹ = (p - θ) * Real.exp (a - b * p) := by
    field_simp
  calc (p - θ) * Real.exp (a - b * p) = Real.exp (a - b * p) * (b * (p - θ)) * b⁻¹ := h2.symm
    _ ≤ Real.exp (a - b * p) * Real.exp (b * (p - θ) - 1) * b⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hb.le)
        exact mul_le_mul_of_nonneg_left h1 hE.le

theorem yb_single_store_optimum {n : ℕ} (a b : Fin n → ℝ) (hb : ∀ k, 0 < b k)
    (θ : ℝ) (hθ : IsTheta a b θ) :
    (∀ (S : Finset (Fin n)) (p : Fin n → ℝ), rev14 a b S p ≤ θ) ∧
      rev14 a b Finset.univ (fun k => θ + 1 / b k) = θ := by
  have hθ' : θ = ∑ k, Real.exp ((a k - Real.log (b k) - 1) - b k * θ) := hθ
  have hpos : ∀ (S : Finset (Fin n)) (p : Fin n → ℝ),
      0 < 1 + ∑ k ∈ S, Real.exp (a k - b k * p k) := by
    intro S p
    have : 0 ≤ ∑ k ∈ S, Real.exp (a k - b k * p k) :=
      Finset.sum_nonneg fun k _ => (Real.exp_pos _).le
    linarith
  refine ⟨fun S p => ?_, ?_⟩
  · unfold rev14
    rw [div_le_iff₀ (hpos S p)]
    have h1 : ∑ k ∈ S, (p k - θ) * Real.exp (a k - b k * p k) ≤
        ∑ k ∈ S, Real.exp ((a k - Real.log (b k) - 1) - b k * θ) :=
      Finset.sum_le_sum fun k _ => yb_key (a k) (b k) (p k) θ (hb k)
    have h2 : ∑ k ∈ S, Real.exp ((a k - Real.log (b k) - 1) - b k * θ) ≤
        ∑ k, Real.exp ((a k - Real.log (b k) - 1) - b k * θ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun k _ _ => (Real.exp_pos _).le)
    have h3 : ∑ k ∈ S, (p k - θ) * Real.exp (a k - b k * p k) =
        ∑ k ∈ S, p k * Real.exp (a k - b k * p k) - θ * ∑ k ∈ S, Real.exp (a k - b k * p k) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    nlinarith
  · unfold rev14
    rw [div_eq_iff (hpos _ _).ne']
    have h3 : ∀ k, (θ + 1 / b k - θ) * Real.exp (a k - b k * (θ + 1 / b k)) =
        Real.exp ((a k - Real.log (b k) - 1) - b k * θ) := by
      intro k
      have hbk := hb k
      have e : (a k - Real.log (b k) - 1) - b k * θ =
          (a k - b k * (θ + 1 / b k)) + (-Real.log (b k)) := by
        have : b k * (1 / b k) = 1 := by field_simp
        rw [mul_add, this]; ring
      rw [e, Real.exp_add, Real.exp_neg, Real.exp_log hbk]
      field_simp
      ring
    have h4 : ∑ k, (θ + 1 / b k - θ) * Real.exp (a k - b k * (θ + 1 / b k)) = θ := by
      exact (Finset.sum_congr rfl fun k _ => h3 k).trans hθ'.symm
    have h5 : ∑ k, (θ + 1 / b k - θ) * Real.exp (a k - b k * (θ + 1 / b k)) =
        ∑ k, (θ + 1 / b k) * Real.exp (a k - b k * (θ + 1 / b k)) -
          θ * ∑ k, Real.exp (a k - b k * (θ + 1 / b k)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    linarith

theorem yb_sf {m n : ℕ} (α β : Fin m → Fin n → ℝ) (c : Fin m → Fin m → Fin n → ℝ)
    (hβ : ∀ i k, 0 < β i k) (hc : ∀ i j k, 0 ≤ c i j k)
    (S : Fin m → Finset (Fin n)) (P : Fin m → Fin n → ℝ) (l : Fin m → Fin n → Fin m)
    (i : Fin m) :
    (∀ k ∈ MultiStoreAssort.SMR.Sbar S \ S i,
        pTilde P l i k ≤ (α i k - Real.log (vTilde α β c P l i k)) / β i k) ∧
      storeRev13 α β c S P l i ≤
        rev14 (α i) (β i) (MultiStoreAssort.SMR.Sbar S)
          (fun k => if k ∈ S i then P i k else (α i k - Real.log (vTilde α β c P l i k)) / β i k) := by
  have h1 : ∀ k ∈ MultiStoreAssort.SMR.Sbar S \ S i,
      pTilde P l i k ≤ (α i k - Real.log (vTilde α β c P l i k)) / β i k := by
    intro k _
    have e : Real.log (vTilde α β c P l i k) = α i k - β i k * P (l i k) k - c i (l i k) k := by
      unfold vTilde util; rw [Real.log_exp]
    rw [e, le_div_iff₀ (hβ i k)]
    unfold pTilde
    have := hc i (l i k) k
    nlinarith
  refine ⟨h1, ?_⟩
  have hsub : S i ⊆ MultiStoreAssort.SMR.Sbar S := by
    unfold MultiStoreAssort.SMR.Sbar
    exact Finset.le_sup (f := S) (Finset.mem_univ i)
  set Pn : Fin n → ℝ := fun k => if k ∈ S i then P i k else (α i k - Real.log (vTilde α β c P l i k)) / β i k with hPn
  have hv : ∀ k, 0 < vTilde α β c P l i k := fun k => Real.exp_pos _
  have hexp1 : ∀ k ∈ S i, Real.exp (α i k - β i k * Pn k) = vP α β P i k := by
    intro k hk
    simp only [hPn, if_pos hk]; rfl
  have hexp2 : ∀ k ∈ MultiStoreAssort.SMR.Sbar S \ S i,
      Real.exp (α i k - β i k * Pn k) = vTilde α β c P l i k := by
    intro k hk
    have hk' : k ∉ S i := (Finset.mem_sdiff.mp hk).2
    simp only [hPn, if_neg hk']
    have hb := (hβ i k).ne'
    have : α i k - β i k * ((α i k - Real.log (vTilde α β c P l i k)) / β i k) = Real.log (vTilde α β c P l i k) := by
      field_simp; ring
    rw [this, Real.exp_log (hv k)]
  have hnum1 : ∀ k ∈ S i, Pn k * Real.exp (α i k - β i k * Pn k) = P i k * vP α β P i k := by
    intro k hk
    rw [hexp1 k hk]; simp only [hPn, if_pos hk]
  have hnum2 : ∀ k ∈ MultiStoreAssort.SMR.Sbar S \ S i,
      pTilde P l i k * vTilde α β c P l i k ≤ Pn k * Real.exp (α i k - β i k * Pn k) := by
    intro k hk
    rw [hexp2 k hk]
    have hk' : k ∉ S i := (Finset.mem_sdiff.mp hk).2
    simp only [hPn, if_neg hk']
    exact mul_le_mul_of_nonneg_right (h1 k hk) (hv k).le
  have hD : ∑ k ∈ MultiStoreAssort.SMR.Sbar S, Real.exp (α i k - β i k * Pn k) =
      ∑ k ∈ S i, vP α β P i k + ∑ k ∈ MultiStoreAssort.SMR.Sbar S \ S i, vTilde α β c P l i k := by
    rw [← Finset.sum_sdiff hsub, add_comm]
    congr 1
    · exact Finset.sum_congr rfl hexp1
    · exact Finset.sum_congr rfl hexp2
  have hN : ∑ k ∈ MultiStoreAssort.SMR.Sbar S, Pn k * Real.exp (α i k - β i k * Pn k) =
      ∑ k ∈ S i, P i k * vP α β P i k + ∑ k ∈ MultiStoreAssort.SMR.Sbar S \ S i,
        Pn k * Real.exp (α i k - β i k * Pn k) := by
    rw [← Finset.sum_sdiff hsub, add_comm]
    congr 1
    exact Finset.sum_congr rfl hnum1
  have hDpos : 0 < 1 + ∑ k ∈ S i, vP α β P i k + ∑ k ∈ MultiStoreAssort.SMR.Sbar S \ S i, vTilde α β c P l i k := by
    have h1 : 0 ≤ ∑ k ∈ S i, vP α β P i k := Finset.sum_nonneg fun k _ => (Real.exp_pos _).le
    have h2 : 0 ≤ ∑ k ∈ MultiStoreAssort.SMR.Sbar S \ S i, vTilde α β c P l i k :=
      Finset.sum_nonneg fun k _ => (hv k).le
    linarith
  unfold storeRev13 rev14
  rw [hD, hN, ← add_assoc]
  apply div_le_div_of_nonneg_right _ hDpos.le
  have := Finset.sum_le_sum hnum2
  linarith

theorem solution {m n : ℕ} (lam : Fin m → ℝ) (α β : Fin m → Fin n → ℝ)
    (c : Fin m → Fin m → Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i) (hlam1 : ∑ i, lam i = 1)
    (hα : ∀ i k, 0 < α i k) (hβ : ∀ i k, 0 < β i k) (hc : ∀ i j k, 0 ≤ c i j k)
    (hcii : ∀ i k, c i i k = 0) (θ : Fin m → ℝ) (hθ : ∀ i, IsTheta (α i) (β i) (θ i)) :
    ∀ (S : Fin m → Finset (Fin n)) (P : Fin m → Fin n → ℝ) (l l' : Fin m → Fin n → Fin m),
      IsBestStore α β c P S l →
        rev13 lam α β c S P l ≤
          rev13 lam α β c (fun _ => Finset.univ) (fun i k => θ i + 1 / β i k) l' := by
  intro S P l l' hl
  have hrev : ∀ i, storeRev13 α β c (fun _ => Finset.univ) (fun i k => θ i + 1 / β i k) l' i = θ i := by
    intro i
    have h := (yb_single_store_optimum (α i) (β i) (hβ i) (θ i) (hθ i)).2
    have hs : MultiStoreAssort.SMR.Sbar (fun _ : Fin m => (Finset.univ : Finset (Fin n))) \ Finset.univ = ∅ :=
      Finset.sdiff_eq_empty_iff_subset.mpr (Finset.subset_univ _)
    unfold storeRev13
    rw [hs]
    simp only [Finset.sum_empty, add_zero]
    unfold rev14 at h
    simpa [vP] using h
  unfold rev13
  refine Finset.sum_le_sum fun i _ => ?_
  rw [hrev i]
  apply mul_le_mul_of_nonneg_left _ (hlam i)
  exact (yb_sf α β c hβ hc S P l i).2.trans
    ((yb_single_store_optimum (α i) (β i) (hβ i) (θ i) (hθ i)).1 _ _)
