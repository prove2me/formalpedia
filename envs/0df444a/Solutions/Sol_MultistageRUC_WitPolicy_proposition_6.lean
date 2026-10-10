-- Prove2me | solution 1 for MultistageRUC.WitPolicy.proposition_6
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T18:20:16.357254+00:00
-- url     : https://prove2.me/submissions/5e3da6e9-f3ea-4f0d-b7f7-9c4eda3272e1

import Mathlib
import Definitions.Def_MultistageRUC_WitPolicy_Setting

namespace RRAux_MultistageRUC_WitPolicy_proposition_6

open MultistageRUC.WitPolicy

lemma aff_lo {lo c p a a1 a2 : ℝ} (h1 : lo ≤ c + p * a1) (h2 : lo ≤ c + p * a2)
    (ha1 : a1 ≤ a) (ha2 : a ≤ a2) : lo ≤ c + p * a := by
  rcases le_total 0 p with hp | hp
  · have := mul_le_mul_of_nonneg_left ha1 hp; linarith
  · have := mul_le_mul_of_nonpos_left ha2 hp; linarith

lemma aff_hi {hi c p a a1 a2 : ℝ} (h1 : c + p * a1 ≤ hi) (h2 : c + p * a2 ≤ hi)
    (ha1 : a1 ≤ a) (ha2 : a ≤ a2) : c + p * a ≤ hi := by
  rcases le_total 0 p with hp | hp
  · have := mul_le_mul_of_nonneg_left ha2 hp; linarith
  · have := mul_le_mul_of_nonpos_left ha1 hp; linarith

lemma aff2_lo {lo c p r a b a1 a2 b1 b2 : ℝ}
    (h11 : lo ≤ c + p * a1 + r * b1) (h12 : lo ≤ c + p * a1 + r * b2)
    (h21 : lo ≤ c + p * a2 + r * b1) (h22 : lo ≤ c + p * a2 + r * b2)
    (ha1 : a1 ≤ a) (ha2 : a ≤ a2) (hb1 : b1 ≤ b) (hb2 : b ≤ b2) :
    lo ≤ c + p * a + r * b := by
  have e1 : lo ≤ (c + r * b1) + p * a := aff_lo (by linarith) (by linarith) ha1 ha2
  have e2 : lo ≤ (c + r * b2) + p * a := aff_lo (by linarith) (by linarith) ha1 ha2
  have := aff_lo (lo := lo) (c := c + p * a) (p := r) (by linarith) (by linarith) hb1 hb2
  linarith

lemma aff2_hi {hi c p r a b a1 a2 b1 b2 : ℝ}
    (h11 : c + p * a1 + r * b1 ≤ hi) (h12 : c + p * a1 + r * b2 ≤ hi)
    (h21 : c + p * a2 + r * b1 ≤ hi) (h22 : c + p * a2 + r * b2 ≤ hi)
    (ha1 : a1 ≤ a) (ha2 : a ≤ a2) (hb1 : b1 ≤ b) (hb2 : b ≤ b2) :
    c + p * a + r * b ≤ hi := by
  have e1 : (c + r * b1) + p * a ≤ hi := aff_hi (by linarith) (by linarith) ha1 ha2
  have e2 : (c + r * b2) + p * a ≤ hi := aff_hi (by linarith) (by linarith) ha1 ha2
  have := aff_hi (hi := hi) (c := c + p * a) (p := r) (by linarith) (by linarith) hb1 hb2
  linarith

end RRAux_MultistageRUC_WitPolicy_proposition_6

open RRAux_MultistageRUC_WitPolicy_proposition_6 in
open MultistageRUC.WitPolicy in
theorem solution {Ng Nd T : ℕ}
    (pmin pmax : Fin Ng → ℝ) (RD RU SD SU : Fin Ng → Fin T → ℝ)
    (x0 p0 : Fin Ng → ℝ) (x u v : Fin Ng → Fin T → ℝ) (w W : Fin Ng → Fin T → ℝ)
    (dbar dhat : Fin T → Fin Nd → ℝ) (Γ : ℝ)
    (dmax dmin : Fin T → Fin Nd → ℝ)
    (hmax : IsMaxLoad (MultistageRUC.Equiv.uncSet dbar dhat Γ) dmax)
    (hmin : IsMinLoad (MultistageRUC.Equiv.uncSet dbar dhat Γ) dmin) :
    ∀ i t,
      (GenLimits pmin pmax x w W (MultistageRUC.Equiv.uncSet dbar dhat Γ) i t ↔
        GenLimits pmin pmax x w W {dmin, dmax} i t) ∧
      ((RampDown RD SD x v p0 w W (MultistageRUC.Equiv.uncSet dbar dhat Γ) i t ↔
          RampDown RD SD x v p0 w W {dmin, dmax, dminmax dmin dmax t, dmaxmin dmin dmax t} i t) ∧
        (RampUp RU SU x0 x u p0 w W (MultistageRUC.Equiv.uncSet dbar dhat Γ) i t ↔
          RampUp RU SU x0 x u p0 w W {dmin, dmax, dminmax dmin dmax t, dmaxmin dmin dmax t} i t)) := by
  intro i t
  have hdmin := hmin.1
  have hdmax := hmax.1
  have hmix : dminmax dmin dmax t ∈ MultistageRUC.Equiv.uncSet dbar dhat Γ ∧
      dmaxmin dmin dmax t ∈ MultistageRUC.Equiv.uncSet dbar dhat Γ := by
    simp only [MultistageRUC.Equiv.uncSet, Set.mem_univ_pi] at hdmin hdmax ⊢
    refine ⟨fun s => ?_, fun s => ?_⟩
    · by_cases hs : s < t <;> simp [dminmax, hs, hdmin s, hdmax s]
    · by_cases hs : s < t <;> simp [dmaxmin, hs, hdmin s, hdmax s]
  have sub2 : ({dmin, dmax} : Set (Fin T → Fin Nd → ℝ)) ⊆
      MultistageRUC.Equiv.uncSet dbar dhat Γ := by
    simp [Set.insert_subset_iff, hdmin, hdmax]
  have sub4 : ({dmin, dmax, dminmax dmin dmax t, dmaxmin dmin dmax t} :
      Set (Fin T → Fin Nd → ℝ)) ⊆ MultistageRUC.Equiv.uncSet dbar dhat Γ := by
    simp [Set.insert_subset_iff, hdmin, hdmax, hmix.1, hmix.2]
  have m1 : dmin ∈ ({dmin, dmax, dminmax dmin dmax t, dmaxmin dmin dmax t} :
      Set (Fin T → Fin Nd → ℝ)) := by simp
  have m2 : dmax ∈ ({dmin, dmax, dminmax dmin dmax t, dmaxmin dmin dmax t} :
      Set (Fin T → Fin Nd → ℝ)) := by simp
  have m3 : dminmax dmin dmax t ∈ ({dmin, dmax, dminmax dmin dmax t, dmaxmin dmin dmax t} :
      Set (Fin T → Fin Nd → ℝ)) := by simp
  have m4 : dmaxmin dmin dmax t ∈ ({dmin, dmax, dminmax dmin dmax t, dmaxmin dmin dmax t} :
      Set (Fin T → Fin Nd → ℝ)) := by simp
  refine ⟨⟨fun h d hd => h d (sub2 hd), fun h d hd => ?_⟩,
    ⟨fun h d hd => h d (sub4 hd), fun h d hd => ?_⟩,
    ⟨fun h d hd => h d (sub4 hd), fun h d hd => ?_⟩⟩
  · -- generation limits
    have h1 := h dmin (by simp)
    have h2 := h dmax (by simp)
    have l1 := hmin.2 d hd t
    have l2 := hmax.2 d hd t
    simp only [witDispatch] at h1 h2 ⊢
    exact ⟨aff_lo h1.1 h2.1 l1 l2, aff_hi h1.2 h2.2 l1 l2⟩
  · -- ramp down
    have h1 := h dmin m1
    have h2 := h dmax m2
    have h3 := h _ m3
    have h4 := h _ m4
    have l1 := hmin.2 d hd t
    have l2 := hmax.2 d hd t
    by_cases h0 : t.val = 0
    · simp only [witPrev, h0, dif_pos, witDispatch, ge_iff_le] at h1 h2 ⊢
      have := aff_lo (lo := -RD i t * x i t - SD i t * v i t) (c := w i t - p0 i) (p := W i t)
        (by linarith) (by linarith) l1 l2
      linarith
    · have hlt : (⟨t.val - 1, by omega⟩ : Fin T) < t := by
        rw [Fin.lt_def]; simp; omega
      have k1 := hmin.2 d hd ⟨t.val - 1, by omega⟩
      have k2 := hmax.2 d hd ⟨t.val - 1, by omega⟩
      have e3a : totalLoad (dminmax dmin dmax t) t = totalLoad dmax t := by
        simp [totalLoad, dminmax]
      have e3b : totalLoad (dminmax dmin dmax t) ⟨t.val - 1, by omega⟩ =
          totalLoad dmin ⟨t.val - 1, by omega⟩ := by
        simp only [totalLoad, dminmax, if_pos hlt]
      have e4a : totalLoad (dmaxmin dmin dmax t) t = totalLoad dmin t := by
        simp [totalLoad, dmaxmin]
      have e4b : totalLoad (dmaxmin dmin dmax t) ⟨t.val - 1, by omega⟩ =
          totalLoad dmax ⟨t.val - 1, by omega⟩ := by
        simp only [totalLoad, dmaxmin, if_pos hlt]
      simp only [witPrev, h0, dif_neg, not_false_eq_true, witDispatch, ge_iff_le] at h1 h2 h3 h4 ⊢
      rw [e3a, e3b] at h3
      rw [e4a, e4b] at h4
      have := aff2_lo (lo := -RD i t * x i t - SD i t * v i t)
        (c := w i t - w i ⟨t.val - 1, by omega⟩) (p := W i t)
        (r := -W i ⟨t.val - 1, by omega⟩)
        (by linarith) (by linarith) (by linarith) (by linarith) l1 l2 k1 k2
      linarith
  · -- ramp up
    have h1 := h dmin m1
    have h2 := h dmax m2
    have h3 := h _ m3
    have h4 := h _ m4
    have l1 := hmin.2 d hd t
    have l2 := hmax.2 d hd t
    by_cases h0 : t.val = 0
    · simp only [witPrev, h0, dif_pos, witDispatch] at h1 h2 ⊢
      have := aff_hi (hi := RU i t * prevCommit x0 x i t + SU i t * u i t)
        (c := w i t - p0 i) (p := W i t) (by linarith) (by linarith) l1 l2
      linarith
    · have hlt : (⟨t.val - 1, by omega⟩ : Fin T) < t := by
        rw [Fin.lt_def]; simp; omega
      have k1 := hmin.2 d hd ⟨t.val - 1, by omega⟩
      have k2 := hmax.2 d hd ⟨t.val - 1, by omega⟩
      have e3a : totalLoad (dminmax dmin dmax t) t = totalLoad dmax t := by
        simp [totalLoad, dminmax]
      have e3b : totalLoad (dminmax dmin dmax t) ⟨t.val - 1, by omega⟩ =
          totalLoad dmin ⟨t.val - 1, by omega⟩ := by
        simp only [totalLoad, dminmax, if_pos hlt]
      have e4a : totalLoad (dmaxmin dmin dmax t) t = totalLoad dmin t := by
        simp [totalLoad, dmaxmin]
      have e4b : totalLoad (dmaxmin dmin dmax t) ⟨t.val - 1, by omega⟩ =
          totalLoad dmax ⟨t.val - 1, by omega⟩ := by
        simp only [totalLoad, dmaxmin, if_pos hlt]
      simp only [witPrev, h0, dif_neg, not_false_eq_true, witDispatch] at h1 h2 h3 h4 ⊢
      rw [e3a, e3b] at h3
      rw [e4a, e4b] at h4
      have := aff2_hi (hi := RU i t * prevCommit x0 x i t + SU i t * u i t)
        (c := w i t - w i ⟨t.val - 1, by omega⟩) (p := W i t)
        (r := -W i ⟨t.val - 1, by omega⟩)
        (by linarith) (by linarith) (by linarith) (by linarith) l1 l2 k1 k2
      linarith

#print axioms solution
