-- Prove2me | solution 1 for MultiStoreAssort.SQR.lemmaB2_revenue_ordered_within
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T13:47:06.635781+00:00
-- url     : https://prove2.me/submissions/577814fd-49f3-4cda-bb58-db425a45510b

import Mathlib
import Definitions.Def_MultiStoreAssort_SQR_Model

namespace SQR2B2

/-- Revenue of (8) written in terms of `G = W(S₁)`, `P = 1 + V(S₁)`, `w = W(S₂∖S₁)`, `y = V(S₂∖S₁)`. -/
noncomputable def h (β G P w y : ℝ) : ℝ := G / P + β * w / (P * (P + β * y))

/-- Moving a product with revenue `r` and attraction `t` into `S₁` (`t > 0`) or out of `S₁`
(`t < 0`): the change in revenue factors as a positive/negative multiple of `r - θ`. -/
theorem move_identity (β G P w y t r : ℝ) (hP : 0 < P) (hQ : 0 < P + β * y) (hPt : 0 < P + t)
    (hQs : 0 < P + β * y + (1 - β) * t) (hQb : 0 < P + β * y - β + (1 - β) * t) :
    h β (G + r * t) (P + t) (w - r * t) (y - t) - h β G P w y =
    t * (P + β * y + (1 - β) * t - β) / ((P + t) * (P + β * y + (1 - β) * t)) *
      (r - ((G * (P + β * y) / P + β * w * ((1 - β) * P + (P + β * y)) / (P * (P + β * y))) +
        (G / P + β * w / (P * (P + β * y))) * ((1 - β) * t)) / (P + β * y - β + (1 - β) * t)) := by
  unfold h
  have h1 : P + t + β * (y - t) = P + β * y + (1 - β) * t := by ring
  rw [h1]
  set Q := P + β * y with hQdef
  set s := (1 - β) * t with hsdef
  have e1 : (P + t) ≠ 0 := hPt.ne'
  have e2 : Q + s ≠ 0 := hQs.ne'
  have e3 : Q - β + s ≠ 0 := hQb.ne'
  have e4 : P ≠ 0 := hP.ne'
  have e5 : Q ≠ 0 := hQ.ne'
  field_simp
  rw [hsdef]
  ring

/-- The exchange inequality behind Lemma B.2: if neither adding product `j` nor removing product
`k` improves (8), then `r_j ≤ r_k`. -/
theorem exchange (β G P w y vj uk rj rk : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hG : 0 ≤ G)
    (hw : 0 ≤ w) (hvj : 0 < vj) (huk : 0 < uk) (hPu : 1 ≤ P - uk) (hyv : vj ≤ y)
    (h1 : h β (G + rj * vj) (P + vj) (w - rj * vj) (y - vj) ≤ h β G P w y)
    (h2 : h β (G + rk * (-uk)) (P + (-uk)) (w - rk * (-uk)) (y - (-uk)) ≤ h β G P w y) :
    rj ≤ rk := by
  have hy : 0 ≤ y := by linarith
  have hP : 0 < P := by linarith
  have hQ : 0 < P + β * y := by nlinarith
  set Q := P + β * y with hQdef
  set g := G / P + β * w / (P * Q)
  set N0 := G * Q / P + β * w * ((1 - β) * P + Q) / (P * Q)
  -- N0 - g (Q - β) ≥ 0
  have hN : 0 ≤ N0 - g * (Q - β) := by
    have : N0 - g * (Q - β) = β * G / P + β * w * ((1 - β) * P + β) / (P * Q) := by
      simp only [N0, g]; field_simp; ring
    rw [this]
    have : 0 ≤ (1 - β) * P + β := by nlinarith
    positivity
  set s1 := (1 - β) * vj
  set s2 := (1 - β) * (-uk)
  have hD1 : 0 < Q - β + s1 := by
    have : 0 ≤ s1 := by positivity
    nlinarith
  have hD2 : 0 < Q - β + s2 := by
    simp only [s2, hQdef]; nlinarith
  -- adding j
  have i1 := move_identity β G P w y vj rj hP hQ (by linarith) (by nlinarith) hD1
  have i2 := move_identity β G P w y (-uk) rk hP hQ (by linarith) (by simp only [hQdef] at hD2 ⊢; nlinarith) hD2
  set θ1 := (N0 + g * s1) / (Q - β + s1)
  set θ2 := (N0 + g * s2) / (Q - β + s2)
  have hc1 : 0 < vj * (Q + s1 - β) / ((P + vj) * (Q + s1)) := by
    have : 0 < Q + s1 := by linarith
    have : 0 < Q + s1 - β := by linarith
    have : 0 < P + vj := by linarith
    positivity
  have hc2 : 0 < uk * (Q + s2 - β) / ((P + -uk) * (Q + s2)) := by
    have : 0 < Q + s2 := by linarith
    have : 0 < Q + s2 - β := by linarith
    have : 0 < P + -uk := by linarith
    positivity
  have hr1 : rj ≤ θ1 := by
    have : vj * (Q + s1 - β) / ((P + vj) * (Q + s1)) * (rj - θ1) ≤ 0 := by
      rw [← i1]; linarith
    by_contra hc; push Not at hc
    have := mul_pos hc1 (sub_pos.mpr hc); linarith
  have hr2 : θ2 ≤ rk := by
    have e : -uk * (Q + s2 - β) / ((P + -uk) * (Q + s2)) * (rk - θ2) =
        -(uk * (Q + s2 - β) / ((P + -uk) * (Q + s2)) * (rk - θ2)) := by ring
    have : -uk * (Q + s2 - β) / ((P + -uk) * (Q + s2)) * (rk - θ2) ≤ 0 := by
      rw [← i2]; linarith
    rw [e] at this
    by_contra hc; push Not at hc
    have := mul_neg_of_pos_of_neg hc2 (sub_neg.mpr hc); linarith
  have hθ : θ1 ≤ θ2 := by
    rw [div_le_div_iff₀ hD1 hD2]
    have hs : s2 ≤ s1 := by simp only [s1, s2]; nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) hN]
  linarith

end SQR2B2

open MultiStoreAssort.SQR in
theorem solution {n : ℕ} (r v : Fin n → ℝ) (β : ℝ) (S2 : Finset (Fin n))
    (hr : StrictAnti r) (hrpos : ∀ k, 0 < r k) (hv : ∀ k, 0 < v k) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ S1 : Finset (Fin n), S1 ⊆ S2 ∧ IsRevOrderedWithin S2 S1 ∧
      ∀ T : Finset (Fin n), T ⊆ S2 → rev8 r v β S2 T ≤ rev8 r v β S2 S1 := by
  classical
  obtain ⟨X, hXmem, hXmax⟩ := Finset.exists_max_image S2.powerset (fun T => rev8 r v β S2 T)
    ⟨∅, Finset.empty_mem_powerset _⟩
  rw [Finset.mem_powerset] at hXmem
  have hopt : ∀ T, T ⊆ S2 → rev8 r v β S2 T ≤ rev8 r v β S2 X :=
    fun T hT => hXmax T (Finset.mem_powerset.mpr hT)
  -- every product outside X has a lower revenue (higher index) than every product inside X
  have hord : ∀ j ∈ S2, j ∉ X → ∀ k ∈ X, k < j := by
    intro j hjS hjX k hkX
    by_contra hlt
    push Not at hlt
    have hjk : j < k := lt_of_le_of_ne hlt (by rintro rfl; exact hjX hkX)
    have hrjk : r k < r j := hr hjk
    set G := Ws r v X
    set P := 1 + Vs v X
    set w := Ws r v (S2 \ X)
    set y := Vs v (S2 \ X)
    have hG : 0 ≤ G := Finset.sum_nonneg (fun k _ => (mul_pos (hrpos k) (hv k)).le)
    have hw : 0 ≤ w := Finset.sum_nonneg (fun k _ => (mul_pos (hrpos k) (hv k)).le)
    have hjd : j ∈ S2 \ X := Finset.mem_sdiff.mpr ⟨hjS, hjX⟩
    have hyv : v j ≤ y := Finset.single_le_sum (f := v) (fun k _ => (hv k).le) hjd
    have hPu : 1 ≤ P - v k := by
      have : Vs v X = v k + Vs v (X.erase k) := by
        unfold Vs; exact (Finset.add_sum_erase X v hkX).symm
      have : 0 ≤ Vs v (X.erase k) := Finset.sum_nonneg (fun k _ => (hv k).le)
      simp only [P]; linarith
    -- adding j does not help
    have h1 := hopt (insert j X) (Finset.insert_subset hjS hXmem)
    have e1 : S2 \ insert j X = (S2 \ X).erase j := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]; tauto
    have h1' : SQR2B2.h β (G + r j * v j) (P + v j) (w - r j * v j) (y - v j) ≤ SQR2B2.h β G P w y := by
      have l : rev8 r v β S2 (insert j X) = SQR2B2.h β (G + r j * v j) (P + v j) (w - r j * v j) (y - v j) := by
        unfold rev8 SQR2B2.h
        have a1 : Ws r v (insert j X) = G + r j * v j := by
          unfold Ws; rw [Finset.sum_insert hjX]; simp only [G, Ws]; ring
        have a2 : 1 + Vs v (insert j X) = P + v j := by
          unfold Vs; rw [Finset.sum_insert hjX]; simp only [P, Vs]; ring
        have a3 : Ws r v (S2 \ insert j X) = w - r j * v j := by
          rw [e1]; unfold Ws; rw [Finset.sum_erase_eq_sub hjd]; rfl
        have a4 : Vs v (S2 \ insert j X) = y - v j := by
          rw [e1]; unfold Vs; rw [Finset.sum_erase_eq_sub hjd]; rfl
        rw [a1, a2, a3, a4]
      have r0 : rev8 r v β S2 X = SQR2B2.h β G P w y := rfl
      rw [← l, ← r0]; exact h1
    -- removing k does not help
    have h2 := hopt (X.erase k) ((Finset.erase_subset k X).trans hXmem)
    have hkd : k ∉ S2 \ X := fun h => (Finset.mem_sdiff.mp h).2 hkX
    have e2 : S2 \ X.erase k = insert k (S2 \ X) := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases hx : x = k
        · left; exact hx
        · right; exact ⟨h1, fun h => h2 ⟨hx, h⟩⟩
      · rintro (h | ⟨h1, h2⟩)
        · subst h; exact ⟨hXmem hkX, fun h => h.1 rfl⟩
        · exact ⟨h1, fun h => h2 h.2⟩
    have h2' : SQR2B2.h β (G + r k * (-v k)) (P + (-v k)) (w - r k * (-v k)) (y - (-v k)) ≤
        SQR2B2.h β G P w y := by
      have l : rev8 r v β S2 (X.erase k) =
          SQR2B2.h β (G + r k * (-v k)) (P + (-v k)) (w - r k * (-v k)) (y - (-v k)) := by
        unfold rev8 SQR2B2.h
        have a1 : Ws r v (X.erase k) = G + r k * (-v k) := by
          unfold Ws; rw [Finset.sum_erase_eq_sub hkX]; simp only [G, Ws]; ring
        have a2 : 1 + Vs v (X.erase k) = P + (-v k) := by
          unfold Vs; rw [Finset.sum_erase_eq_sub hkX]; simp only [P, Vs]; ring
        have a3 : Ws r v (S2 \ X.erase k) = w - r k * (-v k) := by
          rw [e2]; unfold Ws; rw [Finset.sum_insert hkd]; simp only [w, Ws]; ring
        have a4 : Vs v (S2 \ X.erase k) = y - (-v k) := by
          rw [e2]; unfold Vs; rw [Finset.sum_insert hkd]; simp only [y, Vs]; ring
        rw [a1, a2, a3, a4]
      have r0 : rev8 r v β S2 X = SQR2B2.h β G P w y := rfl
      rw [← l, ← r0]; exact h2
    have := SQR2B2.exchange β G P w y (v j) (v k) (r j) (r k) hβ0 hβ1 hG hw (hv j) (hv k) hPu hyv
      h1' h2'
    linarith
  refine ⟨X, hXmem, ?_, hopt⟩
  refine ⟨X.sup (fun k => k.val + 1), ?_⟩
  ext x
  simp only [Finset.mem_filter]
  constructor
  · intro hx
    refine ⟨hXmem hx, ?_⟩
    have := Finset.le_sup (f := fun k : Fin n => k.val + 1) hx
    omega
  · rintro ⟨hxS, hxlt⟩
    by_contra hxX
    obtain ⟨k, hkX, hk⟩ := Finset.exists_mem_eq_sup X
      (by by_contra he; rw [Finset.not_nonempty_iff_eq_empty] at he; rw [he] at hxlt; simp at hxlt)
      (fun k : Fin n => k.val + 1)
    rw [hk] at hxlt
    have := hord x hxS hxX k hkX
    rw [Fin.lt_def] at this
    omega
