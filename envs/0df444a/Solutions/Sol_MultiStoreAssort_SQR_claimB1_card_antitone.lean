-- Prove2me | solution 1 for MultiStoreAssort.SQR.claimB1_card_antitone
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T13:48:51.423113+00:00
-- url     : https://prove2.me/submissions/0c4407c0-5433-43ab-964e-b02ab0fbf22d

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
theorem exchange (β G P w y vj uk rj rk : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hG : 0 ≤ G)
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

open MultiStoreAssort.SQR in
/-- Every optimal solution of (8) is revenue-ordered within `S₂` (for `0 ≤ β < 1`). -/
theorem opt_ordered {n : ℕ} (r v : Fin n → ℝ) (β : ℝ) (S2 X : Finset (Fin n))
    (hr : StrictAnti r) (hrpos : ∀ k, 0 < r k) (hv : ∀ k, 0 < v k) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hXmem : X ⊆ S2) (hopt : ∀ T, T ⊆ S2 → MultiStoreAssort.SQR.rev8 r v β S2 T ≤ MultiStoreAssort.SQR.rev8 r v β S2 X) :
    IsRevOrderedWithin S2 X := by
  classical
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

end SQR2B2

open MultiStoreAssort.SQR in
theorem solution {n : ℕ} (r v : Fin n → ℝ) (S2 S' S'' : Finset (Fin n)) (β' β'' : ℝ)
    (hr : StrictAnti r) (hrpos : ∀ k, 0 < r k) (hv : ∀ k, 0 < v k)
    (hβ'' : 0 ≤ β'') (hββ : β'' ≤ β') (hβ' : β' < 1)
    (hS' : S' ⊆ S2) (huniq' : ∀ T : Finset (Fin n), T ⊆ S2 → T ≠ S' → rev8 r v β' S2 T < rev8 r v β' S2 S')
    (hS'' : S'' ⊆ S2)
    (huniq'' : ∀ T : Finset (Fin n), T ⊆ S2 → T ≠ S'' → rev8 r v β'' S2 T < rev8 r v β'' S2 S'') :
    S'.card ≤ S''.card := by
  classical
  have hopt' : ∀ T, T ⊆ S2 → rev8 r v β' S2 T ≤ rev8 r v β' S2 S' := by
    intro T hT; by_cases h : T = S'
    · rw [h]
    · exact (huniq' T hT h).le
  have hopt'' : ∀ T, T ⊆ S2 → rev8 r v β'' S2 T ≤ rev8 r v β'' S2 S'' := by
    intro T hT; by_cases h : T = S''
    · rw [h]
    · exact (huniq'' T hT h).le
  obtain ⟨J', hJ'⟩ := SQR2B2.opt_ordered r v β' S2 S' hr hrpos hv (by linarith) hβ' hS' hopt'
  obtain ⟨J'', hJ''⟩ := SQR2B2.opt_ordered r v β'' S2 S'' hr hrpos hv hβ'' (by linarith) hS'' hopt''
  by_contra hcard
  push Not at hcard
  -- S'' ⊊ S'
  have hsub : S'' ⊆ S' := by
    rcases le_total J'' J' with h | h
    · rw [hJ', hJ'']; intro x hx; simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, by omega⟩
    · exfalso
      have : S' ⊆ S'' := by rw [hJ', hJ'']; intro x hx; simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, by omega⟩
      have := Finset.card_le_card this; omega
  have hne : S'' ≠ S' := by rintro rfl; omega
  have a1 := huniq' S'' hS'' hne
  have a2 := huniq'' S' hS' (Ne.symm hne)
  -- the difference g_{β'} - g_{β''}
  have key : ∀ (β1 β2 : ℝ) (S : Finset (Fin n)), 0 ≤ β1 → 0 ≤ β2 →
      rev8 r v β1 S2 S - rev8 r v β2 S2 S =
        (β1 - β2) * Ws r v (S2 \ S) /
          ((1 + Vs v S + β1 * Vs v (S2 \ S)) * (1 + Vs v S + β2 * Vs v (S2 \ S))) := by
    intro β1 β2 S h1 h2
    unfold rev8
    have hV : 0 ≤ Vs v S := Finset.sum_nonneg (fun k _ => (hv k).le)
    have hy : 0 ≤ Vs v (S2 \ S) := Finset.sum_nonneg (fun k _ => (hv k).le)
    have e1 : 1 + Vs v S ≠ 0 := by positivity
    have e2 : 1 + Vs v S + β1 * Vs v (S2 \ S) ≠ 0 := by positivity
    have e3 : 1 + Vs v S + β2 * Vs v (S2 \ S) ≠ 0 := by positivity
    field_simp
    ring
  have k1 := key β' β'' S' (by linarith) hβ''
  have k2 := key β' β'' S'' (by linarith) hβ''
  -- f(S') > f(S'')
  have hgt : (β' - β'') * Ws r v (S2 \ S'') /
        ((1 + Vs v S'' + β' * Vs v (S2 \ S'')) * (1 + Vs v S'' + β'' * Vs v (S2 \ S''))) <
      (β' - β'') * Ws r v (S2 \ S') /
        ((1 + Vs v S' + β' * Vs v (S2 \ S')) * (1 + Vs v S' + β'' * Vs v (S2 \ S'))) := by
    rw [← k1, ← k2]; linarith
  -- but f is antitone along inclusion
  have hsd : S2 \ S' ⊆ S2 \ S'' := Finset.sdiff_subset_sdiff (le_refl S2) hsub
  have hW : Ws r v (S2 \ S') ≤ Ws r v (S2 \ S'') :=
    Finset.sum_le_sum_of_subset_of_nonneg hsd (fun k _ _ => (mul_pos (hrpos k) (hv k)).le)
  have hW0 : 0 ≤ Ws r v (S2 \ S') := Finset.sum_nonneg (fun k _ => (mul_pos (hrpos k) (hv k)).le)
  have hy' : Vs v (S2 \ S') ≤ Vs v (S2 \ S'') :=
    Finset.sum_le_sum_of_subset_of_nonneg hsd (fun k _ _ => (hv k).le)
  have hsum' : Vs v (S2 \ S') + Vs v S' = Vs v S2 := by unfold Vs; exact Finset.sum_sdiff hS'
  have hsum'' : Vs v (S2 \ S'') + Vs v S'' = Vs v S2 := by unfold Vs; exact Finset.sum_sdiff hS''
  have hy0 : 0 ≤ Vs v (S2 \ S') := Finset.sum_nonneg (fun k _ => (hv k).le)
  have hy0' : 0 ≤ Vs v (S2 \ S'') := Finset.sum_nonneg (fun k _ => (hv k).le)
  have hV0 : 0 ≤ Vs v S'' := Finset.sum_nonneg (fun k _ => (hv k).le)
  have hV0' : 0 ≤ Vs v S' := Finset.sum_nonneg (fun k _ => (hv k).le)
  set A := Vs v S2
  set y1 := Vs v (S2 \ S')
  set y2 := Vs v (S2 \ S'')
  set w1 := Ws r v (S2 \ S')
  set w2 := Ws r v (S2 \ S'')
  have hd1 : 1 + Vs v S'' + β' * y2 ≤ 1 + Vs v S' + β' * y1 := by nlinarith
  have hd2 : 1 + Vs v S'' + β'' * y2 ≤ 1 + Vs v S' + β'' * y1 := by nlinarith
  have p1 : 0 < 1 + Vs v S'' + β' * y2 := by nlinarith
  have p2 : 0 < 1 + Vs v S'' + β'' * y2 := by nlinarith
  have hden : (1 + Vs v S'' + β' * y2) * (1 + Vs v S'' + β'' * y2) ≤
      (1 + Vs v S' + β' * y1) * (1 + Vs v S' + β'' * y1) :=
    mul_le_mul hd1 hd2 p2.le (by linarith)
  have hle : (β' - β'') * w1 / ((1 + Vs v S' + β' * y1) * (1 + Vs v S' + β'' * y1)) ≤
      (β' - β'') * w2 / ((1 + Vs v S'' + β' * y2) * (1 + Vs v S'' + β'' * y2)) := by
    calc (β' - β'') * w1 / ((1 + Vs v S' + β' * y1) * (1 + Vs v S' + β'' * y1))
        ≤ (β' - β'') * w1 / ((1 + Vs v S'' + β' * y2) * (1 + Vs v S'' + β'' * y2)) :=
          div_le_div_of_nonneg_left (mul_nonneg (by linarith) hW0) (mul_pos p1 p2) hden
      _ ≤ (β' - β'') * w2 / ((1 + Vs v S'' + β' * y2) * (1 + Vs v S'' + β'' * y2)) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hW (by linarith)) (mul_pos p1 p2).le
  linarith
