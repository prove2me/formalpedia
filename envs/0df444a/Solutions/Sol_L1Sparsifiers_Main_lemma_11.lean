-- Prove2me | solution 1 for L1Sparsifiers.Main.lemma_11
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:18:17.455829+00:00
-- url     : https://prove2.me/submissions/5fd528a8-9e8c-4241-b98f-d95483a938be

import Definitions.Def_PSDPolyApprox_lpNorm

open PSDPolyApprox

namespace AuxLemma11

lemma holder_cube {m : ℕ} (f : Cube m → ℝ) (p : ℝ) (hp1 : 1 ≤ p) (hp2 : p < 2) :
    expect (fun x => |f x| ^ p) ≤
      (expect (fun x => |f x| ^ (2 : ℝ))) ^ (p / 2) *
        (expect (fun x => if f x ≠ 0 then (1 : ℝ) else 0)) ^ ((2 - p) / 2) := by
  have hp0 : 0 < p := by linarith
  have h2mp : 0 < 2 - p := by linarith
  set q : ℝ := 2 / p
  set q' : ℝ := 2 / (2 - p)
  have hq1 : 1 < q := by
    rw [one_lt_div hp0]
    exact hp2
  have hconj : q.HolderConjugate q' := by
    rw [Real.holderConjugate_iff]
    refine ⟨hq1, ?_⟩
    simp only [q, q']
    field_simp
    ring
  let u : Cube m → ℝ := fun x => |f x| ^ p
  let v : Cube m → ℝ := fun x => if f x ≠ 0 then (1 : ℝ) else 0
  have huv_eq : ∀ x : Cube m, |f x| ^ p = u x * v x := by
    intro x
    simp only [u, v]
    by_cases hx : f x = 0
    · simp [hx, Real.zero_rpow hp0.ne']
    · simp [hx]
  have hsum_le : ∑ x : Cube m, |f x| ^ p ≤
      (∑ x : Cube m, |u x| ^ q) ^ (1 / q) * (∑ x : Cube m, |v x| ^ q') ^ (1 / q') := by
    calc ∑ x : Cube m, |f x| ^ p
        = ∑ x ∈ (Finset.univ : Finset (Cube m)), u x * v x := by
            refine Finset.sum_congr rfl (fun x _ => huv_eq x)
      _ ≤ (∑ x ∈ (Finset.univ : Finset (Cube m)), |u x| ^ q) ^ (1 / q) *
            (∑ x ∈ (Finset.univ : Finset (Cube m)), |v x| ^ q') ^ (1 / q') :=
            Real.inner_le_Lp_mul_Lq Finset.univ u v hconj
  have hu_pow : ∀ x : Cube m, |u x| ^ q = |f x| ^ (2 : ℝ) := by
    intro x
    have hnn : 0 ≤ |f x| ^ p := Real.rpow_nonneg (abs_nonneg _) _
    rw [abs_of_nonneg hnn, ← Real.rpow_mul (abs_nonneg _)]
    congr 1
    simp only [q]
    field_simp
  have hv_pow : ∀ x : Cube m, |v x| ^ q' = v x := by
    intro x
    have hq'0 : 0 < q' := by positivity
    simp only [v]
    by_cases hx : f x = 0
    · simp [hx, Real.zero_rpow hq'0.ne']
    · simp [hx]
  have h1q : 1 / q = p / 2 := by simp only [q]; field_simp
  have h1q' : 1 / q' = (2 - p) / 2 := by simp only [q']; field_simp
  let w : ℝ := ((2 : ℝ) ^ m)⁻¹
  have hw0 : 0 ≤ w := by positivity
  have hw_split : w = w ^ (p / 2) * w ^ ((2 - p) / 2) := by
    rw [← Real.rpow_add (by positivity : (0 : ℝ) < ((2 : ℝ) ^ m)⁻¹)]
    have : p / 2 + (2 - p) / 2 = (1 : ℝ) := by ring
    rw [this, Real.rpow_one]
  unfold expect
  change w * ∑ x : Cube m, |f x| ^ p ≤
    (w * ∑ x : Cube m, |f x| ^ (2 : ℝ)) ^ (p / 2) * (w * ∑ x : Cube m, v x) ^ ((2 - p) / 2)
  have hsum_u_nn : 0 ≤ ∑ x : Cube m, |f x| ^ (2 : ℝ) :=
    Finset.sum_nonneg (fun x _ => Real.rpow_nonneg (abs_nonneg _) _)
  have hsum_v_nn : 0 ≤ ∑ x : Cube m, v x :=
    Finset.sum_nonneg (fun x _ => by simp only [v]; split_ifs <;> norm_num)
  calc w * ∑ x : Cube m, |f x| ^ p
      ≤ w * ((∑ x : Cube m, |u x| ^ q) ^ (1 / q) * (∑ x : Cube m, |v x| ^ q') ^ (1 / q')) :=
          mul_le_mul_of_nonneg_left hsum_le hw0
    _ = (w ^ (p / 2) * w ^ ((2 - p) / 2)) *
          ((∑ x : Cube m, |f x| ^ (2 : ℝ)) ^ (p / 2) * (∑ x : Cube m, v x) ^ ((2 - p) / 2)) := by
          rw [← hw_split, h1q, h1q']
          simp_rw [hu_pow, hv_pow]
    _ = (w ^ (p / 2) * (∑ x : Cube m, |f x| ^ (2 : ℝ)) ^ (p / 2)) *
          (w ^ ((2 - p) / 2) * (∑ x : Cube m, v x) ^ ((2 - p) / 2)) := by ring
    _ = (w * ∑ x : Cube m, |f x| ^ (2 : ℝ)) ^ (p / 2) *
          (w * ∑ x : Cube m, v x) ^ ((2 - p) / 2) := by
          rw [← Real.mul_rpow hw0 hsum_u_nn, ← Real.mul_rpow hw0 hsum_v_nn]

end AuxLemma11

theorem solution {m : ℕ} (f : Cube m → ℝ) (p : ℝ) (hp1 : 1 ≤ p) (hp2 : p < 2) :
    lpNorm p f ≤
      (expect (fun x => if f x ≠ 0 then (1 : ℝ) else 0)) ^ (1 / p - 1 / 2) * lpNorm 2 f := by
  have hp0 : 0 < p := by linarith
  have h1p_nn : 0 ≤ 1 / p := by positivity
  have h_holder := AuxLemma11.holder_cube f p hp1 hp2
  have hexp_p_nn : 0 ≤ expect (fun x => |f x| ^ p) := by
    unfold expect
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _))
  have hexp_2_nn : 0 ≤ expect (fun x => |f x| ^ (2 : ℝ)) := by
    unfold expect
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _))
  have hα_nn : 0 ≤ expect (fun x => if f x ≠ 0 then (1 : ℝ) else 0) := by
    unfold expect
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num))
  unfold lpNorm
  calc (expect (fun x => |f x| ^ p)) ^ (1 / p)
      ≤ ((expect (fun x => |f x| ^ (2 : ℝ))) ^ (p / 2) *
          (expect (fun x => if f x ≠ 0 then (1 : ℝ) else 0)) ^ ((2 - p) / 2)) ^ (1 / p) :=
          Real.rpow_le_rpow hexp_p_nn h_holder h1p_nn
    _ = ((expect (fun x => |f x| ^ (2 : ℝ))) ^ (p / 2)) ^ (1 / p) *
          ((expect (fun x => if f x ≠ 0 then (1 : ℝ) else 0)) ^ ((2 - p) / 2)) ^ (1 / p) :=
          Real.mul_rpow (Real.rpow_nonneg hexp_2_nn _) (Real.rpow_nonneg hα_nn _)
    _ = (expect (fun x => |f x| ^ (2 : ℝ))) ^ ((p / 2) * (1 / p)) *
          (expect (fun x => if f x ≠ 0 then (1 : ℝ) else 0)) ^ (((2 - p) / 2) * (1 / p)) := by
          rw [← Real.rpow_mul hexp_2_nn, ← Real.rpow_mul hα_nn]
    _ = (expect (fun x => if f x ≠ 0 then (1 : ℝ) else 0)) ^ (1 / p - 1 / 2) *
          (expect (fun x => |f x| ^ (2 : ℝ))) ^ (1 / (2 : ℝ)) := by
          have e1 : (p / 2) * (1 / p) = 1 / (2 : ℝ) := by field_simp
          have e2 : ((2 - p) / 2) * (1 / p) = 1 / p - 1 / 2 := by field_simp
          rw [e1, e2, mul_comm]
