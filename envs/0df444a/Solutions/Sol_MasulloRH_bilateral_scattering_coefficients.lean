-- Prove2me | solution 1 for MasulloRH.bilateral_scattering_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T03:07:00.324527+00:00
-- url     : https://prove2.me/submissions/10c00848-cfa4-44ae-97d2-93af2b444d6a

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
section

namespace MasulloScatter

theorem geometric_ray {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    HasSum (fun n : ℕ => q^n) (1/(1-q)) := by
  simpa only [one_div] using hasSum_geometric_of_lt_one hq₀ hq₁

theorem first_moment_geometric_ray {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    HasSum (fun n : ℕ => (n:ℝ)*q^n) (q/(1-q)^2) :=
  hasSum_coe_mul_geometric_of_norm_lt_one (by simpa only [Real.norm_eq_abs, abs_of_nonneg hq₀] using hq₁)

theorem affine_geometric_ray (q c d : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    HasSum (fun n : ℕ => (d+(n:ℝ))*c*q^n) (d*c/(1-q) + c*q/(1-q)^2) := by
  convert! ((geometric_ray hq₀ hq₁).mul_left (d*c)).add
    ((first_moment_geometric_ray hq₀ hq₁).mul_left c) using 1
  · funext n; ring
  · ring

end MasulloScatter
end

section

namespace MasulloScatter

private noncomputable def b (r : ℝ) (j : ℤ) : ℝ :=
  if j = -1 then -r else if 0 ≤ j then (1-r^2)*r^j.toNat else 0

private theorem b_nat (r : ℝ) (n : ℕ) : b r n = (1-r^2)*r^n := by
  simp [b,show (n:ℤ)≠ -1 by omega]

private theorem hasSum_nat_and_boundary (f : ℤ → ℝ) (a : ℝ)
    (hf : HasSum (fun n : ℕ => f n) a) (hz : ∀ k : ℤ, k < -1 → f k=0) :
    HasSum f (a + f (-1)) := by
  apply hf.of_nat_of_neg_add_one
  convert hasSum_ite_eq (0:ℕ) (f (-1)) using 1
  funext n
  cases n with
  | zero => simp
  | succ n => rw [if_neg (by omega),hz _ (by omega)]

private theorem positive_lag (r : ℝ) (hr : 0 < r) (hr1 : r<1) (n : ℕ) :
    HasSum (fun j : ℤ => b r (j+n)*b r j) (if n=0 then 1 else 0) ∧
    HasSum (fun j : ℤ => (j:ℝ)*b r (j+n)*b r j) (if n=0 then 0 else r^n) := by
  let q := r^2
  let C := (1-q)^2 * r^n
  have hq : 0≤q := sq_nonneg _
  have hq1 : q<1 := by dsimp [q]; nlinarith [mul_pos (sub_pos.mpr hr1) (by linarith : 0<1+r)]
  have hnon : 1-q ≠ 0 := (sub_pos.mpr hq1).ne'
  have hprod (j : ℕ) : b r ((j:ℤ)+n) * b r j = C*q^j := by
    rw [← Nat.cast_add,b_nat,b_nat,pow_add]
    dsimp [C,q]; ring
  have hz (j : ℤ) (hj : j < -1) : b r j=0 := by simp [b,show j ≠ -1 by omega,show ¬0≤j by omega]
  have h₀ : HasSum (fun j : ℕ => b r ((j:ℤ)+n)*b r j) (C/(1-q)) := by
    simp_rw [hprod]
    simpa only [div_eq_mul_inv,one_mul] using (MasulloScatter.geometric_ray hq hq1).mul_left C
  have h₁ : HasSum (fun j : ℕ => ((j:ℤ):ℝ)*b r ((j:ℤ)+n)*b r j) (C*q/(1-q)^2) := by
    have h := MasulloScatter.affine_geometric_ray q C 0 hq hq1
    simp only [zero_add,zero_mul,zero_div] at h
    convert h using 1
    funext j
    rw [mul_assoc, hprod]
    push_cast
    ring
  have H₀ := hasSum_nat_and_boundary (fun j : ℤ => b r (j+n)*b r j) _ h₀
    (fun k hk => by rw [hz _ hk,mul_zero])
  have H₁ := hasSum_nat_and_boundary (fun j : ℤ => (j:ℝ)*b r (j+n)*b r j) _ h₁
    (fun k hk => by rw [hz _ hk,mul_zero])
  have hbase : b r (-1) = -r := by simp [b]
  cases n with
  | zero =>
    dsimp only [C] at H₀ H₁
    simp only [Nat.cast_zero,add_zero,hbase,Int.cast_neg,Int.cast_one,pow_zero,mul_one] at H₀ H₁
    simp only [Nat.cast_zero,add_zero,if_true]
    refine ⟨?_,?_⟩
    · convert H₀ using 1
      dsimp only [q] at *
      field_simp
      ring
    · convert H₁ using 1
      dsimp only [q] at *
      field_simp
      ring
  | succ n =>
    have he : (-1:ℤ)+(n.succ:ℕ) = (n:ℤ) := by omega
    dsimp only [C] at H₀ H₁
    simp only [he,b_nat,hbase,Int.cast_neg,Int.cast_one] at H₀ H₁
    refine ⟨?_,?_⟩
    · convert H₀ using 1
      simp only [Nat.succ_ne_zero,if_false]
      dsimp only [q] at *
      rw [pow_succ]
      field_simp
      ring
    · convert H₁ using 1
      simp only [Nat.succ_ne_zero,if_false]
      dsimp only [q] at *
      rw [pow_succ]
      field_simp
      ring

end MasulloScatter
end

section

namespace MasulloScatter

/-- Translate both factors together. The first moment of a translated correlation gains the
translation times its zeroth moment, which vanishes for every nonzero lag. -/
theorem all_lags_of_positive_lags (b : ℤ → ℝ) (r : ℝ)
    (hp : ∀ n : ℕ, HasSum (fun j : ℤ => b (j+n)*b j) (if n=0 then 1 else 0) ∧
      HasSum (fun j : ℤ => (j:ℝ)*b (j+n)*b j) (if n=0 then 0 else r^n)) :
    ∀ d : ℤ, HasSum (fun j : ℤ => b (j-d)*b j) (if d=0 then 1 else 0) ∧
      HasSum (fun j : ℤ => (j:ℝ)*b (j-d)*b j) (if d=0 then 0 else r^d.natAbs) := by
  intro d
  cases d with
  | negSucc n =>
    simp only [Int.negSucc_ne_zero, if_false, Int.natAbs_negSucc]
    simpa only [Nat.succ_ne_zero, if_false, Int.natCast_succ, Int.negSucc_eq, sub_neg_eq_add] using hp (n+1)
  | ofNat n =>
    rcases n with _ | n
    · simpa using hp 0
    · let N : ℕ := n+1
      have hN : N ≠ 0 := Nat.succ_ne_zero n
      have hNz : (N:ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hN
      obtain ⟨hzero,hmom⟩ := hp N
      simp only [hN,if_false] at hzero hmom
      change HasSum (fun j : ℤ => b (j-(N:ℤ))*b j) (if (N:ℤ)=0 then 1 else 0) ∧
        HasSum (fun j : ℤ => (j:ℝ)*b (j-(N:ℤ))*b j) (if (N:ℤ)=0 then 0 else r^N)
      simp only [hNz,if_false]
      constructor
      · apply (Equiv.addRight (N:ℤ)).hasSum_iff.mp
        apply hzero.congr_fun
        intro j
        simp [Equiv.coe_addRight,mul_comm]
      · apply (Equiv.addRight (N:ℤ)).hasSum_iff.mp
        have hshift := hmom.add (hzero.mul_left (N:ℝ))
        rw [mul_zero,add_zero] at hshift
        apply hshift.congr_fun
        intro j
        simp only [Function.comp_apply,Equiv.coe_addRight,add_sub_cancel_right,Int.cast_add,
          Int.cast_natCast]
        ring

end MasulloScatter
end

section
namespace MasulloScatter

private theorem halfLine_block (r : ℝ) (hr : 0<r) (hr1 : r<1) (i j : ℕ) :
    HasSum (fun n : ℕ => b r ((i:ℤ)+(n:ℤ))*b r ((j:ℤ)+(n:ℤ))) ((1-r^2)*r^(i+j)) := by
  have hr2 : r^2 < 1 := by nlinarith [mul_pos (sub_pos.mpr hr1) (by linarith : 0 < 1+r)]
  have hgeom := (hasSum_geometric_of_lt_one (sq_nonneg r) hr2).mul_left ((1-r^2)^2*r^(i+j))
  convert! hgeom using 1
  · funext n
    rw [← Nat.cast_add, ← Nat.cast_add, b_nat, b_nat, pow_add, pow_add, pow_add]
    ring
  · field_simp [(sub_pos.mpr hr2).ne']

private theorem halfLine_block_int (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i j : ℕ) :
    HasSum (fun k : ℤ => if k ≤ 0 then b r ((i:ℤ)-k)*b r ((j:ℤ)-k) else 0)
      ((1-r^2)*r^(i+j)) := by
  let F (k : ℤ) := if k ≤ 0 then b r ((i:ℤ)-k)*b r ((j:ℤ)-k) else 0
  change HasSum F _
  apply (Equiv.neg ℤ).hasSum_iff.mp
  have hp : HasSum (fun n : ℕ => (F ∘ (Equiv.neg ℤ)) (n : ℤ)) ((1-r^2)*r^(i+j)) := by
    simpa only [F,Function.comp_apply,Equiv.neg_apply,neg_nonpos,Int.natCast_nonneg,
      if_true,sub_neg_eq_add] using halfLine_block r hr hr1 i j
  have hn : HasSum (fun n : ℕ => (F ∘ (Equiv.neg ℤ)) (-(n+1:ℤ))) 0 := by
    apply hasSum_zero.congr_fun
    intro n
    simp [F,Equiv.neg_apply,Function.comp_apply,show ¬ ((n:ℤ)+1 ≤ 0) by omega]
  simpa only [add_zero] using hp.of_nat_of_neg_add_one hn

end MasulloScatter
end

section

namespace MasulloScatter

private theorem halfLine_matrix (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i j : ℤ) :
    let q := if 0 ≤ i ∧ 0 ≤ j then (1-r^2)*r^(i.toNat+j.toNat) else 0
    HasSum (fun k : ℤ => if k ≤ 0 then b r (i-k)*b r (j-k) else 0)
      (q + (if i = j ∧ i ≤ 0 then 1 else 0) - (if i = 0 ∧ j = 0 then 1 else 0)) := by
  dsimp only
  by_cases Hij : 0 ≤ i ∧ 0 ≤ j
  · obtain ⟨ii,rfl⟩ := Int.eq_ofNat_of_zero_le Hij.1
    obtain ⟨jj,rfl⟩ := Int.eq_ofNat_of_zero_le Hij.2
    have h := halfLine_block_int r hr hr1 ii jj
    simp only [if_pos Hij, Int.toNat_natCast]
    convert h using 1
    split_ifs <;> simp_all
    all_goals omega
  · have hS := ((all_lags_of_positive_lags (b r) r (positive_lag r hr hr1)) (j-i)).1
    let e : ℤ ≃ ℤ := (Equiv.neg ℤ).trans (Equiv.addRight j)
    have ht := e.hasSum_iff.mpr hS
    have hsing : (if j-i = 0 then (1:ℝ) else 0) = if i = j then 1 else 0 := by
      by_cases h : i = j  <;> simp [h, show j-i = 0 ↔ i = j by omega]
    rw [hsing] at ht
    have heach (k : ℤ) : (fun t : ℤ => b r (t-(j-i))*b r t) (e k) =
        if k ≤ 0 then b r (i-k)*b r (j-k) else 0 := by
      have he : e k = j-k := by simp [e,sub_eq_add_neg,add_comm]
      rw [he]
      change b r (j-k-(j-i)) * b r (j-k) = _
      rw [show j-k-(j-i) = i-k by omega]
      by_cases hk : k ≤ 0
      · rw [if_pos hk]
      · rw [if_neg hk]
        have hc (a : ℤ) (ha : a < 0) : b r (a-k)=0 := by
          simp only [b,if_neg (show a-k ≠ -1 by omega),if_neg (show ¬ 0 ≤ a-k by omega)]
        by_cases hi : i < 0
        · simp [hc i hi]
        · have hj : j < 0 := by omega
          simp [hc j hj]
    have hcomp := ht.congr_fun (fun k => (heach k).symm)
    convert hcomp using 1
    simp only [if_neg Hij,zero_add]
    split_ifs <;> simp_all
    all_goals omega

end MasulloScatter
end

section

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    let b (j : ℤ) := if j = -1 then -r else if 0 ≤ j then (1-r^2)*r^j.toNat else 0
    (∀ d : ℤ,
      HasSum (fun j : ℤ => b (j-d)*b j) (if d=0 then 1 else 0) ∧
      HasSum (fun j : ℤ => (j:ℝ)*b (j-d)*b j) (if d=0 then 0 else r^d.natAbs)) ∧
    (∀ i j : ℤ,
      let c (k : ℤ) := if k ≤ 0 then b (i-k)*b (j-k) else 0
      Summable c ∧
        (∑' k : ℤ, c k) - (if i=j ∧ i ≤ 0 then 1 else 0) =
          (if 0 ≤ i ∧ 0 ≤ j then (1-r^2)*r^(i.toNat+j.toNat) else 0) -
          (if i=0 ∧ j=0 then 1 else 0)) := by
  constructor
  · exact MasulloScatter.all_lags_of_positive_lags (MasulloScatter.b r) r
      (MasulloScatter.positive_lag r hr hr1)
  · intro i j
    have h := MasulloScatter.halfLine_matrix r hr hr1 i j
    refine ⟨h.summable,?_⟩
    change (∑' k : ℤ, if k ≤ 0 then MasulloScatter.b r (i-k)*MasulloScatter.b r (j-k) else 0) - _ = _
    rw [h.tsum_eq]
    ring
end
