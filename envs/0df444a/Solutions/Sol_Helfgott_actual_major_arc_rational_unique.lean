-- Prove2me | solution 1 for Helfgott.actual_major_arc_rational_unique
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-05T04:41:22.435369+00:00
-- url     : https://prove2.me/submissions/5fbd4e5d-ce1c-48e6-b3ea-2f46bb74fbe0

import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set Metric

namespace Helfgott

lemma reduced_fraction_cross_eq {a q b d : ℕ} (hq : 0 < q) (hd : 0 < d)
    (haq : Nat.Coprime a q) (hbd : Nat.Coprime b d) (he : a*d = b*q) :
    a = b ∧ q = d := by
  have hqd : q ∣ d := haq.symm.dvd_of_dvd_mul_left (by rw [he];exact dvd_mul_left q b)
  have hdq : d ∣ q := hbd.symm.dvd_of_dvd_mul_left (by rw [← he];exact dvd_mul_left d a)
  have hqdEq : q = d := Nat.dvd_antisymm hqd hdq
  have hab : a = b := Nat.eq_of_mul_eq_mul_right hd (by simpa only [hqdEq] using he)
  exact ⟨hab,hqdEq⟩

lemma reduced_fraction_circle_separation {a q b d : ℕ} (hq : 0 < q) (hd : 0 < d)
    (ha : a < q) (hb : b < d) (haq : Nat.Coprime a q) (hbd : Nat.Coprime b d)
    (hne : (a,q) ≠ (b,d)) :
    1/((q:ℝ)*(d:ℝ)) ≤ dist ((a:ℝ)/(q:ℝ) : AddCircle (1:ℝ))
      ((b:ℝ)/(d:ℝ) : AddCircle (1:ℝ)) := by
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  let δ : ℝ := (a:ℝ)/(q:ℝ)-(b:ℝ)/(d:ℝ)
  let k : ℤ := (a:ℤ)*(d:ℤ)-(b:ℤ)*(q:ℤ)-round δ*(q:ℤ)*(d:ℤ)
  have hδlo : -1 < δ := by
    have hba : (b:ℝ)/(d:ℝ) < 1 := (div_lt_one hdR).mpr (by exact_mod_cast hb)
    have haa : 0 ≤ (a:ℝ)/(q:ℝ) := by positivity
    dsimp [δ]
    linarith
  have hδhi : δ < 1 := by
    have haa : (a:ℝ)/(q:ℝ) < 1 := (div_lt_one hqR).mpr (by exact_mod_cast ha)
    have hba : 0 ≤ (b:ℝ)/(d:ℝ) := by positivity
    dsimp [δ]
    linarith
  have hk : (k:ℝ) = (q:ℝ)*(d:ℝ)*(δ-(round δ:ℝ)) := by
    dsimp [k,δ]
    push_cast
    field_simp
  have hk0 : k ≠ 0 := by
    intro hzero
    have hzR : (k:ℝ) = 0 := by exact_mod_cast hzero
    rw [hk] at hzR
    have hδ : δ = (round δ:ℝ) := by
      have hδ0 := (mul_eq_zero.mp hzR).resolve_left (by positivity)
      exact sub_eq_zero.mp hδ0
    have hroundlo : (-1:ℤ) < round δ := by exact_mod_cast (hδ.symm ▸ hδlo)
    have hroundhi : round δ < (1:ℤ) := by exact_mod_cast (hδ.symm ▸ hδhi)
    have hround : round δ = 0 := by omega
    have hcrossR : (a:ℝ)*(d:ℝ) = (b:ℝ)*(q:ℝ) := by
      rw [hround,Int.cast_zero] at hδ
      dsimp only [δ] at hδ
      have ht := (sub_eq_zero.mp hδ)
      exact (div_eq_div_iff hqR.ne' hdR.ne').mp ht
    have hcross : a*d = b*q := by exact_mod_cast hcrossR
    rcases reduced_fraction_cross_eq hq hd haq hbd hcross with ⟨hab,hqd⟩
    exact hne (Prod.ext hab hqd)
  have hkabs : 1 ≤ |(k:ℝ)| := by
    rcases lt_or_gt_of_ne hk0 with hneg | hpos
    · have hkneg : (k:ℝ) < 0 := by exact_mod_cast hneg
      rw [abs_of_neg hkneg]
      have hh : k ≤ -1 := by omega
      have hhR : (k:ℝ) ≤ -1 := by exact_mod_cast hh
      linarith
    · have hkpos : (0:ℝ) < k := by exact_mod_cast hpos
      rw [abs_of_pos hkpos]
      exact_mod_cast (show (1:ℤ) ≤ k by omega)
  have hnorm : dist ((a:ℝ)/(q:ℝ) : AddCircle (1:ℝ))
      ((b:ℝ)/(d:ℝ) : AddCircle (1:ℝ)) = |δ-(round δ:ℝ)| := by
    rw [dist_eq_norm,← QuotientAddGroup.mk_sub,AddCircle.norm_eq]
    simp only [inv_one,one_mul,mul_one]
    rfl
  rw [hnorm]
  apply (div_le_iff₀ (mul_pos hqR hdR)).mpr
  rw [hk,abs_mul,abs_of_pos (mul_pos hqR hdR)] at hkabs
  simpa only [mul_comm] using hkabs

theorem major_arc_balls_disjoint {a q b d r : ℕ} {x : ℝ}
    (hq : 0 < q) (hd : 0 < d) (ha : a < q) (hb : b < d)
    (haq : Nat.Coprime a q) (hbd : Nat.Coprime b d)
    (hqr : q ≤ 2*r) (hdr : d ≤ 2*r) (hx : 32*(r:ℝ)^2 < x)
    (hne : (a,q) ≠ (b,d)) :
    Disjoint (ball ((a:ℝ)/(q:ℝ) : AddCircle (1:ℝ)) (8*(r:ℝ)/((q:ℝ)*x)))
      (ball ((b:ℝ)/(d:ℝ) : AddCircle (1:ℝ)) (8*(r:ℝ)/((d:ℝ)*x))) := by
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hxR : 0 < x := lt_of_le_of_lt (by positivity) hx
  have hqrR : (q:ℝ) ≤ 2*r := by exact_mod_cast hqr
  have hdrR : (d:ℝ) ≤ 2*r := by exact_mod_cast hdr
  have hsep := reduced_fraction_circle_separation hq hd ha hb haq hbd hne
  have hrad : 8*(r:ℝ)/((q:ℝ)*x)+8*(r:ℝ)/((d:ℝ)*x) < 1/((q:ℝ)*(d:ℝ)) := by
    apply (lt_div_iff₀ (mul_pos hqR hdR)).mpr
    have he : (8*(r:ℝ)/((q:ℝ)*x)+8*(r:ℝ)/((d:ℝ)*x))*((q:ℝ)*(d:ℝ)) =
        8*(r:ℝ)*((q:ℝ)+(d:ℝ))/x := by
      field_simp
      ring
    rw [he]
    apply (div_lt_one hxR).mpr
    have hsum : (q:ℝ)+(d:ℝ) ≤ 4*r := by linarith
    have hm := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 8*(r:ℝ))
    nlinarith
  apply Set.disjoint_left.mpr
  intro α hαq hαd
  have hdcenter := dist_triangle ((a:ℝ)/(q:ℝ) : AddCircle (1:ℝ)) α
    ((b:ℝ)/(d:ℝ) : AddCircle (1:ℝ))
  have hqdist := mem_ball.mp hαq
  have hddist := mem_ball.mp hαd
  rw [dist_comm _ α] at hdcenter
  linarith

theorem actual_major_arc_rational_unique {a q b d r : ℕ} {x : ℝ}
    (α : AddCircle (1:ℝ)) (hq : 0 < q) (hd : 0 < d)
    (ha : a < q) (hb : b < d) (haq : Nat.Coprime a q) (hbd : Nat.Coprime b d)
    (hx : 32*(r:ℝ)^2 < x)
    (hαq : (Odd q ∧ q ≤ r ∧ dist α ((a:ℝ)/(q:ℝ) : AddCircle (1:ℝ)) <
        8*r/(2*q*x)) ∨
      (Even q ∧ q ≤ 2*r ∧ dist α ((a:ℝ)/(q:ℝ) : AddCircle (1:ℝ)) < 8*r/(q*x)))
    (hαd : (Odd d ∧ d ≤ r ∧ dist α ((b:ℝ)/(d:ℝ) : AddCircle (1:ℝ)) <
        8*r/(2*d*x)) ∨
      (Even d ∧ d ≤ 2*r ∧ dist α ((b:ℝ)/(d:ℝ) : AddCircle (1:ℝ)) < 8*r/(d*x))) :
    a = b ∧ q = d := by
  have hxR : 0 < x := lt_of_le_of_lt (by positivity) hx
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hqr : q ≤ 2*r := by rcases hαq with h | h <;> omega
  have hdr : d ≤ 2*r := by rcases hαd with h | h <;> omega
  have hqball : α ∈ ball ((a:ℝ)/(q:ℝ) : AddCircle (1:ℝ)) (8*(r:ℝ)/((q:ℝ)*x)) := by
    apply mem_ball.mpr
    rcases hαq with h | h
    · apply h.2.2.trans_le
      have hden : (0:ℝ) < q*x := mul_pos hqR hxR
      have hnum : 0 ≤ 8*(r:ℝ) := by positivity
      apply div_le_div_of_nonneg_left hnum hden
      nlinarith
    · exact h.2.2
  have hdball : α ∈ ball ((b:ℝ)/(d:ℝ) : AddCircle (1:ℝ)) (8*(r:ℝ)/((d:ℝ)*x)) := by
    apply mem_ball.mpr
    rcases hαd with h | h
    · apply h.2.2.trans_le
      have hden : (0:ℝ) < d*x := mul_pos hdR hxR
      have hnum : 0 ≤ 8*(r:ℝ) := by positivity
      apply div_le_div_of_nonneg_left hnum hden
      nlinarith
    · exact h.2.2
  by_contra hh
  have hne : (a,q) ≠ (b,d) := by
    intro he
    exact hh ⟨congrArg Prod.fst he,congrArg Prod.snd he⟩
  exact Set.disjoint_left.mp (major_arc_balls_disjoint hq hd ha hb haq hbd hqr hdr hx hne) hqball hdball

end Helfgott
end

open Set Metric Helfgott

theorem solution {a q b d r : ℕ} {x : ℝ}
    (α : AddCircle (1:ℝ)) (hq : 0 < q) (hd : 0 < d)
    (ha : a < q) (hb : b < d) (haq : Nat.Coprime a q) (hbd : Nat.Coprime b d)
    (hx : 32*(r:ℝ)^2 < x)
    (hαq : (Odd q ∧ q ≤ r ∧ dist α ((a:ℝ)/(q:ℝ) : AddCircle (1:ℝ)) <
        8*r/(2*q*x)) ∨
      (Even q ∧ q ≤ 2*r ∧ dist α ((a:ℝ)/(q:ℝ) : AddCircle (1:ℝ)) < 8*r/(q*x)))
    (hαd : (Odd d ∧ d ≤ r ∧ dist α ((b:ℝ)/(d:ℝ) : AddCircle (1:ℝ)) <
        8*r/(2*d*x)) ∨
      (Even d ∧ d ≤ 2*r ∧ dist α ((b:ℝ)/(d:ℝ) : AddCircle (1:ℝ)) < 8*r/(d*x))) :
    a = b ∧ q = d := Helfgott.actual_major_arc_rational_unique α hq hd ha hb haq hbd hx hαq hαd

#print axioms solution
