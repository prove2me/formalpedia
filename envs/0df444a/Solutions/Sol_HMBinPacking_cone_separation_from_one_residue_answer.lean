-- Prove2me | solution 1 for HMBinPacking.cone_separation_from_one_residue_answer
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T10:12:55.839876+00:00
-- url     : https://prove2.me/submissions/707155c6-0a88-4c0c-b849-d76d765e169d

import Definitions.Def_HMBinPacking_Oracles
import Definitions.Def_HMBinPacking_ILP
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
open HMBinPacking Finset

private lemma boundConfig (I : Instance) (r : Fin I.d → Fin I.d) (x : Fin I.d → ℝ)
    (hx : x ∈ Pr I r) (i) : 0 ≤ x i ∧ x i ≤ I.B := by
  let Q : Set (Fin I.d → ℝ) := {v | 0 ≤ v i ∧ v i ≤ I.B}
  have hf : zCast '' Sr I r ⊆ Q := by
    rintro _ ⟨v,⟨⟨hpos,hcap⟩,_⟩,rfl⟩
    have hh := Finset.single_le_sum (f := fun j => (I.s j:ℤ)*v j)
      (fun j (_ : j ∈ univ) => mul_nonneg (by positivity) (hpos j)) (Finset.mem_univ i)
    have hsi : (1:ℤ) ≤ I.s i := by exact_mod_cast I.s_pos i
    have hu : v i ≤ I.B := le_trans (by simpa using mul_le_mul_of_nonneg_right hsi (hpos i)) (hh.trans hcap)
    change 0 ≤ ((v i:ℤ):ℝ) ∧ ((v i:ℤ):ℝ) ≤ I.B
    exact ⟨by exact_mod_cast hpos i,by exact_mod_cast hu⟩
  apply convexHull_min hf _ hx
  intro a ha b hb x y hxp hyp he
  change 0 ≤ x*a i + y*b i ∧ x*a i + y*b i ≤ I.B
  constructor
  · exact add_nonneg (mul_nonneg hxp ha.1) (mul_nonneg hyp hb.1)
  · have h1 := mul_le_mul_of_nonneg_left ha.2 hxp
    have h2 := mul_le_mul_of_nonneg_left hb.2 hyp
    nlinarith [congrArg (fun t : ℝ => t * (I.B:ℝ)) he]

theorem solution (I : Instance) (r : Fin I.d → Fin I.d)
    (z : Fin I.d → ℚ) (t : ℚ)
    (oracle : 0 < t → ∃ w : List Bool, IsSepAnswer (Pr I r) (fun i => z i / t) w) :
    (qCast z, (t:ℝ)) ∈ Cr I r ∨
    ∃ (u : Fin I.d → ℚ) (a : ℚ),
      (∀ b ∈ Cr I r, (∑ i, (u i : ℝ) * b.1 i) + (a:ℝ) * b.2 ≤ 0) ∧
      0 < (∑ i, (u i : ℝ) * (z i:ℝ)) + (a:ℝ) * (t:ℝ) := by
  classical
  let dot (u : Fin I.d → ℚ) (x : Fin I.d → ℝ) := ∑ i, (u i : ℝ)*x i
  have liftineq (u : Fin I.d → ℚ) (a : ℚ) (hu : ∀ x ∈ Pr I r, dot u x + a ≤ 0) :
      ∀ b ∈ Cr I r, dot u b.1 + (a:ℝ)*b.2 ≤ 0 := by
    rintro b (hb | ⟨x,hx,n,hn,rfl⟩)
    · have h0 : b = (0,0) := hb
      subst b; simp [dot]
    · change (∑ i, (u i : ℝ) * (n * x i)) + (a:ℝ)*n ≤ 0
      have hh : (∑ i, (u i : ℝ) * (n * x i)) = n * dot u x := by
        dsimp [dot]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl
        intro j _; ring
      rw [hh]; nlinarith [mul_nonpos_of_nonneg_of_nonpos hn.le (hu x hx)]
  rcases lt_trichotomy t 0 with hneg | rfl | hpos
  · right
    refine ⟨0,-1,liftineq _ _ (by simp [dot]),?_⟩
    simp; exact_mod_cast hneg
  · by_cases h : ∀ i,z i = 0
    · left
      left; simp [show qCast z = 0 by ext i; simp [qCast,h]]
    push Not at h
    obtain ⟨j,hj⟩ := h
    rcases lt_or_gt_of_ne hj with hneg | hpos
    · right
      let u : Fin I.d → ℚ := fun i => if i=j then -1 else 0
      have eqd (x) : dot u x = -x j := by
        dsimp [dot]
        rw [Finset.sum_eq_single j]
        · simp [u]
        · intro i _ hij; simp [u,hij]
        · simp
      refine ⟨u,0,liftineq _ _ (fun x hx => by rw [eqd]; simpa using (boundConfig I r x hx j).1),?_⟩
      change 0 < dot u (qCast z) + _; rw [eqd]; simp [qCast]; exact_mod_cast hneg
    · right
      let u : Fin I.d → ℚ := fun i => if i=j then 1 else 0
      have eqd (x) : dot u x = x j := by
        dsimp [dot]
        rw [Finset.sum_eq_single j]
        · simp [u]
        · intro i _ hij; simp [u,hij]
        · simp
      refine ⟨u,-I.B,liftineq _ _ (fun x hx => by rw [eqd]; simp; linarith [(boundConfig I r x hx j).2]),?_⟩
      change 0 < dot u (qCast z) + _; rw [eqd]; simp [qCast]; exact_mod_cast hpos
  · let y (i) := z i / t
    have tr : (0:ℝ) < t := by exact_mod_cast hpos
    have he : (t:ℝ) • qCast y = qCast z := by
      ext i; simp [Pi.smul_apply,qCast,y,mul_div_cancel₀ _ tr.ne']
    obtain ⟨w,hw⟩ := oracle hpos
    change IsSepAnswer (Pr I r) y w at hw
    rcases hw with ⟨_,hy⟩ | ⟨u,a,_,hall,hbad⟩
    · left; right; exact ⟨qCast y,hy,t,tr,Prod.ext he.symm rfl⟩
    · right
      refine ⟨u,-a,liftineq _ _ (fun x hx => by simp; linarith [hall x hx]),?_⟩
      have hdr : dot u (qCast z) = (t:ℝ) * dot u (qCast y) := by
        rw [← he]; simp only [dot, Finset.mul_sum]; apply Finset.sum_congr rfl;intro i _
        simp only [Pi.smul_apply,smul_eq_mul]; ring
      change 0 < dot u (qCast z) + _
      rw [hdr]; push_cast
      change (a:ℝ) < dot u (qCast y) at hbad
      nlinarith [mul_pos tr (sub_pos.mpr hbad)]
