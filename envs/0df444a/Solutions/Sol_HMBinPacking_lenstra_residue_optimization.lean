-- Prove2me | solution 1 for HMBinPacking.lenstra_residue_optimization
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T10:00:29.062927+00:00
-- url     : https://prove2.me/submissions/6f93b9a5-42f7-4174-a464-5b356272675b

import Definitions.Def_HMBinPacking_ILP
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
open Finset HMBinPacking
open scoped Pointwise

private lemma sr_image (I : Instance) (r : Fin I.d → Fin I.d) :
    zCast '' Sr I r = (fun y : Fin I.d → ℕ => fun i => (((r i : ℕ)+I.d*y i : ℕ) : ℝ)) ''
       {y : Fin I.d → ℕ | ∑ i, I.s i * ((r i : ℕ)+I.d*y i) ≤ I.B} := by
  classical
  apply Set.Subset.antisymm
  · rintro _ ⟨x,⟨⟨hpos,hcap⟩,⟨y,hy⟩⟩,rfl⟩
    have he (i) : x i = (r i : ℕ) + (I.d:ℤ)*y i := by
      simpa [Pi.smul_apply,zsmul_eq_mul] using congrFun hy i
    have hnon (i) : 0 ≤ y i := by
      by_contra! hn
      have hd : (0:ℤ) ≤ I.d := by positivity
      have hh := mul_le_mul_of_nonneg_left (show y i ≤ -1 by omega) hd
      have hr : ((r i : ℕ):ℤ) < I.d := by exact_mod_cast (r i).isLt
      have hp := hpos i
      rw [he i] at hp; linarith
    let v := fun i => (y i).toNat
    have hev (i) : ((((r i : ℕ)+I.d*v i : ℕ) : ℤ)) = x i := by
      rw [he i]; push_cast; simp [v,Int.toNat_of_nonneg (hnon i)]
    refine ⟨v,?_,?_⟩
    · change (∑ i, I.s i * ((r i : ℕ) + I.d * v i)) ≤ I.B
      have h : (∑ i, (I.s i : ℤ) * ((((r i : ℕ) + I.d * v i : ℕ) : ℤ))) ≤ I.B := by
        simpa only [hev] using hcap
      exact_mod_cast h
    · ext i; change ((((r i : ℕ)+I.d*v i : ℕ) : ℝ)) = (x i : ℝ)
      exact_mod_cast hev i
  · rintro _ ⟨y,hy,rfl⟩
    let x : Fin I.d → ℤ := fun i => (((r i : ℕ)+I.d*y i : ℕ):ℤ)
    refine ⟨x,⟨⟨fun i => by dsimp [x]; positivity,?_⟩,?_⟩,?_⟩
    · dsimp [x]; exact_mod_cast hy
    · refine ⟨fun i => (y i : ℤ),?_⟩
      ext i; simp [x,zsmul_eq_mul]
    · ext i; simp [x,zCast]

theorem solution (I : Instance) (r : Fin I.d → Fin I.d)
    (hr : ∑ i, I.s i * (r i : ℕ) ≤ I.B) :
    (fun i => ((r i : ℕ) : ℤ)) ∈ Sr I r ∧
    {y' : Fin I.d → ℕ | ∑ i, I.s i * ((r i : ℕ) + I.d * y' i) ≤ I.B}.Finite ∧
    (∀ y : Fin I.d → ℕ, (∑ i, I.s i * ((r i : ℕ) + I.d * y i) ≤ I.B) →
      (fun i => (((r i : ℕ) + I.d * y i : ℕ) : ℝ)) ∈ Pr I r) ∧
    ∀ u : Fin I.d → ℚ, ∃ y : Fin I.d → ℕ,
        ∑ i, I.s i * ((r i : ℕ) + I.d * y i) ≤ I.B ∧
        (fun i => (((r i : ℕ) + I.d * y i : ℕ) : ℝ)) ∈ Pr I r ∧
        IsGreatest ((fun x : Fin I.d → ℝ => ∑ i, (u i : ℝ) * x i) '' Pr I r)
          (∑ i, (u i : ℝ) * (((r i : ℕ) + I.d * y i : ℕ) : ℝ)) ∧
        IsGreatest ((fun y' : Fin I.d → ℕ => ∑ i, (u i : ℝ) * (((r i : ℕ) + I.d * y' i : ℕ) : ℝ)) ''
            {y' | ∑ i, I.s i * ((r i : ℕ) + I.d * y' i) ≤ I.B})
          (∑ i, (u i : ℝ) * (((r i : ℕ) + I.d * y i : ℕ) : ℝ)) := by
  classical
  let Y := {y : Fin I.d → ℕ | ∑ i, I.s i * ((r i : ℕ) + I.d * y i) ≤ I.B}
  let g := fun y : Fin I.d → ℕ => fun i => (((r i : ℕ) + I.d * y i : ℕ) : ℝ)
  have hfinite : Y.Finite := by
    apply (Set.Finite.pi (t := fun _ : Fin I.d => Set.Iic I.B) (fun _ => Set.finite_Iic _)).subset
    intro y hy i _
    have hcap : ∑ j, I.s j * ((r j : ℕ) + I.d * y j) ≤ I.B := hy
    have h1 := Finset.single_le_sum (f := fun j => I.s j * ((r j : ℕ) + I.d * y j))
      (fun j (_ : j ∈ univ) => Nat.zero_le _) (Finset.mem_univ i)
    have h2 := Nat.le_mul_of_pos_left (y i) I.d_pos
    have h3 := Nat.le_mul_of_pos_left ((r i : ℕ) + I.d * y i) (I.s_pos i)
    change y i ≤ I.B; omega
  have hsub : g '' Y ⊆ Pr I r := by rw [Pr,sr_image]; exact subset_convexHull _ _
  refine ⟨⟨⟨fun i => by positivity,by change (∑ i, (I.s i : ℤ) * ((r i : ℕ) : ℤ)) ≤ I.B; exact_mod_cast hr⟩,⟨0,by simp⟩⟩,hfinite,(fun y hy => hsub ⟨y,hy,rfl⟩),?_⟩
  intro u
  let f := fun x : Fin I.d → ℝ => ∑ i,(u i : ℝ)*x i
  have h0 : (0 : Fin I.d → ℕ) ∈ Y := by simpa [Y] using hr
  obtain ⟨y,hy,hmax⟩ := Set.exists_max_image Y (fun y => f (g y)) hfinite ⟨_,h0⟩
  have hm : g y ∈ Pr I r := hsub ⟨_,hy,rfl⟩
  refine ⟨y,hy,hm,⟨⟨_,hm,rfl⟩,?_⟩,⟨⟨_,hy,rfl⟩,?_⟩⟩
  · rintro _ ⟨x,hx,rfl⟩
    let Q := {x | f x ≤ f (g y)}
    have hc : Convex ℝ Q := by
      intro x hx z hz a b ha hb hab
      change f (a • x + b • z) ≤ f (g y)
      have ee : f (a • x + b • z) = a * f x + b * f z := by
        dsimp [f]; rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i _
        ring
      change f x ≤ _ at hx;change f z ≤ _ at hz
      rw [ee]; nlinarith [mul_nonneg ha (sub_nonneg.mpr hx), mul_nonneg hb (sub_nonneg.mpr hz),
        congrArg (fun t : ℝ => t * f (g y)) hab]
    have hh : g '' Y ⊆ Q := by rintro _ ⟨v,hv,rfl⟩; exact hmax v hv
    rw [Pr,sr_image] at hx
    exact convexHull_min hh hc hx
  · rintro _ ⟨v,hv,rfl⟩; exact hmax v hv
