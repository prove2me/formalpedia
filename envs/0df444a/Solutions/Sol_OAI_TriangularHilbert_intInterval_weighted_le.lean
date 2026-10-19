-- Prove2me | solution 1 for OAI.TriangularHilbert.intInterval_weighted_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T03:50:51.901828+00:00
-- url     : https://prove2.me/submissions/51494c6e-1582-4d30-b5af-1419fb029460

import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedTraceOrder
import Definitions.Def_OAI_Analysis_TriangularHilbert_MassPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedConvolution
import Definitions.Def_OAI_Analysis_TriangularHilbert_RankJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_ZeroStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_StarJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialAlgebra
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_TotalJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntWeak
import Definitions.Def_OAI_Analysis_TriangularHilbert_StrongLayer
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntMax

open OAI OAI.TriangularHilbert
open scoped BigOperators
theorem h43_tele (g : ℕ → ℝ) (R k : ℕ) (hk : k ≤ R) :
    g k = ∑ r ∈ Finset.range (R+1), if k ≤ r then (if r < R then g r - g (r+1) else g R) else 0 := by
  induction R generalizing k with
  | zero =>
    obtain rfl : k = 0 := by omega
    simp
  | succ R ih =>
    rw [Finset.sum_range_succ]
    rcases Nat.lt_or_ge k (R+1) with h | h
    · have e := ih k (by omega)
      have e2 : ∑ r ∈ Finset.range (R+1), (if k ≤ r then (if r < R+1 then g r - g (r+1) else g (R+1)) else 0)
          = ∑ r ∈ Finset.range (R+1), (if k ≤ r then (if r < R then g r - g (r+1) else g R) else 0)
            - g (R+1) := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ, if_pos (by omega : k ≤ R), if_pos (by omega : k ≤ R),
          if_pos (by omega : R < R + 1), if_neg (lt_irrefl R)]
        have : ∀ r ∈ Finset.range R, (if k ≤ r then (if r < R+1 then g r - g (r+1) else g (R+1)) else 0)
            = (if k ≤ r then (if r < R then g r - g (r+1) else g R) else 0) := by
          intro r hr; rw [Finset.mem_range] at hr; rw [if_pos (by omega : r < R+1), if_pos hr]
        rw [Finset.sum_congr rfl this]; ring
      rw [e2, ← e, if_pos (by omega : k ≤ R+1), if_neg (lt_irrefl _)]; ring
    · obtain rfl : k = R+1 := by omega
      rw [if_pos le_rfl, if_neg (lt_irrefl _)]
      rw [Finset.sum_eq_zero]; · simp
      intro r hr; rw [Finset.mem_range] at hr; rw [if_neg (by omega)]

theorem h43_abel (E : Finset ℤ) (f : ℤ → ℝ) (n : ℤ) (g : ℕ → ℝ) (R : ℕ)
    (hE : ∀ m ∈ E, (m-n).natAbs ≤ R) :
    (∑ m ∈ E, f m * g (m-n).natAbs) = ∑ r ∈ Finset.range (R+1),
      (if r < R then g r - g (r+1) else g R) * ∑ m ∈ E ∩ intInterval n r, f m := by
  have hm : ∀ m ∈ E, f m * g (m-n).natAbs = ∑ r ∈ Finset.range (R+1),
      (if r < R then g r - g (r+1) else g R) * (if m ∈ intInterval n r then f m else 0) := by
    intro m hmE
    rw [h43_tele g R _ (hE m hmE), Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    have : m ∈ intInterval n r ↔ (m-n).natAbs ≤ r := by
      rw [intInterval, Finset.mem_Icc]; omega
    by_cases h : (m-n).natAbs ≤ r
    · rw [if_pos h, if_pos (this.2 h)]; ring
    · rw [if_neg h, if_neg (fun h' => h (this.1 h'))]; ring
  rw [Finset.sum_congr rfl hm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Finset.mul_sum, Finset.sum_ite_mem]

theorem solution (D : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ m ∈ D, 0 ≤ f m)
    (n : ℤ) (g : ℕ → ℝ) (hg : ∀ r, 0 ≤ g r) (hdec : ∀ r, g (r+1) ≤ g r) :
    (∑ m ∈ D, f m*g (m-n).natAbs) ≤
      intMax D f n * ∑ m ∈ intInterval n (supportRadius D n), g (m-n).natAbs := by
  set R := supportRadius D n with hR
  have hE : ∀ m ∈ D, (m-n).natAbs ≤ R := fun m hm => Finset.le_sup (f := fun m => (m-n).natAbs) hm
  have hI : ∀ m ∈ intInterval n R, (m-n).natAbs ≤ R := by
    intro m hm; rw [intInterval, Finset.mem_Icc] at hm; omega
  have hc : ∀ r ∈ Finset.range (R+1), 0 ≤ (if r < R then g r - g (r+1) else g R) := by
    intro r _; split_ifs
    · linarith [hdec r]
    · exact hg R
  rw [h43_abel D f n g R hE]
  have e1 : (∑ m ∈ intInterval n R, g (m-n).natAbs) = ∑ m ∈ intInterval n R, (fun _ => (1:ℝ)) m * g (m-n).natAbs := by
    simp
  rw [e1, h43_abel _ _ n g R hI, Finset.mul_sum]
  refine Finset.sum_le_sum fun r hr => ?_
  rw [mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (hc r hr)
  have hr' : r ≤ R := by rw [Finset.mem_range] at hr; omega
  have hcard : (∑ m ∈ intInterval n R ∩ intInterval n r, (fun _ => (1:ℝ)) m) = 2*(r:ℝ)+1 := by
    have : intInterval n R ∩ intInterval n r = intInterval n r := by
      ext m; simp only [intInterval, Finset.mem_inter, Finset.mem_Icc]; omega
    rw [this]; simp only [Finset.sum_const, nsmul_eq_mul, mul_one, intInterval, Int.card_Icc]
    have : (n + (r:ℤ) + 1 - (n - r)).toNat = 2*r+1 := by omega
    rw [this]; push_cast; ring
  rw [hcard]
  have hav : intAverage D f n r ≤ intMax D f n := by
    unfold intMax; exact Finset.le_sup' (intAverage D f n) hr
  unfold intAverage at hav
  have hpos : (0:ℝ) < 2*(r:ℝ)+1 := by positivity
  rw [div_le_iff₀ hpos] at hav
  exact hav

