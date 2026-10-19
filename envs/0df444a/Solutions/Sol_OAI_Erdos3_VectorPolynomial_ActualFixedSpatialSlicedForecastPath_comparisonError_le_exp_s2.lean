-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.comparisonError_le_exp_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:44:02.252+00:00
-- url     : https://prove2.me/submissions/90c69dfb-a085-400e-b36d-06b86f5e87c1

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B252
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialSlicedForecastPath_density_uniform_budget_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedFixedPathSlicedPerturbation_chosen_tail_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastModularCutoff
namespace OAI

section

namespace Erdos3

theorem forecastJointGridPrefactor_le_exp (dout dj dc d : ℕ)
    (hdout : dout ≤ d) (hdj : dj ≤ d) (hdc : dc ≤ d)
    {P E T D L C K : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hT : 1 ≤ T) (hTexp : T ≤ Real.exp (P + E + 5))
    (hD : 0 ≤ D) (hL : 0 ≤ L) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hDexp : D ≤ Real.exp P) (hLexp : L ≤ Real.exp P)
    (hCexp : C ≤ Real.exp P) (hKexp : K ≤ Real.exp P) :
    (T ^ (dout + 1) * (2 * 8 ^ dj * (L + C * K)) +
      (D / T) * (8 ^ dj * L)) * 6 ^ dc ≤
      Real.exp (((d : ℝ) + 1) * (P + E + 5) + 6 * d + 2 * P + 4) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h8 : (8 : ℝ) ≤ Real.exp 3 := by
    calc
      _ = (2 : ℝ) ^ 3 := by norm_num
      _ ≤ (Real.exp 1) ^ 3 := pow_le_pow_left₀ (by norm_num) h2 _
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have h6 : (6 : ℝ) ≤ Real.exp 3 := (by norm_num : (6 : ℝ) ≤ 8).trans h8
  have hR : 0 ≤ P + E + 5 := by linarith
  have hdoutR : (dout : ℝ) ≤ d := by exact_mod_cast hdout
  have hdjR : (dj : ℝ) ≤ d := by exact_mod_cast hdj
  have hdcR : (dc : ℝ) ≤ d := by exact_mod_cast hdc
  have hTp : T ^ (dout + 1) ≤ Real.exp (((d : ℝ) + 1) * (P + E + 5)) := by
    calc
      _ ≤ (Real.exp (P + E + 5)) ^ (dout + 1) :=
        pow_le_pow_left₀ (by linarith) hTexp _
      _ = Real.exp (((dout : ℝ) + 1) * (P + E + 5)) := by
        rw [← Real.exp_nat_mul]
        simp
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) hR)
  have hjp : (8 : ℝ) ^ dj ≤ Real.exp (3 * (d : ℝ)) := by
    calc
      _ ≤ (Real.exp 3) ^ dj := pow_le_pow_left₀ (by norm_num) h8 _
      _ = Real.exp ((dj : ℝ) * 3) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hcp : (6 : ℝ) ^ dc ≤ Real.exp (3 * (d : ℝ)) := by
    calc
      _ ≤ (Real.exp 3) ^ dc := pow_le_pow_left₀ (by norm_num) h6 _
      _ = Real.exp ((dc : ℝ) * 3) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hsum : L + C * K ≤ Real.exp (2 * P + 1) := by
    have hCK : C * K ≤ Real.exp (2 * P) := by
      calc
        _ ≤ Real.exp P * Real.exp P := mul_le_mul hCexp hKexp hK (Real.exp_nonneg _)
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    have hL2 := hLexp.trans (Real.exp_le_exp.mpr (show P ≤ 2 * P by linarith))
    calc
      _ ≤ 2 * Real.exp (2 * P) := by linarith
      _ ≤ Real.exp 1 * Real.exp (2 * P) := mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hDT : D / T ≤ Real.exp P :=
    (div_le_self hD hT).trans hDexp
  let H := ((d : ℝ) + 1) * (P + E + 5) + 6 * d + 2 * P + 2
  have hfirst : T ^ (dout + 1) * (2 * 8 ^ dj * (L + C * K)) * 6 ^ dc ≤
      Real.exp H := by
    calc
      _ ≤ Real.exp (((d : ℝ) + 1) * (P + E + 5)) *
          (Real.exp 1 * Real.exp (3 * d) * Real.exp (2 * P + 1)) * Real.exp (3 * d) := by
        gcongr
      _ = _ := by simp only [← Real.exp_add]; congr 1; dsimp [H]; ring
  have hsecond : (D / T) * (8 ^ dj * L) * 6 ^ dc ≤ Real.exp H := by
    calc
      _ ≤ Real.exp P * (Real.exp (3 * d) * Real.exp P) * Real.exp (3 * d) := by
        gcongr
      _ = Real.exp (6 * (d : ℝ) + 2 * P) := by
        simp only [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by
        have hp : 0 ≤ ((d : ℝ) + 1) * (P + E + 5) := mul_nonneg (by positivity) hR
        dsimp [H]
        linarith)
  rw [add_mul]
  calc
    _ ≤ 2 * Real.exp H := by linarith
    _ ≤ Real.exp 1 * Real.exp H := mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)
    _ = Real.exp (H + 1) := by rw [← Real.exp_add, add_comm]
    _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [H]; linarith)

end Erdos3

end

section

namespace Erdos3

theorem forecastJointGridCutoff_lower (P E : ℝ) :
    Real.exp (P + E + 4) ≤ (forecastJointGridCutoff P E : ℝ) := Nat.le_ceil _

theorem forecastJointGridCutoff_pos_unconditional (P E : ℝ) : 0 < forecastJointGridCutoff P E := by
  exact_mod_cast (Real.exp_pos (P + E + 4)).trans_le (forecastJointGridCutoff_lower P E)

theorem forecastJointGridCutoff_one_le (P E : ℝ) : 1 ≤ forecastJointGridCutoff P E :=
  forecastJointGridCutoff_pos_unconditional P E

theorem forecastJointGridCutoff_le_exp {P E : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) :
    (forecastJointGridCutoff P E : ℝ) ≤ Real.exp (P + E + 5) := by
  calc
    _ ≤ Real.exp (P + E + 4) + 1 := (Nat.ceil_lt_add_one (Real.exp_nonneg _)).le
    _ = 1 + Real.exp (P + E + 4) := add_comm _ _
    _ ≤ Real.exp ((P + E + 4) + 1) :=
      one_add_le_exp_succ (by linarith) le_rfl
    _ = _ := by congr 1; ring

theorem forecastJointGridCutoff_div_bound {P E D : ℝ} (hD : D ≤ Real.exp P) :
    D / forecastJointGridCutoff P E ≤ Real.exp (-(E + 4)) := by
  have hpos : (0 : ℝ) < forecastJointGridCutoff P E := by
    exact_mod_cast forecastJointGridCutoff_pos_unconditional P E
  apply (div_le_iff₀ hpos).mpr
  calc
    D ≤ Real.exp P := hD
    _ = Real.exp (-(E + 4)) * Real.exp (P + E + 4) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (forecastJointGridCutoff_lower P E) (Real.exp_nonneg _)

theorem forecastJointGridCutoff_tail_le {P E D : ℝ} (_hP : 0 ≤ P) (_hE : 0 ≤ E)
    (hD : D ≤ Real.exp P) :
    D / forecastJointGridCutoff P E ≤ Real.exp (-(E + 4)) :=
  forecastJointGridCutoff_div_bound hD

end Erdos3

end

section

namespace Erdos3

theorem modularForecastRankConstant_decay (s D : ℕ) :
    modularRankDecayExponent s (modularForecastRankConstant s D : ℝ) = (D + 2 : ℕ) := by
  unfold modularRankDecayExponent modularForecastRankConstant
  push_cast
  have htwo : (2 : ℝ) ^ s ≠ 0 := by positivity
  have hfac : (s.factorial : ℝ) ≠ 0 := by positivity
  field_simp

end Erdos3

end

section

namespace Erdos3

theorem forecastJointGridMeshLog_nonneg (d : ℕ) {P E : ℝ}
    (hP : 0 ≤ P) (hE : 0 ≤ E) : 0 ≤ forecastJointGridMeshLog d P E := by
  unfold forecastJointGridMeshLog
  positivity

theorem forecastJointGridMesh_bounds (d : ℕ) {P E : ℝ}
    (hP : 0 ≤ P) (hE : 0 ≤ E) :
    0 < forecastJointGridMesh d P E ∧ forecastJointGridMesh d P E ≤ 1 :=
  ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (neg_nonpos.mpr
    (forecastJointGridMeshLog_nonneg d hP hE))⟩

theorem forecastJointGridError_absorb
    (dout dj dc d cutoff : ℕ) (hdout : dout ≤ d) (hdj : dj ≤ d) (hdc : dc ≤ d)
    {P E D L C K δ : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hcutoff : 1 ≤ cutoff) (hTexp : (cutoff : ℝ) ≤ Real.exp (P + E + 5))
    (hD : 0 ≤ D) (hL : 0 ≤ L) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hDexp : D ≤ Real.exp P) (hLexp : L ≤ Real.exp P)
    (hCexp : C ≤ Real.exp P) (hKexp : K ≤ Real.exp P)
    (htail : D / cutoff ≤ Real.exp (-(E + 4)))
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ forecastJointGridMesh d P E) :
    forecastJointGridError dout dj dc cutoff D L C K δ ≤ Real.exp (-E) := by
  have hpref := forecastJointGridPrefactor_le_exp dout dj dc d hdout hdj hdc
    hP hE (by exact_mod_cast hcutoff) hTexp hD hL hC hK hDexp hLexp hCexp hKexp
  let H := ((d : ℝ) + 1) * (P + E + 5) + 6 * d + 2 * P + 4
  have hmesh : Real.exp H * δ ≤ Real.exp (-(E + 4)) := by
    calc
      _ ≤ Real.exp H * forecastJointGridMesh d P E :=
        mul_le_mul_of_nonneg_left hδsmall (Real.exp_nonneg _)
      _ = _ := by
        unfold forecastJointGridMesh forecastJointGridMeshLog H
        rw [← Real.exp_add]
        congr 1
        ring
  have hpre : forecastJointGridError dout dj dc cutoff D L C K δ ≤
      Real.exp H * δ + 2 * (D / cutoff) := by
    have hh := mul_le_mul_of_nonneg_right hpref hδ
    unfold forecastJointGridError
    dsimp only [H]
    nlinarith only [hh]
  have htotal : forecastJointGridError dout dj dc cutoff D L C K δ ≤
      3 * Real.exp (-(E + 4)) := by linarith only [hpre, hmesh, htail]
  have hthree : (3 : ℝ) ≤ Real.exp 4 := by linarith only [Real.add_one_le_exp (4 : ℝ)]
  refine htotal.trans ?_
  calc
    _ ≤ Real.exp 4 * Real.exp (-(E + 4)) :=
      mul_le_mul_of_nonneg_right hthree (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem forecastJointGridErrorBudget (d : ℕ) {P E : ℝ}
    (hP : 0 ≤ P) (hE : 0 ≤ E) :
    1 ≤ forecastJointGridCutoff P E ∧
    (forecastJointGridCutoff P E : ℝ) ≤ Real.exp (P + E + 5) ∧
    0 < forecastJointGridMesh d P E ∧ forecastJointGridMesh d P E ≤ 1 ∧
    ∀ {dout dj dc : ℕ}, dout ≤ d → dj ≤ d → dc ≤ d →
    ∀ {D L C K δ : ℝ}, 0 ≤ D → 0 ≤ L → 0 ≤ C → 0 ≤ K →
    D ≤ Real.exp P → L ≤ Real.exp P → C ≤ Real.exp P → K ≤ Real.exp P →
    0 ≤ δ → δ ≤ forecastJointGridMesh d P E →
    forecastJointGridError dout dj dc (forecastJointGridCutoff P E) D L C K δ ≤
      Real.exp (-E) := by
  have hm := forecastJointGridMesh_bounds d hP hE
  refine ⟨forecastJointGridCutoff_one_le P E, forecastJointGridCutoff_le_exp hP hE,
    hm.1, hm.2, ?_⟩
  intro dout dj dc hdout hdj hdc D L C K δ hD hL hC hK hDexp hLexp hCexp hKexp hδ hδsmall
  exact forecastJointGridError_absorb dout dj dc d (forecastJointGridCutoff P E)
    hdout hdj hdc hP hE (forecastJointGridCutoff_one_le P E)
    (forecastJointGridCutoff_le_exp hP hE) hD hL hC hK hDexp hLexp hCexp hKexp
    (forecastJointGridCutoff_tail_le hP hE hDexp) hδ hδsmall

end Erdos3

end

section

namespace Erdos3

theorem forecastModularCharge_exp_bound (m D Rbad Qpres : ℕ)
    {Pbad Ppres : ℝ} (hR : (Rbad : ℝ) ≤ Real.exp Pbad)
    (hQ : (Qpres : ℝ) ≤ Real.exp Ppres) :
    ((Rbad * Qpres : ℕ) : ℝ) ^
      (modularRankDecayExponent m (modularForecastRankConstant m D : ℝ) *
        modularRankChargeFactor m) ≤
      Real.exp ((Pbad + Ppres) * ((D + 2 : ℕ) : ℝ) * modularRankChargeFactor m) := by
  rw [modularForecastRankConstant_decay]
  have hbase : ((Rbad * Qpres : ℕ) : ℝ) ≤ Real.exp (Pbad + Ppres) := by
    rw [Nat.cast_mul, Real.exp_add]
    exact mul_le_mul hR hQ (Nat.cast_nonneg _) (Real.exp_nonneg _)
  calc
    _ ≤ (Real.exp (Pbad + Ppres)) ^
        (((D + 2 : ℕ) : ℝ) * modularRankChargeFactor m) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hbase (by positivity)
    _ = _ := by rw [← Real.exp_mul, mul_assoc]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FixedPathSlicedGridMeshBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem fixedPathSlicedGrid_ratio_le {S H q : ℕ} {cost : ℝ}
    (hS : 0 < S) (hH : Real.exp (-cost) * S ≤ (H : ℝ)) :
    (q : ℝ) / H ≤ Real.exp cost * ((q : ℝ) / S) := by
  have hs : (0 : ℝ) < S := Nat.cast_pos.mpr hS
  calc
    _ ≤ (q : ℝ) / (Real.exp (-cost) * S) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) (mul_pos (Real.exp_pos _) hs) hH
    _ = _ := by rw [Real.exp_neg]; field_simp

theorem fixedPathSlicedGrid_sum_ratio_le {Input : Type*} [Fintype Input]
    {D cost : ℝ} {S q : ℕ} (H : Input → ℕ)
    (hcard : (Fintype.card Input : ℝ) ≤ D) (hS : 0 < S)
    (hH : ∀ i, Real.exp (-cost) * S ≤ (H i : ℝ)) :
    (∑ i, (q : ℝ) / H i) ≤ D * Real.exp cost * ((q : ℝ) / S) := by
  calc
    _ ≤ ∑ _ : Input, Real.exp cost * ((q : ℝ) / S) :=
      Finset.sum_le_sum (fun i _ => fixedPathSlicedGrid_ratio_le hS (hH i))
    _ = (Fintype.card Input : ℝ) * (Real.exp cost * ((q : ℝ) / S)) := by simp
    _ ≤ D * (Real.exp cost * ((q : ℝ) / S)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

theorem fixedPathSlicedGridMeshFloor_lower (D C V cost E : ℝ) :
    Real.exp (fixedPathSlicedGridMeshLog D C V cost E) ≤
      (fixedPathSlicedGridMeshFloor D C V cost E : ℝ) := Nat.le_ceil _

theorem fixedPathSlicedGridMeshFloor_pos (D C V cost E : ℝ) :
    0 < fixedPathSlicedGridMeshFloor D C V cost E := by
  exact_mod_cast (Real.exp_pos _).trans_le (fixedPathSlicedGridMeshFloor_lower D C V cost E)

theorem fixedPathSlicedGridMesh_prefactor {D C V cost E : ℝ} {q S : ℕ}
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hq : (q : ℝ) ≤ Real.exp V)
    (hfloor : fixedPathSlicedGridMeshFloor D C V cost E ≤ S) :
    (D + C + 8) * (Real.exp cost * ((q : ℝ) / S)) ≤ Real.exp (-(E + 2)) := by
  have hp : (0 : ℝ) < D + C + 8 := by linarith
  have hS := (fixedPathSlicedGridMeshFloor_lower D C V cost E).trans
    (show (fixedPathSlicedGridMeshFloor D C V cost E : ℝ) ≤ S by exact_mod_cast hfloor)
  have hs : (0 : ℝ) < S := (Real.exp_pos _).trans_le hS
  have hnum : (D + C + 8) * Real.exp cost * (q : ℝ) ≤
      Real.exp (Real.log (D + C + 8) + V + cost) := by
    calc
      _ ≤ (D + C + 8) * Real.exp cost * Real.exp V :=
        mul_le_mul_of_nonneg_left hq (mul_nonneg hp.le (Real.exp_nonneg _))
      _ = _ := by rw [Real.exp_add, Real.exp_add, Real.exp_log hp]; ring
  rw [← mul_div_assoc, ← mul_div_assoc]
  apply (div_le_iff₀ hs).mpr
  calc
    _ ≤ Real.exp (Real.log (D + C + 8) + V + cost) := by simpa only [mul_assoc] using hnum
    _ = Real.exp (-(E + 2)) * Real.exp (fixedPathSlicedGridMeshLog D C V cost E) := by
      rw [← Real.exp_add]
      congr 1
      unfold fixedPathSlicedGridMeshLog
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hS (Real.exp_nonneg _)

theorem fixedPathSlicedGridMesh_of_floor {D C V cost E : ℝ}
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hE : 0 ≤ E)
    {Input : Type*} [Fintype Input] (H : Input → ℕ)
    (hcard : (Fintype.card Input : ℝ) ≤ D) {q S : ℕ}
    (hq0 : 0 < q) (hq : (q : ℝ) ≤ Real.exp V)
    (hfloor : fixedPathSlicedGridMeshFloor D C V cost E ≤ S)
    (hH : ∀ i, Real.exp (-cost) * S ≤ (H i : ℝ))
    (mesh : Input → ℝ) (hmesh : ∀ i, mesh i ≤ 2 * Real.exp cost / S) :
    (∑ i, (q : ℝ) / H i) ≤ Real.exp (-E) ∧
      (∀ i, C * ((q : ℝ) / H i) ≤ Real.exp (-E)) ∧
      (∀ i, mesh i ≤ Real.exp (-E)) ∧
      ∀ i, 2 ≤ H i ∧ q ≤ H i ∧
        scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H i) < 1 := by
  have hS := (fixedPathSlicedGridMeshFloor_pos D C V cost E).trans_le hfloor
  have hSr : (0 : ℝ) < S := Nat.cast_pos.mpr hS
  let r := Real.exp cost * ((q : ℝ) / S)
  have hr : 0 ≤ r := by dsimp only [r]; positivity
  have hbound := fixedPathSlicedGridMesh_prefactor hD hC hq hfloor
  have hsmall : Real.exp (-(E + 2)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have he : Real.exp (-(E + 2)) ≤ Real.exp (-E) := Real.exp_le_exp.mpr (by linarith)
  have hmajor {a : ℝ} (ha : a ≤ D + C + 8) : a * r ≤ Real.exp (-(E + 2)) :=
    (mul_le_mul_of_nonneg_right ha hr).trans hbound
  have hratio (i : Input) : (q : ℝ) / H i ≤ r := fixedPathSlicedGrid_ratio_le hS (hH i)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hsum := fixedPathSlicedGrid_sum_ratio_le (q := q) H hcard hS hH
    have hsummajor : D * Real.exp cost * ((q : ℝ) / S) ≤ Real.exp (-(E + 2)) := by
      simpa only [mul_assoc, r] using hmajor (show D ≤ D + C + 8 by linarith)
    exact hsum.trans (hsummajor.trans he)
  · intro i
    exact ((mul_le_mul_of_nonneg_left (hratio i) hC).trans
      (hmajor (show C ≤ D + C + 8 by linarith))).trans he
  · intro i
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq0
    have htwo : 2 * Real.exp cost / S ≤ 2 * r := by
      dsimp only [r]
      rw [mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right
        (le_mul_of_one_le_right (Real.exp_nonneg _) hq1) hSr.le
    exact ((hmesh i).trans htwo).trans
      ((hmajor (show (2 : ℝ) ≤ D + C + 8 by linarith)).trans he)
  · intro i
    have hHi : (0 : ℝ) < H i := (mul_pos (Real.exp_pos _) hSr).trans_le (hH i)
    have hfour : 4 * ((q : ℝ) / H i) < 1 :=
      ((mul_le_mul_of_nonneg_left (hratio i) (by norm_num : (0 : ℝ) ≤ 4)).trans
        (hmajor (show (4 : ℝ) ≤ D + C + 8 by linarith))).trans_lt hsmall
    have hratio1 : (q : ℝ) / H i < 1 := by
      have hn : (0 : ℝ) ≤ (q : ℝ) / H i := by positivity
      linarith
    have hqH : q < H i := Nat.cast_lt.mp ((div_lt_one hHi).mp hratio1)
    refine ⟨by omega, hqH.le, ?_⟩
    have hconst : scalarCubeGridBoundaryConstant Empty = 4 := by
      norm_num [scalarCubeGridBoundaryConstant]
    rwa [hconst]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedPerturbativeSeedPowerBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : {a : LayerSamplerAxis I n // ¬short a},
  B (Subtype.val a) × Fin (degree (Subtype.val a)))

theorem allocatedOriginalSampleLiftLip_eq_card :
    allocatedOriginalSampleLiftLip B U basis S = (Fintype.card Input : ℝ≥0) * m := rfl

theorem allocatedOriginalSampleFullSliceLip_le_two {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    allocatedOriginalSampleFullSliceLip B U basis S t ≤
      2 * allocatedOriginalSampleLiftLip B U basis S := by
  unfold allocatedOriginalSampleFullSliceLip
  apply mul_le_mul_of_nonneg_right _ zero_le
  apply NNReal.coe_le_coe.mp
  simp only [NNReal.coe_add, NNReal.coe_one, NNReal.coe_ofNat,
    abs_of_nonneg ht0, Real.coe_toNNReal t ht0]
  linarith

theorem allocatedOriginalSampleFullSliceLip_coe_le_two {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (allocatedOriginalSampleFullSliceLip B U basis S t : ℝ) ≤
      2 * (allocatedOriginalSampleLiftLip B U basis S : ℝ) := by
  exact_mod_cast allocatedOriginalSampleFullSliceLip_le_two B U basis S ht0 ht1

theorem allocatedOriginalSampleLiftInput_card_le_allAxis :
    Fintype.card Input ≤ Fintype.card (PrincipalTupleIndex B degree) := by
  simp only [PrincipalTupleIndex, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  apply Finset.sum_le_sum_of_injOn Subtype.val
    (fun _ _ _ _ h => Subtype.val_injective h) (Finset.subset_univ _)
  · intro a _
    exact le_rfl
  · intro a _ _
    exact Nat.zero_le _

theorem allocatedOriginalSampleLiftLip_le_fullInputCount :
    allocatedOriginalSampleLiftLip B U basis S ≤
      (Fintype.card (PrincipalTupleIndex B degree) : ℝ≥0) * m := by
  rw [allocatedOriginalSampleLiftLip_eq_card]
  apply mul_le_mul_of_nonneg_right _ zero_le
  exact_mod_cast allocatedOriginalSampleLiftInput_card_le_allAxis B U basis S

theorem allocatedOriginalSampleLiftLip_coe_le_allAxis :
    (allocatedOriginalSampleLiftLip B U basis S : ℝ) ≤
      (Fintype.card (PrincipalTupleIndex B degree) : ℝ) * (m : ℝ) := by
  exact_mod_cast allocatedOriginalSampleLiftLip_le_fullInputCount B U basis S

theorem allocatedOriginalSampleLiftLip_le_exp_of_allAxis {P : ℝ}
    (hcount : (Fintype.card (PrincipalTupleIndex B degree) : ℝ) * (m : ℝ) ≤ P) :
    (allocatedOriginalSampleLiftLip B U basis S : ℝ) ≤ Real.exp P := by
  exact (allocatedOriginalSampleLiftLip_coe_le_allAxis B U basis S).trans
    (hcount.trans (by linarith [Real.add_one_le_exp P]))

theorem allocatedOriginalSampleFullSliceLip_le_two_exp_of_allAxis
    {P t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hcount : (Fintype.card (PrincipalTupleIndex B degree) : ℝ) * (m : ℝ) ≤ P) :
    (allocatedOriginalSampleFullSliceLip B U basis S t : ℝ) ≤ 2 * Real.exp P :=
  (allocatedOriginalSampleFullSliceLip_coe_le_two B U basis S ht0 ht1).trans
    (mul_le_mul_of_nonneg_left
      (allocatedOriginalSampleLiftLip_le_exp_of_allAxis B U basis S hcount) (by norm_num))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastAmbientPrecision
namespace OAI

section

namespace Erdos3

theorem forecast_ambient_exp_error {δ M Q A E : ℝ}
    (hδ : δ ≤ Real.exp (-(E + 4))) (hM : M ≤ Real.exp Q)
    (hA : Q + E + 4 ≤ A) :
    2 * δ + M * Real.exp (-A) ≤ Real.exp (-E) := by
  have hterm : M * Real.exp (-A) ≤ Real.exp (-(E + 4)) := by
    calc
      _ ≤ Real.exp Q * Real.exp (-A) :=
        mul_le_mul_of_nonneg_right hM (Real.exp_nonneg _)
      _ = Real.exp (Q - A) := by rw [sub_eq_add_neg, Real.exp_add]
      _ ≤ Real.exp (-(E + 4)) := Real.exp_le_exp.mpr (by linarith)
  have h3 : (3 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  calc
    _ ≤ 3 * Real.exp (-(E + 4)) := by linarith
    _ ≤ Real.exp 4 * Real.exp (-(E + 4)) :=
      mul_le_mul_of_nonneg_right h3 (Real.exp_nonneg _)
    _ = Real.exp (-E) := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedFixedPathAmbientUniformPrecision
namespace OAI

section

namespace Erdos3

theorem fixedPathAmbientScalarPrecision_ambient {Q E M : ℝ}
    (hM : M ≤ Real.exp Q) :
    2 * fixedPathForecastTolerance E + M * Real.exp (-fixedPathAmbientPrecision Q E) ≤
      Real.exp (-fixedPathComparisonPrecision E) := by
  apply forecast_ambient_exp_error (Q := Q)
  · unfold fixedPathForecastTolerance fixedPathComparisonPrecision
    apply Real.exp_le_exp.mpr
    linarith
  · exact hM
  · unfold fixedPathComparisonPrecision fixedPathAmbientPrecision
    linarith

theorem fixedPathAmbientScalarPrecision_error {Q E M sourceError : ℝ}
    (hM : M ≤ Real.exp Q)
    (hsource : sourceError ≤ Real.exp (-fixedPathComparisonPrecision E)) :
    sourceError + Real.exp (-fixedPathComparisonPrecision E) +
      (2 * fixedPathForecastTolerance E + M * Real.exp (-fixedPathAmbientPrecision Q E)) ≤
      Real.exp (-E) := by
  have hambient := fixedPathAmbientScalarPrecision_ambient (E := E) hM
  have hthree : (3 : ℝ) ≤ Real.exp 4 := by
    linarith only [Real.add_one_le_exp (4 : ℝ)]
  calc
    _ ≤ 3 * Real.exp (-fixedPathComparisonPrecision E) := by
      linarith only [hsource, hambient]
    _ ≤ Real.exp 4 * Real.exp (-fixedPathComparisonPrecision E) :=
      mul_le_mul_of_nonneg_right hthree (Real.exp_nonneg _)
    _ = Real.exp (-E) := by
      rw [← Real.exp_add]
      unfold fixedPathComparisonPrecision
      congr 1
      ring

end Erdos3

end

section

namespace Erdos3

theorem fixedPathSlicedAmbientScalarPrecision_error
    (dout dj dc d : ℕ) (hdout : dout ≤ d) (hdj : dj ≤ d) (hdc : dc ≤ d)
    {Pg E Q Mmass sourceError Dgrid L C K δgrid : ℝ}
    (hPg : 0 ≤ Pg) (hE : 0 ≤ E)
    (hsource : sourceError ≤ Real.exp (-(E + 4))) (hM : Mmass ≤ Real.exp Q)
    (hD : 0 ≤ Dgrid) (hL : 0 ≤ L) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hDP : Dgrid ≤ Real.exp Pg) (hLP : L ≤ Real.exp Pg)
    (hCP : C ≤ Real.exp Pg) (hKP : K ≤ Real.exp Pg)
    (hδ : 0 ≤ δgrid) (hmesh : δgrid ≤ forecastJointGridMesh d Pg (E + 4)) :
    sourceError + (2 * Real.exp (-(E + 8)) + Mmass * Real.exp (-(Q + E + 8))) +
      forecastJointGridError dout dj dc (forecastJointGridCutoff Pg (E + 4))
        Dgrid L C K δgrid ≤ Real.exp (-E) := by
  have hgrid := (forecastJointGridErrorBudget d hPg (show 0 ≤ E + 4 by linarith)).2.2.2.2
    hdout hdj hdc hD hL hC hK hDP hLP hCP hKP hδ hmesh
  have htotal := fixedPathAmbientScalarPrecision_error hM hsource
  dsimp only [fixedPathComparisonPrecision, fixedPathForecastTolerance,
    fixedPathAmbientPrecision] at htotal
  linarith only [hgrid, htotal]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FixedPathSlicedSourceErrorScalar
namespace OAI

section

namespace Erdos3

theorem fixedPathSlicedSourceError_eq (rP rG C K Kφ ε η ξ : ℝ) :
    fixedPathSlicedSourceError rP rG C K Kφ ε η ξ =
      (1 + 4 * C + 4 * K) * rP + (1 + 4 * C + 3 * Kφ) * rG +
        (2 * K) * ε + 2 * η + Kφ * ξ := by
  unfold fixedPathSlicedSourceError
  ring

theorem fixedPathSlicedSourceError_le_prefactor {P rP rG C K Kφ ε η ξ : ℝ}
    (hP : 0 ≤ P) (hC : C ≤ Real.exp P) (hK : K ≤ Real.exp P) (hφ : Kφ ≤ Real.exp P)
    (hrP : 0 ≤ rP) (hrG : 0 ≤ rG) (hε : 0 ≤ ε) (hη : 0 ≤ η) (hξ : 0 ≤ ξ) :
    fixedPathSlicedSourceError rP rG C K Kφ ε η ξ ≤
      Real.exp (P + 4) * (rP + rG + ε + η + ξ) := by
  have hone : (1 : ℝ) ≤ Real.exp P := Real.one_le_exp hP
  have hnine : (9 : ℝ) ≤ Real.exp 4 := by
    have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)
    norm_num at h
    linarith
  have hbudget : 9 * Real.exp P ≤ Real.exp (P + 4) := by
    rw [Real.exp_add]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hnine (Real.exp_nonneg P)
  have hp : 1 + 4 * C + 4 * K ≤ Real.exp (P + 4) :=
    (show 1 + 4 * C + 4 * K ≤ 9 * Real.exp P by linarith).trans hbudget
  have hg : 1 + 4 * C + 3 * Kφ ≤ Real.exp (P + 4) :=
    (show 1 + 4 * C + 3 * Kφ ≤ 9 * Real.exp P by linarith).trans hbudget
  have he : 2 * K ≤ Real.exp (P + 4) :=
    (show 2 * K ≤ 9 * Real.exp P by linarith).trans hbudget
  have hh : (2 : ℝ) ≤ Real.exp (P + 4) :=
    (show (2 : ℝ) ≤ 9 * Real.exp P by linarith).trans hbudget
  have hx : Kφ ≤ Real.exp (P + 4) :=
    (show Kφ ≤ 9 * Real.exp P by linarith).trans hbudget
  rw [fixedPathSlicedSourceError_eq]
  calc
    _ ≤ Real.exp (P + 4) * rP + Real.exp (P + 4) * rG +
        Real.exp (P + 4) * ε + Real.exp (P + 4) * η + Real.exp (P + 4) * ξ :=
      add_le_add (add_le_add (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right hp hrP) (mul_le_mul_of_nonneg_right hg hrG))
        (mul_le_mul_of_nonneg_right he hε)) (mul_le_mul_of_nonneg_right hh hη))
        (mul_le_mul_of_nonneg_right hx hξ)
    _ = _ := by ring

theorem fixedPathSlicedSourceError_absorb_sharp {P E rP rG C K Kφ ε η ξ : ℝ}
    (hP : 0 ≤ P) (hC : C ≤ Real.exp P) (hK : K ≤ Real.exp P) (hφ : Kφ ≤ Real.exp P)
    (hrP : 0 ≤ rP) (hrG : 0 ≤ rG) (hε : 0 ≤ ε) (hη : 0 ≤ η) (hξ : 0 ≤ ξ)
    (hrPs : rP ≤ Real.exp (-(P + E + 7)))
    (hrGs : rG ≤ Real.exp (-(P + E + 7)))
    (hεs : ε ≤ Real.exp (-(P + E + 7)))
    (hηs : η ≤ Real.exp (-(P + E + 7)))
    (hξs : ξ ≤ Real.exp (-(P + E + 7))) :
    fixedPathSlicedSourceError rP rG C K Kφ ε η ξ ≤ Real.exp (-E) := by
  have hpre := fixedPathSlicedSourceError_le_prefactor hP hC hK hφ hrP hrG hε hη hξ
  have hsum : rP + rG + ε + η + ξ ≤ 5 * Real.exp (-(P + E + 7)) := by linarith
  have hfive : (5 : ℝ) ≤ Real.exp 3 := by
    have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)
    norm_num at h
    linarith
  calc
    _ ≤ Real.exp (P + 4) * (5 * Real.exp (-(P + E + 7))) :=
      hpre.trans (mul_le_mul_of_nonneg_left hsum (Real.exp_nonneg _))
    _ = 5 * Real.exp (-(E + 3)) := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp 3 * Real.exp (-(E + 3)) :=
      mul_le_mul_of_nonneg_right hfive (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem fixedPathSlicedSourceError_absorb {P E rP rG C K Kφ ε η ξ : ℝ}
    (hP : 0 ≤ P) (_hE : 0 ≤ E) (_hC0 : 0 ≤ C) (_hK0 : 0 ≤ K) (_hKφ0 : 0 ≤ Kφ)
    (hCP : C ≤ Real.exp P) (hKP : K ≤ Real.exp P) (hKφP : Kφ ≤ Real.exp P)
    (hrP : 0 ≤ rP) (hrG : 0 ≤ rG) (hε : 0 ≤ ε) (hη : 0 ≤ η) (hξ : 0 ≤ ξ)
    (hrPs : rP ≤ Real.exp (-(P + E + 12)))
    (hrGs : rG ≤ Real.exp (-(P + E + 12)))
    (hεs : ε ≤ Real.exp (-(P + E + 12)))
    (hηs : η ≤ Real.exp (-(P + E + 12)))
    (hξs : ξ ≤ Real.exp (-(P + E + 12))) :
    fixedPathSlicedSourceError rP rG C K Kφ ε η ξ ≤ Real.exp (-E) := by
  have hbudget : Real.exp (-(P + E + 12)) ≤ Real.exp (-(P + E + 7)) :=
    Real.exp_le_exp.mpr (by linarith)
  exact fixedPathSlicedSourceError_absorb_sharp hP hCP hKP hKφP hrP hrG hε hη hξ
    (hrPs.trans hbudget) (hrGs.trans hbudget) (hεs.trans hbudget)
    (hηs.trans hbudget) (hξs.trans hbudget)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedFixedPathSlicedSourceErrorBudget
namespace OAI

section

namespace Erdos3
open scoped BigOperators NNReal Classical

theorem fixedPathSliceWidth_lower {cost : ℝ} {S step H : ℕ}
    (hS : 0 < S) (hstep : 0 < step) (hH : 2 ≤ H)
    (hdense : Real.exp (-cost) * S ≤ (H : ℝ)) :
    Real.exp (-cost) / 2 ≤ (step : ℝ) * ((H : ℝ) - 1) / S := by
  have hSr : (0 : ℝ) < S := Nat.cast_pos.mpr hS
  have hHr : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hstepr : (1 : ℝ) ≤ step := by exact_mod_cast hstep
  apply (le_div_iff₀ hSr).mpr
  calc
    Real.exp (-cost) / 2 * S = (Real.exp (-cost) * S) / 2 := by ring
    _ ≤ (H : ℝ) / 2 := div_le_div_of_nonneg_right hdense (by norm_num)
    _ ≤ (H : ℝ) - 1 := by linarith
    _ ≤ (step : ℝ) * ((H : ℝ) - 1) :=
      le_mul_of_one_le_left (by linarith) hstepr

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem fixedPathSlicedGridMesh_scalar_of_floor {D C V cost E : ℝ} {q S : ℕ}
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hq0 : 0 < q) (hq : (q : ℝ) ≤ Real.exp V)
    (hfloor : fixedPathSlicedGridMeshFloor D C V cost E ≤ S) :
    2 * Real.exp cost / S ≤ Real.exp (-E) := by
  have hS := (fixedPathSlicedGridMeshFloor_pos D C V cost E).trans_le hfloor
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq0
  have hr : 0 ≤ Real.exp cost * ((q : ℝ) / S) := by positivity
  calc
    _ ≤ 2 * (Real.exp cost * ((q : ℝ) / S)) := by
      rw [mul_div_assoc, ← mul_div_assoc (Real.exp cost)]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact div_le_div_of_nonneg_right
        (le_mul_of_one_le_right (Real.exp_nonneg _) hq1) (Nat.cast_nonneg _)
    _ ≤ (D + C + 8) * (Real.exp cost * ((q : ℝ) / S)) :=
      mul_le_mul_of_nonneg_right (by linarith) hr
    _ ≤ Real.exp (-(E + 2)) := fixedPathSlicedGridMesh_prefactor hD hC hq hfloor
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem fixedPathSlicedSourceErrorBudget_of_floor
    {D P V cost E : ℝ} (hD : 0 ≤ D) (hP : 2 ≤ P) (hE : 0 ≤ E)
    {Input Kernel : Type*} [Fintype Input] [Fintype Kernel]
    (HP : Input → ℕ) (HG : Kernel → ℕ)
    (hInput : (Fintype.card Input : ℝ) ≤ D) (hKernel : (Fintype.card Kernel : ℝ) ≤ D)
    {q S : ℕ} (hq0 : 0 < q) (hq : (q : ℝ) ≤ Real.exp V)
    (hfloor : fixedPathSlicedGridMeshFloor D 4 V cost (P + E + 12) ≤ S)
    (hHP : ∀ i, Real.exp (-cost) * S ≤ (HP i : ℝ))
    (hHG : ∀ i, Real.exp (-cost) * S ≤ (HG i : ℝ))
    {K Kφ ξ : ℝ} (hK0 : 0 ≤ K) (hKφ0 : 0 ≤ Kφ) (hξ0 : 0 ≤ ξ)
    (hK : K ≤ Real.exp P) (hKφ : Kφ ≤ Real.exp P)
    (hξ : ξ ≤ Real.exp (-(P + E + 12))) :
    (∀ i, 2 ≤ HP i ∧ q ≤ HP i ∧
      scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / HP i) < 1) ∧
    (∀ i, 2 ≤ HG i ∧ q ≤ HG i ∧
      scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / HG i) < 1) ∧
    fixedPathSlicedSourceError (∑ i, (q : ℝ) / HP i) (∑ i, (q : ℝ) / HG i)
      (scalarCubeGridBoundaryConstant Empty) K Kφ (2 * Real.exp cost / S)
      (Real.exp (-(P + E + 12))) ξ ≤ Real.exp (-E) := by
  have hP0 : 0 ≤ P := by linarith
  have hF : 0 ≤ P + E + 12 := by positivity
  have hPmesh := fixedPathSlicedGridMesh_of_floor hD (by norm_num : (0 : ℝ) ≤ 4) hF
    HP hInput hq0 hq hfloor hHP (fun _ => 2 * Real.exp cost / S) (fun _ => le_rfl)
  have hGmesh := fixedPathSlicedGridMesh_of_floor hD (by norm_num : (0 : ℝ) ≤ 4) hF
    HG hKernel hq0 hq hfloor hHG (fun _ => 2 * Real.exp cost / S) (fun _ => le_rfl)
  have hC : scalarCubeGridBoundaryConstant Empty = 4 := by
    norm_num [scalarCubeGridBoundaryConstant]
  have hCP : scalarCubeGridBoundaryConstant Empty ≤ Real.exp P := by
    rw [hC]
    have he := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    norm_num at he
    exact (by linarith : (4 : ℝ) ≤ Real.exp 2).trans (Real.exp_le_exp.mpr hP)
  refine ⟨hPmesh.2.2.2, hGmesh.2.2.2, ?_⟩
  apply fixedPathSlicedSourceError_absorb hP0 hE
    (by rw [hC]; norm_num) hK0 hKφ0 hCP hK hKφ
    (by positivity) (by positivity) (by positivity) (Real.exp_nonneg _) hξ0
    hPmesh.1 hGmesh.1
    (fixedPathSlicedGridMesh_scalar_of_floor hD (by norm_num) hq0 hq hfloor)
    le_rfl hξ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankCongruenceOutput
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

theorem spatialDegreeOutput_card [Fintype X] (j : Fin m) :
    Fintype.card (SpatialDegreeOutput X j) = if j.val = 0 then Fintype.card X else 0 := by
  rw [Fintype.card_subtype]
  by_cases hj : j.val = 0 <;> simp only [hj, ite_true, ite_false, Finset.filter_true,
    Finset.filter_false, Finset.card_univ, Finset.card_empty]

theorem spatialDegreeOutput_sum_card [Fintype X] (hm : 0 < m) :
    (∑ j : Fin m, Fintype.card (SpatialDegreeOutput X j)) = Fintype.card X := by
  simp_rw [spatialDegreeOutput_card]
  rw [Finset.sum_eq_single (⟨0, hm⟩ : Fin m)]
  · rfl
  · intro j _ hj
    have hne : j.val ≠ 0 := fun he => hj (Fin.ext he)
    simp only [hne, ite_false]
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}

theorem allocatedCongruenceRankOutput_card_le [Fintype X] [∀ j, Fintype (E j)]
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) :
    Fintype.card (AllocatedCongruenceRankOutput X E inactive j) ≤
      Fintype.card (SpatialDegreeOutput X j) + (Fintype.card (E j) + n j) := by
  change Fintype.card (SpatialDegreeOutput X j ⊕
    (E j ⊕ AllocatedCongruenceIntegerAxis inactive j)) ≤ _
  simp only [Fintype.card_sum]
  apply Nat.add_le_add_left
  apply Nat.add_le_add_left
  simpa only [Fintype.card_fin] using Fintype.card_subtype_le
    (fun i : Fin (n j) => ¬ inactive ⟨j, Sum.inr i⟩)

theorem allocatedCongruenceRankOutput_sum_card_le [Fintype X] [∀ j, Fintype (E j)]
    (hm : 0 < m) (inactive : LayerSamplerAxis I n → Prop) :
    (∑ j : Fin m, Fintype.card (AllocatedCongruenceRankOutput X E inactive j)) ≤
      Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) := by
  calc
    _ ≤ ∑ j : Fin m,
        (Fintype.card (SpatialDegreeOutput X j) + (Fintype.card (E j) + n j)) :=
      Finset.sum_le_sum (fun j _ => allocatedCongruenceRankOutput_card_le inactive j)
    _ = _ := by rw [Finset.sum_add_distrib, spatialDegreeOutput_sum_card hm]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedFixedPathSlicedNativeAmbientComparison
namespace OAI

section

namespace Erdos3
open scoped BigOperators NNReal Classical

namespace VectorPolynomial
variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

theorem allocatedSlicedPhysicalComparisonError_eq_sourceError
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (ξ : ℝ) (HG : G → ℕ)
    (H : PrincipalTupleIndex
      (fun a : {a // ¬allocatedShortAxis (I := I) U basis S.value a} => B a.val)
      (fun a => layerSamplerDegree I n a.val) → ℕ)
    (q : ℕ) {t ε η : ℝ} (Kφ : ℝ≥0) :
    allocatedSlicedPhysicalComparisonError B U basis S ξ HG (t := t) H q
      (ε := ε) (η := η) (Kφ := Kφ) =
    fixedPathSlicedSourceError (∑ j, (q : ℝ) / H j) (∑ g, (q : ℝ) / HG g)
      (scalarCubeGridBoundaryConstant Empty)
      ((Kφ : ℝ) * allocatedOriginalSampleFullSliceLip B U basis S t) Kφ ε η ξ := by
  simp only [allocatedSlicedPhysicalComparisonError, fixedPathSlicedSourceError, NNReal.coe_mul]
  ring

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ActualFixedSpatialSlicedGridErrorIdentification
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [decX : DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp))
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0)) (S.value : ℝ) physicalN τ δslice P Pbad Ppres)

omit [Fintype Tsp] in
theorem ambientGridError_eq_forecastJointGridError (ξ : ℝ)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Lip : ℝ≥0} {δ δgrid : ℝ} (hδ : 0 < δ) (cutoff : ℕ) :
    allocatedSlicedPhysicalAmbientGridError (B := B) (U := U) (basis := b) (S := S) (E := Eout)
      (τ := τ) (ξ := ξ) (box := physicalN) (integerFrame := slice.path.noise)
      (HG := slice.kernelLength) (hHG := slice.kernelLength_two) (cG := slice.kernelStart)
      (stepG := slice.step) (hstepG := slice.step_pos) (e := spatialEquiv)
      (h0 := slice.analyticKernelDetFalse ξ) (h1 := slice.analyticKernelDetTrue ξ)
      (hδ := hδ) (o := o) (Lip := Lip) (cutoff := cutoff) (D := slice.decayConstant) (δgrid := δgrid) =
    forecastJointGridError
      (Fintype.card (Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U b S.value))))
      (Fintype.card (X ⊕ AllocatedActiveIntegerAxis U b S.value))
      (Fintype.card (Σ j, I j)) cutoff slice.decayConstant
      (fixedSpatialOriginalForecastLip B (slice.slicedBlockEquiv false)
        (slice.slicedBlockEquiv true) (div_pos hδ (by norm_num : (0 : ℝ) < 2)))
      (fixedSpatialOriginalForecastCap B (slice.slicedBlockEquiv true) (div_pos hδ (by norm_num : (0 : ℝ) < 2)))
      (Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U b o R)) δgrid := by
  cases Subsingleton.elim decX (Classical.decEq X)
  let := Classical.decEq X
  unfold allocatedSlicedPhysicalAmbientGridError
  dsimp only
  unfold slicedBlockEquiv
  congr 4

end ActualFixedSpatialSlicedForecastPath

namespace ActualFixedSpatialForecastSetup

variable {B U b S Dmod τ δslice}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ δslice)

include s in
omit decX in
theorem gridDimensions_le :
    Fintype.card (Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U b S.value))) ≤
        Dmod + Fintype.card (Σ j, I j) ∧
      Fintype.card (X ⊕ AllocatedActiveIntegerAxis U b S.value) ≤
        Dmod + Fintype.card (Σ j, I j) ∧
      Fintype.card (Σ j, I j) ≤ Dmod + Fintype.card (Σ j, I j) := by
  have hout : Fintype.card (Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value))) ≤ Dmod := by
    rw [Fintype.card_sigma]
    exact (allocatedCongruenceRankOutput_sum_card_le s.hm (allocatedShortAxis (I := I) U b S.value)).trans s.hDmod
  have hi : Fintype.card (AllocatedActiveIntegerAxis U b S.value) ≤ ∑ j, n j := by
    calc
      _ ≤ Fintype.card (Σ j : Fin m, Fin (n j)) :=
        Fintype.card_le_of_injective (fun a : AllocatedActiveIntegerAxis U b S.value => a.val)
          (fun _ _ h => Subtype.ext h)
      _ = _ := by simp
  have hjoint : Fintype.card (X ⊕ AllocatedActiveIntegerAxis U b S.value) ≤ Dmod := by
    rw [Fintype.card_sum]
    calc
      _ ≤ Fintype.card X + ∑ j : Fin m, n j := Nat.add_le_add_left hi _
      _ ≤ Fintype.card X + ∑ j : Fin m, (Fintype.card (Eout j) + n j) :=
        Nat.add_le_add_left (Finset.sum_le_sum (fun j _ => Nat.le_add_left _ _)) _
      _ ≤ _ := s.hDmod
  exact ⟨hout.trans (Nat.le_add_right _ _), hjoint.trans (Nat.le_add_right _ _), Nat.le_add_left _ _⟩

end ActualFixedSpatialForecastSetup
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedModelPrecision
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {X : Type} [Fintype X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {A : Type} {Dmod : ℕ} {selected : A → Σ j : Fin m, Fin (n j)}
variable {τ δslice : ℝ}

namespace ActualFixedSpatialForecastSetup

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (hR : ∀ j, 0 < R j)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

include s hR

theorem inverse_radius_le_one (j : Fin m) :
    s.inverse j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 := by
  have hnonneg : 0 ≤ s.inverse j * ((Fintype.card (I j) : ℝ) + 1) * R j :=
    mul_nonneg (mul_nonneg (s.hinverse j) (by positivity)) (hR j).le
  have hbudget := s.hbudget j
  have hcompare := mul_le_mul_of_nonneg_right
    (show (1 : ℝ) ≤ 2 * (s.radius : ℝ) by linarith [s.hr3]) hnonneg
  nlinarith

theorem nativeAmbientLip_le_one : forecastNativeAmbientLip U b o R ≤ 1 := by
  change ‖(forecastNativeAmbientLinear U b o R).toContinuousLinearMap‖ ≤ (1 : ℝ)
  apply (forecastNativeAmbientLinear U b o R).toContinuousLinearMap.opNorm_le_bound zero_le_one
  intro v
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
  intro a
  have hcoord (k : LayerSamplerAxis I n) :
      |R a.1 * v k| ≤ R a.1 * ‖v‖ := by
    rw [abs_mul, abs_of_pos (hR a.1)]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v k) (hR a.1).le
  have hrow := mixedRealPoint_norm_le (euclideanSubspace (U a.1)) (b a.1) (o a.1)
    (s.hinverse a.1) (mul_nonneg (hR a.1).le (norm_nonneg v)) (s.hchart a.1)
    (fun i => R a.1 * v ⟨a.1, Sum.inl i⟩)
    (fun i => R a.1 * v ⟨a.1, Sum.inr i⟩)
    (fun i => hcoord ⟨a.1, Sum.inl i⟩) (fun i => hcoord ⟨a.1, Sum.inr i⟩)
  have hpoint := (PiLp.norm_apply_le (mixedRealPoint (euclideanSubspace (U a.1))
    (b a.1) (o a.1) ((fun i => R a.1 * v ⟨a.1, Sum.inl i⟩),
      fun i => R a.1 * v ⟨a.1, Sum.inr i⟩)) a.2).trans hrow
  change ‖mixedRealPoint (euclideanSubspace (U a.1)) (b a.1) (o a.1)
    ((fun i => R a.1 * v ⟨a.1, Sum.inl i⟩),
      fun i => R a.1 * v ⟨a.1, Sum.inr i⟩) a.2‖ ≤ _
  apply hpoint.trans
  calc
    _ = (s.inverse a.1 * ((Fintype.card (I a.1) : ℝ) + 1) * R a.1) * ‖v‖ := by ring
    _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right (s.inverse_radius_le_one hR a.1) (norm_nonneg v)
    _ = ‖v‖ := one_mul _

theorem nativePullbackLip_le {Lip : ℝ≥0} (hτ1 : τ ≤ 1) :
    Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U b o R) ≤ Lip := by
  have hτnorm : ‖τ / 8‖₊ ≤ (1 : ℝ≥0) := by
    change ‖τ / 8‖ ≤ (1 : ℝ)
    rw [Real.norm_of_nonneg (div_nonneg s.hτ.le (by norm_num))]
    linarith
  exact (mul_le_mul_of_nonneg_left (max_le hτnorm (s.nativeAmbientLip_le_one hR o))
    (show 0 ≤ Lip from zero_le)).trans_eq
    (mul_one _)

end ActualFixedSpatialForecastSetup
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp] {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {physicalN : X → ℕ} {τ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ (Real.exp (-cost) / 2))
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0))
  (S.value : ℝ) physicalN τ (Real.exp (-cost) / 2) s.P s.Pbad s.Ppres)

namespace ActualFixedSpatialSlicedForecastPath

omit [Fintype Tsp] in
theorem decayConstant_le_exp :
    slice.decayConstant ≤
      Real.exp ((s.Pbad + s.Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m) :=
  forecastModularCharge_exp_bound m Dmod slice.path.Rbad
    (∏ p : slice.path.primes, p.val ^ slice.path.prescribed p.val)
    slice.path.RbadBound slice.path.presBound

omit [Fintype Tsp] in
theorem kernelWidth_lower_of_length
    (hHG : ∀ g, Real.exp (-cost) * S.value ≤ (slice.kernelLength g : ℝ)) :
    ∀ g, Real.exp (-(cost + 1)) ≤ slice.kernelWidth g := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hexp : Real.exp (-(cost + 1)) ≤ Real.exp (-cost) / 2 := by
    have he := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg (-(cost + 1)))
    have heq : Real.exp 1 * Real.exp (-(cost + 1)) = Real.exp (-cost) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq] at he
    linarith
  intro g
  apply hexp.trans
  have hwidth := fixedPathSliceWidth_lower S.positive slice.step_pos (slice.kernelLength_two g) (hHG g)
  change Real.exp (-cost) / 2 ≤ (slice.step : ℝ) * ((slice.kernelLength g - 1 : ℕ) : ℝ) / S.value
  rw [Nat.cast_sub (show 1 ≤ slice.kernelLength g by have := slice.kernelLength_two g; omega), Nat.cast_one]
  exact hwidth

theorem comparisonError_le_exp_s2_oai
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Lip : ℝ≥0} {Pu V E Edata Q ξ Mmass : ℝ}
    (hcost : 0 ≤ cost) (hPu : 2 ≤ Pu) (hE : 0 ≤ E)
    (hDsq : s.D * s.D ≤ Pu) (hAL : (s.L : ℝ) ≤ Real.exp Pu)
    (hτ1 : τ ≤ 1) (hLip : (Lip : ℝ) ≤ Real.exp Pu)
    (q : ℕ) [NeZero q] (hq : (q : ℝ) ≤ Real.exp V)
    (hfloor : comparisonPrecisionFloor s (Dmod + Fintype.card (Σ j, I j)) Pu V E ≤ S.value)
    (hHP : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      ∀ p : B a.val × Fin (layerSamplerDegree I n a.val),
        Real.exp (-cost) * S.value ≤ (slice.principalLength ⟨a.val,p⟩ : ℝ))
    (hHG : ∀ g, Real.exp (-cost) * S.value ≤ (slice.kernelLength g : ℝ))
    (hξ0 : 0 ≤ ξ) (hξ : ξ ≤ Real.exp (-(2 * Pu + (E + 4) + 14)))
    (hM : Mmass ≤ Real.exp Q) (hEdata : E + 8 ≤ Edata) :
    let d := Dmod + Fintype.card (Σ j, I j)
    let F := 2 * Pu + (E + 4) + 14
    let η := Real.exp (-F)
    let t := Real.exp (-fixedPathSlicedPerturbationLog s.D (s.D + Pu + 4) (cost + 1) F m)
    let Pg := comparisonGridLog s Pu
    slice.comparisonError (Lip := Lip) (ξ := ξ) (t := t) (δ := Real.exp (-cost))
      (ε := 2 * Real.exp cost / S.value) (η := η) (q := q) (hδ := Real.exp_pos _)
      (o := o) (δnative := Real.exp (-Edata)) (M := Mmass) (Eprec := Q + E + 8)
      (cutoff := forecastJointGridCutoff Pg (E + 4))
      (δgrid := forecastJointGridMesh d Pg (E + 4)) ≤ Real.exp (-E) := by
  intro d F η t Pg
  obtain ⟨hdout, hdj, hdc⟩ := s.gridDimensions_le
  have hNative : ((Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U b o R) : ℝ≥0) : ℝ) ≤
      Real.exp Pu := (show ((Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U b o R) : ℝ≥0) : ℝ) ≤
        (Lip : ℝ) from s.nativePullbackLip_le hR o hτ1).trans hLip
  have hPu0 : 0 ≤ Pu := by linarith
  have hPg : 0 ≤ Pg := hPu0.trans (le_max_left _ _)
  have hE4 : 0 ≤ E + 4 := by linarith
  have hLift : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) * m ≤ Pu :=
    (mul_le_mul s.hD.tuples s.hD.degree (Nat.cast_nonneg _) s.hD.nonneg).trans hDsq
  have hsourceFloor : fixedPathSlicedGridMeshFloor s.D 4 V cost F ≤ S.value :=
    (le_max_left _ _).trans hfloor
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have htdata := allocatedFixedPathSlicedPerturbation_chosen_tail_s2 (G := G) B U b
    s.hD.nonneg hPu0 hcost hF s.hD.tuples s.haxes s.L
    (Real.exp_pos (-F)) hAL (by rw [Real.exp_neg, inv_inv])
  have hL := allocatedOriginalSampleFullSliceLip_le_two_exp_of_allAxis B U b S
    htdata.1.le htdata.2.1 hLift
  let Kφ := Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U b o R)
  have hKK : (Kφ : ℝ) * allocatedOriginalSampleFullSliceLip B U b S t ≤
      Real.exp (2 * Pu + 2) := by
    calc
      _ ≤ Real.exp Pu * (2 * Real.exp Pu) :=
        mul_le_mul hNative hL (NNReal.coe_nonneg _) (Real.exp_nonneg _)
      _ = 2 * Real.exp (2 * Pu) := by rw [two_mul Pu, Real.exp_add]; ring
      _ ≤ Real.exp 2 * Real.exp (2 * Pu) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hNative' : (Kφ : ℝ) ≤ Real.exp (2 * Pu + 2) :=
    hNative.trans (Real.exp_le_exp.mpr (by linarith))
  let HP := fun j : PrincipalTupleIndex
    (fun a : {a // ¬allocatedShortAxis (I := I) U b S.value a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) => slice.principalLength ⟨j.1.val,j.2⟩
  have hcard : (Fintype.card (PrincipalTupleIndex
      (fun a : {a // ¬allocatedShortAxis (I := I) U b S.value a} => B a.val)
      (fun a => layerSamplerDegree I n a.val)) : ℝ) ≤ s.D :=
    (Nat.cast_le.mpr (allocatedOriginalSampleLiftInput_card_le_allAxis B U b S)).trans s.hD.tuples
  have hprec : F = (2 * Pu + 2) + (E + 4) + 12 := by dsimp only [F]; ring
  have hsrc := fixedPathSlicedSourceErrorBudget_of_floor s.hD.nonneg
    (by linarith : 2 ≤ 2 * Pu + 2) hE4 HP slice.kernelLength hcard s.hD.kernel_variables
    (NeZero.pos q) hq (by simpa only [hprec] using hsourceFloor)
    (fun j => hHP j.1 j.2) hHG (by positivity) Kφ.coe_nonneg hξ0 hKK hNative'
    (by simpa only [← hprec] using hξ)
  have hwidth := slice.kernelWidth_lower_of_length s hHG
  have hdensity := slice.density_uniform_budget_s2 s.hBactive s.hP s.hδslice s.hδsliceInv
    s.hX (s.haxes.trans s.hDP) s.hblocks (by linarith : 0 ≤ cost + 1) hwidth
  have hsm : forecastOriginalSmoothBudget m (s.P + (Fintype.card X + 1) * (cost + 1)) ≤ Pg :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hdec : (s.Pbad + s.Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m ≤ Pg :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hC := (show (fixedSpatialOriginalForecastCap B (slice.slicedBlockEquiv true) s.hδslice : ℝ) ≤
      Real.exp (forecastOriginalSmoothBudget m (s.P + (Fintype.card X + 1) * (cost + 1))) by
        linarith [hdensity.1]).trans (Real.exp_le_exp.mpr hsm)
  have hLgrid := hdensity.2.1.trans (Real.exp_le_exp.mpr hsm)
  have hDgrid := (slice.decayConstant_le_exp s).trans (Real.exp_le_exp.mpr hdec)
  have hKgrid : (Kφ : ℝ) ≤ Real.exp Pg :=
    hNative.trans (Real.exp_le_exp.mpr (le_max_left _ _))
  unfold comparisonError
  rw [slice.ambientGridError_eq_forecastJointGridError,
    allocatedSlicedPhysicalComparisonError_eq_sourceError]
  have htotal := fixedPathSlicedAmbientScalarPrecision_error _ _ _ d hdout hdj hdc hPg hE
    hsrc.2.2 hM (Real.rpow_nonneg (Nat.cast_nonneg _) _) (NNReal.coe_nonneg _)
    (NNReal.coe_nonneg _) Kφ.coe_nonneg hDgrid hLgrid hC hKgrid
    (forecastJointGridMesh_bounds d hPg hE4).1.le le_rfl
  have hδnative : Real.exp (-Edata) ≤ Real.exp (-(E + 8)) :=
    Real.exp_le_exp.mpr (neg_le_neg hEdata)
  simp only [η, hprec, Kφ, HP, add_assoc, NNReal.coe_mul, decayConstant] at htotal ⊢
  linarith only [htotal, hδnative]

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.comparisonError_le_exp_s2_oai := @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.comparisonError_le_exp_s2_oai
