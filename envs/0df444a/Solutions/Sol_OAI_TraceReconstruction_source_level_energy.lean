-- Prove2me | solution 1 for OAI.TraceReconstruction.source_level_energy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:03:11.577164+00:00
-- url     : https://prove2.me/submissions/e9e9fccd-4a36-4bb4-b3e6-5fdef43162a2

import Mathlib
import Definitions.Def_OAIQ9Tr002

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Scales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Scales

Exact block exponents, deletion reduction, induction depth, backward target scales, and uniform power absorption.
-/

open scoped ENNReal
noncomputable section

namespace TraceReconstruction

theorem scaleA_top (b : ℕ) (ε : ℝ) : scaleA b b ε = 1 := by
  unfold scaleA
  field_simp
  ring

theorem forcedDecay_summand (b k : ℕ) (ε : ℝ) :
    ((2:ℝ)^b / (2:ℝ)^(k+2))*(scaleKappa b (k+2) ε / 2 + ε) =
      (1+ε)/4 - 3*((2:ℝ)^b/2)*ε + ((2:ℝ)^b/(2:ℝ)^(k+1))*ε := by
  unfold scaleKappa scaleA
  simp only [show k+2-1=k+1 by omega, pow_succ]
  field_simp
  ring

theorem forcedDecay_lower (b : ℕ) (ε d : ℝ) (hb : 1 ≤ b) (he : 0 ≤ ε) :
    d + ((b:ℝ)-1)/4 - (((2:ℝ)^b-1)*d + 3*b*((2:ℝ)^b/2))*ε ≤
      forcedDecay b ε d := by
  have hterm (k : ℕ) : 1/4 - 3*((2:ℝ)^b/2)*ε ≤
      ((2:ℝ)^b / (2:ℝ)^(k+2))*(scaleKappa b (k+2) ε / 2 + ε) := by
    rw [forcedDecay_summand]
    have hp : 0 ≤ ((2:ℝ)^b / (2:ℝ)^(k+1))*ε := by positivity
    linarith
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range (b-1)) => hterm k)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  rw [Nat.cast_sub hb, Nat.cast_one] at hsum
  have ha : (2:ℝ)^b * scaleA b 0 ε * d = d - ((2:ℝ)^b-1)*d*ε := by
    unfold scaleA
    simp only [pow_zero, mul_one]
    field_simp
    ring
  unfold forcedDecay
  rw [ha]
  have hp : 0 ≤ (2:ℝ)^b*ε := by positivity
  nlinarith

theorem nat_add_one_le_two_pow (n : ℕ) : n+1 ≤ 2^n := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; omega

theorem sourceEpsilon_pos (B D : ℕ) : 0 < sourceEpsilon B D := by
  unfold sourceEpsilon
  positivity

theorem sourceEpsilon_loss (B D b : ℕ) (d : ℝ) (hb : b ≤ B)
    (hd0 : 0 ≤ d) (hd : d ≤ 3 + (B:ℝ)*D) :
    (((2:ℝ)^b-1)*d + 3*b*((2:ℝ)^b/2))*sourceEpsilon B D < 1/100 := by
  have hpow : (2:ℝ)^b ≤ (2:ℝ)^B := pow_le_pow_right₀ (by norm_num) hb
  have hB : (B:ℝ)+1 ≤ (2:ℝ)^B := by exact_mod_cast nat_add_one_le_two_pow B
  have hB0 : (0:ℝ) ≤ B := by positivity
  have hD0 : (0:ℝ) ≤ D := by positivity
  have hh : (((2:ℝ)^b-1)*d + 3*b*((2:ℝ)^b/2)) ≤
      4*((2:ℝ)^B)^2*((D:ℝ)+1) := by
    have hb' : (b:ℝ) ≤ B := by exact_mod_cast hb
    have h1 := mul_le_mul_of_nonneg_right (show (2:ℝ)^b-1 ≤ (2:ℝ)^B by linarith) hd0
    have h2 := mul_le_mul_of_nonneg_left hd (show 0 ≤ (2:ℝ)^B by positivity)
    have h3 := mul_le_mul hb' hpow (by positivity : (0:ℝ) ≤ (2:ℝ)^b) hB0
    have h4 := mul_le_mul_of_nonneg_left hB hD0
    have h5 := mul_le_mul_of_nonneg_left h4 (show 0 ≤ (2:ℝ)^B by positivity)
    have h6 := mul_le_mul_of_nonneg_left hB (show 0 ≤ (2:ℝ)^B by positivity)
    nlinarith [sq_nonneg ((2:ℝ)^B)]
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_right hh (sourceEpsilon_pos B D).le)
  unfold sourceEpsilon
  have hpos : 0 < (2:ℝ)^(4*B+100) := by positivity
  have hp2 : (2:ℝ)^(2*B) = ((2:ℝ)^B)^2 := by rw [mul_comm 2 B, pow_mul]
  have hp4 : (2:ℝ)^(4*B+100) = ((2:ℝ)^B)^2 * (2:ℝ)^(2*B+100) := by
    rw [show 4*B+100=2*B+(2*B+100) by omega, pow_add, hp2]
  have hh2 : (400:ℝ) < (2:ℝ)^(2*B+100) := by
    have h := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega : 9 ≤ 2*B+100)
    norm_num at h ⊢
    linarith
  rw [mul_one_div]
  apply (div_lt_iff₀ (by positivity)).mpr
  rw [hp4]
  have := mul_lt_mul_of_pos_left hh2 (show 0 < ((2:ℝ)^B)^2*((D:ℝ)+1) by positivity)
  nlinarith

theorem forcedDecay_margin (B D b : ℕ) (d : ℝ) (hb1 : 1 ≤ b) (hb : b ≤ B)
    (hd0 : 0 ≤ d) (hd : d ≤ 3 + (B:ℝ)*D) :
    d + ((b:ℝ)-1)/4 - 1/20 + 3/100 < forcedDecay b (sourceEpsilon B D) d := by
  have h := forcedDecay_lower b (sourceEpsilon B D) d hb1 (sourceEpsilon_pos B D).le
  have hg := sourceEpsilon_loss B D b d hb hd0 hd
  linarith
end TraceReconstruction

open Filter
open scoped Topology


open Filter
open scoped Topology
namespace TraceReconstruction

theorem blockGain_two : blockGain 2 = 1/5 := by norm_num [blockGain]
theorem blockGain_pos (B : ℕ) (hB : 2 ≤ B) : 0 < blockGain B := by
  have hB' : (2:ℝ) ≤ B := by exact_mod_cast hB
  unfold blockGain
  linarith

theorem totalScoreExponent_exact (B D : ℕ) (hD : warmupBlocks B ≤ D) :
    totalScoreExponent B D = 11/5 + (warmupBlocks B:ℝ)/5 +
      ((D:ℝ)-warmupBlocks B)*blockGain B := by
  unfold totalScoreExponent
  rw [← Nat.add_sub_of_le hD, Finset.sum_range_add]
  have hfirst : (∑ i ∈ Finset.range (warmupBlocks B),
      blockGain (if i<warmupBlocks B then 2 else B)) = (warmupBlocks B:ℝ)/5 := by
    simp only [Finset.sum_congr rfl (fun i hi => congrArg blockGain (ite_eq_left (Finset.mem_range.mp hi))), blockGain_two]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [hfirst]
  have hlast : (∑ i ∈ Finset.range (D-warmupBlocks B),
      blockGain (if warmupBlocks B+i<warmupBlocks B then 2 else B)) =
      ((D:ℝ)-warmupBlocks B)*blockGain B := by
    simp only [show ∀ i, ¬warmupBlocks B+i<warmupBlocks B from fun i => by omega, ite_false,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_sub hD]
  rw [hlast]
  simp only [Nat.add_sub_of_le hD]
  ring

end TraceReconstruction

open Filter
open scoped Topology


end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Oracles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Oracles

TV kernels and trace simulation, anchor costs, counted primitives, common-part lifting, concrete oracle pairs, and paired-flag metadata.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem binaryTreeBudget_nonneg (C : ℕ → ℝ) (hC : ∀n,0≤C n) (n : ℕ) :
    0≤binaryTreeBudget C n := by
  cases n with
  | zero => norm_num [binaryTreeBudget]
  | succ n => exact mul_nonneg (hC n) (sq_nonneg _)

end TraceReconstruction
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_SourceOracle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# SourceOracle

Actual source mechanisms and posteriors, typical metadata, sparse degrees, common-event clipping, approximate oracles, and mixed Hellinger bounds.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology



noncomputable section


noncomputable section


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem hiddenBinomialCap_nonneg (m : ℕ) (ω : ℝ) : 0≤hiddenBinomialCap m ω :=
  Real.sqrt_nonneg _

end TraceReconstruction


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem sourceForcedBudget_nonneg (T n : ℕ → ℕ) (s b r : ℕ) (ω : ℝ) :
    0 ≤ sourceForcedBudget T n s b r ω := by
  have hB := fun j => hiddenBinomialCap_nonneg (n j) ω
  have hC := fun j => hiddenBinomialCap_nonneg (sourceScheduledTrials T n j) ω
  have ht := binaryTreeBudget_nonneg (fun j => 4*((2^s:ℕ):ℝ)^6*
      hiddenBinomialCap (sourceScheduledTrials T n (j+1)) ω*hiddenBinomialCap (n j) ω)
    (fun j => mul_nonneg (mul_nonneg (by positivity) (hC (j+1))) (hB j)) b
  have hb := hB b
  unfold sourceForcedBudget interiorLabelBudget
  positivity

end TraceReconstruction


end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_InitialRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# InitialRates

Initial geometric parameters, moment depths, error and overlap rates, and production of the base induction pair.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

theorem totalScoreExponent_bounds (B D : ℕ) (hB : 2 ≤ B) :
    11/5 ≤ totalScoreExponent B D ∧ totalScoreExponent B D ≤ 3+(D:ℝ)*B := by
  have hdim (i : ℕ) : (2:ℝ) ≤ (if i<warmupBlocks B then (2:ℕ) else B) ∧
      (((if i<warmupBlocks B then (2:ℕ) else B):ℕ):ℝ) ≤ B := by
    split_ifs <;> norm_cast
  have hlo : 0 ≤ ∑i∈Finset.range D,blockGain (if i<warmupBlocks B then 2 else B) := by
    apply Finset.sum_nonneg
    intro i _
    unfold blockGain
    linarith [(hdim i).1]
  have hhi : (∑i∈Finset.range D,blockGain (if i<warmupBlocks B then 2 else B)) ≤ (D:ℝ)*B := by
    calc
      _ ≤ ∑_i∈Finset.range D,(B:ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        unfold blockGain
        linarith [(hdim i).1,(hdim i).2]
      _ = _ := by simp
  unfold totalScoreExponent
  constructor <;> linarith

end TraceReconstruction


end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_LayoutRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# LayoutRates

Integer block schedules, rounding, length and trial margins, sparse gaps, and forced-anchor decay.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem sourceArithmeticLength_step (C N : ℝ) (b : ℕ) (ε : ℝ) (ell k j : ℕ) :
    sourceArithmeticLength C N b ε ell k (j+1)=
      sourceArithmeticLength C N b ε ell k j*sourceArithmeticP C N b ε ell k j := rfl

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Rounding the source windows loses at most a factor two. -/
theorem sourceWindowSize_bounds {N ε : ℝ} {b j : ℕ}
    (h : 8 ≤ N^(scaleKappa b (j+1) ε)) :
    N^(scaleKappa b (j+1) ε)/2 ≤ (sourceWindowSize N b ε j:ℝ) ∧
      (sourceWindowSize N b ε j:ℝ) ≤ N^(scaleKappa b (j+1) ε) := by
  have hlo := Nat.lt_floor_add_one (N^(scaleKappa b (j+1) ε)/4)
  have hhi := Nat.floor_le (show 0 ≤ N^(scaleKappa b (j+1) ε)/4 by linarith)
  unfold sourceWindowSize
  push_cast
  constructor <;> linarith only [h,hlo,hhi]

end TraceReconstruction


noncomputable section


noncomputable section


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Tiny epsilon estimates are uniform in the varying block depth. -/
theorem sourceEpsilon_power_small (B D m : ℕ) (hm : m ≤ 4*B+100) :
    (2:ℝ)^m*sourceEpsilon B D ≤ 1 := by
  have hp : (2:ℝ)^m ≤ 2^(4*B+100) := pow_le_pow_right₀ (by norm_num) hm
  have hd : (1:ℝ) ≤ (D:ℝ)+1 := by linarith only [Nat.cast_nonneg D (α:=ℝ)]
  have hmul := mul_le_mul_of_nonneg_left hd (show 0 ≤ (2:ℝ)^(4*B+100) by positivity)
  unfold sourceEpsilon
  rw [mul_one_div]
  exact (div_le_one (by positivity)).mpr (hp.trans (by simpa only [mul_one] using hmul))

theorem scaleA_le_geometric (b j : ℕ) (ε : ℝ) (he : 0 ≤ ε) (hj : j ≤ b) :
    scaleA b j ε ≤ (2:ℝ)^j/2^b := by
  have hp : (2:ℝ)^j ≤ 2^b := pow_le_pow_right₀ (by norm_num) hj
  have hh := mul_le_mul_of_nonneg_left hp he
  unfold scaleA
  apply (sub_le_iff_le_add).mpr
  apply (div_le_iff₀ (by positivity)).mpr
  simp only [add_mul]
  rw [div_mul_cancel₀ _ (by positivity : (2:ℝ)^b ≠ 0)]
  nlinarith only [hh]

theorem two_power_sum_shift (m : ℕ) :
    (∑j∈Finset.range m,(2:ℝ)^(j+1))=2^(m+1)-2 := by
  induction m with
  | zero => norm_num
  | succ m ih => rw [Finset.sum_range_succ,ih,pow_succ (2:ℝ) (m+1)]; ring

theorem sourceInteriorExponent_upper (b : ℕ) (ε : ℝ) (hb : 1 ≤ b) (he : 0 ≤ ε) :
    sourceInteriorExponent b ε ≤ 1-2/(2:ℝ)^b := by
  have hterm (j : ℕ) (hj : j∈Finset.range (b-1)) :
      scaleKappa b (j+2) ε ≤ (2:ℝ)^(j+1)/2^b := by
    have hj' := Finset.mem_range.mp hj
    have ha := scaleA_le_geometric b (j+1) ε he (by omega)
    have hp : (1:ℝ) ≤ 2^(j+2) := one_le_pow₀ (by norm_num)
    unfold scaleKappa
    simp only [show j+2-1=j+1 by omega]
    linarith only [ha,mul_nonneg (sub_nonneg.mpr hp) he]
  apply (Finset.sum_le_sum hterm).trans_eq
  rw [←Finset.sum_div,two_power_sum_shift,Nat.sub_add_cancel hb]
  field_simp

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem scaleA_zero_simple_lower (b : ℕ) (ε : ℝ) (he : 0 ≤ ε) :
    1/(2:ℝ)^b-ε ≤ scaleA b 0 ε := by
  unfold scaleA
  norm_num only [pow_zero,mul_one]
  exact sub_le_sub_right (div_le_div_of_nonneg_right (by linarith only [he]) (by positivity)) _

/-- Quantitative sparse gap, keeping its growth in d. Both the two-dimensional
 warmup and the post-warmup dimension satisfy this common estimate. -/
theorem source_sparse_gap (B D b : ℕ) (d : ℝ) (hb1 : 1 ≤ b) (_hb : b ≤ B)
    (hd : 11/5 ≤ d) (hcases : b=2 ∨ (b=B ∧ (2:ℝ)^B+2 ≤ d)) :
    (d+1)/(128*(2:ℝ)^(2*B)) ≤
      scaleA b 0 (sourceEpsilon B D)*d-sourceInteriorExponent b (sourceEpsilon B D) := by
  let X := (2:ℝ)^B
  let ε := sourceEpsilon B D
  have hx : 1 ≤ X := one_le_pow₀ (by norm_num)
  have hx0 : 0 < X := by linarith only [hx]
  have hd0 : 0 ≤ d := by linarith only [hd]
  have he : 0 < ε := sourceEpsilon_pos B D
  have hA := mul_le_mul_of_nonneg_right (scaleA_zero_simple_lower b ε he.le) hd0
  have hI := sourceInteriorExponent_upper b ε hb1 he.le
  have hcoeff : (d+1)/(64*X^2) ≤ (d+2)/(2:ℝ)^b-1 := by
    rcases hcases with htwo | ⟨hmain,hdmain⟩
    · rw [htwo]
      have hstep : (d+1)/(64*X^2) ≤ (d+1)/64 := by
        apply div_le_div_of_nonneg_left (by linarith only [hd]) (by norm_num)
        nlinarith only [hx,sq_nonneg (X-1)]
      apply hstep.trans
      norm_num only [show (2:ℝ)^2=4 by norm_num]
      linarith only [hd]
    · rw [hmain]
      change (d+1)/(64*X^2) ≤ (d+2)/X-1
      apply (div_le_iff₀ (by positivity : (0:ℝ)<64*X^2)).mpr
      have heq : ((d+2)/X-1)*(64*X^2)=64*X*(d+2-X) := by field_simp
      rw [heq]
      have hh : 0 ≤ (d-X-2)*(64*X-1) := mul_nonneg (by dsimp [X]; linarith only [hdmain])
        (by linarith only [hx])
      nlinarith only [hh,hx]
  have hsmall := sourceEpsilon_power_small B D (2*B+8) (by omega)
  have hsmall' : 256*X^2*ε ≤ 1 := by
    rw [show 2*B+8=B*2+8 by omega,pow_add,pow_mul] at hsmall
    norm_num only [show (2:ℝ)^8=256 by norm_num] at hsmall
    dsimp [X,ε]
    nlinarith only [hsmall]
  have herr : ε*d ≤ (d+1)/(256*X^2) := by
    apply (le_div_iff₀ (by positivity : (0:ℝ)<256*X^2)).mpr
    have hh := mul_le_mul_of_nonneg_right hsmall' hd0
    nlinarith only [hh]
  have hpow : (2:ℝ)^(2*B)=X^2 := by dsimp [X]; rw [Nat.mul_comm,pow_mul]
  rw [hpow]
  change (d+1)/(128*X^2) ≤ scaleA b 0 ε*d-sourceInteriorExponent b ε
  have hp : 0 < (2:ℝ)^b := by positivity
  have hc : (1/(2:ℝ)^b-ε)*d-(1-2/(2:ℝ)^b)=((d+2)/(2:ℝ)^b-1)-ε*d := by ring
  have hbase := sub_le_sub hA hI
  rw [hc] at hbase
  have hident : (d+1)/(64*X^2)-(d+1)/(256*X^2)=3*(d+1)/(256*X^2) := by ring
  have hlo := (sub_le_sub hcoeff herr).trans hbase
  rw [hident] at hlo
  have hcompare : (d+1)/(128*X^2) ≤ 3*(d+1)/(256*X^2) := by
    have hh : (d+1)/128 ≤ 3*(d+1)/256 := by linarith only [hd]
    simpa only [div_div] using div_le_div_of_nonneg_right hh (sq_nonneg X)
  exact hcompare.trans hlo

theorem totalScoreExponent_step (B i : ℕ) :
    totalScoreExponent B (i+1)=totalScoreExponent B i+blockGain (sourceDimension B i) := by
  unfold totalScoreExponent sourceDimension
  rw [Finset.sum_range_succ]
  ring

theorem totalScoreExponent_after_warmup (B i : ℕ) (hB : 2 ≤ B) (hi : warmupBlocks B ≤ i) :
    (2:ℝ)^B+11/5 ≤ totalScoreExponent B i := by
  rw [totalScoreExponent_exact B i hi]
  have hm : (0:ℝ) ≤ ((i:ℝ)-warmupBlocks B)*blockGain B :=
    mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hi)) (blockGain_pos B hB).le
  unfold warmupBlocks at *
  push_cast at *
  linarith only [hm]

theorem source_level_sparse_gap (B D i : ℕ) (hB : 2 ≤ B) :
    (totalScoreExponent B i+1)/(128*(2:ℝ)^(2*B)) ≤
      scaleA (sourceDimension B i) 0 (sourceEpsilon B D)*totalScoreExponent B i-
        sourceInteriorExponent (sourceDimension B i) (sourceEpsilon B D) := by
  have hb : 2 ≤ sourceDimension B i ∧ sourceDimension B i ≤ B := by
    unfold sourceDimension
    split_ifs <;> omega
  apply source_sparse_gap B D _ _ (by omega) hb.2 (totalScoreExponent_bounds B i hB).1
  unfold sourceDimension
  split_ifs with hi
  · exact Or.inl rfl
  · exact Or.inr ⟨rfl,by linarith only [totalScoreExponent_after_warmup B i hB (by omega)]⟩

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem SourceArithmeticBounds.window_positive {C N F ε : ℝ} {s b ell k : ℕ}
    (H : SourceArithmeticBounds C N F ε s b ell k) (j : ℕ) :
    0 < sourceBlockWindows N b ε j := by
  by_cases hj : j<b
  · have hh := (H.windows j hj).1
    omega
  · simp only [sourceBlockWindows,ite_eq_right hj]
    norm_num

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem binaryTreeExponent_sum (e : ℕ → ℝ) (b : ℕ) :
    binaryTreeExponent e b=∑j∈Finset.range b,((2:ℝ)^b/2^(j+1))*e j := by
  induction b with
  | zero => simp [binaryTreeExponent]
  | succ b ih =>
    rw [binaryTreeExponent,ih,Finset.sum_range_succ,Finset.mul_sum]
    have he : (∑j∈Finset.range b,((2:ℝ)^(b+1)/2^(j+1))*e j)=
        ∑j∈Finset.range b,2*((2^b/2^(j+1))*e j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_succ]
      ring
    rw [he]
    simp only [div_self (by positivity : (2:ℝ)^(b+1)≠0),one_mul]
    ring

theorem binaryTreeBudget_mono {C D : ℕ → ℝ} (b : ℕ)
    (hC : ∀j < b,0 ≤ C j) (hCD : ∀j < b,C j ≤ D j) :
    binaryTreeBudget C b ≤ binaryTreeBudget D b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    have hc : 0 ≤ binaryTreeBudget C b := by
      cases b with
      | zero => norm_num [binaryTreeBudget]
      | succ j => exact mul_nonneg (hC j (by omega)) (sq_nonneg _)
    have hd := ih (fun j hj=>hC j (by omega)) (fun j hj=>hCD j (by omega))
    rw [binaryTreeBudget,binaryTreeBudget]
    exact mul_le_mul (hCD b (by omega)) (pow_le_pow_left₀ hc hd 2)
      (sq_nonneg _) ((hC b (by omega)).trans (hCD b (by omega)))

theorem binaryTreeBudget_scaled (A N : ℝ) (hN : 0 < N) (e : ℕ → ℝ) (b : ℕ) :
    binaryTreeBudget (fun j => A*N^(-e j)) b=
      binaryTreeBudget (fun _=>A) b*N^(-binaryTreeExponent e b) := by
  induction b with
  | zero => simp [binaryTreeBudget,binaryTreeExponent]
  | succ b ih =>
    rw [binaryTreeBudget,ih,binaryTreeBudget,binaryTreeExponent,mul_pow]
    have hr : N^(-e b)*(N^(-binaryTreeExponent e b))^2=
        N^(-(e b+2*binaryTreeExponent e b)) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hN.le,←Real.rpow_add hN]
      congr 1
      norm_num only [Nat.cast_ofNat]
      ring
    calc
      _ = (A*(binaryTreeBudget (fun _=>A) b)^2)*
        (N^(-e b)*(N^(-binaryTreeExponent e b))^2) := by ring
      _ = _ := by rw [hr]

theorem source_interior_product (T : ℕ → ℕ) (b : ℕ) :
    (∏j : Fin (b+1),if j.val=0 then 1 else T j.val)=∏j∈Finset.range b,T (j+1) := by
  rw [Fin.prod_univ_succ]
  simp only [Fin.val_zero,ite_true,Fin.val_succ,Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false,one_mul]
  exact Fin.prod_univ_eq_prod_range (fun j => T (j+1)) b

/-- Pull all extra selected leaves into the sparse-degree small factor.
 Only the mandatory 2^(b+1) bottom leaves pay the old score exponent. -/
theorem sourceForcedBudget_degree_factor (T n : ℕ → ℕ) (s b r : ℕ) (ω w : ℝ)
    (hr : 2^(b+1) ≤ r) :
    w^(2*r)*sourceForcedBudget T n s b r ω=
      (OccupiedParityTree.shapeRoleConstant r (b+1):ℝ)*
      (w^2*((2^s:ℕ):ℝ)*(sourceSparseCount T s b:ℝ))^(r-2^(b+1))*
      (w^2)^(2^(b+1))*
      ((2*((2^s:ℕ):ℝ)^3*hiddenBinomialCap (n b) ω)*
        binaryTreeBudget (fun j => 4*((2^s:ℕ):ℝ)^6*
          hiddenBinomialCap (sourceScheduledTrials T n (j+1)) ω*hiddenBinomialCap (n j) ω) b) := by
  unfold sourceForcedBudget interiorLabelBudget sourceSparseCount
  rw [source_interior_product]
  push_cast
  have hwr : w^(2*r)=(w^2)^(r-2^(b+1))*(w^2)^(2^(b+1)) := by
    rw [←pow_add,Nat.sub_add_cancel hr,pow_mul]
  rw [hwr]
  simp only [mul_pow,pow_mul]
  ring

/-- The remaining extra-degree factor costs no scale power. -/
theorem sourceForcedBudget_degree_le (T n : ℕ → ℕ) (s b r : ℕ) (ω w : ℝ)
    (hr : 2^(b+1) ≤ r)
    (hsmall : w^2*((2^s:ℕ):ℝ)*(sourceSparseCount T s b:ℝ) ≤ 1) :
    w^(2*r)*sourceForcedBudget T n s b r ω ≤
      (OccupiedParityTree.shapeRoleConstant r (b+1):ℝ)*(w^2)^(2^(b+1))*
      ((2*((2^s:ℕ):ℝ)^3*hiddenBinomialCap (n b) ω)*
        binaryTreeBudget (fun j => 4*((2^s:ℕ):ℝ)^6*
          hiddenBinomialCap (sourceScheduledTrials T n (j+1)) ω*hiddenBinomialCap (n j) ω) b) := by
  rw [sourceForcedBudget_degree_factor T n s b r ω w hr]
  have hfac : (w^2*((2^s:ℕ):ℝ)*(sourceSparseCount T s b:ℝ))^(r-2^(b+1)) ≤ 1 :=
    pow_le_one₀ (by positivity) hsmall
  have htree := binaryTreeBudget_nonneg
    (fun j => 4*((2^s:ℕ):ℝ)^6*hiddenBinomialCap (sourceScheduledTrials T n (j+1)) ω*hiddenBinomialCap (n j) ω)
    (fun j => mul_nonneg (mul_nonneg (by positivity) (hiddenBinomialCap_nonneg _ _))
      (hiddenBinomialCap_nonneg _ _)) b
  have hroot := hiddenBinomialCap_nonneg (n b) ω
  have hmul := mul_le_mul_of_nonneg_left hfac
    (show 0 ≤ (OccupiedParityTree.shapeRoleConstant r (b+1):ℝ) by positivity)
  simp only [mul_one] at hmul
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmul (by positivity)) (by positivity)

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem hiddenBinomialCap_rpow {N e F K ω : ℝ} {m : ℕ}
    (hN : 0 < N) (hF : 0 < F) (hK : 0 ≤ K)
    (hm : N^e/F ≤ (m:ℝ)) (hcoef : 4*F ≤ K^2*ω^2) :
    hiddenBinomialCap m ω ≤ K*N^(-e/2) := by
  have hpow : (N^(-e/2))^2=N^(-e) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hN.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  have hprod : N^(-e)*N^e=1 := by rw [←Real.rpow_add hN,neg_add_cancel,Real.rpow_zero]
  unfold hiddenBinomialCap
  apply (Real.sqrt_le_left (mul_nonneg hK (Real.rpow_nonneg hN.le _))).mpr
  rw [mul_pow,hpow]
  apply (div_le_iff₀ (by positivity : (0:ℝ)<(m:ℝ)*ω^2+2)).mpr
  have hh : 4 ≤ K^2*ω^2/F := (le_div_iff₀ hF).mpr hcoef
  calc
    4 ≤ K^2*ω^2/F := hh
    _ = K^2*N^(-e)*(N^e/F*ω^2) := by
      calc
        _ = (K^2*ω^2/F)*(N^(-e)*N^e) := by rw [hprod,mul_one]
        _ = _ := by ring
    _ ≤ K^2*N^(-e)*((m:ℝ)*ω^2+2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hh' := mul_le_mul_of_nonneg_right hm (sq_nonneg ω)
      linarith only [hh']

/-- The exact exponent in the skeleton budget equals the manuscript's
 forcedDecay, not an arbitrary favorable surrogate. -/
theorem forcedDecay_binary (b : ℕ) (ε d : ℝ) (hb : 1 ≤ b) :
    forcedDecay b ε d=ε/2+
      binaryTreeExponent (fun j=>scaleKappa b (j+2) ε/2+ε) (b-1)+
      (2:ℝ)^b*scaleA b 0 ε*d := by
  rw [forcedDecay,binaryTreeExponent_sum]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  have he : (2:ℝ)^b/2^(j+2)=2^(b-1)/2^(j+1) := by
    rw [show b=(b-1)+1 by omega,pow_succ]
    simp only [Nat.add_sub_cancel]
    rw [show j+2=(j+1)+1 by omega,pow_succ]
    field_simp
  rw [he]

theorem sourceSkeletonPrefactor_nonneg (s b : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ sourceSkeletonPrefactor s b K := by
  have h := binaryTreeBudget_nonneg (fun _=>4*((2^s:ℕ):ℝ)^6*K^2) (fun _=>by positivity) b
  unfold sourceSkeletonPrefactor
  positivity

theorem source_forced_core_bound (T n : ℕ → ℕ) (s b : ℕ) (ω N ε K : ℝ)
    (hN : 0 < N) (hK : 0 ≤ K)
    (hn : ∀j ≤ b,hiddenBinomialCap (n j) ω ≤ K*N^(-ε/2))
    (hg : ∀j < b,hiddenBinomialCap (sourceScheduledTrials T n (j+1)) ω ≤
      K*N^(-(scaleKappa (b+1) (j+2) ε+ε)/2)) :
    (2*((2^s:ℕ):ℝ)^3*hiddenBinomialCap (n b) ω)*
      binaryTreeBudget (fun j=>4*((2^s:ℕ):ℝ)^6*
        hiddenBinomialCap (sourceScheduledTrials T n (j+1)) ω*hiddenBinomialCap (n j) ω) b ≤
      sourceSkeletonPrefactor s b K*
        N^(-(ε/2+binaryTreeExponent (fun j=>scaleKappa (b+1) (j+2) ε/2+ε) b)) := by
  let A := 4*((2^s:ℕ):ℝ)^6*K^2
  let e := fun j=>scaleKappa (b+1) (j+2) ε/2+ε
  have hpoints (j : ℕ) (hj : j<b) :
      4*((2^s:ℕ):ℝ)^6*hiddenBinomialCap (sourceScheduledTrials T n (j+1)) ω*
          hiddenBinomialCap (n j) ω ≤ A*N^(-e j) := by
    calc
      _ ≤ 4*((2^s:ℕ):ℝ)^6*(K*N^(-(scaleKappa (b+1) (j+2) ε+ε)/2))*(K*N^(-ε/2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hg j hj) (by positivity)) (hn j (by omega))
          (hiddenBinomialCap_nonneg _ _) (by positivity)
      _ = _ := by
        have hr : N^(-(scaleKappa (b+1) (j+2) ε+ε)/2)*N^(-ε/2)=N^(-e j) := by
          rw [←Real.rpow_add hN]
          congr 1
          dsimp [e]
          ring
        dsimp [A]
        calc
          _ = 4*((2^s:ℕ):ℝ)^6*K^2*
            (N^(-(scaleKappa (b+1) (j+2) ε+ε)/2)*N^(-ε/2)) := by ring
          _ = _ := by rw [hr]
  have htree := binaryTreeBudget_mono b
    (fun j _=>mul_nonneg (mul_nonneg (by positivity) (hiddenBinomialCap_nonneg _ _))
      (hiddenBinomialCap_nonneg _ _)) hpoints
  rw [binaryTreeBudget_scaled A N hN e b] at htree
  have ht0 := binaryTreeBudget_nonneg (fun j=>4*((2^s:ℕ):ℝ)^6*
      hiddenBinomialCap (sourceScheduledTrials T n (j+1)) ω*hiddenBinomialCap (n j) ω)
    (fun j=>mul_nonneg (mul_nonneg (by positivity) (hiddenBinomialCap_nonneg _ _))
      (hiddenBinomialCap_nonneg _ _)) b
  calc
    _ ≤ (2*((2^s:ℕ):ℝ)^3*(K*N^(-ε/2)))*
        (binaryTreeBudget (fun _=>A) b*N^(-binaryTreeExponent e b)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hn b le_rfl) (by positivity)) htree ht0 (by positivity)
    _ = _ := by
      have hr : N^(-ε/2)*N^(-binaryTreeExponent e b)=N^(-(ε/2+binaryTreeExponent e b)) := by
        rw [←Real.rpow_add hN]
        congr 1
        ring
      dsimp [sourceSkeletonPrefactor]
      calc
        _ = (2*((2^s:ℕ):ℝ)^3*K)*binaryTreeBudget (fun _=>A) b*
          (N^(-ε/2)*N^(-binaryTreeExponent e b)) := by ring
        _ = _ := by rw [hr]

/-- The sharp forced degree has the full decay gain, after all actual
 source caps and the old-score factor have been multiplied. -/
theorem source_forced_degree_decay (T n : ℕ → ℕ) (s b r : ℕ) (ω N ε d K W w : ℝ)
    (hN : 0 < N) (hK : 0 ≤ K) (hW : 0 ≤ W) (hr : 2^(b+1) ≤ r)
    (hsmall : w^2*((2^s:ℕ):ℝ)*(sourceSparseCount T s b:ℝ) ≤ 1)
    (hw : w^2 ≤ W*N^(-scaleA (b+1) 0 ε*d))
    (hn : ∀j ≤ b,hiddenBinomialCap (n j) ω ≤ K*N^(-ε/2))
    (hg : ∀j < b,hiddenBinomialCap (sourceScheduledTrials T n (j+1)) ω ≤
      K*N^(-(scaleKappa (b+1) (j+2) ε+ε)/2)) :
    w^(2*r)*sourceForcedBudget T n s b r ω ≤
      (OccupiedParityTree.shapeRoleConstant r (b+1):ℝ)*W^(2^(b+1))*
        sourceSkeletonPrefactor s b K*N^(-forcedDecay (b+1) ε d) := by
  have hstart := sourceForcedBudget_degree_le T n s b r ω w hr hsmall
  have hcore := source_forced_core_bound T n s b ω N ε K hN hK hn hg
  have hpow := pow_le_pow_left₀ (sq_nonneg w) hw (2^(b+1))
  have hpref := sourceSkeletonPrefactor_nonneg s b hK
  have hcore0 := sourceForcedBudget_nonneg T n s b r ω
  have ht := binaryTreeBudget_nonneg (fun j=>4*((2^s:ℕ):ℝ)^6*
      hiddenBinomialCap (sourceScheduledTrials T n (j+1)) ω*hiddenBinomialCap (n j) ω)
    (fun j=>mul_nonneg (mul_nonneg (by positivity) (hiddenBinomialCap_nonneg _ _))
      (hiddenBinomialCap_nonneg _ _)) b
  have hroot := hiddenBinomialCap_nonneg (n b) ω
  apply hstart.trans
  apply le_trans (mul_le_mul
    (mul_le_mul_of_nonneg_left hpow (by positivity)) hcore (by positivity) (by positivity))
  apply le_of_eq
  rw [mul_pow]
  have hrp : (N^(-scaleA (b+1) 0 ε*d))^(2^(b+1))*
      N^(-(ε/2+binaryTreeExponent (fun j=>scaleKappa (b+1) (j+2) ε/2+ε) b))=
      N^(-forcedDecay (b+1) ε d) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hN.le,←Real.rpow_add hN,
      forcedDecay_binary (b+1) ε d (by omega)]
    simp only [Nat.add_sub_cancel,Nat.cast_pow,Nat.cast_ofNat]
    congr 1
    ring
  calc
    _ = (OccupiedParityTree.shapeRoleConstant r (b+1):ℝ)*W^(2^(b+1))*sourceSkeletonPrefactor s b K*
      ((N^(-scaleA (b+1) 0 ε*d))^(2^(b+1))*
        N^(-(ε/2+binaryTreeExponent (fun j=>scaleKappa (b+1) (j+2) ε/2+ε) b))) := by ring
    _ = _ := by rw [hrp]

end TraceReconstruction

end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_ErrorRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# ErrorRates

Realization of block caps, sparse scales, sharp and smoothing budgets, tree tails, fit errors, and uniform polynomial/exponential bounds.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem sourceWindowSize_le (N : ℝ) (b j : ℕ) (ε : ℝ) (hN : 0 ≤ N) :
    (sourceWindowSize N b ε j:ℝ) ≤ N^(scaleKappa b (j+1) ε) := by
  have hh := Nat.floor_le (div_nonneg (Real.rpow_nonneg hN (scaleKappa b (j+1) ε)) (by norm_num : (0:ℝ) ≤ 4))
  unfold sourceWindowSize
  push_cast
  linarith only [hh]

-- We use only positive target scales below.
theorem SourceArithmeticBounds.scheduled_trials {C N F ε : ℝ} {s b ell k : ℕ}
    (H : SourceArithmeticBounds C N F ε s b ell k) (hN : 0 < N) (hC : 0 < C) (hF : 0 < F)
    (j : ℕ) (hj : j+1 < b) :
    N^(scaleKappa b (j+2) ε+ε)/(4800*(C^(2*b)*F)) ≤
      (sourceScheduledTrials (sourceBlockWindows N b ε) (sourceArithmeticTrials C N b ε ell k) (j+1):ℝ) := by
  let T := sourceBlockWindows N b ε
  let n := sourceArithmeticTrials C N b ε ell k
  have htbig := (H.windows (j+1) hj).1
  have hsize : (T (j+1):ℝ) ≤ N^(scaleKappa b (j+2) ε) := by
    dsimp [T]
    rw [sourceBlockWindows,ite_eq_left hj]
    have hh := Nat.floor_le (div_nonneg (Real.rpow_nonneg hN.le (scaleKappa b (j+2) ε)) (by norm_num : (0:ℝ) ≤ 4))
    simp only [sourceWindowSize,Nat.cast_mul,Nat.cast_ofNat]
    linarith only [hh]
  have hx : 8 ≤ N^(scaleKappa b (j+2) ε) := by
    have hh : (24:ℝ) ≤ T (j+1) := by exact_mod_cast htbig
    linarith only [hh,hsize]
  have hlo := (sourceWindowSize_bounds (b:=b) (j:=j+1) hx).1
  have hn := (H.trials j (by omega)).1
  have hdvd : 4 ∣ T (j+1) := by
    dsimp [T]
    rw [sourceBlockWindows,ite_eq_left hj,sourceWindowSize]
    exact dvd_mul_right _ _
  have htlo : N^(scaleKappa b (j+2) ε)/8 ≤ ((T (j+1)/4:ℕ):ℝ) := by
    rw [Nat.cast_div hdvd (by norm_num : (4:ℝ)≠0)]
    have hh : (sourceWindowSize N b ε (j+1):ℝ)=(T (j+1):ℝ) := by simp [T,sourceBlockWindows,hj]
    rw [hh] at hlo
    linarith only [hlo]
  rw [sourceScheduledTrials,Nat.cast_mul,Real.rpow_add hN]
  calc
    _ = (N^(scaleKappa b (j+2) ε)/8)*(N^ε/(600*(C^(2*b)*F))) := by ring
    _ ≤ _ := mul_le_mul htlo hn (by positivity) (by positivity)

theorem SourceArithmeticBounds.binomial_caps {C N F ε ω : ℝ} {s b ell k : ℕ}
    (H : SourceArithmeticBounds C N F ε s b ell k) (hN : 0 < N)
    (hC : 1 ≤ C) (hF : 1 ≤ F) (hω : 0 < ω) :
    (∀j<b,hiddenBinomialCap (sourceArithmeticTrials C N b ε ell k j) ω ≤
       (200*(C^(2*b)*F)/ω)*N^(-ε/2)) ∧
    (∀j,j+1<b →hiddenBinomialCap
      (sourceScheduledTrials (sourceBlockWindows N b ε) (sourceArithmeticTrials C N b ε ell k) (j+1)) ω ≤
        (200*(C^(2*b)*F)/ω)*N^(-(scaleKappa b (j+2) ε+ε)/2)) := by
  let G := C^(2*b)*F
  have hG : 1 ≤ G := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC) hF
  have hcoef : 4*(4800*G) ≤ (200*G/ω)^2*ω^2 := by
    have hident : (200*G/ω)^2*ω^2=40000*G^2 := by field_simp; ring
    rw [hident]
    nlinarith only [hG,sq_nonneg (G-1)]
  constructor
  · intro j hj
    apply hiddenBinomialCap_rpow hN (by positivity : 0 < 600*G) (by positivity) (H.trials j hj).1
    dsimp [G] at *
    have hnon : 0 ≤ C^(2*b)*F := by positivity
    linarith only [hcoef,hnon]
  · intro j hj
    exact hiddenBinomialCap_rpow hN (by positivity : 0 < 4800*G) (by positivity)
      (H.scheduled_trials hN (by linarith only [hC]) (by linarith only [hF]) j hj) hcoef

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem sourceSparseCount_scale (N : ℝ) (b s : ℕ) (ε : ℝ) (hN : 0 < N) :
    (sourceSparseCount (sourceBlockWindows N b ε) s (b-1):ℝ) ≤
      ((2^s:ℕ):ℝ)*N^(sourceInteriorExponent b ε) := by
  unfold sourceSparseCount sourceInteriorExponent
  push_cast
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Real.rpow_sum_of_pos hN]
  apply Finset.prod_le_prod
  · intro j _
    positivity
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [sourceBlockWindows,ite_eq_left (by omega)]
    exact sourceWindowSize_le N b (j+1) ε hN.le

theorem sourceLeafCount_succ (T : ℕ → ℕ) (j : ℕ) :
    SourceLeafCount T (j+1)=T j*SourceLeafCount T j := by
  exact (Fintype.card_prod (α:=Fin (T j)) (β:=WindowLeaf T j)).trans (by rw [Fintype.card_fin])

theorem sourceLeafCount_le_length {P T : ℕ → ℕ} {ell b : ℕ} (hell : 1 ≤ ell)
    (hPT : ∀j<b,T j ≤ P j) : SourceLeafCount T b ≤ sourceBlockLength P ell b := by
  induction b with
  | zero =>
    change Fintype.card (Fin 1) ≤ ell
    simpa using hell
  | succ b ih =>
    rw [sourceLeafCount_succ,sourceBlockLength]
    exact Nat.mul_le_mul (hPT b (by omega)) (ih (fun j hj=>hPT j (by omega)))

theorem sourceArithmeticLength_eq_block (C N : ℝ) (b : ℕ) (ε : ℝ) (ell k j : ℕ) :
    sourceArithmeticLength C N b ε ell k j=
      sourceBlockLength (sourceArithmeticP C N b ε ell k) ell j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [sourceArithmeticLength_step,sourceBlockLength,ih,mul_comm]

theorem SourceArithmeticBounds.leaf_bound {C N F ε : ℝ} {s b ell k : ℕ}
    (H : SourceArithmeticBounds C N F ε s b ell k) (hN : 0 < N) :
    (SourceLeafCount (sourceBlockWindows N b ε) b:ℝ) ≤ N := by
  have hell : 1 ≤ ell := by
    have hh := (H.lengths 0 (Nat.zero_le _)).1
    rw [show sourceArithmeticLength C N b ε ell k 0=ell by rfl] at hh
    have hp : 0 < N^(scaleA b 0 ε)/2 := by positivity
    have he : (0:ℝ)<ell := hp.trans_le hh
    have he' : 0<ell := by exact_mod_cast he
    omega
  have hh := sourceLeafCount_le_length (P:=sourceArithmeticP C N b ε ell k) hell
    (fun j hj=>Nat.le_trans (by omega : sourceBlockWindows N b ε j ≤ 2*sourceBlockWindows N b ε j)
      (H.windows j hj).2.2.1)
  have hh' : (SourceLeafCount (sourceBlockWindows N b ε) b:ℝ) ≤
      sourceArithmeticLength C N b ε ell k b := by
    rw [sourceArithmeticLength_eq_block]
    exact_mod_cast hh
  apply hh'.trans
  simpa only [scaleA_top,Real.rpow_one] using (H.lengths b le_rfl).2

/-- Full sparse degree, with the excluded bottom window and the exact
 source gap. This is the high-degree geometric gain, before constants. -/
theorem source_sparse_weight_bound (N ε d W w : ℝ) (b s : ℕ) (hN : 0 < N) (hW : 0 ≤ W)
    (hw : w^2 ≤ W*N^(-scaleA b 0 ε*d)) :
    w^2*(sourceSparseCount (sourceBlockWindows N b ε) s (b-1):ℝ) ≤
      W*((2^s:ℕ):ℝ)*N^(-(scaleA b 0 ε*d-sourceInteriorExponent b ε)) := by
  have hr : N^(-scaleA b 0 ε*d)*N^(sourceInteriorExponent b ε)=
      N^(-(scaleA b 0 ε*d-sourceInteriorExponent b ε)) := by
    rw [←Real.rpow_add hN]
    congr 1
    ring
  calc
    _ ≤ (W*N^(-scaleA b 0 ε*d))*(((2^s:ℕ):ℝ)*N^(sourceInteriorExponent b ε)) :=
      mul_le_mul hw (sourceSparseCount_scale N b s ε hN) (by positivity) (by positivity)
    _ = (W*((2^s:ℕ):ℝ))*(N^(-scaleA b 0 ε*d)*N^(sourceInteriorExponent b ε)) := by ring
    _ = _ := by rw [hr]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Explicit finite sharp energy bound. The two undesirable pattern classes
 are suppressed by eta and a, and the genuine binary forced skeleton pays
 its full source exponent. The high tail uses the sparse, not dense count. -/
theorem source_sharp_numeric (T n : ℕ→ℕ) (s b R : ℕ) (ω η a w N ε d K W Q gap : ℝ)
    (hN : 1 ≤ N) (hK : 0 ≤ K) (hW : 0 ≤ W) (_hQ : 0 ≤ Q)
    (hleaves : (SourceLeafCount T (b+1):ℝ) ≤ N) (hwone : w^2 ≤ 1)
    (hw : w^2 ≤ W*N^(-scaleA (b+1) 0 ε*d))
    (hsmall : w^2*((2^s:ℕ):ℝ)*(sourceSparseCount T s b:ℝ) ≤ 1)
    (hhalf : w^2*(sourceSparseCount T s b:ℝ) ≤ 1/2)
    (hsparse : w^2*(sourceSparseCount T s b:ℝ) ≤ Q*N^(-gap))
    (hn : ∀j≤b,hiddenBinomialCap (n j) ω ≤ K*N^(-ε/2))
    (hg : ∀j<b,hiddenBinomialCap (sourceScheduledTrials T n (j+1)) ω ≤
      K*N^(-(scaleKappa (b+1) (j+2) ε+ε)/2)) :
    sourceSharpEnergyBudget T n s b R ω η a w ≤
      sourceBadRoleFactor b R*N^R*(η^2+a^2)+
      sourceForcedRoleFactor b R*W^(2^(b+1))*sourceSkeletonPrefactor s b K*N^(-forcedDecay (b+1) ε d)+
      8*Q^R*N^(-gap*(R:ℝ)) := by
  have hN0 : 0 < N := by linarith only [hN]
  let A := W^(2^(b+1))*sourceSkeletonPrefactor s b K*N^(-forcedDecay (b+1) ε d)
  have hA : 0 ≤ A := by dsimp [A]; positivity [sourceSkeletonPrefactor_nonneg s b hK]
  have hlow (r : ℕ) (hr : r∈Finset.range R) :
      w^(2*r)*(if r=0 then 0 else sourceSharpDegreeBudget T n s b r ω η a) ≤
        4*((3^((b+1)*r):ℕ):ℝ)^2*N^R*(η^2+a^2)+
          (4*((3^((b+1)*r):ℕ):ℝ)*(OccupiedParityTree.shapeRoleConstant r (b+1):ℝ))*A := by
    have hr' : r ≤ R := (Finset.mem_range.mp hr).le
    have hw0 : 0 ≤ w^(2*r) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg w) r
    have hw1 : w^(2*r) ≤ 1 := by rw [pow_mul]; exact pow_le_one₀ (sq_nonneg w) hwone
    have hc : ((SourceLeafCount T (b+1)).choose r:ℝ) ≤ N^R := by
      have hh : ((SourceLeafCount T (b+1)).choose r:ℝ) ≤ (SourceLeafCount T (b+1):ℝ)^r := by
        exact_mod_cast Nat.choose_le_pow (SourceLeafCount T (b+1)) r
      exact hh.trans ((pow_le_pow_left₀ (by positivity) hleaves r).trans (pow_le_pow_right₀ hN hr'))
    have hbad : w^(2*r)*(((SourceLeafCount T (b+1)).choose r:ℝ)) ≤ N^R := by
      apply (mul_le_mul hw1 hc (by positivity) (by norm_num : (0:ℝ) ≤ 1)).trans_eq
      exact one_mul _
    by_cases hr0 : r=0
    · rw [ite_eq_left hr0,mul_zero]
      positivity
    rw [ite_eq_right hr0,sourceSharpDegreeBudget,mul_add]
    have hB : w^(2*r)*(4*((3^((b+1)*r):ℕ):ℝ)*
        (((SourceLeafCount T (b+1)).choose r:ℝ)*((3^((b+1)*r):ℕ):ℝ)*(η^2+a^2))) ≤
        4*((3^((b+1)*r):ℕ):ℝ)^2*N^R*(η^2+a^2) := by
      have hh := mul_le_mul_of_nonneg_right hbad
        (show 0 ≤ 4*((3^((b+1)*r):ℕ):ℝ)^2*(η^2+a^2) by positivity)
      nlinarith only [hh]
    rw [mul_add]
    apply add_le_add hB
    by_cases hrf : 2^(b+1) ≤ r
    · rw [ite_eq_left hrf]
      have hh := mul_le_mul_of_nonneg_left
        (source_forced_degree_decay T n s b r ω N ε d K W w hN0 hK hW hrf hsmall hw hn hg)
        (show 0 ≤ 4*((3^((b+1)*r):ℕ):ℝ) by positivity)
      dsimp [A]
      nlinarith only [hh]
    · rw [ite_eq_right hrf,mul_zero,mul_zero]
      positivity
  have hsum := Finset.sum_le_sum hlow
  rw [Finset.sum_add_distrib] at hsum
  have hbadSum : (∑r∈Finset.range R,4*((3^((b+1)*r):ℕ):ℝ)^2*N^R*(η^2+a^2))=
      sourceBadRoleFactor b R*N^R*(η^2+a^2) := by simp only [sourceBadRoleFactor,Finset.sum_mul]
  have hforceSum : (∑r∈Finset.range R,(4*((3^((b+1)*r):ℕ):ℝ)*(OccupiedParityTree.shapeRoleConstant r (b+1):ℝ))*A)=
      sourceForcedRoleFactor b R*W^(2^(b+1))*sourceSkeletonPrefactor s b K*N^(-forcedDecay (b+1) ε d) := by
    rw [←Finset.sum_mul]
    dsimp [sourceForcedRoleFactor,A]
    ring
  rw [hbadSum,hforceSum] at hsum
  apply add_le_add hsum
  have hx : 0 ≤ w^2*(sourceSparseCount T s b:ℝ) := by positivity
  have htail : 4*(w^2*(sourceSparseCount T s b:ℝ))^R/(1-w^2*(sourceSparseCount T s b:ℝ)) ≤
      8*(w^2*(sourceSparseCount T s b:ℝ))^R := by
    apply (div_le_iff₀ (by linarith only [hhalf])).mpr
    have hh := mul_le_mul_of_nonneg_right hhalf (pow_nonneg hx R)
    nlinarith only [hh]
  apply htail.trans
  have hrp : (N^(-gap))^R=N^(-gap*(R:ℝ)) := by rw [←Real.rpow_natCast,←Real.rpow_mul hN0.le]
  have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hsparse R) (by norm_num : (0:ℝ)≤8)
  simpa only [mul_pow,hrp,mul_assoc] using hh

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem hiddenSmoothingBound_scale {N e K ω : ℝ} {m s : ℕ}
    (hN : 0 < N) (hK : 0 ≤ K)
    (hm : hiddenBinomialCap m ω ≤ K*N^(-e/2)) :
    hiddenSmoothingBound m s ω ≤ sourceSmoothingPrefactor s K*N^(-((s:ℝ)+1)*e/2) := by
  have hs : 1 ≤ (s:ℝ)+1 := by linarith [Nat.cast_nonneg s (α:=ℝ)]
  have hs0 : 0 ≤ (s:ℝ)+1 := by positivity
  have heq : 4*((s:ℝ)+1)/((m:ℝ)*ω^2+2)=((s:ℝ)+1)*(4/((m:ℝ)*ω^2+2)) := by ring
  have hh : Real.sqrt (4*((s:ℝ)+1)/((m:ℝ)*ω^2+2)) ≤ ((s:ℝ)+1)*K*N^(-e/2) := by
    rw [heq,Real.sqrt_mul hs0]
    have hsq : Real.sqrt ((s:ℝ)+1) ≤ (s:ℝ)+1 := by
      apply (Real.sqrt_le_iff).mpr
      exact ⟨hs0,by nlinarith only [hs,sq_nonneg ((s:ℝ))]⟩
    have h := mul_le_mul hsq hm (Real.sqrt_nonneg _) hs0
    simpa only [hiddenBinomialCap,mul_assoc] using h
  have hleft := mul_le_mul
    (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤2)) s)
    hh (Real.sqrt_nonneg _) (by positivity)
  apply (mul_le_mul_of_nonneg_left hleft (by positivity : (0:ℝ)≤2^(s*s))).trans_eq
  have hr : (N^(-e/2))^(s+1)=N^(-((s:ℝ)+1)*e/2) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hN.le]
    push_cast
    congr 1
    ring
  dsimp [sourceSmoothingPrefactor]
  rw [pow_add,pow_succ (((s:ℝ)+1)*K)]
  simp only [mul_pow]
  have he : (N^(-e/2))^s*N^(-e/2)=N^(-((s:ℝ)+1)*e/2) := by rw [←pow_succ,hr]
  calc
    _ = (2:ℝ)^(s*s)*2^s*((s:ℝ)+1)^s*K^s*(((s:ℝ)+1)*K)*
      ((N^(-e/2))^s*N^(-e/2)) := by ring
    _ = _ := by rw [he]; ring

end TraceReconstruction


end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Propagation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Propagation

Moment restriction, scale margins, sharp budget closure, clipping and error propagation, and dense/warmup overlap.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem sourceGapFloor_pos (B : ℕ) : 0 < sourceGapFloor B := by unfold sourceGapFloor; positivity

theorem sourceGapFloor_le_one (B : ℕ) : sourceGapFloor B≤1 := by
  unfold sourceGapFloor
  apply (div_le_one (by positivity)).mpr
  have hh : (1:ℝ)≤2^(2*B) := one_le_pow₀ (by norm_num)
  linarith only [hh]

theorem sourceEpsilon_gap_small (B D : ℕ) : 1000*sourceEpsilon B D ≤ sourceGapFloor B := by
  have hp : (1000:ℝ)*128*2^(2*B) ≤ 2^(4*B+100) := by
    have hpow : (2:ℝ)^(2*B+17) ≤ 2^(4*B+100) := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [pow_add] at hpow
    norm_num only [show (2:ℝ)^17=131072 by norm_num] at hpow
    have hpos : 0≤(2:ℝ)^(2*B) := by positivity
    linarith only [hpow,hpos]
  have hd : 1≤(D:ℝ)+1 := by linarith [Nat.cast_nonneg D (α:=ℝ)]
  have hh := mul_le_mul_of_nonneg_left hd (show 0≤(2:ℝ)^(4*B+100) by positivity)
  unfold sourceEpsilon sourceGapFloor
  rw [←mul_div_assoc, mul_one]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [hp,hh]

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem sourceWorkSize_pos (B D : ℕ) (hB : 2≤ B) : 0< sourceWorkSize B D := by
  unfold sourceWorkSize
  have hd := (totalScoreExponent_bounds B D hB).1
  have hr := Nat.cast_nonneg (sourceDegreeCutoff B) (α:=ℝ)
  have hb := Nat.cast_nonneg B (α:=ℝ)
  linarith only [hd,hr,hb]

theorem sourceCancellationOrder_lower (B D : ℕ) :
    100*sourceWorkSize B D ≤ (sourceCancellationOrder B D:ℝ)*sourceEpsilon B D := by
  exact (div_le_iff₀ (sourceEpsilon_pos B D)).mp (Nat.le_ceil _)

theorem source_smoothing_absorb {B D : ℕ} {N K ω : ℝ} {m : ℕ}
    (hB : 2≤ B) (hN : 1≤ N) (hK : 0≤ K)
    (hm : hiddenBinomialCap m ω ≤ K*N^(-sourceEpsilon B D/2))
    (hpref : sourceSmoothingPrefactor (sourceCancellationOrder B D) K ≤ N^(sourceEpsilon B D)) :
    hiddenSmoothingBound m (sourceCancellationOrder B D) ω ≤ N^(-20*sourceWorkSize B D) := by
  have hN0 : 0< N := by linarith only [hN]
  apply (hiddenSmoothingBound_scale hN0 hK hm).trans
  apply (mul_le_mul_of_nonneg_right hpref (by positivity)).trans
  rw [←Real.rpow_add hN0]
  apply Real.rpow_le_rpow_of_exponent_le hN
  have hs := sourceCancellationOrder_lower B D
  have hw := sourceWorkSize_pos B D hB
  have he := sourceEpsilon_pos B D
  have he' : sourceEpsilon B D ≤ 1 := by
    simpa only [pow_zero,one_mul] using sourceEpsilon_power_small B D 0 (by omega)
  have hW : 10≤ sourceWorkSize B D := by
    unfold sourceWorkSize
    have hd := (totalScoreExponent_bounds B D hB).1
    have hr := Nat.cast_nonneg (sourceDegreeCutoff B) (α:=ℝ)
    have hb := Nat.cast_nonneg B (α:=ℝ)
    linarith only [hd,hr,hb]
  nlinarith only [hs,he,he',hW]

/-- The actual sparse count controls both extra forced roles and clipping. -/
theorem sparse_power_absorb {N ε gap W L x : ℝ}
    (hN : 1≤ N) (he : 0≤ε) (hg : 2*ε≤ gap) (hW : 0≤ W) (hL : 1≤ L)
    (hx : x≤ W*L*N^(-gap)) (hfac : 8*W*L^2≤ N^ε) :
    x≤ N^(-gap/2)/8 ∧ x≤1/2 ∧ x*L≤1 := by
  have hN0 : 0< N := by linarith only [hN]
  have hL0 : 0≤ L := by linarith only [hL]
  have hg0 : 0≤ gap := by linarith only [he,hg]
  have hwl : 8*W*L≤ N^ε := by
    have hh : L≤ L^2 := by nlinarith only [hL,sq_nonneg (L-1)]
    exact (mul_le_mul_of_nonneg_left hh (by positivity : 0≤8*W)).trans hfac
  have hx' : x≤ N^(ε-gap)/8 := by
    have hh := mul_le_mul_of_nonneg_right hwl (Real.rpow_pos_of_pos hN0 (-gap)).le
    rw [←Real.rpow_add hN0] at hh
    have heq : ε+-gap=ε-gap := by ring
    rw [heq] at hh
    nlinarith only [hx,hh]
  have hsmall := Real.rpow_le_rpow_of_exponent_le hN (show ε-gap≤-gap/2 by linarith only [hg])
  have hxhalf : x≤ N^(-gap/2)/8 := hx'.trans (div_le_div_of_nonneg_right hsmall (by norm_num))
  have hone : N^(-gap/2)≤1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith only [hg0])
  refine ⟨hxhalf,by linarith only [hxhalf,hone],?_⟩
  have hh := mul_le_mul_of_nonneg_right hfac (Real.rpow_pos_of_pos hN0 (-gap)).le
  rw [←Real.rpow_add hN0] at hh
  have hh' := mul_le_mul_of_nonneg_right hx hL0
  have hr := Real.rpow_le_one_of_one_le_of_nonpos hN (show ε+-gap≤0 by linarith only [hg,he])
  nlinarith only [hh,hh',hr]

theorem source_weight_square {N e d L : ℝ} {k : ℕ} (hN : 0< N)
    (hL : L=N^(-e*d/2)) :
    ((6*(2*k:ℕ):ℝ)*L)^2=144*(k:ℝ)^2*N^(-e*d) := by
  rw [hL,mul_pow]
  have hr : (N^(-e*d/2))^2=N^(-e*d) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hN.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  rw [hr]
  push_cast
  ring

theorem source_high_tail_margin (B : ℕ) {d : ℝ} (_hB : 2≤ B) (hd : 0≤ d) :
    d+blockGain B+1 ≤ ((d+1)*sourceGapFloor B)/2*(sourceDegreeCutoff B:ℝ) := by
  have hp : (2:ℝ)^(2*B+8)*(B+2) ≤ 2^(10*B+40) := by
    have hb : (B:ℝ)+2 ≤ (2:ℝ)^(B+2) := by
      have hh : B+1 < 2^(B+1) := Nat.lt_two_pow_self
      have hh' : B+2≤2^(B+1) := by omega
      have hcast : (B:ℝ)+2≤(2:ℝ)^(B+1) := by exact_mod_cast hh'
      exact hcast.trans (pow_le_pow_right₀ (by norm_num) (by omega))
    have hh := mul_le_mul_of_nonneg_left hb (show (0:ℝ)≤2^(2*B+8) by positivity)
    rw [←pow_add] at hh
    exact hh.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  have hc : (B:ℝ)+2 ≤ sourceGapFloor B/2*(sourceDegreeCutoff B:ℝ) := by
    unfold sourceGapFloor sourceDegreeCutoff
    push_cast
    calc
      (B:ℝ)+2 ≤ 2^(10*B+40)/(256*2^(2*B)) := by
        apply (le_div_iff₀ (by positivity : (0:ℝ)<256*2^(2*B))).mpr
        rw [pow_add] at hp
        norm_num only [show (2:ℝ)^8=256 by norm_num] at hp
        nlinarith only [hp]
      _ = _ := by field_simp; norm_num
  have hh := mul_le_mul_of_nonneg_left hc (show 0≤ d+1 by linarith only [hd])
  unfold blockGain
  have hb : (0:ℝ)≤ B := Nat.cast_nonneg _
  nlinarith only [hh,hd,hb,mul_nonneg hd hb]

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem rpow_coefficient_absorb {N ε e d c : ℝ} (hN : 1≤ N)
    (hc : 3*c≤ N^ε) (he : ε+e≤ d) : c*N^e ≤ N^d/3 := by
  have hN0 : 0< N := by linarith only [hN]
  have hh := mul_le_mul_of_nonneg_right hc (Real.rpow_pos_of_pos hN0 e).le
  rw [←Real.rpow_add hN0] at hh
  have hr := Real.rpow_le_rpow_of_exponent_le hN he
  linarith only [hh,hr]

/-- Closing the three explicit sharp classes, with the source's fixed
 finite degree cutoff and no hidden dependence on N in their constants. -/
theorem sharp_energy_absorb {N ε d M Fdec gap Cr Cf E : ℝ} {R : ℕ}
    (hN : 1≤ N) (he : ε≤1) (hM : d+(R:ℝ)+1≤ M) (hd : 0≤ d) (_hR : 0≤(R:ℝ))
    (hbad : 384*Cr≤ N^ε) (hforce : 192*Cf≤ N^ε) (htail : 1536≤ N^ε)
    (hfdec : d+ε≤ Fdec) (hgap : d+ε≤ gap*(R:ℝ))
    (hE : E ≤ Cr*N^R*((N^(-20*M))^2+(N^(-20*M))^2)+Cf*N^(-Fdec)+8*N^(-gap*(R:ℝ))) :
    64*E≤ N^(-d) := by
  have hN0 : 0< N := by linarith only [hN]
  have hpow : N^R*(N^(-20*M))^2=N^((R:ℝ)-40*M) := by
    rw [←Real.rpow_natCast (N^(-20*M)) 2,←Real.rpow_mul hN0.le,←Real.rpow_natCast N R,←Real.rpow_add hN0]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  have hb := rpow_coefficient_absorb hN (c:=128*Cr) (by nlinarith only [hbad])
    (e:=(R:ℝ)-40*M) (d:=-d) (by linarith only [hM,hd,he])
  have hf := rpow_coefficient_absorb hN (c:=64*Cf) (by nlinarith only [hforce])
    (e:=-Fdec) (d:=-d) (by linarith only [hfdec])
  have ht := rpow_coefficient_absorb hN (c:=512) (by norm_num at htail ⊢; exact htail)
    (e:=-gap*(R:ℝ)) (d:=-d) (by linarith only [hgap])
  have hh := mul_le_mul_of_nonneg_left hE (by norm_num : (0:ℝ)≤64)
  have heq : 64*(Cr*N^R*((N^(-20*M))^2+(N^(-20*M))^2)+Cf*N^(-Fdec)+8*N^(-gap*(R:ℝ))) =
      128*Cr*N^((R:ℝ)-40*M)+64*Cf*N^(-Fdec)+512*N^(-gap*(R:ℝ)) := by
    calc
      _ = 128*Cr*(N^R*(N^(-20*M))^2)+64*Cf*N^(-Fdec)+512*N^(-gap*(R:ℝ)) := by ring
      _ = _ := by rw [hpow]
  rw [heq] at hh
  linarith only [hh,hb,hf,ht]

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem sourceDimension_bounds (B i : ℕ) (hB : 2≤ B) :
    2≤ sourceDimension B i ∧ sourceDimension B i≤ B := by
  unfold sourceDimension
  split_ifs <;> omega

theorem totalScoreExponent_mono (B : ℕ) (hB : 2≤ B) : Monotone (totalScoreExponent B) := by
  apply monotone_nat_of_le_succ
  intro i
  rw [totalScoreExponent_step]
  exact le_add_of_nonneg_right (blockGain_pos _ (sourceDimension_bounds B i hB).1).le

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem sourceSparseCount_ge_one (T : ℕ→ℕ) (s b : ℕ) (hT : ∀j<b,1 ≤ T (j+1)) :
    1 ≤ sourceSparseCount T s b := by
  unfold sourceSparseCount
  apply one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by omega))
  exact Finset.one_le_prod' (fun j hj=>hT j (Finset.mem_range.mp hj))

/-- Scalar closure of the exact sparse/forced block budget. All assumptions
 here are explicit elementary coefficient bounds, not oracle conclusions. -/
theorem source_block_energy_close (T n : ℕ→ℕ) (s b R : ℕ) (ω N ε d dnew K W M gap : ℝ)
    (hN : 1 ≤ N) (he : 0 ≤ ε) (he1 : ε ≤ 1) (hK : 0 ≤ K) (hW : 0 ≤ W)
    (hd : 0 ≤ dnew) (hM : dnew+(R:ℝ)+1 ≤ M) (hg : 2*ε ≤ gap)
    (hf : dnew+ε ≤ forcedDecay (b+1) ε d) (hR : dnew+ε ≤ gap/2*(R:ℝ))
    (hfac : 8*W*((2^s:ℕ):ℝ)^2 ≤ N^ε)
    (hbad : 384*sourceBadRoleFactor b R ≤ N^ε)
    (hforce : 192*(sourceForcedRoleFactor b R*W^(2^(b+1))*sourceSkeletonPrefactor s b K) ≤ N^ε)
    (htail : 1536 ≤ N^ε)
    (hleaf : (SourceLeafCount T (b+1):ℝ) ≤ N)
    (hcount : 1 ≤ sourceSparseCount T s b)
    (k : ℕ) (L : ℝ)
    (hw : ((6*(2*k:ℕ):ℝ)*L)^2 ≤ W*N^(-scaleA (b+1) 0 ε*d))
    (hsparse : ((6*(2*k:ℕ):ℝ)*L)^2*(sourceSparseCount T s b:ℝ) ≤
      W*((2^s:ℕ):ℝ)*N^(-gap))
    (hn : ∀j ≤ b,hiddenBinomialCap (n j) ω ≤ K*N^(-ε/2))
    (hgcap : ∀j<b,hiddenBinomialCap (sourceScheduledTrials T n (j+1)) ω ≤
      K*N^(-(scaleKappa (b+1) (j+2) ε+ε)/2)) :
    ((6*(2*k:ℕ):ℝ)*L)^2*(sourceSparseCount T s b:ℝ) ≤ N^(-gap/2)/8 ∧
    ((6*(2*k:ℕ):ℝ)*L)^2*(sourceSparseCount T s b:ℝ) ≤ 1/2 ∧
    64*sourceSharpEnergyBudget T n s b R ω (N^(-20*M)) (N^(-20*M)) ((6*(2*k:ℕ):ℝ)*L) ≤ N^(-dnew) := by
  let w := (6*(2*k:ℕ):ℝ)*L
  have hmot : 1 ≤ ((2^s:ℕ):ℝ) := by exact_mod_cast (one_le_pow₀ (by omega : 1 ≤ (2:ℕ)) : 1 ≤ (2:ℕ)^s)
  have hx := sparse_power_absorb hN he hg hW hmot hsparse hfac
  have hwone : w^2 ≤ 1 := by
    have hc : (1:ℝ) ≤ sourceSparseCount T s b := by exact_mod_cast hcount
    have hh := mul_le_mul_of_nonneg_left hc (sq_nonneg w)
    dsimp [w] at hh
    nlinarith only [hh,hx.2.1]
  have hsmall : w^2*((2^s:ℕ):ℝ)*(sourceSparseCount T s b:ℝ) ≤ 1 := by
    dsimp [w]
    nlinarith only [hx.2.2]
  have hr : w^2*(sourceSparseCount T s b:ℝ) ≤ 1*N^(-(gap/2)) := by
    have hp : 0 ≤ N^(-gap/2) := Real.rpow_nonneg (by linarith only [hN]) _
    dsimp [w]
    rw [←neg_div]
    nlinarith only [hx.1,hp]
  have hnum := source_sharp_numeric T n s b R ω (N^(-20*M)) (N^(-20*M)) w N ε d K W 1 (gap/2)
    hN hK hW (by norm_num) hleaf hwone hw hsmall hx.2.1 hr hn hgcap
  simp only [one_pow,mul_one] at hnum
  refine ⟨hx.1,hx.2.1,?_⟩
  exact sharp_energy_absorb hN he1 hM hd (Nat.cast_nonneg _) hbad hforce htail hf hR hnum

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Instantiation at the manuscript's literal block dimension, integer
 schedules, source cutoff, moment envelope, and full next score exponent. -/
theorem source_level_energy_oai (B D i ell h k : ℕ) (C N F ω K : ℝ)
    (hB : 2 ≤ B) (hi : i<D) (hN : 1 ≤ N) (hC : 1 ≤ C) (hF : 1 ≤ F) (hω : 0<ω)
    (H : SourceArithmeticBounds C N F (sourceEpsilon B D) (sourceCancellationOrder B D)
      (sourceDimension B i) ell h)
    (hk : (k:ℝ) ≤ sourceMomentEnvelope B D)
    (hK : 200*(C^(2*sourceDimension B i)*F)/ω ≤ K)
    (hfac : 8*sourceWeightEnvelope B D*((2^(sourceCancellationOrder B D):ℕ):ℝ)^2 ≤ N^(sourceEpsilon B D))
    (hbad : 384*sourceBadRoleFactor (sourceDimension B i-1) (sourceDegreeCutoff B) ≤ N^(sourceEpsilon B D))
    (hforce : 192*(sourceForcedRoleFactor (sourceDimension B i-1) (sourceDegreeCutoff B)*
        (sourceWeightEnvelope B D)^(2^(sourceDimension B i))*
        sourceSkeletonPrefactor (sourceCancellationOrder B D) (sourceDimension B i-1) K) ≤ N^(sourceEpsilon B D))
    (htail : 1536 ≤ N^(sourceEpsilon B D))
    (hsmooth : sourceSmoothingPrefactor (sourceCancellationOrder B D) K ≤ N^(sourceEpsilon B D)) :
    let b := sourceDimension B i
    let ε := sourceEpsilon B D
    let s := sourceCancellationOrder B D
    let T := sourceBlockWindows N b ε
    let t := sourceArithmeticTrials C N b ε ell h
    let L := N^(-scaleA b 0 ε*totalScoreExponent B i/2)
    (((6*(2*k:ℕ):ℝ)*L)^2*(sourceSparseCount T s (b-1):ℝ) ≤
        N^(-((totalScoreExponent B i+1)*sourceGapFloor B)/2)/8) ∧
    (((6*(2*k:ℕ):ℝ)*L)^2*(sourceSparseCount T s (b-1):ℝ) ≤ 1/2) ∧
    (64*sourceSharpEnergyBudget T t s (b-1) (sourceDegreeCutoff B) ω
       (N^(-20*sourceWorkSize B D)) (N^(-20*sourceWorkSize B D)) ((6*(2*k:ℕ):ℝ)*L) ≤
       N^(-totalScoreExponent B (i+1))) ∧
    (∀j<b,hiddenSmoothingBound (t j) s ω ≤ N^(-20*sourceWorkSize B D)) := by
  let b := sourceDimension B i
  let ε := sourceEpsilon B D
  let s := sourceCancellationOrder B D
  let d := totalScoreExponent B i
  let dnew := totalScoreExponent B (i+1)
  let W := sourceWeightEnvelope B D
  let gap := (d+1)*sourceGapFloor B
  let T := sourceBlockWindows N b ε
  let t := sourceArithmeticTrials C N b ε ell h
  let L := N^(-scaleA b 0 ε*d/2)
  have hb := sourceDimension_bounds B i hB
  have hb1 : b-1+1=b := by dsimp [b]; omega
  have he := sourceEpsilon_pos B D
  have he1 : ε ≤ 1/100 := by
    have hh := sourceEpsilon_gap_small B D
    have hg := sourceGapFloor_le_one B
    dsimp [ε]
    linarith only [hh,hg]
  have hd : 0 ≤ d := le_trans (by norm_num) (totalScoreExponent_bounds B i hB).1
  have hdnew : 0 ≤ dnew := le_trans (by norm_num) (totalScoreExponent_bounds B (i+1) hB).1
  have hdle : d ≤ totalScoreExponent B D := totalScoreExponent_mono B hB (Nat.le_of_lt hi)
  have hdnewle : dnew ≤ totalScoreExponent B D := totalScoreExponent_mono B hB (by omega)
  have hdd : d ≤ 3+(B:ℝ)*D := by
    have hh := (totalScoreExponent_bounds B D hB).2
    nlinarith only [hdle,hh]
  have hN0 : 0<N := by linarith only [hN]
  have hK0 : 0 ≤ K := le_trans (by positivity : 0 ≤ 200*(C^(2*sourceDimension B i)*F)/ω) hK
  have hW : 0 ≤ W := by dsimp [W,sourceWeightEnvelope]; exact mul_nonneg (by norm_num) (sq_nonneg _)
  have hM : dnew+(sourceDegreeCutoff B:ℝ)+1 ≤ sourceWorkSize B D := by
    unfold sourceWorkSize
    linarith only [hdnewle,Nat.cast_nonneg B (α:=ℝ)]
  have hg : 2*ε ≤ gap := by
    have hf := sourceGapFloor_pos B
    have hh := sourceEpsilon_gap_small B D
    dsimp [gap,ε]
    nlinarith only [hh,hd,mul_nonneg hd hf.le,he]
  have hfdec : dnew+ε ≤ forcedDecay b ε d := by
    have hh := forcedDecay_margin B D b d (by dsimp [b]; omega) hb.2 hd hdd
    have heq : dnew=d+blockGain b := totalScoreExponent_step B i
    rw [heq]
    unfold blockGain
    linarith only [hh,he1]
  have hR : dnew+ε ≤ gap/2*(sourceDegreeCutoff B:ℝ) := by
    have hh := source_high_tail_margin B hB hd
    have heq : dnew=d+blockGain b := totalScoreExponent_step B i
    have hbg : blockGain b ≤ blockGain B := by unfold blockGain; exact (by
      have hcast : (b:ℝ) ≤ B := by exact_mod_cast hb.2
      linarith only [hcast])
    dsimp [gap]
    rw [heq]
    linarith only [hh,hbg,he1]
  have hw : ((6*(2*k:ℕ):ℝ)*L)^2 ≤ W*N^(-scaleA b 0 ε*d) := by
    rw [source_weight_square hN0 (show L=N^(-scaleA b 0 ε*d/2) from rfl)]
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg k) hk 2) (by norm_num : (0:ℝ)≤144)
    exact mul_le_mul_of_nonneg_right hh (Real.rpow_pos_of_pos hN0 _).le
  have hsparse : ((6*(2*k:ℕ):ℝ)*L)^2*(sourceSparseCount T s (b-1):ℝ) ≤ W*((2^s:ℕ):ℝ)*N^(-gap) := by
    apply (source_sparse_weight_bound N ε d W _ b s hN0 hW hw).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le hN
    have hh := source_level_sparse_gap B D i hB
    have heq : (d+1)/(128*(2:ℝ)^(2*B))=gap := by dsimp [gap,sourceGapFloor]; ring
    rw [heq] at hh
    linarith only [hh]
  have hcaps := H.binomial_caps hN0 hC hF hω
  have hncap (j) (hj : j<b) : hiddenBinomialCap (t j) ω ≤ K*N^(-ε/2) :=
    (hcaps.1 j hj).trans (mul_le_mul_of_nonneg_right hK (Real.rpow_pos_of_pos hN0 _).le)
  have hgcap (j) (hj : j<b-1) : hiddenBinomialCap (sourceScheduledTrials T t (j+1)) ω ≤
      K*N^(-(scaleKappa b (j+2) ε+ε)/2) :=
    (hcaps.2 j (by omega)).trans (mul_le_mul_of_nonneg_right hK (Real.rpow_pos_of_pos hN0 _).le)
  have hc : 1 ≤ sourceSparseCount T s (b-1) := sourceSparseCount_ge_one T s (b-1)
    (fun j _=>Nat.succ_le_of_lt (H.window_positive (j+1)))
  have HE := source_block_energy_close T t s (b-1) (sourceDegreeCutoff B) ω N ε d dnew K W
    (sourceWorkSize B D) gap hN he.le (by linarith only [he1]) hK0 hW hdnew hM hg
    (by rw [hb1]; exact hfdec) hR hfac hbad (by rw [hb1]; exact hforce) htail
    (by rw [hb1]; exact H.leaf_bound hN0) hc k L (by rw [hb1]; exact hw) hsparse
    (fun j hj=>hncap j (by omega)) (fun j hj=>by rw [hb1]; exact hgcap j hj)
  refine ⟨HE.1,HE.2.1,HE.2.2,?_⟩
  intro j hj
  exact source_smoothing_absorb hB hN hK0 (hncap j hj) hsmooth

end TraceReconstruction
end
end
end
end
end
end
end
end

end OAI
end

theorem solution : type_of% @OAI.TraceReconstruction.source_level_energy_oai := @OAI.TraceReconstruction.source_level_energy_oai
