-- Prove2me | solution 1 for OAI.TraceReconstruction.source_level_all_budgets
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:02:49.203279+00:00
-- url     : https://prove2.me/submissions/621c09d3-b1d5-4d76-bf4c-6fe61cc9b170

import Mathlib
import Definitions.Def_OAIQ9Tr002
import Theorems.Thm_OAI_TraceReconstruction_source_level_energy

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

theorem scaleA_step (b j : ℕ) (ε : ℝ) : scaleA b (j+1) ε - 2*scaleA b j ε = ε := by
  unfold scaleA
  rw [pow_succ]
  ring

theorem scaleKappa_step (b j : ℕ) (ε : ℝ) (hj : 1 ≤ j) :
    2*scaleKappa b j ε - scaleKappa b (j+1) ε - ε = ε := by
  unfold scaleKappa scaleA
  simp only [Nat.add_sub_cancel]
  rw [show j = (j-1)+1 from by omega, pow_succ]
  simp only [Nat.add_sub_cancel, pow_succ]
  ring

theorem sourceEpsilon_pos (B D : ℕ) : 0 < sourceEpsilon B D := by
  unfold sourceEpsilon
  positivity

end TraceReconstruction

open Filter
open scoped Topology


open Filter
open scoped Topology

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical
open Filter

theorem sourceTargetScale_step (B D i : ℕ) (n : ℝ) (hn : 0 ≤ n) (hi : i < D) :
    sourceTargetScale B D n i =
      (sourceTargetScale B D n (i+1))^(scaleA (sourceDimension B i) 0 (sourceEpsilon B D)) := by
  unfold sourceTargetScale sourceScaleProduct
  rw [←Real.rpow_mul hn,Finset.prod_eq_prod_Ico_succ_bot hi]
  rw [mul_comm]

theorem sourceEpsilon_small (B D : ℕ) :
    ((D:ℝ)+1)*(2:ℝ)^B*sourceEpsilon B D ≤ 1/2 := by
  have hp : 2*(2:ℝ)^B ≤ (2:ℝ)^(4*B+100) := by
    rw [←pow_succ']
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  unfold sourceEpsilon
  have hD : 0 < (D:ℝ)+1 := by positivity
  have hpow : 0 < (2:ℝ)^(4*B+100) := by positivity
  apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  have he : ((D:ℝ)+1)*2^B*(1/(2^(4*B+100)*((D:ℝ)+1)))*2 =
      (2*2^B)/2^(4*B+100) := by field_simp
  rw [he]
  exact (div_le_one hpow).mpr hp

theorem scaleA_zero_lower (b B : ℕ) (ε : ℝ) (hb : b ≤ B) (he : 0 ≤ ε) :
    (1/((2:ℝ)^B))*(1-((2:ℝ)^B-1)*ε) ≤ scaleA b 0 ε := by
  have hp : (2:ℝ)^b ≤ 2^B := pow_le_pow_right₀ (by norm_num) hb
  have hpos : 0 < (2:ℝ)^b := by positivity
  have hposB : 0 < (2:ℝ)^B := by positivity
  have hd := div_le_div_of_nonneg_left (show 0 ≤ 1+ε by linarith) hpos hp
  have heq : (1/((2:ℝ)^B))*(1-((2:ℝ)^B-1)*ε) = (1+ε)/2^B-ε := by
    field_simp; ring
  rw [heq]
  unfold scaleA
  norm_num only [pow_zero,mul_one]
  linarith only [hd]

theorem sourceScaleProduct_lower (B D i : ℕ) (hB : 2 ≤ B) :
    1/(2*((2:ℝ)^(B*D))) ≤ sourceScaleProduct B D i := by
  let ε := sourceEpsilon B D
  let u := ((2:ℝ)^B-1)*ε
  let a := (1/(2:ℝ)^B)*(1-u)
  have hε : 0 < ε := sourceEpsilon_pos _ _
  have hp : (1:ℝ) ≤ 2^B := one_le_pow₀ (by norm_num)
  have hu : 0 ≤ u := mul_nonneg (sub_nonneg.mpr hp) hε.le
  have hsmall := sourceEpsilon_small B D
  have hu' : ((D:ℝ)+1)*u ≤ 1/2 := by
    dsimp [u]
    dsimp [ε] at *
    nlinarith only [mul_nonneg (show 0 ≤ (D:ℝ)+1 by positivity) hε.le,hsmall]
  have hu1 : u ≤ 1/2 := by nlinarith only [hu',mul_nonneg (Nat.cast_nonneg D) hu]
  have ha : 0 ≤ a := mul_nonneg (by positivity) (by linarith only [hu1])
  have ha1 : a ≤ 1 := by
    dsimp [a]
    have h1 : 1/(2:ℝ)^B ≤ 1 := (div_le_one (by positivity)).mpr hp
    exact (mul_le_mul_of_nonneg_left (by linarith only [hu] : 1-u ≤ 1) (by positivity)).trans (by simpa using h1)
  have hb : 1/2 ≤ (1-u)^D := by
    have H := one_add_mul_le_pow (a := -u) (by linarith only [hu1]) D
    have hd : (D:ℝ)*u ≤ 1/2 := by nlinarith only [hu',hu]
    simpa only [sub_eq_add_neg] using (show (1:ℝ)/2 ≤ (1+-u)^D by nlinarith only [H,hd])
  have hc : (Finset.Ico i D).card ≤ D := by simp only [Nat.card_Ico]; omega
  calc
    _ = (1/(2:ℝ)^B)^D*(1/2) := by rw [div_pow,one_pow,←pow_mul]; field_simp
    _ ≤ (1/(2:ℝ)^B)^D*(1-u)^D := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = a^D := (mul_pow _ _ _).symm
    _ ≤ a^(Finset.Ico i D).card := pow_le_pow_of_le_one ha ha1 hc
    _ = ∏j∈Finset.Ico i D,a := by simp
    _ ≤ sourceScaleProduct B D i := by
      apply Finset.prod_le_prod (fun _ _ => ha)
      intro j _
      apply scaleA_zero_lower _ _ _ _ hε.le
      unfold sourceDimension
      split_ifs <;> omega

end TraceReconstruction


end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_InitialOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# InitialOverlap

Literal periods, count overlap, initial low/high energies, genuine densities, and centered moment bounds.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology



noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem primitivePeriodConstant_nonneg : 0 ≤ primitivePeriodConstant := by
  unfold primitivePeriodConstant
  positivity

end TraceReconstruction



noncomputable section



noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem initialOverlapLower_pos (q : ℝ) : 0 < initialOverlapLower q := by
  unfold initialOverlapLower
  positivity

theorem initialOverlapLower_lt_eighth {q : ℝ} (hq : 0 < q) :
    initialOverlapLower q < 1/8 := by
  have hx : -(32+3*primitivePeriodConstant)/q^3 ≤ 0 := by
    have hc := primitivePeriodConstant_nonneg
    apply div_nonpos_of_nonpos_of_nonneg <;> nlinarith [pow_pos hq 3]
  have he : Real.exp (-(32+3*primitivePeriodConstant)/q^3) ≤ 1 := by
    simpa using Real.exp_le_exp.mpr hx
  unfold initialOverlapLower
  linarith

end TraceReconstruction



/-! From the actual displaced period words to their conditional oracle
moments.  The coefficient bounds are the rank kernels,
not assumptions on an abstract pair. -/
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


noncomputable section


noncomputable section


noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section



noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem sourceCenteredBudget_nonneg (T : ℕ → ℕ) (s b k : ℕ) (L : ℝ)
    (hsmall : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b<1) :
    0 ≤ sourceCenteredBudget T s b k L :=
  div_nonneg (by positivity) (sub_nonneg.mpr hsmall.le)

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

theorem sourceHalfMoment_bounds (B D i : ℕ) {n : ℝ} (hB : 2 ≤ B) (hn : 1<n) :
    1 ≤ sourceHalfMoment B D n i ∧
    (sourceHalfMoment B D n i:ℝ) ≤
      ((10^8:ℝ)*2^(10*B)*((B:ℝ)+4)*2+1)*((D:ℝ)+1)*2^(B*D) := by
  have hp := sourceScaleProduct_lower B D i hB
  have hp0 : 0 < sourceScaleProduct B D i := lt_of_lt_of_le (by positivity) hp
  have he : (10^8:ℝ)*2^(10*B)*(totalScoreExponent B D+B+1)*Real.log n/
      Real.log (sourceTargetScale B D n i)=
      (10^8:ℝ)*2^(10*B)*(totalScoreExponent B D+B+1)/sourceScaleProduct B D i := by
    rw [sourceTargetScale,Real.log_rpow (by linarith : 0<n)]
    field_simp [(Real.log_pos hn).ne']
  have hd := totalScoreExponent_bounds B D hB
  have hA : 0<(10^8:ℝ)*2^(10*B)*(totalScoreExponent B D+B+1) := by positivity [hd.1]
  unfold sourceHalfMoment
  rw [he]
  constructor
  · exact Nat.one_le_ceil_iff.mpr (div_pos hA hp0)
  have hc := Nat.ceil_lt_add_one (div_nonneg hA.le hp0.le)
  have hb := div_le_div_of_nonneg_left hA.le (by positivity) hp
  have he' : (10^8:ℝ)*2^(10*B)*(totalScoreExponent B D+B+1)/(1/(2*2^(B*D)))=
      (10^8:ℝ)*2^(10*B)*(totalScoreExponent B D+B+1)*2*2^(B*D) := by field_simp
  rw [he'] at hb
  have hdd : totalScoreExponent B D+B+1 ≤ ((B:ℝ)+4)*((D:ℝ)+1) := by nlinarith [hd.2]
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hdd (by positivity : (0:ℝ) ≤ 10^8*2^(10*B)))
    (by positivity : (0:ℝ) ≤ 2*2^(B*D))
  have hp1 : (1:ℝ) ≤ 2^(B*D) := one_le_pow₀ (by norm_num)
  nlinarith [show (0:ℝ) ≤ D by positivity]

end TraceReconstruction


noncomputable section


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

variable {N f g : ℕ→ℝ} {α β : ℝ}

theorem sourceOverlapConstant_pos {q : ℝ} (hq : 0<q) : 0 < sourceOverlapConstant q := by
  unfold sourceOverlapConstant
  positivity [initialOverlapLower_pos q]

theorem sourceOverlapConstant_large {q : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ)) :
    1073741824 ≤ initialOverlapLower q*sourceOverlapConstant q := by
  have hω := initialOverlapLower_pos q
  have he : initialOverlapLower q*sourceOverlapConstant q=(2:ℝ)^40/q := by
    unfold sourceOverlapConstant
    field_simp
  rw [he]
  apply (le_div_iff₀ hq.1).mpr
  nlinarith [hq.2]

end TraceReconstruction


noncomputable section


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

/-- All backwards targets are no larger than n, with the source epsilon. -/
theorem sourceScaleProduct_le_one (B D i : ℕ) (hB : 2 ≤ B) : sourceScaleProduct B D i ≤ 1 := by
  apply Finset.prod_le_one
  · intro j _
    have hdim : sourceDimension B j ≤ B := by unfold sourceDimension; split_ifs <;> omega
    have he := sourceEpsilon_pos B D
    have hh := sourceEpsilon_small B D
    have hp : (1:ℝ) ≤ 2^B := one_le_pow₀ (by norm_num)
    have hd : 0 ≤ (D:ℝ) := Nat.cast_nonneg _
    have hu : (2:ℝ)^B*sourceEpsilon B D ≤ 1/2 := by
      nlinarith only [hh,mul_nonneg hd (mul_nonneg (le_trans zero_le_one hp) he.le)]
    have hx := scaleA_zero_lower (sourceDimension B j) B (sourceEpsilon B D) hdim he.le
    apply le_trans _ hx
    exact mul_nonneg (by positivity) (by nlinarith only [hu,he])
  · intro j _
    have he := sourceEpsilon_pos B D
    have hp : (1:ℝ) ≤ 2^(sourceDimension B j) := one_le_pow₀ (by norm_num)
    unfold scaleA
    norm_num only [pow_zero,mul_one]
    have hh := (div_le_iff₀ (by positivity : (0:ℝ)<2^(sourceDimension B j))).mpr
      (show 1+sourceEpsilon B D ≤ (1+sourceEpsilon B D)*2^(sourceDimension B j) from
        le_mul_of_one_le_right (by linarith only [he]) hp)
    linarith only [hh]

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

theorem sourceArithmeticCount_step (C N : ℝ) (b : ℕ) (ε : ℝ) (ell k j : ℕ) :
    sourceArithmeticCount C N b ε ell k (j+1)=
      ⌈C*sourceArithmeticCount C N b ε ell k j*sourceArithmeticP C N b ε ell k j⌉₊ := rfl

theorem sourceArithmetic_inner_trials (C N : ℝ) (b : ℕ) (ε : ℝ) (ell k j : ℕ)
    (hj : j+1≠b) : sourceArithmeticTrials C N b ε ell k j=
      sourceLocalTrials (sourceArithmeticP C N b ε ell k j) (sourceArithmeticCount C N b ε ell k j) := by
  simp only [sourceArithmeticTrials,sourceArithmeticP,sourceArithmeticCount,sourceArithmeticStages,ite_eq_right hj]

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

/-- The nonroot even trial count is between one and two times its unrounded
 quotient once the quotient is at least two. -/
theorem sourceLocalTrials_bounds (P h : ℕ) (hlarge : (200:ℝ)*(2*h+1) ≤ P) :
    (P:ℝ)/(100*(2*h+1)) ≤ (sourceLocalTrials P h:ℝ) ∧
      (sourceLocalTrials P h:ℝ) ≤ (P:ℝ)/(50*(2*h+1)) := by
  have hd : 0 < (100:ℝ)*(2*h+1) := by positivity
  have hx : (2:ℝ) ≤ (P:ℝ)/(100*(2*h+1)) := (le_div_iff₀ hd).mpr (by linarith only [hlarge])
  have he : (sourceLocalTrials P h:ℝ)=2*(⌊(P:ℝ)/(100*(2*h+1))⌋₊:ℝ) := by
    unfold sourceLocalTrials
    rw [show (100:ℝ)*(2*h+1)=((100*(2*h+1):ℕ):ℝ) by push_cast; ring,Nat.floor_div_eq_div]
    norm_cast
  rw [he]
  have hlo := Nat.lt_floor_add_one ((P:ℝ)/(100*(2*h+1)))
  have hhi := Nat.floor_le (div_nonneg (Nat.cast_nonneg P) hd.le)
  constructor
  · linarith only [hx,hlo]
  · have heq : (P:ℝ)/(50*(2*h+1))=2*((P:ℝ)/(100*(2*h+1))) := by field_simp; ring
    rw [heq]
    linarith only [hhi]

theorem source_floor_length_bounds {X : ℝ} {S : ℕ} (hS : 0 < S) (hX : 2*(S:ℝ) ≤ X) :
    X/2 ≤ ((S*⌊X/(S:ℝ)⌋₊:ℕ):ℝ) ∧ ((S*⌊X/(S:ℝ)⌋₊:ℕ):ℝ) ≤ X := by
  have hs : (0:ℝ) < S := by exact_mod_cast hS
  have hlo := Nat.lt_floor_add_one (X/(S:ℝ))
  have hhi := Nat.floor_le (div_nonneg (show 0 ≤ X by linarith only [hX,hs]) hs.le)
  have hh := mul_lt_mul_of_pos_left hlo hs
  have hh' := mul_le_mul_of_nonneg_left hhi hs.le
  rw [mul_add,mul_div_cancel₀ _ hs.ne'] at hh
  rw [mul_div_cancel₀ _ hs.ne'] at hh'
  push_cast
  constructor <;> nlinarith only [hX,hh,hh']

theorem source_root_length_bounds {N : ℝ} {S T h : ℕ} (hS : 0 < S)
    (hT : T ≤ ⌊N/(S:ℝ)⌋₊) (hN : (2*h+2:ℝ)*S ≤ N/2) :
    N/2 ≤ (S:ℝ)*(sourceRootTrials N S T h*(2*h+1)+T) ∧
      (S:ℝ)*(sourceRootTrials N S T h*(2*h+1)+T) ≤ N := by
  have hs : (0:ℝ)<S := by exact_mod_cast hS
  have hd : 0 < 2*h+1 := by omega
  have hi := Nat.div_mul_le_self (⌊N/(S:ℝ)⌋₊-T) (2*h+1)
  have hj := Nat.lt_mul_div_succ (⌊N/(S:ℝ)⌋₊-T) hd
  rw [Nat.mul_comm (2*h+1)] at hj
  have hp : sourceRootTrials N S T h*(2*h+1)+T ≤ ⌊N/(S:ℝ)⌋₊ := by
    unfold sourceRootTrials
    omega
  have hp' : ⌊N/(S:ℝ)⌋₊ < (sourceRootTrials N S T h+1)*(2*h+1)+T := by
    unfold sourceRootTrials
    omega
  have hN0 : 0 ≤ N := by
    have hh : (0:ℝ) ≤ (2*h+2:ℝ)*S := by positivity
    linarith only [hN,hh]
  have hfloor := Nat.floor_le (div_nonneg hN0 hs.le)
  have hfloor' := Nat.lt_floor_add_one (N/(S:ℝ))
  have hpr : (sourceRootTrials N S T h:ℝ)*(2*h+1)+T ≤ (⌊N/(S:ℝ)⌋₊:ℝ) := by exact_mod_cast hp
  have hpr' : (⌊N/(S:ℝ)⌋₊:ℝ) < (sourceRootTrials N S T h+1:ℝ)*(2*h+1)+T := by exact_mod_cast hp'
  constructor
  · have hf : N/(S:ℝ) < (sourceRootTrials N S T h:ℝ)*(2*h+1)+T+(2*h+2) := by
      nlinarith only [hfloor',hpr']
    have hh := mul_lt_mul_of_pos_left hf hs
    rw [mul_div_cancel₀ _ hs.ne'] at hh
    nlinarith only [hh,hN]
  · have hh := mul_le_mul_of_nonneg_left (hpr.trans hfloor) hs.le
    simpa only [mul_div_cancel₀ _ hs.ne'] using hh

theorem source_ceil_count_bounds {C F : ℝ} {S h P : ℕ} (hC : 2 ≤ C) (hF : 1 ≤ F)
    (hS : 1 ≤ S) (hP : 1 ≤ P) (hlo : S ≤ h) (hhi : (h:ℝ) ≤ F*S) :
    S*P ≤ ⌈C*h*P⌉₊ ∧ (⌈C*h*P⌉₊:ℝ) ≤ C^2*F*(S*P) := by
  have hs : (1:ℝ) ≤ S := by exact_mod_cast hS
  have hp : (1:ℝ) ≤ P := by exact_mod_cast hP
  have hh : (S:ℝ) ≤ h := by exact_mod_cast hlo
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ C*(h:ℝ)*P by positivity)
  constructor
  · have hbound : (S:ℝ)*P ≤ C*h*P := by
      have hh' := mul_le_mul_of_nonneg_right hh (by positivity : (0:ℝ) ≤ P)
      have hc := mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ C by linarith) (show 0 ≤ (h:ℝ)*P by positivity)
      nlinarith only [hh',hc]
    exact_mod_cast hbound.trans (Nat.le_ceil (C*(h:ℝ)*P))
  · have hmul := mul_le_mul_of_nonneg_left hhi (show 0 ≤ C*(P:ℝ) by positivity)
    have hbase : (1:ℝ) ≤ F*(S*P) := one_le_mul_of_one_le_of_one_le hF (one_le_mul_of_one_le_of_one_le hs hp)
    have hgain : 1 ≤ C*(C-1) := by nlinarith only [hC]
    have hgap := mul_le_mul hgain hbase (by norm_num) (by linarith only [hgain])
    nlinarith only [hceil,hmul,hgap]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem source_scale_target_step {N ε : ℝ} (b j : ℕ) (hN : 0 < N) :
    N^(scaleA b (j+1) ε)=(N^(scaleA b j ε))^2*N^ε := by
  rw [←Real.rpow_natCast,←Real.rpow_mul hN.le,←Real.rpow_add hN]
  congr 1
  have hh := scaleA_step b j ε
  norm_num only [Nat.cast_ofNat]
  linarith only [hh]

theorem sourceWindowSize_le_previous {N ε : ℝ} {b j : ℕ}
    (hN : 1 ≤ N) (he : 0 ≤ ε) :
    (sourceWindowSize N b ε j:ℝ) ≤ N^(scaleA b j ε) := by
  have hf := Nat.floor_le (show 0 ≤ N^(scaleKappa b (j+1) ε)/4 by positivity)
  have hk : scaleKappa b (j+1) ε ≤ scaleA b j ε := by
    unfold scaleKappa
    simp only [Nat.add_sub_cancel]
    have hh : (1:ℝ) ≤ 2^(j+1) := one_le_pow₀ (by norm_num)
    nlinarith only [mul_nonneg (sub_nonneg.mpr hh) he]
  apply le_trans _ (Real.rpow_le_rpow_of_exponent_le hN hk)
  unfold sourceWindowSize
  push_cast
  linarith only [hf]

/-- The root's subtraction and rounding margins follow from the one
 subpower comparison N^epsilon >= 8F. -/
theorem source_root_margins {N X u F : ℝ} {S h T : ℕ}
    (hS : 1 ≤ S) (hX : (S:ℝ) ≤ X) (hF : 1 ≤ F) (hu : 8*F ≤ u)
    (hh : (h:ℝ) ≤ F*S) (hT : (T:ℝ) ≤ X) (hrel : X^2*u=N) :
    T ≤ ⌊N/(S:ℝ)⌋₊ ∧ (2*(h:ℝ)+2)*S ≤ N/2 := by
  have hs : (1:ℝ) ≤ S := by exact_mod_cast hS
  have hx : 1 ≤ X := hs.trans hX
  have hx0 : 0 ≤ X := by linarith only [hx]
  have hs0 : (0:ℝ) < S := by linarith only [hs]
  have hfs : 1 ≤ F*S := by nlinarith only [hF,hs]
  have hsX : (S:ℝ)^2 ≤ X^2 := sq_le_sq₀ hs0.le hx0 |>.mpr hX
  have h8 : 8*F*X^2 ≤ N := by nlinarith only [mul_le_mul_of_nonneg_right hu (sq_nonneg X),hrel]
  constructor
  · apply Nat.le_floor
    apply (le_div_iff₀ hs0).mpr
    have htX := mul_le_mul hT hX hs0.le hx0
    nlinarith only [htX,h8,mul_le_mul_of_nonneg_right hF (sq_nonneg X)]
  · have hhS := mul_le_mul_of_nonneg_right hh hs0.le
    have hS2 := mul_le_mul_of_nonneg_right hfs hs0.le
    have hFsq := mul_le_mul_of_nonneg_left hsX (by linarith only [hF] : 0 ≤ F)
    nlinarith only [hhS,hS2,hFsq,h8]

theorem source_arithmetic_inner_copies (C N : ℝ) (b : ℕ) (ε : ℝ) (ell k j : ℕ)
    (hj : j+1≠b) : sourceArithmeticP C N b ε ell k j=
      ⌊N^(scaleA b (j+1) ε)/(sourceArithmeticLength C N b ε ell k j:ℝ)⌋₊ := by
  simp only [sourceArithmeticP,sourceArithmeticLength,sourceArithmeticStages,ite_eq_right hj]

theorem source_arithmetic_root_copies (C N : ℝ) (b : ℕ) (ε : ℝ) (ell k j : ℕ)
    (hj : j+1=b) : sourceArithmeticP C N b ε ell k j=
      sourceRootTrials N (sourceArithmeticLength C N b ε ell k j) (sourceWindowSize N b ε j)
        (sourceArithmeticCount C N b ε ell k j)*
          (2*sourceArithmeticCount C N b ε ell k j+1)+sourceWindowSize N b ε j := by
  simp only [sourceArithmeticP,sourceArithmeticLength,sourceArithmeticCount,sourceArithmeticStages,ite_eq_left hj]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- All nested lengths and overlap counts for the literal floors/ceilings.
 Only the scalar subpower margin is needed for every rounding step. -/
theorem source_arithmetic_lengths {C N F ε : ℝ} {b ell k : ℕ}
    (hC : 2 ≤ C) (hN : 1 ≤ N) (hF : 1 ≤ F) (he : 0 ≤ ε)
    (ha : ∀j ≤ b,0 ≤ scaleA b j ε)
    (hsmall : 8*C^(2*b)*F ≤ N^ε)
    (hell : N^(scaleA b 0 ε)/2 ≤ (ell:ℝ)) (hell' : (ell:ℝ) ≤ N^(scaleA b 0 ε))
    (hk : ell ≤ k) (hk' : (k:ℝ) ≤ F*ell) :
    ∀j ≤ b,
      N^(scaleA b j ε)/2 ≤ (sourceArithmeticLength C N b ε ell k j:ℝ) ∧
      (sourceArithmeticLength C N b ε ell k j:ℝ) ≤ N^(scaleA b j ε) ∧
      sourceArithmeticLength C N b ε ell k j ≤ sourceArithmeticCount C N b ε ell k j ∧
      (sourceArithmeticCount C N b ε ell k j:ℝ) ≤
        C^(2*j)*F*sourceArithmeticLength C N b ε ell k j := by
  have hN0 : 0 < N := by linarith only [hN]
  have hC1 : 1 ≤ C := by linarith only [hC]
  intro j
  induction j with
  | zero =>
    intro _
    simpa only [sourceArithmeticLength,sourceArithmeticCount,sourceArithmeticStages,
      Nat.mul_zero,pow_zero,one_mul] using And.intro hell (And.intro hell' (And.intro hk hk'))
  | succ j ih =>
    intro hj
    obtain ⟨hlo,hhi,hcount,hcount'⟩ := ih (by omega)
    let S := sourceArithmeticLength C N b ε ell k j
    let H := sourceArithmeticCount C N b ε ell k j
    let P := sourceArithmeticP C N b ε ell k j
    let Fj := C^(2*j)*F
    have hFj : 1 ≤ Fj := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC1) hF
    have hS0 : (0:ℝ)<S := lt_of_lt_of_le (by positivity) hlo
    have hS : 1 ≤ S := by exact_mod_cast (show 0 < S from Nat.cast_pos.mp hS0)
    have hfactor : Fj ≤ C^(2*b)*F := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hC1 (by omega)) (by linarith only [hF])
    have hu : 8*Fj ≤ N^ε := (mul_le_mul_of_nonneg_left hfactor (by norm_num)).trans (by simpa only [mul_assoc] using hsmall)
    have hx : 1 ≤ N^(scaleA b j ε) := Real.one_le_rpow hN (ha j (by omega))
    have hlength : N^(scaleA b (j+1) ε)/2 ≤ ((S*P:ℕ):ℝ) ∧
        ((S*P:ℕ):ℝ) ≤ N^(scaleA b (j+1) ε) := by
      by_cases hr : j+1=b
      · have hrel : (N^(scaleA b j ε))^2*N^ε=N := by
          rw [←source_scale_target_step b j hN0,hr,scaleA_top,Real.rpow_one]
        have hmargin := source_root_margins hS hhi hFj hu hcount'
          (sourceWindowSize_le_previous (b:=b) (j:=j) hN he) hrel
        have hlen := source_root_length_bounds (Nat.pos_of_ne_zero (by omega : S≠0)) hmargin.1 hmargin.2
        have hp : P=sourceRootTrials N S (sourceWindowSize N b ε j) H*(2*H+1)+sourceWindowSize N b ε j :=
          source_arithmetic_root_copies C N b ε ell k j hr
        rw [hp,hr,scaleA_top,Real.rpow_one]
        simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] using hlen
      · have hstep := source_scale_target_step (ε:=ε) b j hN0
        have hX : 2*(S:ℝ) ≤ N^(scaleA b (j+1) ε) := by
          rw [hstep]
          have hu' : 2 ≤ N^ε := by linarith only [hu,hFj]
          have hxx : N^(scaleA b j ε) ≤ (N^(scaleA b j ε))^2 := by nlinarith only [hx]
          nlinarith only [hhi,hxx,mul_le_mul_of_nonneg_left hu' (sq_nonneg (N^(scaleA b j ε)))]
        have hp : P=⌊N^(scaleA b (j+1) ε)/(S:ℝ)⌋₊ :=
          source_arithmetic_inner_copies C N b ε ell k j hr
        rw [hp]
        exact source_floor_length_bounds (by omega) hX
    have hP : 1 ≤ P := by
      have hp : (0:ℝ)<(S*P:ℕ) := lt_of_lt_of_le (by positivity) hlength.1
      have hp' : 0<S*P := Nat.cast_pos.mp hp
      by_contra hp0
      have he : P=0 := by omega
      simp only [he,Nat.mul_zero,lt_self_iff_false] at hp'
    have hceil := source_ceil_count_bounds hC hFj hS hP hcount hcount'
    rw [sourceArithmeticLength_step,sourceArithmeticCount_step]
    refine ⟨hlength.1,hlength.2,hceil.1,?_⟩
    have heq : C^2*Fj=C^(2*(j+1))*F := by
      dsimp [Fj]
      rw [show 2*(j+1)=2+2*j by omega,pow_add]
      ring
    simpa only [←Nat.cast_mul,heq] using hceil.2

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem source_copies_bounds {X u : ℝ} {S P : ℕ} (hX : 0 < X)
    (hSlo : X/2 ≤ S) (hShi : (S:ℝ) ≤ X)
    (hlo : X^2*u/2 ≤ ((S*P:ℕ):ℝ)) (hhi : ((S*P:ℕ):ℝ) ≤ X^2*u) :
    X*u/2 ≤ (P:ℝ) ∧ (P:ℝ) ≤ 2*X*u := by
  have hp := (Nat.cast_nonneg P : (0:ℝ) ≤ P)
  have hlo' := mul_le_mul_of_nonneg_right hShi hp
  have hhi' := mul_le_mul_of_nonneg_right hSlo hp
  push_cast at hlo hhi
  constructor <;> nlinarith only [hX,hlo,hhi,hlo',hhi']

theorem source_inner_trials_scale {X u F : ℝ} {S P h : ℕ}
    (hX : 1 ≤ X) (hF : 1 ≤ F) (hu : 1200*F ≤ u)
    (hSlo : X/2 ≤ S) (hShi : (S:ℝ) ≤ X) (hhlo : S ≤ h) (hhhi : (h:ℝ) ≤ F*S)
    (hPlo : X*u/2 ≤ (P:ℝ)) (hPhi : (P:ℝ) ≤ 2*X*u) :
    u/(600*F) ≤ (sourceLocalTrials P h:ℝ) ∧ (sourceLocalTrials P h:ℝ) ≤ 2*u := by
  have hx : 0<X := by linarith only [hX]
  have hf : 0<F := by linarith only [hF]
  have hfx : 1 ≤ F*X := one_le_mul_of_one_le_of_one_le hF hX
  have hhu : (h:ℝ) ≤ F*X := hhhi.trans (mul_le_mul_of_nonneg_left hShi hf.le)
  have hhl : X ≤ 2*(h:ℝ)+1 := by exact_mod_cast (show X ≤ 2*(h:ℝ)+1 by
    have hh : (S:ℝ) ≤ h := by exact_mod_cast hhlo
    linarith only [hh,hSlo])
  have hhh : 2*(h:ℝ)+1 ≤ 3*F*X := by linarith only [hhu,hfx]
  have hlarge : (200:ℝ)*(2*h+1) ≤ P := by
    have hum := mul_le_mul_of_nonneg_left hu hx.le
    nlinarith only [hhh,hPlo,hum]
  obtain ⟨hlo,hhi⟩ := sourceLocalTrials_bounds P h hlarge
  have hd : 0 < (100:ℝ)*(2*h+1) := by positivity
  constructor
  · apply le_trans _ hlo
    apply (div_le_div_iff₀ (by positivity : (0:ℝ)<600*F) hd).mpr
    have hum := mul_le_mul_of_nonneg_left hhh (by linarith only [hu,hF] : 0 ≤ u)
    have hpm := mul_le_mul_of_nonneg_left hPlo hf.le
    nlinarith only [hum,hpm]
  · apply hhi.trans
    apply (div_le_iff₀ (by positivity : (0:ℝ)<50*(2*h+1))).mpr
    have hmm := mul_le_mul_of_nonneg_left hhl (by linarith only [hu,hF] : 0 ≤ u)
    nlinarith only [hPhi,hmm]

theorem source_root_trials_scale {X u F : ℝ} {S P h J T : ℕ}
    (hX : 1 ≤ X) (hF : 1 ≤ F) (hu : 1200*F ≤ u)
    (hSlo : X/2 ≤ S) (hShi : (S:ℝ) ≤ X) (hhlo : S ≤ h) (hhhi : (h:ℝ) ≤ F*S)
    (hPlo : X*u/2 ≤ (P:ℝ)) (hPhi : (P:ℝ) ≤ 2*X*u)
    (hT : (T:ℝ) ≤ X) (hP : P=J*(2*h+1)+T) :
    u/(600*F) ≤ (J:ℝ) ∧ (J:ℝ) ≤ 2*u := by
  have hx : 0<X := by linarith only [hX]
  have hf : 0<F := by linarith only [hF]
  have hfx : 1 ≤ F*X := one_le_mul_of_one_le_of_one_le hF hX
  have hhu : (h:ℝ) ≤ F*X := hhhi.trans (mul_le_mul_of_nonneg_left hShi hf.le)
  have hhl : X ≤ 2*(h:ℝ)+1 := by
    have hh : (S:ℝ) ≤ h := by exact_mod_cast hhlo
    linarith only [hh,hSlo]
  have hhh : 2*(h:ℝ)+1 ≤ 3*F*X := by linarith only [hhu,hfx]
  have hp : (P:ℝ)=(J:ℝ)*(2*h+1)+T := by exact_mod_cast hP
  have hj : (0:ℝ) ≤ J := Nat.cast_nonneg _
  have hupper := mul_le_mul_of_nonneg_left hhl hj
  have hlower := mul_le_mul_of_nonneg_left hhh hj
  constructor
  · apply (div_le_iff₀ (by positivity : (0:ℝ)<600*F)).mpr
    have hu' : 4 ≤ u := by linarith only [hu,hF]
    nlinarith only [hp,hT,hPlo,hlower,mul_le_mul_of_nonneg_left hu' hx.le,hx]
  · nlinarith only [hupper,hp,hPhi,(Nat.cast_nonneg T : (0:ℝ) ≤ T),hx]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

theorem sourceOverlapConstant_ge_two {q : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ)) :
    2 ≤ sourceOverlapConstant q := by
  have hC := sourceOverlapConstant_pos hq.1
  have hω := initialOverlapLower_lt_eighth hq.1
  have hlarge := sourceOverlapConstant_large hq
  nlinarith only [hC,hω,hlarge]

end TraceReconstruction


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

theorem scaleA_mono_index (b j k : ℕ) (ε : ℝ) (he : 0 ≤ ε) (hjk : j ≤ k) :
    scaleA b j ε ≤ scaleA b k ε := by
  unfold scaleA
  exact sub_le_sub_right (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hjk) (by linarith only [he]))
      (by positivity)) _

theorem sourceKappa_three_epsilon (B D b j : ℕ) (hb : b ≤ B) (_hj : 1 ≤ j) (hj' : j ≤ b) :
    3*sourceEpsilon B D ≤ scaleKappa b j (sourceEpsilon B D) := by
  let ε := sourceEpsilon B D
  let X := (2:ℝ)^B
  have he : 0 < ε := sourceEpsilon_pos _ _
  have hx : 1 ≤ X := one_le_pow₀ (by norm_num)
  have hsmall := sourceEpsilon_power_small B D (2*B+4) (by omega)
  have hsmall' : 16*X^2*ε ≤ 1 := by
    rw [show 2*B+4=B*2+4 by omega,pow_add,pow_mul] at hsmall
    norm_num only [show (2:ℝ)^4=16 by norm_num] at hsmall
    dsimp [X,ε]
    nlinarith only [hsmall]
  have hgeom := scaleA_zero_lower b B ε hb he.le
  have hmono := scaleA_mono_index b 0 (j-1) ε he.le (Nat.zero_le _)
  have hp : (2:ℝ)^j ≤ X := pow_le_pow_right₀ (by norm_num) (hj'.trans hb)
  have hprod : (3*X+4)*X*ε ≤ 1 := by
    have hxx : 0 ≤ X*(X-1) := mul_nonneg (by linarith only [hx]) (by linarith only [hx])
    have hcmp : (3*X+4)*X ≤ 16*X^2 := by nlinarith only [hxx,sq_nonneg X]
    exact (mul_le_mul_of_nonneg_right hcmp he.le).trans hsmall'
  have hq : (3*X+4)*ε ≤ 1/X := (le_div_iff₀ (by linarith only [hx])).mpr (by nlinarith only [hprod])
  have hzero : 1/X-ε ≤ scaleA b 0 ε := by
    have hh : (1/X)*(1-(X-1)*ε)=1/X-ε+ε/X := by field_simp; ring
    dsimp [X] at hh
    rw [hh] at hgeom
    exact (le_add_of_nonneg_right (div_nonneg he.le (by positivity))).trans hgeom
  have hpk := mul_le_mul_of_nonneg_right hp he.le
  unfold scaleKappa
  change 3*ε ≤ scaleA b (j-1) ε-3*(2^j-1)*ε
  nlinarith only [hzero,hmono,hq,hpk,he]

theorem sourceA_nonneg (B D b j : ℕ) (hb : b ≤ B) (hb0 : 1 ≤ b) :
    0 ≤ scaleA b j (sourceEpsilon B D) := by
  have h := sourceKappa_three_epsilon B D b 1 hb (by omega) hb0
  unfold scaleKappa at h
  norm_num only [Nat.sub_self,pow_one] at h
  have hm := scaleA_mono_index b 0 j (sourceEpsilon B D) (sourceEpsilon_pos B D).le (Nat.zero_le _)
  linarith only [h,hm,sourceEpsilon_pos B D]

end TraceReconstruction


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Exact layout inequalities for the literal recursive integer construction.
 The hypotheses are just two scalar subpower margins and the exact scale
 identities, not any probabilistic producer or new overlap premise. -/
theorem source_arithmetic_geometry {C N F ε : ℝ} {s b ell k : ℕ}
    (hC : 2 ≤ C) (hN : 1 ≤ N) (hF : 1 ≤ F) (he : 0 ≤ ε)
    (ha : ∀j ≤ b,0 ≤ scaleA b j ε) (hκ : ∀j<b,3*ε ≤ scaleKappa b (j+1) ε)
    (hsmall : 1200*C^(2*b)*F ≤ N^ε) (hmotif : 48*((2^s:ℕ):ℝ) ≤ N^ε)
    (hell : N^(scaleA b 0 ε)/2 ≤ (ell:ℝ)) (hell' : (ell:ℝ) ≤ N^(scaleA b 0 ε))
    (hk : ell ≤ k) (hk' : (k:ℝ) ≤ F*ell) :
    SourceArithmeticBounds C N F ε s b ell k := by
  let G := C^(2*b)*F
  let u := N^ε
  have hC1 : 1 ≤ C := by linarith only [hC]
  have hN0 : 0 < N := by linarith only [hN]
  have hG : 1 ≤ G := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC1) hF
  have hG0 : 0 < G := by linarith only [hG]
  have hu : 1200*G ≤ u := by simpa only [G,u,mul_assoc] using hsmall
  have hu8 : 8 ≤ u := by linarith only [hu,hG]
  have H := source_arithmetic_lengths hC hN hF he ha
    (show 8*C^(2*b)*F ≤ N^ε by
      have hh : 8*G ≤ u := by linarith only [hu,hG]
      simpa only [G,u,mul_assoc] using hh) hell hell' hk hk'
  have hcopies (j : ℕ) (hj : j<b) :
      N^(scaleA b j ε)*u/2 ≤ (sourceArithmeticP C N b ε ell k j:ℝ) ∧
      (sourceArithmeticP C N b ε ell k j:ℝ) ≤ 2*N^(scaleA b j ε)*u := by
    have hlen := H j (by omega)
    have hnext := H (j+1) (by omega)
    rw [source_scale_target_step b j hN0,sourceArithmeticLength_step] at hnext
    exact source_copies_bounds (Real.rpow_pos_of_pos hN0 _) hlen.1 hlen.2.1 hnext.1 hnext.2.1
  have htrials (j : ℕ) (hj : j<b) :
      u/(600*G) ≤ (sourceArithmeticTrials C N b ε ell k j:ℝ) ∧
      (sourceArithmeticTrials C N b ε ell k j:ℝ) ≤ 2*u := by
    have hlen := H j (by omega)
    have hcp := hcopies j hj
    have hX : 1 ≤ N^(scaleA b j ε) := Real.one_le_rpow hN (ha j (by omega))
    have hcount : (sourceArithmeticCount C N b ε ell k j:ℝ) ≤
        G*sourceArithmeticLength C N b ε ell k j := by
      apply hlen.2.2.2.trans
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC1 (by omega)) (by linarith only [hF])
    by_cases hjroot : j+1=b
    · have hp : sourceArithmeticP C N b ε ell k j=
          sourceArithmeticTrials C N b ε ell k j*(2*sourceArithmeticCount C N b ε ell k j+1)+
            sourceWindowSize N b ε j := by
        simp only [sourceArithmeticP,sourceArithmeticTrials,sourceArithmeticCount,sourceArithmeticStages,ite_eq_left hjroot]
      exact source_root_trials_scale hX hG hu hlen.1 hlen.2.1 hlen.2.2.1 hcount hcp.1 hcp.2
        (sourceWindowSize_le_previous hN he) hp
    · rw [sourceArithmetic_inner_trials C N b ε ell k j hjroot]
      exact source_inner_trials_scale hX hG hu hlen.1 hlen.2.1 hlen.2.2.1 hcount hcp.1 hcp.2
  refine ⟨fun j hj => ⟨(H j hj).1,(H j hj).2.1⟩,fun j hj => (H j hj).2.2,hcopies,htrials,?_⟩
  intro j hj
  rw [sourceBlockWindows,ite_eq_left hj]
  have hp := hcopies j hj
  have ht := htrials j hj
  have hu3 : u^3 ≤ N^(scaleKappa b (j+1) ε) := by
    dsimp [u]
    rw [←Real.rpow_natCast,←Real.rpow_mul hN0.le]
    norm_num only [Nat.cast_ofNat]
    apply Real.rpow_le_rpow_of_exponent_le hN
    linarith only [hκ j hj]
  have hu32 : 64*u ≤ u^3 := by
    have hu_sq : 64 ≤ u^2 := by nlinarith only [hu8,sq_nonneg (u-8)]
    nlinarith only [mul_le_mul_of_nonneg_right hu_sq (by linarith only [hu8] : 0 ≤ u)]
  have hw := sourceWindowSize_bounds (show 8 ≤ N^(scaleKappa b (j+1) ε) by linarith only [hu32,hu8,hu3])
  have hwbig : u^3/2 ≤ (sourceWindowSize N b ε j:ℝ) := le_trans (by linarith only [hu3] : u^3/2 ≤ N^(scaleKappa b (j+1) ε)/2) hw.1
  have hwp := sourceWindowSize_le_previous (b:=b) (j:=j) hN he
  have hX : 0 ≤ N^(scaleA b j ε) := (Real.rpow_pos_of_pos hN0 _).le
  have hambient : (2:ℝ)*(sourceWindowSize N b ε j:ℝ) ≤ sourceArithmeticP C N b ε ell k j := by
    have hh := mul_le_mul_of_nonneg_right hu8 hX
    nlinarith only [hp.1,hwp,hh]
  have h24 : (24:ℝ) ≤ sourceWindowSize N b ε j := by linarith only [hwbig,hu32,hu8]
  have hmot : (24:ℝ)*((2^s:ℕ):ℝ) ≤ sourceWindowSize N b ε j := by
    have hu' : 48*((2^s:ℕ):ℝ) ≤ u := hmotif
    linarith only [hwbig,hu32,hu']
  have hroot : (4:ℝ)*((sourceArithmeticTrials C N b ε ell k j:ℝ)+1) ≤ sourceWindowSize N b ε j := by
    linarith only [hwbig,hu32,hu8,ht.2]
  exact ⟨by exact_mod_cast h24,by exact_mod_cast hmot,by exact_mod_cast hambient,by exact_mod_cast hroot⟩

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

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

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

end TraceReconstruction


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem sourceLeafCount_positive {T : ℕ → ℕ} {b : ℕ} (hT : ∀j<b,1 ≤ T j) :
    1 ≤ SourceLeafCount T b := by
  induction b with
  | zero => change 1 ≤ Fintype.card (Fin 1); simp
  | succ b ih =>
    rw [sourceLeafCount_succ]
    exact one_le_mul_of_one_le_of_one_le (hT b (by omega)) (ih (fun j hj=>hT j (by omega)))

theorem sourceFitTail_simple {T n : ℕ → ℕ} {b : ℕ} {v : ℝ}
    (hT : ∀j<b,1 ≤ T j)
    (hv : ∀j,j+1<b → v ≤ 2*((T j:ℝ)/8)^2/(((T (j+1):ℝ)+1)*(n j:ℝ))) :
    sourceFitTail T n b ≤ 2*(b:ℝ)*(SourceLeafCount T b:ℝ)*Real.exp (-v) := by
  induction b using Nat.twoStepInduction with
  | zero => simp [sourceFitTail]
  | one => simp only [sourceFitTail]; positivity
  | more b _ ih =>
    have hi := ih (fun j hj=>hT j (by omega)) (fun j hj=>hv j (by omega))
    have hleaf : (1:ℝ) ≤ SourceLeafCount T (b+1) := by
      exact_mod_cast sourceLeafCount_positive (fun j hj=>hT j (show j<b+2 by omega))
    have he := Real.exp_le_exp.mpr (neg_le_neg (hv b (by omega)))
    rw [sourceFitTail,sourceLeafCount_succ,Nat.cast_mul]
    have hmul := mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ)≤2)) hi)
      (show 0 ≤ (T (b+1):ℝ) by positivity)
    have hlast := mul_le_mul_of_nonneg_left hleaf (show 0 ≤ (T (b+1):ℝ)*Real.exp (-v) by positivity)
    push_cast at hmul ⊢
    have hex : -(2*((T b:ℝ)/8)^2/(((T (b+1):ℝ)+1)*(n b:ℝ))) =
        -2*((T b:ℝ)/8)^2/(((T (b+1):ℝ)+1)*(n b:ℝ)) := by ring
    rw [hex] at hmul
    nlinarith only [hmul,hlast]

theorem windowCollection_card_bound {T : ℕ → ℕ} {b : ℕ} (hT : ∀j<b,1 ≤ T j) :
    Fintype.card (WindowCollection T b) ≤ 2*b*SourceLeafCount T b := by
  induction b with
  | zero => change Fintype.card PEmpty ≤ _; simp
  | succ b ih =>
    have hi := ih (fun j hj=>hT j (by omega))
    have hp := sourceLeafCount_positive (b:=b) (fun j hj=>hT j (show j<b+1 by omega))
    have ht := hT b (by omega)
    have hc : Fintype.card (WindowCollection T (b+1))=2+T b*Fintype.card (WindowCollection T b) := by
      change Fintype.card (Bool ⊕ (Fin (T b) × WindowCollection T b))=_
      simp only [Fintype.card_sum,Fintype.card_bool,Fintype.card_prod,Fintype.card_fin]
    rw [hc,sourceLeafCount_succ]
    have hm := Nat.mul_le_mul_left (T b) hi
    have hh : 1 ≤ T b*SourceLeafCount T b := one_le_mul_of_one_le_of_one_le ht hp
    nlinarith only [hm,hh]

theorem collectionCount_lower {T n g : ℕ→ℕ} {b : ℕ} {M : ℝ}
    (hn : ∀j<b,M ≤ (n j:ℝ)) (hg : ∀j<b,g j=0 ∨ M ≤ (g j:ℝ))
    (v : WindowCollection T b) :
    collectionCount T n g b v=0 ∨ M ≤ (collectionCount T n g b v:ℝ) := by
  induction b with
  | zero => exact PEmpty.elim v
  | succ b ih =>
    rcases v with a | ⟨u,v⟩
    · cases a
      · exact Or.inr (hn b (by omega))
      · exact hg b (by omega)
    · exact ih (fun j hj=>hn j (by omega)) (fun j hj=>hg j (by omega)) v

theorem sourceEffectiveHiddenTail_simple {T n : ℕ→ℕ} {b : ℕ} {M ω : ℝ}
    (hT : ∀j<b,1 ≤ T j) (hn : ∀j<b,M ≤ (n j:ℝ))
    (hg : ∀j<b,sourceScheduledTrials T n j=0 ∨ M ≤ (sourceScheduledTrials T n j:ℝ)) :
    sourceEffectiveHiddenTail T n b ω ≤ 2*(b:ℝ)*(SourceLeafCount T b:ℝ)*Real.exp (-M*ω^4/16) := by
  unfold sourceEffectiveHiddenTail
  have hh (v : WindowCollection T b) :
      (if collectionCount T n (sourceScheduledTrials T n) b v=0 then 0 else
        Real.exp (-(collectionCount T n (sourceScheduledTrials T n) b v:ℝ)*ω^4/16)) ≤ Real.exp (-M*ω^4/16) := by
    rcases collectionCount_lower hn hg v with hz | hm
    · rw [ite_eq_left hz]; positivity
    · split_ifs
      · positivity
      · apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_right hm (pow_nonneg (sq_nonneg ω) 2)
        nlinarith only [hh]
  apply (Finset.sum_le_sum (fun v _=>hh v)).trans
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact_mod_cast windowCollection_card_bound hT

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The literal centering fluctuation has the source epsilon exponent.
 This does not treat nested window starts as independent. -/
theorem SourceArithmeticBounds.fit_exponent {C N F ε : ℝ} {s b ell k j : ℕ}
    (H : SourceArithmeticBounds C N F ε s b ell k) (hC : 0<C) (hF : 0<F) (hN : 1 ≤ N) (he : 0 ≤ ε)
    (hκ : ∀v<b,3*ε ≤ scaleKappa b (v+1) ε) (hj : j+1<b) :
    N^ε/512 ≤ 2*((sourceBlockWindows N b ε j:ℝ)/8)^2 /
      (((sourceBlockWindows N b ε (j+1):ℝ)+1)*(sourceArithmeticTrials C N b ε ell k j:ℝ)) := by
  have hN0 : 0<N := by linarith only [hN]
  have hpresent := (H.windows j (by omega)).1
  have hwin : 24 ≤ sourceWindowSize N b ε j := by
    simpa only [sourceBlockWindows,ite_eq_left (by omega : j<b)] using hpresent
  have hlarge : 8 ≤ N^(scaleKappa b (j+1) ε) := by
    have hh : (24:ℝ) ≤ sourceWindowSize N b ε j := by exact_mod_cast hwin
    exact (by norm_num : (8:ℝ)≤24).trans (hh.trans (sourceWindowSize_le N b j ε hN0.le))
  have hl : N^(scaleKappa b (j+1) ε)/2 ≤ (sourceBlockWindows N b ε j:ℝ) := by
    simpa only [sourceBlockWindows,ite_eq_left (by omega : j<b)] using (sourceWindowSize_bounds hlarge).1
  have hu : (sourceBlockWindows N b ε (j+1):ℝ)+1 ≤ 2*N^(scaleKappa b (j+2) ε) := by
    have hh := sourceWindowSize_le N b (j+1) ε hN0.le
    have he' : 0 ≤ scaleKappa b (j+2) ε := by linarith only [hκ (j+1) hj,he]
    have ho := Real.one_le_rpow hN he'
    simpa only [sourceBlockWindows,ite_eq_left hj] using (show (sourceWindowSize N b ε (j+1):ℝ)+1 ≤ 2*N^(scaleKappa b (j+2) ε) by linarith only [hh,ho])
  have htr := (H.trials j (by omega)).2
  have hd : ((sourceBlockWindows N b ε (j+1):ℝ)+1)*sourceArithmeticTrials C N b ε ell k j ≤
      4*N^(scaleKappa b (j+2) ε)*N^ε := by
    have hh := mul_le_mul hu htr (by positivity) (by positivity)
    nlinarith only [hh]
  have htrial : 0 < (sourceArithmeticTrials C N b ε ell k j:ℝ) :=
    (show 0 < N^ε/(600*(C^(2*b)*F)) by positivity).trans_le (H.trials j (by omega)).1
  have hdpos : 0 < ((sourceBlockWindows N b ε (j+1):ℝ)+1)*sourceArithmeticTrials C N b ε ell k j := by positivity
  apply (le_div_iff₀ hdpos).mpr
  have hmul := mul_le_mul_of_nonneg_left hd (show 0 ≤ N^ε/512 by positivity)
  have hsquare := pow_le_pow_left₀ (show 0 ≤ N^(scaleKappa b (j+1) ε)/2 by positivity) hl 2
  have hpow : N^ε*N^(scaleKappa b (j+2) ε)*N^ε=(N^(scaleKappa b (j+1) ε))^2 := by
    rw [←Real.rpow_add hN0,←Real.rpow_add hN0,←Real.rpow_natCast,←Real.rpow_mul hN0.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    have hx := scaleKappa_step b (j+1) ε (by omega)
    linarith only [hx]
  nlinarith only [hmul,hsquare,hpow]

end TraceReconstruction


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

theorem sourceCapEnvelope_pos (B D : ℕ) {q : ℝ} (hq : 0<q) : 0 < sourceCapEnvelope B D q := by
  unfold sourceCapEnvelope
  positivity [sourceOverlapConstant_pos hq,initialOverlapLower_pos q]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem SourceArithmeticBounds.fit_tail {C N F ε : ℝ} {s b ell k : ℕ}
    (H : SourceArithmeticBounds C N F ε s b ell k) (hC : 0<C) (hF : 0<F)
    (hN : 1≤N) (he : 0≤ε) (hκ : ∀v<b,3*ε ≤ scaleKappa b (v+1) ε) :
    sourceFitTail (sourceBlockWindows N b ε) (sourceArithmeticTrials C N b ε ell k) b ≤
      2*(b:ℝ)*N*Real.exp (-(N^ε/512)) := by
  have hN0 : 0<N := by linarith only [hN]
  apply (sourceFitTail_simple (fun j hj=>(by omega : 1≤24).trans (H.windows j hj).1)
    (fun j hj=>H.fit_exponent hC hF hN he hκ hj)).trans
  have hh := mul_le_mul_of_nonneg_left (H.leaf_bound hN0) (show 0≤2*(b:ℝ) by positivity)
  exact mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le

theorem SourceArithmeticBounds.metadata_tail {C N F ε ω : ℝ} {s b ell k : ℕ}
    (H : SourceArithmeticBounds C N F ε s b ell k) (hN : 0<N) :
    sourceEffectiveHiddenTail (sourceBlockWindows N b ε) (sourceArithmeticTrials C N b ε ell k) b ω ≤
      2*(b:ℝ)*N*Real.exp (-(N^ε/(600*(C^(2*b)*F)))*ω^4/16) := by
  apply (sourceEffectiveHiddenTail_simple (fun j hj=>(by omega : 1≤24).trans (H.windows j hj).1)
    (fun j hj=>(H.trials j hj).1) ?_).trans
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (H.leaf_bound hN) (show 0≤2*(b:ℝ) by positivity)) (Real.exp_pos _).le
  · intro j hj
    cases j with
    | zero => exact Or.inl rfl
    | succ j =>
      right
      rw [sourceScheduledTrials,Nat.cast_mul]
      have ht := (H.windows (j+1) hj).1
      have hd : 1 ≤ sourceBlockWindows N b ε (j+1)/4 := by omega
      have hd' : (1:ℝ) ≤ (sourceBlockWindows N b ε (j+1)/4:ℕ) := by exact_mod_cast hd
      exact (H.trials j (by omega)).1.trans
        (le_mul_of_one_le_left (Nat.cast_nonneg _) hd')

/-- Quantitative clipping without any default-limit increase or limiting
 interchange: the power is the finite even moment actually used by the oracle. -/
theorem source_clipping_moment_power (T : ℕ→ℕ) (s b k : ℕ) (N gap L : ℝ)
    (hN : 0<N)
    (hhalf : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b ≤ 1/2)
    (hscale : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b ≤ N^(-gap/2)/8) :
    Real.sqrt (6*(4*sourceCenteredBudget T s b k L)^k) ≤ 3*N^(-gap*(k:ℝ)/4) := by
  let x := ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b
  have hx : 0≤x := by dsimp [x]; positivity
  have hden : 0<1-x := by dsimp [x]; linarith only [hhalf]
  have hc : 4*sourceCenteredBudget T s b k L ≤ N^(-gap/2) := by
    have hh : x/(1-x) ≤ 2*x := by
      apply (div_le_iff₀ hden).mpr
      have hxhalf : x≤1/2 := hhalf
      nlinarith only [mul_le_mul_of_nonneg_left hxhalf hx]
    change 4*(x/(1-x)) ≤ _
    nlinarith only [hh,hscale]
  have hc0 : 0 ≤ 4*sourceCenteredBudget T s b k L :=
    mul_nonneg (by norm_num) (sourceCenteredBudget_nonneg T s b k L (by linarith only [hhalf]))
  have hh := pow_le_pow_left₀ hc0 hc k
  have hr : (N^(-gap/2))^k=(N^(-gap*(k:ℝ)/4))^2 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hN.le,←Real.rpow_natCast,←Real.rpow_mul hN.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  rw [hr] at hh
  apply (Real.sqrt_le_left (by positivity : 0≤3*N^(-gap*(k:ℝ)/4))).mpr
  nlinarith only [hh,sq_nonneg (N^(-gap*(k:ℝ)/4))]

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

theorem sourceHalfMoment_strong (B D i : ℕ) {n : ℝ} (hB : 2≤B) (hn : 1<n) :
    (10^8:ℝ)*2^(10*B)*(totalScoreExponent B D+B+1)*Real.log n ≤
      (sourceHalfMoment B D n i:ℝ)*Real.log (sourceTargetScale B D n i) := by
  have hlog : 0<Real.log (sourceTargetScale B D n i) := by
    rw [sourceTargetScale,Real.log_rpow (by linarith only [hn] : 0<n)]
    exact mul_pos (lt_of_lt_of_le (by positivity) (sourceScaleProduct_lower B D i hB)) (Real.log_pos hn)
  exact (div_le_iff₀ hlog).mp (Nat.le_ceil _)

theorem source_clipping_power_delta (B D i : ℕ) {n gap : ℝ}
    (hB : 2≤B) (hn : 4≤n) (hg : sourceGapFloor B ≤ gap) :
    3*(sourceTargetScale B D n i)^(-gap*(sourceHalfMoment B D n i:ℝ)/4) ≤
      n^(-200*(totalScoreExponent B D+B+1)) := by
  let N := sourceTargetScale B D n i
  let A := totalScoreExponent B D+B+1
  let k := sourceHalfMoment B D n i
  have hn1 : 1<n := by linarith only [hn]
  have hn0 : 0<n := by linarith only [hn]
  have hN : 0<N := Real.rpow_pos_of_pos hn0 _
  have hA : 1≤A := by dsimp [A]; linarith only [(totalScoreExponent_bounds B D hB).1,Nat.cast_nonneg B (α:=ℝ)]
  have hlogN : 0≤Real.log N := by
    dsimp [N]
    rw [sourceTargetScale,Real.log_rpow hn0]
    exact mul_nonneg (lt_of_lt_of_le (by positivity) (sourceScaleProduct_lower B D i hB)).le (Real.log_pos hn1).le
  have hk := sourceHalfMoment_strong B D i hB hn1
  change (10^8:ℝ)*2^(10*B)*A*Real.log n ≤ (k:ℝ)*Real.log N at hk
  have hp : (2:ℝ)^(2*B) ≤ 2^(10*B) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hc : 1000 ≤ sourceGapFloor B/4*((10^8:ℝ)*2^(10*B)) := by
    unfold sourceGapFloor
    calc
      (1000:ℝ) ≤ (10^8*2^(10*B))/(512*2^(2*B)) := by
        apply (le_div_iff₀ (by positivity : (0:ℝ)<512*2^(2*B))).mpr
        nlinarith only [hp,show (0:ℝ) ≤ 2^(2*B) by positivity]
      _ = _ := by field_simp; ring
  have hh := mul_le_mul_of_nonneg_left hk (show 0 ≤ sourceGapFloor B/4 by positivity [sourceGapFloor_pos B])
  have hh' := mul_le_mul_of_nonneg_right hc (show 0≤A*Real.log n by positivity [Real.log_pos hn1])
  have hhg := mul_le_mul_of_nonneg_right hg (show 0≤(k:ℝ)*Real.log N/4 by positivity)
  have hdec : 1000*A*Real.log n ≤ gap*(k:ℝ)/4*Real.log N := by nlinarith only [hh,hh',hhg]
  have h3 : Real.log 3 ≤ A*Real.log n := by
    have hl : Real.log 3 ≤ Real.log n := Real.log_le_log (by norm_num) (by linarith only [hn])
    exact hl.trans (le_mul_of_one_le_left (Real.log_pos hn1).le hA)
  rw [show (3:ℝ)=Real.exp (Real.log 3) by rw [Real.exp_log (by norm_num)],Real.rpow_def_of_pos hN,←Real.exp_add,
    Real.rpow_def_of_pos hn0]
  exact Real.exp_le_exp.mpr (by nlinarith only [hdec,h3,mul_nonneg (by linarith only [hA] : 0≤A) (Real.log_pos hn1).le])

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

end TraceReconstruction

noncomputable section

noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem sourceDimension_bounds (B i : ℕ) (hB : 2≤ B) :
    2≤ sourceDimension B i ∧ sourceDimension B i≤ B := by
  unfold sourceDimension
  split_ifs <;> omega

theorem sourceTargetScale_bounds (B D i : ℕ) {n : ℝ} (hB : 2≤ B) (hn : 1≤ n) :
    1≤ sourceTargetScale B D n i ∧ sourceTargetScale B D n i≤ n := by
  have hp : 0≤ sourceScaleProduct B D i :=
    (show (0:ℝ)≤1/(2*2^(B*D)) by positivity).trans (sourceScaleProduct_lower B D i hB)
  refine ⟨Real.one_le_rpow hn hp,?_⟩
  simpa only [sourceTargetScale,Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn (sourceScaleProduct_le_one B D i hB)

end TraceReconstruction

noncomputable section

noncomputable section
noncomputable section
noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem source_count_envelope (B D i b : ℕ) {q : ℝ}
    (hq : q∈Set.Ioc 0 (1/2:ℝ)) (hi : i≤ D) (hb : b≤ B) :
    (sourceOverlapConstant q)^(2*b)*(sourceOverlapConstant q)^(2*B*i+2) ≤
      (sourceOverlapConstant q)^(2*B*(D+1)+2) := by
  rw [←pow_add]
  apply pow_le_pow_right₀ ((by norm_num : (1:ℝ)≤ 2).trans (sourceOverlapConstant_ge_two hq))
  have hh := Nat.mul_le_mul_left (2*B) hi
  nlinarith only [hh,hb]

theorem source_cap_envelope (B D i b : ℕ) {q : ℝ}
    (hq : q∈Set.Ioc 0 (1/2:ℝ)) (hi : i≤ D) (hb : b≤ B) :
    200*((sourceOverlapConstant q)^(2*b)*(sourceOverlapConstant q)^(2*B*i+2))/initialOverlapLower q ≤
      sourceCapEnvelope B D q := by
  dsimp [sourceCapEnvelope]
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (source_count_envelope B D i b hq hi hb)
    (by norm_num)) (inv_pos.mpr (initialOverlapLower_pos q)).le

theorem source_local_envelope (B D i b : ℕ) {q : ℝ}
    (hq : q∈Set.Ioc 0 (1/2:ℝ)) (hi : i≤ D) (hb : b≤ B) :
    (sourceOverlapConstant q)^(2*b)*(sourceOverlapConstant q)^(2*B*i+2) ≤
      sourceCapEnvelope B D q := by
  have hω := initialOverlapLower_lt_eighth hq.1
  have hω0 := initialOverlapLower_pos q
  have hG : 0 ≤ (sourceOverlapConstant q)^(2*b)*(sourceOverlapConstant q)^(2*B*i+2) := by
    positivity [sourceOverlapConstant_pos hq.1]
  apply le_trans _ (source_cap_envelope B D i b hq hi hb)
  apply (le_div_iff₀ hω0).mpr
  nlinarith only [hω,hG,mul_nonneg hG (show 0 ≤ 200-initialOverlapLower q by linarith only [hω])]

theorem sourceErrorUnit_small {B D : ℕ} {n : ℝ} (hB : 2≤ B) (hn : 4≤ n) :
    4*n^(-200*(totalScoreExponent B D+B+1)) ≤ n^(-100*(totalScoreExponent B D+B+1)) ∧
    4*n^(-200*(totalScoreExponent B D+B+1)) ≤ 1/2 := by
  let A := totalScoreExponent B D+B+1
  have hA : 1≤ A := by dsimp [A]; linarith only [(totalScoreExponent_bounds B D hB).1,Nat.cast_nonneg B (α:=ℝ)]
  have hn0 : 0<n := by linarith only [hn]
  have hn1 : 1≤ n := by linarith only [hn]
  have hpow : 4≤ n^(100*A) := hn.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1 (show 1≤ 100*A by linarith only [hA]))
  have hh := mul_le_mul_of_nonneg_right hpow (Real.rpow_pos_of_pos hn0 (-200*A)).le
  rw [←Real.rpow_add hn0] at hh
  have heq : 100*A+(-200*A)=-100*A := by ring
  rw [heq] at hh
  have hsmall : n^(-100*A) ≤ 1/2 := by
    have hh' := Real.rpow_le_rpow_of_exponent_le hn1 (show -100*A≤ (-1:ℝ) by linarith only [hA])
    rw [Real.rpow_neg_one] at hh'
    exact hh'.trans (by apply (inv_le_comm₀ hn0 (by norm_num)).mpr; norm_num; linarith only [hn])
  exact ⟨hh,hh.trans hsmall⟩

end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

/-- Turning the common uniform exponential bound into the two exact
 scheduled-error terms, including the division by the clipping threshold. -/
theorem source_exponential_error_budget {B D b s ell k : ℕ} {C N F ω f n : ℝ}
    (H : SourceArithmeticBounds C N F (sourceEpsilon B D) s b ell k)
    (hB : 2 ≤ B) (hb : b ≤ B) (hC : 0<C) (hF : 0<F) (hω : 0<ω)
    (hn : 1 ≤ n) (hN : 1 ≤ N) (hNn : N ≤ n)
    (hf512 : 512 ≤ f) (hfmeta : 9600*(C^(2*b)*F)/ω^4 ≤ f)
    (htail : 2*(B:ℝ)*Real.exp (-(N^(sourceEpsilon B D)/f)) ≤ n^(-sourceTailExponent B D)) :
    sourceEffectiveHiddenTail (sourceBlockWindows N b (sourceEpsilon B D))
      (sourceArithmeticTrials C N b (sourceEpsilon B D) ell k) b ω ≤ n^(-200*(totalScoreExponent B D+B+1)) ∧
    sourceFitTail (sourceBlockWindows N b (sourceEpsilon B D))
      (sourceArithmeticTrials C N b (sourceEpsilon B D) ell k) b /
      N^(-20*sourceWorkSize B D) ≤ n^(-200*(totalScoreExponent B D+B+1)) ∧
    sourceFitTail (sourceBlockWindows N b (sourceEpsilon B D))
      (sourceArithmeticTrials C N b (sourceEpsilon B D) ell k) b ≤ n^(-200*(totalScoreExponent B D+B+1)) := by
  let A := totalScoreExponent B D+B+1
  let M := sourceWorkSize B D
  let ε := sourceEpsilon B D
  have hN0 : 0<N := by linarith only [hN]
  have hn0 : 0<n := by linarith only [hn]
  have hf0 : 0<f := by linarith only [hf512]
  have hA : 0 ≤ A := by dsimp [A]; linarith only [(totalScoreExponent_bounds B D hB).1,Nat.cast_nonneg B (α:=ℝ)]
  have hM : 0 ≤ M := (sourceWorkSize_pos B D hB).le
  have hexpfit : Real.exp (-(N^ε/512)) ≤ Real.exp (-(N^ε/f)) := by
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (div_le_div_of_nonneg_left (Real.rpow_pos_of_pos hN0 ε).le (by norm_num) hf512)
  have hexpmeta : Real.exp (-(N^ε/(600*(C^(2*b)*F)))*ω^4/16) ≤ Real.exp (-(N^ε/f)) := by
    have hden : 0<9600*(C^(2*b)*F)/ω^4 := by positivity
    have hh := div_le_div_of_nonneg_left (Real.rpow_pos_of_pos hN0 ε).le hden hfmeta
    have heq : N^ε/(9600*(C^(2*b)*F)/ω^4)=N^ε/(600*(C^(2*b)*F))*ω^4/16 := by field_simp; ring
    rw [heq] at hh
    apply Real.exp_le_exp.mpr
    nlinarith only [hh]
  have hcommon : 2*(b:ℝ)*N*Real.exp (-(N^ε/f)) ≤ n^(1-sourceTailExponent B D) := by
    have hcast : (b:ℝ) ≤ B := by exact_mod_cast hb
    have hh := mul_le_mul_of_nonneg_left htail hn0.le
    have hcoeff : 2*(b:ℝ)*N ≤ n*(2*(B:ℝ)) := by
      have hh' := mul_le_mul hcast hNn (by linarith only [hN]) (Nat.cast_nonneg B (α:=ℝ))
      nlinarith only [hh']
    have hp := mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos (-(N^ε/f))).le
    have heq : n*(n^(-sourceTailExponent B D))=n^(1-sourceTailExponent B D) := by
      calc
        _ = n^(1:ℝ)*n^(-sourceTailExponent B D) := by rw [Real.rpow_one]
        _ = _ := by rw [←Real.rpow_add hn0]; rfl
    nlinarith only [hh,hp,heq]
  have hfit := H.fit_tail hC hF hN (sourceEpsilon_pos B D).le
    (fun v hv=>sourceKappa_three_epsilon B D b (v+1) hb (by omega) (by omega))
  have hm := H.metadata_tail (ω:=ω) hN0
  have hf' := hfit.trans ((mul_le_mul_of_nonneg_left hexpfit (by positivity : 0 ≤ 2*(b:ℝ)*N)).trans hcommon)
  have hm' := hm.trans ((mul_le_mul_of_nonneg_left hexpmeta (by positivity : 0 ≤ 2*(b:ℝ)*N)).trans hcommon)
  have hpow : n^(1-sourceTailExponent B D) ≤ n^(-200*A) := by
    apply Real.rpow_le_rpow_of_exponent_le hn
    dsimp [sourceTailExponent]
    dsimp [A,M] at *
    linarith only [hA,hM]
  refine ⟨hm'.trans hpow,?_,hf'.trans hpow⟩
  rw [div_eq_mul_inv,←Real.rpow_neg hN0.le]
  simp only [neg_mul,neg_neg]
  have hr : N^(20*M) ≤ n^(20*M) := Real.rpow_le_rpow hN0.le hNn (by positivity)
  apply (mul_le_mul hf' hr (Real.rpow_pos_of_pos hN0 _).le (Real.rpow_pos_of_pos hn0 _).le).trans
  rw [←Real.rpow_add hn0]
  apply Real.rpow_le_rpow_of_exponent_le hn
  dsimp [sourceTailExponent]
  dsimp [A,M] at *
  linarith only [hA,hM]

end TraceReconstruction
noncomputable section


noncomputable section
noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- All three genuine clipping losses, and fitting, share the same global
 error unit. The reference power is the actual half-moment at this scale. -/
theorem source_level_clipping (B D j s b : ℕ) (T t : ℕ→ℕ) (n ω a gap L : ℝ)
    (hB : 2 ≤ B) (hn : 4 ≤ n) (hg : sourceGapFloor B ≤ gap)
    (hmeta : sourceEffectiveHiddenTail T t (b+1) ω ≤ n^(-200*(totalScoreExponent B D+B+1)))
    (hfit : sourceFitTail T t (b+1)/a ≤ n^(-200*(totalScoreExponent B D+B+1)))
    (hfit' : sourceFitTail T t (b+1) ≤ n^(-200*(totalScoreExponent B D+B+1)))
    (hhalf : ((6*(2*sourceHalfMoment B D n j:ℕ):ℝ)*L)^2*sourceSparseCount T s b ≤ 1/2)
    (hscale : ((6*(2*sourceHalfMoment B D n j:ℕ):ℝ)*L)^2*sourceSparseCount T s b ≤
      (sourceTargetScale B D n j)^(-gap/2)/8) :
    sourceClippingCost T t s b (sourceHalfMoment B D n j) ω a L ≤ 1/2 ∧
    sourceClippingCost T t s b (sourceHalfMoment B D n j) ω a L+sourceFitTail T t (b+1) ≤
      n^(-100*(totalScoreExponent B D+B+1)) := by
  have hN : 0 < sourceTargetScale B D n j := Real.rpow_pos_of_pos (by linarith only [hn]) _
  have hc := (source_clipping_moment_power T s b (sourceHalfMoment B D n j)
    (sourceTargetScale B D n j) gap L hN hhalf hscale).trans (source_clipping_power_delta B D j hB hn hg)
  have hu := sourceErrorUnit_small (D:=D) hB hn
  have hunit : 0 ≤ n^(-200*(totalScoreExponent B D+B+1)) := (Real.rpow_pos_of_pos (by linarith only [hn]) _).le
  unfold sourceClippingCost
  constructor <;> linarith only [hmeta,hfit,hfit',hc,hu.1,hu.2,hunit]

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
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Induction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Induction

Concrete level invariants, metadata prefixes, score/error budgets, overlap, the induction step, and the complete construction.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem source_level_geometry {B D i : ℕ} {n q : ℝ} {hq : q∈Set.Icc 0 1}
    (U : SourceLevelPair B D n q hq i) (hB : 2 ≤ B) (hi : i<D)
    (hn : 1 ≤ n) (hq' : q∈Set.Ioc 0 (1/2:ℝ))
    (H : SourceNumericMargins B D q (sourceTargetScale B D n (i+1))) :
    SourceArithmeticBounds (sourceOverlapConstant q) (sourceTargetScale B D n (i+1))
      ((sourceOverlapConstant q)^(2*B*i+2)) (sourceEpsilon B D)
      (sourceCancellationOrder B D) (sourceDimension B i) U.left.length U.overlapCount := by
  let N := sourceTargetScale B D n (i+1)
  let b := sourceDimension B i
  let C := sourceOverlapConstant q
  have hC : 2 ≤ C := sourceOverlapConstant_ge_two hq'
  have hb := sourceDimension_bounds B i hB
  have hN := (sourceTargetScale_bounds B D (i+1) hB hn).1
  have he := sourceEpsilon_pos B D
  have hG := source_local_envelope B D i b hq' (Nat.le_of_lt hi) hb.2
  apply source_arithmetic_geometry hC hN (one_le_pow₀ (by linarith only [hC])) he.le
    (fun j _=>sourceA_nonneg B D b j hb.2 (by omega))
    (fun j hj=>sourceKappa_three_epsilon B D b (j+1) hb.2 (by omega) (by omega))
  · have hh := mul_le_mul_of_nonneg_left hG (show (0:ℝ) ≤ 1200 by norm_num)
    exact (by nlinarith only [hh] : 1200*C^(2*b)*C^(2*B*i+2) ≤ 1200*sourceCapEnvelope B D q).trans H.geometry
  · simpa only [Nat.cast_pow,Nat.cast_ofNat] using H.motif
  · simpa only [sourceTargetScale_step B D i n (by linarith only [hn]) hi] using U.length_lower
  · simpa only [sourceTargetScale_step B D i n (by linarith only [hn]) hi] using U.length_upper
  · exact U.overlapCount_lower
  · exact U.overlapCount_upper

end TraceReconstruction


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem source_level_tail_budget {B D i : ℕ} {n q : ℝ} {hq : q∈Set.Icc 0 1}
    (U : SourceLevelPair B D n q hq i) (hB : 2 ≤ B) (hi : i<D) (hn : 4 ≤ n)
    (hq' : q∈Set.Ioc 0 (1/2:ℝ))
    (H : SourceNumericMargins B D q (sourceTargetScale B D n (i+1)))
    (htail : 2*(B:ℝ)*Real.exp
      (-(sourceTargetScale B D n (i+1))^(sourceEpsilon B D)/sourceTailDenominator B D q) ≤
        n^(-sourceTailExponent B D)) :
    let N := sourceTargetScale B D n (i+1)
    let b := sourceDimension B i
    let ε := sourceEpsilon B D
    let T := sourceBlockWindows N b ε
    let t := sourceArithmeticTrials (sourceOverlapConstant q) N b ε U.left.length U.overlapCount
    sourceEffectiveHiddenTail T t b (initialOverlapLower q) ≤ n^(-200*(totalScoreExponent B D+B+1)) ∧
    sourceFitTail T t b/N^(-20*sourceWorkSize B D) ≤ n^(-200*(totalScoreExponent B D+B+1)) ∧
    sourceFitTail T t b ≤ n^(-200*(totalScoreExponent B D+B+1)) := by
  have hn1 : 1 ≤ n := by linarith only [hn]
  have H' := source_level_geometry U hB hi hn1 hq' H
  have hb := sourceDimension_bounds B i hB
  have hN := sourceTargetScale_bounds B D (i+1) hB hn1
  have hC := sourceOverlapConstant_pos hq'.1
  have hω := initialOverlapLower_pos q
  have hG := source_local_envelope B D i (sourceDimension B i) hq' (Nat.le_of_lt hi) hb.2
  have hf : 9600*((sourceOverlapConstant q)^(2*sourceDimension B i)*
      (sourceOverlapConstant q)^(2*B*i+2))/(initialOverlapLower q)^4 ≤ sourceTailDenominator B D q := by
    have hh := mul_le_mul_of_nonneg_right hG (show 0 ≤ 9600*(initialOverlapLower q)⁻¹^4 by positivity)
    unfold sourceTailDenominator
    rw [div_eq_mul_inv,←inv_pow]
    nlinarith only [hh]
  exact source_exponential_error_budget H' hB hb.2 hC (by positivity) hω hn1 hN.1 hN.2
    (by
      have hh : 0 ≤ 9600*sourceCapEnvelope B D q*(initialOverlapLower q)⁻¹^4 := by positivity [sourceCapEnvelope_pos B D hq'.1]
      unfold sourceTailDenominator
      linarith only [hh]) hf
    (by simpa only [neg_div] using htail)

theorem source_level_all_budgets_oai {B D i : ℕ} {n q : ℝ} {hq : q∈Set.Icc 0 1}
    (U : SourceLevelPair B D n q hq i) (hB : 2 ≤ B) (hi : i<D) (hn : 4 ≤ n)
    (hq' : q∈Set.Ioc 0 (1/2:ℝ))
    (H : SourceNumericMargins B D q (sourceTargetScale B D n (i+1)))
    (htail : 2*(B:ℝ)*Real.exp
      (-(sourceTargetScale B D n (i+1))^(sourceEpsilon B D)/sourceTailDenominator B D q) ≤
        n^(-sourceTailExponent B D)) :
    let N := sourceTargetScale B D n (i+1)
    let b := sourceDimension B i
    let ε := sourceEpsilon B D
    let s := sourceCancellationOrder B D
    let T := sourceBlockWindows N b ε
    let t := sourceArithmeticTrials (sourceOverlapConstant q) N b ε U.left.length U.overlapCount
    let k := sourceHalfMoment B D n (i+1)
    let L := N^(-scaleA b 0 ε*totalScoreExponent B i/2)
    let a := N^(-20*sourceWorkSize B D)
    let ω := initialOverlapLower q
    let gap := (totalScoreExponent B i+1)*sourceGapFloor B
    (((6*(2*k:ℕ):ℝ)*L)^2*(sourceSparseCount T s (b-1):ℝ) ≤ N^(-gap/2)/8) ∧
    (((6*(2*k:ℕ):ℝ)*L)^2*(sourceSparseCount T s (b-1):ℝ) ≤ 1/2) ∧
    (64*sourceSharpEnergyBudget T t s (b-1) (sourceDegreeCutoff B) ω a a ((6*(2*k:ℕ):ℝ)*L) ≤
       N^(-totalScoreExponent B (i+1))) ∧
    (∀j<b,hiddenSmoothingBound (t j) s ω ≤ a) ∧
    sourceClippingCost T t s (b-1) k ω a L ≤ 1/2 ∧
    sourceClippingCost T t s (b-1) k ω a L+sourceFitTail T t b ≤
      n^(-100*(totalScoreExponent B D+B+1)) := by
  have hn1 : 1 ≤ n := by linarith only [hn]
  have hn2 : 1<n := by linarith only [hn]
  have hC : 1 ≤ sourceOverlapConstant q := (by norm_num : (1:ℝ) ≤ 2).trans (sourceOverlapConstant_ge_two hq')
  have H' := source_level_geometry U hB hi hn1 hq' H
  have hb := sourceDimension_bounds B i hB
  have hb1 : sourceDimension B i-1+1=sourceDimension B i := by omega
  have hN := sourceTargetScale_bounds B D (i+1) hB hn1
  have he := source_level_energy B D i U.left.length U.overlapCount (sourceHalfMoment B D n (i+1))
    (sourceOverlapConstant q) (sourceTargetScale B D n (i+1)) ((sourceOverlapConstant q)^(2*B*i+2))
    (initialOverlapLower q) (sourceCapEnvelope B D q) hB hi hN.1 hC (one_le_pow₀ hC) (initialOverlapLower_pos q)
    H' (sourceHalfMoment_bounds B D (i+1) hB hn2).2
    (source_cap_envelope B D i (sourceDimension B i) hq' (Nat.le_of_lt hi) hb.2)
    (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using H.sparse)
    (H.bad _ (by omega)) (by simpa only [hb1] using H.force (sourceDimension B i-1) (by omega)) H.tail H.smoothing
  have ht := source_level_tail_budget U hB hi hn hq' H htail
  have hg : sourceGapFloor B ≤ (totalScoreExponent B i+1)*sourceGapFloor B := by
    exact le_mul_of_one_le_left (sourceGapFloor_pos B).le
      (by linarith only [(totalScoreExponent_bounds B i hB).1])
  have hc := source_level_clipping B D (i+1) (sourceCancellationOrder B D) (sourceDimension B i-1)
    (sourceBlockWindows (sourceTargetScale B D n (i+1)) (sourceDimension B i) (sourceEpsilon B D))
    (sourceArithmeticTrials (sourceOverlapConstant q) (sourceTargetScale B D n (i+1))
      (sourceDimension B i) (sourceEpsilon B D) U.left.length U.overlapCount)
    n (initialOverlapLower q) ((sourceTargetScale B D n (i+1))^(-20*sourceWorkSize B D))
    ((totalScoreExponent B i+1)*sourceGapFloor B)
    ((sourceTargetScale B D n (i+1))^(-scaleA (sourceDimension B i) 0 (sourceEpsilon B D)*totalScoreExponent B i/2))
    hB hn hg (by simpa only [hb1] using ht.1) (by simpa only [hb1] using ht.2.1)
    (by simpa only [hb1] using ht.2.2) he.2.1 he.1
  exact ⟨he.1,he.2.1,he.2.2.1,he.2.2.2,hc.1,by simpa only [hb1] using hc.2⟩

end TraceReconstruction


end
end
end
end

end OAI
end

theorem solution : type_of% @OAI.TraceReconstruction.source_level_all_budgets_oai := @OAI.TraceReconstruction.source_level_all_budgets_oai
