-- Prove2me | solution 1 for OAI.TraceReconstruction.superpolynomial_one_trace
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T09:56:32.921919+00:00
-- url     : https://prove2.me/submissions/35ce9cde-ebd7-4af7-aaa9-a8ffb33fcacd

import Mathlib
import Definitions.Def_TraceReconstruction
import Definitions.Def_OAIQ9Tr002
import Theorems.Thm_OAI_TraceReconstruction_source_all_levels_eventually

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_FiniteLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# FiniteLaw

Finite laws, common-reference total variation, Hellinger affinity, overlap, scalar moments, hypercontractivity, clipping, and leaf densities.
-/

open scoped ENNReal
noncomputable section

noncomputable section
namespace TraceReconstruction

namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

theorem tv_sq_le_hellingerSq (P Q : FiniteLaw α) :
    tv P Q ^ 2 ≤ hellingerSq P Q := by
  have hpoint (a : α) : |P.mass a - Q.mass a| ^ 2 ≤
      (Real.sqrt (P.mass a) - Real.sqrt (Q.mass a)) ^ 2 *
        (Real.sqrt (P.mass a) + Real.sqrt (Q.mass a)) ^ 2 := by
    rw [sq_abs]
    have hp := Real.sq_sqrt (P.nonneg a)
    have hq := Real.sq_sqrt (Q.nonneg a)
    nlinarith only [hp, hq, sq_nonneg (P.mass a - Q.mass a)]
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (s := Finset.univ)
    (r := fun a => |P.mass a - Q.mass a|)
    (f := fun a => (Real.sqrt (P.mass a) - Real.sqrt (Q.mass a)) ^ 2)
    (g := fun a => (Real.sqrt (P.mass a) + Real.sqrt (Q.mass a)) ^ 2)
    (fun a _ => sq_nonneg _) (fun a _ => sq_nonneg _) (fun a _ => hpoint a)
  have hplus : (∑ a, (Real.sqrt (P.mass a) + Real.sqrt (Q.mass a)) ^ 2) =
      2 + 2 * affinity P Q := by
    unfold affinity
    calc
      _ = (∑ a, P.mass a) + (∑ a, Q.mass a) + 2 * ∑ a,
          Real.sqrt (P.mass a) * Real.sqrt (Q.mass a) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro a _
        have hp := Real.sq_sqrt (P.nonneg a)
        have hq := Real.sq_sqrt (Q.nonneg a)
        nlinarith only [hp, hq]
      _ = _ := by rw [P.total, Q.total]; ring
  rw [hplus] at h
  change (∑ a, |P.mass a - Q.mass a|) ^ 2 ≤ hellingerSq P Q * (2 + 2 * affinity P Q) at h
  have hbound := mul_le_mul_of_nonneg_left (affinity_le_one P Q) (hellingerSq_nonneg P Q)
  unfold tv
  nlinarith only [h, hbound]

theorem tv_le_sqrt_hellingerSq (P Q : FiniteLaw α) :
    tv P Q ≤ Real.sqrt (hellingerSq P Q) := by
  have h := tv_sq_le_hellingerSq P Q
  have hs := Real.sq_sqrt (hellingerSq_nonneg P Q)
  have hn := Real.sqrt_nonneg (hellingerSq P Q)
  nlinarith only [h, hs, hn]

theorem affinity_product (P Q : FiniteLaw α) (m : ℕ) :
    affinity (P.product m) (Q.product m) = affinity P Q ^ m := by
  unfold affinity product
  simp only
  have hexp (a : Fin m → α) :
      Real.sqrt (∏ j, P.mass (a j)) * Real.sqrt (∏ j, Q.mass (a j)) =
        ∏ j, (Real.sqrt (P.mass (a j)) * Real.sqrt (Q.mass (a j))) := by
    rw [Real.sqrt_prod _ (fun j _ => P.nonneg (a j)),
      Real.sqrt_prod _ (fun j _ => Q.nonneg (a j)), Finset.prod_mul_distrib]
  simp_rw [hexp]
  rw [← Fintype.prod_sum (fun (_ : Fin m) a => Real.sqrt (P.mass a) * Real.sqrt (Q.mass a))]
  simp

theorem hellingerSq_product_le (P Q : FiniteLaw α) (m : ℕ) :
    hellingerSq (P.product m) (Q.product m) ≤ (m : ℝ) * hellingerSq P Q := by
  rw [hellingerSq_eq, affinity_product, hellingerSq_eq]
  have ha := affinity_nonneg P Q
  have hb := affinity_le_one P Q
  have hpow : 1 - affinity P Q ^ m ≤ (m : ℝ) * (1 - affinity P Q) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, Nat.cast_add, Nat.cast_one]
      have hmul := mul_le_mul_of_nonneg_right ih ha
      have hm : (0 : ℝ) ≤ (m : ℝ) * (1 - affinity P Q) := by positivity
      have hmon := mul_le_mul_of_nonneg_left hb hm
      nlinarith only [hmul, hmon]
  linarith


theorem tv_bind_le (P Q : FiniteLaw α) (K : α → FiniteLaw β) :
    tv (P.bind K) (Q.bind K) ≤ tv P Q := by
  unfold tv bind
  simp only
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ = ∑ b, |∑ a, (P.mass a - Q.mass a) * (K a).mass b| := by
      apply Finset.sum_congr rfl
      intro b _
      congr 1
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _; ring
    _ ≤ ∑ b, ∑ a, |(P.mass a - Q.mass a) * (K a).mass b| :=
      Finset.sum_le_sum fun b _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a, |P.mass a - Q.mass a| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      simp_rw [abs_mul, abs_of_nonneg ((K a).nonneg _), ← Finset.mul_sum, (K a).total, mul_one]

theorem tv_triangle (P Q R : FiniteLaw α) : tv P R ≤ tv P Q + tv Q R := by
  unfold tv
  rw [← mul_add, ← Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro a _
  exact abs_sub_le _ _ _

theorem tv_tensor_le (P Q : FiniteLaw α) (R S : FiniteLaw β) :
    tv (P.tensor R) (Q.tensor S) ≤ tv P Q + tv R S := by
  unfold tv tensor
  simp only
  rw [Fintype.sum_prod_type, ← mul_add]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hpoint (a : α) (b : β) :
      |P.mass a * R.mass b - Q.mass a * S.mass b| ≤
        |P.mass a - Q.mass a| * R.mass b + Q.mass a * |R.mass b - S.mass b| := by
    calc
      _ = |(P.mass a - Q.mass a) * R.mass b + Q.mass a * (R.mass b - S.mass b)| := by
        congr 1; ring
      _ ≤ |(P.mass a - Q.mass a) * R.mass b| + |Q.mass a * (R.mass b - S.mass b)| :=
        abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg (R.nonneg b), abs_of_nonneg (Q.nonneg a)]
  calc
    _ ≤ ∑ a, ∑ b, (|P.mass a - Q.mass a| * R.mass b + Q.mass a * |R.mass b - S.mass b|) := by
      apply Finset.sum_le_sum
      intro a _
      exact Finset.sum_le_sum fun b _ => hpoint a b
    _ = _ := by
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum, R.total, mul_one]
      rw [← Finset.sum_mul, Q.total, one_mul]

theorem tv_product_succ (P Q : FiniteLaw α) (m : ℕ) :
    tv (P.product (m + 1)) (Q.product (m + 1)) =
      tv (P.tensor (P.product m)) (Q.tensor (Q.product m)) := by
  unfold tv product tensor
  simp only
  congr 1
  rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => α)).sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Fin.prod_univ_succ, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]

theorem tv_product_le (P Q : FiniteLaw α) (m : ℕ) :
    tv (P.product m) (Q.product m) ≤ (m : ℝ) * tv P Q := by
  induction m with
  | zero => simp [tv, product]
  | succ m ih =>
    rw [tv_product_succ]
    apply (tv_tensor_le P Q (P.product m) (Q.product m)).trans
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm] using
      add_le_add_left ih (tv P Q)


theorem affinity_bind_ge (P Q : FiniteLaw α) (K : α → FiniteLaw β) :
    affinity P Q ≤ affinity (P.bind K) (Q.bind K) := by
  have hpoint (b : β) :
      (∑ a, Real.sqrt (P.mass a) * Real.sqrt (Q.mass a) * (K a).mass b) ≤
        Real.sqrt ((P.bind K).mass b) * Real.sqrt ((Q.bind K).mass b) := by
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (s := Finset.univ)
      (r := fun a => Real.sqrt (P.mass a) * Real.sqrt (Q.mass a) * (K a).mass b)
      (f := fun a => P.mass a * (K a).mass b) (g := fun a => Q.mass a * (K a).mass b)
      (fun a _ => mul_nonneg (P.nonneg a) ((K a).nonneg b))
      (fun a _ => mul_nonneg (Q.nonneg a) ((K a).nonneg b)) (by
        intro a _
        rw [mul_pow, mul_pow, Real.sq_sqrt (P.nonneg a), Real.sq_sqrt (Q.nonneg a)]
        nlinarith only [sq_nonneg ((K a).mass b)])
    have hp2 := Real.sq_sqrt ((P.bind K).nonneg b)
    have hq2 := Real.sq_sqrt ((Q.bind K).nonneg b)
    have hsq : (Real.sqrt ((P.bind K).mass b) * Real.sqrt ((Q.bind K).mass b)) ^ 2 =
        (P.bind K).mass b * (Q.bind K).mass b := by rw [mul_pow, hp2, hq2]
    change (∑ a, Real.sqrt (P.mass a) * Real.sqrt (Q.mass a) * (K a).mass b) ^ 2 ≤
      (P.bind K).mass b * (Q.bind K).mass b at hcs
    have hn : 0 ≤ Real.sqrt ((P.bind K).mass b) * Real.sqrt ((Q.bind K).mass b) := by positivity
    nlinarith only [hcs, hsq, hn]
  calc
    affinity P Q = ∑ b, ∑ a, Real.sqrt (P.mass a) * Real.sqrt (Q.mass a) * (K a).mass b := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, (K _).total, mul_one]
      rfl
    _ ≤ _ := Finset.sum_le_sum fun b _ => hpoint b

theorem hellingerSq_bind_le (P Q : FiniteLaw α) (K : α → FiniteLaw β) :
    hellingerSq (P.bind K) (Q.bind K) ≤ hellingerSq P Q := by
  rw [hellingerSq_eq, hellingerSq_eq]
  linarith [affinity_bind_ge P Q K]

end FiniteLaw
end TraceReconstruction

end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Model

Independent deletion, complete trace observations, randomized estimators, ENNReal fixed-budget complexity, concatenation, and literal input words.
-/

open scoped ENNReal
noncomputable section

open scoped ENNReal
noncomputable section

noncomputable section

namespace TraceReconstruction




/-! ## Exact finite channel laws -/

theorem traceTV_nonneg {n : ℕ} (q : ℝ) (x y : Word n) : 0 ≤ traceTV q x y := by
  unfold traceTV
  positivity


end TraceReconstruction

namespace TraceReconstruction

theorem completeTraceLaw_tv {n : ℕ} (q : ℝ) (hq : q ∈ Set.Icc 0 1) (x y : Word n) :
    (completeTraceLaw q hq x).tv (completeTraceLaw q hq y) = traceTV q x y := by
  change (1 / 2 : ℝ) * (∑ w : BoundedTrace n, |traceMass q x w - traceMass q y w|) = _
  rw [Finset.sum_coe_sort (traceSpace n) (fun w => |traceMass q x w - traceMass q y w|)]
  rfl

theorem completeTraceLaw_mask {n : ℕ} (q : ℝ) (hq : q ∈ Set.Icc 0 1) (x : Word n) :
    completeTraceLaw q hq x =
      (maskLaw q hq).map (fun a : Mask n => ⟨traceOfMask x a, traceOfMask_mem x a⟩) := by
  apply FiniteLaw.ext
  funext w
  rw [FiniteLaw.map_mass]
  unfold completeTraceLaw traceMass maskLaw
  simp only
  apply Finset.sum_congr rfl
  intro a _
  rcases w with ⟨w, hw⟩
  simp only [Subtype.mk.injEq]

end TraceReconstruction

end
end
end

end OAI
end

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

theorem sourceEpsilon_pos (B D : ℕ) : 0 < sourceEpsilon B D := by
  unfold sourceEpsilon
  positivity

end TraceReconstruction

open Filter
open scoped Topology


open Filter
open scoped Topology
namespace TraceReconstruction

theorem workingDeletion_bounds {q : ℝ} (hq : q ∈ Set.Ioo 0 1) :
    workingDeletion q ∈ Set.Ioo 0 1 ∧ q/2 ≤ workingDeletion q ∧ workingDeletion q ≤ q := by
  unfold workingDeletion
  constructor
  · constructor
    · exact lt_min hq.1 (by norm_num)
    · exact (min_le_left _ _).trans_lt hq.2
  constructor
  · exact le_min (by linarith [hq.1]) (by linarith [hq.2])
  · exact min_le_left _ _

theorem blockGain_two : blockGain 2 = 1/5 := by norm_num [blockGain]

theorem sourceDepth_tendsto (B : ℕ) (ζ : ℝ) (hB : 2 ≤ B) (hζ : ζ < 1)
    {H : ℕ → ℝ} (hH : Tendsto H atTop atTop) :
    Tendsto (fun k => sourceDepth B ζ (H k)) atTop atTop := by
  have hden : 0 < (B:ℝ)*Real.log 2 := by
    apply mul_pos
    · exact_mod_cast (show 0 < B by omega)
    · exact Real.log_pos (by norm_num)
  have ht := (Real.tendsto_log_atTop.comp hH).const_mul_atTop (sub_pos.mpr hζ)
  have ht' := ht.atTop_div_const hden
  exact tendsto_nat_floor_atTop.comp ht'

end TraceReconstruction

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical
open Filter

theorem sourceTargetScale_top (B D : ℕ) (n : ℝ) : sourceTargetScale B D n D=n := by
  simp [sourceTargetScale,sourceScaleProduct]

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

theorem sourceDepth_upper (B : ℕ) (ζ H : ℝ) (_hB : 2 ≤ B)
    (hζ : ζ ≤ 1) (hH : 1 ≤ H) :
    (sourceDepth B ζ H:ℝ) ≤ (1-ζ)*Real.log H/((B:ℝ)*Real.log 2) := by
  apply Nat.floor_le
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr hζ) (Real.log_nonneg hH))
    (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num)))

theorem sourceDepth_power (B : ℕ) (ζ H : ℝ) (hB : 2 ≤ B)
    (hζ : ζ ≤ 1) (hH : 1 ≤ H) :
    (2:ℝ)^(B*sourceDepth B ζ H) ≤ H^(1-ζ) := by
  have hden : 0 < (B:ℝ)*Real.log 2 :=
    mul_pos (by exact_mod_cast (show 0 < B by omega)) (Real.log_pos (by norm_num))
  have hd := (le_div_iff₀ hden).mp (sourceDepth_upper B ζ H hB hζ hH)
  apply (Real.log_le_log_iff (by positivity) (Real.rpow_pos_of_pos (by linarith) _)).mp
  rw [Real.log_pow,Real.log_rpow (by linarith : 0 < H)]
  push_cast
  nlinarith only [hd]

/-- Source smallest-scale lower bound, with an absolute explicit factor. -/
theorem sourceTargetScale_log_lower (B : ℕ) (ζ H n : ℝ) (i : ℕ) (hB : 2 ≤ B)
    (hζ : ζ ≤ 1) (hH : 1 ≤ H) (hn : 1 < n) :
    Real.log n/(2*H^(1-ζ)) ≤ Real.log (sourceTargetScale B (sourceDepth B ζ H) n i) := by
  have hp := sourceDepth_power B ζ H hB hζ hH
  have hs := sourceScaleProduct_lower B (sourceDepth B ζ H) i hB
  have hfrac : 1/(2*H^(1-ζ)) ≤ 1/(2*(2:ℝ)^(B*sourceDepth B ζ H)) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith only [hp])
  have hh := mul_le_mul_of_nonneg_right (hfrac.trans hs) (Real.log_pos hn).le
  unfold sourceTargetScale
  rw [Real.log_rpow (by linarith)]
  simpa only [div_eq_mul_inv,one_mul,mul_comm] using hh

/-- Polynomial depth losses are negligible compared with the H-zeta gain.
 This statement has no bounded-deletion-rate premise. -/
theorem sourceDepth_polynomial_absorption (B h : ℕ) (ζ : ℝ) (hB : 2 ≤ B)
    (hζ : ζ∈Set.Ioo 0 1) {H : ℕ → ℝ} (hH : Tendsto H atTop atTop) :
    Tendsto (fun k => ((sourceDepth B ζ (H k):ℝ)+1)^h/(H k)^ζ) atTop (nhds 0) := by
  let A := (1-ζ)/((B:ℝ)*Real.log 2)+1
  have hd : 0 < (B:ℝ)*Real.log 2 :=
    mul_pos (by exact_mod_cast (show 0 < B by omega)) (Real.log_pos (by norm_num))
  have hA : 0 < A := by dsimp [A]; positivity [sub_pos.mpr hζ.2]
  have hl := (isLittleO_log_rpow_rpow_atTop (h:ℝ) hζ.1).tendsto_div_nhds_zero.comp hH
  simp only [Real.rpow_natCast] at hl
  have hx := hl.const_mul (A^h)
  simp only [mul_zero] at hx
  apply squeeze_zero' _ _ hx
  · filter_upwards [hH.eventually_gt_atTop 0] with k hk
    exact div_nonneg (by positivity) (Real.rpow_pos_of_pos hk _).le
  · filter_upwards [hH.eventually_ge_atTop 1,
      (Real.tendsto_log_atTop.comp hH).eventually_ge_atTop 1] with k hk hklog
    have hD := sourceDepth_upper B ζ (H k) hB hζ.2.le hk
    have hDa : (sourceDepth B ζ (H k):ℝ)+1 ≤ A*Real.log (H k) := by
      dsimp [A]
      change 1 ≤ Real.log (H k) at hklog
      calc
        _ ≤ (1-ζ)*Real.log (H k)/((B:ℝ)*Real.log 2)+Real.log (H k) := add_le_add hD hklog
        _ = _ := by ring
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ (sourceDepth B ζ (H k):ℝ)+1) hDa h
    rw [mul_pow] at hh
    exact (div_le_div_of_nonneg_right hh (by positivity)).trans_eq (by dsimp only [Function.comp_def]; ring)

/-- Uniform quantitative scale margin.  This is the source's Lambda*H^zeta
 bound, before any little-o notation or parameter choices. -/
theorem sourceTargetScale_epsilon_log_lower (B : ℕ) (ζ H n Λ : ℝ) (i : ℕ)
    (hB : 2 ≤ B) (hζ : ζ ≤ 1) (hH : 1 ≤ H) (hn : 1 < n)
    (hΛ : 0 < Λ) (hrel : Real.log n=Λ*H) :
    Λ*H^ζ/(2*(2:ℝ)^(4*B+100)*((sourceDepth B ζ H:ℝ)+1)) ≤
      sourceEpsilon B (sourceDepth B ζ H)*
        Real.log (sourceTargetScale B (sourceDepth B ζ H) n i) := by
  have h := mul_le_mul_of_nonneg_left (sourceTargetScale_log_lower B ζ H n i hB hζ hH hn)
    (sourceEpsilon_pos B (sourceDepth B ζ H)).le
  apply le_trans _ h
  rw [hrel,Real.rpow_sub (by linarith : 0 < H), Real.rpow_one]
  unfold sourceEpsilon
  have hH0 : H≠0 := by linarith
  have hHz : H^ζ≠0 := (Real.rpow_pos_of_pos (by linarith : 0 < H) _).ne'
  have hd : (sourceDepth B ζ H:ℝ)+1≠0 := by positivity
  have hp : (2:ℝ)^(4*B+100)≠0 := by positivity
  apply le_of_eq
  field_simp

theorem source_absorption_ratio_bound (B h : ℕ) (ζ H n Λ : ℝ) (i : ℕ)
    (hB : 2 ≤ B) (hζ : ζ ≤ 1) (hH : 1 ≤ H) (hn : 1 < n)
    (hΛ : 0 < Λ) (hrel : Real.log n=Λ*H) :
    ((sourceDepth B ζ H:ℝ)+1)^h*Λ /
      (sourceEpsilon B (sourceDepth B ζ H)*
        Real.log (sourceTargetScale B (sourceDepth B ζ H) n i)) ≤
      (2*(2:ℝ)^(4*B+100))*(((sourceDepth B ζ H:ℝ)+1)^(h+1)/H^ζ) := by
  have hHz : 0 < H^ζ := Real.rpow_pos_of_pos (by linarith) _
  have hlow := sourceTargetScale_epsilon_log_lower B ζ H n Λ i hB hζ hH hn hΛ hrel
  have hh := div_le_div_of_nonneg_left
    (by positivity : 0 ≤ ((sourceDepth B ζ H:ℝ)+1)^h*Λ)
    (by positivity : 0 < Λ*H^ζ/(2*(2:ℝ)^(4*B+100)*((sourceDepth B ζ H:ℝ)+1))) hlow
  apply hh.trans_eq
  rw [pow_succ]
  field_simp; ring

theorem source_uniform_exp_absorption (B h : ℕ) (ζ C δ : ℝ) (hB : 2 ≤ B)
    (hζ : ζ∈Set.Ioo 0 1) (hC : 0 ≤ C) (hδ : 0 < δ)
    {n Λ H : ℕ → ℝ} (hn : Tendsto n atTop atTop) (hH : Tendsto H atTop atTop)
    (hΛ : ∀k,0 < Λ k) (hrel : ∀k,Real.log (n k)=Λ k*H k) :
    ∀ᶠk in atTop,∀i,
      Real.exp (C*((sourceDepth B ζ (H k):ℝ)+1)^h*Λ k) ≤
        (sourceTargetScale B (sourceDepth B ζ (H k)) (n k) i)^
          (δ*sourceEpsilon B (sourceDepth B ζ (H k))) := by
  have hb := (sourceDepth_polynomial_absorption B (h+1) ζ hB hζ hH).const_mul
    (C*(2*(2:ℝ)^(4*B+100)))
  simp only [mul_zero] at hb
  filter_upwards [hH.eventually_ge_atTop 1,hn.eventually_gt_atTop 1,
    hb.eventually_lt_const hδ] with k hk hnk hbound
  intro i
  have hratio := source_absorption_ratio_bound B h ζ (H k) (n k) (Λ k) i
    hB hζ.2.le hk hnk (hΛ k) (hrel k)
  have hlower := sourceTargetScale_epsilon_log_lower B ζ (H k) (n k) (Λ k) i
    hB hζ.2.le hk hnk (hΛ k) (hrel k)
  have hΛk := hΛ k
  have hHk : 0 < H k := by linarith
  have hden : 0 < sourceEpsilon B (sourceDepth B ζ (H k))*
      Real.log (sourceTargetScale B (sourceDepth B ζ (H k)) (n k) i) :=
    lt_of_lt_of_le (by positivity) hlower
  have hMul := mul_le_mul_of_nonneg_left hratio hC
  have H' : C*(((sourceDepth B ζ (H k):ℝ)+1)^h*Λ k)/
      (sourceEpsilon B (sourceDepth B ζ (H k))*
        Real.log (sourceTargetScale B (sourceDepth B ζ (H k)) (n k) i)) ≤ δ := by
    calc
      _ = C*(((sourceDepth B ζ (H k):ℝ)+1)^h*Λ k /
        (sourceEpsilon B (sourceDepth B ζ (H k))*
          Real.log (sourceTargetScale B (sourceDepth B ζ (H k)) (n k) i))) := by ring
      _ ≤ _ := hMul.trans (by simpa only [mul_assoc] using hbound.le)
  have HH := (div_le_iff₀ hden).mp H'
  have hN : 0 < sourceTargetScale B (sourceDepth B ζ (H k)) (n k) i :=
    Real.rpow_pos_of_pos (by linarith) _
  rw [Real.rpow_def_of_pos hN]
  exact Real.exp_le_exp.mpr (by nlinarith only [HH])

end TraceReconstruction


end
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
namespace TraceReconstruction.FiniteLaw
open scoped Classical
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem expect_bind (P : FiniteLaw α) (K : α → FiniteLaw β) (f : β → ℝ) :
    (P.bind K).expect f=P.expect (fun a => (K a).expect f) := by
  unfold expect bind
  simp_rw [Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

end TraceReconstruction.FiniteLaw


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem listDeletionExpectation_linear (q : ℝ) (w : List Bool)
    (a b : ℝ) (F G : List Bool → ℝ) :
    listDeletionExpectation q w (fun t => a*F t+b*G t)=
      a*listDeletionExpectation q w F+b*listDeletionExpectation q w G := by
  induction w generalizing F G with
  | nil => rfl
  | cons c w ih => simp only [listDeletionExpectation,ih]; ring

end TraceReconstruction


noncomputable section
noncomputable section
noncomputable section
noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem ext_expect {P Q : FiniteLaw α} (h : ∀f : α→ℝ,P.expect f=Q.expect f) : P=Q := by
  apply ext
  funext a
  have H:=h (fun b => if b=a then 1 else 0)
  simpa only [expect,mul_ite,mul_one,mul_zero,Fintype.sum_ite_eq'] using H

end FiniteLaw

end TraceReconstruction


noncomputable section


noncomputable section
noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem bind_map (P : FiniteLaw α) (f : α→β) (K : β→FiniteLaw γ) :
    (P.map f).bind K=P.bind (K∘f) := by
  apply ext_expect
  intro F
  rw [expect_bind,expect_map,expect_bind]
  rfl

end FiniteLaw

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

theorem sourceEpsilon_le_one (B D : ℕ) : sourceEpsilon B D ≤ 1 := by
  unfold sourceEpsilon
  apply (div_le_one (by positivity)).mpr
  have H : (1:ℝ) ≤ 2^(4*B+100) := one_le_pow₀ (by norm_num)
  nlinarith [show (0:ℝ) ≤ D by positivity]

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


noncomputable section


noncomputable section


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

theorem deletion_inverse_cube_ge_one {q : ℝ} (hq : q∈Set.Ioc 0 1) :
    1 ≤ q^(-3:ℤ) := by
  rw [zpow_neg,zpow_ofNat,one_le_inv₀ (pow_pos hq.1 _)]
  exact pow_le_one₀ hq.1.le hq.2

end TraceReconstruction


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


noncomputable section


noncomputable section


noncomputable section


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

theorem SourcePolyUpper.depth : SourcePolyUpper (fun D=>(D:ℝ)+1) := by
  exact ⟨1,zero_le_one,1,by simp⟩

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

theorem SourcePolyUpper.expUpper {f : ℕ→ℝ} (hf : SourcePolyUpper f) :
    SourceExpUpper (fun D _=>f D) := by
  obtain ⟨C,hC,h,H⟩ := hf
  refine ⟨C,hC,h,?_⟩
  intro D q hq
  have hΛ := deletion_inverse_cube_ge_one ⟨hq.1,by linarith only [hq.2]⟩
  have hmul := mul_le_mul_of_nonneg_left hΛ (show 0 ≤ C*((D:ℝ)+1)^h by positivity)
  exact (H D).trans ((by linarith only [hmul] : C*((D:ℝ)+1)^h ≤ C*((D:ℝ)+1)^h*q^(-3:ℤ)+1).trans
    (Real.add_one_le_exp _))

/-- All indices are inside the same physical n,q instance. -/
theorem SourceExpUpper.uniform (f : ℕ→ℝ→ℝ) (hf : SourceExpUpper f)
    (B : ℕ) (ζ δ : ℝ) (hB : 2 ≤ B) (hζ : ζ∈Set.Ioo 0 1) (hδ : 0<δ)
    {n q : ℕ→ℝ} (hn : Tendsto n atTop atTop) (hq : ∀t,q t∈Set.Ioc 0 (1/2:ℝ))
    (hH : Tendsto (fun t=>(q t)^3*Real.log (n t)) atTop atTop) :
    ∀ᶠt in atTop,∀i,f (sourceDepth B ζ ((q t)^3*Real.log (n t))) (q t) ≤
      (sourceTargetScale B (sourceDepth B ζ ((q t)^3*Real.log (n t))) (n t) i)^(
        δ*sourceEpsilon B (sourceDepth B ζ ((q t)^3*Real.log (n t)))) := by
  obtain ⟨C,hC,h,H⟩ := hf
  have hrel (t) : Real.log (n t)=(q t)^(-3:ℤ)*((q t)^3*Real.log (n t)) := by
    rw [zpow_neg,zpow_ofNat]
    field_simp [(hq t).1.ne']
  filter_upwards [source_uniform_exp_absorption B h ζ C δ hB hζ hC hδ hn hH
    (fun t=>zpow_pos (hq t).1 _) hrel] with t ht i
  exact (H _ _ (hq t)).trans (ht i)

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

noncomputable section

noncomputable section

noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem ConcreteLevelPair.error_le {q N Δ d ω F : ℝ} {hq : q∈Set.Icc 0 1} {i k : ℕ}
    (C : ConcreteLevelPair q hq N Δ d ω F i k) (hN : 0< N) (hΔ : 0≤Δ) :
    C.error≤((i:ℝ)+1)*Δ*N := by
  have hl : 0<(C.left.length:ℝ) := lt_of_lt_of_le (by linarith only [hN]) C.length_lower
  exact ((div_le_iff₀ hl).mp C.normalized_error).trans
    (mul_le_mul_of_nonneg_left C.length_upper (by positivity))

end TraceReconstruction

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


noncomputable section


noncomputable section


noncomputable section


noncomputable section


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

/-- The final source pair has actual length in [n/2,n], an exact common
 complete-trace simulator, prescribed high moment and inductively obtained
 power overlap. This is the construction theorem, before statistical transfer. -/
theorem source_final_pair_eventually (B : ℕ) (ζ : ℝ) (hB : 2 ≤ B)
    (hζ : ζ∈Set.Ioo 0 1) {n q : ℕ→ℝ} (hn : Tendsto n atTop atTop)
    (hq : ∀t,q t∈Set.Ioc 0 (1/2:ℝ))
    (hH : Tendsto (fun t=>(q t)^3*Real.log (n t)) atTop atTop) :
    ∀ᶠt in atTop,Nonempty (ConcreteLevelPair (q t) ⟨(hq t).1.le,by linarith [(hq t).2]⟩ (n t)
      ((n t)^(-100*(totalScoreExponent B (sourceDepth B ζ ((q t)^3*Real.log (n t)))+B+1)))
      (totalScoreExponent B (sourceDepth B ζ ((q t)^3*Real.log (n t))))
      (initialOverlapLower (q t))
      ((sourceOverlapConstant (q t))^(2*B*sourceDepth B ζ ((q t)^3*Real.log (n t))+2))
      (sourceDepth B ζ ((q t)^3*Real.log (n t)))
      (sourceHalfMoment B (sourceDepth B ζ ((q t)^3*Real.log (n t))) (n t)
        (sourceDepth B ζ ((q t)^3*Real.log (n t))))) := by
  filter_upwards [source_all_levels_eventually B ζ hB hζ hn hq hH] with t ht
  simpa only [SourceLevelPair,sourceTargetScale_top] using ht _ le_rfl

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

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Restoration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Restoration

Restoration to honest complete traces, degradation to the requested channel, and exact-length padding.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical

namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

theorem approximate_hellinger_transfer (P Q : FiniteLaw α) (K : α→FiniteLaw β)
    (R S : FiniteLaw β) {E V : ℝ} (hH : P.hellingerSq Q ≤ V)
    (hR : R.tv (P.bind K) ≤ E) (hS : S.tv (Q.bind K) ≤ E) (m : ℕ) :
    (R.product m).tv (S.product m) ≤ Real.sqrt ((m:ℝ)*V)+2*m*E := by
  have hmid := (tv_le_sqrt_hellingerSq ((P.bind K).product m) ((Q.bind K).product m)).trans
    (Real.sqrt_le_sqrt ((hellingerSq_product_le _ _ m).trans
      (mul_le_mul_of_nonneg_left ((hellingerSq_bind_le P Q K).trans hH) (Nat.cast_nonneg m))))
  have hr := (tv_product_le R (P.bind K) m).trans (mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg m))
  have hs := (tv_product_le S (Q.bind K) m).trans (mul_le_mul_of_nonneg_left hS (Nat.cast_nonneg m))
  rw [tv_symm (S.product m)] at hs
  linarith only [hr,hs,hmid,tv_triangle (R.product m) ((P.bind K).product m) (S.product m),
    tv_triangle ((P.bind K).product m) ((Q.bind K).product m) (S.product m)]

end FiniteLaw

theorem boundedTraceProjection_val {n : ℕ} {w : List Bool} (hw : w.length ≤ n) :
    (boundedTraceProjection n w).val=w := by
  simp only [boundedTraceProjection,dite_eq_left (mem_traceSpace_of_length_le w hw)]

theorem listTraceLaw_projection (q : ℝ) (hq : q∈Set.Icc 0 1) (w : List Bool)
    (n : ℕ) (hw : w.length≤n) (f : BoundedTrace n→ℝ) :
    (listTraceLaw q hq w n hw).expect f=
      listDeletionExpectation q w (fun z=>f (boundedTraceProjection n z)) := by
  rw [←listTraceLaw_expect q hq w n hw]
  congr 1
  funext t
  congr 1
  apply Subtype.ext
  exact (boundedTraceProjection_val (length_le_of_mem_traceSpace t.property)).symm

theorem ApproximatesTrace.projected_tv {α : Type*} [Fintype α] {q E : ℝ}
    {P : FiniteLaw α} {decode : α→List Bool} {w : List Bool}
    (H : ApproximatesTrace q P decode w E) (hq : q∈Set.Icc 0 1)
    (n : ℕ) (hw : w.length≤n) :
    (listTraceLaw q hq w n hw).tv (P.map (fun a=>boundedTraceProjection n (decode a))) ≤ E := by
  apply FiniteLaw.tv_le_of_tests
  intro f hf
  rw [listTraceLaw_projection,FiniteLaw.expect_map]
  simp only [Function.comp_def]
  have hh := H (fun z=>f (boundedTraceProjection n z)) (fun z=>hf _)
  linarith only [(abs_le.mp hh).1]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Independent deletion composes on the actual complete output list. -/
theorem listDeletionExpectation_comp (r t : ℝ) (w : List Bool) (F : List Bool→ℝ) :
    listDeletionExpectation r w (fun z=>listDeletionExpectation t z F)=
      listDeletionExpectation (r+(1-r)*t) w F := by
  induction w generalizing F with
  | nil => rfl
  | cons b w ih =>
    simp only [listDeletionExpectation]
    rw [listDeletionExpectation_linear,ih,ih]
    ring

theorem extraDeletion_comp {r q : ℝ} (hr : r<1) : r+(1-r)*extraDeletion r q=q := by
  unfold extraDeletion
  field_simp [(sub_pos.mpr hr).ne']
  ring

theorem listTraceLaw_degrade {r q : ℝ} (hr : r∈Set.Ico 0 1) (hq : q∈Set.Icc 0 1)
    (hrq : r≤q) (w : List Bool) (n : ℕ) (hw : w.length≤n) :
    listTraceLaw q hq w n hw=(listTraceLaw r ⟨hr.1,hr.2.le⟩ w n hw).bind
      (fun z=>listTraceLaw (extraDeletion r q) (extraDeletion_bounds hr.2 hrq hq.2)
        z.val n (length_le_of_mem_traceSpace z.property)) := by
  apply FiniteLaw.ext_expect
  intro f
  rw [FiniteLaw.expect_bind]
  simp_rw [listTraceLaw_projection]
  rw [listTraceLaw_expect r ⟨hr.1,hr.2.le⟩ w n hw
    (fun z=>listDeletionExpectation (extraDeletion r q) z (fun u=>f (boundedTraceProjection n u))),
    listDeletionExpectation_comp,extraDeletion_comp hr.2]

/-- The requested higher-deletion channel preserves the exact m-sample
 restoration estimate, through one common per-sample Markov kernel. -/
theorem HellingerTracePair.degraded_sample_tv {r q E V : ℝ} {x y : List Bool}
    (C : HellingerTracePair r x y E V) (hr : r∈Set.Ico 0 1) (hq : q∈Set.Icc 0 1)
    (hrq : r≤q) (m n : ℕ) (hx : x.length≤n) (hy : y.length≤n) :
    ((listTraceLaw q hq x n hx).product m).tv ((listTraceLaw q hq y n hy).product m) ≤
      Real.sqrt ((m:ℝ)*V)+2*m*E := by
  let := C.finiteOutcome
  let K : BoundedTrace n→FiniteLaw (BoundedTrace n) := fun z=>
    listTraceLaw (extraDeletion r q) (extraDeletion_bounds hr.2 hrq hq.2)
      z.val n (length_le_of_mem_traceSpace z.property)
  let f := fun z=>boundedTraceProjection n (C.decode z)
  have hP := C.first_simulation.projected_tv ⟨hr.1,hr.2.le⟩ n hx
  have hQ := C.second_simulation.projected_tv ⟨hr.1,hr.2.le⟩ n hy
  have hp := (FiniteLaw.tv_bind_le (listTraceLaw r ⟨hr.1,hr.2.le⟩ x n hx) (C.first.map f) K).trans hP
  have hq' := (FiniteLaw.tv_bind_le (listTraceLaw r ⟨hr.1,hr.2.le⟩ y n hy) (C.second.map f) K).trans hQ
  rw [←listTraceLaw_degrade hr hq hrq x n hx,FiniteLaw.bind_map] at hp
  rw [←listTraceLaw_degrade hr hq hrq y n hy,FiniteLaw.bind_map] at hq'
  exact FiniteLaw.approximate_hellinger_transfer C.first C.second (fun z=>K (f z)) _ _ C.bound hp hq' m

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem ofFn_wordOfLength {n : ℕ} (w : List Bool) (h : w.length=n) :
    List.ofFn (wordOfLength w h)=w := by
  subst n
  exact List.ofFn_get w

theorem listTraceLaw_ofFn {n : ℕ} (q : ℝ) (hq : q∈Set.Icc 0 1) (x : Word n) :
    listTraceLaw q hq (List.ofFn x) n (by simp)=completeTraceLaw q hq x := by
  apply FiniteLaw.ext_expect
  intro f
  rw [listTraceLaw_projection,listDeletionExpectation_ofFn,completeTraceLaw_mask,FiniteLaw.expect_map]
  unfold FiniteLaw.expect maskLaw
  apply Finset.sum_congr rfl
  intro a _
  congr 2
  apply Subtype.ext
  exact boundedTraceProjection_val (traceOfMask_length_le x a)

theorem listTraceLaw_wordOfLength {n : ℕ} (q : ℝ) (hq : q∈Set.Icc 0 1)
    (w : List Bool) (hw : w.length=n) :
    listTraceLaw q hq w n hw.le=completeTraceLaw q hq (wordOfLength w hw) := by
  have hh := listTraceLaw_ofFn q hq (wordOfLength w hw)
  simpa only [ofFn_wordOfLength] using hh

/-- Literal exact-length padding and degradation of a level witness. -/
theorem ConcreteLevelPair.restored_words {r q N Δ d ω F : ℝ} {hr : r∈Set.Icc 0 1}
    {i k : ℕ} (U : ConcreteLevelPair r hr N Δ d ω F i k)
    (hr1 : r<1) (hq : q∈Set.Icc 0 1) (hrq : r≤q) (hk : 1≤k)
    (n : ℕ) (hN : N≤n) :
    ∃x y : Word n,x≠y ∧ ∀m : ℕ,
      ((completeTraceLaw q hq x).product m).tv ((completeTraceLaw q hq y).product m) ≤
        Real.sqrt ((m:ℝ)*N^(-d))+2*m*U.error := by
  have hlen : U.left.length≤n := by exact_mod_cast U.length_upper.trans hN
  let tail := List.replicate (n-U.left.length) false
  let x := U.left++tail
  let y := U.right++tail
  have hx : x.length=n := by simp only [x,tail,List.length_append,List.length_replicate]; omega
  have hy : y.length=n := by simp only [y,tail,List.length_append,List.length_replicate,←U.equalLength]; omega
  have hxy : x≠y := fun h=>U.different (List.append_cancel_right h)
  let C := (U.oracle.pad hr [] tail).hellinger hk
  refine ⟨wordOfLength x hx,wordOfLength y hy,?_,?_⟩
  · intro hh
    have hh' := congrArg List.ofFn hh
    rw [ofFn_wordOfLength,ofFn_wordOfLength] at hh'
    exact hxy hh'
  · intro m
    have HH := C.degraded_sample_tv ⟨hr.1,hr1⟩ hq hrq m n
      (by simpa only [List.nil_append] using hx.le) (by simpa only [List.nil_append] using hy.le)
    change ((listTraceLaw q hq x n hx.le).product m).tv ((listTraceLaw q hq y n hy.le).product m) ≤ _ at HH
    rw [listTraceLaw_wordOfLength q hq x hx,listTraceLaw_wordOfLength q hq y hy] at HH
    exact HH

end TraceReconstruction

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Bounds

Restored construction and final scales; quantitative sample lower bound and both fixed-channel superpolynomial endpoints.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

/-- The exact source error is negligible compared to the squared score energy. -/
theorem source_final_error_eventually (B : ℕ) (ζ : ℝ) (hB : 2≤B) (hζ : ζ∈Set.Ioo 0 1)
    {n q : ℕ→ℝ} (hn : Tendsto n atTop atTop) (hq : ∀t,q t∈Set.Ioc 0 (1/2:ℝ))
    (hH : Tendsto (fun t=>(q t)^3*Real.log (n t)) atTop atTop) :
    ∀ᶠt in atTop,∀ (U : ConcreteLevelPair (q t) ⟨(hq t).1.le,by linarith [(hq t).2]⟩ (n t)
      ((n t)^(-100*(totalScoreExponent B (sourceDepth B ζ ((q t)^3*Real.log (n t)))+B+1)))
      (totalScoreExponent B (sourceDepth B ζ ((q t)^3*Real.log (n t))))
      (initialOverlapLower (q t))
      ((sourceOverlapConstant (q t))^(2*B*sourceDepth B ζ ((q t)^3*Real.log (n t))+2))
      (sourceDepth B ζ ((q t)^3*Real.log (n t)))
      (sourceHalfMoment B (sourceDepth B ζ ((q t)^3*Real.log (n t))) (n t)
        (sourceDepth B ζ ((q t)^3*Real.log (n t))))),
      U.error≤(n t)^(-2*totalScoreExponent B (sourceDepth B ζ ((q t)^3*Real.log (n t)))) := by
  have ht := SourceExpUpper.uniform (fun D _=>(D:ℝ)+1) SourcePolyUpper.depth.expUpper
    B ζ 1 hB hζ zero_lt_one hn hq hH
  filter_upwards [ht,hn.eventually_ge_atTop 2] with t ht hn2 U
  let D := sourceDepth B ζ ((q t)^3*Real.log (n t))
  let d := totalScoreExponent B D
  have hn0 : 0<n t := by linarith only [hn2]
  have hn1 : 1≤n t := by linarith only [hn2]
  have hD : (D:ℝ)+1≤n t := by
    have hh := ht D
    rw [sourceTargetScale_top,one_mul] at hh
    exact hh.trans (by simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hn1 (sourceEpsilon_le_one B D))
  have hd : 11/5≤d := (totalScoreExponent_bounds B D hB).1
  calc
    U.error ≤ ((D:ℝ)+1)*(n t)^(-100*(d+B+1))*n t := U.error_le hn0 (Real.rpow_nonneg hn0.le _)
    _ ≤ (n t)*(n t)^(-100*(d+B+1))*n t := by gcongr
    _ = (n t)^(-100*(d+B+1)+2) := by
      rw [Real.rpow_add hn0,Real.rpow_two]
      ring
    _ ≤ (n t)^(-2*d) := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith [Nat.cast_nonneg B (α:=ℝ)])

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

theorem workingDeletion_Ioc {q : ℝ} (hq : q∈Set.Ioo 0 1) :
    workingDeletion q ∈Set.Ioc 0 (1/2:ℝ) :=
  ⟨(workingDeletion_bounds hq).1.1,min_le_right _ _⟩

end TraceReconstruction


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical ENNReal

namespace FiniteLaw
variable {α : Type*} [Fintype α]
theorem tv_product_one (P Q : FiniteLaw α) : (P.product 1).tv (Q.product 1)=P.tv Q := by
  rw [show 1=0+1 from rfl,tv_product_succ]
  simp only [tv,tensor,product,Fintype.sum_prod_type,Fintype.prod_empty,mul_one,Fintype.sum_unique]
end FiniteLaw

theorem totalScoreExponent_two (D : ℕ) : totalScoreExponent 2 D=11/5+(D:ℝ)/5 := by
  simp only [totalScoreExponent,ite_self,blockGain_two,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  ring

theorem minTraceTV_nonneg_of_pair {n : ℕ} (q : ℝ) (x y : Word n) (hxy : x≠y) :
    0 ≤ minTraceTV n q := by
  apply le_csInf (show {t | ∃x y : Word n,x≠y ∧ t=traceTV q x y}.Nonempty from
    ⟨_,x,y,hxy,rfl⟩)
  rintro b ⟨u,v,_,rfl⟩
  exact traceTV_nonneg q u v

theorem minTraceTV_le_pair {n : ℕ} (q : ℝ) (x y : Word n) (hxy : x≠y) :
    minTraceTV n q ≤ traceTV q x y := by
  apply csInf_le (show BddBelow {t | ∃x y : Word n,x≠y ∧ t=traceTV q x y} from ?_) ⟨x,y,hxy,rfl⟩
  exact ⟨0,by rintro b ⟨u,v,_,rfl⟩; exact traceTV_nonneg q u v⟩

theorem one_trace_power_bound {N d C R : ℝ} (hN : 1 ≤ N) (hC : 0<C)
    (hd : 2*(C+1) ≤ d) (hR : R ≤ Real.sqrt (N^(-d))+2*N^(-2*d)) :
    N^C*R ≤ 3/N := by
  have hN0 : 0<N := by linarith only [hN]
  have he : (N^(-(C+1)))^2=N^(-2*(C+1)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hN0.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  have hs : Real.sqrt (N^(-d)) ≤ N^(-(C+1)) := by
    apply (Real.sqrt_le_left (Real.rpow_nonneg hN0.le _)).mpr
    rw [he]
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith only [hd])
  have herr : N^(-2*d) ≤ N^(-(C+1)) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith only [hd,hC])
  calc
    N^C*R ≤ N^C*(3*N^(-(C+1))) :=
      mul_le_mul_of_nonneg_left (by linarith only [hR,hs,herr]) (Real.rpow_nonneg hN0.le _)
    _ = 3/N := by
      rw [mul_left_comm,←Real.rpow_add hN0]
      rw [show C+ -(C+1)=(-1:ℝ) by ring,Real.rpow_neg_one]
      ring

/-- Source Theorem 2, first conclusion, over all integer lengths and at the
 same fixed channel for every power. -/
theorem superpolynomial_one_trace_oai
    (q : ℝ) (hq : q ∈ Set.Ioo 0 1) (C : ℝ) (hC : 0<C) :
    Tendsto (fun n : ℕ=>(n:ℝ)^C*minTraceTV n q) atTop (𝓝 0) := by
  let r := workingDeletion q
  have hr : r∈Set.Ioc 0 (1/2:ℝ) := workingDeletion_Ioc hq
  have hn : Tendsto (fun n : ℕ=>(n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hJ : Tendsto (fun n : ℕ=>r^3*Real.log (n:ℝ)) atTop atTop :=
    (Real.tendsto_log_atTop.comp hn).const_mul_atTop (pow_pos hr.1 3)
  have hpair := source_final_pair_eventually 2 (1/2) (by omega) (by norm_num) hn (fun _=>hr) hJ
  have herr := source_final_error_eventually 2 (1/2) (by omega) (by norm_num) hn (fun _=>hr) hJ
  obtain ⟨D0,hD0⟩ := exists_nat_ge (5*(2*(C+1)))
  have hdepth := (sourceDepth_tendsto 2 (1/2) (by omega) (by norm_num) hJ).eventually_ge_atTop D0
  have hb : ∀ᶠ n : ℕ in atTop,0 ≤ (n:ℝ)^C*minTraceTV n q ∧
      (n:ℝ)^C*minTraceTV n q ≤ 3/(n:ℝ) := by
    filter_upwards [hpair,herr,hdepth,hn.eventually_ge_atTop 2] with n hp he hD hn2
    obtain ⟨U⟩ := hp
    have hn1 : 1<(n:ℝ) := by linarith only [hn2]
    have hk := (sourceHalfMoment_bounds 2
      (sourceDepth 2 (1/2) (r^3*Real.log (n:ℝ)))
      (sourceDepth 2 (1/2) (r^3*Real.log (n:ℝ))) (by omega) hn1).1
    obtain ⟨x,y,hxy,hTV⟩ := U.restored_words (by linarith only [hr.2])
      ⟨hq.1.le,hq.2.le⟩ (workingDeletion_bounds hq).2.2 hk n le_rfl
    have ht := hTV 1
    rw [FiniteLaw.tv_product_one] at ht
    rw [completeTraceLaw_tv q ⟨hq.1.le,hq.2.le⟩ x y] at ht
    norm_num only [Nat.cast_one,one_mul,mul_one] at ht
    have hd : 2*(C+1) ≤ totalScoreExponent 2 (sourceDepth 2 (1/2) (r^3*Real.log (n:ℝ))) := by
      rw [totalScoreExponent_two]
      have hDD : (D0:ℝ) ≤ (sourceDepth 2 (1/2) (r^3*Real.log (n:ℝ)):ℝ) := by exact_mod_cast hD
      linarith only [hD0,hDD]
    refine ⟨mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (minTraceTV_nonneg_of_pair q x y hxy),?_⟩
    apply (mul_le_mul_of_nonneg_left (minTraceTV_le_pair q x y hxy)
      (Real.rpow_nonneg (Nat.cast_nonneg n) C)).trans
    apply one_trace_power_bound hn1.le hC hd
    linarith only [ht,he U]
  exact squeeze_zero' (hb.mono fun _ h=>h.1) (hb.mono fun _ h=>h.2) (hn.const_div_atTop 3)

end TraceReconstruction


end
end
end
end
end
end

end OAI
end

theorem solution : type_of% @OAI.TraceReconstruction.superpolynomial_one_trace_oai := @OAI.TraceReconstruction.superpolynomial_one_trace_oai
