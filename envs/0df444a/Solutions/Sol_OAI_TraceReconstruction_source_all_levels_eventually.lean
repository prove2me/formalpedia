-- Prove2me | solution 1 for OAI.TraceReconstruction.source_all_levels_eventually
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T09:59:53.483856+00:00
-- url     : https://prove2.me/submissions/f9084175-9dc1-4062-a931-2f0fd9c49d9f

import Mathlib
import Definitions.Def_OAIQ9Tr002
import Theorems.Thm_OAI_TraceReconstruction_actual_source_oracle
import Theorems.Thm_OAI_TraceReconstruction_source_initial_level_eventually
import Theorems.Thm_OAI_TraceReconstruction_source_level_all_budgets
import Theorems.Thm_OAI_TraceReconstruction_source_level_overlap

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

theorem atomString_cons (P : ℕ) (w : Bool → List Bool) (θ : Fin (P + 1) → Bool) :
    atomString (P + 1) w θ = w (θ 0) ++ atomString P w (fun i => θ i.succ) := by
  simp only [atomString, List.ofFn_succ, List.flatten_cons]

theorem atomString_length (P S : ℕ) (w : Bool → List Bool) (hw : ∀ b, (w b).length = S)
    (θ : Fin P → Bool) : (atomString P w θ).length = P * S := by
  induction P with
  | zero => simp [atomString]
  | succ P ih => rw [atomString_cons, List.length_append, hw, ih, Nat.add_mul, one_mul, Nat.add_comm]

theorem atomString_injective (P S : ℕ) (w : Bool → List Bool)
    (hw : ∀ b, (w b).length = S) (hinj : Function.Injective w) :
    Function.Injective (atomString P w) := by
  induction P with
  | zero => intro θ φ _; exact Subsingleton.elim _ _
  | succ P ih =>
    intro θ φ h
    rw [atomString_cons, atomString_cons] at h
    have hh := congrArg (List.take S) h
    have hθ (u : List Bool) (b : Bool) : (w b ++ u).take S = w b := by
      rw [← hw b, List.take_left]
    rw [hθ, hθ] at hh
    have hz := hinj hh
    rw [hz] at h
    have ht := ih (List.append_cancel_left h)
    funext i
    exact Fin.cases hz (fun j => congrFun ht j) i

theorem templateType_at (P a L : ℕ) (sign : Fin L → Bool) (τ : Bool)
    (hL : 0 < L) (ha : a < P) :
    templateType P a L sign τ ⟨a, ha⟩ = xor τ (sign ⟨0, hL⟩) := by
  simp [templateType, hL]

theorem templateType_injective (P a L : ℕ) (sign : Fin L → Bool)
    (hL : 0 < L) (ha : a < P) :
    Function.Injective (templateType P a L sign) := by
  intro τ υ h
  have he := congrFun h ⟨a, ha⟩
  rw [templateType_at P a L sign τ hL ha, templateType_at P a L sign υ hL ha] at he
  cases hs : sign ⟨0, hL⟩ <;> cases τ <;> cases υ <;> simp_all

theorem complementaryWords_length (P a L S : ℕ) (sign : Fin L → Bool)
    (w : Bool → List Bool) (hw : ∀ b, (w b).length = S) (τ : Bool) :
    (complementaryWords P a L sign w τ).length = P * S := atomString_length P S w hw _

theorem complementaryWords_injective (P a L S : ℕ) (sign : Fin L → Bool)
    (w : Bool → List Bool) (hw : ∀ b, (w b).length = S) (hinj : Function.Injective w)
    (hL : 0 < L) (ha : a < P) : Function.Injective (complementaryWords P a L sign w) :=
  (atomString_injective P S w hw hinj).comp (templateType_injective P a L sign hL ha)
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

theorem scaleA_top (b : ℕ) (ε : ℝ) : scaleA b b ε = 1 := by
  unfold scaleA
  field_simp
  ring

theorem scaleA_step (b j : ℕ) (ε : ℝ) : scaleA b (j+1) ε - 2*scaleA b j ε = ε := by
  unfold scaleA
  rw [pow_succ]
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

/-- Joint-regime uniform absorption at the genuine backwards scales,
 with an arbitrary index choice and with the channel unchanged across scales. -/
theorem source_uniform_absorption (B h : ℕ) (ζ : ℝ) (hB : 2 ≤ B) (hζ : ζ∈Set.Ioo 0 1)
    {n Λ H : ℕ → ℝ} (i : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hH : Tendsto H atTop atTop)
    (hΛ : ∀k,0 < Λ k) (hrel : ∀k,Real.log (n k)=Λ k*H k) :
    Tendsto (fun k => ((sourceDepth B ζ (H k):ℝ)+1)^h*Λ k /
      (sourceEpsilon B (sourceDepth B ζ (H k))*
        Real.log (sourceTargetScale B (sourceDepth B ζ (H k)) (n k) (i k)))) atTop (nhds 0) := by
  have hb := (sourceDepth_polynomial_absorption B (h+1) ζ hB hζ hH).const_mul
    (2*(2:ℝ)^(4*B+100))
  simp only [mul_zero] at hb
  apply squeeze_zero' _ _ hb
  · filter_upwards [hH.eventually_ge_atTop 1,hn.eventually_gt_atTop 1] with k hk hnk
    have hh := sourceTargetScale_epsilon_log_lower B ζ (H k) (n k) (Λ k) (i k)
      hB hζ.2.le hk hnk (hΛ k) (hrel k)
    have hΛk := hΛ k
    have hHk : 0 < H k := by linarith
    exact div_nonneg (by positivity) ((by positivity :
      0 ≤ Λ k*(H k)^ζ/(2*(2:ℝ)^(4*B+100)*((sourceDepth B ζ (H k):ℝ)+1))).trans hh)
  · filter_upwards [hH.eventually_ge_atTop 1,hn.eventually_gt_atTop 1] with k hk hnk
    exact source_absorption_ratio_bound B h ζ (H k) (n k) (Λ k) (i k)
      hB hζ.2.le hk hnk (hΛ k) (hrel k)

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
-- module Solutions.OAIQ9_TR.TraceReconstruction_Layout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Layout

Multiwindow and paired layouts, coordinate simulations, and literal source types and trees.
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
open scoped Classical

theorem sourceBlockWord_length (s : ℕ) (P : ℕ → ℕ) (atom : Bool → List Bool) (S : ℕ)
    (hw : ∀τ,(atom τ).length=S) (j : ℕ) (τ : Bool) :
    (sourceBlockWord s P atom j τ).length=sourceBlockLength P S j := by
  induction j generalizing τ with
  | zero => exact hw τ
  | succ j ih => exact complementaryWords_length _ _ _ _ _ _ (fun τ => ih τ) τ

theorem sourceBlockWord_injective (s : ℕ) (P : ℕ → ℕ) (atom : Bool → List Bool) (S : ℕ)
    (hw : ∀τ,(atom τ).length=S) (hinj : Function.Injective atom) (j : ℕ)
    (hP : ∀k<j,0<P k) : Function.Injective (sourceBlockWord s P atom j) := by
  induction j with
  | zero => exact hinj
  | succ j ih =>
    apply complementaryWords_injective _ _ _ (sourceBlockLength P S j)
      _ _ (sourceBlockWord_length s P atom S hw j)
    · exact ih (fun k hk => hP k (by omega))
    · positivity
    · have h := hP j (Nat.lt_succ_self j); omega

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

theorem sourceEpsilon_le_one (B D : ℕ) : sourceEpsilon B D ≤ 1 := by
  unfold sourceEpsilon
  apply (div_le_one (by positivity)).mpr
  have H : (1:ℝ) ≤ 2^(4*B+100) := one_le_pow₀ (by norm_num)
  nlinarith [show (0:ℝ) ≤ D by positivity]

theorem sourceTargetScale_tendsto (B : ℕ) (ζ : ℝ) (hB : 2 ≤ B) (hζ : ζ∈Set.Ioo 0 1)
    {n Λ H : ℕ→ℝ} (i : ℕ→ℕ) (hn : Tendsto n atTop atTop) (hH : Tendsto H atTop atTop)
    (hΛ : ∀t,1 ≤ Λ t) (hrel : ∀t,Real.log (n t)=Λ t*H t) :
    Tendsto (fun t=>sourceTargetScale B (sourceDepth B ζ (H t)) (n t) (i t)) atTop atTop := by
  have hlog : Tendsto (fun t=>Real.log (sourceTargetScale B (sourceDepth B ζ (H t)) (n t) (i t))) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ (((tendsto_rpow_atTop hζ.1).comp hH).atTop_div_const (by norm_num : (0:ℝ)<2))
    filter_upwards [hH.eventually_ge_atTop 1,hn.eventually_gt_atTop 1] with t ht hnt
    have hl := sourceTargetScale_log_lower B ζ (H t) (n t) (i t) hB hζ.2.le ht hnt
    have he : Real.log (n t)/(2*(H t)^(1-ζ))=Λ t*(H t)^ζ/2 := by
      rw [hrel t,Real.rpow_sub (by linarith : 0<H t),Real.rpow_one]
      have hp : (H t)^ζ ≠ 0 := (Real.rpow_pos_of_pos (by linarith : 0<H t) _).ne'
      field_simp
    rw [he] at hl
    exact (by nlinarith [hΛ t,Real.rpow_nonneg (by linarith : 0 ≤ H t) ζ] : (H t)^ζ/2 ≤ Λ t*(H t)^ζ/2).trans hl
  apply tendsto_atTop_mono' atTop _ hlog
  filter_upwards [hn.eventually_gt_atTop 1] with t ht
  exact Real.log_le_self (Real.rpow_nonneg (by linarith : 0 ≤ n t) _)

theorem source_uniform_log_absorption (B h : ℕ) (ζ : ℝ) (hB : 2 ≤ B) (hζ : ζ∈Set.Ioo 0 1)
    {n Λ H : ℕ→ℝ} (i : ℕ→ℕ) (hn : Tendsto n atTop atTop) (hH : Tendsto H atTop atTop)
    (hΛ : ∀t,1 ≤ Λ t) (hrel : ∀t,Real.log (n t)=Λ t*H t) :
    Tendsto (fun t=>((sourceDepth B ζ (H t):ℝ)+1)^h*Λ t/
      Real.log (sourceTargetScale B (sourceDepth B ζ (H t)) (n t) (i t))) atTop (𝓝 0) := by
  have hh := source_uniform_absorption B h ζ hB hζ i hn hH (fun t=>lt_of_lt_of_le (by norm_num) (hΛ t)) hrel
  apply squeeze_zero' _ _ hh
  · filter_upwards [(sourceTargetScale_tendsto B ζ hB hζ i hn hH hΛ hrel).eventually_gt_atTop 1] with t ht
    exact div_nonneg (mul_nonneg (by positivity) (by linarith [hΛ t])) (Real.log_pos ht).le
  · filter_upwards [(sourceTargetScale_tendsto B ζ hB hζ i hn hH hΛ hrel).eventually_gt_atTop 1] with t ht
    apply div_le_div_of_nonneg_left (by positivity [hΛ t])
      (mul_pos (sourceEpsilon_pos _ _) (Real.log_pos ht))
    exact mul_le_of_le_one_left (Real.log_pos ht).le (sourceEpsilon_le_one _ _)

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
namespace TraceReconstruction
open Filter
open scoped Topology Classical

/-- The exact varying even moment order is subpower at EVERY working scale. -/
theorem sourceHalfMoment_rate (B : ℕ) (ζ : ℝ) (hB : 2 ≤ B) (hζ : ζ∈Set.Ioo 0 1)
    {n Λ H : ℕ→ℝ} (i : ℕ→ℕ) (hn : Tendsto n atTop atTop) (hH : Tendsto H atTop atTop)
    (hΛ : ∀t,1 ≤ Λ t) (hrel : ∀t,Real.log (n t)=Λ t*H t) :
    PowerRate (fun t=>sourceTargetScale B (sourceDepth B ζ (H t)) (n t) (i t))
      (fun t=>(sourceHalfMoment B (sourceDepth B ζ (H t)) (n t) (i t):ℝ)) 0 := by
  let C : ℝ := ((10^8:ℝ)*2^(10*B)*((B:ℝ)+4)*2+1)
  let A : ℝ := C+1+(B:ℝ)*Real.log 2
  have hC : 0<C := by dsimp [C]; positivity
  have hA : 0<A := by dsimp [A]; positivity
  have hscale := sourceTargetScale_tendsto B ζ hB hζ i hn hH hΛ hrel
  have hlim := (source_uniform_log_absorption B 1 ζ hB hζ i hn hH hΛ hrel).const_mul A
  simp only [pow_one,mul_zero] at hlim
  refine ⟨?_,?_⟩
  · filter_upwards [hn.eventually_gt_atTop 1] with t ht
    have hk := (sourceHalfMoment_bounds B (sourceDepth B ζ (H t)) (i t) hB ht).1
    exact_mod_cast (show 0 < sourceHalfMoment B (sourceDepth B ζ (H t)) (n t) (i t) by omega)
  apply squeeze_zero' _ _ hlim
  · filter_upwards [hn.eventually_gt_atTop 1,hscale.eventually_gt_atTop 1] with t ht hs
    have hk := (sourceHalfMoment_bounds B (sourceDepth B ζ (H t)) (i t) hB ht).1
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hk)) (Real.log_pos hs).le
  · filter_upwards [hn.eventually_gt_atTop 1,hscale.eventually_gt_atTop 1] with t ht hs
    let D := sourceDepth B ζ (H t)
    let k := sourceHalfMoment B D (n t) (i t)
    have hk := sourceHalfMoment_bounds B D (i t) hB ht
    have hkpos : 0<(k:ℝ) := by exact_mod_cast (show 0<k by dsimp [k]; omega)
    have hlog := Real.log_le_log hkpos hk.2
    change Real.log (k:ℝ) ≤ Real.log (C*((D:ℝ)+1)*2^(B*D)) at hlog
    rw [Real.log_mul (mul_pos hC (by positivity)).ne' (by positivity),
      Real.log_mul hC.ne' (by positivity),Real.log_pow] at hlog
    have hD : Real.log ((D:ℝ)+1) ≤ D := by
      simpa using Real.log_le_sub_one_of_pos (by positivity : (0:ℝ)<(D:ℝ)+1)
    have hc := Real.log_le_sub_one_of_pos hC
    have hb : 0 ≤ (B:ℝ)*Real.log 2 := by positivity
    have hd : 0 ≤ (D:ℝ) := Nat.cast_nonneg _
    have hl : Real.log (k:ℝ) ≤ A*((D:ℝ)+1) := by
      dsimp [A]
      push_cast at hlog
      nlinarith
    have hl' : Real.log (k:ℝ) ≤ A*((D:ℝ)+1)*Λ t :=
      hl.trans (le_mul_of_one_le_right (by positivity) (hΛ t))
    have HH := div_le_div_of_nonneg_right hl' (Real.log_pos hs).le
    simpa only [mul_div_assoc,mul_assoc] using HH

end TraceReconstruction


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

theorem sourceTargetScale_le (B D i : ℕ) (n : ℝ) (hB : 2 ≤ B) (hn : 1 ≤ n) :
    sourceTargetScale B D n i ≤ n := by
  simpa only [sourceTargetScale,Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn (sourceScaleProduct_le_one B D i hB)

theorem sourceHalfMoment_sufficient (B D i : ℕ) {n : ℝ} (hB : 2 ≤ B) (hn : 1 < n) :
    10^6*(totalScoreExponent B D+B+1)*Real.log n ≤
      (sourceHalfMoment B D n i:ℝ)*Real.log (sourceTargetScale B D n i) := by
  have hlo := sourceScaleProduct_lower B D i hB
  have hs : 0 < sourceScaleProduct B D i := lt_of_lt_of_le (by positivity) hlo
  have hl : 0 < Real.log (sourceTargetScale B D n i) := by
    rw [sourceTargetScale,Real.log_rpow (by linarith : 0<n)]
    exact mul_pos hs (Real.log_pos hn)
  have hk := (div_le_iff₀ hl).mp (Nat.le_ceil
    ((10^8:ℝ)*2^(10*B)*(totalScoreExponent B D+B+1)*Real.log n/
      Real.log (sourceTargetScale B D n i)))
  apply le_trans _ hk
  have hd := (totalScoreExponent_bounds B D hB).1
  have hA : 0 ≤ (totalScoreExponent B D+B+1)*Real.log n := by positivity [hd,Real.log_pos hn]
  have hp : (1:ℝ) ≤ 2^(10*B) := one_le_pow₀ (by norm_num)
  have hc : (10^6:ℝ) ≤ 10^8*2^(10*B) := by linarith only [hp]
  nlinarith only [mul_le_mul_of_nonneg_right hc hA]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

/-- The source base invariant, with literal target scales, moment ceiling,
 error threshold, count and overlap, uniformly in the joint deletion regime. -/
theorem source_initial_at_smallest_scale (B : ℕ) (ζ : ℝ) (hB : 2 ≤ B)
    (hζ : ζ∈Set.Ioo 0 1) {n q : ℕ→ℝ} (hn : Tendsto n atTop atTop)
    (hq : ∀t,q t∈Set.Ioc 0 (1/2:ℝ))
    (hH : Tendsto (fun t=>(q t)^3*Real.log (n t)) atTop atTop) :
    ∀ᶠt in atTop,Nonempty (ConcreteLevelPair (q t) ⟨(hq t).1.le,by linarith [(hq t).2]⟩
      (sourceTargetScale B (sourceDepth B ζ ((q t)^3*Real.log (n t))) (n t) 0)
      ((n t)^(-100*(totalScoreExponent B (sourceDepth B ζ ((q t)^3*Real.log (n t)))+B+1)))
      (11/5) (initialOverlapLower (q t)) ((sourceOverlapConstant (q t))^2) 0
      (sourceHalfMoment B (sourceDepth B ζ ((q t)^3*Real.log (n t))) (n t) 0)) := by
  let H := fun t=>(q t)^3*Real.log (n t)
  let Λ := fun t=>(q t)^(-3:ℤ)
  have hΛ (t) : 1 ≤ Λ t := by
    dsimp [Λ]
    rw [zpow_neg,zpow_ofNat,one_le_inv₀ (pow_pos (hq t).1 _)]
    exact pow_le_one₀ (hq t).1.le (by linarith [(hq t).2])
  have hrel (t) : Real.log (n t)=Λ t*H t := by
    dsimp [Λ,H]
    rw [zpow_neg,zpow_ofNat]
    field_simp [(hq t).1.ne']
  let D := fun t=>sourceDepth B ζ (H t)
  let N := fun t=>sourceTargetScale B (D t) (n t) 0
  have hN := sourceTargetScale_tendsto B ζ hB hζ (fun _=>0) hn hH hΛ hrel
  have hl := source_uniform_log_absorption B 0 ζ hB hζ (fun _=>0) hn hH hΛ hrel
  simp only [pow_zero,one_mul] at hl
  have hk := sourceHalfMoment_rate B ζ hB hζ (fun _=>0) hn hH hΛ hrel
  apply source_initial_level_eventually hN hn _ hq hl hk
  · filter_upwards [hn.eventually_gt_atTop 1] with t ht
    exact (sourceHalfMoment_bounds B (D t) 0 hB ht).1
  · filter_upwards [hn.eventually_gt_atTop 1] with t ht
    exact sourceHalfMoment_sufficient B (D t) 0 hB ht
  · filter_upwards [hn.eventually_ge_atTop 1] with t ht
    exact sourceTargetScale_le B (D t) 0 (n t) hB ht
  · filter_upwards [] with t
    have hd := (totalScoreExponent_bounds B (D t) hB).1
    have hbn : (0:ℝ) ≤ B := Nat.cast_nonneg _
    linarith only [hd,hbn]

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

theorem sourceLocalTrials_even (P h : ℕ) : Even (sourceLocalTrials P h) :=
  even_two_mul _

theorem sourceLocalTrials_budget (P h : ℕ) :
    50*sourceLocalTrials P h*(2*h+1) ≤ P := by
  have H := Nat.mul_div_le P (100*(2*h+1))
  unfold sourceLocalTrials
  nlinarith only [H]

theorem sourceLocalTrials_reserves (P T h : ℕ) (hT : 2*T ≤ P) :
    2*sourceLayoutReserve (sourceLocalTrials P h) h ≤ (P-T)/2 ∧
    2*sourceLayoutReserve (sourceLocalTrials P h) h ≤ P-T-(P-T)/2 := by
  have H := sourceLocalTrials_budget P h
  rw [mul_assoc] at H
  have he : sourceLocalTrials P h/2=P/(100*(2*h+1)) := by
    unfold sourceLocalTrials
    omega
  have hr : 2*sourceLayoutReserve (sourceLocalTrials P h) h=
      sourceLocalTrials P h*(2*h+1) := by
    unfold sourceLayoutReserve
    rw [he]
    unfold sourceLocalTrials
    ring
  rw [hr]
  have hm : 2*(sourceLocalTrials P h*(2*h+1)) ≤ P-T := by omega
  constructor <;> omega

theorem sourceWindowSize_even (N : ℝ) (b : ℕ) (ε : ℝ) (j : ℕ) :
    Even (sourceWindowSize N b ε j) := by
  unfold sourceWindowSize
  exact ⟨2*⌊N^(scaleKappa b (j+1) ε)/4⌋₊,by ring⟩

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

theorem sourceArithmetic_root_copies (C N : ℝ) (b : ℕ) (ε : ℝ) (ell k : ℕ) (hb : 1 ≤ b) :
    sourceArithmeticP C N b ε ell k (b-1)=
      sourceArithmeticTrials C N b ε ell k (b-1)*(2*sourceArithmeticCount C N b ε ell k (b-1)+1)+
        sourceWindowSize N b ε (b-1) := by
  simp only [sourceArithmeticP,sourceArithmeticTrials,sourceArithmeticCount,sourceArithmeticStages,
    Nat.sub_add_cancel hb,ite_true]

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

theorem sourceChannelLogConstant_pos : 0 < sourceChannelLogConstant := by
  unfold sourceChannelLogConstant primitivePeriodConstant
  positivity

theorem deletion_inverse_cube_ge_one {q : ℝ} (hq : q∈Set.Ioc 0 1) :
    1 ≤ q^(-3:ℤ) := by
  rw [zpow_neg,zpow_ofNat,one_le_inv₀ (pow_pos hq.1 _)]
  exact pow_le_one₀ hq.1.le hq.2

theorem deletion_inverse_le_cube {q : ℝ} (hq : q∈Set.Ioc 0 1) :
    q⁻¹ ≤ q^(-3:ℤ) := by
  rw [zpow_neg,zpow_ofNat]
  apply inv_anti₀ (pow_pos hq.1 3)
  calc
    q^3=q*q^2 := by ring
    _ ≤ q*1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hq.1.le hq.2) hq.1.le
    _=q := mul_one _

theorem sourceOverlapConstant_log_bound {q : ℝ} (hq : q∈Set.Ioc 0 1) :
    Real.log (sourceOverlapConstant q) ≤ sourceChannelLogConstant*q^(-3:ℤ) := by
  have hΛ := deletion_inverse_cube_ge_one hq
  have hlogq : -Real.log q ≤ q^(-3:ℤ) := (neg_le_neg (Real.neg_inv_le_log hq.1.le)).trans
    (by simpa only [neg_neg] using deletion_inverse_le_cube hq)
  have hω : 0 < initialOverlapLower q := initialOverlapLower_pos q
  have hlogC : Real.log (sourceOverlapConstant q)=
      Real.log ((2:ℝ)^40)+Real.log 1536+(32+3*primitivePeriodConstant)*q^(-3:ℤ)-Real.log q := by
    rw [sourceOverlapConstant,Real.log_div (by positivity) (mul_pos hq.1 hω).ne',
      Real.log_mul hq.1.ne' hω.ne',initialOverlapLower,
      Real.log_div (Real.exp_pos _).ne' (by norm_num),Real.log_exp]
    rw [zpow_neg,zpow_ofNat]
    ring
  rw [hlogC]
  have htwo := Real.log_le_self (by positivity : (0:ℝ) ≤ (2:ℝ)^40)
  have h1536 := Real.log_le_self (by norm_num : (0:ℝ) ≤ 1536)
  have hc := mul_le_mul_of_nonneg_left hΛ (show 0 ≤ (2:ℝ)^40+1536 by positivity)
  unfold sourceChannelLogConstant
  nlinarith only [hlogq,htwo,h1536,hc]

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

theorem SourceArithmeticBounds.layout {C N F ε : ℝ} {s b ell k : ℕ}
    (H : SourceArithmeticBounds C N F ε s b ell k) :
    SourceLayoutMargins s (sourceArithmeticP C N b ε ell k) (sourceBlockWindows N b ε)
      (sourceArithmeticTrials C N b ε ell k) (sourceArithmeticCount C N b ε ell k) (b-1) := by
  constructor
  · intro j hj
    have hh := (H.windows j (by omega)).1
    omega
  · intro j hj
    have hh := (H.windows j (by omega)).1
    omega
  · intro j hj
    rw [sourceBlockWindows,ite_eq_left (by omega)]
    exact sourceWindowSize_even N b ε j
  · intro j hj
    exact (H.windows j (by omega)).2.2.1
  · intro j hj
    have hh := (H.windows j (by omega)).2.1
    omega
  · intro j hj
    rw [sourceArithmetic_inner_trials C N b ε ell k j (by omega)]
    exact sourceLocalTrials_even _ _
  · intro j hj
    rw [sourceArithmetic_inner_trials C N b ε ell k j (by omega)]
    exact (sourceLocalTrials_reserves _ _ _ (H.windows j (by omega)).2.2.1).1
  · intro j hj
    rw [sourceArithmetic_inner_trials C N b ε ell k j (by omega)]
    exact (sourceLocalTrials_reserves _ _ _ (H.windows j (by omega)).2.2.1).2

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

theorem binaryTreeBudget_const (A : ℝ) (b : ℕ) :
    binaryTreeBudget (fun _=>A) b=A^(2^b-1) := by
  induction b with
  | zero => simp [binaryTreeBudget]
  | succ b ih =>
    rw [binaryTreeBudget,ih,←pow_mul,←pow_succ']
    congr 1
    have hp : 1 ≤ 2^b := Nat.one_le_pow b 2 (by omega)
    rw [pow_succ]
    omega

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem sourceSkeletonPrefactor_nonneg (s b : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ sourceSkeletonPrefactor s b K := by
  have h := binaryTreeBudget_nonneg (fun _=>4*((2^s:ℕ):ℝ)^6*K^2) (fun _=>by positivity) b
  unfold sourceSkeletonPrefactor
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

end TraceReconstruction


noncomputable section


noncomputable section


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

theorem SourcePolyUpper.const (c : ℝ) : SourcePolyUpper (fun _=>c) := by
  refine ⟨|c|,abs_nonneg _,0,?_⟩
  intro D
  simpa using le_abs_self c

theorem SourcePolyUpper.depth : SourcePolyUpper (fun D=>(D:ℝ)+1) := by
  exact ⟨1,zero_le_one,1,by simp⟩

theorem SourcePolyUpper.mono {f g : ℕ→ℝ} (hg : SourcePolyUpper g) (hf : ∀D,f D ≤ g D) :
    SourcePolyUpper f := by
  obtain ⟨C,hC,h,H⟩ := hg
  exact ⟨C,hC,h,fun D=>(hf D).trans (H D)⟩

theorem SourcePolyUpper.add {f g : ℕ→ℝ} (hf : SourcePolyUpper f) (hg : SourcePolyUpper g) :
    SourcePolyUpper (fun D=>f D+g D) := by
  obtain ⟨C,hC,h,H⟩ := hf
  obtain ⟨K,hK,k,G⟩ := hg
  refine ⟨C+K,add_nonneg hC hK,h+k,?_⟩
  intro D
  have hd : 1 ≤ (D:ℝ)+1 := by linarith [Nat.cast_nonneg D (α:=ℝ)]
  have hh := (H D).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hd (by omega : h ≤ h+k)) hC)
  have hk := (G D).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hd (by omega : k ≤ h+k)) hK)
  nlinarith only [hh,hk]

theorem SourcePolyUpper.mul {f g : ℕ→ℝ} (hf : SourcePolyUpper f) (hg : SourcePolyUpper g)
    (hf0 : ∀D,0 ≤ f D) (hg0 : ∀D,0 ≤ g D) : SourcePolyUpper (fun D=>f D*g D) := by
  obtain ⟨C,hC,h,H⟩ := hf
  obtain ⟨K,hK,k,G⟩ := hg
  refine ⟨C*K,mul_nonneg hC hK,h+k,?_⟩
  intro D
  calc
    f D*g D ≤ (C*((D:ℝ)+1)^h)*(K*((D:ℝ)+1)^k) :=
      mul_le_mul (H D) (G D) (hg0 D) ((hf0 D).trans (H D))
    _ = _ := by rw [pow_add]; ring

theorem sourceEpsilon_inverse_poly (B : ℕ) :
    SourcePolyUpper (fun D=>(sourceEpsilon B D)⁻¹) := by
  refine ⟨(2:ℝ)^(4*B+100),by positivity,1,?_⟩
  intro D
  simp only [sourceEpsilon,one_div,inv_inv,pow_one]
  exact le_rfl

theorem totalScoreExponent_poly (B : ℕ) (hB : 2 ≤ B) :
    SourcePolyUpper (totalScoreExponent B) := by
  apply (SourcePolyUpper.const 3 |>.add
    (SourcePolyUpper.depth.mul (SourcePolyUpper.const (B:ℝ)) (fun D=>by positivity) (fun _=>by positivity))).mono
  intro D
  have hh := (totalScoreExponent_bounds B D hB).2
  nlinarith only [hh,Nat.cast_nonneg B (α:=ℝ)]

theorem SourcePolyUpper.ceil {f : ℕ→ℝ} (hf : SourcePolyUpper f) (hf0 : ∀D,0 ≤ f D) :
    SourcePolyUpper (fun D=>(⌈f D⌉₊:ℝ)) := by
  apply (hf.add (SourcePolyUpper.const 1)).mono
  intro D
  exact (Nat.ceil_lt_add_one (hf0 D)).le

theorem sourceCancellationOrder_poly (B : ℕ) (hB : 2 ≤ B) :
    SourcePolyUpper (fun D=>(sourceCancellationOrder B D:ℝ)) := by
  let f := fun D=>totalScoreExponent B D+(sourceDegreeCutoff B:ℝ)+B+10
  have hf : SourcePolyUpper f := (((totalScoreExponent_poly B hB).add
    (SourcePolyUpper.const (sourceDegreeCutoff B:ℝ))).add (SourcePolyUpper.const (B:ℝ))).add
      (SourcePolyUpper.const 10)
  have hf0 (D) : 0 ≤ f D := by
    have hd := (totalScoreExponent_bounds B D hB).1
    have hr : 0 ≤ (sourceDegreeCutoff B:ℝ) := Nat.cast_nonneg _
    dsimp [f]
    linarith only [hd,hr,Nat.cast_nonneg B (α:=ℝ)]
  have hh := ((SourcePolyUpper.const 100).mul hf (fun _=>by norm_num) hf0).mul
    (sourceEpsilon_inverse_poly B) (fun D=>mul_nonneg (by norm_num) (hf0 D))
      (fun D=>(inv_pos.mpr (sourceEpsilon_pos B D)).le)
  have hc := hh.ceil (fun D=>mul_nonneg (mul_nonneg (by norm_num) (hf0 D))
    (inv_pos.mpr (sourceEpsilon_pos B D)).le)
  simpa only [sourceCancellationOrder,f,div_eq_mul_inv] using hc

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

theorem SourceExpUpper.const (c : ℝ) : SourceExpUpper (fun _ _=>c) :=
  (SourcePolyUpper.const c).expUpper

theorem SourceExpUpper.mul {f g : ℕ→ℝ→ℝ} (hf : SourceExpUpper f) (hg : SourceExpUpper g)
    (hf0 : ∀D q,q∈Set.Ioc 0 (1/2:ℝ) → 0 ≤ f D q)
    (hg0 : ∀D q,q∈Set.Ioc 0 (1/2:ℝ) → 0 ≤ g D q) :
    SourceExpUpper (fun D q=>f D q*g D q) := by
  obtain ⟨C,hC,h,H⟩ := hf
  obtain ⟨K,hK,k,G⟩ := hg
  refine ⟨C+K,add_nonneg hC hK,h+k,?_⟩
  intro D q hq
  have hΛ : 0 ≤ q^(-3:ℤ) := (zpow_pos hq.1 _).le
  have hd : 1 ≤ (D:ℝ)+1 := by linarith [Nat.cast_nonneg D (α:=ℝ)]
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hd (by omega : h≤h+k)) hC) hΛ
  have hk := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hd (by omega : k≤h+k)) hK) hΛ
  calc
    _ ≤ Real.exp (C*((D:ℝ)+1)^h*q^(-3:ℤ))*Real.exp (K*((D:ℝ)+1)^k*q^(-3:ℤ)) :=
      mul_le_mul (H D q hq) (G D q hq) (hg0 D q hq) ((hf0 D q hq).trans (H D q hq))
    _ ≤ _ := by rw [←Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith only [hh,hk]

theorem SourceExpUpper.pow_variably {f : ℕ→ℝ→ℝ} {r : ℕ→ℕ} (hf : SourceExpUpper f)
    (hf0 : ∀D q,q∈Set.Ioc 0 (1/2:ℝ) → 0 ≤ f D q)
    (hr : SourcePolyUpper (fun D=>(r D:ℝ))) : SourceExpUpper (fun D q=>(f D q)^(r D)) := by
  obtain ⟨C,hC,h,H⟩ := hf
  obtain ⟨K,hK,k,G⟩ := hr
  refine ⟨C*K,mul_nonneg hC hK,h+k,?_⟩
  intro D q hq
  have hΛ : 0≤q^(-3:ℤ) := (zpow_pos hq.1 _).le
  have hh := mul_le_mul_of_nonneg_right (G D) (show 0≤C*((D:ℝ)+1)^h*q^(-3:ℤ) by positivity)
  calc
    _ ≤ (Real.exp (C*((D:ℝ)+1)^h*q^(-3:ℤ)))^(r D) := pow_le_pow_left₀ (hf0 D q hq) (H D q hq) _
    _ = Real.exp ((r D:ℝ)*(C*((D:ℝ)+1)^h*q^(-3:ℤ))) := (Real.exp_nat_mul _ _).symm
    _ ≤ _ := by apply Real.exp_le_exp.mpr; rw [pow_add]; nlinarith only [hh]

theorem SourceExpUpper.pow {f : ℕ→ℝ→ℝ} (hf : SourceExpUpper f)
    (hf0 : ∀D q,q∈Set.Ioc 0 (1/2:ℝ) → 0 ≤ f D q) (r : ℕ) :
    SourceExpUpper (fun D q=>(f D q)^r) :=
  hf.pow_variably hf0 (SourcePolyUpper.const (r:ℝ))

theorem sourceOverlapConstant_expUpper : SourceExpUpper (fun _ q=>sourceOverlapConstant q) := by
  refine ⟨sourceChannelLogConstant,sourceChannelLogConstant_pos.le,0,?_⟩
  intro D q hq
  simp only [pow_zero,mul_one]
  apply (Real.log_le_iff_le_exp (sourceOverlapConstant_pos hq.1)).mp
  exact sourceOverlapConstant_log_bound ⟨hq.1,by linarith only [hq.2]⟩

theorem initialOverlapLower_inverse_expUpper : SourceExpUpper (fun _ q=>(initialOverlapLower q)⁻¹) := by
  refine ⟨1536+(32+3*primitivePeriodConstant),by unfold primitivePeriodConstant; positivity,0,?_⟩
  intro D q hq
  have hp := initialOverlapLower_pos q
  have hΛ := deletion_inverse_cube_ge_one ⟨hq.1,by linarith only [hq.2]⟩
  rw [←Real.log_le_iff_le_exp (inv_pos.mpr hp),Real.log_inv,initialOverlapLower,
    Real.log_div (Real.exp_pos _).ne' (by norm_num),Real.log_exp]
  simp only [pow_zero,mul_one,zpow_neg,zpow_ofNat] at hΛ ⊢
  have hh := Real.log_le_self (by norm_num : (0:ℝ)≤1536)
  have hmul := mul_le_mul_of_nonneg_left hΛ (by norm_num : (0:ℝ)≤1536)
  simp only [div_eq_mul_inv] at *
  nlinarith only [hh,hmul]

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


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

theorem sourceMomentEnvelope_pos (B D : ℕ) : 0 < sourceMomentEnvelope B D := by
  unfold sourceMomentEnvelope
  positivity

theorem sourceCapEnvelope_pos (B D : ℕ) {q : ℝ} (hq : 0<q) : 0 < sourceCapEnvelope B D q := by
  unfold sourceCapEnvelope
  positivity [sourceOverlapConstant_pos hq,initialOverlapLower_pos q]

theorem sourceMomentEnvelope_expUpper (B : ℕ) : SourceExpUpper (fun D _=>sourceMomentEnvelope B D) := by
  have hr : SourcePolyUpper (fun D=>((B*D:ℕ):ℝ)) := by
    apply ((SourcePolyUpper.const (B:ℝ)).mul SourcePolyUpper.depth (fun _=>by positivity) (fun _=>by positivity)).mono
    intro D
    push_cast
    nlinarith only [Nat.cast_nonneg B (α:=ℝ)]
  have hpow := (SourceExpUpper.const 2).pow_variably (fun _ _ _=>by norm_num) hr
  have hp := ((SourcePolyUpper.const ((10^8:ℝ)*2^(10*B)*((B:ℝ)+4)*2+1)).mul
    SourcePolyUpper.depth (fun _=>by positivity) (fun _=>by positivity)).expUpper
  exact hp.mul hpow (fun _ _ _=>by positivity) (fun _ _ _=>by positivity)

theorem sourceCapEnvelope_expUpper (B : ℕ) : SourceExpUpper (sourceCapEnvelope B) := by
  have hr : SourcePolyUpper (fun D=>((2*B*(D+1)+2:ℕ):ℝ)) := by
    have hp := ((SourcePolyUpper.const ((2*B:ℕ):ℝ)).mul SourcePolyUpper.depth
      (fun _=>by positivity) (fun _=>by positivity)).add (SourcePolyUpper.const 2)
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using hp
  have hc := sourceOverlapConstant_expUpper.pow_variably (fun _ q hq=>(sourceOverlapConstant_pos hq.1).le) hr
  exact ((SourceExpUpper.const 200).mul hc (fun _ _ _=>by norm_num)
    (fun _ q hq=>pow_nonneg (sourceOverlapConstant_pos hq.1).le _)).mul initialOverlapLower_inverse_expUpper
    (fun _ q hq=>by positivity [sourceOverlapConstant_pos hq.1])
    (fun _ q _=>(inv_pos.mpr (initialOverlapLower_pos q)).le)

theorem sourceWeightEnvelope_expUpper (B : ℕ) : SourceExpUpper (fun D _=>sourceWeightEnvelope B D) := by
  exact (SourceExpUpper.const 144).mul
    ((sourceMomentEnvelope_expUpper B).pow (fun D _ _=>(sourceMomentEnvelope_pos B D).le) 2)
    (fun _ _ _=>by norm_num) (fun _ _ _=>sq_nonneg _)

theorem sourceMotif_expUpper (B : ℕ) (hB : 2 ≤ B) :
    SourceExpUpper (fun D _=>(2:ℝ)^(sourceCancellationOrder B D)) :=
  (SourceExpUpper.const 2).pow_variably (fun _ _ _=>by norm_num) (sourceCancellationOrder_poly B hB)

theorem sourceSmoothingPrefactor_expUpper (B : ℕ) (hB : 2 ≤ B) :
    SourceExpUpper (fun D q=>sourceSmoothingPrefactor (sourceCancellationOrder B D) (sourceCapEnvelope B D q)) := by
  let s := sourceCancellationOrder B
  have hs := sourceCancellationOrder_poly B hB
  have hs0 (D) : 0 ≤ (s D:ℝ) := Nat.cast_nonneg _
  have hp : SourcePolyUpper (fun D=>((s D*s D+s D:ℕ):ℝ)) := by
    simpa only [Nat.cast_add,Nat.cast_mul] using (hs.mul hs hs0 hs0).add hs
  have ht : SourcePolyUpper (fun D=>((s D+1:ℕ):ℝ)) := by
    simpa only [Nat.cast_add,Nat.cast_one] using hs.add (SourcePolyUpper.const 1)
  have hone := (SourceExpUpper.const 2).pow_variably (fun _ _ _=>by norm_num) hp
  have htwo := ((ht.expUpper).mul (sourceCapEnvelope_expUpper B)
    (fun _ _ _=>Nat.cast_nonneg _) (fun D _ hq=>(sourceCapEnvelope_pos B D hq.1).le)).pow_variably
      (fun D q hq=>mul_nonneg (Nat.cast_nonneg _) (sourceCapEnvelope_pos B D hq.1).le) ht
  have H := hone.mul htwo (fun _ _ _=>by positivity)
    (fun D q hq=>pow_nonneg (mul_nonneg (Nat.cast_nonneg _) (sourceCapEnvelope_pos B D hq.1).le) _)
  simpa only [sourceSmoothingPrefactor,s,Nat.cast_add,Nat.cast_one] using H

theorem sourceSkeletonPrefactor_expUpper (B b : ℕ) (hB : 2 ≤ B) :
    SourceExpUpper (fun D q=>sourceSkeletonPrefactor (sourceCancellationOrder B D) b (sourceCapEnvelope B D q)) := by
  have hL := sourceMotif_expUpper B hB
  have hK := sourceCapEnvelope_expUpper B
  have hA := ((SourceExpUpper.const 2).mul (hL.pow (fun _ _ _=>by positivity) 3)
    (fun _ _ _=>by norm_num) (fun _ _ _=>by positivity)).mul hK
      (fun _ _ _=>by positivity) (fun D _ hq=>(sourceCapEnvelope_pos B D hq.1).le)
  have hF := ((SourceExpUpper.const 4).mul (hL.pow (fun _ _ _=>by positivity) 6)
    (fun _ _ _=>by norm_num) (fun _ _ _=>by positivity)).mul
      (hK.pow (fun D _ hq=>(sourceCapEnvelope_pos B D hq.1).le) 2)
      (fun _ _ _=>by positivity) (fun _ _ _=>sq_nonneg _)
  have H := hA.mul (hF.pow (fun _ _ _=>by positivity) (2^b-1))
    (fun D q hq=>by positivity [sourceCapEnvelope_pos B D hq.1]) (fun _ _ _=>by positivity)
  simpa only [sourceSkeletonPrefactor,binaryTreeBudget_const,Nat.cast_pow,Nat.cast_ofNat] using H

end TraceReconstruction


noncomputable section


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

theorem SourceExpUpper.add {f g : ℕ→ℝ→ℝ} (hf : SourceExpUpper f) (hg : SourceExpUpper g) :
    SourceExpUpper (fun D q=>f D q+g D q) := by
  obtain ⟨C,hC,h,H⟩ := hf
  obtain ⟨K,hK,k,G⟩ := hg
  refine ⟨C+K+1,by positivity,h+k,?_⟩
  intro D q hq
  have hΛ := deletion_inverse_cube_ge_one ⟨hq.1,by linarith only [hq.2]⟩
  have hd : 1≤(D:ℝ)+1 := by linarith [Nat.cast_nonneg D (α:=ℝ)]
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hd (by omega : h≤h+k)) hC) (by linarith only [hΛ] : 0≤q^(-3:ℤ))
  have hk := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hd (by omega : k≤h+k)) hK) (by linarith only [hΛ] : 0≤q^(-3:ℤ))
  have hz : 1≤((D:ℝ)+1)^(h+k)*q^(-3:ℤ) := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hd) hΛ
  have hc0 : 0≤C*((D:ℝ)+1)^(h+k)*q^(-3:ℤ) := by positivity
  have hk0 : 0≤K*((D:ℝ)+1)^(h+k)*q^(-3:ℤ) := by positivity
  have he1 : f D q ≤ Real.exp ((C+K)*((D:ℝ)+1)^(h+k)*q^(-3:ℤ)) :=
    (H D q hq).trans (Real.exp_le_exp.mpr (by nlinarith only [hh,hk0]))
  have he2 : g D q ≤ Real.exp ((C+K)*((D:ℝ)+1)^(h+k)*q^(-3:ℤ)) :=
    (G D q hq).trans (Real.exp_le_exp.mpr (by nlinarith only [hk,hc0]))
  have he := Real.add_one_le_exp (((D:ℝ)+1)^(h+k)*q^(-3:ℤ))
  have he' := mul_le_mul_of_nonneg_left (show 2≤Real.exp (((D:ℝ)+1)^(h+k)*q^(-3:ℤ)) by linarith only [he,hz])
    (Real.exp_pos ((C+K)*((D:ℝ)+1)^(h+k)*q^(-3:ℤ))).le
  rw [←Real.exp_add] at he'
  convert (show f D q+g D q ≤ Real.exp ((C+K)*((D:ℝ)+1)^(h+k)*q^(-3:ℤ)+((D:ℝ)+1)^(h+k)*q^(-3:ℤ)) by linarith only [he1,he2,he']) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

theorem sourceScaleInverseEnvelope_expUpper (B : ℕ) : SourceExpUpper (fun D _=>sourceScaleInverseEnvelope B D) := by
  have hr : SourcePolyUpper (fun D=>((B*D:ℕ):ℝ)) := by
    apply ((SourcePolyUpper.const (B:ℝ)).mul SourcePolyUpper.depth (fun _=>by positivity) (fun _=>by positivity)).mono
    intro D
    push_cast
    nlinarith only [Nat.cast_nonneg B (α:=ℝ)]
  exact (SourceExpUpper.const 2).mul ((SourceExpUpper.const 2).pow_variably (fun _ _ _=>by norm_num) hr)
    (fun _ _ _=>by norm_num) (fun _ _ _=>by positivity)

theorem source_log_scale_lower (B D i : ℕ) {n : ℝ} (hB : 2≤B) (hn : 1<n) :
    Real.log n ≤ sourceScaleInverseEnvelope B D*Real.log (sourceTargetScale B D n i) := by
  have hh := mul_le_mul_of_nonneg_right (sourceScaleProduct_lower B D i hB) (Real.log_pos hn).le
  rw [sourceTargetScale,Real.log_rpow (by linarith only [hn] : 0<n)]
  dsimp [sourceScaleInverseEnvelope]
  have hp : 0<(2:ℝ)*2^(B*D) := by positivity
  have H := mul_le_mul_of_nonneg_left hh hp.le
  field_simp at H
  nlinarith only [H]

theorem SourceExpUpper.uniform_log {f : ℕ→ℝ→ℝ} (hf : SourceExpUpper f)
    (hf0 : ∀D q,q∈Set.Ioc 0 (1/2:ℝ) → 0≤f D q)
    (B : ℕ) (ζ δ : ℝ) (hB : 2≤B) (hζ : ζ∈Set.Ioo 0 1) (hδ : 0<δ)
    {n q : ℕ→ℝ} (hn : Tendsto n atTop atTop) (hq : ∀t,q t∈Set.Ioc 0 (1/2:ℝ))
    (hH : Tendsto (fun t=>(q t)^3*Real.log (n t)) atTop atTop) :
    ∀ᶠt in atTop,∀i,f (sourceDepth B ζ ((q t)^3*Real.log (n t))) (q t)*Real.log (n t) ≤
      (sourceTargetScale B (sourceDepth B ζ ((q t)^3*Real.log (n t))) (n t) i)^
        (δ*sourceEpsilon B (sourceDepth B ζ ((q t)^3*Real.log (n t)))) := by
  let g := fun D q=>f D q*sourceScaleInverseEnvelope B D*(2/δ)*(sourceEpsilon B D)⁻¹
  have hg : SourceExpUpper g :=
    ((hf.mul (sourceScaleInverseEnvelope_expUpper B) hf0 (fun _ _ _=>by unfold sourceScaleInverseEnvelope; positivity)).mul
      (SourceExpUpper.const (2/δ)) (fun D q hq=>by unfold sourceScaleInverseEnvelope; positivity [hf0 D q hq]) (fun _ _ _=>by positivity)).mul
        (sourceEpsilon_inverse_poly B).expUpper (fun D q hq=>by unfold sourceScaleInverseEnvelope; positivity [hf0 D q hq])
          (fun D _ _=>(inv_pos.mpr (sourceEpsilon_pos B D)).le)
  have hu := SourceExpUpper.uniform g hg B ζ (δ/2) hB hζ (by positivity) hn hq hH
  filter_upwards [hu,hn.eventually_gt_atTop 1] with t ht hnt
  intro i
  let D := sourceDepth B ζ ((q t)^3*Real.log (n t))
  let N := sourceTargetScale B D (n t) i
  let ε := sourceEpsilon B D
  have he : 0<ε := sourceEpsilon_pos B D
  have hN : 0<N := Real.rpow_pos_of_pos (by linarith only [hnt]) _
  have hl := source_log_scale_lower B D i hB hnt
  have hb := Real.log_le_rpow_div hN.le (show 0<δ*ε/2 by positivity)
  have hmul := mul_le_mul_of_nonneg_left hb
    (show 0≤f D (q t)*sourceScaleInverseEnvelope B D by unfold sourceScaleInverseEnvelope; positivity [hf0 D _ (hq t)])
  have hg' := mul_le_mul_of_nonneg_right (ht i) (Real.rpow_pos_of_pos hN (δ*ε/2)).le
  have hr : N^((δ/2)*ε)*N^(δ*ε/2)=N^(δ*ε) := by rw [←Real.rpow_add hN]; congr 1; ring
  change g D (q t)*N^(δ*ε/2) ≤ N^((δ/2)*ε)*N^(δ*ε/2) at hg'
  rw [hr] at hg'
  have heq : f D (q t)*sourceScaleInverseEnvelope B D*(N^(δ*ε/2)/(δ*ε/2))=g D (q t)*N^(δ*ε/2) := by
    dsimp [g,ε]
    field_simp
  have hfirst := mul_le_mul_of_nonneg_left hl (hf0 D (q t) (hq t))
  change f D (q t)*Real.log (n t) ≤ N^(δ*ε)
  rw [heq] at hmul
  nlinarith only [hfirst,hmul,hg']

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

/-- Uniform exponential domination at every working scale, with the
 full depth and the varying known deletion probability retained. -/
theorem SourceExpUpper.uniform_tail {f g h : ℕ→ℝ→ℝ}
    (hf : SourceExpUpper f) (hg : SourceExpUpper g) (hh : SourceExpUpper h)
    (hf0 : ∀D q,q∈Set.Ioc 0 (1/2:ℝ) → 0<f D q)
    (_hg0 : ∀D q,q∈Set.Ioc 0 (1/2:ℝ) → 0≤g D q)
    (hh0 : ∀D q,q∈Set.Ioc 0 (1/2:ℝ) → 0≤h D q)
    (B : ℕ) (ζ : ℝ) (hB : 2≤B) (hζ : ζ∈Set.Ioo 0 1)
    {n q : ℕ→ℝ} (hn : Tendsto n atTop atTop) (hq : ∀t,q t∈Set.Ioc 0 (1/2:ℝ))
    (hH : Tendsto (fun t=>(q t)^3*Real.log (n t)) atTop atTop) :
    ∀ᶠt in atTop,∀i,
      g (sourceDepth B ζ ((q t)^3*Real.log (n t))) (q t)*
        Real.exp (-(sourceTargetScale B (sourceDepth B ζ ((q t)^3*Real.log (n t))) (n t) i)^
          (sourceEpsilon B (sourceDepth B ζ ((q t)^3*Real.log (n t))))/
          f (sourceDepth B ζ ((q t)^3*Real.log (n t))) (q t)) ≤
      (n t)^(-(h (sourceDepth B ζ ((q t)^3*Real.log (n t))) (q t))) := by
  have hfu := SourceExpUpper.uniform f hf B ζ (1/4) hB hζ (by norm_num) hn hq hH
  have hgu := SourceExpUpper.uniform g hg B ζ (1/4) hB hζ (by norm_num) hn hq hH
  have hhu := hh.uniform_log hh0 B ζ (1/4) hB hζ (by norm_num) hn hq hH
  have hcu := SourceExpUpper.uniform _ (SourceExpUpper.const 2) B ζ (1/4) hB hζ (by norm_num) hn hq hH
  filter_upwards [hfu,hgu,hhu,hcu,hn.eventually_gt_atTop 1] with t hft hgt hht hct hnt
  intro i
  let D := sourceDepth B ζ ((q t)^3*Real.log (n t))
  let N := sourceTargetScale B D (n t) i
  let ε := sourceEpsilon B D
  let X := N^((1/4)*ε)
  have hN : 0<N := Real.rpow_pos_of_pos (by linarith only [hnt]) _
  have hx : 0<X := Real.rpow_pos_of_pos hN _
  have hfD := hf0 D (q t) (hq t)
  have hfX : f D (q t)≤X := hft i
  have hgX : g D (q t)≤X := hgt i
  have hhX : h D (q t)*Real.log (n t)≤X := hht i
  have hX2 : 2≤X := hct i
  have hpow : N^ε=X^4 := by
    dsimp [X]
    rw [←Real.rpow_natCast,←Real.rpow_mul hN.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  have hsize : 2*X*f D (q t) ≤ X^4 := by
    have h1 := mul_le_mul_of_nonneg_left hfX (show 0≤2*X by positivity)
    have h2 : 2*X^2 ≤ X^4 := by nlinarith only [hX2,sq_nonneg (X^2-2),sq_nonneg (X-2)]
    nlinarith only [h1,h2]
  have hden : 2*X ≤ N^ε/f D (q t) := (le_div_iff₀ hfD).mpr (by rw [hpow]; exact hsize)
  have hexp : Real.exp (g D (q t)-N^ε/f D (q t)) ≤ (n t)^(-h D (q t)) := by
    rw [Real.rpow_def_of_pos (by linarith only [hnt] : 0<n t)]
    exact Real.exp_le_exp.mpr (by nlinarith only [hden,hgX,hhX])
  apply le_trans _ hexp
  rw [Real.exp_sub]
  have he := mul_le_mul_of_nonneg_right
    (show g D (q t) ≤ Real.exp (g D (q t)) by linarith only [Real.add_one_le_exp (g D (q t))])
    (Real.exp_pos (-N^ε/f D (q t))).le
  have hnexp : -N^ε/f D (q t) = -(N^ε/f D (q t)) := by ring
  rw [hnexp, Real.exp_neg] at he
  change g D (q t)*Real.exp (-N^ε/f D (q t)) ≤ _
  rw [hnexp, Real.exp_neg]
  simpa only [div_eq_mul_inv] using he

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
namespace TraceReconstruction
open scoped Classical

theorem sourceScaleProduct_step_le (B D i : ℕ) (hB : 2≤B) (hi : i<D) :
    sourceScaleProduct B D i ≤ sourceScaleProduct B D (i+1) := by
  have he := sourceEpsilon_pos B D
  have hp : (1:ℝ)≤2^(sourceDimension B i) := one_le_pow₀ (by norm_num)
  have ha : scaleA (sourceDimension B i) 0 (sourceEpsilon B D)≤1 := by
    unfold scaleA
    norm_num only [pow_zero,mul_one]
    have hh := (div_le_iff₀ (by positivity : (0:ℝ)<2^(sourceDimension B i))).mpr
      (le_mul_of_one_le_right (by linarith only [he] : 0≤1+sourceEpsilon B D) hp)
    linarith only [hh]
  have hs : 0 ≤ sourceScaleProduct B D (i+1) := (lt_of_lt_of_le (by positivity) (sourceScaleProduct_lower B D (i+1) hB)).le
  have hh := mul_le_mul_of_nonneg_right ha hs
  unfold sourceScaleProduct at *
  rw [Finset.prod_eq_prod_Ico_succ_bot hi]
  simpa only [one_mul] using hh

theorem sourceHalfMoment_step (B D i : ℕ) {n : ℝ} (hB : 2≤B) (hi : i<D) (hn : 1<n) :
    sourceHalfMoment B D n (i+1) ≤ sourceHalfMoment B D n i := by
  have hlog : 0<Real.log (sourceTargetScale B D n i) := by
    rw [sourceTargetScale,Real.log_rpow (by linarith only [hn] : 0<n)]
    exact mul_pos (lt_of_lt_of_le (by positivity) (sourceScaleProduct_lower B D i hB)) (Real.log_pos hn)
  have hlog' : Real.log (sourceTargetScale B D n i) ≤ Real.log (sourceTargetScale B D n (i+1)) := by
    rw [sourceTargetScale,sourceTargetScale,Real.log_rpow (by linarith only [hn] : 0<n),Real.log_rpow (by linarith only [hn] : 0<n)]
    exact mul_le_mul_of_nonneg_right (sourceScaleProduct_step_le B D i hB hi) (Real.log_pos hn).le
  unfold sourceHalfMoment
  apply Nat.ceil_mono
  have hd := (totalScoreExponent_bounds B D hB).1
  have hl := (Real.log_pos hn).le
  exact div_le_div_of_nonneg_left (by positivity) hlog hlog'

end TraceReconstruction


noncomputable section

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
namespace TraceReconstruction
open Filter
open scoped Topology Classical

theorem sourceWeightEnvelope_nonneg (B D : ℕ) : 0 ≤ sourceWeightEnvelope B D := by
  unfold sourceWeightEnvelope
  exact mul_nonneg (by norm_num) (sq_nonneg _)

theorem sourceForcedRoleFactor_nonneg (b R : ℕ) : 0 ≤ sourceForcedRoleFactor b R := by
  unfold sourceForcedRoleFactor
  exact Finset.sum_nonneg (fun _ _=>by positivity)

theorem source_forced_prefactor_expUpper (B b : ℕ) (hB : 2 ≤ B) :
    SourceExpUpper (fun D q=>192*(sourceForcedRoleFactor b (sourceDegreeCutoff B)*
      (sourceWeightEnvelope B D)^(2^(b+1))*
      sourceSkeletonPrefactor (sourceCancellationOrder B D) b (sourceCapEnvelope B D q))) := by
  have H := (((SourceExpUpper.const (sourceForcedRoleFactor b (sourceDegreeCutoff B))).mul
    ((sourceWeightEnvelope_expUpper B).pow (fun _ _ _=>sourceWeightEnvelope_nonneg _ _) (2^(b+1)))
    (fun _ _ _=>sourceForcedRoleFactor_nonneg _ _) (fun _ _ _=>pow_nonneg (sourceWeightEnvelope_nonneg _ _) _)).mul
      (sourceSkeletonPrefactor_expUpper B b hB)
      (fun _ _ _=>mul_nonneg (sourceForcedRoleFactor_nonneg _ _) (pow_nonneg (sourceWeightEnvelope_nonneg _ _) _))
      (fun D q hq=>sourceSkeletonPrefactor_nonneg _ _ (sourceCapEnvelope_pos B D hq.1).le))
  exact (SourceExpUpper.const 192).mul H (fun _ _ _=>by norm_num)
    (fun D q hq=>mul_nonneg (mul_nonneg (sourceForcedRoleFactor_nonneg _ _)
      (pow_nonneg (sourceWeightEnvelope_nonneg _ _) _))
        (sourceSkeletonPrefactor_nonneg _ _ (sourceCapEnvelope_pos B D hq.1).le))

theorem source_overlap_prefactor_expUpper (B : ℕ) (hB : 2 ≤ B) :
    SourceExpUpper (fun D q=>1099511627776*(sourceCapEnvelope B D q+1)*(sourceWeightEnvelope B D+1)^2*
      ((2:ℝ)^(sourceCancellationOrder B D))^(B+2)) := by
  have hK := (sourceCapEnvelope_expUpper B).add (SourceExpUpper.const 1)
  have hW := (sourceWeightEnvelope_expUpper B).add (SourceExpUpper.const 1)
  have hL := sourceMotif_expUpper B hB
  exact (((SourceExpUpper.const 1099511627776).mul hK (fun _ _ _=>by norm_num)
    (fun D q hq=>by linarith only [sourceCapEnvelope_pos B D hq.1])).mul
      (hW.pow (fun D _ _=>by linarith only [sourceWeightEnvelope_nonneg B D]) 2)
      (fun D q hq=>by positivity [sourceCapEnvelope_pos B D hq.1]) (fun _ _ _=>sq_nonneg _)).mul
        (hL.pow (fun _ _ _=>by positivity) (B+2))
        (fun D q hq=>by positivity [sourceCapEnvelope_pos B D hq.1]) (fun _ _ _=>by positivity)

theorem source_numeric_margins_eventually (B : ℕ) (ζ : ℝ) (hB : 2 ≤ B) (hζ : ζ∈Set.Ioo 0 1)
    {n q : ℕ→ℝ} (hn : Tendsto n atTop atTop) (hq : ∀t,q t∈Set.Ioc 0 (1/2:ℝ))
    (hH : Tendsto (fun t=>(q t)^3*Real.log (n t)) atTop atTop) :
    ∀ᶠt in atTop,∀i,SourceNumericMargins B (sourceDepth B ζ ((q t)^3*Real.log (n t))) (q t)
      (sourceTargetScale B (sourceDepth B ζ ((q t)^3*Real.log (n t))) (n t) i) := by
  have hu (f : ℕ→ℝ→ℝ) (hf : SourceExpUpper f) :=
    SourceExpUpper.uniform f hf B ζ 1 hB hζ (by norm_num) hn hq hH
  have hgeom := hu _ ((SourceExpUpper.const 1200).mul (sourceCapEnvelope_expUpper B)
    (fun _ _ _=>by norm_num) (fun D q hq=>(sourceCapEnvelope_pos B D hq.1).le))
  have hmot := hu _ ((SourceExpUpper.const 48).mul (sourceMotif_expUpper B hB)
    (fun _ _ _=>by norm_num) (fun _ _ _=>by positivity))
  have hsparse := hu _ (((SourceExpUpper.const 8).mul (sourceWeightEnvelope_expUpper B)
    (fun _ _ _=>by norm_num) (fun _ _ _=>sourceWeightEnvelope_nonneg _ _)).mul
      ((sourceMotif_expUpper B hB).pow (fun _ _ _=>by positivity) 2)
      (fun _ _ _=>mul_nonneg (by norm_num) (sourceWeightEnvelope_nonneg _ _)) (fun _ _ _=>sq_nonneg _))
  have hsmooth := hu _ (sourceSmoothingPrefactor_expUpper B hB)
  have hbad : ∀ᶠt in atTop,∀b∈Finset.range (B+1),∀i,
      384*sourceBadRoleFactor b (sourceDegreeCutoff B) ≤
        (sourceTargetScale B (sourceDepth B ζ ((q t)^3*Real.log (n t))) (n t) i)^
          (sourceEpsilon B (sourceDepth B ζ ((q t)^3*Real.log (n t)))) := by
    apply (Filter.eventually_all_finset _).mpr
    intro b _
    simpa only [one_mul] using hu _ (SourceExpUpper.const (384*sourceBadRoleFactor b (sourceDegreeCutoff B)))
  have hforce : ∀ᶠt in atTop,∀b∈Finset.range (B+1),∀i,
      192*(sourceForcedRoleFactor b (sourceDegreeCutoff B)*
        (sourceWeightEnvelope B (sourceDepth B ζ ((q t)^3*Real.log (n t))))^(2^(b+1))*
        sourceSkeletonPrefactor (sourceCancellationOrder B (sourceDepth B ζ ((q t)^3*Real.log (n t))))
          b (sourceCapEnvelope B (sourceDepth B ζ ((q t)^3*Real.log (n t))) (q t))) ≤
        (sourceTargetScale B (sourceDepth B ζ ((q t)^3*Real.log (n t))) (n t) i)^
          (sourceEpsilon B (sourceDepth B ζ ((q t)^3*Real.log (n t)))) := by
    apply (Filter.eventually_all_finset _).mpr
    intro b _
    simpa only [one_mul] using hu _ (source_forced_prefactor_expUpper B b hB)
  have htail := hu _ (SourceExpUpper.const 1536)
  have herr := hu _ (((SourceExpUpper.const 64).mul
    ((sourceCapEnvelope_expUpper B).add (SourceExpUpper.const 1))
    (fun _ _ _=>by norm_num) (fun D q hq=>by positivity [sourceCapEnvelope_pos B D hq.1])).mul
    SourcePolyUpper.depth.expUpper (fun D q hq=>by positivity [sourceCapEnvelope_pos B D hq.1])
      (fun _ _ _=>by positivity))
  have hov := hu _ (source_overlap_prefactor_expUpper B hB)
  filter_upwards [hgeom,hmot,hsparse,hsmooth,hbad,hforce,htail,herr,hov] with t hg hm hs hsm hb hf ht he ho
  intro i
  refine ⟨?_,?_,?_,?_,fun b h=>hb b (Finset.mem_range.mpr (by omega)) i,
    fun b h=>hf b (Finset.mem_range.mpr (by omega)) i,?_,?_,?_⟩ <;>
    first | simpa only [one_mul] using hg i | simpa only [one_mul] using hm i |
      simpa only [one_mul] using hs i | simpa only [one_mul] using hsm i |
      simpa only [one_mul] using ht i | simpa only [one_mul] using he i | simpa only [one_mul] using ho i

end TraceReconstruction
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

end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

theorem sourceTailDenominator_pos (B D : ℕ) {q : ℝ} (hq : 0<q) :
    0 < sourceTailDenominator B D q := by
  unfold sourceTailDenominator
  positivity [sourceCapEnvelope_pos B D hq]

theorem sourceTailDenominator_expUpper (B : ℕ) : SourceExpUpper (sourceTailDenominator B) := by
  have H := ((SourceExpUpper.const 9600).mul (sourceCapEnvelope_expUpper B)
    (fun _ _ _=>by norm_num) (fun D q hq=>(sourceCapEnvelope_pos B D hq.1).le)).mul
      (initialOverlapLower_inverse_expUpper.pow (fun _ q _=>(inv_pos.mpr (initialOverlapLower_pos q)).le) 4)
      (fun D q hq=>by positivity [sourceCapEnvelope_pos B D hq.1]) (fun _ _ _=>by positivity)
  exact (SourceExpUpper.const 512).add H

theorem sourceWorkSize_poly (B : ℕ) (hB : 2 ≤ B) : SourcePolyUpper (sourceWorkSize B) := by
  exact (((totalScoreExponent_poly B hB).add (SourcePolyUpper.const (sourceDegreeCutoff B:ℝ))).add
    (SourcePolyUpper.const (B:ℝ))).add (SourcePolyUpper.const 10)

theorem sourceTailExponent_expUpper (B : ℕ) (hB : 2 ≤ B) :
    SourceExpUpper (fun D _=>sourceTailExponent B D) := by
  have ha := ((totalScoreExponent_poly B hB).add (SourcePolyUpper.const (B:ℝ))).add (SourcePolyUpper.const 1)
  have hu := (SourcePolyUpper.const 300).mul ha (fun _=>by norm_num)
    (fun D=>by linarith only [(totalScoreExponent_bounds B D hB).1,Nat.cast_nonneg B (α:=ℝ)])
  have hw := (SourcePolyUpper.const 40).mul (sourceWorkSize_poly B hB) (fun _=>by norm_num)
    (fun D=>(sourceWorkSize_pos B D hB).le)
  exact ((hu.add hw).add (SourcePolyUpper.const 5)).expUpper

theorem source_tails_eventually (B : ℕ) (ζ : ℝ) (hB : 2 ≤ B) (hζ : ζ∈Set.Ioo 0 1)
    {n q : ℕ→ℝ} (hn : Tendsto n atTop atTop) (hq : ∀t,q t∈Set.Ioc 0 (1/2:ℝ))
    (hH : Tendsto (fun t=>(q t)^3*Real.log (n t)) atTop atTop) :
    ∀ᶠt in atTop,∀i,2*(B:ℝ)*Real.exp
      (-(sourceTargetScale B (sourceDepth B ζ ((q t)^3*Real.log (n t))) (n t) i)^
        (sourceEpsilon B (sourceDepth B ζ ((q t)^3*Real.log (n t))))/
        sourceTailDenominator B (sourceDepth B ζ ((q t)^3*Real.log (n t))) (q t)) ≤
      (n t)^(-sourceTailExponent B (sourceDepth B ζ ((q t)^3*Real.log (n t)))) := by
  apply (sourceTailDenominator_expUpper B).uniform_tail (SourceExpUpper.const (2*(B:ℝ)))
    (sourceTailExponent_expUpper B hB) (fun D q hq=>sourceTailDenominator_pos B D hq.1)
    (fun _ _ _=>by positivity) (fun D _ _=>?_) B ζ hB hζ hn hq hH
  unfold sourceTailExponent
  have ha : 0 ≤ totalScoreExponent B D+B+1 := by
    linarith only [(totalScoreExponent_bounds B D hB).1,Nat.cast_nonneg B (α:=ℝ)]
  have hw := (sourceWorkSize_pos B D hB).le
  linarith only [ha,hw]

end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem sourceBlockLength_factor (P : ℕ→ℕ) (ell j : ℕ) :
    sourceBlockLength P ell j=ell*sourceBlockLength P 1 j := by
  induction j with
  | zero => simp only [sourceBlockLength,mul_one]
  | succ j ih => rw [sourceBlockLength,sourceBlockLength,ih]; ring

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The normalized error invariant propagates through actual leaf products,
 with one fresh delta paid by clipping and fitting. -/
theorem normalized_block_error {E Δ clip fit : ℝ} {ell newell leaves i : ℕ}
    (hell : 1 ≤ newell) (hE : E ≤ ((i:ℝ)+1)*Δ*ell) (hΔ : 0 ≤ Δ)
    (hleaf : leaves*ell ≤ newell) (hnew : clip+fit ≤ Δ) :
    (clip+(leaves:ℝ)*E+fit)/(newell:ℝ) ≤ ((i:ℝ)+2)*Δ := by
  have hl0 : (0:ℝ)<newell := by exact_mod_cast (show 0<newell by omega)
  apply (div_le_iff₀ hl0).mpr
  have hleaf' : (leaves:ℝ)*ell ≤ newell := by exact_mod_cast hleaf
  have h1 := mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg leaves (α:=ℝ))
  have h2 := mul_le_mul_of_nonneg_left hleaf' (show 0 ≤ ((i:ℝ)+1)*Δ by positivity)
  have h3 : Δ ≤ Δ*newell := le_mul_of_one_le_right hΔ (by exact_mod_cast hell)
  nlinarith only [h1,h2,h3,hnew]

end TraceReconstruction
noncomputable section
noncomputable section
noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem SourceArithmeticBounds.length_positive {C N F ε : ℝ} {s b ell k j : ℕ}
    (H : SourceArithmeticBounds C N F ε s b ell k) (hN : 0<N) (hj : j ≤ b) :
    1 ≤ sourceArithmeticLength C N b ε ell k j := by
  have hp : (0:ℝ) < sourceArithmeticLength C N b ε ell k j :=
    (show 0<N^(scaleA b j ε)/2 by positivity).trans_le (H.lengths j hj).1
  have hh : 0 < sourceArithmeticLength C N b ε ell k j := by exact_mod_cast hp
  omega

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

theorem SourceArithmeticBounds.copies_positive {C N F ε : ℝ} {s b ell k : ℕ}
    (H : SourceArithmeticBounds C N F ε s b ell k) (hN : 0<N) {j : ℕ} (hj : j<b) :
    1 ≤ sourceArithmeticP C N b ε ell k j := by
  have hh := (H.copies j hj).1
  have hp : (0:ℝ)<N^(scaleA b j ε)*N^ε/2 := by positivity
  have hp' : (0:ℝ) < sourceArithmeticP C N b ε ell k j := hp.trans_le hh
  have hp'' : 0 < sourceArithmeticP C N b ε ell k j := by exact_mod_cast hp'
  omega

theorem SourceArithmeticBounds.trials_positive {C N F ε : ℝ} {s b ell k : ℕ}
    (H : SourceArithmeticBounds C N F ε s b ell k) (hN : 0<N) (hC : 0<C) (hF : 0<F)
    {j : ℕ} (hj : j<b) : 0 < sourceArithmeticTrials C N b ε ell k j := by
  have hh := (H.trials j hj).1
  have hp : (0:ℝ)<N^ε/(600*(C^(2*b)*F)) := by positivity
  exact_mod_cast hp.trans_le hh

end TraceReconstruction


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem source_old_variance_scale (B D i : ℕ) {n : ℝ} (hn : 0<n) (hi : i<D) :
    (sourceTargetScale B D n i)^(-totalScoreExponent B i)=
      (sourceTargetScale B D n (i+1))^(-scaleA (sourceDimension B i) 0 (sourceEpsilon B D)*totalScoreExponent B i) := by
  rw [sourceTargetScale_step B D i n hn.le hi,←Real.rpow_mul (show 0 ≤ sourceTargetScale B D n (i+1) from (Real.rpow_pos_of_pos hn _).le)]
  congr 1
  ring

theorem source_old_variance_square (B D i : ℕ) {n : ℝ} (hn : 0<n) (hi : i<D) :
    (sourceTargetScale B D n i)^(-totalScoreExponent B i)=
      ((sourceTargetScale B D n (i+1))^(-scaleA (sourceDimension B i) 0 (sourceEpsilon B D)*totalScoreExponent B i/2))^2 := by
  rw [source_old_variance_scale B D i hn hi,←Real.rpow_natCast,←Real.rpow_mul (show 0 ≤ sourceTargetScale B D n (i+1) from (Real.rpow_pos_of_pos hn _).le)]
  congr 1
  norm_num

end TraceReconstruction


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The exact manuscript block is now a producer: no new level invariant or
 overlap is assumed. All hypotheses besides the old actual pair are literal
 scalar schedule margins. -/
theorem source_level_step {B D i : ℕ} {n q : ℝ} {hq : q∈Set.Icc 0 1}
    (U : SourceLevelPair B D n q hq i) (hB : 2 ≤ B) (hi : i<D) (hn : 4 ≤ n)
    (hq' : q∈Set.Ioc 0 (1/2:ℝ))
    (H : SourceNumericMargins B D q (sourceTargetScale B D n (i+1)))
    (htail : 2*(B:ℝ)*Real.exp
      (-(sourceTargetScale B D n (i+1))^(sourceEpsilon B D)/sourceTailDenominator B D q) ≤
        n^(-sourceTailExponent B D)) :
    Nonempty (SourceLevelPair B D n q hq (i+1)) := by
  let N := sourceTargetScale B D n (i+1)
  let b := sourceDimension B i
  let ε := sourceEpsilon B D
  let s := sourceCancellationOrder B D
  let C := sourceOverlapConstant q
  let P := sourceArithmeticP C N b ε U.left.length U.overlapCount
  let h := sourceArithmeticCount C N b ε U.left.length U.overlapCount
  let T := sourceBlockWindows N b ε
  let t := sourceArithmeticTrials C N b ε U.left.length U.overlapCount
  let atom := fun (τ : Bool)=>if τ then U.right else U.left
  let k := sourceHalfMoment B D n (i+1)
  let L := N^(-scaleA b 0 ε*totalScoreExponent B i/2)
  let a := N^(-20*sourceWorkSize B D)
  let ω := initialOverlapLower q
  let Δ := n^(-100*(totalScoreExponent B D+B+1))
  have hn1 : 1 ≤ n := by linarith only [hn]
  have hn2 : 1 < n := by linarith only [hn]
  have hn0 : 0<n := by linarith only [hn]
  have hN : 0<N := (by norm_num : (0:ℝ)<1).trans_le (sourceTargetScale_bounds B D (i+1) hB hn1).1
  have hC : 1 ≤ C := (by norm_num : (1:ℝ)≤2).trans (sourceOverlapConstant_ge_two hq')
  have H' := source_level_geometry U hB hi hn1 hq' H
  have hb := sourceDimension_bounds B i hB
  have hb1 : b-1+1=b := by dsimp [b]; omega
  have hk : 1 ≤ k := (sourceHalfMoment_bounds B D (i+1) hB hn2).1
  let O := U.oracle.restrict hk (sourceHalfMoment_step B D i hB hi hn2)
  let := O.finiteOutcome
  have hnum := source_level_all_budgets U hB hi hn hq' H htail
  have hov := source_level_overlap U hB hi hn hq' H htail
  have hv : (sourceTargetScale B D n i)^(-totalScoreExponent B i) ≤ L^2 := by
    rw [source_old_variance_square B D i hn0 hi]
  have hm : O.first.expect (fun z=>|O.score z|^(2*k)) ≤ L^(2*k) := by
    have hh := O.first.expect_even_pow_le_of_moment O.score k hk (O.moment.trans hv)
    simpa only [pow_mul] using hh
  have he (j : ℕ) (hj : j ≤ b-1) : Even (T j) := by
    change Even (sourceBlockWindows N b ε j)
    rw [sourceBlockWindows,ite_eq_left (by omega : j<b)]
    exact sourceWindowSize_even _ _ _ _
  obtain ⟨W⟩ := actual_source_oracle hq U.error_nonneg s P T t h atom (b-1) (sourceDegreeCutoff B) k
    H'.layout H'.window_positive (by
      simpa only [P,t,h,T,sourceBlockWindows,ite_eq_left (show b-1<b by omega)] using
        sourceArithmetic_root_copies C N b ε U.left.length U.overlapCount (by omega))
    (fun j hj=>H'.trials_positive hN (by linarith only [hC]) (by positivity) (by omega))
    (fun j hj=>(H'.windows j (by omega)).1) he (fun j hj=>(H'.windows j (by omega)).2.1)
    (H'.windows (b-1) (by omega)).2.2.2 O.first O.second O.decode O.score O.density O.likelihood_nonneg
    O.first_simulation O.second_simulation ω a a L (by positivity) (by positivity)
    ⟨initialOverlapLower_pos q,lt_of_lt_of_le (initialOverlapLower_lt_eighth hq'.1) (by norm_num)⟩
    (fun j hj=>hov j (by omega)) hk hm hnum.2.1
    (fun j hj=>hnum.2.2.2.1 j (by omega)) hnum.2.2.2.2.1
  rw [hb1] at W
  have hlen (τ : Bool) : (sourceBlockWord s P atom b τ).length=sourceArithmeticLength C N b ε U.left.length U.overlapCount b := by
    rw [sourceArithmeticLength_eq_block]
    apply sourceBlockWord_length
    intro σ
    cases σ
    · rfl
    · exact U.equalLength.symm
  have hinj : Function.Injective atom := by
    intro τ σ hτσ
    cases τ <;> cases σ
    · rfl
    · exact False.elim (U.different hτσ)
    · exact False.elim (U.different hτσ.symm)
    · rfl
  have hne : sourceBlockWord s P atom b false≠sourceBlockWord s P atom b true := by
    intro hh
    have hh' := sourceBlockWord_injective s P atom U.left.length (by
      intro τ; cases τ; rfl; exact U.equalLength.symm) hinj b
      (fun j hj=>Nat.lt_of_lt_of_le (by omega : 0<1) (H'.copies_positive hN hj)) hh
    contradiction
  have hlength := H'.lengths b le_rfl
  change N^(scaleA b b ε)/2 ≤ (sourceArithmeticLength C N b ε U.left.length U.overlapCount b:ℝ) ∧
    (sourceArithmeticLength C N b ε U.left.length U.overlapCount b:ℝ) ≤ N^(scaleA b b ε) at hlength
  simp only [scaleA_top,Real.rpow_one] at hlength
  have hE : U.error ≤ ((i:ℝ)+1)*Δ*U.left.length := by
    apply (div_le_iff₀ ?_).mp U.normalized_error
    exact (show 0 < sourceTargetScale B D n i/2 by positivity [Real.rpow_pos_of_pos hn0 (sourceScaleProduct B D i)]).trans_le U.length_lower
  have hleaf : SourceLeafCount T b*U.left.length ≤ sourceArithmeticLength C N b ε U.left.length U.overlapCount b := by
    rw [sourceArithmeticLength_eq_block,sourceBlockLength_factor]
    rw [Nat.mul_comm]
    apply Nat.mul_le_mul_left
    apply sourceLeafCount_le_length (by omega : 1≤1)
    intro j hj
    have hh := (H'.windows j hj).2.2.1
    change 2*T j ≤ P j at hh
    change T j ≤ P j
    omega
  have herror := normalized_block_error (H'.length_positive hN le_rfl) hE
    (show 0≤Δ by positivity) hleaf hnum.2.2.2.2.2
  have hfac : C^(2*b)*C^(2*B*i+2) ≤ C^(2*B*(i+1)+2) := by
    rw [←pow_add]
    apply pow_le_pow_right₀ hC
    dsimp [b]
    nlinarith only [hb.2]
  refine ⟨W.toConcrete hq ((hlen false).trans (hlen true).symm) hne ?_ ?_ ?_ hnum.2.2.1 ?_ ?_ (hov b le_rfl)⟩
  · rw [hlen]; exact hlength.1
  · rw [hlen]; exact hlength.2
  · rw [hlen]
    simpa only [Δ,Nat.cast_add,Nat.cast_one,add_assoc,show (1:ℝ)+1=2 by norm_num] using herror
  · rw [hlen]; exact (H'.counts b le_rfl).1
  · rw [hlen]
    exact (H'.counts b le_rfl).2.trans (mul_le_mul_of_nonneg_right hfac (Nat.cast_nonneg _))

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

/-- Full source construction at every scheduled level, uniformly in the
 joint deletion regime. No level witnesses are assumed. -/
theorem source_all_levels_eventually_oai (B : ℕ) (ζ : ℝ) (hB : 2 ≤ B)
    (hζ : ζ∈Set.Ioo 0 1) {n q : ℕ→ℝ} (hn : Tendsto n atTop atTop)
    (hq : ∀t,q t∈Set.Ioc 0 (1/2:ℝ))
    (hH : Tendsto (fun t=>(q t)^3*Real.log (n t)) atTop atTop) :
    ∀ᶠt in atTop,∀i ≤ sourceDepth B ζ ((q t)^3*Real.log (n t)),
      Nonempty (SourceLevelPair B (sourceDepth B ζ ((q t)^3*Real.log (n t)))
        (n t) (q t) ⟨(hq t).1.le,by linarith [(hq t).2]⟩ i) := by
  filter_upwards [source_initial_at_smallest_scale B ζ hB hζ hn hq hH,
    source_numeric_margins_eventually B ζ hB hζ hn hq hH,
    source_tails_eventually B ζ hB hζ hn hq hH,hn.eventually_ge_atTop 4] with t h0 hm ht hn4
  intro i hi
  induction i with
  | zero => simpa only [SourceLevelPair,totalScoreExponent,Finset.range_zero,
      Finset.sum_empty,add_zero,Nat.mul_zero,Nat.zero_add] using h0
  | succ i ih =>
    obtain ⟨U⟩ := ih (by omega)
    exact source_level_step U hB (by omega) hn4 (hq t) (hm (i+1)) (ht (i+1))

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

theorem solution : type_of% @OAI.TraceReconstruction.source_all_levels_eventually_oai := @OAI.TraceReconstruction.source_all_levels_eventually_oai
