-- Prove2me | solution 2 for OAI.C0Absorption.compatible_detectors_false
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:25:55.547215+00:00
-- url     : https://prove2.me/submissions/249a2509-a801-471d-bf69-37d2db03d2bc

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Operations.lean:L36-L83
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.compatible_detectors_false. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization
import Definitions.Def_OAI_Analysis_C0Absorption_Coordinates
import Definitions.Def_OAI_Analysis_C0Absorption_Triangular
import Definitions.Def_OAI_Analysis_C0Absorption_Tests
import Definitions.Def_OAI_Analysis_C0Absorption_Duality
import Definitions.Def_OAI_Analysis_C0Absorption_Selection
import Definitions.Def_OAI_Analysis_C0Absorption_Supports
import Definitions.Def_OAI_Analysis_C0Absorption_Operations

-- ---- from OAI.Analysis.C0Absorption.Norm ----
namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

section SelectedNorm

variable {S : Type*} [MetricSpace S]

theorem listExponent_toReal (n : ℕ) :
    (listExponent n).toReal = 1 + 1 / ((triple n).2.2 + 1 : ℝ) := by
  simp [listExponent, ENNReal.toReal_add, one_div]

end SelectedNorm

end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.Completion ----
namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

section CompletedSeminorms

open UniformSpace Completion

variable {X : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]

theorem completedSeminorm_continuous (q : Seminorm ℝ X) (C : ℝ≥0)
    (h : ∀ x, q x ≤ C * ‖x‖) : Continuous (completedSeminorm q C h) :=
  Completion.continuous_extension

end CompletedSeminorms

section SelectedCompletion

open UniformSpace Completion

variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

theorem completedCoordinate_continuous (n : ℕ) : Continuous (completedCoordinate L o n) :=
  completedSeminorm_continuous _ _ _

end SelectedCompletion

end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.Signs ----
namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

section Signs

theorem sum_sign_sq (n : ℕ) (a : Fin n → ℝ) :
    ∑ ε : Fin n → Bool, (∑ i, realSign (ε i) * a i) ^ 2 =
      (2 : ℝ) ^ n * ∑ i, a i ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Bool))
      (fun p : Bool × (Fin n → Bool) =>
        (∑ i : Fin (n + 1), realSign ((Fin.consEquiv (fun _ => Bool)) p i) * a i) ^ 2)
      (fun ε : Fin (n + 1) → Bool => (∑ i, realSign (ε i) * a i) ^ 2)
      (fun _ => rfl)]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_succ, Fin.consEquiv_apply,
      Fin.cons_zero, Fin.cons_succ, Fintype.sum_bool, realSign_true, realSign_false,
      one_mul, neg_one_mul]
    rw [← Finset.sum_add_distrib]
    have heq (x y : ℝ) : (x + y) ^ 2 + (-x + y) ^ 2 = 2 * x ^ 2 + 2 * y ^ 2 := by ring
    simp_rw [heq]
    rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, ih]
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_pow, Nat.cast_ofNat, pow_succ]
    ring

theorem finite_detector_bound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (n : ℕ) (m : Fin n → X) (u : Fin n → X →ₗ[ℝ] ℝ)
    (α M δ : ℝ) (hα : 0 ≤ α) (_hM : 0 ≤ M)
    (hsum : ∀ ε : Fin n → Bool, ‖∑ i, realSign (ε i) • m i‖ ≤ M)
    (hdual : ∀ x, α * ∑ k, (u k x) ^ 2 ≤ ‖x‖ ^ 2)
    (hdetect : ∀ i, δ ^ 2 ≤ (u i (m i)) ^ 2) :
    α * (n : ℝ) * δ ^ 2 ≤ M ^ 2 := by
  classical
  have hdiag : (n : ℝ) * δ ^ 2 ≤ ∑ k : Fin n, ∑ i : Fin n, (u k (m i)) ^ 2 := by
    calc
      (n : ℝ) * δ ^ 2 = ∑ k : Fin n, δ ^ 2 := by simp
      _ ≤ ∑ k : Fin n, ∑ i : Fin n, (u k (m i)) ^ 2 := by
        apply Finset.sum_le_sum
        intro k hk
        exact (hdetect k).trans (Finset.single_le_sum (fun i _ => sq_nonneg (u k (m i))) (mem_univ k))
  have havg : (2 : ℝ) ^ n * (α * ∑ k : Fin n, ∑ i : Fin n, (u k (m i)) ^ 2) ≤
      (2 : ℝ) ^ n * M ^ 2 := by
    calc
      (2 : ℝ) ^ n * (α * ∑ k : Fin n, ∑ i : Fin n, (u k (m i)) ^ 2) =
          ∑ ε : Fin n → Bool, α * ∑ k : Fin n,
            (u k (∑ i : Fin n, realSign (ε i) • m i)) ^ 2 := by
        simp only [map_sum, map_smul, smul_eq_mul]
        conv_rhs => rw [← Finset.mul_sum, Finset.sum_comm]
        simp_rw [sum_sign_sq]
        rw [← Finset.mul_sum]
        ring
      _ ≤ ∑ ε : Fin n → Bool, M ^ 2 := by
        apply Finset.sum_le_sum
        intro ε hε
        exact (hdual _).trans (pow_le_pow_left₀ (norm_nonneg _) (hsum ε) 2)
      _ = (2 : ℝ) ^ n * M ^ 2 := by
        simp
  have ht : α * (∑ k : Fin n, ∑ i : Fin n, (u k (m i)) ^ 2) ≤ M ^ 2 :=
    le_of_mul_le_mul_left havg (by positivity)
  calc
    α * (n : ℝ) * δ ^ 2 = α * ((n : ℝ) * δ ^ 2) := by ring
    _ ≤ α * (∑ k : Fin n, ∑ i : Fin n, (u k (m i)) ^ 2) :=
      mul_le_mul_of_nonneg_left hdiag hα
    _ ≤ M ^ 2 := ht

theorem no_infinite_detectors {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (m : ℕ → X) (u : ℕ → X →ₗ[ℝ] ℝ) (α M δ : ℝ)
    (hα : 0 < α) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hsum : ∀ n (ε : Fin n → Bool), ‖∑ i, realSign (ε i) • m i‖ ≤ M)
    (hdual : ∀ n x, α * ∑ k : Fin n, (u k x) ^ 2 ≤ ‖x‖ ^ 2)
    (hdetect : ∀ i, δ ≤ |u i (m i)|) : False := by
  have hbound (n : ℕ) : α * (n : ℝ) * δ ^ 2 ≤ M ^ 2 := by
    apply finite_detector_bound n (fun i => m i) (fun i => u i) α M δ hα.le hM
      (hsum n) (hdual n)
    intro i
    simpa only [sq_abs] using pow_le_pow_left₀ hδ.le (hdetect i) 2
  obtain ⟨n, hn⟩ := exists_nat_gt (M ^ 2 / (α * δ ^ 2))
  have hpos : 0 < α * δ ^ 2 := mul_pos hα (sq_pos_of_pos hδ)
  have hn' : M ^ 2 < (n : ℝ) * (α * δ ^ 2) := (div_lt_iff₀ hpos).mp hn
  nlinarith [hbound n]

end Signs

end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.Lists ----
namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

section CompletedLists

open UniformSpace Completion
variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

theorem completedSigma_continuous (n : ℕ) : Continuous (completedSigma L o n) :=
  continuous_const.mul (completedCoordinate_continuous L o n)

theorem completedSigma_le (n : ℕ) (z : TestSpace L o) :
    completedSigma L o n z ≤ (squareWeight n : ℝ)⁻¹ * ‖z‖ := by
  induction z using Completion.induction_on with
  | hp => exact isClosed_le (completedSigma_continuous L o n) (by fun_prop)
  | ih m =>
    change completedSigma L o n (toTestSpace L o m) ≤
      (squareWeight n : ℝ)⁻¹ * ‖toTestSpace L o m‖
    rw [completedSigma_coe, norm_toTestSpace]
    exact sigma_le_preNorm L o n m

theorem completedList_le_sigma (n : ℕ)
    (l : AdmissibleList (L (triple n).1) (listConstant n)) (z : TestSpace L o) :
    ‖completedList L o n l z‖ ≤ completedSigma L o n z := by
  induction z using Completion.induction_on with
  | hp =>
    exact isClosed_le (completedList L o n l).continuous.norm
      (completedSigma_continuous L o n)
  | ih m =>
    change ‖completedList L o n l (toTestSpace L o m)‖ ≤
      completedSigma L o n (toTestSpace L o m)
    rw [completedList_coe, completedSigma_coe]
    exact list_le_sigma _ _ _ o l m

end CompletedLists

section InterpolationAndDenseLimits

 theorem finite_lp_norm_rpow {ι : Type*} [Fintype ι]
    (p : ℝ≥0∞) (hp : 0 < p.toReal) (x : PiLp p (fun _ : ι => ℝ)) :
    ‖x‖ ^ p.toReal = ∑ i, |x i| ^ p.toReal := by
  rw [PiLp.norm_eq_sum hp, ← Real.rpow_mul (Finset.sum_nonneg
    (fun i _ => Real.rpow_nonneg (norm_nonneg _) _))]
  rw [one_div_mul_cancel hp.ne', Real.rpow_one]
  simp only [Real.norm_eq_abs]

end InterpolationAndDenseLimits

end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.Pairings ----
namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

section CompletedPairings

open UniformSpace Completion
variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

theorem completedTest_eq (f : S → ℝ) (K : ℝ≥0)
    (h : ∀ m : PreSpace L o, |pairing S f m| ≤ K * ‖m‖) (z : TestSpace L o) :
    completedTest L o f K h z = completedPairing L o f z := by
  induction z using Completion.induction_on with
  | hp => exact isClosed_eq (completedTest L o f K h).continuous Completion.continuous_extension
  | ih m =>
    change (initialPairing L o f K h).extend (toTestSpace L o) (toTestSpace L o m) =
      completedPairing L o f (toTestSpace L o m)
    rw [ContinuousLinearMap.extend_eq _ Completion.denseRange_coe
      (Completion.isUniformInducing_coe (PreSpace L o)), completedPairing_coe L o f K h]
    rfl

theorem list_test_pairing_bound (n : ℕ)
    (l : AdmissibleList (L (triple n).1) (listConstant n)) (i : Fin l.length)
    (m : PreSpace L o) : |pairing S (l.test i) m| ≤ (squareWeight n)⁻¹ * ‖m‖ := by
  have h := PiLp.norm_apply_le (l.eval (listExponent n) (show Molecule S from m)) i
  change |pairing S (l.test i) m| ≤ ‖l.eval (listExponent n) m‖ at h
  exact h.trans ((list_le_sigma _ _ _ o l m).trans (sigma_le_preNorm L o n m))

theorem completedList_apply (n : ℕ)
    (l : AdmissibleList (L (triple n).1) (listConstant n)) (z : TestSpace L o) (i : Fin l.length) :
    completedList L o n l z i = completedPairing L o (l.test i) z := by
  induction z using Completion.induction_on with
  | hp =>
    exact isClosed_eq ((PiLp.proj (listExponent n) (𝕜 := ℝ) (fun _ : Fin l.length => ℝ) i).continuous.comp
      (completedList L o n l).continuous) Completion.continuous_extension
  | ih m =>
    change completedList L o n l (toTestSpace L o m) i =
      completedPairing L o (l.test i) (toTestSpace L o m)
    rw [completedList_coe, completedPairing_coe L o (l.test i) ((squareWeight n)⁻¹)
      (list_test_pairing_bound L o n l i)]
    rfl

end CompletedPairings

section FurtherDetectors

variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

end FurtherDetectors

end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.Operations ----
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

namespace SignedBound
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {m : ℕ → X} {M : ℝ} (hm : SignedBound m M)

include hm

theorem initial : ∀ n (ε : Fin n → Bool), ‖∑ i, realSign (ε i) • m i‖ ≤ M :=
  fun n ε => hm n Fin.val Fin.val_injective ε

theorem nonneg : 0 ≤ M := by
  simpa using hm.initial 0 (fun i => Fin.elim0 i)

end SignedBound

theorem compatible_detectors_false {S : Type*} [MetricSpace S]
    (L : ℕ → Set (S → ℝ)) (o : S)
    (m : ℕ → TestSpace L o) (M : ℝ) (hm : SignedBound m M)
    (F : ℕ → S → ℝ) (h : ℕ) (K : ℝ≥0) (hF : ∀ i, F i ∈ L h)
    (hLip : ∀ n (ε : Fin n → ℝ), (∀ i, |ε i|=1) →
      LipschitzWith K (fun s => ∑ i, ε i*F i s))
    {δ : ℝ} (hδ : 0 < δ) (hd : ∀ i, δ ≤ |completedPairing L o (F i) (m i)|) : False := by
  obtain ⟨C,hC⟩ := exists_nat_gt (K : ℝ)
  obtain ⟨d,hdtriple⟩ := triple_surjective (h,C,0)
  have hKC : K ≤ listConstant d := by
    change K ≤ ((triple d).2.1 : ℝ≥0)+1
    rw [hdtriple]
    exact_mod_cast (show (K : ℝ) ≤ (C : ℝ)+1 by linarith)
  let l (n : ℕ) : AdmissibleList (L (triple d).1) (listConstant d) :=
    ⟨n,fun i => F i,fun i => by simpa only [hdtriple] using hF i,
      fun ε hε => (hLip n ε hε).weaken hKC⟩
  have hExp : (listExponent d).toReal = 2 := by rw [listExponent_toReal,hdtriple]; norm_num
  have hb (i : ℕ) : ∃ A : ℝ≥0, ∀ z : PreSpace L o, |pairing S (F i) z| ≤ A*‖z‖ := by
    let j : Fin (i+1) := ⟨i,Nat.lt_succ_self i⟩
    exact ⟨(squareWeight d)⁻¹,list_test_pairing_bound L o d (l (i+1)) j⟩
  choose A hA using hb
  let u (i : ℕ) : TestSpace L o →ₗ[ℝ] ℝ := (completedTest L o (F i) (A i) (hA i)).toLinearMap
  have hu (i : ℕ) (z : TestSpace L o) : u i z = completedPairing L o (F i) z :=
    completedTest_eq L o _ _ _ _
  apply no_infinite_detectors m u ((squareWeight d : ℝ)^2) M δ
    (sq_pos_of_pos (squareWeight_pos d)) hm.nonneg hδ hm.initial
  · intro n z
    have hl := (completedList_le_sigma L o d (l n) z).trans (completedSigma_le L o d z)
    have heq : ‖completedList L o d (l n) z‖^2 = ∑ i : Fin n, (u i z)^2 := by
      have he := finite_lp_norm_rpow (listExponent d) (by rw [hExp]; norm_num)
        (completedList L o d (l n) z)
      rw [hExp] at he
      simp only [Real.rpow_two,sq_abs] at he
      rw [he]
      apply Finset.sum_congr rfl
      intro i hi
      change (completedList L o d (l n) z i)^2 = (u i z)^2
      rw [completedList_apply,hu]
    have hleft : 0 ≤ ‖completedList L o d (l n) z‖ := norm_nonneg _
    have hscale : (squareWeight d : ℝ)*‖completedList L o d (l n) z‖ ≤ ‖z‖ := by
      calc
        _ ≤ (squareWeight d : ℝ)*((squareWeight d : ℝ)⁻¹*‖z‖) :=
          mul_le_mul_of_nonneg_left hl (squareWeight d).coe_nonneg
        _ = ‖z‖ := by rw [← mul_assoc,mul_inv_cancel₀ (ne_of_gt (squareWeight_pos d)),one_mul]
    have hs := pow_le_pow_left₀ (mul_nonneg (squareWeight d).coe_nonneg hleft) hscale 2
    simpa only [mul_pow,heq] using hs
  · intro i
    simpa only [hu] using hd i

variable {Γ : Type*} {B : CylinderBases Γ}

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

namespace CylinderOperation
variable {I : Finset ℕ}

end CylinderOperation

namespace GeneratedRepresentation
variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

end GeneratedRepresentation

variable {Γ : Type*} {B : CylinderBases Γ}

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

namespace TailOperation
end TailOperation

end
end C0Absorption

end OAI

-- ---- platform node ----
open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty


theorem solution : type_of% @_root_.OAI.C0Absorption.compatible_detectors_false := @_root_.OAI.C0Absorption.compatible_detectors_false
