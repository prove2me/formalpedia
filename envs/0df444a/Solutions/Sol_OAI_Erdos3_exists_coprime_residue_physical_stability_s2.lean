-- Prove2me | solution 1 for OAI.Erdos3.exists_coprime_residue_physical_stability_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:14:11.975994+00:00
-- url     : https://prove2.me/submissions/475e5fa4-2dd0-406d-98d4-faadd7d640b7

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B193
import Definitions.Def_OAIE3v2B226
import Theorems.Thm_OAI_Erdos3_exists_physical_stability_parameters_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceCountingCost
namespace OAI

section

namespace Erdos3

theorem scalarResidue_card_mul_le (a b r v : ℤ) (hab : a ≤ b) (hr : 0 < r) :
    ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℤ) * r ≤ b - a + r := by
  have hrQ : (0 : ℚ) < r := by exact_mod_cast hr
  have hc := Int.Ico_filter_modEq_card a b hr v
  have hcQ := congrArg (fun n : ℤ => (n : ℚ)) hc
  simp only [Int.cast_natCast, Int.cast_max, Int.cast_sub, Int.cast_zero] at hcQ
  have hn : (0 : ℚ) ≤ ((b - a : ℤ) : ℚ) / r :=
    div_nonneg (by exact_mod_cast sub_nonneg.mpr hab) hrQ.le
  have hbound : ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℚ) ≤
      ((b - a : ℤ) : ℚ) / r + 1 := by
    rw [hcQ]
    apply max_le
    · have hx := Int.ceil_lt_add_one (((b : ℚ) - v) / r)
      have hy := Int.le_ceil (((a : ℚ) - v) / r)
      have heq : ((b : ℚ) - v) / r - ((a : ℚ) - v) / r = ((b - a : ℤ) : ℚ) / r := by
        push_cast
        ring
      linarith
    · linarith
  have hm := mul_le_mul_of_nonneg_right hbound hrQ.le
  have heq : (((b - a : ℤ) : ℚ) / r + 1) * r = (b - a : ℤ) + (r : ℚ) := by
    field_simp
  rw [heq] at hm
  exact_mod_cast hm

theorem scalarResidue_card_real_le (a b r v : ℤ) (hab : a ≤ b) (hr : 0 < r) :
    ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) ≤
      ((b - a : ℤ) : ℝ) / r + 1 := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have h := scalarResidue_card_mul_le a b r v hab hr
  have hR : ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) * r ≤
      ((b - a : ℤ) : ℝ) + r := by exact_mod_cast h
  have heq : ((b - a : ℤ) : ℝ) + r = (((b - a : ℤ) : ℝ) / r + 1) * r := by
    field_simp
  rw [heq] at hR
  exact (mul_le_mul_iff_left₀ hrR).mp hR

end Erdos3

end

section

namespace Erdos3

theorem scalarResidue_card_mul_ge (a b r v : ℤ) (hr : 0 < r) :
    b - a - r ≤ ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℤ) * r := by
  have hrQ : (0 : ℚ) < r := by exact_mod_cast hr
  have hc := congrArg (fun n : ℤ => (n : ℚ)) (Int.Ico_filter_modEq_card a b hr v)
  simp only [Int.cast_natCast, Int.cast_max, Int.cast_sub, Int.cast_zero] at hc
  have hbound : ((b - a : ℤ) : ℚ) / r - 1 ≤
      ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℚ) := by
    rw [hc]
    apply le_trans _ (le_max_left _ _)
    have hx := Int.le_ceil (((b : ℚ) - v) / r)
    have hy := Int.ceil_lt_add_one (((a : ℚ) - v) / r)
    have heq : ((b : ℚ) - v) / r - ((a : ℚ) - v) / r = ((b - a : ℤ) : ℚ) / r := by
      push_cast
      ring
    linarith
  have hm := mul_le_mul_of_nonneg_right hbound hrQ.le
  have heq : (((b - a : ℤ) : ℚ) / r - 1) * r = ((b - a - r : ℤ) : ℚ) := by
    push_cast
    field_simp
  rw [heq] at hm
  exact_mod_cast hm

theorem scalarResidue_card_absolute_error (a b r v : ℤ) (hab : a ≤ b) (hr : 0 < r) :
    |((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) -
      ((b - a : ℤ) : ℝ) / r| ≤ 1 := by
  have hu := scalarResidue_card_real_le a b r v hab hr
  have hl : ((b - a - r : ℤ) : ℝ) ≤
      ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) * r := by
    exact_mod_cast scalarResidue_card_mul_ge a b r v hr
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have heq : (((b - a : ℤ) : ℝ) / r - 1) * r = ((b - a - r : ℤ) : ℝ) := by
    push_cast
    field_simp
  rw [← heq] at hl
  have hlow := (mul_le_mul_iff_left₀ hrR).mp hl
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Erdos3

end

section

namespace Erdos3

theorem residueIndexLength_eq_card (a b r v : ℤ) (hr : 0 < r) :
    residueIndexLength a b r v =
      (Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card := by
  rw [residueInterval_eq_map a b r v hr, Finset.card_map, Int.card_Ico]
  omega

theorem residueIndexLength_absolute_error (a b r v : ℤ) (hab : a ≤ b) (hr : 0 < r) :
    |(residueIndexLength a b r v : ℝ) - ((b - a : ℤ) : ℝ) / (r : ℝ)| ≤ 1 := by
  rw [residueIndexLength_eq_card a b r v hr]
  exact scalarResidue_card_absolute_error a b r v hab hr

end Erdos3

end

section

namespace Erdos3

theorem residueIndexLength_ge_of_width (a b r v : ℤ) (hr : 0 < r)
    (B : ℝ) (hB : 0 ≤ B) (hwidth : (r : ℝ) * (B + 1) ≤ ((b - a : ℤ) : ℝ)) :
    B ≤ (residueIndexLength a b r v : ℝ) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hwidthpos : (0 : ℝ) < ((b - a : ℤ) : ℝ) :=
    (mul_pos hr' (by linarith : 0 < B + 1)).trans_le hwidth
  have hab : a ≤ b := by
    have h : (0 : ℤ) ≤ b - a := by exact_mod_cast hwidthpos.le
    omega
  have hlower := (abs_le.mp (residueIndexLength_absolute_error a b r v hab hr)).1
  have hratio : B + 1 ≤ ((b - a : ℤ) : ℝ) / (r : ℝ) :=
    (le_div_iff₀ hr').mpr (by simpa only [mul_comm] using hwidth)
  linarith

end Erdos3

end

section

namespace Erdos3

theorem residueIndexLength_half_width (a v : ℤ) (N r : ℕ) (hr : 0 < r)
    (hwidth : 2 * (r : ℝ) ≤ (N : ℝ)) :
    0 < residueIndexLength a (a + N) r v ∧
    (N : ℝ) / 2 ≤ (r : ℝ) * (residueIndexLength a (a + N) r v : ℝ) := by
  have hrz : (0 : ℤ) < r := by exact_mod_cast hr
  have hrr : (0 : ℝ) < r := by exact_mod_cast hr
  have hlength := residueIndexLength_ge_of_width a (a + N) r v hrz 1 (by norm_num)
    (by simpa only [add_sub_cancel_left, Int.cast_natCast] using (show (r : ℝ) * (1 + 1) ≤ (N : ℝ) by linarith))
  have herror := residueIndexLength_absolute_error a (a + N) r v (by omega) hrz
  simp only [add_sub_cancel_left, Int.cast_natCast] at herror
  have hlo := (abs_le.mp herror).1
  have hmul := mul_le_mul_of_nonneg_left hlo hrr.le
  have hdiv : (r : ℝ) * ((N : ℝ) / r) = (N : ℝ) := by field_simp
  refine ⟨?_, ?_⟩
  · exact_mod_cast (show (0 : ℝ) < (residueIndexLength a (a + N) r v : ℝ) by linarith)
  · nlinarith

end Erdos3

end

section

namespace Erdos3

theorem residueIndexLength_large_of_exp (lo a : ℤ) (N M : ℕ) (P B : ℝ)
    (hM : 0 < M) (hB : 0 ≤ B) (hmodulus : (M : ℝ) ≤ Real.exp P)
    (hside : Real.exp (P + B + 2) ≤ (N : ℝ)) :
    Real.exp B ≤ (residueIndexLength lo (lo + N) M a : ℝ) := by
  have hMreal : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hBexp : 1 ≤ Real.exp B := Real.one_le_exp hB
  have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hproduct : 2 * (M : ℝ) * Real.exp B ≤ Real.exp (P + B + 2) := by
    rw [Real.exp_add, Real.exp_add]
    calc
      2 * (M : ℝ) * Real.exp B ≤ 2 * Real.exp P * Real.exp B := by
        gcongr
      _ ≤ Real.exp P * Real.exp B * Real.exp 2 := by
        have hm := mul_le_mul_of_nonneg_left htwo
          (mul_nonneg (Real.exp_pos P).le (Real.exp_pos B).le)
        nlinarith
  have hwidth : 2 * (M : ℝ) ≤ (N : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hBexp (show 0 ≤ 2 * (M : ℝ) by positivity)
    nlinarith [hproduct.trans hside]
  have hlength := (residueIndexLength_half_width lo a N M hM hwidth).2
  apply le_of_mul_le_mul_left (a := (M : ℝ)) _ hMreal
  nlinarith [hproduct.trans hside]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CommonStrideResidueGeometry
namespace OAI

section

namespace Erdos3

theorem commonStridePoint_index_of_modEq {I : Type*} (c : I → ℤ) (m : ℕ) (y : I → ℤ)
    (hy : ∀ i, y i ≡ c i [ZMOD (m : ℤ)]) :
    commonStridePoint c m (commonStrideIndex c m y) = y := by
  funext i
  have hd := Int.modEq_iff_dvd.mp (hy i).symm
  change c i + (m : ℤ) * ((y i - c i) / (m : ℤ)) = y i
  rw [mul_comm, Int.ediv_mul_cancel hd]
  omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RankAdaptedNiltest
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.AdaptedModelData

open Module CircleFourier
open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} (F : D.AdaptedModelData) (H : ℕ)
  (hH : ∀ i j, RationalHeightLE (D.basis.repr (F.basis i) j) H) {w : σ → ℕ}

theorem rebaseNiltest_eval (T : D.Niltest w) (x : σ → ℤ) : (F.rebaseNiltest H hH T).eval x = T.eval x := rfl

theorem rebaseNiltest_unit_interval (T : D.Niltest w) (hT : T.UnitIntervalValued) :
    (F.rebaseNiltest H hH T).UnitIntervalValued := hT

end Erdos3.RationalFilteredNilmanifold.AdaptedModelData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledAdaptedRebase
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct

theorem exists_controlled_adapted_rebase :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p →
      ∃ (F : D.AdaptedModelData) (H : ℕ)
        (hH : ∀ i j, RationalHeightLE (D.basis.repr (F.basis i) j) H),
        p ≤ (p + C) ^ C ∧ F.model.GeometryComplexityLE ((p + C) ^ C) ∧
        (∀ {σ : Type*} {w : σ → ℕ} (T : D.Niltest w), T.ComplexityLE p →
          (F.rebaseNiltest H hH T).ComplexityLE ((p + C) ^ C)) ∧
        ∀ eta : L →ₗ[ℚ] ℚ, (∀ i, rationalLogHeight (eta (D.basis i)) ≤ p) →
          ∀ j, rationalLogHeight (eta (F.model.basis j)) ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let R := (X + 3) ^ 11 + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + (R + 2) ^ 2 + (X + 3) ^ 4 + X)
  refine ⟨C, hC, ?_⟩
  intro L _ _ s d _ _ _ _ D p hp hD
  obtain ⟨F, hF, hb⟩ := D.exists_adapted_model_data hp hD
  let H := ⌈Real.exp (p + 1)⌉₊
  have hH (i j) : RationalHeightLE (D.basis.repr (F.basis i) j) H :=
    rationalHeightLE_ceil_exp (hb i j)
  let r := (p + 3) ^ 11 + p + 2
  have hpow : 0 ≤ (p + 3) ^ 11 := by positivity
  have hpr : p ≤ r := by dsimp [r]; linarith
  have hfr : (p + 3) ^ 11 ≤ r := by dsimp [r]; linarith
  have hHbound : (H : ℝ) ≤ Real.exp r :=
    (ceil_exp_le_exp_add_one (by linarith : 0 ≤ p + 1)).trans
      (Real.exp_le_exp.mpr (by dsimp [r]; linarith))
  have hr : 0 ≤ r := hp.trans hpr
  have hbud : r + (r + 2) ^ 2 + (p + 3) ^ 4 + p ≤ (p + C) ^ C := by
    simpa [R, X, r, Polynomial.eval₂_pow] using hbudget p hp
  have hfreq0 : 0 ≤ (p + 3) ^ 4 := by positivity
  have hcomp : r + (r + 2) ^ 2 ≤ (p + C) ^ C := by linarith
  have hfreq : (p + 3) ^ 4 ≤ (p + C) ^ C := by nlinarith [sq_nonneg (r + 2)]
  have hbase : p ≤ (p + C) ^ C := hpr.trans ((le_add_of_nonneg_right (sq_nonneg _)).trans hcomp)
  have hgeom : F.model.GeometryComplexityLE r := hF.mono F.model hfr
  refine ⟨F, H, hH, hbase, hgeom.mono F.model
    ((le_add_of_nonneg_right (sq_nonneg _)).trans hcomp), ?_, ?_⟩
  · intro σ w T hT
    exact (F.rebaseNiltest_complexity H hH T hr (hT.mono hpr) hgeom hHbound).mono hcomp
  · intro eta heta j
    have hdim : (Fintype.card (Fin d) : ℝ) ≤ p + 1 := by
      simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ p + 1 by linarith)
    have hval := rational_functional_value_logHeight D.basis eta
      (by linarith : 0 ≤ p + 1) hdim (fun i => (heta i).trans (by linarith : p ≤ p + 1))
      (F.basis j) (hb j)
    apply le_trans _ hfreq
    change rationalLogHeight (eta (F.basis j)) ≤ (p + 3) ^ 4
    simpa only [show p + 1 + 2 = p + 3 by ring] using hval

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.EpochEventRank
namespace OAI

section

namespace Erdos3

theorem EpochStackEvent.length_eq {d : ℕ} {xs ys : List ℕ} (h : EpochStackEvent d xs ys) :
    ys.length = xs.length := by
  induction h with
  | head _ hlen _ => simpa only [List.length_cons] using congrArg Nat.succ hlen
  | tail _ ih => simpa only [List.length_cons] using congrArg Nat.succ ih

theorem epochStackRank_lt (d : ℕ) (xs : List ℕ) (hbounded : ∀ q ∈ xs, q ≤ d) :
    epochStackRank d xs < (d + 1) ^ xs.length := by
  revert hbounded
  induction xs with
  | nil => simp [epochStackRank]
  | cons r xs ih =>
    intro hbounded
    have hr : r ≤ d := hbounded r (by simp)
    have ht := ih (fun q hq => hbounded q (by simp [hq]))
    change r * (d + 1) ^ xs.length + epochStackRank d xs < (d + 1) ^ (xs.length + 1)
    calc
      r * (d + 1) ^ xs.length + epochStackRank d xs <
          r * (d + 1) ^ xs.length + (d + 1) ^ xs.length := Nat.add_lt_add_left ht _
      _ = (r + 1) * (d + 1) ^ xs.length := by ring
      _ ≤ (d + 1) * (d + 1) ^ xs.length := Nat.mul_le_mul_right _ (Nat.add_le_add_right hr 1)
      _ = (d + 1) ^ (xs.length + 1) := by rw [pow_succ]; ring

theorem EpochStackEvent.rank_lt {d : ℕ} {xs ys : List ℕ} (h : EpochStackEvent d xs ys) :
    epochStackRank d ys < epochStackRank d xs := by
  induction h with
  | @head r r' xs ys hdrop hlen hbounded =>
    have htail := epochStackRank_lt d ys hbounded
    change r' * (d + 1) ^ ys.length + epochStackRank d ys <
      r * (d + 1) ^ xs.length + epochStackRank d xs
    rw [hlen] at htail ⊢
    calc
      r' * (d + 1) ^ xs.length + epochStackRank d ys <
          r' * (d + 1) ^ xs.length + (d + 1) ^ xs.length := Nat.add_lt_add_left htail _
      _ = (r' + 1) * (d + 1) ^ xs.length := by ring
      _ ≤ r * (d + 1) ^ xs.length := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hdrop)
      _ ≤ r * (d + 1) ^ xs.length + epochStackRank d xs := Nat.le_add_right _ _
  | @tail r xs ys hevent ih =>
    change r * (d + 1) ^ ys.length + epochStackRank d ys <
      r * (d + 1) ^ xs.length + epochStackRank d xs
    rw [hevent.length_eq]
    exact Nat.add_lt_add_left ih _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PhysicalEpochComparison
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

universe u v

attribute [instance] PhysicalEpochSource.lieRing PhysicalEpochSource.lieAlgebra
  PhysicalEpochSource.topology PhysicalEpochSource.topologicalAddGroup
  PhysicalEpochSource.continuousSMul PhysicalEpochSource.t2Space

namespace PhysicalEpochRecords

variable {σ : Type u} [Fintype σ] {s bound : ℕ} {base : PhysicalEpochSource.{u, v} σ s bound}

theorem dimension_le (state : PhysicalEpochRecords base) : state.dimension ≤ bound := by
  have h := lie_subalgebra_finrank_le
    (base.model.filtration.associatedGradedBasis base.model.basis base.weights base.adapted)
    (epochRecordIntersection state.records)
  have hdim : state.dimension ≤ base.dimension := by simpa only [dimension, Fintype.card_fin] using h
  exact hdim.trans base.dimension_le

end PhysicalEpochRecords

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ScheduledPhysicalEpochStack
namespace OAI

section

namespace Erdos3

theorem physicalEpochBudget_nonneg (A C : ℕ) {b : ℝ} (hb : 0 ≤ b) (k : ℕ) :
    0 ≤ physicalEpochBudget A C b k := by
  induction k with
  | zero => exact hb
  | succ k ih => simp only [physicalEpochBudget]; positivity

theorem physicalEpochBudget_work_le {A C : ℕ} (hA : 1 ≤ A) {b : ℝ} (hb : 0 ≤ b) (k : ℕ) :
    (physicalEpochBudget A C b k + 2) ^ C ≤ physicalEpochBudget A C b (k + 1) := by
  have hx := physicalEpochBudget_nonneg A C hb k
  have hp : 0 ≤ (physicalEpochBudget A C b k + 2) ^ C := by positivity
  change (physicalEpochBudget A C b k + 2) ^ C ≤ ((physicalEpochBudget A C b k + 2) ^ C + 2) ^ A
  calc
    (physicalEpochBudget A C b k + 2) ^ C ≤ (physicalEpochBudget A C b k + 2) ^ C + 2 := by linarith
    _ = ((physicalEpochBudget A C b k + 2) ^ C + 2) ^ 1 := (pow_one _).symm
    _ ≤ ((physicalEpochBudget A C b k + 2) ^ C + 2) ^ A := pow_le_pow_right₀ (by linarith) hA

theorem physicalEpochBudget_mono {A C : ℕ} (hA : 1 ≤ A) (hC : 1 ≤ C) {b : ℝ} (hb : 0 ≤ b) :
    Monotone (physicalEpochBudget A C b) := by
  apply monotone_nat_of_le_succ
  intro k
  have hx := physicalEpochBudget_nonneg A C hb k
  calc
    physicalEpochBudget A C b k ≤ physicalEpochBudget A C b k + 2 := by linarith
    _ = (physicalEpochBudget A C b k + 2) ^ 1 := (pow_one _).symm
    _ ≤ (physicalEpochBudget A C b k + 2) ^ C := pow_le_pow_right₀ (by linarith) hC
    _ ≤ physicalEpochBudget A C b (k + 1) := physicalEpochBudget_work_le hA hb k

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

universe u v

namespace PhysicalEpochStack

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {bound s : ℕ}
  {base : PhysicalEpochSource.{u, v} σ s bound}

theorem dimensions_length (stack : PhysicalEpochStack base) : stack.dimensions.length = s := by
  induction stack with
  | zero => rfl
  | succ frame tail ih => simp only [dimensions, List.length_cons, ih]

theorem dimensions_bounded (stack : PhysicalEpochStack base) :
    ∀ q ∈ stack.dimensions, q ≤ bound := by
  induction stack with
  | zero => simp [dimensions]
  | succ frame tail ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact frame.state.dimension_le
    · exact ih q hq

theorem Event.to_dimension_event {oldStack newStack : PhysicalEpochStack base}
    (event : Event oldStack newStack) :
    EpochStackEvent bound oldStack.dimensions newStack.dimensions := by
  induction event with
  | @head s base oldFrame newFrame record records modulus anchor oldTail newTail =>
    have hhistory := newFrame.state.history
    rw [records] at hhistory
    have hdrop : newFrame.state.dimension < oldFrame.state.dimension := by
      cases hhistory with
      | cons history drop =>
        change finrank ℚ (epochRecordIntersection newFrame.state.records) < _
        rw [records]
        change finrank ℚ ↥(record.fast ⊓ epochRecordIntersection oldFrame.state.records) < _
        rw [inf_comm record.fast]
        exact drop
    exact EpochStackEvent.head hdrop
      (newTail.dimensions_length.trans oldTail.dimensions_length.symm) newTail.dimensions_bounded
  | tail frame event ih => exact EpochStackEvent.tail ih

theorem Event.rank_lt {oldStack newStack : PhysicalEpochStack base}
    (event : Event oldStack newStack) :
    epochStackRank bound newStack.dimensions < epochStackRank bound oldStack.dimensions :=
  event.to_dimension_event.rank_lt

end PhysicalEpochStack

end Erdos3

end

section

namespace Erdos3.PhysicalEpochStack

universe u v

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {bound s : ℕ}
  {base : PhysicalEpochSource.{u, v} σ s bound}

theorem UniformAt.budgeted {A M : ℕ} {anchor : σ → ℤ} {budget : ℝ} {power : ℕ}
    {stack : PhysicalEpochStack base} (h : UniformAt A M anchor budget power stack)
    (hinflate : (base.incomingBudget + 2) ^ A ≤ base.recordBudget) : BudgetedAt A budget power stack := by
  induction stack with
  | zero => exact ⟨h.2, hinflate⟩
  | succ frame tail ih =>
    obtain ⟨_, hr, _, _, hw, hp, hf, he, hi, ht⟩ := h
    exact ⟨hr, hinflate, hw, hp, hf, he, ih ht (le_of_eq hi.symm)⟩

theorem AlignedAt.refine {M N : ℕ} {anchor refined : σ → ℤ}
    {stack : PhysicalEpochStack base} (h : AlignedAt M anchor stack)
    (hMN : M ∣ N) (hanchor : ∀ i, refined i ≡ anchor i [ZMOD (M : ℤ)]) :
    AlignedAt N refined stack := by
  induction stack with
  | zero => trivial
  | succ frame tail ih =>
    obtain ⟨hm, ha, ht⟩ := h
    refine ⟨hm.trans hMN, ?_, ih ht⟩
    intro i
    exact (Int.ModEq.of_dvd (by exact_mod_cast hm) (hanchor i)).trans (ha i)

end Erdos3.PhysicalEpochStack

end

section

namespace Erdos3.PhysicalEpochStack

universe u v

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {bound s : ℕ}
  {base : PhysicalEpochSource.{u, v} σ s bound}

theorem ScheduledAt.inflation {A C depth : ℕ} {b : ℝ} {stack : PhysicalEpochStack base}
    (h : ScheduledAt A C b depth stack) : (base.incomingBudget + 2) ^ A ≤ base.recordBudget := by
  cases stack with
  | zero => exact h.2
  | succ => exact h.2.1

theorem ScheduledAt.budgeted {A C depth : ℕ} {b : ℝ} {stack : PhysicalEpochStack base}
    (h : ScheduledAt A C b depth stack) (hA : 1 ≤ A) (hC : 1 ≤ C) (hb : 0 ≤ b) :
    BudgetedAt A (physicalEpochBudget A C b (depth + s)) C stack := by
  induction stack generalizing depth with
  | zero => exact h
  | @succ s base frame tail ih =>
    obtain ⟨hr, hi, hw, hp, hf, he, ht⟩ := h
    have hmono := physicalEpochBudget_mono hA hC hb
    have hroot : physicalEpochBudget A C b depth ≤ physicalEpochBudget A C b (depth + (s + 1)) :=
      hmono (by omega)
    have hwork : (physicalEpochBudget A C b depth + 2) ^ C ≤
        physicalEpochBudget A C b (depth + (s + 1)) :=
      (physicalEpochBudget_work_le hA hb depth).trans (hmono (by omega))
    refine ⟨hr.trans hroot, hi, hw.trans hwork, hp.trans (Real.exp_le_exp.mpr hwork), hf, he, ?_⟩
    have hidx : depth + 1 + s = depth + (s + 1) := by omega
    simpa only [hidx] using ih ht

end Erdos3.PhysicalEpochStack

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformPhysicalVisitBounds
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

namespace RationalFilteredNilmanifold.Niltest

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d}

theorem scalarAffinePullback_eval_stride (T : D.Niltest (fun _ : σ => 1))
    (M : ℕ) (u x : σ → ℤ) (hx : ∀ i, x i ≡ u i [ZMOD (M : ℤ)]) :
    (T.scalarAffinePullback (M : ℚ) (fun i => (u i : ℚ))).eval (commonStrideIndex u M x) = T.eval x := by
  have heq : (fun i => (M : ℤ) * commonStrideIndex u M x i + u i) = x := by
    funext i
    have h := congrFun (commonStridePoint_index_of_modEq u M x hx) i
    change u i + (M : ℤ) * commonStrideIndex u M x i = x i at h
    linarith
  simpa only [Int.cast_natCast, heq] using T.scalarAffinePullback_eval_integer (M : ℤ) u (commonStrideIndex u M x)

theorem scalarAffinePullback_pair_false [Fintype σ] [DecidableEq σ]
    (T : D.Niltest (fun _ : σ => 1)) (lo : σ → ℤ) (N : σ → ℕ) (M J : ℕ) (u v : σ → ℤ) :
    residuePairMean (T.scalarAffinePullback (M : ℚ) (fun i => (u i : ℚ))).eval lo N M u v (fun _ => J) false =
      physicalResidueMean T.eval lo N M u := by
  rw [residuePairMean_false]
  apply Finset.expect_congr rfl
  intro x _
  exact T.scalarAffinePullback_eval_stride M u (fun i => (x i).val)
    (fun i => (Finset.mem_filter.mp (x i).property).2)

theorem scalarAffinePullback_pair_true [Fintype σ] [DecidableEq σ]
    (T : D.Niltest (fun _ : σ => 1)) (lo : σ → ℤ) (N : σ → ℕ) (M J : ℕ) (u v : σ → ℤ)
    (hv : ∀ i, v i ≡ u i [ZMOD (M : ℤ)]) :
    residuePairMean (T.scalarAffinePullback (M : ℚ) (fun i => (u i : ℚ))).eval lo N M u v (fun _ => J) true =
      physicalResidueMean T.eval lo N (M * J) v := by
  rw [residuePairMean_true]
  apply Finset.expect_congr rfl
  intro x _
  apply T.scalarAffinePullback_eval_stride
  intro i
  have hd : (M : ℤ) ∣ ((M * J : ℕ) : ℤ) := by exact_mod_cast Nat.dvd_mul_right M J
  exact (Int.ModEq.of_dvd hd (Finset.mem_filter.mp (x i).property).2).trans (hv i)

end RationalFilteredNilmanifold.Niltest

universe u v

theorem exists_initial_physical_comparison
    {σ : Type u} [Fintype σ] [DecidableEq σ] {s bound m J : ℕ} {gap : ℝ}
    (base : PhysicalEpochSource.{u, v} σ s bound) (T : base.model.Niltest (fun _ : σ => 1))
    (horbit : T.orbit = base.fixedMap.orbit) (hpositive : T.UnitIntervalValued)
    (hcomplexity : T.ComplexityLE base.incomingBudget)
    (hm : 0 < m) (hJ : 0 < J) (anchor refined : σ → ℤ)
    (hanchor : ∀ i, base.lower i ≤ anchor i ∧ anchor i < base.lower i + base.sides i)
    (hrefined : ∀ i, base.lower i ≤ refined i ∧ refined i < base.lower i + base.sides i)
    (hcompat : ∀ i, refined i ≡ anchor i [ZMOD (m : ℤ)])
    (hgap : 0 < gap) (hgap1 : gap ≤ 1) (hinverse : gap⁻¹ ≤ Real.exp base.incomingBudget)
    (hrecord : 2 ≤ base.recordBudget)
    (hdiscrepancy : gap ≤ ‖physicalResidueMean T.eval base.lower base.sides m anchor -
      physicalResidueMean T.eval base.lower base.sides (m * J) refined‖) :
    ∃ c : PhysicalEpochComparison base m 1 J gap,
      c.Controlled ∧ c.anchor = anchor ∧ c.refined = refined ∧ c.lower = base.lower ∧ c.sides = base.sides := by
  let S := T.scalarAffinePullback (m : ℚ) (fun i => (anchor i : ℚ))
  have hSorbit : S.orbit = (base.fixedMap.scalarAffinePullback (m : ℚ) (fun i => (anchor i : ℚ))).orbit := by
    dsimp only [S, RationalFilteredNilmanifold.Niltest.scalarAffinePullback,
      RationalFilteredNilmanifold.Niltest.substitute]
    rw [horbit]
  have hpair : gap ≤ ‖residuePairMean S.eval base.lower base.sides m anchor refined (fun _ => J) false -
      residuePairMean S.eval base.lower base.sides m anchor refined (fun _ => J) true‖ := by
    rw [T.scalarAffinePullback_pair_false, T.scalarAffinePullback_pair_true _ _ _ _ _ _ hcompat]
    exact hdiscrepancy
  let c : PhysicalEpochComparison base m 1 J gap := {
    selected_pos := hm
    auxiliary_pos := by omega
    pending_pos := hJ
    lower := base.lower
    sides := base.sides
    sides_pos := base.sides_pos
    contained := fun _ => ⟨le_rfl, le_rfl⟩
    anchor := anchor
    refined := refined
    anchor_inside := hanchor
    refined_inside := hrefined
    compatible := by simpa only [Nat.mul_one] using hcompat
    test := S
    orbit := by simpa only [Nat.mul_one] using hSorbit
    positive := hpositive
    complexity := hcomplexity
    gap_pos := hgap
    gap_le_one := hgap1
    gap_inverse := hinverse
    discrepancy := by simpa only [Nat.mul_one] using hpair }
  refine ⟨c, ?_, rfl, rfl, rfl, rfl⟩
  have htwo : 2 ≤ Real.exp base.recordBudget := by linarith [Real.add_one_le_exp base.recordBudget]
  have hcoef : 2 * Real.exp (-base.recordBudget) ≤ 1 := by
    calc
      2 * Real.exp (-base.recordBudget) ≤ Real.exp base.recordBudget * Real.exp (-base.recordBudget) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add]; simp
  exact ⟨by simp only [Nat.cast_one]; linarith,
    fun i => by simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg (α := ℝ) (base.sides i))⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrimeCoordinateCells
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem periodPrimeCoordinates_card_pow_le {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime)
    {M : ℕ} (hM : 0 < M) : 2 ^ (periodPrimeCoordinates prime M).card ≤ M := by
  classical
  let A := periodPrimeCoordinates prime M
  have hsub : A.image prime ⊆ M.primeFactors := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hprime i, (mem_periodPrimeCoordinates prime M i).mp hi, hM.ne'⟩
  have hcard : A.card ≤ M.primeFactors.card := by
    rw [← Finset.card_image_of_injective A hinj]
    exact Finset.card_le_card hsub
  calc
    2 ^ A.card ≤ 2 ^ M.primeFactors.card := Nat.pow_le_pow_right (by norm_num) hcard
    _ = ∏ _p ∈ M.primeFactors, 2 := by simp
    _ ≤ ∏ p ∈ M.primeFactors, p := Finset.prod_le_prod' fun p hp => (Nat.mem_primeFactors.mp hp).1.two_le
    _ ≤ M := Nat.le_of_dvd hM (Nat.prod_primeFactors_dvd M)

theorem periodPrimeCoordinates_card_log_le {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime)
    {M : ℕ} (hM : 0 < M) :
    (periodPrimeCoordinates prime M).card * Real.log 2 ≤ Real.log M := by
  have hpow : (2 : ℝ) ^ (periodPrimeCoordinates prime M).card ≤ M := by
    exact_mod_cast periodPrimeCoordinates_card_pow_le prime hprime hinj hM
  simpa only [Real.log_pow] using Real.log_le_log (by positivity) hpow

theorem periodPrimeCoordinates_card_le {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime)
    {M : ℕ} (hM : 0 < M) {B : ℝ} (hMB : (M : ℝ) ≤ Real.exp B) :
    ((periodPrimeCoordinates prime M).card : ℝ) ≤ 2 * B := by
  have h := (periodPrimeCoordinates_card_log_le prime hprime hinj hM).trans
    ((Real.log_le_iff_le_exp (by exact_mod_cast hM)).mpr hMB)
  have hlog : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have ht := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at ht ⊢
    linarith
  have hc : (0 : ℝ) ≤ (periodPrimeCoordinates prime M).card := Nat.cast_nonneg _
  nlinarith

theorem periodPrimeCoordinates_pending_coprime {ι : Type*} [Fintype ι]
    (prime power : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (M : ℕ) (J : Finset ι)
    (hJ : Disjoint J (periodPrimeCoordinates prime M)) :
    Nat.Coprime (∏ i ∈ J, prime i ^ power i) M := by
  classical
  apply Nat.coprime_prod_left_iff.mpr
  intro i hi
  apply Nat.Coprime.pow_left
  apply (hprime i).coprime_iff_not_dvd.mpr
  intro hd
  exact Finset.disjoint_left.mp hJ hi ((mem_periodPrimeCoordinates prime M i).mpr hd)

theorem disjoint_prime_power_products_coprime {ι : Type*} [Fintype ι]
    (prime power : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime)
    (A B : Finset ι) (hAB : Disjoint A B) :
    Nat.Coprime (∏ i ∈ A, prime i ^ power i) (∏ j ∈ B, prime j ^ power j) := by
  classical
  apply Nat.coprime_prod_left_iff.mpr
  intro i hi
  apply Nat.coprime_prod_right_iff.mpr
  intro j hj
  apply Nat.Coprime.pow
  apply (Nat.coprime_primes (hprime i) (hprime j)).mpr
  intro heq
  have hij := hinj heq
  exact Finset.disjoint_left.mp hAB hi (hij.symm ▸ hj)

theorem periodPrimeCoordinates_unfixed_coprime {ι : Type*} [Fintype ι] [DecidableEq ι]
    (prime power : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime)
    (M : ℕ) (K J : Finset ι)
    (hJ : Disjoint J (K ∪ periodPrimeCoordinates prime M)) :
    Nat.Coprime (∏ i ∈ J, prime i ^ power i) ((∏ i ∈ K, prime i ^ power i) * M) := by
  have hJK : Disjoint J K := hJ.mono_right Finset.subset_union_left
  have hJM : Disjoint J (periodPrimeCoordinates prime M) := hJ.mono_right Finset.subset_union_right
  exact (disjoint_prime_power_products_coprime prime power hprime hinj J K hJK).mul_right
    (periodPrimeCoordinates_pending_coprime prime power hprime M J hJM)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem selectedPrimePowers_pairwise_coprime {ι : Type*}
    (prime power : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime) :
    Pairwise (fun i j => (prime i ^ power i).Coprime (prime j ^ power j)) := by
  intro i j hij
  apply Nat.Coprime.pow
  apply (Nat.coprime_primes (hprime i) (hprime j)).mpr
  intro heq
  exact hij (hinj heq)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem primeCoordinateCell_anchor {ι σ : Type*} [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ) (I : Finset ι) (x : ∀ i, σ → ZMod (q i))
    (u : σ → ℤ) (hu : u ∈ primeCoordinateCell lo N q I x) :
    primeCoordinateCell lo N q I x = primeCoordinateCell lo N q I (fun i j => (u j : ZMod (q i))) := by
  ext z
  simp only [mem_primeCoordinateCell] at hu ⊢
  constructor
  · rintro ⟨hz, heq⟩
    exact ⟨hz, fun i hi => (heq i hi).trans (hu.2 i hi).symm⟩
  · rintro ⟨hz, heq⟩
    exact ⟨hz, fun i hi => (heq i hi).trans (hu.2 i hi)⟩

theorem primeCoordinateCell_mean {ι σ : Type*} [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ)
    (hcop : Pairwise (fun i j => (q i).Coprime (q j))) (I : Finset ι) (u : σ → ℤ)
    (f : (σ → ℤ) → ℂ) :
    (𝔼 z : primeCoordinateCell lo N q I (fun i j => (u j : ZMod (q i))), f z.val) =
      physicalResidueMean f lo N (∏ i ∈ I, q i) u := by
  exact Fintype.expect_equiv (primeCoordinateCellEquiv lo N q hcop I u) _ _ (fun _ => rfl)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalStabilityParameters
namespace OAI

section

namespace Erdos3.PhysicalEpochStack

open scoped BigOperators

universe u v

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {bound s : ℕ}
  {base : PhysicalEpochSource.{u, v} σ s bound}

theorem periods_product_pos (stack : PhysicalEpochStack base) : 0 < stack.periods.prod := by
  induction stack with
  | zero => simp [periods]
  | succ frame tail ih => exact Nat.mul_pos frame.period_pos ih

theorem UniformAt.periods_product_le {A M : ℕ} {anchor : σ → ℤ} {budget : ℝ} {power : ℕ}
    {stack : PhysicalEpochStack base} (h : UniformAt A M anchor budget power stack) :
    (stack.periods.prod : ℝ) ≤ Real.exp ((s : ℝ) * budget) := by
  revert h
  induction stack with
  | zero => intro h; simp [periods]
  | @succ t base frame tail ih =>
    intro h
    obtain ⟨_, _, _, _, _, hperiod, _, _, _, htail⟩ := h
    change ((frame.period * tail.periods.prod : ℕ) : ℝ) ≤ _
    rw [Nat.cast_mul]
    calc
      (frame.period : ℝ) * tail.periods.prod ≤ Real.exp budget * Real.exp ((t : ℝ) * budget) :=
        mul_le_mul hperiod (ih htail) (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (((t + 1 : ℕ) : ℝ) * budget) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring

theorem UniformAt.period_exclusions_card_le {A M : ℕ} {anchor : σ → ℤ} {budget logM : ℝ}
    {power : ℕ} {stack : PhysicalEpochStack base}
    (h : UniformAt A M anchor budget power stack) (hM : 0 < M) (hMb : (M : ℝ) ≤ Real.exp logM)
    {ι : Type*} [Fintype ι] (prime : ι → ℕ) (hprime : ∀ i, (prime i).Prime)
    (hinj : Function.Injective prime) :
    ((periodPrimeCoordinates prime (M * stack.periods.prod)).card : ℝ) ≤ 2 * (logM + (s : ℝ) * budget) := by
  apply periodPrimeCoordinates_card_le prime hprime hinj (Nat.mul_pos hM stack.periods_product_pos)
  rw [Nat.cast_mul, Real.exp_add]
  exact mul_le_mul hMb h.periods_product_le (Nat.cast_nonneg _) (Real.exp_nonneg _)

end Erdos3.PhysicalEpochStack

end

section

namespace Erdos3

open PhysicalEpochStack

universe u v

theorem exists_scheduled_physical_epoch_stack (A C limit : ℕ) (hA : 1 ≤ A) (hC : 1 ≤ C)
    (hframes : ∀ t : ℕ, t ≤ limit → PhysicalFrameConstructionBound.{u, v} t C)
    (b : ℝ) (hb : 0 ≤ b) (s : ℕ) :
    s ≤ limit → ∀ depth : ℕ, ∀ {σ : Type u} [Fintype σ] [DecidableEq σ] {bound : ℕ}
      (base : PhysicalEpochSource.{u, v} σ s bound) (state : PhysicalEpochRecords base)
      (M : ℕ), 0 < M → ∀ anchor : σ → ℤ,
      (∀ i, base.lower i ≤ anchor i ∧ anchor i < base.lower i + base.sides i) →
      (∀ r ∈ state.records, r.modulus ∣ M) →
      base.recordBudget ≤ physicalEpochBudget A C b depth →
      (base.incomingBudget + 2) ^ A ≤ base.recordBudget →
      (∀ i, Real.exp (physicalEpochBudget A C b (depth + s)) ≤ (base.sides i : ℝ) / M) →
      ∃ stack : PhysicalEpochStack base, RootState state stack ∧ RootCreatedAt M anchor stack ∧
        AlignedAt M anchor stack ∧ ScheduledAt A C b depth stack := by
  induction s with
  | zero =>
    intro hs depth σ _ _ bound base state M hM anchor hanchor hmod hcap hinflate hlarge
    exact ⟨.zero base, trivial, trivial, trivial, hcap, hinflate⟩
  | succ s ih =>
    intro hs depth σ _ _ bound base state M hM anchor hanchor hmod hcap hinflate hlarge
    have hp : 0 ≤ base.recordBudget := base.incoming_nonneg.trans base.incoming_le_record
    have hbudget := physicalEpochBudget_nonneg A C hb depth
    have hpow : (base.recordBudget + 2) ^ C ≤ (physicalEpochBudget A C b depth + 2) ^ C :=
      pow_le_pow_left₀ (by linarith) (by linarith) C
    have hbound : (physicalEpochBudget A C b depth + 2) ^ C ≤
        physicalEpochBudget A C b (depth + (s + 1)) :=
      (physicalEpochBudget_work_le hA hb depth).trans (physicalEpochBudget_mono hA hC hb (by omega))
    have hinflation : ∀ x : ℝ, 0 ≤ x → x ≤ (x + 2) ^ A := by
      intro x hx
      calc
        x ≤ x + 2 := by linarith
        _ = (x + 2) ^ 1 := (pow_one _).symm
        _ ≤ (x + 2) ^ A := pow_le_pow_right₀ (by linarith) hA
    obtain ⟨frame, hstate, hmodulus, hframeAnchor, hwork, hchildIncoming, hchildRecord, hperiod, hfreeze, hevent⟩ :=
      hframes s (by omega) base state M hM anchor hanchor hmod (fun x => (x + 2) ^ A) hinflation
        (fun i => (Real.exp_le_exp.mpr (hpow.trans hbound)).trans (hlarge i))
    have hchildCap : frame.child.recordBudget ≤ physicalEpochBudget A C b (depth + 1) := by
      rw [hchildRecord]
      change (frame.child.incomingBudget + 2) ^ A ≤ ((physicalEpochBudget A C b depth + 2) ^ C + 2) ^ A
      have hx := frame.child.incoming_nonneg
      have hcost := hchildIncoming.trans hpow
      gcongr
    have hchildInflate : (frame.child.incomingBudget + 2) ^ A ≤ frame.child.recordBudget := le_of_eq hchildRecord.symm
    have hchildAnchor : ∀ i, frame.child.lower i ≤ anchor i ∧ anchor i < frame.child.lower i + frame.child.sides i := by
      simpa only [frame.child_lower, frame.child_sides] using hanchor
    have hidx : depth + 1 + s = depth + (s + 1) := by omega
    have hchildLarge : ∀ i, Real.exp (physicalEpochBudget A C b (depth + 1 + s)) ≤
        (frame.child.sides i : ℝ) / M := by
      simpa only [frame.child_sides, hidx] using hlarge
    obtain ⟨tail, _, _, htailAlign, htailSchedule⟩ :=
      ih (by omega) (depth + 1) frame.child (PhysicalEpochRecords.empty frame.child) M hM anchor hchildAnchor
        (by simp [PhysicalEpochRecords.empty]) hchildCap hchildInflate hchildLarge
    refine ⟨.succ frame tail, hstate, ⟨hmodulus, hframeAnchor⟩, ?_, ?_⟩
    · exact ⟨hmodulus ▸ dvd_refl M, fun i => hframeAnchor ▸ Int.ModEq.refl (frame.anchor i), htailAlign⟩
    · exact ⟨hcap, hinflate, hwork.trans hpow, hperiod.trans (Real.exp_le_exp.mpr hpow),
        hfreeze, hevent, htailSchedule⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.BudgetedPhysicalStackPeriods
namespace OAI

section

namespace Erdos3.PhysicalEpochStack

open scoped BigOperators

universe u v

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {bound s : ℕ}
  {base : PhysicalEpochSource.{u, v} σ s bound}

theorem BudgetedAt.periods_product_le {A C : ℕ} {U : ℝ} {stack : PhysicalEpochStack base}
    (h : BudgetedAt A U C stack) : (stack.periods.prod : ℝ) ≤ Real.exp ((s : ℝ) * U) := by
  induction stack with
  | zero => simp [periods]
  | @succ t base frame tail ih =>
    obtain ⟨_, _, _, hperiod, _, _, ht⟩ := h
    change ((frame.period * tail.periods.prod : ℕ) : ℝ) ≤ _
    rw [Nat.cast_mul]
    calc
      (frame.period : ℝ) * tail.periods.prod ≤ Real.exp U * Real.exp ((t : ℝ) * U) :=
        mul_le_mul hperiod (ih ht) (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (((t + 1 : ℕ) : ℝ) * U) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring

theorem BudgetedAt.period_exclusions_card_le {A C : ℕ} {U : ℝ} {stack : PhysicalEpochStack base}
    (h : BudgetedAt A U C stack) {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime) :
    ((periodPrimeCoordinates prime stack.periods.prod).card : ℝ) ≤ 2 * ((s : ℝ) * U) :=
  periodPrimeCoordinates_card_le prime hprime hinj stack.periods_product_pos h.periods_product_le

theorem BudgetedAt.new_period_exclusions_card_le {A C : ℕ} {U : ℝ} {stack : PhysicalEpochStack base}
    (h : BudgetedAt A U C stack) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (prime : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime) (selected : Finset ι) :
    (((periodPrimeCoordinates prime stack.periods.prod) \ selected).card : ℝ) ≤ 2 * ((s : ℝ) * U) := by
  have hcard : ((periodPrimeCoordinates prime stack.periods.prod) \ selected).card ≤
      (periodPrimeCoordinates prime stack.periods.prod).card := Finset.card_le_card Finset.sdiff_subset
  exact (Nat.cast_le.mpr hcard).trans (h.period_exclusions_card_le prime hprime hinj)

theorem pending_coprime_selected_periods (stack : PhysicalEpochStack base)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (prime power : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime)
    (selected pending : Finset ι)
    (hdisjoint : Disjoint pending (selected ∪ periodPrimeCoordinates prime stack.periods.prod)) :
    ((∏ i ∈ selected, prime i ^ power i) * stack.periods.prod).Coprime
      (∏ i ∈ pending, prime i ^ power i) :=
  (periodPrimeCoordinates_unfixed_coprime prime power hprime hinj stack.periods.prod selected pending hdisjoint).symm

end Erdos3.PhysicalEpochStack

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateTreeTrace
namespace OAI

section

namespace Erdos3

universe u v

namespace CoordinateDecisionTree

variable {ι : Type u} [DecidableEq ι] {Value : ι → Type v}

theorem Valid.weaken {Good : Finset ι → (∀ i, Value i) → Prop}
    {I : Finset ι} {x : ∀ i, Value i} {tree : CoordinateDecisionTree ι Value} {d : ℕ}
    (h : Valid Good I x tree d) (extra : ℕ) : Valid Good I x tree (d + extra) := by
  induction h with
  | leaf good => exact .leaf good
  | @split I x i children d fresh branches ih =>
    have hsum : d + 1 + extra = d + extra + 1 := by omega
    rw [hsum]
    exact .split fresh ih

theorem Valid.mono {Good : Finset ι → (∀ i, Value i) → Prop}
    {I : Finset ι} {x : ∀ i, Value i} {tree : CoordinateDecisionTree ι Value} {d e : ℕ}
    (h : Valid Good I x tree d) (hde : d ≤ e) : Valid Good I x tree e := by
  have he : d + (e - d) = e := Nat.add_sub_of_le hde
  simpa only [he] using h.weaken (e - d)

end CoordinateDecisionTree

end Erdos3

end

section

namespace Erdos3.CoordinateDecisionTree

universe u v

variable {ι : Type u} [DecidableEq ι] {Value : ι → Type v}

theorem Valid.congr_assignment {Good : Finset ι → (∀ i, Value i) → Prop}
    (hlocal : ∀ I x y, (∀ i ∈ I, x i = y i) → Good I x → Good I y)
    {I : Finset ι} {x : ∀ i, Value i} {tree : CoordinateDecisionTree ι Value} {d : ℕ}
    (h : Valid Good I x tree d) (y : ∀ i, Value i) (hxy : ∀ i ∈ I, x i = y i) :
    Valid Good I y tree d := by
  induction h generalizing y with
  | leaf good => exact .leaf (hlocal _ _ _ hxy good)
  | @split I x i children d fresh branches ih =>
    apply Valid.split fresh
    intro value
    apply ih value (Function.update y i value)
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · simp only [Function.update_self]
    · have hji : j ≠ i := by intro heq; subst j; exact fresh hj
      simpa only [Function.update_of_ne hji] using hxy j hj

end Erdos3.CoordinateDecisionTree

end

section

namespace Erdos3.CoordinateDecisionTree

universe u v

variable {ι : Type u} [DecidableEq ι] {Value : ι → Type v}

theorem Valid.preserve_subset {Good : Finset ι → (∀ i, Value i) → Prop}
    {I M : Finset ι} {x : ∀ i, Value i} {tree : CoordinateDecisionTree ι Value} {d : ℕ}
    (h : Valid Good I x tree d) (hMI : M ⊆ I) :
    Valid (fun J y => M ⊆ J ∧ Good J y) I x tree d := by
  revert hMI
  induction h with
  | leaf good => intro hMI; exact .leaf ⟨hMI, good⟩
  | @split I x i children d fresh branches ih =>
    intro hMI
    exact .split fresh (fun value => ih value (hMI.trans (Finset.subset_insert i I)))

end Erdos3.CoordinateDecisionTree

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankedCoordinateDecisionTree
namespace OAI

section

namespace Erdos3.CoordinateDecisionTree

universe u v w

variable {ι : Type u} [DecidableEq ι] {Value : ι → Type v}

theorem Valid.map {Good Better : Finset ι → (∀ i, Value i) → Prop}
    {I : Finset ι} {x : ∀ i, Value i} {tree : CoordinateDecisionTree ι Value} {d : ℕ}
    (h : Valid Good I x tree d) (hmap : ∀ J y, Good J y → Better J y) : Valid Better I x tree d := by
  induction h with
  | leaf good => exact .leaf (hmap _ _ good)
  | split fresh branches ih => exact .split fresh ih

theorem Valid.substitute {Good Better : Finset ι → (∀ i, Value i) → Prop}
    {I : Finset ι} {x : ∀ i, Value i} {tree : CoordinateDecisionTree ι Value} {d e : ℕ}
    (h : Valid Good I x tree d)
    (replace : ∀ J y, Good J y → ∃ next : CoordinateDecisionTree ι Value, Valid Better J y next e) :
    ∃ next : CoordinateDecisionTree ι Value, Valid Better I x next (d + e) := by
  classical
  induction h with
  | @leaf I x d good =>
    obtain ⟨next, hnext⟩ := replace I x good
    exact ⟨next, hnext.mono (by omega)⟩
  | @split I x i children d fresh branches ih =>
    choose next hnext using ih
    have hsum : d + 1 + e = (d + e) + 1 := by omega
    rw [hsum]
    exact ⟨.split i next, .split fresh hnext⟩

theorem exists_of_rank_decreasing_step
    (State : Finset ι → (∀ i, Value i) → Type w)
    (rank : ∀ I x, State I x → ℕ) (Good : Finset ι → (∀ i, Value i) → Prop) (cost : ℕ)
    (step : ∀ I x (state : State I x), ∃ tree : CoordinateDecisionTree ι Value,
      Valid (fun J y => Good J y ∨ ∃ next : State J y, rank J y next < rank I x state) I x tree cost)
    (I : Finset ι) (x : ∀ i, Value i) (state : State I x) :
    ∃ tree : CoordinateDecisionTree ι Value, Valid Good I x tree (cost * (rank I x state + 1)) := by
  have build : ∀ n : ℕ, ∀ I x (state : State I x), rank I x state = n →
      ∃ tree : CoordinateDecisionTree ι Value, Valid Good I x tree (cost * (n + 1)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro I x state hn
      obtain ⟨tree, htree⟩ := step I x state
      have replace : ∀ J y, (Good J y ∨ ∃ next : State J y, rank J y next < rank I x state) →
          ∃ nextTree : CoordinateDecisionTree ι Value, Valid Good J y nextTree (cost * n) := by
        intro J y hleaf
        rcases hleaf with hgood | ⟨next, hlt⟩
        · exact ⟨.leaf, .leaf hgood⟩
        · have hlt' : rank J y next < n := by simpa only [hn] using hlt
          obtain ⟨nextTree, hnext⟩ := ih (rank J y next) hlt' J y next rfl
          exact ⟨nextTree, hnext.mono (Nat.mul_le_mul_left cost (by omega))⟩
      simpa only [Nat.mul_add, Nat.mul_one, Nat.add_comm] using htree.substitute replace
  exact build (rank I x state) I x state rfl

end Erdos3.CoordinateDecisionTree

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateTreeBatch
namespace OAI

section

namespace Erdos3.CoordinateDecisionTree

universe u v

variable {ι : Type u} [DecidableEq ι] {Value : ι → Type v}

theorem exists_query_batch
    (Good : Finset ι → (∀ i, Value i) → Prop) (batch : Finset ι) (d : ℕ) :
    ∀ (I : Finset ι) (x : ∀ i, Value i), Disjoint I batch →
    (∀ y : ∀ i, Value i, (∀ i ∈ I, y i = x i) →
      ∃ tree : CoordinateDecisionTree ι Value, Valid Good (I ∪ batch) y tree d) →
    ∃ tree : CoordinateDecisionTree ι Value, Valid Good I x tree (batch.card + d) := by
  classical
  induction batch using Finset.induction_on with
  | empty =>
    intro I x hdisjoint continuation
    simpa only [Finset.union_empty, Finset.card_empty, Nat.zero_add] using
      continuation x (fun _ _ => rfl)
  | @insert i batch fresh ih =>
    intro I x hdisjoint continuation
    have hi : i ∉ I := by
      intro hi
      exact Finset.disjoint_left.mp hdisjoint hi (Finset.mem_insert_self _ _)
    have hIB : Disjoint (insert i I) batch := by
      apply Finset.disjoint_left.mpr
      intro j hj hbatch
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact fresh hbatch
      · exact Finset.disjoint_left.mp hdisjoint hj (Finset.mem_insert_of_mem hbatch)
    have hchildren : ∀ value : Value i, ∃ tree : CoordinateDecisionTree ι Value,
        Valid Good (insert i I) (Function.update x i value) tree (batch.card + d) := by
      intro value
      apply ih (insert i I) (Function.update x i value) hIB
      intro y hy
      have hbase : ∀ j ∈ I, y j = x j := by
        intro j hj
        have hji : j ≠ i := by intro h; subst j; exact hi hj
        have h := hy j (Finset.mem_insert_of_mem hj)
        simpa only [Function.update_of_ne hji] using h
      have hunion : insert i I ∪ batch = I ∪ insert i batch := by ext j; simp only [Finset.mem_union, Finset.mem_insert]; tauto
      simpa only [hunion] using continuation y hbase
    choose children hchildren using hchildren
    have hcard : (insert i batch).card + d = (batch.card + d) + 1 := by
      rw [Finset.card_insert_of_notMem fresh]
      omega
    rw [hcard]
    exact ⟨.split i children, .split hi hchildren⟩

end Erdos3.CoordinateDecisionTree

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateTreeRelabel
namespace OAI

section

namespace Erdos3.CoordinateDecisionTree

universe u v w

variable {ι : Type u} [DecidableEq ι] {Value : ι → Type v} {Other : ι → Type w}

theorem relabelAssignment_update (e : ∀ i, Value i ≃ Other i)
    (x : ∀ i, Value i) (i : ι) (v : Value i) :
    relabelAssignment e (Function.update x i v) =
      Function.update (relabelAssignment e x) i (e i v) := by
  funext j
  by_cases h : j = i
  · subst j; simp only [relabelAssignment, Function.update_self]
  · simp only [relabelAssignment, Function.update_of_ne h]

omit [DecidableEq ι] in
theorem relabelAssignment_inverse (e : ∀ i, Value i ≃ Other i) (x : ∀ i, Value i) :
    relabelAssignment (fun i => (e i).symm) (relabelAssignment e x) = x := by
  funext i
  exact (e i).symm_apply_apply (x i)

theorem Valid.relabel {Good : Finset ι → (∀ i, Value i) → Prop}
    {I : Finset ι} {x : ∀ i, Value i} {tree : CoordinateDecisionTree ι Value} {d : ℕ}
    (h : Valid Good I x tree d) (e : ∀ i, Value i ≃ Other i) :
    Valid (fun J y => Good J (relabelAssignment (fun i => (e i).symm) y))
      I (relabelAssignment e x) (tree.relabel e) d := by
  induction h with
  | leaf good =>
    exact .leaf (by simpa only [relabelAssignment_inverse] using good)
  | @split I x i children d fresh branches ih =>
    apply Valid.split fresh
    intro v
    simpa only [relabelAssignment_update, Equiv.apply_symm_apply] using ih ((e i).symm v)

end Erdos3.CoordinateDecisionTree

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineSampleAlphabet
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem primeCoordinateCell_mono {ι σ : Type*} [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ) {I J : Finset ι}
    {x y : ∀ i, σ → ZMod (q i)} (hIJ : I ⊆ J) (hxy : ∀ i ∈ I, y i = x i) :
    primeCoordinateCell lo N q J y ⊆ primeCoordinateCell lo N q I x := by
  intro z hz
  obtain ⟨hz, heq⟩ := (mem_primeCoordinateCell lo N q J y z).mp hz
  exact (mem_primeCoordinateCell lo N q I x z).mpr ⟨hz, fun i hi => (heq i (hIJ hi)).trans (hxy i hi)⟩

theorem primeCoordinateMean_eq_physical {ι σ : Type*} [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ)
    (hcop : Pairwise (fun i j => (q i).Coprime (q j))) (I : Finset ι) (x : ∀ i, σ → ZMod (q i))
    (u : σ → ℤ) (hu : u ∈ primeCoordinateCell lo N q I x) :
    primeCoordinateMean f lo N q I x = physicalResidueMean f lo N (∏ i ∈ I, q i) u := by
  unfold primeCoordinateMean
  rw [primeCoordinateCell_anchor lo N q I x u hu]
  exact primeCoordinateCell_mean lo N q hcop I u f

theorem primeCoordinateStable_of_empty {ι σ : Type*} [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ)
    (r : ℕ) (δ : ℝ) (I : Finset ι) (x : ∀ i, σ → ZMod (q i))
    (hempty : ¬ (primeCoordinateCell lo N q I x).Nonempty) : PrimeCoordinateStable f lo N q r δ I x := by
  intro J hIJ hJ y hxy hnonempty
  obtain ⟨z, hz⟩ := hnonempty
  exact False.elim (hempty ⟨z, primeCoordinateCell_mono lo N q Finset.subset_union_left hxy hz⟩)

universe u v

theorem exists_prime_cell_physical_comparison
    {ι : Type*} [DecidableEq ι] {σ : Type u} [Fintype σ] [DecidableEq σ]
    {s bound : ℕ} {gap : ℝ} (base : PhysicalEpochSource.{u, v} σ s bound)
    (T : base.model.Niltest (fun _ : σ => 1)) (horbit : T.orbit = base.fixedMap.orbit)
    (hpositive : T.UnitIntervalValued) (hcomplexity : T.ComplexityLE base.incomingBudget)
    (q : ι → ℕ) (hq : ∀ i, 0 < q i) (hcop : Pairwise (fun i j => (q i).Coprime (q j)))
    (I J : Finset ι) (hIJ : Disjoint I J) (x y : ∀ i, σ → ZMod (q i))
    (hxy : ∀ i ∈ I, y i = x i) (u v : σ → ℤ)
    (hu : u ∈ primeCoordinateCell base.lower base.sides q I x)
    (hv : v ∈ primeCoordinateCell base.lower base.sides q (I ∪ J) y)
    (hgap : 0 < gap) (hgap1 : gap ≤ 1) (hinverse : gap⁻¹ ≤ Real.exp base.incomingBudget)
    (hrecord : 2 ≤ base.recordBudget)
    (hdiscrepancy : gap ≤ ‖primeCoordinateMean T.eval base.lower base.sides q I x -
      primeCoordinateMean T.eval base.lower base.sides q (I ∪ J) y‖) :
    ∃ c : PhysicalEpochComparison base (∏ i ∈ I, q i) 1 (∏ i ∈ J, q i) gap,
      c.Controlled ∧ c.anchor = u ∧ c.refined = v := by
  have hvmem := primeCoordinateCell_mono base.lower base.sides q Finset.subset_union_left hxy hv
  have hanchorCell := primeCoordinateCell_anchor base.lower base.sides q I x u hu
  have hcompat : ∀ i, v i ≡ u i [ZMOD ((∏ j ∈ I, q j : ℕ) : ℤ)] := by
    rw [hanchorCell] at hvmem
    exact ((mem_primeCoordinateCell_anchor base.lower base.sides q hcop I u v).mp hvmem).2
  have huinside := (mem_translatedIntegerBox base.lower base.sides u).mp
    ((mem_primeCoordinateCell base.lower base.sides q I x u).mp hu).1
  have hvinside := (mem_translatedIntegerBox base.lower base.sides v).mp
    ((mem_primeCoordinateCell base.lower base.sides q (I ∪ J) y v).mp hv).1
  have hm : 0 < ∏ i ∈ I, q i := Finset.prod_pos (fun i _ => hq i)
  have hJ : 0 < ∏ i ∈ J, q i := Finset.prod_pos (fun i _ => hq i)
  have hphysical : gap ≤ ‖physicalResidueMean T.eval base.lower base.sides (∏ i ∈ I, q i) u -
      physicalResidueMean T.eval base.lower base.sides ((∏ i ∈ I, q i) * ∏ i ∈ J, q i) v‖ := by
    rw [primeCoordinateMean_eq_physical T.eval base.lower base.sides q hcop I x u hu,
      primeCoordinateMean_eq_physical T.eval base.lower base.sides q hcop (I ∪ J) y v hv,
      Finset.prod_union hIJ] at hdiscrepancy
    exact hdiscrepancy
  obtain ⟨c, hc, hcu, hcv, _, _⟩ := exists_initial_physical_comparison base T horbit hpositive hcomplexity
    hm hJ u v huinside hvinside hcompat hgap hgap1 hinverse hrecord hphysical
  exact ⟨c, hc, hcu, hcv⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrimeStabilityTree
namespace OAI

section

namespace Erdos3

open PhysicalEpochStack
open scoped BigOperators

universe u v w

namespace PrimeStabilityContext

variable {ι : Type w} {σ : Type u} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  {s bound : ℕ}

theorem moduli_pos (ctx : PrimeStabilityContext.{u, v, w} ι σ s bound) (i : ι) : 0 < ctx.moduli i :=
  pow_pos (ctx.prime_prime i).pos _

theorem moduli_coprime (ctx : PrimeStabilityContext.{u, v, w} ι σ s bound) :
    Pairwise (fun i j => (ctx.moduli i).Coprime (ctx.moduli j)) :=
  selectedPrimePowers_pairwise_coprime ctx.prime ctx.power ctx.prime_prime ctx.prime_injective

theorem workBudget_nonneg (ctx : PrimeStabilityContext.{u, v, w} ι σ s bound) : 0 ≤ ctx.workBudget :=
  physicalEpochBudget_nonneg ctx.parameters.A ctx.parameters.C ctx.recordCap_nonneg s

end PrimeStabilityContext

end Erdos3

end

section

namespace Erdos3.PrimeStabilityContext

open PhysicalEpochStack
open scoped BigOperators

universe u v w

variable {ι : Type w} {σ : Type u} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  {s bound : ℕ}

theorem product_pos (ctx : PrimeStabilityContext.{u, v, w} ι σ s bound) (I : Finset ι) :
    0 < ∏ i ∈ I, ctx.moduli i := Finset.prod_pos (fun i _ => ctx.moduli_pos i)

theorem product_le_exp_card (ctx : PrimeStabilityContext.{u, v, w} ι σ s bound) (I : Finset ι) :
    ((∏ i ∈ I, ctx.moduli i : ℕ) : ℝ) ≤ Real.exp (ctx.primeBudget * I.card) := by
  rw [Nat.cast_prod]
  calc
    (∏ i ∈ I, (ctx.moduli i : ℝ)) ≤ ∏ _i ∈ I, Real.exp ctx.primeBudget :=
      Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun i _ => ctx.prime_bound i)
    _ = Real.exp ((I.card : ℝ) * ctx.primeBudget) := by rw [Finset.prod_const, Real.exp_nat_mul]
    _ = Real.exp (ctx.primeBudget * I.card) := by rw [mul_comm]

theorem node_width (ctx : PrimeStabilityContext.{u, v, w} ι σ s bound) (hlarge : ctx.HasLargeSides)
    (I : Finset ι) (hcard : I.card ≤ ctx.allowance) (j : σ) :
    ((∏ i ∈ I, ctx.moduli i : ℕ) : ℝ) *
      Real.exp (5 * ctx.workBudget + 2 * (ctx.workBudget + 2) ^ ctx.parameters.Kf + 16) ≤ (ctx.base.sides j : ℝ) := by
  have hcardR : (I.card : ℝ) ≤ ctx.allowance := by exact_mod_cast hcard
  have hprod : ((∏ i ∈ I, ctx.moduli i : ℕ) : ℝ) ≤ Real.exp (ctx.primeBudget * ctx.allowance) :=
    (ctx.product_le_exp_card I).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hcardR ctx.primeBudget_nonneg))
  calc
    _ ≤ Real.exp (ctx.primeBudget * ctx.allowance) *
        Real.exp (5 * ctx.workBudget + 2 * (ctx.workBudget + 2) ^ ctx.parameters.Kf + 16) :=
      mul_le_mul_of_nonneg_right hprod (Real.exp_nonneg _)
    _ = Real.exp (ctx.primeBudget * ctx.allowance + 5 * ctx.workBudget +
        2 * (ctx.workBudget + 2) ^ ctx.parameters.Kf + 16) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ (ctx.base.sides j : ℝ) := hlarge j

theorem construction_width (ctx : PrimeStabilityContext.{u, v, w} ι σ s bound) (hlarge : ctx.HasLargeSides)
    (I : Finset ι) (hcard : I.card ≤ ctx.allowance) (j : σ) :
    Real.exp ctx.workBudget ≤ (ctx.base.sides j : ℝ) / (∏ i ∈ I, ctx.moduli i : ℕ) := by
  have hp : (0 : ℝ) < ((∏ i ∈ I, ctx.moduli i : ℕ) : ℝ) := by exact_mod_cast ctx.product_pos I
  have hU := ctx.workBudget_nonneg
  have hpow : 0 ≤ (ctx.workBudget + 2) ^ ctx.parameters.Kf := by positivity
  apply (le_div_iff₀ hp).mpr
  calc
    _ = ((∏ i ∈ I, ctx.moduli i : ℕ) : ℝ) * Real.exp ctx.workBudget := mul_comm _ _
    _ ≤ ((∏ i ∈ I, ctx.moduli i : ℕ) : ℝ) *
        Real.exp (5 * ctx.workBudget + 2 * (ctx.workBudget + 2) ^ ctx.parameters.Kf + 16) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hp.le
    _ ≤ (ctx.base.sides j : ℝ) := ctx.node_width hlarge I hcard j

variable {ctx : PrimeStabilityContext.{u, v, w} ι σ s bound}
  {I : Finset ι} {x : ∀ i, σ → ZMod (ctx.moduli i)}

theorem State.periodBatch_disjoint (state : ctx.State I x) : Disjoint I state.periodBatch := by
  apply Finset.disjoint_left.mpr
  intro i hi hp
  exact (Finset.mem_sdiff.mp hp).2 hi

theorem State.periodBatch_card (state : ctx.State I x) : state.periodBatch.card ≤ ctx.periodCap := by
  have hb : BudgetedAt ctx.parameters.A ctx.workBudget ctx.parameters.C state.stack := by
    simpa only [Nat.zero_add, workBudget] using
      state.scheduled.budgeted ctx.parameters.A_pos (by linarith [ctx.parameters.C_ge_two]) ctx.recordCap_nonneg
  have hcard := hb.new_period_exclusions_card_le ctx.prime ctx.prime_prime ctx.prime_injective I
  have hceil : 2 * ((s : ℝ) * ctx.workBudget) ≤ (ctx.periodCap : ℝ) := Nat.le_ceil _
  exact_mod_cast hcard.trans hceil

theorem State.periods_covered (state : ctx.State I x) :
    periodPrimeCoordinates ctx.prime state.stack.periods.prod ⊆ I ∪ state.periodBatch := by
  intro i hi
  by_cases hI : i ∈ I
  · exact Finset.mem_union_left _ hI
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hi, hI⟩)

theorem State.one_step_room (state : ctx.State I x) : I.card + ctx.stepCost ≤ ctx.allowance := by
  have hmul : ctx.stepCost ≤ ctx.stepCost * (state.rank + 1) := by
    have h := Nat.mul_le_mul_left ctx.stepCost (show 1 ≤ state.rank + 1 by omega)
    simpa only [Nat.mul_one] using h
  have hroom : I.card + ctx.stepCost * (state.rank + 1) ≤ ctx.allowance := state.room
  omega

theorem State.room_of_smaller_rank (state : ctx.State I x) (J : Finset ι) (rank : ℕ)
    (hcard : J.card ≤ I.card + ctx.stepCost) (hrank : rank < state.rank) :
    J.card + ctx.stepCost * (rank + 1) ≤ ctx.allowance := by
  have hmul := Nat.mul_le_mul_left ctx.stepCost (Nat.succ_le_of_lt hrank)
  have hroom : I.card + ctx.stepCost * (state.rank + 1) ≤ ctx.allowance := state.room
  nlinarith

theorem State.aligned_refinement (state : ctx.State I x) {J : Finset ι}
    {y : ∀ i, σ → ZMod (ctx.moduli i)} (hIJ : I ⊆ J) (hxy : ∀ i ∈ I, y i = x i)
    (u : σ → ℤ) (hu : u ∈ primeCoordinateCell ctx.base.lower ctx.base.sides ctx.moduli J y) :
    AlignedAt (∏ i ∈ J, ctx.moduli i) u state.stack := by
  apply state.aligned.refine (Finset.prod_dvd_prod_of_subset I J ctx.moduli hIJ)
  have hmem := primeCoordinateCell_mono ctx.base.lower ctx.base.sides ctx.moduli hIJ hxy hu
  rw [primeCoordinateCell_anchor ctx.base.lower ctx.base.sides ctx.moduli I x state.anchor state.anchor_mem] at hmem
  exact ((mem_primeCoordinateCell_anchor ctx.base.lower ctx.base.sides ctx.moduli ctx.moduli_coprime I state.anchor u).mp hmem).2

end Erdos3.PrimeStabilityContext

end

section

namespace Erdos3.PrimeStabilityContext

open PhysicalEpochStack
open scoped BigOperators

universe u v w

variable {ι : Type w} {σ : Type u} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  {s bound : ℕ} {ctx : PrimeStabilityContext.{u, v, w} ι σ s bound}
  {I : Finset ι} {x : ∀ i, σ → ZMod (ctx.moduli i)}

theorem State.repair_cell (state : ctx.State I x) (hlarge : ctx.HasLargeSides)
    (L J : Finset ι) (hIL : I ⊆ L) (hLJ : Disjoint L J)
    (hperiods : periodPrimeCoordinates ctx.prime state.stack.periods.prod ⊆ L)
    (hcard : (L ∪ J).card ≤ I.card + ctx.stepCost)
    (y z : ∀ i, σ → ZMod (ctx.moduli i))
    (hy : ∀ i ∈ I, y i = x i) (hz : ∀ i ∈ L, z i = y i)
    (u v : σ → ℤ)
    (hu : u ∈ primeCoordinateCell ctx.base.lower ctx.base.sides ctx.moduli L y)
    (hv : v ∈ primeCoordinateCell ctx.base.lower ctx.base.sides ctx.moduli (L ∪ J) z)
    (hgap : ctx.gap ≤ ‖primeCoordinateMean ctx.baseline.eval ctx.base.lower ctx.base.sides ctx.moduli L y -
      primeCoordinateMean ctx.baseline.eval ctx.base.lower ctx.base.sides ctx.moduli (L ∪ J) z‖)
    (target : ∀ i, σ → ZMod (ctx.moduli i)) (htarget : ∀ i ∈ L, target i = y i)
    (anchor : σ → ℤ)
    (hanchor : anchor ∈ primeCoordinateCell ctx.base.lower ctx.base.sides ctx.moduli (L ∪ J) target) :
    ∃ next : ctx.State (L ∪ J) target, next.rank < state.rank := by
  have halign := state.aligned_refinement hIL hy u hu
  obtain ⟨c, hc, hcu, _⟩ := exists_prime_cell_physical_comparison ctx.base ctx.baseline ctx.orbit
    ctx.positive ctx.complexity ctx.moduli ctx.moduli_pos ctx.moduli_coprime L J hLJ y z hz u v hu hv
    ctx.gap_pos ctx.gap_le_one ctx.gap_inverse ctx.record_two hgap
  have hdisjoint : Disjoint J (L ∪ periodPrimeCoordinates ctx.prime state.stack.periods.prod) :=
    hLJ.symm.mono_right (Finset.union_subset (Finset.Subset.refl _) hperiods)
  have hcop := state.stack.pending_coprime_selected_periods ctx.prime ctx.power ctx.prime_prime
    ctx.prime_injective L J hdisjoint
  have hcardD : (L ∪ J).card ≤ ctx.allowance := hcard.trans state.one_step_room
  have hsource : ∀ j, (((∏ i ∈ L, ctx.moduli i) * (∏ i ∈ J, ctx.moduli i) : ℕ) : ℝ) *
      Real.exp (5 * ctx.workBudget + 2 * (ctx.workBudget + 2) ^ ctx.parameters.Kf + 16) ≤ (ctx.base.sides j : ℝ) := by
    intro j
    simpa only [Finset.prod_union hLJ] using ctx.node_width hlarge (L ∪ J) hcardD j
  have hinside := (mem_translatedIntegerBox ctx.base.lower ctx.base.sides anchor).mp
    ((mem_primeCoordinateCell ctx.base.lower ctx.base.sides ctx.moduli (L ∪ J) target anchor).mp hanchor).1
  have hanchorOld := primeCoordinateCell_mono ctx.base.lower ctx.base.sides ctx.moduli
    Finset.subset_union_left htarget hanchor
  rw [primeCoordinateCell_anchor ctx.base.lower ctx.base.sides ctx.moduli L y u hu] at hanchorOld
  have hcompat := ((mem_primeCoordinateCell_anchor ctx.base.lower ctx.base.sides ctx.moduli
    ctx.moduli_coprime L u anchor).mp hanchorOld).2
  obtain ⟨nextStack, hevent, hnextAlign, hnextSchedule⟩ := ctx.parameters.event ctx.recordCap 0 u
    state.stack c ctx.recordCap_nonneg (by omega) state.scheduled halign hc
    (fun i => by rw [hcu]) (by simpa only [Nat.mul_one, moduli] using hcop)
    (by simpa only [Nat.zero_add, workBudget] using hsource) anchor hinside hcompat
  have hnextAlign' : AlignedAt (∏ i ∈ L ∪ J, ctx.moduli i) anchor nextStack := by
    simpa only [Finset.prod_union hLJ] using hnextAlign
  have hdrop : epochStackRank bound nextStack.dimensions < state.rank := hevent.rank_lt
  let next : ctx.State (L ∪ J) target := {
    anchor := anchor
    anchor_mem := hanchor
    stack := nextStack
    scheduled := hnextSchedule
    aligned := hnextAlign'
    room := state.room_of_smaller_rank (L ∪ J) _ hcard hdrop }
  exact ⟨next, hdrop⟩

end Erdos3.PrimeStabilityContext

end

section

namespace Erdos3.PrimeStabilityContext

open PhysicalEpochStack CoordinateDecisionTree

universe u v w

variable {ι : Type w} {σ : Type u} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  {s bound : ℕ} {ctx : PrimeStabilityContext.{u, v, w} ι σ s bound}
  {I : Finset ι} {x : ∀ i, σ → ZMod (ctx.moduli i)}

theorem State.local_tree (state : ctx.State I x) (hlarge : ctx.HasLargeSides) :
    ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (ctx.moduli i)),
      Valid (fun J y => ctx.Good J y ∨ ∃ next : ctx.State J y, next.rank < state.rank)
        I x tree ctx.stepCost := by
  classical
  let Post := fun (J : Finset ι) (y : ∀ i, σ → ZMod (ctx.moduli i)) =>
    ctx.Good J y ∨ ∃ next : ctx.State J y, next.rank < state.rank
  let batch := state.periodBatch
  have hbatchCard : batch.card ≤ ctx.periodCap := state.periodBatch_card
  have afterPeriods : ∀ y : ∀ i, σ → ZMod (ctx.moduli i), (∀ i ∈ I, y i = x i) →
      ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (ctx.moduli i)),
        Valid Post (I ∪ batch) y tree ctx.witnessSize := by
    intro y hy
    let L := I ∪ batch
    by_cases hgood : ctx.Good L y
    · exact ⟨.leaf, .leaf (Or.inl hgood)⟩
    · have hnonempty : (primeCoordinateCell ctx.base.lower ctx.base.sides ctx.moduli L y).Nonempty := by
        by_contra hempty
        exact hgood (primeCoordinateStable_of_empty ctx.baseline.eval ctx.base.lower ctx.base.sides
          ctx.moduli ctx.witnessSize ctx.gap L y hempty)
      obtain ⟨u, hu⟩ := hnonempty
      have hbad := hgood
      change ¬ PrimeCoordinateStable ctx.baseline.eval ctx.base.lower ctx.base.sides ctx.moduli
        ctx.witnessSize ctx.gap L y at hbad
      unfold PrimeCoordinateStable at hbad
      push Not at hbad
      obtain ⟨J, hLJ, hJ, z, hzy, hznonempty, hgap⟩ := hbad
      obtain ⟨v, hv⟩ := hznonempty
      have hcard : (L ∪ J).card ≤ I.card + ctx.stepCost := by
        have hL : L.card ≤ I.card + batch.card := Finset.card_union_le I batch
        have hLJcard : (L ∪ J).card ≤ L.card + J.card := Finset.card_union_le L J
        change (L ∪ J).card ≤ I.card + (ctx.periodCap + ctx.witnessSize)
        omega
      have hperiods : periodPrimeCoordinates ctx.prime state.stack.periods.prod ⊆ L := state.periods_covered
      have afterWitness : ∀ target : ∀ i, σ → ZMod (ctx.moduli i), (∀ i ∈ L, target i = y i) →
          ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (ctx.moduli i)),
            Valid Post (L ∪ J) target tree 0 := by
        intro target htarget
        by_cases hnonempty : (primeCoordinateCell ctx.base.lower ctx.base.sides ctx.moduli (L ∪ J) target).Nonempty
        · obtain ⟨anchor, hanchor⟩ := hnonempty
          obtain ⟨next, hnext⟩ := state.repair_cell hlarge L J Finset.subset_union_left hLJ hperiods hcard
            y z hy hzy u v hu hv hgap.le target htarget anchor hanchor
          exact ⟨.leaf, .leaf (Or.inr ⟨next, hnext⟩)⟩
        · exact ⟨.leaf, .leaf (Or.inl (primeCoordinateStable_of_empty ctx.baseline.eval ctx.base.lower
            ctx.base.sides ctx.moduli ctx.witnessSize ctx.gap (L ∪ J) target hnonempty))⟩
      obtain ⟨tree, htree⟩ := exists_query_batch Post J 0 L y hLJ afterWitness
      exact ⟨tree, htree.mono (by omega)⟩
  obtain ⟨tree, htree⟩ := exists_query_batch Post batch ctx.witnessSize I x state.periodBatch_disjoint afterPeriods
  exact ⟨tree, htree.mono (by change batch.card + ctx.witnessSize ≤ ctx.periodCap + ctx.witnessSize; omega)⟩

end Erdos3.PrimeStabilityContext

end

section

namespace Erdos3.PrimeStabilityContext

open PhysicalEpochStack CoordinateDecisionTree
open scoped BigOperators

universe u v w

variable {ι : Type w} {σ : Type u} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  {s bound : ℕ}

theorem State.stable_tree {ctx : PrimeStabilityContext.{u, v, w} ι σ s bound}
    {I : Finset ι} {x : ∀ i, σ → ZMod (ctx.moduli i)} (state : ctx.State I x) (hlarge : ctx.HasLargeSides) :
    ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (ctx.moduli i)),
      Valid ctx.Good I x tree (ctx.stepCost * (state.rank + 1)) :=
  exists_of_rank_decreasing_step (fun I x => ctx.State I x) (fun _ _ state => state.rank)
    ctx.Good ctx.stepCost (fun _ _ state => state.local_tree hlarge) I x state

theorem exists_stable_tree (ctx : PrimeStabilityContext.{u, v, w} ι σ s bound) (hlarge : ctx.HasLargeSides) :
    ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (ctx.moduli i)),
      Valid (fun I x => ctx.mandatory ⊆ I ∧ ctx.Good I x) ∅ (fun _ _ => 0) tree ctx.allowance := by
  classical
  let Final := fun (I : Finset ι) (x : ∀ i, σ → ZMod (ctx.moduli i)) => ctx.mandatory ⊆ I ∧ ctx.Good I x
  let depth := ctx.stepCost * (bound + 1) ^ s
  have afterMandatory : ∀ y : ∀ i, σ → ZMod (ctx.moduli i),
      ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (ctx.moduli i)),
        Valid Final ctx.mandatory y tree depth := by
    intro y
    by_cases hnonempty : (primeCoordinateCell ctx.base.lower ctx.base.sides ctx.moduli ctx.mandatory y).Nonempty
    · obtain ⟨anchor, hanchor⟩ := hnonempty
      have hinside := (mem_translatedIntegerBox ctx.base.lower ctx.base.sides anchor).mp
        ((mem_primeCoordinateCell ctx.base.lower ctx.base.sides ctx.moduli ctx.mandatory y anchor).mp hanchor).1
      have hmandatory : ctx.mandatory.card ≤ ctx.allowance := by
        change ctx.mandatory.card ≤ ctx.mandatory.card + _
        omega
      have hnorm : ∀ i, Real.exp (physicalEpochBudget ctx.parameters.A ctx.parameters.C ctx.recordCap (0 + s)) ≤
          (ctx.base.sides i : ℝ) / (∏ j ∈ ctx.mandatory, ctx.moduli j : ℕ) := by
        intro i
        simpa only [Nat.zero_add, workBudget] using ctx.construction_width hlarge ctx.mandatory hmandatory i
      obtain ⟨stack, _, _, halign, hschedule⟩ :=
        exists_scheduled_physical_epoch_stack ctx.parameters.A ctx.parameters.C s ctx.parameters.A_pos
          (by linarith [ctx.parameters.C_ge_two]) (@PhysicalStabilityParameters.frames _ ctx.parameters)
          ctx.recordCap ctx.recordCap_nonneg s le_rfl 0 ctx.base (PhysicalEpochRecords.empty ctx.base)
          (∏ i ∈ ctx.mandatory, ctx.moduli i) (ctx.product_pos ctx.mandatory) anchor hinside
          (by simp [PhysicalEpochRecords.empty]) ctx.record_le_cap ctx.inflation hnorm
      have hrank : epochStackRank bound stack.dimensions + 1 ≤ (bound + 1) ^ s := by
        have h := epochStackRank_lt bound stack.dimensions stack.dimensions_bounded
        rw [stack.dimensions_length] at h
        omega
      have hroom : ctx.mandatory.card + ctx.stepCost * (epochStackRank bound stack.dimensions + 1) ≤ ctx.allowance :=
        Nat.add_le_add_left (Nat.mul_le_mul_left ctx.stepCost hrank) _
      let initial : ctx.State ctx.mandatory y := ⟨anchor, hanchor, stack, hschedule, halign, hroom⟩
      obtain ⟨tree, htree⟩ := initial.stable_tree hlarge
      exact ⟨tree, (htree.preserve_subset (Finset.Subset.refl _)).mono (Nat.mul_le_mul_left ctx.stepCost hrank)⟩
    · exact ⟨.leaf, .leaf ⟨Finset.Subset.refl _, primeCoordinateStable_of_empty ctx.baseline.eval
        ctx.base.lower ctx.base.sides ctx.moduli ctx.witnessSize ctx.gap ctx.mandatory y hnonempty⟩⟩
  obtain ⟨tree, htree⟩ := exists_query_batch Final ctx.mandatory depth ∅ (fun _ _ => 0)
    (Finset.disjoint_empty_left _) (fun y _ => by simpa only [Finset.empty_union] using afterMandatory y)
  exact ⟨tree, htree⟩

end Erdos3.PrimeStabilityContext

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PrimeStabilityPolynomialBudget
namespace OAI

section

namespace Erdos3

universe u v w

theorem exists_prime_stability_polynomial_budget (s K Kf : ℕ) :
    ∃ L : ℕ, 2 ≤ L ∧ ∀ {ι : Type w} {σ : Type u} [Fintype ι] [DecidableEq ι]
      [Fintype σ] [DecidableEq σ] {bound : ℕ}
      (ctx : PrimeStabilityContext.{u, v, w} ι σ s bound) (Q : ℝ),
      0 ≤ Q → ctx.parameters.K ≤ K → ctx.parameters.Kf ≤ Kf →
      ctx.recordCap ≤ Q → ctx.primeBudget ≤ Q → (ctx.witnessSize : ℝ) ≤ Q →
      (ctx.mandatory.card : ℝ) ≤ Q → (bound : ℝ) ≤ Q →
      (ctx.allowance : ℝ) ≤ (Q + 2) ^ L ∧
      ctx.primeBudget * ctx.allowance + 5 * ctx.workBudget +
        2 * (ctx.workBudget + 2) ^ ctx.parameters.Kf + 16 ≤ (Q + 2) ^ L := by
  let U : Polynomial ℕ := (Polynomial.X + 2) ^ K
  let D : Polynomial ℕ := Polynomial.X +
    (2 * Polynomial.C s * U + 1 + Polynomial.X) * (Polynomial.X + 1) ^ s
  let P : Polynomial ℕ := D + Polynomial.X * D + 5 * U + 2 * (U + 2) ^ Kf + 16
  obtain ⟨L, hL, hbudget⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨L, hL, ?_⟩
  intro ι σ _ _ _ _ bound ctx Q hQ hK hKf hb hp hr hM hd
  let ub : ℝ := (Q + 2) ^ K
  let db : ℝ := Q + (2 * s * ub + 1 + Q) * (Q + 1) ^ s
  have hub : 0 ≤ ub := by dsimp [ub]; positivity
  have hdb : 0 ≤ db := by dsimp [db]; positivity
  have hU0 := ctx.workBudget_nonneg
  have hU : ctx.workBudget ≤ ub := by
    calc
      ctx.workBudget ≤ (ctx.recordCap + 2) ^ ctx.parameters.K :=
        ctx.parameters.growth ctx.recordCap ctx.recordCap_nonneg
      _ ≤ (Q + 2) ^ ctx.parameters.K := pow_le_pow_left₀ (by linarith [ctx.recordCap_nonneg]) (by linarith) _
      _ ≤ (Q + 2) ^ K := pow_le_pow_right₀ (by linarith) hK
  have hperiod : (ctx.periodCap : ℝ) ≤ 2 * ((s : ℝ) * ctx.workBudget) + 1 := by
    exact (Nat.ceil_lt_add_one (show 0 ≤ 2 * ((s : ℝ) * ctx.workBudget) by positivity)).le
  have hcost : (ctx.stepCost : ℝ) ≤ 2 * s * ub + 1 + Q := by
    simp only [PrimeStabilityContext.stepCost, Nat.cast_add]
    have hmul := mul_le_mul_of_nonneg_left hU (show 0 ≤ 2 * (s : ℝ) by positivity)
    nlinarith
  have hD : (ctx.allowance : ℝ) ≤ db := by
    simp only [PrimeStabilityContext.allowance, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one]
    dsimp only [db]
    gcongr
  have hF : (ctx.workBudget + 2) ^ ctx.parameters.Kf ≤ (ub + 2) ^ Kf :=
    (pow_le_pow_left₀ (by linarith) (show ctx.workBudget + 2 ≤ ub + 2 by linarith) _).trans
      (pow_le_pow_right₀ (by linarith) hKf)
  have hsum : db + Q * db + 5 * ub + 2 * (ub + 2) ^ Kf + 16 ≤ (Q + 2) ^ L := by
    simpa [P, D, U, ub, db, Polynomial.eval₂_pow] using hbudget Q hQ
  have hproduct : 0 ≤ Q * db := mul_nonneg hQ hdb
  have hpow : 0 ≤ (ub + 2) ^ Kf := by positivity
  refine ⟨hD.trans (by linarith), ?_⟩
  have hwidth : ctx.primeBudget * ctx.allowance + 5 * ctx.workBudget +
      2 * (ctx.workBudget + 2) ^ ctx.parameters.Kf + 16 ≤ Q * db + 5 * ub + 2 * (ub + 2) ^ Kf + 16 := by
    gcongr
  exact hwidth.trans (by linarith)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CoprimeResiduePhysicalStability
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem residuePrimeCoordinateMean_congr_assignment {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (I : Finset ι) (x y : ∀ i, σ → ZMod (q i)) (hxy : ∀ i ∈ I, x i = y i) :
    residuePrimeCoordinateMean f lo N M a q I x = residuePrimeCoordinateMean f lo N M a q I y := by
  classical
  let e : ResiduePrimeCoordinateCell lo N M a q I x ≃ ResiduePrimeCoordinateCell lo N M a q I y :=
    Equiv.subtypeEquivRight (fun z => ⟨fun hz i hi => (hz i hi).trans (hxy i hi),
      fun hz i hi => (hz i hi).trans (hxy i hi).symm⟩)
  exact Fintype.expect_equiv e _ _ (fun _ => rfl)

theorem ResiduePrimeCoordinateStable.congr_assignment {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    {f : (σ → ℤ) → ℂ} {lo : σ → ℤ} {N : σ → ℕ} {M : ℕ} {a : σ → ℤ} {q : ι → ℕ}
    {r : ℕ} {δ : ℝ} {I : Finset ι} {x y : ∀ i, σ → ZMod (q i)}
    (h : ResiduePrimeCoordinateStable f lo N M a q r δ I x) (hxy : ∀ i ∈ I, x i = y i) :
    ResiduePrimeCoordinateStable f lo N M a q r δ I y := by
  intro J hIJ hJ z hyz hnonempty
  rw [← residuePrimeCoordinateMean_congr_assignment f lo N M a q I x y hxy]
  exact h J hIJ hJ z (fun i hi => (hyz i hi).trans (hxy i hi).symm) hnonempty

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem residuePrimeCoordinateMean_affine {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (hM : 0 < M) (hcop : ∀ i, M.Coprime (q i)) (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    residuePrimeCoordinateMean f lo N M a q I
      (fun i => affineResidueCoordinateEquiv M (q i) a (hcop i) (x i)) =
    primeCoordinateMean (fun z => f (fun j => a j + (M : ℤ) * z j))
      (fun j => residueIndexLower (lo j) M (a j))
      (fun j => residueIndexLength (lo j) (lo j + N j) M (a j)) q I x := by
  classical
  exact (Fintype.expect_equiv (residuePrimeCoordinateCellEquiv lo N M a q hM hcop I x)
    _ _ (fun _ => rfl)).symm

theorem PrimeCoordinateStable.on_residue_slice {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (hM : 0 < M) (hcop : ∀ i, M.Coprime (q i)) (r : ℕ) (δ : ℝ)
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i))
    (h : PrimeCoordinateStable (fun z => f (fun j => a j + (M : ℤ) * z j))
      (fun j => residueIndexLower (lo j) M (a j))
      (fun j => residueIndexLength (lo j) (lo j + N j) M (a j)) q r δ I x) :
    ResiduePrimeCoordinateStable f lo N M a q r δ I
      (fun i => affineResidueCoordinateEquiv M (q i) a (hcop i) (x i)) := by
  intro J hIJ hJ y hxy hnonempty
  let inv : ∀ i, σ → ZMod (q i) := fun i =>
    (affineResidueCoordinateEquiv M (q i) a (hcop i)).symm (y i)
  have hy : (fun i => affineResidueCoordinateEquiv M (q i) a (hcop i) (inv i)) = y := by
    funext i
    exact Equiv.apply_symm_apply _ _
  have hagree : ∀ i ∈ I, inv i = x i := by
    intro i hi
    dsimp only [inv]
    rw [hxy i hi]
    exact Equiv.symm_apply_apply _ _
  have hne : (primeCoordinateCell (fun j => residueIndexLower (lo j) M (a j))
      (fun j => residueIndexLength (lo j) (lo j + N j) M (a j)) q (I ∪ J) inv).Nonempty := by
    rw [← hy] at hnonempty
    obtain ⟨z⟩ := hnonempty
    exact ⟨((residuePrimeCoordinateCellEquiv lo N M a q hM hcop (I ∪ J) inv).symm z).val,
      ((residuePrimeCoordinateCellEquiv lo N M a q hM hcop (I ∪ J) inv).symm z).property⟩
  rw [residuePrimeCoordinateMean_affine f lo N M a q hM hcop I x]
  have hmean := residuePrimeCoordinateMean_affine f lo N M a q hM hcop (I ∪ J) inv
  rw [hy] at hmean
  rw [hmean]
  exact h J hIJ hJ inv hagree hne

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

universe u v w

theorem exists_adapted_prime_coordinate_stability (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {ι : Type w} {σ : Type u} {L : Type v}
      [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] [TopologicalSpace (ℝ ⊗[ℚ] L)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)] [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (ω : Fin d → ℕ),
    (∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i})) →
    ∀ (p δ : ℝ), 2 ≤ p → (d : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
    0 < δ → δ ≤ 1 → δ⁻¹ ≤ Real.exp p →
    ∀ T : D.Niltest (fun _ : σ => 1), T.UnitIntervalValued → T.ComplexityLE p →
    ∀ (prime power : ι → ℕ), (∀ i, (prime i).Prime) → Function.Injective prime →
    (∀ i, ((prime i ^ power i : ℕ) : ℝ) ≤ Real.exp p) →
    ∀ (mandatory : Finset ι) (r : ℕ), (mandatory.card : ℝ) ≤ p → (r : ℝ) ≤ p →
    ∀ (lo : σ → ℤ) (N : σ → ℕ), (∀ i, 0 < N i) →
    (∀ i, Real.exp ((p + 2) ^ E) ≤ (N i : ℝ)) →
    ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (prime i ^ power i)), ∃ depth : ℕ,
      (depth : ℝ) ≤ (p + 2) ^ E ∧
      CoordinateDecisionTree.Valid
        (fun I x => mandatory ⊆ I ∧ PrimeCoordinateStable T.eval lo N (fun i => prime i ^ power i) r δ I x)
        ∅ (fun _ _ => 0) tree depth := by
  obtain ⟨parameters⟩ := exists_physical_stability_parameters_s2.{u, v} s
  obtain ⟨Lexp, hLexp, hbounds⟩ :=
    exists_prime_stability_polynomial_budget.{u, v, w} s parameters.K parameters.Kf
  let R : Polynomial ℕ := ((Polynomial.X + 2) ^ parameters.A + 2) ^ Lexp
  obtain ⟨E, hE, hpoly⟩ := exists_natPolynomial_fixed_power_budget R
  refine ⟨E, hE, ?_⟩
  intro ι σ L _ _ _ _ _ _ _ _ _ _ d D ω hadapted p δ hp hd hσ hδ hδone hδinv T hpositive hcomplexity
    prime power hprime hinj hprimeBound mandatory r hmandatory hr lo N hN hlarge
  let b := (p + 2) ^ parameters.A
  have hp0 : 0 ≤ p := by linarith
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hpb : p ≤ b := by
    calc
      p ≤ p + 2 := by linarith
      _ = (p + 2) ^ 1 := (pow_one _).symm
      _ ≤ (p + 2) ^ parameters.A := pow_le_pow_right₀ (by linarith) parameters.A_pos
  let base : PhysicalEpochSource.{u, v} σ s d := {
    Carrier := L
    dimension := d
    dimension_le := le_rfl
    model := D
    weights := ω
    adapted := hadapted
    fixedMap := T
    lower := lo
    sides := N
    sides_pos := hN
    incomingBudget := p
    recordBudget := b
    incoming_nonneg := hp0
    incoming_le_record := hpb
    geometry := hcomplexity.1
    coordinates_le := hσ }
  let ctx : PrimeStabilityContext.{u, v, w} ι σ s d := {
    parameters := parameters
    base := base
    baseline := T
    orbit := rfl
    positive := hpositive
    complexity := hcomplexity
    recordCap := b
    recordCap_nonneg := hb
    record_le_cap := le_rfl
    inflation := le_rfl
    record_two := hp.trans hpb
    gap := δ
    gap_pos := hδ
    gap_le_one := hδone
    gap_inverse := hδinv
    prime := prime
    power := power
    prime_prime := hprime
    prime_injective := hinj
    primeBudget := p
    primeBudget_nonneg := hp0
    prime_bound := hprimeBound
    witnessSize := r
    mandatory := mandatory }
  obtain ⟨hallowance, hwidth⟩ := hbounds ctx b hb le_rfl le_rfl le_rfl hpb (hr.trans hpb) (hmandatory.trans hpb) (hd.trans hpb)
  have hpower : (b + 2) ^ Lexp ≤ (p + 2) ^ E := by
    simpa [R, b, Polynomial.eval₂_pow] using hpoly p hp0
  have hctxLarge : ctx.HasLargeSides := by
    intro i
    exact (Real.exp_le_exp.mpr (hwidth.trans hpower)).trans (hlarge i)
  obtain ⟨tree, htree⟩ := ctx.exists_stable_tree hctxLarge
  exact ⟨tree, ctx.allowance, hallowance.trans hpower, htree⟩

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

universe u v w

theorem exists_prime_coordinate_box_stability (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {ι : Type w} {σ : Type u} {L : Type v}
      [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] [TopologicalSpace (ℝ ⊗[ℚ] L)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)] [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (p δ : ℝ),
    2 ≤ p → (Fintype.card σ : ℝ) ≤ p → 0 < δ → δ ≤ 1 → δ⁻¹ ≤ Real.exp p →
    ∀ T : D.Niltest (fun _ : σ => 1), T.UnitIntervalValued → T.ComplexityLE p →
    ∀ (prime power : ι → ℕ), (∀ i, (prime i).Prime) → Function.Injective prime →
    (∀ i, ((prime i ^ power i : ℕ) : ℝ) ≤ Real.exp p) →
    ∀ (mandatory : Finset ι) (r : ℕ), (mandatory.card : ℝ) ≤ p → (r : ℝ) ≤ p →
    ∀ (lo : σ → ℤ) (N : σ → ℕ), (∀ i, 0 < N i) →
    (∀ i, Real.exp ((p + 2) ^ E) ≤ (N i : ℝ)) →
    ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (prime i ^ power i)), ∃ depth : ℕ,
      (depth : ℝ) ≤ (p + 2) ^ E ∧
      CoordinateDecisionTree.Valid
        (fun I x => mandatory ⊆ I ∧ PrimeCoordinateStable T.eval lo N (fun i => prime i ^ power i) r δ I x)
        ∅ (fun _ _ => 0) tree depth := by
  obtain ⟨C, _, hrebase⟩ := RationalFilteredNilmanifold.exists_controlled_adapted_rebase
  obtain ⟨E₀, _, hstability⟩ := exists_adapted_prime_coordinate_stability.{u, v, w} s
  let P : Polynomial ℕ := ((Polynomial.X + Polynomial.C C) ^ C + 2) ^ E₀
  obtain ⟨E, hE, hpoly⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨E, hE, ?_⟩
  intro ι σ L _ _ _ _ _ _ _ _ _ _ d D p δ hp hσ hδ hδone hδinv T hpositive hcomplexity
    prime power hprime hinj hprimeBound mandatory r hmandatory hr lo N hN hlarge
  have hp0 : 0 ≤ p := by linarith
  obtain ⟨F, H, hH, hpq, hgeometry, htest, _⟩ := hrebase D hp0 hcomplexity.1
  let q := (p + C) ^ C
  have hpower : (q + 2) ^ E₀ ≤ (p + 2) ^ E := by
    simpa [P, q, Polynomial.eval₂_pow] using hpoly p hp0
  have hnewLarge : ∀ i, Real.exp ((q + 2) ^ E₀) ≤ (N i : ℝ) :=
    fun i => (Real.exp_le_exp.mpr hpower).trans (hlarge i)
  obtain ⟨tree, depth, hdepth, htree⟩ := hstability F.model F.weight F.model_layers q δ (hp.trans hpq)
    hgeometry.1 (hσ.trans hpq) hδ hδone (hδinv.trans (Real.exp_le_exp.mpr hpq))
    (F.rebaseNiltest H hH T) (F.rebaseNiltest_unit_interval H hH T hpositive) (htest T hcomplexity)
    prime power hprime hinj (fun i => (hprimeBound i).trans (Real.exp_le_exp.mpr hpq))
    mandatory r (hmandatory.trans hpq) (hr.trans hpq) lo N hN hnewLarge
  have heval : (F.rebaseNiltest H hH T).eval = T.eval := funext (F.rebaseNiltest_eval H hH T)
  rw [heval] at htree
  exact ⟨tree, depth, hdepth.trans hpower, htree⟩

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

theorem PrimeCoordinateStable.mono_tolerance
    {ι σ : Type*} [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    {f : (σ → ℤ) → ℂ} {lo : σ → ℤ} {N : σ → ℕ} {q : ι → ℕ}
    {r : ℕ} {δ ε : ℝ} {I : Finset ι} {x : ∀ i, σ → ZMod (q i)}
    (h : PrimeCoordinateStable f lo N q r δ I x) (hδε : δ ≤ ε) :
    PrimeCoordinateStable f lo N q r ε I x := by
  intro J hIJ hJ y hxy hnonempty
  exact (h J hIJ hJ y hxy hnonempty).trans hδε

universe u v w

theorem exists_prime_coordinate_box_stability_pos (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {ι : Type w} {σ : Type u} {L : Type v}
      [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] [TopologicalSpace (ℝ ⊗[ℚ] L)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)] [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (p δ : ℝ),
    2 ≤ p → (Fintype.card σ : ℝ) ≤ p → 0 < δ → δ⁻¹ ≤ Real.exp p →
    ∀ T : D.Niltest (fun _ : σ => 1), T.UnitIntervalValued → T.ComplexityLE p →
    ∀ (prime power : ι → ℕ), (∀ i, (prime i).Prime) → Function.Injective prime →
    (∀ i, ((prime i ^ power i : ℕ) : ℝ) ≤ Real.exp p) →
    ∀ (mandatory : Finset ι) (r : ℕ), (mandatory.card : ℝ) ≤ p → (r : ℝ) ≤ p →
    ∀ (lo : σ → ℤ) (N : σ → ℕ), (∀ i, 0 < N i) →
    (∀ i, Real.exp ((p + 2) ^ E) ≤ (N i : ℝ)) →
    ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (prime i ^ power i)), ∃ depth : ℕ,
      (depth : ℝ) ≤ (p + 2) ^ E ∧
      CoordinateDecisionTree.Valid
        (fun I x => mandatory ⊆ I ∧ PrimeCoordinateStable T.eval lo N (fun i => prime i ^ power i) r δ I x)
        ∅ (fun _ _ => 0) tree depth := by
  obtain ⟨E, hE, hstability⟩ := exists_prime_coordinate_box_stability.{u, v, w} s
  refine ⟨E, hE, ?_⟩
  intro ι σ L _ _ _ _ _ _ _ _ _ _ d D p δ hp hσ hδ hδinv T hpositive hcomplexity
    prime power hprime hinj hprimeBound mandatory r hmandatory hr lo N hN hlarge
  let ε := min δ 1
  have hε : 0 < ε := lt_min hδ (by norm_num)
  have hεone : ε ≤ 1 := min_le_right _ _
  have hεinv : ε⁻¹ ≤ Real.exp p := by
    by_cases hsmall : δ ≤ 1
    · simpa only [ε, min_eq_left hsmall] using hδinv
    · have hlargeδ : 1 ≤ δ := le_of_lt (lt_of_not_ge hsmall)
      simpa only [ε, min_eq_right hlargeδ, inv_one] using Real.one_le_exp (show 0 ≤ p by linarith)
  obtain ⟨tree, depth, hdepth, htree⟩ := hstability D p ε hp hσ hε hεone hεinv T hpositive hcomplexity
    prime power hprime hinj hprimeBound mandatory r hmandatory hr lo N hN hlarge
  refine ⟨tree, depth, hdepth, htree.map ?_⟩
  intro I x hleaf
  exact ⟨hleaf.1, hleaf.2.mono_tolerance (min_le_left δ 1)⟩

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

universe u v w

theorem exists_coprime_residue_prime_stability (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {ι : Type w} {σ : Type u} {L : Type v}
      [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] [TopologicalSpace (ℝ ⊗[ℚ] L)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)] [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (p δ : ℝ),
    2 ≤ p → (Fintype.card σ : ℝ) ≤ p → 0 < δ → δ⁻¹ ≤ Real.exp p →
    ∀ T : D.Niltest (fun _ : σ => 1), T.UnitIntervalValued → T.ComplexityLE p →
    ∀ (prime power : ι → ℕ), (∀ i, (prime i).Prime) → Function.Injective prime →
    (∀ i, ((prime i ^ power i : ℕ) : ℝ) ≤ Real.exp p) →
    ∀ (mandatory : Finset ι) (r : ℕ), (mandatory.card : ℝ) ≤ p → (r : ℝ) ≤ p →
    ∀ (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ), 0 < M →
    (∀ i, M.Coprime (prime i ^ power i)) →
    (∀ j, Real.exp ((p + 2) ^ E) ≤
      (residueIndexLength (lo j) (lo j + N j) M (a j) : ℝ)) →
    ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (prime i ^ power i)), ∃ depth : ℕ,
      (depth : ℝ) ≤ (p + 2) ^ E ∧
      CoordinateDecisionTree.Valid
        (fun I x => mandatory ⊆ I ∧
          ResiduePrimeCoordinateStable T.eval lo N M a (fun i => prime i ^ power i) r δ I x)
        ∅ (fun _ _ => 0) tree depth := by
  obtain ⟨E, hE, hstability⟩ := exists_prime_coordinate_box_stability_pos.{u, v, w} s
  refine ⟨E, hE, ?_⟩
  intro ι σ L _ _ _ _ _ _ _ _ _ _ d D p δ hp hσ hδ hδinv T hpositive hcomplexity
    prime power hprime hinj hprimeBound mandatory r hmandatory hr lo N M a hM hcop hlarge
  let q : ι → ℕ := fun i => prime i ^ power i
  let S := T.scalarAffinePullback (M : ℤ) (fun j => (a j : ℚ))
  have hSpos : S.UnitIntervalValued := hpositive
  have hScomplexity : S.ComplexityLE p := hcomplexity
  have hN : ∀ j, 0 < residueIndexLength (lo j) (lo j + N j) M (a j) := by
    intro j
    exact_mod_cast (Real.exp_pos ((p + 2) ^ E)).trans_le (hlarge j)
  obtain ⟨tree, depth, hdepth, htree⟩ := hstability D p δ hp hσ hδ hδinv S hSpos hScomplexity
    prime power hprime hinj hprimeBound mandatory r hmandatory hr
    (fun j => residueIndexLower (lo j) M (a j))
    (fun j => residueIndexLength (lo j) (lo j + N j) M (a j)) hN hlarge
  have heval : S.eval = (fun z => T.eval (fun j => a j + (M : ℤ) * z j)) := by
    funext z
    simpa only [S, add_comm] using T.scalarAffinePullback_eval_integer (M : ℤ) a z
  rw [heval] at htree
  let e : ∀ i, (σ → ZMod (q i)) ≃ (σ → ZMod (q i)) :=
    fun i => affineResidueCoordinateEquiv M (q i) a (hcop i)
  have hrelabeled := htree.relabel e
  have hresult : CoordinateDecisionTree.Valid
      (fun I x => mandatory ⊆ I ∧ ResiduePrimeCoordinateStable T.eval lo N M a q r δ I x)
      ∅ (CoordinateDecisionTree.relabelAssignment e (fun _ _ => 0)) (tree.relabel e) depth := by
    apply hrelabeled.map
    intro I x hx
    refine ⟨hx.1, ?_⟩
    have hs := PrimeCoordinateStable.on_residue_slice T.eval lo N M a q hM hcop r δ I
      (CoordinateDecisionTree.relabelAssignment (fun i => (e i).symm) x) hx.2
    simpa only [CoordinateDecisionTree.relabelAssignment, e, Equiv.apply_symm_apply] using hs
  refine ⟨tree.relabel e, depth, hdepth, hresult.congr_assignment ?_ (fun _ _ => 0) ?_⟩
  · intro I x y hxy hx
    exact ⟨hx.1, hx.2.congr_assignment hxy⟩
  · intro i hi
    exact False.elim (Finset.notMem_empty i hi)

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

universe u v w

theorem exists_coprime_residue_physical_stability_s2_oai (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {ι : Type w} {σ : Type u} {L : Type v}
      [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] [TopologicalSpace (ℝ ⊗[ℚ] L)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)] [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (p δ : ℝ),
    2 ≤ p → (Fintype.card σ : ℝ) ≤ p → 0 < δ → δ⁻¹ ≤ Real.exp p →
    ∀ T : D.Niltest (fun _ : σ => 1), T.UnitIntervalValued → T.ComplexityLE p →
    ∀ (prime power : ι → ℕ), (∀ i, (prime i).Prime) → Function.Injective prime →
    (∀ i, ((prime i ^ power i : ℕ) : ℝ) ≤ Real.exp p) →
    ∀ (mandatory : Finset ι) (r : ℕ), (mandatory.card : ℝ) ≤ p → (r : ℝ) ≤ p →
    ∀ (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ), 0 < M → (M : ℝ) ≤ Real.exp p →
    (∀ i, M.Coprime (prime i ^ power i)) →
    (∀ j, Real.exp ((p + 2) ^ E) ≤ (N j : ℝ)) →
    ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (prime i ^ power i)), ∃ depth : ℕ,
      (depth : ℝ) ≤ (p + 2) ^ E ∧
      CoordinateDecisionTree.Valid
        (fun I x => mandatory ⊆ I ∧
          ResiduePrimeCoordinateStable T.eval lo N M a (fun i => prime i ^ power i) r δ I x)
        ∅ (fun _ _ => 0) tree depth := by
  obtain ⟨E₀, _, hstability⟩ := exists_coprime_residue_prime_stability.{u, v, w} s
  let P : Polynomial ℕ := Polynomial.X + (Polynomial.X + 2) ^ E₀ + 2
  obtain ⟨E, hE, hpoly⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨E, hE, ?_⟩
  intro ι σ L _ _ _ _ _ _ _ _ _ _ d D p δ hp hσ hδ hδinv T hpositive hcomplexity
    prime power hprime hinj hprimeBound mandatory r hmandatory hr lo N M a hM hmodulus hcop hlarge
  have hp0 : 0 ≤ p := by linarith
  have hpower : p + (p + 2) ^ E₀ + 2 ≤ (p + 2) ^ E := by
    simpa [P, Polynomial.eval₂_pow] using hpoly p hp0
  have hparameters : ∀ j, Real.exp ((p + 2) ^ E₀) ≤
      (residueIndexLength (lo j) (lo j + N j) M (a j) : ℝ) := by
    intro j
    apply residueIndexLength_large_of_exp (lo j) (a j) (N j) M p ((p + 2) ^ E₀)
      hM (by positivity) hmodulus
    exact (Real.exp_le_exp.mpr hpower).trans (hlarge j)
  obtain ⟨tree, depth, hdepth, htree⟩ := hstability D p δ hp hσ hδ hδinv T hpositive hcomplexity
    prime power hprime hinj hprimeBound mandatory r hmandatory hr lo N M a hM hcop hparameters
  exact ⟨tree, depth, hdepth.trans (by linarith), htree⟩

end Erdos3

end

end OAI
end

theorem solution.{u, v, w} : type_of% @OAI.Erdos3.exists_coprime_residue_physical_stability_s2_oai.{u, v, w} := @OAI.Erdos3.exists_coprime_residue_physical_stability_s2_oai.{u, v, w}
