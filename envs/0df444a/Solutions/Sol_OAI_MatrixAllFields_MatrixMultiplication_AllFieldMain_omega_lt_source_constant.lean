-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:18:08.43597+00:00
-- url     : https://prove2.me/submissions/21ec9f30-f980-46e6-8d1c-c618ee299c17

import Mathlib
import Definitions.Def_MatrixFields
import Definitions.Def_OAIQ254M007
import Definitions.Def_OAIQ254M011
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldConstructionFamily_fixed_allocation_constraint
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldScheduledPositivity_nativeH0_pos
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_capacityABalls_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_initialProbs_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_nativeLBBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_native_denominator_gap
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_native_sharp_rate_bound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_native_stageC_balanced_positive
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_native_stageC_feasible
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_native_volume_positive

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_CertificatesReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.AllFieldCertificates

open MatrixMultiplication.Foundation.RationalLogCertificate

namespace Ball

theorem bounds {b : Ball} {x : ℝ} (h : b.Encloses x) :
    (b.lower : ℝ) ≤ x ∧ x ≤ (b.upper : ℝ) := by
  obtain ⟨hl, hu⟩ := abs_le.mp h
  simp only [lower, upper, Rat.cast_sub, Rat.cast_add]
  constructor <;> linarith

theorem add_sound {a b : Ball} {x y : ℝ} (hx : a.Encloses x) (hy : b.Encloses y) :
    (add a b).Encloses (x + y) := by
  unfold Encloses add
  simp only [Rat.cast_add]
  calc
    _ = |(x - (a.center : ℝ)) + (y - (b.center : ℝ))| := by congr 1; ring
    _ ≤ |x - (a.center : ℝ)| + |y - (b.center : ℝ)| := abs_add_le _ _
    _ ≤ _ := add_le_add hx hy

theorem widen_sound {a b : Ball} {x : ℝ} (hx : a.Encloses x)
    (h : |a.center - b.center| + a.radius ≤ b.radius) : b.Encloses x := by
  have hc : |(a.center : ℝ) - (b.center : ℝ)| + (a.radius : ℝ) ≤ (b.radius : ℝ) := by
    exact_mod_cast h
  unfold Encloses
  calc
    _ = |(x - (a.center : ℝ)) + ((a.center : ℝ) - (b.center : ℝ))| := by congr 1; ring
    _ ≤ |x - (a.center : ℝ)| + |(a.center : ℝ) - (b.center : ℝ)| := abs_add_le _ _
    _ ≤ (a.radius : ℝ) + |(a.center : ℝ) - (b.center : ℝ)| := add_le_add hx (le_refl _)
    _ ≤ _ := by linarith

end Ball

end MatrixMultiplication.AllFieldCertificates

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.AllFieldCertificates.Replay

open MatrixMultiplication.Foundation.RationalLogCertificate

theorem contains_sound {a b : Ball} {x : ℝ}
    (ha : a.Encloses x) (hab : contains a b = true) : b.Encloses x :=
  Ball.widen_sound ha (of_decide_eq_true hab)

end MatrixMultiplication.AllFieldCertificates.Replay

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistoryChildLaws
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryMasks.permutationsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.Staggering

theorem balanceFraction_pos (a b : Capacity) (high base : ℝ)
    (hbase : base < high)
    (hfeas : ∀ i, totalCapacity a b base - (a i + b i) < high) (i : Fin 3) :
    0 < balanceFraction a b high base i := by
  apply div_pos
  · linarith [hfeas i]
  · exact mul_pos (by norm_num) (sub_pos.mpr hbase)

theorem sum_balanceFraction (a b : Capacity) (high base : ℝ)
    (hbase : base < high) : ∑ i, balanceFraction a b high base i = 1 := by
  have hn : high - base ≠ 0 := ne_of_gt (sub_pos.mpr hbase)
  simp only [balanceFraction, Fin.sum_univ_succ,
    Fin.sum_univ_zero, add_zero]
  unfold totalCapacity
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  field_simp
  ring

theorem thirdCapacity_eq (a b : Capacity) (high base : ℝ)
    (hbase : base < high) (i : Fin 3) :
    thirdCapacity a b high base i = totalCapacity a b base - (a i + b i) := by
  have hn : high - base ≠ 0 := ne_of_gt (sub_pos.mpr hbase)
  unfold thirdCapacity balanceFraction
  field_simp
  ring

theorem minCapacity_pos (a : Capacity) (h : ∀ i, 0 < a i) :
    0 < minCapacity a := by
  exact lt_min (h 0) (lt_min (h 1) (h 2))

theorem finite_schedule_yield (a b c : Capacity) (full : ℝ) (K : ℕ) (hK : 2 ≤ K) :
    (K - 2 : ℕ) * full + minCapacity a + minCapacity (fun i => a i + b i) +
      minCapacity (fun i => b i + c i) + minCapacity c =
      (K : ℝ) * full - boundaryDeficit a b c full := by
  rw [Nat.cast_sub hK]
  norm_num [boundaryDeficit]
  ring

end MatrixMultiplication.Staggering

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.FiniteSchedule

open Staggering

theorem tickCapacity_first (K : ℕ) (hK : 2 ≤ K) (a b c : Capacity) :
    tickCapacity K a b c 0 = a := by
  funext i
  have h0 : 0 < K := by omega
  simp [tickCapacity, stageActive, h0]

theorem tickCapacity_second (K : ℕ) (hK : 2 ≤ K) (a b c : Capacity) :
    tickCapacity K a b c 1 = fun i => a i + b i := by
  funext i
  have h1 : 1 < K := by omega
  have h2 : 1 < K + 1 := by omega
  simp [tickCapacity, stageActive, h1, h2]

theorem tickCapacity_interior (K tick : ℕ) (ht : 2 ≤ tick) (htK : tick < K)
    (a b c : Capacity) :
    tickCapacity K a b c tick = fun i => a i + b i + c i := by
  funext i
  have h1 : 1 ≤ tick := by omega
  have ht1 : tick < K + 1 := by omega
  have ht2 : tick < K + 2 := by omega
  simp [tickCapacity, stageActive, ht, htK, h1, ht1, ht2]

theorem tickCapacity_penultimate (K : ℕ) (hK : 2 ≤ K) (a b c : Capacity) :
    tickCapacity K a b c K = fun i => b i + c i := by
  funext i
  have h1 : 1 ≤ K := by omega
  simp [tickCapacity, stageActive, hK, h1]

theorem tickCapacity_last (K : ℕ) (hK : 2 ≤ K) (a b c : Capacity) :
    tickCapacity K a b c (K + 1) = c := by
  funext i
  have h1 : 2 ≤ K + 1 := by omega
  simp [tickCapacity, stageActive, h1]

theorem sum_tick_minima (K : ℕ) (hK : 2 ≤ K) (a b c : Capacity) (full : ℝ)
    (hfull : ∀ i, a i + b i + c i = full) :
    (∑ tick ∈ Finset.range (K + 2), minCapacity (tickCapacity K a b c tick)) =
      (K - 2 : ℕ) * full + minCapacity a + minCapacity (fun i => a i + b i) +
        minCapacity (fun i => b i + c i) + minCapacity c := by
  let f : ℕ → ℝ := fun tick => minCapacity (tickCapacity K a b c tick)
  have hhead : ∑ tick ∈ Finset.range 2, f tick =
      minCapacity a + minCapacity (fun i => a i + b i) := by
    simp [f, Finset.sum_range_succ, tickCapacity_first K hK,
      tickCapacity_second K hK]
  have hinterior : (∑ tick ∈ Finset.range (K - 2), f (2 + tick)) =
      (K - 2 : ℕ) * full := by
    calc
      _ = ∑ _tick ∈ Finset.range (K - 2), full := by
        apply Finset.sum_congr rfl
        intro tick htick
        have hlt := Finset.mem_range.mp htick
        dsimp [f]
        rw [tickCapacity_interior K (2 + tick) (by omega) (by omega)]
        simp [minCapacity, hfull]
      _ = _ := by simp
  have htail : (∑ tick ∈ Finset.range 2, f (K + tick)) =
      minCapacity (fun i => b i + c i) + minCapacity c := by
    simp [f, Finset.sum_range_succ, tickCapacity_penultimate K hK,
      tickCapacity_last K hK]
  change (∑ tick ∈ Finset.range (K + 2), f tick) = _
  rw [Finset.sum_range_add f K 2, htail]
  have hsplit : (∑ tick ∈ Finset.range K, f tick) =
      (∑ tick ∈ Finset.range 2, f tick) +
        ∑ tick ∈ Finset.range (K - 2), f (2 + tick) := by
    have hKsum : 2 + (K - 2) = K := by omega
    simpa only [hKsum] using Finset.sum_range_add f 2 (K - 2)
  rw [hsplit, hhead, hinterior]
  ring

theorem finite_schedule_yield (K : ℕ) (hK : 2 ≤ K) (a b c : Capacity) (full : ℝ)
    (hfull : ∀ i, a i + b i + c i = full) :
    (∑ tick ∈ Finset.range (K + 2), minCapacity (tickCapacity K a b c tick)) =
      (K : ℝ) * full - boundaryDeficit a b c full := by
  rw [sum_tick_minima K hK a b c full hfull]
  exact Staggering.finite_schedule_yield a b c full K hK

theorem fixed_lot_boundary_limit {Y beta w S R : ℝ}
    (hfixed : ∀ K : ℕ, 2 ≤ K → Y - beta / (K : ℝ) + w * S / 3 ≤ R) :
    Y + w * S / 3 ≤ R := by
  by_contra hnot
  have hgap : 0 < Y + w * S / 3 - R := by linarith
  obtain ⟨K, hK⟩ := exists_nat_gt (max (beta / (Y + w * S / 3 - R)) (2 : ℝ))
  have hKtwo : (2 : ℝ) < (K : ℝ) := lt_of_le_of_lt (le_max_right _ _) hK
  have hKnat : 2 ≤ K := Nat.ofNat_le_cast.mp hKtwo.le
  have hKpos : (0 : ℝ) < (K : ℝ) := by linarith
  have hsmall : beta / (K : ℝ) < Y + w * S / 3 - R := by
    apply (div_lt_iff₀ hKpos).2
    have hquot : beta / (Y + w * S / 3 - R) < (K : ℝ) :=
      lt_of_le_of_lt (le_max_left _ _) hK
    simpa only [mul_comm] using (div_lt_iff₀ hgap).1 hquot
  have hbound := hfixed K hKnat
  linarith

end MatrixMultiplication.FiniteSchedule

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.PhysicalOrders

open Staggering

variable {History : Type*} [Fintype History]

theorem sum_physical_order_minima (amount : History → ℝ)
    (capacity : History → Capacity) (priority : History → PhysicalOrder) :
    (∑ sigma : PhysicalOrder,
      minCapacity (perPhysicalOrderCapacity amount capacity priority sigma)) =
        minCapacity (aggregateCapacity amount capacity) := by
  simp_rw [perPhysicalOrderCapacity_eq,
    minCapacity_mul _ (1 / 6 : ℝ) (by norm_num)]
  simp only [Finset.sum_const, Finset.card_univ, card_physical_orders, nsmul_eq_mul]
  norm_num
  ring

end MatrixMultiplication.PhysicalOrders

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters

theorem sum_physicalTick_minima {K : ℕ} (allocation : Allocation) (tick : ℕ)
    (capacity : Work K → Staggering.Capacity) :
    (∑ sigma : Placement, Staggering.minCapacity
      (physicalTickCapacity allocation tick capacity sigma)) =
        Staggering.minCapacity (activeAggregateCapacity allocation tick capacity) := by
  simp_rw [physicalTickCapacity_eq_partition]
  exact PhysicalOrders.sum_physical_order_minima _ _ _

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_ComplexRationalTypes
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.branchLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.placedLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.Foundation

open scoped BigOperators

private theorem exists_nonnegative_rat_below (x : ℝ) (hx : 0 ≤ x)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ r : ℚ, 0 ≤ r ∧ (r : ℝ) ≤ x ∧ (r = 0 ↔ x = 0) ∧
      |(r : ℝ) - x| < δ := by
  by_cases hx0 : x = 0
  · subst x
    exact ⟨0, le_rfl, by simp, by simp, by simpa using hδ⟩
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hlo : max 0 (x - δ) < x := max_lt hxpos (by linarith)
  obtain ⟨r, hrlo, hrhi⟩ := exists_rat_btwn hlo
  have hrpos : (0 : ℝ) < r := lt_of_le_of_lt (le_max_left _ _) hrlo
  have hrposq : (0 : ℚ) < r := by exact_mod_cast hrpos
  refine ⟨r, hrposq.le, hrhi.le,
    iff_of_false (ne_of_gt hrposq) hx0, ?_⟩
  have hrlo' : x - δ < r := lt_of_le_of_lt (le_max_right _ _) hrlo
  rw [abs_of_nonpos (sub_nonpos.mpr hrhi.le)]
  linarith

namespace FiniteLaw

variable {A : Type*} [Fintype A]

theorem exists_rational_approximation (p : FiniteLaw A) (ε : ℝ) (hε : 0 < ε) :
    ∃ q : RationalLaw A,
      (∀ a, q.mass a = 0 ↔ p.mass a = 0) ∧
      ∀ a, |(q.mass a : ℝ) - p.mass a| < ε := by
  classical
  have hpivot : ∃ a, 0 < p.mass a := by
    by_contra h
    have hnonpos : ∀ a, p.mass a ≤ 0 :=
      fun a => le_of_not_gt (fun ha => h ⟨a, ha⟩)
    have hsum : (∑ a, p.mass a) ≤ 0 :=
      Finset.sum_nonpos (fun a _ => hnonpos a)
    rw [p.total] at hsum
    norm_num at hsum
  obtain ⟨a₀, ha₀⟩ := hpivot
  let δ : ℝ := ε / ((Fintype.card A : ℝ) + 1)
  have hcard : 0 ≤ (Fintype.card A : ℝ) := Nat.cast_nonneg _
  have hden : 0 < (Fintype.card A : ℝ) + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hden
  have hδε : δ * ((Fintype.card A : ℝ) + 1) = ε :=
    div_mul_cancel₀ ε (ne_of_gt hden)
  have hcardδ : 0 ≤ (Fintype.card A : ℝ) * δ := mul_nonneg hcard hδ.le
  have hδle : δ ≤ ε := by nlinarith
  choose r hrnonneg hrle hrzero hrclose using
    fun a => exists_nonnegative_rat_below (p.mass a) (p.nonneg a) δ hδ
  have hsum : (∑ a, (r a : ℝ)) ≤ 1 := by
    calc
      (∑ a, (r a : ℝ)) ≤ ∑ a, p.mass a :=
        Finset.sum_le_sum (fun a _ => hrle a)
      _ = 1 := p.total
  have hrest : 0 ≤ 1 - ∑ a, (r a : ℝ) := sub_nonneg.mpr hsum
  have hrestq : (0 : ℚ) ≤ 1 - ∑ a, r a := by exact_mod_cast hrest
  have hrest_le : 1 - ∑ a, (r a : ℝ) ≤ (Fintype.card A : ℝ) * δ := by
    calc
      1 - ∑ a, (r a : ℝ) = ∑ a, (p.mass a - (r a : ℝ)) := by
        rw [Finset.sum_sub_distrib, p.total]
      _ ≤ ∑ _a : A, δ := by
        apply Finset.sum_le_sum
        intro a _
        have h := (abs_lt.mp (hrclose a)).1
        linarith
      _ = (Fintype.card A : ℝ) * δ := by simp
  let q : RationalLaw A :=
    { mass := fun a => r a + if a = a₀ then 1 - ∑ b, r b else 0
      nonneg := by
        intro a
        apply add_nonneg (hrnonneg a)
        split_ifs
        · exact hrestq
        · exact le_rfl
      total := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
        ring }
  refine ⟨q, ?_, ?_⟩
  · intro a
    by_cases ha : a = a₀
    · subst a
      have hrpos : 0 < r a₀ :=
        lt_of_le_of_ne (hrnonneg a₀) (Ne.symm (fun hz => (ne_of_gt ha₀) ((hrzero a₀).mp hz)))
      have hqpos : 0 < q.mass a₀ := by
        dsimp [q]
        simp only [ite_true, if_true]
        linarith
      exact iff_of_false (ne_of_gt hqpos) (ne_of_gt ha₀)
    · simpa only [q, ite_eq_right ha, add_zero] using hrzero a
  · intro a
    by_cases ha : a = a₀
    · have hqcast : (q.mass a : ℝ) =
          (r a : ℝ) + (1 - ∑ b, (r b : ℝ)) := by
        simp [q, ha]
      rw [hqcast]
      have habs : |(r a : ℝ) + (1 - ∑ b, (r b : ℝ)) - p.mass a| ≤
          |(r a : ℝ) - p.mass a| + (1 - ∑ b, (r b : ℝ)) := by
        calc
          _ = |((r a : ℝ) - p.mass a) + (1 - ∑ b, (r b : ℝ))| := by
            congr 1
            ring
          _ ≤ |(r a : ℝ) - p.mass a| + |1 - ∑ b, (r b : ℝ)| := abs_add_le _ _
          _ = _ := by rw [abs_of_nonneg hrest]
      have hclose := hrclose a
      nlinarith
    · simpa only [q, ite_eq_right ha, add_zero] using
        lt_of_lt_of_le (hrclose a) hδle

end FiniteLaw

end MatrixMultiplication.Foundation

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_NativeCapacity
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldNativeCapacity

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {A : Type*} [Fintype A]

theorem nativeLC_expansion (allocation : Fin 3 → ℝ) (i : Fin 3) :
    nativeLC allocation i = nativeHigh - 3 * allocation i * (nativeHigh - nativeB) := by
  unfold nativeLC nativeHigh nativeT nativeB
  have h : ∀ xs : List (Shape × Shape),
      (xs.map fun tu => interiorMass tu *
        ((1 - allocation i) * Real.log 2 + allocation i * interiorEntropy tu)).sum =
      (xs.map interiorMass).sum * Real.log 2 - 3 * allocation i *
        ((xs.map interiorMass).sum * Real.log 2 -
          (xs.map fun tu => interiorMass tu *
            (2 * Real.log 2 + interiorEntropy tu)).sum / 3) := by
    intro xs
    induction xs with
    | nil => simp
    | cons tu xs ih => simp only [List.map_cons, List.sum_cons]; rw [ih]; ring
  exact h interiorPairs

theorem nativeLC_balanced (hgap : nativeB < nativeHigh) (i : Fin 3) :
    nativeLC nativeLambda i = nativeCstar - (nativeLA i + nativeLB i) := by
  rw [nativeLC_expansion]
  exact Staggering.thirdCapacity_eq nativeLA nativeLB nativeHigh nativeB hgap i

theorem native_balanced (hgap : nativeB < nativeHigh) (i : Fin 3) :
    nativeLA i + nativeLB i + nativeLC nativeLambda i = nativeCstar := by
  rw [nativeLC_balanced hgap]
  ring

end MatrixMultiplication.AllFieldNativeCapacity

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SparseContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldInitialEntropyCertificate
open AllFieldParameters AllFieldCertificates AllFieldCertificates.Replay
open scoped BigOperators

lemma listSumBall_sound {α : Type*} (xs : List α) (b : α → Ball) (v : α → ℝ)
    (h : ∀ x ∈ xs, (b x).Encloses (v x)) :
    (listSumBall xs b).Encloses ((xs.map v).sum) := by
  induction xs with
  | nil => simpa [listSumBall] using Ball.exact_sound 0
  | cons x xs ih =>
    simpa only [listSumBall, List.foldr_cons, List.map_cons, List.sum_cons] using
      Ball.add_sound (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

end MatrixMultiplication.AllFieldInitialEntropyCertificate

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators

lemma forall_fin3 {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ i, P i := by
  intro i
  fin_cases i <;> assumption

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_NativeSharp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma nativeLABall_sound_0 : (nativeLABall 0).Encloses (nativeLA 0) := by
  exact contains_sound (listSumBall_sound positiveInitial
    (fun s => .mul (initialProbs s) (capacityABalls s 0)) _
    (fun s hs => Ball.mul_sound (initialProbs_sound s (List.mem_filter.mp hs).1)
      (capacityABalls_sound s hs 0))) (by decide +kernel)
lemma nativeLABall_sound_1 : (nativeLABall 1).Encloses (nativeLA 1) := by
  exact contains_sound (listSumBall_sound positiveInitial
    (fun s => .mul (initialProbs s) (capacityABalls s 1)) _
    (fun s hs => Ball.mul_sound (initialProbs_sound s (List.mem_filter.mp hs).1)
      (capacityABalls_sound s hs 1))) (by decide +kernel)
lemma nativeLABall_sound_2 : (nativeLABall 2).Encloses (nativeLA 2) := by
  exact contains_sound (listSumBall_sound positiveInitial
    (fun s => .mul (initialProbs s) (capacityABalls s 2)) _
    (fun s hs => Ball.mul_sound (initialProbs_sound s (List.mem_filter.mp hs).1)
      (capacityABalls_sound s hs 2))) (by decide +kernel)
lemma nativeLABall_sound (i : Fin 3) : (nativeLABall i).Encloses (nativeLA i) := by
  revert i
  exact forall_fin3 nativeLABall_sound_0 nativeLABall_sound_1 nativeLABall_sound_2

theorem native_stageA_positive (i : Fin 3) : 0 < nativeLA i := by
  have hp : 0 < (nativeLABall i).lower := by fin_cases i <;> decide +kernel
  have hp' : (0 : ℝ) < (nativeLABall i).lower := by exact_mod_cast hp
  exact hp'.trans_le (Ball.bounds (nativeLABall_sound i)).1

theorem native_stageB_positive (i : Fin 3) : 0 < nativeLB i := by
  have hp : 0 < (nativeLBBall i).lower := by fin_cases i <;> decide +kernel
  have hp' : (0 : ℝ) < (nativeLBBall i).lower := by exact_mod_cast hp
  exact hp'.trans_le (Ball.bounds (nativeLBBall_sound i)).1

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_ConditionalContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.ConditionalLabels

open MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology Classical

universe u v w
variable {A : Type u} [Fintype A] {Label : ℕ → Type v}
  [∀ n, Fintype (Label n)]

theorem exists_rational_law_sequence (p : FiniteLaw A) :
    ∃ q : ℕ → RationalLaw A,
      ∀ a, Tendsto (fun n => (q n).toFiniteLaw.mass a) atTop (𝓝 (p.mass a)) := by
  have hexists (n : ℕ) := p.exists_rational_approximation
    (1 / ((n : ℝ) + 1)) (by positivity)
  choose q _support close using hexists
  refine ⟨q, fun a => ?_⟩
  have hdifference : Tendsto
      (fun n => (q n).toFiniteLaw.mass a - p.mass a) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ tendsto_one_div_add_atTop_nhds_zero_nat
    intro n
    simpa only [Real.norm_eq_abs, RationalLaw.toFiniteLaw_mass] using (close n a).le
  simpa only [sub_add_cancel, zero_add] using hdifference.add_const (p.mass a)

end MatrixMultiplication.ConditionalLabels

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_ScheduledPositivity
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.card_tags _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldStageCFinish.counts_false _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.bWeight_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldScheduledYield

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory AllFieldNativeCapacity
open Filter
open scoped BigOperators Topology

theorem physicalYield_eq_scheduled (K : ℕ) (allocation : Allocation) :
    physicalYield K allocation = scheduledYield K (fun i => (allocation.mass i : ℝ)) := by
  unfold physicalYield scheduledYield
  apply Finset.sum_congr rfl
  intro tick htick
  rw [sum_physicalTick_minima, active_native_capacity]

theorem balanced_scheduledYield (K : ℕ) (hK : 2 ≤ K) (hgap : nativeB < nativeHigh) :
    scheduledYield K nativeLambda = (K : ℝ) * nativeCstar - nativeBeta :=
  FiniteSchedule.finite_schedule_yield K hK nativeLA nativeLB
    (nativeLC nativeLambda) nativeCstar (native_balanced hgap)

theorem nativeLC_tendsto {J : Type*} {filter : Filter J}
    {allocation : J → Fin 3 → ℝ} {limit : Fin 3 → ℝ}
    (h : ∀ i, Tendsto (fun j => allocation j i) filter (𝓝 (limit i))) (i : Fin 3) :
    Tendsto (fun j => nativeLC (allocation j) i) filter (𝓝 (nativeLC limit i)) := by
  simp_rw [nativeLC_expansion]
  exact tendsto_const_nhds.sub (((h i).const_mul 3).mul_const (nativeHigh - nativeB))

theorem tickCapacity_tendsto (K tick : ℕ) {J : Type*} {filter : Filter J}
    {allocation : J → Fin 3 → ℝ} {limit : Fin 3 → ℝ}
    (h : ∀ i, Tendsto (fun j => allocation j i) filter (𝓝 (limit i))) (i : Fin 3) :
    Tendsto (fun j => FiniteSchedule.tickCapacity K nativeLA nativeLB
      (nativeLC (allocation j)) tick i) filter
      (𝓝 (FiniteSchedule.tickCapacity K nativeLA nativeLB (nativeLC limit) tick i)) := by
  have hc : Tendsto (fun j => if FiniteSchedule.stageActive K tick 2 then
      nativeLC (allocation j) i else 0) filter
      (𝓝 (if FiniteSchedule.stageActive K tick 2 then nativeLC limit i else 0)) := by
    by_cases hh : FiniteSchedule.stageActive K tick 2
    · simpa only [hh, ite_true, if_true] using nativeLC_tendsto h i
    · simpa only [hh, ite_false, if_false] using (tendsto_const_nhds :
        Tendsto (fun _ : J => (0 : ℝ)) filter (𝓝 0))
  exact (tendsto_const_nhds.add tendsto_const_nhds).add hc

theorem scheduledYield_tendsto (K : ℕ) {J : Type*} {filter : Filter J}
    {allocation : J → Fin 3 → ℝ} {limit : Fin 3 → ℝ}
    (h : ∀ i, Tendsto (fun j => allocation j i) filter (𝓝 (limit i))) :
    Tendsto (fun j => scheduledYield K (allocation j)) filter
      (𝓝 (scheduledYield K limit)) := by
  unfold scheduledYield
  apply tendsto_finsetSum
  intro tick htick
  exact (tickCapacity_tendsto K tick h 0).min
    ((tickCapacity_tendsto K tick h 1).min (tickCapacity_tendsto K tick h 2))

theorem physicalYield_tendsto_balanced (K : ℕ) (hK : 2 ≤ K)
    (hgap : nativeB < nativeHigh) (allocation : ℕ → Allocation)
    (h : ∀ i, Tendsto (fun j => ((allocation j).mass i : ℝ)) atTop (𝓝 (nativeLambda i))) :
    Tendsto (fun j => physicalYield K (allocation j)) atTop
      (𝓝 ((K : ℝ) * nativeCstar - nativeBeta)) := by
  simp_rw [physicalYield_eq_scheduled]
  rw [← balanced_scheduledYield K hK hgap]
  exact scheduledYield_tendsto K h

theorem exists_balanced_allocation_sequence (hgap : nativeB < nativeHigh)
    (hfeas : ∀ i, nativeCstar - (nativeLA i + nativeLB i) < nativeHigh) :
    ∃ allocation : ℕ → Allocation,
      ∀ i, Tendsto (fun j => ((allocation j).mass i : ℝ)) atTop (𝓝 (nativeLambda i)) := by
  have hpos (i : Fin 3) : 0 < nativeLambda i :=
    Staggering.balanceFraction_pos nativeLA nativeLB nativeHigh nativeB hgap hfeas i
  let p : FiniteLaw (Fin 3) := {
    mass := nativeLambda
    nonneg := fun i => (hpos i).le
    total := Staggering.sum_balanceFraction nativeLA nativeLB nativeHigh nativeB hgap }
  obtain ⟨q, hq⟩ := ConditionalLabels.exists_rational_law_sequence p
  have he : ∀ᶠ j in atTop, ∀ i, 0 < (q j).toFiniteLaw.mass i :=
    Filter.eventually_all.mpr (fun i => (hq i).eventually_const_lt (hpos i))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp he
  let allocation : ℕ → Allocation := fun j => {
    mass := (q (j + N)).mass
    positive := fun i => by
      have hi := hN (j + N) (by omega) i
      change (0 : ℝ) < ((q (j + N)).mass i : ℝ) at hi
      exact_mod_cast hi
    total := (q (j + N)).total }
  refine ⟨allocation, fun i => ?_⟩
  exact (hq i).comp (tendsto_add_atTop_nat N)

end MatrixMultiplication.AllFieldScheduledYield

namespace MatrixMultiplication.AllFieldScheduledPositivity

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open AllFieldInitialEntropy AllFieldNativeCapacity AllFieldScheduledYield Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

theorem initial_capacity_pos (K : ℕ) (hK : 0 < K) :
    0 < (K : ℝ) * nativeH0 := mul_pos (Nat.cast_pos.mpr hK) nativeH0_pos

theorem tickCapacity_pos (K tick : ℕ) (hK : 2 ≤ K) (htick : tick < K + 2)
    (a b c : Staggering.Capacity)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (i : Fin 3) : 0 < FiniteSchedule.tickCapacity K a b c tick i := by
  have hA := ha i
  have hB := hb i
  have hC := hc i
  unfold FiniteSchedule.tickCapacity
  split_ifs <;> first
    | positivity
    | (simp only [FiniteSchedule.stageActive, Fin.val_zero, Fin.val_one] at *; omega)

theorem physical_order_capacity_pos (K tick : ℕ) (hK : 2 ≤ K)
    (htick : tick < K + 2) (allocation : Allocation) (sigma : Placement)
    (ha : ∀ i, 0 < nativeLA i) (hb : ∀ i, 0 < nativeLB i)
    (hc : ∀ i, 0 < nativeLC (fun j => (allocation.mass j : ℝ)) i) :
    0 < Staggering.minCapacity
      (physicalTickCapacity allocation tick (workCapacity (K := K)) sigma) := by
  rw [physical_order_native_capacity, PhysicalOrders.minCapacity_mul _ _ (by norm_num)]
  exact mul_pos (by norm_num) (Staggering.minCapacity_pos _
    (tickCapacity_pos K tick hK htick _ _ _ ha hb hc))

theorem eventually_physical_order_capacity_pos (K : ℕ) (hK : 2 ≤ K)
    (allocation : ℕ → Allocation)
    (h : ∀ i, Tendsto (fun j => ((allocation j).mass i : ℝ)) atTop (𝓝 (nativeLambda i)))
    (ha : ∀ i, 0 < nativeLA i) (hb : ∀ i, 0 < nativeLB i)
    (hc : ∀ i, 0 < nativeLC nativeLambda i) :
    ∀ᶠ j in atTop, ∀ tick < K + 2, ∀ sigma : Placement,
      0 < Staggering.minCapacity
        (physicalTickCapacity (allocation j) tick (workCapacity (K := K)) sigma) := by
  have he : ∀ᶠ j in atTop, ∀ i,
      0 < nativeLC (fun k => ((allocation j).mass k : ℝ)) i :=
    Filter.eventually_all.mpr fun i => (nativeLC_tendsto h i).eventually_const_lt (hc i)
  filter_upwards [he] with j hj
  exact fun tick htick sigma =>
    physical_order_capacity_pos K tick hK htick (allocation j) sigma ha hb hj

end MatrixMultiplication.AllFieldScheduledPositivity

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_ConstructionLabels
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldConstructionRates

open MatrixMultiplication.Foundation AllFieldHistory AllFieldScheduledYield
open AllFieldActiveLaws Filter
open scoped BigOperators Topology Classical

variable {K : ℕ}

theorem eventually_capacity_pos (hK : 2 ≤ K) (allocation : ℕ → Allocation)
    (h : ∀ i, Tendsto (fun j => ((allocation j).mass i : ℝ)) atTop
      (𝓝 (AllFieldNativeCapacity.nativeLambda i)))
    (ha : ∀ i, 0 < AllFieldNativeCapacity.nativeLA i)
    (hb : ∀ i, 0 < AllFieldNativeCapacity.nativeLB i)
    (hc : ∀ i, 0 < AllFieldNativeCapacity.nativeLC AllFieldNativeCapacity.nativeLambda i) :
    ∀ᶠ j in atTop, ∀ slot : Slot K, 0 < capacity (allocation j) slot := by
  filter_upwards [AllFieldScheduledPositivity.eventually_physical_order_capacity_pos
    K hK allocation h ha hb hc] with j hj
  intro slot
  cases slot with
  | inl u => exact AllFieldScheduledPositivity.initial_capacity_pos K (by omega)
  | inr p => exact hj p.1.val p.1.isLt p.2

end MatrixMultiplication.AllFieldConstructionRates

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_OrderedLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldOrderedLimits

open AllFieldHistory AllFieldNativeCapacity AllFieldScheduledYield
open AllFieldConstructionRates Filter
open scoped Topology

variable (F : Type*) [Field F]

theorem fixed_lot_constraint (K : ℕ) (hK : 2 ≤ K)
    (hgap : nativeB < nativeHigh)
    (hfeas : ∀ i, nativeCstar - (nativeLA i + nativeLB i) < nativeHigh)
    (ha : ∀ i, 0 < nativeLA i) (hb : ∀ i, 0 < nativeLB i)
    (hc : ∀ i, 0 < nativeLC nativeLambda i) :
    AllFieldInitialEntropy.nativeH0 + nativeCstar - nativeBeta / (K : ℝ) +
      (Arithmetic.omega F / 3) * AllFieldTerminalRates.S ≤ 8 * Real.log 7 := by
  obtain ⟨allocation, halloc⟩ := exists_balanced_allocation_sequence hgap hfeas
  have hcap := eventually_capacity_pos hK allocation halloc ha hb hc
  have hy := (physicalYield_tendsto_balanced K hK hgap allocation halloc).div_const (K : ℝ)
  have hH0 : Tendsto (fun _ : ℕ => AllFieldInitialEntropy.nativeH0) atTop
      (𝓝 AllFieldInitialEntropy.nativeH0) := tendsto_const_nhds
  have hlimit := (hH0.add hy).add
    (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
      (Arithmetic.omega F / 3) * AllFieldTerminalRates.S) atTop (𝓝 _))
  have hineq : AllFieldInitialEntropy.nativeH0 +
      ((K : ℝ) * nativeCstar - nativeBeta) / (K : ℝ) +
      (Arithmetic.omega F / 3) * AllFieldTerminalRates.S ≤ 8 * Real.log 7 := by
    apply le_of_tendsto_of_tendsto hlimit tendsto_const_nhds
    filter_upwards [hcap] with j hj
    exact AllFieldConstructionFamily.fixed_allocation_constraint F (by omega)
      (allocation j) hj
  have hk : (K : ℝ) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
  have heq : ((K : ℝ) * nativeCstar - nativeBeta) / (K : ℝ) =
      nativeCstar - nativeBeta / (K : ℝ) := by
    rw [sub_div, mul_div_cancel_left₀ _ hk]
  rw [heq] at hineq
  linarith

theorem native_rank_constraint
    (hgap : nativeB < nativeHigh)
    (hfeas : ∀ i, nativeCstar - (nativeLA i + nativeLB i) < nativeHigh)
    (ha : ∀ i, 0 < nativeLA i) (hb : ∀ i, 0 < nativeLB i)
    (hc : ∀ i, 0 < nativeLC nativeLambda i) :
    AllFieldInitialEntropy.nativeH0 + nativeCstar +
      (Arithmetic.omega F / 3) * AllFieldTerminalRates.S ≤ 8 * Real.log 7 := by
  have hfixed (K : ℕ) (hK : 2 ≤ K) :
      (AllFieldInitialEntropy.nativeH0 + nativeCstar) - nativeBeta / (K : ℝ) +
        Arithmetic.omega F * AllFieldTerminalRates.S / 3 ≤ 8 * Real.log 7 := by
    have h := fixed_lot_constraint F K hK hgap hfeas ha hb hc
    nlinarith
  have h := FiniteSchedule.fixed_lot_boundary_limit hfixed
  nlinarith

theorem omega_le_native_ratio
    (hgap : nativeB < nativeHigh)
    (hfeas : ∀ i, nativeCstar - (nativeLA i + nativeLB i) < nativeHigh)
    (ha : ∀ i, 0 < nativeLA i) (hb : ∀ i, 0 < nativeLB i)
    (hc : ∀ i, 0 < nativeLC nativeLambda i)
    (hS : 0 < AllFieldTerminalRates.S) :
    Arithmetic.omega F ≤
      3 * (8 * Real.log 7 -
        (AllFieldInitialEntropy.nativeH0 + nativeCstar)) / AllFieldTerminalRates.S := by
  apply (le_div_iff₀ hS).mpr
  have h := native_rank_constraint F hgap hfeas ha hb hc
  nlinarith

end MatrixMultiplication.AllFieldOrderedLimits

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Conclusions_AllFieldsBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.AllFieldMain
open AllFieldNativeCapacity AllFieldTerminalRates AllFieldInitialEntropy NativeNumerics

universe u

theorem omega_lt_source_constant_oai (F : Type u) [Field F] :
    Arithmetic.omega F < (2371054886006746 : ℝ) / 10 ^ 15 ∧
    (2371054886006746 : ℝ) / 10 ^ 15 < (2371056 : ℝ) / 10 ^ 6 := by
  constructor
  · have hbound := AllFieldOrderedLimits.omega_le_native_ratio F
      native_denominator_gap native_stageC_feasible
      native_stageA_positive native_stageB_positive
      native_stageC_balanced_positive native_volume_positive
    exact lt_of_le_of_lt hbound native_sharp_rate_bound
  · norm_num

end MatrixMultiplication.AllFieldMain

end

end MatrixAllFields

end OAI
end

theorem solution.{u} : type_of% @OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant_oai.{u} := @OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant_oai.{u}
