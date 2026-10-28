-- Prove2me | solution 2 for OAI.BinPackingGap.main_results
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T15:38:45.465778+00:00
-- url     : https://prove2.me/submissions/bbeb9aa6-dc10-4869-aeac-7f16932adb2d

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_BinPackingGap
import Definitions.Def_OAIQ082C029
import Theorems.Thm_OAI_BinPackingGap_InventoryData_edge_long_matches_capacity_oaiq082
import Theorems.Thm_OAI_BinPackingGap_InventoryData_long_matches_at_nonexcluded_oaiq082
import Theorems.Thm_OAI_BinPackingGap_extractedCover_card_le_oaiq082
import Theorems.Thm_OAI_BinPackingGap_pEqualsNP_of_absoluteAdditiveAlgorithm_oaiq082
import Theorems.Thm_OAI_BinPackingGap_packingGapNPHard_oaiq082

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_FractionWidth
attribute [-instance] _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.Packing.instFintypeTableBin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

open scoped BigOperators

namespace Packing

variable {I : Instance} {b : ℕ}

theorem chosen_injective (p : Packing I b) {J : Type*}
    (bin : J → Fin b) (hbin : Function.Injective bin)
    (chosen : J → I.Item) (hchosen : ∀ j, chosen j ∈ p.binItems (bin j)) :
    Function.Injective chosen := by
  intro j k hjk
  apply hbin
  have hj := (p.mem_binItems (bin j) (chosen j)).mp (hchosen j)
  have hk := (p.mem_binItems (bin k) (chosen k)).mp (hchosen k)
  rw [hjk] at hj
  exact hj.symm.trans hk

end Packing

theorem not_hasPacking_iff_lt_opt (I : Instance) (b : ℕ) :
    ¬ HasPacking I b ↔ b < opt I := by
  rw [hasPacking_iff_opt_le, Nat.not_le]

namespace IndividualConfiguration

variable {I : Instance}

theorem card_le_five (hlarge : ∀ i, (1 / 6 : ℚ) < I.size i)
    (H : IndividualConfiguration I) : H.val.card ≤ 5 := by
  by_contra h
  have hcard : 6 ≤ H.val.card := by omega
  have hne : H.val.Nonempty := Finset.card_pos.mp (by omega)
  have hstrict := Finset.sum_lt_sum_of_nonempty hne (fun i _ => hlarge i)
  have hsum : (H.val.card : ℚ) * (1 / 6) < ∑ i ∈ H.val, I.size i := by
    simpa using hstrict
  have hc : (6 : ℚ) ≤ H.val.card := by exact_mod_cast hcard
  have hcap := H.property
  linarith

end IndividualConfiguration

end BinPackingGap

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Configurations_ConfigurationLP
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators
open Set

namespace BinPackingGap.FractionalCover

variable {I C : Type*} [Fintype C]

theorem objective_nonneg {w : C → ℝ} (hw : ∀ c, 0 ≤ w c) :
    0 ≤ objective w :=
  Finset.sum_nonneg fun c _ => hw c

theorem coordinate_le_objective {w : C → ℝ} (hw : ∀ c, 0 ≤ w c) (c : C) :
    w c ≤ objective w :=
  Finset.single_le_sum (fun j _ => hw j) (Finset.mem_univ c)

theorem objectiveSet_nonempty {a : C → I → ℝ} {d : I → ℝ}
    (hfeas : ∃ w, Feasible a d w) : (objectiveSet a d).Nonempty := by
  obtain ⟨w, hw⟩ := hfeas
  exact ⟨objective w, w, hw, rfl⟩

theorem objectiveSet_bddBelow (a : C → I → ℝ) (d : I → ℝ) :
    BddBelow (objectiveSet a d) := by
  refine ⟨0, ?_⟩
  rintro v ⟨w, hw, rfl⟩
  exact objective_nonneg hw.1

theorem value_le_of_feasible {a : C → I → ℝ} {d : I → ℝ} {w : C → ℝ}
    (hw : Feasible a d w) : value a d ≤ objective w :=
  csInf_le (objectiveSet_bddBelow a d) ⟨w, hw, rfl⟩

theorem le_value_of_lower_bound {a : C → I → ℝ} {d : I → ℝ} {b : ℝ}
    (hfeas : ∃ w, Feasible a d w)
    (hb : ∀ w, Feasible a d w → b ≤ objective w) : b ≤ value a d := by
  apply le_csInf (objectiveSet_nonempty hfeas)
  rintro v ⟨w, hw, rfl⟩
  exact hb w hw

theorem continuous_objective : Continuous (objective (C := C)) := by
  unfold objective
  exact continuous_finsetSum _ fun c _ => continuous_apply c

theorem continuous_coverage (a : C → I → ℝ) (i : I) :
    Continuous (fun w : C → ℝ => ∑ c, a c i * w c) :=
  continuous_finsetSum _ fun c _ => continuous_const.mul (continuous_apply c)

theorem isClosed_feasible (a : C → I → ℝ) (d : I → ℝ) :
    IsClosed {w | Feasible a d w} := by
  have hn : IsClosed {w : C → ℝ | ∀ c, 0 ≤ w c} := by
    rw [Set.ofPred_forall]
    exact isClosed_iInter fun c => isClosed_le continuous_const (continuous_apply c)
  have hd : IsClosed {w : C → ℝ | ∀ i, d i ≤ ∑ c, a c i * w c} := by
    rw [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_coverage a i)
  exact hn.inter hd

theorem isCompact_sublevel (a : C → I → ℝ) (d : I → ℝ) (b : ℝ) :
    IsCompact {w | Feasible a d w ∧ objective w ≤ b} := by
  have hc : IsClosed {w | Feasible a d w ∧ objective w ≤ b} :=
    (isClosed_feasible a d).inter (isClosed_le continuous_objective continuous_const)
  apply (isCompact_Icc (a := (0 : C → ℝ)) (b := fun _ => b)).of_isClosed_subset hc
  intro w hw
  exact ⟨hw.1.1, fun c => (coordinate_le_objective hw.1.1 c).trans hw.2⟩

theorem exists_minimum {a : C → I → ℝ} {d : I → ℝ}
    (hfeas : ∃ w, Feasible a d w) :
    ∃ w, Feasible a d w ∧ ∀ v, Feasible a d v → objective w ≤ objective v := by
  obtain ⟨w₀, hw₀⟩ := hfeas
  obtain ⟨w, hw, hmin⟩ :=
    (isCompact_sublevel a d (objective w₀)).exists_isMinOn
      ⟨w₀, hw₀, le_rfl⟩ continuous_objective.continuousOn
  refine ⟨w, hw.1, fun v hv => ?_⟩
  rcases le_total (objective v) (objective w₀) with h | h
  · exact hmin ⟨hv, h⟩
  · exact hw.2.trans h

theorem exists_minimizer {a : C → I → ℝ} {d : I → ℝ}
    (hfeas : ∃ w, Feasible a d w) :
    ∃ w, Feasible a d w ∧ objective w = value a d := by
  obtain ⟨w, hw, hmin⟩ := exists_minimum hfeas
  exact ⟨w, hw, le_antisymm (le_value_of_lower_bound ⟨w, hw⟩ hmin)
    (value_le_of_feasible hw)⟩

theorem sum_demand_le_mul_objective [Fintype I] {a : C → I → ℝ} {d : I → ℝ}
    {w : C → ℝ} {K : ℝ} (hw : Feasible a d w)
    (hcol : ∀ c, (∑ i, a c i) ≤ K) : (∑ i, d i) ≤ K * objective w := by
  calc
    (∑ i, d i) ≤ ∑ i, ∑ c, a c i * w c :=
      Finset.sum_le_sum fun i _ => hw.2 i
    _ = ∑ c, (∑ i, a c i) * w c := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ ≤ ∑ c, K * w c :=
      Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_right (hcol c) (hw.1 c)
    _ = K * objective w := (Finset.mul_sum _ _ _).symm

variable {J : Type*} [Fintype J]

omit [Fintype C] in
theorem pushforward_nonneg (f : J → C) {mass : J → ℝ}
    (hmass : ∀ j, 0 ≤ mass j) : ∀ c, 0 ≤ pushforward f mass c := by
  classical
  intro c
  exact Finset.sum_nonneg fun j _ => by
    by_cases h : f j = c
    · simpa [h] using hmass j
    · simp [h]

theorem objective_pushforward (f : J → C) (mass : J → ℝ) :
    objective (pushforward f mass) = objective mass := by
  classical
  unfold objective pushforward
  rw [Finset.sum_comm]
  simp

theorem coverage_pushforward (a : C → I → ℝ) (f : J → C) (mass : J → ℝ) (i : I) :
    (∑ c, a c i * pushforward f mass c) = ∑ j, a (f j) i * mass j := by
  classical
  simp only [pushforward, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp

theorem feasible_pushforward {a : C → I → ℝ} {d : I → ℝ}
    (f : J → C) {mass : J → ℝ}
    (hmass : Feasible (fun j i => a (f j) i) d mass) :
    Feasible a d (pushforward f mass) := by
  refine ⟨pushforward_nonneg f hmass.1, fun i => ?_⟩
  rw [coverage_pushforward]
  exact hmass.2 i

end BinPackingGap.FractionalCover

end

namespace BinPackingGap

open scoped BigOperators

namespace TypeConfiguration

variable {I : Instance}

theorem card_le_five (hlarge : ∀ i, (1 / 6 : ℚ) < I.size i)
    (c : TypeConfiguration I) : (∑ s, c.val s) ≤ 5 := by
  classical
  by_contra h
  have hc : 6 ≤ ∑ s, c.val s := by omega
  have hcq : (6 : ℚ) ≤ ∑ s, (c.val s : ℚ) := by exact_mod_cast hc
  have hsize : ∀ s : NumericalSize I, (1 / 6 : ℚ) < s.val := by
    intro s
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp s.property
    simpa [hi] using hlarge i
  have hnz : ∃ s : NumericalSize I, 0 < c.val s := by
    by_contra hn
    push Not at hn
    have hz : ∀ s, c.val s = 0 := fun s => Nat.eq_zero_of_le_zero (hn s)
    simp [hz] at hc
  obtain ⟨s, hs⟩ := hnz
  have hstrict : (∑ t : NumericalSize I, (1 / 6 : ℚ) * (c.val t : ℚ)) <
      ∑ t : NumericalSize I, t.val * (c.val t : ℚ) := by
    apply Finset.sum_lt_sum
    · intro t _
      exact mul_le_mul_of_nonneg_right (le_of_lt (hsize t)) (Nat.cast_nonneg _)
    · refine ⟨s, Finset.mem_univ _, ?_⟩
      exact mul_lt_mul_of_pos_right (hsize s) (by exact_mod_cast hs)
  rw [← Finset.mul_sum] at hstrict
  have hcap := c.property
  linarith

end TypeConfiguration

theorem sum_type_multiplicity (I : Instance) :
    ∑ s : NumericalSize I, s.multiplicity = I.n := by
  classical
  simp only [NumericalSize.multiplicity, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  calc
    (∑ i : I.Item, ∑ s : NumericalSize I, if I.size i = s.val then 1 else 0) =
        ∑ _i : I.Item, 1 := by
      apply Finset.sum_congr rfl
      intro i _
      have heq : ∀ s : NumericalSize I, I.size i = s.val ↔ NumericalSize.ofItem i = s := by
        intro s
        constructor
        · intro h
          exact Subtype.ext h
        · intro h
          exact congrArg Subtype.val h
      simp [heq]
    _ = I.n := by simp [Instance.Item]

theorem individualMatrix_sum (I : Instance) (H : IndividualConfiguration I) :
    ∑ i, individualMatrix I H i = (H.val.card : ℝ) := by
  classical
  simp [individualMatrix]

theorem typeMatrix_sum (I : Instance) (c : TypeConfiguration I) :
    ∑ s, typeMatrix I c s = ((∑ s, c.val s : ℕ) : ℝ) := by
  simp [typeMatrix]

theorem singletonWeights_feasible (I : Instance) : IndividualFeasible I (singletonWeights I) := by
  classical
  apply FractionalCover.feasible_pushforward
  constructor
  · intro i
    norm_num
  · intro i
    simp [individualMatrix, IndividualConfiguration.singleton]

theorem individualLP_attained (I : Instance) :
    ∃ w, IndividualFeasible I w ∧ FractionalCover.objective w = individualLP I :=
  FractionalCover.exists_minimizer ⟨singletonWeights I, singletonWeights_feasible I⟩

theorem typeMatrix_ofIndividual (I : Instance) (H : IndividualConfiguration I)
    (s : NumericalSize I) :
    typeMatrix I (TypeConfiguration.ofIndividual H) s =
      ∑ i : I.Item, if I.size i = s.val then individualMatrix I H i else 0 := by
  classical
  change ((H.val.filter fun i => I.size i = s.val).card : ℝ) = _
  calc
    _ = ∑ i ∈ H.val, if I.size i = s.val then (1 : ℝ) else 0 := by
      simp
    _ = ∑ i ∈ H.val, if I.size i = s.val then individualMatrix I H i else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [individualMatrix, hi]
    _ = ∑ i : I.Item, if I.size i = s.val then individualMatrix I H i else 0 := by
      apply Finset.sum_subset (Finset.subset_univ H.val)
      intro i _ hi
      simp [individualMatrix, hi]

theorem projectWeights_objective (I : Instance) (w : IndividualConfiguration I → ℝ) :
    FractionalCover.objective (projectWeights I w) = FractionalCover.objective w :=
  FractionalCover.objective_pushforward _ _

theorem projectWeights_feasible (I : Instance) {w : IndividualConfiguration I → ℝ}
    (hw : IndividualFeasible I w) : TypeFeasible I (projectWeights I w) := by
  classical
  apply FractionalCover.feasible_pushforward
  refine ⟨hw.1, fun s => ?_⟩
  have hcoverage := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    show (if I.size i = s.val then (1 : ℝ) else 0) ≤
      if I.size i = s.val then ∑ H, individualMatrix I H i * w H else 0 by
        split_ifs
        · exact hw.2 i
        · rfl)
  have hleft : (∑ i : I.Item, if I.size i = s.val then (1 : ℝ) else 0) =
      s.multiplicity := by
    simp [NumericalSize.multiplicity]
  have hright :
      (∑ i : I.Item, if I.size i = s.val then ∑ H, individualMatrix I H i * w H else 0) =
      ∑ H, typeMatrix I (TypeConfiguration.ofIndividual H) s * w H := by
    simp_rw [typeMatrix_ofIndividual, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with h
    · simp
    · simp
  simpa only [hleft, hright] using hcoverage

theorem typeLP_attained (I : Instance) :
    ∃ w, TypeFeasible I w ∧ FractionalCover.objective w = typeLP I :=
  FractionalCover.exists_minimizer
    ⟨projectWeights I (singletonWeights I), projectWeights_feasible I (singletonWeights_feasible I)⟩

theorem typeLP_le_individualLP (I : Instance) : typeLP I ≤ individualLP I := by
  obtain ⟨w, hw, hobj⟩ := individualLP_attained I
  calc
    typeLP I ≤ FractionalCover.objective (projectWeights I w) :=
      FractionalCover.value_le_of_feasible (projectWeights_feasible I hw)
    _ = individualLP I := (projectWeights_objective I w).trans hobj

theorem n_le_five_mul_individual_objective (I : Instance)
    (hlarge : ∀ i, (1 / 6 : ℚ) < I.size i)
    {w : IndividualConfiguration I → ℝ} (hw : IndividualFeasible I w) :
    (I.n : ℝ) ≤ 5 * FractionalCover.objective w := by
  have hcol : ∀ H : IndividualConfiguration I, (∑ i, individualMatrix I H i) ≤ 5 := by
    intro H
    rw [individualMatrix_sum]
    exact_mod_cast H.card_le_five hlarge
  simpa [Instance.Item] using FractionalCover.sum_demand_le_mul_objective hw hcol

theorem n_le_five_mul_type_objective (I : Instance)
    (hlarge : ∀ i, (1 / 6 : ℚ) < I.size i)
    {w : TypeConfiguration I → ℝ} (hw : TypeFeasible I w) :
    (I.n : ℝ) ≤ 5 * FractionalCover.objective w := by
  have hcol : ∀ c : TypeConfiguration I, (∑ s, typeMatrix I c s) ≤ 5 := by
    intro c
    rw [typeMatrix_sum]
    exact_mod_cast c.card_le_five hlarge
  have h := FractionalCover.sum_demand_le_mul_objective hw hcol
  have hdem : (∑ s : NumericalSize I, (s.multiplicity : ℝ)) = I.n := by
    rw [← Nat.cast_sum, sum_type_multiplicity]
  simpa only [hdem] using h

theorem n_le_five_mul_individualLP (I : Instance)
    (hlarge : ∀ i, (1 / 6 : ℚ) < I.size i) : (I.n : ℝ) ≤ 5 * individualLP I := by
  obtain ⟨w, hw, hobj⟩ := individualLP_attained I
  rw [← hobj]
  exact n_le_five_mul_individual_objective I hlarge hw

theorem n_le_five_mul_typeLP (I : Instance)
    (hlarge : ∀ i, (1 / 6 : ℚ) < I.size i) : (I.n : ℝ) ≤ 5 * typeLP I := by
  obtain ⟨w, hw, hobj⟩ := typeLP_attained I
  rw [← hobj]
  exact n_le_five_mul_type_objective I hlarge hw

theorem bothLP_eq_of_physical_witness (I : Instance) (B : ℕ)
    (hcount : I.n = 5 * B) (hlarge : ∀ i, (1 / 6 : ℚ) < I.size i)
    (w : IndividualConfiguration I → ℝ) (hw : IndividualFeasible I w)
    (hobj : FractionalCover.objective w = (B : ℝ)) :
    individualLP I = (B : ℝ) ∧ typeLP I = (B : ℝ) := by
  have hcountR : (I.n : ℝ) = 5 * (B : ℝ) := by exact_mod_cast hcount
  have hilow := n_le_five_mul_individualLP I hlarge
  have htlow := n_le_five_mul_typeLP I hlarge
  have hiup : individualLP I ≤ (B : ℝ) := by
    rw [← hobj]
    exact FractionalCover.value_le_of_feasible hw
  have htup : typeLP I ≤ (B : ℝ) := (typeLP_le_individualLP I).trans hiup
  constructor <;> linarith

end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PackingScalar
attribute [-instance] _root_.OAI.BinPackingGap.InventoryData.roleCopiesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap

section

open scoped BigOperators

namespace Packing

variable {I : Instance} {b : ℕ}

theorem itemAtRole_mem (p : Packing I b) (subclass : I.Item → Subclass)
    (t : p.TableBin subclass) (r : Role) :
    p.itemAtRole subclass t r ∈ p.binItems t.val :=
  (p.tableEquiv subclass t r).property

theorem itemAtRole_injective (p : Packing I b) (subclass : I.Item → Subclass)
    (r : Role) : Function.Injective (fun t => p.itemAtRole subclass t r) :=
  p.chosen_injective Subtype.val Subtype.val_injective
    (fun t => p.itemAtRole subclass t r) (fun t => p.itemAtRole_mem subclass t r)

end Packing

end

open scoped BigOperators

end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Trees_CompletionGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.Geometry

theorem lambda_one_le_hundredth (m R D : ℕ) : lambda m R D 1 ≤ gap m R / 100 := by
  unfold lambda
  rw [pow_one]
  apply div_le_div_of_nonneg_left (gap_nonneg _ _) (by norm_num)
  have hD : (0 : ℚ) ≤ D := Nat.cast_nonneg D
  linarith

theorem lambda_one_add_two_delta_lt_gap (m R D : ℕ) {L : ℕ} (hL : 1 ≤ L) :
    lambda m R D 1 + 2 * delta m R D L < gap m R := by
  have hd := delta_le_tenth m R D hL
  have hl := lambda_one_le_hundredth m R D
  have hg := gap_pos m R
  linarith

end BinPackingGap.Geometry

namespace BinPackingGap

theorem completion_zero_global_length_le (b : ℚ) (short : Bool) (localLen delta : ℚ)
    (hdelta : 0 ≤ delta) :
    b - completion b short 0 localLen delta ≤ localLen + delta := by
  cases short <;> simp only [completion_false, completion_true] <;> linarith

end BinPackingGap

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_CurrentMatches
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.InventoryData.roleCopiesFintype _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap
namespace Coverage

variable {I : Instance} {b n : ℕ}

@[simp] theorem roleItems_card (p : Packing I b) (cls : I.Item → Subclass)
    (s : Finset (p.TableBin cls)) (role : Role) : (roleItems p cls s role).card = s.card :=
  Finset.card_image_of_injective s (p.itemAtRole_injective cls role)

theorem card_le_role_resources (p : Packing I b) (cls : I.Item → Subclass)
    (s : Finset (p.TableBin cls)) (role : Role) (resources : Finset I.Item)
    (hmap : ∀ t ∈ s, p.itemAtRole cls t role ∈ resources) : s.card ≤ resources.card :=
  Finset.card_le_card_of_injOn (fun t => p.itemAtRole cls t role) hmap
    (p.itemAtRole_injective cls role).injOn

end Coverage
end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_K4Graph
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeBEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeBEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype _root_.OAI.BinPackingGap.instFintypeGlobalSpecies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap

theorem depthDemand_one_le (c : ℕ) (ρ : ℝ) : 1 ≤ depthDemand c ρ :=
  Nat.succ_le_of_lt (depthDemand_pos c ρ)

theorem three_quarter_lower {d K x L : ℝ} (h72 : 72 * K ≤ d)
    (hx : x ≤ d / 8) (hL : d - x - 9 * K ≤ L) : 3 * d / 4 ≤ L := by
  linarith

theorem repetitions_cast (P n K : ℕ) :
    (repetitions P n K : ℝ) = 100 * ((P : ℝ) + (n : ℝ) * K + 1) := by
  simp [repetitions]

theorem edge_demand_exceeds_capacity_real {P n K d : ℝ}
    (hP : 0 ≤ P) (hn : 0 ≤ n) (hK : 0 ≤ K) (hd : 1 ≤ d) :
    d * (100 * (P + n * K + 1)) + 3 * n * K <
      2 * (100 * (P + n * K + 1) - P) * (3 * d / 4) := by
  have hd0 : 0 ≤ d := le_trans zero_le_one hd
  have hdP : 0 ≤ d * P := mul_nonneg hd0 hP
  have hnK : 0 ≤ n * K := mul_nonneg hn hK
  have hrest : 0 ≤ (50 * d - 3) * (n * K) :=
    mul_nonneg (by linarith) hnK
  nlinarith

theorem edge_demand_exceeds_capacity (P n K d : ℕ) (hd : 1 ≤ d) :
    (d : ℝ) * (repetitions P n K : ℝ) + 3 * (n : ℝ) * K <
      2 * ((repetitions P n K : ℝ) - P) * (3 * (d : ℝ) / 4) := by
  rw [repetitions_cast]
  exact edge_demand_exceeds_capacity_real (Nat.cast_nonneg P) (Nat.cast_nonneg n)
    (Nat.cast_nonneg K) (by exact_mod_cast hd)

open scoped BigOperators

end BinPackingGap

section
open scoped BigOperators

namespace BinPackingGap

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem longMatch_sum_lower {R P : ℕ} (S : Finset (Fin R)) (L : Fin R → ℕ)
    {a : ℝ} (ha : 0 ≤ a) (hS : (R : ℝ) - P ≤ (S.card : ℝ))
    (hL : ∀ j ∈ S, a ≤ (L j : ℝ)) :
    ((R : ℝ) - P) * a ≤ ∑ j, (L j : ℝ) := by
  calc
    _ ≤ (S.card : ℝ) * a := mul_le_mul_of_nonneg_right hS ha
    _ = ∑ _j ∈ S, a := by simp
    _ ≤ ∑ j ∈ S, (L j : ℝ) := Finset.sum_le_sum hL
    _ ≤ ∑ j, (L j : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)

theorem thresholdCover_isCover (G : GraphInput) {d K P R : ℕ}
    (xplus : G.Vertex → ℕ)
    (Sleft Sright : G.Edge → Finset (Fin R))
    (Lleft Lright : G.Edge → Fin R → ℕ)
    (hd : 1 ≤ d) (h72 : 72 * K ≤ d) (hR : R = repetitions P G.n K)
    (hSleft : ∀ e, (R : ℝ) - P ≤ ((Sleft e).card : ℝ))
    (hSright : ∀ e, (R : ℝ) - P ≤ ((Sright e).card : ℝ))
    (hLleft : ∀ e j, j ∈ Sleft e → d ≤ Lleft e j + xplus (G.left e) + 9 * K)
    (hLright : ∀ e j, j ∈ Sright e → d ≤ Lright e j + xplus (G.right e) + 9 * K)
    (hcapacity : ∀ e, (∑ j, Lleft e j) + (∑ j, Lright e j) ≤
      d * R + 3 * G.n * K) :
    G.IsCover (thresholdCover d xplus) := by
  classical
  let C := thresholdCover d xplus
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hd)
  have h72' : 72 * (K : ℝ) ≤ d := by exact_mod_cast h72
  have hstrict : (d : ℝ) * R + 3 * (G.n : ℝ) * K <
      2 * ((R : ℝ) - P) * (3 * (d : ℝ) / 4) := by
    rw [hR]
    exact edge_demand_exceeds_capacity P G.n K d hd
  have hindex : ∀ e : G.Edge, G.left e ∈ C ∨ G.right e ∈ C := by
    intro e
    by_cases hv : G.left e ∈ C
    · exact Or.inl hv
    right
    by_contra hw
    have hxleft : (xplus (G.left e) : ℝ) ≤ (d : ℝ) / 8 := by
      apply le_of_not_gt
      simpa [C, thresholdCover] using hv
    have hxright : (xplus (G.right e) : ℝ) ≤ (d : ℝ) / 8 := by
      apply le_of_not_gt
      simpa [C, thresholdCover] using hw
    have hleft : ((R : ℝ) - P) * (3 * (d : ℝ) / 4) ≤
        ∑ j, (Lleft e j : ℝ) := by
      apply longMatch_sum_lower _ _ (by positivity) (hSleft e)
      intro j hj
      have hmatch : (d : ℝ) ≤ (Lleft e j : ℝ) + xplus (G.left e) + 9 * K := by
        exact_mod_cast hLleft e j hj
      exact three_quarter_lower h72' hxleft (by linarith)
    have hright : ((R : ℝ) - P) * (3 * (d : ℝ) / 4) ≤
        ∑ j, (Lright e j : ℝ) := by
      apply longMatch_sum_lower _ _ (by positivity) (hSright e)
      intro j hj
      have hmatch : (d : ℝ) ≤ (Lright e j : ℝ) + xplus (G.right e) + 9 * K := by
        exact_mod_cast hLright e j hj
      exact three_quarter_lower h72' hxright (by linarith)
    have hcap : (∑ j, (Lleft e j : ℝ)) + (∑ j, (Lright e j : ℝ)) ≤
        (d : ℝ) * R + 3 * (G.n : ℝ) * K := by exact_mod_cast hcapacity e
    linarith
  intro e he
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp he
  have h := hindex ⟨i, hi⟩
  change (G.edges[i]).1 ∈ C ∨ (G.edges[i]).2 ∈ C at h
  rw [heq] at h
  exact h

end BinPackingGap

end

namespace BinPackingGap

theorem completeFourGraph_cover_card {C : Finset completeFourGraph.Vertex}
    (hC : completeFourGraph.IsCover C) : 3 ≤ C.card := by
  classical
  change Finset (Fin 4) at C
  change 3 ≤ C.card
  change ∀ e : Fin 4 × Fin 4,
    e ∈ [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)] →
      e.1 ∈ C ∨ e.2 ∈ C at hC
  have h01 : (0 : Fin 4) ∈ C ∨ (1 : Fin 4) ∈ C :=
    hC ((0 : Fin 4), (1 : Fin 4)) (by decide)
  have h02 : (0 : Fin 4) ∈ C ∨ (2 : Fin 4) ∈ C :=
    hC ((0 : Fin 4), (2 : Fin 4)) (by decide)
  have h03 : (0 : Fin 4) ∈ C ∨ (3 : Fin 4) ∈ C :=
    hC ((0 : Fin 4), (3 : Fin 4)) (by decide)
  have h12 : (1 : Fin 4) ∈ C ∨ (2 : Fin 4) ∈ C :=
    hC ((1 : Fin 4), (2 : Fin 4)) (by decide)
  have h13 : (1 : Fin 4) ∈ C ∨ (3 : Fin 4) ∈ C :=
    hC ((1 : Fin 4), (3 : Fin 4)) (by decide)
  have h23 : (2 : Fin 4) ∈ C ∨ (3 : Fin 4) ∈ C :=
    hC ((2 : Fin 4), (3 : Fin 4)) (by decide)
  have hsmall : (Finset.univ \ C).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    have hxC : x ∉ C := (Finset.mem_sdiff.mp hx).2
    have hyC : y ∉ C := (Finset.mem_sdiff.mp hy).2
    fin_cases x <;> fin_cases y <;> simp_all
  have htotal : (Finset.univ \ C).card + C.card = 4 := by
    simpa only [Finset.card_univ, Fintype.card_fin, completeFourGraph] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ C)
  omega

theorem completeFourGraph_no_small_cover :
    ¬ ∃ C : Finset completeFourGraph.Vertex,
      completeFourGraph.IsCover C ∧
        (C.card : ℝ) ≤ 2 + (1 / 8 : ℝ) * completeFourGraph.n := by
  rintro ⟨C, hC, hcard⟩
  have hthree : (3 : ℝ) ≤ C.card := by exact_mod_cast completeFourGraph_cover_card hC
  norm_num [completeFourGraph] at hcard
  linarith

end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_InventoryScores
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.decidableAncestor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

open scoped BigOperators

namespace InventoryData

variable (D : InventoryData)

theorem card_localBin (v : D.Vertex) :
    Fintype.card (D.LocalBin v) = D.t + 2 * D.J v :=
  D.card_anchorAt v

end InventoryData

end BinPackingGap

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PackingSelections
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open scoped BigOperators

namespace BinPackingGap
namespace PackingCounts

variable {D : InventoryData} {I : Instance} {b : ℕ}

theorem positiveLocalCopy_injective (e : D.Item ≃ I.Item) (v : D.Vertex) :
    Function.Injective (fun i : D.PositiveLocal =>
      e ⟨.«local», ⟨v, Sum.inl (Sum.inl i)⟩⟩) := by
  intro i j hij
  have h := e.injective hij
  have hl := @sigma_mk_injective Role D.RoleCopies .«local» _ _ h
  have hv := @sigma_mk_injective D.Vertex D.LocalAt v _ _ hl
  exact Sum.inl.inj (Sum.inl.inj hv)

@[simp] theorem positiveLocalResources_card (e : D.Item ≃ I.Item) (v : D.Vertex) :
    (positiveLocalResources e v).card = D.P := by
  classical
  rw [positiveLocalResources,
    Finset.card_image_of_injective _ (positiveLocalCopy_injective e v),
    Finset.card_univ, D.card_positiveLocal]

theorem card_le_positiveLocal_stock (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (S : Finset (p.TableBin (subclass e)))
    (hres : ∀ t ∈ S,
      p.itemAtRole (subclass e) t .«local» ∈ positiveLocalResources e v) :
    S.card ≤ D.P := by
  rw [← positiveLocalResources_card e v]
  exact Coverage.card_le_role_resources p (subclass e) S .«local» _ hres

end PackingCounts
end BinPackingGap

end

namespace BinPackingGap
namespace PackingCounts

variable {D : InventoryData} {I : Instance} {b : ℕ}

private theorem elementAtRole_mk (i : D.Item) (r : Role) (h : i.1 = r) :
    (⟨r, elementAtRole i r h⟩ : D.Item) = i := by
  rcases i with ⟨s, i⟩
  dsimp at h
  cases h
  rfl

@[simp] theorem roleCopy_item (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (r : Role) :
    e ⟨r, roleCopy p e t r⟩ = p.itemAtRole (subclass e) t r := by
  rw [roleCopy, elementAtRole_mk, e.apply_symm_apply]

@[simp] theorem selected_row_label (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) :
    label e (p.itemAtRole (subclass e) t .x) = some (rowCopy p e t).1 := by
  change D.itemLabel (e.symm (p.itemAtRole (subclass e) t .x)) =
    some (rowCopy p e t).1
  rw [← roleCopy_item p e t .x, e.symm_apply_apply]
  rfl

@[simp] theorem selected_anchor_label (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) :
    label e (p.itemAtRole (subclass e) t .anchor) = some (anchorCopy p e t).1 := by
  change D.itemLabel (e.symm (p.itemAtRole (subclass e) t .anchor)) =
    some (anchorCopy p e t).1
  rw [← roleCopy_item p e t .anchor, e.symm_apply_apply]
  rfl

@[simp] theorem selected_local_label (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) :
    label e (p.itemAtRole (subclass e) t .«local») = some (localCopy p e t).1 := by
  change D.itemLabel (e.symm (p.itemAtRole (subclass e) t .«local»)) =
    some (localCopy p e t).1
  rw [← roleCopy_item p e t .«local», e.symm_apply_apply]
  rfl

@[simp] theorem mem_zeroPositiveTuples (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e)) :
    t ∈ zeroPositiveTuples p e v ↔
      t ∈ Coverage.mainTuplesAt p (subclass e) (label e) v ∧
        D.globalUnit (globalCopy p e t) = false ∧
          p.itemAtRole (subclass e) t .«local» ∈ positiveLocalResources e v := by
  classical
  simp [zeroPositiveTuples, and_assoc]

theorem zeroPositiveTuples_card_le (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) : (zeroPositiveTuples p e v).card ≤ D.P := by
  apply card_le_positiveLocal_stock p e v
  intro t ht
  exact ((mem_zeroPositiveTuples p e v t).mp ht).2.2

end PackingCounts
end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Trees_TestGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.Geometry

variable {m R D L : ℕ}

theorem closed_interval_gap_le_length {a b l₁ u₁ l₂ u₂ : ℚ}
    (h₁ : (Set.Icc a b ∩ Set.Icc l₁ u₁).Nonempty)
    (h₂ : (Set.Icc a b ∩ Set.Icc l₂ u₂).Nonempty) :
    l₂ - u₁ ≤ b - a := by
  rcases h₁ with ⟨x, hx⟩
  rcases h₂ with ⟨y, hy⟩
  have hax := hx.1.1
  have hxu := hx.2.2
  have hly := hy.2.1
  have hyb := hy.1.2
  linarith

theorem closedJobCell_unique_of_short_interval (hL : 1 ≤ L)
    {a b : ℚ} {r s : Position m R}
    (hlen : b - a ≤ lambda m R D 1 + delta m R D L)
    (hr : (Set.Icc a b ∩ closedJobCell m R D L r).Nonempty)
    (hs : (Set.Icc a b ∩ closedJobCell m R D L s).Nonempty) : r = s := by
  have hwidth := lambda_one_add_two_delta_lt_gap m R D hL
  rcases posLT_trichotomy r s with hrs | hrs | hsr
  · have hgap := job_gap_of_posLT D L hrs
    have hspan := closed_interval_gap_le_length hr hs
    linarith
  · exact hrs
  · have hgap := job_gap_of_posLT D L hsr
    have hspan := closed_interval_gap_le_length hs hr
    linarith

end BinPackingGap.Geometry

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PackingCoordinates
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap
namespace PackingCounts

variable {D : InventoryData} {I : Instance} {b : ℕ}

@[simp] theorem mem_tupleCovering (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (a : ℚ) (t : p.TableBin (subclass e)) :
    t ∈ tupleCovering p e v a ↔
      t ∈ Coverage.mainTuplesAt p (subclass e) (label e) v ∧
        tupleFinish p e t ≤ a ∧ a < tupleBaseline p e t := by
  classical
  simp [tupleCovering, and_assoc]

theorem tupleGlobalLength_eq_of_unit_false (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (hu : D.globalUnit (globalCopy p e t) = false) :
    tupleGlobalLength p e t = 0 := by
  have h : D.globalLength (globalCopy p e t) =
      if D.globalUnit (globalCopy p e t) then 1 else 0 := by
    rcases globalCopy p e t with ⟨s, i⟩
    cases s <;> rfl
  simpa only [tupleGlobalLength, hu, Bool.false_eq_true, ↓reduceIte] using h

private theorem localLength_le_first {v : D.Vertex} (l : D.LocalAt v) :
    D.localLength l ≤ Geometry.lambda D.graph.edges.length D.R D.geometryBound 1 := by
  rcases l with ((⟨ell, i⟩ | z) | g)
  · exact Geometry.lambda_antitone _ _ _ (Finset.mem_Icc.mp ell.property).1
  · exact Geometry.lambda_nonneg _ _ _ _
  · exact Geometry.lambda_nonneg _ _ _ _

theorem tupleLocalLength_le_first (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) :
    tupleLocalLength p e t ≤ Geometry.lambda D.graph.edges.length D.R D.geometryBound 1 :=
  localLength_le_first _

theorem selected_interval_length_first (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e)) (ht : t ∈ zeroPositiveTuples p e v) :
    tupleBaseline p e t - tupleFinish p e t ≤
      Geometry.lambda D.graph.edges.length D.R D.geometryBound 1 +
        Geometry.delta D.graph.edges.length D.R D.geometryBound D.L := by
  have hu := ((mem_zeroPositiveTuples p e v t).mp ht).2.1
  unfold tupleFinish
  rw [tupleGlobalLength_eq_of_unit_false p e t hu]
  apply le_trans (completion_zero_global_length_le
    (tupleBaseline p e t) (tupleShort p e t) (tupleLocalLength p e t)
    (Geometry.delta D.graph.edges.length D.R D.geometryBound D.L)
    (Geometry.delta_nonneg D.graph.edges.length D.R D.geometryBound D.L))
  exact add_le_add (tupleLocalLength_le_first p e t) le_rfl

end PackingCounts
end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_InventoryPrefixConservation
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap

section

open scoped BigOperators

namespace InventoryData

variable (D : InventoryData)

theorem packingInstance_size_mem_interval (i : D.packingInstance.Item) :
    1 / 6 < D.packingInstance.size i ∧ D.packingInstance.size i < 1 :=
  D.itemSize_mem_interval _

theorem packingInstance_n (hk : D.k ≤ D.graph.n) :
    D.packingInstance.n = 5 * D.B := D.card_item hk

end InventoryData

end

end BinPackingGap

namespace BinPackingGap.InventoryData

open scoped BigOperators

variable (D : InventoryData)

theorem itemEquiv_mem_physicalGlobalPool_iff (a : D.Item) (s : GlobalSpecies D.graph) :
    D.itemEquiv a ∈ D.physicalGlobalPool s ↔
      ∃ j : Fin (D.globalStock s), a = ⟨.«global», ⟨s, j⟩⟩ := by
  rw [mem_physicalGlobalPool]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, (D.itemEquiv.injective hj).symm⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j, rfl⟩

theorem itemEquiv_mem_physicalFlagPool_iff (a : D.Item) (s : FlagSpecies) :
    D.itemEquiv a ∈ D.physicalFlagPool s ↔
      ∃ j : Fin (D.flagStock s), a = ⟨.flag, ⟨s, j⟩⟩ := by
  rw [mem_physicalFlagPool]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, (D.itemEquiv.injective hj).symm⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j, rfl⟩

@[simp] theorem globalItem_mem_physicalGlobalPool (s t : GlobalSpecies D.graph)
    (j : Fin (D.globalStock s)) :
    D.itemEquiv ⟨.«global», ⟨s, j⟩⟩ ∈ D.physicalGlobalPool t ↔ s = t := by
  rw [itemEquiv_mem_physicalGlobalPool_iff]
  constructor
  · rintro ⟨q, hq⟩
    have hcopy : (⟨s, j⟩ : D.GlobalCopy) = ⟨t, q⟩ :=
      sigma_mk_injective (β := D.RoleCopies) (i := Role.«global») hq
    exact congrArg Sigma.fst hcopy
  · intro h
    subst t
    exact ⟨j, rfl⟩

@[simp] theorem flagItem_mem_physicalFlagPool (s t : FlagSpecies)
    (j : Fin (D.flagStock s)) :
    D.itemEquiv ⟨.flag, ⟨s, j⟩⟩ ∈ D.physicalFlagPool t ↔ s = t := by
  rw [itemEquiv_mem_physicalFlagPool_iff]
  constructor
  · rintro ⟨q, hq⟩
    have hcopy : (⟨s, j⟩ : D.FlagCopy) = ⟨t, q⟩ :=
      sigma_mk_injective (β := D.RoleCopies) (i := Role.flag) hq
    exact congrArg Sigma.fst hcopy
  · intro h
    subst t
    exact ⟨j, rfl⟩

private theorem not_mem_physicalGlobalPool_of_role_ne (r : Role) (c : D.RoleCopies r)
    (s : GlobalSpecies D.graph) (hr : r ≠ .«global») :
    D.itemEquiv ⟨r, c⟩ ∉ D.physicalGlobalPool s := by
  intro hi
  have h := D.role_eq_global_of_mem_physicalGlobalPool s hi
  exact hr (by simpa only [Equiv.symm_apply_apply] using h)

private theorem not_mem_physicalFlagPool_of_role_ne (r : Role) (c : D.RoleCopies r)
    (s : FlagSpecies) (hr : r ≠ .flag) :
    D.itemEquiv ⟨r, c⟩ ∉ D.physicalFlagPool s := by
  intro hi
  have h := D.role_eq_flag_of_mem_physicalFlagPool s hi
  exact hr (by simpa only [Equiv.symm_apply_apply] using h)

theorem physicalInventory_indicator_partition (i : D.packingInstance.Item) :
    (if i ∈ D.labeledItems then (1 : ℝ) else 0) +
      (∑ s, if i ∈ D.physicalGlobalPool s then (1 : ℝ) else 0) +
      (∑ s, if i ∈ D.physicalFlagPool s then (1 : ℝ) else 0) = 1 := by
  classical
  obtain ⟨⟨r, c⟩, rfl⟩ := D.itemEquiv.surjective i
  cases r with
  | x =>
    simp [not_mem_physicalGlobalPool_of_role_ne, not_mem_physicalFlagPool_of_role_ne]
  | anchor =>
    simp [not_mem_physicalGlobalPool_of_role_ne, not_mem_physicalFlagPool_of_role_ne]
  | «global» =>
    rcases c with ⟨s, j⟩
    have hflag : ∀ t : FlagSpecies,
        D.itemEquiv ⟨.«global», ⟨s, j⟩⟩ ∉ D.physicalFlagPool t := fun t =>
      not_mem_physicalFlagPool_of_role_ne D .«global» ⟨s, j⟩ t (by decide)
    simp [hflag]
  | «local» =>
    simp [not_mem_physicalGlobalPool_of_role_ne, not_mem_physicalFlagPool_of_role_ne]
  | flag =>
    rcases c with ⟨s, j⟩
    have hglobal : ∀ t : GlobalSpecies D.graph,
        D.itemEquiv ⟨.flag, ⟨s, j⟩⟩ ∉ D.physicalGlobalPool t := fun t =>
      not_mem_physicalGlobalPool_of_role_ne D .flag ⟨s, j⟩ t (by decide)
    simp [hglobal]

end BinPackingGap.InventoryData

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_InventoryCoverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinPackingGap
namespace InventoryCoverage

variable {D : InventoryData} {I : Instance} {b : ℕ}

@[simp] theorem rowBaseline_selected (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (PackingCounts.subclass e)) :
    rowBaseline e (p.itemAtRole (PackingCounts.subclass e) t .x) =
      D.rowBaseline (PackingCounts.rowCopy p e t).2 := by
  rw [← PackingCounts.roleCopy_item p e t .x]
  change itemRowBaseline D (e.symm (e ⟨.x, PackingCounts.rowCopy p e t⟩)) = _
  rw [e.symm_apply_apply]
  rfl

@[simp] theorem rowShort_selected (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (PackingCounts.subclass e)) :
    rowShort e (p.itemAtRole (PackingCounts.subclass e) t .x) =
      D.rowShort (PackingCounts.rowCopy p e t).2 := by
  rw [← PackingCounts.roleCopy_item p e t .x]
  change itemRowShort D (e.symm (e ⟨.x, PackingCounts.rowCopy p e t⟩)) = _
  rw [e.symm_apply_apply]
  rfl

end InventoryCoverage
end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PackingFeasibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap
namespace PackingCounts

open scoped BigOperators

variable {D : InventoryData} {I : Instance} {b : ℕ}

@[simp] theorem selected_itemCoordinate (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (r : Role) :
    D.itemCoordinate (e.symm (p.itemAtRole (subclass e) t r)) =
      D.itemCoordinate ⟨r, roleCopy p e t r⟩ := by
  rw [← roleCopy_item p e t r]
  simp only [Equiv.symm_apply_apply]

end PackingCounts
end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_PackingExclusions
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap

theorem excludedPositions_card_le {T Pos : Type*} [Fintype Pos]
    (selected : Finset T) (I : T → Pos → Prop)
    (hunique : ∀ t ∈ selected, ∀ r s, I t r → I t s → r = s) :
    (excludedPositions selected I).card ≤ selected.card := by
  classical
  have witness (r : ↥(excludedPositions selected I)) : ∃ t ∈ selected, I t r :=
    (mem_excludedPositions selected I).mp r.property
  let f : ↥(excludedPositions selected I) → ↥selected := fun r =>
    ⟨(witness r).choose, (witness r).choose_spec.1⟩
  have hf (r : ↥(excludedPositions selected I)) : I (f r) r :=
    (witness r).choose_spec.2
  have hinj : Function.Injective f := by
    intro r s hrs
    have ht : (f r : T) = (f s : T) := congrArg (fun t : ↥selected => (t : T)) hrs
    apply Subtype.ext
    apply hunique (f r) (f r).property r s (hf r)
    rw [ht]
    exact hf s
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj

theorem excludedRepetitions_card_le {E : Type*} {R : ℕ}
    (bad : Finset (E × Fin R)) (e : E) :
    (excludedRepetitions bad e).card ≤ bad.card := by
  classical
  let f : ↥(excludedRepetitions bad e) → ↥bad := fun j =>
    ⟨(e, j), (mem_excludedRepetitions bad e).mp j.property⟩
  have hinj : Function.Injective f := by
    intro j k hjk
    apply Subtype.ext
    exact congrArg Prod.snd (congrArg (fun x : ↥bad => (x : E × Fin R)) hjk)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj

theorem excluded_nonexcluded_card {E : Type*} {R : ℕ}
    (bad : Finset (E × Fin R)) (e : E) :
    (excludedRepetitions bad e).card + (nonexcludedRepetitions bad e).card = R := by
  classical
  have hdis : Disjoint (excludedRepetitions bad e) (nonexcludedRepetitions bad e) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    exact ((mem_nonexcludedRepetitions bad e).mp hk)
      ((mem_excludedRepetitions bad e).mp hj)
  have hunion : excludedRepetitions bad e ∪ nonexcludedRepetitions bad e = Finset.univ := by
    ext j
    by_cases hj : (e, j) ∈ bad <;> simp [hj]
  calc
    _ = (excludedRepetitions bad e ∪ nonexcludedRepetitions bad e).card :=
      (Finset.card_union_of_disjoint hdis).symm
    _ = R := by rw [hunion]; simp

theorem nonexcludedRepetitions_add_card_bound {E : Type*} {R P : ℕ}
    (bad : Finset (E × Fin R)) (e : E) (hbad : bad.card ≤ P) :
    R ≤ P + (nonexcludedRepetitions bad e).card := by
  calc
    R = (excludedRepetitions bad e).card + (nonexcludedRepetitions bad e).card :=
      (excluded_nonexcluded_card bad e).symm
    _ ≤ P + (nonexcludedRepetitions bad e).card :=
      Nat.add_le_add_right ((excludedRepetitions_card_le bad e).trans hbad) _

theorem nonexcludedRepetitions_card_ge_real {E : Type*} {R P : ℕ}
    (bad : Finset (E × Fin R)) (e : E) (hbad : bad.card ≤ P) :
    (R : ℝ) - P ≤ ((nonexcludedRepetitions bad e).card : ℝ) := by
  have h : (R : ℝ) ≤ (P : ℝ) + ((nonexcludedRepetitions bad e).card : ℝ) := by
    exact_mod_cast nonexcludedRepetitions_add_card_bound bad e hbad
  apply sub_le_iff_le_add.mpr
  simpa only [add_comm] using h

namespace PackingCounts

variable {D : InventoryData} {I : Instance} {b : ℕ}

theorem selected_hits_job_unique (p : Packing I b) (e : D.Item ≃ I.Item)
    (hL : 1 ≤ D.L) (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ zeroPositiveTuples p e v) {r s : D.Position}
    (hr : tupleHitsJob p e t r) (hs : tupleHitsJob p e t s) : r = s :=
  Geometry.closedJobCell_unique_of_short_interval hL
    (selected_interval_length_first p e v t ht) hr hs

theorem excludedAt_card_le (p : Packing I b) (e : D.Item ≃ I.Item)
    (hL : 1 ≤ D.L) (v : D.Vertex) : (excludedAt p e v).card ≤ D.P := by
  apply (excludedPositions_card_le (zeroPositiveTuples p e v) (tupleHitsJob p e) ?_).trans
    (zeroPositiveTuples_card_le p e v)
  intro t ht r s hr hs
  exact selected_hits_job_unique p e hL v t ht hr hs

theorem goodRepetitions_card_ge_real (p : Packing I b) (e : D.Item ≃ I.Item)
    (hL : 1 ≤ D.L) (v : D.Vertex) (edge : D.Edge) :
    (D.R : ℝ) - D.P ≤ ((goodRepetitions p e v edge).card : ℝ) :=
  nonexcludedRepetitions_card_ge_real _ edge (excludedAt_card_le p e hL v)

end PackingCounts
end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_ExtractedCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap

section

theorem reductionInventory_R (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ) :
    (reductionInventory c ρ G k).R =
      repetitions (reductionInventory c ρ G k).P G.n (lossAllowance c) := rfl

theorem reductionInventory_height_pos (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ) :
    0 < (reductionInventory c ρ G k).L := (reductionTrees c ρ).height_pos

theorem reductionInstance_count (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ)
    (hk : k ≤ G.n) :
    (reductionInstance c ρ G k).n = 5 * reductionBinBound c ρ G k :=
  (reductionInventory c ρ G k).packingInstance_n hk

theorem reductionInstance_size_bounds (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ)
    (i : (reductionInstance c ρ G k).Item) :
    (1 / 6 : ℚ) < (reductionInstance c ρ G k).size i ∧
      (reductionInstance c ρ G k).size i < 1 :=
  (reductionInventory c ρ G k).packingInstance_size_mem_interval i

open UniformTree

end

end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Configurations_K4Soundness
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinPackingGap

theorem extractedCover_isCover (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ)
    (hk : k ≤ G.n) {b : ℕ} (p : Packing (reductionInstance c ρ G k) b)
    (hb : b ≤ reductionBinBound c ρ G k + c) :
    G.IsCover (extractedCover c ρ G k p) := by
  classical
  let D := reductionInventory c ρ G k
  let Sleft : G.Edge → Finset (Fin D.R) := fun edge =>
    PackingCounts.goodRepetitions p D.itemEquiv (G.left edge) edge
  let Sright : G.Edge → Finset (Fin D.R) := fun edge =>
    PackingCounts.goodRepetitions p D.itemEquiv (G.right edge) edge
  let Lleft : G.Edge → Fin D.R → ℕ := fun edge j =>
    (D.edgeLongTuplesAt p edge (0, j)).card
  let Lright : G.Edge → Fin D.R → ℕ := fun edge j =>
    (D.edgeLongTuplesAt p edge (1, j)).card
  have hL : 1 ≤ D.L := Nat.succ_le_of_lt (reductionInventory_height_pos c ρ G k)
  apply thresholdCover_isCover G (PackingCounts.xplus p D.itemEquiv)
    Sleft Sright Lleft Lright (depthDemand_one_le c ρ) (depthDemand_ge_72 c ρ)
    (reductionInventory_R c ρ G k)
  · intro edge
    exact PackingCounts.goodRepetitions_card_ge_real p D.itemEquiv hL (G.left edge) edge
  · intro edge
    exact PackingCounts.goodRepetitions_card_ge_real p D.itemEquiv hL (G.right edge) edge
  · intro edge j hj
    have hj' : (edge, j) ∉ PackingCounts.excludedAt p D.itemEquiv (G.left edge) :=
      (mem_nonexcludedRepetitions _ _).mp hj
    exact D.long_matches_at_nonexcluded_oaiq082 (reductionInventory_plus_height c ρ G k)
      (reductionInventory_minus_height c ρ G k) hL hk p hb (G.left edge)
      (leftIncidencePosition G D.R edge j) hj'
  · intro edge j hj
    have hj' : (edge, j) ∉ PackingCounts.excludedAt p D.itemEquiv (G.right edge) :=
      (mem_nonexcludedRepetitions _ _).mp hj
    exact D.long_matches_at_nonexcluded_oaiq082 (reductionInventory_plus_height c ρ G k)
      (reductionInventory_minus_height c ρ G k) hL hk p hb (G.right edge)
      (rightIncidencePosition G D.R edge j) hj'
  · intro edge
    have hcap := D.edge_long_matches_capacity_oaiq082 hk p hb edge Finset.univ
    have htwo : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
    change (∑ j : Fin D.R, Lleft edge j) + (∑ j : Fin D.R, Lright edge j) ≤
      D.d * D.R + 3 * D.graph.n * lossAllowance c
    simpa [htwo, Lleft, Lright] using hcap

theorem packing_extracts_cover (c : ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (G : GraphInput) (k : ℕ) (hk : k ≤ G.n) {b : ℕ}
    (p : Packing (reductionInstance c ρ G k) b)
    (hb : b ≤ reductionBinBound c ρ G k + c) :
    ∃ C : Finset G.Vertex, G.IsCover C ∧ (C.card : ℝ) ≤ (k : ℝ) + ρ * G.n :=
  ⟨extractedCover c ρ G k p, extractedCover_isCover c ρ G k hk p hb,
    extractedCover_card_le_oaiq082 c ρ hρ G k hk p hb⟩

end BinPackingGap

end

namespace BinPackingGap

theorem completeFourGraph_reduction_no_packing (c : ℕ) :
    ¬ HasPacking (reductionInstance c (1 / 8) completeFourGraph 2)
      (reductionBinBound c (1 / 8) completeFourGraph 2 + c) := by
  rintro ⟨p⟩
  exact completeFourGraph_no_small_cover
    (packing_extracts_cover c (1 / 8) (by norm_num) completeFourGraph 2
      (by decide) p le_rfl)

theorem completeFourGraph_reduction_opt_gap (c : ℕ) :
    reductionBinBound c (1 / 8) completeFourGraph 2 + c <
      opt (reductionInstance c (1 / 8) completeFourGraph 2) :=
  (not_hasPacking_iff_lt_opt _ _).mp (completeFourGraph_reduction_no_packing c)

end BinPackingGap

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_PhysicalPoolLift
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace BinPackingGap

namespace PoolTemplates

variable {I : Instance} {T U F : Type*} [Fintype T]

variable (D : PoolTemplates I T U F)

omit [Fintype T] in
theorem templateMass_nonneg (t : T) : 0 ≤ D.templateMass t := by
  unfold templateMass
  positivity

omit [Fintype T] in
theorem global_card_ne_zero (t : T) :
    ((D.globalPool (D.globalSpecies t)).card : ℝ) ≠ 0 := by
  exact_mod_cast (Finset.card_pos.mpr (D.global_nonempty t)).ne'

omit [Fintype T] in
theorem flag_card_ne_zero (t : T) :
    ((D.flagPool (D.flagSpecies t)).card : ℝ) ≠ 0 := by
  exact_mod_cast (Finset.card_pos.mpr (D.flag_nonempty t)).ne'

omit [Fintype T] in
theorem sum_templateMass (t : T) :
    (∑ _u : D.Globals t, ∑ _f : D.Flags t, D.templateMass t) = (1 / 2 : ℝ) := by
  have hu := D.global_card_ne_zero t
  have hf := D.flag_card_ne_zero t
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
  unfold templateMass
  field_simp [hu, hf]

theorem objective_weights :
    FractionalCover.objective D.weights = (Fintype.card T : ℝ) / 2 := by
  rw [weights, FractionalCover.objective_pushforward]
  unfold FractionalCover.objective sampleMass
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type, sum_templateMass]
  simp [div_eq_mul_inv]

theorem sum_pool_eq (S : Finset I.Item) (i : I.Item) (a : ℝ) :
    (∑ u : {j // j ∈ S}, if i = u.val then a else 0) =
      if i ∈ S then a else 0 := by
  classical
  by_cases hi : i ∈ S
  · have he : ∀ u : {j // j ∈ S}, i = u.val ↔ u = ⟨i, hi⟩ := by
      intro u
      constructor
      · intro h
        exact Subtype.ext h.symm
      · intro h
        exact (congrArg Subtype.val h).symm
    simp only [he]
    simp [hi]
  · have he : ∀ u : {j // j ∈ S}, i ≠ u.val := by
      intro u h
      exact hi (h.symm ▸ u.property)
    simp [he, hi]

omit [Fintype T] in
theorem template_coverage (t : T) (i : I.Item) :
    (∑ u : D.Globals t, ∑ f : D.Flags t,
      (if i ∈ (D.column t u f).val then (1 : ℝ) else 0) * D.templateMass t) =
    (if i ∈ D.base t then (1 / 2 : ℝ) else 0) +
    (if i ∈ D.globalPool (D.globalSpecies t) then
      1 / (2 * ((D.globalPool (D.globalSpecies t)).card : ℝ)) else 0) +
    (if i ∈ D.flagPool (D.flagSpecies t) then
      1 / (2 * ((D.flagPool (D.flagSpecies t)).card : ℝ)) else 0) := by
  classical
  have hu := D.global_card_ne_zero t
  have hf := D.flag_card_ne_zero t
  by_cases hb : i ∈ D.base t
  · have hgu : i ∉ D.globalPool (D.globalSpecies t) :=
      fun h => Finset.disjoint_left.mp (D.base_global t) hb h
    have hfl : i ∉ D.flagPool (D.flagSpecies t) :=
      fun h => Finset.disjoint_left.mp (D.base_flag t) hb h
    simpa [column, hb, hgu, hfl] using D.sum_templateMass t
  · by_cases hg : i ∈ D.globalPool (D.globalSpecies t)
    · have hfl : i ∉ D.flagPool (D.flagSpecies t) :=
        fun h => Finset.disjoint_left.mp (D.global_flag t) hg h
      have hcol : ∀ u : D.Globals t, ∀ f : D.Flags t,
          i ∈ (D.column t u f).val ↔ i = u.val := by
        intro u f
        have hn : i ≠ f.val := fun h => hfl (h.symm ▸ f.property)
        simp [column, hb, hn]
      simp only [hcol, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_comm]
      simp_rw [sum_pool_eq]
      simp only [hb, hg, hfl, ite_false, ite_true, if_true, zero_add, add_zero,
        Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      unfold templateMass
      field_simp [hu, hf]
    · by_cases hfl : i ∈ D.flagPool (D.flagSpecies t)
      · have hcol : ∀ u : D.Globals t, ∀ f : D.Flags t,
            i ∈ (D.column t u f).val ↔ i = f.val := by
          intro u f
          have hn : i ≠ u.val := fun h => hg (h.symm ▸ u.property)
          simp [column, hb, hn]
        simp only [hcol, ite_mul, one_mul, zero_mul]
        simp_rw [sum_pool_eq]
        simp only [hb, hg, hfl, ite_false, ite_true, if_true, zero_add,
          Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
        unfold templateMass
        field_simp [hu, hf]
      · have hcol : ∀ u : D.Globals t, ∀ f : D.Flags t,
            i ∉ (D.column t u f).val := by
          intro u f
          have hnu : i ≠ u.val := fun h => hg (h.symm ▸ u.property)
          have hnf : i ≠ f.val := fun h => hfl (h.symm ▸ f.property)
          simp [column, hb, hnu, hnf]
        simp [hcol, hb, hg, hfl]

theorem sum_by_species {S : Type*} [Fintype S] [DecidableEq S]
    (species : T → S) (a : S → ℝ) :
    (∑ t, a (species t)) =
      ∑ s, ((Finset.univ.filter (fun t => species t = s)).card : ℝ) * a s := by
  classical
  calc
    (∑ t, a (species t)) = ∑ t, ∑ s, if species t = s then a s else 0 := by simp
    _ = ∑ s, ∑ t, if species t = s then a s else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      rw [← Finset.sum_filter]
      simp

theorem sum_pool_demands {S : Type*} [Fintype S] [DecidableEq S]
    (species : T → S) (pool : S → Finset I.Item)
    (hdemand : ∀ s, (Finset.univ.filter (fun t => species t = s)).card =
      2 * (pool s).card) (i : I.Item) :
    (∑ t, if i ∈ pool (species t) then
      1 / (2 * ((pool (species t)).card : ℝ)) else 0) =
    ∑ s, if i ∈ pool s then (1 : ℝ) else 0 := by
  classical
  rw [sum_by_species species (fun s =>
    if i ∈ pool s then 1 / (2 * ((pool s).card : ℝ)) else 0)]
  apply Finset.sum_congr rfl
  intro s _
  rw [hdemand s]
  by_cases hi : i ∈ pool s
  · have hs : ((pool s).card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr ⟨i, hi⟩).ne'
    simp only [hi, ite_true, if_true, Nat.cast_mul, Nat.cast_ofNat]
    field_simp [hs]
  · simp [hi]

variable [Fintype U] [Fintype F] [DecidableEq U] [DecidableEq F]

theorem weights_feasible
    (labeled : Finset I.Item)
    (hbase : ∀ i, (Finset.univ.filter (fun t => i ∈ D.base t)).card =
      if i ∈ labeled then 2 else 0)
    (hglobal : ∀ u, (Finset.univ.filter (fun t => D.globalSpecies t = u)).card =
      2 * (D.globalPool u).card)
    (hflag : ∀ f, (Finset.univ.filter (fun t => D.flagSpecies t = f)).card =
      2 * (D.flagPool f).card)
    (hpartition : ∀ i,
      (if i ∈ labeled then (1 : ℝ) else 0) +
      (∑ u, if i ∈ D.globalPool u then (1 : ℝ) else 0) +
      (∑ f, if i ∈ D.flagPool f then (1 : ℝ) else 0) = 1) :
    IndividualFeasible I D.weights := by
  classical
  refine ⟨FractionalCover.pushforward_nonneg D.sampleColumn
    (fun s => D.templateMass_nonneg s.1), ?_⟩
  intro i
  change 1 ≤ ∑ H, individualMatrix I H i * D.weights H
  rw [weights, FractionalCover.coverage_pushforward]
  change 1 ≤ ∑ s : D.Sample,
    (if i ∈ (D.column s.1 s.2.1 s.2.2).val then (1 : ℝ) else 0) * D.templateMass s.1
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type, template_coverage, Finset.sum_add_distrib]
  rw [sum_pool_demands D.globalSpecies D.globalPool hglobal,
    sum_pool_demands D.flagSpecies D.flagPool hflag]
  have hb : (∑ t, if i ∈ D.base t then (1 / 2 : ℝ) else 0) =
      if i ∈ labeled then (1 : ℝ) else 0 := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, hbase]
    split_ifs <;> norm_num
  simpa only [hb, hpartition i] using (le_refl (1 : ℝ))

end PoolTemplates

end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_LocalTemplateBases
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.decidableAncestor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.InventoryData

open scoped BigOperators

variable (D : InventoryData)

private theorem templateTagged_ne {r s : Role} (hrs : r ≠ s)
    (a : D.RoleCopies r) (b : D.RoleCopies s) :
    D.itemEquiv ⟨r, a⟩ ≠ D.itemEquiv ⟨s, b⟩ := by
  intro h
  exact hrs (congrArg (fun i : D.Item => i.1) (D.itemEquiv.injective h))

private theorem templateTagged_eq_iff (r : Role) (a b : D.RoleCopies r) :
    D.itemEquiv ⟨r, a⟩ = D.itemEquiv ⟨r, b⟩ ↔ a = b := by
  constructor
  · intro h
    exact sigma_mk_injective (β := D.RoleCopies) (i := r) (D.itemEquiv.injective h)
  · rintro rfl
    rfl

private theorem card_templatePredicate {C : Type*}
    (e : D.Template ≃ Bool × C) (c : C) (p : D.Template → Prop) [DecidablePred p]
    (hp : ∀ t, p t ↔ (e t).2 = c) :
    ((Finset.univ : Finset D.Template).filter p).card = 2 := by
  rw [← Fintype.card_subtype p]
  exact (Fintype.card_congr
    ((Equiv.subtypeEquivRight hp).trans (templateFiberBoolEquiv e c))).trans
      Fintype.card_bool

@[simp] theorem itemEquiv_x_mem_templateBase (S : ∀ v s, D.LocalState v s)
    (t : D.Template) (c : D.RoleCopies .x) :
    D.itemEquiv ⟨.x, c⟩ ∈ D.templateBase S t ↔ D.templateRowCopy t = c := by
  have hxa := D.templateTagged_ne (by decide : Role.x ≠ .anchor) c
    (D.templateAnchorCopy S t)
  have hxl := D.templateTagged_ne (by decide : Role.x ≠ .«local») c
    (D.templateLocalCopy S t)
  simp only [templateBase, Finset.mem_insert, Finset.mem_singleton, hxa, hxl, or_false]
  exact (D.templateTagged_eq_iff .x c (D.templateRowCopy t)).trans eq_comm

@[simp] theorem itemEquiv_anchor_mem_templateBase (S : ∀ v s, D.LocalState v s)
    (t : D.Template) (c : D.RoleCopies .anchor) :
    D.itemEquiv ⟨.anchor, c⟩ ∈ D.templateBase S t ↔ D.templateAnchorCopy S t = c := by
  have hax := D.templateTagged_ne (by decide : Role.anchor ≠ .x) c
    (D.templateRowCopy t)
  have hal := D.templateTagged_ne (by decide : Role.anchor ≠ .«local») c
    (D.templateLocalCopy S t)
  simp only [templateBase, Finset.mem_insert, Finset.mem_singleton, hax, hal,
    false_or, or_false]
  exact (D.templateTagged_eq_iff .anchor c (D.templateAnchorCopy S t)).trans eq_comm

@[simp] theorem itemEquiv_local_mem_templateBase (S : ∀ v s, D.LocalState v s)
    (t : D.Template) (c : D.RoleCopies .«local») :
    D.itemEquiv ⟨.«local», c⟩ ∈ D.templateBase S t ↔ D.templateLocalCopy S t = c := by
  have hlx := D.templateTagged_ne (by decide : Role.«local» ≠ .x) c
    (D.templateRowCopy t)
  have hla := D.templateTagged_ne (by decide : Role.«local» ≠ .anchor) c
    (D.templateAnchorCopy S t)
  simp only [templateBase, Finset.mem_insert, Finset.mem_singleton, hlx, hla, false_or]
  exact (D.templateTagged_eq_iff .«local» c (D.templateLocalCopy S t)).trans eq_comm

@[simp] theorem itemEquiv_global_not_mem_templateBase (S : ∀ v s, D.LocalState v s)
    (t : D.Template) (c : D.RoleCopies .«global») :
    D.itemEquiv ⟨.«global», c⟩ ∉ D.templateBase S t := by
  simp only [templateBase, Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨D.templateTagged_ne (by decide : Role.«global» ≠ .x) _ _,
    D.templateTagged_ne (by decide : Role.«global» ≠ .anchor) _ _,
    D.templateTagged_ne (by decide : Role.«global» ≠ .«local») _ _⟩

@[simp] theorem itemEquiv_flag_not_mem_templateBase (S : ∀ v s, D.LocalState v s)
    (t : D.Template) (c : D.RoleCopies .flag) :
    D.itemEquiv ⟨.flag, c⟩ ∉ D.templateBase S t := by
  simp only [templateBase, Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨D.templateTagged_ne (by decide : Role.flag ≠ .x) _ _,
    D.templateTagged_ne (by decide : Role.flag ≠ .anchor) _ _,
    D.templateTagged_ne (by decide : Role.flag ≠ .«local») _ _⟩

theorem templateBase_appearance_count (S : ∀ v s, D.LocalState v s)
    (i : D.packingInstance.Item) :
    ((Finset.univ : Finset D.Template).filter (fun t => i ∈ D.templateBase S t)).card =
      if i ∈ D.labeledItems then 2 else 0 := by
  classical
  obtain ⟨⟨r, c⟩, rfl⟩ := D.itemEquiv.surjective i
  cases r with
  | x =>
    rw [ite_eq_left (by simp)]
    apply D.card_templatePredicate (D.templateCopyEquiv (fun v s => D.stateRowEquiv v s)) c
      (fun t => D.itemEquiv ⟨.x, c⟩ ∈ D.templateBase S t)
    intro t
    simpa only [templateCopyEquiv_apply, templateRowCopy] using
      D.itemEquiv_x_mem_templateBase S t c
  | anchor =>
    rw [ite_eq_left (by simp)]
    apply D.card_templatePredicate
      (D.templateCopyEquiv (fun v s => (S v s).anchorAtEquiv)) c
      (fun t => D.itemEquiv ⟨.anchor, c⟩ ∈ D.templateBase S t)
    intro t
    simpa only [templateCopyEquiv_apply, templateAnchorCopy] using
      D.itemEquiv_anchor_mem_templateBase S t c
  | «global» => simp
  | «local» =>
    rw [ite_eq_left (by simp)]
    apply D.card_templatePredicate
      (D.templateCopyEquiv (fun v s => (S v s).localAtEquiv)) c
      (fun t => D.itemEquiv ⟨.«local», c⟩ ∈ D.templateBase S t)
    intro t
    simpa only [templateCopyEquiv_apply, templateLocalCopy] using
      D.itemEquiv_local_mem_templateBase S t c
  | flag => simp

end BinPackingGap.InventoryData

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Configurations_ReductionFractional
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.InventoryData

open scoped BigOperators

variable (D : InventoryData)

theorem card_template : Fintype.card D.Template = 2 * D.B := by
  simp only [Template, Fintype.card_sigma, Fintype.card_prod, Fintype.card_bool,
    D.card_localBin]
  rw [← Finset.mul_sum]
  rfl

theorem statePoolTemplates_feasible (hn : D.graph.n = 2 * D.k)
    (S : ∀ v s, D.LocalState v s) :
    IndividualFeasible D.packingInstance (D.statePoolTemplates hn S).weights := by
  apply (D.statePoolTemplates hn S).weights_feasible D.labeledItems
  · exact D.templateBase_appearance_count S
  · intro s
    change (Finset.univ.filter (fun t : D.Template =>
      D.templateGlobalSpecies t = s)).card = 2 * (D.physicalGlobalPool s).card
    rw [D.card_physicalGlobalPool]
    exact D.doubled_stateGlobalSpecies_count hn s
  · intro f
    change (Finset.univ.filter (fun t : D.Template =>
      D.templateFlagSpecies t = f)).card = 2 * (D.physicalFlagPool f).card
    rw [D.card_physicalFlagPool]
    exact D.doubled_stateFlagSpecies_count f
  · exact D.physicalInventory_indicator_partition

theorem statePoolTemplates_objective (hn : D.graph.n = 2 * D.k)
    (S : ∀ v s, D.LocalState v s) :
    FractionalCover.objective (D.statePoolTemplates hn S).weights = (D.B : ℝ) := by
  rw [(D.statePoolTemplates hn S).objective_weights, D.card_template]
  push_cast
  ring

theorem ofCompetingTrees_physical_witness (G : GraphInput) {d : ℕ}
    (T : CompetingTrees d) (hd : 0 < d) (R k : ℕ) (hn : G.n = 2 * k) :
    ∃ w : IndividualConfiguration (ofCompetingTrees G T R k).packingInstance → ℝ,
      IndividualFeasible (ofCompetingTrees G T R k).packingInstance w ∧
      FractionalCover.objective w = ((ofCompetingTrees G T R k).B : ℝ) := by
  let D := ofCompetingTrees G T R k
  let S : ∀ v s, D.LocalState v s := constructedLocalState G T hd R k
  exact ⟨(D.statePoolTemplates hn S).weights,
    D.statePoolTemplates_feasible hn S, D.statePoolTemplates_objective hn S⟩

theorem ofCompetingTrees_bothLP_eq (G : GraphInput) {d : ℕ}
    (T : CompetingTrees d) (hd : 0 < d) (R k : ℕ) (hn : G.n = 2 * k) :
    individualLP (ofCompetingTrees G T R k).packingInstance =
        ((ofCompetingTrees G T R k).B : ℝ) ∧
      typeLP (ofCompetingTrees G T R k).packingInstance =
        ((ofCompetingTrees G T R k).B : ℝ) := by
  obtain ⟨w, hw, hobj⟩ := ofCompetingTrees_physical_witness G T hd R k hn
  exact bothLP_eq_of_physical_witness _ _
    ((ofCompetingTrees G T R k).packingInstance_n (by change k ≤ G.n; omega))
    (fun i => ((ofCompetingTrees G T R k).packingInstance_size_mem_interval i).1)
    w hw hobj

end BinPackingGap.InventoryData

end

namespace BinPackingGap

theorem reduction_bothLP_eq (c : ℕ) (rho : ℝ) (G : GraphInput) (k : ℕ)
    (hn : G.n = 2 * k) :
    individualLP (reductionInstance c rho G k) =
        (reductionBinBound c rho G k : ℝ) ∧
      typeLP (reductionInstance c rho G k) =
        (reductionBinBound c rho G k : ℝ) :=
  InventoryData.ofCompetingTrees_bothLP_eq G (reductionTrees c rho)
    (depthDemand_pos c rho) _ k hn

end BinPackingGap

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchInitializeEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchMachineComposition

open Turing BinPackingGames.Foundations.Complexity
open SearchSemantics SearchEncoding

theorem algorithm_invalid (D : List Bool → Bool) (items : RawInstance)
    (invalid : ¬ items.Valid) :
    algorithm D (BinaryEncoding.rawInstanceBits items) = none := by
  have rejected : ExtensionCertificate.validItems items = false := by
    cases checked : ExtensionCertificate.validItems items with
    | false => rfl
    | true => exact False.elim (invalid
        ((ExtensionCertificate.validItems_eq_true_iff items).mp checked))
  simp [rejected]

end BinPackingGap.SearchMachineComposition

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Results_AdditiveHardness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

theorem pEqualsNP_of_exists_absoluteAdditiveAlgorithm
    (h : ∃ c : Nat, Nonempty (AbsoluteAdditiveAlgorithm c)) : PEqualsNP := by
  obtain ⟨c, ⟨algorithm⟩⟩ := h
  exact pEqualsNP_of_absoluteAdditiveAlgorithm_oaiq082 c algorithm

end BinPackingGap

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Results_OptimalSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

open Turing BinPackingGames.Foundations.Complexity

theorem absoluteAdditiveAlgorithm_of_pEqualsNP_optimal (h : PEqualsNP)
    (items : RawInstance) (valid : items.Valid) :
    ∃ packing : RawPacking,
      (absoluteAdditiveAlgorithm_of_pEqualsNP h).run (BinaryEncoding.rawInstanceBits items) =
        some packing ∧ packing.Feasible items ∧ packing.bins = opt (items.toInstance valid) :=
  SearchMachineComposition.algorithm_optimal (OptimalSearch.decidesExtension h) items valid

theorem absoluteAdditiveAlgorithm_of_pEqualsNP_malformed (h : PEqualsNP)
    (input : List Bool) (malformed : BinaryEncoding.decodeRawInstance input = none) :
    (absoluteAdditiveAlgorithm_of_pEqualsNP h).run input = none :=
  SearchMachineComposition.algorithm_malformed (OptimalSearch.decider h) input malformed

theorem absoluteAdditiveAlgorithm_of_pEqualsNP_invalid (h : PEqualsNP)
    (items : RawInstance) (invalid : ¬ items.Valid) :
    (absoluteAdditiveAlgorithm_of_pEqualsNP h).run (BinaryEncoding.rawInstanceBits items) = none :=
  SearchMachineComposition.algorithm_invalid (OptimalSearch.decider h) items invalid

end BinPackingGap

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Results_StructuralGap
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

theorem completeFourGraph_reduction_bothLP_eq (c : ℕ) :
    individualLP (reductionInstance c (1 / 8) completeFourGraph 2) =
        (reductionBinBound c (1 / 8) completeFourGraph 2 : ℝ) ∧
      typeLP (reductionInstance c (1 / 8) completeFourGraph 2) =
        (reductionBinBound c (1 / 8) completeFourGraph 2 : ℝ) :=
  reduction_bothLP_eq c (1 / 8) completeFourGraph 2 (by decide)

theorem structural_additive_gap (c : ℕ) :
    ∃ I : Instance, ∃ B : ℕ,
      I.n = 5 * B ∧
      (∀ i, (1 / 6 : ℚ) < I.size i ∧ I.size i < 1) ∧
      B + c < opt I ∧ individualLP I = (B : ℝ) ∧ typeLP I = (B : ℝ) := by
  refine ⟨reductionInstance c (1 / 8) completeFourGraph 2,
    reductionBinBound c (1 / 8) completeFourGraph 2,
    reductionInstance_count c (1 / 8) completeFourGraph 2 (by decide),
    reductionInstance_size_bounds c (1 / 8) completeFourGraph 2,
    completeFourGraph_reduction_opt_gap c, ?_⟩
  exact completeFourGraph_reduction_bothLP_eq c

end BinPackingGap

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Results_AlgorithmEquivalence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

theorem exists_absoluteAdditiveAlgorithm_iff_pEqualsNP :
    (∃ c : Nat, Nonempty (AbsoluteAdditiveAlgorithm c)) ↔ PEqualsNP := by
  constructor
  · exact pEqualsNP_of_exists_absoluteAdditiveAlgorithm
  · intro equality
    exact ⟨0, ⟨absoluteAdditiveAlgorithm_of_pEqualsNP equality⟩⟩

end BinPackingGap

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

theorem main_results_oai :
    (∀ c : ℕ, ∃ I : Instance, ∃ B : ℕ,
      I.n = 5 * B ∧
      (∀ i, (1 / 6 : ℚ) < I.size i ∧ I.size i < 1) ∧
      B + c < opt I ∧ individualLP I = (B : ℝ) ∧ typeLP I = (B : ℝ)) ∧
    (∀ c : Nat, PackingGapNPHard c) ∧
    ((∃ c : Nat, Nonempty (AbsoluteAdditiveAlgorithm c)) ↔ PEqualsNP) ∧
    (PEqualsNP → ∃ algorithm : AbsoluteAdditiveAlgorithm 0,
    (∀ (items : RawInstance) (valid : items.Valid), ∃ packing : RawPacking,
      algorithm.run (BinaryEncoding.rawInstanceBits items) = some packing ∧
      packing.Feasible items ∧ packing.bins = opt (items.toInstance valid)) ∧
    algorithm.run (BinaryEncoding.rawInstanceBits []) = some ⟨0, []⟩ ∧
    (∀ input : List Bool, BinaryEncoding.decodeRawInstance input = none →
      algorithm.run input = none) ∧
    (∀ items : RawInstance, ¬ items.Valid →
      algorithm.run (BinaryEncoding.rawInstanceBits items) = none)) := by
  refine ⟨structural_additive_gap, packingGapNPHard_oaiq082,
    exists_absoluteAdditiveAlgorithm_iff_pEqualsNP, ?_⟩
  intro h
  exact ⟨absoluteAdditiveAlgorithm_of_pEqualsNP h,
    absoluteAdditiveAlgorithm_of_pEqualsNP_optimal h,
    absoluteAdditiveAlgorithm_of_pEqualsNP_empty h,
    absoluteAdditiveAlgorithm_of_pEqualsNP_malformed h,
    absoluteAdditiveAlgorithm_of_pEqualsNP_invalid h⟩

end BinPackingGap

end OAI
end

theorem solution : type_of% @OAI.BinPackingGap.main_results_oai := @OAI.BinPackingGap.main_results_oai
