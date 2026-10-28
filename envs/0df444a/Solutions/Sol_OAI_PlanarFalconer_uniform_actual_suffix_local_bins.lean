-- Prove2me | solution 1 for OAI.PlanarFalconer.uniform_actual_suffix_local_bins
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:17:32.843329+00:00
-- url     : https://prove2.me/submissions/547c6afe-1c2e-4e9f-94ef-45167c87febb

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002

section
-- module Solutions.OAIQ038_FA.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_DyadicGeometry
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric

theorem DyadicSquare.cover_children (Q : DyadicSquare) :
    Q.carrier = ((Q.child false false).carrier ∪ (Q.child false true).carrier) ∪
      ((Q.child true false).carrier ∪ (Q.child true true).carrier) := by
  ext z
  simp only [carrier, child, Bool.false_eq_true, ↓reduceIte,
    add_zero, mem_ofPred_eq, mem_union]
  constructor
  · intro hz
    by_cases hx : z 0 < Q.x + Q.side / 2 <;>
      by_cases hy : z 1 < Q.y + Q.side / 2
    · exact Or.inl (Or.inl ⟨hz.1,hx,hz.2.2.1,hy⟩)
    · exact Or.inl (Or.inr ⟨hz.1,hx,by linarith,by linarith [hz.2.2.2]⟩)
    · exact Or.inr (Or.inl ⟨by linarith,by linarith [hz.2.1],hz.2.2.1,hy⟩)
    · exact Or.inr (Or.inr ⟨by linarith,by linarith [hz.2.1],
        by linarith,by linarith [hz.2.2.2]⟩)
  · intro hz
    rcases hz with (hz | hz) | (hz | hz) <;>
      refine ⟨by linarith [hz.1,hz.2.1], by linarith [hz.1,hz.2.1],
        by linarith [hz.2.2.1,hz.2.2.2], by linarith [hz.2.2.1,hz.2.2.2]⟩

theorem DyadicSquare.dist_le (Q : DyadicSquare) (hQ : 0 ≤ Q.side)
    {z w : Plane} (hz : z ∈ Q.carrier) (hw : w ∈ Q.carrier) :
    dist z w ≤ 2 * Q.side := by
  have h0 : |z 0 - w 0| ≤ Q.side := by
    apply abs_le.mpr; constructor <;> linarith [hz.1,hz.2.1,hw.1,hw.2.1]
  have h1 : |z 1 - w 1| ≤ Q.side := by
    apply abs_le.mpr; constructor <;>
      linarith [hz.2.2.1,hz.2.2.2,hw.2.2.1,hw.2.2.2]
  have hs := EuclideanSpace.dist_sq_eq z w
  simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs] at hs
  have hs0 := sq_le_sq₀ (abs_nonneg _) hQ |>.mpr h0
  have hs1 := sq_le_sq₀ (abs_nonneg _) hQ |>.mpr h1
  rw [sq_abs] at hs0 hs1
  nlinarith [dist_nonneg (x := z) (y := w)]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_DyadicMeasure
attribute [-instance] _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal NNReal

theorem DyadicSquare.descendant_side_pos (Q : DyadicSquare) (hQ : 0 < Q.side)
    (p : List (Bool × Bool)) : 0 < (Q.descendant p).side := by
  induction p generalizing Q with
  | nil => exact hQ
  | cons a p ih => exact ih _ (Q.child_side_pos hQ a.1 a.2)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_DyadicPacking
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal NNReal

theorem DyadicSquare.descendant_side (Q : DyadicSquare) (p : List (Bool × Bool)) :
    (Q.descendant p).side = Q.side / (2 : ℝ)^p.length := by
  induction p generalizing Q with
  | nil => simp [descendant]
  | cons a p ih =>
    simp only [descendant, ih, child, List.length_cons, pow_succ]
    ring

theorem DyadicSquare.mem_descendant_at_depth (Q : DyadicSquare) (n : ℕ)
    {z : Plane} (hz : z ∈ Q.carrier) :
    ∃ p ∈ dyadicPaths n, z ∈ (Q.descendant p).carrier := by
  induction n generalizing Q with
  | zero => exact ⟨[],by simp, hz⟩
  | succ n ih =>
    have step (i j : Bool) (hz : z ∈ (Q.child i j).carrier) :
        ∃ p ∈ dyadicPaths (n+1), z ∈ (Q.descendant p).carrier := by
      obtain ⟨p,hp,hz⟩ := ih _ hz
      exact ⟨(i,j) :: p,by simpa using hp,hz⟩
    rw [Q.cover_children] at hz
    rcases hz with (hz | hz) | (hz | hz)
    · exact step false false hz
    · exact step false true hz
    · exact step true false hz
    · exact step true true hz

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_ScaledDyadicPacking
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem DyadicSquare.center_mem (Q : DyadicSquare) (hQ : 0 < Q.side) : Q.center ∈ Q.carrier := by
  simp only [center,carrier,mem_ofPred_eq,Matrix.cons_val_zero,Matrix.cons_val_one]
  constructor
  · linarith
  · exact ⟨by linarith,by linarith,by linarith⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_PrefixMass
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem DyadicSquare.descendant_append (Q : DyadicSquare) (p q : CellPath) :
    Q.descendant (p++q) = (Q.descendant p).descendant q := by
  induction p generalizing Q with
  | nil => rfl
  | cons a p ih => exact ih (Q.child a.1 a.2)

theorem DyadicSquare.descendant_subset_take (Q : DyadicSquare) (hQ : 0 < Q.side)
    (p : CellPath) (a : ℕ) : (Q.descendant p).carrier ⊆ (Q.descendant (p.take a)).carrier := by
  have he := Q.descendant_append (p.take a) (p.drop a)
  rw [List.take_append_drop] at he
  rw [he]
  exact (Q.descendant (p.take a)).descendant_subset (Q.descendant_side_pos hQ _) _

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphGeometry
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem planeDot_abs_le (v w : Plane) : |planeDot v w| ≤ ‖v‖*‖w‖ := by
  have hv := EuclideanSpace.real_norm_sq_eq v
  have hw := EuclideanSpace.real_norm_sq_eq w
  simp only [Fin.sum_univ_two] at hv hw
  have hsq : (planeDot v w)^2 ≤ ‖v‖^2*‖w‖^2 := by
    rw [hv,hw]
    unfold planeDot
    nlinarith [sq_nonneg (v 0*w 1-v 1*w 0)]
  have hp : 0 ≤ ‖v‖*‖w‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith [sq_abs (planeDot v w),abs_nonneg (planeDot v w)]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_ActualAngularTests
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory

theorem stripCount_transfer {ι : Type*} (S : Finset ι) (v : ι → Plane)
    {W W' D d : ℝ} (hD : 0 ≤ D) (hv : ∀ i ∈ S, ‖v i‖ ≤ D)
    {ω ω' : Plane} (hd : dist ω ω' ≤ d) (hgap : W'+D*d ≤ W) :
    stripCount S v W' ω' ≤ stripCount S v W ω := by
  classical
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hi,hstrip⟩ := Finset.mem_filter.mp hi
  refine Finset.mem_filter.mpr ⟨hi,?_⟩
  have he : planeDot (v i) ω = planeDot (v i) ω' + planeDot (v i) (ω-ω') := by
    simp [planeDot]; ring
  have hn : ‖ω-ω'‖ ≤ d := by simpa only [dist_eq_norm] using hd
  calc
    |planeDot (v i) ω| ≤ |planeDot (v i) ω'|+|planeDot (v i) (ω-ω')| := by
      rw [he]; exact abs_add_le _ _
    _ ≤ W'+D*d := add_le_add hstrip ((planeDot_abs_le _ _).trans
      (mul_le_mul (hv i hi) hn (norm_nonneg _) hD))
    _ ≤ W := hgap

theorem projectionTestCount_transfer (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane)
    (p u : ℕ) {P : CellPath} (hP : P.length = p) {W W' d : ℝ} {ω ω' : Plane}
    (hd : dist ω ω' ≤ d) (hgap : W'+(2*Q.side/(2:ℝ)^p)*d ≤ W) :
    projectionTestCount Q ρ p u P W' ω' ≤ projectionTestCount Q ρ p u P W ω := by
  classical
  apply stripCount_transfer _ _ (by positivity : 0 ≤ 2*Q.side/(2:ℝ)^p) _ hd hgap
  intro cc hcc
  have hmem {c : CellPath} (hc : c ∈ projectionTestCells Q ρ p u P) :
      (Q.descendant c).center ∈ (Q.descendant P).carrier := by
    rw [← (Finset.mem_filter.mp hc).2.2]
    exact Q.descendant_subset_take hQ c p ((Q.descendant c).center_mem (Q.descendant_side_pos hQ c))
  have hh := (Q.descendant P).dist_le (Q.descendant_side_pos hQ P).le
    (hmem (Finset.mem_product.mp hcc).1) (hmem (Finset.mem_product.mp hcc).2)
  simpa only [dist_eq_norm,Q.descendant_side,hP,mul_div_assoc] using hh

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Frostman_FrostmanProfileCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Metric
open scoped ENNReal

theorem fixed_constant_absorbed {lam : ℝ} (hlam : 0 < lam) (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, C ≤ ((2:ℝ)^N)^lam := by
  have hb : 1 < (2:ℝ)^lam := Real.one_lt_rpow (by norm_num) hlam
  obtain ⟨N₀,hN₀⟩ := pow_unbounded_of_one_lt C hb
  refine ⟨N₀,fun N hN => ?_⟩
  have hh := hN₀.le.trans (pow_le_pow_right₀ hb.le hN)
  rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2),mul_comm,
    Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)] at hh
  exact hh

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_SuffixAngularRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem suffix_direction_scale {a p u : ℕ} (hs : a+u ≤ 2*p) (hpu : p ≤ u) :
    (2:ℝ)^a/(2:ℝ)^p ≤ 1/(2:ℝ)^(u-p) := by
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  rw [one_mul,← pow_add]
  exact pow_le_pow_right₀ (by norm_num) (by omega)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_InteriorPolicy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem finiteArgmin_spec {S : Finset ℕ} (hS : S.Nonempty) (f : ℕ → ℝ) :
    finiteArgmin S f ∈ S ∧ ∀ j ∈ S, f (finiteArgmin S f) ≤ f j := by
  rw [finiteArgmin,dite_eq_left hS]
  have hs := Classical.choose_spec (Finset.exists_mem_eq_inf' hS f)
  refine ⟨hs.1,?_⟩
  intro j hj
  rw [← hs.2]
  exact Finset.inf'_le f hj

theorem policyBlock_nonempty {N q k : ℕ} (hq : 0 < q) (hk : k*q ≤ N) :
    (policyBlock N q k).Nonempty := by
  apply Finset.nonempty_Ico.mpr
  have he : (k+1)*q = k*q+q := by ring
  omega

theorem policyRepresentative_spec (A : ℕ → ℝ) {N q k : ℕ} (hq : 0 < q) (hk : k*q ≤ N) :
    k*q ≤ policyRepresentative A N q k ∧ policyRepresentative A N q k < (k+1)*q ∧
      policyRepresentative A N q k ≤ N ∧
      ∀ n ∈ policyBlock N q k, A (policyRepresentative A N q k) ≤ A n := by
  have hh := finiteArgmin_spec (policyBlock_nonempty hq hk) A
  have hm := Finset.mem_Ico.mp hh.1
  refine ⟨hm.1,lt_of_lt_of_le hm.2 (min_le_left _ _),?_,hh.2⟩
  exact Nat.le_of_lt_succ (lt_of_lt_of_le hm.2 (min_le_right _ _))

theorem policyBlocks_mem {N q a t k : ℕ} (h : k ∈ policyBlocks N q a t) :
    k ≤ N/q ∧ a+q ≤ k*q ∧ (k+1)*q ≤ t-q+1 := by
  obtain ⟨hk,hl,hr⟩ := Finset.mem_filter.mp h
  exact ⟨Nat.le_of_lt_succ (Finset.mem_range.mp hk),hl,hr⟩

theorem policy_left_block {N q a t : ℕ} (hq : 0 < q) (ht : t ≤ N) (hwide : a+100*q < t) :
    ∃ k ∈ policyBlocks N q a t, k*q ≤ a+2*q := by
  let k := (a+2*q-1)/q
  have hlo := Nat.div_mul_le_self (a+2*q-1) q
  have hhi := Nat.lt_mul_div_succ (a+2*q-1) hq
  have hprod : (k+1)*q = k*q+q := by ring
  change k*q ≤ a+2*q-1 at hlo
  have hceil : a+q ≤ k*q := by
    rw [Nat.mul_comm q] at hhi
    change a+2*q-1 < (k+1)*q at hhi
    omega
  have hend : (k+1)*q ≤ t-q+1 := by omega
  have hkn : k*q ≤ N := by omega
  refine ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_,hceil,hend⟩,by omega⟩
  exact Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le hq).mpr hkn)

theorem policyBlocks_nonempty {N q a t : ℕ} (hq : 0 < q) (ht : t ≤ N) (hwide : a+100*q < t) :
    (policyBlocks N q a t).Nonempty := by
  obtain ⟨k,hk,_⟩ := policy_left_block hq ht hwide
  exact ⟨k,hk⟩

theorem policyDepth_interior (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q)
    (hne : (policyBlocks N q a t).Nonempty) :
    a+q ≤ policyDepth A N q a t ∧ policyDepth A N q a t ≤ t-q := by
  have hkey := (finiteArgmin_spec hne (fun k => A (policyRepresentative A N q k))).1
  have hb := policyBlocks_mem hkey
  have hrep := policyRepresentative_spec A hq ((Nat.le_div_iff_mul_le hq).mp hb.1)
  exact ⟨hb.2.1.trans hrep.1,Nat.le_of_lt_succ (hrep.2.1.trans_le hb.2.2)⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_PositiveDistancePushforward
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

namespace PositiveDistanceData

theorem distance_prod (d e : PositiveDistanceData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ] :
    d.distance.prod e.distance = Measure.map
      (fun z : (Plane × Plane) × (Plane × Plane) =>
        (dist z.1.1 z.1.2, dist z.2.1 z.2.2)) (d.pair.prod e.pair) :=
  Measure.map_prod_map _ _ (continuous_fst.dist continuous_snd).measurable
    (continuous_fst.dist continuous_snd).measurable

theorem distance_collision (d : PositiveDistanceData) [IsFiniteMeasure d.ρ] (w : ℝ) :
    (d.distance.prod d.distance) {z : ℝ × ℝ | |z.1-z.2| ≤ w} =
      (d.pair.prod d.pair) {z | |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ w} := by
  rw [distance_prod,Measure.map_apply (by fun_prop) (by measurability)]
  rfl

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphDirectionStability
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric

 theorem endpoint_direction_dist_le {x y c d : Plane} (hxy : y ≠ x) (hcd : d ≠ c) :
    dist (sourceRadialUnit x y) (sourceRadialUnit c d) ≤
      2*(dist x c + dist y d)/dist x y := by
  change dist (sourceRadialVector x y) (sourceRadialVector c d) ≤ _
  simp only [sourceRadialVector, ite_eq_right hxy, ite_eq_right hcd]
  have hn := normalized_vector_dist_le (y-x) (d-c) (sub_ne_zero.mpr hxy) (sub_ne_zero.mpr hcd)
  have hd : dist (y-x) (d-c) ≤ dist x c + dist y d := by
    rw [dist_eq_norm, show (y-x)-(d-c) = (y-d)-(x-c) by abel]
    exact (norm_sub_le _ _).trans_eq (by rw [dist_eq_norm,dist_eq_norm]; ring)
  have he : ‖y-x‖ = dist x y := by rw [dist_eq_norm, norm_sub_rev]
  rw [he] at hn ⊢
  exact hn.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by norm_num))
    (dist_nonneg))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_SourceStrongSeparation
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set

theorem dyadic_strong_separation_endpoints (P Q : DyadicSquare)
    (hP : 0 < P.side) (hQ : 0 < Q.side) {s : ℝ}
    (hp : P.side ≤ s) (hq : Q.side ≤ s)
    (hl : 100*s ≤ dist P.center Q.center) (hu : dist P.center Q.center ≤ 2000*s)
    {x y : Plane} (hx : x ∈ P.carrier) (hy : y ∈ Q.carrier) :
    96*s ≤ dist x y ∧ dist x y ≤ 2004*s := by
  have hx' := P.dist_le hP.le hx (P.center_mem hP)
  have hy' := Q.dist_le hQ.le hy (Q.center_mem hQ)
  have ht₁ := dist_triangle P.center x Q.center
  have ht₂ := dist_triangle x y Q.center
  have ht₃ := dist_triangle x P.center y
  have ht₄ := dist_triangle P.center Q.center y
  rw [dist_comm P.center x] at ht₁
  rw [dist_comm Q.center y] at ht₄
  constructor <;> linarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_PositiveDistanceWeight
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
namespace PositiveDistanceData

theorem separated_distance_ratio (d : PositiveDistanceData) (hQ : 0 < d.Q.side)
    (hs : d.StronglySeparated) {z : Plane × Plane}
    (hx : z.1 ∈ (d.Q.descendant d.X).carrier)
    (hy : z.2 ∈ (d.Q.descendant d.Y).carrier) :
    96 ≤ dist z.1 z.2 / (2:ℝ)^(-(d.a:ℝ)) ∧
    dist z.1 z.2 / (2:ℝ)^(-(d.a:ℝ)) ≤ 2004 := by
  have h := dyadic_strong_separation_endpoints _ _
    (d.Q.descendant_side_pos hQ d.X) (d.Q.descendant_side_pos hQ d.Y)
    hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 hx hy
  exact ⟨(le_div_iff₀ (by positivity)).mpr h.1,
    (div_le_iff₀ (by positivity)).mpr h.2⟩

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_Bins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set

theorem diagonal_bin_mass_le {ι : Type*} [Countable ι]
    (μ : Measure ℝ) [IsFiniteMeasure μ] (I : ι → Set ℝ)
    (hmeas : ∀ i, MeasurableSet (I i))
    (hdisj : Pairwise fun i j => Disjoint (I i) (I j)) (w : ℝ)
    (hdiam : ∀ i x, x ∈ I i → ∀ y, y ∈ I i → |x-y| ≤ w) :
    (∑' i, (μ (I i))^2) ≤ (μ.prod μ) {z : ℝ × ℝ | |z.1-z.2| ≤ w} := by
  have hd : Pairwise fun i j => Disjoint (I i ×ˢ I i) (I j ×ˢ I j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro z hi hj
    exact Set.disjoint_left.mp (hdisj hij) hi.1 hj.1
  calc
    (∑' i, (μ (I i))^2) = ∑' i, (μ.prod μ) (I i ×ˢ I i) := by
      simp only [Measure.prod_prod, pow_two]
    _ = (μ.prod μ) (⋃ i, I i ×ˢ I i) :=
      (measure_iUnion hd (fun i => (hmeas i).prod (hmeas i))).symm
    _ ≤ (μ.prod μ) {z : ℝ × ℝ | |z.1-z.2| ≤ w} := by
      apply measure_mono
      intro z hz
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hz
      exact hdiam i z.1 hi.1 z.2 hi.2

theorem realBin_measurable (w : ℝ) (j : ℤ) : MeasurableSet (realBin w j) :=
  measurableSet_Ico

theorem realBin_disjoint {w : ℝ} (hw : 0 < w) :
    Pairwise fun i j => Disjoint (realBin w i) (realBin w j) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with h | h
  · have hc : ((i+1 : ℤ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast (show i+1 ≤ j by omega)
    have hm := mul_le_mul_of_nonneg_right hc hw.le
    exact (not_lt_of_ge (hxj.1.trans' hm)) hxi.2
  · have hc : ((j+1 : ℤ) : ℝ) ≤ (i : ℝ) := by exact_mod_cast (show j+1 ≤ i by omega)
    have hm := mul_le_mul_of_nonneg_right hc hw.le
    exact (not_lt_of_ge (hxi.1.trans' hm)) hxj.2

theorem realBin_diameter (w : ℝ) (j : ℤ) {x y : ℝ}
    (hx : x ∈ realBin w j) (hy : y ∈ realBin w j) : |x-y| ≤ w := by
  simp only [realBin, Set.mem_Ico, Int.cast_add, Int.cast_one] at hx hy
  apply abs_le.mpr
  constructor <;> nlinarith

theorem real_bin_collision_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    {w : ℝ} (hw : 0 < w) :
    (∑' j : ℤ, (μ (realBin w j))^2) ≤
      (μ.prod μ) {z : ℝ × ℝ | |z.1-z.2| ≤ w} :=
  diagonal_bin_mass_le μ (realBin w) (realBin_measurable w) (realBin_disjoint hw) w
    (fun j _ hx _ hy => realBin_diameter w j hx hy)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_BinOffsets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

 theorem ennreal_offset_cauchy (a b : ℤ → ℝ≥0∞) (h : ℤ) :
    (∑' j : ℤ, a j*b (j-h)) ≤
      (∑' j : ℤ, (a j)^2)^(1/2 : ℝ) * (∑' j : ℤ, (b j)^2)^(1/2 : ℝ) := by
  have hpq : (2:ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]; norm_num
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq (Measure.count : Measure ℤ) hpq
    (measurable_of_countable a).aemeasurable
    (measurable_of_countable (fun j => b (j-h))).aemeasurable
  simp only [lintegral_count, ENNReal.rpow_two] at hh
  have he : (∑' j : ℤ, (b (j-h))^2) = ∑' j : ℤ, (b j)^2 :=
    (Equiv.subRight h).tsum_eq (fun j => (b j)^2)
  simpa only [one_div, he, Pi.mul_apply] using hh

 theorem realBin_cover {w : ℝ} (hw : 0 < w) (x : ℝ) :
    x ∈ realBin w ⌊x/w⌋ := by
  constructor
  · exact (le_div_iff₀ hw).mp (Int.floor_le (x/w))
  · simpa only [Int.cast_add,Int.cast_one] using
      (div_lt_iff₀ hw).mp (Int.lt_floor_add_one (x/w))

 theorem offset_rectangles_mass_le (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (w : ℝ) (h : ℤ) :
    (μ.prod ν) (⋃ j : ℤ, realBin w j ×ˢ realBin w (j-h)) ≤
      binL2Norm μ w * binL2Norm ν w := by
  apply (measure_iUnion_le _).trans
  simp only [Measure.prod_prod]
  exact ennreal_offset_cauchy (fun j => μ (realBin w j)) (fun j => ν (realBin w j)) h

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_BinBands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

 theorem realBin_band_offset {w C s₀ x y : ℝ} (hw : 0 < w)
    (hb : |x-y-s₀| ≤ C*w) {i j : ℤ}
    (hi : x ∈ realBin w i) (hj : y ∈ realBin w j) :
    i-j-⌊s₀/w⌋ ∈ bandOffsets C := by
  have hi1 : (i:ℝ) ≤ x/w := (le_div_iff₀ hw).mpr hi.1
  have hi2 : x/w < (i:ℝ)+1 := by
    simpa only [Int.cast_add,Int.cast_one] using (div_lt_iff₀ hw).mpr hi.2
  have hj1 : (j:ℝ) ≤ y/w := (le_div_iff₀ hw).mpr hj.1
  have hj2 : y/w < (j:ℝ)+1 := by
    simpa only [Int.cast_add,Int.cast_one] using (div_lt_iff₀ hw).mpr hj.2
  have hm1 := Int.floor_le (s₀/w)
  have hm2 := Int.lt_floor_add_one (s₀/w)
  have hb' : |x/w-y/w-s₀/w| ≤ C := by
    rw [← sub_div,← sub_div,abs_div,abs_of_pos hw]
    exact (div_le_iff₀ hw).mpr hb
  obtain ⟨hl,hu⟩ := abs_le.mp hb'
  have hC := Nat.le_ceil C
  apply Finset.mem_Icc.mpr
  constructor
  · have h : -((⌈C⌉₊:ℕ):ℝ)-2 ≤ (i:ℝ)-(j:ℝ)-(⌊s₀/w⌋:ℝ) := by linarith
    exact_mod_cast h
  · have h : (i:ℝ)-(j:ℝ)-(⌊s₀/w⌋:ℝ) ≤ ((⌈C⌉₊:ℕ):ℝ)+2 := by linarith
    exact_mod_cast h

 theorem real_bin_shifted_band_bound (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {w : ℝ} (hw : 0 < w) (C s₀ : ℝ) :
    (μ.prod ν) {z : ℝ × ℝ | |z.1-z.2-s₀| ≤ C*w} ≤
      ((bandOffsets C).card : ℝ≥0∞) * (binL2Norm μ w * binL2Norm ν w) := by
  let m : ℤ := ⌊s₀/w⌋
  have hs : {z : ℝ × ℝ | |z.1-z.2-s₀| ≤ C*w} ⊆
      ⋃ h ∈ bandOffsets C, ⋃ j : ℤ, realBin w j ×ˢ realBin w (j-(h+m)) := by
    intro z hz
    let i : ℤ := ⌊z.1/w⌋
    let j : ℤ := ⌊z.2/w⌋
    have hi := realBin_cover hw z.1
    have hj := realBin_cover hw z.2
    refine mem_iUnion.mpr ⟨i-j-m,mem_iUnion.mpr ⟨realBin_band_offset hw hz hi hj,?_⟩⟩
    apply mem_iUnion.mpr
    refine ⟨i,hi,?_⟩
    have he : i-(i-j-m+m)=j := by omega
    simpa only [he] using hj
  calc
    _ ≤ (μ.prod ν) (⋃ h ∈ bandOffsets C, ⋃ j : ℤ,
        realBin w j ×ˢ realBin w (j-(h+m))) := measure_mono hs
    _ ≤ ∑ h ∈ bandOffsets C, (μ.prod ν) (⋃ j : ℤ,
        realBin w j ×ˢ realBin w (j-(h+m))) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _h ∈ bandOffsets C, binL2Norm μ w * binL2Norm ν w :=
      Finset.sum_le_sum (fun h _ => offset_rectangles_mass_le μ ν w (h+m))
    _ = _ := by simp

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_BinEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

theorem binL2Norm_mul_self (μ : Measure ℝ) (w : ℝ) :
    binL2Norm μ w * binL2Norm μ w = ∑' j : ℤ, (μ (realBin w j))^2 := by
  unfold binL2Norm
  rw [← ENNReal.rpow_add_of_nonneg (1/2) (1/2) (by norm_num) (by norm_num)]
  norm_num

theorem real_bin_shifted_self_band_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    {w : ℝ} (hw : 0 < w) (C s₀ : ℝ) :
    (μ.prod μ) {z : ℝ × ℝ | |z.1-z.2-s₀| ≤ C*w} ≤
      ((bandOffsets C).card : ℝ≥0∞) *
        (μ.prod μ) {z : ℝ × ℝ | |z.1-z.2| ≤ w} := by
  have h := real_bin_shifted_band_bound μ μ hw C s₀
  rw [binL2Norm_mul_self] at h
  exact h.trans (mul_le_mul_right (real_bin_collision_bound μ hw) _)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_PositiveDistanceBins
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
namespace PositiveDistanceData

theorem width_pos (d : PositiveDistanceData) : 0 < d.width := by
  unfold width; positivity

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_PairCollisionTonelli
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem four_pair_lintegral_regroup (μ ν : Measure Plane)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (F : (Plane × Plane) × (Plane × Plane) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F z ∂(μ.prod ν).prod (μ.prod ν)) =
      ∫⁻ xx, ∫⁻ yy, F ((xx.1,yy.1),(xx.2,yy.2)) ∂ν.prod ν ∂μ.prod μ := by
  calc
    _ = ∫⁻ x, ∫⁻ y, ∫⁻ x', ∫⁻ y', F ((x,y),(x',y')) ∂ν ∂μ ∂ν ∂μ := by
      rw [lintegral_prod _ hF.aemeasurable,
        lintegral_prod _ hF.lintegral_prod_right'.aemeasurable]
      apply lintegral_congr
      intro x
      apply lintegral_congr
      intro y
      exact lintegral_prod _ ((hF.comp (by fun_prop)).aemeasurable)
    _ = ∫⁻ x, ∫⁻ x', ∫⁻ y, ∫⁻ y', F ((x,y),(x',y')) ∂ν ∂ν ∂μ ∂μ := by
      apply lintegral_congr
      intro x
      apply lintegral_lintegral_swap
      have hm : Measurable (fun z : (Plane × Plane) × Plane => F ((x,z.1.1),(z.1.2,z.2))) :=
        hF.comp (by fun_prop)
      exact hm.lintegral_prod_right'.aemeasurable
    _ = _ := by
      have hm : Measurable (fun z : (Plane × Plane) × (Plane × Plane) =>
          F ((z.1.1,z.2.1),(z.1.2,z.2.2))) := hF.comp (by fun_prop)
      rw [lintegral_prod _ hm.lintegral_prod_right'.aemeasurable]
      apply lintegral_congr
      intro x
      apply lintegral_congr
      intro x'
      exact (lintegral_prod (fun yy : Plane × Plane => F ((x,yy.1),(x',yy.2)))
        ((hF.comp (by fun_prop)).aemeasurable)).symm

theorem pair_collision_fiber_bound (μ ν : Measure Plane)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (S : Set ((Plane × Plane) × (Plane × Plane))) (hS : MeasurableSet S)
    (K : ℝ≥0∞)
    (hbound : ∀ᵐ xx ∂μ.prod μ,
      (ν.prod ν) {yy | ((xx.1,yy.1),(xx.2,yy.2)) ∈ S} ≤ K) :
    ((μ.prod ν).prod (μ.prod ν)) S ≤ (μ univ)^2*K := by
  have hm : Measurable (S.indicator (fun _ => (1:ℝ≥0∞))) := measurable_const.indicator hS
  have he := four_pair_lintegral_regroup μ ν _ hm
  rw [lintegral_indicator hS,lintegral_const] at he
  simp only [one_mul,Measure.restrict_apply_univ] at he
  have hinner (xx : Plane × Plane) :
      (∫⁻ yy, S.indicator (fun _ => (1:ℝ≥0∞)) ((xx.1,yy.1),(xx.2,yy.2)) ∂ν.prod ν) =
      (ν.prod ν) {yy | ((xx.1,yy.1),(xx.2,yy.2)) ∈ S} := by
    change (∫⁻ yy, {yy : Plane × Plane | ((xx.1,yy.1),(xx.2,yy.2)) ∈ S}.indicator
      (fun _ => (1:ℝ≥0∞)) yy ∂ν.prod ν) = _
    have hmeas : MeasurableSet {yy : Plane × Plane | ((xx.1,yy.1),(xx.2,yy.2)) ∈ S} :=
      hS.preimage (show Measurable (fun yy : Plane × Plane => ((xx.1,yy.1),(xx.2,yy.2))) by fun_prop)
    rw [lintegral_indicator hmeas]
    simp
  simp_rw [hinner] at he
  rw [he]
  calc
    _ ≤ ∫⁻ _xx, K ∂μ.prod μ := lintegral_mono_ae hbound
    _ = _ := by
      rw [lintegral_const,← univ_prod_univ,Measure.prod_prod]
      simp only [pow_two,mul_comm]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_ProjectionShiftedBand
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem projection_shifted_band_bound (μ : Measure Plane) [IsFiniteMeasure μ]
    (e : Plane) {w : ℝ} (hw : 0 < w) (C s : ℝ) :
    (μ.prod μ) {z : Plane × Plane | |planeDot (z.1-z.2) e-s| ≤ C*w} ≤
      ((bandOffsets C).card : ℝ≥0∞) *
        (μ.prod μ) {z : Plane × Plane | |planeDot (z.1-z.2) e| ≤ w} := by
  let f : Plane → ℝ := fun y => planeDot y e
  have hf : Measurable f := by dsimp [f,planeDot]; fun_prop
  let ν := Measure.map f μ
  have he (v s : ℝ) :
      (ν.prod ν) {z : ℝ × ℝ | |z.1-z.2-s| ≤ v} =
      (μ.prod μ) {z : Plane × Plane | |planeDot (z.1-z.2) e-s| ≤ v} := by
    rw [show ν.prod ν = Measure.map (Prod.map f f) (μ.prod μ) from
      Measure.map_prod_map μ μ hf hf,Measure.map_apply (hf.prodMap hf) (by measurability)]
    congr 1
    ext z
    have hdot : f z.1-f z.2 = planeDot (z.1-z.2) e := by simp [f,planeDot]; ring
    change |f z.1-f z.2-s| ≤ v ↔ _
    rw [hdot]
    rfl
  have h := real_bin_shifted_self_band_bound ν hw C s
  rw [he] at h
  have hz := he w 0
  simp only [sub_zero] at hz
  rwa [hz] at h

theorem affine_distance_collision {x x' y y' e : Plane} {w : ℝ}
    (hx : |dist x y-planeDot (x-y) e| ≤ w)
    (hx' : |dist x' y'-planeDot (x'-y') e| ≤ w)
    (hc : |dist x y-dist x' y'| ≤ w) :
    |planeDot (y-y') e-planeDot (x-x') e| ≤ 3*w := by
  have he : planeDot (y-y') e-planeDot (x-x') e =
      -(planeDot (x-y) e-planeDot (x'-y') e) := by simp [planeDot]; ring
  rw [he,abs_neg]
  obtain ⟨h₁,h₂⟩ := abs_le.mp hx
  obtain ⟨h₃,h₄⟩ := abs_le.mp hx'
  obtain ⟨h₅,h₆⟩ := abs_le.mp hc
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_LocalDistanceCollision
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem local_distance_collision_bound (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (P Q : DyadicSquare) (e : Plane) {w : ℝ} (hw : 0 < w)
    (haff : ∀ x ∈ P.carrier, ∀ y ∈ Q.carrier, |dist x y-planeDot (x-y) e| ≤ w)
    {H : ℝ≥0∞}
    (hproj : ((ρ.restrict Q.carrier).prod (ρ.restrict Q.carrier))
      {z : Plane × Plane | |planeDot (z.1-z.2) e| ≤ w} ≤ H) :
    (((ρ.restrict P.carrier).prod (ρ.restrict Q.carrier)).prod
      ((ρ.restrict P.carrier).prod (ρ.restrict Q.carrier)))
        {z | |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ w} ≤
      (ρ P.carrier)^2 * (((bandOffsets 3).card : ℝ≥0∞)*H) := by
  apply (pair_collision_fiber_bound (ρ.restrict P.carrier) (ρ.restrict Q.carrier)
    _ (by measurability) (((bandOffsets 3).card : ℝ≥0∞)*H) ?_).trans_eq (by simp)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem P.measurable),
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem P.measurable)] with xx hx hx'
  apply le_trans _ (mul_le_mul' le_rfl hproj)
  apply le_trans _ (projection_shifted_band_bound (ρ.restrict Q.carrier) e hw 3
    (planeDot (xx.1-xx.2) e))
  apply measure_mono_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem Q.measurable),
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem Q.measurable)] with yy hy hy'
  intro hc
  exact affine_distance_collision (haff xx.1 hx yy.1 hy) (haff xx.2 hx' yy.2 hy') hc

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_DyadicIntegralSplitting
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem DyadicSquare.biUnion_descendants (Q : DyadicSquare) (hQ : 0 < Q.side)
    (n : ℕ) : (⋃ P ∈ dyadicPaths n, (Q.descendant P).carrier) = Q.carrier := by
  ext x
  constructor
  · intro hx
    obtain ⟨P, _, hx⟩ := mem_iUnion₂.mp hx
    exact Q.descendant_subset hQ P hx
  · intro hx
    obtain ⟨P, hP, hxP⟩ := Q.mem_descendant_at_depth n hx
    exact mem_iUnion₂.mpr ⟨P, hP, hxP⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_DyadicMeasureSplitting
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

 theorem DyadicSquare.measure_split_occupied (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) (n : ℕ) :
    ρ.restrict Q.carrier =
      ∑ P ∈ occupiedAnchorPaths Q ρ n, ρ.restrict (Q.descendant P).carrier := by
  classical
  have hall : ρ.restrict Q.carrier =
      ∑ P ∈ dyadicPaths n, ρ.restrict (Q.descendant P).carrier := by
    rw [← Q.biUnion_descendants hQ n]
    rw [Measure.restrict_biUnion_finset]
    · rw [Measure.sum_fintype]
      exact Finset.sum_coe_sort (dyadicPaths n) (fun P => ρ.restrict (Q.descendant P).carrier)
    · intro P hP S hS hne
      exact Q.descendants_disjoint hQ
        (((mem_dyadicPaths n P).mp hP).trans ((mem_dyadicPaths n S).mp hS).symm) hne
    · exact fun P => (Q.descendant P).measurable
  rw [hall]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro P hP hnot
  apply Measure.restrict_eq_zero.mpr
  by_contra hne
  exact hnot (Finset.mem_filter.mpr ⟨hP,bot_lt_iff_ne_bot.mpr hne⟩)

 theorem occupied_absolute_measure_sum (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) (A : CellPath) (n : ℕ) :
    (∑ P ∈ (occupiedAnchorPaths (Q.descendant A) ρ n).image (fun c => A++c),
      ρ.restrict (Q.descendant P).carrier) = ρ.restrict (Q.descendant A).carrier := by
  classical
  rw [Finset.sum_image (fun _ _ _ _ he => List.append_cancel_left he)]
  simp only [DyadicSquare.descendant_append]
  exact ((Q.descendant A).measure_split_occupied (Q.descendant_side_pos hQ A) ρ n).symm

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_NormAffineRemainder
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem norm_affine_remainder (v u : Plane) (hu : u ≠ 0) :
    |‖v‖-planeDot v (‖u‖⁻¹ • u)| ≤ ‖v-u‖^2/(2*‖u‖) := by
  have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hnonneg : 0 ≤ ‖v‖-planeDot v (‖u‖⁻¹ • u) := by
    have h := (le_abs_self (planeDot v (‖u‖⁻¹ • u))).trans (planeDot_abs_le _ _)
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hupos),
      inv_mul_cancel₀ hupos.ne',mul_one] at h
    linarith
  have hdot : ‖u‖*planeDot v (‖u‖⁻¹ • u) = planeDot v u := by
    simp only [planeDot,PiLp.smul_apply,smul_eq_mul]
    field_simp
  have hi : inner ℝ v u = planeDot v u := by
    simp [planeDot,EuclideanSpace.inner_eq_star_dotProduct,Fin.sum_univ_two,dotProduct,mul_comm]
  have he := norm_sub_sq_real v u
  rw [hi] at he
  rw [abs_of_nonneg hnonneg]
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith [sq_nonneg (‖v‖-‖u‖)]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_ProjectionCellPartition
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem projectionTestCells_eq_image (Q : DyadicSquare) (ρ : Measure Plane)
    {p u : ℕ} (hpu : p ≤ u) {P : CellPath} (hP : P.length = p) :
    projectionTestCells Q ρ p u P =
      (occupiedAnchorPaths (Q.descendant P) ρ (u-p)).image (fun c => P++c) := by
  classical
  ext C
  constructor
  · intro hC
    obtain ⟨hC,hpos,htake⟩ := Finset.mem_filter.mp hC
    have hlen := (mem_dyadicPaths _ _).mp hC
    refine Finset.mem_image.mpr ⟨C.drop p,?_,?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨(mem_dyadicPaths _ _).mpr (by simp [hlen]),?_⟩
      simpa only [← Q.descendant_append,← htake,List.take_append_drop] using hpos
    · rw [← htake,List.take_append_drop]
  · intro hmem
    obtain ⟨D,hD,rfl⟩ := Finset.mem_image.mp hmem
    obtain ⟨hD,hpos⟩ := Finset.mem_filter.mp hD
    have hlen := (mem_dyadicPaths _ _).mp hD
    apply Finset.mem_filter.mpr
    refine ⟨(mem_dyadicPaths _ _).mpr (by simp [hP,hlen,Nat.add_sub_of_le hpu]),?_,?_⟩
    · simpa only [Q.descendant_append] using hpos
    · simpa only [← hP] using (List.take_left : (P++D).take P.length = P)

theorem projection_measure_split (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) {p u : ℕ} (hpu : p ≤ u)
    {P : CellPath} (hP : P.length = p) :
    ρ.restrict (Q.descendant P).carrier =
      ∑ C ∈ projectionTestCells Q ρ p u P, ρ.restrict (Q.descendant C).carrier := by
  rw [projectionTestCells_eq_image Q ρ hpu hP]
  exact (occupied_absolute_measure_sum Q hQ ρ P (u-p)).symm

theorem ae_projection_cell (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) {p u : ℕ} (hpu : p ≤ u)
    {P : CellPath} (hP : P.length = p) :
    ∀ᵐ x ∂ρ.restrict (Q.descendant P).carrier,
      ∃ C ∈ projectionTestCells Q ρ p u P, x ∈ (Q.descendant C).carrier := by
  rw [projection_measure_split Q hQ ρ hpu hP]
  apply ae_finsetSum_measure_iff.mpr
  intro C hC
  filter_upwards [ae_restrict_mem (Q.descendant C).measurable] with x hx
  exact ⟨C,hC,hx⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_ProjectionCollisionCount
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem projection_center_replacement (Q : DyadicSquare) (hQ : 0 < Q.side)
    {u : ℕ} {C D : CellPath} (hC : C.length = u) (hD : D.length = u)
    {x y ω : Plane} (hx : x ∈ (Q.descendant C).carrier)
    (hy : y ∈ (Q.descendant D).carrier) (hω : ‖ω‖ ≤ 1) :
    |planeDot ((Q.descendant C).center-(Q.descendant D).center) ω| ≤
      |planeDot (x-y) ω|+4*Q.side/(2:ℝ)^u := by
  have he : planeDot ((Q.descendant C).center-(Q.descendant D).center) ω =
      planeDot (x-y) ω +
      planeDot (((Q.descendant C).center-x)-((Q.descendant D).center-y)) ω := by
    simp [planeDot]; ring
  have hc := (Q.descendant C).dist_le (Q.descendant_side_pos hQ C).le
    ((Q.descendant C).center_mem (Q.descendant_side_pos hQ C)) hx
  have hd := (Q.descendant D).dist_le (Q.descendant_side_pos hQ D).le
    ((Q.descendant D).center_mem (Q.descendant_side_pos hQ D)) hy
  rw [dist_eq_norm,Q.descendant_side,hC] at hc
  rw [dist_eq_norm,Q.descendant_side,hD] at hd
  have hnorm : ‖((Q.descendant C).center-x)-((Q.descendant D).center-y)‖ ≤
      4*Q.side/(2:ℝ)^u := by
    exact (norm_sub_le _ _).trans ((add_le_add hc hd).trans_eq (by ring))
  rw [he]
  apply (abs_add_le _ _).trans
  apply add_le_add le_rfl
  exact (planeDot_abs_le _ _).trans
    ((mul_le_mul_of_nonneg_left hω (norm_nonneg _)).trans (by simpa using hnorm))

theorem projection_collision_le_count (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) [IsFiniteMeasure ρ] {p u : ℕ} (hpu : p ≤ u)
    {P : CellPath} (hP : P.length = p) {ω : Plane} (hω : ‖ω‖ ≤ 1)
    (w : ℝ) {H : ℝ≥0∞}
    (hm : ∀ C ∈ projectionTestCells Q ρ p u P, ρ (Q.descendant C).carrier ≤ H) :
    ((ρ.restrict (Q.descendant P).carrier).prod (ρ.restrict (Q.descendant P).carrier))
      {z : Plane × Plane | |planeDot (z.1-z.2) ω| ≤ w} ≤
      (projectionTestCount Q ρ p u P (w+4*Q.side/(2:ℝ)^u) ω : ℝ≥0∞)*H^2 := by
  classical
  let S := projectionTestCells Q ρ p u P
  let T := (S.product S).filter fun cc =>
    |planeDot ((Q.descendant cc.1).center-(Q.descendant cc.2).center) ω| ≤
      w+4*Q.side/(2:ℝ)^u
  let μ := ρ.restrict (Q.descendant P).carrier
  have hcover : ∀ᵐ z ∂μ.prod μ,
      |planeDot (z.1-z.2) ω| ≤ w →
        z ∈ ⋃ cc ∈ T, (Q.descendant cc.1).carrier ×ˢ (Q.descendant cc.2).carrier := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_projection_cell Q hQ ρ hpu hP),
      Measure.quasiMeasurePreserving_snd.ae (ae_projection_cell Q hQ ρ hpu hP)] with z hx hy
    intro hz
    obtain ⟨C,hC,hx⟩ := hx
    obtain ⟨D,hD,hy⟩ := hy
    refine mem_iUnion₂.mpr ⟨(C,D),?_,hx,hy⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hC,hD⟩,?_⟩
    exact (projection_center_replacement Q hQ
      ((mem_dyadicPaths _ _).mp (Finset.mem_filter.mp hC).1)
      ((mem_dyadicPaths _ _).mp (Finset.mem_filter.mp hD).1) hx hy hω).trans
      (add_le_add hz le_rfl)
  calc
    _ ≤ (μ.prod μ) (⋃ cc ∈ T, (Q.descendant cc.1).carrier ×ˢ (Q.descendant cc.2).carrier) :=
      measure_mono_ae hcover
    _ ≤ ∑ cc ∈ T, (μ.prod μ) ((Q.descendant cc.1).carrier ×ˢ (Q.descendant cc.2).carrier) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _cc ∈ T, H^2 := by
      apply Finset.sum_le_sum
      intro cc hcc
      have hc := Finset.mem_product.mp (Finset.mem_filter.mp hcc).1
      rw [Measure.prod_prod]
      exact (mul_le_mul' (Measure.restrict_apply_le _ _) (Measure.restrict_apply_le _ _)).trans
        (by simpa only [pow_two] using mul_le_mul' (hm _ hc.1) (hm _ hc.2))
    _ = _ := by simp [projectionTestCount,stripCount,T,S]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_ProfileProjectionCollision
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem profile_projection_collision (Q : DyadicSquare) (hQ : Q.side = 1)
    (ρ : Measure Plane) {N B p u J i : ℕ} {δ lam sig : ℝ} {m : ℝ → ℝ}
    (hprof : RegularizedProfileData Q ρ N B δ lam m)
    (hpu : p ≤ u) (hu : u ≤ N) {P : CellPath} (hP : P.length = p)
    {ω e : UnitCircle} {w d : ℝ} (hd : dist (ω:Plane) (e:Plane) ≤ d)
    (hgap : w+4/(2:ℝ)^u+(2/(2:ℝ)^p)*d ≤ sourceAngularWidth N sig J i u)
    (hgood : ω ∈ descriptorGoodSet Q ρ m N lam sig J i P (.projection p u)) :
    ((ρ.restrict (Q.descendant P).carrier).prod (ρ.restrict (Q.descendant P).carrier))
      {z : Plane × Plane | |planeDot (z.1-z.2) (e:Plane)| ≤ w} ≤
      (ρ (Q.descendant P).carrier)^2 * ENNReal.ofReal (((2:ℝ)^N)^
        (-(m u-m p)+height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) p u+
          2000*(lam+sig)+12*lam)) := by
  have := hprof.probability
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  by_cases hz : ρ (Q.descendant P).carrier = 0
  · simp [Measure.restrict_eq_zero.mpr hz,hz]
  have hpos : 0 < ρ (Q.descendant P).carrier := bot_lt_iff_ne_bot.mpr hz
  let R : ℝ := (2:ℝ)^N
  let k : ℝ := height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) p u
  have hR : 0 < R := by dsimp [R]; positivity
  let H : ℝ := R^(3*lam)*R^(-m u)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hcount : (projectionTestCount Q ρ p u P (w+4*Q.side/(2:ℝ)^u) (e:Plane):ℝ) ≤
      R^(m u-m p+k+2000*(lam+sig)) := by
    apply le_trans (Nat.cast_le.mpr (projectionTestCount_transfer Q hside ρ p u hP hd ?_)) hgood
    simpa only [hQ,mul_one] using hgap
  have hbound := projection_collision_le_count Q hside ρ hpu hP (by simpa using e.property.le) w
    (H := ENNReal.ofReal H) (fun C hC => by
      have hc := hprof.cells u hu C ((mem_dyadicPaths _ _).mp (Finset.mem_filter.mp hC).1)
        (Finset.mem_filter.mp hC).2.1
      rw [← ENNReal.ofReal_toReal (measure_ne_top ρ _)]
      exact ENNReal.ofReal_le_ofReal hc.2)
  have hcoarse := (hprof.cells p (hpu.trans hu) P hP hpos).1
  have hsq : (R^(-3*lam)*R^(-m p))^2 ≤ (ρ (Q.descendant P).carrier).toReal^2 :=
    pow_le_pow_left₀ (by positivity) hcoarse 2
  have he : R^(m u-m p+k+2000*(lam+sig))*H^2 =
      (R^(-3*lam)*R^(-m p))^2 * R^(-(m u-m p)+k+2000*(lam+sig)+12*lam) := by
    dsimp [H]
    simp only [pow_two,← Real.rpow_add hR]
    congr 1
    ring
  calc
    _ ≤ _ := hbound
    _ ≤ ENNReal.ofReal (R^(m u-m p+k+2000*(lam+sig)))*ENNReal.ofReal H^2 := by
      apply mul_le_mul' _ le_rfl
      have hh := ENNReal.ofReal_le_ofReal hcount
      simpa only [ENNReal.ofReal_natCast] using hh
    _ = ENNReal.ofReal (R^(m u-m p+k+2000*(lam+sig))*H^2) := by
      rw [← ENNReal.ofReal_pow hH,← ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _)]
    _ ≤ ENNReal.ofReal ((ρ (Q.descendant P).carrier).toReal^2 *
        R^(-(m u-m p)+k+2000*(lam+sig)+12*lam)) := by
      rw [he]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hsq (by positivity))
    _ = _ := by
      rw [ENNReal.ofReal_mul (sq_nonneg _),ENNReal.ofReal_pow ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (measure_ne_top ρ _)]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_SuffixProjectionWidths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem sourceAngularWidth_lower (N : ℕ) (sig : ℝ) {J i : ℕ}
    (hJ : 0 < J) (hi : i ≤ J) (u : ℕ) :
    ((2:ℝ)^N)^(1000*sig)/(2:ℝ)^u ≤ sourceAngularWidth N sig J i u := by
  have hj : 0 < (J:ℝ) := by exact_mod_cast hJ
  have hir : (i:ℝ) ≤ (J:ℝ) := by exact_mod_cast hi
  have hcoeff : 1 ≤ 2-(i:ℝ)/(J:ℝ) := by
    have := (div_le_one hj).mpr hir
    linarith
  unfold sourceAngularWidth
  calc
    _ = (1/(2:ℝ)^u)*((2:ℝ)^N)^(1000*sig) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hcoeff (by positivity)) (by positivity)

theorem uniform_suffix_projection_gap {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) (C K : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p u : ℕ, p ≤ u → ∀ i ≤ J,
      K/(2:ℝ)^u+4/(2:ℝ)^u+(2/(2:ℝ)^p)*(C/(2:ℝ)^(u-p)) ≤
        sourceAngularWidth N sig J i u := by
  obtain ⟨N₀,hN₀⟩ := fixed_constant_absorbed (by positivity : 0 < 1000*sig) (K+4+2*C)
  refine ⟨N₀,?_⟩
  intro N hN p u hpu i hi
  have hp : (2:ℝ)^p*(2:ℝ)^(u-p) = (2:ℝ)^u := by
    rw [← pow_add,Nat.add_sub_of_le hpu]
  calc
    _ = (K+4+2*C)/(2:ℝ)^u := by
      rw [div_mul_div_comm, hp]
      ring
    _ ≤ ((2:ℝ)^N)^(1000*sig)/(2:ℝ)^u :=
      div_le_div_of_nonneg_right (hN₀ N hN) (by positivity)
    _ ≤ _ := sourceAngularWidth_lower N sig hJ hi u

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_UniformProjectionCollision
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem uniform_profile_projection_collision {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) (C K : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicSquare), Q.side = 1 →
      ∀ (ρ : Measure Plane) (B : ℕ) (δ lam : ℝ) (m : ℝ → ℝ),
      RegularizedProfileData Q ρ N B δ lam m →
      ∀ p u : ℕ, p ≤ u → u ≤ N → ∀ P : CellPath, P.length = p →
      ∀ i ≤ J, ∀ ω e : UnitCircle,
      dist (ω:Plane) (e:Plane) ≤ C/(2:ℝ)^(u-p) →
      ω ∈ descriptorGoodSet Q ρ m N lam sig J i P (.projection p u) →
      ((ρ.restrict (Q.descendant P).carrier).prod (ρ.restrict (Q.descendant P).carrier))
        {z : Plane × Plane | |planeDot (z.1-z.2) (e:Plane)| ≤ K/(2:ℝ)^u} ≤
        (ρ (Q.descendant P).carrier)^2 * ENNReal.ofReal (((2:ℝ)^N)^
          (-(m u-m p)+height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) p u+
            2000*(lam+sig)+12*lam)) := by
  obtain ⟨N₀,hN₀⟩ := uniform_suffix_projection_gap hsig hJ C K
  refine ⟨N₀,?_⟩
  intro N hN Q hQ ρ B δ lam m hprof p u hpu hu P hP i hi ω e hd hg
  exact profile_projection_collision Q hQ ρ hprof hpu hu hP hd
    (hN₀ N hN p u hpu i hi) hg

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_SuffixDescriptors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set

theorem suffix_projection_mem (A : ℕ → ℝ) {N q a t : ℕ}
    (ht : t ≤ N) (hw : a+100*q < t)
    (hs : a+t < 2*policyDepth A N q a t) :
    PolicyDescriptor.projection (policyDepth A N q a t) t ∈
      policyDescriptorList A N q a t := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨(a,t),?_,?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr (by omega)⟩,
      le_rfl,le_rfl,hw⟩
  · apply Finset.mem_union_right
    simp [hs]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_SuffixDirectionGeometry
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set

theorem fine_cell_direction_dist (P Q : DyadicSquare)
    (hP : 0 < P.side) (hQ : 0 < Q.side) {a p : ℕ}
    (hp : P.side ≤ 1/(2:ℝ)^p) (hq : Q.side ≤ 1/(2:ℝ)^p)
    {x y x' y' : Plane} (hx : x ∈ P.carrier) (hy : y ∈ Q.carrier)
    (hx' : x' ∈ P.carrier) (hy' : y' ∈ Q.carrier)
    (hs : 96/(2:ℝ)^a ≤ dist x y) (hne : x' ≠ y') :
    dist (sourceRadialUnit y x) (sourceRadialUnit y' x') ≤ (2:ℝ)^a/(2:ℝ)^p := by
  have hdist : 0 < dist x y := (by positivity : 0 < 96/(2:ℝ)^a).trans_le hs
  have hxy : x ≠ y := dist_pos.mp hdist
  have hb := endpoint_direction_dist_le hxy hne
  rw [dist_comm y x] at hb
  have hxmove := P.dist_le hP.le hx hx'
  have hymove := Q.dist_le hQ.le hy hy'
  have hnum : 2*(dist y y'+dist x x') ≤ 8/(2:ℝ)^p := by
    calc
      _ ≤ 2*(2*Q.side+2*P.side) :=
        mul_le_mul_of_nonneg_left (add_le_add hymove hxmove) (by norm_num)
      _ ≤ 2*(2*(1/(2:ℝ)^p)+2*(1/(2:ℝ)^p)) := by gcongr
      _ = _ := by ring
  have hscale : 8/(2:ℝ)^p/(96/(2:ℝ)^a) ≤ (2:ℝ)^a/(2:ℝ)^p := by
    have hratio : 0 < (2:ℝ)^a/(2:ℝ)^p := by positivity
    have he : 8/(2:ℝ)^p/(96/(2:ℝ)^a) = ((2:ℝ)^a/(2:ℝ)^p)/12 := by field_simp; ring
    rw [he]
    linarith only [hratio]
  exact hb.trans ((div_le_div₀ (by positivity) hnum (by positivity) hs).trans hscale)

namespace PositiveDistanceData

theorem fine_endpoints_separated (d : PositiveDistanceData) (hQ : 0 < d.Q.side)
    (hs : d.StronglySeparated) {P C : CellPath}
    (hP : P.take d.a = d.X) (hC : C.take d.a = d.Y)
    {x y : Plane} (hx : x ∈ (d.Q.descendant P).carrier)
    (hy : y ∈ (d.Q.descendant C).carrier) :
    96/(2:ℝ)^d.a ≤ dist x y := by
  have hh := (d.separated_distance_ratio hQ hs (z := (x,y))
    (hP ▸ d.Q.descendant_subset_take hQ P d.a hx)
    (hC ▸ d.Q.descendant_subset_take hQ C d.a hy)).1
  have hh' := (le_div_iff₀ (by positivity : 0 < (2:ℝ)^(-(d.a:ℝ)))).mp hh
  simpa only [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,div_eq_mul_inv] using hh'

theorem fine_directions (d : PositiveDistanceData) (hQ : d.Q.side = 1)
    (hs : d.StronglySeparated) {p : ℕ} {P C : CellPath}
    (hP : P.length = p) (hC : C.length = p)
    (hPX : P.take d.a = d.X) (hCY : C.take d.a = d.Y)
    {x y x' y' : Plane} (hx : x ∈ (d.Q.descendant P).carrier)
    (hy : y ∈ (d.Q.descendant C).carrier)
    (hx' : x' ∈ (d.Q.descendant P).carrier) (hy' : y' ∈ (d.Q.descendant C).carrier) :
    dist (sourceRadialUnit y x) (sourceRadialUnit y' x') ≤ (2:ℝ)^d.a/(2:ℝ)^p := by
  have hside : 0 < d.Q.side := by rw [hQ]; norm_num
  have hs' := d.fine_endpoints_separated hside hs hPX hCY hx' hy'
  exact fine_cell_direction_dist _ _ (d.Q.descendant_side_pos hside P)
    (d.Q.descendant_side_pos hside C)
    (by simp only [DyadicSquare.descendant_side,hQ,hP,le_refl])
    (by simp only [DyadicSquare.descendant_side,hQ,hC,le_refl]) hx hy hx' hy'
    (d.fine_endpoints_separated hside hs hPX hCY hx hy)
    (dist_pos.mp ((by positivity : 0 < 96/(2:ℝ)^d.a).trans_le hs'))

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_ActualSuffixProjection
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem uniform_actual_suffix_projection {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) (K : ℝ) :
    ∃ N₀ : ℕ, ∀ d : PositiveDistanceData, d.sig = sig → d.J = J →
      N₀ ≤ d.N → d.Q.side = 1 → d.StronglySeparated → 0 < d.q →
      ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
      d.a+100*d.q < d.t → d.t ≤ d.N → d.i ≤ J →
      let p := policyDepth (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t
      d.a+d.t < 2*p → ∀ P C : CellPath, P.length = p → C.length = p →
      P.take d.a = d.X → C.take d.a = d.Y →
      ∀ x ∈ (d.Q.descendant P).carrier, ∀ y ∈ (d.Q.descendant C).carrier,
      (x,y) ∈ d.good →
      ((d.ρ.restrict (d.Q.descendant C).carrier).prod (d.ρ.restrict (d.Q.descendant C).carrier))
        {z : Plane × Plane | |planeDot (z.1-z.2)
          (sourceRadialUnit (d.Q.descendant C).center (d.Q.descendant P).center : Plane)| ≤
            K/(2:ℝ)^d.t} ≤
        (d.ρ (d.Q.descendant C).carrier)^2 * ENNReal.ofReal (((2:ℝ)^d.N)^
          (-(d.mass d.t-d.mass p)+height (fun n : ℕ => d.mass n-(n:ℝ)/(d.N:ℝ)) p d.t+
            2000*(d.lam+sig)+12*d.lam)) := by
  obtain ⟨N₀,hN₀⟩ := uniform_profile_projection_collision hsig hJ 1 K
  refine ⟨N₀,?_⟩
  intro d hsig' hJ' hN hQ hs hq B δ hprof hw htN hi p hsuffix P C hP hC hPX hCY x hx y hy hg
  have hside : 0 < d.Q.side := by rw [hQ]; norm_num
  have hp := policyDepth_interior (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) hq
    (policyBlocks_nonempty hq htN hw)
  have hpt : p ≤ d.t := by dsimp [p]; omega
  have hmem := suffix_projection_mem (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) htN hw hsuffix
  have hgC := (hg _ hmem).2 C ((mem_dyadicPaths _ _).mpr hC) hy
  have hdir := d.fine_directions hQ hs hP hC hPX hCY hx hy
    ((d.Q.descendant P).center_mem (d.Q.descendant_side_pos hside P))
    ((d.Q.descendant C).center_mem (d.Q.descendant_side_pos hside C))
  have hsmall := hdir.trans (suffix_direction_scale (by omega : d.a+d.t ≤ 2*p) hpt)
  rw [hsig',hJ'] at hgC
  exact hN₀ d.N hN d.Q hQ d.ρ B δ d.lam d.mass hprof p d.t hpt htN C hC
    d.i hi _ _ hsmall hgC

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_SuffixDistanceTaylor
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set

theorem fine_distance_affine_error (P Q : DyadicSquare)
    (hP : 0 < P.side) (hQ : 0 < Q.side) {a p t : ℕ}
    (hp : P.side ≤ 1/(2:ℝ)^p) (hq : Q.side ≤ 1/(2:ℝ)^p)
    (hs : 96/(2:ℝ)^a ≤ dist P.center Q.center) (hst : a+t ≤ 2*p)
    {x y : Plane} (hx : x ∈ P.carrier) (hy : y ∈ Q.carrier) :
    |dist x y-planeDot (x-y) (sourceRadialUnit Q.center P.center : Plane)| ≤ 1/(2:ℝ)^t := by
  have hdist : 0 < dist P.center Q.center := (by positivity : 0 < 96/(2:ℝ)^a).trans_le hs
  have hc : P.center ≠ Q.center := dist_pos.mp hdist
  have hraw := norm_affine_remainder (x-y) (P.center-Q.center) (sub_ne_zero.mpr hc)
  have hmove : ‖(x-y)-(P.center-Q.center)‖ ≤ 4/(2:ℝ)^p := by
    have hh := dist_sub_sub_le x y P.center Q.center
    rw [dist_eq_norm] at hh
    have h₁ := P.dist_le hP.le hx (P.center_mem hP)
    have h₂ := Q.dist_le hQ.le hy (Q.center_mem hQ)
    have hsum : dist x P.center+dist y Q.center ≤ 4/(2:ℝ)^p := by
      calc
        _ ≤ 2*P.side+2*Q.side := add_le_add h₁ h₂
        _ ≤ 2*(1/(2:ℝ)^p)+2*(1/(2:ℝ)^p) := by gcongr
        _ = _ := by ring
    exact hh.trans hsum
  have hbound : ‖(x-y)-(P.center-Q.center)‖^2/(2*‖P.center-Q.center‖) ≤ 1/(2:ℝ)^t := by
    rw [← dist_eq_norm]
    calc
      _ ≤ (4/(2:ℝ)^p)^2/(2*(96/(2:ℝ)^a)) :=
        div_le_div₀ (sq_nonneg _) (pow_le_pow_left₀ (norm_nonneg _) hmove 2)
          (by positivity) (mul_le_mul_of_nonneg_left hs (by norm_num))
      _ = ((2:ℝ)^a/((2:ℝ)^p)^2)/12 := by field_simp; ring
      _ ≤ (2:ℝ)^a/((2:ℝ)^p)^2 := by
        have hh : 0 ≤ (2:ℝ)^a/((2:ℝ)^p)^2 := by positivity
        linarith
      _ ≤ 1/(2:ℝ)^t := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        rw [one_mul,← pow_add,← pow_mul]
        exact pow_le_pow_right₀ (by norm_num) (by omega)
  apply le_trans _ hbound
  simpa only [sourceRadialUnit,sourceRadialVector,ite_eq_right hc,dist_eq_norm] using hraw

namespace PositiveDistanceData

theorem suffix_distance_affine (d : PositiveDistanceData) (hQ : d.Q.side = 1)
    (hs : d.StronglySeparated) {p : ℕ} (hst : d.a+d.t ≤ 2*p)
    {P C : CellPath} (hP : P.length = p) (hC : C.length = p)
    (hPX : P.take d.a = d.X) (hCY : C.take d.a = d.Y)
    {x y : Plane} (hx : x ∈ (d.Q.descendant P).carrier)
    (hy : y ∈ (d.Q.descendant C).carrier) :
    |dist x y-planeDot (x-y)
      (sourceRadialUnit (d.Q.descendant C).center (d.Q.descendant P).center : Plane)| ≤
        1/(2:ℝ)^d.t := by
  have hside : 0 < d.Q.side := by rw [hQ]; norm_num
  exact fine_distance_affine_error _ _ (d.Q.descendant_side_pos hside P)
    (d.Q.descendant_side_pos hside C)
    (by simp only [DyadicSquare.descendant_side,hQ,hP,le_refl])
    (by simp only [DyadicSquare.descendant_side,hQ,hC,le_refl])
    (d.fine_endpoints_separated hside hs hPX hCY
      ((d.Q.descendant P).center_mem (d.Q.descendant_side_pos hside P))
      ((d.Q.descendant C).center_mem (d.Q.descendant_side_pos hside C))) hst hx hy

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_SuffixLocalBins
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
namespace PositiveDistanceData

theorem bin_sq_le_unrestricted_collision (d : PositiveDistanceData) [IsFiniteMeasure d.ρ] :
    (binL2Norm d.distance d.width)^2 ≤
      (d.cellPair.prod d.cellPair) {z | |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ d.width} := by
  rw [pow_two,binL2Norm_mul_self]
  apply (real_bin_collision_bound d.distance d.width_pos).trans
  rw [d.distance_collision]
  exact Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self _

theorem suffix_local_bin_sq (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : d.Q.side = 1) (hs : d.StronglySeparated) {p : ℕ} (hst : d.a+d.t ≤ 2*p)
    {P C : CellPath} (hP : P.length = p) (hC : C.length = p)
    (hPX : P.take d.a = d.X) (hCY : C.take d.a = d.Y) {H : ℝ≥0∞}
    (hproj : ((d.ρ.restrict (d.Q.descendant C).carrier).prod (d.ρ.restrict (d.Q.descendant C).carrier))
      {z : Plane × Plane | |planeDot (z.1-z.2)
        (sourceRadialUnit (d.Q.descendant C).center (d.Q.descendant P).center : Plane)| ≤
          1/(2:ℝ)^d.t} ≤ H) :
    (binL2Norm ({d with X := P,Y := C} : PositiveDistanceData).distance d.width)^2 ≤
      (d.ρ (d.Q.descendant P).carrier)^2 * (((bandOffsets 3).card : ℝ≥0∞)*H) := by
  have hw : d.width = 1/(2:ℝ)^d.t := by
    simp only [width,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,one_div]
  apply (bin_sq_le_unrestricted_collision ({d with X := P,Y := C} : PositiveDistanceData)).trans
  simpa only [cellPair,width,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,one_div]
    using local_distance_collision_bound d.ρ (d.Q.descendant P) (d.Q.descendant C) _
      (by positivity : 0 < 1/(2:ℝ)^d.t)
      (fun x hx y hy => d.suffix_distance_affine hQ hs hst hP hC hPX hCY hx hy) hproj

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_SuffixRetainedPairs
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
namespace PositiveDistanceData

theorem suffix_retained_spec (d : PositiveDistanceData) {p : ℕ} {c : CellPath × CellPath}
    (hc : c ∈ d.suffixRetained p) :
    c.1.length = p ∧ c.2.length = p ∧ c.1.take d.a = d.X ∧ c.2.take d.a = d.Y ∧
      ∃ x ∈ (d.Q.descendant c.1).carrier, ∃ y ∈ (d.Q.descendant c.2).carrier, (x,y) ∈ d.good := by
  classical
  obtain ⟨hc,hw⟩ := Finset.mem_filter.mp hc
  obtain ⟨h₁,h₂⟩ := Finset.mem_product.mp hc
  exact ⟨(mem_dyadicPaths _ _).mp (Finset.mem_filter.mp h₁).1,
    (mem_dyadicPaths _ _).mp (Finset.mem_filter.mp h₂).1,
    (Finset.mem_filter.mp h₁).2.2,(Finset.mem_filter.mp h₂).2.2,hw⟩

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_ActualSuffixLocalBins
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem uniform_actual_suffix_local_bins_oai {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ d : PositiveDistanceData, d.sig = sig → d.J = J →
      N₀ ≤ d.N → d.Q.side = 1 → d.StronglySeparated → 0 < d.q →
      ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
      d.a+100*d.q < d.t → d.t ≤ d.N → d.i ≤ J →
      let p := policyDepth (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t
      d.a+d.t < 2*p → ∀ c ∈ d.suffixRetained p,
      (binL2Norm (d.suffixData c).distance d.width)^2 ≤
        (((bandOffsets 3).card : ℝ≥0∞)*ENNReal.ofReal (((2:ℝ)^d.N)^
          (-(d.mass d.t-d.mass p)+height (fun n : ℕ => d.mass n-(n:ℝ)/(d.N:ℝ)) p d.t+
            2000*(d.lam+sig)+12*d.lam))) * (d.suffixFullDistance c univ)^2 := by
  obtain ⟨N₀,hN₀⟩ := uniform_actual_suffix_projection hsig hJ 1
  refine ⟨N₀,?_⟩
  intro d hsig' hJ' hN hQ hs hq B δ hprof hw htN hi p hsuffix c hc
  let := hprof.probability
  obtain ⟨hP,hC,hPX,hCY,x,hx,y,hy,hg⟩ := d.suffix_retained_spec hc
  have hproj := hN₀ d hsig' hJ' hN hQ hs hq B δ hprof hw htN hi hsuffix
    c.1 c.2 hP hC hPX hCY x hx y hy hg
  have hh := d.suffix_local_bin_sq hQ hs (by omega : d.a+d.t ≤ 2*p) hP hC hPX hCY hproj
  apply hh.trans_eq
  rw [PositiveDistanceData.suffixFullDistance,Measure.map_apply (by fun_prop) MeasurableSet.univ]
  simp only [preimage_univ,PositiveDistanceData.cellPair]
  rw [← univ_prod_univ,Measure.prod_prod]
  simp only [Measure.restrict_apply_univ]
  ring

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.uniform_actual_suffix_local_bins_oai := @OAI.PlanarFalconer.uniform_actual_suffix_local_bins_oai
