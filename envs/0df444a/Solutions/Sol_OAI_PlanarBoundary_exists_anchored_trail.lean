-- Prove2me | solution 1 for OAI.PlanarBoundary.exists_anchored_trail
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:24:52.898212+00:00
-- url     : https://prove2.me/submissions/2bd6697e-4889-48ae-8e36-e51126b16597

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry
import Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths
import Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers
import Definitions.Def_OAI_Probability_CriticalZ3_SeedTrials
import Definitions.Def_OAI_Probability_CriticalZ3_Conditioning
import Definitions.Def_OAI_Probability_CriticalZ3_ConditionalQuality
import Definitions.Def_OAI_Probability_CriticalZ3_TrialCounts
import Definitions.Def_OAI_Probability_CriticalZ3_ShellProbability
import Definitions.Def_OAI_Probability_CriticalZ3_SeedQuality
import Definitions.Def_OAI_Probability_CriticalZ3_Scales
import Definitions.Def_OAI_Probability_CriticalZ3_Relay
import Definitions.Def_OAI_Probability_CriticalZ3_RelayProbability
import Definitions.Def_OAI_Probability_CriticalZ3_FiniteTrails
import Definitions.Def_OAI_Probability_CriticalZ3_PlanarBoundary

open OAI OAI.PlanarBoundary
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open Classical
open Classical
theorem pl_succ_tail {D : Type*} {V : Type*} [Fintype D] (tail head : D → V)
    (hbal : ∀ v, Fintype.card {d // head d = v} = Fintype.card {d // tail d = v}) (d : D) :
    tail (FiniteTrails.successor tail head hbal d) = head d :=
  (Fintype.equivOfCardEq (hbal (head d)) ⟨d, rfl⟩).property

theorem pl_closed_trail {D : Type*} {V : Type*} [Fintype D] (tail head : D → V)
    (hbal : ∀ v, Fintype.card {d // head d = v} = Fintype.card {d // tail d = v})
    (w : D → ℤ) (hw : ∑ d, w d ≠ 0) :
    ∃ n : ℕ, ∃ hn : 0 < n, ∃ e : Fin n → D, Function.Injective e ∧
      (∀ i : Fin n, tail (e (FiniteTrails.next hn i)) = head (e i)) ∧ (∑ i, w (e i)) ≠ 0 := by
  set σ := FiniteTrails.successor tail head hbal with hσ
  have hst : ∀ d, tail (σ d) = head d := pl_succ_tail tail head hbal
  let g : D → Quotient (Equiv.Perm.SameCycle.setoid σ) := fun d => Quotient.mk _ d
  have hsum := Finset.sum_fiberwise Finset.univ g w
  rw [← hsum] at hw
  obtain ⟨q, -, hq⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
  induction q using Quotient.inductionOn with
  | h d =>
  refine ⟨minimalPeriod σ d, FiniteTrails.period_pos σ d, fun i => σ^[i.val] d, ?_, ?_, ?_⟩
  · intro i j hij; exact Fin.ext ((iterate_eq_iterate_iff_of_lt_minimalPeriod i.isLt j.isLt).mp hij)
  · intro i
    show tail (σ^[((i.val+1) % minimalPeriod σ d)] d) = head (σ^[i.val] d)
    rw [iterate_mod_minimalPeriod_eq, iterate_succ_apply', hst]
  · have h1 : ∑ i : Fin (minimalPeriod σ d), w (σ^[i.val] d) = ∑ e : {e // σ.SameCycle d e}, w e.val :=
      Equiv.sum_comp (FiniteTrails.cycleEquiv σ d) (fun e => w e.val)
    rw [h1]
    convert hq using 1
    symm
    apply Finset.sum_subtype
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, g]
    rw [Quotient.eq]
    exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem pl_balanced (X : Finset Point) (v : Point) :
    Fintype.card {e : Boundary X // head e = v} =
      Fintype.card {e : Boundary X // tail e = v} := by
  have h1 : Fintype.card {e : Boundary X // head e = v} = Fintype.card {d : Direction // v-headOffset d ∈ X ∧ v-headOffset d+outward d ∉ X} :=
    Fintype.card_congr (atVertex X v headOffset)
  have h2 : Fintype.card {e : Boundary X // tail e = v} = Fintype.card {d : Direction // v-tailOffset d ∈ X ∧ v-tailOffset d+outward d ∉ X} :=
    Fintype.card_congr (atVertex X v tailOffset)
  rw [h1, h2, Fintype.card_subtype, Fintype.card_subtype, Finset.card_filter, Finset.card_filter, Fin.sum_univ_four, Fin.sum_univ_four]
  obtain ⟨a, b⟩ := v
  simp [headOffset, tailOffset, outward]
  simp only [← sub_eq_add_neg] at *
  by_cases hA : (a-1, b-1) ∈ X <;> by_cases hB : (a-1, b) ∈ X <;> by_cases hC : (a, b) ∈ X <;> by_cases hD : (a, b-1) ∈ X <;> simp [hA, hB, hC, hD]

theorem pl_sideFlux_rev (x : Point) (d : Direction) :
    sideFlux (x + outward d) (opposite d) = - sideFlux x d := by
  obtain ⟨a, b⟩ := x
  fin_cases d <;> simp [sideFlux, rayFlux, tailOffset, headOffset, outward, opposite]

theorem pl_cell_sum (x : Point) :
    ∑ d : Direction, sideFlux x d = if x = (0,0) then 1 else 0 := by
  obtain ⟨a, b⟩ := x
  rw [Fin.sum_univ_four]
  simp [sideFlux, rayFlux, tailOffset, headOffset]; split_ifs <;> omega

theorem pl_flux (X : Finset Point) :
    (∑ e : Boundary X, rayFlux (tail e) (head e)) = if (0,0) ∈ X then 1 else 0 := by
  let g : FullSide X → ℤ := fun e => sideFlux e.1.val e.2
  have h1 : (∑ e : Boundary X, rayFlux (tail e) (head e)) = ∑ e : {e : FullSide X // ¬isInternal e}, g e.val :=
    Fintype.sum_equiv (boundaryEquiv X) _ _ (fun e => rfl)
  have h2 : (∑ e : {e : FullSide X // isInternal e}, g e.val) = 0 := by
    have hc := Equiv.sum_comp (internalReverse X) (fun e => g e.val)
    have hp : ∀ e, g (internalReverse X e).val = - g e.val := by
      intro e
      show sideFlux (e.val.1.val + outward e.val.2) (opposite e.val.2) = _
      exact pl_sideFlux_rev _ _
    simp only [hp, Finset.sum_neg_distrib] at hc
    linarith
  have h3 := Fintype.sum_subtype_add_sum_subtype (fun e : FullSide X => isInternal e) g
  rw [h1, ← add_left_cancel_iff (a := ∑ e : {e : FullSide X // isInternal e}, g e.val), h3, h2, zero_add]
  rw [Fintype.sum_prod_type]
  simp only [g, pl_cell_sum]
  rw [Finset.sum_coe_sort X (fun x => if x = ((0:ℤ),(0:ℤ)) then (1:ℤ) else 0)]
  simp

theorem pl_outward_fst_le (d : Direction) : (outward d).1 ≤ 1 := by
  fin_cases d <;> simp [outward]

theorem pl_diam {n : ℕ} (hn : 0 < n) (v : Fin n → Point)
    (hedge : ∀ i, Neighbor (v i) (v (FiniteTrails.next hn i))) (i j : Fin n) :
    (v i).1-(v j).1 < 2*(n : ℤ) := by
  have key : ∀ k : ℕ, (v ⟨(j.val + k) % n, Nat.mod_lt _ hn⟩).1 - (v j).1 ≤ k := by
    intro k
    induction k with
    | zero => simp [Nat.mod_eq_of_lt j.isLt]
    | succ k ih =>
      obtain ⟨d, hd⟩ := hedge ⟨(j.val + k) % n, Nat.mod_lt _ hn⟩
      have hnx : FiniteTrails.next hn ⟨(j.val + k) % n, Nat.mod_lt _ hn⟩ = ⟨(j.val + (k+1)) % n, Nat.mod_lt _ hn⟩ := by
        apply Fin.ext
        simp only [FiniteTrails.next]
        rw [Nat.mod_add_mod, ← add_assoc]
      rw [hnx] at hd
      rw [hd, Prod.fst_add]
      have := pl_outward_fst_le d
      push_cast
      linarith
  have hk := key (i.val + n - j.val)
  have hi : (⟨(j.val + (i.val + n - j.val)) % n, Nat.mod_lt _ hn⟩ : Fin n) = i := by
    apply Fin.ext
    simp only
    have : j.val + (i.val + n - j.val) = i.val + n := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
  rw [hi] at hk
  have h1 : ((i.val + n - j.val : ℕ) : ℤ) < 2 * (n : ℤ) := by
    have := i.isLt; have := j.isLt
    omega
  linarith

theorem pl_ray_eq_line (a : Point) (d : Direction) (ha : 0 < a.1) :
    rayFlux a (a + displacement d) = lineFlux a (a + displacement d) := by
  obtain ⟨x, y⟩ := a
  simp only at ha
  fin_cases d <;> simp [rayFlux, lineFlux, displacement, headOffset, tailOffset] <;> split_ifs <;> omega

theorem pl_ray_pos (a : Point) (d : Direction) (h : rayFlux a (a + displacement d) ≠ 0) : 0 < a.1 := by
  obtain ⟨x, y⟩ := a
  simp only
  fin_cases d <;> simp [rayFlux, displacement, headOffset, tailOffset] at h ⊢ <;> split_ifs at h <;> omega

theorem pl_head_eq {X : Finset Point} (e : Boundary X) : head e = tail e + displacement e.val.2 := by
  simp only [head, tail, displacement]; abel

theorem pl_disp_neighbor (a : Point) (d : Direction) : Neighbor a (a + displacement d) :=
  ⟨d+1, by congr 1; fin_cases d <;> decide⟩

theorem pl_next_bij {n : ℕ} (hn : 0 < n) : Function.Bijective (FiniteTrails.next hn) := by
  rw [← Finite.injective_iff_bijective]
  intro i j h
  have h' := congrArg Fin.val h
  simp only [FiniteTrails.next] at h'
  have hi := i.isLt; have hj := j.isLt
  apply Fin.ext
  rcases Nat.lt_or_ge (i.val+1) n with h1 | h1 <;> rcases Nat.lt_or_ge (j.val+1) n with h2 | h2
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at h'; omega
  · have : j.val + 1 = n := by omega
    rw [Nat.mod_eq_of_lt h1, this, Nat.mod_self] at h'; omega
  · have : i.val + 1 = n := by omega
    rw [Nat.mod_eq_of_lt h2, this, Nat.mod_self] at h'; omega
  · omega

theorem solution (X : Finset Point) (hX : (0,0) ∈ X) :
    ∃ n : ℕ, ∃ hn : 0 < n, ∃ e : Fin n → Boundary X,
      Function.Injective e ∧
      (∀ i, tail (e (FiniteTrails.next hn i)) = head (e i)) ∧
      ∃ i, 0 < (tail (e i)).1 ∧ (tail (e i)).1 < 2*(n : ℤ) ∧
        rayFlux (tail (e i)) (head (e i)) ≠ 0 := by
  have hw : (∑ e : Boundary X, rayFlux (tail e) (head e)) ≠ 0 := by
    rw [pl_flux X, if_pos hX]; norm_num
  obtain ⟨n, hn, e, hinj, hch, hsum⟩ :=
    pl_closed_trail (tail (X := X)) (head (X := X)) (fun v => by convert pl_balanced X v) _ hw
  refine ⟨n, hn, e, hinj, hch, ?_⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hpos : 0 < (tail (e i)).1 := by
    rw [pl_head_eq] at hi
    exact pl_ray_pos _ _ hi
  have hj : ∃ j, (tail (e j)).1 ≤ 0 := by
    by_contra hcon
    push Not at hcon
    apply hsum
    have heq : ∀ k, rayFlux (tail (e k)) (head (e k)) =
        (if 1 ≤ (tail (e (FiniteTrails.next hn k))).2 then 1 else 0) - (if 1 ≤ (tail (e k)).2 then 1 else 0) := by
      intro k
      rw [hch k, pl_head_eq, pl_ray_eq_line _ _ (hcon k)]
      rfl
    simp only [heq, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    exact Function.Bijective.sum_comp (pl_next_bij hn) (fun k => if 1 ≤ (tail (e k)).2 then (1:ℤ) else 0)
  obtain ⟨j, hj⟩ := hj
  have hedge : ∀ k, Neighbor (tail (e k)) (tail (e (FiniteTrails.next hn k))) := by
    intro k
    rw [hch k, pl_head_eq]
    exact pl_disp_neighbor _ _
  have hd := pl_diam hn (fun k => tail (e k)) hedge i j
  exact ⟨i, hpos, by linarith, hi⟩

