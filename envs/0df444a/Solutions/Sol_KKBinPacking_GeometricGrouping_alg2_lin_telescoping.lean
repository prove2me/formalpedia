-- Prove2me | solution 1 for KKBinPacking.GeometricGrouping.alg2_lin_telescoping
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-02T13:33:05.55164+00:00
-- url     : https://prove2.me/submissions/4d681118-a28c-41b7-95f0-d1e68f3fbbb7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Algorithm 2 LP telescoping, reduced to its two existing analytic milestones.
import Theorems.Thm_KKBinPacking_GeometricGrouping_alg2_size_recursion
import Theorems.Thm_KKBinPacking_GeometricGrouping_geomGroup_bounds

set_option autoImplicit false

open KKBinPacking.Shared KKBinPacking.GeometricGrouping

namespace KKContribution

lemma takeUntil_append_drop (k : ℝ) (L : List ℝ) :
    takeUntil k L ++ L.drop (takeUntil k L).length = L := by
  induction L generalizing k with
  | nil => simp [takeUntil]
  | cons x xs ih =>
    rw [takeUntil]
    split_ifs with h
    · simp
    · simpa using congrArg (List.cons x) (ih (k - x))

lemma groups_sum (k : ℝ) : (L : List ℝ) →
    ((geomGroupsList k L).map (fun (G : List ℝ) => (G : Multiset ℝ))).sum =
      (L : Multiset ℝ)
  | [] => by simp [geomGroupsList]
  | x :: xs => by
    rw [geomGroupsList]
    simp only [List.map_cons, List.sum_cons]
    rw [groups_sum k ((x :: xs).drop (takeUntil k (x :: xs)).length)]
    rw [Multiset.coe_add, takeUntil_append_drop]
termination_by L => L.length
decreasing_by
  simp only [List.length_drop, List.length_cons]
  have := takeUntil_cons_length_pos k x xs
  omega

lemma adjacent_partition (A : List ℝ) (Gs : List (List ℝ)) :
    (List.zipWith
      (fun (Gprev Gi : List ℝ) =>
        (((Gi.take Gprev.length).map (fun p => (p, Gi.headD 0))) : Multiset (ℝ × ℝ)))
      (A :: Gs) Gs).sum.map Prod.fst +
    (List.zipWith (fun (Gprev Gi : List ℝ) => ((Gi.drop Gprev.length) : Multiset ℝ))
      (A :: Gs) Gs).sum = (Gs.map (fun (G : List ℝ) => (G : Multiset ℝ))).sum := by
  induction Gs generalizing A with
  | nil => simp
  | cons G Gs ih =>
    have hsplit :
      ((G.take A.length : List ℝ) : Multiset ℝ) + (G.drop A.length : List ℝ) =
      (G : Multiset ℝ) := by rw [Multiset.coe_add, List.take_append_drop]
    simp only [List.zipWith_cons_cons, List.sum_cons, Multiset.map_add,
      Multiset.map_coe, List.map_map, Function.comp_def, List.map_id']
    simp only [List.map_cons, List.sum_cons]
    calc
      _ = ((G.take A.length : List ℝ) : Multiset ℝ) + (G.drop A.length : List ℝ) +
        ((List.zipWith
          (fun (Gprev Gi : List ℝ) =>
            (((Gi.take Gprev.length).map (fun p => (p, Gi.headD 0))) : Multiset (ℝ × ℝ)))
          (G :: Gs) Gs).sum.map Prod.fst +
        (List.zipWith (fun (Gprev Gi : List ℝ) => ((Gi.drop Gprev.length) : Multiset ℝ))
          (G :: Gs) Gs).sum) := by abel
      _ = _ := by rw [hsplit, ih G]

lemma geom_partition (k : ℕ) (I : Multiset ℝ) :
    (geomPairs k I).map Prod.fst + geomJ' k I = I := by
  have hsum : ((geomGroups k I).map (fun (G : List ℝ) => (G : Multiset ℝ))).sum = I := by
    rw [geomGroups, groups_sum, Multiset.sort_eq]
  apply Eq.trans (b := ((geomGroups k I).map (fun (G : List ℝ) => (G : Multiset ℝ))).sum) ?_ hsum
  unfold geomPairs geomJ'
  generalize geomGroups k I = Gs
  cases Gs with
  | nil => simp
  | cons A Gs =>
    simp only [List.tail_cons, List.headD_cons, List.map_cons, List.sum_cons]
    rw [show
      (List.zipWith
        (fun (Gprev Gi : List ℝ) =>
          (((Gi.take Gprev.length).map (fun p => (p, Gi.headD 0))) : Multiset (ℝ × ℝ)))
        (A :: Gs) Gs).sum.map Prod.fst +
      ((A : Multiset ℝ) +
        (List.zipWith (fun (Gprev Gi : List ℝ) => ((Gi.drop Gprev.length) : Multiset ℝ))
          (A :: Gs) Gs).sum) =
      (A : Multiset ℝ) + ((Gs.map (fun (G : List ℝ) => (G : Multiset ℝ))).sum) by
        rw [← adjacent_partition A Gs]
        abel]

lemma fst_mem_source (k : ℕ) (I : Multiset ℝ) {p : ℝ × ℝ} (hp : p ∈ geomPairs k I) :
    p.1 ∈ I := by
  rw [← geom_partition k I]
  exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_map.mpr ⟨p, hp, rfl⟩))

end KKContribution

namespace KKTelescopeAudit

/-- If `g > 1`, Step 1 removes every item of a valid instance. -/
lemma inst_zero_eq_zero_of_one_lt (k : ℕ) (g : ℝ) (I : Multiset ℝ)
    (hI : IsInstance I) (tr : Alg2Trace k g I) (hg : 1 < g) :
    tr.inst 0 = 0 := by
  rw [tr.inst_zero]
  apply Multiset.filter_eq_nil.mpr
  intro x hx
  have hxlt := (hI x hx).2
  simp only [not_lt]
  linarith

/-- A zero current instance has no rounded pairs, hence the next instance is empty. -/
lemma inst_succ_eq_zero_of_inst_eq_zero (k : ℕ) (g : ℝ) (I : Multiset ℝ)
    (tr : Alg2Trace k g I) (i : ℕ) (hi : i < tr.t)
    (hzero : tr.inst i = 0) :
    tr.inst (i + 1) = 0 := by
  have hpairs : geomPairs k (tr.inst i) = 0 := by
    rw [hzero]
    simp [geomPairs, geomGroups, geomGroupsList]
  have hsub := tr.Bp_sub i hi
  rw [hpairs] at hsub
  have hbp : (tr.Bp i).join = 0 := Multiset.le_zero.mp hsub
  rw [tr.inst_succ i hi, hpairs, hbp]
  simp

/-- Once Step 1 is empty, every state in the finite trace is empty. -/
lemma all_inst_eq_zero_of_one_lt (k : ℕ) (g : ℝ) (I : Multiset ℝ)
    (hI : IsInstance I) (tr : Alg2Trace k g I) (hg : 1 < g) :
    ∀ i ≤ tr.t, tr.inst i = 0 := by
  have hzero := inst_zero_eq_zero_of_one_lt k g I hI tr hg
  intro i
  induction i with
  | zero =>
      intro _
      exact hzero
  | succ i ih =>
      intro hi
      apply inst_succ_eq_zero_of_inst_eq_zero k g I tr i (by omega)
      exact ih (by omega)

/-- For any valid input, a trace with `g > 1` cannot execute the loop. -/
theorem trace_t_eq_zero_of_one_lt (k : ℕ) (g : ℝ) (I : Multiset ℝ)
    (hI : IsInstance I) (tr : Alg2Trace k g I) (hg : 1 < g) :
    tr.t = 0 := by
  by_contra ht
  have htpos : 1 ≤ tr.t := by omega
  have hall := all_inst_eq_zero_of_one_lt k g I hI tr hg
  have hzero0 := hall 0 (by omega)
  have hzerot := hall tr.t le_rfl
  have hexit := tr.loop_exit
  rw [hzerot, SIZE] at hexit
  have hrun := tr.loop_run 0 (by omega)
  rw [hzero0, SIZE] at hrun
  simp at hexit hrun
  linarith

/-- A trace that executes at least one iteration must have `g ≤ 1`. -/
theorem trace_g_le_one_of_t_pos (k : ℕ) (hk : 2 ≤ k) (g : ℝ) (hg0 : 0 < g)
    (I : Multiset ℝ) (hI : IsInstance I) (tr : Alg2Trace k g I)
    (ht : 1 ≤ tr.t) :
    g ≤ 1 := by
  by_contra hnot
  have hg : 1 < g := lt_of_not_ge hnot
  have htzero := trace_t_eq_zero_of_one_lt k g I hI tr hg
  omega

/-- Every state through the exit is a valid instance: each residual piece is the first
component of a geometric pair from the previous instance. -/
theorem trace_inst_isInstance (k : ℕ) (g : ℝ) (I : Multiset ℝ)
    (hI : IsInstance I) (tr : Alg2Trace k g I) :
    ∀ i ≤ tr.t, IsInstance (tr.inst i) := by
  intro i
  induction i with
  | zero =>
      intro _ x hx
      rw [tr.inst_zero] at hx
      exact hI x (Multiset.mem_filter.mp hx).1
  | succ i ih =>
      intro hi
      have hprev := ih (by omega)
      have hiter : i < tr.t := by omega
      rw [tr.inst_succ i hiter]
      intro x hx
      obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hx
      have hpairs : p ∈ geomPairs k (tr.inst i) :=
        Multiset.mem_of_le (Multiset.sub_le_self _ _) hp
      exact hprev p.1 (KKContribution.fst_mem_source k (tr.inst i) hpairs)

/-- Each instance at the beginning of an executed iteration is nonempty. -/
theorem trace_inst_ne_zero_of_lt (k : ℕ) (hk : 2 ≤ k) (g : ℝ) (hg0 : 0 < g)
    (I : Multiset ℝ) (hI : IsInstance I) (tr : Alg2Trace k g I)
    (i : ℕ) (hi : i < tr.t) :
    tr.inst i ≠ 0 := by
  have hg1 : g ≤ 1 := trace_g_le_one_of_t_pos k hk g hg0 I hI tr (by omega)
  have hlog : 0 ≤ Real.log (1 / g) := Real.log_nonneg (by
    exact (le_div_iff₀ hg0).2 (by simpa using hg1))
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hden : 0 < 1 - 1 / (k : ℝ) := by
    have hlt : 1 / (k : ℝ) < 1 := (div_lt_one (by positivity)).2 (by linarith)
    linarith
  have hcoeff : 0 ≤ 1 / (1 - 1 / (k : ℝ)) := by positivity
  have hthreshold : 1 ≤ alg2Threshold k g := by
    simp only [alg2Threshold]
    have := mul_nonneg hcoeff hlog
    linarith
  have hrun := tr.loop_run i hi
  have hsize : 0 < SIZE (tr.inst i) := by linarith
  intro hzero
  rw [hzero, SIZE] at hsize
  norm_num at hsize

end KKTelescopeAudit

namespace KKTelescope

lemma lin_nonneg (I : Multiset ℝ) : 0 ≤ LIN I := by
  apply Real.sInf_nonneg
  rintro z ⟨x, hx, rfl⟩
  exact Finset.sum_nonneg (fun c _ => hx.2.1 c)

lemma fractional_cost (x : Multiset ℝ →₀ ℝ) :
    (∑ c ∈ x.support, (x c - (⌊x c⌋₊ : ℝ))) = lpCost x - principalCount x := by
  simp [lpCost, principalCount, Finset.sum_sub_distrib, Nat.cast_sum]

end KKTelescope

theorem solution (k : ℕ) (hk : 2 ≤ k) (g : ℝ) (hg0 : 0 < g)
    (I : Multiset ℝ) (hI : IsInstance I) (tr : Alg2Trace k g I) :
    (∀ i < tr.t,
      LIN (tr.inst (i + 1)) ≤ LIN (geomJ k (tr.inst i)) + 1 - principalCount (tr.x i) ∧
        LIN (geomJ k (tr.inst i)) + 1 - principalCount (tr.x i) ≤
          LIN (tr.inst i) + 1 - principalCount (tr.x i)) ∧
    ((∑ i ∈ Finset.range tr.t, principalCount (tr.x i) : ℕ) : ℝ) ≤
      LIN (geomJ k (tr.inst 0)) + tr.t := by
  classical
  have hstep : ∀ i < tr.t,
      LIN (tr.inst (i + 1)) ≤ LIN (geomJ k (tr.inst i)) + 1 - principalCount (tr.x i) ∧
        LIN (geomJ k (tr.inst i)) + 1 - principalCount (tr.x i) ≤
          LIN (tr.inst i) + 1 - principalCount (tr.x i) := by
    intro i hi
    have hg1 := KKTelescopeAudit.trace_g_le_one_of_t_pos k hk g hg0 I hI tr (by omega)
    have hinst := KKTelescopeAudit.trace_inst_isInstance k g I hI tr i (by omega)
    have hne := KKTelescopeAudit.trace_inst_ne_zero_of_lt k hk g hg0 I hI tr i hi
    have hrec := (alg2_size_recursion k hk g hg0 hg1 I hI tr i hi).2.1
    rw [KKTelescope.fractional_cost] at hrec
    have hcost := tr.x_cost i hi
    have hmono := (geomGroup_bounds (tr.inst i) hinst hne k hk).2.1.1
    constructor <;> linarith
  refine ⟨hstep, ?_⟩
  by_cases ht : tr.t = 0
  · simp only [ht, Finset.range_zero, Finset.sum_empty, Nat.cast_zero, add_zero]
    exact KKTelescope.lin_nonneg _
  have hsum : ∀ n, 1 ≤ n → n ≤ tr.t →
      ((∑ i ∈ Finset.range n, principalCount (tr.x i) : ℕ) : ℝ) + LIN (tr.inst n) ≤
        LIN (geomJ k (tr.inst 0)) + n := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
      intro hn hnt
      by_cases hn0 : n = 0
      · subst n
        have hs := (hstep 0 (by omega)).1
        simpa using
          (show (principalCount (tr.x 0) : ℝ) + LIN (tr.inst 1) ≤
            LIN (geomJ k (tr.inst 0)) + 1 by linarith)
      · have hprev := ih (by omega) (by omega)
        have hs := (hstep n (by omega)).1.trans (hstep n (by omega)).2
        rw [Finset.sum_range_succ, Nat.cast_add, Nat.cast_add, Nat.cast_one]
        linarith
  have hs := hsum tr.t (by omega) le_rfl
  have hn := KKTelescope.lin_nonneg (tr.inst tr.t)
  linarith
