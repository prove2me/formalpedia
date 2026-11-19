-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.recursive_joint_solve_overhead
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T12:01:29.791148+00:00
-- url     : https://prove2.me/submissions/71e7f519-8365-419d-b710-643464c96751

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
import Definitions.Def_NearlyOptimalPPR_Computation_push
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_residual_identities
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_control_parameters
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_queue_domains
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_numerical_invariants
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_discovery_credit

set_option linter.all false
set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

abbrev region_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_residual_identities m n g s α q ℓ schedule t).1

abbrev root_identity_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_residual_identities m n g s α q ℓ schedule t).2.1

abbrev root_threshold_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_residual_identities m n g s α q ℓ schedule t).2.2.2

abbrev depth_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_control_parameters m n g s α q ℓ schedule t).1

abbrev keys_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 ≤ q) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_queue_domains m n g s α q ℓ schedule t).1 hq

abbrev isolate_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_queue_domains m n g s α q ℓ schedule t).2.1 hs

abbrev stored_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 ≤ q) (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_queue_domains m n g s α q ℓ schedule t).2.2 hq hs

abbrev numerical_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  recursive_numerical_invariants m n g s α q hα hq hs ℓ schedule t

abbrev stored_credit_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  recursive_discovery_credit m n g s α q hα hq hs ℓ schedule t

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LogOverhead

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation

lemma queue_log_overhead_bound (ε : ℝ) (hε : 0 < ε ∧ ε ≤ 1) (ℓ t : ℕ) (ht : t ≤ ℓ) :
    1+Real.logb 2 (2+(3+2*(t+1 : ℕ))/rootThreshold ε ℓ) ≤
      (1+(Real.log 128+4)/Real.log 2)*(2+Real.log (2/ε)+(ℓ : ℝ)) := by
  have he0 : 0 < ε := hε.1
  have hel0 : (0 : ℝ) ≤ (ℓ : ℝ) := by positivity
  let A : ℝ := ℓ+3
  let L := Real.log (2/ε)
  let B : ℝ := 2+L+ℓ
  let D := Real.log 128+4
  let z : ℝ := 2+(3+2*(t+1 : ℕ))/rootThreshold ε ℓ
  have hA : 0 < A := by dsimp [A]; positivity
  have hA3 : 3 ≤ A := by dsimp [A]; linarith
  have hqr : rootThreshold ε ℓ = ε/(32*A) := by simp [rootThreshold,kappa,A]
  have hq : 0 < rootThreshold ε ℓ := by rw [hqr]; positivity
  have hz : 0 < z := by dsimp [z]; positivity
  have htc : (t : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast ht
  have hP : (3+2*(t+1 : ℕ) : ℝ) ≤ 2*A := by dsimp [A]; push_cast; linarith
  have hze : z*ε = 2*ε+(3+2*(t+1 : ℕ))*32*A := by
    dsimp only [z]
    rw [hqr]
    field_simp [he0.ne',hA.ne'] <;> push_cast <;> ring
  have hupper : z ≤ 128*A^2/ε := by
    apply (le_div_iff₀ hε.1).mpr
    rw [hze]
    have hm := mul_le_mul_of_nonneg_right hP (show 0 ≤ 32*A by positivity)
    nlinarith [hε.2]
  have hlog : Real.log z ≤ Real.log 128+2*Real.log A-Real.log ε := by
    have hh := Real.log_le_log hz hupper
    have hnum : (128 : ℝ)*A^2 ≠ 0 := by positivity
    rw [Real.log_div hnum hε.1.ne',Real.log_mul (by norm_num : (128 : ℝ) ≠ 0) (pow_ne_zero 2 hA.ne'),Real.log_pow] at hh
    norm_num at hh
    exact hh
  have hL : 0 ≤ L := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hε.1).mpr
    linarith [hε.2]
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog128 : 0 ≤ Real.log (128 : ℝ) := Real.log_nonneg (by norm_num)
  have hLA : Real.log A ≤ (ℓ : ℝ)+2 := by
    have hh := Real.log_le_sub_one_of_pos hA
    dsimp [A] at hh
    linarith
  have hεL : -Real.log ε ≤ L := by
    dsimp only [L]
    rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hε.1.ne']
    linarith
  have hD : 2 ≤ D := by dsimp [D]; linarith
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hlogB : Real.log z ≤ D*B := by
    have hel : (0 : ℝ) ≤ (ℓ : ℝ) := by positivity
    have hm1 := mul_le_mul_of_nonneg_right hD hel
    have hm2 := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ D by linarith) hL
    dsimp [D,B]
    dsimp [D] at hm1 hm2
    nlinarith [hlog,hLA,hεL]
  change 1+Real.logb 2 z ≤ (1+D/Real.log 2)*B
  rw [Real.logb]
  calc
    _ ≤ B+(D*B)/Real.log 2 := add_le_add hB (div_le_div_of_nonneg_right hlogB hlog2.le)
    _ = _ := by ring

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.SolverLogBound

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma queueLogConstant_positive : 0 < queueLogConstant := by
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h128 : 0 ≤ Real.log (128 : ℝ) := Real.log_nonneg (by norm_num)
  unfold queueLogConstant
  positivity

lemma primitiveLogConstant_bounds : 1 ≤ primitiveLogConstant ∧ queueLogConstant ≤ primitiveLogConstant ∧
    1+queueLogConstant*Real.log 2 ≤ primitiveLogConstant := by
  have hA := queueLogConstant_positive.le
  have h2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  refine ⟨?_,?_,?_⟩ <;> unfold primitiveLogConstant <;> nlinarith [mul_nonneg hA h2]

lemma solver_log_linear (ε : ℝ) (hε : 0 < ε ∧ ε ≤ 1) (ℓ : ℕ) (V : ℝ)
    (hV : 0 ≤ V) (hvol : V ≤ 1/rootThreshold ε ℓ) :
    1+Real.log (2+3*V) ≤ primitiveLogConstant*(2+Real.log (2/ε)+(ℓ : ℝ)) := by
  let q := rootThreshold ε ℓ
  let B := 2+Real.log (2/ε)+(ℓ : ℝ)
  let z : ℝ := 2+(3+2*(ℓ+1 : ℕ))/q
  have he : 0 < ε := hε.1
  have hq : 0 < q := by dsimp [q,rootThreshold,kappa]; positivity
  have hB : 1 ≤ B := by
    have hL : 0 ≤ Real.log (2/ε) := Real.log_nonneg ((le_div_iff₀ he).mpr (by linarith [hε.2]))
    have hl : (0 : ℝ) ≤ (ℓ : ℝ) := by positivity
    dsimp only [B]
    linarith
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  have hP : (3 : ℝ) ≤ (3+2*(ℓ+1 : ℕ) : ℝ) := by
    have hl : (0 : ℝ) ≤ (ℓ : ℝ) := by positivity
    push_cast
    linarith
  have hupper : 2+3*V ≤ z := by
    calc
      _ ≤ 2+3*(1/q) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hvol (by norm_num))
      _ = 2+3/q := by ring
      _ ≤ _ := add_le_add le_rfl (div_le_div_of_nonneg_right hP hq.le)
  have hlog := Real.log_le_log (show 0 < 2+3*V by positivity) hupper
  have hqueue := queue_log_overhead_bound ε hε ℓ ℓ le_rfl
  change 1+Real.logb 2 z ≤ queueLogConstant*B at hqueue
  rw [Real.logb] at hqueue
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hz : Real.log z ≤ queueLogConstant*Real.log 2*B := by
    have hh : Real.log z/Real.log 2 ≤ queueLogConstant*B-1 := by linarith
    have hm := (div_le_iff₀ h2).mp hh
    nlinarith
  calc
    _ ≤ B+queueLogConstant*Real.log 2*B := add_le_add hB (hlog.trans hz)
    _ = (1+queueLogConstant*Real.log 2)*B := by ring
    _ ≤ primitiveLogConstant*B := mul_le_mul_of_nonneg_right primitiveLogConstant_bounds.2.2 hB0

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.DepthInvariant

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

@[simp] lemma top_ite (P : Prop) [Decidable P] (a b : RecursiveState n) :
    (if P then a else b).top = if P then a.top else b.top := by split <;> rfl
@[simp] lemma top_debit (st : RecursiveState n) (j : ℕ) (w : ℝ≥0∞) : (debit st j w).top = st.top := rfl
@[simp] lemma top_changeFrame (st : RecursiveState n) (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n) :
    (changeFrame st j f).top = st.top := rfl
@[simp] lemma top_changePC (st : RecursiveState n) (pc : NormalizePC) : (changePC st pc).top = st.top := rfl
@[simp] lemma top_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) :
    (refreshKeys g st T).top = st.top := rfl
@[simp] lemma top_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (h : Fin n → ℝ) :
    (jointUpdate g α st h).top = st.top := rfl
@[simp] lemma top_finish (st : RecursiveState n) : (finishEpisode st).top = st.top := rfl
@[simp] lemma top_complete (m : SolveModel) (g : InputGraph n) (s : Fin n)
    (α : ℝ) (st : RecursiveState n) : (completeComponent m g s α st).top = st.top := rfl
@[simp] lemma top_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n) :
    (endCall g α st).top = if st.top = 0 then st.top else st.top-1 := by
  unfold endCall
  dsimp only
  split <;> rfl
@[simp] lemma top_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) : (exteriorPush g α st t v).top = st.top := by
  simp [exteriorPush]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RegionInvariants

set_option autoImplicit false
open Finset
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma active_subset_root (st : RecursiveState n) (hi : RegionInvariant st)
    (j : ℕ) (hj : j ≤ st.top) : (st.frames j).active ⊆ (st.frames 0).active := by
  induction j with
  | zero => exact Finset.Subset.refl _
  | succ j ih =>
    have hh := (hi (j+1) hj).1
    have hp : parentDomain st (j+1) = (st.frames j).active := by simp [parentDomain]
    rw [hp] at hh
    exact hh.trans (ih (Nat.le_of_succ_le hj))

@[simp] lemma refresh_active (g : InputGraph n) (st : RecursiveState n)
    (T : Finset (Fin n)) (i : ℕ) :
    ((refreshKeys g st T).frames i).active = (st.frames i).active := by
  by_cases hi : i ≤ st.top <;> simp [refreshKeys,hi]

@[simp] lemma refresh_parentDomain (g : InputGraph n) (st : RecursiveState n)
    (T : Finset (Fin n)) (i : ℕ) :
    parentDomain (refreshKeys g st T) i = parentDomain st i := by
  unfold parentDomain
  split <;> simp

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LayerIdentity

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}


lemma active_subset_between (st : RecursiveState n) (hr : RegionInvariant st)
    (a b : ℕ) (hab : a ≤ b) (hbt : b ≤ st.top) :
    (st.frames b).active ⊆ (st.frames a).active := by
  induction b with
  | zero =>
    have he : a = 0 := by omega
    subst a
    exact Finset.Subset.refl _
  | succ b ih =>
    by_cases he : a = b+1
    · subst a; exact Finset.Subset.refl _
    · have hh := (hr (b+1) hbt).1
      have hp : parentDomain st (b+1) = (st.frames b).active := by simp [parentDomain]
      rw [hp] at hh
      exact hh.trans (ih (by omega) (by omega))


end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.GraphCut

set_option autoImplicit false
open Finset
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma neighbor_degree (g : InputGraph n) (v : Fin n) :
    (g.neighbors v).length = g.graph.degree v := by
  have he : (g.neighbors v).toFinset = g.graph.neighborFinset v := by
    ext u
    simp [g.correct]
  rw [← List.toFinset_card_of_nodup (g.nodup v),he,SimpleGraph.card_neighborFinset_eq_degree]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.StoredStep

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma run_active_domain_valid (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 ≤ q) (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule) (t i : ℕ)
    (hi : i ≤ (recursiveRun m g s α q ℓ schedule t).top) :
    let st := recursiveRun m g s α q ℓ schedule t
    (st.frames i).active ⊆ st.stored ∧ ∀ v ∈ (st.frames i).active, 0 < g.graph.degree v := by
  have hh := stored_run m g s α q hq hs ℓ schedule t
  exact ⟨hh.1 i hi,fun v hv => hh.2 v (hh.1 i hi hv)⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootControl

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

@[simp] lemma frame_pc_debit (st : RecursiveState n) (j i : ℕ) (w : ℝ≥0∞) :
    ((debit st j w).frames i).pc = (st.frames i).pc := by simp [debit]
@[simp] lemma frame_pc_refresh (g : InputGraph n) (st : RecursiveState n)
    (T : Finset (Fin n)) (i : ℕ) :
    ((refreshKeys g st T).frames i).pc = (st.frames i).pc := by
  by_cases he : i ≤ st.top <;> simp [refreshKeys,he]
@[simp] lemma frame_pc_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (h : Fin n → ℝ) (i : ℕ) :
    ((jointUpdate g α st h).frames i).pc = (st.frames i).pc := by
  by_cases he : i ≤ st.top <;> simp [jointUpdate,he]
@[simp] lemma frame_pc_ite (P : Prop) [Decidable P] (a b : RecursiveState n) (i : ℕ) :
    ((if P then a else b).frames i).pc = if P then (a.frames i).pc else (b.frames i).pc := by
  split <;> rfl
@[simp] lemma frame_pc_changeFrame (st : RecursiveState n) (j i : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n) :
    ((changeFrame st j f).frames i).pc =
      if i = j then (f (st.frames j)).pc else (st.frames i).pc := by
  by_cases he : i = j <;> simp [changeFrame,he]

@[simp] lemma frame_pc_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) (i : ℕ) :
    ((exteriorPush g α st t v).frames i).pc = (st.frames i).pc := by
  let f := st.frames t
  let d := LocalPush.deg g.graph v
  let h := min (f.residual v/(5*d)) (3*f.q/8-relative st t v)
  let base : RecursiveState n :=
    {st with
      x := Function.update st.x v (st.x v+h)
      stored := insert v st.stored
      frames := fun i => if i ≤ st.top then
        let fi := st.frames i
        {fi with
          residual := fun w => fi.residual w +
          (if w = v then if i < t then -d*h else if i = t then -5*d*h else 0 else 0) +
          (if w ∈ parentDomain st i ∧ g.graph.Adj w v then (1-α)*h else 0)
          W := fi.W + if fi.openBudget = true ∧ t ≤ i then (1-α)*d*h else 0}
        else st.frames i}
  let admitted := changeFrame base t (fun fi =>
    {fi with
      active := insert v fi.active
      residual := Function.update fi.residual v (fi.residual v+f.q*d/2)
      W := fi.W + if fi.openBudget then (t+3 : ℕ)*f.q*d/2 else 0})
  let child := if t < st.top then changeFrame admitted (t+1) (fun fc =>
    {fc with
      reference := Function.update fc.reference v (admitted.x v)
      residual := Function.update fc.residual v ((admitted.frames t).residual v)}) else admitted
  let final := if t = 0 then {child with boundaryEdges := st.boundaryEdges +
    (g.neighbors v).length - 2*((g.neighbors v).filter (fun w => w ∈ f.active)).length} else child
  have hb (i : ℕ) : (base.frames i).pc = (st.frames i).pc := by
    by_cases hi : i ≤ st.top <;> simp [base,hi]
  have ha (i : ℕ) : (admitted.frames i).pc = (st.frames i).pc := by
    simp only [admitted,frame_pc_changeFrame]
    split <;> simp_all [hb]
  have hc (i : ℕ) : (child.frames i).pc = (st.frames i).pc := by
    unfold child
    split
    · simp only [frame_pc_changeFrame]
      split <;> simp_all [ha]
    · exact ha i
  have hf (i : ℕ) : (final.frames i).pc = (st.frames i).pc := by
    unfold final
    split <;> exact hc i
  unfold exteriorPush
  simp only [frame_pc_debit,frame_pc_refresh]
  change ((if relative st t v+h = 3*f.q/8 then final else base).frames i).pc = _
  split
  · exact hf i
  · exact hb i

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.NumericalRaw

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma parent_domain_nested (st : RecursiveState n) (hreg : RegionInvariant st)
    (a b : ℕ) (hab : a < b) (hbt : b ≤ st.top) : parentDomain st b ⊆ (st.frames a).active := by
  have hb : b ≠ 0 := by omega
  rw [parentDomain,if_neg hb]
  exact active_subset_between st hreg a (b-1) (by omega) (by omega)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootMass

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma lap_sum (g : InputGraph n) (α : ℝ) (x : Fin n → ℝ) :
    (∑ v, (LocalPush.Lα g.graph α *ᵥ x) v) = α*∑ v, LocalPush.deg g.graph v*x v := by
  classical
  have hadj (u : Fin n) : (∑ v, LocalPush.adjM g.graph v u) = LocalPush.deg g.graph u := by
    have he : (fun v => if g.graph.Adj v u then (1 : ℝ) else 0) =
        (fun v => if g.graph.Adj u v then (1 : ℝ) else 0) := by
      funext v
      simp only [g.graph.adj_comm]
    change (∑ v, if g.graph.Adj v u then (1 : ℝ) else 0) = _
    rw [he]
    exact (g.graph.degree_eq_sum_if_adj (R := ℝ) u).symm
  have hcol (u : Fin n) : (∑ v, LocalPush.Lα g.graph α v u) = α*LocalPush.deg g.graph u := by
    simp only [LocalPush.Lα,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
      Finset.sum_sub_distrib,← Finset.mul_sum]
    rw [hadj]
    simp [LocalPush.degM,Matrix.diagonal]
    ring
  simp only [Matrix.mulVec,dotProduct]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul,hcol]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  ring

lemma residual_sum (g : InputGraph n) (s : Fin n) (α : ℝ) (x : Fin n → ℝ) :
    (∑ v, residual g.graph α s x v) = 1-α*∑ v, LocalPush.deg g.graph v*x v := by
  simp [residual,Pi.sub_apply,Finset.sum_sub_distrib,lap_sum,LocalPush.e,Pi.single_apply]

lemma volume_real (g : InputGraph n) (H : Finset (Fin n)) :
    (volumeNat g H : ℝ) = ∑ v ∈ H, LocalPush.deg g.graph v := by
  simp [volumeNat,LocalPush.deg,neighbor_degree]

lemma root_volume_bound (g : InputGraph n) (s : Fin n) (α : ℝ) (hα : 0 ≤ α)
    (st : RecursiveState n) (hi : RootIdentity g s α st) (hn : NumericalInvariant g st) :
    (st.frames 0).q*(volumeNat g (st.frames 0).active : ℝ) ≤ 1 := by
  classical
  have hr (v : Fin n) : 0 ≤ (st.frames 0).residual v := by
    exact ((hn 0 (Nat.zero_le _)).1 v (by simp [parentDomain])).1
  have hx (v : Fin n) : 0 ≤ st.x v := by
    simpa [relative] using ((hn 0 (Nat.zero_le _)).1 v (by simp [parentDomain])).2.1
  have hd (v : Fin n) : 0 ≤ LocalPush.deg g.graph v := by unfold LocalPush.deg; positivity
  have hs : 0 ≤ ∑ v, LocalPush.deg g.graph v*st.x v :=
    Finset.sum_nonneg fun v _ => mul_nonneg (hd v) (hx v)
  have hb : (∑ v, if v ∈ (st.frames 0).active then
      (st.frames 0).q*LocalPush.deg g.graph v else 0) ≤ ∑ v, residual g.graph α s st.x v := by
    apply Finset.sum_le_sum
    intro v _
    rw [hi v]
    by_cases hv : v ∈ (st.frames 0).active
    · simp only [hv,ite_true]
      nlinarith [hr v]
    · simp only [hv,ite_false]
      nlinarith [hr v,mul_nonneg (hd v) (hx v)]
  have hsum : (∑ v, if v ∈ (st.frames 0).active then
      (st.frames 0).q*LocalPush.deg g.graph v else 0) =
      (st.frames 0).q*(volumeNat g (st.frames 0).active : ℝ) := by
    rw [volume_real,Finset.mul_sum,← Finset.sum_filter]
    congr 1
    ext v
    simp
  rw [hsum,residual_sum] at hb
  nlinarith [mul_nonneg hα hs]

lemma card_le_volume (g : InputGraph n) (H : Finset (Fin n))
    (hH : ∀ v ∈ H, 0 < g.graph.degree v) : H.card ≤ volumeNat g H := by
  calc
    H.card = ∑ v ∈ H, (1 : ℕ) := by simp
    _ ≤ ∑ v ∈ H, (g.neighbors v).length := by
      apply Finset.sum_le_sum
      intro v hv
      rw [neighbor_degree]
      exact hH v hv

lemma run_root_volume_bound (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    let st := recursiveRun m g s α q ℓ schedule t
    (volumeNat g (st.frames 0).active : ℝ) ≤ 1/q ∧ ((st.frames 0).active.card : ℝ) ≤ 1/q := by
  let st := recursiveRun m g s α q ℓ schedule t
  have hv := root_volume_bound g s α hα.1.le st (root_identity_run m g s α q ℓ schedule t)
    (numerical_run m g s α q hα hq hs ℓ schedule t)
  have hq' : (st.frames 0).q = q := root_threshold_run m g s α q ℓ schedule t
  rw [hq'] at hv
  have hvol : (volumeNat g (st.frames 0).active : ℝ) ≤ 1/q := by
    apply (le_div_iff₀ hq).mpr
    nlinarith
  have hdom := run_active_domain_valid m g s α q hq.le hs ℓ schedule t 0 (Nat.zero_le _)
  have hcard : ((st.frames 0).active.card : ℝ) ≤ (volumeNat g (st.frames 0).active : ℝ) := by
    exact_mod_cast card_le_volume g (st.frames 0).active hdom.2
  exact ⟨hvol,hcard.trans hvol⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.DiscoveryCredit

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma root_reserve_mass_bound (g : InputGraph n) (s : Fin n) (α : ℝ) (hα : 0 ≤ α)
    (st : RecursiveState n) (hi : RootIdentity g s α st) (hn : NumericalInvariant g st) :
    (st.frames 0).q*(volumeNat g (st.frames 0).active : ℝ)+
      4*(∑ v ∈ Finset.univ \ (st.frames 0).active, LocalPush.deg g.graph v*st.x v) ≤ 1 := by
  classical
  have hr (v : Fin n) : 0 ≤ (st.frames 0).residual v :=
    ((hn 0 (Nat.zero_le _)).1 v (by simp [parentDomain])).1
  have hx (v : Fin n) : 0 ≤ st.x v := by
    simpa [relative] using ((hn 0 (Nat.zero_le _)).1 v (by simp [parentDomain])).2.1
  have hd (v : Fin n) : 0 ≤ LocalPush.deg g.graph v := by unfold LocalPush.deg; positivity
  have hs : 0 ≤ ∑ v, LocalPush.deg g.graph v*st.x v :=
    Finset.sum_nonneg (fun v _ => mul_nonneg (hd v) (hx v))
  have hb : (∑ v, LocalPush.deg g.graph v*(if v ∈ (st.frames 0).active then (st.frames 0).q else 4*st.x v)) ≤
      ∑ v, residual g.graph α s st.x v := by
    apply Finset.sum_le_sum
    intro v _
    rw [hi v]
    linarith [hr v]
  have hsum : (∑ v, LocalPush.deg g.graph v*(if v ∈ (st.frames 0).active then (st.frames 0).q else 4*st.x v)) =
      (st.frames 0).q*(volumeNat g (st.frames 0).active : ℝ)+
        4*(∑ v ∈ Finset.univ \ (st.frames 0).active, LocalPush.deg g.graph v*st.x v) := by
    rw [volume_real,Finset.mul_sum,Finset.mul_sum]
    have hfirst : (∑ v ∈ (st.frames 0).active, (st.frames 0).q*LocalPush.deg g.graph v) =
        ∑ v, if v ∈ (st.frames 0).active then (st.frames 0).q*LocalPush.deg g.graph v else 0 := by
      rw [←Finset.sum_filter]
      apply Finset.sum_congr
      · ext v; simp
      · intro v _; rfl
    have hsecond : (∑ v ∈ Finset.univ \ (st.frames 0).active, 4*(LocalPush.deg g.graph v*st.x v)) =
        ∑ v, if v ∉ (st.frames 0).active then 4*(LocalPush.deg g.graph v*st.x v) else 0 := by
      rw [←Finset.sum_filter]
      apply Finset.sum_congr
      · ext v; simp
      · intro v _; rfl
    rw [hfirst,hsecond,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : v ∈ (st.frames 0).active <;> simp [hv] <;> ring

  rw [hsum,residual_sum] at hb
  nlinarith [mul_nonneg hα hs]

lemma root_discoveryCredit_bound (g : InputGraph n) (s : Fin n) (α : ℝ) (hα : 0 ≤ α)
    (st : RecursiveState n) (hi : RootIdentity g s α st) (hn : NumericalInvariant g st)
    (hq : 0 ≤ (st.frames 0).q) : discoveryCredit g st 0 ≤ 3/8 := by
  have hh := root_reserve_mass_bound g s α hα st hi hn
  have hs : 0 ≤ ∑ v ∈ Finset.univ \ (st.frames 0).active, LocalPush.deg g.graph v*st.x v := by
    apply Finset.sum_nonneg
    intro v _
    apply mul_nonneg
    · unfold LocalPush.deg; positivity
    · simpa [relative] using ((hn 0 (Nat.zero_le _)).1 v (by simp [parentDomain])).2.1
  unfold discoveryCredit
  simp only [parentDomain,ite_true,relative]
  nlinarith

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.QueueMass

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma root_residual_mass_bound (g : InputGraph n) (s : Fin n) (α : ℝ) (hα : 0 ≤ α)
    (st : RecursiveState n) (hi : RootIdentity g s α st) (hn : NumericalInvariant g st)
    (hq : 0 ≤ (st.frames 0).q) : (∑ v, (st.frames 0).residual v) ≤ 1 := by
  classical
  have hx (v : Fin n) : 0 ≤ st.x v := by
    simpa [relative] using ((hn 0 (Nat.zero_le _)).1 v (by simp [parentDomain])).2.1
  have hd (v : Fin n) : 0 ≤ LocalPush.deg g.graph v := by unfold LocalPush.deg; positivity
  have hs : 0 ≤ ∑ v, LocalPush.deg g.graph v*st.x v :=
    Finset.sum_nonneg (fun v _ => mul_nonneg (hd v) (hx v))
  have hh : (∑ v, (st.frames 0).residual v) ≤ ∑ v, residual g.graph α s st.x v := by
    apply Finset.sum_le_sum
    intro v _
    rw [hi v]
    apply le_add_of_nonneg_right
    apply mul_nonneg (hd v)
    split
    · exact hq
    · have hh := hx v; positivity
  rw [residual_sum] at hh
  nlinarith [mul_nonneg hα hs]

lemma root_exterior_positive (g : InputGraph n) (st : RecursiveState n)
    (hk : KeysInvariant g st) (hiso : IsolateResidual g st) (v : Fin n)
    (hv : v ∈ (st.frames 0).exterior) : 0 < g.graph.degree v := by
  have hh := (((hk 0 (Nat.zero_le _)).1 v).mp hv).2.2
  by_contra hn
  have hd : g.graph.degree v = 0 := by omega
  have hr := hiso 0 (Nat.zero_le _) v hd
  simp [LocalPush.deg,hd,hr] at hh

lemma root_exterior_mass_bound (g : InputGraph n) (s : Fin n) (α : ℝ) (hα : 0 ≤ α)
    (st : RecursiveState n) (hi : RootIdentity g s α st) (hn : NumericalInvariant g st)
    (hk : KeysInvariant g st) (hq : 0 < (st.frames 0).q) :
    (volumeNat g (st.frames 0).exterior : ℝ) ≤ 1/(st.frames 0).q := by
  classical
  have hr := root_residual_mass_bound g s α hα st hi hn hq.le
  have hsum : (∑ v ∈ (st.frames 0).exterior, (st.frames 0).residual v) ≤ ∑ v, (st.frames 0).residual v :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun v _ _ =>
      ((hn 0 (Nat.zero_le _)).1 v (by simp [parentDomain])).1)
  have hh : (st.frames 0).q*(volumeNat g (st.frames 0).exterior : ℝ) ≤
      ∑ v ∈ (st.frames 0).exterior, (st.frames 0).residual v := by
    rw [volume_real,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v hv
    exact ((((hk 0 (Nat.zero_le _)).1 v).mp hv).2.2).le
  apply (le_div_iff₀ hq).mpr
  nlinarith [hh.trans (hsum.trans hr)]

lemma run_stored_volume_bound (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    (volumeNat g (recursiveRun m g s α q ℓ schedule t).stored : ℝ) ≤ 3/q := by
  let st := recursiveRun m g s α q ℓ schedule t
  have hi : StoredCreditInvariant g st := stored_credit_run m g s α q hα hq hs ℓ schedule t
  have hqr : (st.frames 0).q = q := root_threshold_run m g s α q ℓ schedule t
  have hqr0 : 0 ≤ (st.frames 0).q := by rw [hqr]; exact hq.le
  have hc := root_discoveryCredit_bound g s α hα.1.le st (root_identity_run m g s α q ℓ schedule t)
    (numerical_run m g s α q hα hq hs ℓ schedule t) hqr0
  have hv := root_volume_bound g s α hα.1.le st (root_identity_run m g s α q ℓ schedule t)
    (numerical_run m g s α q hα hq hs ℓ schedule t)
  rw [hqr] at hv
  unfold StoredCreditInvariant rootScanPotential at hi
  rw [hqr] at hi
  have hm := mul_le_mul_of_nonneg_left hi hq.le
  have hcancel : q*(5/q*discoveryCredit g st 0+(volumeNat g (st.frames 0).active : ℝ)) =
      5*discoveryCredit g st 0+q*(volumeNat g (st.frames 0).active : ℝ) := by
    field_simp [hq.ne'] <;> ring
  rw [hcancel] at hm
  change (volumeNat g st.stored : ℝ) ≤ _
  apply (le_div_iff₀ hq).mpr
  nlinarith

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.KeyCostBound

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma active_card_bound (g : InputGraph n) (s : Fin n) (α : ℝ) (hα : 0 ≤ α)
    (st : RecursiveState n) (hreg : RegionInvariant st) (hroot : RootIdentity g s α st)
    (hnum : NumericalInvariant g st) (hstore : StoredInvariant g st) (hq : 0 < (st.frames 0).q)
    (j : ℕ) (hj : j ≤ st.top) : ((st.frames j).active.card : ℝ) ≤ 1/(st.frames 0).q := by
  have hc : (st.frames j).active.card ≤ volumeNat g (st.frames 0).active :=
    (Finset.card_le_card (active_subset_root st hreg j hj)).trans
      (card_le_volume g (st.frames 0).active (fun v hv => hstore.2 v (hstore.1 0 (Nat.zero_le _) hv)))
  have hc' : ((st.frames j).active.card : ℝ) ≤ (volumeNat g (st.frames 0).active : ℝ) := by exact_mod_cast hc
  have hv := root_volume_bound g s α hα st hroot hnum
  apply hc'.trans
  apply (le_div_iff₀ hq).mpr
  nlinarith

lemma exterior_card_bound (g : InputGraph n) (s : Fin n) (α : ℝ) (hα : 0 ≤ α)
    (st : RecursiveState n) (hreg : RegionInvariant st) (hroot : RootIdentity g s α st)
    (hnum : NumericalInvariant g st) (hstore : StoredInvariant g st) (hkeys : KeysInvariant g st)
    (hiso : IsolateResidual g st) (hq : 0 < (st.frames 0).q)
    (j : ℕ) (hj : j ≤ st.top) : ((st.frames j).exterior.card : ℝ) ≤ 1/(st.frames 0).q := by
  by_cases hz : j = 0
  · subst j
    have hc := card_le_volume g (st.frames 0).exterior (fun v hv => root_exterior_positive g st hkeys hiso v hv)
    have hc' : ((st.frames 0).exterior.card : ℝ) ≤ (volumeNat g (st.frames 0).exterior : ℝ) := by exact_mod_cast hc
    exact hc'.trans (root_exterior_mass_bound g s α hα st hroot hnum hkeys hq)
  · have hp : parentDomain st j ⊆ (st.frames 0).active :=
      parent_domain_nested st hreg 0 j (Nat.pos_of_ne_zero hz) hj
    have hc := Finset.card_le_card (((hreg j hj).2.1.trans Finset.sdiff_subset).trans hp)
    have hc' : ((st.frames j).exterior.card : ℝ) ≤ ((st.frames 0).active.card : ℝ) := by exact_mod_cast hc
    exact hc'.trans (active_card_bound g s α hα st hreg hroot hnum hstore hq 0 (Nat.zero_le _))

lemma keyCost_log_bound (g : InputGraph n) (s : Fin n) (α : ℝ) (hα : 0 ≤ α)
    (st : RecursiveState n) (hreg : RegionInvariant st) (hroot : RootIdentity g s α st)
    (hnum : NumericalInvariant g st) (hstore : StoredInvariant g st) (hkeys : KeysInvariant g st)
    (hiso : IsolateResidual g st) (hq : 0 < (st.frames 0).q)
    (hvol : (volumeNat g st.stored : ℝ) ≤ 3/(st.frames 0).q) :
    (keyCost st : ℝ) ≤ 1+Real.logb 2 (2+(3+2*(st.top+1 : ℕ))/(st.frames 0).q) := by
  classical
  let L := 2+st.stored.card+∑ i ∈ Finset.range (st.top+1), ((st.frames i).exterior.card+(st.frames i).active.card)
  have hS : (st.stored.card : ℝ) ≤ 3/(st.frames 0).q := by
    have hh := card_le_volume g st.stored hstore.2
    exact (show (st.stored.card : ℝ) ≤ (volumeNat g st.stored : ℝ) by exact_mod_cast hh).trans hvol
  have hsum : ((∑ i ∈ Finset.range (st.top+1), ((st.frames i).exterior.card+(st.frames i).active.card) : ℕ) : ℝ) ≤
      (st.top+1 : ℕ)*(2/(st.frames 0).q) := by
    push_cast
    calc
      _ ≤ ∑ i ∈ Finset.range (st.top+1), (2/(st.frames 0).q) := by
        apply Finset.sum_le_sum
        intro i hi
        have his : i ≤ st.top := by have := Finset.mem_range.mp hi; omega
        have ha := active_card_bound g s α hα st hreg hroot hnum hstore hq i his
        have he := exterior_card_bound g s α hα st hreg hroot hnum hstore hkeys hiso hq i his
        calc
          _ ≤ 1/(st.frames 0).q+1/(st.frames 0).q := add_le_add he ha
          _ = _ := by ring
      _ = _ := by simp
  have hL : (L : ℝ) ≤ 2+(3+2*(st.top+1 : ℕ))/(st.frames 0).q := by
    calc
      (L : ℝ) = 2+(st.stored.card : ℝ)+
          ((∑ i ∈ Finset.range (st.top+1), ((st.frames i).exterior.card+(st.frames i).active.card) : ℕ) : ℝ) := by
        simp only [L,Nat.cast_add,Nat.cast_ofNat]
      _ ≤ 2+3/(st.frames 0).q+(st.top+1 : ℕ)*(2/(st.frames 0).q) :=
        add_le_add (add_le_add (le_refl (2 : ℝ)) hS) hsum
      _ = _ := by push_cast; ring
  have hLp : (0 : ℝ) < (L : ℝ) := by
    have hh : 2 ≤ L := by dsimp [L]; omega
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hh)
  have hlog := (Real.log2_le_logb L).trans (Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hLp hL)
  change ((1+Nat.log2 L : ℕ) : ℝ) ≤ _
  push_cast
  simpa only [Nat.cast_add,Nat.cast_one] using add_le_add (le_refl (1 : ℝ)) hlog

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RunKeyCost

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
variable {n : ℕ}

lemma run_keyCost_linear (m : SolveModel) (g : InputGraph n) (s : Fin n) (α ε : ℝ)
    (hα : 0 < α ∧ α < 1) (hε : 0 < ε ∧ ε ≤ 1) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    (keyCost (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t) : ℝ) ≤
      (1+(Real.log 128+4)/Real.log 2)*(2+Real.log (2/ε)+(ℓ : ℝ)) := by
  let q := rootThreshold ε ℓ
  let st := recursiveRun m g s α q ℓ schedule t
  have he : 0 < ε := hε.1
  have hq : 0 < q := by dsimp [q,rootThreshold,kappa]; positivity
  have hqr : (st.frames 0).q = q := root_threshold_run m g s α q ℓ schedule t
  have hvol : (volumeNat g st.stored : ℝ) ≤ 3/(st.frames 0).q := by
    rw [hqr]
    exact run_stored_volume_bound m g s α q hα hq hs ℓ schedule t
  have hK := keyCost_log_bound g s α hα.1.le st (region_run m g s α q ℓ schedule t)
    (root_identity_run m g s α q ℓ schedule t) (numerical_run m g s α q hα hq hs ℓ schedule t)
    (stored_run m g s α q hq.le hs ℓ schedule t) (keys_run m g s α q hq.le ℓ schedule t)
    (isolate_run m g s α q hs ℓ schedule t) (by rw [hqr]; exact hq) hvol
  rw [hqr] at hK
  exact hK.trans (queue_log_overhead_bound ε hε ℓ st.top (depth_run m g s α q ℓ schedule t))

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.SolveChargeBounds

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation

lemma solveCharge_size_bound (m : SolveModel) (k q : ℕ) (V : ℝ) (hV : 0 ≤ V)
    (hs : (k+q : ℝ) ≤ V) :
    solveCharge m k q ≤ ENNReal.ofReal ((1+m.constant)*(V+1)*(1+Real.log (2+V))^m.logPower) := by
  have hm0 : 0 ≤ m.constant := m.positive.le
  have hs0 : (0 : ℝ) ≤ (k+q : ℝ) := by positivity
  have hL : 1 ≤ 1+Real.log (2+V) := by
    have hh := Real.log_nonneg (show (1 : ℝ) ≤ 2+V by linarith)
    linarith
  have hLs : 0 ≤ 1+Real.log (2+(k+q : ℝ)) := by
    have hh := Real.log_nonneg (show (1 : ℝ) ≤ 2+(k+q : ℝ) by linarith)
    linarith
  have hlog : 1+Real.log (2+(k+q : ℝ)) ≤ 1+Real.log (2+V) :=
    add_le_add le_rfl (Real.log_le_log (by positivity : 0 < 2+(k+q : ℝ)) (by linarith : 2+(k+q : ℝ) ≤ 2+V))
  have hp : (1+Real.log (2+(k+q : ℝ)))^m.logPower ≤ (1+Real.log (2+V))^m.logPower := by
    gcongr
  have hterm : m.constant*(k+q : ℝ)*(1+Real.log (2+(k+q : ℝ)))^m.logPower ≤
      m.constant*V*(1+Real.log (2+V))^m.logPower := by
    gcongr
  have hpow : 1 ≤ (1+Real.log (2+V))^m.logPower := one_le_pow₀ hL
  have h1 : 1 ≤ (V+1)*(1+Real.log (2+V))^m.logPower := by
    nlinarith [mul_nonneg hV (le_trans zero_le_one hpow)]
  have hnext : m.constant*V*(1+Real.log (2+V))^m.logPower ≤
      m.constant*(V+1)*(1+Real.log (2+V))^m.logPower := by
    gcongr
    linarith
  have hreal : 1+m.constant*(k+q : ℝ)*(1+Real.log (2+(k+q : ℝ)))^m.logPower ≤
      (1+m.constant)*(V+1)*(1+Real.log (2+V))^m.logPower := by
    calc
      _ ≤ 1+m.constant*V*(1+Real.log (2+V))^m.logPower := add_le_add le_rfl hterm
      _ ≤ (V+1)*(1+Real.log (2+V))^m.logPower+
          m.constant*(V+1)*(1+Real.log (2+V))^m.logPower := add_le_add h1 hnext
      _ = _ := by ring
  unfold solveCharge
  rw [←ENNReal.ofReal_one,←ENNReal.ofReal_add zero_le_one (by positivity)]
  exact ENNReal.ofReal_le_ofReal hreal

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.JointChargeBounds

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma jointCost_volume_bound (m : SolveModel) (g : InputGraph n) (st : RecursiveState n)
    (T : Finset (Fin n)) (hT : ∀ v ∈ T, 0 < g.graph.degree v) (K : ℝ)
    (hK : 1 ≤ K) (hkey : (keyCost st : ℝ) ≤ K)
    (hlog : 1+Real.log (2+3*(volumeNat g T : ℝ)) ≤ K) :
    jointCost m g st T ≤ ENNReal.ofReal
      ((3*(1+m.constant)+64)*(st.top+1 : ℕ)*((volumeNat g T : ℝ)+1)*K^(m.logPower+1)) := by
  have hm : 0 ≤ m.constant := m.positive.le
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  have hvol : 0 ≤ (volumeNat g T : ℝ) := by positivity
  have hcard : (T.card : ℝ) ≤ (volumeNat g T : ℝ) := by exact_mod_cast card_le_volume g T hT
  have hsize : (T.card+(volumeNat g T+T.card) : ℝ) ≤ 3*(volumeNat g T : ℝ) := by
    push_cast
    linarith
  have hsolve := solveCharge_size_bound m T.card (volumeNat g T+T.card) (3*(volumeNat g T : ℝ))
    (by positivity) (by push_cast; exact hsize)
  have hbase : 0 ≤ 1+Real.log (2+3*(volumeNat g T : ℝ)) := by
    have hh := Real.log_nonneg (show (1 : ℝ) ≤ 2+3*(volumeNat g T : ℝ) by linarith)
    linarith
  have hp : (1+Real.log (2+3*(volumeNat g T : ℝ)))^m.logPower ≤ K^m.logPower := by gcongr
  have hpow : K^m.logPower ≤ K^(m.logPower+1) := by
    rw [pow_succ]
    exact le_mul_of_one_le_right (pow_nonneg hK0 _) hK
  have hKpow : K ≤ K^(m.logPower+1) := by
    rw [pow_succ]
    have hh : 1 ≤ K^m.logPower := one_le_pow₀ hK
    nlinarith
  have ht1 : (1 : ℝ) ≤ (st.top+1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le st.top)
  have hsolveReal : (1+m.constant)*(3*(volumeNat g T : ℝ)+1)*
      (1+Real.log (2+3*(volumeNat g T : ℝ)))^m.logPower ≤
      3*(1+m.constant)*(st.top+1 : ℕ)*((volumeNat g T : ℝ)+1)*K^(m.logPower+1) := by
    calc
      _ ≤ (1+m.constant)*(3*(volumeNat g T : ℝ)+1)*K^(m.logPower+1) := mul_le_mul_of_nonneg_left (hp.trans hpow) (by positivity)
      _ ≤ 3*(1+m.constant)*((volumeNat g T : ℝ)+1)*K^(m.logPower+1) := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hK0 _)
        nlinarith
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left ht1
          (show 0 ≤ 3*(1+m.constant)*((volumeNat g T : ℝ)+1)*K^(m.logPower+1) by positivity)
        calc
          _ = (3*(1+m.constant)*((volumeNat g T : ℝ)+1)*K^(m.logPower+1))*1 := by ring
          _ ≤ (3*(1+m.constant)*((volumeNat g T : ℝ)+1)*K^(m.logPower+1))*(st.top+1 : ℕ) := hh
          _ = _ := by ring
  have hscalar : ((32*(st.top+1)*(volumeNat g T+T.card+1)*keyCost st : ℕ) : ℝ) ≤
      64*(st.top+1 : ℕ)*((volumeNat g T : ℝ)+1)*K^(m.logPower+1) := by
    push_cast
    have hkey' := hkey.trans hKpow
    have ht0 : (0 : ℝ) ≤ (st.top : ℝ)+1 := by positivity
    calc
      _ ≤ 32*((st.top : ℝ)+1)*(2*((volumeNat g T : ℝ)+1))*K^(m.logPower+1) := by
        gcongr <;> linarith
      _ = _ := by push_cast; ring
  unfold jointCost
  have hbound := add_le_add (hsolve.trans (ENNReal.ofReal_le_ofReal hsolveReal))
    (ENNReal.ofReal_le_ofReal hscalar)
  rw [←ENNReal.ofReal_add (by positivity) (by positivity)] at hbound
  have heq : 3*(1+m.constant)*(st.top+1 : ℕ)*((volumeNat g T : ℝ)+1)*K^(m.logPower+1)+
      64*(st.top+1 : ℕ)*((volumeNat g T : ℝ)+1)*K^(m.logPower+1) =
      (3*(1+m.constant)+64)*(st.top+1 : ℕ)*((volumeNat g T : ℝ)+1)*K^(m.logPower+1) := by ring
  rw [heq] at hbound
  simpa only [ENNReal.ofReal_natCast] using hbound

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PrimitiveOverhead

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma volumeNat_mono {n : ℕ} (g : InputGraph n) {S T : Finset (Fin n)} (hST : S ⊆ T) :
    volumeNat g S ≤ volumeNat g T := Finset.sum_le_sum_of_subset hST

lemma uniform_jointCost_overhead (m : SolveModel) :
    ∃ (C : ℝ) (c : ℕ), 0 < C ∧ 0 < c ∧
      ∀ (n : ℕ) (g : InputGraph n) (s : Fin n) (α ε : ℝ) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ),
        (0 < α ∧ α < 1) → (0 < ε ∧ ε ≤ 1) → 0 < g.graph.degree s →
        ∀ T : Finset (Fin n), T ⊆ ((recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t).frames 0).active →
          jointCost m g (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t) T ≤
            ENNReal.ofReal (overhead C c ε ℓ*((volumeNat g T : ℝ)+1)) := by
  let A := primitiveLogConstant
  let C := (3*(1+m.constant)+64)*A^(m.logPower+1)
  let c := m.logPower+2
  have hA : 1 ≤ A := primitiveLogConstant_bounds.1
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hm := m.positive
  have hcoef : 0 < 3*(1+m.constant)+64 := by positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,c,hC,by dsimp [c]; omega,?_⟩
  intro n g s α ε ℓ schedule t hα hε hs T hT
  let q := rootThreshold ε ℓ
  let st := recursiveRun m g s α q ℓ schedule t
  let B := 2+Real.log (2/ε)+(ℓ : ℝ)
  let K := A*B
  have he : 0 < ε := hε.1
  have hq : 0 < q := by dsimp [q,rootThreshold,kappa]; positivity
  have hL : 0 ≤ Real.log (2/ε) :=
    Real.log_nonneg ((le_div_iff₀ he).mpr (by linarith [hε.2]))
  have hB : 1 ≤ B := by
    have hel : (0 : ℝ) ≤ (ℓ : ℝ) := by positivity
    dsimp only [B]
    linarith
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  have hK : 1 ≤ K := hB.trans (le_mul_of_one_le_left hB0 hA)
  have hregion : RegionInvariant st := region_run m g s α q ℓ schedule t
  have hstored : StoredInvariant g st := stored_run m g s α q hq.le hs ℓ schedule t
  have hpos : ∀ v ∈ T, 0 < g.graph.degree v := fun v hv => hstored.2 v (hstored.1 0 (Nat.zero_le _) (hT hv))
  have hvmono : (volumeNat g T : ℝ) ≤ (volumeNat g (st.frames 0).active : ℝ) := by
    exact_mod_cast volumeNat_mono g hT
  have hvroot : (volumeNat g (st.frames 0).active : ℝ) ≤ 1/q :=
    (run_root_volume_bound m g s α q hα hq hs ℓ schedule t).1
  have hkey0 := run_keyCost_linear m g s α ε hα hε hs ℓ schedule t
  have hkey : (keyCost st : ℝ) ≤ K := hkey0.trans
    (mul_le_mul_of_nonneg_right primitiveLogConstant_bounds.2.1 hB0)
  have hlog : 1+Real.log (2+3*(volumeNat g T : ℝ)) ≤ K :=
    solver_log_linear ε hε ℓ (volumeNat g T) (by positivity) (hvmono.trans hvroot)
  have htop : ((st.top+1 : ℕ) : ℝ) ≤ B := by
    have hh : st.top ≤ ℓ := depth_run m g s α q ℓ schedule t
    have hh' : (st.top : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hh
    dsimp [B]
    push_cast
    linarith
  have hcharge := jointCost_volume_bound m g st T hpos K hK hkey hlog
  apply hcharge.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (3*(1+m.constant)+64)*B*((volumeNat g T : ℝ)+1)*K^(m.logPower+1) := by
      gcongr
    _ = overhead C c ε ℓ*((volumeNat g T : ℝ)+1) := by
      change (3*(1+m.constant)+64)*B*((volumeNat g T : ℝ)+1)*(A*B)^(m.logPower+1) =
        ((3*(1+m.constant)+64)*A^(m.logPower+1))*B^(m.logPower+2)*((volumeNat g T : ℝ)+1)
      rw [mul_pow,show m.logPower+2=(m.logPower+1)+1 by omega,pow_succ]
      ring

end
end NearlyOptimalPPR.Computation

attribute [local instance] Classical.propDecidable
set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
open scoped ENNReal

theorem solution (m : SolveModel) :
    ∃ (C : ℝ) (c : ℕ), 0 < C ∧ 0 < c ∧
      ∀ (n : ℕ) (g : InputGraph n) (s : Fin n) (α ε : ℝ) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ),
        (0 < α ∧ α < 1) → (0 < ε ∧ ε ≤ 1) → 0 < g.graph.degree s →
        ∀ T : Finset (Fin n), T ⊆ ((recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t).frames 0).active →
          jointCost m g (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t) T ≤
            ENNReal.ofReal (overhead C c ε ℓ*((volumeNat g T : ℝ)+1)) := by
  exact uniform_jointCost_overhead m
