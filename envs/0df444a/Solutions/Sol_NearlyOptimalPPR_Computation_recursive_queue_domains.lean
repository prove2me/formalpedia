-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.recursive_queue_domains
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:32:05.366887+00:00
-- url     : https://prove2.me/submissions/5d858d0c-7e0b-4746-9223-78ed7472698e

import Definitions.Def_NearlyOptimalPPR_Computation_proof_invariants


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

set_option maxHeartbeats 1000000 in
lemma depth_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (hi : st.top ≤ ℓ) :
    (recursiveStep m g s α ℓ schedule st).top ≤ ℓ := by
  classical
  cases hp : pendingPush st with
  | none =>
    cases hpc : (st.frames st.top).pc <;>
      simp [recursiveStep,hpc,hp,debit] <;> (try split_ifs) <;> simp_all <;> omega
  | some p =>
    obtain ⟨t,v⟩ := p
    cases hpc : (st.frames st.top).pc <;>
      simp [recursiveStep,hpc,hp,debit] <;> (try split_ifs) <;> simp_all <;> omega

lemma depth_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    (recursiveRun m g s α q ℓ schedule t).top ≤ ℓ := by
  induction t with
  | zero => simp [recursiveRun,recursiveInit]
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using depth_step m g s α ℓ schedule _ ih

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RegionInvariants

set_option autoImplicit false
open Finset
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

@[simp] lemma refresh_active (g : InputGraph n) (st : RecursiveState n)
    (T : Finset (Fin n)) (i : ℕ) :
    ((refreshKeys g st T).frames i).active = (st.frames i).active := by
  by_cases hi : i ≤ st.top <;> simp [refreshKeys,hi]

lemma parentDomain_same (st st' : RecursiveState n)
    (ha : ∀ i, (st'.frames i).active = (st.frames i).active) :
    ∀ i, parentDomain st' i = parentDomain st i := by
  intro i
  unfold parentDomain
  split <;> simp [ha]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PendingPush

set_option autoImplicit false
open Finset
namespace NearlyOptimalPPR.Computation

lemma pending_push_member {n : ℕ} (st : RecursiveState n) (t : ℕ) (v : Fin n)
    (hp : pendingPush st = some (t,v)) : t ≤ st.top ∧ v ∈ (st.frames t).exterior := by
  classical
  unfold pendingPush at hp
  dsimp only at hp
  split at hp
  · rename_i hlevel
    split at hp
    · rename_i hrow
      have hh := Option.some.inj hp
      have ht := congrArg Prod.fst hh
      have hv := congrArg Prod.snd hh
      dsimp only at ht hv
      rw [← ht, ← hv]
      refine ⟨?_, Finset.min'_mem _ hrow⟩
      have hl := Finset.min'_mem _ hlevel
      exact Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hl).1)
    · simp at hp
  · simp at hp

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PPRLinearAlgebra

set_option autoImplicit false
open Finset Matrix
open NearlyOptimalPPR.Computation

namespace NearlyOptimalPPR.Computation
variable {V : Type*} [Fintype V] [DecidableEq V]
local instance positive_adjacency (G : SimpleGraph V) [DecidableRel G.Adj] :
    DecidableRel (positiveGraph G).Adj :=
  inferInstanceAs (DecidableRel (G.induce {v | 0 < G.degree v}).Adj)

lemma lap_mul_apply (G : SimpleGraph V) [DecidableRel G.Adj]
    (α : ℝ) (x : V → ℝ) (v : V) :
    (LocalPush.Lα G α *ᵥ x) v =
      LocalPush.deg G v * x v - (1 - α) * ∑ u ∈ G.neighborFinset v, x u := by
  simp [LocalPush.Lα, LocalPush.degM, LocalPush.adjM, sub_mulVec,
    smul_mulVec, SimpleGraph.adjMatrix_mulVec_apply, mulVec_diagonal]

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootIdentityControl

set_option autoImplicit false
open Finset
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma solveOn_outside (g : InputGraph n) (α : ℝ) (T : Finset (Fin n))
    (b : Fin n → ℝ) (v : Fin n) (hv : v ∉ T) : solveOn g α T b v = 0 := by
  classical
  simp [solveOn,hv]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.QueueInvariant

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma keys_refresh_transition (g : InputGraph n) (st u : RecursiveState n)
    (T : Finset (Fin n)) (hi : KeysInvariant g st) (ht : u.top = st.top)
    (hE : ∀ i ≤ st.top, (u.frames i).exterior = (st.frames i).exterior)
    (hH : ∀ i ≤ st.top, (u.frames i).high = (st.frames i).high)
    (hext : ∀ i ≤ st.top, ∀ v ∉ T, exteriorKey g u i v ↔ exteriorKey g st i v)
    (hhigh : ∀ i ≤ st.top, ∀ v ∉ T, highKey g u i v ↔ highKey g st i v) :
    KeysInvariant g (refreshKeys g u T) := by
  classical
  intro i hh
  have hiu : i ≤ u.top := hh
  have his : i ≤ st.top := by simpa [ht] using hiu
  have hp : parentDomain (refreshKeys g u T) i = parentDomain u i := by
    exact parentDomain_same u (refreshKeys g u T) (fun j => refresh_active g u T j) i
  have hek (v : Fin n) : exteriorKey g (refreshKeys g u T) i v ↔ exteriorKey g u i v := by
    unfold exteriorKey
    rw [hp]
    simp [refreshKeys,hiu]
  have hhk (v : Fin n) : highKey g (refreshKeys g u T) i v ↔ highKey g u i v := by
    simp [highKey,refreshKeys,hiu]
  constructor
  · intro v
    rw [hek]
    by_cases hv : v ∈ T
    · simp [refreshKeys,hiu,hv,exteriorKey,hp]
    · have he := (hi i his).1 v
      have hk := hext i his v hv
      simp only [refreshKeys,hiu,ite_true,Finset.mem_union,Finset.mem_sdiff,Finset.mem_filter,hv,
        and_false,false_and,or_false,and_true,not_false_eq_true]
      rw [hE i his]
      rw [he,← hk]
  · intro v
    rw [hhk]
    by_cases hv : v ∈ T
    · simp [refreshKeys,hiu,hv,highKey]
    · have he := (hi i his).2 v
      have hk := hhigh i his v hv
      simp only [refreshKeys,hiu,ite_true,Finset.mem_union,Finset.mem_sdiff,Finset.mem_filter,hv,
        and_false,false_and,or_false,and_true,not_false_eq_true]
      rw [hH i his]
      rw [he,← hk]

lemma keys_init (g : InputGraph n) (s : Fin n) (q : ℝ) (hq : 0 ≤ q)
    (ℓ : ℕ) (schedule : BlockSchedule) : KeysInvariant g (recursiveInit g s q ℓ schedule) := by
  classical
  intro i hi
  have he : i = 0 := by change i ≤ 0 at hi; omega
  subst i
  constructor
  · intro v
    by_cases hv : v = s
    · subst v
      simp [recursiveInit,freshFrame,emptyFrame,exteriorKey,parentDomain]
    · have hn : ¬q*LocalPush.deg g.graph v < 0 := by
        apply not_lt.mpr
        apply mul_nonneg hq
        unfold LocalPush.deg
        positivity
      simp [recursiveInit,freshFrame,emptyFrame,exteriorKey,parentDomain,LocalPush.e,
        Pi.single_apply,hv,hn]
  · intro v
    simp [recursiveInit,freshFrame,emptyFrame,highKey]

lemma keys_transport (g : InputGraph n) (st u : RecursiveState n)
    (hi : KeysInvariant g st) (ht : u.top ≤ st.top)
    (hE : ∀ i ≤ u.top, (u.frames i).exterior = (st.frames i).exterior)
    (hH : ∀ i ≤ u.top, (u.frames i).high = (st.frames i).high)
    (hext : ∀ i ≤ u.top, ∀ v, exteriorKey g u i v ↔ exteriorKey g st i v)
    (hhigh : ∀ i ≤ u.top, ∀ v, highKey g u i v ↔ highKey g st i v) :
    KeysInvariant g u := by
  intro i hh
  constructor
  · intro v
    rw [hE i hh,hext i hh v]
    exact (hi i (hh.trans ht)).1 v
  · intro v
    rw [hH i hh,hhigh i hh v]
    exact (hi i (hh.trans ht)).2 v

lemma keys_touched_update (g : InputGraph n) (st u : RecursiveState n)
    (T : Finset (Fin n)) (hi : KeysInvariant g st) (ht : u.top = st.top)
    (hE : ∀ i ≤ st.top, (u.frames i).exterior = (st.frames i).exterior)
    (hH : ∀ i ≤ st.top, (u.frames i).high = (st.frames i).high)
    (hq : ∀ i ≤ st.top, (u.frames i).q = (st.frames i).q)
    (hθ : ∀ i ≤ st.top, (u.frames i).theta = (st.frames i).theta)
    (hA : ∀ i ≤ st.top, ∀ v ∉ T, v ∈ (u.frames i).active ↔ v ∈ (st.frames i).active)
    (hr : ∀ i ≤ st.top, ∀ v ∉ T, (u.frames i).residual v = (st.frames i).residual v) :
    KeysInvariant g (refreshKeys g u T) := by
  apply keys_refresh_transition g st u T hi ht hE hH
  · intro i hh v hv
    have hp : v ∈ parentDomain u i ↔ v ∈ parentDomain st i := by
      unfold parentDomain
      split
      · rfl
      · exact hA (i-1) (by omega) v hv
    simp only [exteriorKey,hp,hA i hh v hv,hq i hh,hr i hh v hv]
  · intro i hh v hv
    simp only [highKey,hA i hh v hv,hθ i hh,hr i hh v hv]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.QueueExterior

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma observe_changeFrame {β : Type*} (F : NormalizeFrame n → β) (st : RecursiveState n)
    (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n)
    (hf : F (f (st.frames j)) = F (st.frames j)) (i : ℕ) :
    F ((changeFrame st j f).frames i) = F (st.frames i) := by
  by_cases he : i = j
  · subst i
    simpa [changeFrame] using hf
  · simp [changeFrame,he]

set_option maxHeartbeats 1000000 in
lemma keys_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hi : KeysInvariant g st) (t : ℕ) (v : Fin n) :
    KeysInvariant g (exteriorPush g α st t v) := by
  classical
  let f := st.frames t
  let d := LocalPush.deg g.graph v
  let δ := min (f.residual v/(5*d)) (3*f.q/8-relative st t v)
  let base := rawExterior g α st t v δ
  let admitted := changeFrame base t (fun fi =>
    {fi with
      active := insert v fi.active
      residual := Function.update fi.residual v (fi.residual v+f.q*d/2)
      W := fi.W + if fi.openBudget then (t+3 : ℕ)*f.q*d/2 else 0})
  let child := if t < st.top then changeFrame admitted (t+1) (fun fc =>
    {fc with
      reference := Function.update fc.reference v (admitted.x v)
      residual := Function.update fc.residual v ((admitted.frames t).residual v)}) else admitted
  let final := if t = 0 then {child with boundaryEdges := st.boundaryEdges+
    (g.neighbors v).length-2*((g.neighbors v).filter (fun w => w ∈ f.active)).length} else child
  let prepared := if relative st t v+δ = 3*f.q/8 then final else base
  trace "queue exterior: starting static view"
  have hstatic (i : ℕ) : queueStaticView (prepared.frames i) = queueStaticView (st.frames i) := by
    have hb (i : ℕ) : queueStaticView (base.frames i) = queueStaticView (st.frames i) := by
      by_cases hh : i ≤ st.top <;> simp [base,rawExterior,hh,queueStaticView]
    have ha (i : ℕ) : queueStaticView (admitted.frames i) = queueStaticView (st.frames i) := by
      exact (observe_changeFrame queueStaticView base t _ rfl i).trans (hb i)
    have hc (i : ℕ) : queueStaticView (child.frames i) = queueStaticView (st.frames i) := by
      unfold child
      split
      · exact (observe_changeFrame queueStaticView admitted (t+1) _ rfl i).trans (ha i)
      · exact ha i
    have hf (i : ℕ) : queueStaticView (final.frames i) = queueStaticView (st.frames i) := by
      unfold final
      split <;> exact hc i
    unfold prepared
    split
    · exact hf i
    · exact hb i
  trace "queue exterior: static view proved"
  have hrow (i : ℕ) (w : Fin n) (hw : w ∉ insert v (g.neighbors v).toFinset) :
      queueRowView (prepared.frames i) w = queueRowView (st.frames i) w := by
    have hwv : w ≠ v := by intro he; subst w; exact hw (Finset.mem_insert_self _ _)
    have hadj : ¬g.graph.Adj w v := by
      intro ha
      apply hw
      exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr ((g.correct v w).mpr ha.symm))
    have hb (i : ℕ) : queueRowView (base.frames i) w = queueRowView (st.frames i) w := by
      by_cases hh : i ≤ st.top <;> simp [base,rawExterior,hh,queueRowView,hwv,hadj]
    have ha (i : ℕ) : queueRowView (admitted.frames i) w = queueRowView (st.frames i) w := by
      apply Eq.trans _ (hb i)
      apply observe_changeFrame (fun f => queueRowView f w) base t
      simp [queueRowView,hwv]
    have hc (i : ℕ) : queueRowView (child.frames i) w = queueRowView (st.frames i) w := by
      unfold child
      split
      · apply Eq.trans _ (ha i)
        apply observe_changeFrame (fun f => queueRowView f w) admitted (t+1)
        simp [queueRowView,hwv]
      · exact ha i
    have hf (i : ℕ) : queueRowView (final.frames i) w = queueRowView (st.frames i) w := by
      unfold final
      split <;> exact hc i
    unfold prepared
    split
    · exact hf i
    · exact hb i
  trace "queue exterior: row view proved"
  have htop : prepared.top = st.top := by
    have hc : child.top = st.top := by unfold child; split <;> rfl
    have hf : final.top = st.top := by unfold final; split <;> exact hc
    unfold prepared
    split
    · exact hf
    · rfl
  trace "queue exterior: top proved"
  have hkeys : KeysInvariant g (refreshKeys g prepared (insert v (g.neighbors v).toFinset)) := by
    apply keys_touched_update g st prepared _ hi htop
    · intro i _
      exact congrArg (fun z => z.2.2.1) (hstatic i)
    · intro i _
      exact congrArg (fun z => z.2.2.2) (hstatic i)
    · intro i _
      exact congrArg Prod.fst (hstatic i)
    · intro i _
      exact congrArg (fun z => z.2.1) (hstatic i)
    · intro i _ w hw
      exact Iff.of_eq (congrArg Prod.fst (hrow i w hw))
    · intro i _ w hw
      exact congrArg Prod.snd (hrow i w hw)
  trace "queue exterior: keys proved"
  unfold KeysInvariant exteriorKey highKey parentDomain
  change KeysInvariant g (refreshKeys g prepared (insert v (g.neighbors v).toFinset))
  exact hkeys

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.IsolateResidual

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma isolate_lap_row (g : InputGraph n) (α : ℝ) (h : Fin n → ℝ)
    (v : Fin n) (hv : g.graph.degree v = 0) : (LocalPush.Lα g.graph α *ᵥ h) v = 0 := by
  have he : g.graph.neighborFinset v = ∅ := Finset.card_eq_zero.mp (by simpa using hv)
  simp [lap_mul_apply,he,LocalPush.deg,hv]

lemma isolate_residual_init (g : InputGraph n) (s : Fin n) (hs : 0 < g.graph.degree s)
    (q : ℝ) (ℓ : ℕ) (schedule : BlockSchedule) :
    IsolateResidual g (recursiveInit g s q ℓ schedule) := by
  intro i hi v hv
  have he : i = 0 := by change i ≤ 0 at hi; omega
  subst i
  have hvs : v ≠ s := by intro he; subst v; omega
  simp [recursiveInit,freshFrame,LocalPush.e,Pi.single_apply,hvs]

lemma isolate_residual_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (h : Fin n → ℝ) (hi : IsolateResidual g st) :
    IsolateResidual g (jointUpdate g α st h) := by
  intro i hh v hv
  have his : i ≤ st.top := hh
  have hl := isolate_lap_row g α h v hv
  simp [jointUpdate,his,hl,hi i his v hv]

lemma isolate_residual_transport (g : InputGraph n) (st u : RecursiveState n)
    (hi : IsolateResidual g st) (ht : u.top ≤ st.top)
    (hr : ∀ i ≤ u.top, (u.frames i).residual = (st.frames i).residual) :
    IsolateResidual g u := by
  intro i hh v hv
  rw [hr i hh]
  exact hi i (hh.trans ht) v hv

lemma isolate_residual_changeFrame (g : InputGraph n) (st : RecursiveState n)
    (hi : IsolateResidual g st) (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n)
    (hf : ∀ v, g.graph.degree v = 0 → j ≤ st.top → (f (st.frames j)).residual v = 0) :
    IsolateResidual g (changeFrame st j f) := by
  intro i hh v hv
  have his : i ≤ st.top := hh
  by_cases he : i = j
  · subst i
    simpa [changeFrame] using hf v hv his
  · simpa [changeFrame,he] using hi i his v hv

lemma isolate_pending_positive (g : InputGraph n) (st : RecursiveState n)
    (hi : IsolateResidual g st) (hk : KeysInvariant g st)
    (t : ℕ) (v : Fin n) (hp : pendingPush st = some (t,v)) : 0 < g.graph.degree v := by
  obtain ⟨ht,hm⟩ := pending_push_member st t v hp
  have hh := ((hk t ht).1 v).mp hm
  by_contra hn
  have hz : g.graph.degree v = 0 := by omega
  have hr := hi t ht v hz
  have hf := hh.2.2
  rw [hr] at hf
  simp [LocalPush.deg,hz] at hf

lemma isolate_metadata (g : InputGraph n) (st : RecursiveState n) (hi : IsolateResidual g st)
    (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n)
    (hr : (f (st.frames j)).residual = (st.frames j).residual) :
    IsolateResidual g (changeFrame st j f) := by
  apply isolate_residual_changeFrame g st hi j f
  intro v hv hh
  rw [hr]
  exact hi j hh v hv

lemma isolate_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n))
    (hi : IsolateResidual g st) : IsolateResidual g (refreshKeys g st T) := by
  apply isolate_residual_transport g st (refreshKeys g st T) hi le_rfl
  intro i hh
  have his : i ≤ st.top := hh
  simp [refreshKeys,his]

lemma isolate_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hi : IsolateResidual g st) : IsolateResidual g (endCall g α st) := by
  classical
  unfold endCall
  dsimp only
  split
  · exact hi
  · intro i hh v hv
    exact hi i (hh.trans (Nat.sub_le _ _)) v hv

lemma isolate_newFrame (g : InputGraph n) (st : RecursiveState n) (f : NormalizeFrame n)
    (hi : IsolateResidual g st)
    (hf : ∀ v, g.graph.degree v = 0 → f.residual v = 0) :
    IsolateResidual g {st with top := st.top+1, frames := Function.update st.frames (st.top+1) f} := by
  intro i hh v hv
  change i ≤ st.top+1 at hh
  by_cases he : i = st.top+1
  · subst i
    simpa using hf v hv
  · have his : i ≤ st.top := by omega
    simpa [he] using hi i his v hv

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.IsolateExterior

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

set_option maxHeartbeats 1000000 in
lemma isolate_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hi : IsolateResidual g st) (t : ℕ) (ht : t ≤ st.top) (v : Fin n) :
    IsolateResidual g (exteriorPush g α st t v) := by
  classical
  let f := st.frames t
  let d := LocalPush.deg g.graph v
  let δ := min (f.residual v/(5*d)) (3*f.q/8-relative st t v)
  let base := rawExterior g α st t v δ
  let admitted := changeFrame base t (fun fi =>
    {fi with
      active := insert v fi.active
      residual := Function.update fi.residual v (fi.residual v+f.q*d/2)
      W := fi.W + if fi.openBudget then (t+3 : ℕ)*f.q*d/2 else 0})
  let child := if t < st.top then changeFrame admitted (t+1) (fun fc =>
    {fc with
      reference := Function.update fc.reference v (admitted.x v)
      residual := Function.update fc.residual v ((admitted.frames t).residual v)}) else admitted
  let final := if t = 0 then {child with boundaryEdges := st.boundaryEdges+
    (g.neighbors v).length-2*((g.neighbors v).filter (fun w => w ∈ f.active)).length} else child
  let prepared := if relative st t v+δ = 3*f.q/8 then final else base
  have hb : IsolateResidual g base := by
    intro i hh w hw
    have his : i ≤ st.top := hh
    have hn : ¬g.graph.Adj w v := by intro ha; have hp := ha.degree_pos_left; omega
    have hr := hi i his w hw
    by_cases he : w = v
    · subst w
      simp [base,rawExterior,his,hr,hn,LocalPush.deg,hw,d]
    · simp [base,rawExterior,his,hr,hn,he]
  have ha : IsolateResidual g admitted := by
    apply isolate_residual_changeFrame g base hb t
    intro w hw hh
    have hz := hb t hh w hw
    by_cases he : w = v
    · subst w
      simp [hz,Function.update_self,d,LocalPush.deg,hw]
    · simp [Function.update_of_ne he,hz]
  have hc : IsolateResidual g child := by
    unfold child
    split
    · apply isolate_residual_changeFrame g admitted ha (t+1)
      intro w hw hh
      have hz := ha (t+1) hh w hw
      by_cases he : w = v
      · subst w
        simp [ha t ht v hw]
      · simp [Function.update_of_ne he,hz]
    · exact ha
  have hf : IsolateResidual g final := by unfold final; split <;> exact hc
  have hp : IsolateResidual g prepared := by unfold prepared; split; exact hf; exact hb
  have hr : IsolateResidual g (refreshKeys g prepared (insert v (g.neighbors v).toFinset)) := by
    apply isolate_residual_transport g prepared (refreshKeys g prepared (insert v (g.neighbors v).toFinset)) hp le_rfl
    intro i hh
    have his : i ≤ prepared.top := hh
    simp [refreshKeys,his]
  unfold IsolateResidual
  change IsolateResidual g (refreshKeys g prepared (insert v (g.neighbors v).toFinset))
  exact hr

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.TouchedRows

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma untouched_not_adjacent (g : InputGraph n) (T : Finset (Fin n)) (v : Fin n)
    (hv : v ∉ touchedBy g T) : v ∉ T ∧ ∀ w ∈ T, ¬g.graph.Adj v w := by
  classical
  constructor
  · intro h
    apply hv
    exact Finset.mem_union_left _ h
  · intro w hw ha
    apply hv
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨w,hw,?_⟩
    simpa [g.correct] using ha.symm

lemma lap_untouched (g : InputGraph n) (α : ℝ) (T : Finset (Fin n))
    (h : Fin n → ℝ) (hs : ∀ v ∉ T, h v = 0) (v : Fin n)
    (hv : v ∉ touchedBy g T) : (LocalPush.Lα g.graph α *ᵥ h) v = 0 := by
  classical
  obtain ⟨hvT,hn⟩ := untouched_not_adjacent g T v hv
  rw [lap_mul_apply,hs v hvT,mul_zero]
  have hh : ∑ w ∈ g.graph.neighborFinset v, h w = 0 := by
    apply Finset.sum_eq_zero
    intro w hw
    apply hs w
    intro hwT
    exact hn w hwT (by simpa using hw)
  rw [hh,mul_zero,sub_zero]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.QueueSolves

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma keys_joint_refresh (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (T : Finset (Fin n)) (h : Fin n → ℝ) (hs : ∀ v ∉ T, h v = 0)
    (hi : KeysInvariant g st) :
    KeysInvariant g (refreshKeys g (jointUpdate g α st h) (touchedBy g T)) := by
  classical
  have ha (i : ℕ) : ((jointUpdate g α st h).frames i).active = (st.frames i).active := by
    by_cases he : i ≤ st.top <;> simp [jointUpdate,he]
  have hp := parentDomain_same st (jointUpdate g α st h) ha
  apply keys_refresh_transition g st (jointUpdate g α st h) (touchedBy g T) hi rfl
  · intro i hh
    simp [jointUpdate,hh]
  · intro i hh
    simp [jointUpdate,hh]
  · intro i hh v hv
    have hl := lap_untouched g α T h hs v hv
    unfold exteriorKey
    rw [hp]
    simp [jointUpdate,hh,hl]
  · intro i hh v hv
    have hl := lap_untouched g α T h hs v hv
    simp [highKey,jointUpdate,hh,hl]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.QueueControl

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma keys_changeFrame (g : InputGraph n) (st : RecursiveState n) (hi : KeysInvariant g st)
    (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n)
    (hq : (f (st.frames j)).q = (st.frames j).q)
    (hA : (f (st.frames j)).active = (st.frames j).active)
    (hr : (f (st.frames j)).residual = (st.frames j).residual)
    (hE : (f (st.frames j)).exterior = (st.frames j).exterior)
    (hH : j ≤ st.top → ∀ v, v ∈ (f (st.frames j)).high ↔
      v ∈ (f (st.frames j)).active ∧
        3*(f (st.frames j)).theta*LocalPush.deg g.graph v ≤ (f (st.frames j)).residual v) :
    KeysInvariant g (changeFrame st j f) := by
  classical
  have ha (i : ℕ) : ((changeFrame st j f).frames i).active = (st.frames i).active := by
    by_cases he : i = j <;> simp [changeFrame,he,hA]
  have hp := parentDomain_same st (changeFrame st j f) ha
  intro i hh
  have his : i ≤ st.top := hh
  constructor
  · intro v
    unfold exteriorKey
    rw [hp i]
    by_cases he : i = j
    · subst i
      simpa [changeFrame,hq,hA,hr,hE,exteriorKey] using (hi j his).1 v
    · simpa [changeFrame,he,exteriorKey] using (hi i his).1 v
  · intro v
    by_cases he : i = j
    · subst i
      simpa [changeFrame,highKey] using hH his v
    · simpa [changeFrame,he,highKey] using (hi i his).2 v

lemma keys_controlFrame (g : InputGraph n) (st : RecursiveState n) (hi : KeysInvariant g st)
    (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n)
    (hq : (f (st.frames j)).q = (st.frames j).q)
    (hθ : (f (st.frames j)).theta = (st.frames j).theta)
    (hA : (f (st.frames j)).active = (st.frames j).active)
    (hr : (f (st.frames j)).residual = (st.frames j).residual)
    (hE : (f (st.frames j)).exterior = (st.frames j).exterior)
    (hH : (f (st.frames j)).high = (st.frames j).high) :
    KeysInvariant g (changeFrame st j f) := by
  apply keys_changeFrame g st hi j f hq hA hr hE
  intro hh v
  simpa only [hH,hA,hθ,hr,highKey] using (hi j hh).2 v

lemma keys_debit (g : InputGraph n) (st : RecursiveState n) (j : ℕ) (w : ℝ≥0∞)
    (hi : KeysInvariant g st) : KeysInvariant g (debit st j w) := by
  intro i hh
  have his : i ≤ st.top := hh
  simpa [debit,exteriorKey,highKey,parentDomain] using hi i his

lemma keys_changePC (g : InputGraph n) (st : RecursiveState n) (pc : NormalizePC)
    (hi : KeysInvariant g st) : KeysInvariant g (changePC st pc) :=
  keys_controlFrame g st hi st.top _ rfl rfl rfl rfl rfl rfl

lemma keys_finish (g : InputGraph n) (st : RecursiveState n) (hi : KeysInvariant g st) :
    KeysInvariant g (finishEpisode st) := by
  apply keys_controlFrame g _ _ st.top _ rfl rfl rfl rfl rfl rfl
  exact hi

lemma keys_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (hi : KeysInvariant g st) :
    KeysInvariant g (endCall g α st) := by
  classical
  unfold endCall
  dsimp only
  split
  · intro i hh
    exact hi i hh
  · intro i hh
    exact hi i (hh.trans (Nat.sub_le _ _))

lemma keys_complete (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (st : RecursiveState n) (hi : KeysInvariant g st) :
    KeysInvariant g (completeComponent m g s α st) := by
  intro i hh
  exact hi i hh

lemma keys_fresh (g : InputGraph n) (st : RecursiveState n) (f : NormalizeFrame n)
    (hi : KeysInvariant g st) (hA : f.active = ∅) (hH : f.high = ∅)
    (hE : f.exterior = (st.frames st.top).active.filter (fun v =>
      f.q*LocalPush.deg g.graph v < f.residual v)) :
    KeysInvariant g {st with top := st.top+1, frames := Function.update st.frames (st.top+1) f} := by
  classical
  let u : RecursiveState n := {st with top := st.top+1, frames := Function.update st.frames (st.top+1) f}
  change KeysInvariant g u
  intro i hh
  change i ≤ st.top+1 at hh
  by_cases he : i = st.top+1
  · subst i
    have hf : u.frames (st.top+1) = f := by simp [u]
    have hp : parentDomain u (st.top+1) = (st.frames st.top).active := by simp [u,parentDomain]
    constructor
    · intro v
      unfold exteriorKey
      rw [hf,hp]
      simp [hE,hA]
    · intro v
      simp [highKey,hf,hH,hA]
  · have his : i ≤ st.top := by omega
    have hf : u.frames i = st.frames i := by simp [u,he]
    have hp : parentDomain u i = parentDomain st i := by
      unfold parentDomain
      split
      · rfl
      · have hne : i-1 ≠ st.top+1 := by omega
        simp [u,hne]
    constructor
    · intro v
      unfold exteriorKey
      rw [hf,hp]
      exact (hi i his).1 v
    · intro v
      simp only [highKey,hf]
      exact (hi i his).2 v

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.QueueStep

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma keys_drain (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hi : KeysInvariant g st) (pc : NormalizePC) :
    KeysInvariant g (if anyExhausted st then changePC (debit st st.top 1) pc else
      match pendingPush st with
      | some (t,v) => exteriorPush g α st t v
      | none => changePC (debit st st.top 1) pc) := by
  split
  · exact keys_changePC g _ pc (keys_debit g st _ _ hi)
  · cases hp : pendingPush st with
    | none => exact keys_changePC g _ pc (keys_debit g st _ _ hi)
    | some p => obtain ⟨t,v⟩ := p; exact keys_exterior g α st hi t v

set_option maxHeartbeats 1000000 in
lemma keys_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hi : KeysInvariant g st) : KeysInvariant g (recursiveStep m g s α ℓ schedule st) := by
  classical
  by_cases hd : st.done = true
  · simpa [recursiveStep,hd] using hi
  simp only [recursiveStep,hd,Bool.false_eq_true,ite_false]
  by_cases hc : componentComplete st
  · simp only [hc,ite_true]
    exact keys_complete m g s α st hi
  simp only [hc,ite_false]
  have hcheap := keys_debit g st st.top 1 hi
  cases hpc : (st.frames st.top).pc with
  | initialDrain =>
    simp only [hpc]
    split
    · exact keys_changePC g _ _ hcheap
    · split
      · exact keys_drain g α st hi _
      · split <;> exact keys_changePC g _ _ hcheap
  | beginEpisode =>
    simp only [hpc]
    apply keys_changeFrame g _ (by exact hi) _ _ rfl rfl rfl rfl
    intro hh v
    simp [highKey,debit]
  | fullSolve =>
    simp only [hpc]
    split
    · exact keys_changePC g _ _ hcheap
    · split
      · apply keys_changePC g _ _
        unfold KeysInvariant exteriorKey highKey parentDomain
        exact keys_joint_refresh g α st (st.frames st.top).active
          (solveOn g α (st.frames st.top).active (st.frames st.top).residual)
          (fun v hv => solveOn_outside g α (st.frames st.top).active _ v hv) hi
      · exact hcheap
  | normalize =>
    simp only [hpc]
    split
    · exact keys_changePC g _ _ hcheap
    · split
      · exact keys_changePC g _ _ hcheap
      · let c := freshFrame g schedule ℓ (st.top+1) st.nextId (st.frames st.top).block
          (st.frames st.top).theta (st.frames st.top).active st.x (st.frames st.top).residual
        let u := debit st st.top (16*(volumeNat g (st.frames st.top).active+1)*keyCost st+
          8*(ℓ+2)*((st.frames st.top).block+2) : ℕ)
        let up := changeFrame u st.top (fun fc =>
          {fc with pc := .afterChild, childrenThisEpisode := fc.childrenThisEpisode+1})
        have hup : KeysInvariant g up := keys_controlFrame g u (keys_debit g st _ _ hi)
          st.top _ rfl rfl rfl rfl rfl rfl
        have hn := keys_fresh g up c hup (by rfl) (by rfl) (by
          simp [c,freshFrame,up,u,changeFrame,debit])
        exact hn
  | leafDrain =>
    simp only [hpc]
    split
    · exact keys_changePC g _ _ hcheap
    · split
      · cases hp : pendingPush st with
        | none => exact keys_changePC g _ _ hcheap
        | some p => obtain ⟨t,v⟩ := p; exact keys_exterior g α st hi t v
      · split
        · exact keys_changePC g _ _ hcheap
        · split
          · let C := (st.frames st.top).cache ∪ (st.frames st.top).high
            let u := changeFrame st st.top (fun fc => {fc with cache := C})
            have hu : KeysInvariant g u := keys_controlFrame g st hi st.top _ rfl rfl rfl rfl rfl rfl
            unfold KeysInvariant exteriorKey highKey parentDomain
            exact keys_joint_refresh g α u C
              (solveOn g α C (fun v => (st.frames st.top).residual v-(st.frames st.top).theta*LocalPush.deg g.graph v))
              (fun v hv => solveOn_outside g α C _ v hv) hu
          · exact hcheap
  | afterChild =>
    simp only [hpc]
    split
    · exact keys_changePC g _ _ (keys_finish g _ hcheap)
    · split
      · exact keys_changePC g _ _ (keys_finish g _ hcheap)
      · exact keys_drain g α st hi _
  | finishEpisode =>
    simp only [hpc]
    split
    · exact keys_changePC g _ _ (keys_finish g _ hcheap)
    · split
      · exact keys_changePC g _ _ (keys_finish g _ hcheap)
      · apply keys_controlFrame g _ _ _ _ rfl rfl rfl rfl rfl rfl
        apply keys_finish
        exact hi
  | restartDrain =>
    simp only [hpc]
    split
    · exact keys_changePC g _ _ hcheap
    · split
      · exact keys_drain g α st hi _
      · exact keys_controlFrame g _ hcheap _ _ rfl rfl rfl rfl rfl rfl
  | normal =>
    simp only [hpc]
    exact keys_end g α _ hcheap
  | interrupted =>
    simp only [hpc]
    exact keys_end g α _ hcheap

lemma keys_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 ≤ q) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    KeysInvariant g (recursiveRun m g s α q ℓ schedule t) := by
  induction t with
  | zero => simpa [recursiveRun] using keys_init g s q hq ℓ schedule
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using keys_step m g s α ℓ schedule _ ih

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.IsolateStep

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma isolate_PC (g : InputGraph n) (st : RecursiveState n) (pc : NormalizePC)
    (hi : IsolateResidual g st) : IsolateResidual g (changePC st pc) :=
  isolate_metadata g st hi st.top _ rfl
lemma isolate_finish (g : InputGraph n) (st : RecursiveState n) (hi : IsolateResidual g st) :
    IsolateResidual g (finishEpisode st) := by
  apply isolate_metadata g _ _ st.top _ rfl
  exact hi
lemma isolate_pending (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hi : IsolateResidual g st) (t : ℕ) (v : Fin n) (hp : pendingPush st = some (t,v)) :
    IsolateResidual g (exteriorPush g α st t v) :=
  isolate_exterior g α st hi t (pending_push_member st t v hp).1 v
lemma isolate_drain (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hi : IsolateResidual g st) (pc : NormalizePC) :
    IsolateResidual g (if anyExhausted st then changePC (debit st st.top 1) pc else
      match pendingPush st with
      | some (t,v) => exteriorPush g α st t v
      | none => changePC (debit st st.top 1) pc) := by
  split
  · exact isolate_PC g _ pc hi
  · cases hp : pendingPush st with
    | none => exact isolate_PC g _ pc hi
    | some p => obtain ⟨t,v⟩ := p; exact isolate_pending g α st hi t v hp

set_option maxHeartbeats 1000000 in
lemma isolate_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hi : IsolateResidual g st) : IsolateResidual g (recursiveStep m g s α ℓ schedule st) := by
  classical
  by_cases hd : st.done = true
  · simpa [recursiveStep,hd] using hi
  simp only [recursiveStep,hd,Bool.false_eq_true,ite_false]
  by_cases hc : componentComplete st
  · simp only [hc,ite_true]
    exact hi
  simp only [hc,ite_false]
  cases hpc : (st.frames st.top).pc with
  | initialDrain =>
    simp only [hpc]
    split
    · exact isolate_PC g _ _ hi
    · split
      · exact isolate_drain g α st hi _
      · split <;> exact isolate_PC g _ _ hi
  | beginEpisode =>
    simp only [hpc]
    apply isolate_metadata g _ _ _ _ rfl
    exact hi
  | fullSolve =>
    simp only [hpc]
    split
    · exact isolate_PC g _ _ hi
    · split
      · apply isolate_PC g _ _
        unfold IsolateResidual
        exact isolate_refresh g _ (touchedBy g (st.frames st.top).active)
          (isolate_residual_joint g α st _ hi)
      · exact hi
  | normalize =>
    simp only [hpc]
    split
    · exact isolate_PC g _ _ hi
    · split
      · exact isolate_PC g _ _ hi
      · let c := freshFrame g schedule ℓ (st.top+1) st.nextId (st.frames st.top).block
          (st.frames st.top).theta (st.frames st.top).active st.x (st.frames st.top).residual
        let u := debit st st.top (16*(volumeNat g (st.frames st.top).active+1)*keyCost st+
          8*(ℓ+2)*((st.frames st.top).block+2) : ℕ)
        let up := changeFrame u st.top (fun fc =>
          {fc with pc := .afterChild, childrenThisEpisode := fc.childrenThisEpisode+1})
        have hup : IsolateResidual g up := isolate_metadata g u hi st.top _ rfl
        apply isolate_newFrame g up c hup
        intro v hv
        exact hi st.top le_rfl v hv
  | leafDrain =>
    simp only [hpc]
    split
    · exact isolate_PC g _ _ hi
    · split
      · cases hp : pendingPush st with
        | none => exact isolate_PC g _ _ hi
        | some p => obtain ⟨t,v⟩ := p; exact isolate_pending g α st hi t v hp
      · split
        · exact isolate_PC g _ _ hi
        · split
          · let C := (st.frames st.top).cache ∪ (st.frames st.top).high
            let u := changeFrame st st.top (fun fc => {fc with cache := C})
            have hu : IsolateResidual g u := isolate_metadata g st hi st.top _ rfl
            unfold IsolateResidual
            exact isolate_refresh g _ (touchedBy g C) (isolate_residual_joint g α u _ hu)
          · exact hi
  | afterChild =>
    simp only [hpc]
    split
    · exact isolate_PC g _ _ (isolate_finish g _ hi)
    · split
      · exact isolate_PC g _ _ (isolate_finish g _ hi)
      · exact isolate_drain g α st hi _
  | finishEpisode =>
    simp only [hpc]
    split
    · exact isolate_PC g _ _ (isolate_finish g _ hi)
    · split
      · exact isolate_PC g _ _ (isolate_finish g _ hi)
      · apply isolate_metadata g _ _ _ _ rfl
        exact isolate_finish g _ hi
  | restartDrain =>
    simp only [hpc]
    split
    · exact isolate_PC g _ _ hi
    · split
      · exact isolate_drain g α st hi _
      · exact isolate_metadata g (debit st st.top 1) hi st.top
          (fun fc => {fc with needFull := true, pc := .beginEpisode}) rfl
  | normal =>
    simp only [hpc]
    exact isolate_end g α _ hi
  | interrupted =>
    simp only [hpc]
    exact isolate_end g α _ hi

lemma isolate_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    IsolateResidual g (recursiveRun m g s α q ℓ schedule t) := by
  induction t with
  | zero => simpa [recursiveRun] using isolate_residual_init g s hs q ℓ schedule
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using isolate_step m g s α ℓ schedule _ ih

lemma run_pending_positive (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 ≤ q) (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule)
    (k t : ℕ) (v : Fin n)
    (hp : pendingPush (recursiveRun m g s α q ℓ schedule k) = some (t,v)) : 0 < g.graph.degree v := by
  exact isolate_pending_positive g _ (isolate_run m g s α q hs ℓ schedule k)
    (keys_run m g s α q hq ℓ schedule k) t v hp

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BoundaryInvariant

set_option autoImplicit false
open Finset
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

@[simp] lemma active_debit (st : RecursiveState n) (j i : ℕ) (w : ℝ≥0∞) :
    ((debit st j w).frames i).active = (st.frames i).active := by
  classical
  simp [debit]
@[simp] lemma active_changeFrame (st : RecursiveState n) (j i : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n) :
    ((changeFrame st j f).frames i).active =
      if i = j then (f (st.frames j)).active else (st.frames i).active := by
  classical
  by_cases h : i = j <;> simp [changeFrame,h]
@[simp] lemma active_refresh (g : InputGraph n) (st : RecursiveState n)
    (T : Finset (Fin n)) (i : ℕ) :
    ((refreshKeys g st T).frames i).active = (st.frames i).active := by
  classical
  by_cases h : i ≤ st.top <;> simp [refreshKeys,h]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.StoredInvariant

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

@[simp] lemma stored_ite (P : Prop) [Decidable P] (a b : RecursiveState n) :
    (if P then a else b).stored = if P then a.stored else b.stored := by split <;> rfl

lemma exterior_stored (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) : (exteriorPush g α st t v).stored = insert v st.stored := by
  simp [exteriorPush,refreshKeys,debit,changeFrame]

set_option maxHeartbeats 1000000 in
lemma exterior_active (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) (i : ℕ) :
    let δ := min ((st.frames t).residual v/(5*LocalPush.deg g.graph v))
      (3*(st.frames t).q/8-relative st t v)
    ((exteriorPush g α st t v).frames i).active =
      if relative st t v+δ = 3*(st.frames t).q/8 ∧ i = t then insert v (st.frames i).active
      else (st.frames i).active := by
  classical
  let f := st.frames t
  let d := LocalPush.deg g.graph v
  let δ := min (f.residual v/(5*d)) (3*f.q/8-relative st t v)
  let base := rawExterior g α st t v δ
  let admitted := changeFrame base t (fun fi =>
    {fi with
      active := insert v fi.active
      residual := Function.update fi.residual v (fi.residual v+f.q*d/2)
      W := fi.W + if fi.openBudget then (t+3 : ℕ)*f.q*d/2 else 0})
  let child := if t < st.top then changeFrame admitted (t+1) (fun fc =>
    {fc with
      reference := Function.update fc.reference v (admitted.x v)
      residual := Function.update fc.residual v ((admitted.frames t).residual v)}) else admitted
  let final := if t = 0 then {child with boundaryEdges := st.boundaryEdges+
    (g.neighbors v).length-2*((g.neighbors v).filter (fun w => w ∈ f.active)).length} else child
  let prepared := if relative st t v+δ = 3*f.q/8 then final else base
  have hb (i : ℕ) : (base.frames i).active = (st.frames i).active := by
    by_cases hh : i ≤ st.top <;> simp [base,rawExterior,hh]
  have ha (i : ℕ) : (admitted.frames i).active =
      if i = t then insert v (st.frames i).active else (st.frames i).active := by
    simp only [admitted,active_changeFrame]
    by_cases hh : i = t <;> simp [hh,hb]
  have hc (i : ℕ) : (child.frames i).active = (admitted.frames i).active := by
    unfold child
    split
    · exact observe_changeFrame (fun f => f.active) admitted (t+1) _ rfl i
    · rfl
  have hf (i : ℕ) : (final.frames i).active = (admitted.frames i).active := by
    unfold final
    split <;> exact hc i
  have hp (i : ℕ) : (prepared.frames i).active =
      if relative st t v+δ = 3*f.q/8 ∧ i = t then insert v (st.frames i).active
      else (st.frames i).active := by
    unfold prepared
    split
    · rename_i hh
      rw [hf,ha]
      simp [hh]
    · rename_i hh
      rw [hb]
      simp [hh]
  dsimp only
  unfold exteriorPush
  simp only [active_debit,active_refresh]
  change (prepared.frames i).active = _
  exact hp i

lemma stored_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) (hi : StoredInvariant g st) (hv : 0 < g.graph.degree v) :
    StoredInvariant g (exteriorPush g α st t v) := by
  classical
  constructor
  · intro i hh
    have his : i ≤ st.top := by simpa using hh
    rw [exterior_active,exterior_stored]
    split
    · exact Finset.insert_subset_insert v (hi.1 i his)
    · exact (hi.1 i his).trans (Finset.subset_insert _ _)
  · intro w hw
    rw [exterior_stored] at hw
    obtain he|hm := Finset.mem_insert.mp hw
    · subst w; exact hv
    · exact hi.2 w hm

lemma stored_transport (g : InputGraph n) (st u : RecursiveState n) (hi : StoredInvariant g st)
    (ht : u.top ≤ st.top) (hs : u.stored = st.stored)
    (hA : ∀ i ≤ u.top, (u.frames i).active = (st.frames i).active) : StoredInvariant g u := by
  constructor
  · intro i hh
    rw [hs,hA i hh]
    exact hi.1 i (hh.trans ht)
  · intro v hv
    rw [hs] at hv
    exact hi.2 v hv

lemma stored_metadata (g : InputGraph n) (st : RecursiveState n) (hi : StoredInvariant g st)
    (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n)
    (hA : (f (st.frames j)).active = (st.frames j).active) :
    StoredInvariant g (changeFrame st j f) := by
  apply stored_transport g st (changeFrame st j f) hi le_rfl rfl
  intro i hh
  by_cases he : i = j <;> simp [changeFrame,he,hA]

lemma stored_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (h : Fin n → ℝ) (hi : StoredInvariant g st) : StoredInvariant g (jointUpdate g α st h) := by
  apply stored_transport g st (jointUpdate g α st h) hi le_rfl rfl
  intro i hh
  have his : i ≤ st.top := hh
  simp [jointUpdate,his]

lemma stored_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n))
    (hi : StoredInvariant g st) : StoredInvariant g (refreshKeys g st T) := by
  apply stored_transport g st (refreshKeys g st T) hi le_rfl rfl
  intro i hh
  exact refresh_active g st T i

lemma stored_newFrame (g : InputGraph n) (st : RecursiveState n) (f : NormalizeFrame n)
    (hi : StoredInvariant g st) (hf : f.active = ∅) :
    StoredInvariant g {st with top := st.top+1, frames := Function.update st.frames (st.top+1) f} := by
  constructor
  · intro i hh
    change i ≤ st.top+1 at hh
    by_cases he : i = st.top+1
    · subst i
      simpa [hf] using (Finset.empty_subset st.stored)
    · have his : i ≤ st.top := by omega
      simpa [he] using hi.1 i his
  · exact hi.2

lemma stored_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hi : StoredInvariant g st) : StoredInvariant g (endCall g α st) := by
  classical
  unfold endCall
  dsimp only
  split
  · exact hi
  · exact ⟨fun i hh => hi.1 i (hh.trans (Nat.sub_le _ _)),hi.2⟩

lemma stored_init (g : InputGraph n) (s : Fin n) (q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) : StoredInvariant g (recursiveInit g s q ℓ schedule) := by
  constructor
  · intro i hh
    have he : i = 0 := by change i ≤ 0 at hh; omega
    subst i
    simp [recursiveInit,freshFrame,emptyFrame]
  · simp [recursiveInit]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.StoredStep

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma stored_PC (g : InputGraph n) (st : RecursiveState n) (pc : NormalizePC)
    (hi : StoredInvariant g st) : StoredInvariant g (changePC st pc) :=
  stored_metadata g st hi st.top _ rfl
lemma stored_finish (g : InputGraph n) (st : RecursiveState n) (hi : StoredInvariant g st) :
    StoredInvariant g (finishEpisode st) := by
  apply stored_metadata g _ _ st.top _ rfl
  exact hi
lemma stored_pending (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hi : StoredInvariant g st)
    (hpend : ∀ t v, pendingPush st = some (t,v) → 0 < g.graph.degree v)
    (t : ℕ) (v : Fin n) (hp : pendingPush st = some (t,v)) :
    StoredInvariant g (exteriorPush g α st t v) :=
  stored_exterior g α st t v hi (hpend t v hp)
lemma stored_drain (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hi : StoredInvariant g st)
    (hpend : ∀ t v, pendingPush st = some (t,v) → 0 < g.graph.degree v)
    (pc : NormalizePC) :
    StoredInvariant g (if anyExhausted st then changePC (debit st st.top 1) pc else
      match pendingPush st with
      | some (t,v) => exteriorPush g α st t v
      | none => changePC (debit st st.top 1) pc) := by
  split
  · exact stored_PC g _ pc hi
  · cases hp : pendingPush st with
    | none => exact stored_PC g _ pc hi
    | some p => obtain ⟨t,v⟩ := p; exact stored_pending g α st hi hpend t v hp

set_option maxHeartbeats 1000000 in
lemma stored_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hi : StoredInvariant g st)
    (hpend : ∀ t v, pendingPush st = some (t,v) → 0 < g.graph.degree v) :
    StoredInvariant g (recursiveStep m g s α ℓ schedule st) := by
  classical
  by_cases hd : st.done = true
  · simpa [recursiveStep,hd] using hi
  simp only [recursiveStep,hd,Bool.false_eq_true,ite_false]
  by_cases hc : componentComplete st
  · simp only [hc,ite_true]
    exact hi
  simp only [hc,ite_false]
  cases hpc : (st.frames st.top).pc with
  | initialDrain =>
    simp only [hpc]
    split
    · exact stored_PC g _ _ hi
    · split
      · exact stored_drain g α st hi hpend _
      · split <;> exact stored_PC g _ _ hi
  | beginEpisode =>
    simp only [hpc]
    apply stored_metadata g _ _ _ _ rfl
    exact hi
  | fullSolve =>
    simp only [hpc]
    split
    · exact stored_PC g _ _ hi
    · split
      · apply stored_PC g _ _
        unfold StoredInvariant
        exact stored_refresh g _ (touchedBy g (st.frames st.top).active)
          (stored_joint g α st _ hi)
      · exact hi
  | normalize =>
    simp only [hpc]
    split
    · exact stored_PC g _ _ hi
    · split
      · exact stored_PC g _ _ hi
      · let c := freshFrame g schedule ℓ (st.top+1) st.nextId (st.frames st.top).block
          (st.frames st.top).theta (st.frames st.top).active st.x (st.frames st.top).residual
        let u := debit st st.top (16*(volumeNat g (st.frames st.top).active+1)*keyCost st+
          8*(ℓ+2)*((st.frames st.top).block+2) : ℕ)
        let up := changeFrame u st.top (fun fc =>
          {fc with pc := .afterChild, childrenThisEpisode := fc.childrenThisEpisode+1})
        have hup : StoredInvariant g up := stored_metadata g u hi st.top _ rfl
        exact stored_newFrame g up c hup rfl
  | leafDrain =>
    simp only [hpc]
    split
    · exact stored_PC g _ _ hi
    · split
      · cases hp : pendingPush st with
        | none => exact stored_PC g _ _ hi
        | some p => obtain ⟨t,v⟩ := p; exact stored_pending g α st hi hpend t v hp
      · split
        · exact stored_PC g _ _ hi
        · split
          · let C := (st.frames st.top).cache ∪ (st.frames st.top).high
            let u := changeFrame st st.top (fun fc => {fc with cache := C})
            have hu : StoredInvariant g u := stored_metadata g st hi st.top _ rfl
            unfold StoredInvariant
            exact stored_refresh g _ (touchedBy g C) (stored_joint g α u _ hu)
          · exact hi
  | afterChild =>
    simp only [hpc]
    split
    · exact stored_PC g _ _ (stored_finish g _ hi)
    · split
      · exact stored_PC g _ _ (stored_finish g _ hi)
      · exact stored_drain g α st hi hpend _
  | finishEpisode =>
    simp only [hpc]
    split
    · exact stored_PC g _ _ (stored_finish g _ hi)
    · split
      · exact stored_PC g _ _ (stored_finish g _ hi)
      · apply stored_metadata g _ _ _ _ rfl
        exact stored_finish g _ hi
  | restartDrain =>
    simp only [hpc]
    split
    · exact stored_PC g _ _ hi
    · split
      · exact stored_drain g α st hi hpend _
      · exact stored_metadata g (debit st st.top 1) hi st.top
          (fun fc => {fc with needFull := true, pc := .beginEpisode}) rfl
  | normal =>
    simp only [hpc]
    exact stored_end g α _ hi
  | interrupted =>
    simp only [hpc]
    exact stored_end g α _ hi

lemma stored_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 ≤ q) (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    StoredInvariant g (recursiveRun m g s α q ℓ schedule t) := by
  induction t with
  | zero => simpa [recursiveRun] using stored_init g s q ℓ schedule
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using stored_step m g s α ℓ schedule _ ih
      (fun level v hp => run_pending_positive m g s α q hq hs ℓ schedule t level v hp)

end
end NearlyOptimalPPR.Computation

set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
noncomputable section
theorem solution (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    let st := recursiveRun m g s α q ℓ schedule t
    (0 ≤ q → KeysInvariant g st) ∧ (0 < g.graph.degree s → IsolateResidual g st) ∧
      (0 ≤ q → 0 < g.graph.degree s → StoredInvariant g st) := by
  exact ⟨fun hq => keys_run m g s α q hq ℓ schedule t,
    fun hs => isolate_run m g s α q hs ℓ schedule t,
    fun hq hs => stored_run m g s α q hq hs ℓ schedule t⟩
end

