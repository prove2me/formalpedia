-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.active_region_potentials
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:34:43.217625+00:00
-- url     : https://prove2.me/submissions/0beca65c-d715-4e52-b8d6-59f7d7410c68

import Definitions.Def_NearlyOptimalPPR_Computation_proof_invariants
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_residual_identities
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_control_parameters
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_queue_domains
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_numerical_invariants

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}
lemma region_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    RegionInvariant (recursiveRun m g s α q ℓ schedule t) := by
  exact (recursive_residual_identities m n g s α q ℓ schedule t).1

theorem root_identity_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    RootIdentity g s α (recursiveRun m g s α q ℓ schedule t) := by
  exact (recursive_residual_identities m n g s α q ℓ schedule t).2.1

lemma layer_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    LayerIdentity g (recursiveRun m g s α q ℓ schedule t) := by
  exact (recursive_residual_identities m n g s α q ℓ schedule t).2.2.1

lemma root_threshold_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    ((recursiveRun m g s α q ℓ schedule t).frames 0).q = q := by
  exact (recursive_residual_identities m n g s α q ℓ schedule t).2.2.2

lemma depth_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    (recursiveRun m g s α q ℓ schedule t).top ≤ ℓ := by
  exact (recursive_control_parameters m n g s α q ℓ schedule t).1

lemma budget_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    BudgetInvariant (recursiveRun m g s α q ℓ schedule t) := by
  exact (recursive_control_parameters m n g s α q ℓ schedule t).2.1

lemma cache_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    CacheControlInvariant ℓ (recursiveRun m g s α q ℓ schedule t) := by
  exact (recursive_control_parameters m n g s α q ℓ schedule t).2.2.1

lemma parameters_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 < q) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    ParameterInvariant (recursiveRun m g s α q ℓ schedule t) := by
  exact (recursive_control_parameters m n g s α q ℓ schedule t).2.2.2 hq

lemma keys_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 ≤ q) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    KeysInvariant g (recursiveRun m g s α q ℓ schedule t) := by
  exact (recursive_queue_domains m n g s α q ℓ schedule t).1 hq

lemma isolate_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    IsolateResidual g (recursiveRun m g s α q ℓ schedule t) := by
  exact (recursive_queue_domains m n g s α q ℓ schedule t).2.1 hs

lemma stored_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 ≤ q) (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    StoredInvariant g (recursiveRun m g s α q ℓ schedule t) := by
  exact (recursive_queue_domains m n g s α q ℓ schedule t).2.2 hq hs

lemma numerical_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    NumericalInvariant g (recursiveRun m g s α q ℓ schedule t) := by
  exact recursive_numerical_invariants m n g s α q hα hq hs ℓ schedule t

end
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

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RecursiveInvariants

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section

variable {n : ℕ}

lemma root_exterior_projection (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (v : Fin n) :
    let f := st.frames 0
    let h := min (f.residual v / (5 * LocalPush.deg g.graph v)) (3*f.q/8 - st.x v)
    let activated := st.x v+h = 3*f.q/8
    let u := exteriorPush g α st 0 v
    u.x = Function.update st.x v (st.x v+h) ∧
    (u.frames 0).q = f.q ∧
    (u.frames 0).active = (if activated then insert v f.active else f.active) ∧
    (u.frames 0).residual = fun w => f.residual w +
      (if w = v then -5*LocalPush.deg g.graph v*h else 0) +
      (if g.graph.Adj w v then (1-α)*h else 0) +
      (if activated ∧ w = v then f.q*LocalPush.deg g.graph v/2 else 0) := by
  classical
  dsimp only
  by_cases ha : st.x v + min ((st.frames 0).residual v / (5*LocalPush.deg g.graph v))
      (3*(st.frames 0).q/8 - st.x v) = 3*(st.frames 0).q/8
  · by_cases ht : 0 < st.top
    all_goals
      simp [exteriorPush, relative, ha, ht, refreshKeys, debit, changeFrame, parentDomain]
      ext w
      by_cases hw : w = v <;> simp [Function.update_apply, hw] <;> ring
  · simp [exteriorPush, relative, ha, refreshKeys, debit, changeFrame, parentDomain]

lemma nonroot_exterior_projection (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) (ht : 0 < t) :
    let f := st.frames t
    let h := min (f.residual v / (5*LocalPush.deg g.graph v)) (3*f.q/8-relative st t v)
    let u := exteriorPush g α st t v
    u.x = Function.update st.x v (st.x v+h) ∧
    (u.frames 0).q = (st.frames 0).q ∧
    (u.frames 0).active = (st.frames 0).active ∧
    (u.frames 0).residual = fun w => (st.frames 0).residual w +
      (if w = v then -LocalPush.deg g.graph v*h else 0) +
      (if g.graph.Adj w v then (1-α)*h else 0) := by
  classical
  dsimp only
  by_cases ha : relative st t v +
      min ((st.frames t).residual v / (5*LocalPush.deg g.graph v))
        (3*(st.frames t).q/8-relative st t v) = 3*(st.frames t).q/8
  · by_cases htop : t < st.top
    all_goals simp [exteriorPush,ha,htop,refreshKeys,debit,changeFrame,parentDomain,
      ht,ht.ne',Ne.symm ht.ne']
  · simp [exteriorPush,ha,refreshKeys,debit,changeFrame,parentDomain,
      ht,ht.ne',Ne.symm ht.ne']

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.IsolateResidual

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

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

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.IsolateStep

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma run_pending_positive (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 ≤ q) (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule)
    (k t : ℕ) (v : Fin n)
    (hp : pendingPush (recursiveRun m g s α q ℓ schedule k) = some (t,v)) : 0 < g.graph.degree v := by
  exact isolate_pending_positive g _ (isolate_run m g s α q hs ℓ schedule k)
    (keys_run m g s α q hq ℓ schedule k) t v hp

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CrossingPush

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation

lemma crossing_push_bounds (d q r y : ℝ) (hd : 0 < d) (hq : 0 < q)
    (hr : 0 ≤ r) (hy : 0 ≤ y ∧ y ≤ 3*q/8) :
    let δ := min (r/(5*d)) (3*q/8-y)
    0 ≤ δ ∧ 0 ≤ r-5*d*δ ∧ 0 ≤ y+δ ∧ y+δ ≤ 3*q/8 := by
  dsimp only
  have hden : 0 < 5*d := by positivity
  have hδ : 0 ≤ min (r/(5*d)) (3*q/8-y) :=
    le_min (div_nonneg hr hden.le) (sub_nonneg.mpr hy.2)
  have hres := (le_div_iff₀ hden).mp (min_le_left (r/(5*d)) (3*q/8-y))
  have hcap := min_le_right (r/(5*d)) (3*q/8-y)
  refine ⟨hδ,?_,by linarith,by linarith⟩
  nlinarith

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ConnectedInsertion

set_option autoImplicit false
open Finset
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma singleton_connected (g : InputGraph n) (v : Fin n) :
    (g.graph.induce (↑({v} : Finset (Fin n)) : Set (Fin n))).Connected := by
  letI : Nonempty {w : Fin n // w ∈ ({v} : Finset (Fin n))} := ⟨⟨v,by simp⟩⟩
  letI : Subsingleton {w : Fin n // w ∈ ({v} : Finset (Fin n))} :=
    ⟨fun a b => Subtype.ext (by
      have ha : a.val = v := Finset.mem_singleton.mp a.property
      have hb : b.val = v := Finset.mem_singleton.mp b.property
      exact ha.trans hb.symm)⟩
  exact SimpleGraph.Connected.of_subsingleton

lemma connected_insert_neighbor (g : InputGraph n) (H : Finset (Fin n))
    (hH : (g.graph.induce (↑H : Set (Fin n))).Connected) (v w : Fin n)
    (hw : w ∈ H) (hvw : g.graph.Adj v w) :
    (g.graph.induce (↑(insert v H) : Set (Fin n))).Connected := by
  classical
  let φ : g.graph.induce (↑H : Set (Fin n)) →g g.graph.induce (↑(insert v H) : Set (Fin n)) :=
    { toFun := fun a => ⟨a.val,Finset.mem_insert_of_mem a.property⟩
      map_rel' := fun ha => ha }
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨⟨w,Finset.mem_insert_of_mem hw⟩,?_⟩
  intro u
  by_cases hu : u.val = v
  · have he : u = ⟨v,Finset.mem_insert_self _ _⟩ := Subtype.ext hu
    rw [he]
    exact SimpleGraph.Adj.reachable hvw.symm
  · have huH : u.val ∈ H := (Finset.mem_insert.mp u.property).resolve_left hu
    simpa [φ] using (hH.preconnected ⟨w,hw⟩ ⟨u.val,huH⟩).map φ

lemma connected_insert_source (g : InputGraph n) (s : Fin n) (H : Finset (Fin n))
    (hi : H.Nonempty → s ∈ H ∧ (g.graph.induce (↑H : Set (Fin n))).Connected)
    (v : Fin n) (hout : v ∉ H) (hv : v = s ∨ ∃ w ∈ H, g.graph.Adj v w) :
    s ∈ insert v H ∧ (g.graph.induce (↑(insert v H) : Set (Fin n))).Connected := by
  classical
  by_cases he : H = ∅
  · subst H
    have hvs : v = s := by
      rcases hv with hs|⟨w,hw,_⟩
      · exact hs
      · simp at hw
    subst v
    simpa using And.intro (by simp : s ∈ ({s} : Finset (Fin n))) (singleton_connected g s)
  · obtain ⟨hs,hconn⟩ := hi (Finset.nonempty_iff_ne_empty.mpr he)
    have hneighbor : ∃ w ∈ H, g.graph.Adj v w := by
      rcases hv with hv|hh
      · subst v
        exact False.elim (hout hs)
      · exact hh
    obtain ⟨w,hw,hvw⟩ := hneighbor
    exact ⟨Finset.mem_insert_of_mem hs,connected_insert_neighbor g H hconn v w hw hvw⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.Activation

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma activation_attaches (g : InputGraph n) (s v : Fin n) (α : ℝ)
    (st : RecursiveState n) (hα : 0 < α ∧ α < 1)
    (hi : RootIdentity g s α st) (hq : 0 < (st.frames 0).q)
    (hd : 0 < g.graph.degree v) (hv : v ∉ (st.frames 0).active)
    (hvs : v ≠ s)
    (hx : ∀ w ∉ (st.frames 0).active, st.x w ≤ 3*(st.frames 0).q/8)
    (δ : ℝ) (hc : st.x v+δ = 3*(st.frames 0).q/8)
    (hr : 5*LocalPush.deg g.graph v*δ ≤ (st.frames 0).residual v) :
    ∃ w ∈ (st.frames 0).active, g.graph.Adj v w := by
  classical
  by_contra hn
  have hw : ∀ w ∈ g.graph.neighborFinset v, w ∉ (st.frames 0).active := by
    intro w ha hm
    exact hn ⟨w,hm,by simpa using ha⟩
  have hsum : (∑ w ∈ g.graph.neighborFinset v, st.x w) ≤
      LocalPush.deg g.graph v*(3*(st.frames 0).q/8) := by
    calc
      _ ≤ ∑ w ∈ g.graph.neighborFinset v, (3*(st.frames 0).q/8) :=
        Finset.sum_le_sum fun w ha => hx w (hw w ha)
      _ = _ := by simp [LocalPush.deg]
  have hid := hi v
  simp only [hv,ite_false] at hid
  unfold residual at hid
  simp only [Pi.sub_apply,LocalPush.e,Pi.single_apply, hvs,ite_false] at hid
  rw [lap_mul_apply] at hid
  have hdeg : 0 < LocalPush.deg g.graph v := by
    unfold LocalPush.deg
    exact_mod_cast hd
  have hcap : 0 < 3*(st.frames 0).q/8 := by positivity
  have hh := mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hα.2.le)
  have hprod := mul_pos (mul_pos hα.1 hdeg) hcap
  nlinarith

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootConnected

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma root_connected_transport (g : InputGraph n) (s : Fin n) (st u : RecursiveState n)
    (hi : RootConnected g s st) (hA : (u.frames 0).active = (st.frames 0).active) :
    RootConnected g s u := by
  change ConnectedRootSet g s (u.frames 0).active
  rw [hA]
  exact hi

lemma root_connected_exterior (g : InputGraph n) (s : Fin n) (α : ℝ) (hα : 0 < α ∧ α < 1)
    (st : RecursiveState n) (hroot : RootIdentity g s α st) (hparam : ParameterInvariant st)
    (hnum : NumericalInvariant g st) (hi : RootConnected g s st)
    (t : ℕ) (v : Fin n) (hout : v ∉ (st.frames t).active) (hd : 0 < g.graph.degree v) :
    RootConnected g s (exteriorPush g α st t v) := by
  classical
  by_cases ht : t = 0
  · subst t
    let δ := min ((st.frames 0).residual v/(5*LocalPush.deg g.graph v))
      (3*(st.frames 0).q/8-st.x v)
    have hA := (root_exterior_projection g α st v).2.2.1
    change ConnectedRootSet g s ((exteriorPush g α st 0 v).frames 0).active
    rw [hA]
    by_cases ha : st.x v+δ = 3*(st.frames 0).q/8
    · rw [if_pos ha]
      intro _
      apply connected_insert_source g s (st.frames 0).active hi v hout
      by_cases hvs : v = s
      · exact Or.inl hvs
      · apply Or.inr
        have hx (w : Fin n) (hw : w ∉ (st.frames 0).active) : st.x w ≤ 3*(st.frames 0).q/8 := by
          simpa [relative] using (((hnum 0 (Nat.zero_le _)).1 w (by simp [parentDomain])).2.2.2 hw).le
        have hn := (hnum 0 (Nat.zero_le _)).1 v (by simp [parentDomain])
        have hd' : 0 < LocalPush.deg g.graph v := by unfold LocalPush.deg; exact_mod_cast hd
        have hb := crossing_push_bounds (LocalPush.deg g.graph v) (st.frames 0).q
          ((st.frames 0).residual v) (st.x v) hd' (hparam 0 (Nat.zero_le _)).1 hn.1
          ⟨by simpa [relative] using hn.2.1,hx v hout⟩
        exact activation_attaches g s v α st hα hroot (hparam 0 (Nat.zero_le _)).1 hd hout hvs hx δ ha
          (sub_nonneg.mp hb.2.1)
    · rw [if_neg ha]
      exact hi
  · apply root_connected_transport g s st _ hi
    exact (nonroot_exterior_projection g α st t v (Nat.pos_of_ne_zero ht)).2.2.1

lemma root_connected_init (g : InputGraph n) (s : Fin n) (q : ℝ) (ℓ : ℕ) (schedule : BlockSchedule) :
    RootConnected g s (recursiveInit g s q ℓ schedule) := by
  simp [RootConnected,ConnectedRootSet,recursiveInit,freshFrame,emptyFrame]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootConnectedControl

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma root_connected_metadata (g : InputGraph n) (s : Fin n) (st : RecursiveState n)
    (hi : RootConnected g s st) (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n)
    (hA : (f (st.frames j)).active = (st.frames j).active) :
    RootConnected g s (changeFrame st j f) := by
  apply root_connected_transport g s st (changeFrame st j f) hi
  by_cases he : (0 : ℕ) = j <;> simp [changeFrame,he,hA]

lemma root_connected_PC (g : InputGraph n) (s : Fin n) (st : RecursiveState n)
    (pc : NormalizePC) (hi : RootConnected g s st) : RootConnected g s (changePC st pc) :=
  root_connected_metadata g s st hi st.top _ rfl

lemma root_connected_joint (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n)
    (h : Fin n → ℝ) (hi : RootConnected g s st) : RootConnected g s (jointUpdate g α st h) := by
  apply root_connected_transport g s st (jointUpdate g α st h) hi
  simp [jointUpdate]

lemma root_connected_refresh (g : InputGraph n) (s : Fin n) (st : RecursiveState n)
    (T : Finset (Fin n)) (hi : RootConnected g s st) : RootConnected g s (refreshKeys g st T) :=
  root_connected_transport g s st (refreshKeys g st T) hi (refresh_active g st T 0)

lemma root_connected_finish (g : InputGraph n) (s : Fin n) (st : RecursiveState n)
    (hi : RootConnected g s st) : RootConnected g s (finishEpisode st) := by
  apply root_connected_transport g s st (finishEpisode st) hi
  by_cases he : (0 : ℕ) = st.top <;> simp [finishEpisode,changeFrame,he]

lemma root_connected_newFrame (g : InputGraph n) (s : Fin n) (st : RecursiveState n)
    (f : NormalizeFrame n) (hi : RootConnected g s st) :
    RootConnected g s {st with top := st.top+1, frames := Function.update st.frames (st.top+1) f} := by
  apply root_connected_transport g s st _ hi
  simp

lemma root_connected_end (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n)
    (hi : RootConnected g s st) : RootConnected g s (endCall g α st) := by
  classical
  unfold endCall
  dsimp only
  split <;> exact hi

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootConnectedStep

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma root_connected_pending (g : InputGraph n) (s : Fin n) (α : ℝ) (hα : 0 < α ∧ α < 1)
    (st : RecursiveState n) (hreg : RegionInvariant st) (hroot : RootIdentity g s α st)
    (hparam : ParameterInvariant st) (hnum : NumericalInvariant g st) (hi : RootConnected g s st)
    (hpend : ∀ t v, pendingPush st = some (t,v) → 0 < g.graph.degree v)
    (t : ℕ) (v : Fin n) (hp : pendingPush st = some (t,v)) :
    RootConnected g s (exteriorPush g α st t v) := by
  obtain ⟨ht,hm⟩ := pending_push_member st t v hp
  have hout := (Finset.mem_sdiff.mp ((hreg t ht).2.1 hm)).2
  exact root_connected_exterior g s α hα st hroot hparam hnum hi t v hout (hpend t v hp)

lemma root_connected_drain (g : InputGraph n) (s : Fin n) (α : ℝ) (hα : 0 < α ∧ α < 1)
    (st : RecursiveState n) (hreg : RegionInvariant st) (hroot : RootIdentity g s α st)
    (hparam : ParameterInvariant st) (hnum : NumericalInvariant g st) (hi : RootConnected g s st)
    (hpend : ∀ t v, pendingPush st = some (t,v) → 0 < g.graph.degree v) (pc : NormalizePC) :
    RootConnected g s (if anyExhausted st then changePC (debit st st.top 1) pc else
      match pendingPush st with
      | some (t,v) => exteriorPush g α st t v
      | none => changePC (debit st st.top 1) pc) := by
  split
  · exact root_connected_PC g s _ pc hi
  · cases hp : pendingPush st with
    | none => exact root_connected_PC g s _ pc hi
    | some p =>
      obtain ⟨t,v⟩ := p
      exact root_connected_pending g s α hα st hreg hroot hparam hnum hi hpend t v hp

set_option maxHeartbeats 1000000 in
lemma root_connected_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (hα : 0 < α ∧ α < 1) (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hroot : RootIdentity g s α st) (hparam : ParameterInvariant st)
    (hnum : NumericalInvariant g st) (hi : RootConnected g s st)
    (hpend : ∀ t v, pendingPush st = some (t,v) → 0 < g.graph.degree v) :
    RootConnected g s (recursiveStep m g s α ℓ schedule st) := by
  classical
  by_cases hd : st.done = true
  · simpa [recursiveStep,hd] using hi
  simp only [recursiveStep,hd,Bool.false_eq_true,ite_false]
  by_cases hc : componentComplete st
  · simp only [hc,ite_true]
    exact hi
  simp only [hc,ite_false]
  have hdrain (pc : NormalizePC) := root_connected_drain g s α hα st hreg hroot hparam hnum hi hpend pc
  cases hpc : (st.frames st.top).pc with
  | initialDrain =>
    simp only [hpc]
    split
    · exact root_connected_PC g s _ _ hi
    · split
      · exact hdrain _
      · split <;> exact root_connected_PC g s _ _ hi
  | beginEpisode =>
    simp only [hpc]
    apply root_connected_metadata g s _ (by exact hi) _ _ rfl
  | fullSolve =>
    simp only [hpc]
    split
    · exact root_connected_PC g s _ _ hi
    · split
      · apply root_connected_PC g s _ _
        unfold RootConnected
        exact root_connected_refresh g s _ (touchedBy g (st.frames st.top).active)
          (root_connected_joint g s α st _ hi)
      · exact hi
  | normalize =>
    simp only [hpc]
    split
    · exact root_connected_PC g s _ _ hi
    · split
      · exact root_connected_PC g s _ _ hi
      · let c := freshFrame g schedule ℓ (st.top+1) st.nextId (st.frames st.top).block
          (st.frames st.top).theta (st.frames st.top).active st.x (st.frames st.top).residual
        let u := debit st st.top (16*(volumeNat g (st.frames st.top).active+1)*keyCost st+
          8*(ℓ+2)*((st.frames st.top).block+2) : ℕ)
        let up := changeFrame u st.top (fun fc =>
          {fc with pc := .afterChild, childrenThisEpisode := fc.childrenThisEpisode+1})
        have hup : RootConnected g s up := root_connected_metadata g s u hi st.top _ rfl
        exact root_connected_newFrame g s up c hup
  | leafDrain =>
    simp only [hpc]
    split
    · exact root_connected_PC g s _ _ hi
    · split
      · cases hp : pendingPush st with
        | none => exact root_connected_PC g s _ _ hi
        | some p =>
          obtain ⟨t,v⟩ := p
          exact root_connected_pending g s α hα st hreg hroot hparam hnum hi hpend t v hp
      · split
        · exact root_connected_PC g s _ _ hi
        · split
          · let C := (st.frames st.top).cache ∪ (st.frames st.top).high
            let u := changeFrame st st.top (fun fc => {fc with cache := C})
            have hu : RootConnected g s u := root_connected_metadata g s st hi st.top _ rfl
            unfold RootConnected
            exact root_connected_refresh g s _ (touchedBy g C) (root_connected_joint g s α u _ hu)
          · exact hi
  | afterChild =>
    simp only [hpc]
    split
    · exact root_connected_PC g s _ _ (root_connected_finish g s _ hi)
    · split
      · exact root_connected_PC g s _ _ (root_connected_finish g s _ hi)
      · exact hdrain _
  | finishEpisode =>
    simp only [hpc]
    split
    · exact root_connected_PC g s _ _ (root_connected_finish g s _ hi)
    · split
      · exact root_connected_PC g s _ _ (root_connected_finish g s _ hi)
      · apply root_connected_metadata g s _ (root_connected_finish g s _ (by exact hi)) _ _ rfl
  | restartDrain =>
    simp only [hpc]
    split
    · exact root_connected_PC g s _ _ hi
    · split
      · exact hdrain _
      · exact root_connected_metadata g s (debit st st.top 1) hi st.top
          (fun fc => {fc with needFull := true, pc := .beginEpisode}) rfl
  | normal =>
    simp only [hpc]
    exact root_connected_end g s α _ hi
  | interrupted =>
    simp only [hpc]
    exact root_connected_end g s α _ hi

lemma root_connected_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    RootConnected g s (recursiveRun m g s α q ℓ schedule t) := by
  induction t with
  | zero => simpa [recursiveRun] using root_connected_init g s q ℓ schedule
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using
      root_connected_step m g s α hα ℓ schedule _ (region_run m g s α q ℓ schedule t)
        (root_identity_run m g s α q ℓ schedule t) (parameters_run m g s α q hq ℓ schedule t)
        (numerical_run m g s α q hα hq hs ℓ schedule t) ih
        (fun level v hp => run_pending_positive m g s α q hq.le hs ℓ schedule t level v hp)

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

-- Proof module: Solutions.RootPrune

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma root_prune_subsolution (g : InputGraph n) (s : Fin n) (α : ℝ)
    (hα : 0 < α ∧ α < 1) (st : RecursiveState n) (hq : 0 < (st.frames 0).q)
    (hroot : RootIdentity g s α st) (hnum : NumericalInvariant g st) :
    let H := (st.frames 0).active
    let z := prune (st.frames 0).q st.x
    (∀ v, 0 ≤ z v) ∧ (∀ v ∉ H, z v = 0) ∧
      ∀ v ∈ H, (LocalPush.Lα g.graph α *ᵥ z) v ≤ LocalPush.e s v := by
  classical
  let q := (st.frames 0).q
  let H := (st.frames 0).active
  let c := 3*q/8
  let z := prune q st.x
  let w := st.x-z
  have hc : 0 ≤ c := by dsimp [c,q]; positivity
  have hcore (v : Fin n) := (hnum 0 (Nat.zero_le _)).1 v (by simp [parentDomain])
  have hx (v : Fin n) : 0 ≤ st.x v := by simpa [relative] using (hcore v).2.1
  have hactive (v : Fin n) (hv : v ∈ H) : c ≤ st.x v := by
    simpa [c,q,relative] using (hcore v).2.2.1 hv
  have hout (v : Fin n) (hv : v ∉ H) : st.x v ≤ c := by
    simpa [c,q,relative] using ((hcore v).2.2.2 hv).le
  have hw (v : Fin n) : 0 ≤ w v ∧ w v ≤ c := by
    by_cases hv : st.x v ≤ c
    · have he : z v = 0 := max_eq_right (sub_nonpos.mpr hv)
      simpa [w,he] using And.intro (hx v) hv
    · have he : z v = st.x v-c := max_eq_left (sub_nonneg.mpr (le_of_not_ge hv))
      have he' : w v = c := by simp [w,he]
      rw [he']
      exact ⟨hc,le_rfl⟩
  have hwH (v : Fin n) (hv : v ∈ H) : w v = c := by
    have he : z v = st.x v-c := max_eq_left (sub_nonneg.mpr (hactive v hv))
    simp [w,he]
  have hMw (v : Fin n) (hv : v ∈ H) : 0 ≤ (LocalPush.Lα g.graph α *ᵥ w) v := by
    have hsum : (∑ u ∈ g.graph.neighborFinset v, w u) ≤ LocalPush.deg g.graph v*c := by
      calc
        _ ≤ ∑ u ∈ g.graph.neighborFinset v, c := Finset.sum_le_sum fun u _ => (hw u).2
        _ = _ := by simp [LocalPush.deg]
    rw [lap_mul_apply,hwH v hv]
    have hh := mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hα.2.le)
    have hd : 0 ≤ LocalPush.deg g.graph v := by unfold LocalPush.deg; positivity
    have hp := mul_nonneg (mul_nonneg hα.1.le hd) hc
    nlinarith
  refine ⟨fun v => le_max_right _ _,?_,?_⟩
  · intro v hv
    exact max_eq_right (sub_nonpos.mpr (hout v hv))
  · intro v hv
    have hraw := hroot v
    have hr := (hcore v).1
    have hd : 0 ≤ LocalPush.deg g.graph v := by unfold LocalPush.deg; positivity
    have hqd : 0 ≤ LocalPush.deg g.graph v*q := mul_nonneg hd hq.le
    unfold residual at hraw
    simp only [Pi.sub_apply,hv,ite_true] at hraw
    have he : z = st.x-w := by dsimp [w]; abel
    change (LocalPush.Lα g.graph α *ᵥ z) v ≤ _
    rw [he,Matrix.mulVec_sub]
    simp only [Pi.sub_apply]
    have hm := hMw v hv
    change LocalPush.e s v-(LocalPush.Lα g.graph α *ᵥ st.x) v =
      (st.frames 0).residual v+LocalPush.deg g.graph v*q at hraw
    linarith

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CutFlux

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma edge_difference_sum (g : InputGraph n) (z : Fin n → ℝ) (u : Fin n) :
    (∑ v, edgeDifference g z u v) = LocalPush.deg g.graph u*z u-∑ v ∈ g.graph.neighborFinset u, z v := by
  classical
  have he : (∑ v, edgeDifference g z u v) = ∑ v ∈ g.graph.neighborFinset u, (z u-z v) := by
    unfold edgeDifference
    rw [← Finset.sum_filter]
    congr 1
    ext v
    simp
  rw [he,Finset.sum_sub_distrib]
  simp [LocalPush.deg]

lemma lap_edge_difference (g : InputGraph n) (α : ℝ) (z : Fin n → ℝ) (u : Fin n) :
    (LocalPush.Lα g.graph α *ᵥ z) u = α*(LocalPush.deg g.graph u*z u)+
      (1-α)*∑ v, edgeDifference g z u v := by
  rw [lap_mul_apply,edge_difference_sum]
  ring

lemma internal_flux_zero (g : InputGraph n) (z : Fin n → ℝ) (S : Finset (Fin n)) :
    (∑ u ∈ S, ∑ v ∈ S, edgeDifference g z u v) = 0 := by
  classical
  have hskew (u v : Fin n) : edgeDifference g z u v = -edgeDifference g z v u := by
    by_cases ha : g.graph.Adj u v
    · simp [edgeDifference,ha,ha.symm]
    · have hb : ¬g.graph.Adj v u := fun h => ha h.symm
      simp [edgeDifference,ha,hb]
  have hneg : (∑ u ∈ S, ∑ v ∈ S, edgeDifference g z u v) =
      -(∑ u ∈ S, ∑ v ∈ S, edgeDifference g z u v) := by
    calc
      _ = ∑ u ∈ S, ∑ v ∈ S, edgeDifference g z v u := Finset.sum_comm
      _ = ∑ u ∈ S, ∑ v ∈ S, -edgeDifference g z u v := by
        apply Finset.sum_congr rfl
        intro u hu
        apply Finset.sum_congr rfl
        intro v hv
        exact hskew v u
      _ = _ := by simp only [Finset.sum_neg_distrib]
  linarith

lemma cut_flux_identity (g : InputGraph n) (α : ℝ) (z : Fin n → ℝ) (S : Finset (Fin n)) :
    (∑ u ∈ S, (LocalPush.Lα g.graph α *ᵥ z) u) =
      α*(∑ u ∈ S, LocalPush.deg g.graph u*z u)+(1-α)*boundaryFlux g z S := by
  classical
  have hsplit : (∑ u ∈ S, ∑ v, edgeDifference g z u v) = boundaryFlux g z S := by
    simp_rw [← Finset.sum_add_sum_compl S]
    rw [Finset.sum_add_distrib,internal_flux_zero,zero_add]
    rfl
  simp_rw [lap_edge_difference]
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,hsplit]

lemma edge_drop_bound (g : InputGraph n) (s : Fin n) (α : ℝ) (hα : 0 ≤ α ∧ α ≤ 1/2)
    (H : Finset (Fin n)) (z : Fin n → ℝ) (hz : ∀ v, 0 ≤ z v)
    (hs : ∀ v ∉ H, z v = 0)
    (hr : ∀ v ∈ H, (LocalPush.Lα g.graph α *ᵥ z) v ≤ LocalPush.e s v)
    (a b : Fin n) (hab : g.graph.Adj a b) : z a ≤ z b+2 := by
  classical
  by_cases hle : z a ≤ z b
  · linarith
  have hlt : z b < z a := lt_of_not_ge hle
  let S := Finset.univ.filter (fun v => z b < z v)
  have ha : a ∈ S := by simp [S,hlt]
  have hb : b ∈ Sᶜ := by simp [S]
  have hSH : S ⊆ H := by
    intro v hv
    have hv' : z b < z v := (Finset.mem_filter.mp hv).2
    by_contra hno
    rw [hs v hno] at hv'
    linarith [hz b]
  have hterm (u : Fin n) (hu : u ∈ S) (v : Fin n) (hv : v ∈ Sᶜ) :
      0 ≤ edgeDifference g z u v := by
    have hu' : z b < z u := (Finset.mem_filter.mp hu).2
    have hv' : z v ≤ z b := by simpa [S] using hv
    unfold edgeDifference
    split <;> linarith
  have hrow (u : Fin n) (hu : u ∈ S) : 0 ≤ ∑ v ∈ Sᶜ, edgeDifference g z u v :=
    Finset.sum_nonneg fun v hv => hterm u hu v hv
  have hsingle := Finset.single_le_sum (f := fun v => edgeDifference g z a v) (fun v hv => hterm a ha v hv) hb
  have houter := Finset.single_le_sum (f := fun u => ∑ v ∈ Sᶜ, edgeDifference g z u v) hrow ha
  have hflux : z a-z b ≤ boundaryFlux g z S := by
    simpa [edgeDifference,hab,boundaryFlux] using hsingle.trans houter
  have hsum : (∑ u ∈ S, (LocalPush.Lα g.graph α *ᵥ z) u) ≤ 1 := by
    calc
      _ ≤ ∑ u ∈ S, LocalPush.e s u := Finset.sum_le_sum fun u hu => hr u (hSH hu)
      _ ≤ 1 := by
        simp [LocalPush.e,Pi.single_apply]
        split_ifs <;> norm_num
  have hmass : 0 ≤ ∑ u ∈ S, LocalPush.deg g.graph u*z u := by
    apply Finset.sum_nonneg
    intro u hu
    apply mul_nonneg _ (hz u)
    unfold LocalPush.deg
    positivity
  rw [cut_flux_identity] at hsum
  have hp : (1-α)*(z a-z b) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hflux (show 0 ≤ 1-α by linarith [hα.2])
    nlinarith [mul_nonneg hα.1 hmass]
  have hh := mul_le_mul_of_nonneg_right (show (1/2 : ℝ) ≤ 1-α by linarith [hα.2]) (sub_nonneg.mpr hlt.le)
  nlinarith

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BoundaryPaths

set_option autoImplicit false
open Finset
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma exists_boundary_of_reachable (g : InputGraph n) (H : Finset (Fin n)) (s v : Fin n)
    (hs : s ∈ H) (hv : v ∉ H) (hr : g.graph.Reachable s v) :
    ∃ a ∈ H, ∃ b ∉ H, g.graph.Adj a b := by
  classical
  by_contra hn
  have hc (a : Fin n) (ha : a ∈ H) (b : Fin n) (hab : g.graph.Adj a b) : b ∈ H := by
    by_contra hb
    exact hn ⟨a,ha,b,hb,hab⟩
  have hwalk : ∀ {a b : Fin n}, (p : g.graph.Walk a b) → a ∈ H → b ∈ H := by
    intro a b p
    induction p with
    | nil => exact id
    | cons hab p ih =>
      intro ha
      exact ih (hc _ ha _ hab)
  obtain ⟨p⟩ := hr
  exact hv (hwalk p hs)

lemma walk_drop_bound {V : Type*} (G : SimpleGraph V) (z : V → ℝ) (B : ℝ)
    (hedge : ∀ a b, G.Adj a b → z a ≤ z b+B) {a b : V} (p : G.Walk a b) :
    z a ≤ z b+B*(p.length : ℝ) := by
  induction p with
  | nil => simp
  | cons hab p ih =>
    have hh := hedge _ _ hab
    simp only [SimpleGraph.Walk.length_cons,Nat.cast_add,Nat.cast_one]
    nlinarith

lemma proper_domain_path_bound (g : InputGraph n) (s : Fin n) (H : Finset (Fin n))
    (hs : s ∈ H) (hconn : (g.graph.induce (↑H : Set (Fin n))).Connected)
    (hproper : ∃ v, g.graph.Reachable s v ∧ v ∉ H)
    (z : Fin n → ℝ) (hzero : ∀ v ∉ H, z v = 0)
    (hedge : ∀ a b, g.graph.Adj a b → z a ≤ z b+2) :
    ∀ u, z u ≤ 2*(H.card : ℝ) := by
  classical
  obtain ⟨v,hr,hv⟩ := hproper
  obtain ⟨a,ha,b,hb,hab⟩ := exists_boundary_of_reachable g H s v hs hv hr
  have hba : z a ≤ 2 := by simpa [hzero b hb] using hedge a b hab
  intro u
  by_cases hu : u ∈ H
  · obtain ⟨p,hp⟩ := (hconn.preconnected ⟨u,hu⟩ ⟨a,ha⟩).exists_isPath
    have hlen : p.length < H.card := by simpa using hp.length_lt
    have hlen' : (p.length : ℝ)+1 ≤ (H.card : ℝ) := by exact_mod_cast hlen
    have hh := walk_drop_bound (g.graph.induce (↑H : Set (Fin n))) (fun v => z v.val) 2
      (fun x y hxy => hedge x.val y.val hxy) p
    change z u ≤ z a+2*(p.length : ℝ) at hh
    nlinarith
  · rw [hzero u hu]
    positivity

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ActivePotential

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma run_proper_potential_bound (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α ≤ 1/2) (hq : 0 < q ∧ q ≤ 1) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    let st := recursiveRun m g s α q ℓ schedule t
    let H := (st.frames 0).active
    (∃ v, g.graph.Reachable s v ∧ v ∉ H) → ∀ v, st.x v ≤ 3/q := by
  classical
  let st := recursiveRun m g s α q ℓ schedule t
  let H := (st.frames 0).active
  let z := prune q st.x
  change (∃ v, g.graph.Reachable s v ∧ v ∉ H) → ∀ v, st.x v ≤ 3/q
  rw [show (3 : ℝ)/q = 3*(1/q) by ring]
  have ha : 0 < α ∧ α < 1 := ⟨hα.1,by linarith [hα.2]⟩
  have hn := numerical_run m g s α q ha hq.1 hs ℓ schedule t
  change NumericalInvariant g st at hn
  have hr := root_identity_run m g s α q ℓ schedule t
  have hqr : (st.frames 0).q = q := root_threshold_run m g s α q ℓ schedule t
  have hq' : 0 < (st.frames 0).q := by rw [hqr]; exact hq.1
  have hsub := root_prune_subsolution g s α ha st hq' hr hn
  rw [hqr] at hsub
  have hcard := (run_root_volume_bound m g s α q ha hq.1 hs ℓ schedule t).2
  change (H.card : ℝ) ≤ 1/q at hcard
  have hinv : 1 ≤ 1/q := (le_div_iff₀ hq.1).mpr (by simpa using hq.2)
  have hcap : 3*q/8 ≤ 1/q := (show 3*q/8 ≤ 1 by linarith [hq.2]).trans hinv
  intro hproper v
  by_cases he : H = ∅
  · have hout : v ∉ H := by simp [he]
    have hh := ((hn 0 (Nat.zero_le _)).1 v (by simp [parentDomain])).2.2.2 hout
    have hx : st.x v ≤ 3*q/8 := by simpa only [relative,ite_true,hqr] using hh.le
    have hpos : 0 < 1/q := div_pos (by norm_num) hq.1
    linarith
  · have hc := root_connected_run m g s α q ha hq.1 hs ℓ schedule t
    obtain ⟨hsH,hconn⟩ := hc (Finset.nonempty_iff_ne_empty.mpr he)
    have hedge := edge_drop_bound g s α ⟨hα.1.le,hα.2⟩ H z hsub.1 hsub.2.1 hsub.2.2
    have hz := proper_domain_path_bound g s H hsH hconn hproper z hsub.2.1 hedge v
    have hp : st.x v-3*q/8 ≤ z v := le_max_left _ _
    linarith

end
end NearlyOptimalPPR.Computation


set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
noncomputable section

theorem solution (m : SolveModel) (n : ℕ) (g : InputGraph n)
    (s : Fin n) (α q : ℝ) (ℓ : ℕ) (schedule : BlockSchedule)
    (hα : 0 < α ∧ α ≤ 1 / 2) (hq : 0 < q ∧ q ≤ 1)
    (hs : 0 < g.graph.degree s) (t : ℕ) :
    let st := recursiveRun m g s α q ℓ schedule t
    let H := (st.frames 0).active
    (H.Nonempty → s ∈ H ∧ (g.graph.induce (↑H : Set (Fin n))).Connected) ∧
    ((∃ v, g.graph.Reachable s v ∧ v ∉ H) → ∀ v, 0 ≤ st.x v ∧ st.x v ≤ 3 / q) := by
  have ha : 0 < α ∧ α < 1 := ⟨hα.1,by linarith [hα.2]⟩
  refine ⟨root_connected_run m g s α q ha hq.1 hs ℓ schedule t,?_⟩
  intro hproper v
  have hn := numerical_run m g s α q ha hq.1 hs ℓ schedule t
  refine ⟨?_,run_proper_potential_bound m g s α q hα hq hs ℓ schedule t hproper v⟩
  simpa [relative] using
    ((hn 0 (Nat.zero_le _)).1 v (by simp [parentDomain])).2.1

end
