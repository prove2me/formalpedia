-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.recursive_residual_identities
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:31:30.978219+00:00
-- url     : https://prove2.me/submissions/c70295fe-a316-4557-9fdb-b7caec39a210

import Definitions.Def_NearlyOptimalPPR_Computation_proof_invariants


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

lemma region_init (g : InputGraph n) (s : Fin n) (q : ℝ) (ℓ : ℕ)
    (schedule : BlockSchedule) : RegionInvariant (recursiveInit g s q ℓ schedule) := by
  intro i hi
  have hi0 : i = 0 := by simpa only [recursiveInit, Nat.le_zero] using hi
  subst i
  simp [recursiveInit, freshFrame, emptyFrame, parentDomain]

@[simp] lemma refresh_active (g : InputGraph n) (st : RecursiveState n)
    (T : Finset (Fin n)) (i : ℕ) :
    ((refreshKeys g st T).frames i).active = (st.frames i).active := by
  by_cases hi : i ≤ st.top <;> simp [refreshKeys,hi]

@[simp] lemma refresh_parentDomain (g : InputGraph n) (st : RecursiveState n)
    (T : Finset (Fin n)) (i : ℕ) :
    parentDomain (refreshKeys g st T) i = parentDomain st i := by
  unfold parentDomain
  split <;> simp

lemma region_refresh (g : InputGraph n) (st : RecursiveState n)
    (T : Finset (Fin n)) (hi : RegionInvariant st) : RegionInvariant (refreshKeys g st T) := by
  intro i hle
  have hle' : i ≤ st.top := hle
  have hh := hi i hle'
  refine ⟨?_,?_,?_,?_⟩
  · simpa using hh.1
  · rw [refresh_parentDomain, refresh_active]
    simp only [refreshKeys, if_pos hle']
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact hh.2.1 ((Finset.mem_sdiff.mp hv).1)
    · have hv' := (Finset.mem_filter.mp hv).2
      exact Finset.mem_sdiff.mpr ⟨hv'.1,hv'.2.1⟩
  · rw [refresh_active]
    simp only [refreshKeys, if_pos hle']
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact hh.2.2.1 ((Finset.mem_sdiff.mp hv).1)
    · exact ((Finset.mem_filter.mp hv).2).1
  · simpa only [refreshKeys, if_pos hle'] using hh.2.2.2

lemma parentDomain_same (st st' : RecursiveState n)
    (ha : ∀ i, (st'.frames i).active = (st.frames i).active) :
    ∀ i, parentDomain st' i = parentDomain st i := by
  intro i
  unfold parentDomain
  split <;> simp [ha]

lemma region_same (st st' : RecursiveState n) (ht : st'.top = st.top)
    (ha : ∀ i, (st'.frames i).active = (st.frames i).active)
    (he : ∀ i, (st'.frames i).exterior = (st.frames i).exterior)
    (hh : ∀ i, (st'.frames i).high = (st.frames i).high)
    (hc : ∀ i, (st'.frames i).cache ⊆ (st.frames i).cache)
    (hi : RegionInvariant st) : RegionInvariant st' := by
  intro i hle
  rw [ht] at hle
  have h := hi i hle
  rw [ha, he, hh, parentDomain_same st st' ha]
  exact ⟨h.1,h.2.1,h.2.2.1,(hc i).trans h.2.2.2⟩

lemma region_debit (st : RecursiveState n) (producer : ℕ) (cost : ℝ≥0∞)
    (hi : RegionInvariant st) : RegionInvariant (debit st producer cost) := hi

lemma region_changePC (st : RecursiveState n) (pc : NormalizePC)
    (hi : RegionInvariant st) : RegionInvariant (changePC st pc) := by
  refine region_same st (changePC st pc) rfl ?_ ?_ ?_ ?_ hi
  all_goals intro i; by_cases he : i = st.top <;> simp [changePC,changeFrame,he]

lemma region_finishEpisode (st : RecursiveState n)
    (hi : RegionInvariant st) : RegionInvariant (finishEpisode st) := by
  refine region_same st (finishEpisode st) rfl ?_ ?_ ?_ ?_ hi
  all_goals intro i; by_cases he : i = st.top <;> simp [finishEpisode,changeFrame,he]

lemma parentDomain_mono (st st' : RecursiveState n)
    (ha : ∀ i, (st.frames i).active ⊆ (st'.frames i).active) :
    ∀ i, parentDomain st i ⊆ parentDomain st' i := by
  intro i
  unfold parentDomain
  split
  · exact Finset.Subset.refl _
  · exact ha _

lemma region_refresh_of_growth (g : InputGraph n) (st st' : RecursiveState n)
    (T : Finset (Fin n)) (hi : RegionInvariant st) (ht : st'.top = st.top)
    (ha : ∀ i, (st.frames i).active ⊆ (st'.frames i).active)
    (hnew : ∀ i, (st'.frames i).active ⊆ (st.frames i).active ∪ T)
    (hvalid : ∀ i ≤ st.top, (st'.frames i).active ⊆ parentDomain st' i)
    (he : ∀ i, (st'.frames i).exterior ⊆ (st.frames i).exterior)
    (hh : ∀ i, (st'.frames i).high ⊆ (st.frames i).high)
    (hc : ∀ i, (st'.frames i).cache ⊆ (st.frames i).cache) :
    RegionInvariant (refreshKeys g st' T) := by
  intro i hle
  have hle' : i ≤ st'.top := hle
  have hle0 : i ≤ st.top := ht ▸ hle'
  have hs := hi i hle0
  refine ⟨?_,?_,?_,?_⟩
  · simpa using hvalid i hle0
  · rw [refresh_parentDomain,refresh_active]
    simp only [refreshKeys,if_pos hle']
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · have ho := Finset.mem_sdiff.mp hv
      have hold := Finset.mem_sdiff.mp (hs.2.1 (he i ho.1))
      refine Finset.mem_sdiff.mpr ⟨parentDomain_mono st st' ha i hold.1, ?_⟩
      intro hv'
      rcases Finset.mem_union.mp (hnew i hv') with hv' | hv'
      · exact hold.2 hv'
      · exact ho.2 hv'
    · have hn := (Finset.mem_filter.mp hv).2
      exact Finset.mem_sdiff.mpr ⟨hn.1,hn.2.1⟩
  · rw [refresh_active]
    simp only [refreshKeys,if_pos hle']
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact ha i (hs.2.2.1 (hh i (Finset.mem_sdiff.mp hv).1))
    · exact (Finset.mem_filter.mp hv).2.1
  · have hcache := (hc i).trans hs.2.2.2 |>.trans (ha i)
    simpa only [refreshKeys,if_pos hle'] using hcache

lemma region_insert_refresh (g : InputGraph n) (st : RecursiveState n) (t : ℕ)
    (v : Fin n) (T : Finset (Fin n)) (hi : RegionInvariant st)
    (hv : v ∈ parentDomain st t) (hvt : v ∈ T) :
    RegionInvariant (refreshKeys g (changeFrame st t (fun f => {f with active := insert v f.active})) T) := by
  let u := changeFrame st t (fun f => {f with active := insert v f.active})
  have ha : ∀ i, (st.frames i).active ⊆ (u.frames i).active := by
    intro i
    by_cases he : i = t <;> simp [u,changeFrame,he]
  apply region_refresh_of_growth g st u T hi rfl ha
  · intro i
    by_cases he : i = t
    · simp only [u,changeFrame,he,Function.update_self]
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact Finset.mem_union_right _ hvt
      · exact Finset.mem_union_left _ hw
    · simp [u,changeFrame,he]
  · intro i hle
    have hm := parentDomain_mono st u ha i
    by_cases he : i = t
    · subst i
      simp only [u,changeFrame,Function.update_self]
      apply Finset.insert_subset
      · exact hm hv
      · exact ((hi t hle).1).trans hm
    · simpa [u,changeFrame,he] using ((hi i hle).1).trans hm
  all_goals intro i; by_cases he : i = t <;> simp [u,changeFrame,he]

lemma region_jointUpdate (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (h : Fin n → ℝ) (hi : RegionInvariant st) : RegionInvariant (jointUpdate g α st h) := by
  refine region_same st (jointUpdate g α st h) rfl ?_ ?_ ?_ ?_ hi
  all_goals intro i; by_cases he : i ≤ st.top <;> simp [jointUpdate,he]

lemma region_after_admission (g : InputGraph n) (st st' : RecursiveState n)
    (t : ℕ) (v : Fin n) (T : Finset (Fin n)) (hi : RegionInvariant st)
    (hv : v ∈ parentDomain st t) (hvt : v ∈ T) (ht : st'.top = st.top)
    (hA : ∀ i, (st'.frames i).active =
      if i = t then insert v (st.frames i).active else (st.frames i).active)
    (hE : ∀ i, (st'.frames i).exterior = (st.frames i).exterior)
    (hH : ∀ i, (st'.frames i).high = (st.frames i).high)
    (hC : ∀ i, (st'.frames i).cache = (st.frames i).cache) :
    RegionInvariant (refreshKeys g st' T) := by
  have ha : ∀ i, (st.frames i).active ⊆ (st'.frames i).active := by
    intro i
    rw [hA]
    split <;> simp
  apply region_refresh_of_growth g st st' T hi ht ha
  · intro i
    rw [hA]
    split
    · exact Finset.insert_subset_iff.mpr ⟨Finset.mem_union_right _ hvt,Finset.subset_union_left⟩
    · exact Finset.subset_union_left
  · intro i hle
    have hm := parentDomain_mono st st' ha i
    rw [hA]
    split
    · rename_i he
      subst i
      exact Finset.insert_subset_iff.mpr ⟨hm hv,((hi t hle).1).trans hm⟩
    · exact ((hi i hle).1).trans hm
  · intro i; rw [hE]
  · intro i; rw [hH]
  · intro i; rw [hC]

lemma changeFrame_regions_same (st : RecursiveState n) (j : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n)
    (hf : frameRegions (f (st.frames j)) = frameRegions (st.frames j)) :
    ∀ i, frameRegions ((changeFrame st j f).frames i) = frameRegions (st.frames i) := by
  intro i
  by_cases he : i = j <;> simp [changeFrame,he,hf]


end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RegionExterior

set_option autoImplicit false
open Finset
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

set_option maxHeartbeats 500000 in
lemma region_exteriorPush (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) (hi : RegionInvariant st) (hv : v ∈ parentDomain st t) :
    RegionInvariant (exteriorPush g α st t v) := by
  classical
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
  have hba : ∀ i, (base.frames i).active = (st.frames i).active := by
    intro i
    by_cases he : i ≤ st.top <;> simp [base,he]
  have hib : RegionInvariant base := by
    refine region_same st base rfl hba ?_ ?_ ?_ hi
    all_goals intro i; by_cases he : i ≤ st.top <;> simp [base,he]
  have hvb : v ∈ parentDomain base t := by rw [parentDomain_same st base hba]; exact hv
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
  trace "region: prepared intermediate state"
  unfold RegionInvariant parentDomain
  change RegionInvariant (refreshKeys g (if relative st t v+h = 3*f.q/8 then final else base)
    (insert v (g.neighbors v).toFinset))
  trace "region: reduced exterior update"
  by_cases ha : relative st t v+h = 3*f.q/8
  · rw [if_pos ha]
    have htop : final.top = base.top := by
      dsimp [final,child,admitted,changeFrame]
      split_ifs <;> rfl
    trace "region: top proved"
    have hadmit : ∀ i, frameRegions (admitted.frames i) =
        (if i = t then insert v (base.frames i).active else (base.frames i).active,
          (base.frames i).exterior,(base.frames i).high,(base.frames i).cache) := by
      intro i
      by_cases he : i = t <;> simp [admitted,changeFrame,he,frameRegions]
    trace "region: admission proved"
    have hchild : ∀ i, frameRegions (child.frames i) = frameRegions (admitted.frames i) := by
      intro i
      unfold child
      split
      · apply changeFrame_regions_same
        rfl
      · rfl
    trace "region: child proved"
    have hfinal : ∀ i, frameRegions (final.frames i) = frameRegions (child.frames i) := by
      intro i
      unfold final
      split <;> rfl
    have hview (i : ℕ) := (hfinal i).trans ((hchild i).trans (hadmit i))
    trace "region: applying admission invariant"
    refine region_after_admission g base final t v _ hib hvb (by simp) htop ?_ ?_ ?_ ?_
    · intro i
      exact congrArg Prod.fst (hview i)
    · intro i
      exact congrArg (fun z => z.2.1) (hview i)
    · intro i
      exact congrArg (fun z => z.2.2.1) (hview i)
    · intro i
      exact congrArg (fun z => z.2.2.2) (hview i)
  · rw [if_neg ha]
    exact region_refresh g base _ hib

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

-- Proof module: Solutions.RegionControl

set_option autoImplicit false
open Finset
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma region_changeFrame (st : RecursiveState n) (j : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n) (hi : RegionInvariant st)
    (hA : (f (st.frames j)).active = (st.frames j).active)
    (hE : (f (st.frames j)).exterior ⊆ (st.frames j).exterior)
    (hH : (f (st.frames j)).high ⊆ (st.frames j).active)
    (hC : (f (st.frames j)).cache ⊆ (st.frames j).active) :
    RegionInvariant (changeFrame st j f) := by
  have ha : ∀ i, ((changeFrame st j f).frames i).active = (st.frames i).active := by
    intro i
    by_cases he : i = j <;> simp [changeFrame,he,hA]
  have hp := parentDomain_same st (changeFrame st j f) ha
  intro i hle
  have hh := hi i hle
  rw [hp,ha]
  by_cases he : i = j
  · subst i
    simp only [changeFrame,Function.update_self]
    exact ⟨hh.1,hE.trans hh.2.1,hH,hC⟩
  · simpa [changeFrame,he] using hh

lemma region_completeComponent (m : SolveModel) (g : InputGraph n)
    (s : Fin n) (α : ℝ) (st : RecursiveState n) (hi : RegionInvariant st) :
    RegionInvariant (completeComponent m g s α st) := hi

lemma region_endCall (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hi : RegionInvariant st) : RegionInvariant (endCall g α st) := by
  classical
  unfold endCall
  dsimp only
  split
  · exact hi
  · intro i hle
    exact hi i (hle.trans (Nat.sub_le _ _))

lemma region_newframe (st : RecursiveState n) (f : NormalizeFrame n)
    (hi : RegionInvariant st) (hA : f.active = ∅)
    (hE : f.exterior ⊆ (st.frames st.top).active)
    (hH : f.high ⊆ f.active) (hC : f.cache ⊆ f.active) :
    RegionInvariant {st with
      top := st.top+1
      frames := Function.update st.frames (st.top+1) f} := by
  let u : RecursiveState n := {st with
      top := st.top+1
      frames := Function.update st.frames (st.top+1) f}
  change RegionInvariant u
  intro i hle
  change i ≤ st.top+1 at hle
  by_cases he : i = st.top+1
  · subst i
    have hf : u.frames (st.top+1) = f := by simp [u]
    rw [hf]
    have hp : parentDomain u (st.top+1) = (st.frames st.top).active := by
      simp [u,parentDomain]
    rw [hp]
    simpa [hA] using And.intro (show f.active ⊆ (st.frames st.top).active by simp [hA])
      (And.intro (by simpa [hA] using hE) (And.intro hH hC))
  · have hi0 : i ≤ st.top := by omega
    have hp : parentDomain u i = parentDomain st i := by
      unfold parentDomain
      split
      · rfl
      · have hne : i-1 ≠ st.top+1 := by omega
        simp [u,hne]
    change (u.frames i).active ⊆ parentDomain u i ∧
      (u.frames i).exterior ⊆ parentDomain u i \ (u.frames i).active ∧
      (u.frames i).high ⊆ (u.frames i).active ∧ (u.frames i).cache ⊆ (u.frames i).active
    rw [hp]
    simpa [u,he] using hi i hi0

lemma region_controlFrame (st : RecursiveState n) (j : ℕ) (hj : j ≤ st.top)
    (f : NormalizeFrame n → NormalizeFrame n) (hi : RegionInvariant st)
    (hA : (f (st.frames j)).active = (st.frames j).active)
    (hE : (f (st.frames j)).exterior = (st.frames j).exterior)
    (hH : (f (st.frames j)).high = (st.frames j).high)
    (hC : (f (st.frames j)).cache = (st.frames j).cache) :
    RegionInvariant (changeFrame st j f) := by
  apply region_changeFrame st j f hi hA
  · rw [hE]
  · rw [hH]
    exact (hi j hj).2.2.1
  · rw [hC]
    exact (hi j hj).2.2.2

lemma region_drain (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (pc : NormalizePC) (hi : RegionInvariant st) :
    RegionInvariant (if anyExhausted st then changePC (debit st st.top 1) pc else
      match pendingPush st with
      | some (t,v) => exteriorPush g α st t v
      | none => changePC (debit st st.top 1) pc) := by
  classical
  by_cases he : anyExhausted st
  · simp only [he,ite_true]
    exact region_changePC _ pc hi
  · simp only [he,ite_false]
    cases hp : pendingPush st with
    | none => exact region_changePC _ pc hi
    | some p =>
      obtain ⟨t,v⟩ := p
      have hm := pending_push_member st t v hp
      have hv := (Finset.mem_sdiff.mp ((hi t hm.1).2.1 hm.2)).1
      exact region_exteriorPush g α st t v hi hv

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RegionStep

set_option autoImplicit false
open Finset
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

set_option maxHeartbeats 1000000 in
lemma region_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (hi : RegionInvariant st) :
    RegionInvariant (recursiveStep m g s α ℓ schedule st) := by
  classical
  by_cases hd : st.done = true
  · simpa [recursiveStep,hd] using hi
  simp only [recursiveStep,hd,Bool.false_eq_true,↓reduceIte]
  by_cases hc : componentComplete st
  · simp only [hc,ite_true]
    exact region_completeComponent m g s α st hi
  simp only [hc,ite_false]
  cases hpc : (st.frames st.top).pc with
  | initialDrain =>
    simp only [hpc]
    split
    · exact region_changePC _ _ hi
    · split
      · exact region_drain g α st .initialDrain hi
      · split <;> exact region_changePC _ _ hi
  | beginEpisode =>
    simp only [hpc]
    refine region_changeFrame _ _ _ hi rfl (Finset.Subset.refl _) ?_ (Finset.empty_subset _)
    exact Finset.filter_subset _ _
  | fullSolve =>
    simp only [hpc]
    split
    · exact region_changePC _ _ hi
    · split
      · apply region_changePC
        unfold RegionInvariant parentDomain
        exact region_refresh g _ (touchedBy g (st.frames st.top).active)
          (region_jointUpdate g α st _ hi)
      · exact hi
  | normalize =>
    simp only [hpc]
    split
    · exact region_changePC _ _ hi
    · split
      · exact region_changePC _ _ hi
      · let c := freshFrame g schedule ℓ (st.top+1) st.nextId (st.frames st.top).block
          (st.frames st.top).theta (st.frames st.top).active st.x (st.frames st.top).residual
        let u := debit st st.top (16*(volumeNat g (st.frames st.top).active+1)*keyCost st+
          8*(ℓ+2)*((st.frames st.top).block+2) : ℕ)
        let up := changeFrame u st.top (fun fc =>
          {fc with pc := .afterChild, childrenThisEpisode := fc.childrenThisEpisode+1})
        have hup : RegionInvariant up := region_controlFrame u st.top le_rfl _ hi rfl rfl rfl rfl
        have hactive : (up.frames up.top).active = (st.frames st.top).active := by
          simp [up,u,changeFrame,debit]
        have he : c.exterior ⊆ (up.frames up.top).active := by
          rw [hactive]
          exact Finset.filter_subset _ _
        have hnew := region_newframe up c hup rfl he (by simp [c,freshFrame,emptyFrame])
          (by simp [c,freshFrame,emptyFrame])
        unfold RegionInvariant parentDomain
        exact hnew
  | leafDrain =>
    simp only [hpc]
    split
    · exact region_changePC _ _ hi
    · rename_i he
      split
      · cases hp : pendingPush st with
        | none => exact region_changePC _ _ hi
        | some p =>
          obtain ⟨t,v⟩ := p
          have hm := pending_push_member st t v hp
          exact region_exteriorPush g α st t v hi
            (Finset.mem_sdiff.mp ((hi t hm.1).2.1 hm.2)).1
      · split
        · exact region_changePC _ _ hi
        · split
          · let C := (st.frames st.top).cache ∪ (st.frames st.top).high
            let u := changeFrame st st.top (fun fc => {fc with cache := C})
            have hu : RegionInvariant u := by
              refine region_changeFrame st st.top _ hi rfl (Finset.Subset.refl _) (hi st.top le_rfl).2.2.1 ?_
              exact Finset.union_subset_iff.mpr ⟨(hi st.top le_rfl).2.2.2,(hi st.top le_rfl).2.2.1⟩
            unfold RegionInvariant parentDomain
            exact region_refresh g _ (touchedBy g C) (region_jointUpdate g α u _ hu)
          · exact hi
  | afterChild =>
    simp only [hpc]
    split
    · exact region_changePC _ _ (region_finishEpisode _ hi)
    · split
      · exact region_changePC _ _ (region_finishEpisode _ hi)
      · exact region_drain g α st .finishEpisode hi
  | finishEpisode =>
    simp only [hpc]
    split
    · exact region_changePC _ _ (region_finishEpisode _ hi)
    · split
      · exact region_changePC _ _ (region_finishEpisode _ hi)
      · let u := finishEpisode (debit st st.top (16*(volumeNat g (st.frames st.top).active+1) : ℕ))
        have hu : RegionInvariant u := region_finishEpisode _ hi
        exact region_controlFrame u st.top le_rfl
          (fun fc => {fc with
            needFull := decide ((st.frames st.top).Q/2 ≤ ∑ v ∈ (st.frames st.top).active, (st.frames st.top).residual v)
            pc := if (st.frames st.top).theta = (st.frames st.top).q then .normal else .beginEpisode})
          hu rfl rfl rfl rfl
  | restartDrain =>
    simp only [hpc]
    split
    · exact region_changePC _ _ hi
    · split
      · exact region_drain g α st .restartDrain hi
      · exact region_controlFrame (debit st st.top 1) st.top le_rfl
          (fun fc => {fc with needFull := true, pc := .beginEpisode}) hi rfl rfl rfl rfl
  | normal =>
    simp only [hpc]
    exact region_endCall g α _ hi
  | interrupted =>
    simp only [hpc]
    exact region_endCall g α _ hi

lemma region_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    RegionInvariant (recursiveRun m g s α q ℓ schedule t) := by
  induction t with
  | zero => simpa [recursiveRun] using region_init g s q ℓ schedule
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using
      region_step m g s α ℓ schedule _ ih

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RecursiveInvariants

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section

variable {n : ℕ}

lemma root_identity_init (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) :
    RootIdentity g s α (recursiveInit g s q ℓ schedule) := by
  classical
  intro v
  simp [recursiveInit, RootIdentity, freshFrame, emptyFrame, residual,
    show (fun _ : Fin n => (0 : ℝ)) = 0 from rfl]

lemma residual_addition (g : InputGraph n) (s : Fin n) (α : ℝ)
    (x h : Fin n → ℝ) :
    residual g.graph α s (x+h) = residual g.graph α s x - LocalPush.Lα g.graph α *ᵥ h := by
  unfold residual
  rw [Matrix.mulVec_add]
  abel

lemma root_identity_jointUpdate (g : InputGraph n) (s : Fin n) (α : ℝ)
    (st : RecursiveState n) (h : Fin n → ℝ) (hi : RootIdentity g s α st)
    (hh : ∀ v ∉ (st.frames 0).active, h v = 0) :
    RootIdentity g s α (jointUpdate g α st h) := by
  classical
  intro v
  have hbase := hi v
  simp only [jointUpdate, Nat.zero_le, ↓reduceIte, parentDomain, ite_true,
    Finset.mem_univ, Pi.add_apply]
  rw [residual_addition]
  simp only [Pi.sub_apply]
  by_cases hv : v ∈ (st.frames 0).active
  · simp only [hv, ite_true] at hbase ⊢
    linarith
  · simp only [hv, ite_false, hh v hv, add_zero] at hbase ⊢
    linarith

lemma residual_coordinate_update (g : InputGraph n) (s v : Fin n) (α h : ℝ)
    (x : Fin n → ℝ) :
    residual g.graph α s (Function.update x v (x v+h)) =
      residual g.graph α s x - fun u => LocalPush.Lα g.graph α u v * h := by
  have he : Function.update x v (x v+h) = x + Pi.single v h := by
    ext u
    by_cases hu : u = v <;> simp [hu]
  rw [he, residual_addition, Matrix.mulVec_single]
  rfl


lemma root_exterior_x (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (v : Fin n) :
    (exteriorPush g α st 0 v).x = Function.update st.x v
      (st.x v + min ((st.frames 0).residual v / (5*LocalPush.deg g.graph v))
        (3*(st.frames 0).q/8 - st.x v)) := by
  classical
  by_cases ha : st.x v + min ((st.frames 0).residual v / (5*LocalPush.deg g.graph v))
      (3*(st.frames 0).q/8 - st.x v) = 3*(st.frames 0).q/8
  · by_cases ht : 0 < st.top
    · simp [exteriorPush, relative, ha, ht, refreshKeys, debit, changeFrame, parentDomain]
    · simp [exteriorPush, relative, ha, ht, refreshKeys, debit, changeFrame, parentDomain]
  · simp [exteriorPush, relative, ha, refreshKeys, debit, changeFrame]

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

lemma root_identity_exterior_root (g : InputGraph n) (s : Fin n) (α : ℝ)
    (st : RecursiveState n) (v : Fin n) (hi : RootIdentity g s α st)
    (hv : v ∉ (st.frames 0).active) :
    RootIdentity g s α (exteriorPush g α st 0 v) := by
  classical
  let h := min ((st.frames 0).residual v / (5*LocalPush.deg g.graph v))
    (3*(st.frames 0).q/8 - st.x v)
  have hp := root_exterior_projection g α st v
  dsimp only at hp
  rcases hp with ⟨hx,hq,hH,hr⟩
  intro w
  simp only [hx, hq, hH, hr, residual_coordinate_update, Pi.sub_apply]
  change residual g.graph α s st.x w - LocalPush.Lα g.graph α w v*h = _
  rw [hi w]
  by_cases hw : w = v
  · subst w
    simp only [hv, ite_false, Function.update_self]
    have hM : LocalPush.Lα g.graph α v v = LocalPush.deg g.graph v := by
      simp [LocalPush.Lα, LocalPush.degM, LocalPush.adjM]
    rw [hM]
    by_cases ha : st.x v+h = 3*(st.frames 0).q/8
    · dsimp only [h] at ha
      have ham := congrArg (fun z : ℝ => 4*LocalPush.deg g.graph v*z) ha
      simp [ha, hv, h]
      nlinarith
    · dsimp only [h] at ha
      simp [ha, hv, h]
      ring
  · have hM : LocalPush.Lα g.graph α w v =
        -(1-α) * (if g.graph.Adj w v then 1 else 0) := by
      simp [LocalPush.Lα, LocalPush.degM, LocalPush.adjM, Matrix.diagonal_apply_ne _ hw,
        SimpleGraph.adjMatrix_apply]
      split <;> ring
    rw [hM]
    by_cases ha : st.x v+h = 3*(st.frames 0).q/8
    <;> dsimp only [h] at ha
    <;> by_cases hadj : g.graph.Adj w v
    <;> simp [ha, hw, hadj, h, Function.update_of_ne hw]
    <;> ring

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

lemma root_identity_exterior_nonroot (g : InputGraph n) (s : Fin n) (α : ℝ)
    (st : RecursiveState n) (t : ℕ) (v : Fin n) (ht : 0 < t)
    (hi : RootIdentity g s α st) (hv : v ∈ (st.frames 0).active) :
    RootIdentity g s α (exteriorPush g α st t v) := by
  classical
  let h := min ((st.frames t).residual v / (5*LocalPush.deg g.graph v))
    (3*(st.frames t).q/8-relative st t v)
  have hp := nonroot_exterior_projection g α st t v ht
  dsimp only at hp
  rcases hp with ⟨hx,hq,hH,hr⟩
  intro w
  simp only [hx,hq,hH,hr,residual_coordinate_update,Pi.sub_apply]
  change residual g.graph α s st.x w - LocalPush.Lα g.graph α w v*h = _
  rw [hi w]
  by_cases hw : w = v
  · subst w
    simp [LocalPush.Lα, LocalPush.degM, LocalPush.adjM, hv, h]
    ring
  · have hM : LocalPush.Lα g.graph α w v =
        -(1-α)*(if g.graph.Adj w v then 1 else 0) := by
      simp [LocalPush.Lα, LocalPush.degM, LocalPush.adjM, Matrix.diagonal_apply_ne _ hw,
        SimpleGraph.adjMatrix_apply]
      split <;> ring
    rw [hM]
    by_cases ha : g.graph.Adj w v
    <;> simp [hw,ha,h]
    <;> ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootIdentityControl

set_option autoImplicit false
open Finset
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma root_identity_same (g : InputGraph n) (s : Fin n) (α : ℝ)
    (st st' : RecursiveState n) (hx : st'.x = st.x)
    (hq : (st'.frames 0).q = (st.frames 0).q)
    (hA : (st'.frames 0).active = (st.frames 0).active)
    (hr : (st'.frames 0).residual = (st.frames 0).residual)
    (hi : RootIdentity g s α st) : RootIdentity g s α st' := by
  intro v
  simpa only [hx,hq,hA,hr] using hi v

lemma root_identity_debit (g : InputGraph n) (s : Fin n) (α : ℝ)
    (st : RecursiveState n) (producer : ℕ) (cost : ℝ≥0∞) (hi : RootIdentity g s α st) :
    RootIdentity g s α (debit st producer cost) := hi

lemma root_identity_changeFrame (g : InputGraph n) (s : Fin n) (α : ℝ)
    (st : RecursiveState n) (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n)
    (hq : (f (st.frames j)).q = (st.frames j).q)
    (hA : (f (st.frames j)).active = (st.frames j).active)
    (hr : (f (st.frames j)).residual = (st.frames j).residual)
    (hi : RootIdentity g s α st) : RootIdentity g s α (changeFrame st j f) := by
  refine root_identity_same g s α st (changeFrame st j f) rfl ?_ ?_ ?_ hi
  all_goals by_cases he : (0 : ℕ) = j <;> simp_all [changeFrame]

lemma root_identity_otherFrame (g : InputGraph n) (s : Fin n) (α : ℝ)
    (st : RecursiveState n) (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n)
    (hj : j ≠ 0) (hi : RootIdentity g s α st) : RootIdentity g s α (changeFrame st j f) := by
  refine root_identity_same g s α st (changeFrame st j f) rfl ?_ ?_ ?_ hi
  all_goals simp [changeFrame,Ne.symm hj]

lemma root_identity_changePC (g : InputGraph n) (s : Fin n) (α : ℝ)
    (st : RecursiveState n) (pc : NormalizePC) (hi : RootIdentity g s α st) :
    RootIdentity g s α (changePC st pc) :=
  root_identity_changeFrame g s α st st.top _ rfl rfl rfl hi

lemma root_identity_finishEpisode (g : InputGraph n) (s : Fin n) (α : ℝ)
    (st : RecursiveState n) (hi : RootIdentity g s α st) :
    RootIdentity g s α (finishEpisode st) := by
  apply root_identity_changeFrame g s α _ st.top _ rfl rfl rfl
  exact hi

lemma root_identity_endCall (g : InputGraph n) (s : Fin n) (α : ℝ)
    (st : RecursiveState n) (hi : RootIdentity g s α st) :
    RootIdentity g s α (endCall g α st) := by
  classical
  unfold endCall
  dsimp only
  split <;> exact hi

lemma root_identity_completeComponent (m : SolveModel) (g : InputGraph n)
    (s : Fin n) (α : ℝ) (st : RecursiveState n) (hi : RootIdentity g s α st) :
    RootIdentity g s α (completeComponent m g s α st) := hi

lemma solveOn_outside (g : InputGraph n) (α : ℝ) (T : Finset (Fin n))
    (b : Fin n → ℝ) (v : Fin n) (hv : v ∉ T) : solveOn g α T b v = 0 := by
  classical
  simp [solveOn,hv]

lemma root_identity_jointSolve (g : InputGraph n) (s : Fin n) (α : ℝ)
    (st : RecursiveState n) (T : Finset (Fin n)) (b : Fin n → ℝ)
    (hi : RootIdentity g s α st) (hT : T ⊆ (st.frames 0).active) :
    RootIdentity g s α (jointUpdate g α st (solveOn g α T b)) := by
  apply root_identity_jointUpdate g s α st _ hi
  intro v hv
  exact solveOn_outside g α T b v (fun h => hv (hT h))

lemma root_identity_refresh (g : InputGraph n) (s : Fin n) (α : ℝ)
    (st : RecursiveState n) (T : Finset (Fin n)) (hi : RootIdentity g s α st) :
    RootIdentity g s α (refreshKeys g st T) := by
  intro v
  simpa [refreshKeys] using hi v

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootPending

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma root_identity_pendingPush (g : InputGraph n) (s : Fin n) (α : ℝ)
    (st : RecursiveState n) (t : ℕ) (v : Fin n)
    (hr : RegionInvariant st) (hi : RootIdentity g s α st)
    (hp : pendingPush st = some (t,v)) : RootIdentity g s α (exteriorPush g α st t v) := by
  have hm := pending_push_member st t v hp
  have hv := Finset.mem_sdiff.mp ((hr t hm.1).2.1 hm.2)
  by_cases ht : t = 0
  · subst t
    exact root_identity_exterior_root g s α st v hi hv.2
  · have htpos : 0 < t := Nat.pos_of_ne_zero ht
    have hroot : v ∈ (st.frames 0).active := by
      have hpar : parentDomain st t = (st.frames (t-1)).active := by simp [parentDomain,ht]
      rw [hpar] at hv
      exact active_subset_root st hr (t-1) ((Nat.sub_le _ _).trans hm.1) hv.1
    exact root_identity_exterior_nonroot g s α st t v htpos hi hroot

lemma root_identity_drain (g : InputGraph n) (s : Fin n) (α : ℝ)
    (st : RecursiveState n) (pc : NormalizePC)
    (hr : RegionInvariant st) (hi : RootIdentity g s α st) :
    RootIdentity g s α
      (if anyExhausted st then changePC (debit st st.top 1) pc else
        match pendingPush st with
        | some (t,v) => exteriorPush g α st t v
        | none => changePC (debit st st.top 1) pc) := by
  classical
  by_cases he : anyExhausted st
  · simp only [he,ite_true]
    exact root_identity_changePC g s α _ pc (root_identity_debit g s α st st.top 1 hi)
  · simp only [he,ite_false]
    cases hp : pendingPush st with
    | none => exact root_identity_changePC g s α _ pc (root_identity_debit g s α st st.top 1 hi)
    | some p =>
      obtain ⟨t,v⟩ := p
      exact root_identity_pendingPush g s α st t v hr hi hp

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootStep

set_option autoImplicit false
open Finset
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

set_option maxHeartbeats 1000000 in
lemma root_identity_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hr : RegionInvariant st) (hi : RootIdentity g s α st) :
    RootIdentity g s α (recursiveStep m g s α ℓ schedule st) := by
  classical
  by_cases hd : st.done = true
  · simpa [recursiveStep,hd] using hi
  simp only [recursiveStep,hd,Bool.false_eq_true,↓reduceIte]
  by_cases hc : componentComplete st
  · simp only [hc,ite_true]
    exact root_identity_completeComponent m g s α st hi
  simp only [hc,ite_false]
  have hsRoot := active_subset_root st hr st.top le_rfl
  cases hpc : (st.frames st.top).pc with
  | initialDrain =>
    simp only [hpc]
    split
    · exact root_identity_changePC g s α _ _ hi
    · split
      · exact root_identity_drain g s α st _ hr hi
      · split <;> exact root_identity_changePC g s α _ _ hi
  | beginEpisode =>
    simp only [hpc]
    apply root_identity_changeFrame g s α _ _ _ rfl rfl rfl
    exact hi
  | fullSolve =>
    simp only [hpc]
    split
    · exact root_identity_changePC g s α _ _ hi
    · split
      · apply root_identity_changePC
        unfold RootIdentity
        exact root_identity_refresh g s α _ (touchedBy g (st.frames st.top).active)
          (root_identity_jointSolve g s α st (st.frames st.top).active (st.frames st.top).residual hi hsRoot)
      · exact hi
  | normalize =>
    simp only [hpc]
    split
    · exact root_identity_changePC g s α _ _ hi
    · split
      · exact root_identity_changePC g s α _ _ hi
      · let c := freshFrame g schedule ℓ (st.top+1) st.nextId (st.frames st.top).block
          (st.frames st.top).theta (st.frames st.top).active st.x (st.frames st.top).residual
        let u := debit st st.top (16*(volumeNat g (st.frames st.top).active+1)*keyCost st+
          8*(ℓ+2)*((st.frames st.top).block+2) : ℕ)
        let up := changeFrame u st.top (fun fc =>
          {fc with pc := .afterChild, childrenThisEpisode := fc.childrenThisEpisode+1})
        have hup : RootIdentity g s α up := root_identity_changeFrame g s α u st.top _ rfl rfl rfl hi
        unfold RootIdentity
        change RootIdentity g s α (changeFrame up (st.top+1) (fun _ => c))
        exact root_identity_otherFrame g s α up (st.top+1) (fun _ => c) (by omega) hup
  | leafDrain =>
    simp only [hpc]
    split
    · exact root_identity_changePC g s α _ _ hi
    · rename_i he
      split
      · cases hp : pendingPush st with
        | none => exact root_identity_changePC g s α _ _ hi
        | some p =>
          obtain ⟨t,v⟩ := p
          exact root_identity_pendingPush g s α st t v hr hi hp
      · split
        · exact root_identity_changePC g s α _ _ hi
        · split
          · let C := (st.frames st.top).cache ∪ (st.frames st.top).high
            let u := changeFrame st st.top (fun fc => {fc with cache := C})
            have hu : RootIdentity g s α u := root_identity_changeFrame g s α st st.top _ rfl rfl rfl hi
            have hactive : (u.frames 0).active = (st.frames 0).active := by
              by_cases he : (0 : ℕ) = st.top <;> simp [u,changeFrame,he]
            have hC : C ⊆ (u.frames 0).active := by
              rw [hactive]
              exact Finset.Subset.trans (Finset.union_subset_iff.mpr ⟨(hr st.top le_rfl).2.2.2,(hr st.top le_rfl).2.2.1⟩) hsRoot
            unfold RootIdentity
            exact root_identity_refresh g s α _ (touchedBy g C)
              (root_identity_jointSolve g s α u C
                (fun v => (st.frames st.top).residual v - (st.frames st.top).theta*LocalPush.deg g.graph v) hu hC)
          · exact hi
  | afterChild =>
    simp only [hpc]
    split
    · apply root_identity_changePC
      exact root_identity_finishEpisode g s α _ hi
    · split
      · apply root_identity_changePC
        exact root_identity_finishEpisode g s α _ hi
      · exact root_identity_drain g s α st _ hr hi
  | finishEpisode =>
    simp only [hpc]
    split
    · apply root_identity_changePC
      exact root_identity_finishEpisode g s α _ hi
    · split
      · apply root_identity_changePC
        exact root_identity_finishEpisode g s α _ hi
      · apply root_identity_changeFrame g s α _ _ _ rfl rfl rfl
        exact root_identity_finishEpisode g s α _ hi
  | restartDrain =>
    simp only [hpc]
    split
    · exact root_identity_changePC g s α _ _ hi
    · split
      · exact root_identity_drain g s α st _ hr hi
      · exact root_identity_changeFrame g s α _ _ _ rfl rfl rfl hi
  | normal =>
    simp only [hpc]
    exact root_identity_endCall g s α _ hi
  | interrupted =>
    simp only [hpc]
    exact root_identity_endCall g s α _ hi

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ThresholdInvariant

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

@[simp] lemma frame_q_ite (p : Prop) [Decidable p] (a b : RecursiveState n) :
    ((if p then a else b).frames 0).q = if p then (a.frames 0).q else (b.frames 0).q := by
  split <;> rfl

@[simp] lemma frame_q_debit (st : RecursiveState n) (j : ℕ) (cost : ℝ≥0∞) :
    ((debit st j cost).frames 0).q = (st.frames 0).q := rfl

@[simp] lemma frame_q_changeFrame (st : RecursiveState n) (j : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n) (hf : (f (st.frames j)).q = (st.frames j).q) :
    ((changeFrame st j f).frames 0).q = (st.frames 0).q := by
  by_cases he : (0 : ℕ) = j <;> simp_all [changeFrame]

@[simp] lemma frame_q_changePC (st : RecursiveState n) (pc : NormalizePC) :
    ((changePC st pc).frames 0).q = (st.frames 0).q :=
  frame_q_changeFrame st st.top _ rfl

@[simp] lemma frame_q_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) :
    ((refreshKeys g st T).frames 0).q = (st.frames 0).q := by simp [refreshKeys]

@[simp] lemma frame_q_jointUpdate (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (h : Fin n → ℝ) :
    ((jointUpdate g α st h).frames 0).q = (st.frames 0).q := by simp [jointUpdate]

@[simp] lemma frame_q_exteriorPush (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n) :
    ((exteriorPush g α st t v).frames 0).q = (st.frames 0).q := by
  by_cases ht : t = 0
  · subst t
    exact (root_exterior_projection g α st v).2.1
  · exact (nonroot_exterior_projection g α st t v (Nat.pos_of_ne_zero ht)).2.1

@[simp] lemma frame_q_finishEpisode (st : RecursiveState n) :
    ((finishEpisode st).frames 0).q = (st.frames 0).q := by
  by_cases he : (0 : ℕ) = st.top <;> simp [finishEpisode,changeFrame,he]

@[simp] lemma frame_q_endCall (g : InputGraph n) (α : ℝ) (st : RecursiveState n) :
    ((endCall g α st).frames 0).q = (st.frames 0).q := by
  unfold endCall
  dsimp only
  split <;> rfl

@[simp] lemma frame_q_completeComponent (m : SolveModel) (g : InputGraph n) (s : Fin n)
    (α : ℝ) (st : RecursiveState n) :
    ((completeComponent m g s α st).frames 0).q = (st.frames 0).q := rfl

set_option maxHeartbeats 500000 in
lemma root_threshold_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) :
    ((recursiveStep m g s α ℓ schedule st).frames 0).q = (st.frames 0).q := by
  classical
  cases hp : pendingPush st with
  | none =>
    cases hpc : (st.frames st.top).pc <;>
      simp [recursiveStep,hpc,hp,Function.update_apply,debit]
  | some p =>
    obtain ⟨t,v⟩ := p
    cases hpc : (st.frames st.top).pc <;>
      simp [recursiveStep,hpc,hp,Function.update_apply,debit]

lemma root_threshold_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    ((recursiveRun m g s α q ℓ schedule t).frames 0).q = q := by
  induction t with
  | zero => simp [recursiveRun,recursiveInit,freshFrame]
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply',root_threshold_step] using ih

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RunInvariants

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

theorem root_identity_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    RootIdentity g s α (recursiveRun m g s α q ℓ schedule t) := by
  induction t with
  | zero => simpa [recursiveRun] using root_identity_init g s α q ℓ schedule
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using
      root_identity_step m g s α ℓ schedule _ (region_run m g s α q ℓ schedule t) ih

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LayerIdentity

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

/-- The relative residual identity (source equation (4)) between adjacent open calls. -/
lemma layer_identity_init (g : InputGraph n) (s : Fin n) (q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) :
    LayerIdentity g (recursiveInit g s q ℓ schedule) := by
  intro j hj
  simp only [recursiveInit] at hj
  omega

lemma layer_identity_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hr : RegionInvariant st) (hi : LayerIdentity g st) (h : Fin n → ℝ)
    (hs : ∀ v ∉ (st.frames st.top).active, h v = 0) :
    LayerIdentity g (jointUpdate g α st h) := by
  classical
  intro j hj v hv
  have hj' : j ≤ st.top := Nat.le_of_lt hj
  have hc : j+1 ≤ st.top := hj
  have hv' : v ∈ (st.frames j).active := by
    simpa [jointUpdate,hj'] using hv
  have hvp : v ∈ parentDomain st j := (hr j hj').1 hv'
  have hvc : v ∈ parentDomain st (j+1) := by simpa [parentDomain] using hv'
  have hid := hi j hj v hv'
  simp only [jointUpdate,hj',hc,ite_true,relative,Nat.add_eq_zero_iff,
    Nat.one_ne_zero,and_false,ite_false,Pi.add_apply]
  simp only [hvp,hvc,ite_true]
  by_cases hvchild : v ∈ (st.frames (j+1)).active
  · simp only [hvchild,ite_true] at hid ⊢
    linarith
  · have hn : h v = 0 := by
      apply hs v
      intro ht
      have ha : (st.frames st.top).active ⊆ (st.frames (j+1)).active := by
        have hnest : ∀ a b : ℕ, a ≤ b → b ≤ st.top →
            (st.frames b).active ⊆ (st.frames a).active := by
          intro a b hab hbt
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
        exact hnest (j+1) st.top hc le_rfl
      exact hvchild (ha ht)
    simp only [hvchild,ite_false,hn,add_zero] at hid ⊢
    unfold relative at hid
    simp only [Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,ite_false] at hid
    linarith

lemma layer_identity_transport (g : InputGraph n) (st st' : RecursiveState n)
    (ht : st'.top ≤ st.top) (hx : st'.x = st.x)
    (hf : ∀ i ≤ st'.top, layerView (st'.frames i) = layerView (st.frames i))
    (hi : LayerIdentity g st) : LayerIdentity g st' := by
  intro j hj v hv
  have hfields (i : ℕ) (hh : i ≤ st'.top) :
      (st'.frames i).q = (st.frames i).q ∧
      (st'.frames i).active = (st.frames i).active ∧
      (st'.frames i).reference = (st.frames i).reference ∧
      (st'.frames i).residual = (st.frames i).residual := by
    simpa only [layerView,Prod.mk.injEq] using hf i hh
  have hp := hfields j (by omega)
  have hc := hfields (j+1) hj
  rw [hp.2.1] at hv
  have hh := hi j (lt_of_lt_of_le hj ht) v hv
  simpa only [hp.2.2.2,hc.1,hc.2.1,hc.2.2.1,hc.2.2.2,relative,hx] using hh

lemma layer_identity_fresh (g : InputGraph n) (st st' : RecursiveState n)
    (ht : st'.top = st.top+1) (hx : st'.x = st.x)
    (hf : ∀ i ≤ st.top, layerView (st'.frames i) = layerView (st.frames i))
    (hA : (st'.frames (st.top+1)).active = ∅)
    (href : (st'.frames (st.top+1)).reference = st.x)
    (hr : (st'.frames (st.top+1)).residual = (st.frames st.top).residual)
    (hi : LayerIdentity g st) : LayerIdentity g st' := by
  classical
  intro j hj v hv
  have hfields (i : ℕ) (hh : i ≤ st.top) :
      (st'.frames i).q = (st.frames i).q ∧
      (st'.frames i).active = (st.frames i).active ∧
      (st'.frames i).reference = (st.frames i).reference ∧
      (st'.frames i).residual = (st.frames i).residual := by
    simpa only [layerView,Prod.mk.injEq] using hf i hh
  by_cases he : j = st.top
  · subst j
    rw [(hfields st.top le_rfl).2.2.2,hr,hA]
    simp [relative,href,hx]
  · have hlt : j < st.top := by omega
    have hp := hfields j (by omega)
    have hc := hfields (j+1) hlt
    rw [hp.2.1] at hv
    have hh := hi j hlt v hv
    simpa only [hp.2.2.2,hc.1,hc.2.1,hc.2.2.1,hc.2.2.2,relative,hx] using hh

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

/-- Coordinate update before the optional activation and child reference reset. -/
lemma raw_relative (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) (δ : ℝ) (i : ℕ) (w : Fin n) :
    relative (rawExterior g α st t v δ) i w =
      relative st i w+(if w = v then δ else 0) := by
  classical
  by_cases hi : i = 0 <;> by_cases hw : w = v <;> by_cases ht : i ≤ st.top <;>
    simp [relative,rawExterior,hi,hw,ht] <;> ring

lemma layer_identity_raw (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hr : RegionInvariant st) (hi : LayerIdentity g st)
    (t : ℕ) (ht : t ≤ st.top) (v : Fin n)
    (hv : v ∈ parentDomain st t) (hout : v ∉ (st.frames t).active) (δ : ℝ) :
    LayerIdentity g (rawExterior g α st t v δ) := by
  classical
  intro j hj w hw
  have hjt : j ≤ st.top := by exact Nat.le_of_lt hj
  have hct : j+1 ≤ st.top := hj
  have hw' : w ∈ (st.frames j).active := by simpa [rawExterior,hjt] using hw
  have hp : w ∈ parentDomain st j := (hr j hjt).1 hw'
  have hc : w ∈ parentDomain st (j+1) := by simpa [parentDomain] using hw'
  have hid := hi j hj w hw'
  rw [raw_relative]
  simp only [rawExterior,hjt,hct,ite_true]
  simp only [hp,hc,ite_true]
  by_cases hwv : w = v
  · subst w
    by_cases hlt : j+1 < t
    · have hm : v ∈ (st.frames (j+1)).active := by
        have ht0 : t ≠ 0 := by omega
        have hparent : parentDomain st t = (st.frames (t-1)).active := by simp [parentDomain,ht0]
        rw [hparent] at hv
        exact active_subset_between st hr (j+1) (t-1) (by omega) (by omega) hv
      simp only [hm,ite_true] at hid ⊢
      simp only [hlt,show j < t by omega,ite_true]
      linarith
    · by_cases he : j+1 = t
      · have hjlt : j < t := by omega
        have hjne : j ≠ t := by omega
        simp only [he,hout,ite_false] at hid ⊢
        simp only [hjlt,ite_true,lt_self_iff_false,ite_false,ite_true]
        ring_nf at hid ⊢
        linarith
      · have htj : t ≤ j := by omega
        have ha := active_subset_between st hr t j htj hjt hw'
        exact False.elim (hout ha)
  · simp only [hwv,ite_false,add_zero] at hid ⊢
    linarith

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LayerControl

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma layer_debit (g : InputGraph n) (st : RecursiveState n)
    (j : ℕ) (w : ℝ≥0∞) (hi : LayerIdentity g st) :
    LayerIdentity g (debit st j w) := by
  apply layer_identity_transport g st (debit st j w) le_rfl rfl _ hi
  intro i hh
  simp [debit,layerView]

lemma layer_changeFrame (g : InputGraph n) (st : RecursiveState n)
    (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n)
    (hf : layerView (f (st.frames j)) = layerView (st.frames j))
    (hi : LayerIdentity g st) : LayerIdentity g (changeFrame st j f) := by
  apply layer_identity_transport g st (changeFrame st j f) le_rfl rfl _ hi
  intro i hh
  by_cases he : i = j
  · subst i
    simpa [changeFrame] using hf
  · simp [changeFrame,he]

lemma layer_changePC (g : InputGraph n) (st : RecursiveState n) (pc : NormalizePC)
    (hi : LayerIdentity g st) : LayerIdentity g (changePC st pc) :=
  layer_changeFrame g st st.top _ rfl hi

lemma layer_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n))
    (hi : LayerIdentity g st) : LayerIdentity g (refreshKeys g st T) := by
  apply layer_identity_transport g st (refreshKeys g st T) le_rfl rfl _ hi
  intro i hh
  change i ≤ st.top at hh
  simp [refreshKeys,hh,layerView]

lemma layer_finish (g : InputGraph n) (st : RecursiveState n) (hi : LayerIdentity g st) :
    LayerIdentity g (finishEpisode st) := by
  apply layer_changeFrame g _ st.top _ rfl
  exact hi

lemma layer_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hi : LayerIdentity g st) : LayerIdentity g (endCall g α st) := by
  classical
  unfold endCall
  dsimp only
  split
  · exact hi
  · intro j hj v hv
    exact hi j (lt_of_lt_of_le hj (Nat.sub_le _ _)) v hv

lemma layer_complete (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (st : RecursiveState n) (hi : LayerIdentity g st) :
    LayerIdentity g (completeComponent m g s α st) := by
  exact hi

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LayerAdmission

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma layer_identity_admission (g : InputGraph n) (st st' : RecursiveState n)
    (hi : LayerIdentity g st) (hreg : RegionInvariant st) (t : ℕ) (ht : t ≤ st.top)
    (v : Fin n) (hv : v ∉ (st.frames t).active)
    (hcap : relative st t v = 3*(st.frames t).q/8)
    (htop : st'.top = st.top) (hx : st'.x = st.x)
    (hq : ∀ i, (st'.frames i).q = (st.frames i).q)
    (hA : ∀ i, (st'.frames i).active =
      if i = t then insert v (st.frames i).active else (st.frames i).active)
    (href : ∀ i w, (st'.frames i).reference w =
      if t < st.top ∧ i = t+1 ∧ w = v then st.x v else (st.frames i).reference w)
    (hr : ∀ i w, (st'.frames i).residual w =
      if t < st.top ∧ i = t+1 ∧ w = v then
        (st.frames t).residual v+(st.frames t).q*LocalPush.deg g.graph v/2
      else (st.frames i).residual w+
        if i = t ∧ w = v then (st.frames t).q*LocalPush.deg g.graph v/2 else 0) :
    LayerIdentity g st' := by
  classical
  intro j hj w hw
  rw [htop] at hj
  by_cases hwv : w = v
  · subst w
    by_cases hjt : j = t
    · subst j
      have hchild : v ∉ (st.frames (t+1)).active := by
        intro ha
        exact hv (active_subset_between st hreg t (t+1) (by omega) hj ha)
      simp [hr,hA,hq,href,relative,hx,hj,hchild]
    · have hwold : v ∈ (st.frames j).active := by simpa [hA,hjt] using hw
      have hid := hi j hj v hwold
      by_cases hct : j+1 = t
      · have htpos : t ≠ 0 := by omega
        simp only [hct,hv,ite_false] at hid
        have hne : j ≠ t+1 := by omega
        have hctne : j+1 ≠ t+1 := by omega
        simp [hr,hA,hq,href,relative,hx,hjt,hct,hne,hctne]
        have hrel : st.x v-(st.frames t).reference v = 3*(st.frames t).q/8 := by
          simpa [relative,htpos] using hcap
        simp only [relative,htpos,ite_false] at hid
        rw [hrel] at hid
        nlinarith
      · have hne : j ≠ t+1 := by
          intro he
          exact hv (active_subset_between st hreg t j (by omega) (by omega) hwold)
        have hctne : j+1 ≠ t+1 := by omega
        simpa [hr,hA,hq,href,relative,hx,hjt,hct,hne,hctne] using hid
  · have hwold : w ∈ (st.frames j).active := by
      by_cases hjt : j = t <;> simpa [hA,hwv,hjt] using hw
    have hid := hi j hj w hwold
    by_cases hjt : j = t <;> by_cases hct : j+1 = t <;>
      simpa [hr,hA,hq,href,relative,hx,hwv,hjt,hct] using hid

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LayerExterior

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

set_option maxHeartbeats 1000000 in
lemma layer_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hi : LayerIdentity g st) (t : ℕ) (ht : t ≤ st.top)
    (v : Fin n) (hv : v ∈ parentDomain st t) (hout : v ∉ (st.frames t).active) :
    LayerIdentity g (exteriorPush g α st t v) := by
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
  have hbtop : base.top = st.top := rfl
  have hib : LayerIdentity g base := layer_identity_raw g α st hreg hi t ht v hv hout δ
  have hba (i : ℕ) : (base.frames i).active = (st.frames i).active := by
    by_cases hh : i ≤ st.top <;> simp [base,rawExterior,hh]
  have hbq : (base.frames t).q = f.q := by simp [base,rawExterior,ht,f]
  have hibr : RegionInvariant base := by
    apply region_same st base rfl hba _ _ _ hreg
    all_goals intro i; by_cases hh : i ≤ st.top <;> simp [base,rawExterior,hh]
  unfold exteriorPush
  apply layer_debit
  apply layer_refresh
  change LayerIdentity g (if relative st t v+δ = 3*f.q/8 then final else base)
  split
  · rename_i hcap
    have hcapb : relative base t v = 3*(base.frames t).q/8 := by
      rw [raw_relative]
      simpa [base,hbq] using hcap
    apply layer_identity_admission g base final hib hibr t ht v (by simpa [hba] using hout)
      hcapb
    · have hc : child.top = base.top := by unfold child; split <;> rfl
      unfold final
      split <;> exact hc
    · have hc : child.x = base.x := by unfold child; split <;> rfl
      unfold final
      split <;> exact hc
    · intro i
      have hff : final.frames = child.frames := by unfold final; split <;> rfl
      rw [hff]
      by_cases hc : t < st.top <;> by_cases hit : i = t <;> by_cases hic : i = t+1 <;>
        simp [child,hc,admitted,changeFrame,hit,hic]
    · intro i
      have hff : final.frames = child.frames := by unfold final; split <;> rfl
      rw [hff]
      by_cases hc : t < st.top <;> by_cases hit : i = t <;> by_cases hic : i = t+1 <;>
        simp [child,hc,admitted,changeFrame,hit,hic]
    · intro i w
      have hff : final.frames = child.frames := by unfold final; split <;> rfl
      rw [hff,hbtop]
      by_cases hc : t < st.top <;> by_cases hit : i = t <;>
        by_cases hic : i = t+1 <;> by_cases hw : w = v <;>
        simp [child,hc,admitted,changeFrame,Function.update_apply,hit,hic,hw]
    · intro i w
      have hff : final.frames = child.frames := by unfold final; split <;> rfl
      rw [hff,hbtop]
      by_cases hc : t < st.top <;> by_cases hit : i = t <;>
        by_cases hic : i = t+1 <;> by_cases hw : w = v <;>
        simp [child,hc,admitted,changeFrame,Function.update_apply,hit,hic,hw,hbq,d]
  · exact hib

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LayerStep

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma layer_pending (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hi : LayerIdentity g st)
    (t : ℕ) (v : Fin n) (hp : pendingPush st = some (t,v)) :
    LayerIdentity g (exteriorPush g α st t v) := by
  obtain ⟨ht,hv⟩ := pending_push_member st t v hp
  obtain ⟨hdom,hout⟩ := Finset.mem_sdiff.mp ((hreg t ht).2.1 hv)
  exact layer_exterior g α st hreg hi t ht v hdom hout

lemma layer_drain (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hi : LayerIdentity g st) (pc : NormalizePC) :
    LayerIdentity g (if anyExhausted st then changePC (debit st st.top 1) pc else
      match pendingPush st with
      | some (t,v) => exteriorPush g α st t v
      | none => changePC (debit st st.top 1) pc) := by
  split
  · exact layer_changePC g _ pc (layer_debit g st _ _ hi)
  · cases hp : pendingPush st with
    | none => exact layer_changePC g _ pc (layer_debit g st _ _ hi)
    | some p => obtain ⟨t,v⟩ := p; exact layer_pending g α st hreg hi t v hp

set_option maxHeartbeats 1000000 in
lemma layer_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hi : LayerIdentity g st) :
    LayerIdentity g (recursiveStep m g s α ℓ schedule st) := by
  classical
  by_cases hd : st.done = true
  · simpa [recursiveStep,hd] using hi
  simp only [recursiveStep,hd,Bool.false_eq_true,ite_false]
  by_cases hc : componentComplete st
  · simp only [hc,ite_true]
    exact layer_complete m g s α st hi
  simp only [hc,ite_false]
  have hcheap : LayerIdentity g (debit st st.top 1) := layer_debit g st _ _ hi
  cases hpc : (st.frames st.top).pc with
  | initialDrain =>
    simp only [hpc]
    split
    · exact layer_changePC g _ _ hcheap
    · split
      · exact layer_drain g α st hreg hi _
      · split <;> exact layer_changePC g _ _ hcheap
  | beginEpisode =>
    simp only [hpc]
    apply layer_changeFrame g _ _ _ rfl
    exact hi
  | fullSolve =>
    simp only [hpc]
    split
    · exact layer_changePC g _ _ hcheap
    · split
      · apply layer_changePC
        unfold LayerIdentity relative
        exact layer_refresh g _ (touchedBy g (st.frames st.top).active)
          (layer_identity_joint g α st hreg hi
            (solveOn g α (st.frames st.top).active (st.frames st.top).residual)
            (fun v hv => solveOn_outside g α (st.frames st.top).active _ v hv))
      · exact hcheap
  | normalize =>
    simp only [hpc]
    split
    · exact layer_changePC g _ _ hcheap
    · split
      · exact layer_changePC g _ _ hcheap
      · let c := freshFrame g schedule ℓ (st.top+1) st.nextId (st.frames st.top).block
          (st.frames st.top).theta (st.frames st.top).active st.x (st.frames st.top).residual
        let u := debit st st.top (16*(volumeNat g (st.frames st.top).active+1)*keyCost st+
          8*(ℓ+2)*((st.frames st.top).block+2) : ℕ)
        let up := changeFrame u st.top (fun fc =>
          {fc with pc := .afterChild, childrenThisEpisode := fc.childrenThisEpisode+1})
        have hup : LayerIdentity g up := layer_changeFrame g u st.top _ rfl
          (layer_debit g st _ _ hi)
        let newState : RecursiveState n := {up with
          top := st.top+1
          nextId := st.nextId+1
          frames := Function.update up.frames (st.top+1) c
          information := Function.update up.information c.id (some ⟨st.top+1,(st.frames st.top).block,c.block⟩)}
        change LayerIdentity g newState
        apply layer_identity_fresh g up newState rfl rfl _ _ _ _ hup
        · intro i hh
          have hne : i ≠ st.top+1 := by change i ≤ st.top at hh; omega
          simp [newState,hne,up,u,changeFrame,debit,layerView]
        · simp [newState,up,u,changeFrame,debit,c,freshFrame,emptyFrame]
        · simp [newState,up,u,changeFrame,debit,c,freshFrame]
        · simp [newState,up,u,changeFrame,debit,c,freshFrame]
  | leafDrain =>
    simp only [hpc]
    split
    · exact layer_changePC g _ _ hcheap
    · split
      · cases hp : pendingPush st with
        | none => exact layer_changePC g _ _ hcheap
        | some p => obtain ⟨t,v⟩ := p; exact layer_pending g α st hreg hi t v hp
      · split
        · exact layer_changePC g _ _ hcheap
        · split
          · let C := (st.frames st.top).cache ∪ (st.frames st.top).high
            let u := changeFrame st st.top (fun fc => {fc with cache := C})
            have hu : LayerIdentity g u := layer_changeFrame g st st.top _ rfl hi
            have hur : RegionInvariant u := by
              apply region_changeFrame st st.top _ hreg rfl (Finset.Subset.refl _)
              · exact (hreg st.top le_rfl).2.2.1
              · exact Finset.union_subset_iff.mpr
                  ⟨(hreg st.top le_rfl).2.2.2,(hreg st.top le_rfl).2.2.1⟩
            apply layer_debit g _ st.top (jointCost m g st C)
            apply layer_refresh g _ (touchedBy g C)
            apply layer_identity_joint g α u hur hu
            intro v hv
            apply solveOn_outside
            intro hm
            have hC := Finset.union_subset_iff.mpr
              ⟨(hreg st.top le_rfl).2.2.2,(hreg st.top le_rfl).2.2.1⟩ hm
            apply hv
            simpa [u,changeFrame] using hC
          · exact hcheap
  | afterChild =>
    simp only [hpc]
    split
    · exact layer_changePC g _ _ (layer_finish g _ hcheap)
    · split
      · exact layer_changePC g _ _ (layer_finish g _ hcheap)
      · exact layer_drain g α st hreg hi _
  | finishEpisode =>
    simp only [hpc]
    split
    · exact layer_changePC g _ _ (layer_finish g _ hcheap)
    · split
      · exact layer_changePC g _ _ (layer_finish g _ hcheap)
      · apply layer_changeFrame g _ _ _ rfl
        apply layer_finish
        exact hi
  | restartDrain =>
    simp only [hpc]
    split
    · exact layer_changePC g _ _ hcheap
    · split
      · exact layer_drain g α st hreg hi _
      · exact layer_changeFrame g _ _ _ rfl hcheap
  | normal =>
    simp only [hpc]
    exact layer_end g α _ hcheap
  | interrupted =>
    simp only [hpc]
    exact layer_end g α _ hcheap

lemma layer_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    LayerIdentity g (recursiveRun m g s α q ℓ schedule t) := by
  induction t with
  | zero => simpa [recursiveRun] using layer_identity_init g s q ℓ schedule
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using
      layer_step m g s α ℓ schedule _ (region_run m g s α q ℓ schedule t) ih

end
end NearlyOptimalPPR.Computation

set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
noncomputable section
theorem solution (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    let st := recursiveRun m g s α q ℓ schedule t
    RegionInvariant st ∧ RootIdentity g s α st ∧ LayerIdentity g st ∧ (st.frames 0).q = q := by
  exact ⟨region_run m g s α q ℓ schedule t, root_identity_run m g s α q ℓ schedule t,
    layer_run m g s α q ℓ schedule t, root_threshold_run m g s α q ℓ schedule t⟩
end

