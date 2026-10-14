-- Prove2me | solution 2 for GradErrors.Stochastic.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-12T03:08:00.662261+00:00
-- url     : https://prove2.me/submissions/4d94f9ba-744c-43f0-b95a-a74e30633c31

-- Complete checked reconstruction of the native stochastic gradient convergence theorem.
-- Licensed under Apache 2.0.
import Mathlib


-- Begin SeriesBasic

open Filter Topology Finset InnerProductSpace
namespace GradErrors.Stochastic.Proof

/-- Convergence of ordered initial partial sums; no unconditional-summability assertion. -/
def SeriesConverges {E : Type*} [AddCommMonoid E] [TopologicalSpace E] (a : ℕ → E) : Prop :=
  ∃ l : E, Tendsto (fun n => ∑ t ∈ range n, a t) atTop (𝓝 l)

structure NoiseLimits {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (γ : ℕ → ℝ) (g w : ℕ → E) (G χ : ℕ → ℝ) : Prop where
  smallInner : SeriesConverges (fun t => χ t * γ t * ⟪g t, w t⟫_ℝ)
  scaledVector : SeriesConverges (fun t => (γ t / G t) • w t)
  scaledInner : SeriesConverges (fun t => γ t * ⟪g t, w t⟫_ℝ / (G t)^2)
  scaledSquare : SeriesConverges (fun t => (γ t)^2 * ‖w t‖^2 / (G t)^2)
  smallSquare : SeriesConverges (fun t => (γ t)^2 * χ t * ‖w t‖^2)

end GradErrors.Stochastic.Proof
-- End SeriesBasic

-- Begin BlockState

open Filter Topology Finset
namespace GradErrors.Stochastic.Proof

structure BlockState where
  start : ℕ
  height : ℝ
  spent : ℝ
  active : Bool

def idleState (δ : ℝ) (t : ℕ) : BlockState := ⟨t,δ,0,false⟩

def CanContinue (η : ℝ) (γ g : ℕ → ℝ) (t : ℕ) (q : BlockState) : Prop :=
  q.active = true ∧ q.height / 2 ≤ g t ∧ g t ≤ 2*q.height ∧ q.spent + γ t ≤ η

noncomputable def blockStep (δ η : ℝ) (γ g : ℕ → ℝ) (t : ℕ) (q : BlockState) : BlockState := by
  classical
  exact if CanContinue η γ g t q then
    ⟨q.start,q.height,q.spent+γ t,true⟩
  else if δ ≤ g t then ⟨t,g t,γ t,true⟩ else idleState δ t

noncomputable def blockBefore (δ η : ℝ) (γ g : ℕ → ℝ) : ℕ → BlockState
  | 0 => idleState δ 0
  | t+1 => blockStep δ η γ g t (blockBefore δ η γ g t)

noncomputable def blockAt (δ η : ℝ) (γ g : ℕ → ℝ) (t : ℕ) : BlockState :=
  blockBefore δ η γ g (t+1)

noncomputable def scaleAt (δ η : ℝ) (γ g : ℕ → ℝ) (t : ℕ) : ℝ :=
  (blockAt δ η γ g t).height

noncomputable def smallAt (δ η : ℝ) (γ g : ℕ → ℝ) (t : ℕ) : ℝ :=
  if (blockAt δ η γ g t).active then 0 else 1

theorem blockAt_zero (δ η : ℝ) (γ g : ℕ → ℝ) :
    blockAt δ η γ g 0 = blockStep δ η γ g 0 (idleState δ 0) := rfl

theorem blockAt_succ (δ η : ℝ) (γ g : ℕ → ℝ) (t : ℕ) :
    blockAt δ η γ g (t+1) = blockStep δ η γ g (t+1) (blockAt δ η γ g t) := rfl

end GradErrors.Stochastic.Proof
-- End BlockState

-- Begin BlockInvariants

open Filter Topology Finset
namespace GradErrors.Stochastic.Proof

theorem block_height_ge {δ η : ℝ} {γ g : ℕ → ℝ} (t : ℕ) :
    δ ≤ (blockAt δ η γ g t).height := by
  classical
  induction t with
  | zero => simp only [blockAt_zero, blockStep, CanContinue, idleState]; split_ifs <;> simp_all
  | succ t ih =>
    rw [blockAt_succ]
    unfold blockStep
    split_ifs <;> simp_all [idleState]

theorem block_active_bounds {δ η : ℝ} {γ g : ℕ → ℝ} (hδ : 0 ≤ δ)
    (hγ : ∀ t, γ t ≤ η) (t : ℕ) (ha : (blockAt δ η γ g t).active = true) :
    (blockAt δ η γ g t).height / 2 ≤ g t ∧
    g t ≤ 2*(blockAt δ η γ g t).height ∧ (blockAt δ η γ g t).spent ≤ η := by
  classical
  change (blockStep δ η γ g t (blockBefore δ η γ g t)).active = true at ha
  change (blockStep δ η γ g t (blockBefore δ η γ g t)).height / 2 ≤ g t ∧
    g t ≤ 2*(blockStep δ η γ g t (blockBefore δ η γ g t)).height ∧
    (blockStep δ η γ g t (blockBefore δ η γ g t)).spent ≤ η
  unfold blockStep at ha ⊢
  split_ifs at ha ⊢ with hc hg
  · exact ⟨hc.2.1,hc.2.2.1,hc.2.2.2⟩
  · exact ⟨by dsimp; linarith,by dsimp; linarith,hγ t⟩
  · simp [idleState] at ha

theorem block_inactive {δ η : ℝ} {γ g : ℕ → ℝ} (t : ℕ)
    (ha : (blockAt δ η γ g t).active = false) :
    blockAt δ η γ g t = idleState δ t ∧ g t < δ := by
  classical
  change (blockStep δ η γ g t (blockBefore δ η γ g t)).active = false at ha
  change blockStep δ η γ g t (blockBefore δ η γ g t) = idleState δ t ∧ g t < δ
  by_cases hc : CanContinue η γ g t (blockBefore δ η γ g t)
  · simp [blockStep,hc] at ha
  · by_cases hg : δ ≤ g t
    · simp [blockStep,hc,hg] at ha
    · exact ⟨by simp [blockStep,hc,hg],lt_of_not_ge hg⟩

theorem block_start_le {δ η : ℝ} {γ g : ℕ → ℝ} (t : ℕ) :
    (blockAt δ η γ g t).start ≤ t := by
  classical
  induction t with
  | zero => simp only [blockAt_zero, blockStep, CanContinue, idleState]; split_ifs <;> simp_all
  | succ t ih =>
    rw [blockAt_succ]
    unfold blockStep
    split_ifs <;> simp_all [idleState]
    omega

theorem scale_bound {δ η : ℝ} {γ g : ℕ → ℝ} (hδ : 0 ≤ δ)
    (hγ : ∀ t, γ t ≤ η) (t : ℕ) : g t ≤ 2*scaleAt δ η γ g t := by
  cases ha : (blockAt δ η γ g t).active
  · have h := block_inactive t ha
    simp only [scaleAt,h.1,idleState]
    linarith [h.2]
  · exact (block_active_bounds hδ hγ t ha).2.1

theorem small_binary (δ η : ℝ) (γ g : ℕ → ℝ) (t : ℕ) :
    smallAt δ η γ g t = 0 ∨ smallAt δ η γ g t = 1 := by
  unfold smallAt
  split <;> simp

theorem small_gradient {δ η : ℝ} {γ g : ℕ → ℝ} {t : ℕ}
    (h : smallAt δ η γ g t = 1) : g t < δ := by
  cases ha : (blockAt δ η γ g t).active
  · exact (block_inactive t ha).2
  · simp [smallAt,ha] at h

end GradErrors.Stochastic.Proof
-- End BlockInvariants

-- Begin BlockRuns

open Finset
namespace GradErrors.Stochastic.Proof

theorem block_step_cases (δ η : ℝ) (γ g : ℕ → ℝ) (t : ℕ) :
    (CanContinue η γ g (t+1) (blockAt δ η γ g t) ∧
      blockAt δ η γ g (t+1) =
        ⟨(blockAt δ η γ g t).start,(blockAt δ η γ g t).height,
          (blockAt δ η γ g t).spent+γ (t+1),true⟩) ∨
    (blockAt δ η γ g (t+1)).start = t+1 := by
  classical
  rw [blockAt_succ]
  unfold blockStep
  split_ifs with hc hg
  · exact Or.inl ⟨hc,rfl⟩
  · exact Or.inr rfl
  · exact Or.inr rfl

theorem block_start_mono (δ η : ℝ) (γ g : ℕ → ℝ) :
    Monotone (fun t => (blockAt δ η γ g t).start) := by
  apply monotone_nat_of_le_succ
  intro t
  rcases block_step_cases δ η γ g t with ⟨hc,he⟩ | he
  · simp only [he,le_refl]
  · rw [he]
    exact (block_start_le t).trans (Nat.le_succ t)

theorem block_reference {δ η : ℝ} {γ g : ℕ → ℝ} (t : ℕ)
    (ha : (blockAt δ η γ g t).active = true) :
    (blockAt δ η γ g t).height = g (blockAt δ η γ g t).start := by
  classical
  induction t with
  | zero =>
    simp only [blockAt_zero,blockStep,CanContinue,idleState] at ha ⊢
    split_ifs <;> simp_all
  | succ t ih =>
    rw [blockAt_succ] at ha ⊢
    unfold blockStep at ha ⊢
    split_ifs at ha ⊢ with hc hg
    · exact ih hc.1
    · rfl
    · simp [idleState] at ha

theorem block_spent_sum {δ η : ℝ} {γ g : ℕ → ℝ} (t : ℕ)
    (ha : (blockAt δ η γ g t).active = true) :
    (blockAt δ η γ g t).spent = ∑ i ∈ Ico (blockAt δ η γ g t).start (t+1), γ i := by
  classical
  induction t with
  | zero =>
    simp only [blockAt_zero,blockStep,CanContinue,idleState] at ha ⊢
    split_ifs <;> simp_all
  | succ t ih =>
    rw [blockAt_succ] at ha ⊢
    unfold blockStep at ha ⊢
    split_ifs at ha ⊢ with hc hg
    · simp only
      rw [sum_Ico_succ_top (by have hh := block_start_le (δ:=δ) (η:=η) (γ:=γ) (g:=g) t; omega : (blockAt δ η γ g t).start ≤ t+1), ih hc.1]
    · simp
    · simp [idleState] at ha

theorem block_past {δ η : ℝ} {γ g : ℕ → ℝ} (t : ℕ)
    (ha : (blockAt δ η γ g t).active = true) :
    ∀ i, (blockAt δ η γ g t).start ≤ i → i ≤ t →
      (blockAt δ η γ g i).active = true ∧
      (blockAt δ η γ g i).start = (blockAt δ η γ g t).start := by
  classical
  induction t with
  | zero =>
    intro i hi hit
    have he : i = 0 := by omega
    subst i
    exact ⟨ha,rfl⟩
  | succ t ih =>
    intro i hi hit
    by_cases he : i = t+1
    · subst i; exact ⟨ha,rfl⟩
    have hit' : i ≤ t := by omega
    rcases block_step_cases δ η γ g t with ⟨hc,hstep⟩ | hstart
    · rw [hstep] at hi ⊢
      exact ih hc.1 i hi hit'
    · rw [hstart] at hi
      omega

end GradErrors.Stochastic.Proof
-- End BlockRuns

-- Begin BlockStops

open Finset Filter Topology
namespace GradErrors.Stochastic.Proof

theorem exists_block_change {δ η : ℝ} {γ g : ℕ → ℝ} (hδ : 0 ≤ δ)
    (hγ : ∀ t, γ t ≤ η)
    (hsum : Tendsto (fun n => ∑ t ∈ range n, γ t) atTop atTop) (a : ℕ) :
    ∃ b, a < b ∧ (blockAt δ η γ g b).start ≠ a := by
  by_contra hn
  push Not at hn
  obtain ⟨n,hlarge,hnlarge⟩ := ((hsum.eventually (eventually_gt_atTop
    ((∑ t ∈ range a, γ t)+η))).and (eventually_ge_atTop (a+2))).exists
  have hlt : a < n-1 := by omega
  have he := hn (n-1) hlt
  have ha : (blockAt δ η γ g (n-1)).active = true := by
    cases hx : (blockAt δ η γ g (n-1)).active
    · have hs := congrArg BlockState.start (block_inactive (n-1) hx).1
      simp only [idleState] at hs
      omega
    · rfl
  have hb := (block_active_bounds hδ hγ (n-1) ha).2.2
  rw [block_spent_sum (n-1) ha,he] at hb
  have hnn : n-1+1 = n := by omega
  rw [hnn,sum_Ico_eq_sub γ (by omega)] at hb
  linarith

noncomputable def blockStop {δ η : ℝ} {γ g : ℕ → ℝ} (hδ : 0 ≤ δ)
    (hγ : ∀ t, γ t ≤ η)
    (hsum : Tendsto (fun n => ∑ t ∈ range n, γ t) atTop atTop) (a : ℕ) : ℕ :=
  Nat.find (exists_block_change (g:=g) hδ hγ hsum a)

theorem blockStop_gt {δ η : ℝ} {γ g : ℕ → ℝ} (hδ : 0 ≤ δ)
    (hγ : ∀ t, γ t ≤ η)
    (hsum : Tendsto (fun n => ∑ t ∈ range n, γ t) atTop atTop) (a : ℕ) :
    a < blockStop (g:=g) hδ hγ hsum a := (Nat.find_spec (exists_block_change hδ hγ hsum a)).1

theorem blockStop_changed {δ η : ℝ} {γ g : ℕ → ℝ} (hδ : 0 ≤ δ)
    (hγ : ∀ t, γ t ≤ η)
    (hsum : Tendsto (fun n => ∑ t ∈ range n, γ t) atTop atTop) (a : ℕ) :
    (blockAt δ η γ g (blockStop (g:=g) hδ hγ hsum a)).start ≠ a :=
  (Nat.find_spec (exists_block_change hδ hγ hsum a)).2

theorem blockStop_inside {δ η : ℝ} {γ g : ℕ → ℝ} (hδ : 0 ≤ δ)
    (hγ : ∀ t, γ t ≤ η)
    (hsum : Tendsto (fun n => ∑ t ∈ range n, γ t) atTop atTop) {a t : ℕ}
    (ha : (blockAt δ η γ g a).start = a) (hat : a ≤ t)
    (ht : t < blockStop (g:=g) hδ hγ hsum a) : (blockAt δ η γ g t).start = a := by
  by_cases he : t = a
  · simpa only [he] using ha
  · by_contra hn
    exact Nat.find_min (exists_block_change hδ hγ hsum a) ht ⟨by omega,hn⟩

theorem blockStop_is_start {δ η : ℝ} {γ g : ℕ → ℝ} (hδ : 0 ≤ δ)
    (hγ : ∀ t, γ t ≤ η)
    (hsum : Tendsto (fun n => ∑ t ∈ range n, γ t) atTop atTop) {a : ℕ}
    (ha : (blockAt δ η γ g a).start = a) :
    (blockAt δ η γ g (blockStop (g:=g) hδ hγ hsum a)).start =
      blockStop (g:=g) hδ hγ hsum a := by
  let b := blockStop (g:=g) hδ hγ hsum a
  have hab : a < b := blockStop_gt hδ hγ hsum a
  have hb : b-1+1 = b := by omega
  have hprev : (blockAt δ η γ g (b-1)).start = a :=
    blockStop_inside hδ hγ hsum ha (by omega) (by omega)
  rcases block_step_cases δ η γ g (b-1) with ⟨_,he⟩ | he
  · have hh := congrArg BlockState.start he
    simp only [hb] at hh
    exact False.elim (blockStop_changed hδ hγ hsum a (hh.trans hprev))
  · simpa only [hb] using he

end GradErrors.Stochastic.Proof
-- End BlockStops

-- Begin BlockIntervals

open Finset Filter Topology
namespace GradErrors.Stochastic.Proof
variable {δ η : ℝ} {γ g : ℕ → ℝ}

theorem blockStop_active_inside (hδ : 0 ≤ δ) (hγ : ∀ t, γ t ≤ η)
    (hsum : Tendsto (fun n => ∑ t ∈ range n, γ t) atTop atTop) {a t : ℕ}
    (ha : (blockAt δ η γ g a).start = a)
    (haa : (blockAt δ η γ g a).active = true) (hat : a ≤ t)
    (ht : t < blockStop (g:=g) hδ hγ hsum a) :
    (blockAt δ η γ g t).active = true ∧ (blockAt δ η γ g t).height = g a := by
  have he := blockStop_inside hδ hγ hsum ha hat ht
  have hact : (blockAt δ η γ g t).active = true := by
    by_cases hta : t = a
    · simpa only [hta] using haa
    · cases hh : (blockAt δ η γ g t).active
      · have hs := congrArg BlockState.start (block_inactive t hh).1
        simp only [idleState] at hs
        omega
      · rfl
  exact ⟨hact,(block_reference t hact).trans (congrArg g he)⟩

theorem blockStop_budget (hδ : 0 ≤ δ) (hγ : ∀ t, γ t ≤ η)
    (hsum : Tendsto (fun n => ∑ t ∈ range n, γ t) atTop atTop) {a : ℕ}
    (ha : (blockAt δ η γ g a).start = a)
    (haa : (blockAt δ η γ g a).active = true) :
    (∑ i ∈ Ico a (blockStop (g:=g) hδ hγ hsum a), γ i) ≤ η := by
  let b := blockStop (g:=g) hδ hγ hsum a
  have hab : a < b := blockStop_gt hδ hγ hsum a
  have hact := (blockStop_active_inside hδ hγ hsum ha haa (t:=b-1) (by omega) (by omega)).1
  have hstart := blockStop_inside hδ hγ hsum ha (t:=b-1) (by omega) (by omega)
  have hb := (block_active_bounds hδ hγ (b-1) hact).2.2
  rw [block_spent_sum (b-1) hact,hstart] at hb
  simpa only [show b-1+1=b by omega] using hb

theorem blockStop_exhausted (hδ : 0 ≤ δ) (hγ : ∀ t, γ t ≤ η)
    (hsum : Tendsto (fun n => ∑ t ∈ range n, γ t) atTop atTop) {a : ℕ}
    (ha : (blockAt δ η γ g a).start = a)
    (haa : (blockAt δ η γ g a).active = true)
    (hb : g a / 2 ≤ g (blockStop (g:=g) hδ hγ hsum a) ∧
      g (blockStop (g:=g) hδ hγ hsum a) ≤ 2*g a) :
    η < (∑ i ∈ Ico a (blockStop (g:=g) hδ hγ hsum a), γ i) +
      γ (blockStop (g:=g) hδ hγ hsum a) := by
  classical
  let b := blockStop (g:=g) hδ hγ hsum a
  have hab : a < b := blockStop_gt hδ hγ hsum a
  have hbp : b-1+1=b := by omega
  have ht := blockStop_active_inside hδ hγ hsum ha haa (t:=b-1) (by omega) (by omega)
  have hs := blockStop_inside hδ hγ hsum ha (t:=b-1) (by omega) (by omega)
  by_contra hn
  have hc : CanContinue η γ g b (blockAt δ η γ g (b-1)) := by
    refine ⟨ht.1,?_,?_,?_⟩
    · simpa only [ht.2] using hb.1
    · simpa only [ht.2] using hb.2
    · rw [block_spent_sum (b-1) ht.1,hs,hbp]
      exact le_of_not_gt hn
  have he := blockAt_succ δ η γ g (b-1)
  rw [hbp,blockStep,if_pos hc] at he
  have he' := congrArg BlockState.start he
  exact blockStop_changed hδ hγ hsum a (he'.trans hs)

theorem blockStop_inactive (hδ : 0 ≤ δ) (hγ : ∀ t, γ t ≤ η)
    (hsum : Tendsto (fun n => ∑ t ∈ range n, γ t) atTop atTop) {a : ℕ}
    (haa : (blockAt δ η γ g a).active = false) :
    blockStop (g:=g) hδ hγ hsum a = a+1 := by
  classical
  have hs : (blockAt δ η γ g (a+1)).start = a+1 := by
    rw [blockAt_succ]
    simp only [blockStep,CanContinue,haa,Bool.false_eq_true,false_and,ite_false]
    split_ifs <;> rfl
  have hle : blockStop (g:=g) hδ hγ hsum a ≤ a+1 :=
    Nat.find_min' (exists_block_change hδ hγ hsum a) ⟨by omega,by rw [hs]; omega⟩
  have hgt := blockStop_gt (g:=g) hδ hγ hsum a
  omega

end GradErrors.Stochastic.Proof
-- End BlockIntervals

-- Begin ActiveInterval

open Finset Filter Topology
namespace GradErrors.Stochastic.Proof

structure ActiveInterval (δ η : ℝ) (γ h G : ℕ → ℝ) (a b : ℕ) : Prop where
  nonempty : a < b
  height_ge : δ ≤ h a
  scale_eq : ∀ t ∈ Ico a b, G t = h a
  lower : ∀ t ∈ Ico a b, h a / 2 ≤ h t
  upper : ∀ t ∈ Ico a b, h t ≤ 2*h a
  budget : (∑ t ∈ Ico a b, γ t) ≤ η
  maximal : h a / 2 ≤ h b → h b ≤ 2*h a → η < (∑ t ∈ Ico a b, γ t)+γ b

theorem activeInterval_of_stop {δ η : ℝ} {γ h : ℕ → ℝ}
    (hδ : 0 ≤ δ) (hγ : ∀ t, γ t ≤ η)
    (hsum : Tendsto (fun n => ∑ t ∈ range n, γ t) atTop atTop) {a : ℕ}
    (ha : (blockAt δ η γ h a).start = a)
    (haa : (blockAt δ η γ h a).active = true) :
    ActiveInterval δ η γ h (scaleAt δ η γ h) a (blockStop (g:=h) hδ hγ hsum a) := by
  have href : (blockAt δ η γ h a).height = h a := (block_reference a haa).trans (congrArg h ha)
  refine ⟨blockStop_gt hδ hγ hsum a,?_,?_,?_,?_,blockStop_budget hδ hγ hsum ha haa,?_⟩
  · rw [← href]
    exact block_height_ge a
  · intro t ht
    exact (blockStop_active_inside hδ hγ hsum ha haa (mem_Ico.mp ht).1 (mem_Ico.mp ht).2).2
  · intro t ht
    have hh := blockStop_active_inside hδ hγ hsum ha haa (mem_Ico.mp ht).1 (mem_Ico.mp ht).2
    simpa only [hh.2] using (block_active_bounds hδ hγ t hh.1).1
  · intro t ht
    have hh := blockStop_active_inside hδ hγ hsum ha haa (mem_Ico.mp ht).1 (mem_Ico.mp ht).2
    simpa only [hh.2] using (block_active_bounds hδ hγ t hh.1).2.1
  · intro hb1 hb2
    exact blockStop_exhausted hδ hγ hsum ha haa ⟨hb1,hb2⟩

end GradErrors.Stochastic.Proof
-- End ActiveInterval

-- Begin FiniteMotion

open Finset InnerProductSpace
namespace GradErrors.Stochastic.Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem motion_sum {x s w : ℕ → E} {γ : ℕ → ℝ}
    (hx : ∀ t, x (t+1) = x t + γ t • (s t+w t)) {a b : ℕ} (hab : a ≤ b) :
    x b-x a = (∑ t ∈ Ico a b, γ t • s t)+(∑ t ∈ Ico a b, γ t • w t) := by
  calc
    x b-x a = ∑ t ∈ Ico a b, (x (t+1)-x t) := (sum_Ico_sub x hab).symm
    _ = ∑ t ∈ Ico a b, γ t • (s t+w t) := by
      apply sum_congr rfl
      intro t ht
      rw [hx]
      abel
    _ = _ := by simp only [smul_add,sum_add_distrib]

theorem drift_sum_bound {s : ℕ → E} {γ : ℕ → ℝ} {a b : ℕ} {C η : ℝ}
    (hγ : ∀ t ∈ Ico a b, 0 ≤ γ t) (hC : 0 ≤ C)
    (hs : ∀ t ∈ Ico a b, ‖s t‖ ≤ C) (hbudget : (∑ t ∈ Ico a b, γ t) ≤ η) :
    ‖∑ t ∈ Ico a b, γ t • s t‖ ≤ η*C := by
  calc
    _ ≤ ∑ t ∈ Ico a b, ‖γ t • s t‖ := norm_sum_le _ _
    _ = ∑ t ∈ Ico a b, γ t * ‖s t‖ := by
      apply sum_congr rfl
      intro t ht
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hγ t ht)]
    _ ≤ ∑ t ∈ Ico a b, γ t*C := sum_le_sum (fun t ht => mul_le_mul_of_nonneg_left (hs t ht) (hγ t ht))
    _ = (∑ t ∈ Ico a b, γ t)*C := (sum_mul _ _ _).symm
    _ ≤ η*C := mul_le_mul_of_nonneg_right hbudget hC

theorem scaled_vector_sum {γ G : ℕ → ℝ} {w : ℕ → E} {a b : ℕ} {H : ℝ}
    (hH : H ≠ 0) (hG : ∀ t ∈ Ico a b, G t = H) :
    (∑ t ∈ Ico a b, γ t • w t) = H • (∑ t ∈ Ico a b, (γ t/G t) • w t) := by
  rw [smul_sum]
  apply sum_congr rfl
  intro t ht
  rw [hG t ht,smul_smul]
  congr 1
  field_simp

theorem scaled_real_sum {a G : ℕ → ℝ} {i j : ℕ} {H : ℝ}
    (hH : H ≠ 0) (hG : ∀ t ∈ Ico i j, G t = H) :
    (∑ t ∈ Ico i j,a t) = H^2 * (∑ t ∈ Ico i j,a t/(G t)^2) := by
  rw [mul_sum]
  apply sum_congr rfl
  intro t ht
  rw [hG t ht]
  field_simp

end GradErrors.Stochastic.Proof
-- End FiniteMotion

-- Begin BlockMotion

open Finset InnerProductSpace
namespace GradErrors.Stochastic.Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem interval_prefix_budget {δ η : ℝ} {γ h G : ℕ → ℝ} {a b t : ℕ}
    (hI : ActiveInterval δ η γ h G a b) (hγ : ∀ i, 0 ≤ γ i) (htb : t ≤ b) :
    (∑ i ∈ Ico a t, γ i) ≤ η := by
  apply le_trans _ hI.budget
  exact sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico le_rfl htb) (fun i _ _ => hγ i)

theorem active_interval_motion {δ η c₂ ε : ℝ} {γ G : ℕ → ℝ}
    {x s w g : ℕ → E} {a b t : ℕ}
    (hI : ActiveInterval δ η γ (fun i => ‖g i‖) G a b) (hδ : 0 < δ)
    (hγ : ∀ i, 0 ≤ γ i) (hc₂ : 0 ≤ c₂)
    (hx : ∀ i, x (i+1) = x i + γ i • (s i+w i))
    (hs : ∀ i, ‖s i‖ ≤ c₂*(1+‖g i‖)) (hat : a ≤ t) (htb : t ≤ b)
    (htail : ‖∑ i ∈ Ico a t, (γ i/G i) • w i‖ ≤ ε) :
    ‖x t-x a‖ ≤ η*c₂*(1+2*‖g a‖)+‖g a‖*ε := by
  have hH : 0 < ‖g a‖ := lt_of_lt_of_le hδ hI.height_ge
  have hsub : Ico a t ⊆ Ico a b := Ico_subset_Ico le_rfl htb
  have hd := drift_sum_bound (s:=s) (fun i _ => hγ i)
    (mul_nonneg hc₂ (by positivity : 0 ≤ 1+2*‖g a‖))
    (fun i hi => (hs i).trans (mul_le_mul_of_nonneg_left
      (by linarith [hI.upper i (hsub hi)]) hc₂)) (interval_prefix_budget hI hγ htb)
  have hw : ‖∑ i ∈ Ico a t, γ i • w i‖ ≤ ‖g a‖*ε := by
    rw [scaled_vector_sum (ne_of_gt hH) (fun i hi => hI.scale_eq i (hsub hi)),norm_smul,
      Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_left htail (norm_nonneg _)
  rw [motion_sum hx hat]
  have hh := norm_add_le (∑ i ∈ Ico a t,γ i • s i) (∑ i ∈ Ico a t,γ i • w i)
  nlinarith

end GradErrors.Stochastic.Proof
-- End BlockMotion

-- Begin BlockEndpoint

open Finset
namespace GradErrors.Stochastic.Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem active_motion_small {δ η c₂ ε ℓ : ℝ} {γ G : ℕ → ℝ}
    {x s w g : ℕ → E} {a b t : ℕ}
    (hI : ActiveInterval δ η γ (fun i => ‖g i‖) G a b) (hδ : 0 < δ)
    (hγ : ∀ i, 0 ≤ γ i) (hc₂ : 0 ≤ c₂) (hη : 0 ≤ η) (hℓ : 0 < ℓ)
    (hchoice : ℓ*η*(c₂*(1/δ+2)+1) ≤ 1/4) (hε : ε ≤ η)
    (hx : ∀ i, x (i+1) = x i + γ i • (s i+w i))
    (hs : ∀ i, ‖s i‖ ≤ c₂*(1+‖g i‖)) (hat : a ≤ t) (htb : t ≤ b)
    (htail : ‖∑ i ∈ Ico a t, (γ i/G i) • w i‖ ≤ ε) :
    ℓ*‖x t-x a‖ ≤ ‖g a‖/4 := by
  have hm := active_interval_motion hI hδ hγ hc₂ hx hs hat htb htail
  have hH := hI.height_ge
  have hd : 1 ≤ ‖g a‖ / δ := (le_div_iff₀ hδ).2 (by simpa using hH)
  have hd' : 1+2*‖g a‖ ≤ ‖g a‖*(1/δ+2) := by
    simp only [div_eq_mul_inv] at hd ⊢
    nlinarith
  have h1 := mul_le_mul_of_nonneg_left hd' (mul_nonneg hη hc₂)
  have h2 := mul_le_mul_of_nonneg_left hε (norm_nonneg (g a))
  have h3 := mul_le_mul_of_nonneg_left hchoice (norm_nonneg (g a))
  have h4 := mul_le_mul_of_nonneg_left hm hℓ.le
  nlinarith

theorem active_endpoint_budget {δ η c₂ ε ℓ : ℝ} {γ G : ℕ → ℝ}
    {x s w g : ℕ → E} {a b : ℕ}
    (hI : ActiveInterval δ η γ (fun i => ‖g i‖) G a b) (hδ : 0 < δ)
    (hγ : ∀ i, 0 ≤ γ i) (hc₂ : 0 ≤ c₂) (hη : 0 ≤ η) (hℓ : 0 < ℓ)
    (hchoice : ℓ*η*(c₂*(1/δ+2)+1) ≤ 1/4) (hε : ε ≤ η)
    (hx : ∀ i, x (i+1) = x i + γ i • (s i+w i))
    (hs : ∀ i, ‖s i‖ ≤ c₂*(1+‖g i‖))
    (hg : ‖g b-g a‖ ≤ ℓ*‖x b-x a‖) (hstep : γ b ≤ η/2)
    (htail : ‖∑ i ∈ Ico a b, (γ i/G i) • w i‖ ≤ ε) :
    ‖g b‖ ≤ 3*‖g a‖/2 ∧ η/2 ≤ ∑ i ∈ Ico a b,γ i := by
  have hm := active_motion_small hI hδ hγ hc₂ hη hℓ hchoice hε hx hs hI.nonempty.le le_rfl htail
  have hn := norm_sub_norm_le (g b) (g a)
  have hn' := norm_sub_norm_le (g a) (g b)
  rw [norm_sub_rev (g a) (g b)] at hn'
  have hlo : ‖g a‖/2 ≤ ‖g b‖ := by linarith [norm_nonneg (g a)]
  have hup : ‖g b‖ ≤ 2*‖g a‖ := by linarith [norm_nonneg (g a)]
  have hb := hI.maximal hlo hup
  constructor <;> linarith [norm_nonneg (g a)]

end GradErrors.Stochastic.Proof
-- End BlockEndpoint

-- Begin SeriesTails

open Finset Filter Topology
namespace GradErrors.Stochastic.Proof

variable {E : Type*} [NormedAddCommGroup E]

theorem SeriesConverges.interval_tail {a : ℕ → E} (h : SeriesConverges a)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ m ≥ N, ∀ n ≥ m, ‖∑ i ∈ Ico m n, a i‖ ≤ ε := by
  obtain ⟨l,hl⟩ := h
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hl (ε/2) (by linarith)
  refine ⟨N,fun m hm n hn => ?_⟩
  have h1 := hN n (hm.trans hn)
  have h2 := hN m hm
  have ht := dist_triangle_right (∑ i ∈ range n, a i) (∑ i ∈ range m, a i) l
  rw [dist_eq_norm,← sum_Ico_eq_sub a hn] at ht
  linarith

theorem SeriesConverges.drop {a : ℕ → E} (h : SeriesConverges a) (N : ℕ) :
    SeriesConverges (fun t => a (N+t)) := by
  obtain ⟨l,hl⟩ := h
  refine ⟨l-(∑ t ∈ range N,a t),?_⟩
  have hh := (hl.comp (tendsto_add_atTop_nat N)).sub_const (∑ t ∈ range N,a t)
  convert hh using 1
  funext n
  dsimp only [Function.comp_apply]
  rw [Nat.add_comm n N,← sum_Ico_eq_sub a (Nat.le_add_right N n),sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]

omit [NormedAddCommGroup E] in
 theorem seriesConverges_of_summable {a : ℕ → ℝ} (h : Summable a) : SeriesConverges a :=
  ⟨∑' t,a t,h.hasSum.tendsto_sum_nat⟩

theorem SeriesConverges.add {a b : ℕ → E} (ha : SeriesConverges a) (hb : SeriesConverges b) :
    SeriesConverges (fun t => a t+b t) := by
  obtain ⟨la,ha⟩ := ha
  obtain ⟨lb,hb⟩ := hb
  exact ⟨la+lb,by simpa only [sum_add_distrib] using ha.add hb⟩

theorem SeriesConverges.const_mul {a : ℕ → ℝ} (ha : SeriesConverges a) (c : ℝ) :
    SeriesConverges (fun t => c*a t) := by
  obtain ⟨l,hl⟩ := ha
  exact ⟨c*l,by simpa only [mul_sum] using hl.const_mul c⟩

end GradErrors.Stochastic.Proof
-- End SeriesTails

-- Begin IntervalTails

open Finset InnerProductSpace
namespace GradErrors.Stochastic.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure IntervalTails (γ : ℕ → ℝ) (g w : ℕ → E) (G : ℕ → ℝ) (ε : ℝ) (N : ℕ) : Prop where
  vector : ∀ a ≥ N, ∀ b ≥ a, ‖∑ i ∈ Ico a b,(γ i/G i) • w i‖ ≤ ε
  inner : ∀ a ≥ N, ∀ b ≥ a, (∑ i ∈ Ico a b,γ i*⟪g i,w i⟫_ℝ/(G i)^2) ≤ ε
  square : ∀ a ≥ N, ∀ b ≥ a, (∑ i ∈ Ico a b,(γ i)^2*‖w i‖^2/(G i)^2) ≤ ε
  step : ∀ a ≥ N, ∀ b ≥ a, (∑ i ∈ Ico a b,(γ i)^2) ≤ ε

theorem NoiseLimits.intervalTails {γ G χ : ℕ → ℝ} {g w : ℕ → E}
    (h : NoiseLimits γ g w G χ) (hγ : Summable (fun i => (γ i)^2))
    {ε : ℝ} (hε : 0 < ε) : ∃ N, IntervalTails γ g w G ε N := by
  obtain ⟨N₁,h₁⟩ := h.scaledVector.interval_tail hε
  obtain ⟨N₂,h₂⟩ := h.scaledInner.interval_tail hε
  obtain ⟨N₃,h₃⟩ := h.scaledSquare.interval_tail hε
  obtain ⟨N₄,h₄⟩ := (seriesConverges_of_summable hγ).interval_tail hε
  refine ⟨N₁+N₂+N₃+N₄,?_,?_,?_,?_⟩
  · intro a ha b hb
    exact h₁ a (by omega) b hb
  · intro a ha b hb
    exact (le_abs_self _).trans (h₂ a (by omega) b hb)
  · intro a ha b hb
    exact (le_abs_self _).trans (h₃ a (by omega) b hb)
  · intro a ha b hb
    exact (le_abs_self _).trans (h₄ a (by omega) b hb)

end GradErrors.Stochastic.Proof
-- End IntervalTails

-- Begin IntervalDescent

open Finset
namespace GradErrors.Stochastic.Proof

theorem sum_descent {y z : ℕ → ℝ} (h : ∀ i,y (i+1) ≤ y i+z i) {a b : ℕ} (hab : a≤b) :
    y b ≤ y a+∑ i ∈ Ico a b,z i := by
  have hh := sum_le_sum (s:=Ico a b) (fun i _ => (show y (i+1)-y i ≤ z i by linarith [h i]))
  rw [sum_Ico_sub] at hh
  · linarith
  · exact hab

theorem active_gradient_sum_lower {δ η : ℝ} {γ h G : ℕ → ℝ} {a b : ℕ}
    (hI : ActiveInterval δ η γ h G a b) (hδ : 0≤δ) (hγ : ∀ i,0≤γ i) :
    (h a)^2/4*(∑ i ∈ Ico a b,γ i) ≤ ∑ i ∈ Ico a b,γ i*(h i)^2 := by
  rw [mul_sum]
  apply sum_le_sum
  intro i hi
  have hh := hI.lower i hi
  have ha : 0≤h a := hδ.trans hI.height_ge
  have hs : (h a)^2/4 ≤ (h i)^2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hs (hγ i)]

theorem active_error_sum_upper {δ η D ℓ ε : ℝ} {γ h G u v : ℕ → ℝ} {a b t : ℕ}
    (hI : ActiveInterval δ η γ h G a b) (hδ : 0<δ)
    (hD : 0≤D) (hℓ : 0≤ℓ) (hε : 0≤ε) (ht : t≤b)
    (hu : (∑ i ∈ Ico a t,u i/(G i)^2)≤ε)
    (hv : (∑ i ∈ Ico a t,v i/(G i)^2)≤ε)
    (hstep : (∑ i ∈ Ico a t,(γ i)^2)≤ε) :
    (∑ i ∈ Ico a t,(u i+D*(γ i)^2+ℓ*v i)) ≤
      (ε*(1+ℓ+D/δ^2))*(h a)^2 := by
  have hH : 0<h a := hδ.trans_le hI.height_ge
  have heq : ∀ i∈Ico a t,G i=h a := fun i hi => hI.scale_eq i (Ico_subset_Ico le_rfl ht hi)
  have huu : (∑ i ∈ Ico a t,u i) ≤ (h a)^2*ε := by
    rw [scaled_real_sum (ne_of_gt hH) heq]
    exact mul_le_mul_of_nonneg_left hu (sq_nonneg _)
  have hvv : (∑ i ∈ Ico a t,v i) ≤ (h a)^2*ε := by
    rw [scaled_real_sum (ne_of_gt hH) heq]
    exact mul_le_mul_of_nonneg_left hv (sq_nonneg _)
  have hratio : 1≤(h a)^2/δ^2 := (le_div_iff₀ (sq_pos_of_pos hδ)).2 (by nlinarith [hI.height_ge])
  have hd := mul_le_mul_of_nonneg_left hstep hD
  have hd' := mul_le_mul_of_nonneg_left hratio (mul_nonneg hD hε)
  have hl := mul_le_mul_of_nonneg_left hvv hℓ
  simp only [sum_add_distrib,←mul_sum]
  simp only [div_eq_mul_inv] at hd' ⊢
  nlinarith

end GradErrors.Stochastic.Proof
-- End IntervalDescent

-- Begin ActiveDescent

open Finset
namespace GradErrors.Stochastic.Proof

theorem active_descent_estimate {δ η c D ℓ ε : ℝ} {γ h G u v y : ℕ → ℝ} {a b t : ℕ}
    (hI : ActiveInterval δ η γ h G a b) (hδ : 0<δ)
    (_hc : 0≤c) (hD : 0≤D) (hℓ : 0≤ℓ) (hε : 0≤ε)
    (_hγ : ∀ i,0≤γ i) (hat : a≤t) (ht : t≤b)
    (hy : ∀ i,y (i+1)≤y i-c*γ i*(h i)^2+u i+D*(γ i)^2+ℓ*v i)
    (hu : (∑ i ∈ Ico a t,u i/(G i)^2)≤ε)
    (hv : (∑ i ∈ Ico a t,v i/(G i)^2)≤ε)
    (hstep : (∑ i ∈ Ico a t,(γ i)^2)≤ε) :
    y t≤y a-c*(∑ i ∈ Ico a t,γ i*(h i)^2)+(ε*(1+ℓ+D/δ^2))*(h a)^2 := by
  have hd := sum_descent (y:=y)
    (z:=fun i => -c*(γ i*(h i)^2)+(u i+D*(γ i)^2+ℓ*v i))
    (fun i => by linarith [hy i]) hat
  have he := active_error_sum_upper hI hδ hD hℓ hε ht hu hv hstep
  simp only [sum_add_distrib,←mul_sum] at hd he
  linarith

theorem active_excursion {δ η c D ℓ ε : ℝ} {γ h G u v y : ℕ → ℝ} {a b t : ℕ}
    (hI : ActiveInterval δ η γ h G a b) (hδ : 0<δ)
    (hc : 0≤c) (hD : 0≤D) (hℓ : 0≤ℓ) (hε : 0≤ε)
    (hγ : ∀ i,0≤γ i) (hat : a≤t) (ht : t≤b)
    (hy : ∀ i,y (i+1)≤y i-c*γ i*(h i)^2+u i+D*(γ i)^2+ℓ*v i)
    (hu : (∑ i ∈ Ico a t,u i/(G i)^2)≤ε)
    (hv : (∑ i ∈ Ico a t,v i/(G i)^2)≤ε)
    (hstep : (∑ i ∈ Ico a t,(γ i)^2)≤ε) :
    y t≤y a+(ε*(1+ℓ+D/δ^2))*(h a)^2 := by
  have hd := active_descent_estimate hI hδ hc hD hℓ hε hγ hat ht hy hu hv hstep
  have hn : 0≤c*(∑ i ∈ Ico a t,γ i*(h i)^2) :=
    mul_nonneg hc (sum_nonneg fun i _ => mul_nonneg (hγ i) (sq_nonneg _))
  linarith

theorem active_full_drop {δ η c D ℓ ε κ : ℝ} {γ h G u v y : ℕ → ℝ} {a b : ℕ}
    (hI : ActiveInterval δ η γ h G a b) (hδ : 0<δ)
    (hc : 0≤c) (hD : 0≤D) (hℓ : 0≤ℓ) (hε : 0≤ε)
    (hγ : ∀ i,0≤γ i) (hbudget : η/2≤∑ i∈Ico a b,γ i)
    (hk : ε*(1+ℓ+D/δ^2)≤c*η/8-κ)
    (hy : ∀ i,y (i+1)≤y i-c*γ i*(h i)^2+u i+D*(γ i)^2+ℓ*v i)
    (hu : (∑ i ∈ Ico a b,u i/(G i)^2)≤ε)
    (hv : (∑ i ∈ Ico a b,v i/(G i)^2)≤ε)
    (hstep : (∑ i ∈ Ico a b,(γ i)^2)≤ε) :
    y b≤y a-κ*(h a)^2 := by
  have hd := active_descent_estimate hI hδ hc hD hℓ hε hγ hI.nonempty.le le_rfl hy hu hv hstep
  have hg := active_gradient_sum_lower hI hδ.le hγ
  have hg' := mul_le_mul_of_nonneg_left hg hc
  have hb := mul_le_mul_of_nonneg_left hbudget (mul_nonneg hc (sq_nonneg (h a)))
  have hk' := mul_le_mul_of_nonneg_right hk (sq_nonneg (h a))
  nlinarith

end GradErrors.Stochastic.Proof
-- End ActiveDescent

-- Begin SmallErrorSeries

open Finset InnerProductSpace
namespace GradErrors.Stochastic.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def smallError (γ χ : ℕ → ℝ) (g w : ℕ → E) (D ℓ : ℝ) (t : ℕ) : ℝ :=
  χ t*γ t*⟪g t,w t⟫_ℝ+D*(χ t*(γ t)^2)+ℓ*((γ t)^2*χ t*‖w t‖^2)

theorem smallError_converges {γ G χ : ℕ → ℝ} {g w : ℕ → E}
    (h : NoiseLimits γ g w G χ) (hγ : Summable (fun i => (γ i)^2))
    (hχ : ∀ i,χ i=0 ∨ χ i=1) (D ℓ : ℝ) : SeriesConverges (smallError γ χ g w D ℓ) := by
  have hs : Summable (fun i => χ i*(γ i)^2) := by
    apply Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hγ
    · rcases hχ i with hi|hi <;> simp [hi,sq_nonneg]
    · rcases hχ i with hi|hi <;> simp [hi,sq_nonneg]
  exact (h.smallInner.add ((seriesConverges_of_summable hs).const_mul D)).add
    (h.smallSquare.const_mul ℓ)

end GradErrors.Stochastic.Proof
-- End SmallErrorSeries

-- Begin BlockSkeleton

open Finset Filter Topology
namespace GradErrors.Stochastic.Proof
variable {δ η : ℝ} {γ g : ℕ → ℝ}

noncomputable def blockSkeleton (hδ : 0 ≤ δ) (hγ : ∀ t, γ t ≤ η)
    (hsum : Tendsto (fun n => ∑ t ∈ range n, γ t) atTop atTop) : ℕ → ℕ
  | 0 => 0
  | k+1 => blockStop (g:=g) hδ hγ hsum (blockSkeleton hδ hγ hsum k)

theorem skeleton_strictMono (hδ : 0 ≤ δ) (hγ : ∀ t, γ t ≤ η)
    (hsum : Tendsto (fun n => ∑ t ∈ range n, γ t) atTop atTop) :
    StrictMono (blockSkeleton (g:=g) hδ hγ hsum) := by
  apply strictMono_nat_of_lt_succ
  intro k
  exact blockStop_gt hδ hγ hsum _

theorem skeleton_tendsto (hδ : 0 ≤ δ) (hγ : ∀ t, γ t ≤ η)
    (hsum : Tendsto (fun n => ∑ t ∈ range n, γ t) atTop atTop) :
    Tendsto (blockSkeleton (g:=g) hδ hγ hsum) atTop atTop :=
  (skeleton_strictMono hδ hγ hsum).tendsto_atTop

theorem skeleton_start (hδ : 0 ≤ δ) (hγ : ∀ t, γ t ≤ η)
    (hsum : Tendsto (fun n => ∑ t ∈ range n, γ t) atTop atTop) (k : ℕ) :
    (blockAt δ η γ g (blockSkeleton (g:=g) hδ hγ hsum k)).start = blockSkeleton (g:=g) hδ hγ hsum k := by
  classical
  induction k with
  | zero =>
    simp only [blockSkeleton,blockAt_zero,blockStep,CanContinue,idleState]
    split_ifs <;> rfl
  | succ k ih => exact blockStop_is_start hδ hγ hsum ih

theorem exists_skeleton_after (hδ : 0 ≤ δ) (hγ : ∀ t, γ t ≤ η)
    (hsum : Tendsto (fun n => ∑ t ∈ range n, γ t) atTop atTop) (t : ℕ) :
    ∃ k, t < blockSkeleton (g:=g) hδ hγ hsum k := by
  exact ⟨t+1,lt_of_lt_of_le (Nat.lt_succ_self t) ((skeleton_strictMono hδ hγ hsum).id_le _)⟩

noncomputable def chunkIndex (hδ : 0 ≤ δ) (hγ : ∀ t, γ t ≤ η)
    (hsum : Tendsto (fun n => ∑ t ∈ range n, γ t) atTop atTop) (t : ℕ) : ℕ :=
  Nat.find (exists_skeleton_after (g:=g) hδ hγ hsum t) - 1

theorem chunkIndex_bounds (hδ : 0 ≤ δ) (hγ : ∀ t, γ t ≤ η)
    (hsum : Tendsto (fun n => ∑ t ∈ range n, γ t) atTop atTop) (t : ℕ) :
    blockSkeleton (g:=g) hδ hγ hsum (chunkIndex (g:=g) hδ hγ hsum t) ≤ t ∧
    t < blockSkeleton (g:=g) hδ hγ hsum (chunkIndex (g:=g) hδ hγ hsum t+1) := by
  let ex := exists_skeleton_after (g:=g) hδ hγ hsum t
  have hpos : 0 < Nat.find ex := by
    by_contra hn
    have he : Nat.find ex = 0 := by omega
    have hh := Nat.find_spec ex
    rw [he] at hh
    change t < 0 at hh
    omega
  constructor
  · apply Nat.le_of_not_gt
    exact Nat.find_min ex (by omega : Nat.find ex-1 < Nat.find ex)
  · change t < blockSkeleton (g:=g) hδ hγ hsum (Nat.find ex-1+1)
    rw [Nat.sub_add_cancel hpos]
    exact Nat.find_spec ex

theorem chunkIndex_tendsto (hδ : 0 ≤ δ) (hγ : ∀ t, γ t ≤ η)
    (hsum : Tendsto (fun n => ∑ t ∈ range n, γ t) atTop atTop) :
    Tendsto (chunkIndex (g:=g) hδ hγ hsum) atTop atTop := by
  apply tendsto_atTop.2
  intro k
  filter_upwards [eventually_ge_atTop (blockSkeleton hδ hγ hsum k)] with t ht
  have hh := (chunkIndex_bounds (g:=g) hδ hγ hsum t).2
  have hlt : k < chunkIndex (g:=g) hδ hγ hsum t+1 :=
    (skeleton_strictMono hδ hγ hsum).lt_iff_lt.mp (lt_of_le_of_lt ht hh)
  omega

end GradErrors.Stochastic.Proof
-- End BlockSkeleton

-- Begin SkeletonError

open Finset Filter Topology
namespace GradErrors.Stochastic.Proof
variable {δ η : ℝ} {γ g : ℕ → ℝ}

theorem sum_chunk_intervals {q : ℕ → ℕ} (hq : Monotone q) (hq0 : q 0=0) (z : ℕ → ℝ) (k : ℕ) :
    (∑ j ∈ range k,∑ i∈Ico (q j) (q (j+1)),z i)=∑ i∈range (q k),z i := by
  induction k with
  | zero => simp [hq0]
  | succ k ih =>
    rw [sum_range_succ,ih,sum_Ico_eq_sub z (hq (by omega))]
    ring

theorem seriesConverges_chunks {q : ℕ → ℕ} (hq : StrictMono q) (hq0 : q 0=0)
    {z : ℕ → ℝ} (hz : SeriesConverges z) :
    SeriesConverges (fun k => ∑ i∈Ico (q k) (q (k+1)),z i) := by
  obtain ⟨l,hl⟩ := hz
  exact ⟨l,by simpa only [sum_chunk_intervals hq.monotone hq0,Function.comp_def] using hl.comp hq.tendsto_atTop⟩

theorem block_small_interval {a b : ℕ} (_ha : (blockAt δ η γ g a).active=true)
    (hin : ∀t∈Ico a b,(blockAt δ η γ g t).active=true)
    {z : ℕ → ℝ} (hz : ∀t,smallAt δ η γ g t=0→z t=0) :
    (∑ t∈Ico a b,z t)=0 := by
  apply sum_eq_zero
  intro t ht
  apply hz
  simp [smallAt,hin t ht]

end GradErrors.Stochastic.Proof
-- End SkeletonError

-- Begin SmallMotion

open Finset
namespace GradErrors.Stochastic.Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem small_step_growth {δ η c₂ ε ℓ : ℝ} {γ G : ℕ → ℝ}
    {x s w g : ℕ → E} {a : ℕ} (hδ : 0<δ) (hη : 0≤η)
    (hc₂ : 0≤c₂) (hℓ : 0<ℓ) (hchoice : ℓ*η*(c₂*(1/δ+2)+1)≤1/4)
    (hγ : 0≤γ a) (hstep : γ a≤η) (hε : ε≤η)
    (hx : x (a+1)=x a+γ a • (s a+w a))
    (hs : ‖s a‖≤c₂*(1+‖g a‖)) (ha : ‖g a‖<δ) (hG : G a=δ)
    (hg : ‖g (a+1)-g a‖≤ℓ*‖x (a+1)-x a‖)
    (htail : ‖(γ a/G a) • w a‖≤ε) : ‖g (a+1)‖≤3*δ/2 := by
  have hw : ‖γ a • w a‖≤δ*ε := by
    have he : γ a • w a=δ • ((γ a/G a) • w a) := by
      rw [hG,smul_smul]
      congr 1
      field_simp
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos hδ]
    exact mul_le_mul_of_nonneg_left htail hδ.le
  have hd : ‖γ a • s a‖≤η*c₂*(1+δ) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hγ]
    have h1 := mul_le_mul_of_nonneg_left hs hγ
    have h2 := mul_le_mul_of_nonneg_left (by linarith : 1+‖g a‖≤1+δ) hc₂
    have h3 := mul_le_mul_of_nonneg_left h2 hγ
    have h4 := mul_le_mul_of_nonneg_right hstep (mul_nonneg hc₂ (by linarith : 0≤1+δ))
    nlinarith
  have hm : ‖x (a+1)-x a‖≤η*c₂*(1+δ)+δ*ε := by
    rw [hx,add_sub_cancel_left,smul_add]
    exact (norm_add_le _ _).trans (add_le_add hd hw)
  have he := mul_le_mul_of_nonneg_left hε hδ.le
  have hc := mul_le_mul_of_nonneg_left hchoice hδ.le
  have hc' : ℓ*(η*c₂*(1+2*δ)+δ*η)≤δ/4 := by
    calc
      _ = δ*(ℓ*η*(c₂*(1/δ+2)+1)) := by field_simp
      _ ≤ δ*(1/4) := hc
      _ = δ/4 := by ring
  have hn := norm_sub_norm_le (g (a+1)) (g a)
  have hh := mul_le_mul_of_nonneg_left hm hℓ.le
  have hp : 0≤ℓ*η*c₂*δ := by positivity
  nlinarith

end GradErrors.Stochastic.Proof
-- End SmallMotion

-- Begin ChunkTransfer

open Filter Topology
namespace GradErrors.Stochastic.Proof

/-- Quantitative control for transferring a stopped sequence back to every time. -/
structure ChunkControl (y H : ℕ → ℝ) (q : ℕ → ℕ) (active : ℕ → Bool)
    (δ B K : ℝ) (J : ℕ) : Prop where
  idle : ∀ k,active k=false→q (k+1)=q k+1
  excursion : ∀ k≥J,active k=true→∀t,q k≤t→t<q (k+1)→y t≤y (q k)+B*(H k)^2
  drop : ∀ k≥J,active k=true→y (q (k+1))≤y (q k)-K*(H k)^2
  growth : ∀ k≥J,active k=true→0≤H (k+1) ∧ H (k+1)≤3*H k/2
  idle_growth : ∀ k≥J,active k=false→0≤H (k+1) ∧ H (k+1)≤3*δ/2
  height : ∀ k,0≤H k

theorem chunk_upper_bound {y H : ℕ → ℝ} {q r : ℕ → ℕ} {active : ℕ → Bool}
    {δ B K : ℝ} {J t : ℕ} (h : ChunkControl y H q active δ B K J)
    (hB : 0≤B) (hδ : 0≤δ) (hBK : 9*B/4≤K)
    (hr : q (r t)≤t ∧ t<q (r t+1)) (hk : J+1≤r t) :
    y t ≤ max (y (q (r t))) (y (q (r t-1))) + B*(3*δ/2)^2 := by
  have hj : J≤r t := by omega
  have hp : J≤r t-1 := by omega
  have he : r t-1+1=r t := by omega
  have hC : 0≤B*(3*δ/2)^2 := mul_nonneg hB (sq_nonneg _)
  cases ha : active (r t)
  · have ht : t=q (r t) := by have hh:=h.idle _ ha; omega
    calc
      y t = y (q (r t)) := congrArg y ht
      _ ≤ max (y (q (r t))) (y (q (r t-1))) + B*(3*δ/2)^2 :=
        (le_max_left _ _).trans (le_add_of_nonneg_right hC)
  · have hh := h.excursion _ hj ha t hr.1 hr.2
    cases hb : active (r t-1)
    · have hg := h.idle_growth _ hp hb
      rw [he] at hg
      have hs : (H (r t))^2≤(3*δ/2)^2 := by nlinarith
      have hm := mul_le_mul_of_nonneg_left hs hB
      have hl := le_max_left (y (q (r t))) (y (q (r t-1)))
      linarith
    · have hg := h.growth _ hp hb
      have hd := h.drop _ hp hb
      rw [he] at hg hd
      have hs : (H (r t))^2≤9/4*(H (r t-1))^2 := by
        nlinarith [h.height (r t-1)]
      have hm := mul_le_mul_of_nonneg_left hs hB
      have hm' := mul_le_mul_of_nonneg_right hBK (sq_nonneg (H (r t-1)))
      have hl := le_max_right (y (q (r t))) (y (q (r t-1)))
      nlinarith

theorem chunk_tendsto_atBot {y H : ℕ → ℝ} {q r : ℕ → ℕ} {active : ℕ → Bool}
    {δ B K : ℝ} {J : ℕ} (h : ChunkControl y H q active δ B K J)
    (hB : 0≤B) (hδ : 0≤δ) (hBK : 9*B/4≤K)
    (hr : ∀t,q (r t)≤t ∧ t<q (r t+1)) (hrt : Tendsto r atTop atTop)
    (hy : Tendsto (fun k=>y (q k)) atTop atBot) : Tendsto y atTop atBot := by
  apply tendsto_atBot.mpr
  intro c
  have hy1 := (tendsto_atBot.mp (hy.comp hrt)) (c-B*(3*δ/2)^2)
  have hrp : Tendsto (fun t=>r t-1) atTop atTop := (tendsto_sub_atTop_nat 1).comp hrt
  have hy2 := (tendsto_atBot.mp (hy.comp hrp)) (c-B*(3*δ/2)^2)
  filter_upwards [hy1,hy2,hrt.eventually (eventually_ge_atTop (J+1))] with t ht1 ht2 ht3
  have hh := chunk_upper_bound h hB hδ hBK (hr t) ht3
  have hm : max (y (q (r t))) (y (q (r t-1)))≤c-B*(3*δ/2)^2 := max_le ht1 ht2
  linarith

theorem chunk_finite_transfer {y : ℕ → ℝ} {q r : ℕ → ℕ} {active : ℕ → Bool} {l : ℝ}
    (hidle : ∀ k,active k=false→q (k+1)=q k+1)
    (hr : ∀t,q (r t)≤t ∧ t<q (r t+1)) (hrt : Tendsto r atTop atTop)
    (ha : ∀ᶠ k in atTop,active k=false) (hy : Tendsto (fun k=>y (q k)) atTop (𝓝 l)) :
    Tendsto y atTop (𝓝 l) := by
  apply (hy.comp hrt).congr'
  filter_upwards [hrt.eventually ha] with t ht
  have hh := hidle _ ht
  have hb := hr t
  have he : q (r t)=t := by omega
  simp only [Function.comp_apply,he]

end GradErrors.Stochastic.Proof
-- End ChunkTransfer

-- Begin PathData

open Finset Filter Topology InnerProductSpace
namespace GradErrors.Stochastic.Proof

structure PathData (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  γ : ℕ→ℝ
  x : ℕ→E
  s : ℕ→E
  w : ℕ→E
  g : ℕ→E
  y : ℕ→ℝ
  δ : ℝ
  η : ℝ
  c : ℝ
  c₂ : ℝ
  ℓ : ℝ
  D : ℝ
  ε : ℝ
  B : ℝ
  K : ℝ
  N : ℕ
  δ_pos : 0<δ
  η_pos : 0<η
  c_pos : 0<c
  c₂_nonneg : 0≤c₂
  ℓ_pos : 0<ℓ
  D_nonneg : 0≤D
  ε_pos : 0<ε
  ε_le : ε≤η
  B_nonneg : 0≤B
  K_pos : 0<K
  coefficient : ε*(1+ℓ+D/δ^2)≤B
  drop_coefficient : B≤c*η/8-K
  absorption : 9*B/4≤K
  choice : ℓ*η*(c₂*(1/δ+2)+1)≤1/4
  γ_pos : ∀i,0<γ i
  γ_le : ∀i,γ i≤η/2
  γ_sum : Tendsto (fun n=>∑i∈range n,γ i) atTop atTop
  γ_square : Summable (fun i=>(γ i)^2)
  recurrence : ∀i,x (i+1)=x i+γ i • (s i+w i)
  drift : ∀i,‖s i‖≤c₂*(1+‖g i‖)
  gradient : ∀a b,‖g b-g a‖≤ℓ*‖x b-x a‖
  descent : ∀i,y (i+1)≤y i-c*γ i*‖g i‖^2+γ i*⟪g i,w i⟫_ℝ+D*(γ i)^2+ℓ*((γ i)^2*‖w i‖^2)
  tails : IntervalTails γ g w (scaleAt δ η γ (fun i=>‖g i‖)) ε N
  noise : NoiseLimits γ g w (scaleAt δ η γ (fun i=>‖g i‖)) (smallAt δ η γ (fun i=>‖g i‖))

namespace PathData
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (p : PathData E)

theorem γ_le_eta (i : ℕ) : p.γ i≤p.η := (p.γ_le i).trans (by linarith [p.η_pos])
noncomputable def q : ℕ→ℕ := blockSkeleton (g:=fun i=>‖p.g i‖) p.δ_pos.le p.γ_le_eta p.γ_sum
noncomputable def r : ℕ→ℕ := chunkIndex (g:=fun i=>‖p.g i‖) p.δ_pos.le p.γ_le_eta p.γ_sum
noncomputable def active (k : ℕ) : Bool := (blockAt p.δ p.η p.γ (fun i=>‖p.g i‖) (p.q k)).active
noncomputable def H (k : ℕ) : ℝ := ‖p.g (p.q k)‖
noncomputable def z : ℕ→ℝ := smallError p.γ (smallAt p.δ p.η p.γ (fun i=>‖p.g i‖)) p.g p.w p.D p.ℓ
noncomputable def Z (k : ℕ) : ℝ := ∑i∈Ico (p.q k) (p.q (k+1)),p.z i

theorem q_strict : StrictMono p.q := skeleton_strictMono _ _ _
theorem q_zero : p.q 0=0 := rfl
theorem r_bounds (t : ℕ) : p.q (p.r t)≤t ∧ t<p.q (p.r t+1) := chunkIndex_bounds _ _ _ t
theorem r_tendsto : Tendsto p.r atTop atTop := chunkIndex_tendsto _ _ _
theorem q_start (k : ℕ) : (blockAt p.δ p.η p.γ (fun i=>‖p.g i‖) (p.q k)).start=p.q k := skeleton_start _ _ _ k

theorem interval (k : ℕ) (ha : p.active k=true) :
    ActiveInterval p.δ p.η p.γ (fun i=>‖p.g i‖) (scaleAt p.δ p.η p.γ (fun i=>‖p.g i‖)) (p.q k) (p.q (k+1)) :=
  activeInterval_of_stop p.δ_pos.le p.γ_le_eta p.γ_sum (p.q_start k) ha

theorem idle (k : ℕ) (ha : p.active k=false) : p.q (k+1)=p.q k+1 :=
  blockStop_inactive p.δ_pos.le p.γ_le_eta p.γ_sum ha

theorem Z_converges : SeriesConverges p.Z := seriesConverges_chunks p.q_strict p.q_zero
  (smallError_converges p.noise p.γ_square (small_binary _ _ _ _) p.D p.ℓ)

theorem Z_active (k : ℕ) (ha : p.active k=true) : p.Z k=0 := by
  apply block_small_interval ha
  · intro t ht
    exact (blockStop_active_inside p.δ_pos.le p.γ_le_eta p.γ_sum (p.q_start k) ha
      (mem_Ico.mp ht).1 (mem_Ico.mp ht).2).1
  · intro t ht
    simp only [z,smallError,ht,zero_mul,mul_zero,add_zero]

end PathData
end GradErrors.Stochastic.Proof
-- End PathData

-- Begin PathEstimates

open Finset Filter Topology InnerProductSpace
namespace GradErrors.Stochastic.Proof.PathData
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (p : PathData E)

theorem q_late {k : ℕ} (hk : p.N≤k) : p.N≤p.q k := hk.trans (p.q_strict.id_le k)

theorem endpoint {k : ℕ} (hk : p.N≤k) (ha : p.active k=true) :
    p.H (k+1)≤3*p.H k/2 ∧ p.η/2≤∑i∈Ico (p.q k) (p.q (k+1)),p.γ i := by
  exact active_endpoint_budget (p.interval k ha) p.δ_pos (fun i=>(p.γ_pos i).le)
    p.c₂_nonneg p.η_pos.le p.ℓ_pos p.choice p.ε_le p.recurrence p.drift
    (p.gradient _ _) (p.γ_le _) (p.tails.vector _ (p.q_late hk) _ (p.q_strict.monotone (by omega)))

theorem excursion {k : ℕ} (hk : p.N≤k) (ha : p.active k=true) {t : ℕ}
    (ht : p.q k≤t) (ht' : t≤p.q (k+1)) : p.y t≤p.y (p.q k)+p.B*(p.H k)^2 := by
  have hh := active_excursion (p.interval k ha) p.δ_pos p.c_pos.le p.D_nonneg p.ℓ_pos.le
    p.ε_pos.le (fun i=>(p.γ_pos i).le) ht ht' p.descent
    (p.tails.inner _ (p.q_late hk) _ ht) (p.tails.square _ (p.q_late hk) _ ht)
    (p.tails.step _ (p.q_late hk) _ ht)
  have hm := mul_le_mul_of_nonneg_right p.coefficient (sq_nonneg (p.H k))
  exact hh.trans (add_le_add_right hm _)

theorem drop {k : ℕ} (hk : p.N≤k) (ha : p.active k=true) :
    p.y (p.q (k+1))≤p.y (p.q k)-p.K*(p.H k)^2 := by
  exact active_full_drop (p.interval k ha) p.δ_pos p.c_pos.le p.D_nonneg p.ℓ_pos.le
    p.ε_pos.le (fun i=>(p.γ_pos i).le) (p.endpoint hk ha).2
    (p.coefficient.trans p.drop_coefficient) p.descent
    (p.tails.inner _ (p.q_late hk) _ (p.q_strict.monotone (by omega)))
    (p.tails.square _ (p.q_late hk) _ (p.q_strict.monotone (by omega)))
    (p.tails.step _ (p.q_late hk) _ (p.q_strict.monotone (by omega)))

theorem idle_growth {k : ℕ} (hk : p.N≤k) (ha : p.active k=false) : p.H (k+1)≤3*p.δ/2 := by
  have hi := block_inactive (p.q k) ha
  have hG : scaleAt p.δ p.η p.γ (fun i=>‖p.g i‖) (p.q k)=p.δ := by
    simp only [scaleAt,hi.1,idleState]
  have ht := p.tails.vector (p.q k) (p.q_late hk) (p.q k+1) (by omega)
  simp only [Nat.Ico_succ_singleton,sum_singleton] at ht
  have hh := small_step_growth p.δ_pos p.η_pos.le p.c₂_nonneg p.ℓ_pos p.choice
    (p.γ_pos _).le (p.γ_le_eta _) p.ε_le (p.recurrence _) (p.drift _) hi.2 hG
    (p.gradient _ _) ht
  simpa only [H,p.idle k ha] using hh

theorem control : ChunkControl p.y p.H p.q p.active p.δ p.B p.K p.N := by
  refine ⟨p.idle,?_,?_,?_,?_,fun k=>norm_nonneg _⟩
  · intro k hk ha t ht ht'
    exact p.excursion hk ha ht ht'.le
  · intro k hk ha
    exact p.drop hk ha
  · intro k hk ha
    exact ⟨norm_nonneg _,(p.endpoint hk ha).1⟩
  · intro k hk ha
    exact ⟨norm_nonneg _,p.idle_growth hk ha⟩

theorem skeleton_step {k : ℕ} (hk : p.N≤k) :
    p.y (p.q (k+1))≤p.y (p.q k)+p.Z k-(if p.active k then p.K*p.δ^2 else 0) := by
  cases ha : p.active k
  · rw [if_neg (by simp),sub_zero,p.idle k ha]
    have hi := block_inactive (p.q k) ha
    have hz : p.Z k=p.z (p.q k) := by
      simp only [Z,p.idle k ha,Nat.Ico_succ_singleton,sum_singleton]
    rw [hz]
    have hχ : smallAt p.δ p.η p.γ (fun i=>‖p.g i‖) (p.q k)=1 := by simp only [smallAt,show (blockAt p.δ p.η p.γ (fun i=>‖p.g i‖) (p.q k)).active=false from ha,Bool.false_eq_true,ite_false]
    have hh := p.descent (p.q k)
    have hn : 0≤p.c*p.γ (p.q k)*‖p.g (p.q k)‖^2 := mul_nonneg (mul_nonneg p.c_pos.le (p.γ_pos _).le) (sq_nonneg _)
    simp only [z,smallError,hχ,one_mul,mul_one]
    linarith
  · rw [if_pos rfl,p.Z_active k ha,add_zero]
    have hh := p.drop hk ha
    have hδ := (p.interval k ha).height_ge
    have hs : p.δ^2≤(p.H k)^2 := by dsimp only [H]; nlinarith [p.δ_pos]
    have hm := mul_le_mul_of_nonneg_left hs p.K_pos.le
    linarith

end GradErrors.Stochastic.Proof.PathData
-- End PathEstimates

-- Begin CorrectedSequence

open Filter Topology Finset
namespace GradErrors.Stochastic.Proof

lemma corrected_sequence_converges {y z : ℕ → ℝ}
    (h : ∀ n, y (n+1) ≤ y n + z n) (hz : SeriesConverges z) :
    Tendsto y atTop atBot ∨ ∃ l, Tendsto y atTop (𝓝 l) := by
  obtain ⟨l, hl⟩ := hz
  let a : ℕ → ℝ := fun n => y n - ∑ i ∈ range n, z i
  have ha : Antitone a := antitone_nat_of_succ_le fun n => by
    dsimp [a]
    rw [sum_range_succ]
    linarith [h n]
  rcases tendsto_atTop_of_antitone ha with hb | ⟨b,hb⟩
  · left
    apply tendsto_atBot.mpr
    intro c
    have hz' := hl.eventually (gt_mem_nhds (show l < l+1 by linarith))
    have hy := (tendsto_atBot.mp hb) (c-(l+1))
    filter_upwards [hz',hy] with n hn hm
    dsimp [a] at hm
    linarith
  · right
    refine ⟨b+l, ?_⟩
    convert hb.add hl using 1
    ext n
    simp [a]

end GradErrors.Stochastic.Proof
-- End CorrectedSequence

-- Begin SkeletonConvergence

open Filter Topology Finset
namespace GradErrors.Stochastic.Proof

lemma SeriesConverges.tendsto_zero {E : Type*} [NormedAddCommGroup E] {a : ℕ → E}
    (h : SeriesConverges a) : Tendsto a atTop (𝓝 0) := by
  obtain ⟨l,hl⟩ := h
  have hsucc : Tendsto (fun n => ∑i∈range (n+1),a i) atTop (𝓝 l) := by
    simpa only [Function.comp_def] using hl.comp (tendsto_add_atTop_nat 1)
  have hh := hsucc.sub hl
  simpa only [sum_range_succ,add_sub_cancel_left,sub_self] using hh

lemma skeleton_converges {y z : ℕ → ℝ} {a : ℕ → Bool} {c : ℝ} (hc : 0<c)
    (hy : ∀n,y (n+1)≤y n+z n-(if a n then c else 0))
    (hz : SeriesConverges z) :
    Tendsto y atTop atBot ∨
      ∃l, Tendsto y atTop (𝓝 l) ∧ ∀ᶠ n in atTop,a n=false := by
  have hstep n : y (n+1)≤y n+z n := by
    have hh := hy n
    by_cases ha : a n=true
    · rw [if_pos ha] at hh; linarith
    · rw [if_neg ha,sub_zero] at hh; exact hh
  rcases corrected_sequence_converges hstep hz with hh | ⟨l,hl⟩
  · exact Or.inl hh
  · right
    refine ⟨l,hl,?_⟩
    have hsucc : Tendsto (fun n => y (n+1)) atTop (𝓝 l) := by
      simpa only [Function.comp_def] using hl.comp (tendsto_add_atTop_nat 1)
    have he : Tendsto (fun n => y (n+1)-y n-z n) atTop (𝓝 0) := by
      simpa only [sub_self,sub_zero] using (hsucc.sub hl).sub hz.tendsto_zero
    filter_upwards [he.eventually (lt_mem_nhds (neg_lt_zero.mpr hc))] with n hn
    cases ha : a n
    · rfl
    · have hh := hy n
      simp only [ha,ite_true] at hh
      linarith

end GradErrors.Stochastic.Proof
-- End SkeletonConvergence

-- Begin PathConvergence

open Finset Filter Topology InnerProductSpace
namespace GradErrors.Stochastic.Proof.PathData
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (p : PathData E)

theorem skeleton_limit :
    Tendsto (fun k=>p.y (p.q k)) atTop atBot ∨
      ∃l,Tendsto (fun k=>p.y (p.q k)) atTop (𝓝 l) ∧ ∀ᶠ k in atTop,p.active k=false := by
  have hh := skeleton_converges (y:=fun k=>p.y (p.q (p.N+k)))
    (z:=fun k=>p.Z (p.N+k)) (a:=fun k=>p.active (p.N+k))
    (mul_pos p.K_pos (sq_pos_of_pos p.δ_pos))
    (fun k => by simpa only [Nat.add_assoc] using p.skeleton_step (k:=p.N+k) (by omega))
    (p.Z_converges.drop p.N)
  rcases hh with hh|⟨l,hl,ha⟩
  · left
    apply (tendsto_add_atTop_iff_nat p.N).1
    simpa only [Nat.add_comm] using hh
  · right
    refine ⟨l,?_,?_⟩
    · apply (tendsto_add_atTop_iff_nat p.N).1
      simpa only [Nat.add_comm] using hl
    · obtain ⟨M,hM⟩ := eventually_atTop.mp ha
      filter_upwards [eventually_ge_atTop (p.N+M)] with k hk
      have hh := hM (k-p.N) (by omega)
      simpa only [Nat.add_sub_of_le (show p.N≤k by omega)] using hh

theorem threshold : Tendsto p.y atTop atBot ∨
    ∃l,Tendsto p.y atTop (𝓝 l) ∧ ∀ᶠ t in atTop,‖p.g t‖<p.δ := by
  rcases p.skeleton_limit with hb|⟨l,hl,ha⟩
  · left
    exact chunk_tendsto_atBot p.control p.B_nonneg p.δ_pos.le p.absorption p.r_bounds p.r_tendsto hb
  · right
    refine ⟨l,chunk_finite_transfer p.idle p.r_bounds p.r_tendsto ha hl,?_⟩
    filter_upwards [p.r_tendsto.eventually ha] with t ht
    have hq := p.idle _ ht
    have hr := p.r_bounds t
    have he : p.q (p.r t)=t := by omega
    have hi := (block_inactive (p.q (p.r t)) ht).2
    simpa only [he] using hi

end GradErrors.Stochastic.Proof.PathData
-- End PathConvergence

-- Begin ThresholdInterface

open Filter Topology InnerProductSpace
namespace GradErrors.Stochastic.Proof

def DeterministicThreshold (n : ℕ) : Prop :=
  ∀ (γ : ℕ → ℝ) (x s w g : ℕ → EuclideanSpace ℝ (Fin n)) (y : ℕ → ℝ)
    (δ η c c₂ D ℓ : ℝ),
    0<δ → 0<η → 0<c → 0≤c₂ → 0≤D → 0<ℓ →
    (∀t,0<γ t) → (∀t,γ t≤η/2) →
    Tendsto (fun T => ∑t∈Finset.range T,γ t) atTop atTop →
    Summable (fun t => γ t^2) →
    ℓ*η*(c₂*(1/δ+2)+1)≤1/4 →
    (∀t,x (t+1)=x t+γ t • (s t+w t)) →
    (∀t,‖s t‖≤c₂*(1+‖g t‖)) →
    (∀i j,‖g i-g j‖≤ℓ*‖x i-x j‖) →
    (∀t,y (t+1)≤y t-c*γ t*‖g t‖^2+γ t*⟪g t,w t⟫_ℝ+D*γ t^2+ℓ*γ t^2*‖w t‖^2) →
    NoiseLimits γ g w (scaleAt δ η γ (fun t => ‖g t‖))
      (smallAt δ η γ (fun t => ‖g t‖)) →
    Tendsto y atTop atBot ∨ (∃l,Tendsto y atTop (𝓝 l) ∧ ∀ᶠ t in atTop,‖g t‖<δ)

end GradErrors.Stochastic.Proof
-- End ThresholdInterface

-- Begin DeterministicThreshold

open Finset Filter Topology InnerProductSpace
namespace GradErrors.Stochastic.Proof

theorem deterministic_threshold (n : ℕ) : DeterministicThreshold n := by
  intro γ x s w g y δ η c c₂ D ℓ hδ hη hc hc₂ hD hℓ hγ hγle hsum hsquare hchoice hx hs hg hy hnoise
  let B : ℝ := c*η/64
  let K : ℝ := c*η/16
  let C : ℝ := 1+ℓ+D/δ^2
  have hB : 0<B := by dsimp [B]; positivity
  have hK : 0<K := by dsimp [K]; positivity
  have hC : 0<C := by dsimp [C]; positivity
  let ε : ℝ := min η (B/C)
  have hε : 0<ε := lt_min hη (div_pos hB hC)
  have heη : ε≤η := min_le_left _ _
  have heC : ε*C≤B := (le_div_iff₀ hC).mp (min_le_right _ _)
  obtain ⟨N,hN⟩ := hnoise.intervalTails hsquare hε
  let p : PathData (EuclideanSpace ℝ (Fin n)) := {
    γ:=γ, x:=x, s:=s, w:=w, g:=g, y:=y,
    δ:=δ, η:=η, c:=c, c₂:=c₂, D:=D, ℓ:=ℓ, ε:=ε, B:=B, K:=K, N:=N,
    δ_pos:=hδ, η_pos:=hη, c_pos:=hc, c₂_nonneg:=hc₂, D_nonneg:=hD, ℓ_pos:=hℓ,
    ε_pos:=hε, ε_le:=heη, B_nonneg:=hB.le, K_pos:=hK,
    coefficient:=heC,
    drop_coefficient:=by dsimp [B,K]; nlinarith [mul_pos hc hη],
    absorption:=by dsimp [B,K]; nlinarith [mul_pos hc hη],
    choice:=hchoice, γ_pos:=hγ, γ_le:=hγle, γ_sum:=hsum, γ_square:=hsquare,
    recurrence:=hx, drift:=hs, gradient:=fun a b=>hg b a,
    descent:=fun i=>by simpa only [mul_assoc] using hy i,
    tails:=hN, noise:=hnoise }
  exact p.threshold

end GradErrors.Stochastic.Proof
-- End DeterministicThreshold

-- Begin BlockMeasurable

open MeasureTheory
namespace GradErrors.Stochastic.Proof
variable {Ω : Type*} [MeasurableSpace Ω]

def StateMeasurable (q : Ω → BlockState) : Prop :=
  Measurable (fun ω => (q ω).start) ∧ Measurable (fun ω => (q ω).height) ∧
  Measurable (fun ω => (q ω).spent) ∧ Measurable (fun ω => (q ω).active)

theorem blockStep_measurable (δ η : ℝ) (γ : ℕ → ℝ) (g : ℕ → Ω → ℝ)
    (t : ℕ) {q : Ω → BlockState} (hq : StateMeasurable q) (hg : Measurable (g t)) :
    StateMeasurable (fun ω => blockStep δ η γ (fun i => g i ω) t (q ω)) := by
  classical
  have hc : MeasurableSet {ω | CanContinue η γ (fun i => g i ω) t (q ω)} := by
    exact (measurableSet_eq_fun hq.2.2.2 measurable_const).inter
      ((measurableSet_le (hq.2.1.div_const 2) hg).inter
        ((measurableSet_le hg (hq.2.1.const_mul 2)).inter
          (measurableSet_le (hq.2.2.1.add_const (γ t)) measurable_const)))
  have hd : MeasurableSet {ω | δ ≤ g t ω} := measurableSet_le measurable_const hg
  refine ⟨?_,?_,?_,?_⟩
  · convert hq.1.ite hc ((measurable_const : Measurable (fun _ : Ω => t)).ite hd measurable_const) using 1
    funext ω
    unfold blockStep
    dsimp only
    split_ifs <;> rfl
    all_goals infer_instance
  · convert hq.2.1.ite hc (hg.ite hd (measurable_const : Measurable (fun _ : Ω => δ))) using 1
    funext ω
    unfold blockStep
    dsimp only
    split_ifs <;> rfl
    all_goals infer_instance
  · convert (hq.2.2.1.add_const (γ t)).ite hc ((measurable_const : Measurable (fun _ : Ω => γ t)).ite hd (measurable_const : Measurable (fun _ : Ω => (0:ℝ)))) using 1
    funext ω
    unfold blockStep
    dsimp only
    split_ifs <;> rfl
    all_goals infer_instance
  · convert (measurable_const : Measurable (fun _ : Ω => true)).ite hc ((measurable_const : Measurable (fun _ : Ω => true)).ite hd (measurable_const : Measurable (fun _ : Ω => false))) using 1
    funext ω
    unfold blockStep
    dsimp only
    split_ifs <;> rfl
    all_goals infer_instance

theorem blockAt_measurable (δ η : ℝ) (γ : ℕ → ℝ) (g : ℕ → Ω → ℝ) (t : ℕ)
    (hg : ∀ i ≤ t, Measurable (g i)) :
    StateMeasurable (fun ω => blockAt δ η γ (fun i => g i ω) t) := by
  induction t with
  | zero =>
    apply blockStep_measurable δ η γ g 0
    · exact ⟨measurable_const,measurable_const,measurable_const,measurable_const⟩
    · exact hg 0 le_rfl
  | succ t ih =>
    apply blockStep_measurable δ η γ g (t+1)
    · exact ih (fun i hi => hg i (by omega))
    · exact hg (t+1) le_rfl

theorem scaleAt_measurable (δ η : ℝ) (γ : ℕ → ℝ) (g : ℕ → Ω → ℝ) (t : ℕ)
    (hg : ∀ i ≤ t, Measurable (g i)) :
    Measurable (fun ω => scaleAt δ η γ (fun i => g i ω) t) :=
  (blockAt_measurable δ η γ g t hg).2.1

theorem smallAt_measurable (δ η : ℝ) (γ : ℕ → ℝ) (g : ℕ → Ω → ℝ) (t : ℕ)
    (hg : ∀ i ≤ t, Measurable (g i)) :
    Measurable (fun ω => smallAt δ η γ (fun i => g i ω) t) := by
  unfold smallAt
  apply measurable_const.ite _ measurable_const
  exact measurableSet_eq_fun (blockAt_measurable δ η γ g t hg).2.2.2 measurable_const

end GradErrors.Stochastic.Proof
-- End BlockMeasurable

-- Begin PrefixScale

open MeasureTheory ProbabilityTheory
namespace GradErrors.Stochastic.Proof

variable {Ω E : Type*} [NormedAddCommGroup E]

noncomputable def prefixScale (δ η : ℝ) (γ : ℕ → ℝ) (g : ℕ → Ω → E)
    (N t : ℕ) (ω : Ω) : ℝ :=
  if N≤t then scaleAt δ η (fun i => γ (N+i)) (fun i => ‖g (N+i) ω‖) (t-N)
  else max δ ‖g t ω‖

noncomputable def prefixSmall (δ η : ℝ) (γ : ℕ → ℝ) (g : ℕ → Ω → E)
    (N t : ℕ) (ω : Ω) : ℝ :=
  if N≤t then smallAt δ η (fun i => γ (N+i)) (fun i => ‖g (N+i) ω‖) (t-N)
  else 0

lemma prefixScale_add (δ η : ℝ) (γ : ℕ → ℝ) (g : ℕ → Ω → E) (N t : ℕ) (ω : Ω) :
    prefixScale δ η γ g N (N+t) ω =
      scaleAt δ η (fun i => γ (N+i)) (fun i => ‖g (N+i) ω‖) t := by
  simp [prefixScale]

lemma prefixSmall_add (δ η : ℝ) (γ : ℕ → ℝ) (g : ℕ → Ω → E) (N t : ℕ) (ω : Ω) :
    prefixSmall δ η γ g N (N+t) ω =
      smallAt δ η (fun i => γ (N+i)) (fun i => ‖g (N+i) ω‖) t := by
  simp [prefixSmall]

lemma prefixScale_ge (δ η : ℝ) (γ : ℕ → ℝ) (g : ℕ → Ω → E) (N t : ℕ) (ω : Ω) :
    δ≤prefixScale δ η γ g N t ω := by
  unfold prefixScale
  split
  · exact block_height_ge _
  · exact le_max_left _ _

lemma prefixScale_bound {δ η : ℝ} (hd : 0≤δ) {γ : ℕ → ℝ} (g : ℕ → Ω → E)
    (N : ℕ) (hγ : ∀t,γ (N+t)≤η) (t : ℕ) (ω : Ω) :
    ‖g t ω‖≤2*prefixScale δ η γ g N t ω := by
  unfold prefixScale
  split_ifs with h
  · have hh := scale_bound (g:=fun i => ‖g (N+i) ω‖) hd hγ (t-N)
    simpa only [Nat.add_sub_of_le h] using hh
  · have hh := le_max_right δ ‖g t ω‖
    linarith [norm_nonneg (g t ω)]

lemma prefixSmall_binary (δ η : ℝ) (γ : ℕ → ℝ) (g : ℕ → Ω → E) (N t : ℕ) (ω : Ω) :
    prefixSmall δ η γ g N t ω=0 ∨ prefixSmall δ η γ g N t ω=1 := by
  unfold prefixSmall
  split
  · exact small_binary _ _ _ _ _
  · exact Or.inl rfl

lemma prefixSmall_gradient {δ η : ℝ} {γ : ℕ → ℝ} {g : ℕ → Ω → E} {N t : ℕ} {ω : Ω}
    (h : prefixSmall δ η γ g N t ω=1) : ‖g t ω‖<δ := by
  unfold prefixSmall at h
  split_ifs at h with ht
  · have hh := small_gradient h
    simpa only [Nat.add_sub_of_le ht] using hh
  · norm_num at h

variable [m0 : MeasurableSpace Ω] (ℱ : Filtration ℕ m0)

lemma prefixScale_measurable (δ η : ℝ) (γ : ℕ → ℝ) (g : ℕ → Ω → E)
    (hg : ∀t,StronglyMeasurable[ℱ t] (g t)) (N t : ℕ) :
    Measurable[ℱ t] (prefixScale δ η γ g N t) := by
  unfold prefixScale
  split_ifs with h
  · apply @scaleAt_measurable Ω (ℱ t) δ η (fun i => γ (N+i))
      (fun i ω => ‖g (N+i) ω‖) (t-N)
    intro i hi
    exact ((hg (N+i)).mono (ℱ.mono (by omega))).norm.measurable
  · exact measurable_const.max (hg t).norm.measurable

lemma prefixSmall_measurable (δ η : ℝ) (γ : ℕ → ℝ) (g : ℕ → Ω → E)
    (hg : ∀t,StronglyMeasurable[ℱ t] (g t)) (N t : ℕ) :
    Measurable[ℱ t] (prefixSmall δ η γ g N t) := by
  unfold prefixSmall
  split_ifs with h
  · apply @smallAt_measurable Ω (ℱ t) δ η (fun i => γ (N+i))
      (fun i ω => ‖g (N+i) ω‖) (t-N)
    intro i hi
    exact ((hg (N+i)).mono (ℱ.mono (by omega))).norm.measurable
  · exact measurable_const

end GradErrors.Stochastic.Proof
-- End PrefixScale

-- Begin WeightedLocal

open MeasureTheory
open scoped ENNReal
namespace GradErrors.Stochastic.Proof

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {m : MeasurableSpace Ω} {P : @Measure Ω m0}

lemma weighted_lintegral_le (hm : m ≤ m0) {a b : Ω → ℝ≥0∞}
    (ha : Measurable[m0] a) (hb : Measurable[m0] b)
    (h : ∀ S, MeasurableSet[m] S → ∫⁻ ω in S, a ω ∂P ≤ ∫⁻ ω in S, b ω ∂P)
    {q : Ω → ℝ≥0∞} (hq : Measurable[m] q) :
    (∫⁻ ω, a ω * q ω ∂P) ≤ ∫⁻ ω, b ω * q ω ∂P := by
  have hh : (P.withDensity a).trim hm ≤ (P.withDensity b).trim hm := by
    apply Measure.le_iff.mpr
    intro S hS
    rw [trim_measurableSet_eq hm hS, trim_measurableSet_eq hm hS,
      withDensity_apply _ (hm S hS), withDensity_apply _ (hm S hS)]
    exact h S hS
  have hh := lintegral_mono' hh (fun _ => le_rfl : q ≤ q)
  rw [lintegral_trim hm hq, lintegral_trim hm hq,
    lintegral_withDensity_eq_lintegral_mul _ ha (hq.mono hm le_rfl),
    lintegral_withDensity_eq_lintegral_mul _ hb (hq.mono hm le_rfl)] at hh
  exact hh

end GradErrors.Stochastic.Proof
-- End WeightedLocal

-- Begin SquareMoment

open MeasureTheory
open scoped ENNReal NNReal
namespace GradErrors.Stochastic.Proof

variable {Ω E : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [NormedAddCommGroup E]

lemma memLp_two_of_enorm_sq_bound {r : Ω → E} (hr : AEStronglyMeasurable r P)
    {C : ℝ} (h : (∫⁻ ω, ‖r ω‖ₑ^2 ∂P) ≤ ENNReal.ofReal C) : MemLp r 2 P := by
  apply (memLp_two_iff_integrable_sq_norm hr).2
  refine ⟨hr.norm.pow 2, hasFiniteIntegral_iff_enorm.mpr ?_⟩
  have hh : (∫⁻ ω, ‖r ω‖ₑ^2 ∂P) < ⊤ := h.trans_lt ENNReal.ofReal_lt_top
  simpa only [enorm_pow, enorm_norm] using hh

lemma integral_sq_norm_le_of_enorm {r : Ω → E} (hr : AEStronglyMeasurable r P)
    {C : ℝ} (hC : 0≤C) (h : (∫⁻ ω, ‖r ω‖ₑ^2 ∂P) ≤ ENNReal.ofReal C) :
    (∫ω, ‖r ω‖^2 ∂P) ≤ C := by
  have hi := (memLp_two_iff_integrable_sq_norm hr).1 (memLp_two_of_enorm_sq_bound hr h)
  apply (ENNReal.ofReal_le_ofReal_iff hC).mp
  rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => sq_nonneg _)]
  simpa only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm] using h

end GradErrors.Stochastic.Proof
-- End SquareMoment

-- Begin LocalizedMean

open MeasureTheory
namespace GradErrors.Stochastic.Proof

variable {Ω E F H : Type*} {m : MeasurableSpace Ω} [m0 : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

lemma condExp_eq_zero_of_setIntegral (hm : m ≤ m0) {w : Ω → E}
    (hw : Integrable w P)
    (hz : ∀ S, MeasurableSet[m] S → ∫ ω in S, w ω ∂P = 0) :
    P[w|m] =ᵐ[P] 0 := by
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm hw
  · intro S _ _; exact (integrable_zero _ _ _).integrableOn
  · intro S hS _; simpa using (hz S hS).symm
  · exact stronglyMeasurable_zero.aestronglyMeasurable

omit [IsFiniteMeasure P] in
lemma localized_bilin_condExp_zero (hm : m ≤ m0) (B : F →L[ℝ] E →L[ℝ] H)
    {a : Ω → F} {w : Ω → E} (ha : StronglyMeasurable[m] a)
    (hi : Integrable (fun ω => B (a ω) (w ω)) P)
    (S : ℕ → Set Ω) (hS : ∀ n, MeasurableSet[m] (S n))
    (hcover : ∀ ω, ∃ n, ω ∈ S n)
    (hw : ∀ n, Integrable ((S n).indicator w) P)
    (hz : ∀ n, P[(S n).indicator w|m] =ᵐ[P] 0) :
    P[fun ω => B (a ω) (w ω)|m] =ᵐ[P] 0 := by
  classical
  have he (n : ℕ) : (fun ω => B (a ω) ((S n).indicator w ω)) =
      (S n).indicator (fun ω => B (a ω) (w ω)) := by
    ext ω
    by_cases h : ω ∈ S n <;> simp [h]
  have hh (n : ℕ) : (S n).indicator (P[fun ω => B (a ω) (w ω)|m]) =ᵐ[P] 0 := by
    have hp := condExp_bilin_of_stronglyMeasurable_left (B:=B) ha
      (show Integrable (fun ω => B (a ω) ((S n).indicator w ω)) P by
        rw [he]; exact hi.indicator (hm _ (hS n))) (hw n)
    rw [he] at hp
    have hc := condExp_indicator hi (hS n)
    filter_upwards [hp,hc,hz n] with ω hp hc hz
    rw [← hc,hp,hz]
    simp
  filter_upwards [ae_all_iff.mpr hh] with ω hω
  obtain ⟨n,hn⟩ := hcover ω
  have hh := hω n
  simpa [Set.indicator_of_mem hn] using hh

end GradErrors.Stochastic.Proof
-- End LocalizedMean

-- Begin LocalNoise

open MeasureTheory Set
open scoped ENNReal NNReal
namespace GradErrors.Stochastic.Proof

variable {Ω E : Type*} {m : MeasurableSpace Ω} [m0 : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma indicator_noise_memLp (hm : m ≤ m0) {w : Ω → E}
    (hw : AEStronglyMeasurable w P) {b : Ω → ℝ≥0∞}
    (hb : ∀ S, MeasurableSet[m] S → ∫⁻ ω in S, ‖w ω‖ₑ^2 ∂P ≤ ∫⁻ ω in S, b ω ∂P)
    {S : Set Ω} (hS : MeasurableSet[m] S) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbound : ∀ ω∈S, b ω ≤ C) : MemLp (S.indicator w) 2 P := by
  have hh : (∫⁻ ω, ‖S.indicator w ω‖ₑ^2 ∂P) ≤ C := by
    calc
      _ = ∫⁻ ω in S, ‖w ω‖ₑ^2 ∂P := by
        rw [← lintegral_indicator (hm S hS)]
        congr 1; ext ω; by_cases h : ω∈S <;> simp [h]
      _ ≤ ∫⁻ ω in S, b ω ∂P := hb S hS
      _ ≤ ∫⁻ _ in S, C ∂P := lintegral_mono_ae <|
        (ae_restrict_mem (hm S hS)).mono fun ω hω => hbound ω hω
      _ ≤ C := by simp only [setLIntegral_const]; exact mul_le_of_le_one_right' prob_le_one
  apply memLp_two_of_enorm_sq_bound (hw.indicator (hm S hS))
  exact hh.trans (by rw [ENNReal.ofReal_toReal hC])

lemma indicator_noise_condExp_zero (hm : m ≤ m0) {w : Ω → E}
    (hz : ∀ S, MeasurableSet[m] S → (∫⁻ ω in S, ‖w ω‖ₑ ∂P) < ⊤ →
      ∫ ω in S, w ω ∂P = 0)
    {S : Set Ω} (hS : MeasurableSet[m] S) (hw : Integrable (S.indicator w) P) :
    P[S.indicator w|m] =ᵐ[P] 0 := by
  apply condExp_eq_zero_of_setIntegral hm hw
  intro T hT
  rw [integral_indicator (hm S hS), Measure.restrict_restrict (hm S hS)]
  apply hz (S∩T) (hS.inter hT)
  have hi : IntegrableOn w (S∩T) P :=
    ((integrable_indicator_iff (hm S hS)).mp hw).mono_set inter_subset_left
  exact hasFiniteIntegral_iff_enorm.mp hi.2

end GradErrors.Stochastic.Proof
-- End LocalNoise

-- Begin NoiseTransform

open MeasureTheory Set
open scoped ENNReal NNReal
namespace GradErrors.Stochastic.Proof

variable {Ω E F H : Type*} {m : MeasurableSpace Ω} [m0 : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

lemma noise_bilin_condExp_zero (hm : m ≤ m0) (B : F →L[ℝ] E →L[ℝ] H)
    {w : Ω → E} (hw : StronglyMeasurable w) {b : Ω → ℝ} (hb : Measurable[m] b)
    (hvar : ∀ S, MeasurableSet[m] S → ∫⁻ ω in S, ‖w ω‖ₑ^2 ∂P ≤
      ∫⁻ ω in S, ENNReal.ofReal (b ω) ∂P)
    (hmean : ∀ S, MeasurableSet[m] S → (∫⁻ ω in S, ‖w ω‖ₑ ∂P) < ⊤ →
      ∫ ω in S, w ω ∂P = 0)
    {a : Ω → F} (ha : StronglyMeasurable[m] a)
    (hi : Integrable (fun ω => B (a ω) (w ω)) P) :
    P[fun ω => B (a ω) (w ω)|m] =ᵐ[P] 0 := by
  let S : ℕ → Set Ω := fun n => {ω | b ω ≤ n}
  have hS n : MeasurableSet[m] (S n) := measurableSet_le hb measurable_const
  have hcover : ∀ ω, ∃ n, ω∈S n := fun ω => exists_nat_ge (b ω)
  have h2 n : MemLp ((S n).indicator w) 2 P :=
    indicator_noise_memLp hm hw.aestronglyMeasurable hvar (hS n)
      (C:=ENNReal.ofReal n) ENNReal.ofReal_ne_top (fun ω hω => ENNReal.ofReal_le_ofReal hω)
  exact localized_bilin_condExp_zero hm B ha hi S hS hcover
    (fun n => (h2 n).integrable (by norm_num))
    (fun n => indicator_noise_condExp_zero hm hmean (hS n) ((h2 n).integrable (by norm_num)))

omit [NormedSpace ℝ E] [CompleteSpace E] [NormedSpace ℝ H] [CompleteSpace H] in
lemma transformed_square_bound (hm : m ≤ m0)
    {w : Ω → E} (hw : StronglyMeasurable w) {b : Ω → ℝ} (hb : Measurable[m] b)
    (hvar : ∀ S, MeasurableSet[m] S → ∫⁻ ω in S, ‖w ω‖ₑ^2 ∂P ≤
      ∫⁻ ω in S, ENNReal.ofReal (b ω) ∂P)
    {q : Ω → ℝ} (hq : Measurable[m] q) {r : Ω → H}
    (hr : ∀ω, ‖r ω‖^2 ≤ ‖w ω‖^2*q ω^2)
    {C : ℝ} (hC : ∀ω, b ω*q ω^2 ≤ C) :
    (∫⁻ ω, ‖r ω‖ₑ^2 ∂P) ≤ ENNReal.ofReal C := by
  have he (v : H) : ‖v‖ₑ^2 = ENNReal.ofReal (‖v‖^2) := by
    rw [ENNReal.ofReal_pow (norm_nonneg _),ofReal_norm]
  have hew (v : E) : ‖v‖ₑ^2 = ENNReal.ofReal (‖v‖^2) := by
    rw [ENNReal.ofReal_pow (norm_nonneg _),ofReal_norm]
  calc
    _ ≤ ∫⁻ ω, ‖w ω‖ₑ^2*ENNReal.ofReal (q ω^2) ∂P := by
      apply lintegral_mono
      intro ω
      dsimp only
      rw [he,hew,← ENNReal.ofReal_mul (sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (hr ω)
    _ ≤ ∫⁻ ω, ENNReal.ofReal (b ω)*ENNReal.ofReal (q ω^2) ∂P :=
      weighted_lintegral_le hm (hw.enorm.pow_const 2)
        (hb.mono hm le_rfl).ennreal_ofReal hvar (hq.pow_const 2).ennreal_ofReal
    _ ≤ ∫⁻ _ : Ω, ENNReal.ofReal C ∂P := by
      apply lintegral_mono
      intro ω
      dsimp only
      rw [← ENNReal.ofReal_mul' (sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (hC ω)
    _ = _ := by simp

end GradErrors.Stochastic.Proof
-- End NoiseTransform

-- Begin MartingaleSeries

open Filter Topology MeasureTheory ProbabilityTheory Finset
open scoped ENNReal
namespace GradErrors.Stochastic.Proof

variable {Ω : Type*} [m0 : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℕ m0} {a : ℕ → Ω → ℝ}

lemma martingale_partial_sums
    (ha : ∀ n, StronglyMeasurable[ℱ (n+1)] (a n))
    (hi : ∀ n, Integrable (a n) P) (hz : ∀ n, P[a n|ℱ n] =ᵐ[P] 0) :
    Martingale (fun n ω => ∑ i ∈ range n, a i ω) ℱ P := by
  have hm n : StronglyMeasurable[ℱ n] (fun ω => ∑ i ∈ range n, a i ω) := by
    simpa only [← Finset.sum_apply] using Finset.stronglyMeasurable_sum (range n) (fun i hi =>
      (ha i).mono (ℱ.mono (by simpa using Finset.mem_range.mp hi)))
  have hii n : Integrable (fun ω => ∑ i ∈ range n, a i ω) P := by
    simpa only [← Finset.sum_apply] using integrable_finsetSum' (range n) (fun i _ => hi i)
  apply martingale_nat hm hii
  intro n
  simp only [sum_range_succ]
  have hc := condExp_add (hii n) (hi n) (ℱ n)
  rw [condExp_of_stronglyMeasurable (ℱ.le n) (hm n) (hii n)] at hc
  change P[(fun ω => ∑ i ∈ range n, a i ω + a n ω)|ℱ n] =ᵐ[P] _ at hc
  filter_upwards [hc,hz n] with ω hc hz
  simpa [hz] using hc.symm

lemma partial_sums_energy
    (ha : ∀ n, StronglyMeasurable[ℱ (n+1)] (a n))
    (h2 : ∀ n, MemLp (a n) 2 P) (hz : ∀ n, P[a n|ℱ n] =ᵐ[P] 0) (n : ℕ) :
    (∫ω, (∑ i ∈ range n, a i ω)^2 ∂P) = ∑ i ∈ range n, ∫ω, (a i ω)^2 ∂P := by
  induction n with
  | zero => simp
  | succ n ih =>
    let s : Ω → ℝ := fun ω => ∑ i ∈ range n, a i ω
    have hs : MemLp s 2 P := by
      simpa only [s, ← Finset.sum_apply] using memLp_finsetSum' (range n) (fun i _ => h2 i)
    have hm : StronglyMeasurable[ℱ n] s := by
      simpa only [s, ← Finset.sum_apply] using Finset.stronglyMeasurable_sum (range n) (fun i hi =>
        (ha i).mono (ℱ.mono (by simpa using Finset.mem_range.mp hi)))
    have hp := condExp_mul_of_stronglyMeasurable_left hm
      (hs.integrable_mul (h2 n)) ((h2 n).integrable (by norm_num))
    change P[(fun ω => s ω*a n ω)|ℱ n] =ᵐ[P] (fun ω => s ω*P[a n|ℱ n] ω) at hp
    have hprod : Integrable (fun ω => s ω*a n ω) P := hs.integrable_mul (h2 n)
    have hzero : (∫ω, s ω*a n ω ∂P)=0 := by
      calc
        _ = ∫ω,P[(fun ω => s ω*a n ω)|ℱ n] ω ∂P := (integral_condExp (ℱ.le n)).symm
        _ = 0 := by
          have hh : P[(fun ω => s ω*a n ω)|ℱ n] =ᵐ[P] 0 := by
            filter_upwards [hp,hz n] with ω hp hz
            rw [hp,hz]; simp
          rw [integral_congr_ae hh]; simp
    have hi : Integrable (fun ω => s ω^2+2*(s ω*a n ω)) P :=
      hs.integrable_sq.add (hprod.const_mul 2)
    rw [sum_range_succ]
    have he : (∫ω,(s ω+a n ω)^2 ∂P) =
        (∫ω,s ω^2 ∂P)+2*(∫ω,s ω*a n ω ∂P)+(∫ω,(a n ω)^2 ∂P) := by
      calc
        _ = ∫ω,(s ω^2+2*(s ω*a n ω))+(a n ω)^2 ∂P := by congr 1; funext ω; ring
        _ = _ := by rw [integral_add hi (h2 n).integrable_sq,
          integral_add hs.integrable_sq (hprod.const_mul 2),integral_const_mul]
    simp only [sum_range_succ]
    change (∫ω,(s ω+a n ω)^2 ∂P) = _
    rw [he,hzero]
    simpa [s] using ih

lemma scalar_martingale_series
    (ha : ∀ n, StronglyMeasurable[ℱ (n+1)] (a n))
    (h2 : ∀ n, MemLp (a n) 2 P) (hz : ∀ n, P[a n|ℱ n] =ᵐ[P] 0)
    (hv : Summable (fun n => ∫ω,(a n ω)^2 ∂P)) :
    ∀ᵐ ω ∂P, SeriesConverges (fun n => a n ω) := by
  have hm := martingale_partial_sums ha (fun n => (h2 n).integrable (by norm_num)) hz
  apply hm.submartingale.exists_ae_tendsto_of_bdd (R:=Real.toNNReal (1+∑' n, ∫ω,(a n ω)^2 ∂P))
  intro n
  have hs : MemLp (fun ω => ∑ i ∈ range n, a i ω) 2 P := by
    simpa only [← Finset.sum_apply] using memLp_finsetSum' (range n) (fun i _ => h2 i)
  rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm (hs.integrable (by norm_num))]
  change ENNReal.ofReal _ ≤ ENNReal.ofReal _
  apply ENNReal.ofReal_le_ofReal
  have hh := integral_mono (hs.integrable (by norm_num)).norm
    ((integrable_const 1).add hs.integrable_sq)
    (fun ω => show ‖∑ i ∈ range n,a i ω‖ ≤ 1+(∑ i ∈ range n,a i ω)^2 by
      rw [Real.norm_eq_abs]; nlinarith [sq_nonneg (|∑ i ∈ range n,a i ω|-1),sq_abs (∑ i ∈ range n,a i ω)])
  simp only [Pi.add_apply] at hh
  rw [integral_add (integrable_const 1) hs.integrable_sq,integral_const] at hh
  simp only [probReal_univ,smul_eq_mul,one_mul] at hh
  rw [partial_sums_energy ha h2 hz n] at hh
  exact hh.trans (add_le_add le_rfl (hv.sum_le_tsum (range n) (fun i _ => integral_nonneg fun _ => sq_nonneg _)))

end GradErrors.Stochastic.Proof
-- End MartingaleSeries

-- Begin VectorSeries

open Filter Topology MeasureTheory ProbabilityTheory Finset
open scoped ENNReal
namespace GradErrors.Stochastic.Proof

variable {Ω : Type*} [m0 : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℕ m0}

omit [IsProbabilityMeasure P] in
lemma nonnegative_integral_series {a : ℕ → Ω → ℝ}
    (ha : ∀ n, Integrable (a n) P) (hn : ∀ n ω, 0≤a n ω)
    (hs : Summable (fun n => ∫ω,a n ω ∂P)) :
    ∀ᵐ ω ∂P, SeriesConverges (fun n => a n ω) := by
  have hb : (∑' n, eLpNorm (a n) 1 P) ≠ ⊤ := by
    have he n : eLpNorm (a n) 1 P = ENNReal.ofReal (∫ω,a n ω ∂P) := by
      rw [eLpNorm_one_eq_lintegral_enorm,← ofReal_integral_norm_eq_lintegral_enorm (ha n)]
      congr 1
      apply integral_congr_ae
      exact ae_of_all _ fun ω => Real.norm_of_nonneg (hn n ω)
    simp_rw [he]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg (hn n)) hs]
    exact ENNReal.ofReal_ne_top
  filter_upwards [summable_norm_of_tsum_eLpNorm_ne_top (by norm_num : (1:ℝ≥0∞)≤1)
    (fun n => (ha n).aestronglyMeasurable) hb] with ω hω
  have hh : Summable (fun n => a n ω) := by
    simpa only [Real.norm_of_nonneg (hn _ _)] using hω
  exact ⟨_,hh.hasSum.tendsto_sum_nat⟩

lemma vector_martingale_series {d : ℕ} {a : ℕ → Ω → EuclideanSpace ℝ (Fin d)}
    (ha : ∀ n, StronglyMeasurable[ℱ (n+1)] (a n))
    (h2 : ∀ n, MemLp (a n) 2 P) (hz : ∀ n, P[a n|ℱ n] =ᵐ[P] 0)
    (hv : Summable (fun n => ∫ω,‖a n ω‖^2 ∂P)) :
    ∀ᵐ ω ∂P, SeriesConverges (fun n => a n ω) := by
  have hh (i : Fin d) : ∀ᵐ ω ∂P, SeriesConverges (fun n => a n ω i) := by
    let T : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := EuclideanSpace.proj i
    have h2i n : MemLp (fun ω => a n ω i) 2 P := (h2 n).continuousLinearMap_comp T
    apply scalar_martingale_series (ℱ:=ℱ)
      (fun n => T.continuous.comp_stronglyMeasurable (ha n)) h2i
    · intro n
      have hc := T.comp_condExp_comm ((h2 n).integrable (by norm_num)) (m:=ℱ n)
      filter_upwards [hc,hz n] with ω hc hz
      change T (P[a n|ℱ n] ω) = P[(fun ω => a n ω i)|ℱ n] ω at hc
      rw [hz] at hc
      change P[(fun ω => a n ω i)|ℱ n] ω = 0
      simpa only [Pi.zero_apply,map_zero] using hc.symm
    · apply Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => sq_nonneg _) _ hv
      intro n
      apply integral_mono (h2i n).integrable_sq ((memLp_two_iff_integrable_sq_norm (h2 n).1).1 (h2 n))
      intro ω
      dsimp only
      have h := PiLp.norm_apply_le (a n ω) i
      rw [Real.norm_eq_abs] at h
      nlinarith [sq_abs (a n ω i),norm_nonneg (a n ω),abs_nonneg (a n ω i)]
  filter_upwards [ae_all_iff.mpr hh] with ω hω
  choose l hl using hω
  let T := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)
  refine ⟨T.symm l, ?_⟩
  have hp := (tendsto_pi_nhds.mpr hl)
  have ht := T.symm.continuous.continuousAt.tendsto.comp hp
  convert ht using 1
  ext n i
  simp [T]

end GradErrors.Stochastic.Proof
-- End VectorSeries

-- Begin WeightedSeries

open Filter Topology MeasureTheory ProbabilityTheory Finset
open scoped ENNReal
namespace GradErrors.Stochastic.Proof

variable {Ω E : Type*} [m0 : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℕ m0}
    [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma weighted_square_integral (r : Ω → E) (c : ℝ) :
    (∫ω,‖c • r ω‖^2 ∂P) = c^2*(∫ω,‖r ω‖^2 ∂P) := by
  simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,integral_const_mul]

lemma weighted_energy_summable {r : ℕ → Ω → E} {γ : ℕ → ℝ}
    {C : ℝ} (hC : ∀n, (∫ω,‖r n ω‖^2 ∂P) ≤ C) (hs : Summable (fun n => γ n^2)) :
    Summable (fun n => ∫ω,‖γ n • r n ω‖^2 ∂P) := by
  apply Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => sq_nonneg _) _ (hs.mul_right C)
  intro n
  rw [weighted_square_integral]
  exact mul_le_mul_of_nonneg_left (hC n) (sq_nonneg _)

lemma weighted_nonnegative_series {r : ℕ → Ω → E} {γ : ℕ → ℝ}
    (h2 : ∀n, MemLp (r n) 2 P) {C : ℝ}
    (hC : ∀n, (∫ω,‖r n ω‖^2 ∂P) ≤ C) (hs : Summable (fun n => γ n^2)) :
    ∀ᵐ ω ∂P, SeriesConverges (fun n => γ n^2*‖r n ω‖^2) := by
  have hi n : Integrable (fun ω => ‖γ n • r n ω‖^2) P :=
    (memLp_two_iff_integrable_sq_norm ((h2 n).const_smul (γ n)).1).1 ((h2 n).const_smul (γ n))
  have hh := nonnegative_integral_series hi (fun n ω => sq_nonneg _) (weighted_energy_summable hC hs)
  simpa only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] using hh

variable [IsProbabilityMeasure P]

lemma weighted_scalar_series {r : ℕ → Ω → ℝ} {γ : ℕ → ℝ}
    (hm : ∀n,StronglyMeasurable[ℱ (n+1)] (r n))
    (h2 : ∀n, MemLp (r n) 2 P) (hz : ∀n,P[r n|ℱ n]=ᵐ[P] 0)
    {C : ℝ} (hC : ∀n, (∫ω,‖r n ω‖^2 ∂P) ≤ C) (hs : Summable (fun n => γ n^2)) :
    ∀ᵐ ω ∂P, SeriesConverges (fun n => γ n*r n ω) := by
  apply scalar_martingale_series (ℱ:=ℱ) (fun n => (hm n).const_mul (γ n))
    (fun n => (h2 n).const_mul (γ n))
  · intro n
    have hh := condExp_smul (μ:=P) (γ n) (r n) (ℱ n)
    change P[(fun ω => γ n*r n ω)|ℱ n] =ᵐ[P] _ at hh
    filter_upwards [hh,hz n] with ω hh hz
    simpa only [Pi.smul_apply,smul_eq_mul,hz,Pi.zero_apply,mul_zero] using hh
  · simpa only [Real.norm_eq_abs,smul_eq_mul,sq_abs] using weighted_energy_summable (γ:=γ) hC hs

lemma weighted_vector_series {d : ℕ} {r : ℕ → Ω → EuclideanSpace ℝ (Fin d)} {γ : ℕ → ℝ}
    (hm : ∀n,StronglyMeasurable[ℱ (n+1)] (r n))
    (h2 : ∀n, MemLp (r n) 2 P) (hz : ∀n,P[r n|ℱ n]=ᵐ[P] 0)
    {C : ℝ} (hC : ∀n, (∫ω,‖r n ω‖^2 ∂P) ≤ C) (hs : Summable (fun n => γ n^2)) :
    ∀ᵐ ω ∂P, SeriesConverges (fun n => γ n • r n ω) := by
  apply vector_martingale_series (ℱ:=ℱ) (fun n => (hm n).const_smul (γ n))
    (fun n => (h2 n).const_smul (γ n))
  · intro n
    have hh := condExp_smul (μ:=P) (γ n) (r n) (ℱ n)
    filter_upwards [hh,hz n] with ω hh hz
    simpa only [Pi.smul_apply,hz,Pi.zero_apply,smul_zero] using hh
  · exact weighted_energy_summable hC hs

end GradErrors.Stochastic.Proof
-- End WeightedSeries

-- Begin NoiseMoments

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace GradErrors.Stochastic.Proof

variable {Ω : Type*} [m0 : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℕ m0}

structure NoiseMoments {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℱ : Filtration ℕ m0) (P : Measure Ω) (r : ℕ → Ω → E) : Prop where
  measurable : ∀t, StronglyMeasurable[ℱ (t+1)] (r t)
  square : ∀t, MemLp (r t) 2 P
  mean : ∀t, P[r t|ℱ t] =ᵐ[P] 0
  bounded : ∃C:ℝ, ∀t, (∫ω,‖r t ω‖^2 ∂P) ≤ C

lemma bilinear_noise_moments {E F H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (B : F →L[ℝ] E →L[ℝ] H) {w : ℕ → Ω → E}
    (hw : ∀t,StronglyMeasurable[ℱ (t+1)] (w t))
    {b : ℕ → Ω → ℝ} (hb : ∀t,Measurable[ℱ t] (b t))
    (hvar : ∀t S, MeasurableSet[ℱ t] S → ∫⁻ ω in S, ‖w t ω‖ₑ^2 ∂P ≤
      ∫⁻ ω in S, ENNReal.ofReal (b t ω) ∂P)
    (hmean : ∀t S, MeasurableSet[ℱ t] S → (∫⁻ ω in S, ‖w t ω‖ₑ ∂P) < ⊤ →
      ∫ ω in S, w t ω ∂P = 0)
    {a : ℕ → Ω → F} (ha : ∀t,StronglyMeasurable[ℱ t] (a t))
    {q : ℕ → Ω → ℝ} (hq : ∀t,Measurable[ℱ t] (q t))
    (hr : ∀t ω, ‖B (a t ω) (w t ω)‖^2 ≤ ‖w t ω‖^2*q t ω^2)
    {C : ℝ} (hC0 : 0≤C) (hC : ∀t ω,b t ω*q t ω^2 ≤ C) :
    NoiseMoments ℱ P (fun t ω => B (a t ω) (w t ω)) := by
  have hm t : StronglyMeasurable[ℱ (t+1)] (fun ω => B (a t ω) (w t ω)) :=
    B.continuous₂.comp_stronglyMeasurable ((ha t).mono (ℱ.mono t.le_succ) |>.prodMk (hw t))
  have hh t := transformed_square_bound (ℱ.le t) ((hw t).mono (ℱ.le (t+1)))
    (hb t) (hvar t) (hq t) (hr t) (hC t)
  have h2 t := memLp_two_of_enorm_sq_bound ((hm t).mono (ℱ.le (t+1))).aestronglyMeasurable (hh t)
  refine ⟨hm,h2,?_,C,?_⟩
  · intro t
    exact noise_bilin_condExp_zero (ℱ.le t) B ((hw t).mono (ℱ.le (t+1)))
      (hb t) (hvar t) (hmean t) (ha t) ((h2 t).integrable (by norm_num))
  · intro t
    exact integral_sq_norm_le_of_enorm ((hm t).mono (ℱ.le (t+1))).aestronglyMeasurable hC0 (hh t)

lemma NoiseMoments.scalar_series {r : ℕ → Ω → ℝ} (h : NoiseMoments ℱ P r)
    {γ : ℕ → ℝ} (hs : Summable (fun t => γ t^2)) :
    ∀ᵐ ω ∂P, SeriesConverges (fun t => γ t*r t ω) := by
  obtain ⟨C,hC⟩ := h.bounded
  exact weighted_scalar_series h.measurable h.square h.mean hC hs

lemma NoiseMoments.vector_series {d : ℕ} {r : ℕ → Ω → EuclideanSpace ℝ (Fin d)}
    (h : NoiseMoments ℱ P r) {γ : ℕ → ℝ} (hs : Summable (fun t => γ t^2)) :
    ∀ᵐ ω ∂P, SeriesConverges (fun t => γ t • r t ω) := by
  obtain ⟨C,hC⟩ := h.bounded
  exact weighted_vector_series h.measurable h.square h.mean hC hs

omit [IsProbabilityMeasure P] in
lemma NoiseMoments.square_series {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℕ → Ω → E} (h : NoiseMoments ℱ P r)
    {γ : ℕ → ℝ} (hs : Summable (fun t => γ t^2)) :
    ∀ᵐ ω ∂P, SeriesConverges (fun t => γ t^2*‖r t ω‖^2) := by
  obtain ⟨C,hC⟩ := h.bounded
  exact weighted_nonnegative_series h.square hC hs

end GradErrors.Stochastic.Proof
-- End NoiseMoments

-- Begin SpecialNoise

open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped ENNReal
namespace GradErrors.Stochastic.Proof

variable {Ω E : Type*} [m0 : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℕ m0}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {w : ℕ → Ω → E} (hw : ∀t,StronglyMeasurable[ℱ (t+1)] (w t))
    {b : ℕ → Ω → ℝ} (hb : ∀t,Measurable[ℱ t] (b t))
    (hvar : ∀t S, MeasurableSet[ℱ t] S → ∫⁻ ω in S, ‖w t ω‖ₑ^2 ∂P ≤
      ∫⁻ ω in S, ENNReal.ofReal (b t ω) ∂P)
    (hmean : ∀t S, MeasurableSet[ℱ t] S → (∫⁻ ω in S, ‖w t ω‖ₑ ∂P) < ⊤ →
      ∫ ω in S, w t ω ∂P = 0)

include hw hb hvar hmean

lemma smul_noise_moments {a : ℕ → Ω → ℝ} (ha : ∀t,Measurable[ℱ t] (a t))
    {C : ℝ} (hC0 : 0≤C) (hC : ∀t ω,b t ω*(a t ω)^2 ≤ C) :
    NoiseMoments ℱ P (fun t ω => a t ω • w t ω) := by
  apply bilinear_noise_moments (ContinuousLinearMap.lsmul ℝ ℝ) hw hb hvar hmean
    (fun t => (ha t).stronglyMeasurable) ha _ hC0 hC
  intro t ω
  simp only [ContinuousLinearMap.lsmul_apply,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  exact le_of_eq (mul_comm _ _)

lemma inner_noise_moments {a : ℕ → Ω → E} (ha : ∀t,StronglyMeasurable[ℱ t] (a t))
    {C : ℝ} (hC0 : 0≤C) (hC : ∀t ω,b t ω*‖a t ω‖^2 ≤ C) :
    NoiseMoments ℱ P (fun t ω => ⟪a t ω,w t ω⟫_ℝ) := by
  apply bilinear_noise_moments (innerSL ℝ) hw hb hvar hmean ha
    (fun t => (ha t).norm.measurable) _ hC0 hC
  intro t ω
  change ‖⟪a t ω,w t ω⟫_ℝ‖^2 ≤ _
  have hi := norm_inner_le_norm (𝕜:=ℝ) (a t ω) (w t ω)
  have hh := mul_self_le_mul_self (norm_nonneg _) hi
  simpa only [← sq,mul_pow,mul_comm] using hh

end GradErrors.Stochastic.Proof
-- End SpecialNoise

-- Begin NormalizationBounds

namespace GradErrors.Stochastic.Proof

lemma normalized_variance {A δ G h : ℝ} (hA : 0≤A) (hd : 0<δ)
    (hG : δ≤G) (hh : 0≤h) (hg : h≤2*G) :
    A*(1+h^2)*(G⁻¹)^2 ≤ A*((δ⁻¹)^2+4) := by
  have hGp : 0<G := hd.trans_le hG
  have hsq : δ^2≤G^2 := by nlinarith
  have hi : (G⁻¹)^2≤(δ⁻¹)^2 := by
    simpa only [one_div, inv_pow] using
      div_le_div_of_nonneg_left zero_le_one (sq_pos_of_pos hd) hsq
  have hh2 : h^2*(G⁻¹)^2≤4 := by
    have hs : h^2≤4*G^2 := by nlinarith
    have ht := mul_le_mul_of_nonneg_right hs (sq_nonneg (G⁻¹))
    have he : 4*G^2*(G⁻¹)^2=4 := by field_simp
    rwa [he] at ht
  have he : A*(1+h^2)*(G⁻¹)^2 = A*((G⁻¹)^2+h^2*(G⁻¹)^2) := by ring
  rw [he]
  exact mul_le_mul_of_nonneg_left (add_le_add hi hh2) hA

lemma normalized_inner_variance {A δ G h : ℝ} (hA : 0≤A) (hd : 0<δ)
    (hG : δ≤G) (hh : 0≤h) (hg : h≤2*G) :
    A*(1+h^2)*(((G^2)⁻¹)*h)^2 ≤ 4*(A*((δ⁻¹)^2+4)) := by
  have hGp : 0<G := hd.trans_le hG
  have hsq : h^2*(G⁻¹)^2≤4 := by
    have hs : h^2≤4*G^2 := by nlinarith
    have ht := mul_le_mul_of_nonneg_right hs (sq_nonneg (G⁻¹))
    have he : 4*G^2*(G⁻¹)^2=4 := by field_simp
    rwa [he] at ht
  have he : A*(1+h^2)*(((G^2)⁻¹)*h)^2 =
      (A*(1+h^2)*(G⁻¹)^2)*(h^2*(G⁻¹)^2) := by rw [inv_pow]; ring
  rw [he]
  have hh := mul_le_mul (normalized_variance hA hd hG hh hg) hsq
    (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (by positivity : 0≤A*((δ⁻¹)^2+4))
  simpa only [mul_comm] using hh

lemma small_variance {A δ χ h : ℝ} (hA : 0≤A) (hd : 0<δ)
    (hh : 0≤h) (hc : χ=0 ∨ χ=1) (hs : χ=1 → h<δ) :
    A*(1+h^2)*χ^2 ≤ A*(1+δ^2) := by
  rcases hc with rfl | rfl
  · simp only [zero_pow (by omega : 2≠0),mul_zero]; positivity
  · have hs := hs rfl
    simp only [one_pow,mul_one]
    apply mul_le_mul_of_nonneg_left _ hA
    nlinarith

lemma small_inner_variance {A δ χ h : ℝ} (hA : 0≤A) (hd : 0<δ)
    (hh : 0≤h) (hc : χ=0 ∨ χ=1) (hs : χ=1 → h<δ) :
    A*(1+h^2)*(χ*h)^2 ≤ A*(1+δ^2)*δ^2 := by
  rcases hc with rfl | rfl
  · simp only [zero_mul,zero_pow (by omega : 2≠0),mul_zero]; positivity
  · have hs := hs rfl
    simp only [one_mul]
    apply mul_le_mul
    · apply mul_le_mul_of_nonneg_left _ hA; nlinarith
    · nlinarith
    · positivity
    · positivity

end GradErrors.Stochastic.Proof
-- End NormalizationBounds

-- Begin NormalizedNoise

open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped ENNReal
namespace GradErrors.Stochastic.Proof

lemma normalized_noise_limits {Ω : Type*} [m0 : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0) {d : ℕ}
    {g w : ℕ → Ω → EuclideanSpace ℝ (Fin d)}
    (hg : ∀t,StronglyMeasurable[ℱ t] (g t))
    (hw : ∀t,StronglyMeasurable[ℱ (t+1)] (w t))
    {A δ : ℝ} (hA : 0<A) (hd : 0<δ)
    (hvar : ∀t S, MeasurableSet[ℱ t] S → ∫⁻ ω in S, ‖w t ω‖ₑ^2 ∂P ≤
      ∫⁻ ω in S, ENNReal.ofReal (A*(1+‖g t ω‖^2)) ∂P)
    (hmean : ∀t S, MeasurableSet[ℱ t] S → (∫⁻ ω in S, ‖w t ω‖ₑ ∂P) < ⊤ →
      ∫ ω in S, w t ω ∂P = 0)
    {G χ : ℕ → Ω → ℝ} (hGm : ∀t,Measurable[ℱ t] (G t))
    (hχm : ∀t,Measurable[ℱ t] (χ t)) (hG : ∀t ω,δ≤G t ω)
    (hgG : ∀t ω,‖g t ω‖≤2*G t ω) (hχ : ∀t ω,χ t ω=0 ∨ χ t ω=1)
    (hsmall : ∀t ω,χ t ω=1 → ‖g t ω‖<δ)
    {γ : ℕ → ℝ} (hs : Summable (fun t => γ t^2)) :
    ∀ᵐ ω ∂P, NoiseLimits γ (fun t => g t ω) (fun t => w t ω)
      (fun t => G t ω) (fun t => χ t ω) := by
  let b : ℕ → Ω → ℝ := fun t ω => A*(1+‖g t ω‖^2)
  have hb t : Measurable[ℱ t] (b t) :=
    ((hg t).norm.measurable.pow_const 2 |>.const_add 1).const_mul A
  have hV : NoiseMoments ℱ P (fun t ω => (G t ω)⁻¹ • w t ω) := by
    apply smul_noise_moments hw hb hvar hmean (fun t => (hGm t).inv)
      (C:=A*((δ⁻¹)^2+4)) (by positivity)
    intro t ω
    exact normalized_variance hA.le hd (hG t ω) (norm_nonneg _) (hgG t ω)
  have hI : NoiseMoments ℱ P (fun t ω => ⟪((G t ω)^2)⁻¹ • g t ω,w t ω⟫_ℝ) := by
    apply inner_noise_moments hw hb hvar hmean
      (fun t => ((hGm t).pow_const 2 |>.inv).stronglyMeasurable.smul (hg t))
      (C:=4*(A*((δ⁻¹)^2+4))) (by positivity)
    intro t ω
    change b t ω * ‖((G t ω)^2)⁻¹ • g t ω‖^2 ≤ _
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (sq_nonneg (G t ω)))]
    exact normalized_inner_variance hA.le hd (hG t ω) (norm_nonneg _) (hgG t ω)
  have hSV : NoiseMoments ℱ P (fun t ω => χ t ω • w t ω) := by
    apply smul_noise_moments hw hb hvar hmean hχm (C:=A*(1+δ^2)) (by positivity)
    intro t ω
    exact small_variance hA.le hd (norm_nonneg _) (hχ t ω) (hsmall t ω)
  have hSI : NoiseMoments ℱ P (fun t ω => ⟪χ t ω • g t ω,w t ω⟫_ℝ) := by
    apply inner_noise_moments hw hb hvar hmean
      (fun t => (hχm t).stronglyMeasurable.smul (hg t)) (C:=A*(1+δ^2)*δ^2) (by positivity)
    intro t ω
    change b t ω * ‖χ t ω • g t ω‖^2 ≤ _
    simpa only [b,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] using
      small_inner_variance hA.le hd (norm_nonneg (g t ω)) (hχ t ω) (hsmall t ω)
  filter_upwards [hV.vector_series hs,hI.scalar_series hs,hSV.square_series hs,
    hSI.scalar_series hs,hV.square_series hs] with ω hV hI hSV hSI hVS
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa only [real_inner_smul_left,mul_left_comm,mul_assoc] using hSI
  · simpa only [div_eq_mul_inv,mul_smul] using hV
  · simpa only [real_inner_smul_left,div_eq_mul_inv,mul_left_comm,mul_assoc,mul_comm] using hI
  · simpa only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,div_eq_mul_inv,inv_pow,mul_assoc,mul_comm,mul_left_comm] using hVS
  · convert hSV using 1
    ext t
    rcases hχ t ω with hc | hc <;> simp [hc]

end GradErrors.Stochastic.Proof
-- End NormalizedNoise

-- Begin PrefixNoise

open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped ENNReal
namespace GradErrors.Stochastic.Proof

lemma NoiseLimits.drop {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {γ G χ : ℕ → ℝ} {g w : ℕ → E} (h : NoiseLimits γ g w G χ) (N : ℕ) :
    NoiseLimits (fun t => γ (N+t)) (fun t => g (N+t)) (fun t => w (N+t))
      (fun t => G (N+t)) (fun t => χ (N+t)) :=
  ⟨h.smallInner.drop N,h.scaledVector.drop N,h.scaledInner.drop N,
    h.scaledSquare.drop N,h.smallSquare.drop N⟩

lemma shifted_block_noise_limits {Ω : Type*} [m0 : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0) {d : ℕ}
    {g w : ℕ → Ω → EuclideanSpace ℝ (Fin d)}
    (hg : ∀t,StronglyMeasurable[ℱ t] (g t))
    (hw : ∀t,StronglyMeasurable[ℱ (t+1)] (w t))
    {A δ η : ℝ} (hA : 0<A) (hd : 0<δ)
    (hvar : ∀t S, MeasurableSet[ℱ t] S → ∫⁻ ω in S, ‖w t ω‖ₑ^2 ∂P ≤
      ∫⁻ ω in S, ENNReal.ofReal (A*(1+‖g t ω‖^2)) ∂P)
    (hmean : ∀t S, MeasurableSet[ℱ t] S → (∫⁻ ω in S, ‖w t ω‖ₑ ∂P) < ⊤ →
      ∫ ω in S, w t ω ∂P = 0)
    {γ : ℕ → ℝ} (hs : Summable (fun t => γ t^2)) (N : ℕ)
    (hγ : ∀t,γ (N+t)≤η) :
    ∀ᵐ ω ∂P, NoiseLimits (fun t => γ (N+t)) (fun t => g (N+t) ω)
      (fun t => w (N+t) ω)
      (scaleAt δ η (fun t => γ (N+t)) (fun t => ‖g (N+t) ω‖))
      (smallAt δ η (fun t => γ (N+t)) (fun t => ‖g (N+t) ω‖)) := by
  have hh := normalized_noise_limits P ℱ hg hw hA hd hvar hmean
    (prefixScale_measurable ℱ δ η γ g hg N)
    (prefixSmall_measurable ℱ δ η γ g hg N)
    (prefixScale_ge δ η γ g N)
    (prefixScale_bound hd.le g N hγ)
    (prefixSmall_binary δ η γ g N)
    (fun _ _ => prefixSmall_gradient) hs
  filter_upwards [hh] with ω hω
  have hh := hω.drop N
  simpa only [prefixScale_add,prefixSmall_add] using hh

end GradErrors.Stochastic.Proof
-- End PrefixNoise

-- Begin NativeAdapted

open MeasureTheory ProbabilityTheory
namespace GradErrors.Stochastic.Proof

lemma noise_stronglyMeasurable {Ω E : Type*} [m0 : MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (ℱ : Filtration ℕ m0)
    {x s w : ℕ → Ω → E} {γ : ℕ → ℝ} (hγ : ∀t,0<γ t)
    (hx : ∀t ω,x (t+1) ω=x t ω+γ t • (s t ω+w t ω))
    (hxm : ∀t,StronglyMeasurable[ℱ t] (x t))
    (hsm : ∀t,StronglyMeasurable[ℱ t] (s t)) (t : ℕ) :
    StronglyMeasurable[ℱ (t+1)] (w t) := by
  have he : w t = fun ω => (γ t)⁻¹ • (x (t+1) ω-x t ω)-s t ω := by
    ext ω
    rw [hx]
    simp [smul_add,smul_smul,(hγ t).ne']
  rw [he]
  exact (((hxm (t+1)).sub ((hxm t).mono (ℱ.mono t.le_succ))).const_smul _).sub
    ((hsm t).mono (ℱ.mono t.le_succ))

end GradErrors.Stochastic.Proof
-- End NativeAdapted

-- Begin Descent

open Set InnerProductSpace
open scoped NNReal
namespace GradErrors.Stochastic.Proof

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma smooth_descent {f : E → ℝ} (hf : Differentiable ℝ f)
    {L : ℝ≥0} (hL : LipschitzWith L (gradient f)) (x z : E) :
    f (x+z) ≤ f x + ⟪gradient f x,z⟫_ℝ + (L:ℝ)/2*‖z‖^2 := by
  let F : ℝ → ℝ := fun t => f (x+t • z)-t*⟪gradient f x,z⟫_ℝ-
    (L:ℝ)/2*t^2*‖z‖^2
  have hd (t : ℝ) : HasDerivAt F
      (⟪gradient f (x+t • z),z⟫_ℝ-⟪gradient f x,z⟫_ℝ-(L:ℝ)*t*‖z‖^2) t := by
    have hp : HasDerivAt (fun t : ℝ => x+t • z) z t := by
      simpa using (hasDerivAt_id t).smul_const z |>.const_add x
    have hf' := (hf (x+t • z)).hasFDerivAt.comp_hasDerivAt t hp
    rw [← inner_gradient_left] at hf'
    convert (hf'.sub ((hasDerivAt_id t).mul_const ⟪gradient f x,z⟫_ℝ)).sub
      ((((hasDerivAt_id t).pow 2).const_mul ((L:ℝ)/2)).mul_const (‖z‖^2)) using 1 <;> first | rfl | (simp only [id_eq]; ring)
  have hm : AntitoneOn F (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
      ((continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt).continuousOn)
      (fun t _ => (hd t).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hd t).deriv]
    have ht0 : 0≤t := (interior_subset ht).1
    have hn := hL.norm_sub_le (x+t • z) x
    simp only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht0] at hn
    have hi := real_inner_le_norm (gradient f (x+t • z)-gradient f x) z
    rw [inner_sub_left] at hi
    have hn' := mul_le_mul_of_nonneg_right hn (norm_nonneg z)
    nlinarith
  have hh := hm (show (0:ℝ)∈Set.Icc 0 1 by simp) (show (1:ℝ)∈Set.Icc 0 1 by simp) zero_le_one
  simp [F] at hh
  rw [inner_gradient_left]
  linarith

end GradErrors.Stochastic.Proof
-- End Descent

-- Begin OneStep

open InnerProductSpace
open scoped NNReal
namespace GradErrors.Stochastic.Proof

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma one_step_descent {f : E → ℝ} (hf : Differentiable ℝ f)
    {L : ℝ≥0} (hL : LipschitzWith L (gradient f)) {x s w : E}
    {γ c₁ c₂ : ℝ} (hγ : 0≤γ) (_hc₂ : 0≤c₂)
    (hs : ‖s‖≤c₂*(1+‖gradient f x‖))
    (hd : c₁*‖gradient f x‖^2 ≤ -⟪gradient f x,s⟫_ℝ)
    (hsmall : γ*(2*((L:ℝ)+1)*c₂^2) ≤ c₁/2) :
    f (x+γ • (s+w)) ≤ f x-γ*(c₁/2)*‖gradient f x‖^2+
      γ*⟪gradient f x,w⟫_ℝ+(2*((L:ℝ)+1)*c₂^2)*γ^2+
      ((L:ℝ)+1)*γ^2*‖w‖^2 := by
  have hbase := smooth_descent hf hL x (γ • (s+w))
  rw [inner_smul_right,inner_add_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg hγ,mul_pow] at hbase
  have hs2 : ‖s‖^2≤2*c₂^2*(1+‖gradient f x‖^2) := by
    have hh := mul_self_le_mul_self (norm_nonneg s) hs
    nlinarith [sq_nonneg (‖gradient f x‖-1),mul_nonneg (sq_nonneg c₂) (sq_nonneg (‖gradient f x‖-1))]
  have hsw : ‖s+w‖^2≤2*‖s‖^2+2*‖w‖^2 := by
    have hh := mul_self_le_mul_self (norm_nonneg (s+w)) (norm_add_le s w)
    nlinarith [sq_nonneg (‖s‖-‖w‖)]
  have hquad : (L:ℝ)/2*(γ^2*‖s+w‖^2) ≤
      ((L:ℝ)+1)*γ^2*(2*c₂^2*(1+‖gradient f x‖^2)+‖w‖^2) := by
    have h1 := mul_le_mul_of_nonneg_left hsw (show 0≤(L:ℝ)/2*γ^2 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hs2 (show 0≤(L:ℝ)*γ^2 by positivity)
    have h3 : 0≤γ^2*(2*c₂^2*(1+‖gradient f x‖^2)+‖w‖^2) := by positivity
    nlinarith
  have hd' := mul_le_mul_of_nonneg_left hd hγ
  have ha := mul_le_mul_of_nonneg_right hsmall (mul_nonneg hγ (sq_nonneg ‖gradient f x‖))
  nlinarith

end GradErrors.Stochastic.Proof
-- End OneStep

-- Begin TimeShift

open Filter Topology Finset
namespace GradErrors.Stochastic.Proof

lemma steps_tendsto_zero {γ : ℕ → ℝ} (hγ : ∀t,0≤γ t)
    (hs : Summable (fun t => γ t^2)) : Tendsto γ atTop (𝓝 0) := by
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hs.tendsto_atTop_zero
  simpa only [Function.comp_def,Real.sqrt_sq (hγ _),Real.sqrt_zero] using hh

lemma shifted_sum_atTop {γ : ℕ → ℝ}
    (hs : Tendsto (fun n => ∑i∈range n,γ i) atTop atTop) (N : ℕ) :
    Tendsto (fun n => ∑i∈range n,γ (N+i)) atTop atTop := by
  have hh := tendsto_atTop_add_const_right atTop (-(∑i∈range N,γ i))
    (hs.comp (tendsto_add_atTop_nat N))
  convert hh using 1
  ext n
  simp only [Function.comp_apply,← sub_eq_add_neg]
  rw [Nat.add_comm n N,← sum_Ico_eq_sub γ (Nat.le_add_right N n),sum_Ico_eq_sum_range,Nat.add_sub_cancel_left]

lemma shifted_summable {γ : ℕ → ℝ} (hs : Summable (fun t => γ t^2)) (N : ℕ) :
    Summable (fun t => γ (N+t)^2) := by
  exact hs.comp_injective (fun a b h => Nat.add_left_cancel h)

lemma tendsto_unshift {E : Type*} {f : ℕ → E} {l : Filter E} {N : ℕ}
    (h : Tendsto (fun t => f (N+t)) atTop l) : Tendsto f atTop l := by
  apply (tendsto_add_atTop_iff_nat N).mp
  simpa only [Nat.add_comm] using h

lemma eventually_unshift {p : ℕ → Prop} {N : ℕ}
    (h : ∀ᶠ t in atTop,p (N+t)) : ∀ᶠ t in atTop,p t := by
  obtain ⟨M,hM⟩ := eventually_atTop.mp h
  filter_upwards [eventually_ge_atTop (N+M)] with t ht
  have hh := hM (t-N) (by omega)
  simpa only [Nat.add_sub_of_le (by omega : N≤t)] using hh

end GradErrors.Stochastic.Proof
-- End TimeShift

-- Begin NativeThreshold

open Filter Topology NNReal ENNReal MeasureTheory ProbabilityTheory InnerProductSpace
namespace GradErrors.Stochastic.Proof

lemma native_threshold {n : ℕ} (hdet : DeterministicThreshold n) {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (L : ℝ≥0) (hL : LipschitzWith L (gradient f))
    (x s w : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (γ : ℕ → ℝ) (hγ : ∀ t, 0 < γ t)
    (hx : ∀ t ω, x (t + 1) ω = x t ω + γ t • (s t ω + w t ω))
    (hxm : ∀ t, StronglyMeasurable[ℱ t] (x t)) (hsm : ∀ t, StronglyMeasurable[ℱ t] (s t))
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (h41a : ∀ t ω, c₁ * ‖gradient f (x t ω)‖ ^ 2 ≤ -⟪gradient f (x t ω), s t ω⟫_ℝ)
    (h41b : ∀ t ω, ‖s t ω‖ ≤ c₂ * (1 + ‖gradient f (x t ω)‖))
    (A : ℝ) (hA : 0 < A)
    (h42 : ∀ t (S : Set Ω), MeasurableSet[ℱ t] S → ∫⁻ ω in S, ‖w t ω‖ₑ ∂P < ∞ →
      ∫ ω in S, w t ω ∂P = 0)
    (h43 : ∀ t (S : Set Ω), MeasurableSet[ℱ t] S →
      ∫⁻ ω in S, ‖w t ω‖ₑ ^ 2 ∂P ≤
        ∫⁻ ω in S, ENNReal.ofReal (A * (1 + ‖gradient f (x t ω)‖ ^ 2)) ∂P)
    (hsum : Tendsto (fun T => ∑ t ∈ Finset.range T, γ t) atTop atTop)
    (hsq : Summable (fun t => γ t ^ 2)) (δ : ℝ) (hd : 0<δ) :
    ∀ᵐ ω ∂P, Tendsto (fun t => f (x t ω)) atTop atBot ∨
      ∃l,Tendsto (fun t => f (x t ω)) atTop (𝓝 l) ∧
        ∀ᶠ t in atTop,‖gradient f (x t ω)‖<δ := by
  let ell : ℝ := (L:ℝ)+1
  let D : ℝ := 2*ell*c₂^2
  let K : ℝ := c₂*(1/δ+2)+1
  let eta : ℝ := (4*ell*K)⁻¹
  have hell : 0<ell := by dsimp [ell]; positivity
  have hD : 0≤D := by dsimp [D]; positivity
  have hK : 0<K := by dsimp [K]; positivity
  have heta : 0<eta := by dsimp [eta]; positivity
  have hchoice : ell*eta*(c₂*(1/δ+2)+1)≤1/4 := by
    have he : ell*eta*K=1/4 := by dsimp [eta]; field_simp
    exact he.le
  have hz := steps_tendsto_zero (fun t => (hγ t).le) hsq
  have hzD : Tendsto (fun t => γ t*D) atTop (𝓝 0) := by
    simpa only [zero_mul] using hz.mul_const D
  have hb := (hz.eventually (gt_mem_nhds (half_pos heta))).and
    (hzD.eventually (gt_mem_nhds (half_pos hc₁)))
  obtain ⟨N,hN⟩ := eventually_atTop.mp hb
  have hstep t : γ (N+t)≤eta/2 := (hN _ (Nat.le_add_right N t)).1.le
  have hg : ∀t,StronglyMeasurable[ℱ t] (fun ω => gradient f (x t ω)) :=
    fun t => hL.continuous.comp_stronglyMeasurable (hxm t)
  have hw := noise_stronglyMeasurable ℱ hγ hx hxm hsm
  have hn := shifted_block_noise_limits P ℱ hg hw hA hd h43 h42 hsq N
    (fun t => (hstep t).trans (by linarith : eta/2≤eta))
  filter_upwards [hn] with ω hnoise
  have hdif : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hy t : f (x (N+(t+1)) ω) ≤ f (x (N+t) ω)-
      (c₁/2)*γ (N+t)*‖gradient f (x (N+t) ω)‖^2+
      γ (N+t)*⟪gradient f (x (N+t) ω),w (N+t) ω⟫_ℝ+
      D*γ (N+t)^2+ell*γ (N+t)^2*‖w (N+t) ω‖^2 := by
    have hh := one_step_descent hdif hL (w:=w (N+t) ω) (hγ (N+t)).le hc₂.le (h41b (N+t) ω)
      (h41a (N+t) ω) (hN _ (Nat.le_add_right N t)).2.le
    rw [show N+(t+1)=(N+t)+1 by omega,hx]
    simpa only [D,ell,mul_comm (γ (N+t)) (c₁/2)] using hh
  have hh := hdet (fun t => γ (N+t)) (fun t => x (N+t) ω)
    (fun t => s (N+t) ω) (fun t => w (N+t) ω)
    (fun t => gradient f (x (N+t) ω)) (fun t => f (x (N+t) ω))
    δ eta (c₁/2) c₂ D ell hd heta (half_pos hc₁) hc₂.le hD hell
    (fun t => hγ (N+t)) hstep (shifted_sum_atTop hsum N) (shifted_summable hsq N)
    hchoice (fun t => by simpa only [Nat.add_assoc] using hx (N+t) ω)
    (fun t => h41b (N+t) ω)
    (fun i j => (hL.norm_sub_le _ _).trans (mul_le_mul_of_nonneg_right
      (show (L:ℝ)≤ell by dsimp [ell]; linarith) (norm_nonneg _))) hy hnoise
  rcases hh with hh | ⟨l,hl,hg⟩
  · exact Or.inl (tendsto_unshift hh)
  · exact Or.inr ⟨l,tendsto_unshift hl,eventually_unshift hg⟩

end GradErrors.Stochastic.Proof
-- End NativeThreshold

-- Begin ThresholdLimit

open Filter Topology
namespace GradErrors.Stochastic.Proof

lemma countable_threshold_dichotomy {E : Type*} [NormedAddCommGroup E]
    {y : ℕ → ℝ} {g : ℕ → E}
    (h : ∀k:ℕ,Tendsto y atTop atBot ∨
      ∃l,Tendsto y atTop (𝓝 l) ∧ ∀ᶠ t in atTop,‖g t‖<1/((k:ℝ)+1)) :
    Tendsto y atTop atBot ∨ (∃l,Tendsto y atTop (𝓝 l)) ∧ Tendsto g atTop (𝓝 0) := by
  by_cases hb : Tendsto y atTop atBot
  · exact Or.inl hb
  · have hh k := (h k).resolve_left hb
    refine Or.inr ⟨⟨(hh 0).choose,(hh 0).choose_spec.1⟩,?_⟩
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨k,hk⟩ := exists_nat_one_div_lt hε
    filter_upwards [(hh k).choose_spec.2] with t ht
    simpa only [dist_zero_right] using ht.trans hk

lemma cluster_stationary_of_dichotomy {E : Type*} [NormedAddCommGroup E]
    {x : ℕ → E} {f : E → ℝ} {g : E → E} (hf : Continuous f) (hg : Continuous g)
    (h : Tendsto (fun t => f (x t)) atTop atBot ∨
      (∃l,Tendsto (fun t => f (x t)) atTop (𝓝 l)) ∧
        Tendsto (fun t => g (x t)) atTop (𝓝 0)) :
    ∀xbar,MapClusterPt xbar atTop x → g xbar=0 := by
  intro xbar hx
  obtain ⟨φ,hφ,hxφ⟩ := hx.tendsto_subseq
  rcases h with h | h
  · have hh := hf.continuousAt.tendsto.comp hxφ
    have hb := h.comp hφ.tendsto_atTop
    exact False.elim (not_tendsto_nhds_of_tendsto_atBot hb (f xbar) hh)
  · have hh := hg.continuousAt.tendsto.comp hxφ
    have hzero := h.2.comp hφ.tendsto_atTop
    exact tendsto_nhds_unique hh hzero

end GradErrors.Stochastic.Proof
-- End ThresholdLimit

-- Begin NativeConclusion

open Filter Topology NNReal ENNReal MeasureTheory ProbabilityTheory InnerProductSpace
namespace GradErrors.Stochastic.Proof

theorem native_convergence_of_threshold {n : ℕ} (hdet : DeterministicThreshold n) {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (L : ℝ≥0) (hL : LipschitzWith L (gradient f))
    (x s w : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (γ : ℕ → ℝ) (hγ : ∀ t, 0 < γ t)
    (hx : ∀ t ω, x (t + 1) ω = x t ω + γ t • (s t ω + w t ω))
    (hxm : ∀ t, StronglyMeasurable[ℱ t] (x t)) (hsm : ∀ t, StronglyMeasurable[ℱ t] (s t))
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (h41a : ∀ t ω, c₁ * ‖gradient f (x t ω)‖ ^ 2 ≤ -⟪gradient f (x t ω), s t ω⟫_ℝ)
    (h41b : ∀ t ω, ‖s t ω‖ ≤ c₂ * (1 + ‖gradient f (x t ω)‖))
    (A : ℝ) (hA : 0 < A)
    (h42 : ∀ t (S : Set Ω), MeasurableSet[ℱ t] S → ∫⁻ ω in S, ‖w t ω‖ₑ ∂P < ∞ →
      ∫ ω in S, w t ω ∂P = 0)
    (h43 : ∀ t (S : Set Ω), MeasurableSet[ℱ t] S →
      ∫⁻ ω in S, ‖w t ω‖ₑ ^ 2 ∂P ≤
        ∫⁻ ω in S, ENNReal.ofReal (A * (1 + ‖gradient f (x t ω)‖ ^ 2)) ∂P)
    (hsum : Tendsto (fun T => ∑ t ∈ Finset.range T, γ t) atTop atTop)
    (hsq : Summable (fun t => γ t ^ 2)) :
    ∀ᵐ ω ∂P,
      (Tendsto (fun t => f (x t ω)) atTop atBot ∨
        ((∃ l : ℝ, Tendsto (fun t => f (x t ω)) atTop (𝓝 l)) ∧
          Tendsto (fun t => gradient f (x t ω)) atTop (𝓝 0))) ∧
      ∀ xbar, MapClusterPt xbar atTop (fun t => x t ω) → gradient f xbar = 0  := by
  have hh (k : ℕ) := native_threshold hdet P ℱ f hf L hL x s w γ hγ hx hxm hsm c₁ c₂ hc₁ hc₂ h41a h41b A hA h42 h43 hsum hsq (1/((k:ℝ)+1)) (by positivity)
  filter_upwards [ae_all_iff.mpr hh] with ω hω
  have hdich := countable_threshold_dichotomy hω
  exact ⟨hdich,cluster_stationary_of_dichotomy hf.continuous hL.continuous hdich⟩

end GradErrors.Stochastic.Proof
-- End NativeConclusion

-- Begin RootAssembly

open Filter Topology NNReal ENNReal MeasureTheory ProbabilityTheory InnerProductSpace

namespace GradErrors.Stochastic

theorem proposition_3 {n : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (L : ℝ≥0) (hL : LipschitzWith L (gradient f))
    (x s w : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (γ : ℕ → ℝ) (hγ : ∀ t, 0 < γ t)
    (hx : ∀ t ω, x (t + 1) ω = x t ω + γ t • (s t ω + w t ω))
    (hxm : ∀ t, StronglyMeasurable[ℱ t] (x t)) (hsm : ∀ t, StronglyMeasurable[ℱ t] (s t))
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (h41a : ∀ t ω, c₁ * ‖gradient f (x t ω)‖ ^ 2 ≤ -⟪gradient f (x t ω), s t ω⟫_ℝ)
    (h41b : ∀ t ω, ‖s t ω‖ ≤ c₂ * (1 + ‖gradient f (x t ω)‖))
    (A : ℝ) (hA : 0 < A)
    (h42 : ∀ t (S : Set Ω), MeasurableSet[ℱ t] S → ∫⁻ ω in S, ‖w t ω‖ₑ ∂P < ∞ →
      ∫ ω in S, w t ω ∂P = 0)
    (h43 : ∀ t (S : Set Ω), MeasurableSet[ℱ t] S →
      ∫⁻ ω in S, ‖w t ω‖ₑ ^ 2 ∂P ≤
        ∫⁻ ω in S, ENNReal.ofReal (A * (1 + ‖gradient f (x t ω)‖ ^ 2)) ∂P)
    (hsum : Tendsto (fun T => ∑ t ∈ Finset.range T, γ t) atTop atTop)
    (hsq : Summable (fun t => γ t ^ 2)) :
    ∀ᵐ ω ∂P,
      (Tendsto (fun t => f (x t ω)) atTop atBot ∨
        ((∃ l : ℝ, Tendsto (fun t => f (x t ω)) atTop (𝓝 l)) ∧
          Tendsto (fun t => gradient f (x t ω)) atTop (𝓝 0))) ∧
      ∀ xbar, MapClusterPt xbar atTop (fun t => x t ω) → gradient f xbar = 0 := by
  exact Proof.native_convergence_of_threshold (Proof.deterministic_threshold n) P ℱ f hf L hL x s w γ hγ hx hxm hsm c₁ c₂ hc₁ hc₂ h41a h41b A hA h42 h43 hsum hsq

end GradErrors.Stochastic
-- End RootAssembly

-- Begin Solution

open Filter Topology NNReal ENNReal MeasureTheory ProbabilityTheory InnerProductSpace

theorem solution {n : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (L : ℝ≥0) (hL : LipschitzWith L (gradient f))
    (x s w : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (γ : ℕ → ℝ) (hγ : ∀ t, 0 < γ t)
    (hx : ∀ t ω, x (t + 1) ω = x t ω + γ t • (s t ω + w t ω))
    (hxm : ∀ t, StronglyMeasurable[ℱ t] (x t)) (hsm : ∀ t, StronglyMeasurable[ℱ t] (s t))
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (h41a : ∀ t ω, c₁ * ‖gradient f (x t ω)‖ ^ 2 ≤ -⟪gradient f (x t ω), s t ω⟫_ℝ)
    (h41b : ∀ t ω, ‖s t ω‖ ≤ c₂ * (1 + ‖gradient f (x t ω)‖))
    (A : ℝ) (hA : 0 < A)
    (h42 : ∀ t (S : Set Ω), MeasurableSet[ℱ t] S → ∫⁻ ω in S, ‖w t ω‖ₑ ∂P < ∞ →
      ∫ ω in S, w t ω ∂P = 0)
    (h43 : ∀ t (S : Set Ω), MeasurableSet[ℱ t] S →
      ∫⁻ ω in S, ‖w t ω‖ₑ ^ 2 ∂P ≤
        ∫⁻ ω in S, ENNReal.ofReal (A * (1 + ‖gradient f (x t ω)‖ ^ 2)) ∂P)
    (hsum : Tendsto (fun T => ∑ t ∈ Finset.range T, γ t) atTop atTop)
    (hsq : Summable (fun t => γ t ^ 2)) :
    ∀ᵐ ω ∂P,
      (Tendsto (fun t => f (x t ω)) atTop atBot ∨
        ((∃ l : ℝ, Tendsto (fun t => f (x t ω)) atTop (𝓝 l)) ∧
          Tendsto (fun t => gradient f (x t ω)) atTop (𝓝 0))) ∧
      ∀ xbar, MapClusterPt xbar atTop (fun t => x t ω) → gradient f xbar = 0 := by
  exact GradErrors.Stochastic.proposition_3 P ℱ f hf L hL x s w γ hγ hx hxm hsm c₁ c₂ hc₁ hc₂ h41a h41b A hA h42 h43 hsum hsq
-- End Solution
