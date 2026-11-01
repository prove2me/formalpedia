-- Prove2me | solution 1 for NashFlowLT.SteadyState.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T09:34:34.960371+00:00
-- url     : https://prove2.me/submissions/0fe95c35-50fe-47d1-b9da-f46add59eb1d

import Mathlib
import Definitions.Def_NashFlowLT_SteadyState_Model
import Theorems.Thm_NashFlowLT_SteadyState_queue_identity

open NashFlowLT.SteadyState MeasureTheory Set Finset Filter Topology

namespace P2MNFLTLemma1

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

lemma pathTime_append (N : Network V E) (F : FlowOverTime V E) (p q : List E) (x : ℝ) :
    pathTime N F (p ++ q) x = pathTime N F q (pathTime N F p x) := by
  induction p generalizing x with
  | nil => rfl
  | cons e p ih => simp only [List.cons_append, pathTime]; exact ih _

lemma exitTime_ge (N : Network V E) (hN : N.Standing) (F : FlowOverTime V E)
    (hF : IsFlowOverTime N F) (e : E) (x : ℝ) (hx : 0 ≤ x) : x ≤ exitTime N F e x := by
  have hz := (hF.2.2.2.1 e x hx).1
  have hnu := hN.1 e
  have htau := hN.2.1 e
  unfold exitTime
  have : 0 ≤ F.z e x / N.nu e := div_nonneg hz hnu.le
  linarith

lemma pathTime_ge (N : Network V E) (hN : N.Standing) (F : FlowOverTime V E)
    (hF : IsFlowOverTime N F) (p : List E) (x : ℝ) (hx : 0 ≤ x) : x ≤ pathTime N F p x := by
  induction p generalizing x with
  | nil => exact le_rfl
  | cons e p ih =>
    simp only [pathTime]
    have h1 := exitTime_ge N hN F hF e x hx
    exact h1.trans (ih _ (hx.trans h1))

lemma walkNodes_length (N : Network V E) (v : V) (p : List E) :
    (walkNodes N v p).length = p.length + 1 := by
  induction p generalizing v with
  | nil => rfl
  | cons e p ih => simp [walkNodes, ih]

lemma walkNodes_append_single (N : Network V E) (x : V) (p : List E) (e : E) :
    walkNodes N x (p ++ [e]) = walkNodes N x p ++ [N.head e] := by
  induction p generalizing x with
  | nil => rfl
  | cons e' p ih => simp [walkNodes, ih]

lemma isWalk_append_single (N : Network V E) (x v : V) (p : List E) (e : E)
    (hp : IsWalk N x v p) (he : N.tail e = v) : IsWalk N x (N.head e) (p ++ [e]) := by
  induction p generalizing x with
  | nil =>
    simp only [IsWalk] at hp
    subst hp
    simp [IsWalk, he]
  | cons e' p ih =>
    simp only [IsWalk] at hp
    simp only [List.cons_append, IsWalk]
    exact ⟨hp.1, ih _ hp.2⟩

lemma walkNodes_head (N : Network V E) (x : V) (p : List E) :
    ∃ l, walkNodes N x p = x :: l := by
  cases p with
  | nil => exact ⟨[], rfl⟩
  | cons e p => exact ⟨_, rfl⟩

lemma walkNodes_sublist (N : Network V E) (x : V) (p1 p2 : List E) :
    (walkNodes N x p1).Sublist (walkNodes N x (p1 ++ p2)) := by
  induction p1 generalizing x with
  | nil =>
    obtain ⟨l, hl⟩ := walkNodes_head N x p2
    simp only [walkNodes, List.nil_append, hl]
    exact List.Sublist.cons₂ _ (List.nil_sublist _)
  | cons e p ih =>
    simp only [walkNodes, List.cons_append]
    exact List.Sublist.cons₂ _ (ih _)

lemma path_prefix (N : Network V E) (p : List E) :
    ∀ a b : V, IsWalk N a b p → (walkNodes N a p).Nodup → ∀ w ∈ walkNodes N a p,
      ∃ p1 p2, p = p1 ++ p2 ∧ IsWalk N a w p1 ∧ (walkNodes N a p1).Nodup := by
  induction p with
  | nil =>
    intro a b _ _ w hw
    simp [walkNodes] at hw
    subst hw
    exact ⟨[], [], rfl, rfl, by simp [walkNodes]⟩
  | cons e p ih =>
    intro a b hwk hnd w hw
    simp only [IsWalk] at hwk
    simp only [walkNodes, List.mem_cons] at hw
    rcases hw with hw | hw
    · subst hw
      exact ⟨[], e :: p, rfl, rfl, by simp [walkNodes]⟩
    · simp only [walkNodes, List.nodup_cons] at hnd
      obtain ⟨p1, p2, hp, hw1, hnd1⟩ := ih _ _ hwk.2 hnd.2 w hw
      refine ⟨e :: p1, p2, by rw [hp]; rfl, ⟨hwk.1, hw1⟩, ?_⟩
      simp only [walkNodes, List.nodup_cons]
      refine ⟨fun hmem => hnd.1 ?_, hnd1⟩
      rw [hp]
      exact (walkNodes_sublist N _ p1 p2).subset hmem

lemma paths_finite (N : Network V E) (v : V) :
    {p : List E | IsPath N N.s v p}.Finite := by
  apply (List.finite_length_le E (Fintype.card V)).subset
  intro p hp
  have h1 := hp.2.length_le_card
  rw [walkNodes_length] at h1
  simp only [Set.mem_setOf_eq]
  omega

lemma ell_spec (N : Network V E) (hN : N.Standing) (F : FlowOverTime V E) (v : V) (θ : ℝ) :
    (∃ p, IsPath N N.s v p ∧ ell N F v θ = pathTime N F p θ) ∧
      ∀ p, IsPath N N.s v p → ell N F v θ ≤ pathTime N F p θ := by
  set S := {r | ∃ p, IsPath N N.s v p ∧ r = pathTime N F p θ} with hS
  have hfin : S.Finite := by
    have : S = (fun p => pathTime N F p θ) '' {p : List E | IsPath N N.s v p} := by
      ext r; simp [S, eq_comm]
    rw [this]; exact (paths_finite N v).image _
  obtain ⟨p0, hp0⟩ := hN.2.2.2.2 v
  have hne : S.Nonempty := ⟨_, p0, hp0, rfl⟩
  refine ⟨?_, fun p hp => csInf_le hfin.bddBelow ⟨p, hp, rfl⟩⟩
  obtain ⟨p, hp, hr⟩ := hne.csInf_mem hfin
  exact ⟨p, hp, hr⟩

lemma ell_ge (N : Network V E) (hN : N.Standing) (F : FlowOverTime V E)
    (hF : IsFlowOverTime N F) (v : V) (θ : ℝ) (hθ : 0 ≤ θ) : θ ≤ ell N F v θ := by
  obtain ⟨p, _, hp⟩ := (ell_spec N hN F v θ).1
  rw [hp]; exact pathTime_ge N hN F hF p θ hθ


/-- With frozen queues after `θ₀`, path exit times are translations. -/
lemma pathTime_frozen (N : Network V E) (hN : N.Standing) (F : FlowOverTime V E)
    (hF : IsFlowOverTime N F) (θ₀ : ℝ) (hθ₀ : 0 ≤ θ₀)
    (hz : ∀ e θ, θ₀ ≤ θ → F.z e θ = F.z e θ₀) (p : List E) (x : ℝ) (hx : θ₀ ≤ x) :
    pathTime N F p x = pathTime N F p θ₀ + (x - θ₀) := by
  induction p generalizing x θ₀ with
  | nil => simp [pathTime]
  | cons e p ih =>
    simp only [pathTime]
    have h1 : exitTime N F e x = exitTime N F e θ₀ + (x - θ₀) := by
      simp only [exitTime, hz e x hx]; ring
    have hge : θ₀ ≤ exitTime N F e θ₀ := exitTime_ge N hN F hF e θ₀ hθ₀
    have hz' : ∀ e' θ, exitTime N F e θ₀ ≤ θ → F.z e' θ = F.z e' (exitTime N F e θ₀) := by
      intro e' θ hθ
      rw [hz e' θ (hge.trans hθ), hz e' _ hge]
    rw [h1, ih (exitTime N F e θ₀) (hθ₀.trans hge) hz' _ (by linarith)]
    rw [ih (exitTime N F e θ₀) (hθ₀.trans hge) hz' _ le_rfl]
    ring

lemma ell_frozen (N : Network V E) (hN : N.Standing) (F : FlowOverTime V E)
    (hF : IsFlowOverTime N F) (θ₀ : ℝ) (hθ₀ : 0 ≤ θ₀)
    (hz : ∀ e θ, θ₀ ≤ θ → F.z e θ = F.z e θ₀) (v : V) (x : ℝ) (hx : θ₀ ≤ x) :
    ell N F v x = ell N F v θ₀ + (x - θ₀) := by
  obtain ⟨p, hp, hpx⟩ := (ell_spec N hN F v x).1
  obtain ⟨q, hq, hqx⟩ := (ell_spec N hN F v θ₀).1
  have h1 := (ell_spec N hN F v x).2 q hq
  have h2 := (ell_spec N hN F v θ₀).2 p hp
  rw [pathTime_frozen N hN F hF θ₀ hθ₀ hz q x hx] at h1
  rw [hpx, pathTime_frozen N hN F hF θ₀ hθ₀ hz p x hx] at *
  apply le_antisymm
  · rw [← hqx] at h1; linarith
  · linarith

end P2MNFLTLemma1

open P2MNFLTLemma1 in
theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (N : Network V E) (hN : N.Standing) (F : FlowOverTime V E)
    (hF : IsDynamicEquilibrium N F) :
    AttainsSteadyState N F ↔
      ∃ θs : ℝ, 0 ≤ θs ∧ ∀ v θ, θs < θ → HasDerivAt (ell N F v) 1 θ := by
  have hFO := hF.1
  constructor
  · rintro ⟨θ₀, hθ₀, hz⟩
    refine ⟨θ₀, hθ₀, fun v θ hθ => ?_⟩
    have hA : HasDerivAt (fun x => ell N F v θ₀ + (x - θ₀)) 1 θ := by
      simpa using ((hasDerivAt_id θ).sub_const θ₀).const_add (ell N F v θ₀)
    apply hA.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hθ] with x hx
    exact ell_frozen N hN F hFO θ₀ hθ₀ hz v x (le_of_lt hx)
  · rintro ⟨θs, hθs, hd⟩
    -- labels are translations after `θs`
    set d : V → ℝ := fun v => ell N F v (θs + 1) - (θs + 1) with hddef
    have hlin : ∀ v θ, θs < θ → ell N F v θ = θ + d v := by
      intro v θ hθ
      have key : ∀ a b, θs < a → a < b → ell N F v b - b = ell N F v a - a := by
        intro a b ha hab
        have hcont : ContinuousOn (fun x => ell N F v x - x) (Icc a b) := by
          intro x hx
          exact ((hd v x (by linarith [hx.1])).continuousAt.sub continuousAt_id).continuousWithinAt
        obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope (fun x => ell N F v x - x) (fun _ => 0)
          hab hcont (fun x hx => by
            have h := (hd v x (by linarith [hx.1])).sub (hasDerivAt_id x)
            rw [sub_self] at h
            exact h)
        have hba : b - a ≠ 0 := by linarith
        field_simp at hc'
        linarith
      simp only [d]
      rcases lt_trichotomy θ (θs + 1) with h | h | h
      · linarith [key θ (θs + 1) hθ h]
      · subst h; ring
      · linarith [key (θs + 1) θ (by linarith) h]
    have hq := queue_identity N hN F hF
    set θ₀ := θs + 1 + ∑ v, |d v| with hθ₀
    have hdle : ∀ v, d v ≤ ∑ v, |d v| := fun v =>
      (le_abs_self _).trans (Finset.single_le_sum (fun i _ => abs_nonneg (d i)) (Finset.mem_univ v))
    have hdge : ∀ v, -(∑ v, |d v|) ≤ d v := fun v => by
      have := (neg_abs_le (d v)); linarith [(Finset.single_le_sum (fun i _ => abs_nonneg (d i)) (Finset.mem_univ v) : |d v| ≤ ∑ v, |d v|)]
    have hsum0 : 0 ≤ ∑ v, |d v| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
    have hzval : ∀ e x, θ₀ ≤ x →
        F.z e x = N.nu e * max (d (N.head e) - d (N.tail e) - N.tau e) 0 := by
      intro e x hx
      have hθ1 : θs < x - d (N.tail e) := by linarith [hdle (N.tail e)]
      have h1 := hq e (x - d (N.tail e)) (by linarith)
      rw [hlin _ _ hθ1, hlin _ _ hθ1, sub_add_cancel] at h1
      rw [h1]; congr 2; ring
    refine ⟨θ₀, by linarith, fun e θ hθ => ?_⟩
    rw [hzval e θ hθ, hzval e θ₀ le_rfl]
