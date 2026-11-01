-- Prove2me | solution 1 for NashFlowLT.SteadyState.dual_feasible_phi_le
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T09:30:07.27529+00:00
-- url     : https://prove2.me/submissions/25e42b2b-18ca-4034-8742-6b9359bc5914

import Mathlib
import Definitions.Def_NashFlowLT_SteadyState_Model

open NashFlowLT.SteadyState MeasureTheory Set Finset

namespace P2MNFLTDual

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

lemma bellman (N : Network V E) (hN : N.Standing) (F : FlowOverTime V E)
    (hF : IsFlowOverTime N F) (e : E) (θ : ℝ) (hθ : 0 ≤ θ) :
    ell N F (N.head e) θ ≤ exitTime N F e (ell N F (N.tail e) θ) := by
  obtain ⟨p, hp, hpe⟩ := (ell_spec N hN F (N.tail e) θ).1
  have hpt0 : 0 ≤ pathTime N F p θ := hθ.trans (pathTime_ge N hN F hF p θ hθ)
  by_cases hw : N.head e ∈ walkNodes N N.s p
  · obtain ⟨p1, p2, hpp, hw1, hnd1⟩ := path_prefix N p N.s (N.tail e) hp.1 hp.2 _ hw
    have h1 := (ell_spec N hN F (N.head e) θ).2 p1 ⟨hw1, hnd1⟩
    have h2 : pathTime N F p1 θ ≤ pathTime N F p θ := by
      rw [hpp, pathTime_append]
      exact pathTime_ge N hN F hF p2 _ (hθ.trans (pathTime_ge N hN F hF p1 θ hθ))
    have h3 := exitTime_ge N hN F hF e (ell N F (N.tail e) θ) (by rw [hpe]; exact hpt0)
    rw [hpe] at h3 ⊢
    linarith
  · have hpath : IsPath N N.s (N.head e) (p ++ [e]) := by
      refine ⟨isWalk_append_single N _ _ p e hp.1 rfl, ?_⟩
      rw [walkNodes_append_single, List.nodup_append]
      refine ⟨hp.2, by simp, ?_⟩
      intro a ha b hb hab
      simp only [List.mem_singleton] at hb
      subst hb; subst hab; exact hw ha
    have h1 := (ell_spec N hN F (N.head e) θ).2 _ hpath
    rw [pathTime_append] at h1
    rw [hpe]
    simpa [pathTime] using h1

end P2MNFLTDual

open P2MNFLTDual in
theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (N : Network V E) (hN : N.Standing) (F : FlowOverTime V E)
    (hF : IsDynamicEquilibrium N F) (θ : ℝ) (hθ : 0 ≤ θ) :
    IsDualFeasible N (fun v => ell N F v θ - ell N F N.s θ)
        (fun e => F.z e (ell N F (N.tail e) θ) / N.nu e) ∧
      ∀ y : E → ℝ, IsPrimalFeasible N y → Phi N F θ ≤ ∑ e, N.tau e * y e := by
  have hFO := hF.1
  set d : V → ℝ := fun v => ell N F v θ - ell N F N.s θ with hd
  set q : E → ℝ := fun e => F.z e (ell N F (N.tail e) θ) / N.nu e with hq
  have hq0 : ∀ e, 0 ≤ q e := fun e =>
    div_nonneg (hFO.2.2.2.1 e _ (hθ.trans (ell_ge N hN F hFO _ θ hθ))).1 (hN.1 e).le
  have hdual : ∀ e, d (N.head e) ≤ d (N.tail e) + N.tau e + q e := by
    intro e
    have := bellman N hN F hFO e θ hθ
    simp only [exitTime] at this
    simp only [d, q]
    linarith
  refine ⟨⟨by simp [d], hdual, hq0⟩, ?_⟩
  intro y hy
  obtain ⟨hflow, hy0⟩ := hy
  have hst := hN.2.2.2.1
  -- telescoping: ∑_e (d tail - d head) y_e = u0 (d s - d t)
  have hfib : ∀ g : E → V, ∑ e, d (g e) * y e = ∑ v, d v * ∑ e ∈ univ.filter (fun e => g e = v), y e := by
    intro g
    rw [← Finset.sum_fiberwise univ g (fun e => d (g e) * y e)]
    apply Finset.sum_congr rfl
    intro v _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [(Finset.mem_filter.1 he).2]
  have htel : ∑ e, d (N.tail e) * y e - ∑ e, d (N.head e) * y e = N.u0 * d N.s - N.u0 * d N.t := by
    rw [hfib N.tail, hfib N.head, ← Finset.sum_sub_distrib]
    simp_rw [← mul_sub]
    simp_rw [hflow _]
    rw [Fintype.sum_eq_add N.s N.t hst]
    · simp [hst.symm]; ring
    · intro v ⟨h1, h2⟩; simp [h1, h2]
  have hds : d N.s = 0 := by simp [d]
  have h1 : ∑ e, (d (N.head e) - d (N.tail e) - q e) * y e ≤ ∑ e, N.tau e * y e := by
    apply Finset.sum_le_sum; intro e _
    apply mul_le_mul_of_nonneg_right _ (hy0 e).1
    linarith [hdual e]
  have h2 : ∑ e, q e * y e ≤ ∑ e, N.nu e * q e := by
    apply Finset.sum_le_sum; intro e _
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hy0 e).2 (hq0 e)
  have h3 : ∑ e, (d (N.head e) - d (N.tail e) - q e) * y e =
      (∑ e, d (N.head e) * y e - ∑ e, d (N.tail e) * y e) - ∑ e, q e * y e := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intros; ring
  have h4 : Phi N F θ = N.u0 * d N.t - ∑ e, N.nu e * q e := by
    simp only [Phi, d, q]
    congr 1
    apply Finset.sum_congr rfl; intro e _
    field_simp [(hN.1 e).ne']
  rw [h4]
  linarith
