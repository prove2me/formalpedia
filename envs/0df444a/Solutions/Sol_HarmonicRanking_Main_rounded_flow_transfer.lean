-- Prove2me | solution 1 for HarmonicRanking.Main.rounded_flow_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T05:49:58.670376+00:00
-- url     : https://prove2.me/submissions/6cdd727a-ed93-46a8-8229-cee8f26a2a2e

import Mathlib
import Definitions.Def_HarmonicRanking_Main_ExplicitScore
import Theorems.Thm_AppliedComb_Flows_max_flow_min_cut

set_option autoImplicit false
open AppliedComb.Flows HarmonicRanking.Main
open Classical

namespace HRGen

variable {V A : Type*} [Fintype V] [Fintype A]

def adjS (G : CombOpt.MinCostFlow.Digraph V A) : V ⊕ A → V ⊕ A → Prop
  | .inl v, .inr a => G.tail a = v
  | .inr a, .inl v => G.head a = v
  | _, _ => False

noncomputable def capS (c : A → ℝ) : V ⊕ A → V ⊕ A → ℝ
  | .inl _, .inr a => c a
  | .inr a, .inl _ => c a
  | _, _ => 0

noncomputable def splitNet (N : ArcNetwork V A) (hs : N.source ≠ N.sink)
    (hcap : ∀ e, 0 ≤ N.capacity e) (hin : ∀ e, N.graph.head e ≠ N.source)
    (hout : ∀ e, N.graph.tail e ≠ N.sink) (hl : ∀ e, N.graph.tail e ≠ N.graph.head e) :
    Network (V ⊕ A) where
  adj := adjS N.graph
  S := .inl N.source
  T := .inl N.sink
  cap := capS N.capacity
  source_ne_sink := by simpa using hs
  oriented := by
    intro x y h h'
    rcases x with v | a <;> rcases y with w | b <;> simp [adjS] at h h'
    · exact hl _ (h.trans h'.symm)
    · exact hl _ (h'.trans h.symm)
  no_edge_into_source := by
    intro x h
    rcases x with v | a <;> simp [adjS] at h
    exact hin a h
  no_edge_out_of_sink := by
    intro y h
    rcases y with v | a <;> simp [adjS] at h
    exact hout a h
  cap_nonneg := by
    intro x y _
    rcases x with v | a <;> rcases y with w | b <;> simp [capS, hcap]

section
variable (N : ArcNetwork V A) (hs : N.source ≠ N.sink)
    (hcap : ∀ e, 0 ≤ N.capacity e) (hin : ∀ e, N.graph.head e ≠ N.source)
    (hout : ∀ e, N.graph.tail e ≠ N.sink) (hl : ∀ e, N.graph.tail e ≠ N.graph.head e)

noncomputable def phiOf (G : CombOpt.MinCostFlow.Digraph V A) (f : A → ℝ) : V ⊕ A → V ⊕ A → ℝ
  | .inl v, .inr a => if G.tail a = v then f a else 0
  | .inr a, .inl v => if G.head a = v then f a else 0
  | _, _ => 0

include hs hcap hin hout hl

theorem total_div (f : A → ℝ) :
    ∑ v, divergence N f v = 0 := by
  classical
  unfold divergence
  rw [Finset.sum_sub_distrib]
  have h1 : ∀ g : A → V, ∑ v, ∑ e, (if g e = v then f e else 0) = ∑ e, f e := by
    intro g
    rw [Finset.sum_comm]
    simp
  rw [h1, h1]; simp

theorem flow_to_split (f : A → ℝ) (hf : FeasibleFlow N f) :
    (splitNet N hs hcap hin hout hl).IsFlow (phiOf N.graph f) ∧
    (splitNet N hs hcap hin hout hl).value (phiOf N.graph f) = flowValue N f := by
  classical
  have hdiv : ∀ v, divergence N f v = (∑ e, if N.graph.tail e = v then f e else 0) -
      ∑ e, if N.graph.head e = v then f e else 0 := by
    intro v; rfl
  have hsrc : flowValue N f = ∑ e, if N.graph.tail e = N.source then f e else 0 := by
    unfold flowValue; rw [hdiv]
    have : ∀ e, (if N.graph.head e = N.source then f e else 0) = 0 := by
      intro e; simp [hin e]
    simp [this]
  have hsnk : divergence N f N.sink = - ∑ e, if N.graph.head e = N.sink then f e else 0 := by
    rw [hdiv]
    have : ∀ e, (if N.graph.tail e = N.sink then f e else 0) = 0 := by
      intro e; simp [hout e]
    simp [this]
  have hT := total_div N hs hcap hin hout hl f
  have hsum : ∑ v, divergence N f v = divergence N f N.source + divergence N f N.sink := by
    rw [Finset.sum_eq_add_of_mem N.source N.sink (Finset.mem_univ _) (Finset.mem_univ _) hs]
    intro v _ hv
    exact hf.2 v hv.1 hv.2
  have hlaw : (∑ e, if N.graph.tail e = N.source then f e else 0) =
      ∑ e, if N.graph.head e = N.sink then f e else 0 := by
    have : divergence N f N.source = ∑ e, if N.graph.tail e = N.source then f e else 0 := by
      have := hsrc; unfold flowValue at this; exact this
    linarith
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x y hxy
    rcases x with v | a <;> rcases y with w | b <;> simp [splitNet, adjS] at hxy
    · subst hxy
      simp only [phiOf, splitNet, capS, if_true]
      exact hf.1 b
    · subst hxy
      simp only [phiOf, splitNet, capS, if_true]
      exact hf.1 a
  · intro x y hxy
    rcases x with v | a <;> rcases y with w | b <;> simp [splitNet, adjS, phiOf] at hxy ⊢
    · intro h; exact (hxy h).elim
    · intro h; exact (hxy h).elim
  · simp only [splitNet, Fintype.sum_sum_type, phiOf]
    simpa using hlaw
  · intro y hy1 hy2
    simp only [splitNet] at hy1 hy2
    rcases y with v | a
    · have hv1 : v ≠ N.source := fun h => hy1 (by rw [h])
      have hv2 : v ≠ N.sink := fun h => hy2 (by rw [h])
      have := hf.2 v hv1 hv2
      rw [hdiv] at this
      simp only [Fintype.sum_sum_type, phiOf, Finset.sum_const_zero, zero_add]
      linarith
    · simp only [Fintype.sum_sum_type, phiOf, Finset.sum_const_zero, zero_add, add_zero]
      simp
  · simp only [Network.value, splitNet, Fintype.sum_sum_type, phiOf, Finset.sum_const_zero,
      zero_add]
    exact hsrc.symm

theorem split_to_flow (ϕ : V ⊕ A → V ⊕ A → ℝ) (hϕ : (splitNet N hs hcap hin hout hl).IsFlow ϕ) :
    FeasibleFlow N (fun a => ϕ (.inr a) (.inl (N.graph.head a))) ∧
    flowValue N (fun a => ϕ (.inr a) (.inl (N.graph.head a))) =
      (splitNet N hs hcap hin hout hl).value ϕ := by
  classical
  obtain ⟨h1, h2, h3, h4⟩ := hϕ
  have hnz : ∀ x y, ¬ adjS N.graph x y → ϕ x y = 0 := h2
  have key : ∀ a, ϕ (.inl (N.graph.tail a)) (.inr a) = ϕ (.inr a) (.inl (N.graph.head a)) := by
    intro a
    have := h4 (.inr a) (by simp [splitNet]) (by simp [splitNet])
    simp only [Fintype.sum_sum_type] at this
    have e1 : ∑ w, ϕ (.inl w) (.inr a) = ϕ (.inl (N.graph.tail a)) (.inr a) := by
      rw [Finset.sum_eq_single (N.graph.tail a)]
      · intro w _ hw
        exact hnz _ _ (by simp only [adjS]; exact fun h => hw h.symm)
      · simp
    have e2 : ∑ w, ϕ (.inr a) (.inl w) = ϕ (.inr a) (.inl (N.graph.head a)) := by
      rw [Finset.sum_eq_single (N.graph.head a)]
      · intro w _ hw
        exact hnz _ _ (by simpa [adjS, eq_comm] using hw)
      · simp
    have e3 : ∑ b, ϕ (.inr b) (.inr a) = 0 := Finset.sum_eq_zero (fun b _ => hnz _ _ (by simp [adjS]))
    have e4 : ∑ b, ϕ (.inr a) (.inr b) = 0 := Finset.sum_eq_zero (fun b _ => hnz _ _ (by simp [adjS]))
    linarith
  have hrow : ∀ v, ∑ x, ϕ (.inl v) x = ∑ a, if N.graph.tail a = v then
      ϕ (.inr a) (.inl (N.graph.head a)) else 0 := by
    intro v
    rw [Fintype.sum_sum_type]
    have e0 : ∑ w, ϕ (.inl v) (.inl w) = 0 :=
      Finset.sum_eq_zero (fun w _ => hnz _ _ (by simp [adjS]))
    rw [e0, zero_add]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    by_cases h : N.graph.tail a = v
    · subst h; simp [key a]
    · rw [if_neg h]; exact hnz _ _ (by simpa [adjS] using h)
  have hcol : ∀ v, ∑ x, ϕ x (.inl v) = ∑ a, if N.graph.head a = v then
      ϕ (.inr a) (.inl (N.graph.head a)) else 0 := by
    intro v
    rw [Fintype.sum_sum_type]
    have e0 : ∑ w, ϕ (.inl w) (.inl v) = 0 :=
      Finset.sum_eq_zero (fun w _ => hnz _ _ (by simp [adjS]))
    rw [e0, zero_add]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    by_cases h : N.graph.head a = v
    · subst h; simp
    · rw [if_neg h]; exact hnz _ _ (by simpa [adjS] using h)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro a
    have := h1 (.inr a) (.inl (N.graph.head a)) (by simp [splitNet, adjS])
    simpa [splitNet, capS] using this
  · intro v hv1 hv2
    have := h4 (.inl v) (by simp [splitNet, hv1]) (by simp [splitNet, hv2])
    rw [hrow, hcol] at this
    unfold divergence
    simp only
    linarith
  · have hs' : flowValue N (fun a => ϕ (.inr a) (.inl (N.graph.head a))) =
        ∑ e, if N.graph.tail e = N.source then ϕ (.inr e) (.inl (N.graph.head e)) else 0 := by
      unfold flowValue divergence
      have : ∀ e, (if N.graph.head e = N.source then ϕ (.inr e) (.inl (N.graph.head e)) else 0) = 0 := by
        intro e; simp [hin e]
      simp [this]
    rw [hs']
    unfold Network.value
    simp only [splitNet]
    rw [hrow]


theorem cut_formula (L : Finset (V ⊕ A)) :
    (splitNet N hs hcap hin hout hl).cutCapacity L =
      ∑ a, ((if Sum.inl (N.graph.tail a) ∈ L ∧ Sum.inr a ∉ L then N.capacity a else 0) +
        (if Sum.inr a ∈ L ∧ Sum.inl (N.graph.head a) ∉ L then N.capacity a else 0)) := by
  have h1 : ∀ g : V ⊕ A → V ⊕ A → ℝ, ∑ x ∈ L, ∑ y ∈ Lᶜ, g x y =
      ∑ x, ∑ y, if x ∈ L ∧ y ∉ L then g x y else 0 := by
    intro g
    have hL : ∑ x ∈ L, (∑ y ∈ Lᶜ, g x y) = ∑ x, if x ∈ L then ∑ y ∈ Lᶜ, g x y else 0 := by
      rw [← Finset.sum_filter]; congr; ext; simp
    rw [hL]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases hx : x ∈ L
    · simp only [hx, if_true, true_and]
      rw [← Finset.sum_filter]; congr; ext; simp
    · simp [hx]
  unfold Network.cutCapacity
  rw [h1]
  simp only [Fintype.sum_sum_type]
  simp only [splitNet, adjS, capS]
  simp
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  congr 1
  · rw [Finset.sum_eq_single (N.graph.tail a)]
    · by_cases h : Sum.inl (N.graph.tail a) ∈ L ∧ Sum.inr a ∉ L <;> simp [h]
    · intro v _ hv; simp [Ne.symm hv]
    · simp
  · rw [Finset.sum_eq_single (N.graph.head a)]
    · by_cases h : Sum.inr a ∈ L ∧ Sum.inl (N.graph.head a) ∉ L <;> simp [h]
    · intro v _ hv; simp [hv.symm]
    · simp

theorem mfmc_arc : ∃ v0 : ℝ,
    IsGreatest {v | ∃ f, FeasibleFlow N f ∧ flowValue N f = v} v0 ∧
    IsLeast {v | ∃ S, IsShore N S ∧ cutCapacity N S = v} v0 := by
  obtain ⟨v0, ⟨⟨ϕ, hϕ, hv⟩, hub⟩, ⟨⟨L, hL, hc⟩, hlb⟩⟩ :=
    max_flow_min_cut (splitNet N hs hcap hin hout hl)
  have hcut : ∀ S : Finset V, cutCapacity N S =
      ∑ e, if N.graph.tail e ∈ S ∧ N.graph.head e ∉ S then N.capacity e else 0 := fun S => rfl
  refine ⟨v0, ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨h1, h2⟩ := split_to_flow N hs hcap hin hout hl ϕ hϕ
    exact ⟨_, h1, h2.trans hv⟩
  · rintro v ⟨f, hf, rfl⟩
    obtain ⟨h1, h2⟩ := flow_to_split N hs hcap hin hout hl f hf
    rw [← h2]
    exact hub ⟨_, h1, rfl⟩
  · have hL1 : Sum.inl N.source ∈ L := hL.1
    have hL2 : Sum.inl N.sink ∉ L := hL.2
    have lb : ∀ S : Finset V, IsShore N S → v0 ≤ cutCapacity N S := by
      intro S hS
      let L' : Finset (V ⊕ A) := Finset.univ.filter (fun x => match x with
        | Sum.inl v => v ∈ S
        | Sum.inr a => N.graph.head a ∈ S)
      have hc' : (splitNet N hs hcap hin hout hl).IsCut L' := by
        refine ⟨?_, ?_⟩
        · simpa [L', splitNet] using hS.1
        · simpa [L', splitNet] using hS.2
      refine le_trans (hlb ⟨L', hc', rfl⟩) ?_
      rw [cut_formula N hs hcap hin hout hl L', hcut]
      refine Finset.sum_le_sum (fun a _ => ?_)
      have := hcap a
      by_cases h1 : N.graph.tail a ∈ S <;> by_cases h2 : N.graph.head a ∈ S <;>
        simp [L', h1, h2, this]
    have hmem : IsShore N (Finset.univ.filter (fun v => Sum.inl v ∈ L)) := by
      exact ⟨by simpa using hL1, by simpa using hL2⟩
    refine ⟨⟨_, hmem, ?_⟩, fun v ⟨S, hS, hv⟩ => hv ▸ lb S hS⟩
    apply le_antisymm
    · rw [← hc, cut_formula N hs hcap hin hout hl L, hcut]
      refine Finset.sum_le_sum (fun a _ => ?_)
      have := hcap a
      by_cases h1 : Sum.inl (N.graph.tail a) ∈ L <;> by_cases h2 : Sum.inl (N.graph.head a) ∈ L <;>
        by_cases h3 : Sum.inr a ∈ L <;> simp [h1, h2, h3, this]
    · exact lb _ hmem

end



theorem height_nonneg {m : ℕ} (H : Fin m → ℝ) (hH : ∀ i, 0 < H i) (j : ℕ) : 0 ≤ height H j := by
  unfold height; split_ifs with h
  · exact (hH _).le
  · exact le_refl _

theorem height_anti {m : ℕ} (H : Fin m → ℝ) (hH : ∀ i, 0 < H i) (hA : Antitone H) {j k : ℕ}
    (hjk : j ≤ k) : height H k ≤ height H j := by
  unfold height
  by_cases hk : k < m
  · have hj : j < m := lt_of_le_of_lt hjk hk
    simp only [hk, hj, dif_pos]
    exact hA (by exact hjk)
  · simp only [hk, dif_neg, not_false_eq_true]
    split_ifs with hj
    · exact (hH _).le
    · exact le_refl _

theorem gridGain_nonneg {m : ℕ} (H : Fin m → ℝ) (hH : ∀ i, 0 < H i) (i : Fin m) (j : ℕ) :
    0 ≤ gridGain H i j := by
  unfold gridGain; split_ifs with h
  · have := height_nonneg H hH j
    have := hH i
    positivity
  · exact le_refl _

theorem gridGain_anti {m : ℕ} (H : Fin m → ℝ) (hH : ∀ i, 0 < H i) (hA : Antitone H)
    (i : Fin m) (j : ℕ) : gridGain H i (j+1) ≤ gridGain H i j := by
  by_cases h2 : j + 1 < m
  · have h1 : j < m := by omega
    unfold gridGain
    simp only [h1, h2, if_true]
    have a1 := height_anti H hH hA (Nat.le_succ j)
    have a2 := height_nonneg H hH (j+1)
    have a3 := hH i
    have a4 := height_nonneg H hH j
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  · have : gridGain H i (j+1) = 0 := by unfold gridGain; simp [h2]
    rw [this]; exact gridGain_nonneg H hH i j

theorem stepCapacity_nonneg {m : ℕ} (H : Fin m → ℝ) (hH : IsProfile H) (e : StepArc m) :
    0 ≤ stepCapacity H e := by
  obtain ⟨hm, hpos, hA⟩ := hH
  have hq : ∀ i j, 0 ≤ q H i j := fun i j => by
    unfold q; linarith [gridGain_anti H hpos hA i j.val]
  have hr : ∀ i j : Fin m, 0 ≤ rCoeff H i j := fun i j => by
    unfold rCoeff
    have h1 := gridGain_anti H hpos hA i j.val
    have h2 := gridGain_nonneg H hpos i j.val
    have h3 : (0:ℝ) ≤ (m:ℝ) - j.val - 1 := by
      have := j.2
      have : (j.val : ℝ) + 1 ≤ m := by exact_mod_cast this
      linarith
    nlinarith
  have hm2 : (0:ℝ) ≤ (m:ℝ)^2 := by positivity
  cases e <;> simp only [stepCapacity] <;> first
    | positivity
    | exact div_nonneg (hr _ _) hm2
    | exact div_nonneg (hq _ _) hm2
    | norm_num

/-! smooth profile -/

theorem sm_exp (u : ℝ) (hu : 0 < u) :
    smoothProfile (1 - u) = Real.exp ((9938/10000 : ℝ) * Real.log u +
      ((-74112772 / 100000000 : ℝ) * (u - 1) + (58515414 / 100000000 : ℝ) * (u^2 - 1))) := by
  unfold smoothProfile
  have : (1 - (1 - u)) = u := by ring
  rw [this, Real.rpow_def_of_pos hu, ← Real.exp_add]
  ring_nf

theorem sm_anti {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y < 1) :
    smoothProfile y ≤ smoothProfile x := by
  have hu : 0 < 1 - y := by linarith
  have huv : 1 - y ≤ 1 - x := by linarith
  have hv1 : 1 - x ≤ 1 := by linarith
  set u := 1 - y with hu_def
  set v := 1 - x with hv_def
  have hv : 0 < v := by linarith
  have e1 : y = 1 - u := by rw [hu_def]; ring
  have e2 : x = 1 - v := by rw [hv_def]; ring
  rw [e1, e2, sm_exp u hu, sm_exp v hv]
  apply Real.exp_le_exp.2
  have hlog : Real.log u - Real.log v ≤ u / v - 1 := by
    rw [← Real.log_div hu.ne' hv.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hu hv)
  have hkey : (v - u) * ((74112772 / 100000000 : ℝ) - (58515414 / 100000000 : ℝ) * (u + v)) * v
      ≤ (9938/10000 : ℝ) * (v - u) := by
    have h1 : 0 ≤ v - u := by linarith
    have h2 : (0:ℝ) ≤ 9938/10000 - (74112772 / 100000000 : ℝ) * v + (58515414 / 100000000 : ℝ) * v^2 := by
      nlinarith [sq_nonneg (v - 6/10)]
    nlinarith [mul_nonneg h1 h2, mul_nonneg h1 (mul_nonneg hu.le hv.le)]
  have hdiv : (u / v - 1) * (9938/10000 : ℝ) =
      -((9938/10000 : ℝ) * (v - u)) / v := by field_simp; ring
  have h3 : -((9938/10000 : ℝ) * (v - u)) / v +
      (v - u) * ((74112772 / 100000000 : ℝ) - (58515414 / 100000000 : ℝ) * (u + v)) ≤ 0 := by
    have : (v - u) * ((74112772 / 100000000 : ℝ) - (58515414 / 100000000 : ℝ) * (u + v)) ≤
        ((9938/10000 : ℝ) * (v - u)) / v := by
      rw [le_div_iff₀ hv]; exact hkey
    rw [neg_div]; linarith
  nlinarith [mul_le_mul_of_nonneg_left hlog (by norm_num : (0:ℝ) ≤ 9938/10000)]

theorem sm_lower {x : ℝ} (hx : 0 ≤ x) (hx2 : x ≤ 1 - 1/400) : 1/1000 ≤ smoothProfile x := by
  have hu : 0 < 1 - x := by linarith
  unfold smoothProfile
  set u := 1 - x with hu_def
  have hu1 : u ≤ 1 := by linarith
  have h1 : u ≤ u ^ (9938 / 10000 : ℝ) := by
    calc u = u ^ (1:ℝ) := (Real.rpow_one u).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hu hu1 (by norm_num)
  have h2 : (0.4:ℝ) ≤ Real.exp ((-74112772 / 100000000 : ℝ) * (u - 1) +
      (58515414 / 100000000 : ℝ) * (u ^ 2 - 1)) := by
    have := Real.add_one_le_exp ((-74112772 / 100000000 : ℝ) * (u - 1) +
      (58515414 / 100000000 : ℝ) * (u ^ 2 - 1))
    nlinarith [sq_nonneg u]
  have hu2 : 1/400 ≤ u := by linarith
  have : (0:ℝ) ≤ u := hu.le
  calc (1:ℝ)/1000 ≤ u * 0.4 := by nlinarith
    _ ≤ _ := by
      have h3 : 0 ≤ u ^ (9938 / 10000 : ℝ) := by positivity
      nlinarith

theorem sm_upper {x : ℝ} (hx : 0 ≤ x) (hx2 : x < 1) : smoothProfile x ≤ 3 := by
  have hu : 0 < 1 - x := by linarith
  unfold smoothProfile
  set u := 1 - x with hu_def
  have hu1 : u ≤ 1 := by linarith
  have h1 : u ^ (9938 / 10000 : ℝ) ≤ 1 := Real.rpow_le_one hu.le hu1 (by norm_num)
  have h2 : Real.exp ((-74112772 / 100000000 : ℝ) * (u - 1) +
      (58515414 / 100000000 : ℝ) * (u ^ 2 - 1)) ≤ 3 := by
    have e : Real.exp ((-74112772 / 100000000 : ℝ) * (u - 1) +
      (58515414 / 100000000 : ℝ) * (u ^ 2 - 1)) ≤ Real.exp 1 := by
      apply Real.exp_le_exp.2
      nlinarith [sq_nonneg u]
    have := Real.exp_one_lt_d9
    linarith
  have h3 : 0 ≤ Real.exp ((-74112772 / 100000000 : ℝ) * (u - 1) +
      (58515414 / 100000000 : ℝ) * (u ^ 2 - 1)) := (Real.exp_pos _).le
  have h4 : 0 ≤ u ^ (9938 / 10000 : ℝ) := by positivity
  nlinarith

theorem explicit_profile : IsProfile explicitHeights := by
  have hden : 1/1000 ≤ smoothProfile ((30/100 : ℝ) / 240) :=
    sm_lower (by norm_num) (by norm_num)
  have hden3 : smoothProfile ((30/100 : ℝ) / 240) ≤ 3 := sm_upper (by norm_num) (by norm_num)
  have hdpos : 0 < smoothProfile ((30/100 : ℝ) / 240) := by linarith
  refine ⟨by norm_num, ?_, ?_⟩
  · intro i
    have hi : (i.val : ℝ) ≤ 239 := by
      have := i.2
      have : i.val ≤ 239 := by omega
      exact_mod_cast this
    have hi0 : (0:ℝ) ≤ i.val := Nat.cast_nonneg _
    have hnum : 1/1000 ≤ smoothProfile (((i.val : ℝ) + 30/100) / 240) :=
      sm_lower (by positivity) (by rw [div_le_iff₀ (by norm_num)]; nlinarith)
    unfold explicitHeights explicitHeightInt
    have : (0:ℝ) < ((⌊(10 : ℝ)^30 * smoothProfile (((i.val : ℝ) + 30/100) / 240) /
        smoothProfile ((30/100 : ℝ) / 240)⌋ : ℤ) : ℝ) := by
      have h1 : (1:ℤ) ≤ ⌊(10 : ℝ)^30 * smoothProfile (((i.val : ℝ) + 30/100) / 240) /
        smoothProfile ((30/100 : ℝ) / 240)⌋ := by
        rw [Int.le_floor, le_div_iff₀ hdpos]
        push_cast
        nlinarith
      have : (1:ℝ) ≤ ((⌊(10 : ℝ)^30 * smoothProfile (((i.val : ℝ) + 30/100) / 240) /
        smoothProfile ((30/100 : ℝ) / 240)⌋ : ℤ) : ℝ) := by exact_mod_cast h1
      linarith
    exact this
  · intro i j hij
    have hij' : (i.val : ℝ) ≤ j.val := by exact_mod_cast hij
    have hj : (j.val : ℝ) ≤ 239 := by
      have := j.2
      have : j.val ≤ 239 := by omega
      exact_mod_cast this
    have hi0 : (0:ℝ) ≤ i.val := Nat.cast_nonneg _
    have hs : smoothProfile (((j.val : ℝ) + 30/100) / 240) ≤
        smoothProfile (((i.val : ℝ) + 30/100) / 240) :=
      sm_anti (by positivity) (by gcongr) (by rw [div_lt_iff₀ (by norm_num)]; linarith)
    unfold explicitHeights explicitHeightInt
    have : ⌊(10 : ℝ)^30 * smoothProfile (((j.val : ℝ) + 30/100) / 240) /
        smoothProfile ((30/100 : ℝ) / 240)⌋ ≤ ⌊(10 : ℝ)^30 * smoothProfile (((i.val : ℝ) + 30/100) / 240) /
        smoothProfile ((30/100 : ℝ) / 240)⌋ := by
      apply Int.floor_le_floor
      gcongr
    exact_mod_cast this


theorem step_hs : (stepNetwork explicitHeights).source ≠ (stepNetwork explicitHeights).sink := by
  intro h; cases h

theorem step_hin (e : StepArc 240) :
    (stepNetwork explicitHeights).graph.head e ≠ (stepNetwork explicitHeights).source := by
  cases e <;> simp [stepNetwork, stepDigraph]

theorem step_hout (e : StepArc 240) :
    (stepNetwork explicitHeights).graph.tail e ≠ (stepNetwork explicitHeights).sink := by
  cases e <;> simp [stepNetwork, stepDigraph]

theorem step_hl (e : StepArc 240) :
    (stepNetwork explicitHeights).graph.tail e ≠ (stepNetwork explicitHeights).graph.head e := by
  cases e <;> simp [stepNetwork, stepDigraph, previous, next, Fin.ext_iff]

end HRGen

open HRGen in
theorem solution (f : StepArc 240 → ℤ) (hf : IntegerFeasible f) (F : ℤ)
    (hF : integerFlowValue f = F) :
    MC explicitHeights = MF explicitHeights ∧
      (F : ℝ) / 10^12 ≤ MF explicitHeights := by
  classical
  have hcap : ∀ e, 0 ≤ (stepNetwork explicitHeights).capacity e :=
    fun e => stepCapacity_nonneg _ explicit_profile e
  obtain ⟨v0, hg, hl⟩ := mfmc_arc (stepNetwork explicitHeights) step_hs hcap step_hin step_hout step_hl
  have hMF : MF explicitHeights = v0 := hg.csSup_eq
  have hMC : MC explicitHeights = v0 := hl.csInf_eq
  rw [hMC, hMF]
  refine ⟨rfl, ?_⟩
  let f' : StepArc 240 → ℝ := fun e => (f e : ℝ) / 10^12
  have hdiv : ∀ v, divergence (stepNetwork explicitHeights) f' v = (integerDivergence f v : ℝ) / 10^12 := by
    intro v
    unfold divergence integerDivergence
    push_cast
    rw [sub_div, Finset.sum_div, Finset.sum_div]
    have key : ∀ (p : Prop) (d1 d2 : Decidable p) (e : StepArc 240),
        @ite ℝ p d1 (f' e) 0 = (@ite ℝ p d2 (f e : ℝ) 0) / 10^12 := by
      intro p d1 d2 e
      by_cases h : p
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h, zero_div]
    refine congrArg₂ (fun a b : ℝ => a - b) ?_ ?_
    · exact Finset.sum_congr rfl (fun e _ => key _ _ _ e)
    · exact Finset.sum_congr rfl (fun e _ => key _ _ _ e)
  have hfeas : FeasibleFlow (stepNetwork explicitHeights) f' := by
    refine ⟨fun e => ⟨?_, ?_⟩, fun v hv1 hv2 => ?_⟩
    · have := (hf.1 e).1
      have : (0:ℝ) ≤ f e := by exact_mod_cast this
      exact div_nonneg this (by positivity)
    · have h1 := (hf.1 e).2
      have h2 : (f e : ℝ) ≤ (roundedCapacity e : ℝ) := by exact_mod_cast h1
      have h3 : (roundedCapacity e : ℝ) ≤ (certificateScale : ℝ) * stepCapacity explicitHeights e :=
        Int.floor_le _
      have h4 : (certificateScale : ℝ) = 10^12 := by unfold certificateScale; push_cast; norm_num
      rw [h4] at h3
      show (f e : ℝ) / 10^12 ≤ stepCapacity explicitHeights e
      rw [div_le_iff₀ (by positivity)]
      linarith
    · rw [hdiv]
      have := hf.2 v hv1 hv2
      simp [this]
  have hval : flowValue (stepNetwork explicitHeights) f' = (F : ℝ) / 10^12 := by
    unfold flowValue
    rw [hdiv, ← hF]; rfl
  rw [← hval]
  exact hg.2 ⟨f', hfeas, rfl⟩
