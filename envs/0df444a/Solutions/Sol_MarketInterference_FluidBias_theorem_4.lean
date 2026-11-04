-- Prove2me | solution 1 for MarketInterference.FluidBias.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T13:01:18.748197+00:00
-- url     : https://prove2.me/submissions/b5ce1687-2917-4fe3-8bbc-dbe7e6b156f2

import Mathlib
import Definitions.Def_MarketInterference_FluidBias_NetworkLP
import Definitions.Def_MarketInterference_FluidBias_PathFlow
import Definitions.Def_MarketInterference_FluidBias_Estimators


namespace MIFBThm4Proof

open Finset

/-- Lagrangian duality for a box-constrained LP `max c·x s.t. 0 ≤ x ≤ ub, A x ≤ b`. -/
theorem lp_dual_box {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    (A : m → n → ℝ) (b : m → ℝ) (c ub : n → ℝ) (hub : ∀ e, 0 ≤ ub e) (hb : ∀ r, 0 ≤ b r)
    (V : ℝ)
    (hV : ∀ x : n → ℝ, (∀ e, 0 ≤ x e ∧ x e ≤ ub e) → (∀ r, ∑ e, A r e * x e ≤ b r) →
      ∑ e, c e * x e ≤ V)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ w : m → ℝ, (∀ r, 0 ≤ w r) ∧
      ∑ r, w r * b r + ∑ e, ub e * max 0 (c e - ∑ r, w r * A r e) < V + ε := by
  classical
  -- the linear map
  let L : (n → ℝ) →ₗ[ℝ] (Option m → ℝ) :=
    { toFun := fun x k => match k with
        | some r => ∑ e, A r e * x e
        | none => ∑ e, c e * x e
      map_add' := by
        intro x y; funext k; cases k <;> simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a x; funext k; cases k <;> simp [Finset.mul_sum] <;>
          exact Finset.sum_congr rfl (fun _ _ => by ring) }
  let B : Set (n → ℝ) := Set.pi Set.univ (fun e => Set.Icc 0 (ub e))
  let K : Set (Option m → ℝ) := L '' B
  let C : Set (Option m → ℝ) := {z | (∀ r, z (some r) ≤ b r) ∧ V + ε ≤ z none}
  have hBc : IsCompact B := isCompact_univ_pi (fun e => isCompact_Icc)
  have hBconv : Convex ℝ B := convex_pi (fun e _ => convex_Icc 0 (ub e))
  have hKc : IsCompact K := hBc.image (LinearMap.continuous_of_finiteDimensional L)
  have hKconv : Convex ℝ K := hBconv.linear_image L
  have hCc : IsClosed C := by
    have hC : C = (⋂ r, {z : Option m → ℝ | z (some r) ≤ b r}) ∩ {z | V + ε ≤ z none} := by
      ext z; simp [C]
    rw [hC]
    apply IsClosed.inter
    · exact isClosed_iInter (fun r => isClosed_le (continuous_apply _) continuous_const)
    · exact isClosed_le continuous_const (continuous_apply _)
  have hCconv : Convex ℝ C := by
    intro z hz z' hz' s t hs ht hst
    refine ⟨fun r => ?_, ?_⟩
    · have h1 := hz.1 r; have h2 := hz'.1 r
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := mul_le_mul_of_nonneg_left h1 hs
      have := mul_le_mul_of_nonneg_left h2 ht
      have : s * b r + t * b r = b r := by rw [← add_mul, hst, one_mul]
      linarith
    · have h1 := hz.2; have h2 := hz'.2
      change V + ε ≤ z none at h1
      change V + ε ≤ z' none at h2
      change V + ε ≤ s * z none + t * z' none
      have := mul_le_mul_of_nonneg_left h1 hs
      have := mul_le_mul_of_nonneg_left h2 ht
      have : s * (V + ε) + t * (V + ε) = V + ε := by rw [← add_mul, hst, one_mul]
      linarith
  have hdisj : Disjoint K C := by
    rw [Set.disjoint_left]
    rintro z ⟨x, hx, rfl⟩ hz
    have hx' : ∀ e, 0 ≤ x e ∧ x e ≤ ub e := fun e => hx e (Set.mem_univ _)
    have := hV x hx' (fun r => hz.1 r)
    have h2 := hz.2
    change V + ε ≤ ∑ e, c e * x e at h2
    linarith
  obtain ⟨f, u, v, hfK, huv, hfC⟩ :=
    geometric_hahn_banach_compact_closed hKconv hKc hCconv hCc hdisj
  -- coefficients
  let g : Option m → ℝ := fun k => f (Pi.single k 1)
  have hf : ∀ z, f z = ∑ k, z k * g k := by
    intro z
    have := LinearMap.pi_apply_eq_sum_univ (f : (Option m → ℝ) →L[ℝ] ℝ).toLinearMap z
    rw [ContinuousLinearMap.coe_coe] at this
    rw [this]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [smul_eq_mul, g]
    congr 2
    funext j
    simp [Pi.single_apply, eq_comm]
  let z0 : Option m → ℝ := fun k => match k with
    | some r => b r
    | none => V + ε
  have hz0 : z0 ∈ C := ⟨fun r => le_refl _, le_refl _⟩
  -- f along a ray
  have hray : ∀ (k : Option m) (t : ℝ), f (z0 + t • Pi.single k 1) = f z0 + t * g k := by
    intro k t
    rw [map_add, map_smul]; rfl
  have hgr : ∀ r, g (some r) ≤ 0 := by
    intro r
    by_contra hpos
    push Not at hpos
    set t : ℝ := (f z0 - v) / g (some r) + 1 with ht
    have htpos : 0 ≤ t := by
      have : 0 < f z0 - v := by linarith [hfC z0 hz0]
      positivity
    have hmem : z0 + (-t) • Pi.single (some r) 1 ∈ C := by
      refine ⟨fun r' => ?_, ?_⟩
      · by_cases h : r' = r
        · subst h; simp [z0]; linarith
        · simp [z0, Pi.single_apply, h]
      · simp [z0]
    have := hfC _ hmem
    rw [hray] at this
    have : t * g (some r) < f z0 - v := by linarith
    have hh : t * g (some r) = (f z0 - v) + g (some r) := by
      rw [ht]; field_simp
    linarith
  have hgn : 0 ≤ g none := by
    by_contra hneg
    push Not at hneg
    set t : ℝ := (f z0 - v) / (-g none) + 1 with ht
    have htpos : 0 ≤ t := by
      have : 0 < f z0 - v := by linarith [hfC z0 hz0]
      have : 0 < -g none := by linarith
      positivity
    have hmem : z0 + t • Pi.single none 1 ∈ C := by
      refine ⟨fun r' => ?_, ?_⟩
      · simp [z0]
      · simp [z0]; linarith
    have := hfC _ hmem
    rw [hray] at this
    have hne : g none ≠ 0 := hneg.ne
    have hh : t * g none = -(f z0 - v) + g none := by
      rw [ht]; field_simp
    linarith
  -- f z0
  have hfz0 : f z0 = ∑ r, b r * g (some r) + (V + ε) * g none := by
    rw [hf, Fintype.sum_option]; simp [z0]; ring
  have h0B : (0 : n → ℝ) ∈ B := fun e _ => ⟨le_refl _, hub e⟩
  have hf0 : f (L 0) < u := hfK _ ⟨0, h0B, rfl⟩
  rw [map_zero, map_zero] at hf0
  have hzpos : 0 < f z0 := by linarith [hfC z0 hz0]
  have hgnpos : 0 < g none := by
    rcases hgn.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [hfz0, ← h] at hzpos
      have : ∑ r, b r * g (some r) ≤ 0 :=
        Finset.sum_nonpos (fun r _ => mul_nonpos_of_nonneg_of_nonpos (hb r) (hgr r))
      linarith
  set μ := g none
  refine ⟨fun r => -g (some r) / μ, fun r => ?_, ?_⟩
  · exact div_nonneg (by linarith [hgr r]) hgnpos.le
  -- choose x
  set w : m → ℝ := fun r => -g (some r) / μ
  let x : n → ℝ := fun e => if 0 < c e - ∑ r, w r * A r e then ub e else 0
  have hxB : x ∈ B := by
    intro e _
    simp only [x]; split_ifs
    · exact ⟨hub e, le_refl _⟩
    · exact ⟨le_refl _, hub e⟩
  have hfx : f (L x) < f z0 := by linarith [hfK _ ⟨x, hxB, rfl⟩, hfC z0 hz0]
  rw [hf, Fintype.sum_option, hfz0] at hfx
  change (∑ e, c e * x e) * μ + ∑ r, (∑ e, A r e * x e) * g (some r) <
    ∑ r, b r * g (some r) + (V + ε) * μ at hfx
  have hgw : ∀ r, g (some r) = -(w r * μ) := by
    intro r; simp only [w]; field_simp
  simp only [hgw] at hfx
  have key : ∑ e, ub e * max 0 (c e - ∑ r, w r * A r e) =
      ∑ e, c e * x e - ∑ r, w r * ∑ e, A r e * x e := by
    have hs : ∑ r, w r * ∑ e, A r e * x e = ∑ e, ∑ r, w r * (A r e * x e) := by
      simp only [Finset.mul_sum]; exact Finset.sum_comm
    rw [hs, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    simp only [x]
    split_ifs with h
    · rw [max_eq_right h.le]
      have : ∑ r, w r * (A r e * ub e) = (∑ r, w r * A r e) * ub e := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun _ _ => by ring)
      rw [this]; ring
    · push Not at h
      rw [max_eq_left h]; simp
  rw [key]
  have e1 : ∑ r, -(w r * μ) * b r = -(μ * ∑ r, w r * b r) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  have e2 : ∑ r, (∑ e, A r e * x e) * -(w r * μ) = -(μ * ∑ r, w r * ∑ e, A r e * x e) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  have e3 : ∑ r, b r * -(w r * μ) = -(μ * ∑ r, w r * b r) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [e2, e3] at hfx
  have : μ * (∑ e, c e * x e - ∑ r, w r * ∑ e, A r e * x e + ∑ r, w r * b r) < μ * (V + ε) := by
    nlinarith
  have := lt_of_mul_lt_mul_left this hgnpos.le
  linarith

end MIFBThm4Proof


namespace MIFBThm4Proof

open Finset MarketInterference.FluidBias

variable {nd ns : ℕ} {I E : Type} [Fintype E] [DecidableEq E] [DecidableEq I]

/-- intermediate nodes touched by some arc -/
def nodes (N : Network nd ns I E) : Finset I :=
  univ.biUnion fun e => (N.tail e).getRight?.toFinset ∪ (N.head e).getRight?.toFinset

lemma mem_nodes_tail (N : Network nd ns I E) {e : E} {u : I} (h : N.tail e = Sum.inr u) :
    u ∈ nodes N := by
  simp only [nodes, mem_biUnion, mem_univ, true_and, mem_union]
  exact ⟨e, Or.inl (by simp [h])⟩

lemma mem_nodes_head (N : Network nd ns I E) {e : E} {u : I} (h : N.head e = Sum.inr u) :
    u ∈ nodes N := by
  simp only [nodes, mem_biUnion, mem_univ, true_and, mem_union]
  exact ⟨e, Or.inr (by simp [h])⟩

/-- expansion of the dual potentials on an arc -/
lemma pot_expand (N : Network nd ns I E) (q : DualVar nd ns I E) (e : E) :
    tailPot (N := N) q e + headPot (N := N) q e =
      ∑ i, q.a i * (if N.head e = Sum.inl i then 1 else 0) +
      ∑ j, q.b j * (if N.tail e = Sum.inl j then 1 else 0) +
      ∑ u ∈ nodes N, q.m u * ((if N.tail e = Sum.inr u then 1 else 0) -
        (if N.head e = Sum.inr u then 1 else 0)) := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  rcases ht : N.tail e with j | u <;> rcases hh : N.head e with i | w
  · simp [tailPot, headPot, ht, hh] <;> ring
  · simp [tailPot, headPot, ht, hh, mem_nodes_head N hh] <;> ring
  · simp [tailPot, headPot, ht, hh, mem_nodes_tail N ht] <;> ring
  · simp [tailPot, headPot, ht, hh, mem_nodes_head N hh,
      mem_nodes_tail N ht] <;> ring

lemma sum_filter_eq (P : E → Prop) [DecidablePred P] (x : E → ℝ) :
    ∑ e with P e, x e = ∑ e, (if P e then 1 else 0) * x e := by
  rw [Finset.sum_filter]; exact Finset.sum_congr rfl (fun e _ => by split_ifs <;> simp)

lemma balance_out (N : Network nd ns I E) (x : E → ℝ) (u : I) (hu : u ∉ nodes N) :
    ∑ e with N.tail e = Sum.inr u, x e = 0 ∧ ∑ e with N.head e = Sum.inr u, x e = 0 := by
  constructor <;> refine Finset.sum_eq_zero (fun e he => ?_) <;> simp only [mem_filter] at he
  · exact absurd (mem_nodes_tail N he.2) hu
  · exact absurd (mem_nodes_head N he.2) hu

/-- the dual-potential pairing with an arbitrary flow -/
lemma pot_pair (N : Network nd ns I E) (q : DualVar nd ns I E) (x : E → ℝ) :
    ∑ e, (tailPot (N := N) q e + headPot (N := N) q e) * x e =
      ∑ i, q.a i * ∑ e with N.head e = Sum.inl i, x e +
      ∑ j, q.b j * ∑ e with N.tail e = Sum.inl j, x e +
      ∑ u ∈ nodes N, q.m u * (∑ e with N.tail e = Sum.inr u, x e -
        ∑ e with N.head e = Sum.inr u, x e) := by
  simp only [pot_expand, sum_filter_eq, add_mul, Finset.sum_add_distrib, Finset.sum_mul,
    Finset.mul_sum, mul_sub, sub_mul, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (s := univ) (t := univ) (f := fun e i => q.a i * _ * x e)]
  rw [Finset.sum_comm (s := univ) (t := univ) (f := fun e j => q.b j * _ * x e)]
  rw [Finset.sum_comm (s := univ) (t := nodes N)
      (f := fun e u => q.m u * (if N.tail e = Sum.inr u then (1:ℝ) else 0) * x e)]
  rw [Finset.sum_comm (s := univ) (t := nodes N)
      (f := fun e u => q.m u * (if N.head e = Sum.inr u then (1:ℝ) else 0) * x e)]
  simp only [mul_assoc]

theorem weak_duality (N : Network nd ns I E) (τ : ℝ) (d : Fin nd → ℝ) (s : Fin ns → ℝ)
    (x : E → ℝ) (q : DualVar nd ns I E) (hx : Feasible N τ d s x) (hq : DualFeasible N q) :
    obj N x ≤ dualObj N τ d s q := by
  obtain ⟨hbox, hdem, hsup, hbal⟩ := hx
  obtain ⟨hv, ha, hb, hξ⟩ := hq
  have h1 : obj N x ≤ ∑ e, (tailPot (N := N) q e + headPot (N := N) q e) * x e +
      ∑ e, q.ξ e * x e := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun e _ => by
      have := mul_le_mul_of_nonneg_right (hv e) (hbox e).1; linarith)
  rw [pot_pair] at h1
  have h2 : ∑ u ∈ nodes N, q.m u * (∑ e with N.tail e = Sum.inr u, x e -
        ∑ e with N.head e = Sum.inr u, x e) = 0 :=
    Finset.sum_eq_zero (fun u _ => by rw [hbal u]; ring)
  have h3 : ∑ i, q.a i * ∑ e with N.head e = Sum.inl i, x e ≤ ∑ i, q.a i * d i :=
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hdem i) (ha i))
  have h4 : ∑ j, q.b j * ∑ e with N.tail e = Sum.inl j, x e ≤ ∑ j, q.b j * s j :=
    Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hsup j) (hb j))
  have h5 : ∑ e, q.ξ e * x e ≤ ∑ e, q.ξ e * N.k e * τ :=
    Finset.sum_le_sum (fun e _ => by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (by linarith [(hbox e).2]) (hξ e))
  unfold dualObj
  linarith

/-- constraint matrix of the network LP -/
def rowA (N : Network nd ns I E) :
    (Fin nd ⊕ Fin ns ⊕ ((nodes N) ⊕ (nodes N))) → E → ℝ
  | Sum.inl i, e => if N.head e = Sum.inl i then 1 else 0
  | Sum.inr (Sum.inl j), e => if N.tail e = Sum.inl j then 1 else 0
  | Sum.inr (Sum.inr (Sum.inl u)), e =>
      (if N.tail e = Sum.inr (u : I) then 1 else 0) - (if N.head e = Sum.inr (u : I) then 1 else 0)
  | Sum.inr (Sum.inr (Sum.inr u)), e =>
      (if N.head e = Sum.inr (u : I) then 1 else 0) - (if N.tail e = Sum.inr (u : I) then 1 else 0)

def rowB (N : Network nd ns I E) (d : Fin nd → ℝ) (s : Fin ns → ℝ) :
    (Fin nd ⊕ Fin ns ⊕ ((nodes N) ⊕ (nodes N))) → ℝ
  | Sum.inl i => d i
  | Sum.inr (Sum.inl j) => s j
  | Sum.inr (Sum.inr _) => 0

lemma ind_sub_mul (P Q : Prop) [Decidable P] [Decidable Q] (t : ℝ) :
    ((if P then (1:ℝ) else 0) - (if Q then 1 else 0)) * t =
      (if P then 1 else 0) * t - (if Q then 1 else 0) * t := sub_mul _ _ _

theorem strong_duality (N : Network nd ns I E) (τ : ℝ) (hτ : 0 ≤ τ) (d : Fin nd → ℝ)
    (s : Fin ns → ℝ) (hd : 0 ≤ d) (hs : 0 ≤ s) (x : E → ℝ) (hx : IsOptimal N τ d s x)
    (q : DualVar nd ns I E) (hq : IsOptimalDual N τ d s q) :
    dualObj N τ d s q = obj N x := by
  refine le_antisymm ?_ (weak_duality N τ d s x q hx.1 hq.1)
  refine le_of_forall_pos_lt_add (fun ε hε => ?_)
  have hV : ∀ x' : E → ℝ, (∀ e, 0 ≤ x' e ∧ x' e ≤ τ * N.k e) →
      (∀ r, ∑ e, rowA N r e * x' e ≤ rowB N d s r) → ∑ e, N.v e * x' e ≤ obj N x := by
    intro x' hbox hrow
    apply hx.2 x'
    refine ⟨hbox, fun i => ?_, fun j => ?_, fun u => ?_⟩
    · have := hrow (Sum.inl i)
      simpa [rowA, rowB, sum_filter_eq] using this
    · have := hrow (Sum.inr (Sum.inl j))
      simpa [rowA, rowB, sum_filter_eq] using this
    · by_cases hu : u ∈ nodes N
      · have h1 := hrow (Sum.inr (Sum.inr (Sum.inl ⟨u, hu⟩)))
        have h2 := hrow (Sum.inr (Sum.inr (Sum.inr ⟨u, hu⟩)))
        simp only [rowA, rowB, ind_sub_mul, Finset.sum_sub_distrib] at h1 h2
        rw [sum_filter_eq, sum_filter_eq]
        linarith
      · rw [(balance_out N x' u hu).1, (balance_out N x' u hu).2]
  obtain ⟨w, hw0, hwlt⟩ := lp_dual_box (rowA N) (rowB N d s) N.v (fun e => τ * N.k e)
    (fun e => mul_nonneg hτ (N.k_nonneg e))
    (fun r => by
      rcases r with i | j | u | u
      · exact hd i
      · exact hs j
      · exact le_refl _
      · exact le_refl _)
    (obj N x) hV ε hε
  let q' : DualVar nd ns I E :=
    { a := fun i => w (Sum.inl i)
      b := fun j => w (Sum.inr (Sum.inl j))
      m := fun u => if h : u ∈ nodes N then
          w (Sum.inr (Sum.inr (Sum.inl ⟨u, h⟩))) - w (Sum.inr (Sum.inr (Sum.inr ⟨u, h⟩)))
        else 0
      ξ := fun e => max 0 (N.v e - ∑ r, w r * rowA N r e) }
  have hkey : ∀ e, ∑ r, w r * rowA N r e = tailPot (N := N) q' e + headPot (N := N) q' e := by
    intro e
    rw [pot_expand]
    simp only [Fintype.sum_sum_type, rowA]
    have hn : ∑ u : (nodes N), w (Sum.inr (Sum.inr (Sum.inl u))) *
          ((if N.tail e = Sum.inr (u : I) then 1 else 0) -
            (if N.head e = Sum.inr (u : I) then 1 else 0)) +
        ∑ u : (nodes N), w (Sum.inr (Sum.inr (Sum.inr u))) *
          ((if N.head e = Sum.inr (u : I) then 1 else 0) -
            (if N.tail e = Sum.inr (u : I) then 1 else 0)) =
        ∑ u ∈ nodes N, q'.m u * ((if N.tail e = Sum.inr u then 1 else 0) -
          (if N.head e = Sum.inr u then 1 else 0)) := by
      rw [← Finset.sum_coe_sort (nodes N), ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      simp only [q', dif_pos u.2]
      ring
    rw [← hn]
    simp only [q']
    ring
  have hfeas : DualFeasible N q' := by
    refine ⟨fun e => ?_, fun i => hw0 _, fun j => hw0 _, fun e => le_max_left _ _⟩
    rw [← hkey]
    simp only [q']
    linarith [le_max_right 0 (N.v e - ∑ r, w r * rowA N r e)]
  have hobj : dualObj N τ d s q' =
      ∑ r, w r * rowB N d s r + ∑ e, τ * N.k e * max 0 (N.v e - ∑ r, w r * rowA N r e) := by
    simp only [dualObj, Fintype.sum_sum_type, rowB, q', mul_zero, Finset.sum_const_zero,
      add_zero]
    congr 1
    exact Finset.sum_congr rfl (fun e _ => by ring)
  have := hq.2 q' hfeas
  linarith

end MIFBThm4Proof


namespace MIFBThm4Proof

open Finset MarketInterference.FluidBias

variable {nd ns : ℕ} {I E : Type} [Fintype E] [DecidableEq E] [DecidableEq I]

lemma sum_mul_count (g : E → ℝ) (l : List E) :
    ∑ e, g e * (l.count e : ℝ) = (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.count_cons, List.map_cons, List.sum_cons, beq_iff_eq, Nat.cast_add,
      Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_add, Finset.sum_add_distrib, ih]
    rw [add_comm]
    congr 1
    simp [Finset.sum_ite_eq']

lemma pair_pathflow {N : Network nd ns I E} (g : E → ℝ) (P : Finset (SDPath N))
    (w : SDPath N → ℝ) :
    ∑ e, g e * ∑ p ∈ P, w p * (p.arcs.count e : ℝ) = ∑ p ∈ P, w p * (p.arcs.map g).sum := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [← sum_mul_count, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun e _ => by ring)

/-- chain relation of a path -/
def ChainR (N : Network nd ns I E) (e f : E) : Prop :=
  ∃ u : I, N.head e = Sum.inr u ∧ N.tail f = Sum.inr u

lemma chain_last (N : Network nd ns I E) (H : E → ℝ)
    (hH : ∀ e, (∃ u, N.head e = Sum.inr u) → H e = 0) :
    ∀ (t : List E) (a : E), (a :: t).IsChain (ChainR N) →
      ((a :: t).map H).sum = H ((a :: t).getLast (by simp)) := by
  intro t
  induction t with
  | nil => intro a _; simp
  | cons b t ih =>
    intro a h
    rw [List.isChain_cons_cons] at h
    obtain ⟨⟨u, hu, -⟩, h2⟩ := h
    rw [List.map_cons, List.sum_cons, ih b h2, hH a ⟨u, hu⟩, zero_add, List.getLast_cons_cons]

lemma chain_telescope (N : Network nd ns I E) (T H : E → ℝ)
    (hTH : ∀ e f, ChainR N e f → H e = T f) :
    ∀ (t : List E) (a : E), (a :: t).IsChain (ChainR N) →
      ((a :: t).map (fun e => T e - H e)).sum = T a - H ((a :: t).getLast (by simp)) := by
  intro t
  induction t with
  | nil => intro a _; simp
  | cons b t ih =>
    intro a h
    rw [List.isChain_cons_cons] at h
    obtain ⟨hab, h2⟩ := h
    rw [List.map_cons, List.sum_cons, ih b h2, List.getLast_cons_cons, hTH a b hab]
    ring

lemma path_demand {N : Network nd ns I E} (p : SDPath N) (i : Fin nd) :
    (p.arcs.map (fun e => if N.head e = Sum.inl i then (1:ℝ) else 0)).sum =
      if p.i = i then 1 else 0 := by
  obtain ⟨pi, pj, arcs, hne, _, hft, hlh, hch⟩ := p
  simp only
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  rw [chain_last N _ (fun e ⟨u, hu⟩ => by simp [hu]) t a hch]
  have := hlh _ (by rw [List.getLast?_eq_getLast (by simp)]; rfl)
  rw [this]
  simp

lemma path_balance {N : Network nd ns I E} (p : SDPath N) (u : I) :
    (p.arcs.map (fun e => (if N.tail e = Sum.inr u then (1:ℝ) else 0) -
      (if N.head e = Sum.inr u then 1 else 0))).sum = 0 := by
  obtain ⟨pi, pj, arcs, hne, _, hft, hlh, hch⟩ := p
  simp only
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  rw [chain_telescope N (fun e => if N.tail e = Sum.inr u then (1:ℝ) else 0)
    (fun e => if N.head e = Sum.inr u then (1:ℝ) else 0)
    (fun e f ⟨w, h1, h2⟩ => by simp [h1, h2]) t a hch]
  have h1 := hlh _ (by rw [List.getLast?_eq_getLast (by simp)]; rfl)
  have h2 := hft a (by simp)
  simp [h1, h2]

end MIFBThm4Proof


namespace MIFBThm4Proof

open Finset MarketInterference.FluidBias

variable {nd ns : ℕ} {I E : Type} [Fintype E] [DecidableEq E] [DecidableEq I]

lemma phi_eq_of_opt (N : Network nd ns I E) (τ : ℝ) (d : Fin nd → ℝ) (s : Fin ns → ℝ)
    (x : E → ℝ) (hx : IsOptimal N τ d s x) : Phi N τ d s = obj N x :=
  IsGreatest.csSup_eq ⟨⟨x, hx.1, rfl⟩, by rintro _ ⟨y, hy, rfl⟩; exact hx.2 y hy⟩

lemma phi_le_dual (N : Network nd ns I E) (τ : ℝ) (d : Fin nd → ℝ) (s : Fin ns → ℝ)
    (q : DualVar nd ns I E) (h0 : Feasible N τ d s 0) (hq : DualFeasible N q) :
    Phi N τ d s ≤ dualObj N τ d s q :=
  csSup_le ⟨_, 0, h0, rfl⟩ (by rintro _ ⟨y, hy, rfl⟩; exact weak_duality N τ d s y q hy hq)

lemma le_phi (N : Network nd ns I E) (τ : ℝ) (d : Fin nd → ℝ) (s : Fin ns → ℝ)
    (q : DualVar nd ns I E) (x : E → ℝ) (hx : Feasible N τ d s x) (hq : DualFeasible N q) :
    obj N x ≤ Phi N τ d s :=
  le_csSup ⟨dualObj N τ d s q, by rintro _ ⟨y, hy, rfl⟩; exact weak_duality N τ d s y q hy hq⟩
    ⟨x, hx, rfl⟩

lemma zero_feasible (N : Network nd ns I E) (d : Fin nd → ℝ) (s : Fin ns → ℝ)
    (hd : ∀ i, 0 ≤ d i) (hs : ∀ j, 0 ≤ s j) : Feasible N 1 d s 0 :=
  ⟨fun e => ⟨le_refl _, by simp [N.k_nonneg e]⟩, fun i => by simp [hd i],
    fun j => by simp [hs j], fun u => by simp⟩

/-- inflow of a path flow at a demand node -/
lemma inflow_path {N : Network nd ns I E} (P : Finset (SDPath N)) (w : SDPath N → ℝ)
    (i : Fin nd) :
    ∑ e with N.head e = Sum.inl i, ∑ p ∈ P, w p * (p.arcs.count e : ℝ) =
      ∑ p ∈ P, w p * (if p.i = i then 1 else 0) := by
  rw [sum_filter_eq, pair_pathflow]
  exact Finset.sum_congr rfl (fun p _ => by rw [path_demand])

lemma balance_path {N : Network nd ns I E} (P : Finset (SDPath N)) (w : SDPath N → ℝ)
    (u : I) :
    ∑ e with N.tail e = Sum.inr u, ∑ p ∈ P, w p * (p.arcs.count e : ℝ) =
      ∑ e with N.head e = Sum.inr u, ∑ p ∈ P, w p * (p.arcs.count e : ℝ) := by
  rw [← sub_eq_zero, sum_filter_eq, sum_filter_eq, ← Finset.sum_sub_distrib]
  simp only [← ind_sub_mul]
  rw [pair_pathflow]
  exact Finset.sum_eq_zero (fun p _ => by rw [path_balance, mul_zero])

/-- scaling a path decomposition type by type gives a feasible flow -/
lemma scaled_feasible (N : Network nd ns I E) (d t : Fin nd → ℝ) (s : Fin ns → ℝ)
    (x : E → ℝ) (hx : Feasible N 1 d s x) (y : SDPath N →₀ ℝ) (hy : IsPathDecomposition N y x)
    (c : Fin nd → ℝ) (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1)
    (hct : ∀ i, c i * d i ≤ t i) :
    Feasible N 1 t s (fun e => ∑ p ∈ y.support, (y p * c p.i) * (p.arcs.count e : ℝ)) ∧
    obj N (fun e => ∑ p ∈ y.support, (y p * c p.i) * (p.arcs.count e : ℝ)) =
      ∑ p ∈ y.support, y p * c p.i * pathValue p := by
  obtain ⟨hbox, hdem, hsup, hbal⟩ := hx
  obtain ⟨hy0, hyx⟩ := hy
  have hle : ∀ e, 0 ≤ ∑ p ∈ y.support, (y p * c p.i) * (p.arcs.count e : ℝ) ∧
      ∑ p ∈ y.support, (y p * c p.i) * (p.arcs.count e : ℝ) ≤ x e := by
    intro e
    rw [← hyx e]
    constructor
    · exact Finset.sum_nonneg (fun p _ => by
        have := hy0 p; have := hc0 p.i; positivity)
    · exact Finset.sum_le_sum (fun p _ => by
        have := hy0 p; have := hc1 p.i
        have hcnt : (0:ℝ) ≤ (p.arcs.count e : ℝ) := by positivity
        have : y p * c p.i ≤ y p := by nlinarith
        exact mul_le_mul_of_nonneg_right this hcnt)
  refine ⟨⟨fun e => ⟨(hle e).1, ((hle e).2.trans (hbox e).2)⟩, fun i => ?_, fun j => ?_,
    fun u => balance_path _ _ u⟩, ?_⟩
  · rw [inflow_path]
    have hin := hdem i
    have hx' : ∑ e with N.head e = Sum.inl i, x e =
        ∑ p ∈ y.support, y p * (if p.i = i then 1 else 0) := by
      rw [← inflow_path]
      exact Finset.sum_congr rfl (fun e _ => (hyx e).symm)
    rw [hx'] at hin
    have : ∑ p ∈ y.support, y p * c p.i * (if p.i = i then 1 else 0) =
        c i * ∑ p ∈ y.support, y p * (if p.i = i then 1 else 0) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun p _ => by split_ifs with h <;> simp [h]; ring)
    rw [this]
    have := mul_le_mul_of_nonneg_left hin (hc0 i)
    linarith [hct i]
  · exact le_trans (Finset.sum_le_sum (fun e _ => (hle e).2)) (hsup j)
  · unfold obj
    rw [pair_pathflow]
    rfl

theorem main_bound {nd ns : ℕ} {I E : Type} [Fintype I] [DecidableEq I] [Fintype E]
    [DecidableEq E]
    (N : Network nd ns I E) (lam beta : Fin nd → ℝ) (pi : Fin ns → ℝ)
    (hlam : 0 ≤ lam) (hlamb : 0 ≤ lam + beta) (hpi : 0 ≤ pi)
    (hsign : (∀ i, 0 ≤ beta i) ∨ (∀ i, beta i ≤ 0))
    (x : E → ℝ) (hx : IsOptimal N 1 (lam + (1 / 2 : ℝ) • beta) pi x)
    (y : SDPath N →₀ ℝ) (hy : IsPathDecomposition N y x)
    (q : DualVar nd ns I E) (hq : IsOptimalDual N 1 (lam + (1 / 2 : ℝ) • beta) pi q) :
    |spFluid q beta - Delta N lam beta pi| ≤
      |rctFluid lam beta (1 / 2) y - Delta N lam beta pi| := by
  set d : Fin nd → ℝ := lam + (1 / 2 : ℝ) • beta with hd_def
  have hdi : ∀ i, d i = lam i + 1 / 2 * beta i := fun i => by simp [d]
  have hlami : ∀ i, 0 ≤ lam i := fun i => hlam i
  have hlambi : ∀ i, 0 ≤ lam i + beta i := fun i => hlamb i
  have hpij : ∀ j, 0 ≤ pi j := fun j => hpi j
  have hd0 : ∀ i, 0 ≤ d i := fun i => by
    rw [hdi]; linarith [hlami i, hlambi i]
  have hd : 0 ≤ d := fun i => hd0 i
  have hqf := hq.1
  have hSD := strong_duality N 1 zero_le_one d pi hd hpi x hx q hq
  -- the three values of Ψ
  set O := obj N x with hO
  set g := spFluid q beta with hg
  set Ψ0 := Phi N 1 lam pi with hΨ0
  set Ψ1 := Phi N 1 (lam + beta) pi with hΨ1
  have hDelta : Delta N lam beta pi = Ψ1 - Ψ0 := by
    simp [Delta, Psi, Ψ0, Ψ1]
  have hsa : ∑ i, q.a i * d i = ∑ i, q.a i * lam i + 1 / 2 * g := by
    simp only [hdi, mul_add, Finset.sum_add_distrib, hg, spFluid, dotProduct, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hsb : ∑ i, q.a i * (lam + beta) i = ∑ i, q.a i * lam i + g := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hg, spFluid, dotProduct]
  have hU0 : Ψ0 ≤ O - 1 / 2 * g := by
    have h := phi_le_dual N 1 lam pi q (zero_feasible N lam pi hlami hpij) hqf
    have : dualObj N 1 lam pi q = dualObj N 1 d pi q - 1 / 2 * g := by
      simp only [dualObj]; linarith
    linarith
  have hU1 : Ψ1 ≤ O + 1 / 2 * g := by
    have h := phi_le_dual N 1 (lam + beta) pi q (zero_feasible N _ pi hlambi hpij) hqf
    have : dualObj N 1 (lam + beta) pi q = dualObj N 1 d pi q + 1 / 2 * g := by
      simp only [dualObj]; linarith
    linarith
  -- path quantities
  set S : Fin nd → ℝ := fun i => ∑ p ∈ y.support with p.i = i, y p * pathValue p with hS
  set vb := vbar (N := N) lam beta (1 / 2) y with hvb
  have hvbi : ∀ i, vb i = S i / d i := fun i => by simp [vb, vbar, S, hdi]
  have hR : rctFluid lam beta (1 / 2) y = ∑ i, vb i * beta i := rfl
  have hfib : ∀ c : Fin nd → ℝ, ∑ p ∈ y.support, y p * c p.i * pathValue p =
      ∑ i, c i * S i := by
    intro c
    rw [← Finset.sum_fiberwise y.support (fun p => p.i)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [S, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [(Finset.mem_filter.mp hp).2]; ring
  -- S i = vb i * d i
  have hSvd : ∀ i, S i = vb i * d i := by
    intro i
    rw [hvbi]
    by_cases hdz : d i = 0
    · rw [hdz, mul_zero]
      -- no flow ends at i
      have hin := hx.1.2.1 i
      have hx' : ∑ e with N.head e = Sum.inl i, x e =
          ∑ p ∈ y.support, y p * (if p.i = i then 1 else 0) := by
        rw [← inflow_path]
        exact Finset.sum_congr rfl (fun e _ => (hy.2 e).symm)
      rw [hx', hdz] at hin
      have hz : ∀ p ∈ y.support, y p * (if p.i = i then 1 else 0) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => by
          have := hy.1 p; split_ifs <;> simp [this])).mp
          (le_antisymm hin (Finset.sum_nonneg (fun p _ => by
            have := hy.1 p; split_ifs <;> simp [this])))
      refine Finset.sum_eq_zero (fun p hp => ?_)
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
      have := hz p hp1
      simp [hp2] at this
      simp [this]
    · field_simp
  have hOS : O = ∑ i, S i := by
    have := hfib (fun _ => 1)
    simp only [mul_one, one_mul] at this
    rw [← this, hO]
    unfold obj
    have hxe : ∀ e, x e = ∑ p ∈ y.support, y p * (p.arcs.count e : ℝ) := fun e => (hy.2 e).symm
    simp only [hxe, pair_pathflow]
    rfl
  have hOv : O = ∑ i, vb i * lam i + 1 / 2 * ∑ i, vb i * beta i := by
    rw [hOS, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by rw [hSvd, hdi]; ring)
  -- lower bound from a scaled flow
  have hlow : ∀ t : Fin nd → ℝ, (∀ i, 0 ≤ t i) → (∀ i, t i ≤ d i) →
      ∑ i, vb i * t i ≤ Phi N 1 t pi := by
    intro t ht0 htd
    set c : Fin nd → ℝ := fun i => t i / d i
    have hc0 : ∀ i, 0 ≤ c i := fun i => div_nonneg (ht0 i) (hd0 i)
    have hc1 : ∀ i, c i ≤ 1 := fun i => div_le_one_of_le₀ (htd i) (hd0 i)
    have hct : ∀ i, c i * d i ≤ t i := by
      intro i
      by_cases hdz : d i = 0
      · simp [hdz, ht0 i]
      · simp only [c]; rw [div_mul_cancel₀ _ hdz]
    obtain ⟨hf, hobj⟩ := scaled_feasible N d t pi x hx.1 y hy c hc0 hc1 hct
    have := le_phi N 1 t pi q _ hf hqf
    rw [hobj, hfib] at this
    have heq : ∑ i, c i * S i = ∑ i, vb i * t i :=
      Finset.sum_congr rfl (fun i _ => by simp only [c]; rw [hvbi]; ring)
    linarith
  rw [hDelta, hR]
  set R := ∑ i, vb i * beta i with hRdef
  have hSP : |g - (Ψ1 - Ψ0)| ≤ 2 * O - Ψ1 - Ψ0 := by
    rw [abs_le]; constructor <;> linarith
  rcases hsign with hpos | hneg
  · have h := hlow lam hlami (fun i => by rw [hdi]; linarith [hpos i])
    have : 2 * O - Ψ1 - Ψ0 ≤ R - (Ψ1 - Ψ0) := by linarith
    exact hSP.trans (this.trans (le_abs_self _))
  · have h := hlow (lam + beta) hlambi (fun i => by
      rw [hdi]; simp only [Pi.add_apply]; linarith [hneg i])
    have hM : ∑ i, vb i * (lam + beta) i = ∑ i, vb i * lam i + R := by
      rw [hRdef]; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    have : 2 * O - Ψ1 - Ψ0 ≤ -(R - (Ψ1 - Ψ0)) := by linarith
    exact hSP.trans (this.trans (neg_le_abs _))

end MIFBThm4Proof


open MarketInterference.FluidBias in
theorem solution {nd ns : ℕ} {I E : Type} [Fintype I] [DecidableEq I] [Fintype E]
    [DecidableEq E]
    (N : Network nd ns I E) (lam beta : Fin nd → ℝ) (pi : Fin ns → ℝ)
    (hlam : 0 ≤ lam) (hlamb : 0 ≤ lam + beta) (hpi : 0 ≤ pi)
    (hsign : (∀ i, 0 ≤ beta i) ∨ (∀ i, beta i ≤ 0))
    (hA2p : ∃! x, IsOptimal N 1 (lam + (1 / 2 : ℝ) • beta) pi x)
    (hA2d : ∃! q, IsOptimalDual N 1 (lam + (1 / 2 : ℝ) • beta) pi q)
    (x : E → ℝ) (hx : IsOptimal N 1 (lam + (1 / 2 : ℝ) • beta) pi x)
    (y : SDPath N →₀ ℝ) (hy : IsPathDecomposition N y x)
    (q : DualVar nd ns I E) (hq : IsOptimalDual N 1 (lam + (1 / 2 : ℝ) • beta) pi q) :
    |spFluid q beta - Delta N lam beta pi| ≤
      |rctFluid lam beta (1 / 2) y - Delta N lam beta pi| :=
  MIFBThm4Proof.main_bound N lam beta pi hlam hlamb hpi hsign x hx y hy q hq
