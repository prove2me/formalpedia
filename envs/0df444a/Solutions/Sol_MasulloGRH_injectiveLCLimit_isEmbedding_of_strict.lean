-- Prove2me | solution 1 for MasulloGRH.injectiveLCLimit_isEmbedding_of_strict
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:28:54.704089+00:00
-- url     : https://prove2.me/submissions/843d174c-2ae9-440f-9c24-bbb4a79dd4e6

import Mathlib
import Definitions.Def_RiemannMasullo_AppC_InductiveLimits

open Topology

set_option autoImplicit false

namespace Sol_MasulloGRH_injectiveLCLimit_isEmbedding_of_strict

open RiemannMasullo Set Filter

/-- **Extension of a continuous seminorm along an inducing linear map.**  If `f : M → F` is a
linear map into a locally convex space `F` and `M` carries the topology induced by `f`, then
every continuous seminorm `p` on `M` is of the form `q ∘ f` for a continuous seminorm `q` on `F`.
The extension is the infimal convolution `q y = ⨅ x, p x + r (y - f x)`, where `r` is a
continuous seminorm on `F` with `p ≤ r ∘ f`. -/
theorem exists_seminorm_extension {M F : Type*} [AddCommGroup M] [Module ℂ M]
    [TopologicalSpace M] [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [PolynormableSpace ℂ F] {f : M →ₗ[ℂ] F} (hf : IsInducing f)
    {p : Seminorm ℂ M} (hp : Continuous p) :
    ∃ q : Seminorm ℂ F, Continuous q ∧ ∀ x, q (f x) = p x := by
  obtain ⟨r, hr, hpr⟩ := Seminorm.exists_le_comp_of_isInducing hp hf
  have hpr' : ∀ x, p x ≤ r (f x) := fun x => Seminorm.le_def.1 hpr x
  let cost (y : F) (x : M) : ℝ := p x + r (y - f x)
  have hcost_nonneg : ∀ y x, 0 ≤ cost y x := fun y x =>
    add_nonneg (apply_nonneg p x) (apply_nonneg r _)
  have hbounded : ∀ y : F, BddBelow (range (cost y)) := fun y =>
    ⟨0, forall_mem_range.mpr fun x => hcost_nonneg y x⟩
  let s (y : F) : ℝ := ⨅ x, cost y x
  have hs_le : ∀ (y : F) (x : M), s y ≤ cost y x := fun y x => ciInf_le (hbounded y) x
  have hs_nonneg : ∀ y, 0 ≤ s y := fun y => le_ciInf fun x => hcost_nonneg y x
  have hsr : ∀ y : F, s y ≤ r y := by
    intro y
    have h := hs_le y 0
    simpa [cost] using h
  have hs_zero : s 0 = 0 := le_antisymm ((hsr 0).trans_eq (map_zero r)) (hs_nonneg 0)
  let q : Seminorm ℂ F := Seminorm.ofSMulLE s hs_zero
    (by
      intro y z
      refine le_ciInf_add_ciInf fun x w => (hs_le (y + z) (x + w)).trans ?_
      have h1 : p (x + w) ≤ p x + p w := map_add_le_add p x w
      have h2 : r (y + z - f (x + w)) ≤ r (y - f x) + r (z - f w) := by
        have h3 : y + z - f (x + w) = (y - f x) + (z - f w) := by
          rw [map_add f]; abel
        rw [h3]
        exact map_add_le_add r _ _
      show p (x + w) + r (y + z - f (x + w)) ≤ p x + r (y - f x) + (p w + r (z - f w))
      linarith)
    (by
      intro a y
      show s (a • y) ≤ ‖a‖ * ⨅ x, cost y x
      rw [Real.mul_iInf_of_nonneg (norm_nonneg a)]
      refine le_ciInf fun x => (hs_le (a • y) (a • x)).trans_eq ?_
      show p (a • x) + r (a • y - f (a • x)) = ‖a‖ * (p x + r (y - f x))
      rw [map_smul f, ← smul_sub, map_smul_eq_mul, map_smul_eq_mul, mul_add])
  have hq : ∀ y, q y = s y := fun _ => rfl
  refine ⟨q, Seminorm.continuous_of_le hr (Seminorm.le_def.2 fun y => (hq y).trans_le (hsr y)), ?_⟩
  intro x
  rw [hq]
  apply le_antisymm
  · have h := hs_le (f x) x
    simpa [cost] using h
  · refine le_ciInf fun w => ?_
    have h1 : p x ≤ p w + p (x - w) := by
      have := map_add_le_add p w (x - w)
      rwa [add_sub_cancel] at this
    have h2 : p (x - w) ≤ r (f x - f w) := by
      have := hpr' (x - w)
      rwa [map_sub f] at this
    show p x ≤ p w + r (f x - f w)
    linarith

section limit

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  {X : ℕ → Type*} [∀ k, AddCommGroup (X k)] [∀ k, Module ℂ (X k)]
  [∀ k, TopologicalSpace (X k)]
  {j : ∀ k, X k →L[ℂ] X (k + 1)} {i : ∀ k, X k →L[ℂ] E}

/-- The topology of an injective locally convex limit is the topology of the family of all
seminorms that are continuous on every stage. -/
theorem withSeminorms (h : IsInjectiveLCLimit j i) :
    WithSeminorms
      (Subtype.val : {s : Seminorm ℂ E // ∀ k, Continuous (s ∘ i k)} → Seminorm ℂ E) :=
  ⟨h.topology_eq⟩

/-- **Key step.**  In a strict system, a continuous seminorm `p` on a stage `X n` is the
restriction along `i n` of a continuous seminorm on the limit. -/
theorem seminorm_extension [∀ k, IsTopologicalAddGroup (X k)] [∀ k, PolynormableSpace ℂ (X k)]
    (h : IsInjectiveLCLimit j i) (hj : ∀ k, IsEmbedding (j k)) (n : ℕ)
    (p : Seminorm ℂ (X n)) (hp : Continuous p) :
    ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ z, q (i n z) = p z := by
  classical
  have hstep : ∀ (k : ℕ) (z : X k), i (k + 1) (j k z) = i k z := fun k z =>
    DFunLike.congr_fun (h.compatible k) z
  -- transition maps between arbitrary stages
  have htransition : ∀ a b : ℕ, a ≤ b → ∃ f : X a →L[ℂ] X b, ∀ z, i b (f z) = i a z := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => exact ⟨ContinuousLinearMap.id ℂ _, fun _ => rfl⟩
    | succ b _ ih =>
      obtain ⟨f, hf⟩ := ih
      exact ⟨(j b).comp f, fun z => (hstep b (f z)).trans (hf z)⟩
  choose f hf using fun k (hk : k ≤ n) => htransition k n hk
  let C (k : ℕ) := {s : Seminorm ℂ (X k) // Continuous s}
  -- on the stages below `n`: pull `p` back
  let base (k : ℕ) (hk : k ≤ n) : C k :=
    ⟨p.comp (f k hk).toLinearMap, hp.comp (f k hk).continuous⟩
  -- one extension step, from stage `k` to stage `k + 1`
  have hext : ∀ (k : ℕ) (s : C k), ∃ t : Seminorm ℂ (X (k + 1)),
      Continuous t ∧ ∀ z, t (j k z) = s.val z := fun k s =>
    exists_seminorm_extension (f := (j k).toLinearMap) (hj k).isInducing s.property
  choose next hnext hnextcomp using hext
  -- pull back to the earlier stages and extend successively to the later stages
  let r : ∀ k, C k := fun k => Nat.rec (motive := fun k => C k) (base 0 (Nat.zero_le n))
    (fun k s => if hk : k + 1 ≤ n then base (k + 1) hk else ⟨next k s, hnext k s⟩) k
  have hrsucc : ∀ k, r (k + 1) =
      if hk : k + 1 ≤ n then base (k + 1) hk else ⟨next k (r k), hnext k (r k)⟩ := fun _ => rfl
  have hrbase : ∀ (k : ℕ) (hk : k ≤ n), r k = base k hk := by
    intro k hk
    cases k with
    | zero => rfl
    | succ k => rw [hrsucc, dif_pos hk]
  have hr : ∀ (k : ℕ) (z : X k), (r (k + 1)).val (j k z) = (r k).val z := by
    intro k z
    by_cases hk : k + 1 ≤ n
    · rw [hrbase _ hk, hrbase _ (Nat.le_of_succ_le hk)]
      show p (f (k + 1) hk (j k z)) = p (f k _ z)
      congr 1
      apply h.injective n
      exact (hf (k + 1) hk (j k z)).trans ((hstep k z).trans (hf k _ z).symm)
    · rw [hrsucc, dif_neg hk]
      exact hnextcomp k (r k) z
  have hlift : ∀ (a : ℕ) (x : X a) (b : ℕ), a ≤ b →
      ∃ y : X b, i b y = i a x ∧ (r b).val y = (r a).val x := by
    intro a x b hab
    induction b, hab using Nat.le_induction with
    | base => exact ⟨x, rfl, rfl⟩
    | succ b _ ih =>
      obtain ⟨y, hy, hy'⟩ := ih
      exact ⟨j b y, (hstep b y).trans hy, (hr b y).trans hy'⟩
  -- two representatives of the same point of `E` have the same value
  have hagree : ∀ {a b : ℕ} {x : X a} {y : X b}, i a x = i b y →
      (r a).val x = (r b).val y := by
    intro a b x y he
    obtain ⟨x', hx', hx⟩ := hlift a x (max a b) (le_max_left _ _)
    obtain ⟨y', hy', hy⟩ := hlift b y (max a b) (le_max_right _ _)
    have he' : x' = y' := h.injective (max a b) (hx'.trans (he.trans hy'.symm))
    exact hx.symm.trans ((congrArg (r (max a b)).val he').trans hy)
  choose stage repr hrepr using h.exhaustive
  let s (x : E) : ℝ := (r (stage x)).val (repr x)
  have hs : ∀ (k : ℕ) (z : X k), s (i k z) = (r k).val z := fun k z => hagree (hrepr (i k z))
  let q : Seminorm ℂ E := Seminorm.ofSMulLE s
    (by
      have h0 := hs 0 0
      rw [map_zero, map_zero] at h0
      exact h0)
    (fun x y => by
      obtain ⟨u, hu, -⟩ := hlift _ (repr x) (max (stage x) (stage y)) (le_max_left _ _)
      obtain ⟨v, hv, -⟩ := hlift _ (repr y) (max (stage x) (stage y)) (le_max_right _ _)
      have hx : s x = (r _).val u := by
        rw [← hs _ u, hu, hrepr x]
      have hy : s y = (r _).val v := by
        rw [← hs _ v, hv, hrepr y]
      have hxy : s (x + y) = (r _).val (u + v) := by
        rw [← hs _ (u + v), map_add, hu, hv, hrepr x, hrepr y]
      rw [hx, hy, hxy]
      exact map_add_le_add (r _).val u v)
    (fun a x => by
      have hx : s x = (r _).val (repr x) := rfl
      have hax : s (a • x) = (r _).val (a • repr x) := by
        rw [← hs _ (a • repr x), map_smul, hrepr x]
      rw [hx, hax, map_smul_eq_mul])
  have hq : ∀ (k : ℕ) (z : X k), q (i k z) = (r k).val z := hs
  refine ⟨q, (withSeminorms h).continuous_seminorm ⟨q, fun k => ?_⟩, ?_⟩
  · have h1 : (q ∘ i k) = (r k).val := funext fun z => hq k z
    rw [h1]
    exact (r k).property
  · intro z
    rw [hq, hrbase n le_rfl]
    show p (f n le_rfl z) = p z
    congr 1
    exact h.injective n (hf n le_rfl z)

end limit

end Sol_MasulloGRH_injectiveLCLimit_isEmbedding_of_strict

open Sol_MasulloGRH_injectiveLCLimit_isEmbedding_of_strict

theorem solution {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E]
    {X : ℕ → Type*} [∀ k, AddCommGroup (X k)] [∀ k, Module ℂ (X k)]
    [∀ k, TopologicalSpace (X k)] [∀ k, IsTopologicalAddGroup (X k)]
    [∀ k, PolynormableSpace ℂ (X k)]
    {j : ∀ k, X k →L[ℂ] X (k + 1)} {i : ∀ k, X k →L[ℂ] E}
    (h : RiemannMasullo.IsInjectiveLCLimit j i) (hj : ∀ k, Topology.IsEmbedding (j k)) :
    (∀ k, Topology.IsEmbedding (i k)) ∧ ((∀ k, T2Space (X k)) → T2Space E) := by
  have hE := withSeminorms h
  have hgrp : IsTopologicalAddGroup E := hE.topologicalAddGroup
  refine ⟨fun k => ⟨?_, h.injective k⟩, fun hT2 => ?_⟩
  · -- the topology of `X k` is induced by `i k`
    refine IsTopologicalAddGroup.isInducing_iff_nhds_zero.mpr (le_antisymm ?_ ?_)
    · have h0 : Filter.Tendsto (i k) (𝓝 0) (𝓝 0) := by
        have := (i k).continuous.tendsto 0
        rwa [map_zero] at this
      exact Filter.map_le_iff_le_comap.mp h0
    · refine ((PolynormableSpace.withSeminorms ℂ (X k)).hasBasis_zero_ball).ge_iff.mpr ?_
      rintro ⟨s, r⟩ hr
      -- a basic neighbourhood: a ball of a finite supremum of continuous seminorms
      let P : SeminormFamily ℂ (X k) {p : Seminorm ℂ (X k) // Continuous p} := fun p => p.1
      have hpc : Continuous (s.sup P : Seminorm ℂ (X k)) :=
        Seminorm.continuous_finsetSup
          fun (p : {p : Seminorm ℂ (X k) // Continuous p}) _ => p.2
      obtain ⟨q, hq, heq⟩ := seminorm_extension h hj k (s.sup P) hpc
      have hball : q.ball 0 r ∈ 𝓝 (0 : E) := by
        have hsub : q ⁻¹' Set.Iio r ⊆ q.ball 0 r := fun x hx =>
          (Seminorm.mem_ball_zero _).mpr hx
        refine Filter.mem_of_superset ((isOpen_Iio.preimage hq).mem_nhds ?_) hsub
        show q 0 < r
        rw [map_zero]
        exact hr
      refine Filter.mem_comap.mpr ⟨q.ball 0 r, hball, ?_⟩
      intro z hz
      have hz' : q (i k z) < r := (Seminorm.mem_ball_zero _).mp hz
      rw [heq z] at hz'
      exact (Seminorm.mem_ball_zero _).mpr hz'
  · -- separation: the continuous seminorms of the limit separate points
    have hT1 : T1Space E := by
      refine WithSeminorms.T1_of_separating hE ?_
      intro x hx
      obtain ⟨k, z, rfl⟩ := h.exhaustive x
      have hz : z ≠ 0 := by
        rintro rfl
        exact hx (map_zero (i k))
      have hT2k : T2Space (X k) := hT2 k
      obtain ⟨p, hp⟩ :=
        WithSeminorms.separating_of_T1 (PolynormableSpace.withSeminorms ℂ (X k)) z hz
      obtain ⟨q, hq, heq⟩ := seminorm_extension h hj k p.1 p.2
      refine ⟨⟨q, fun m => hq.comp (i m).continuous⟩, ?_⟩
      show q (i k z) ≠ 0
      rw [heq z]
      exact hp
    exact inferInstance
