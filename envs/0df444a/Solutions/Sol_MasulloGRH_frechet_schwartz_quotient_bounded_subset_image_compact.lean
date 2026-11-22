-- Prove2me | solution 1 for MasulloGRH.frechet_schwartz_quotient_bounded_subset_image_compact
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:52:54.722947+00:00
-- url     : https://prove2.me/submissions/5a2cdcc3-2b44-4da5-a465-4439acfb6be0

import Mathlib
import Definitions.Def_MasulloGRH_LocallyConvex
import Definitions.Def_LocallyConvex_SchwartzSpace

open Topology

set_option autoImplicit false

open MasulloGRH

namespace Sol_MasulloGRH_frechet_schwartz_quotient_bounded_subset_image_compact

section complete

open Uniformity

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]

/-- For a topological vector space, the Cauchy filters of the additive uniform structure are the
filters that are Cauchy in the sense of `IsCauchyFilter`. -/
theorem cauchy_iff_isCauchyFilter (f : Filter E) :
    @Cauchy E (IsTopologicalAddGroup.rightUniformSpace E) f ↔ IsCauchyFilter f := by
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  rw [cauchy_iff]
  refine and_congr Iff.rfl ⟨fun h U hU => ?_, fun h s hs => ?_⟩
  · have h2 : (fun p : E × E => p.2 + -p.1) ⁻¹' U ∈ 𝓤 E := by
      rw [uniformity_eq_comap_nhds_zero' E]
      exact Filter.preimage_mem_comap hU
    obtain ⟨A, hA, hAU⟩ := h _ h2
    refine ⟨A, hA, fun x hx y hy => ?_⟩
    have h3 : x + -y ∈ U := hAU (Set.mk_mem_prod hy hx)
    rwa [← sub_eq_add_neg] at h3
  · rw [uniformity_eq_comap_nhds_zero' E] at hs
    obtain ⟨U, hU, hUs⟩ := Filter.mem_comap.mp hs
    obtain ⟨A, hA, hAU⟩ := h U hU
    refine ⟨A, hA, fun q hq => hUs ?_⟩
    have h3 : q.2 - q.1 ∈ U := hAU q.2 hq.2 q.1 hq.1
    rwa [sub_eq_add_neg] at h3

/-- Completeness in the sense of `IsCompleteTVS` gives completeness of the additive uniform
structure. -/
theorem completeSpace_of_isCompleteTVS (h : IsCompleteTVS E) :
    @CompleteSpace E (IsTopologicalAddGroup.rightUniformSpace E) := by
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  exact ⟨fun {f} hf => h.2 f ((cauchy_iff_isCauchyFilter f).mp hf)⟩

end complete

section lift

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]

/-- `A` is precompact modulo the subgroup `N`: for every `0`-neighbourhood `V`, finitely many
translates of `V + N` cover `A`. -/
def PrecompactMod (N : AddSubgroup E) (A : Set E) : Prop :=
  ∀ V ∈ 𝓝 (0 : E), ∃ F : Set E, F.Finite ∧ ∀ a ∈ A, ∃ f ∈ F, ∃ w ∈ N, a - f - w ∈ V

/-- The centres of the covering translates can be taken in the set itself. -/
theorem PrecompactMod.exists_inner {N : AddSubgroup E} {A : Set E} (hA : PrecompactMod N A)
    {V : Set E} (hV : V ∈ 𝓝 (0 : E)) :
    ∃ F : Set E, F.Finite ∧ F ⊆ A ∧ ∀ a ∈ A, ∃ f ∈ F, ∃ w ∈ N, a - f - w ∈ V := by
  classical
  obtain ⟨V', hV', hsub⟩ : ∃ V' ∈ 𝓝 (0 : E), ∀ x ∈ V', ∀ y ∈ V', x - y ∈ V := by
    have h1 : Filter.Tendsto (fun q : E × E => q.1 - q.2) (𝓝 ((0 : E), (0 : E))) (𝓝 (0 : E)) :=
      continuous_sub.tendsto' _ _ (sub_zero 0)
    have h2 := h1 hV
    rw [Filter.mem_map, nhds_prod_eq, Filter.mem_prod_iff] at h2
    obtain ⟨V1, h1', V2, h2', h12⟩ := h2
    exact ⟨V1 ∩ V2, Filter.inter_mem h1' h2', fun x hx y hy => h12 (Set.mk_mem_prod hx.1 hy.2)⟩
  obtain ⟨F0, hF0, hnet⟩ := hA V' hV'
  have hch : ∀ f : E, (∃ a ∈ A, ∃ w ∈ N, a - f - w ∈ V') →
      ∃ a : E, a ∈ A ∧ ∃ w ∈ N, a - f - w ∈ V' := fun f h => h
  choose! g hg using hch
  refine ⟨g '' {f ∈ F0 | ∃ a ∈ A, ∃ w ∈ N, a - f - w ∈ V'},
    (hF0.subset (Set.sep_subset _ _)).image g, ?_, ?_⟩
  · rintro _ ⟨f, ⟨-, hf⟩, rfl⟩
    exact (hg f hf).1
  · intro a ha
    obtain ⟨f, hf, w, hw, hafw⟩ := hnet a ha
    have hgood : ∃ a ∈ A, ∃ w ∈ N, a - f - w ∈ V' := ⟨a, ha, w, hw, hafw⟩
    obtain ⟨-, w0, hw0, hg0⟩ := hg f hgood
    refine ⟨g f, ⟨f, ⟨hf, hgood⟩, rfl⟩, w - w0, N.sub_mem hw hw0, ?_⟩
    have h3 := hsub _ hafw _ hg0
    have h4 : a - g f - (w - w0) = a - f - w - (g f - f - w0) := by abel
    rw [h4]
    exact h3

omit [IsTopologicalAddGroup E] in
/-- Translating by a finite set, moving by elements of `N` and passing to a subset preserve
precompactness modulo `N`. -/
theorem PrecompactMod.step {N : AddSubgroup E} {A : Set E} (hA : PrecompactMod N A) {F : Set E}
    (hF : F.Finite) (V : Set E) :
    PrecompactMod N {x | x ∈ V ∧ ∃ a ∈ A, ∃ f ∈ F, ∃ w ∈ N, x = a - f - w} := by
  intro V' hV'
  obtain ⟨G, hG, hnet⟩ := hA V' hV'
  refine ⟨Set.image2 (fun g f => g - f) G F, hG.image2 _ hF, ?_⟩
  rintro x ⟨-, a, ha, f, hf, w, hw, rfl⟩
  obtain ⟨g, hg, w', hw', h⟩ := hnet a ha
  refine ⟨g - f, Set.mem_image2_of_mem hg hf, w' - w, N.sub_mem hw' hw, ?_⟩
  have h4 : a - f - w - (g - f) - (w' - w) = a - g - w' := by abel
  rw [h4]
  exact h

open Classical in
/-- A finite set of centres in `A` for the neighbourhood `V` (empty if there is none). -/
noncomputable def net (N : AddSubgroup E) (A V : Set E) : Set E :=
  if h : PrecompactMod N A ∧ V ∈ 𝓝 (0 : E) then (h.1.exists_inner h.2).choose else ∅

theorem net_spec {N : AddSubgroup E} {A V : Set E} (hA : PrecompactMod N A)
    (hV : V ∈ 𝓝 (0 : E)) :
    (net N A V).Finite ∧ net N A V ⊆ A ∧ ∀ a ∈ A, ∃ f ∈ net N A V, ∃ w ∈ N, a - f - w ∈ V := by
  have h : PrecompactMod N A ∧ V ∈ 𝓝 (0 : E) := ⟨hA, hV⟩
  simp only [net, dif_pos h]
  exact (h.1.exists_inner h.2).choose_spec

/-- The successive remainders: `As (n + 1)` consists of the `a - f - w ∈ U (n + 1)` with
`a ∈ As n`, `f` in the chosen finite net of `As n` and `w ∈ N`. -/
noncomputable def As (N : AddSubgroup E) (U : ℕ → Set E) (A : Set E) : ℕ → Set E
  | 0 => A
  | n + 1 => {x | x ∈ U (n + 1) ∧
      ∃ a ∈ As N U A n, ∃ f ∈ net N (As N U A n) (U (n + 1)), ∃ w ∈ N, x = a - f - w}

/-- The finite sets of partial sums `f₀ + ⋯ + f_{n-1}`, `fᵢ` in the `i`-th net. -/
noncomputable def Ts (N : AddSubgroup E) (U : ℕ → Set E) (A : Set E) : ℕ → Set E
  | 0 => {0}
  | n + 1 => Set.image2 (fun s f => s + f) (Ts N U A n) (net N (As N U A n) (U (n + 1)))

/-- **Lifting of precompact sets.** Let `E` be a first countable complete commutative topological
group and `N` a closed subgroup.  If `A ⊆ E` is precompact modulo `N`, there is a compact set
`C ⊆ E` meeting every coset `a + N`, `a ∈ A`. -/
theorem exists_compact_lift [FirstCountableTopology E] (N : AddSubgroup E)
    (hN : IsClosed (N : Set E))
    (hc : @CompleteSpace E (IsTopologicalAddGroup.rightUniformSpace E))
    (A : Set E) (hA : PrecompactMod N A) :
    ∃ C : Set E, IsCompact C ∧ ∀ a ∈ A, ∃ c ∈ C, a - c ∈ N := by
  obtain ⟨U, hU, hUU⟩ := IsTopologicalAddGroup.exists_antitone_basis_nhds_zero E
  have hU0 : ∀ n, U n ∈ 𝓝 (0 : E) := fun n => hU.1.mem_of_mem trivial
  have h0U : ∀ n, (0 : E) ∈ U n := fun n => mem_of_mem_nhds (hU0 n)
  -- the remainders are precompact modulo `N`
  have hAs : ∀ n, PrecompactMod N (As N U A n) := by
    intro n
    induction n with
    | zero => exact hA
    | succ n ih => exact ih.step (net_spec ih (hU0 (n + 1))).1 (U (n + 1))
  have hFfin : ∀ n, (net N (As N U A n) (U (n + 1))).Finite := fun n =>
    (net_spec (hAs n) (hU0 (n + 1))).1
  have hFsub : ∀ n, net N (As N U A n) (U (n + 1)) ⊆ As N U A n := fun n =>
    (net_spec (hAs n) (hU0 (n + 1))).2.1
  have hFnet : ∀ n, ∀ a ∈ As N U A n,
      ∃ f ∈ net N (As N U A n) (U (n + 1)), ∃ w ∈ N, a - f - w ∈ U (n + 1) := fun n =>
    (net_spec (hAs n) (hU0 (n + 1))).2.2
  have hAsU : ∀ n, As N U A (n + 1) ⊆ U (n + 1) := fun n x hx => hx.1
  have hFU : ∀ n, net N (As N U A (n + 1)) (U (n + 1 + 1)) ⊆ U (n + 1) := fun n =>
    (hFsub (n + 1)).trans (hAsU n)
  have hTfin : ∀ n, (Ts N U A n).Finite := by
    intro n
    induction n with
    | zero => exact Set.finite_singleton 0
    | succ n ih => exact ih.image2 _ (hFfin n)
  -- every element of `A` is, modulo `N`, a partial sum plus a remainder
  have hQ : ∀ a ∈ A, ∀ n, ∃ s ∈ Ts N U A n, ∃ w ∈ N, a - s - w ∈ As N U A n := by
    intro a ha n
    induction n with
    | zero =>
      refine ⟨0, rfl, 0, N.zero_mem, ?_⟩
      have h4 : a - 0 - 0 = a := by abel
      rw [h4]
      exact ha
    | succ n ih =>
      obtain ⟨s, hs, w, hw, hsw⟩ := ih
      obtain ⟨f, hf, w', hw', hfw⟩ := hFnet n _ hsw
      refine ⟨s + f, Set.mem_image2_of_mem hs hf, w + w', N.add_mem hw hw', ?_⟩
      have h4 : a - (s + f) - (w + w') = a - s - w - f - w' := by abel
      refine ⟨?_, a - s - w, hsw, f, hf, w', hw', h4⟩
      rw [h4]
      exact hfw
  -- the partial sums of length `≥ m + 1` are `U m`-close to those of length `m + 1`
  have hT : ∀ k m, Ts N U A (m + 1 + k) ⊆ {x | ∃ t ∈ Ts N U A (m + 1), ∃ u ∈ U m, x = t + u} := by
    intro k
    induction k with
    | zero =>
      intro m x hx
      exact ⟨x, hx, 0, h0U m, (add_zero x).symm⟩
    | succ k ih =>
      intro m x hx
      have hidx : m + 1 + (k + 1) = m + 1 + 1 + k := by omega
      rw [hidx] at hx
      obtain ⟨t, ht, u, hu, rfl⟩ := ih (m + 1) hx
      obtain ⟨t', ht', f, hf, rfl⟩ := ht
      refine ⟨t', ht', f + u, hUU m (Set.add_mem_add (hFU m hf) hu), ?_⟩
      exact add_assoc t' f u
  -- the closure of the set of all partial sums is compact
  have hcompact : IsCompact (closure (⋃ n, Ts N U A n)) := by
    let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
    have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
    have htb : TotallyBounded (⋃ n, Ts N U A n) := by
      rw [totallyBounded_iff_subset_finite_iUnion_nhds_zero]
      intro V hV
      obtain ⟨m, -, hm⟩ := hU.1.mem_iff.mp hV
      refine ⟨⋃ n ∈ {i : ℕ | i ≤ m + 1}, Ts N U A n,
        (Set.finite_le_nat (m + 1)).biUnion fun n _ => hTfin n, ?_⟩
      intro x hx
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
      rcases le_total n (m + 1) with hnm | hnm
      · refine Set.mem_iUnion₂.mpr ⟨x, Set.mem_iUnion₂.mpr ⟨n, hnm, hn⟩, ?_⟩
        exact Set.mem_vadd_set.mpr ⟨0, mem_of_mem_nhds hV, add_zero x⟩
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
        obtain ⟨t, ht, u, hu, rfl⟩ := hT k m hn
        refine Set.mem_iUnion₂.mpr ⟨t, Set.mem_iUnion₂.mpr ⟨m + 1, (le_refl (m + 1) : m + 1 ≤ m + 1), ht⟩, ?_⟩
        exact Set.mem_vadd_set.mpr ⟨u, hm hu, rfl⟩
    exact htb.closure.isCompact_of_isClosed isClosed_closure
  refine ⟨closure (⋃ n, Ts N U A n), hcompact, fun a ha => ?_⟩
  -- partial sums `s n` with `a - s n ∈ U (n + 1) + N`
  have hex : ∀ n, ∃ s ∈ Ts N U A (n + 1), ∃ w ∈ N, a - s - w ∈ U (n + 1) := by
    intro n
    obtain ⟨s, hs, w, hw, hsw⟩ := hQ a ha (n + 1)
    exact ⟨s, hs, w, hw, hAsU n hsw⟩
  choose s hs w hw hsw using hex
  have hsC : ∀ n, s n ∈ closure (⋃ n, Ts N U A n) := fun n =>
    subset_closure (Set.mem_iUnion.mpr ⟨n + 1, hs n⟩)
  obtain ⟨c, hcC, φ, hφ, hlim⟩ := hcompact.tendsto_subseq hsC
  refine ⟨c, hcC, ?_⟩
  -- the remainders tend to `0`
  have hu : Filter.Tendsto (fun n => a - s (φ n) - w (φ n)) Filter.atTop (𝓝 (0 : E)) := by
    refine hU.tendsto fun n => ?_
    exact hU.2 ((hφ.id_le n).trans (Nat.le_succ _)) (hsw (φ n))
  -- hence `w (φ n) → a - c`
  have hw' : Filter.Tendsto (fun n => w (φ n)) Filter.atTop (𝓝 (a - c)) := by
    have h1 : Filter.Tendsto (fun n => a - s (φ n) - (a - s (φ n) - w (φ n))) Filter.atTop
        (𝓝 (a - c - 0)) := (tendsto_const_nhds.sub hlim).sub hu
    rw [sub_zero] at h1
    refine h1.congr fun n => ?_
    abel
  exact hN.mem_of_tendsto hw' (Filter.Eventually.of_forall fun n => hw (φ n))

end lift

end Sol_MasulloGRH_frechet_schwartz_quotient_bounded_subset_image_compact

open Sol_MasulloGRH_frechet_schwartz_quotient_bounded_subset_image_compact Pointwise in
theorem solution (E : Type*) [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] (hF : IsFrechet E) (hS : IsSchwartzLCS E)
    (W : Submodule ℂ E) (hW : IsClosed (W : Set E)) (B : Set (E ⧸ W))
    (hB : Bornology.IsVonNBounded ℂ B) :
    ∃ C : Set E, IsCompact C ∧ B ⊆ W.mkQ '' C := by
  obtain ⟨hlc, hcomp, hmet⟩ := hF
  obtain ⟨ι, _, p, hp⟩ := id hlc
  have := hp.topologicalAddGroup
  have := hp.continuousSMul
  have hc := completeSpace_of_isCompleteTVS hcomp
  -- the preimage of `B` is precompact modulo `W`
  have hpre : PrecompactMod W.toAddSubgroup (W.mkQ ⁻¹' B) := by
    intro V hV
    obtain ⟨⟨s, ρ⟩, hρ, hsub⟩ := hp.hasBasis_zero_ball.mem_iff.mp hV
    have hρ' : 0 < ρ := hρ
    let P : Seminorm ℂ E := s.sup p
    have hsub' : P.ball 0 ρ ⊆ V := hsub
    have hPcont : Continuous P :=
      Seminorm.continuous (r := ρ) (hp.hasBasis_zero_ball.mem_of_mem (i := (s, ρ)) hρ)
    obtain ⟨V', hV', hfin⟩ := hS.2 P hPcont
    have hqV' : W.mkQ '' V' ∈ 𝓝 (0 : E ⧸ W) := by
      have h := W.isOpenMap_mkQ.image_mem_nhds hV'
      rwa [map_zero] at h
    obtain ⟨R, hR, habs⟩ := (hB hqV').exists_pos
    have hRnorm : ‖(R : ℂ)‖ = R := by
      rw [Complex.norm_real, Real.norm_of_nonneg hR.le]
    have hBsub : B ⊆ (R : ℂ) • (W.mkQ '' V') := habs (R : ℂ) hRnorm.ge
    obtain ⟨S, hS'⟩ := hfin (ρ / R) (div_pos hρ' hR)
    refine ⟨(fun y => (R : ℂ) • y) '' (S : Set E), S.finite_toSet.image _, ?_⟩
    intro a ha
    obtain ⟨_, ⟨v, hv, rfl⟩, hva⟩ := Set.mem_smul_set.mp (hBsub ha)
    have hw : a - (R : ℂ) • v ∈ W := by
      rw [← Submodule.ker_mkQ W, LinearMap.mem_ker, map_sub, map_smul, hva, sub_self]
    obtain ⟨y, hyS, hy⟩ := Set.mem_iUnion₂.mp (hS' hv)
    have hy' : P (v - y) < ρ / R := hy
    refine ⟨(R : ℂ) • y, ⟨y, hyS, rfl⟩, a - (R : ℂ) • v, hw, hsub' ?_⟩
    have h4 : a - (R : ℂ) • y - (a - (R : ℂ) • v) = (R : ℂ) • (v - y) := by
      rw [smul_sub]
      abel
    rw [h4, Seminorm.mem_ball_zero, map_smul_eq_mul, hRnorm]
    calc R * P (v - y) < R * (ρ / R) := mul_lt_mul_of_pos_left hy' hR
      _ = ρ := mul_div_cancel₀ ρ hR.ne'
  have hWcl : IsClosed (W.toAddSubgroup : Set E) := hW
  obtain ⟨C, hC, hlift⟩ := exists_compact_lift W.toAddSubgroup hWcl hc _ hpre
  refine ⟨C, hC, fun b hb => ?_⟩
  obtain ⟨a, rfl⟩ := W.mkQ_surjective b
  obtain ⟨c, hcC, hac⟩ := hlift a hb
  refine ⟨c, hcC, ?_⟩
  have hac' : a - c ∈ W := hac
  have h5 : W.mkQ (a - c) = 0 := by
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
    exact hac'
  rw [map_sub, sub_eq_zero] at h5
  exact h5.symm
