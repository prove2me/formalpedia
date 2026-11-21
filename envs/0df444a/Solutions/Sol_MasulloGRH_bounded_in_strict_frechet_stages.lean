-- Prove2me | solution 1 for MasulloGRH.bounded_in_strict_frechet_stages
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:49:23.961461+00:00
-- url     : https://prove2.me/submissions/d200a8a4-6d5b-492f-95f1-ebc3e2aefd68

import Theorems.Thm_MasulloGRH_bounded_sets_strict_inductive_limit

open MasulloGRH Set Filter Topology

private theorem complete_stage_closed {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E] (V : Submodule ℂ E)
    (hc : IsCompleteTVS V) : IsClosed (V : Set E) := by
  apply closure_subset_iff_isClosed.mp
  intro x hx
  let f := comap (Subtype.val : V → E) (𝓝 x)
  haveI : NeBot f := by
    apply (map_neBot_iff (Subtype.val : V → E)).mp
    rw [show map Subtype.val f = 𝓝[(V : Set E)] x from subtype_coe_map_comap _ _]
    exact mem_closure_iff_nhdsWithin_neBot.mp hx
  have hf : IsCauchyFilter f := by
    refine ⟨inferInstance, ?_⟩
    intro U hU
    rw [nhds_subtype_eq_comap] at hU
    obtain ⟨W, hW, hWU⟩ := hU
    have hd : Tendsto (fun z : E × E => z.1 - z.2) (𝓝 (x,x)) (𝓝 (0:E)) := by
      have hs : Continuous (fun z : E × E => z.1 - z.2) :=
        continuous_fst.sub continuous_snd
      simpa only [sub_self] using hs.tendsto (x,x)
    have hw := hd hW
    rw [nhds_prod_eq] at hw
    obtain ⟨A, hA, C, hC, hsub⟩ := mem_prod_iff.mp hw
    refine ⟨Subtype.val ⁻¹' (A ∩ C), preimage_mem_comap (inter_mem hA hC), ?_⟩
    intro a ha b hb
    exact hWU (hsub (show (a.val,b.val) ∈ A ×ˢ C from ⟨ha.1,hb.2⟩))
  obtain ⟨y, hy⟩ := hc.2 f hf
  have he : y.val = x := tendsto_nhds_unique
    ((continuous_subtype_val.tendsto y).comp (show Tendsto id f (𝓝 y) from hy))
    (show Tendsto (Subtype.val : V → E) f (𝓝 x) from tendsto_comap)
  exact he ▸ y.property

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E] [t : TopologicalSpace E]
    (X : ℕ → Submodule ℂ E) (hmono : Monotone X) (hexh : ∀ x : E, ∃ n, x ∈ X n)
    (hX : ∀ n, IsFrechet (X n)) (htop : t = sInf {τ | IsLocallyConvexTopology E τ ∧
      ∀ n, @Continuous (X n) E _ τ Subtype.val}) :
    IsHLCS E ∧ ∀ B : Set E, Bornology.IsVonNBounded ℂ B → ∃ (n : ℕ) (A : Set (X n)),
      Bornology.IsVonNBounded ℂ A ∧ B = Subtype.val '' A := by
  haveI : PolynormableSpace ℂ E := by
    rw [htop]
    apply PolynormableSpace.sInf
    intro τ hτ
    obtain ⟨I, _, p, hp⟩ := hτ.1
    exact hp.toPolynormableSpace
  have hp := PolynormableSpace.withSeminorms ℂ E
  haveI := hp.topologicalAddGroup
  haveI : T1Space E := by
    apply t1Space_iff_specializes_imp_eq.mpr
    intro x y h
    obtain ⟨i, hi⟩ := hexh x
    obtain ⟨j, hj⟩ := hexh y
    let a : X (max i j) := ⟨x, hmono (le_max_left _ _) hi⟩
    let b : X (max i j) := ⟨y, hmono (le_max_right _ _) hj⟩
    haveI := (hX (max i j)).2.1.1
    have hab : a ⤳ b := IsInducing.subtypeVal.specializes_iff.mp h
    exact congrArg Subtype.val hab.eq
  have hE : IsHLCS E := ⟨⟨_, ⟨⟨0, continuous_const⟩⟩, _, hp⟩, inferInstance⟩
  exact ⟨hE, fun B => (bounded_sets_strict_inductive_limit E hE X hmono hexh
    (fun n => complete_stage_closed (X n) (hX n).2.1) htop B).mp⟩
