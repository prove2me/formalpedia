-- Prove2me | solution 1 for MasulloGRH.strictLF_nhds_zero_of_absConvex_traces
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:11:48.769708+00:00
-- url     : https://prove2.me/submissions/7b0faf74-3c88-46fd-80ce-7843acf6d37d

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

open MasulloGRH Set Filter Topology Pointwise

-- The auxiliary lemmas below are reproduced from masullo-80's accepted proof bba86984 of
-- `MasulloGRH.open_mapping_LF` (same account, namespace `OpenMappingLF`).
namespace TraceNhdsAux

theorem continuous_into_seminorms {A F I : Type*} [AddCommGroup A] [Module ℂ A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [AddCommGroup F] [Module ℂ F]
    {τ : TopologicalSpace F} {q : SeminormFamily ℂ F I}
    (hq : WithSeminorms (topology := τ) q) (f : A →ₗ[ℂ] F)
    (h : ∀ i, Continuous ((q i).comp f)) : @Continuous A F _ τ f := by
  let := τ
  exact hq.continuous_of_continuous_comp f h

theorem exists_withSeminorms {F I : Type*} [AddCommGroup F] [Module ℂ F] [Nonempty I]
    (q : SeminormFamily ℂ F I) : ∃ τ : TopologicalSpace F, WithSeminorms (topology := τ) q := by
  let τ : TopologicalSpace F := q.moduleFilterBasis.topology
  exact ⟨τ, ⟨rfl⟩⟩

theorem unitBall_mem_nhds_of_withSeminorms {F I : Type*} [AddCommGroup F] [Module ℂ F]
    [Nonempty I] {τ : TopologicalSpace F} {q : SeminormFamily ℂ F I}
    (hq : WithSeminorms (topology := τ) q) (i : I) : {x : F | q i x < 1} ∈ @nhds F τ 0 := by
  let := τ
  have hc : Continuous (q i) := hq.continuous_seminorm i
  exact (isOpen_lt hc continuous_const).mem_nhds (by simp)

/-- **Neighbourhoods of `0` in a locally convex inductive limit.**  If `E` carries the finest
locally convex topology making the linear maps `i m : A m → E` continuous, then a balanced, convex,
absorbent set whose preimage under every `i m` is a `0`-neighbourhood is a `0`-neighbourhood. -/
theorem mem_nhds_zero_of_inductive {E : Type*} [AddCommGroup E] [Module ℂ E]
    [tE : TopologicalSpace E] (hlc : IsLocallyConvexTopology E tE)
    {A : ℕ → Type*} [∀ m, AddCommGroup (A m)] [∀ m, Module ℂ (A m)]
    [∀ m, TopologicalSpace (A m)] [∀ m, IsTopologicalAddGroup (A m)]
    [∀ m, ContinuousSMul ℂ (A m)] (i : ∀ m, A m →ₗ[ℂ] E)
    (htop : tE = sInf {t | IsLocallyConvexTopology E t ∧ ∀ m, @Continuous (A m) E _ t (i m)})
    (W : Set E) (hWb : Balanced ℂ W) (hWc : Convex ℝ W) (hWa : Absorbent ℝ W)
    (hW : ∀ m, (i m) ⁻¹' W ∈ 𝓝 (0 : A m)) : W ∈ 𝓝 (0 : E) := by
  obtain ⟨ι, _, p, hp⟩ := hlc
  have hi : ∀ m, Continuous (i m) := by
    intro m
    have h : @Continuous (A m) E _
        (sInf {t | IsLocallyConvexTopology E t ∧ ∀ m, @Continuous (A m) E _ t (i m)}) (i m) :=
      continuous_sInf_rng.2 fun t ht => ht.2 m
    rw [htop]
    exact h
  have h0W : (0 : E) ∈ W := by simpa using mem_of_mem_nhds (hW 0)
  let g : Seminorm ℂ E := gaugeSeminorm hWb hWc hWa
  have hg : ∀ x, g x = gauge W x := fun _ => rfl
  have hgW : {x : E | g x < 1} ⊆ W := fun x hx =>
    setOfPred_gauge_lt_one_subset_self hWc h0W hWa (by simpa [hg] using hx)
  let p' : SeminormFamily ℂ E (Option ι) := fun o => o.elim g p
  have hcomp : ∀ m (o : Option ι), Continuous ((p' o).comp (i m)) := by
    intro m o
    cases o with
    | none =>
      refine Seminorm.continuous' (r := 1) (mem_of_superset (hW m) fun x hx => ?_)
      rw [Seminorm.mem_closedBall_zero]
      exact gauge_le_one_of_mem hx
    | some k =>
      exact (hp.continuous_seminorm k).comp (hi m)
  have hunit : {x : E | p' none x < 1} ⊆ W := hgW
  obtain ⟨τ', hτ'⟩ := exists_withSeminorms p'
  have hin : ∀ m, @Continuous (A m) E _ τ' (i m) := fun m =>
    continuous_into_seminorms hτ' (i m) (hcomp m)
  have hle : tE ≤ τ' := htop.le.trans (sInf_le ⟨⟨Option ι, inferInstance, p', hτ'⟩, hin⟩)
  exact mem_of_superset (nhds_mono hle (unitBall_mem_nhds_of_withSeminorms hτ' none)) hunit

end TraceNhdsAux

open TraceNhdsAux in
theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (Ω : Set E) (hconv : Convex ℝ Ω) (hbal : Balanced ℂ Ω)
    (htr : ∀ n, ((↑) : X n → E) ⁻¹' Ω ∈ nhds (0 : X n)) :
    Ω ∈ nhds (0 : E) := by
  -- `E` is locally convex: an infimum of locally convex topologies
  have hP : PolynormableSpace ℂ E := by
    rw [htop]
    apply PolynormableSpace.sInf
    intro t ht
    obtain ⟨ι, _, p, hp⟩ := ht.1
    exact hp.toPolynormableSpace
  have hlc : IsLocallyConvexTopology E ‹TopologicalSpace E› :=
    ⟨{p : Seminorm ℂ E // Continuous p}, ⟨⟨0, continuous_const⟩⟩, fun p => p.1,
      PolynormableSpace.withSeminorms ℂ E⟩
  have : ∀ n, IsTopologicalAddGroup (X n) := fun n => by
    obtain ⟨ι, _, p, hp⟩ := (hX n).1
    exact hp.topologicalAddGroup
  have : ∀ n, ContinuousSMul ℂ (X n) := fun n => by
    obtain ⟨ι, _, p, hp⟩ := (hX n).1
    exact hp.continuousSMul
  -- `Ω` absorbs every point, since every point lies in a stage where the trace is a neighbourhood
  have hΩa : Absorbent ℝ Ω := by
    intro x
    obtain ⟨m, hm⟩ := hexh x
    have hab : Absorbs ℂ (((↑) : X m → E) ⁻¹' Ω) {(⟨x, hm⟩ : X m)} :=
      absorbent_nhds_zero (htr m) _
    obtain ⟨r, hr⟩ := absorbs_iff_norm.1 hab
    refine absorbs_iff_norm.2 ⟨r, fun c hc => ?_⟩
    have hc' : r ≤ ‖(c : ℂ)‖ := by simpa using hc
    obtain ⟨a', ha', ha'eq⟩ := hr (c : ℂ) hc' (mem_singleton _)
    rw [singleton_subset_iff]
    refine ⟨(a' : E), ha', ?_⟩
    have := congrArg Subtype.val ha'eq
    simpa [Complex.coe_smul] using this
  exact mem_nhds_zero_of_inductive hlc (A := fun m => X m) (fun m => (X m).subtype) htop Ω hbal
    hconv hΩa htr
