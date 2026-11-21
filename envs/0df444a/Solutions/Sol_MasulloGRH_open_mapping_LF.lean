-- Prove2me | solution 1 for MasulloGRH.open_mapping_LF
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T22:44:01.904423+00:00
-- url     : https://prove2.me/submissions/f95be7f0-de90-4bf7-b903-b0481caf7b1d

import Theorems.Thm_MasulloGRH_frechet_countable_pullback_open_quotient

set_option autoImplicit false

open MasulloGRH Filter Set Topology
open scoped Pointwise

universe u

private theorem continuous_linearMap_of_countable_locallyConvex_limit
    (E : Type u) [AddCommGroup E] [Module ℂ E] [tE : TopologicalSpace E]
    (X : ℕ → Submodule ℂ E) (τ : ∀ n, TopologicalSpace (X n))
    (hexh : ∀ x : E, ∃ n, x ∈ X n)
    (hX : ∀ n, IsLocallyConvexTopology (X n) (τ n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E (τ n) t Subtype.val})
    (G : Type*) [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [ContinuousSMul ℂ G]
    (f : E →ₗ[ℂ] G)
    (hf : ∀ n, @Continuous (X n) G (τ n) _ (fun x => f x.val)) :
    Continuous f := by
  classical
  have ht (t : TopologicalSpace E) (hlt : IsLocallyConvexTopology E t)
      (hit : ∀ n, @Continuous (X n) E (τ n) t Subtype.val) :
      tE ≤ t := by
    rw [htop]
    exact sInf_le ⟨hlt, hit⟩
  have hE : PolynormableSpace ℂ E := by
    rw [htop]
    apply PolynormableSpace.sInf
    intro t ht
    obtain ⟨ι, _, p, hp⟩ := ht.1
    exact hp.toPolynormableSpace
  let : IsTopologicalAddGroup E := (PolynormableSpace.withSeminorms ℂ E).topologicalAddGroup
  apply continuous_of_continuousAt_zero f
  rw [ContinuousAt, f.map_zero, Filter.tendsto_def]
  intro U hU
  choose shrink hshrink hsum using 
    (fun (s : {s : Set G // s ∈ 𝓝 (0 : G)}) => exists_nhds_zero_half s.property)
  let N : ℕ → {s : Set G // s ∈ 𝓝 (0 : G)} :=
    Nat.rec ⟨U, hU⟩ (fun _ s => ⟨shrink s, hshrink s⟩)
  have hN (k : ℕ) : (N (k + 1)).val + (N (k + 1)).val ⊆ (N k).val := add_subset_iff.mpr (hsum (N k))
  have hballs (n : ℕ) : ∃ W : Set (X n),
      W ∈ @nhds (X n) (τ n) 0 ∧ Balanced ℂ W ∧ Convex ℝ W ∧
        W ⊆ (fun x : X n => f x.val) ⁻¹' (N (n + 1)).val := by
    let : TopologicalSpace (X n) := τ n
    obtain ⟨ι, _, p, hp⟩ := hX n
    have hpre : (fun x : X n => f x.val) ⁻¹' (N (n + 1)).val ∈ 𝓝 (0 : X n) := by
      apply (hf n).continuousAt.preimage_mem_nhds
      simpa using (N (n + 1)).property
    obtain ⟨⟨s, r⟩, hr, hs⟩ := hp.hasBasis_zero_ball.mem_iff.mp hpre
    exact ⟨_, hp.hasBasis_zero_ball.mem_of_mem hr, (s.sup p).balanced_ball_zero r,
      (s.sup p).convex_ball 0 r, hs⟩
  choose W hWmem hWbal hWconv hWsub using hballs
  let V (n : ℕ) : Set E := Subtype.val '' W n
  have hVzero (n : ℕ) : (0 : E) ∈ V n := ⟨0, mem_of_mem_nhds (hWmem n), rfl⟩
  have hVbal (n : ℕ) : Balanced ℂ (V n) := by
    rw [balanced_iff_smul_mem]
    rintro a ha _ ⟨x, hx, rfl⟩
    exact ⟨a • x, (hWbal n).smul_mem ha hx, rfl⟩
  have hVconv (n : ℕ) : Convex ℝ (V n) :=
    (hWconv n).linear_image ((X n).subtype.restrictScalars ℝ)
  -- S m k sums m successive stage neighborhoods, beginning at stage k.
  let S : ℕ → ℕ → Set E := Nat.rec (fun _ => {0}) (fun _ s k => V k + s (k + 1))
  have hzero (m k : ℕ) : 0 ∈ S m k := by
    induction m generalizing k with
    | zero => exact mem_singleton 0
    | succ m ih => exact ⟨0, hVzero k, 0, ih (k + 1), zero_add 0⟩
  have hmono : ∀ k, Monotone (fun m => S m k) := by
    intro k
    apply monotone_nat_of_le_succ
    intro m
    induction m generalizing k with
    | zero => exact singleton_subset_iff.mpr (hzero 1 k)
    | succ m ih => exact add_subset_add Subset.rfl (ih (k + 1))
  have hbal (m k : ℕ) : Balanced ℂ (S m k) := by
    induction m generalizing k with
    | zero =>
      rw [balanced_iff_smul_mem]
      intro a _ x hx
      change x ∈ ({0} : Set E) at hx
      simp [S, mem_singleton_iff.mp hx]
    | succ m ih => exact (hVbal k).add (ih (k + 1))
  have hconv (m k : ℕ) : Convex ℝ (S m k) := by
    induction m generalizing k with
    | zero => exact convex_singleton 0
    | succ m ih => exact (hVconv k).add (ih (k + 1))
  have himage (m k : ℕ) : S m k ⊆ f ⁻¹' (N k).val := by
    induction m generalizing k with
    | zero =>
      intro x hx
      change x ∈ ({0} : Set E) at hx
      subst x
      simp only [mem_preimage, map_zero]
      exact mem_of_mem_nhds (N k).property
    | succ m ih =>
      rintro _ ⟨_, ⟨x, hx, rfl⟩, y, hy, rfl⟩
      change f (x.val + y) ∈ (N k).val
      rw [map_add]
      exact hN k ⟨f x.val, hWsub k hx, f y, ih (k + 1) hy, rfl⟩
  have hlead (k m : ℕ) : V (k + m) ⊆ S (m + 1) k := by
    induction m generalizing k with
    | zero =>
      intro x hx
      exact ⟨x, hx, 0, hzero 0 (k + 1), add_zero x⟩
    | succ m ih =>
      intro x hx
      have hx' : x ∈ V (k + 1 + m) := by
        simpa only [show k + 1 + m = k + (m + 1) by omega] using hx
      exact ⟨0, hVzero k, x, ih (k + 1) hx', zero_add x⟩
  let D := ⋃ m, S m 0
  have hWD (n : ℕ) : W n ⊆ Subtype.val ⁻¹' D := by
    intro x hx
    have hx' : x.val ∈ V (0 + n) := by
      rw [zero_add]
      exact ⟨x, hx, rfl⟩
    exact mem_iUnion.mpr ⟨n + 1, hlead 0 n hx'⟩
  have hDbal : Balanced ℂ D := balanced_iUnion fun m => hbal m 0
  have hDconv : Convex ℝ D := (hmono 0).directed_le.convex_iUnion fun m => hconv m 0
  have hDabs : Absorbent ℝ D := by
    rw [absorbent_iff_eventually_nhdsNE_zero]
    intro x
    obtain ⟨n, hn⟩ := hexh x
    let : TopologicalSpace (X n) := τ n
    obtain ⟨ι, _, p, hp⟩ := hX n
    let : ContinuousSMul ℂ (X n) := hp.continuousSMul
    let xₙ : X n := ⟨x, hn⟩
    have hc : Continuous (fun r : ℝ => (r : ℂ) • xₙ) :=
      Complex.continuous_ofReal.smul continuous_const
    have hz : Tendsto (fun r : ℝ => (r : ℂ) • xₙ) (𝓝 0) (𝓝 0) := by
      simpa only [ContinuousAt, Complex.ofReal_zero, zero_smul] using
        hc.continuousAt (x := (0 : ℝ))
    have hw : ∀ᶠ r : ℝ in 𝓝[≠] 0, (r : ℂ) • xₙ ∈ W n :=
      (hz.mono_left nhdsWithin_le_nhds).eventually (hWmem n)
    exact hw.mono fun r hr => hWD n hr
  let p := gaugeSeminorm hDbal hDconv hDabs
  -- Continuity on the stages makes the topology of p admissible in the defining infimum.
  have hp : Continuous p := by
    let family : SeminormFamily ℂ E (ULift.{u} (Fin 1)) := fun _ => p
    let t := family.moduleFilterBasis.topology
    have htseminorms : @WithSeminorms ℂ E (ULift.{u} (Fin 1)) _ _ _ family t := ⟨rfl⟩
    have hinc (n : ℕ) : @Continuous (X n) E (τ n) t Subtype.val := by
      let : TopologicalSpace (X n) := τ n
      obtain ⟨ι, _, pn, hpn⟩ := hX n
      let : ContinuousSMul ℂ (X n) := hpn.continuousSMul
      let : IsTopologicalAddGroup (X n) := hpn.topologicalAddGroup
      apply htseminorms.continuous_of_continuous_comp (X n).subtype
      intro i
      exact Seminorm.continuous' (r := 1) (mem_of_superset (hWmem n) fun x hx => by
        rw [Seminorm.closedBall_zero_eq]
        change gauge D x.val ≤ 1
        exact gauge_le_one_of_mem (show x.val ∈ D from hWD n hx))
    have hle := ht t ⟨ULift.{u} (Fin 1), inferInstance, family, htseminorms⟩ hinc
    exact continuous_iff_le_induced.mpr
      (hle.trans (continuous_iff_le_induced.mp (htseminorms.continuous_seminorm ⟨0⟩)))
  have hball : p.ball 0 1 ∈ 𝓝 (0 : E) := by
    have htend : Tendsto (fun x : E => p x) (𝓝 0) (𝓝 (0 : ℝ)) := by
      have hc := hp.continuousAt (x := (0 : E))
      rwa [ContinuousAt, map_zero] at hc
    rw [p.ball_zero_eq]
    exact htend (Iio_mem_nhds (show (0 : ℝ) < 1 from one_pos))
  refine mem_of_superset hball ?_
  intro x hx
  rw [p.ball_zero_eq] at hx
  have hxD : x ∈ D := setOfPred_gauge_lt_one_subset_self hDconv hDabs.zero_mem hDabs hx
  obtain ⟨m, hm⟩ := mem_iUnion.mp hxD
  exact himage m 0 hm

theorem solution (E F : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul ℂ F] [T2Space F] (hE : IsLF E)
    (hF : ∃ (X : ℕ → Submodule ℂ F) (τ : ∀ n, TopologicalSpace (X n)), Monotone X ∧
      (∀ x : F, ∃ n, x ∈ X n) ∧ (∀ n, @IsFrechet (X n) _ _ (τ n)) ∧
      ∀ n, @Continuous (X n) F (τ n) _ Subtype.val)
    (q : F →ₗ[ℂ] E) (hq : Continuous q) (hsurj : Function.Surjective q) :
    IsOpenMap q := by
  obtain ⟨⟨_, ht2⟩, X, τ, hXcover, hXfrechet, _, htop⟩ := hE
  obtain ⟨Y, σ, _, hYcover, hYfrechet, hYcont⟩ := hF
  let : T2Space E := ht2
  let : ∀ n, TopologicalSpace (Y n) := σ
  let e := q.quotKerEquivOfSurjective hsurj
  let b : ∀ n, Y n →ₗ[ℂ] E := fun n => q.comp (Y n).subtype
  have hb (n : ℕ) : Continuous (b n) := hq.comp (hYcont n)
  have hbcover (x : E) : ∃ n, x ∈ Set.range (b n) := by
    obtain ⟨y, rfl⟩ := hsurj x
    obtain ⟨n, hn⟩ := hYcover y
    exact ⟨n, ⟨⟨y, hn⟩, rfl⟩⟩
  have hXcont (n : ℕ) : @Continuous (X n) E (τ n) _ Subtype.val := by
    rw [continuous_iff_coinduced_le, htop]
    exact le_sInf fun _ ht => continuous_iff_coinduced_le.mp (ht.2 n)
  have hinv : Continuous e.symm := by
    apply continuous_linearMap_of_countable_locallyConvex_limit E X τ hXcover
      (fun n => (hXfrechet n).1) htop (F ⧸ LinearMap.ker q) e.symm.toLinearMap
    intro n
    let : TopologicalSpace (X n) := τ n
    obtain ⟨k, hk⟩ := frechet_countable_pullback_open_quotient
      (X n) (hXfrechet n) (fun j => Y j) hYfrechet E (X n).subtype (hXcont n) b hb hbcover
    apply hk.isQuotientMap.continuous_iff.mpr
    let P := {p : X n × Y k // (p.1 : E) = b k p.2}
    have hp : Continuous (fun z : P => (LinearMap.ker q).mkQ (z.val.2 : F)) :=
      (LinearMap.ker q).continuous_mkQ.comp
        ((hYcont k).comp (continuous_snd.comp continuous_subtype_val))
    have hcommute : (fun z : P => e.symm (z.val.1 : E)) =
        (fun z : P => (LinearMap.ker q).mkQ (z.val.2 : F)) := by
      funext z
      rw [z.property]
      exact q.quotKerEquivOfSurjective_symm_apply hsurj z.val.2
    change Continuous (fun z : P => e.symm (z.val.1 : E))
    rw [hcommute]
    exact hp
  have heopen : IsOpenMap e := IsOpenMap.of_inverse (f' := e.symm) hinv
    e.right_inv e.left_inv
  have hcomp : (e : (F ⧸ LinearMap.ker q) → E) ∘ (LinearMap.ker q).mkQ = q :=
    funext (q.quotKerEquivOfSurjective_apply_mk hsurj)
  rw [← hcomp]
  exact heopen.comp (LinearMap.ker q).isOpenMap_mkQ
