-- Prove2me | solution 3 for MasulloGRH.open_mapping_LF
-- status  : ACCEPTED   (prove)
-- author  : @ijawdoij123
-- created : 2026-11-20T22:54:07.750815+00:00
-- url     : https://prove2.me/submissions/5557e986-b5ec-48e9-951b-aeb3e682d110

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

open MasulloGRH Filter Topology Uniformity Pointwise

-- Open mapping theorem for complete metrizable TVS with non-meagre range (Rudin, FA 2.11).
open Set in
private lemma frechet_open
    {X Y : Type*} [AddCommGroup X] [Module ℂ X] [UniformSpace X] [IsUniformAddGroup X]
    [ContinuousSMul ℂ X] [CompleteSpace X] [TopologicalSpace.MetrizableSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
    [ContinuousSMul ℂ Y] [T2Space Y]
    (T : X →L[ℂ] Y) (hT : ¬ IsMeagre (Set.range T)) : IsOpenMap T := by
  -- Step 1: closures of images of neighbourhoods are neighbourhoods.
  have claimA : ∀ W ∈ 𝓝 (0 : X), closure (T '' W) ∈ 𝓝 (0 : Y) := by
    intro W hW
    obtain ⟨W', hW', hW'W⟩ : ∃ W' ∈ 𝓝 (0 : X), ∀ a ∈ W', ∀ b ∈ W', a - b ∈ W := by
      have : Tendsto (fun p : X × X => p.1 - p.2) (𝓝 ((0 : X), (0 : X))) (𝓝 0) := by
        have h : Tendsto (fun p : X × X => p.1 - p.2) (𝓝 ((0 : X), (0 : X))) (𝓝 ((0 : X) - 0)) :=
          (continuous_fst.sub continuous_snd).tendsto _
        rwa [sub_zero] at h
      obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.1 (this hW)
      exact ⟨A ∩ B, inter_mem hA hB, fun a ha b hb => hAB (mk_mem_prod ha.1 hb.2)⟩
    have habs : Absorbent ℂ W' := absorbent_nhds_zero hW'
    have h2 : Tendsto (fun n : ℕ => ((n : ℂ) + 1)) atTop (Bornology.cobounded ℂ) := by
      rw [← comap_norm_atTop, tendsto_comap_iff]
      have : (norm ∘ fun n : ℕ => ((n : ℂ) + 1)) = fun n : ℕ => ((n : ℝ) + 1) := by
        funext n
        simp only [Function.comp_apply]
        exact_mod_cast Complex.norm_natCast (n + 1)
      rw [this]
      exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have hcover : Set.range T ⊆ ⋃ n : ℕ, ((n : ℂ) + 1) • (T '' W') := by
      rintro _ ⟨x, rfl⟩
      have h1 : ∀ᶠ c in Bornology.cobounded ℂ, {x} ⊆ c • W' := habs x
      obtain ⟨n, hn⟩ := (h2.eventually h1).exists
      rw [singleton_subset_iff] at hn
      obtain ⟨w, hw, rfl⟩ := hn
      exact mem_iUnion.2 ⟨n, ⟨T w, ⟨w, hw, rfl⟩, by simp⟩⟩
    obtain ⟨n, hn⟩ : ∃ n : ℕ, ¬ IsNowhereDense (((n : ℂ) + 1) • (T '' W')) := by
      by_contra h
      push Not at h
      exact hT ((isMeagre_iUnion fun n => (h n).isMeagre).mono hcover)
    have hc : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    rw [IsNowhereDense, closure_smul₀' hc, interior_smul₀ hc, ← Ne,
      ← nonempty_iff_ne_empty, smul_set_nonempty] at hn
    obtain ⟨y0, hy0⟩ := hn
    have hpre : (fun z => y0 + z) ⁻¹' interior (closure (T '' W')) ∈ 𝓝 (0 : Y) := by
      have hc' : Tendsto (fun z => y0 + z) (𝓝 (0 : Y)) (𝓝 (y0 + 0)) :=
        (continuous_const_add y0).tendsto 0
      rw [add_zero] at hc'
      exact hc' (isOpen_interior.mem_nhds hy0)
    refine mem_of_superset hpre fun z hz => ?_
    have h1 : y0 + z ∈ closure (T '' W') := interior_subset hz
    have h2 : y0 ∈ closure (T '' W') := interior_subset hy0
    have hmap : MapsTo (fun p : Y × Y => p.1 - p.2) ((T '' W') ×ˢ (T '' W')) (T '' W) := by
      rintro ⟨_, _⟩ ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩
      exact ⟨a - b, hW'W a ha b hb, map_sub T a b⟩
    have := hmap.closure (continuous_fst.sub continuous_snd)
    have h3 := this (show (y0 + z, y0) ∈ closure ((T '' W') ×ˢ (T '' W')) by
      rw [closure_prod_eq]; exact ⟨h1, h2⟩)
    simpa using h3
  -- Step 2: images of neighbourhoods are neighbourhoods.
  have claimB : ∀ V ∈ 𝓝 (0 : X), T '' V ∈ 𝓝 (0 : Y) := by
    intro V hV
    obtain ⟨u, hu⟩ := (𝓝 (0 : X)).exists_antitone_basis
    obtain ⟨V0, hV0, hV0c, hV0V⟩ := exists_mem_nhds_isClosed_subset hV
    have hex : ∀ p : ℕ × {W : Set X // W ∈ 𝓝 (0 : X)},
        ∃ H ∈ 𝓝 (0 : X), H ⊆ u p.1 ∧ ∀ a ∈ H, ∀ b ∈ H, a + b ∈ p.2.1 := by
      intro p
      obtain ⟨H, hH, hH2⟩ := exists_nhds_zero_half p.2.2
      exact ⟨H ∩ u p.1, inter_mem hH (hu.mem p.1), inter_subset_right,
        fun a ha b hb => hH2 a ha.1 b hb.1⟩
    choose half hhalf0 hhalfsub hhalf using hex
    let Vs : ℕ → {W : Set X // W ∈ 𝓝 (0 : X)} :=
      fun k => Nat.rec ⟨V0, hV0⟩ (fun k W => ⟨half (k + 1, W), hhalf0 _⟩) k
    have hVadd : ∀ n, ∀ a ∈ (Vs (n + 1)).1, ∀ b ∈ (Vs (n + 1)).1, a + b ∈ (Vs n).1 :=
      fun n => hhalf (n + 1, Vs n)
    have hVu : ∀ n, (Vs (n + 1)).1 ⊆ u (n + 1) := fun n => hhalfsub (n + 1, Vs n)
    have hV0' : ∀ n, (0 : X) ∈ (Vs n).1 := fun n => mem_of_mem_nhds (Vs n).2
    have hVanti : Antitone fun n => (Vs n).1 := by
      refine antitone_nat_of_succ_le fun n a ha => ?_
      simpa using hVadd n a ha 0 (hV0' (n + 1))
    refine mem_of_superset (claimA _ (Vs 1).2) ?_
    intro y hy
    have step : ∀ n (z : Y), z ∈ closure (T '' (Vs (n + 1)).1) →
        ∃ x ∈ (Vs (n + 1)).1, z - T x ∈ closure (T '' (Vs (n + 2)).1) := by
      intro n z hz
      have hN := claimA _ (Vs (n + 2)).2
      have hpre : (fun a => z - a) ⁻¹' closure (T '' (Vs (n + 2)).1) ∈ 𝓝 z := by
        have hc : Tendsto (fun a => z - a) (𝓝 z) (𝓝 (z - z)) :=
          (continuous_const.sub continuous_id).tendsto z
        rw [sub_self] at hc
        exact hc hN
      obtain ⟨_, ha, ⟨x, hx, rfl⟩⟩ := mem_closure_iff_nhds.1 hz _ hpre
      exact ⟨x, hx, ha⟩
    choose f hf1 hf2 using step
    let zs : (n : ℕ) → {z : Y // z ∈ closure (T '' (Vs (n + 1)).1)} := fun n =>
      Nat.rec ⟨y, hy⟩ (fun n z => ⟨z.1 - T (f n z.1 z.2), hf2 n z.1 z.2⟩) n
    let xs : ℕ → X := fun n => f n (zs n).1 (zs n).2
    have hxs : ∀ n, xs n ∈ (Vs (n + 1)).1 := fun n => hf1 _ _ _
    let s : ℕ → X := fun n => ∑ i ∈ Finset.range n, xs i
    have hzs : ∀ n, (zs n).1 = y - T (s n) := by
      intro n
      induction n with
      | zero => simp [zs, s]
      | succ n ih =>
        show (zs n).1 - T (xs n) = _
        rw [ih]
        simp [s, Finset.sum_range_succ, sub_sub]
    have hIco : ∀ j n, ∑ i ∈ Finset.Ico n (n + j), xs i ∈ (Vs n).1 := by
      intro j
      induction j with
      | zero => intro n; simpa using hV0' n
      | succ j ih =>
        intro n
        rw [Finset.sum_eq_sum_Ico_succ_bot (by omega), show n + (j + 1) = (n + 1) + j by omega]
        exact hVadd n _ (hxs n) _ (ih (n + 1))
    have hdiff : ∀ n k, n ≤ k → s k - s n ∈ (Vs n).1 := by
      intro n k hnk
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hnk
      rw [show s (n + j) - s n = ∑ i ∈ Finset.Ico n (n + j), xs i from
        (Finset.sum_Ico_eq_sub _ hnk).symm]
      exact hIco j n
    have hsmall : ∀ U ∈ 𝓝 (0 : X), ∃ N, ∀ n ≥ N, (Vs n).1 ⊆ U := by
      intro U hU
      obtain ⟨N, -, hN⟩ := hu.1.mem_iff.1 hU
      refine ⟨N + 1, fun n hn => (hVanti (show N + 1 ≤ n from hn)).trans ?_⟩
      exact (hVu N).trans ((hu.antitone (Nat.le_succ N)).trans hN)
    have hcs : CauchySeq s := by
      refine (IsUniformAddGroup.cauchy_map_iff_tendsto_swapped atTop s).2 ⟨inferInstance, ?_⟩
      intro U hU
      obtain ⟨N, hN⟩ := hsmall _ (inter_mem hU (neg_mem_nhds_zero X hU))
      refine Filter.mem_map.2 (mem_of_superset
        (prod_mem_prod (eventually_ge_atTop N) (eventually_ge_atTop N)) fun p hp => ?_)
      show s p.2 - s p.1 ∈ U
      rcases le_total p.1 p.2 with h | h
      · exact (hN p.1 hp.1 (hdiff _ _ h)).1
      · have := (hN p.2 hp.2 (hdiff _ _ h)).2
        rw [Set.mem_neg, neg_sub] at this
        exact this
    obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcs
    have hxV : x ∈ V := by
      refine hV0V (hV0c.closure_subset (mem_closure_of_tendsto hx (Eventually.of_forall
        fun k => ?_)))
      have := hdiff 0 k (Nat.zero_le k)
      simpa [s, Vs] using this
    have h1 : Tendsto (fun n => T (s n)) atTop (𝓝 (T x)) := (T.continuous.tendsto x).comp hx
    have h3 : Tendsto (fun n => y - T (s n)) atTop (𝓝 0) := by
      intro W hW
      obtain ⟨W', hW', hW'c, hW'W⟩ := exists_mem_nhds_isClosed_subset hW
      have hTW : T ⁻¹' W' ∈ 𝓝 (0 : X) :=
        T.continuous.continuousAt.preimage_mem_nhds (by simpa using hW')
      obtain ⟨N, hN⟩ := hsmall _ hTW
      refine Filter.mem_map.2 ((eventually_ge_atTop N).mono fun n hn => ?_)
      apply hW'W
      show y - T (s n) ∈ W'
      rw [← hzs n]
      refine closure_minimal ?_ hW'c (zs n).2
      rintro _ ⟨a, ha, rfl⟩
      exact hN (n + 1) (by omega) ha
    have h2 : Tendsto (fun n => T (s n)) atTop (𝓝 y) := by
      have := (tendsto_const_nhds (x := y)).sub h3
      simpa using this
    exact ⟨x, hxV, tendsto_nhds_unique h1 h2⟩
  -- Step 3: translate.
  rw [isOpenMap_iff_nhds_le]
  intro x
  have h0' : 𝓝 (0 : Y) ≤ map T (𝓝 0) := fun U hU =>
    mem_of_superset (by simpa using claimB _ hU) (image_preimage_subset _ _)
  rw [← map_add_left_nhds_zero x, ← map_add_left_nhds_zero (T x), Filter.map_map]
  have : (⇑T ∘ fun y => x + y) = (fun z => T x + z) ∘ ⇑T := by
    funext y; simp
  rw [this, ← Filter.map_map]
  exact Filter.map_mono h0'

universe u

/-- A locally convex topology is a vector space topology. -/
private lemma lc_tvs {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    (h : IsLocallyConvexTopology V ‹_›) : IsTopologicalAddGroup V ∧ ContinuousSMul ℂ V := by
  obtain ⟨ι, _, p, hp⟩ := h
  exact ⟨hp.topologicalAddGroup, hp.continuousSMul⟩

/-- Completeness in the sense of `IsCompleteTVS` gives completeness of the group uniformity. -/
private lemma complete_of {V : Type*} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] (h : ∀ f : Filter V, IsCauchyFilter f → ∃ x : V, f ≤ 𝓝 x) :
    @CompleteSpace V (IsTopologicalAddGroup.rightUniformSpace V) := by
  let _ := IsTopologicalAddGroup.rightUniformSpace V
  refine ⟨fun {f} hf => h f ⟨hf.1, fun U hU => ?_⟩⟩
  have hmem : {p : V × V | p.2 - p.1 ∈ U} ∈ 𝓤 V := by
    rw [uniformity_eq_comap_nhds_zero' V]
    refine mem_of_superset (preimage_mem_comap hU) ?_
    intro p hp
    simpa [sub_eq_add_neg] using hp
  obtain ⟨A, hA, hAA⟩ := Filter.mem_prod_same_iff.1 (hf.2 hmem)
  exact ⟨A, hA, fun x hx y hy => hAA (Set.mk_mem_prod hy hx)⟩


private lemma core {E F : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    (X : ℕ → Submodule ℂ F) (τ : ∀ n, TopologicalSpace (X n))
    (hcov : ∀ x : F, ∃ n, x ∈ X n) (hX : ∀ n, @IsFrechet (X n) _ _ (τ n))
    (hXc : ∀ n, @Continuous (X n) F (τ n) _ Subtype.val)
    (H : Submodule ℂ E) (σ : TopologicalSpace H) (hH : @IsFrechet H _ _ σ)
    (hHc : @Continuous H E σ _ Subtype.val)
    (q : F →ₗ[ℂ] E) (hq : Continuous q) (hsurj : Function.Surjective q)
    (U : Set F) (hU : U ∈ 𝓝 (0 : F)) :
    Subtype.val ⁻¹' (q '' U) ∈ @nhds H σ 0 := by
  let _ := σ
  obtain ⟨hHlc, ⟨hHt2, hHc'⟩, hHm⟩ := hH
  obtain ⟨_, _⟩ := lc_tvs hHlc
  let uH : UniformSpace H := IsTopologicalAddGroup.rightUniformSpace H
  have : IsUniformAddGroup H := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace H := complete_of hHc'
  have : (𝓤 H).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  let R : ℕ → Set H := fun n => {y | ∃ x : X n, q x = y}
  have hcovR : (⋃ n, R n) = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨x, hx⟩ := hsurj (y : E)
    obtain ⟨n, hn⟩ := hcov x
    exact Set.mem_iUnion.2 ⟨n, ⟨x, hn⟩, hx⟩
  obtain ⟨n, hn⟩ : ∃ n, ¬ IsMeagre (R n) := by
    by_contra hcon
    push Not at hcon
    have := isMeagre_iUnion hcon
    rw [hcovR] at this
    exact not_isMeagre_of_isOpen isOpen_univ Set.univ_nonempty this
  let _ := τ n
  obtain ⟨hXlc, ⟨_, hXc'⟩, hXm⟩ := hX n
  obtain ⟨_, _⟩ := lc_tvs hXlc
  let uX : UniformSpace (X n) := IsTopologicalAddGroup.rightUniformSpace (X n)
  have : IsUniformAddGroup (X n) := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace (X n) := complete_of hXc'
  let L : (X n × H) →ₗ[ℂ] E :=
    q ∘ₗ (X n).subtype ∘ₗ LinearMap.fst ℂ _ _ - H.subtype ∘ₗ LinearMap.snd ℂ _ _
  have hLc : Continuous L :=
    (hq.comp ((hXc n).comp continuous_fst)).sub (hHc.comp continuous_snd)
  let Gr : Submodule ℂ (X n × H) := LinearMap.ker L
  have hcl : IsClosed (Gr : Set (X n × H)) := isClosed_eq hLc continuous_const
  have := hHm
  have := hXm
  have : CompleteSpace Gr := hcl.completeSpace_coe
  have hm1 : TopologicalSpace.MetrizableSpace (X n × H) := inferInstance
  have : TopologicalSpace.MetrizableSpace Gr :=
    TopologicalSpace.MetrizableSpace.subtype (Gr : Set (X n × H))
  have : IsUniformAddGroup Gr := IsUniformInducing.isUniformAddGroup Gr.subtype ⟨rfl⟩
  let π : Gr →L[ℂ] H :=
    ⟨(LinearMap.snd ℂ _ _) ∘ₗ Gr.subtype, continuous_snd.comp continuous_subtype_val⟩
  have hrange : Set.range π = R n := by
    ext y
    constructor
    · rintro ⟨g, rfl⟩
      refine ⟨g.1.1, ?_⟩
      have := g.2
      simp only [Gr, L, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.coe_comp,
        Function.comp_apply, LinearMap.fst_apply, Submodule.coe_subtype,
        LinearMap.snd_apply, sub_eq_zero] at this
      exact this
    · rintro ⟨x, hx⟩
      refine ⟨⟨(x, y), ?_⟩, rfl⟩
      simp only [Gr, L, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.coe_comp,
        Function.comp_apply, LinearMap.fst_apply, Submodule.coe_subtype,
        LinearMap.snd_apply, sub_eq_zero]
      exact hx
  have hopen := frechet_open π (hrange ▸ hn)
  let N : Set Gr := {g | ((g : X n × H).1 : F) ∈ U}
  have hN : N ∈ 𝓝 (0 : Gr) := by
    have hc : Continuous fun g : Gr => ((g : X n × H).1 : F) :=
      (hXc n).comp (continuous_fst.comp continuous_subtype_val)
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hU)
  have := hopen.image_mem_nhds hN
  rw [map_zero] at this
  refine Filter.mem_of_superset this ?_
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨((g : X n × H).1 : F), hg, ?_⟩
  have := g.2
  simp only [Gr, L, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.fst_apply, Submodule.coe_subtype,
    LinearMap.snd_apply, sub_eq_zero] at this
  exact this

private lemma lf_nhds {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (Y : ℕ → Submodule ℂ E) (τ : ∀ m, TopologicalSpace (Y m))
    (hlc : ∀ m, IsLocallyConvexTopology (Y m) (τ m)) (hcov : ∀ x : E, ∃ m, x ∈ Y m)
    (heq : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (Y n) E (τ n) t Subtype.val})
    (V : Set E) (hconv : Convex ℝ V) (hbal : Balanced ℂ V)
    (hV : ∀ m, Subtype.val ⁻¹' V ∈ @nhds (Y m) (τ m) 0) : V ∈ 𝓝 (0 : E) := by
  have habsC : Absorbent ℂ V := by
    intro x
    obtain ⟨m, hm⟩ := hcov x
    let _ := τ m
    obtain ⟨_, _⟩ := lc_tvs (hlc m)
    have h1 : Absorbent ℂ (Subtype.val ⁻¹' V : Set (Y m)) := absorbent_nhds_zero (hV m)
    have h2 : ∀ᶠ c in Bornology.cobounded ℂ, {(⟨x, hm⟩ : Y m)} ⊆ c • (Subtype.val ⁻¹' V) :=
      h1 ⟨x, hm⟩
    show ∀ᶠ c in Bornology.cobounded ℂ, {x} ⊆ c • V
    refine h2.mono fun c hc => ?_
    rw [Set.singleton_subset_iff] at hc ⊢
    obtain ⟨w, hw, hwx⟩ := hc
    exact ⟨w, hw, by simpa using congrArg Subtype.val hwx⟩
  have hbdd : Tendsto (fun r : ℝ => r • (1 : ℂ)) (Bornology.cobounded ℝ)
      (Bornology.cobounded ℂ) := by
    rw [← comap_norm_atTop (E := ℂ), tendsto_comap_iff]
    have : (norm ∘ fun r : ℝ => r • (1 : ℂ)) = norm := by
      funext r; simp
    rw [this]
    exact tendsto_norm_cobounded_atTop
  have habs : Absorbent ℝ V := fun x => (habsC x).restrict_scalars hbdd
  let p : Seminorm ℂ E := gaugeSeminorm hbal hconv habs
  let pf : SeminormFamily ℂ E PUnit.{u+1} := fun _ => p
  let t : TopologicalSpace E := pf.moduleFilterBasis.topology
  have hw : @WithSeminorms ℂ E PUnit.{u+1} _ _ _ pf t := ⟨rfl⟩
  have hVsub : V ⊆ p.closedBall 0 1 := fun x hx => by
    rw [Seminorm.mem_closedBall_zero]
    exact gauge_le_one_of_mem hx
  have ht : t ∈ {t | IsLocallyConvexTopology E t ∧
      ∀ n, @Continuous (Y n) E (τ n) t Subtype.val} := by
    refine ⟨⟨PUnit.{u+1}, inferInstance, pf, hw⟩, fun m => ?_⟩
    let _ := τ m
    obtain ⟨_, _⟩ := lc_tvs (hlc m)
    refine WithSeminorms.continuous_of_continuous_comp (hq := hw) (f := (Y m).subtype)
      (fun _ => ?_)
    refine Seminorm.continuous' (r := 1) ?_
    have : (p.comp (Y m).subtype).closedBall 0 1 = Subtype.val ⁻¹' p.closedBall 0 1 := by
      ext y; simp [Seminorm.mem_closedBall]
    rw [this]
    exact mem_of_superset (hV m) (Set.preimage_mono hVsub)
  have hball : p.ball 0 1 ⊆ V := fun x hx => by
    rw [Seminorm.mem_ball_zero] at hx
    exact setOfPred_gauge_lt_one_subset_self hconv habs.zero_mem habs hx
  have hmem : V ∈ @nhds E t 0 := by
    rw [hw.mem_nhds_iff]
    exact ⟨{PUnit.unit}, 1, one_pos, by simpa [pf] using hball⟩
  have := nhds_mono (sInf_le ht) hmem
  rw [heq]
  exact this

theorem solution (E F : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul ℂ F] [T2Space F] (hE : IsLF E)
    (hF : ∃ (X : ℕ → Submodule ℂ F) (τ : ∀ n, TopologicalSpace (X n)), Monotone X ∧
      (∀ x : F, ∃ n, x ∈ X n) ∧ (∀ n, @IsFrechet (X n) _ _ (τ n)) ∧
      ∀ n, @Continuous (X n) F (τ n) _ Subtype.val)
    (q : F →ₗ[ℂ] E) (hq : Continuous q) (hsurj : Function.Surjective q) :
    IsOpenMap q := by
  obtain ⟨⟨hElc, hEt2⟩, Y, τ', hYcov, hYfr, -, heq⟩ := hE
  obtain ⟨X, τ, -, hXcov, hXfr, hXc⟩ := hF
  obtain ⟨_, _⟩ := lc_tvs hElc
  have hYc : ∀ m, @Continuous (Y m) E (τ' m) _ Subtype.val := by
    intro m
    rw [heq]
    exact continuous_sInf_rng.2 fun t ht => ht.2 m
  suffices h0 : ∀ U ∈ 𝓝 (0 : F), q '' U ∈ 𝓝 (0 : E) by
    rw [isOpenMap_iff_nhds_le]
    intro x
    have h0' : 𝓝 (0 : E) ≤ map q (𝓝 0) := fun U hU =>
      mem_of_superset (h0 _ hU) (Set.image_preimage_subset _ _)
    rw [← map_add_left_nhds_zero x, ← map_add_left_nhds_zero (q x), Filter.map_map]
    have : (⇑q ∘ fun y => x + y) = (fun z => q x + z) ∘ ⇑q := by
      funext y; simp
    rw [this, ← Filter.map_map]
    exact Filter.map_mono h0'
  intro U hU
  choose half hhalf0 hhalf using
    fun W : {W : Set F // W ∈ 𝓝 (0 : F)} => exists_nhds_zero_half W.2
  let B : ℕ → {W : Set F // W ∈ 𝓝 (0 : F)} :=
    fun k => Nat.rec ⟨U, hU⟩ (fun _ W => ⟨half W, hhalf0 W⟩) k
  have hBs : ∀ k, ∀ v ∈ (B (k + 1)).1, ∀ w ∈ (B (k + 1)).1, v + w ∈ (B k).1 :=
    fun k => hhalf (B k)
  have hB0 : ∀ k, (0 : F) ∈ (B k).1 := fun k => mem_of_mem_nhds (B k).2
  have hW : ∀ m, ∃ W : Set (Y m), W ∈ @nhds (Y m) (τ' m) 0 ∧ Convex ℝ W ∧ Balanced ℂ W ∧
      W ⊆ Subtype.val ⁻¹' (q '' (B (m + 1)).1) := by
    intro m
    let _ := τ' m
    obtain ⟨ι, _, p, hp⟩ := (hYfr m).1
    have hc := core X τ hXcov hXfr hXc (Y m) (τ' m) (hYfr m) (hYc m) q hq hsurj _ (B (m + 1)).2
    obtain ⟨⟨s, r⟩, hr, hsub⟩ := hp.hasBasis_zero_ball.mem_iff.1 hc
    exact ⟨_, hp.hasBasis_zero_ball.mem_of_mem hr, Seminorm.convex_ball _ _ _,
      Seminorm.balanced_ball_zero _ _, hsub⟩
  choose W hWn hWc hWb hWs using hW
  let A : ℕ → Set E := fun m => Subtype.val '' W m
  have hA0 : ∀ m, (0 : E) ∈ A m := fun m => ⟨0, mem_of_mem_nhds (hWn m), rfl⟩
  have hAc : ∀ m, Convex ℝ (A m) := fun m =>
    (hWc m).is_linear_image (f := Subtype.val) ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have hAb : ∀ m, Balanced ℂ (A m) := by
    intro m a ha
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨a • w, hWb m a ha (Set.smul_mem_smul_set hw), rfl⟩
  have hAq : ∀ m, A m ⊆ q '' (B (m + 1)).1 := fun m =>
    Set.image_subset_iff.2 (hWs m)
  let S : ℕ → Set E := fun K => Nat.rec (A 0) (fun K SK => SK + A (K + 1)) K
  let T : ℕ → Set F := fun K => Nat.rec (B 1).1 (fun K TK => TK + (B (K + 2)).1) K
  have hT : ∀ K, T K + (B (K + 1)).1 ⊆ (B 0).1 := by
    intro K
    induction K with
    | zero =>
      rintro _ ⟨a, ha, b, hb, rfl⟩
      exact hBs 0 a ha b hb
    | succ K ih =>
      rintro _ ⟨_, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩
      apply ih
      exact ⟨a, ha, b + c, hBs (K + 1) b hb c hc, by ac_rfl⟩
  have hTU : ∀ K, T K ⊆ U := fun K x hx =>
    hT K ⟨x, hx, 0, hB0 (K + 1), add_zero x⟩
  have hSq : ∀ K, S K ⊆ q '' T K := by
    intro K
    induction K with
    | zero => exact hAq 0
    | succ K ih =>
      rintro _ ⟨a, ha, b, hb, rfl⟩
      obtain ⟨x, hx, rfl⟩ := ih ha
      obtain ⟨y, hy, rfl⟩ := hAq (K + 1) hb
      exact ⟨x + y, ⟨x, hx, y, hy, rfl⟩, map_add q x y⟩
  have hS0 : ∀ K, (0 : E) ∈ S K := by
    intro K
    induction K with
    | zero => exact hA0 0
    | succ K ih => exact ⟨0, ih, 0, hA0 _, add_zero 0⟩
  have hAS : ∀ m, A m ⊆ S m := by
    intro m
    cases m with
    | zero => exact le_rfl
    | succ K => exact fun a ha => ⟨0, hS0 K, a, ha, zero_add a⟩
  have hSmono : Monotone S :=
    monotone_nat_of_le_succ fun K a ha => ⟨a, ha, 0, hA0 _, add_zero a⟩
  have hSc : ∀ K, Convex ℝ (S K) := by
    intro K
    induction K with
    | zero => exact hAc 0
    | succ K ih => exact ih.add (hAc _)
  have hSb : ∀ K, Balanced ℂ (S K) := by
    intro K
    induction K with
    | zero => exact hAb 0
    | succ K ih => exact ih.add (hAb _)
  let V : Set E := ⋃ K, S K
  have hVU : V ⊆ q '' U := Set.iUnion_subset fun K =>
    (hSq K).trans (Set.image_mono (hTU K))
  have hVn : V ∈ 𝓝 (0 : E) := by
    refine lf_nhds Y τ' (fun m => (hYfr m).1) hYcov heq V
      (Directed.convex_iUnion hSmono.directed_le hSc) (balanced_iUnion hSb) fun m => ?_
    refine mem_of_superset (hWn m) fun w hw => ?_
    exact Set.mem_iUnion.2 ⟨m, hAS m ⟨w, hw, rfl⟩⟩
  exact mem_of_superset hVn hVU
