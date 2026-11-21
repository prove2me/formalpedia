-- Prove2me | solution 2 for MasulloGRH.open_mapping_LF
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T22:51:30.156301+00:00
-- url     : https://prove2.me/submissions/bba86984-3fd2-4518-a60e-c0e547de4bce

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

open MasulloGRH Set Filter Topology Pointwise

namespace OpenMappingLF

/-- In a topological additive group every `0`-neighbourhood `U` contains the differences of a
smaller `0`-neighbourhood. -/
theorem exists_nhds_zero_sub {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] {U : Set G} (hU : U ∈ 𝓝 (0 : G)) :
    ∃ W ∈ 𝓝 (0 : G), ∀ a ∈ W, ∀ b ∈ W, a - b ∈ U := by
  have hc : ContinuousAt (fun p : G × G => p.1 - p.2) (0, 0) :=
    (continuous_fst.sub continuous_snd).continuousAt
  have hpre : (fun p : G × G => p.1 - p.2) ⁻¹' U ∈ 𝓝 ((0 : G), (0 : G)) := by
    apply hc.preimage_mem_nhds
    simpa using hU
  obtain ⟨U₁, hU₁, U₂, hU₂, h⟩ := mem_nhds_prod_iff.1 hpre
  exact ⟨U₁ ∩ U₂, inter_mem hU₁ hU₂, fun a ha b hb => h (mk_mem_prod ha.1 hb.2)⟩

/-- **Successive approximation.**  Let `T : G → X` be a continuous linear map from a complete
first countable topological vector space to a Hausdorff one.  If the closure of the image of every
`0`-neighbourhood is a `0`-neighbourhood, then the image of every `0`-neighbourhood is a
`0`-neighbourhood. -/
theorem image_mem_nhds_of_closure {G X : Type*} [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [FirstCountableTopology G]
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X] [T2Space X]
    (hG : ∀ f : Filter G, IsCauchyFilter f → ∃ x : G, f ≤ 𝓝 x)
    (T : G →ₗ[ℂ] X) (hT : Continuous T)
    (hcl : ∀ V ∈ 𝓝 (0 : G), closure (T '' V) ∈ 𝓝 (0 : X))
    (V : Set G) (hV : V ∈ 𝓝 (0 : G)) : T '' V ∈ 𝓝 (0 : X) := by
  obtain ⟨V', hV', hV'cl, hV'V⟩ := exists_mem_nhds_isClosed_subset hV
  obtain ⟨B, hB⟩ := (𝓝 (0 : G)).exists_antitone_basis
  have hBn : ∀ k, B k ∈ 𝓝 (0 : G) := fun k => hB.mem k
  -- a halving operation on `0`-neighbourhoods
  have half : ∀ s : Set G, ∃ U : Set G,
      s ∈ 𝓝 (0 : G) → (U ∈ 𝓝 (0 : G) ∧ ∀ v ∈ U, ∀ w ∈ U, v + w ∈ s) := by
    intro s
    by_cases hs : s ∈ 𝓝 (0 : G)
    · obtain ⟨U, hU, h⟩ := exists_nhds_zero_half hs
      exact ⟨U, fun _ => ⟨hU, h⟩⟩
    · exact ⟨univ, fun h => absurd h hs⟩
  choose half hhalf using half
  obtain ⟨W, hW0, hWs⟩ : ∃ W : ℕ → Set G, W 0 = half (V' ∩ B 0) ∧
      ∀ k, W (k + 1) = half (W k ∩ B (k + 1)) :=
    ⟨fun k => Nat.rec (half (V' ∩ B 0)) (fun k Wk => half (Wk ∩ B (k + 1))) k, rfl, fun _ => rfl⟩
  have hWn : ∀ k, W k ∈ 𝓝 (0 : G) := by
    intro k
    induction k with
    | zero => rw [hW0]; exact (hhalf _ (inter_mem hV' (hBn 0))).1
    | succ k ih => rw [hWs]; exact (hhalf _ (inter_mem ih (hBn _))).1
  have hW0mem : ∀ k, (0 : G) ∈ W k := fun k => mem_of_mem_nhds (hWn k)
  have hWadd0 : ∀ v ∈ W 0, ∀ w ∈ W 0, v + w ∈ V' := by
    intro v hv w hw
    rw [hW0] at hv hw
    exact ((hhalf _ (inter_mem hV' (hBn 0))).2 v hv w hw).1
  have hWadd : ∀ k, ∀ v ∈ W (k + 1), ∀ w ∈ W (k + 1), v + w ∈ W k := by
    intro k v hv w hw
    rw [hWs] at hv hw
    exact ((hhalf _ (inter_mem (hWn k) (hBn _))).2 v hv w hw).1
  have hWB : ∀ k, W k ⊆ B k := by
    intro k v hv
    have h0 := hW0mem k
    cases k with
    | zero =>
      rw [hW0] at hv h0
      have := ((hhalf _ (inter_mem hV' (hBn 0))).2 v hv 0 h0).2
      simpa using this
    | succ k =>
      rw [hWs] at hv h0
      have := ((hhalf _ (inter_mem (hWn k) (hBn _))).2 v hv 0 h0).2
      simpa using this
  -- it suffices to show `closure (T '' W 0) ⊆ T '' V`
  refine mem_of_superset (hcl _ (hWn 0)) ?_
  intro y hy
  have step : ∀ (k : ℕ) (z : X), ∃ x : G,
      z ∈ closure (T '' W k) → (x ∈ W k ∧ z - T x ∈ closure (T '' W (k + 1))) := by
    intro k z
    by_cases hz : z ∈ closure (T '' W k)
    · have hM : {w : X | z - w ∈ closure (T '' W (k + 1))} ∈ 𝓝 z := by
        have hc : ContinuousAt (fun w : X => z - w) z :=
          (continuous_const.sub continuous_id).continuousAt
        apply hc.preimage_mem_nhds
        simpa using hcl _ (hWn (k + 1))
      obtain ⟨w, hwM, x, hx, rfl⟩ := mem_closure_iff_nhds.1 hz _ hM
      exact ⟨x, fun _ => ⟨hx, hwM⟩⟩
    · exact ⟨0, fun h => absurd h hz⟩
  choose g hg using step
  obtain ⟨ys, hys0, hyss⟩ : ∃ ys : ℕ → X, ys 0 = y ∧ ∀ k, ys (k + 1) = ys k - T (g k (ys k)) :=
    ⟨fun k => Nat.rec y (fun k yk => yk - T (g k yk)) k, rfl, fun _ => rfl⟩
  have hysmem : ∀ k, ys k ∈ closure (T '' W k) := by
    intro k
    induction k with
    | zero => rw [hys0]; exact hy
    | succ k ih => rw [hyss]; exact (hg k _ ih).2
  obtain ⟨x, hx⟩ : ∃ x : ℕ → G, ∀ k, x k = g k (ys k) := ⟨fun k => g k (ys k), fun _ => rfl⟩
  have hxmem : ∀ k, x k ∈ W k := fun k => by rw [hx]; exact (hg k _ (hysmem k)).1
  obtain ⟨s, hs⟩ : ∃ s : ℕ → G, ∀ m, s m = ∑ k ∈ Finset.range m, x k := ⟨_, fun _ => rfl⟩
  have hTs : ∀ m, T (s m) = y - ys m := by
    intro m
    induction m with
    | zero => simp [hs, hys0]
    | succ m ih =>
      have h1 : s (m + 1) = s m + x m := by rw [hs, hs, Finset.sum_range_succ]
      rw [h1, map_add, ih, hyss, hx]
      abel
  -- tails of the series stay in the `W j`
  have htail : ∀ n j, ∑ i ∈ Finset.range n, x (j + 1 + i) ∈ W j := by
    intro n
    induction n with
    | zero => intro j; simpa using hW0mem j
    | succ n ih =>
      intro j
      rw [Finset.sum_range_succ']
      have h2 : ∑ i ∈ Finset.range n, x (j + 1 + (i + 1)) =
          ∑ i ∈ Finset.range n, x (j + 1 + 1 + i) :=
        Finset.sum_congr rfl fun i _ => by rw [show j + 1 + (i + 1) = j + 1 + 1 + i by omega]
      rw [h2]
      exact hWadd j _ (ih (j + 1)) _ (by simpa using hxmem (j + 1))
  have hsplit : ∀ j n, s (j + 1 + n) = s (j + 1) + ∑ i ∈ Finset.range n, x (j + 1 + i) := by
    intro j n
    rw [hs, hs, Finset.sum_range_add]
  have hsV' : ∀ m, 1 ≤ m → s m ∈ V' := by
    intro m hm
    obtain ⟨n, rfl⟩ : ∃ n, m = 0 + 1 + n := ⟨m - 1, by omega⟩
    rw [hsplit]
    have h1 : s (0 + 1) = x 0 := by rw [hs]; simp
    rw [h1]
    exact hWadd0 _ (hxmem 0) _ (htail n 0)
  -- the partial sums form a Cauchy filter
  have hcau : IsCauchyFilter (map s atTop) := by
    refine ⟨inferInstance, fun U hU => ?_⟩
    obtain ⟨U₁, hU₁, hsub⟩ := exists_nhds_zero_sub hU
    obtain ⟨j, -, hj⟩ := hB.toHasBasis.mem_iff.1 hU₁
    refine ⟨s '' {m | j + 1 ≤ m}, image_mem_map (mem_atTop (j + 1)), ?_⟩
    rintro _ ⟨m, hm, rfl⟩ _ ⟨m', hm', rfl⟩
    obtain ⟨n, rfl⟩ : ∃ n, m = j + 1 + n := ⟨m - (j + 1), by have hm' : j + 1 ≤ m := hm; omega⟩
    obtain ⟨n', rfl⟩ : ∃ n', m' = j + 1 + n' :=
      ⟨m' - (j + 1), by have hm'' : j + 1 ≤ m' := hm'; omega⟩
    rw [hsplit, hsplit]
    have := hsub _ (hj (hWB j (htail n j))) _ (hj (hWB j (htail n' j)))
    simpa using this
  obtain ⟨x₀, hx₀⟩ := hG _ hcau
  have hlim : Tendsto s atTop (𝓝 x₀) := hx₀
  have hx₀V : x₀ ∈ V' :=
    hV'cl.mem_of_tendsto hlim (eventually_atTop.2 ⟨1, hsV'⟩)
  -- `ys k → 0`
  have hys : Tendsto ys atTop (𝓝 0) := by
    refine tendsto_def.2 fun N hN => ?_
    obtain ⟨N', hN', hN'cl, hN'N⟩ := exists_mem_nhds_isClosed_subset hN
    have hpre : T ⁻¹' N' ∈ 𝓝 (0 : G) := by
      apply hT.continuousAt.preimage_mem_nhds
      simpa using hN'
    obtain ⟨j, -, hj⟩ := hB.toHasBasis.mem_iff.1 hpre
    refine mem_atTop_sets.2 ⟨j, fun k hk => ?_⟩
    have hsub : T '' W k ⊆ N' := by
      rintro _ ⟨v, hv, rfl⟩
      exact hj (hB.antitone hk (hWB k hv))
    exact hN'N (closure_minimal hsub hN'cl (hysmem k))
  have h1 : Tendsto (fun m => T (s m)) atTop (𝓝 (T x₀)) :=
    (hT.tendsto x₀).comp hlim
  have h2 : Tendsto (fun m => T (s m)) atTop (𝓝 y) := by
    have : Tendsto (fun m => y - ys m) atTop (𝓝 (y - 0)) := tendsto_const_nhds.sub hys
    simpa [hTs] using this
  exact ⟨x₀, hV'V hx₀V, tendsto_nhds_unique h1 h2⟩

/-- **Baire category step.**  If countably many linear images of topological vector spaces cover a
Baire topological vector space `X`, then for one of the maps the closure of the image of every
`0`-neighbourhood is a `0`-neighbourhood. -/
theorem exists_closure_image_mem_nhds {X : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℂ X] [BaireSpace X]
    {G : ℕ → Type*} [∀ n, AddCommGroup (G n)] [∀ n, Module ℂ (G n)]
    [∀ n, TopologicalSpace (G n)] [∀ n, IsTopologicalAddGroup (G n)]
    [∀ n, ContinuousSMul ℂ (G n)]
    (T : ∀ n, G n →ₗ[ℂ] X) (hcov : ∀ x : X, ∃ n, x ∈ range (T n)) :
    ∃ n, ∀ V ∈ 𝓝 (0 : G n), closure (T n '' V) ∈ 𝓝 (0 : X) := by
  by_contra! h
  choose V hV hVn using h
  have hW : ∀ n, ∃ W ∈ 𝓝 (0 : G n), ∀ a ∈ W, ∀ b ∈ W, a - b ∈ V n :=
    fun n => exists_nhds_zero_sub (hV n)
  choose W hW hWV using hW
  let C : ℕ × ℕ → Set X := fun p => closure (((p.2 : ℂ) + 1) • (T p.1 '' W p.1))
  have hCcl : ∀ p, IsClosed (C p) := fun p => isClosed_closure
  have hc0 : ∀ k : ℕ, ((k : ℂ) + 1) ≠ 0 := fun k => by
    exact_mod_cast Nat.succ_ne_zero k
  have hU : ⋃ p, C p = univ := by
    refine eq_univ_of_forall fun x => ?_
    obtain ⟨n, g, rfl⟩ := hcov x
    have hlim : Tendsto (fun k : ℕ => ((k : ℂ) + 1)⁻¹ • g) atTop (𝓝 0) := by
      have h1 : Tendsto (fun k : ℕ => ((k : ℂ) + 1)⁻¹) atTop (𝓝 0) := by
        have h2 : Tendsto (fun k : ℕ => (((1 : ℝ) / ((k : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
          (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
        refine (h2.congr fun k => ?_).trans_eq ?_
        · push_cast; rw [one_div]
        · simp
      simpa using h1.smul_const g
    obtain ⟨k, hk⟩ := (hlim.eventually (hW n)).exists
    refine mem_iUnion.2 ⟨(n, k), subset_closure ?_⟩
    refine ⟨T n (((k : ℂ) + 1)⁻¹ • g), ⟨_, hk, rfl⟩, ?_⟩
    simp only [map_smul]
    rw [smul_smul, mul_inv_cancel₀ (hc0 k), one_smul]
  obtain ⟨⟨n, k⟩, w', hw'⟩ := nonempty_interior_of_iUnion_of_closed hCcl hU
  simp only [C] at hw'
  rw [closure_smul₀' (hc0 k), interior_smul₀ (hc0 k)] at hw'
  obtain ⟨w, hw, -⟩ := hw'
  refine hVn n ?_
  have hO : {z : X | w + z ∈ interior (closure (T n '' W n))} ∈ 𝓝 (0 : X) := by
    have hc : ContinuousAt (fun z : X => w + z) 0 :=
      (continuous_const.add continuous_id).continuousAt
    apply hc.preimage_mem_nhds
    simpa using isOpen_interior.mem_nhds hw
  refine mem_of_superset hO fun z hz => ?_
  have hz' : w + z ∈ closure (T n '' W n) := interior_subset hz
  have hw' : w ∈ closure (T n '' W n) := interior_subset hw
  have := map_mem_closure₂ (f := fun a b : X => a - b) (continuous_fst.sub continuous_snd)
    hz' hw' (u := T n '' V n) (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact ⟨a - b, hWV n a ha b hb, map_sub _ _ _⟩)
  simpa using this

/-- A locally convex topology (in the sense of the mission's definitions) is a vector space
topology. -/
theorem tvs_of_lc {E : Type*} [AddCommGroup E] [Module ℂ E] [t : TopologicalSpace E]
    (h : IsLocallyConvexTopology E t) : IsTopologicalAddGroup E ∧ ContinuousSMul ℂ E := by
  obtain ⟨ι, _, p, hp⟩ := h
  exact ⟨hp.topologicalAddGroup, hp.continuousSMul⟩

/-- Every `0`-neighbourhood of a locally convex space contains a balanced convex one. -/
theorem exists_absConvex_subset {A : Type*} [AddCommGroup A] [Module ℂ A] [t : TopologicalSpace A]
    (h : IsLocallyConvexTopology A t) {N : Set A} (hN : N ∈ 𝓝 (0 : A)) :
    ∃ C ∈ 𝓝 (0 : A), Balanced ℂ C ∧ Convex ℝ C ∧ C ⊆ N := by
  obtain ⟨ι, _, p, hp⟩ := h
  obtain ⟨⟨s, r⟩, hr, hsub⟩ := hp.hasBasis_zero_ball.mem_iff.1 hN
  exact ⟨(s.sup p).ball 0 r, hp.hasBasis_zero_ball.mem_of_mem (i := (s, r)) hr,
    Seminorm.balanced_ball_zero _ r, Seminorm.convex_ball _ _ _, hsub⟩

/-- A Fréchet space is a Baire space. -/
theorem baireSpace_of_isFrechet {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (h : IsFrechet E) : BaireSpace E := by
  obtain ⟨hlc, ⟨_, hcomp⟩, hmet⟩ := h
  obtain ⟨hadd, _⟩ := tvs_of_lc hlc
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have : (uniformity E).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : CompleteSpace E := by
    refine ⟨fun {f} hf => hcomp f ⟨hf.1, fun U hU => ?_⟩⟩
    have hmem : {p : E × E | p.2 - p.1 ∈ U} ∈ uniformity E := by
      rw [uniformity_eq_comap_nhds_zero E]
      exact preimage_mem_comap hU
    obtain ⟨t, ht, hts⟩ := mem_prod_same_iff.1 (hf.2 hmem)
    exact ⟨t, ht, fun x hx y hy => hts (mk_mem_prod hy hx)⟩
  infer_instance

/-- A closed subspace of a product of two complete spaces is complete. -/
theorem complete_closed_prod {A B : Type*} [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B]
    (hA : ∀ f : Filter A, IsCauchyFilter f → ∃ x : A, f ≤ 𝓝 x)
    (hB : ∀ f : Filter B, IsCauchyFilter f → ∃ x : B, f ≤ 𝓝 x)
    (S : Submodule ℂ (A × B)) (hS : IsClosed (S : Set (A × B))) :
    ∀ f : Filter S, IsCauchyFilter f → ∃ x : S, f ≤ 𝓝 x := by
  intro f hf
  have := hf.1
  have h1 : IsCauchyFilter (map (fun p : S => (p : A × B).1) f) := by
    refine ⟨inferInstance, fun U hU => ?_⟩
    have hc : ContinuousAt (fun p : S => (p : A × B).1) 0 :=
      (continuous_fst.comp continuous_subtype_val).continuousAt
    obtain ⟨D, hD, h⟩ := hf.2 _ (hc.preimage_mem_nhds (by simpa using hU))
    refine ⟨_, image_mem_map hD, ?_⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simpa using h x hx y hy
  have h2 : IsCauchyFilter (map (fun p : S => (p : A × B).2) f) := by
    refine ⟨inferInstance, fun U hU => ?_⟩
    have hc : ContinuousAt (fun p : S => (p : A × B).2) 0 :=
      (continuous_snd.comp continuous_subtype_val).continuousAt
    obtain ⟨D, hD, h⟩ := hf.2 _ (hc.preimage_mem_nhds (by simpa using hU))
    refine ⟨_, image_mem_map hD, ?_⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simpa using h x hx y hy
  obtain ⟨a, ha⟩ := hA _ h1
  obtain ⟨b, hb⟩ := hB _ h2
  have hlim : Tendsto (fun p : S => (p : A × B)) f (𝓝 (a, b)) := by
    rw [nhds_prod_eq]
    exact Filter.Tendsto.prodMk ha hb
  have hmem : (a, b) ∈ (S : Set (A × B)) :=
    hS.mem_of_tendsto hlim (Eventually.of_forall fun p => p.2)
  exact ⟨⟨(a, b), hmem⟩, tendsto_id'.1 (tendsto_subtype_rng.2 hlim)⟩

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

/-- A sequence of `0`-neighbourhoods starting at `U` with `V (k+1) + V (k+1) ⊆ V k`. -/
theorem exists_halving_seq {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] {U : Set G} (hU : U ∈ 𝓝 (0 : G)) :
    ∃ V : ℕ → Set G, V 0 = U ∧ (∀ k, V k ∈ 𝓝 (0 : G)) ∧
      ∀ k, ∀ v ∈ V (k + 1), ∀ w ∈ V (k + 1), v + w ∈ V k := by
  have half : ∀ s : Set G, ∃ U : Set G,
      s ∈ 𝓝 (0 : G) → (U ∈ 𝓝 (0 : G) ∧ ∀ v ∈ U, ∀ w ∈ U, v + w ∈ s) := by
    intro s
    by_cases hs : s ∈ 𝓝 (0 : G)
    · obtain ⟨U, hU, h⟩ := exists_nhds_zero_half hs
      exact ⟨U, fun _ => ⟨hU, h⟩⟩
    · exact ⟨univ, fun h => absurd h hs⟩
  choose half hhalf using half
  obtain ⟨V, hV0, hVs⟩ : ∃ V : ℕ → Set G, V 0 = U ∧ ∀ k, V (k + 1) = half (V k) :=
    ⟨fun k => Nat.rec U (fun _ Vk => half Vk) k, rfl, fun _ => rfl⟩
  have hVn : ∀ k, V k ∈ 𝓝 (0 : G) := by
    intro k
    induction k with
    | zero => rw [hV0]; exact hU
    | succ k ih => rw [hVs]; exact (hhalf _ ih).1
  refine ⟨V, hV0, hVn, fun k v hv w hw => ?_⟩
  rw [hVs] at hv hw
  exact (hhalf _ (hVn k)).2 v hv w hw

/-- **Open mapping theorem**, abstract form.  `E` is the locally convex inductive limit of the
Fréchet spaces `A m` along `i m`, the space `F` is covered by continuous linear images of the
Fréchet spaces `B n`, and `q : F → E` is a continuous linear surjection.  Then `q` is open. -/
theorem key {E F : Type*} [AddCommGroup E] [Module ℂ E] [tE : TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    (hE : IsHLCS E)
    {A : ℕ → Type*} [∀ m, AddCommGroup (A m)] [∀ m, Module ℂ (A m)]
    [tA : ∀ m, TopologicalSpace (A m)]
    (hA : ∀ m, IsFrechet (A m)) (i : ∀ m, A m →ₗ[ℂ] E) (hi : ∀ x : E, ∃ m, x ∈ range (i m))
    (htop : tE = sInf {t | IsLocallyConvexTopology E t ∧ ∀ m, @Continuous (A m) E _ t (i m)})
    {B : ℕ → Type*} [∀ n, AddCommGroup (B n)] [∀ n, Module ℂ (B n)]
    [tB : ∀ n, TopologicalSpace (B n)]
    (hB : ∀ n, IsFrechet (B n)) (j : ∀ n, B n →ₗ[ℂ] F) (hj : ∀ n, Continuous (j n))
    (hjcov : ∀ y : F, ∃ n, y ∈ range (j n))
    (q : F →ₗ[ℂ] E) (hq : Continuous q) (hsurj : Function.Surjective q) : IsOpenMap q := by
  obtain ⟨hlcE, hT2E⟩ := hE
  have := hT2E
  have hEadd : IsTopologicalAddGroup E := (tvs_of_lc hlcE).1
  have : ∀ m, IsTopologicalAddGroup (A m) := fun m => (tvs_of_lc (hA m).1).1
  have : ∀ m, ContinuousSMul ℂ (A m) := fun m => (tvs_of_lc (hA m).1).2
  have : ∀ n, IsTopologicalAddGroup (B n) := fun n => (tvs_of_lc (hB n).1).1
  have : ∀ n, ContinuousSMul ℂ (B n) := fun n => (tvs_of_lc (hB n).1).2
  have : ∀ m, T2Space (A m) := fun m => (hA m).2.1.1
  have : ∀ m, BaireSpace (A m) := fun m => baireSpace_of_isFrechet (hA m)
  have : ∀ m, FirstCountableTopology (A m) := fun m => by
    have := (hA m).2.2
    infer_instance
  have : ∀ n, FirstCountableTopology (B n) := fun n => by
    have := (hB n).2.2
    infer_instance
  have hic : ∀ m, Continuous (i m) := by
    intro m
    have h : @Continuous (A m) E _
        (sInf {t | IsLocallyConvexTopology E t ∧ ∀ m, @Continuous (A m) E _ t (i m)}) (i m) :=
      continuous_sInf_rng.2 fun t ht => ht.2 m
    rw [htop]
    exact h
  -- Step 1: for every `m`, the trace of `q '' U` on `A m` is a `0`-neighbourhood.
  have star : ∀ m, ∀ U ∈ 𝓝 (0 : F), {a : A m | i m a ∈ q '' U} ∈ 𝓝 (0 : A m) := by
    intro m
    let Gr : ∀ n : ℕ, Submodule ℂ (A m × B n) := fun n =>
      LinearMap.eqLocus ((i m).comp (LinearMap.fst ℂ (A m) (B n)))
        ((q.comp (j n)).comp (LinearMap.snd ℂ (A m) (B n)))
    have hGr : ∀ n (p : A m × B n), p ∈ Gr n ↔ i m p.1 = q (j n p.2) := fun n p =>
      LinearMap.mem_eqLocus
    let T : ∀ n : ℕ, Gr n →ₗ[ℂ] A m := fun n =>
      (LinearMap.fst ℂ (A m) (B n)).comp (Gr n).subtype
    have hTapp : ∀ n (p : Gr n), T n p = (p : A m × B n).1 := fun _ _ => rfl
    have hcov : ∀ a : A m, ∃ n, a ∈ range (T n) := by
      intro a
      obtain ⟨y, hy⟩ := hsurj (i m a)
      obtain ⟨n, b, rfl⟩ := hjcov y
      exact ⟨n, ⟨⟨(a, b), (hGr n _).2 hy.symm⟩, rfl⟩⟩
    obtain ⟨n, hn⟩ := exists_closure_image_mem_nhds (G := fun n => Gr n) T hcov
    have hclosed : IsClosed (Gr n : Set (A m × B n)) := by
      have h : IsClosed {p : A m × B n | i m p.1 = q (j n p.2)} :=
        isClosed_eq ((hic m).comp continuous_fst) (hq.comp ((hj n).comp continuous_snd))
      convert h using 1
      ext p
      exact hGr n p
    have hTc : Continuous (T n) := continuous_fst.comp continuous_subtype_val
    have hfc : FirstCountableTopology (Gr n) :=
      TopologicalSpace.Subtype.firstCountableTopology (Gr n : Set (A m × B n))
    have hopen := image_mem_nhds_of_closure
      (complete_closed_prod (hA m).2.1.2 (hB n).2.1.2 (Gr n) hclosed) (T n) hTc hn
    intro U hU
    have hV : {p : Gr n | j n (p : A m × B n).2 ∈ U} ∈ 𝓝 (0 : Gr n) := by
      have hc : ContinuousAt (fun p : Gr n => j n (p : A m × B n).2) 0 :=
        ((hj n).comp (continuous_snd.comp continuous_subtype_val)).continuousAt
      apply hc.preimage_mem_nhds
      simpa using hU
    refine mem_of_superset (hopen _ hV) ?_
    rintro _ ⟨p, hp, rfl⟩
    rw [hTapp]
    exact ⟨_, hp, ((hGr n _).1 p.2).symm⟩
  -- Step 2: `q` maps `0`-neighbourhoods to `0`-neighbourhoods.
  have h0 : ∀ U ∈ 𝓝 (0 : F), q '' U ∈ 𝓝 (0 : E) := by
    intro U hU
    obtain ⟨V, hV0, hVn, hVadd⟩ := exists_halving_seq hU
    have hC : ∀ m, ∃ C ∈ 𝓝 (0 : A m), Balanced ℂ C ∧ Convex ℝ C ∧
        C ⊆ {a : A m | i m a ∈ q '' V (m + 1)} :=
      fun m => exists_absConvex_subset (hA m).1 (star m _ (hVn (m + 1)))
    choose C hCn hCb hCc hCsub using hC
    have hD0 : ∀ m, (0 : E) ∈ i m '' C m := fun m =>
      ⟨0, mem_of_mem_nhds (hCn m), map_zero _⟩
    have hDb : ∀ m, Balanced ℂ (i m '' C m) := by
      intro m a ha
      rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨a • c, hCb m a ha (smul_mem_smul_set hc), map_smul _ _ _⟩
    have hDc : ∀ m, Convex ℝ (i m '' C m) := fun m =>
      (hCc m).is_linear_image ⟨map_add _, fun c x => LinearMap.map_smul_of_tower _ c x⟩
    obtain ⟨S, hS0, hSs⟩ : ∃ S : ℕ → Set E, S 0 = {0} ∧ ∀ k, S (k + 1) = S k + i k '' C k :=
      ⟨fun k => Nat.rec {0} (fun k Sk => Sk + i k '' C k) k, rfl, fun _ => rfl⟩
    have hSzero : ∀ k, (0 : E) ∈ S k := by
      intro k
      induction k with
      | zero => rw [hS0]; rfl
      | succ k ih => rw [hSs]; exact ⟨0, ih, 0, hD0 k, add_zero 0⟩
    have hSb : ∀ k, Balanced ℂ (S k) := by
      intro k
      induction k with
      | zero => rw [hS0]; exact balanced_zero
      | succ k ih => rw [hSs]; exact ih.add (hDb k)
    have hSc : ∀ k, Convex ℝ (S k) := by
      intro k
      induction k with
      | zero => rw [hS0]; exact convex_singleton 0
      | succ k ih => rw [hSs]; exact ih.add (hDc k)
    have hSmono : Monotone S := monotone_nat_of_le_succ fun k x hx => by
      rw [hSs]
      exact ⟨x, hx, 0, hD0 k, add_zero x⟩
    have hJ : ∀ k, ∀ z ∈ S k, ∃ r : F, q r = z ∧ ∀ v ∈ V k, r + v ∈ U := by
      intro k
      induction k with
      | zero =>
        intro z hz
        rw [hS0] at hz
        refine ⟨0, by rw [map_zero]; exact hz.symm, fun v hv => ?_⟩
        rw [zero_add, ← hV0]
        exact hv
      | succ k ih =>
        intro z hz
        rw [hSs] at hz
        obtain ⟨s, hs, _, ⟨c, hc, rfl⟩, rfl⟩ := hz
        obtain ⟨w, hw, hqw⟩ := hCsub k hc
        obtain ⟨r, hr, hrv⟩ := ih s hs
        refine ⟨r + w, by rw [map_add, hr, hqw], fun v hv => ?_⟩
        rw [add_assoc]
        exact hrv _ (hVadd k w hw v hv)
    have hWsub : (⋃ k, S k) ⊆ q '' U := by
      intro z hz
      obtain ⟨k, hk⟩ := mem_iUnion.1 hz
      obtain ⟨r, hr, hrv⟩ := hJ k z hk
      exact ⟨r, by simpa using hrv 0 (mem_of_mem_nhds (hVn k)), hr⟩
    have hWb : Balanced ℂ (⋃ k, S k) := balanced_iUnion hSb
    have hWc : Convex ℝ (⋃ k, S k) := hSmono.directed_le.convex_iUnion hSc
    have hWpre : ∀ m, C m ⊆ (i m) ⁻¹' (⋃ k, S k) := by
      intro m a ha
      refine mem_iUnion.2 ⟨m + 1, ?_⟩
      rw [hSs]
      exact ⟨0, hSzero m, i m a, ⟨a, ha, rfl⟩, zero_add _⟩
    have hWa : Absorbent ℝ (⋃ k, S k) := by
      intro x
      obtain ⟨m, a, rfl⟩ := hi x
      have hab : Absorbs ℂ (C m) {a} := absorbent_nhds_zero (hCn m) a
      obtain ⟨r, hr⟩ := absorbs_iff_norm.1 hab
      refine absorbs_iff_norm.2 ⟨r, fun c hc => ?_⟩
      have hc' : r ≤ ‖(c : ℂ)‖ := by simpa using hc
      obtain ⟨a', ha', rfl⟩ := hr (c : ℂ) hc' (mem_singleton a)
      rw [singleton_subset_iff]
      refine ⟨i m a', hWpre m ha', ?_⟩
      rw [map_smul]
      rfl
    exact mem_of_superset
      (mem_nhds_zero_of_inductive hlcE i htop _ hWb hWc hWa
        fun m => mem_of_superset (hCn m) (hWpre m)) hWsub
  -- Step 3: translate to arbitrary points.
  refine IsOpenMap.of_nhds_le fun x => ?_
  intro S hS
  have hS' : q ⁻¹' S ∈ 𝓝 x := hS
  have hU : {u : F | x + u ∈ q ⁻¹' S} ∈ 𝓝 (0 : F) := by
    have hc : ContinuousAt (fun u : F => x + u) 0 :=
      (continuous_const.add continuous_id).continuousAt
    apply hc.preimage_mem_nhds
    simpa using hS'
  have hN : {e : E | e - q x ∈ q '' {u : F | x + u ∈ q ⁻¹' S}} ∈ 𝓝 (q x) := by
    have hc : ContinuousAt (fun e : E => e - q x) (q x) :=
      (continuous_id.sub continuous_const).continuousAt
    apply hc.preimage_mem_nhds
    simpa using h0 _ hU
  refine mem_of_superset hN ?_
  rintro e ⟨u, hu, hue⟩
  have : q (x + u) = e := by rw [map_add, hue]; abel
  rw [← this]
  exact hu

end OpenMappingLF

theorem solution (E F : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul ℂ F] [T2Space F] (hE : IsLF E)
    (hF : ∃ (X : ℕ → Submodule ℂ F) (τ : ∀ n, TopologicalSpace (X n)), Monotone X ∧
      (∀ x : F, ∃ n, x ∈ X n) ∧ (∀ n, @IsFrechet (X n) _ _ (τ n)) ∧
      ∀ n, @Continuous (X n) F (τ n) _ Subtype.val)
    (q : F →ₗ[ℂ] E) (hq : Continuous q) (hsurj : Function.Surjective q) :
    IsOpenMap q := by
  obtain ⟨hHLCS, X, τ, hXexh, hXfre, -, hXtop⟩ := hE
  obtain ⟨Y, σ, -, hYexh, hYfre, hYcont⟩ := hF
  exact OpenMappingLF.key (A := fun m => X m) (tA := τ) (B := fun n => Y n) (tB := σ)
    hHLCS hXfre (fun m => (X m).subtype)
    (fun x => (hXexh x).imp fun m hm => ⟨⟨x, hm⟩, rfl⟩) hXtop
    hYfre (fun n => (Y n).subtype) hYcont
    (fun y => (hYexh y).imp fun n hn => ⟨⟨y, hn⟩, rfl⟩) q hq hsurj
