-- Prove2me | solution 1 for MasulloGRH.frechet_isSchauderBasis_of_existsUnique_expansion
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T17:54:26.07865+00:00
-- url     : https://prove2.me/submissions/0c1388d8-8f00-4a49-859e-2bb3db76b0d4

import Definitions.Def_MasulloGRH_SchauderBases

open Filter Topology

set_option autoImplicit false

namespace Sol_MasulloGRH_frechet_isSchauderBasis_of_existsUnique_expansion

open Set Function
open scoped Pointwise Uniformity UniformConvergence

set_option linter.unusedSectionVars false

/-- A continuous homomorphism from a complete first-countable additive group is open
if the closure of the image of each zero-neighborhood is a zero-neighborhood. -/
theorem isOpenMap_of_closure_image_mem_nhds_zero {G H : Type*}
    [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G] [CompleteSpace G]
    [FirstCountableTopology G] [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    [FirstCountableTopology H] [T2Space H] (f : G →+ H) (hf : Continuous f)
    (h : ∀ U ∈ 𝓝 (0 : G), closure (f '' U) ∈ 𝓝 (0 : H)) : IsOpenMap f := by
  obtain ⟨u, hu, hadd⟩ := IsTopologicalAddGroup.exists_antitone_basis_nhds_zero G
  obtain ⟨v, hv⟩ := (𝓝 (0 : H)).exists_antitone_basis
  apply IsTopologicalAddGroup.isOpenMap_iff_nhds_zero.mpr
  apply (hu.toHasBasis.map f).ge_iff.mpr
  intro m _
  let W (n : ℕ) := v n ∩ closure (f '' u (m + n + 2))
  have hW (n : ℕ) : W n ∈ 𝓝 (0 : H) := inter_mem (hv.mem n) (h _ (hu.mem _))
  refine mem_of_superset (hW 0) fun y hy ↦ ?_
  have step (n : ℕ) (z : G) (hz : y - f z ∈ W n) :
      ∃ a ∈ u (m + n + 2), y - f (z + a) ∈ W (n + 1) := by
    let r := y - f z
    have hn : {s : H | r - s ∈ W (n + 1)} ∈ 𝓝 r :=
      (continuous_const.sub continuous_id).tendsto' r 0 (sub_self r) (hW _)
    obtain ⟨_, ht, a, ha, rfl⟩ := (mem_closure_iff_nhds.mp hz.2) _ hn
    change y - f z - f a ∈ W (n + 1) at ht
    exact ⟨a, ha, by simpa only [map_add, sub_add_eq_sub_sub] using ht⟩
  let z : (n : ℕ) → {x : G // y - f x ∈ W n} := fun n ↦ Nat.recOn n
    ⟨0, by simpa using hy⟩ fun k zk ↦
      ⟨zk.val + (step k zk.val zk.property).choose, (step k zk.val zk.property).choose_spec.2⟩
  have hstep (n : ℕ) : (z (n + 1)).val - (z n).val ∈ u (m + n + 2) := by
    change (z n).val + (step n (z n).val (z n).property).choose - (z n).val ∈ _
    simpa only [add_sub_cancel_left] using (step n (z n).val (z n).property).choose_spec.1
  have hdiff {a b : ℕ} (hab : a ≤ b) : (z b).val - (z a).val ∈ u (m + a + 1) := by
    refine Nat.decreasingInduction' (P := fun a ↦ (z b).val - (z a).val ∈ u (m + a + 1)) ?_ hab ?_
    · intro k _ _ hk
      exact hadd (m + k + 1) ⟨_, hk, _, hstep k, sub_add_sub_cancel _ _ _⟩
    · simpa only [sub_self] using mem_of_mem_nhds (hu.mem (m + b + 1))
  have hc : CauchySeq (fun n ↦ (z n).val) := by
    have hb : (𝓤 G).HasBasis (fun _ : ℕ ↦ True) fun n ↦ {p : G × G | p.1 - p.2 ∈ u n} := by
      rw [uniformity_eq_comap_nhds_zero_swapped]
      exact hu.toHasBasis.comap _
    exact hb.cauchySeq_iff'.mpr fun n _ ↦
      ⟨n, fun b hb ↦ hu.antitone (by omega : n ≤ m + n + 1) (hdiff hb)⟩
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hc
  have hmem : x ∈ closure (u (m + 1)) := mem_closure_of_tendsto hx (Eventually.of_forall fun n ↦ by
    simpa only [show (z 0).val = 0 from rfl, sub_zero, Nat.add_zero] using hdiff (Nat.zero_le n))
  refine ⟨x, hadd m ((closure_subset_add_self_of_mem_nhds_zero (hu.mem _)) hmem), ?_⟩
  have hr : Tendsto (fun n ↦ y - f (z n).val) atTop (𝓝 0) := hv.toHasBasis.tendsto_right_iff.mpr
    fun k _ ↦ (eventually_ge_atTop k).mono fun n hn ↦ hv.antitone hn (z n).property.1
  exact (sub_eq_zero.mp
    (tendsto_nhds_unique (tendsto_const_nhds.sub ((hf.tendsto x).comp hx)) hr)).symm


/-- A continuous linear map from a complete first-countable topological vector space to a
first-countable Hausdorff space is open whenever its range is nonmeagre. -/
theorem isOpenMap_of_not_isMeagre_range
    {𝕜 G H : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup G] [Module 𝕜 G]
    [UniformSpace G] [IsUniformAddGroup G] [CompleteSpace G] [FirstCountableTopology G]
    [ContinuousSMul 𝕜 G] [AddCommGroup H] [Module 𝕜 H] [TopologicalSpace H]
    [IsTopologicalAddGroup H] [FirstCountableTopology H] [T2Space H] [ContinuousSMul 𝕜 H]
    (f : G →L[𝕜] H) (h : ¬ IsMeagre (range f)) : IsOpenMap f := by
  apply isOpenMap_of_closure_image_mem_nhds_zero f.toLinearMap.toAddMonoidHom f.continuous
  intro U hU
  have hs := (continuous_sub : Continuous (fun p : G × G ↦ p.1 - p.2)).tendsto' (0, 0) 0 (sub_self 0)
  obtain ⟨P, hP, Q, hQ, hPQ⟩ := mem_nhds_prod_iff.mp (hs hU)
  let V := P ∩ Q
  have hV : V ∈ 𝓝 (0 : G) := inter_mem hP hQ
  have hnon : (interior (closure (f '' V))).Nonempty := by
    by_contra! hd
    have hnd : IsNowhereDense (f '' V) := hd
    obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt 𝕜 zero_lt_one
    let t : 𝕜ˣ := Units.mk0 c (norm_pos_iff.mp hc0)
    let e (n : ℕ) : H ≃ₜ H := Homeomorph.smul ((t ^ n)⁻¹)
    have hcover : range f ⊆ ⋃ n : ℕ, e n '' (f '' V) := by
      rintro _ ⟨x, rfl⟩
      have hsmall : Tendsto (fun n : ℕ ↦ c ^ n • x) atTop (𝓝 0) := by
        simpa only [zero_smul] using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hc1).smul_const x
      have hevent : ∀ᶠ n : ℕ in atTop, c ^ n • x ∈ V := hsmall hV
      obtain ⟨n, hn⟩ := hevent.exists
      refine mem_iUnion.mpr ⟨n, f (c ^ n • x), ⟨_, hn, rfl⟩, ?_⟩
      change (t ^ n)⁻¹ • f (c ^ n • x) = f x
      rw [map_smul]
      exact inv_smul_smul (t ^ n) (f x)
    have hm := isMeagre_iUnion fun n ↦ ((e n).isEmbedding.isInducing.isNowhereDense_image hnd).isMeagre
    exact h (hm.mono hcover)
  obtain ⟨z, hz⟩ := hnon
  have hz' : {a : H | a + z ∈ closure (f '' V)} ∈ 𝓝 0 :=
    (continuous_id.add continuous_const).tendsto' 0 z (zero_add z) (mem_interior_iff_mem_nhds.mp hz)
  filter_upwards [hz'] with a ha
  rw [← add_sub_cancel_right a z]
  apply map_mem_closure₂ continuous_sub ha (interior_subset hz)
  rintro _ ⟨b, hb, rfl⟩ _ ⟨d, hd, rfl⟩
  exact ⟨b - d, hPQ (a := (b, d)) ⟨hb.1, hd.2⟩, map_sub f b d⟩

section complete

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]

/-- For a topological vector space, the Cauchy filters of the additive uniform structure are the
filters that are Cauchy in the sense of `IsCauchyFilter`. -/
theorem cauchy_iff_isCauchyFilter (f : Filter E) :
    @Cauchy E (IsTopologicalAddGroup.rightUniformSpace E) f ↔ MasulloGRH.IsCauchyFilter f := by
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
theorem completeSpace_of_isCompleteTVS [Module ℂ E] (h : MasulloGRH.IsCompleteTVS E) :
    @CompleteSpace E (IsTopologicalAddGroup.rightUniformSpace E) := by
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  exact ⟨fun {f} hf => h.2 f ((cauchy_iff_isCauchyFilter f).mp hf)⟩

end complete

/-- In the space `ℕ →ᵤ β` of sequences with the topology of uniform convergence, the Cauchy
sequences form a closed set. -/
theorem isClosed_setOf_cauchySeq {β : Type*} [UniformSpace β] :
    IsClosed {s : ℕ →ᵤ β | CauchySeq (UniformFun.toFun s)} := by
  refine isClosed_of_closure_subset fun s hs => ?_
  rw [mem_closure_iff_nhds_basis (UniformFun.hasBasis_nhds ℕ β s)] at hs
  refine cauchySeq_iff.mpr fun V hV => ?_
  obtain ⟨W, hW, hWs, hWV⟩ := comp_comp_symm_mem_uniformity_sets hV
  obtain ⟨t, ht, hst⟩ := hs W hW
  obtain ⟨N, hN⟩ := cauchySeq_iff.mp ht W hW
  refine ⟨N, fun k hk l hl => hWV ?_⟩
  have h1 : (UniformFun.toFun s k, UniformFun.toFun t k) ∈ W := hst k
  have h2 : (UniformFun.toFun t k, UniformFun.toFun t l) ∈ W := hN k hk l hl
  have h3 : (UniformFun.toFun t l, UniformFun.toFun s l) ∈ W := SetRel.symm W (hst l)
  exact ⟨_, ⟨_, h1, h2⟩, h3⟩

section core

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
  [ContinuousSMul ℂ E] [CompleteSpace E] [T2Space E] [FirstCountableTopology E]

/-- The partial sums `∑_{m ≤ k} a_m x_m`. -/
def psum (x : ℕ → E) (a : ℕ → ℂ) (k : ℕ) : E := ∑ m ∈ Finset.range (k + 1), a m • x m

theorem psum_zero (x : ℕ → E) (a : ℕ → ℂ) : psum x a 0 = a 0 • x 0 := by
  simp [psum]

theorem psum_succ (x : ℕ → E) (a : ℕ → ℂ) (k : ℕ) :
    psum x a (k + 1) = psum x a k + a (k + 1) • x (k + 1) := by
  simp only [psum]
  rw [Finset.sum_range_succ]

/-- The space of sequences of partial sums of convergent expansions along `x`, as a subspace of
the space `ℕ →ᵤ E` of sequences with the topology of uniform convergence. -/
def seqSpace (x : ℕ → E) : Submodule ℂ (ℕ →ᵤ E) where
  carrier := {s | (∃ v, Tendsto (UniformFun.toFun s) atTop (𝓝 v)) ∧
      UniformFun.toFun s 0 ∈ ℂ ∙ x 0 ∧
      ∀ k, UniformFun.toFun s (k + 1) - UniformFun.toFun s k ∈ ℂ ∙ x (k + 1)}
  add_mem' := by
    rintro s t ⟨⟨v, hv⟩, h0, hk⟩ ⟨⟨w, hw⟩, h0', hk'⟩
    refine ⟨⟨v + w, hv.add hw⟩, Submodule.add_mem _ h0 h0', fun k => ?_⟩
    have := Submodule.add_mem _ (hk k) (hk' k)
    convert this using 1
    change (UniformFun.toFun s (k + 1) + UniformFun.toFun t (k + 1)) -
      (UniformFun.toFun s k + UniformFun.toFun t k) = _
    abel
  zero_mem' := by
    refine ⟨⟨0, tendsto_const_nhds⟩, Submodule.zero_mem _, fun k => ?_⟩
    change (0 : E) - 0 ∈ _
    rw [sub_zero]
    exact Submodule.zero_mem _
  smul_mem' := by
    rintro c s ⟨⟨v, hv⟩, h0, hk⟩
    refine ⟨⟨c • v, hv.const_smul c⟩, Submodule.smul_mem _ c h0, fun k => ?_⟩
    have := Submodule.smul_mem _ c (hk k)
    convert this using 1
    change c • UniformFun.toFun s (k + 1) - c • UniformFun.toFun s k = _
    rw [smul_sub]

theorem isClosed_seqSpace (x : ℕ → E) : IsClosed (seqSpace x : Set (ℕ →ᵤ E)) := by
  have hcl : ∀ k, IsClosed ((ℂ ∙ x k : Submodule ℂ E) : Set E) := fun k =>
    Submodule.closed_of_finiteDimensional _
  have hev : ∀ k, Continuous fun s : ℕ →ᵤ E => UniformFun.toFun s k := fun k =>
    (UniformFun.uniformContinuous_eval E k).continuous
  have h1 : IsClosed {s : ℕ →ᵤ E | ∃ v, Tendsto (UniformFun.toFun s) atTop (𝓝 v)} := by
    have : {s : ℕ →ᵤ E | ∃ v, Tendsto (UniformFun.toFun s) atTop (𝓝 v)} =
        {s : ℕ →ᵤ E | CauchySeq (UniformFun.toFun s)} :=
      Set.ext fun s => ⟨fun ⟨v, hv⟩ => hv.cauchySeq, fun h => cauchySeq_tendsto_of_complete h⟩
    rw [this]
    exact isClosed_setOf_cauchySeq
  have h2 : IsClosed {s : ℕ →ᵤ E | UniformFun.toFun s 0 ∈ ℂ ∙ x 0} :=
    (hcl 0).preimage (hev 0)
  have h3 : IsClosed {s : ℕ →ᵤ E |
      ∀ k, UniformFun.toFun s (k + 1) - UniformFun.toFun s k ∈ ℂ ∙ x (k + 1)} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun k => (hcl (k + 1)).preimage ((hev (k + 1)).sub (hev k))
  exact h1.inter (h2.inter h3)


theorem mem_seqSpace (x : ℕ → E) (s : ℕ →ᵤ E) :
    s ∈ seqSpace x ↔ (∃ v, Tendsto (UniformFun.toFun s) atTop (𝓝 v)) ∧
      UniformFun.toFun s 0 ∈ ℂ ∙ x 0 ∧
      ∀ k, UniformFun.toFun s (k + 1) - UniformFun.toFun s k ∈ ℂ ∙ x (k + 1) := Iff.rfl

/-- Banach's theorem on coefficient functionals, for complete first-countable topological vector
spaces: if every vector has a unique expansion along `x`, the coefficient functionals are
continuous. -/
theorem core (x : ℕ → E)
    (hx : ∀ u : E, ∃! a : ℕ → ℂ,
      Tendsto (fun k => ∑ m ∈ Finset.range (k + 1), a m • x m) atTop (𝓝 u)) :
    ∃ f : ℕ → (E →L[ℂ] ℂ), (∀ m n, f m (x n) = if m = n then 1 else 0) ∧
      ∀ u, Tendsto (fun k => ∑ m ∈ Finset.range (k + 1), f m u • x m) atTop (𝓝 u) := by
  choose a ha hau using hx
  have ha' : ∀ u, Tendsto (psum x (a u)) atTop (𝓝 u) := ha
  have hu : ∀ u (b : ℕ → ℂ), Tendsto (psum x b) atTop (𝓝 u) → b = a u :=
    fun u b hb => hau u b hb
  -- linearity of the coefficients
  have a_add : ∀ u v, a (u + v) = a u + a v := by
    intro u v
    symm
    apply hu
    have : psum x (a u + a v) = psum x (a u) + psum x (a v) := by
      funext k
      simp only [psum, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    rw [this]
    exact (ha' u).add (ha' v)
  have a_smul : ∀ (c : ℂ) u, a (c • u) = c • a u := by
    intro c u
    symm
    apply hu
    have : psum x (c • a u) = c • psum x (a u) := by
      funext k
      simp only [psum, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
    rw [this]
    exact (ha' u).const_smul c
  -- the basis vectors are nonzero
  have hx0 : ∀ m, x m ≠ 0 := by
    intro m hm
    have h1 : Pi.single m (1 : ℂ) = a 0 := by
      apply hu
      have : psum x (Pi.single m 1) = fun _ => 0 := by
        funext k
        simp only [psum]
        refine Finset.sum_eq_zero fun j _ => ?_
        by_cases hj : j = m
        · subst hj
          simp [hm]
        · simp [Pi.single_eq_of_ne hj]
      rw [this]
      exact tendsto_const_nhds
    have h2 : (0 : ℕ → ℂ) = a 0 := by
      apply hu
      have : psum x 0 = fun _ => 0 := by
        funext k
        simp [psum]
      rw [this]
      exact tendsto_const_nhds
    have := congrFun (h1.trans h2.symm) m
    simp at this
  -- coefficients of the basis vectors
  have hortho : ∀ n, a (x n) = Pi.single n 1 := by
    intro n
    symm
    apply hu
    apply tendsto_atTop_of_eventually_const (i₀ := n)
    intro k hk
    simp only [psum]
    rw [Finset.sum_eq_single n]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · intro hn
      exact absurd (Finset.mem_range.mpr (by omega)) hn
  -- the sequence space and its structure
  let G := seqSpace x
  have : IsUniformAddGroup G := G.toAddSubgroup.isUniformAddGroup
  have : CompleteSpace G := completeSpace_coe_iff_isComplete.mpr (isClosed_seqSpace x).isComplete
  have : IsCountablyGenerated (𝓤 E) := IsUniformAddGroup.uniformity_countably_generated
  have : IsCountablyGenerated (𝓤 (ℕ →ᵤ E)) := by
    obtain ⟨V, hV⟩ := (𝓤 E).exists_antitone_basis
    exact (UniformFun.hasBasis_uniformity_of_basis ℕ E hV.toHasBasis).isCountablyGenerated
  have : FirstCountableTopology (ℕ →ᵤ E) := UniformSpace.firstCountableTopology _
  have : FirstCountableTopology G :=
    inferInstanceAs (FirstCountableTopology (G : Set (ℕ →ᵤ E)))
  let φ : G →ₗ[ℂ] (ℕ → E) :=
    { toFun := fun s => UniformFun.toFun (s : ℕ →ᵤ E)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have : ContinuousSMul ℂ G := by
    refine UniformFun.continuousSMul_induced_of_range_bounded ℂ ℕ E G φ IsInducing.subtypeVal ?_
    intro s
    obtain ⟨⟨v, hv⟩, -, -⟩ := (mem_seqSpace x _).mp s.2
    exact hv.isVonNBounded_range ℂ
  -- the limit map
  have hlim : ∀ s : G, Tendsto (UniformFun.toFun (s : ℕ →ᵤ E)) atTop
      (𝓝 (limUnder atTop (UniformFun.toFun (s : ℕ →ᵤ E)))) := fun s =>
    tendsto_nhds_limUnder ((mem_seqSpace x _).mp s.2).1
  let Llin : G →ₗ[ℂ] E :=
    { toFun := fun s => limUnder atTop (UniformFun.toFun (s : ℕ →ᵤ E))
      map_add' := fun s t => tendsto_nhds_unique (hlim (s + t)) ((hlim s).add (hlim t))
      map_smul' := fun c s => tendsto_nhds_unique (hlim (c • s)) ((hlim s).const_smul c) }
  have hLlim : ∀ s : G, Tendsto (UniformFun.toFun (s : ℕ →ᵤ E)) atTop (𝓝 (Llin s)) := hlim
  have hLcont : Continuous Llin := by
    apply continuous_of_continuousAt_zero Llin
    rw [ContinuousAt, map_zero]
    refine (closed_nhds_basis (0 : E)).tendsto_right_iff.mpr fun V ⟨hV, hVc⟩ => ?_
    have hmem : {s : G | ∀ k, UniformFun.toFun (s : ℕ →ᵤ E) k ∈ V} ∈ 𝓝 (0 : G) := by
      rw [nhds_subtype_eq_comap]
      exact preimage_mem_comap
        ((UniformFun.hasBasis_nhds_zero_of_basis (𝓝 (0 : E)).basis_sets).mem_of_mem hV)
    filter_upwards [hmem] with s hs
    exact hVc.mem_of_tendsto (hLlim s) (Eventually.of_forall hs)
  -- the inverse map
  have hψmem : ∀ u, UniformFun.ofFun (psum x (a u)) ∈ G := by
    intro u
    refine (mem_seqSpace x _).mpr ⟨⟨u, ha' u⟩, ?_, fun k => ?_⟩
    · change psum x (a u) 0 ∈ _
      rw [psum_zero]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · change psum x (a u) (k + 1) - psum x (a u) k ∈ _
      rw [psum_succ, add_sub_cancel_left]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  let ψ : E → G := fun u => ⟨UniformFun.ofFun (psum x (a u)), hψmem u⟩
  have hLψ : ∀ u, Llin (ψ u) = u := fun u => tendsto_nhds_unique (hLlim (ψ u)) (ha' u)
  have hψL : ∀ s : G, ψ (Llin s) = s := by
    intro s
    obtain ⟨-, h0, hk⟩ := (mem_seqSpace x _).mp s.2
    obtain ⟨b0, hb0⟩ := Submodule.mem_span_singleton.mp h0
    choose bk hbk using fun k => Submodule.mem_span_singleton.mp (hk k)
    let b : ℕ → ℂ := fun k => Nat.casesOn k b0 bk
    have hsb : ∀ k, UniformFun.toFun (s : ℕ →ᵤ E) k = psum x b k := by
      intro k
      induction k with
      | zero =>
        rw [psum_zero]
        exact hb0.symm
      | succ k ih =>
        rw [psum_succ, ← ih, show b (k + 1) = bk k from rfl, hbk k]
        abel
    have hsb' : UniformFun.toFun (s : ℕ →ᵤ E) = psum x b := funext hsb
    have hb : b = a (Llin s) := hu _ b (hsb' ▸ hLlim s)
    apply Subtype.ext
    change UniformFun.ofFun (psum x (a (Llin s))) = (s : ℕ →ᵤ E)
    rw [← hb, ← hsb']
    rfl
  -- open mapping
  let L : G →L[ℂ] E := ⟨Llin, hLcont⟩
  have : BaireSpace E := BaireSpace.of_completelyPseudoMetrizable
  have hrange : range L = univ := eq_univ_of_forall fun u => ⟨ψ u, hLψ u⟩
  have hopen : IsOpenMap L := isOpenMap_of_not_isMeagre_range L (by
    rw [hrange]
    exact not_isMeagre_of_isOpen isOpen_univ univ_nonempty)
  have hψcont : Continuous ψ := by
    rw [continuous_def]
    intro O hO
    have h := Set.image_eq_preimage_of_inverse (f := (L : G → E)) (g := ψ) hψL hLψ
    rw [← h]
    exact hopen O hO
  -- continuity of the coefficient functionals
  have hPcont : ∀ k, Continuous fun u => psum x (a u) k := fun k =>
    (UniformFun.uniformContinuous_eval E k).continuous.comp (continuous_subtype_val.comp hψcont)
  have hcoef : ∀ m, Continuous fun u => a u m • x m := by
    intro m
    cases m with
    | zero => simpa only [psum_zero] using hPcont 0
    | succ k =>
      refine ((hPcont (k + 1)).sub (hPcont k)).congr fun u => ?_
      simp only [Pi.sub_apply, psum_succ, add_sub_cancel_left]
  have hacont : ∀ m, Continuous fun u => a u m := fun m =>
    (isClosedEmbedding_smul_left (𝕜 := ℂ) (hx0 m)).isEmbedding.continuous_iff.mpr (hcoef m)
  let f : ℕ → (E →L[ℂ] ℂ) := fun m =>
    { toFun := fun u => a u m
      map_add' := fun u v => by simp only [a_add, Pi.add_apply]
      map_smul' := fun c u => by simp only [a_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      cont := hacont m }
  refine ⟨f, fun m n => ?_, fun u => ha' u⟩
  show a (x n) m = _
  rw [hortho n, Pi.single_apply]

end core

end Sol_MasulloGRH_frechet_isSchauderBasis_of_existsUnique_expansion

open MasulloGRH Sol_MasulloGRH_frechet_isSchauderBasis_of_existsUnique_expansion

theorem solution
    (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hF : IsFrechet E) (x : ℕ → E)
    (hx : ∀ u : E, ∃! a : ℕ → ℂ,
      Tendsto (fun k => ∑ m ∈ Finset.range (k + 1), a m • x m) atTop (𝓝 u)) :
    ∃ f : ℕ → StrongDual ℂ E, IsSchauderBasis x f := by
  obtain ⟨⟨ι, hι, p, hp⟩, hcomp, hmet⟩ := hF
  have : IsTopologicalAddGroup E := hp.topologicalAddGroup
  have : ContinuousSMul ℂ E := hp.continuousSMul
  have : T2Space E := hcomp.1
  letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace E := completeSpace_of_isCompleteTVS hcomp
  have : FirstCountableTopology E := inferInstance
  obtain ⟨f, hbi, hexp⟩ := core x hx
  exact ⟨f, ⟨hbi, hexp⟩⟩
