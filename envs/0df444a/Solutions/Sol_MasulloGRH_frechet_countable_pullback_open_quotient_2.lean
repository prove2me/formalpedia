-- Prove2me | solution 2 for MasulloGRH.frechet_countable_pullback_open_quotient
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T22:55:56.780278+00:00
-- url     : https://prove2.me/submissions/ed0f0a44-8de1-4e43-b63f-74175569bec4

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

open MasulloGRH Filter Function Set Topology TopologicalSpace
open scoped Pointwise Uniformity

private theorem addGroup_of_frechet {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (h : IsFrechet E) : IsTopologicalAddGroup E := by
  obtain ⟨_, _, _, hp⟩ := h.1
  exact hp.topologicalAddGroup

private theorem smul_of_frechet {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (h : IsFrechet E) : ContinuousSMul ℂ E := by
  obtain ⟨_, _, _, hp⟩ := h.1
  exact hp.continuousSMul

private theorem completeSpace_right_of_completeTVS {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] (h : IsCompleteTVS E) :
    @CompleteSpace E (IsTopologicalAddGroup.rightUniformSpace E) := by
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  refine ⟨fun {l} hl => h.2 l ?_⟩
  obtain ⟨hne, hdiff⟩ := (IsUniformAddGroup.cauchy_iff_tendsto l).mp hl
  refine ⟨hne, fun U hU => ?_⟩
  obtain ⟨s, hs, t, ht, hst⟩ := Filter.mem_prod_iff.mp (hdiff hU)
  exact ⟨s ∩ t, inter_mem hs ht, fun x hx y hy => hst (show (x, y) ∈ s ×ˢ t from ⟨hx.1, hy.2⟩)⟩

private theorem closure_image_mem_zero_of_nonmeagre {D E : Type*}
    [AddCommGroup D] [Module ℂ D] [TopologicalSpace D] [IsTopologicalAddGroup D]
    [ContinuousSMul ℂ D] [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] (p : D →ₗ[ℂ] E)
    (hp : ¬ IsMeagre (range p)) {U : Set D} (hU : U ∈ 𝓝 (0 : D)) :
    closure (p '' U) ∈ 𝓝 (0 : E) := by
  classical
  obtain ⟨V, hV, _, hsymm, hsum⟩ := exists_closed_nhds_zero_neg_eq_add_subset hU
  let c (n : ℕ) : ℂ := ((n + 1 : ℕ) : ℂ)
  have hc (n : ℕ) : c n ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have hcover : range p ⊆ ⋃ n, c n • (p '' V) := by
    rintro _ ⟨x, rfl⟩
    have hx : Absorbs ℂ V {x} := (absorbent_nhds_zero hV) x
    obtain ⟨R, _, hR⟩ := hx.exists_pos
    obtain ⟨n, hn⟩ := exists_nat_ge R
    have hn' : R ≤ ‖c n‖ := by
      rw [show ‖c n‖ = ((n + 1 : ℕ) : ℝ) from Complex.norm_natCast _]
      exact hn.trans (by exact_mod_cast Nat.le_succ n)
    obtain ⟨v, hv, hvx⟩ := mem_smul_set.mp (hR (c n) hn' (mem_singleton x))
    exact mem_iUnion.mpr ⟨n, mem_smul_set.mpr
      ⟨p v, ⟨v, hv, rfl⟩, by rw [← p.map_smul, hvx]⟩⟩
  have hinterior : (interior (closure (p '' V))).Nonempty := by
    by_contra h
    have he : interior (closure (p '' V)) = ∅ := not_nonempty_iff_eq_empty.mp h
    apply hp
    apply IsMeagre.mono hcover
    apply isMeagre_iUnion
    intro n
    apply IsNowhereDense.isMeagre
    change interior (closure (c n • (p '' V))) = ∅
    rw [closure_smul₀' (hc n), interior_smul₀ (hc n), he, smul_set_empty]
  obtain ⟨w, hw⟩ := hinterior
  have hdiff {x y : E} (hx : x ∈ closure (p '' V)) (hy : y ∈ closure (p '' V)) :
      x - y ∈ closure (p '' U) := by
    let subPair := fun z : E × E => z.1 - z.2
    have hsub : subPair '' ((p '' V) ×ˢ (p '' V)) ⊆ p '' U := by
      rintro _ ⟨⟨_, _⟩, ⟨⟨v, hv, rfl⟩, ⟨v', hv', rfl⟩⟩, rfl⟩
      have hneg : -v' ∈ V := hsymm ▸ neg_mem_neg.mpr hv'
      exact ⟨v - v', hsum ⟨v, hv, -v', hneg, (sub_eq_add_neg _ _).symm⟩, p.map_sub v v'⟩
    have hxy : (x, y) ∈ closure ((p '' V) ×ˢ (p '' V)) := by
      rw [closure_prod_eq]
      exact ⟨hx, hy⟩
    exact closure_mono hsub (image_closure_subset_closure_image
      (continuous_fst.sub continuous_snd) (mem_image_of_mem subPair hxy))
  have ht : Tendsto (fun z : E => z + w) (𝓝 0) (𝓝 w) := by
    simpa only [zero_add, id_eq] using (tendsto_id.add (tendsto_const_nhds (x := w)) :
      Tendsto (fun z : E => z + w) (𝓝 0) (𝓝 (0 + w)))
  have hn : ∀ᶠ z : E in 𝓝 0, z + w ∈ closure (p '' V) :=
    ht.eventually (mem_interior_iff_mem_nhds.mp hw)
  change ∀ᶠ z : E in 𝓝 0, z ∈ closure (p '' U)
  filter_upwards [hn] with z hz
  simpa only [add_sub_cancel_right] using hdiff hz (interior_subset hw)

private theorem image_mem_zero_of_closure_image {D E : Type*}
    [AddCommGroup D] [UniformSpace D] [IsUniformAddGroup D] [CompleteSpace D]
    [T2Space D] [FirstCountableTopology D] [AddCommGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [T2Space E] [FirstCountableTopology E]
    (p : D →+ E) (hp : Continuous p)
    (hclosure : ∀ U ∈ 𝓝 (0 : D), closure (p '' U) ∈ 𝓝 (0 : E))
    (U : Set D) (hU : U ∈ 𝓝 (0 : D)) : p '' U ∈ 𝓝 (0 : E) := by
  classical
  obtain ⟨K, hK, hKclosed, hKU⟩ := exists_mem_nhds_isClosed_subset hU
  obtain ⟨u, hu, hadd⟩ := IsTopologicalAddGroup.exists_antitone_basis_nhds_zero D
  obtain ⟨k, _, hk⟩ := hu.toHasBasis.mem_iff.mp hK
  obtain ⟨w, hw⟩ := (𝓝 (0 : E)).exists_antitone_basis
  let V (n : ℕ) := closure (p '' u (k + n + 1)) ∩ w n
  have hV (n : ℕ) : V n ∈ 𝓝 (0 : E) := inter_mem (hclosure _ (hu.mem _)) (hw.mem n)
  refine mem_of_superset (hV 0) ?_
  intro y hy
  -- At step n the residual is small enough to be approximated by the image of u (k+n+1).
  have improve (n : ℕ) (r : E) (hr : r ∈ V n) :
      ∃ d ∈ u (k + n + 1), r - p d ∈ V (n + 1) := by
    have ht : Tendsto (fun z : E => r - z) (𝓝 r) (𝓝 0) := by
      simpa only [sub_self] using ((tendsto_const_nhds (x := r)).sub tendsto_id :
        Tendsto (fun z : E => r - z) (𝓝 r) (𝓝 (r - r)))
    obtain ⟨_, ⟨d, hd, rfl⟩, hnext⟩ :=
      ((mem_closure_iff_frequently.mp hr.1).and_eventually (ht.eventually (hV (n + 1)))).exists
    exact ⟨d, hd, hnext⟩
  choose d hd hnext using improve
  have hinit : y - p 0 ∈ V 0 := by simpa only [map_zero, sub_zero] using hy
  let approx : (n : ℕ) → {x : D // y - p x ∈ V n} :=
    Nat.rec ⟨0, hinit⟩ (fun n x => ⟨x.val + d n (y - p x.val) x.property, by
      rw [map_add, ← sub_sub]
      exact hnext n (y - p x.val) x.property⟩)
  have hstep (n : ℕ) : (approx (n + 1)).val - (approx n).val ∈ u (k + n + 1) := by
    change (approx n).val + _ - (approx n).val ∈ _
    rw [add_sub_cancel_left]
    exact hd n (y - p (approx n).val) (approx n).property
  have htail (m n : ℕ) (hmn : m ≤ n) : (approx n).val - (approx m).val ∈ u (k + m) := by
    refine Nat.decreasingInduction' (fun j _ _ hj => ?_) hmn ?_
    · exact hadd (k + j) ⟨_, hstep j, _, by simpa only [Nat.add_assoc] using hj,
        (add_comm _ _).trans (sub_add_sub_cancel _ _ _)⟩
    · simpa only [sub_self] using mem_of_mem_nhds (hu.mem (k + n))
  have hc : CauchySeq (fun n => (approx n).val) := by
    have hUu : (𝓤 D).HasBasis (fun _ => True) (fun i => {z | z.1 - z.2 ∈ u i}) := by
      rw [uniformity_eq_comap_nhds_zero_swapped]
      exact hu.toHasBasis.comap _
    rw [hUu.cauchySeq_iff']
    exact fun i _ => ⟨i, fun n hi => hu.antitone (Nat.le_add_left i k) (htail i n hi)⟩
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hc
  have hxK : x ∈ K := hKclosed.mem_of_tendsto hx (Eventually.of_forall fun n =>
    hk (by simpa [approx] using htail 0 n (Nat.zero_le n)))
  have hres : Tendsto (fun n => y - p (approx n).val) atTop (𝓝 0) := by
    apply hw.toHasBasis.tendsto_right_iff.mpr
    intro i _
    exact (eventually_ge_atTop i).mono fun n hn => hw.antitone hn (approx n).property.2
  have hlim : Tendsto (fun n => y - p (approx n).val) atTop (𝓝 (y - p x)) :=
    tendsto_const_nhds.sub ((hp.tendsto x).comp hx)
  exact ⟨x, hKU hxK, (sub_eq_zero.mp (tendsto_nhds_unique hlim hres)).symm⟩

private theorem openQuotient_of_nonmeagre {D E : Type*}
    [AddCommGroup D] [Module ℂ D] [UniformSpace D] [IsUniformAddGroup D] [CompleteSpace D]
    [ContinuousSMul ℂ D] [T2Space D] [FirstCountableTopology D]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E] [T2Space E] [FirstCountableTopology E]
    (p : D →ₗ[ℂ] E) (hp : Continuous p) (hlarge : ¬ IsMeagre (range p)) :
    IsOpenQuotientMap p := by
  have himage : ∀ U ∈ 𝓝 (0 : D), p '' U ∈ 𝓝 (0 : E) :=
    image_mem_zero_of_closure_image p.toAddMonoidHom hp
      (fun _ hU => closure_image_mem_zero_of_nonmeagre p hlarge hU)
  have hsurj : Surjective p := by
    apply LinearMap.range_eq_top.mp
    apply Absorbent.submodule_eq_top
    apply absorbent_nhds_zero
    change range p ∈ 𝓝 (0 : E)
    simpa only [image_univ] using himage univ univ_mem
  refine ⟨hsurj, hp, isOpenMap_iff_nhds_le.mpr ?_⟩
  intro x
  have hz : 𝓝 (0 : E) ≤ map p (𝓝 (0 : D)) := le_map_iff.mpr himage
  calc
    𝓝 (p x) = map (fun z => p x + z) (𝓝 (0 : E)) := (map_add_left_nhds_zero _).symm
    _ ≤ map (fun z => p x + z) (map p (𝓝 (0 : D))) := map_mono hz
    _ = map p (𝓝 x) := by
      rw [← map_add_left_nhds_zero x, map_map, map_map]
      simp only [Function.comp_def, map_add]

theorem solution
    (A : Type*) [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] (hA : IsFrechet A)
    (B : ℕ → Type*) [∀ n, AddCommGroup (B n)] [∀ n, Module ℂ (B n)]
    [∀ n, TopologicalSpace (B n)] (hB : ∀ n, IsFrechet (B n))
    (G : Type*) [AddCommGroup G] [Module ℂ G] [TopologicalSpace G] [T2Space G]
    (a : A →ₗ[ℂ] G) (ha : Continuous a) (b : ∀ n, B n →ₗ[ℂ] G)
    (hb : ∀ n, Continuous (b n)) (hcover : ∀ g : G, ∃ n, g ∈ Set.range (b n)) :
    ∃ n, IsOpenQuotientMap
      (fun z : {p : A × B n // a p.1 = b n p.2} => z.val.1) := by
  classical
  let : IsTopologicalAddGroup A := addGroup_of_frechet hA
  let : ∀ n, IsTopologicalAddGroup (B n) := fun n => addGroup_of_frechet (hB n)
  let : ContinuousSMul ℂ A := smul_of_frechet hA
  let : ∀ n, ContinuousSMul ℂ (B n) := fun n => smul_of_frechet (hB n)
  let : T2Space A := hA.2.1.1
  let : ∀ n, T2Space (B n) := fun n => (hB n).2.1.1
  let : MetrizableSpace A := hA.2.2
  let : ∀ n, MetrizableSpace (B n) := fun n => (hB n).2.2
  let : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  let : ∀ n, UniformSpace (B n) := fun n => IsTopologicalAddGroup.rightUniformSpace (B n)
  let : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  let : ∀ n, IsUniformAddGroup (B n) := fun _ => isUniformAddGroup_of_addCommGroup
  let : CompleteSpace A := completeSpace_right_of_completeTVS hA.2.1
  let : ∀ n, CompleteSpace (B n) := fun n => completeSpace_right_of_completeTVS (hB n).2.1
  let : (𝓤 A).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  let P (n : ℕ) : Submodule ℂ (A × B n) :=
    { carrier := {z | a z.1 = b n z.2}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy
        change a x.1 = b n x.2 at hx
        change a y.1 = b n y.2 at hy
        change a (x.1 + y.1) = b n (x.2 + y.2)
        rw [map_add, map_add, hx, hy]
      smul_mem' := by
        intro r x hx
        change a x.1 = b n x.2 at hx
        change a (r • x.1) = b n (r • x.2)
        rw [map_smul, map_smul, hx] }
  let p (n : ℕ) : P n →ₗ[ℂ] A := (LinearMap.fst ℂ A (B n)).comp (P n).subtype
  have hcoverA : ⋃ n, range (p n) = univ := eq_univ_of_forall fun x => by
    obtain ⟨n, y, hy⟩ := hcover (a x)
    exact mem_iUnion.mpr ⟨n, ⟨⟨(x, y), hy.symm⟩, rfl⟩⟩
  have hAmeagre : ¬ IsMeagre (univ : Set A) := not_isMeagre_of_isOpen isOpen_univ univ_nonempty
  obtain ⟨n, hn⟩ : ∃ n, ¬ IsMeagre (range (p n)) := by
    by_contra! hm
    exact hAmeagre (hcoverA ▸ isMeagre_iUnion hm)
  have hclosed : IsClosed (P n : Set (A × B n)) :=
    isClosed_eq (ha.comp continuous_fst) ((hb n).comp continuous_snd)
  let : CompleteSpace (P n) := hclosed.isComplete.completeSpace_coe
  let : IsUniformAddGroup (P n) :=
    isUniformEmbedding_subtype_val.isUniformInducing.isUniformAddGroup (P n).subtype.toAddMonoidHom
  let : FirstCountableTopology (B n) := inferInstance
  let : FirstCountableTopology (P n) := Subtype.firstCountableTopology (P n : Set (A × B n))
  exact ⟨n, openQuotient_of_nonmeagre (p n) (continuous_fst.comp continuous_subtype_val) hn⟩
