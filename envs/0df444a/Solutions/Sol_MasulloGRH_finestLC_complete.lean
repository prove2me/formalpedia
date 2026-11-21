-- Prove2me | solution 1 for MasulloGRH.finestLC_complete
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:49:15.46788+00:00
-- url     : https://prove2.me/submissions/a17fd0de-a9be-4fee-b531-ec28cb27d4da

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

open MasulloGRH Set Topology

universe u v

namespace FinestLC

variable {E : Type u} [AddCommGroup E] [Module ℂ E]

/-- The family of all seminorms on `E`. -/
abbrev allSeminorms (E : Type u) [AddCommGroup E] [Module ℂ E] : SeminormFamily ℂ E (Seminorm ℂ E) :=
  fun p => p

theorem continuous_into_seminorms {A F I : Type*} [AddCommGroup A] [Module ℂ A]
    [tA : TopologicalSpace A] [gA : IsTopologicalAddGroup A] [AddCommGroup F] [Module ℂ F]
    {τ : TopologicalSpace F} {q : SeminormFamily ℂ F I}
    (hq : WithSeminorms (topology := τ) q) (f : A →ₗ[ℂ] F)
    (h : ∀ i, Continuous ((q i).comp f)) : @Continuous A F _ τ f := by
  let _ := τ
  exact hq.continuous_of_continuous_comp f h

/-- The topology defined by all seminorms is the finest locally convex topology. -/
theorem allSeminorms_topology_eq :
    (allSeminorms E).moduleFilterBasis.topology = sInf {t | IsLocallyConvexTopology E t} := by
  have hτ : WithSeminorms (topology := (allSeminorms E).moduleFilterBasis.topology)
      (allSeminorms E) := by
    let _ : TopologicalSpace E := (allSeminorms E).moduleFilterBasis.topology
    exact ⟨rfl⟩
  apply le_antisymm
  · refine le_sInf fun t ht => ?_
    obtain ⟨κ, _, q, hq⟩ := ht
    rw [← continuous_id_iff_le]
    let _ : TopologicalSpace E := (allSeminorms E).moduleFilterBasis.topology
    have : IsTopologicalAddGroup E := hτ.topologicalAddGroup
    refine continuous_into_seminorms hq LinearMap.id fun i => ?_
    rw [Seminorm.comp_id]
    exact hτ.continuous_seminorm (q i)
  · exact sInf_le ⟨Seminorm ℂ E, ⟨0⟩, allSeminorms E, hτ⟩

/-- **Proposition C.2.5.1(1)**: the finest locally convex topology is defined by the family of
all seminorms. -/
theorem withSeminorms_all [TopologicalSpace E] (h : HasFinestLocallyConvexTopology E) :
    WithSeminorms (allSeminorms E) :=
  ⟨h.trans allSeminorms_topology_eq.symm⟩

/-- **Proposition C.2.5.1(2)**: every linear map into a locally convex space is continuous. -/
theorem linearMap_continuous [TopologicalSpace E] (h : HasFinestLocallyConvexTopology E)
    {M : Type v} [AddCommGroup M] [Module ℂ M] [TopologicalSpace M]
    (hM : IsLocallyConvexTopology M ‹TopologicalSpace M›) (T : E →ₗ[ℂ] M) : Continuous T := by
  have hall := withSeminorms_all h
  obtain ⟨κ, _, q, hq⟩ := hM
  have : IsTopologicalAddGroup E := hall.topologicalAddGroup
  exact hq.continuous_of_continuous_comp T fun i => hall.continuous_seminorm ((q i).comp T)


theorem isLocallyConvexTopology_complex :
    IsLocallyConvexTopology ℂ (inferInstance : TopologicalSpace ℂ) :=
  ⟨Fin 1, inferInstance, fun _ => normSeminorm ℂ ℂ, norm_withSeminorms ℂ ℂ⟩

/-- Every linear functional is continuous for the finest locally convex topology. -/
theorem linearFunctional_continuous [TopologicalSpace E] (h : HasFinestLocallyConvexTopology E)
    (f : E →ₗ[ℂ] ℂ) : Continuous f :=
  linearMap_continuous h isLocallyConvexTopology_complex f

/-- **Proposition C.2.5.1(3)**, closedness: every linear subspace is closed. -/
theorem submodule_isClosed [TopologicalSpace E] (h : HasFinestLocallyConvexTopology E)
    (V : Submodule ℂ E) : IsClosed (V : Set E) := by
  have hV : (V : Set E) = ⋂ φ ∈ V.dualAnnihilator, {x : E | φ x = 0} := by
    ext x
    have h1 : x ∈ V ↔ x ∈ V.dualAnnihilator.dualCoannihilator := by
      rw [Subspace.dualAnnihilator_dualCoannihilator_eq]
    simp only [SetLike.mem_coe, mem_iInter, mem_ofPred_eq]
    rw [h1, Submodule.mem_dualCoannihilator]
  rw [hV]
  refine isClosed_biInter fun φ _ => ?_
  exact isClosed_eq (linearFunctional_continuous h φ) continuous_const

/-- **Proposition C.2.5.1(3)**, complements: every linear subspace is topologically
complemented. -/
theorem submodule_closedComplemented [TopologicalSpace E] (h : HasFinestLocallyConvexTopology E)
    (V : Submodule ℂ E) : V.ClosedComplemented := by
  have hall := withSeminorms_all h
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl V
  have hlcV : IsLocallyConvexTopology V (inferInstance : TopologicalSpace V) :=
    ⟨Seminorm ℂ E, ⟨0⟩, _, V.subtype.withSeminorms_induced hall⟩
  exact ⟨⟨Submodule.projectionOnto V W hW,
    linearMap_continuous h hlcV (Submodule.projectionOnto V W hW)⟩,
    fun x => Submodule.projectionOnto_apply_left hW x⟩

/-- **Proposition C.2.5.1(3)**, subspaces: the induced topology on a subspace is its finest locally
convex topology. -/
theorem submodule_finest [TopologicalSpace E] (h : HasFinestLocallyConvexTopology E)
    (V : Submodule ℂ E) : HasFinestLocallyConvexTopology V := by
  have hall := withSeminorms_all h
  have hadd : IsTopologicalAddGroup E := hall.topologicalAddGroup
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl V
  have haddV : IsTopologicalAddGroup V := inferInstance
  -- every seminorm on `V` is continuous for the induced topology
  have hsc : ∀ r : Seminorm ℂ V, Continuous r := by
    intro r
    have h1 : Continuous fun v : V =>
        (r.comp (Submodule.projectionOnto V W hW)) (v : E) :=
      (hall.continuous_seminorm (r.comp (Submodule.projectionOnto V W hW))).comp
        continuous_subtype_val
    have h2 : (fun v : V => (r.comp (Submodule.projectionOnto V W hW)) (v : E)) = ⇑r := by
      funext v
      rw [Seminorm.comp_apply, Submodule.projectionOnto_apply_left]
    rw [h2] at h1
    exact h1
  apply le_antisymm
  · refine le_sInf fun t ht => ?_
    obtain ⟨κ, _, q, hq⟩ := ht
    rw [← continuous_id_iff_le]
    refine continuous_into_seminorms (tA := instTopologicalSpaceSubtype) (gA := haddV) hq
      LinearMap.id fun i => ?_
    rw [Seminorm.comp_id]
    exact hsc (q i)
  · exact sInf_le ⟨Seminorm ℂ E, ⟨0⟩, _, V.subtype.withSeminorms_induced hall⟩

/-- **Proposition C.2.5.1(3)**, quotients: the quotient topology on `E ⧸ V` is its finest locally
convex topology. -/
theorem quotient_finest [TopologicalSpace E] (h : HasFinestLocallyConvexTopology E)
    (V : Submodule ℂ E) : HasFinestLocallyConvexTopology (E ⧸ V) := by
  have hall := withSeminorms_all h
  have hadd : IsTopologicalAddGroup E := hall.topologicalAddGroup
  have hlcE : IsLocallyConvexTopology E ‹TopologicalSpace E› :=
    ⟨Seminorm ℂ E, ⟨0⟩, _, hall⟩
  change (inferInstance : TopologicalSpace (E ⧸ V)) = sInf {t | IsLocallyConvexTopology (E ⧸ V) t}
  rw [← allSeminorms_topology_eq]
  have hτ : WithSeminorms (topology := (allSeminorms (E ⧸ V)).moduleFilterBasis.topology)
      (allSeminorms (E ⧸ V)) := by
    let _ : TopologicalSpace (E ⧸ V) := (allSeminorms (E ⧸ V)).moduleFilterBasis.topology
    exact ⟨rfl⟩
  apply le_antisymm
  · -- every seminorm on the quotient is continuous for the quotient topology
    rw [← continuous_id_iff_le]
    refine continuous_into_seminorms hτ LinearMap.id fun r => ?_
    rw [Seminorm.comp_id]
    refine V.isQuotientMap_mkQL.continuous_iff.2 ?_
    exact hall.continuous_seminorm (r.comp V.mkQ)
  · -- a linear section of the quotient map is continuous for the finest topology
    obtain ⟨s, hs⟩ := V.mkQ.exists_rightInverse_of_surjective (Submodule.range_mkQ V)
    rw [← continuous_id_iff_le]
    have hsc : @Continuous (E ⧸ V) E (allSeminorms (E ⧸ V)).moduleFilterBasis.topology _ s :=
      @linearMap_continuous (E ⧸ V) _ _ (allSeminorms (E ⧸ V)).moduleFilterBasis.topology
        allSeminorms_topology_eq E _ _ _ hlcE s
    have hcomp : @Continuous (E ⧸ V) (E ⧸ V) (allSeminorms (E ⧸ V)).moduleFilterBasis.topology _
        (fun x => V.mkQ (s x)) :=
      @Continuous.comp _ _ _ (allSeminorms (E ⧸ V)).moduleFilterBasis.topology _ _ _ _
        V.mkQL.continuous hsc
    have hid : (fun x : E ⧸ V => V.mkQ (s x)) = id := by
      funext x
      exact LinearMap.congr_fun hs x
    rw [hid] at hcomp
    exact hcomp

/-- A continuous seminorm is bounded on a von Neumann bounded set. -/
theorem seminorm_bounded_on {G : Type*} [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    (q : Seminorm ℂ G) (hq : Continuous q) {B : Set G}
    (hB : Bornology.IsVonNBounded ℂ B) : ∃ M : ℝ, 0 < M ∧ ∀ x ∈ B, q x ≤ M := by
  have hq1 : {x : G | q x < 1} ∈ 𝓝 (0 : G) :=
    (isOpen_lt hq continuous_const).mem_nhds (by simp)
  obtain ⟨ρ, hρ⟩ := absorbs_iff_norm.1 (hB hq1)
  refine ⟨max ρ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun x hx => ?_⟩
  have hnorm : ‖((max ρ 1 : ℝ) : ℂ)‖ = max ρ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (le_trans zero_le_one (le_max_right _ _))]
  obtain ⟨y, hy, rfl⟩ := hρ ((max ρ 1 : ℝ) : ℂ) (by rw [hnorm]; exact le_max_left _ _) hx
  have hy' : q y < 1 := hy
  change q (((max ρ 1 : ℝ) : ℂ) • y) ≤ max ρ 1
  rw [map_smul_eq_mul, hnorm]
  nlinarith [le_max_right ρ 1, apply_nonneg q y]

/-- **Proposition C.2.5.1(4)**: a set is bounded for the finest locally convex topology iff it is a
bounded subset of a finite-dimensional subspace. -/
theorem isVonNBounded_iff [TopologicalSpace E] (h : HasFinestLocallyConvexTopology E)
    (B : Set E) :
    Bornology.IsVonNBounded ℂ B ↔ ∃ V : Submodule ℂ E, FiniteDimensional ℂ V ∧
      ∃ B' : Set V, Bornology.IsVonNBounded ℂ B' ∧ B = Subtype.val '' B' := by
  have hall := withSeminorms_all h
  have hadd : IsTopologicalAddGroup E := hall.topologicalAddGroup
  have hsmul : ContinuousSMul ℂ E := hall.continuousSMul
  constructor
  · intro hB
    -- the span of `B` is finite-dimensional
    have hfin : FiniteDimensional ℂ (Submodule.span ℂ B) := by
      obtain ⟨b, hbB, hspan, hli⟩ := exists_linearIndependent ℂ B
      by_cases hbf : b.Finite
      · rw [← hspan]
        exact FiniteDimensional.span_of_finite ℂ hbf
      · exfalso
        let emb := Set.Infinite.natEmbedding b hbf
        have hlin : LinearIndependent ℂ (fun n : ℕ => ((emb n : b) : E)) :=
          hli.comp emb emb.injective
        -- a linear functional with values `n` on the `n`-th vector
        let f₀ : Submodule.span ℂ (range fun n : ℕ => ((emb n : b) : E)) →ₗ[ℂ] ℂ :=
          (Finsupp.linearCombination ℂ fun n : ℕ => (n : ℂ)) ∘ₗ hlin.repr
        obtain ⟨φ, hφ⟩ := LinearMap.exists_extend f₀
        have hφn : ∀ n : ℕ, φ ((emb n : b) : E) = (n : ℂ) := by
          intro n
          have hmem : ((emb n : b) : E) ∈ Submodule.span ℂ (range fun n : ℕ => ((emb n : b) : E)) :=
            Submodule.subset_span ⟨n, rfl⟩
          have h1 := LinearMap.congr_fun hφ ⟨_, hmem⟩
          have h2 : hlin.repr ⟨_, hmem⟩ = Finsupp.single n 1 :=
            hlin.repr_eq_single n ⟨_, hmem⟩ rfl
          simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h1
          rw [h1]
          simp [f₀, h2]
        have hφc : Continuous φ := linearFunctional_continuous h φ
        obtain ⟨M, -, hM⟩ := seminorm_bounded_on φ.toSeminorm (continuous_norm.comp hφc) hB
        obtain ⟨n, hn⟩ := exists_nat_gt M
        have h3 := hM _ (hbB (emb n).2)
        rw [LinearMap.toSeminorm_apply, hφn] at h3
        simp at h3
        linarith
    refine ⟨Submodule.span ℂ B, hfin, Subtype.val ⁻¹' B, ?_, ?_⟩
    · have hind := (Submodule.span ℂ B).subtype.withSeminorms_induced hall
      apply hind.isVonNBounded_iff_seminorm_bounded.mpr
      intro p
      obtain ⟨r, hr, hrB⟩ := hall.isVonNBounded_iff_seminorm_bounded.mp hB p
      exact ⟨r, hr, fun x hx => hrB _ hx⟩
    · ext x
      constructor
      · intro hx
        exact ⟨⟨x, Submodule.subset_span hx⟩, hx, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact hy
  · rintro ⟨V, -, B', hB', rfl⟩
    exact hB'.image V.subtypeL


/-- A linear map from a finite-dimensional Hausdorff topological vector space into a locally convex
space is continuous. -/
theorem fd_continuous {V : Type*} {F : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup F] [Module ℂ F] (σ : TopologicalSpace V) (h1 : @T2Space V σ)
    (h2 : @IsTopologicalAddGroup V σ _) (h3 : @ContinuousSMul ℂ V _ _ σ)
    (t : TopologicalSpace F) (ht : IsLocallyConvexTopology F t) (f : V →ₗ[ℂ] F) :
    @Continuous V F σ t f := by
  obtain ⟨κ, _, q, hq⟩ := ht
  have : IsTopologicalAddGroup F := hq.topologicalAddGroup
  have : ContinuousSMul ℂ F := hq.continuousSMul
  exact f.continuous_of_finiteDimensional


/-- The finest locally convex topology is Hausdorff. -/
theorem t2Space_of_finest [TopologicalSpace E] (h : HasFinestLocallyConvexTopology E) :
    T2Space E := by
  have hall := withSeminorms_all h
  have hadd : IsTopologicalAddGroup E := hall.topologicalAddGroup
  refine IsTopologicalAddGroup.t2Space_of_zero_sep fun x hx => ?_
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ E, φ x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx ((Module.forall_dual_apply_eq_zero_iff ℂ x).1 hcon)
  have hc := linearFunctional_continuous h φ
  exact ⟨{y | ‖φ y‖ < ‖φ x‖}, (isOpen_lt hc.norm continuous_const).mem_nhds (by simpa using hφ),
    by simp⟩

/-- **Proposition C.2.5.1(5)**: a set is sequentially closed iff its intersection with every
finite-dimensional subspace is closed. -/
theorem isSeqClosed_iff [TopologicalSpace E] (h : HasFinestLocallyConvexTopology E) (C : Set E) :
    IsSeqClosed C ↔
      ∀ V : Submodule ℂ E, FiniteDimensional ℂ V → IsClosed (C ∩ (V : Set E)) := by
  have hall := withSeminorms_all h
  have hadd : IsTopologicalAddGroup E := hall.topologicalAddGroup
  have hsmul : ContinuousSMul ℂ E := hall.continuousSMul
  have hT2 : T2Space E := t2Space_of_finest h
  constructor
  · intro hC V hV
    have hVcl : IsClosed (V : Set E) := submodule_isClosed h V
    -- a finite-dimensional Hausdorff topological vector space is first countable
    have hfc : FirstCountableTopology V :=
      (Module.finBasis ℂ V).equivFunL.toHomeomorph.isInducing.firstCountableTopology
    have hpre : IsSeqClosed ((Subtype.val : V → E) ⁻¹' C) :=
      hC.preimage continuous_subtype_val.seqContinuous
    have hclV : IsClosed ((Subtype.val : V → E) ⁻¹' C) := hpre.isClosed
    have himg := hVcl.isClosedEmbedding_subtypeVal.isClosedMap _ hclV
    have heq : (Subtype.val : V → E) '' ((Subtype.val : V → E) ⁻¹' C) = C ∩ (V : Set E) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨hy, y.2⟩
      · rintro ⟨hxC, hxV⟩
        exact ⟨⟨x, hxV⟩, hxC, rfl⟩
    rw [← heq]
    exact himg
  · intro hfd x a hx ha
    have hb : Bornology.IsVonNBounded ℂ (insert a (range x)) :=
      (ha.isVonNBounded_range ℂ).insert a
    obtain ⟨V, hV, B', -, hB'⟩ := (isVonNBounded_iff h _).1 hb
    have hsub : insert a (range x) ⊆ (V : Set E) := by
      rw [hB']
      rintro _ ⟨y, -, rfl⟩
      exact y.2
    have hmem : a ∈ C ∩ (V : Set E) :=
      (hfd V hV).mem_of_tendsto ha
        (Filter.Eventually.of_forall fun n => ⟨hx n, hsub (mem_insert_of_mem _ ⟨n, rfl⟩)⟩)
    exact hmem.1


/-- The weighted `ℓ¹` seminorm `x ↦ ∑ w i * |x_i|` with respect to a basis. -/
noncomputable def wSeminorm {ι : Type*} (b : Module.Basis ι ℂ E) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) : Seminorm ℂ E :=
  Seminorm.of (fun x => ∑ i ∈ (b.repr x).support, w i * ‖b.repr x i‖)
    (fun x y => by
      classical
      have key : ∀ (z : E) (S : Finset ι), (b.repr z).support ⊆ S →
          ∑ i ∈ (b.repr z).support, w i * ‖b.repr z i‖ = ∑ i ∈ S, w i * ‖b.repr z i‖ := by
        intro z S hS
        refine Finset.sum_subset hS fun i _ hi => ?_
        rw [Finsupp.notMem_support_iff.1 hi, norm_zero, mul_zero]
      have hsup : (b.repr (x + y)).support ⊆ (b.repr x).support ∪ (b.repr y).support := by
        rw [map_add]; exact Finsupp.support_add
      rw [key (x + y) _ hsup, key x _ Finset.subset_union_left, key y _ Finset.subset_union_right,
        ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [← mul_add, map_add, Finsupp.add_apply]
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (hw i))
    (fun c x => by
      classical
      have hsup : (b.repr (c • x)).support ⊆ (b.repr x).support := by
        rw [map_smul]; exact Finsupp.support_smul
      rw [Finset.sum_subset hsup fun i _ hi => by
        rw [Finsupp.notMem_support_iff.1 hi, norm_zero, mul_zero], Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]
      ring)

theorem wSeminorm_eq_sum {ι : Type*} (b : Module.Basis ι ℂ E) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (x : E) (S : Finset ι) (hS : (b.repr x).support ⊆ S) :
    wSeminorm b w hw x = ∑ i ∈ S, w i * ‖b.repr x i‖ := by
  change ∑ i ∈ (b.repr x).support, w i * ‖b.repr x i‖ = _
  refine Finset.sum_subset hS fun i _ hi => ?_
  rw [Finsupp.notMem_support_iff.1 hi, norm_zero, mul_zero]

theorem le_wSeminorm {ι : Type*} (b : Module.Basis ι ℂ E) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (x : E) (i : ι) : w i * ‖b.repr x i‖ ≤ wSeminorm b w hw x := by
  classical
  rw [wSeminorm_eq_sum b w hw x (insert i (b.repr x).support) (Finset.subset_insert _ _)]
  exact Finset.single_le_sum (f := fun j => w j * ‖b.repr x j‖)
    (fun j _ => mul_nonneg (hw j) (norm_nonneg _)) (Finset.mem_insert_self _ _)

theorem seminorm_finset_sum_le (p : Seminorm ℂ E) {ι : Type*} (S : Finset ι) (g : ι → E) :
    p (∑ i ∈ S, g i) ≤ ∑ i ∈ S, p (g i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (map_add_le_add p _ _).trans (add_le_add le_rfl ih)

theorem seminorm_le_wSeminorm {ι : Type*} (b : Module.Basis ι ℂ E) (p : Seminorm ℂ E) (x : E) :
    p x ≤ wSeminorm b (fun i => p (b i)) (fun i => apply_nonneg p _) x := by
  have hx : x = ∑ i ∈ (b.repr x).support, b.repr x i • b i := by
    conv_lhs => rw [← b.linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
  change p x ≤ ∑ i ∈ (b.repr x).support, p (b i) * ‖b.repr x i‖
  calc p x = p (∑ i ∈ (b.repr x).support, b.repr x i • b i) := by rw [← hx]
    _ ≤ ∑ i ∈ (b.repr x).support, p (b.repr x i • b i) := seminorm_finset_sum_le p _ _
    _ = ∑ i ∈ (b.repr x).support, p (b i) * ‖b.repr x i‖ :=
        Finset.sum_congr rfl fun i _ => by rw [map_smul_eq_mul, mul_comm]

/-- **Proposition C.2.5.1(3)**, completeness: the finest locally convex topology is complete. -/
theorem complete_of_finest [TopologicalSpace E] (h : HasFinestLocallyConvexTopology E) :
    IsCompleteTVS E := by
  classical
  have hall := withSeminorms_all h
  have hadd : IsTopologicalAddGroup E := hall.topologicalAddGroup
  have hsmul : ContinuousSMul ℂ E := hall.continuousSMul
  refine ⟨t2Space_of_finest h, fun f hf => ?_⟩
  obtain ⟨hne, hcau⟩ := hf
  have hne' : f.NeBot := hne
  let b := Module.Basis.ofVectorSpace ℂ E
  -- the filter is Cauchy for every seminorm
  have hcs : ∀ (q : Seminorm ℂ E) (ε : ℝ), 0 < ε → ∃ A ∈ f, ∀ x ∈ A, ∀ y ∈ A, q (x - y) < ε :=
    fun q ε hε => hcau {z | q z < ε}
      ((isOpen_lt (hall.continuous_seminorm q) continuous_const).mem_nhds (by simpa using hε))
  -- every coordinate converges
  have hcoord : ∀ i, ∃ a : ℂ, Filter.Tendsto (fun x => b.repr x i) f (𝓝 a) := by
    intro i
    have hC : Cauchy (Filter.map (fun x => b.repr x i) f) := by
      rw [Metric.cauchy_iff]
      refine ⟨inferInstance, fun ε hε => ?_⟩
      obtain ⟨A, hA, hAd⟩ := hcs (b.coord i).toSeminorm ε hε
      refine ⟨_, Filter.image_mem_map hA, ?_⟩
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      have h1 := hAd x hx y hy
      rw [LinearMap.toSeminorm_apply, Module.Basis.coord_apply, map_sub, Finsupp.sub_apply] at h1
      rw [dist_eq_norm]
      exact h1
    obtain ⟨a, ha⟩ := CompleteSpace.complete hC
    exact ⟨a, ha⟩
  choose a ha using hcoord
  -- only finitely many limits are nonzero
  have hfin : (Function.support a).Finite := by
    by_contra hinf
    let emb := Set.Infinite.natEmbedding _ hinf
    obtain ⟨sq, hsq⟩ : ∃ sq : ℕ → Module.Basis.ofVectorSpaceIndex ℂ E, ∀ n, sq n = (emb n).1 :=
      ⟨fun n => (emb n).1, fun _ => rfl⟩
    have hs_inj : Function.Injective sq := fun m n hmn => by
      rw [hsq, hsq] at hmn
      exact emb.injective (Subtype.ext hmn)
    have hs_ne : ∀ n : ℕ, a (sq n) ≠ 0 := fun n => by rw [hsq]; exact (emb n).2
    let w : Module.Basis.ofVectorSpaceIndex ℂ E → ℝ := fun i =>
      if hi : ∃ n : ℕ, sq n = i then (hi.choose : ℝ) / ‖a i‖ else 0
    have hw : ∀ i, 0 ≤ w i := by
      intro i
      simp only [w]
      split_ifs with hi
      · positivity
      · exact le_rfl
    have hwn : ∀ n : ℕ, w (sq n) = (n : ℝ) / ‖a (sq n)‖ := by
      intro n
      have hi : ∃ m : ℕ, sq m = sq n := ⟨n, rfl⟩
      simp only [w, dif_pos hi]
      rw [hs_inj hi.choose_spec]
    obtain ⟨A, hA, hAd⟩ := hcs (wSeminorm b w hw) 1 one_pos
    obtain ⟨y₀, hy₀⟩ := hne'.nonempty_of_mem hA
    -- an index `n ≥ 2` outside the support of `y₀`
    have hfinN : {n : ℕ | sq n ∈ (b.repr y₀).support}.Finite :=
      (b.repr y₀).support.finite_toSet.preimage (hs_inj.injOn)
    obtain ⟨n, hn⟩ := (hfinN.union (Set.finite_lt_nat 2)).exists_notMem
    have hn1 : sq n ∉ (b.repr y₀).support := fun hc => hn (Or.inl hc)
    have hn2 : 2 ≤ n := by
      by_contra hc
      exact hn (Or.inr (not_le.1 hc))
    have hy0 : b.repr y₀ (sq n) = 0 := Finsupp.notMem_support_iff.1 hn1
    have hapos : 0 < ‖a (sq n)‖ := norm_pos_iff.2 (hs_ne n)
    have hbound : ∀ x ∈ A, ‖b.repr x (sq n)‖ ≤ ‖a (sq n)‖ / 2 := by
      intro x hx
      have h1 := (le_wSeminorm b w hw (x - y₀) (sq n)).trans (hAd x hx y₀ hy₀).le
      rw [hwn, map_sub, Finsupp.sub_apply, hy0, sub_zero, div_mul_eq_mul_div,
        div_le_one hapos] at h1
      have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      nlinarith [norm_nonneg (b.repr x (sq n))]
    have hlim : Filter.Tendsto (fun x => ‖b.repr x (sq n)‖) f (𝓝 ‖a (sq n)‖) :=
      (ha (sq n)).norm
    have hle : ‖a (sq n)‖ ≤ ‖a (sq n)‖ / 2 :=
      le_of_tendsto hlim (Filter.mem_of_superset hA hbound)
    linarith
  -- the candidate limit
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : E, ∀ i, b.repr x₀ i = a i :=
    ⟨b.repr.symm (Finsupp.ofSupportFinite a hfin), fun i => by
      rw [LinearEquiv.apply_symm_apply]; rfl⟩
  refine ⟨x₀, ?_⟩
  rw [(hall.hasBasis_ball (x := x₀)).ge_iff]
  rintro ⟨s, ε⟩ hε
  have hε : 0 < ε := hε
  obtain ⟨p, hp⟩ : ∃ p : Seminorm ℂ E, p = s.sup (allSeminorms E) := ⟨_, rfl⟩
  rw [← hp]
  obtain ⟨A, hA, hAd⟩ :=
    hcs (wSeminorm b (fun i => p (b i)) (fun i => apply_nonneg p _)) (ε / 2) (by positivity)
  obtain ⟨y₀, hy₀⟩ := hne'.nonempty_of_mem hA
  obtain ⟨S, hS⟩ : ∃ S : Finset _, S = (b.repr y₀).support ∪ hfin.toFinset := ⟨_, rfl⟩
  -- on the finite set `S` the coordinates converge
  have hG : Filter.Tendsto (fun z => ∑ i ∈ S, p (b i) * ‖b.repr z i - a i‖) f (𝓝 0) := by
    have h1 : Filter.Tendsto (fun z => ∑ i ∈ S, p (b i) * ‖b.repr z i - a i‖) f
        (𝓝 (∑ i ∈ S, p (b i) * ‖a i - a i‖)) :=
      tendsto_finsetSum _ fun i _ => ((ha i).sub_const (a i)).norm.const_mul _
    simpa using h1
  have hGev : ∀ᶠ z in f, ∑ i ∈ S, p (b i) * ‖b.repr z i - a i‖ < ε / 2 :=
    hG.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hGev, hA] with z hz hzA
  rw [Seminorm.mem_ball]
  refine lt_of_le_of_lt (seminorm_le_wSeminorm b p (z - x₀)) ?_
  -- split the weighted sum into the part on `S` and the rest
  obtain ⟨T, hT⟩ : ∃ T : Finset _, T = S ∪ (b.repr (z - x₀)).support ∪ (b.repr (z - y₀)).support :=
    ⟨_, rfl⟩
  have hST : S ⊆ T := by rw [hT]; exact Finset.subset_union_left.trans Finset.subset_union_left
  rw [wSeminorm_eq_sum b _ _ (z - x₀) T
    (by rw [hT]; exact Finset.subset_union_right.trans Finset.subset_union_left),
    ← Finset.sum_sdiff hST]
  have hrest : ∑ i ∈ T \ S, p (b i) * ‖b.repr (z - x₀) i‖ ≤
      wSeminorm b (fun i => p (b i)) (fun i => apply_nonneg p _) (z - y₀) := by
    rw [wSeminorm_eq_sum b _ _ (z - y₀) T (by rw [hT]; exact Finset.subset_union_right)]
    have hcongr : ∑ i ∈ T \ S, p (b i) * ‖b.repr (z - x₀) i‖ =
        ∑ i ∈ T \ S, p (b i) * ‖b.repr (z - y₀) i‖ := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hiS : i ∉ S := (Finset.mem_sdiff.1 hi).2
      rw [hS, Finset.mem_union, not_or] at hiS
      have h1 : b.repr y₀ i = 0 := Finsupp.notMem_support_iff.1 hiS.1
      have h2 : a i = 0 := by
        by_contra hne0
        exact hiS.2 (hfin.mem_toFinset.2 hne0)
      rw [map_sub, map_sub, Finsupp.sub_apply, Finsupp.sub_apply, hx₀, h1, h2]
    rw [hcongr]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      fun i _ _ => mul_nonneg (apply_nonneg p _) (norm_nonneg _)
  have hSsum : ∑ i ∈ S, p (b i) * ‖b.repr (z - x₀) i‖ =
      ∑ i ∈ S, p (b i) * ‖b.repr z i - a i‖ :=
    Finset.sum_congr rfl fun i _ => by rw [map_sub, Finsupp.sub_apply, hx₀]
  rw [hSsum]
  have h3 := hAd z hzA y₀ hy₀
  linarith

end FinestLC

theorem solution (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (h : HasFinestLocallyConvexTopology E) : IsCompleteTVS E := by
  exact FinestLC.complete_of_finest h
