-- Prove2me | solution 1 for MasulloGRH.finestLC_countable_dimension
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T01:01:11.958901+00:00
-- url     : https://prove2.me/submissions/b294b774-7470-431e-a9d7-ac977e506f9e

import Theorems.Thm_MasulloGRH_nuclear_of_quasinuclear_domination
import Theorems.Thm_MasulloGRH_nuclear_of_countable_inductive_limit
import Theorems.Thm_MasulloGRH_nuclear_barrelled_quasiComplete_isMontel
import Theorems.Thm_MasulloGRH_strongDual_nuclear_of_complete_nuclear_DF
import Theorems.Thm_MasulloGRH_strongDual_isHLCS

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


/-- The finest locally convex topology is Hausdorff locally convex. -/
theorem isHLCS_of_finest [TopologicalSpace E] (h : HasFinestLocallyConvexTopology E) : IsHLCS E :=
  ⟨⟨Seminorm ℂ E, ⟨0⟩, _, withSeminorms_all h⟩, t2Space_of_finest h⟩

/-- A finite-dimensional space with its finest locally convex topology is nuclear. -/
theorem nuclear_of_finiteDimensional [TopologicalSpace E] (h : HasFinestLocallyConvexTopology E)
    [FiniteDimensional ℂ E] : IsNuclear E := by
  classical
  have hall := withSeminorms_all h
  refine nuclear_of_quasinuclear_domination E (isHLCS_of_finest h) fun p _ => ?_
  let b := Module.finBasis ℂ E
  let k := Module.finrank ℂ E
  let q : Seminorm ℂ E := wSeminorm b (fun _ => 1) (fun _ => zero_le_one)
  let f : ℕ → StrongDual ℂ E := fun n =>
    if hn : n < k then ⟨b.coord ⟨n, hn⟩, linearFunctional_continuous h _⟩ else 0
  let c : ℕ → ℝ := fun n => if hn : n < k then p (b ⟨n, hn⟩) else 0
  have hf : ∀ (n : ℕ) (hn : n < k) (x : E), f n x = b.repr x ⟨n, hn⟩ := by
    intro n hn x
    simp only [f, dif_pos hn]
    rfl
  have hc : ∀ (n : ℕ) (hn : n < k), c n = p (b ⟨n, hn⟩) := fun n hn => by
    simp only [c, dif_pos hn]
  have hc0 : ∀ n, k ≤ n → c n = 0 := fun n hn => by
    simp only [c, dif_neg (not_lt.2 hn)]
  refine ⟨q, f, c, hall.continuous_seminorm q, fun n => ?_, ?_, fun n x => ?_, fun x => ?_⟩
  · by_cases hn : n < k
    · rw [hc n hn]; exact apply_nonneg p _
    · rw [hc0 n (not_lt.1 hn)]
  · exact summable_of_ne_finset_zero (s := Finset.range k) fun n hn =>
      hc0 n (not_lt.1 fun h' => hn (Finset.mem_range.2 h'))
  · by_cases hn : n < k
    · rw [hf n hn]
      have := le_wSeminorm b (fun _ => (1 : ℝ)) (fun _ => zero_le_one) x ⟨n, hn⟩
      simpa using this
    · have : f n = 0 := by simp only [f, dif_neg hn]
      rw [this]
      simpa using apply_nonneg q x
  · have h1 := seminorm_le_wSeminorm b p x
    rw [wSeminorm_eq_sum b _ _ x Finset.univ (Finset.subset_univ _)] at h1
    have h2 : ∑' n, c n * ‖f n x‖ = ∑ n ∈ Finset.range k, c n * ‖f n x‖ :=
      tsum_eq_sum fun n hn => by
        rw [hc0 n (not_lt.1 fun h' => hn (Finset.mem_range.2 h')), zero_mul]
    rw [h2, ← Fin.sum_univ_eq_sum_range (fun n => c n * ‖f n x‖) k]
    refine h1.trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
    rw [hc j j.2, hf j j.2]

/-- A finite-dimensional space with its finest locally convex topology is a Fréchet space. -/
theorem isFrechet_of_finiteDimensional [TopologicalSpace E]
    (h : HasFinestLocallyConvexTopology E) [FiniteDimensional ℂ E] : IsFrechet E := by
  have hall := withSeminorms_all h
  have hadd : IsTopologicalAddGroup E := hall.topologicalAddGroup
  have hsmul : ContinuousSMul ℂ E := hall.continuousSMul
  have hT2 : T2Space E := t2Space_of_finest h
  refine ⟨⟨Seminorm ℂ E, ⟨0⟩, _, hall⟩, complete_of_finest h, ?_⟩
  exact (Module.finBasis ℂ E).equivFunL.toHomeomorph.isEmbedding.metrizableSpace

/-- A linear map from a subspace (with the induced finest topology) into a locally convex space
is continuous. -/
theorem subtype_continuous_into [tE : TopologicalSpace E] (h : HasFinestLocallyConvexTopology E)
    (V : Submodule ℂ E) {F : Type v} [AddCommGroup F] [Module ℂ F] (τ : TopologicalSpace F)
    (hτ : IsLocallyConvexTopology F τ) (T : V →ₗ[ℂ] F) : @Continuous V F _ τ T := by
  have hV := submodule_finest h V
  have hallV := withSeminorms_all hV
  have haddV : IsTopologicalAddGroup V := hallV.topologicalAddGroup
  obtain ⟨κ, _, q, hq⟩ := hτ
  exact continuous_into_seminorms hq T fun i => hallV.continuous_seminorm ((q i).comp T)

/-- **Proposition C.2.5.1(6)**, first assertion: a countable-dimensional space with its finest
locally convex topology is a strict countable inductive limit of nuclear Fréchet spaces. -/
theorem strictLF_of_countable [tE : TopologicalSpace E] (h : HasFinestLocallyConvexTopology E)
    (hc : ∃ s : Set E, s.Countable ∧ Submodule.span ℂ s = ⊤) :
    IsStrictLFOfNuclearFrechet E := by
  have hall := withSeminorms_all h
  have hadd : IsTopologicalAddGroup E := hall.topologicalAddGroup
  obtain ⟨s, hs, hspan⟩ := hc
  obtain ⟨g, hg⟩ := (hs.insert 0).exists_eq_range (insert_nonempty 0 s)
  let X : ℕ → Submodule ℂ E := fun n => Submodule.span ℂ (g '' Iio n)
  have hmono : Monotone X := fun m n hmn =>
    Submodule.span_mono (image_mono (Iio_subset_Iio hmn))
  have hfd : ∀ n, FiniteDimensional ℂ (X n) := fun n =>
    FiniteDimensional.span_of_finite ℂ ((finite_Iio n).image g)
  have hexh : ∀ x : E, ∃ n, x ∈ X n := by
    intro x
    have hx : x ∈ Submodule.span ℂ (range g) := by
      rw [← hg]
      exact Submodule.span_mono (subset_insert 0 s) (hspan ▸ Submodule.mem_top)
    have hU : range g = ⋃ n, g '' Iio n := by
      ext y
      constructor
      · rintro ⟨k, rfl⟩
        exact mem_iUnion.2 ⟨k + 1, ⟨k, Nat.lt_succ_self k, rfl⟩⟩
      · intro hy
        obtain ⟨n, k, -, rfl⟩ := mem_iUnion.1 hy
        exact ⟨k, rfl⟩
    rw [hU, Submodule.span_iUnion] at hx
    exact (Submodule.mem_iSup_of_directed _ hmono.directed_le).1 hx
  have hfin : ∀ n, HasFinestLocallyConvexTopology (X n) := fun n => submodule_finest h (X n)
  refine ⟨X, hmono, hexh, fun n => ⟨?_, ?_⟩, ?_⟩
  · have := hfd n
    exact isFrechet_of_finiteDimensional (hfin n)
  · have := hfd n
    exact nuclear_of_finiteDimensional (hfin n)
  · -- every locally convex topology makes the inclusions of the steps continuous
    have hset : {t | IsLocallyConvexTopology E t ∧
        ∀ n, @Continuous (X n) E _ t Subtype.val} = {t | IsLocallyConvexTopology E t} := by
      ext t
      constructor
      · exact fun ht => ht.1
      · intro ht
        exact ⟨ht, fun n => subtype_continuous_into (tE := tE) h (X n) t ht (X n).subtype⟩
    rw [hset]
    exact h

/-- **Proposition C.2.5.1(6)**: nuclearity in the countable-dimensional case. -/
theorem nuclear_of_countable [TopologicalSpace E] (h : HasFinestLocallyConvexTopology E)
    (hc : ∃ s : Set E, s.Countable ∧ Submodule.span ℂ s = ⊤) : IsNuclear E := by
  obtain ⟨X, hmono, hexh, hX, htop⟩ := strictLF_of_countable h hc
  refine nuclear_of_countable_inductive_limit E (isHLCS_of_finest h) X
    (fun n => instTopologicalSpaceSubtype) hexh (fun n => ⟨hmono (Nat.le_succ n), ?_⟩)
    (fun n => (hX n).2) htop
  exact Continuous.subtype_mk continuous_subtype_val _

/-- For the finest locally convex topology every seminorm is continuous, so the space is
barrelled. -/
theorem barrelled_of_finest [TopologicalSpace E] (h : HasFinestLocallyConvexTopology E) :
    BarrelledSpace ℂ E :=
  ⟨fun p _ => (withSeminorms_all h).continuous_seminorm p⟩

/-- **Proposition C.2.5.1(6)**: the Montel property in the countable-dimensional case. -/
theorem montel_of_countable [TopologicalSpace E] (h : HasFinestLocallyConvexTopology E)
    (hc : ∃ s : Set E, s.Countable ∧ Submodule.span ℂ s = ⊤) : IsMontel E := by
  have := barrelled_of_finest h
  have hcomp := complete_of_finest h
  exact nuclear_barrelled_quasiComplete_isMontel E ⟨hcomp.1, fun f hf _ => hcomp.2 f hf⟩
    (nuclear_of_countable h hc)


theorem isLocallyConvexTopology_pi (m : ℕ) :
    IsLocallyConvexTopology (Fin m → ℂ) (inferInstance : TopologicalSpace (Fin m → ℂ)) :=
  ⟨Fin 1, inferInstance, fun _ => normSeminorm ℂ (Fin m → ℂ), norm_withSeminorms ℂ (Fin m → ℂ)⟩

/-- A countable-dimensional space with its finest locally convex topology has a fundamental
sequence of bounded sets. -/
theorem exists_fundamental_bounded [TopologicalSpace E] (h : HasFinestLocallyConvexTopology E)
    (hc : ∃ s : Set E, s.Countable ∧ Submodule.span ℂ s = ⊤) :
    ∃ B : ℕ → Set E, (∀ n, Bornology.IsVonNBounded ℂ (B n)) ∧
      ∀ S : Set E, Bornology.IsVonNBounded ℂ S → ∃ n, S ⊆ B n := by
  classical
  have hall := withSeminorms_all h
  have hadd : IsTopologicalAddGroup E := hall.topologicalAddGroup
  have hsmul : ContinuousSMul ℂ E := hall.continuousSMul
  obtain ⟨s, hs, hspan⟩ := hc
  obtain ⟨g, hg⟩ := (hs.insert 0).exists_eq_range (insert_nonempty 0 s)
  have hgspan : Submodule.span ℂ (range g) = ⊤ := by
    rw [← hg]
    exact top_le_iff.1 (hspan ▸ Submodule.span_mono (subset_insert 0 s))
  let B : ℕ → Set E := fun n =>
    {x | ∃ c : ℕ → ℂ, (∀ k, ‖c k‖ ≤ n) ∧ x = ∑ k ∈ Finset.range n, c k • g k}
  refine ⟨B, fun n => ?_, fun S hS => ?_⟩
  · -- each `B n` is bounded
    apply hall.isVonNBounded_iff_seminorm_bounded.mpr
    intro p
    refine ⟨∑ k ∈ Finset.range n, (n : ℝ) * p (g k) + 1, by positivity, ?_⟩
    rintro x ⟨c, hcn, rfl⟩
    have h1 : p (∑ k ∈ Finset.range n, c k • g k) ≤ ∑ k ∈ Finset.range n, (n : ℝ) * p (g k) := by
      refine (seminorm_finset_sum_le p _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [map_smul_eq_mul]
      exact mul_le_mul_of_nonneg_right (hcn k) (apply_nonneg p _)
    change p (∑ k ∈ Finset.range n, c k • g k) < _
    linarith
  · -- every bounded set lies in some `B n`
    obtain ⟨V, hV, S', hS', rfl⟩ := (isVonNBounded_iff h S).1 hS
    -- `V` is contained in the range of a finite linear combination map
    have hVm : ∃ m : ℕ, V ≤ LinearMap.range (Fintype.linearCombination ℂ fun k : Fin m => g k) := by
      obtain ⟨t, ht⟩ := (Submodule.fg_iff_finiteDimensional V).2 hV
      have hmem : ∀ y : E, ∃ m : ℕ, y ∈ Submodule.span ℂ (g '' Iio m) := by
        intro y
        have hy : y ∈ Submodule.span ℂ (range g) := hgspan ▸ Submodule.mem_top
        have hU : range g = ⋃ n, g '' Iio n := by
          ext z
          constructor
          · rintro ⟨k, rfl⟩
            exact mem_iUnion.2 ⟨k + 1, ⟨k, Nat.lt_succ_self k, rfl⟩⟩
          · intro hz
            obtain ⟨n, k, -, rfl⟩ := mem_iUnion.1 hz
            exact ⟨k, rfl⟩
        rw [hU, Submodule.span_iUnion] at hy
        exact (Submodule.mem_iSup_of_directed _
          (Monotone.directed_le fun a b hab =>
            Submodule.span_mono (image_mono (Iio_subset_Iio hab)))).1 hy
      choose mf hmf using hmem
      refine ⟨t.sup mf, ?_⟩
      rw [Fintype.range_linearCombination, ← ht, Submodule.span_le]
      intro y hy
      have h1 : y ∈ Submodule.span ℂ (g '' Iio (mf y)) := hmf y
      refine Submodule.span_mono ?_ h1
      rintro _ ⟨k, hk, rfl⟩
      exact ⟨⟨k, lt_of_lt_of_le hk (Finset.le_sup (f := mf) hy)⟩, rfl⟩
    obtain ⟨m, hm⟩ := hVm
    -- a continuous linear choice of coefficients on `V`
    obtain ⟨ρ, hρ⟩ := (Fintype.linearCombination ℂ fun k : Fin m => g k).rangeRestrict
      |>.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict _)
    let R : V →ₗ[ℂ] (Fin m → ℂ) := ρ ∘ₗ Submodule.inclusion hm
    have hR : ∀ v : V, ∑ k : Fin m, R v k • g k = (v : E) := by
      intro v
      have h1 := LinearMap.congr_fun hρ (Submodule.inclusion hm v)
      have h2 := congrArg Subtype.val h1
      simpa [R, Fintype.linearCombination_apply] using h2
    have hRc : Continuous R :=
      linearMap_continuous (submodule_finest h V) (isLocallyConvexTopology_pi m) R
    have hRb : Bornology.IsVonNBounded ℂ (R '' S') := hS'.image ⟨R, hRc⟩
    rw [NormedSpace.isVonNBounded_iff] at hRb
    obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hRb
    obtain ⟨N, hN⟩ := exists_nat_ge (max (m : ℝ) M)
    have hmN : m ≤ N := by exact_mod_cast (le_max_left _ _).trans hN
    refine ⟨N, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨fun k => if hk : k < m then R v ⟨k, hk⟩ else 0, fun k => ?_, ?_⟩
    · by_cases hk : k < m
      · simp only [dif_pos hk]
        exact ((norm_le_pi_norm (R v) ⟨k, hk⟩).trans (hM _ ⟨v, hv, rfl⟩)).trans
          ((le_max_right _ _).trans hN)
      · simp only [dif_neg hk, norm_zero]
        exact Nat.cast_nonneg N
    · rw [← hR v, ← Finset.sum_subset (Finset.range_mono hmN) fun k _ hk => by
        simp only [dif_neg (fun h' : k < m => hk (Finset.mem_range.2 h')), zero_smul],
        ← Fin.sum_univ_eq_sum_range (fun k => (if hk : k < m then R v ⟨k, hk⟩ else 0) • g k) m]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [dif_pos k.2]

/-- For the finest locally convex topology every balanced convex absorbing set is a
`0`-neighbourhood; in particular the (DF) condition holds. -/
theorem df_of_finest [TopologicalSpace E] (h : HasFinestLocallyConvexTopology E)
    (U : ℕ → Set E)
    (hU : ∀ n, U n ∈ nhds (0 : E) ∧ IsClosed (U n) ∧ Balanced ℂ (U n) ∧ Convex ℝ (U n))
    (hb : ∀ S : Set E, Bornology.IsVonNBounded ℂ S → Absorbs ℂ (⋂ n, U n) S) :
    (⋂ n, U n) ∈ nhds (0 : E) := by
  have hall := withSeminorms_all h
  have hadd : IsTopologicalAddGroup E := hall.topologicalAddGroup
  have hsmul : ContinuousSMul ℂ E := hall.continuousSMul
  have hWb : Balanced ℂ (⋂ n, U n) := balanced_iInter fun n => (hU n).2.2.1
  have hWc : Convex ℝ (⋂ n, U n) := convex_iInter fun n => (hU n).2.2.2
  have hWa : Absorbent ℝ (⋂ n, U n) := by
    intro x
    obtain ⟨r, hr⟩ := absorbs_iff_norm.1 (hb {x} (Bornology.isVonNBounded_singleton x))
    refine absorbs_iff_norm.2 ⟨r, fun c hc => ?_⟩
    have hc' : r ≤ ‖(c : ℂ)‖ := by simpa using hc
    obtain ⟨y, hy, hyx⟩ := hr (c : ℂ) hc' (mem_singleton x)
    rw [singleton_subset_iff]
    exact ⟨y, hy, hyx⟩
  have h0 : (0 : E) ∈ ⋂ n, U n := mem_iInter.2 fun n => mem_of_mem_nhds (hU n).1
  let gs : Seminorm ℂ E := gaugeSeminorm hWb hWc hWa
  have hgs : {x : E | gs x < 1} ⊆ ⋂ n, U n := fun x hx =>
    setOfPred_gauge_lt_one_subset_self hWc h0 hWa hx
  exact Filter.mem_of_superset
    ((isOpen_lt (hall.continuous_seminorm gs) continuous_const).mem_nhds (by simp)) hgs

/-- **Proposition C.2.5.1(6)**: the strong dual is nuclear in the countable-dimensional case. -/
theorem strongDual_nuclear_of_countable [TopologicalSpace E]
    (h : HasFinestLocallyConvexTopology E)
    (hc : ∃ s : Set E, s.Countable ∧ Submodule.span ℂ s = ⊤) : IsNuclear (StrongDual ℂ E) :=
  strongDual_nuclear_of_complete_nuclear_DF E (complete_of_finest h) (nuclear_of_countable h hc)
    (exists_fundamental_bounded h hc) (df_of_finest h)


/-- **Proposition C.2.5.1(6)**: the strong dual is a Fréchet space in the countable-dimensional
case. -/
theorem strongDual_isFrechet_of_countable [TopologicalSpace E]
    (h : HasFinestLocallyConvexTopology E)
    (hc : ∃ s : Set E, s.Countable ∧ Submodule.span ℂ s = ⊤) : IsFrechet (StrongDual ℂ E) := by
  have hall := withSeminorms_all h
  have hadd : IsTopologicalAddGroup E := hall.topologicalAddGroup
  have hsmul : ContinuousSMul ℂ E := hall.continuousSMul
  have hHL : IsHLCS (StrongDual ℂ E) := strongDual_isHLCS E (isHLCS_of_finest h)
  have hT2 : T2Space (StrongDual ℂ E) := hHL.2
  have hAG : IsTopologicalAddGroup (StrongDual ℂ E) := inferInstance
  obtain ⟨B, hBb, hBc⟩ := exists_fundamental_bounded h hc
  have hbasis := ContinuousLinearMap.hasBasis_nhds_zero (𝕜₁ := ℂ) (𝕜₂ := ℂ) (σ := RingHom.id ℂ)
    (E := E) (F := ℂ)
  refine ⟨hHL.1, ⟨hT2, fun F hF => ?_⟩, ?_⟩
  · -- completeness
    obtain ⟨hne, hcau⟩ := hF
    have hne' : F.NeBot := hne
    have hUmem : ∀ (S : Set E), Bornology.IsVonNBounded ℂ S → ∀ ε : ℝ, 0 < ε →
        {f : StrongDual ℂ E | ∀ x ∈ S, f x ∈ Metric.ball (0 : ℂ) ε} ∈ 𝓝 (0 : StrongDual ℂ E) :=
      fun S hS ε hε => hbasis.mem_of_mem (i := (S, Metric.ball (0 : ℂ) ε))
        ⟨hS, Metric.ball_mem_nhds 0 hε⟩
    -- pointwise limits
    have hpt : ∀ x : E, ∃ l : ℂ, Filter.Tendsto (fun f : StrongDual ℂ E => f x) F (𝓝 l) := by
      intro x
      have hC : Cauchy (Filter.map (fun f : StrongDual ℂ E => f x) F) := by
        rw [Metric.cauchy_iff]
        refine ⟨inferInstance, fun ε hε => ?_⟩
        obtain ⟨A, hA, hAd⟩ :=
          hcau _ (hUmem {x} (Bornology.isVonNBounded_singleton x) ε hε)
        refine ⟨_, Filter.image_mem_map hA, ?_⟩
        rintro _ ⟨f, hf, rfl⟩ _ ⟨f', hf', rfl⟩
        have h1 := hAd f hf f' hf' x (mem_singleton x)
        rw [mem_ball_zero_iff, sub_apply] at h1
        rw [dist_eq_norm]
        exact h1
      obtain ⟨l, hl⟩ := CompleteSpace.complete hC
      exact ⟨l, hl⟩
    choose L₀ hL₀ using hpt
    let Llin : E →ₗ[ℂ] ℂ :=
      { toFun := L₀
        map_add' := fun x y => by
          have h1 : Filter.Tendsto (fun f : StrongDual ℂ E => f (x + y)) F (𝓝 (L₀ x + L₀ y)) := by
            have := (hL₀ x).add (hL₀ y)
            refine this.congr fun f => ?_
            rw [map_add]
          exact tendsto_nhds_unique (hL₀ (x + y)) h1
        map_smul' := fun c x => by
          have h1 : Filter.Tendsto (fun f : StrongDual ℂ E => f (c • x)) F (𝓝 (c • L₀ x)) := by
            have := (hL₀ x).const_smul c
            refine this.congr fun f => ?_
            rw [map_smul]
          exact tendsto_nhds_unique (hL₀ (c • x)) h1 }
    let L : StrongDual ℂ E := ⟨Llin, linearFunctional_continuous h Llin⟩
    have hLapp : ∀ x, L x = L₀ x := fun _ => rfl
    refine ⟨L, fun N hN => ?_⟩
    -- a basic neighbourhood of `L`
    have hpre : (fun g : StrongDual ℂ E => g + L) ⁻¹' N ∈ 𝓝 (0 : StrongDual ℂ E) := by
      have hcont : ContinuousAt (fun g : StrongDual ℂ E => g + L) 0 :=
        (continuous_id.add continuous_const).continuousAt
      apply hcont.preimage_mem_nhds
      simpa using hN
    obtain ⟨⟨S, V⟩, ⟨hS, hV⟩, hsub⟩ := hbasis.mem_iff.1 hpre
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hV
    obtain ⟨A, hA, hAd⟩ := hcau _ (hUmem S hS (ε / 2) (by positivity))
    refine Filter.mem_of_superset hA fun f hf => ?_
    have hmem : (f - L) ∈ {g : StrongDual ℂ E | ∀ x ∈ S, g x ∈ V} := by
      intro x hx
      apply hball
      rw [mem_ball_zero_iff, sub_apply, hLapp]
      have hle : ‖f x - L₀ x‖ ≤ ε / 2 := by
        have hlim : Filter.Tendsto (fun f' : StrongDual ℂ E => ‖f x - f' x‖) F
            (𝓝 ‖f x - L₀ x‖) := ((hL₀ x).const_sub (f x)).norm
        refine le_of_tendsto hlim (Filter.mem_of_superset hA fun f' hf' => ?_)
        have h1 := hAd f hf f' hf' x hx
        rw [mem_ball_zero_iff, sub_apply] at h1
        exact h1.le
      linarith
    have h2 := hsub hmem
    have h3 : (f - L) + L = f := sub_add_cancel f L
    change (f - L) + L ∈ N at h2
    rwa [h3] at h2
  · -- metrizability: a countable neighbourhood basis of `0`
    have hcb : (𝓝 (0 : StrongDual ℂ E)).HasBasis (fun _ : ℕ × ℕ => True)
        (fun nm => {f : StrongDual ℂ E | ∀ x ∈ B nm.1,
          f x ∈ Metric.ball (0 : ℂ) (1 / ((nm.2 : ℝ) + 1))}) := by
      refine hbasis.to_hasBasis (fun SV hSV => ?_) (fun nm _ => ?_)
      · obtain ⟨n, hn⟩ := hBc SV.1 hSV.1
        obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hSV.2
        obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
        refine ⟨(n, m), trivial, fun f hf x hx => hball ?_⟩
        exact Metric.ball_subset_ball hm.le (hf x (hn hx))
      · exact ⟨(B nm.1, Metric.ball (0 : ℂ) (1 / ((nm.2 : ℝ) + 1))),
          ⟨hBb nm.1, Metric.ball_mem_nhds 0 (by positivity)⟩, subset_rfl⟩
    have hcg : (𝓝 (0 : StrongDual ℂ E)).IsCountablyGenerated := hcb.isCountablyGenerated
    have hug : (uniformity (StrongDual ℂ E)).IsCountablyGenerated :=
      IsUniformAddGroup.uniformity_countably_generated
    exact UniformSpace.metrizableSpace

end FinestLC

theorem solution (E : Type u) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (h : HasFinestLocallyConvexTopology E)
    (hc : ∃ s : Set E, s.Countable ∧ Submodule.span ℂ s = ⊤) :
    IsStrictLFOfNuclearFrechet E ∧ IsCompleteTVS E ∧ IsNuclear E ∧ IsMontel E ∧
      IsFrechet (StrongDual ℂ E) ∧ IsNuclear (StrongDual ℂ E) := by
  exact ⟨FinestLC.strictLF_of_countable h hc, FinestLC.complete_of_finest h,
    FinestLC.nuclear_of_countable h hc, FinestLC.montel_of_countable h hc,
    FinestLC.strongDual_isFrechet_of_countable h hc,
    FinestLC.strongDual_nuclear_of_countable h hc⟩
