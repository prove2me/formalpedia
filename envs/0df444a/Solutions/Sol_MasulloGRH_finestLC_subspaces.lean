-- Prove2me | solution 1 for MasulloGRH.finestLC_subspaces
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:44:35.620191+00:00
-- url     : https://prove2.me/submissions/0adb3cba-2b64-4097-8e63-4fc289a64cd7

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

end FinestLC

theorem solution (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (h : HasFinestLocallyConvexTopology E) (V : Submodule ℂ E) :
    IsClosed (V : Set E) ∧ V.ClosedComplemented ∧
      HasFinestLocallyConvexTopology V ∧ HasFinestLocallyConvexTopology (E ⧸ V) := by
  exact ⟨FinestLC.submodule_isClosed h V, FinestLC.submodule_closedComplemented h V,
    FinestLC.submodule_finest h V, FinestLC.quotient_finest h V⟩
