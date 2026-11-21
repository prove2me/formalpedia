-- Prove2me | solution 1 for MasulloGRH.projTensor_isHLCS
-- status  : ACCEPTED   (prove)
-- author  : @nlehmann
-- created : 2026-11-20T23:02:03.652117+00:00
-- url     : https://prove2.me/submissions/838ef21c-3bcd-4c55-9229-49f917706131

import Definitions.Def_MasulloGRH_LocallyConvex

open Topology Filter

universe u

/-- The indiscrete topology is the seminorm topology of the zero seminorm. -/
theorem MasulloGRH_zero_seminorm_top (E : Type u) [AddCommGroup E] [Module ℂ E] :
    @WithSeminorms ℂ E PUnit.{u+1} _ _ _ (fun _ => 0) ⊤ := by
  letI : TopologicalSpace E := ⊤
  have : IsTopologicalAddGroup E :=
    { continuous_add := continuous_top, continuous_neg := continuous_top }
  rw [SeminormFamily.withSeminorms_iff_topologicalSpace_eq_iInf]
  simp only [ciInf_const]
  symm
  rw [eq_top_iff]
  intro s hs
  rw [TopologicalSpace.isOpen_top_iff]
  rcases s.eq_empty_or_nonempty with h | ⟨x, hx⟩
  · exact Or.inl h
  · right
    letI := (0 : Seminorm ℂ E).toSeminormedAddCommGroup
    rw [Metric.isOpen_iff] at hs
    obtain ⟨ε, hε, hball⟩ := hs x hx
    refine Set.eq_univ_of_forall fun y => hball ?_
    rw [Metric.mem_ball, dist_eq_norm]
    change (0 : Seminorm ℂ E) (y - x) < ε
    simpa using hε

/-- An infimum of locally convex topologies is locally convex. -/
theorem MasulloGRH_lc_sInf {E : Type u} [AddCommGroup E] [Module ℂ E]
    (S : Set (TopologicalSpace E))
    (hS : ∀ t ∈ S, MasulloGRH.IsLocallyConvexTopology E t) :
    MasulloGRH.IsLocallyConvexTopology E (sInf S) := by
  have hS' : ∀ t ∈ insert (⊤ : TopologicalSpace E) S, MasulloGRH.IsLocallyConvexTopology E t := by
    rintro t (rfl | ht)
    · exact ⟨PUnit, inferInstance, fun _ => 0, MasulloGRH_zero_seminorm_top E⟩
    · exact hS t ht
  have heq : sInf S = sInf (insert (⊤ : TopologicalSpace E) S) := by
    rw [sInf_insert, top_inf_eq]
  rw [heq]
  set T := insert (⊤ : TopologicalSpace E) S
  let κ : T → Type u := fun t => (hS' t.1 t.2).choose
  have hκ : ∀ t : T, Nonempty (κ t) := fun t => (hS' t.1 t.2).choose_spec.choose
  let p : (t : T) → SeminormFamily ℂ E (κ t) :=
    fun t => (hS' t.1 t.2).choose_spec.choose_spec.choose
  have hp : ∀ t : T, @WithSeminorms ℂ E (κ t) _ _ _ (p t) t.1 :=
    fun t => (hS' t.1 t.2).choose_spec.choose_spec.choose_spec
  have htop : sInf T = ⨅ t : T, t.1 := sInf_eq_iInf' T
  rw [htop]
  refine ⟨(t : T) × κ t, ?_, SeminormFamily.sigma p, withSeminorms_iInf hp⟩
  obtain ⟨t0⟩ : Nonempty T := ⟨⟨⊤, Set.mem_insert _ _⟩⟩
  obtain ⟨k⟩ := hκ t0
  exact ⟨⟨t0, k⟩⟩


open TensorProduct

/-- `ℂ` with its seminorm family indexed by `PUnit`. -/
theorem MasulloGRH_complex_withSeminorms :
    WithSeminorms (fun _ : PUnit.{u+1} => normSeminorm ℂ ℂ) := by
  have h1 := (SeminormFamily.withSeminorms_iff_topologicalSpace_eq_iInf _).1 (norm_withSeminorms ℂ ℂ)
  rw [SeminormFamily.withSeminorms_iff_topologicalSpace_eq_iInf]
  simpa [ciInf_const] using h1

/-- Hahn–Banach: a Hausdorff locally convex space has a separating dual. -/
theorem MasulloGRH_sepDual (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (h : MasulloGRH.IsHLCS E) : SeparatingDual ℂ E := by
  obtain ⟨⟨ι, _, p, hp⟩, hT2⟩ := h
  haveI := hp.topologicalAddGroup
  haveI := hp.continuousSMul
  haveI : LocallyConvexSpace ℝ E := hp.toLocallyConvexSpace
  refine ⟨fun x hx => ?_⟩
  obtain ⟨f, hf⟩ := RCLike.geometric_hahn_banach_point_point (𝕜 := ℂ) hx
  exact ⟨f, fun h0 => by simp [h0] at hf⟩

theorem MasulloGRH_tensorFunctional_sum {E F : Type u} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    (f : StrongDual ℂ E) (g : StrongDual ℂ F) {ι : Type*} (s : Finset ι) (m : ι → E) (n : ι → F) :
    MasulloGRH.tensorFunctional E F (f, g) (∑ i ∈ s, m i ⊗ₜ[ℂ] n i) = ∑ i ∈ s, f (m i) * g (n i) := by
  simp [MasulloGRH.tensorFunctional, map_sum]

/-- Products of continuous functionals separate the points of `E ⊗ F`. -/
theorem MasulloGRH_tensor_sep {E F : Type u} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [SeparatingDual ℂ E] [SeparatingDual ℂ F] (u : E ⊗[ℂ] F)
    (hu : ∀ (f : StrongDual ℂ E) (g : StrongDual ℂ F), MasulloGRH.tensorFunctional E F (f, g) u = 0) :
    u = 0 := by
  classical
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset u
  rw [← Finset.sum_coe_sort]
  set m : S → E := fun i => i.1.1
  set n : S → F := fun i => i.1.2
  change ∑ i : S, m i ⊗ₜ[ℂ] n i = 0
  set W : Submodule ℂ F := Submodule.span ℂ (Set.range n)
  haveI : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (Set.finite_range n)
  let b := Module.finBasis ℂ W
  let nW : S → W := fun i => ⟨n i, Submodule.subset_span ⟨i, rfl⟩⟩
  let a : S → Fin (Module.finrank ℂ W) → ℂ := fun i j => b.repr (nW i) j
  apply TensorProduct.sum_tmul_eq_zero_of_vanishesTrivially
  refine TensorProduct.VanishesTrivially.of_fintype a (fun j => (b j : F)) ?_ ?_
  · intro i
    have h2 := congrArg Subtype.val (b.sum_repr (nW i))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    exact h2.symm
  · intro j
    by_contra hz
    obtain ⟨f, hf⟩ := SeparatingDual.exists_ne_zero (R := ℂ) hz
    apply hf
    -- the vector `∑ f(m_i) n_i` vanishes
    have hv : ∑ i, f (m i) • nW i = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero, nW]
      by_contra hv
      obtain ⟨g, hg⟩ := SeparatingDual.exists_ne_zero (R := ℂ) hv
      apply hg
      have := hu f g
      rw [← Finset.sum_coe_sort] at this
      rw [MasulloGRH_tensorFunctional_sum] at this
      simpa [map_sum, smul_eq_mul] using this
    have := congrArg (fun w => b.repr w j) hv
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at this
    simp only [map_sum, map_smul, smul_eq_mul, a]
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- Each `f ⊗ g` is continuous for the projective topology. -/
theorem MasulloGRH_tensorFunctional_continuous {E F : Type u} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    (f : StrongDual ℂ E) (g : StrongDual ℂ F) :
    @Continuous _ _ (MasulloGRH.projTensorTopology E F) _
      (MasulloGRH.tensorFunctional E F (f, g)) := by
  let Λ : E ⊗[ℂ] F →ₗ[ℂ] ℂ :=
    (TensorProduct.lid ℂ ℂ).toLinearMap ∘ₗ TensorProduct.map (f : E →ₗ[ℂ] ℂ) (g : F →ₗ[ℂ] ℂ)
  have hΛ : MasulloGRH.tensorFunctional E F (f, g) = Λ := rfl
  rw [hΛ, continuous_iff_le_induced]
  unfold MasulloGRH.projTensorTopology
  apply sInf_le
  refine ⟨⟨PUnit, inferInstance, fun _ => (normSeminorm ℂ ℂ).comp Λ, ?_⟩, ?_⟩
  · exact Λ.withSeminorms_induced MasulloGRH_complex_withSeminorms
  · rw [continuous_induced_rng]
    have : (Λ ∘ fun q : E × F => q.1 ⊗ₜ[ℂ] q.2) = fun q => f q.1 * g q.2 := by
      funext q; simp [Λ]
    rw [this]
    exact (f.continuous.comp continuous_fst).mul (g.continuous.comp continuous_snd)

open MasulloGRH

theorem solution (E F : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] (hE : IsHLCS E) (hF : IsHLCS F) :
    @IsHLCS (E ⊗[ℂ] F) _ _ (projTensorTopology E F) := by
  haveI := MasulloGRH_sepDual E hE
  haveI := MasulloGRH_sepDual F hF
  letI : TopologicalSpace (E ⊗[ℂ] F) := projTensorTopology E F
  refine ⟨?_, ?_⟩
  · exact MasulloGRH_lc_sInf _ (fun t ht => ht.1)
  · rw [t2Space_iff]
    intro u v huv
    have hne : u - v ≠ 0 := sub_ne_zero.2 huv
    by_contra hcon
    apply hne
    apply MasulloGRH_tensor_sep
    intro f g
    by_contra hfg
    apply hcon
    have hc := MasulloGRH_tensorFunctional_continuous (E := E) (F := F) f g
    have hneq : tensorFunctional E F (f, g) u ≠ tensorFunctional E F (f, g) v := by
      intro h; apply hfg
      have : tensorFunctional E F (f, g) (u - v) =
          tensorFunctional E F (f, g) u - tensorFunctional E F (f, g) v := by
        simp [tensorFunctional, map_sub]
      rw [this, h, sub_self]
    obtain ⟨U, V, hU, hV, hu, hv, hUV⟩ := t2_separation hneq
    exact ⟨_, _, hU.preimage hc, hV.preimage hc, hu, hv, hUV.preimage _⟩
