-- Prove2me | solution 1 for MasulloGRH.isAbsoluteBasis_iff_summable_of_frechet_or_strictLF
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T17:54:32.942668+00:00
-- url     : https://prove2.me/submissions/d71437e4-8c3d-4d4c-a6f0-5c489c5b1487

import Definitions.Def_MasulloGRH_SchauderBases

open Filter Topology

set_option autoImplicit false

namespace Sol_MasulloGRH_isAbsoluteBasis_iff_summable_of_frechet_or_strictLF

open MasulloGRH

/-- A topological vector space that is complete in the sense of `IsCompleteTVS` and whose topology
is first countable at `0` is a Baire space: its additive uniformity is countably generated and
complete, so the space is completely pseudometrizable. -/
theorem baireSpace_of_isCompleteTVS (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] (hc : IsCompleteTVS E)
    [(𝓝 (0 : E)).IsCountablyGenerated] : BaireSpace E := by
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have : (uniformity E).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : CompleteSpace E := by
    refine ⟨fun {f} hf => ?_⟩
    refine hc.2 f ⟨hf.1, fun U hU => ?_⟩
    have hmem : {p : E × E | p.2 - p.1 ∈ U} ∈ uniformity E := by
      rw [uniformity_eq_comap_nhds_zero E]
      exact Filter.preimage_mem_comap hU
    obtain ⟨A, hA, hAU⟩ := Filter.mem_prod_same_iff.1 (hf.2 hmem)
    refine ⟨A, hA, fun x hx y hy => ?_⟩
    have h : ((y, x) : E × E) ∈ {p : E × E | p.2 - p.1 ∈ U} := hAU (Set.mk_mem_prod hy hx)
    exact h
  infer_instance

/-- A Fréchet space is barrelled (via the Baire category theorem). -/
theorem barrelledSpace_of_isFrechet (F : Type*) [AddCommGroup F] [Module ℂ F]
    [TopologicalSpace F] (hF : IsFrechet F) : BarrelledSpace ℂ F := by
  obtain ⟨⟨ι, _, p, hp⟩, hc, hm⟩ := hF
  have : IsTopologicalAddGroup F := hp.topologicalAddGroup
  have : ContinuousSMul ℂ F := hp.continuousSMul
  have : BaireSpace F := baireSpace_of_isCompleteTVS F hc
  infer_instance

/-- A strict inductive limit of a sequence of Fréchet spaces is barrelled: a lower semicontinuous
seminorm restricts to a lower semicontinuous, hence continuous, seminorm on every step, so the
locally convex topology it defines makes all inclusions continuous and is therefore coarser than
the inductive limit topology. -/
theorem barrelledSpace_of_strictLF (E : Type*) [AddCommGroup E] [Module ℂ E]
    [τ : TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hX : ∀ n, IsFrechet (X n))
    (htop : τ =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val}) :
    BarrelledSpace ℂ E := by
  refine ⟨fun p hp => ?_⟩
  have hcont : ∀ n, Continuous ((p.comp (X n).subtype : Seminorm ℂ (X n)) : X n → ℝ) := by
    intro n
    have : BarrelledSpace ℂ (X n) := barrelledSpace_of_isFrechet _ (hX n)
    exact (p.comp (X n).subtype).continuous_of_lowerSemicontinuous
      (hp.comp continuous_subtype_val)
  have hXtg : ∀ n, IsTopologicalAddGroup (X n) := by
    intro n
    obtain ⟨⟨ι, _, r, hr⟩, _, _⟩ := hX n
    exact hr.topologicalAddGroup
  let q : SeminormFamily ℂ E PUnit := fun _ => p
  have hq : @WithSeminorms ℂ E PUnit _ _ _ q q.moduleFilterBasis.topology :=
    @WithSeminorms.mk ℂ E PUnit _ _ _ q q.moduleFilterBasis.topology rfl
  have ht' : q.moduleFilterBasis.topology ∈
      {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val} := by
    refine ⟨⟨PUnit, inferInstance, q, hq⟩, fun n => ?_⟩
    exact @WithSeminorms.continuous_of_continuous_comp ℂ ℂ (X n) E PUnit _ _ _ _ _ _
      (RingHom.id ℂ) _ q _ (hXtg n) q.moduleFilterBasis.topology hq (X n).subtype
      (fun _ => hcont n)
  have hle : τ ≤ q.moduleFilterBasis.topology := htop ▸ sInf_le ht'
  have hpc : @Continuous E ℝ q.moduleFilterBasis.topology _ p :=
    @WithSeminorms.continuous_seminorm ℂ E PUnit _ _ _ q.moduleFilterBasis.topology q hq PUnit.unit
  exact continuous_le_dom hle hpc

/-- On a barrelled space, McArthur's condition implies Jarchow's: the finite partial sums
`u ↦ ∑_{m ∈ s} q(f_m(u) x_m)` form a pointwise bounded family of continuous seminorms, whose
supremum is continuous. -/
theorem isAbsoluteBasis_of_barrelled (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [BarrelledSpace ℂ E] (x : ℕ → E) (f : ℕ → StrongDual ℂ E)
    (hsum : ∀ q : Seminorm ℂ E, Continuous q → ∀ u : E, Summable (fun m => q (f m u • x m))) :
    IsAbsoluteBasis x f := by
  intro q hq
  let L (m : ℕ) : E →ₗ[ℂ] E := (f m : E →ₗ[ℂ] ℂ).smulRight (x m)
  let p (s : Finset ℕ) : Seminorm ℂ E := ∑ m ∈ s, q.comp (L m)
  have hp_apply (s : Finset ℕ) (u : E) : p s u = ∑ m ∈ s, q (f m u • x m) := by
    change FunLike.coeAddMonoidHom (Seminorm ℂ E) E ℝ (∑ m ∈ s, q.comp (L m)) u = _
    rw [map_sum, Finset.sum_apply]
    rfl
  have hL (m : ℕ) : Continuous (fun u : E => q (f m u • x m)) := by
    have h : (fun u : E => q (f m u • x m)) = fun u => ‖f m u‖ * q (x m) := by
      funext u
      exact map_smul_eq_mul q (f m u) (x m)
    rw [h]
    exact ((f m).continuous.norm).mul continuous_const
  have hp (s : Finset ℕ) : Continuous (p s) := by
    have h : (p s : E → ℝ) = fun u => ∑ m ∈ s, q (f m u • x m) := funext (hp_apply s)
    rw [h]
    exact continuous_finsetSum s fun m _ => hL m
  have hbdd : BddAbove (Set.range p) := Seminorm.bddAbove_range_iff.mpr fun u =>
    ⟨∑' m, q (f m u • x m), Set.forall_mem_range.mpr fun s => by
      rw [hp_apply]
      exact (hsum q hq u).sum_le_tsum s fun m _ => apply_nonneg q _⟩
  refine ⟨⨆ s, p s, ?_, fun u => ⟨hsum q hq u, (hsum q hq u).tsum_le_of_sum_le ?_⟩⟩
  · rw [Seminorm.coe_iSup_eq hbdd]
    exact Seminorm.continuous_iSup p hp hbdd
  · intro s
    rw [← hp_apply]
    exact (show p s ≤ ⨆ t, p t from le_ciSup hbdd s) u

end Sol_MasulloGRH_isAbsoluteBasis_iff_summable_of_frechet_or_strictLF

open MasulloGRH Sol_MasulloGRH_isAbsoluteBasis_iff_summable_of_frechet_or_strictLF

theorem solution
    (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : IsHLCS E) (x : ℕ → E) (f : ℕ → StrongDual ℂ E) (hx : IsSchauderBasis x f)
    (hspace : IsFrechet E ∨ IsStrictLFOfNuclearFrechet E) :
    IsAbsoluteBasis x f ↔
      ∀ q : Seminorm ℂ E, Continuous q → ∀ u : E, Summable (fun m => q (f m u • x m)) := by
  constructor
  · intro h q hq u
    obtain ⟨_, _, hbound⟩ := h q hq
    exact (hbound u).1
  · intro hsum
    have : BarrelledSpace ℂ E := by
      rcases hspace with hF | ⟨X, _, _, hX, htop⟩
      · exact barrelledSpace_of_isFrechet E hF
      · exact barrelledSpace_of_strictLF E X (fun n => (hX n).1) htop
    exact isAbsoluteBasis_of_barrelled E x f hsum
