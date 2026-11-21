-- Prove2me | solution 2 for MasulloGRH.strictLF_closed_subspace_bornological_of_limit_subspace
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:01:23.840078+00:00
-- url     : https://prove2.me/submissions/5bd4d7a0-7f6f-49e3-8219-6ccc05b811cf

import Theorems.Thm_MasulloGRH_bounded_in_strict_frechet_stages

set_option autoImplicit false

open MasulloGRH Filter Topology Set Bornology
open scoped Pointwise

namespace BornLimitAux

/-- On a first-countable topological vector space, a seminorm that is bounded on bounded sets is
continuous. -/
theorem seminorm_continuous_of_bounded {F : Type*} [AddCommGroup F] [Module ℂ F]
    [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [FirstCountableTopology F]
    (q : Seminorm ℂ F) (hq : ∀ B : Set F, IsVonNBounded ℂ B → BddAbove (q '' B)) :
    Continuous q := by
  refine Seminorm.continuous' (r := 1) ?_
  by_contra hball
  obtain ⟨b, hb⟩ := (𝓝 (0 : F)).exists_antitone_basis
  -- in each shrunken basic set there is a point of `q`-size greater than one
  have hpt : ∀ n : ℕ, ∃ x : F, x ∈ (((n : ℂ) + 1)⁻¹) • b n ∧ 1 < q x := by
    intro n
    have hc : ((n : ℂ) + 1)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast Nat.succ_ne_zero n)
    have hW : (((n : ℂ) + 1)⁻¹) • b n ∈ 𝓝 (0 : F) :=
      (set_smul_mem_nhds_zero_iff hc).2 (hb.mem n)
    by_contra! h
    exact hball (mem_of_superset hW fun x hx => by
      rw [Seminorm.mem_closedBall_zero]; exact h x hx)
  choose x hx hqx using hpt
  -- rescaling gives a null, hence bounded, sequence on which `q` is unbounded
  let y : ℕ → F := fun n => ((n : ℂ) + 1) • x n
  have hyb : ∀ n, y n ∈ b n := by
    intro n
    have hc : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    obtain ⟨w, hw, hwx⟩ := hx n
    show ((n : ℂ) + 1) • x n ∈ b n
    rw [← hwx, smul_smul, mul_inv_cancel₀ hc, one_smul]
    exact hw
  have hyt : Tendsto y atTop (𝓝 0) := hb.tendsto hyb
  obtain ⟨C, hC⟩ := hq _ (hyt.isVonNBounded_range ℂ)
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have h1 : q (y n) ≤ C := hC ⟨y n, mem_range_self n, rfl⟩
  have h2 : q (y n) = ((n : ℝ) + 1) * q (x n) := by
    show q (((n : ℂ) + 1) • x n) = _
    rw [map_smul_eq_mul]
    congr 1
    rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  have h3 : ((n : ℝ) + 1) * 1 < ((n : ℝ) + 1) * q (x n) :=
    mul_lt_mul_of_pos_left (hqx n) (by positivity)
  linarith

theorem continuous_into_seminorms {A F I : Type*} [AddCommGroup A] [Module ℂ A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [AddCommGroup F] [Module ℂ F]
    {τ : TopologicalSpace F} {q : SeminormFamily ℂ F I}
    (hq : WithSeminorms (topology := τ) q) (f : A →ₗ[ℂ] F)
    (h : ∀ i, Continuous ((q i).comp f)) : @Continuous A F _ τ f := by
  let := τ
  exact hq.continuous_of_continuous_comp f h

end BornLimitAux

open BornLimitAux in
theorem solution
    (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hlim : (instTopologicalSpaceSubtype : TopologicalSpace V) =
        sInf {t | IsLocallyConvexTopology V t ∧
          ∀ n, @Continuous ↥(V ⊓ X n) V _ t (Submodule.inclusion inf_le_left)}) :
    IsBornological V := by
  intro p hp
  obtain ⟨hHLCS, -⟩ := bounded_in_strict_frechet_stages E X hmono hexh hX htop
  obtain ⟨⟨ι, _, P, hP⟩, _⟩ := hHLCS
  have : IsTopologicalAddGroup E := hP.topologicalAddGroup
  have : ContinuousSMul ℂ E := hP.continuousSMul
  -- each stage restriction of `p` is continuous (metrizable stages are bornological)
  have hpcomp : ∀ n, Continuous (p.comp (Submodule.inclusion (inf_le_left : V ⊓ X n ≤ V))) := by
    intro n
    have hfc : FirstCountableTopology ↥(V ⊓ X n) := by
      have : TopologicalSpace.MetrizableSpace ↥(X n) := (hX n).2.2
      have hind : Topology.IsInducing (Submodule.inclusion (inf_le_right : V ⊓ X n ≤ X n)) :=
        Topology.IsInducing.of_comp (continuous_subtype_val.subtype_mk _) continuous_subtype_val
          Topology.IsInducing.subtypeVal
      exact hind.firstCountableTopology
    have hι : Continuous (Submodule.inclusion (inf_le_left : V ⊓ X n ≤ V)) :=
      continuous_subtype_val.subtype_mk _
    refine seminorm_continuous_of_bounded _ fun B hB => ?_
    have hB' : IsVonNBounded ℂ ((Submodule.inclusion (inf_le_left : V ⊓ X n ≤ V)) '' B) :=
      hB.image (⟨Submodule.inclusion inf_le_left, hι⟩ : ↥(V ⊓ X n) →L[ℂ] V)
    obtain ⟨C, hC⟩ := hp _ hB'
    refine ⟨C, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact hC ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  -- the topology on `V` defined by `p` alone
  let fam : SeminormFamily ℂ V PUnit := fun _ => p
  let t₀ : TopologicalSpace V := fam.moduleFilterBasis.topology
  have hw : WithSeminorms (topology := t₀) fam := ⟨rfl⟩
  have hlc : IsLocallyConvexTopology V t₀ := ⟨PUnit, inferInstance, fam, hw⟩
  -- each stage inclusion is continuous into `(V, t₀)`
  have hcont : ∀ n, @Continuous ↥(V ⊓ X n) V _ t₀ (Submodule.inclusion inf_le_left) :=
    fun n => continuous_into_seminorms hw _ fun _ => hpcomp n
  have hle : (instTopologicalSpaceSubtype : TopologicalSpace V) ≤ t₀ := by
    rw [hlim]
    exact sInf_le ⟨hlc, hcont⟩
  have hpc : @Continuous V ℝ t₀ _ p := hw.continuous_seminorm PUnit.unit
  exact continuous_le_dom hle hpc
