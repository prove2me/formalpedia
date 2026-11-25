-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.exists_isMinimal_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:13:45.857439+00:00
-- url     : https://prove2.me/submissions/ac6f065d-9004-4224-9d01-e2bf6094e866

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations
import Definitions.Def_GroundTheory_AutomorphicForms_DiscreteSpectrumAbstract
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_isSymmetric_absSqOp
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_absSqOp_apply_ne_zero
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsInvariant_absSqOp_mem
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_exists_integrated_ne_zero
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsInvariant_inf
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_isClosed_cyclicSubspace
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_isInvariant_cyclicSubspace
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_mem_cyclicSubspace_self
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_cyclicSubspace_le
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_trans
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsInvariant_orthogonal
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_directSum_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.directSum_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.UnitaryRep
open MeasureTheory Filter Topology Module End
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap
noncomputable section
variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (π : UnitaryRep G H) (μ : Measure G)
variable {π μ}
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    (hcpt : ∀ f : CompactlySupportedContinuousMap G ℂ,
      IsCompactOperator (π.integrated μ (ccToL1 μ f)))
    {W : Submodule ℂ H} (hWcl : IsClosed (W : Set H)) (hWinv : π.IsInvariant W) (hW : W ≠ ⊥) :
    ∃ U, π.IsMinimal U ∧ U ≤ W := by
  classical
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  obtain ⟨f, hf⟩ := exists_integrated_ne_zero π μ hw0
  set A := π.absSqOp μ (ccToL1 μ f) with hA
  have hAc : IsCompactOperator A := IsCompactOperator.absSqOp π μ (hcpt f)
  have hAs : (A : H →ₗ[ℂ] H).IsSymmetric := π.isSymmetric_absSqOp μ _
  have hAinv : ∀ {V : Submodule ℂ H}, IsClosed (V : Set H) → π.IsInvariant V →
      ∀ v ∈ V, A v ∈ V := fun hcl hV v hv => hV.absSqOp_mem hcl _ hv

  obtain ⟨lam, hlam0, u, huW, hu0, hu⟩ :
      ∃ lam : ℂ, lam ≠ 0 ∧ ∃ u ∈ W, u ≠ 0 ∧ A u = lam • u := by
    have : CompleteSpace W := hWcl.completeSpace_coe
    let S : W →L[ℂ] W := A.restrict (hAinv hWcl hWinv)
    have hSc : IsCompactOperator S := hAc.restrict' (hAinv hWcl hWinv)
    have hSs : (S : W →ₗ[ℂ] W).IsSymmetric := hAs.restrict_invariant (hAinv hWcl hWinv)
    have hS0 : S ≠ 0 := by
      intro h
      apply absSqOp_apply_ne_zero π μ hf
      have := congrArg (fun g : W →L[ℂ] W => ((g ⟨w, hwW⟩ : W) : H)) h
      simpa [S] using this
    obtain ⟨lam, hlam, hlam0⟩ : ∃ lam, HasEigenvalue (S : W →ₗ[ℂ] W) lam ∧ lam ≠ 0 := by
      by_contra h'
      push Not at h'
      exact hS0 ((ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero hSc hSs).1 h')
    obtain ⟨u, hu1, hu2⟩ := hlam.exists_hasEigenvector
    refine ⟨lam, hlam0, u, u.2, fun h => hu2 (Subtype.ext h), ?_⟩
    have := congrArg Subtype.val (mem_eigenspace_iff.1 hu1)
    simpa [S] using this
  set E := eigenspace (A : H →ₗ[ℂ] H) lam with hE
  have hEfin : FiniteDimensional ℂ E := ContinuousLinearMap.finite_dimensional_eigenspace hAc lam hlam0
  have hmemE : ∀ x, x ∈ E ↔ A x = lam • x := fun x => by
    rw [hE, mem_eigenspace_iff, ContinuousLinearMap.coe_coe]

  let P : ℕ → Prop := fun n => ∃ V : Submodule ℂ H, IsClosed (V : Set H) ∧ π.IsInvariant V ∧
    V ≤ W ∧ E ⊓ V ≠ ⊥ ∧ finrank ℂ ↥(E ⊓ V) = n
  have hP : ∃ n, P n := ⟨_, W, hWcl, hWinv, le_rfl, fun h => by
    have : u ∈ E ⊓ W := ⟨(hmemE u).2 hu, huW⟩
    rw [h, Submodule.mem_bot] at this
    exact hu0 this, rfl⟩
  obtain ⟨V₀, hV₀cl, hV₀inv, hV₀W, hV₀ne, hV₀n⟩ := Nat.find_spec hP
  have hmin : ∀ V : Submodule ℂ H, IsClosed (V : Set H) → π.IsInvariant V → V ≤ V₀ →
      E ⊓ V ≠ ⊥ → E ⊓ V = E ⊓ V₀ := by
    intro V hVcl hVinv hVV₀ hVne
    have hle : E ⊓ V ≤ E ⊓ V₀ := inf_le_inf_left E hVV₀
    have : FiniteDimensional ℂ ↥(E ⊓ V₀) := Submodule.finiteDimensional_of_le inf_le_left
    refine Submodule.eq_of_le_of_finrank_le hle ?_
    rw [hV₀n]
    exact Nat.find_min' hP ⟨V, hVcl, hVinv, hVV₀.trans hV₀W, hVne, rfl⟩
  obtain ⟨v, hvEV, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV₀ne
  set U := π.cyclicSubspace v with hU
  have hUcl : IsClosed (U : Set H) := π.isClosed_cyclicSubspace v
  have hUinv : π.IsInvariant U := π.isInvariant_cyclicSubspace v
  have hvU : v ∈ U := π.mem_cyclicSubspace_self v
  have hUV₀ : U ≤ V₀ := π.cyclicSubspace_le hV₀cl hV₀inv hvEV.2
  refine ⟨U, ⟨hUcl, hUinv, fun h => hv0 (by rw [h] at hvU; exact hvU), ?_⟩, hUV₀.trans hV₀W⟩
  intro U' hU'cl hU'inv hU'U
  have : CompleteSpace U' := hU'cl.completeSpace_coe
  set p := U'.starProjection v with hp
  set q := v - p with hq
  have hpU' : p ∈ U' := U'.starProjection_apply_mem v
  have hqU' : q ∈ U'ᗮ := U'.sub_starProjection_mem_orthogonal v
  have hqU : q ∈ U := sub_mem hvU (hU'U hpU')

  have h1 : A p - lam • p ∈ U' :=
    sub_mem (hAinv hU'cl hU'inv p hpU') (Submodule.smul_mem _ _ hpU')
  have h2 : A q - lam • q ∈ U'ᗮ :=
    sub_mem (hAinv (Submodule.isClosed_orthogonal U') hU'inv.orthogonal q hqU')
      (Submodule.smul_mem _ _ hqU')
  have hsum : (A p - lam • p) + (A q - lam • q) = 0 := by
    have hv : A v = lam • v := (hmemE v).1 hvEV.1
    have : v = p + q := by rw [hq]; abel
    rw [this, map_add, smul_add] at hv
    rw [← sub_eq_zero] at hv
    rw [← hv]
    abel
  have hp0 : A p - lam • p = 0 := by
    have h3 : A p - lam • p = -(A q - lam • q) := eq_neg_of_add_eq_zero_left hsum
    have h4 : A p - lam • p ∈ U' ⊓ U'ᗮ := ⟨h1, h3 ▸ neg_mem h2⟩
    rwa [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at h4
  have hq0 : A q - lam • q = 0 := by
    rw [hp0, zero_add] at hsum
    exact hsum
  have hpE : p ∈ E := (hmemE p).2 (sub_eq_zero.1 hp0)
  have hqE : q ∈ E := (hmemE q).2 (sub_eq_zero.1 hq0)
  set U'' := U'ᗮ ⊓ U with hU''
  have hU''cl : IsClosed (U'' : Set H) := (Submodule.isClosed_orthogonal U').inter hUcl
  have hU''inv : π.IsInvariant U'' := hU'inv.orthogonal.inf hUinv
  by_cases hpz : p = 0
  ·
    left
    have hvU'' : v ∈ U'' := by
      have : v = q := by rw [hq, hpz, sub_zero]
      rw [this]
      exact ⟨hqU', hqU⟩
    have hUU'' : U ≤ U'' := π.cyclicSubspace_le hU''cl hU''inv hvU''
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ U'ᗮ := (hUU'' (hU'U hx)).1
    have : x ∈ U' ⊓ U'ᗮ := ⟨hx, hx'⟩
    rwa [Submodule.inf_orthogonal_eq_bot] at this
  by_cases hqz : q = 0
  ·
    right
    have hvU' : v ∈ U' := by
      have : v = p := by rw [← sub_eq_zero]; exact hqz
      rw [this]
      exact hpU'
    exact le_antisymm hU'U (π.cyclicSubspace_le hU'cl hU'inv hvU')
  exfalso
  have hne1 : E ⊓ U' ≠ ⊥ := fun h => by
    have : p ∈ E ⊓ U' := ⟨hpE, hpU'⟩
    rw [h, Submodule.mem_bot] at this
    exact hpz this
  have hne2 : E ⊓ U'' ≠ ⊥ := fun h => by
    have : q ∈ E ⊓ U'' := ⟨hqE, hqU', hqU⟩
    rw [h, Submodule.mem_bot] at this
    exact hqz this
  have e1 := hmin U' hU'cl hU'inv (hU'U.trans hUV₀) hne1
  have e2 := hmin U'' hU''cl hU''inv (inf_le_right.trans hUV₀) hne2
  have hpU'' : p ∈ E ⊓ U'' := by rw [e2, ← e1]; exact ⟨hpE, hpU'⟩
  have : p ∈ U' ⊓ U'ᗮ := ⟨hpU', hpU''.2.1⟩
  rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at this
  exact hpz this
end GroundTheory.Automorphic.UnitaryRep
