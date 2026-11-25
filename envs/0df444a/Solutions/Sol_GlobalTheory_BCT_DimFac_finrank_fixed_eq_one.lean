-- Prove2me | solution 1 for GlobalTheory.BCT.DimFac.finrank_fixed_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:48:16.612785+00:00
-- url     : https://prove2.me/submissions/30822fae-f2e5-48d6-a8f8-16b9f0a3876c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactorUnique
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsIrreducibleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompOfSurjective
import Theorems.Thm_GlobalTheory_BCT_DimFac_mem_fix
import Theorems.Thm_GlobalTheory_BCT_DimFac_HasComp_exists_op
import Theorems.Thm_Reformulated_TransposeInverseTheory_coe_transposeInv
import Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_symm
import Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_transposeInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.TransposeInverseTheory.coe_transposeInv
attribute [local simp] Reformulated.TransposeInverseTheory.transposeInv_symm
attribute [local simp] Reformulated.TransposeInverseTheory.transposeInv_transposeInv



set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GroundTheory.Automorphic.RestrictedTensor Module
open scoped TensorProduct
open GlobalTheory GlobalTheory.BCT GlobalTheory.BCT.DimFac
variable {Γ V W M : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup M] [Module ℂ M]
variable {ι : Type} {e : ι → Γ →* Γ} {L : Subgroup Γ}
namespace GlobalTheory.BCT.DimFac
theorem _root_.solution (he : ∀ i g, e i (e i g) = e i g) (hne : ∀ i j, i ≠ j → ∀ g, e i (e j g) = 1)
    (hc : ∀ i g y, Commute ((e i g)⁻¹ * g) (e i y)) (hL : ∀ g, g ∈ L ↔ ∀ i, e i g ∈ L)
    (hfin : ∀ g, {i | e i g ∉ L}.Finite) {ρ : Representation ℂ Γ V} (hρ : ρ.IsIrreducible)
    (h : ∀ i, HasComp ρ (e i) L 1) {m : V} (hm0 : m ≠ 0) (hm : m ∈ fixed ρ L) : finrank ℂ (fixed ρ L) = 1 := by
  classical
  let N : Finset ι → Submodule ℂ V := fun U => Submodule.span ℂ {v | ∃ g, (∀ i ∉ U, e i g ∈ L) ∧ ρ g m = v}
  have hmono : Monotone N := fun U U' hU => Submodule.span_mono fun v ⟨g, hg, hv⟩ =>
    ⟨g, fun i hi => hg i fun h => hi (hU h), hv⟩
  have htop : ∀ v, ∃ U, v ∈ N U := by
    have h1 : Submodule.span ℂ (Set.range fun g => ρ g m) = ⊤ := by
      refine (((GlobalTheory.CuspRep.isIrreducible_iff ρ).1 hρ).2 _ fun g v hv => ?_).resolve_left fun h0 => hm0 ?_
      · refine (Submodule.span_le (p := (Submodule.span ℂ (Set.range fun g => ρ g m)).comap (ρ g))).2 ?_ hv
        rintro _ ⟨a, rfl⟩
        exact Submodule.subset_span ⟨g * a, (rep_mul ρ g a m).symm⟩
      · have : m ∈ Submodule.span ℂ (Set.range fun g => ρ g m) := Submodule.subset_span ⟨1, by simp⟩
        rwa [h0] at this
    have h2 : Submodule.span ℂ (Set.range fun g => ρ g m) ≤ ⨆ U, N U := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, rfl⟩
      exact Submodule.mem_iSup_of_mem (hfin g).toFinset (Submodule.subset_span ⟨g, fun i hi => by simpa using hi, rfl⟩)
    exact fun v => (Submodule.mem_iSup_of_directed _ hmono.directed_le).1 (h2 (h1 ▸ Submodule.mem_top))
  have hdown : ∀ v ∈ fixed ρ L, ∀ U, v ∈ N U → v ∈ N ∅ := by
    intro v hv U
    induction U using Finset.induction_on with
    | empty => exact id
    | insert i U hi ih =>
      intro hU
      obtain ⟨P, hP1, hP2⟩ := (h i).exists_op hρ (he i) (hc i)
      have hfx : ∀ u ∈ fixed ρ L, ∀ g ∈ L, ρ (e i g) u = u := fun u hu g hg => mem_fix.1 hu _ ((hL g).1 hg i)
      refine ih ?_
      rw [← (hP2 v (hfx v hv)).1]
      refine (Submodule.span_le (p := (N U).comap P)).2 ?_ hU
      rintro _ ⟨g, hg, rfl⟩
      obtain ⟨c, hc'⟩ := (hP2 m (hfx m hm)).2 g
      have h1 : e i ((e i g)⁻¹ * g) = 1 := by rw [map_mul, map_inv, he, inv_mul_cancel]
      have h2 : ρ g m = ρ ((e i g)⁻¹ * g) (ρ (e i g) m) := by rw [rep_mul, (hc i g g).eq, mul_inv_cancel_left]
      change P (ρ g m) ∈ N U
      rw [h2, hP1 _ h1, hc', map_smul]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, fun j hj => ?_, rfl⟩)
      by_cases hji : j = i
      · rw [hji, h1]; exact L.one_mem
      · rw [map_mul, map_inv, hne j i hji, inv_one, one_mul]
        exact hg j (by simp [hji, hj])
  refine finrank_eq_one_iff'.2 ⟨⟨m, hm⟩, fun h => hm0 (congrArg Subtype.val h), fun v => ?_⟩
  obtain ⟨U, hU⟩ := htop v.1
  have h3 : N ∅ ≤ Submodule.span ℂ {m} := Submodule.span_mono (by
    rintro _ ⟨g, hg, rfl⟩
    exact mem_fix.1 hm g ((hL g).2 fun i => hg i (by simp)))
  obtain ⟨c, hc'⟩ := Submodule.mem_span_singleton.1 (h3 (hdown v.1 v.2 U hU))
  exact ⟨c, Subtype.ext hc'⟩
end GlobalTheory.BCT.DimFac
