-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementJacquet.exists_reps_congruenceSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:47:53.369387+00:00
-- url     : https://prove2.me/submissions/7a74a35d-3ee3-4b6e-a7b0-86e9f939fe33

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJZetaDefs
import Definitions.Def_GroundTheory_AutomorphicForms_HaarCosets
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJInducedCoeff
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_isCompact_integralGL


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementJacquet
open Matrix GLnLocal Parabolic Iwasawa MeasureTheory
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
  {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}
variable (F n)
namespace GroundTheory.Automorphic.GodementJacquet
theorem _root_.solution (m : ℕ) :
    ∃ R : Finset (GL (Fin n) F), (∀ x ∈ R, x ∈ integralGL F n) ∧
      ∀ k ∈ integralGL F n, ∃ x ∈ R, x⁻¹ * k ∈ congruenceSubgroup F n m := by
  classical
  set K₀ := integralGL F n
  set K := congruenceSubgroup F n m
  have : CompactSpace K₀ := isCompact_iff_compactSpace.1 (isCompact_integralGL F n)
  have hQ : Finite (K₀ ⧸ K.subgroupOf K₀) := by
    refine Subgroup.quotient_finite_of_isOpen _ ?_
    rw [Subgroup.coe_subgroupOf]
    exact (isOpen_congruenceSubgroup F n m).preimage continuous_subtype_val
  have := Fintype.ofFinite (K₀ ⧸ K.subgroupOf K₀)
  refine ⟨Finset.univ.image fun q : K₀ ⧸ K.subgroupOf K₀ => ((Quotient.out q : K₀) : GL (Fin n) F),
    ?_, fun k hk => ?_⟩
  · intro x hx
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hx
    exact (Quotient.out q).2
  · refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (QuotientGroup.mk (⟨k, hk⟩ : K₀))), ?_⟩
    have h := QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk (⟨k, hk⟩ : K₀) :
      K₀ ⧸ K.subgroupOf K₀))
    exact Subgroup.mem_subgroupOf.1 h
end GroundTheory.Automorphic.GodementJacquet
