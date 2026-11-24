-- Prove2me | solution 1 for GlobalTheory.TraceIso.exists_equiv_of_trace_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:08:35.466926+00:00
-- url     : https://prove2.me/submissions/5be91ae8-5580-4f6b-b847-8ee60e9fce5b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyLinearEquivOfCharpolyEq
import Theorems.Thm_GlobalTheory_TraceIso_nonempty_linear_equiv_of_charpoly_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TraceIso
open Module
variable {k A : Type} [Field k] [Ring A] [Algebra k A]
namespace GlobalTheory.TraceIso
theorem _root_.solution [CharZero k] {Γ V W : Type} [Monoid Γ] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k V] [FiniteDimensional k W]
    (ρ : Representation k Γ V) (σ : Representation k Γ W) (hρ : ρ.IsSemisimpleRepresentation)
    (hσ : σ.IsSemisimpleRepresentation)
    (h : ∀ g, LinearMap.trace k V (ρ g) = LinearMap.trace k W (σ g)) :
    ∃ e : V ≃ₗ[k] W, ∀ g v, e (ρ g v) = σ g (e v) := by
  haveI := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).1 hρ
  haveI := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule σ).1 hσ
  have key : ∀ a : MonoidAlgebra k Γ, tr k ρ.asModule a = tr k σ.asModule a := by
    intro a
    unfold tr
    induction a using MonoidAlgebra.induction_on with
    | of g =>
      have e₁ : LinearMap.trace k _ (Algebra.lsmul k k ρ.asModule (MonoidAlgebra.of k Γ g)) =
          LinearMap.trace k V (ρ g) := by
        rw [← LinearMap.trace_conj' (ρ g) ρ.asModuleEquiv.symm]
        congr 1
        ext v
        rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm,
          Representation.asModuleEquiv_symm_map_rho, LinearEquiv.symm_apply_apply]
        rfl
      have e₂ : LinearMap.trace k _ (Algebra.lsmul k k σ.asModule (MonoidAlgebra.of k Γ g)) =
          LinearMap.trace k W (σ g) := by
        rw [← LinearMap.trace_conj' (σ g) σ.asModuleEquiv.symm]
        congr 1
        ext v
        rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm,
          Representation.asModuleEquiv_symm_map_rho, LinearEquiv.symm_apply_apply]
        rfl
      rw [e₁, e₂, h]
    | add a b ha hb => simp only [map_add, ha, hb]
    | smul c a ha => simp only [map_smul, ha]
  obtain ⟨e⟩ := nonempty_linear_equiv_of_charpoly_eq (k := k) (A := MonoidAlgebra k Γ) _ ρ.asModule σ.asModule le_rfl key
  refine ⟨ρ.asModuleEquiv.symm.trans ((e.restrictScalars k).trans σ.asModuleEquiv), fun g v => ?_⟩
  change σ.asModuleEquiv (e (ρ.asModuleEquiv.symm (ρ g v))) =
    σ g (σ.asModuleEquiv (e (ρ.asModuleEquiv.symm v)))
  rw [Representation.asModuleEquiv_symm_map_rho, map_smul, Representation.asModuleEquiv_map_smul]
  simp
end GlobalTheory.TraceIso
