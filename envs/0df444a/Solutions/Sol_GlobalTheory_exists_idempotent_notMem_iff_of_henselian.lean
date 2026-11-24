-- Prove2me | solution 1 for GlobalTheory.exists_idempotent_notMem_iff_of_henselian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:38:56.933244+00:00
-- url     : https://prove2.me/submissions/f0263339-ec7f-4d32-b0df-ce43d6b08767

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Theorems.Thm_GlobalTheory_exists_algHom_lift_of_etale_of_isLocalRing
import Theorems.Thm_GlobalTheory_comap_eq_maximalIdeal_of_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open IsLocalRing Polynomial TensorProduct
namespace GlobalTheory
theorem _root_.solution (R : Type*) {S : Type*} [CommRing R]
    [HenselianLocalRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (q : Ideal S) [hq : q.IsMaximal] :
    ∃ e : S, IsIdempotentElem e ∧ ∀ n : Ideal S, n.IsMaximal → (e ∉ n ↔ n = q) := by
  have : q.LiesOver (maximalIdeal R) := ⟨(comap_eq_maximalIdeal_of_finite q).symm⟩
  obtain ⟨R', _, _, _, P, _, _, e, he, P', _, _, hP'q, heP', hbij, -, H⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq (maximalIdeal R) q
  let ε : (maximalIdeal R).ResidueField ≃ₐ[R] P.ResidueField := .ofBijective _ hbij
  let ε' : (R ⧸ maximalIdeal R) ≃ₐ[R] (maximalIdeal R).ResidueField :=
    .ofBijective (IsScalarTower.toAlgHom _ _ _)
      (Ideal.bijective_algebraMap_quotient_residueField _)
  obtain ⟨σ, hσ⟩ := exists_algHom_lift_of_etale_of_isLocalRing (maximalIdeal R)
    ((ε'.trans ε).symm.toAlgHom.comp (IsScalarTower.toAlgHom R R' P.ResidueField))
  have hσP : ∀ a, σ a ∈ maximalIdeal R ↔ a ∈ P := fun a ↦ by
    rw [← Ideal.Quotient.eq_zero_iff_mem, hσ, ← Ideal.algebraMap_residueField_eq_zero (I := P)]
    simp
  let τ : R' ⊗[R] S →ₐ[R] S :=
    Algebra.TensorProduct.lift ((Algebra.ofId R S).comp σ) (.id R S) fun _ _ ↦ .all _ _
  have hlies : ∀ n : Ideal S, n.IsMaximal → (n.comap τ).LiesOver P := fun n hn ↦ ⟨by
    ext a
    rw [← hσP, ← comap_eq_maximalIdeal_of_finite n]
    simp [τ, Ideal.under, Algebra.TensorProduct.algebraMap_apply]⟩
  have hcomap : ∀ n : Ideal S,
      (n.comap τ).comap Algebra.TensorProduct.includeRight.toRingHom = n := fun n ↦ by
    ext a
    simp [τ]
  refine ⟨τ e, he.map τ, fun n hn ↦ ⟨fun h ↦ ?_, ?_⟩⟩
  · have := H (n.comap τ) inferInstance (hlies n hn) h
    rw [← hcomap n, this, hP'q]
  · rintro rfl
    have := hlies n hn
    have : n.comap τ = P' :=
      Ideal.eq_of_comap_eq_comap_of_bijective_residueFieldMap hbij _ _ (by rw [hcomap, hP'q])
    rw [← this] at heP'
    exact heP'
end GlobalTheory
