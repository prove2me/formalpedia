-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LocalSplit.exists_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:05:15.068535+00:00
-- url     : https://prove2.me/submissions/6182ab5f-34d1-4aa9-9a42-9e03e7823e2d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalFreeKernelSplitting
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalSplit_injective_of_basis_image

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LocalSplit
namespace GlobalTheory.CompanionTheory.LocalSplit
theorem _root_.solution {A Q P : Type} [CommRing A] [IsLocalRing A] [AddCommGroup Q] [Module A Q]
    [AddCommGroup P] [Module A P] [Module.Finite A Q] [Module.Free A Q] [Module.Finite A P]
    [Module.Free A P] (d : Q →ₗ[A] P) :
    ∃ (s : ℕ) (f : (Fin s → A) →ₗ[A] Q) (t : P →ₗ[A] (Fin s → A)),
      t ∘ₗ (d ∘ₗ f) = LinearMap.id ∧
      s + Module.finrank (IsLocalRing.ResidueField A)
        (LinearMap.ker (d.baseChange (IsLocalRing.ResidueField A))) = Module.finrank A Q := by
  classical
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl
    (LinearMap.ker (d.baseChange (IsLocalRing.ResidueField A)))
  let v := Module.finBasis (IsLocalRing.ResidueField A) C
  have hsurj : Function.Surjective (TensorProduct.mk A (IsLocalRing.ResidueField A) Q 1) :=
    TensorProduct.mk_surjective A Q (IsLocalRing.ResidueField A) IsLocalRing.residue_surjective
  choose a ha using fun i => hsurj (v i : (IsLocalRing.ResidueField A) ⊗[A] Q)
  let f : (Fin (Module.finrank (IsLocalRing.ResidueField A) C) → A) →ₗ[A] Q :=
    Fintype.linearCombination A a
  have hf : ∀ i, f (Pi.single i 1) = a i := by
    intro i
    simp [f, Fintype.linearCombination_apply_single]
  have hgk : LinearMap.ker ((d.baseChange (IsLocalRing.ResidueField A)) ∘ₗ C.subtype) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have hx1 : (x : (IsLocalRing.ResidueField A) ⊗[A] Q) ∈
        LinearMap.ker (d.baseChange (IsLocalRing.ResidueField A)) := hx
    have := hC.disjoint.le_bot ⟨hx1, x.2⟩
    simpa using this
  have hinj : Function.Injective ((d ∘ₗ f).lTensor (IsLocalRing.ResidueField A)) := by
    rw [← LinearMap.baseChange_eq_ltensor]
    apply injective_of_basis_image
      (Algebra.TensorProduct.basis (IsLocalRing.ResidueField A) (Pi.basisFun A _))
    have hl := v.linearIndependent.map' _ hgk
    have key : ⇑((d ∘ₗ f).baseChange (IsLocalRing.ResidueField A)) ∘
        ⇑(Algebra.TensorProduct.basis (IsLocalRing.ResidueField A)
          (Pi.basisFun A (Fin (Module.finrank (IsLocalRing.ResidueField A) C)))) =
        ⇑((d.baseChange (IsLocalRing.ResidueField A)) ∘ₗ C.subtype) ∘ ⇑v := by
      funext i
      have h2 := ha i
      simp only [TensorProduct.mk_apply] at h2
      simp [Algebra.TensorProduct.basis_apply, hf, ← h2]
    rw [key]
    exact hl
  obtain ⟨t, ht⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective (d ∘ₗ f)).2 hinj
  refine ⟨_, f, t, ht, ?_⟩
  rw [← Module.finrank_baseChange (R := IsLocalRing.ResidueField A) (S := A) (M' := Q),
    ← Submodule.finrank_add_eq_of_isCompl hC]
  omega
end GlobalTheory.CompanionTheory.LocalSplit
