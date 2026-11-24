-- Prove2me | solution 1 for GlobalTheory.FinEt.exists_section_of_isSepClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:04:49.234705+00:00
-- url     : https://prove2.me/submissions/8096b9ed-3824-4467-b6be-1cc20f8ffc40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits TopologicalSpace AlgebraicGeometry
universe u
noncomputable section
open GlobalTheory GlobalTheory.FinEt
attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc
variable {S : Scheme.{u}} {X Y : Over S}
namespace GlobalTheory.FinEt
theorem _root_.solution {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsFinite p] [Etale p] [Nonempty X] :
    ∃ σ : Spec (.of k) ⟶ X, σ ≫ p = 𝟙 _ := by
  wlog hX : ∃ A, X = Spec A generalizing X
  · have _ : IsAffine X := isAffine_of_isAffineHom p
    have _ : Nonempty (Spec Γ(X, ⊤)) := ⟨X.isoSpec.hom (Classical.arbitrary X)⟩
    obtain ⟨σ, hσ⟩ := this (X.isoSpec.inv ≫ p) ⟨_, rfl⟩
    exact ⟨σ ≫ X.isoSpec.inv, by simpa using hσ⟩
  obtain ⟨A, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective p
  have h1 : φ.hom.Etale := HasRingHomProperty.Spec_iff (P := @Etale).mp inferInstance
  let : Algebra k A := φ.hom.toAlgebra
  have : Algebra.Etale k A := h1
  let x : PrimeSpectrum A := Classical.arbitrary (Spec A)
  let ψ := (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum k A).symm x
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom), ?_⟩
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext a
  exact ψ.commutes a
end GlobalTheory.FinEt
