-- Prove2me | solution 1 for GlobalTheory.ProjModFinIso.exists_finite_reps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:13:00.701843+00:00
-- url     : https://prove2.me/submissions/146cdaa0-a492-4890-8d97-a878aed468d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FinitelyManyIsoClassesProjectiveNumberField
import Theorems.Thm_GlobalTheory_ProjModFinIso_nonempty_equiv_of_mk0_eq
import Theorems.Thm_GlobalTheory_ProjModFinIso_exists_equiv_pi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.ProjModFinIso
variable {R : Type} [CommRing R] [IsDedekindDomain R]
namespace GlobalTheory.ProjModFinIso
theorem _root_.solution [Finite (ClassGroup R)] (q : ℕ) :
    ∃ (n : ℕ) (Y : Fin n → ModuleCat.{0} R), ∀ (X : Type) [AddCommGroup X] [Module R X]
      [Module.Finite R X] [Module.Projective R X], Module.finrank R X ≤ q →
      ∃ k, Nonempty (X ≃ₗ[R] Y k) := by
  let rep : ClassGroup R → Ideal R := fun c => ((ClassGroup.mk0_surjective c).choose : Ideal R)
  have hrep : ∀ c : ClassGroup R, ClassGroup.mk0 (ClassGroup.mk0_surjective c).choose = c :=
    fun c => (ClassGroup.mk0_surjective c).choose_spec
  let S := Σ r : Fin (q + 1), (Fin r → ClassGroup R)
  let Y' : S → ModuleCat.{0} R := fun s => ModuleCat.of R ((b : Fin s.1) → rep (s.2 b))
  obtain ⟨n, ⟨eS⟩⟩ := Finite.exists_equiv_fin S
  refine ⟨n, fun k => Y' (eS.symm k), ?_⟩
  intro X _ _ _ _ hX
  obtain ⟨ι, _, I, hcard, ⟨e⟩⟩ := exists_equiv_pi (R := R) (Module.finrank R X) X rfl
  let eι := Fintype.equivFin ι
  let s : S := ⟨⟨Fintype.card ι, by omega⟩, fun b => ClassGroup.mk0 (I (eι.symm b))⟩
  refine ⟨eS s, ?_⟩
  show Nonempty (X ≃ₗ[R] Y' (eS.symm (eS s)))
  rw [Equiv.symm_apply_apply]
  have hI : ∀ i, Nonempty ((I i : Ideal R) ≃ₗ[R] rep (ClassGroup.mk0 (I i))) := fun i =>
    nonempty_equiv_of_mk0_eq (hrep _).symm
  exact ⟨e ≪≫ₗ LinearEquiv.piCongrRight (fun i => (hI i).some) ≪≫ₗ
    LinearEquiv.piCongrLeft' R (fun i => ↥(rep (ClassGroup.mk0 (I i)))) eι⟩
end GlobalTheory.ProjModFinIso
