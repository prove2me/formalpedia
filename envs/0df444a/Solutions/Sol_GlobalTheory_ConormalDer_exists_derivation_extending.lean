-- Prove2me | solution 1 for GlobalTheory.ConormalDer.exists_derivation_extending
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:42:50.807445+00:00
-- url     : https://prove2.me/submissions/372cb418-9376-48b6-b1bb-8e1950a7cb6f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDerivationExtendingCotangentForm
import Theorems.Thm_GlobalTheory_ConormalDer_exists_derivation_cotangent
import Theorems.Thm_GlobalTheory_ConormalDer_formallySmooth_residueField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.ConormalDer
namespace GlobalTheory.ConormalDer
theorem _root_.solution :
    ∀ (R B : Type) [CommRing R] [IsDomain R] [Algebra ℚ R] [CommRing B] [IsLocalRing B] [Algebra R B], (∀ r : R, r ≠ 0 → IsUnit (algebraMap R B r)) → ∀ (lam : CotangentSpace B →ₗ[ResidueField B] ResidueField B), ∃ δ : Derivation R B (ResidueField B), ∀ y (hy : y ∈ maximalIdeal B), δ y = lam ((maximalIdeal B).toCotangent ⟨y, hy⟩) := by
  intro R B _ _ _ _ _ _ hu lam
  haveI := formallySmooth_residueField R B hu
  obtain ⟨D, hmul, hD⟩ := exists_derivation_cotangent R B
  have hsm : ∀ (a : B) (v : CotangentSpace B), lam (a • v) = a • lam v := fun a v => by
    rw [← algebraMap_smul (ResidueField B) a v, map_smul, algebraMap_smul]
  let L : B →ₗ[R] ResidueField B :=
    { toFun := fun a => lam (D a)
      map_add' := fun a b => by rw [map_add, map_add]
      map_smul' := fun c a => by
        rw [RingHom.id_apply, map_smul, ← algebraMap_smul B c (D a), hsm, algebraMap_smul] }
  refine ⟨Derivation.mk' L fun a b => ?_, fun y hy => ?_⟩
  · change lam (D (a * b)) = a • lam (D b) + b • lam (D a)
    rw [hmul, map_add, hsm, hsm]
  · show lam (D y) = _
    exact congrArg lam (hD ⟨y, hy⟩)
end GlobalTheory.ConormalDer
