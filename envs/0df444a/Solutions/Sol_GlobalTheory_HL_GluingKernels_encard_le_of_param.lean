-- Prove2me | solution 1 for GlobalTheory.HL.GluingKernels.encard_le_of_param
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:49:27.09967+00:00
-- url     : https://prove2.me/submissions/5f37deef-a251-44ef-bb48-9664de19d445

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardSubmoduleAndHomLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsGluingHomomorphismDefectGroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameLatticeGramDetAndMinorsOrbitInvariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsBasisFgMaximalOrderSpanningFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardGluingHomKernelsLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.GluingKernels
namespace GlobalTheory.HL.GluingKernels
theorem _root_.solution {R D β : Type} [CommRing R] [AddCommGroup D] [Module R D] [Finite D]
    (m j : ℕ) (Φ : (Fin m → D) → β) (T : Set β)
    (hT : ∀ t ∈ T, ∃ I : Submodule R D, Nat.card I = j ∧ ∃ x : Fin m → D, (∀ i, x i ∈ I) ∧ Φ x = t) :
    T.encard ≤ ((Nat.card (Submodule R D) * j ^ m : ℕ) : ℕ∞) := by
  haveI : Finite (Submodule R D) := Finite.of_injective _ (SetLike.coe_injective (A := Submodule R D))
  let A := Σ I : {I : Submodule R D // Nat.card I = j}, (Fin m → I.1)
  let Ψ : A → β := fun a => Φ fun i => (a.2 i : D)
  have hsub : T ⊆ Ψ '' Set.univ := by
    intro t ht
    obtain ⟨I, hI, x, hx, rfl⟩ := hT t ht
    exact ⟨⟨⟨I, hI⟩, fun i => ⟨x i, hx i⟩⟩, trivial, rfl⟩
  haveI : Fintype {I : Submodule R D // Nat.card I = j} := Fintype.ofFinite _
  have hA : Nat.card A ≤ Nat.card (Submodule R D) * j ^ m := by
    have h1 : Nat.card A = ∑ I : {I : Submodule R D // Nat.card I = j}, j ^ m := by
      rw [Nat.card_sigma]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [Nat.card_fun, I.2, Nat.card_eq_fintype_card, Fintype.card_fin]
    rw [h1, Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]
    exact Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective _ Subtype.val_injective)
  calc T.encard ≤ (Ψ '' Set.univ).encard := Set.encard_le_encard hsub
    _ ≤ (Set.univ : Set A).encard := Set.encard_image_le _ _
    _ = (Nat.card A : ℕ∞) := by
      rw [Set.encard_univ, ENat.card_eq_coe_natCard]
    _ ≤ _ := by exact_mod_cast hA
end GlobalTheory.HL.GluingKernels
