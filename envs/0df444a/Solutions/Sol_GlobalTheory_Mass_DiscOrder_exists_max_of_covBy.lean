-- Prove2me | solution 1 for GlobalTheory.Mass.DiscOrder.exists_max_of_covBy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:12:24.304263+00:00
-- url     : https://prove2.me/submissions/d2a69843-eda1-4650-99bf-7e326b9a258b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovol
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Theorems.Thm_GlobalTheory_Mass_DiscOrder_idxN_eq_card

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.DiscOrder
variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
namespace GlobalTheory.Mass.DiscOrder
theorem _root_.solution {X Y : Submodule R W} (h : X ⋖ Y) :
    ∃ P : Ideal R, P.IsMaximal ∧ (∀ r : R, r ∈ P ↔ ∀ y ∈ Y, r • y ∈ X) ∧ idxN Y X = Nat.card (R ⧸ P) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 ((covBy_iff_quot_is_simple h.le).1 h)
  refine ⟨P, hP, fun r => ⟨fun hr y hy => ?_, fun hr => ?_⟩, by rw [idxN_eq_card]; exact Nat.card_congr e.toEquiv⟩
  · have : r • (Submodule.Quotient.mk ⟨y, hy⟩ : Y ⧸ X.comap Y.subtype) = 0 := by
      apply e.injective
      rw [map_smul, map_zero]
      obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective P (e (Submodule.Quotient.mk ⟨y, hy⟩))
      rw [← ha, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact P.mul_mem_right a hr
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
    exact this
  · obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (e.symm (Submodule.Quotient.mk 1))
    have h0 : r • e.symm (Submodule.Quotient.mk 1) = 0 := by
      rw [← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact hr y y.2
    rw [← map_smul, EmbeddingLike.map_eq_zero_iff, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero] at h0
    simpa using h0
end GlobalTheory.Mass.DiscOrder
