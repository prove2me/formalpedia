-- Prove2me | solution 1 for GlobalTheory.LabelsAgree.exists_char_root
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:35.341114+00:00
-- url     : https://prove2.me/submissions/a7706a0f-7389-4727-b38c-d46dd9475426

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaConstantTermRepresentativeDependence
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormRepGeneratorsAndThetaSeriesTermStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomTransportStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SymmPairingEqOneOfOddOfDiag
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsBasisUniqueMinPairSums
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourierExtractionTsumClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaRecognitionLabelsAgreeOfIso
import Theorems.Thm_GlobalTheory_realExtBilin_tmul
import Theorems.Thm_GlobalTheory_realExt_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.realExtBilin_tmul
attribute [local simp] GlobalTheory.realExt_tmul



set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.LabelsAgree
namespace GlobalTheory.LabelsAgree
theorem _root_.solution {C X : Type} [Field C] [IsAlgClosed C] [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (u : Multiplicative X →* Cˣ) {k : ℕ} (hk : k ≠ 0) : ∃ t : Multiplicative X →* Cˣ, t ^ k = u := by
  let b := Module.finBasis ℤ X
  have h : ∀ x : Cˣ, ∃ y : Cˣ, y ^ k = x := fun x => by
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x : C) (Nat.pos_of_ne_zero hk)
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [zero_pow hk] at hy
      exact x.ne_zero hy.symm
    exact ⟨Units.mk0 y hy0, Units.ext (by simpa using hy)⟩
  choose r hr using h
  refine ⟨TorsionFourier.charOfValues b fun i => r (u (Multiplicative.ofAdd (b i))), MonoidHom.ext fun x => ?_⟩
  change (∏ i, r (u (Multiplicative.ofAdd (b i))) ^ (b.repr x.toAdd i)) ^ k = u (Multiplicative.ofAdd x.toAdd)
  rw [TorsionFourier.char_apply_eq_prod b u, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hr]
end GlobalTheory.LabelsAgree
