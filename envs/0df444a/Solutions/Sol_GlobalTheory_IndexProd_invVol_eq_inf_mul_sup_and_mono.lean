-- Prove2me | solution 1 for GlobalTheory.IndexProd.invVol_eq_inf_mul_sup_and_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:30:45.368803+00:00
-- url     : https://prove2.me/submissions/39282a75-dbb6-4019-878c-4a8633a7ae8b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolEqInfMulSupAndMono
import Theorems.Thm_GlobalTheory_IndexProd_relIndex_eq_inf_mul_sup
import Theorems.Thm_GlobalTheory_HL_invVol_eq_div_of_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.IndexProd
namespace GlobalTheory.IndexProd
theorem _root_.solution : ∀ (G : Type) [Group G] (R M A B : Subgroup G), M ≤ R → A ≤ R → B ≤ R → (∀ s ∈ R, ∀ t ∈ M, s * t * s⁻¹ ∈ M) → A.relIndex B ≠ 0 → B.relIndex A ≠ 0 → GlobalTheory.HL.invVol A B = GlobalTheory.HL.invVol (A ⊓ M) (B ⊓ M) * GlobalTheory.HL.invVol (A ⊔ M) (B ⊔ M) ∧ ∀ B' ≤ B, B'.relIndex A ≠ 0 → A.relIndex B' ≠ 0 → GlobalTheory.HL.invVol A B ≤ GlobalTheory.HL.invVol A B' ∧ GlobalTheory.HL.invVol A B ≤ (B'.relIndex A : ℝ) := by
  intro G _ R M A B _ hA hB hn hAB hBA
  constructor
  · have eA := relIndex_eq_inf_mul_sup (D := A ⊓ B) (M := M) inf_le_left
      (fun s hs => hn s (hA hs))
    have eB := relIndex_eq_inf_mul_sup (D := A ⊓ B) (M := M) inf_le_right
      (fun s hs => hn s (hB hs))
    have dA : (A ⊓ B).relIndex A ≠ 0 := by rwa [Subgroup.inf_relIndex_left]
    have dA' := dA
    rw [eA, mul_ne_zero_iff] at dA'
    rw [GlobalTheory.HL.invVol_eq_div_of_le inf_le_left inf_le_right dA,
      GlobalTheory.HL.invVol_eq_div_of_le (inf_le_inf_right M inf_le_left)
        (inf_le_inf_right M inf_le_right) dA'.1,
      GlobalTheory.HL.invVol_eq_div_of_le (sup_le_sup_right inf_le_left M)
        (sup_le_sup_right inf_le_right M) dA'.2, eA, eB]
    push_cast
    rw [div_mul_div_comm]
  · intro B' hB' h1 h2
    have dA : (A ⊓ B').relIndex A ≠ 0 := by rwa [Subgroup.inf_relIndex_left]
    have dB : (A ⊓ B').relIndex B ≠ 0 :=
      Subgroup.relIndex_inf_ne_zero hAB (Subgroup.relIndex_ne_zero_trans h1 hAB)
    have dB' : (A ⊓ B').relIndex B' ≠ 0 := by rwa [Subgroup.inf_relIndex_right]
    have hle : GlobalTheory.HL.invVol A B ≤ GlobalTheory.HL.invVol A B' := by
      rw [GlobalTheory.HL.invVol_eq_div_of_le inf_le_left (inf_le_right.trans hB') dA,
        GlobalTheory.HL.invVol_eq_div_of_le inf_le_left inf_le_right dA]
      refine div_le_div_of_nonneg_left (Nat.cast_nonneg _)
        (by exact_mod_cast Nat.pos_of_ne_zero dB') ?_
      exact_mod_cast Subgroup.relIndex_le_of_le_right hB' dB
    refine ⟨hle, hle.trans ?_⟩
    rw [GlobalTheory.HL.invVol]
    exact div_le_self (Nat.cast_nonneg _) (by exact_mod_cast Nat.pos_of_ne_zero h2)
end GlobalTheory.IndexProd
