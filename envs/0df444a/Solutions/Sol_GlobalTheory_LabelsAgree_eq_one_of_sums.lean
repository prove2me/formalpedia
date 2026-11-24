-- Prove2me | solution 1 for GlobalTheory.LabelsAgree.eq_one_of_sums
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:57:13.687884+00:00
-- url     : https://prove2.me/submissions/ebb42b61-d93f-401e-918a-d013828a82e0

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
import Theorems.Thm_GlobalTheory_LabelsAgree_norm_char
import Theorems.Thm_GlobalTheory_fourier_extraction_tsum_class
import Theorems.Thm_GlobalTheory_realExtBilin_tmul
import Theorems.Thm_GlobalTheory_realExt_tmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
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
theorem _root_.solution {C X : Type} [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C]
    [IsAlgClosed C] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {m : ℕ} (hm : ‖(m : C)‖ = 1)
    (T : X → C) (hT : Filter.Tendsto T Filter.cofinite (nhds 0)) (h0 : T 0 ≠ 0)
    (hdom : ∀ z, z ≠ 0 → ‖T (m • z)‖ < ‖T 0‖) (w : C) (τ : Multiplicative X →* Cˣ) (hτ : τ ^ m = 1)
    (h : ∀ u : Multiplicative X →* Cˣ, u ^ m = 1 →
      ∑' χ, w * (τ (Multiplicative.ofAdd χ) : C) * T χ * (u (Multiplicative.ofAdd χ) : C) =
        ∑' χ, T χ * (u (Multiplicative.ofAdd χ) : C)) : w = 1 := by
  have hmC : (m : C) ≠ 0 := by
    intro h; rw [h, norm_zero] at hm; exact zero_ne_one hm
  have hm0 : m ≠ 0 := by rintro rfl; simp at hmC
  haveI : NeZero (m : C) := ⟨hmC⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C m
  have hT' : Filter.Tendsto (fun χ => w * (τ (Multiplicative.ofAdd χ) : C) * T χ) Filter.cofinite (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero] at hT ⊢
    simpa only [norm_mul, norm_char hm0 hτ, mul_one, mul_zero] using hT.const_mul ‖w‖
  obtain ⟨-, a1, a2⟩ := fourier_extraction_tsum_class C X m ζ (Nat.pos_of_ne_zero hm0) hm hζ T hT 0
  obtain ⟨-, b1, -⟩ := fourier_extraction_tsum_class C X m ζ (Nat.pos_of_ne_zero hm0) hm hζ _ hT' 0
  simp only [zero_add] at a1 a2 b1
  rw [finsum_congr fun u => by rw [h u.1 u.2], a1] at b1
  have e : ∀ z : X, (τ (Multiplicative.ofAdd (m • z)) : C) = 1 := fun z => by
    rw [ofAdd_nsmul, map_pow, TorsionFourier.apply_pow_eq_one hτ, Units.val_one]
  simp only [e, mul_one, tsum_mul_left] at b1
  have b2 := mul_left_cancel₀ (pow_ne_zero _ hmC) b1
  have hS : ∑' z, T (m • z) ≠ 0 := by
    rw [← norm_ne_zero_iff, a2 hdom, norm_ne_zero_iff]; exact h0
  exact (mul_eq_right₀ hS).1 b2.symm
end GlobalTheory.LabelsAgree
