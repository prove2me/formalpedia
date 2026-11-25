-- Prove2me | solution 1 for GlobalTheory.DegCnt.trip_fixLat_inf_eq_and_pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:01:47.49782+00:00
-- url     : https://prove2.me/submissions/fd16b77f-3455-4d21-bc4d-0b0184ad9d94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FixedLatticeInfEqAndPairingOfIsometry
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt
namespace GlobalTheory.DegCnt
theorem _root_.solution : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ (x x' : ℕ), ∀ p ∈ Trip H g L₀ j x x', fixLat p.1.2 ⊓ rs (𝓞 K) (fixSp p.2.2) = fixLat p.2.1.2 ⊓ rs (𝓞 K) (fixSp p.2.2) ∧ ∀ y ∈ fixLat p.1.2, ∀ y' ∈ fixLat p.2.1.2, ∃ t : 𝓞 K, H.B y (y' - p.2.2 y') = (g : K) * (t : K) := by
  intro K V _ _ _ _ _ _ _ _ H _ _ L₀ g j D₀ _ _ _ _ x x' p hp
  obtain ⟨h1, -, -, -, h5⟩ := hp
  have hmem : ∀ (Γ : Submodule (𝓞 K) (V × V)) (y : V), y ∈ fixLat Γ ↔ (y, y) ∈ Γ := fun _ _ => Iff.rfl
  refine ⟨?_, ?_⟩
  · ext y
    have hf : y ∈ rs (𝓞 K) (fixSp p.2.2) ↔ p.2.2 y = y := by
      simp [fixSp, sub_eq_zero]
    rw [Submodule.mem_inf, Submodule.mem_inf, hmem, hmem, hf, h5]
    refine and_congr_left fun h => ?_
    rw [h]
  · intro y hy y' hy'
    rw [hmem] at hy hy'
    rw [h5] at hy'
    obtain ⟨t, ht⟩ := h1.2.2.1.2.2.2.2.2.2 _ hy _ hy'
    refine ⟨-t, ?_⟩
    simp only [map_mul, map_natCast] at ht
    rw [map_sub]
    have : ((-t : 𝓞 K) : K) = -(algebraMap (𝓞 K) K t) := map_neg (algebraMap (𝓞 K) K) t
    rw [this]
    linear_combination -ht
end GlobalTheory.DegCnt
