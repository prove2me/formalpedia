-- Prove2me | solution 1 for GlobalTheory.DegCnt.sublat_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:37:11.273552+00:00
-- url     : https://prove2.me/submissions/76f12e95-e15c-47b3-af27-87aeb80bf90e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardEmbeddedDataWithGivenFixedLattice
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardEmbeddedHermDataIndexLe
import Theorems.Thm_GlobalTheory_DegCnt_finrank_sub_le
import Theorems.Thm_Formalism_SLP_Final_omegaPow
import Theorems.Thm_Formalism_SLP_Final_submoduleIndexCountO
import Theorems.Thm_GlobalTheory_DegCnt_DatCount_GenBy_trans


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
open GlobalTheory GlobalTheory.DegCnt
namespace GlobalTheory.DegCnt
theorem _root_.solution {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V) (hL : L.FG) (x : ℕ) (hx : 1 ≤ x) :
    {N : Submodule (𝓞 K) V | N ≤ L ∧ idx L N = x}.Finite ∧
      (({N : Submodule (𝓞 K) V | N ≤ L ∧ idx L N = x}.ncard : ℕ) : ℝ) ≤
        (x : ℝ) ^ (((Module.finrank K V) : ℝ) + cf K) := by
  have : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.2 hL
  have : Module.IsTorsionFree (𝓞 K) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K V
  have : Module.Flat (𝓞 K) L := inferInstance
  have : Module.FinitePresentation (𝓞 K) L := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) L := Module.Flat.projective_of_finitePresentation
  obtain ⟨h1, h2⟩ := Formalism.SLP.Final.submoduleIndexCountO K L x hx
  have hsub : {N : Submodule (𝓞 K) V | N ≤ L ∧ idx L N = x} ⊆
      (Submodule.map L.subtype) '' {N : Submodule (𝓞 K) L | N.toAddSubgroup.index = x} := by
    rintro N ⟨hN, hi⟩
    refine ⟨N.comap L.subtype, ?_, ?_⟩
    · exact hi
    · rw [Submodule.map_comap_subtype, inf_eq_right.2 hN]
  refine ⟨(h1.image _).subset hsub, ?_⟩
  have h3 := (Set.ncard_le_ncard hsub (h1.image _)).trans (Set.ncard_image_le h1)
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  have h4 := Formalism.SLP.Final.omegaPow (Module.finrank ℚ K) x Module.finrank_pos hx
  have h5 : ((Module.finrank (𝓞 K) L : ℕ) : ℝ) ≤ (Module.finrank K V : ℝ) := by
    exact_mod_cast finrank_sub_le L
  calc (({N : Submodule (𝓞 K) V | N ≤ L ∧ idx L N = x}.ncard : ℕ) : ℝ)
      ≤ ((Module.finrank ℚ K : ℕ) : ℝ) ^ (Nat.primeFactorsList x).length * (x : ℝ) ^ Module.finrank (𝓞 K) L := by
        exact_mod_cast h3.trans h2
    _ ≤ (x : ℝ) ^ Real.logb 2 (Module.finrank ℚ K) * (x : ℝ) ^ Module.finrank (𝓞 K) L :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = (x : ℝ) ^ (((Module.finrank (𝓞 K) L : ℕ) : ℝ) + Real.logb 2 (Module.finrank ℚ K)) := by
        rw [Real.rpow_add hx0, Real.rpow_natCast, mul_comm]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by unfold cf; linarith)
end GlobalTheory.DegCnt
