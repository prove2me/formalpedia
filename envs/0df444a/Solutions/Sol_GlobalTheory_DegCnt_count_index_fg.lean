-- Prove2me | solution 1 for GlobalTheory.DegCnt.count_index_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:01:45.973798+00:00
-- url     : https://prove2.me/submissions/78576e9b-3d48-4a5a-b2b7-0741ab373e3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardSublatticesDefiniteQuotientNormalFormLe
import Theorems.Thm_Formalism_SLP_Final_omegaPow
import Theorems.Thm_Formalism_SLP_Final_submoduleIndexCountO


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
theorem _root_.solution {K Q : Type} [Field K] [NumberField K] [AddCommGroup Q] [Module K Q]
    [Module (𝓞 K) Q] [IsScalarTower (𝓞 K) K Q] [FiniteDimensional K Q] (M : Submodule (𝓞 K) Q) (hM : M.FG)
    (S : Submodule K Q) (hS : M ≤ S.restrictScalars (𝓞 K)) (k : ℕ) (hk : Module.finrank K S ≤ k)
    (x : ℕ) (hx : 1 ≤ x) :
    {N : Submodule (𝓞 K) M | N.toAddSubgroup.index = x}.Finite ∧
      (({N : Submodule (𝓞 K) M | N.toAddSubgroup.index = x}.ncard : ℕ) : ℝ) ≤ (x : ℝ) ^ ((k : ℝ) + cf K) := by
  have : Module.Finite (𝓞 K) M := Module.Finite.iff_fg.2 hM
  have : Module.IsTorsionFree (𝓞 K) Q := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K Q
  have : Module.FinitePresentation (𝓞 K) M := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) M := Module.Flat.projective_of_finitePresentation
  obtain ⟨h1, h2⟩ := Formalism.SLP.Final.submoduleIndexCountO K M x hx
  refine ⟨h1, ?_⟩
  have hr : Module.finrank (𝓞 K) M ≤ k := by
    refine le_trans ?_ hk
    apply Module.finrank_le_of_rank_le
    have h3 : Module.rank (𝓞 K) M ≤ Module.rank (𝓞 K) S := Submodule.rank_mono hS
    have h5 : Module.rank K S = Module.rank (𝓞 K) S := IsLocalization.rank_eq K (nonZeroDivisors (𝓞 K)) le_rfl
    rw [Module.finrank_eq_rank, h5]
    exact h3
  have hn : 1 ≤ Module.finrank ℚ K := Module.finrank_pos
  have hx1 : (1:ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0:ℝ) < x := by linarith
  have h4 := Formalism.SLP.Final.omegaPow (Module.finrank ℚ K) x hn hx
  have h3 : (({N : Submodule (𝓞 K) M | N.toAddSubgroup.index = x}.ncard : ℕ) : ℝ) ≤
      ((Module.finrank ℚ K : ℕ) : ℝ) ^ (Nat.primeFactorsList x).length *
        (x : ℝ) ^ Module.finrank (𝓞 K) M := by exact_mod_cast h2
  have hr' : (Module.finrank (𝓞 K) M : ℝ) ≤ k := by exact_mod_cast hr
  calc _ ≤ _ := h3
    _ ≤ (x : ℝ) ^ Real.logb 2 (Module.finrank ℚ K) * (x : ℝ) ^ Module.finrank (𝓞 K) M :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = (x : ℝ) ^ ((Module.finrank (𝓞 K) M : ℝ) + Real.logb 2 (Module.finrank ℚ K)) := by
        rw [Real.rpow_add hx0, Real.rpow_natCast, mul_comm]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by unfold cf; linarith)
end GlobalTheory.DegCnt
