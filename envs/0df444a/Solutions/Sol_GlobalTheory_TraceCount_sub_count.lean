-- Prove2me | solution 1 for GlobalTheory.TraceCount.sub_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:03:32.937313+00:00
-- url     : https://prove2.me/submissions/c3c0b4b6-ed03-473f-8f5f-204bce4479dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexCongruenceSubgroupLeAbsNormPow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardSublatticesIndexFixedTraceLe
import Theorems.Thm_GlobalTheory_TraceCount_proj_rank
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_Formalism_SLP_Final_omegaPow
import Theorems.Thm_Formalism_SLP_Final_submoduleIndexCountO
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
open GlobalTheory GlobalTheory.TraceCount
namespace GlobalTheory.TraceCount
theorem _root_.solution {K W : Type} [Field K] [NumberField K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (C : Submodule (𝓞 K) W) (hC : C.FG) (j : ℕ) (hj : 1 ≤ j) :
    {N : Submodule (𝓞 K) W | N ≤ C ∧ N.toAddSubgroup.relIndex C.toAddSubgroup = j}.Finite ∧
    (({N : Submodule (𝓞 K) W | N ≤ C ∧ N.toAddSubgroup.relIndex C.toAddSubgroup = j}.ncard : ℕ) : ℝ) ≤
      (j : ℝ) ^ Real.logb 2 (Module.finrank ℚ K) * (j : ℝ) ^ Module.finrank K W := by
  obtain ⟨h1, h2, h3⟩ := proj_rank C hC
  obtain ⟨h4, h5⟩ := Formalism.SLP.Final.submoduleIndexCountO K C j hj
  have h6 := Formalism.SLP.Final.omegaPow (Module.finrank ℚ K) j Module.finrank_pos hj
  have hsub : {N : Submodule (𝓞 K) W | N ≤ C ∧ N.toAddSubgroup.relIndex C.toAddSubgroup = j} ⊆
      (fun N : Submodule (𝓞 K) C => N.map C.subtype) '' {N | N.toAddSubgroup.index = j} := by
    rintro N ⟨hN, hNj⟩
    refine ⟨N.comap C.subtype, hNj, ?_⟩
    simp only [Submodule.map_comap_subtype]
    exact inf_eq_right.2 hN
  refine ⟨(h4.image _).subset hsub, ?_⟩
  have h7 := ((Set.ncard_le_ncard hsub (h4.image _)).trans (Set.ncard_image_le h4)).trans h5
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  calc _ ≤ ((Module.finrank ℚ K : ℕ) : ℝ) ^ (Nat.primeFactorsList j).length * (j : ℝ) ^ Module.finrank (𝓞 K) C := by
        exact_mod_cast h7
    _ ≤ _ := mul_le_mul h6 (pow_le_pow_right₀ hj1 h3) (by positivity) (by positivity)
end GlobalTheory.TraceCount
