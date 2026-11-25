-- Prove2me | solution 1 for GlobalTheory.DegCnt.FixDisc.idx_gmap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:58:03.514814+00:00
-- url     : https://prove2.me/submissions/142a7baa-7d68-48bf-b399-678ea1cce141

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DiscriminantOrderCommonFixedLatticeEmbeddedData
import Theorems.Thm_GlobalTheory_DegCnt_FixDisc_exists_rat_basis
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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.FixDisc
open GlobalTheory.Mass GlobalTheory.Mass.DiscOrder Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.DegCnt.FixDisc
theorem _root_.solution [FiniteDimensional K V] {A B : Submodule (𝓞 K) V} (hA : Submodule.IsLattice K A)
    (hB : Submodule.IsLattice K B) (F : V ≃ₗ[K] V) (h1 : B ≤ A) (h2 : gmap F B ≤ A) :
    (idxN A (gmap F B) : ℚ) = |Algebra.norm ℚ (LinearMap.det (F : V →ₗ[K] V))| * idxN A B := by
  let _ : Module ℚ V := Module.compHom V (algebraMap ℚ K)
  have : IsScalarTower ℚ K V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Finite ℚ V := Module.Finite.trans K V
  obtain ⟨a, ha⟩ := exists_rat_basis hA
  obtain ⟨b, hb⟩ := exists_rat_basis hB
  have hb' : (gmap F B).toAddSubgroup = AddSubgroup.closure (Set.range (b.map (F.restrictScalars ℚ))) := by
    have e : (gmap F B).toAddSubgroup = B.toAddSubgroup.map (F : V →ₗ[K] V).toAddMonoidHom := by
      ext x
      simp [gmap]
    rw [e, hb, AddMonoidHom.map_closure, ← Set.range_comp]
    rfl
  have e1 := AddSubgroup.relIndex_eq_abs_det _ _ ((Submodule.toAddSubgroup_le _ _).mpr h1) b a hb ha
  have e2 := AddSubgroup.relIndex_eq_abs_det _ _ ((Submodule.toAddSubgroup_le _ _).mpr h2) _ a hb' ha
  unfold idxN
  rw [e1, e2, ← abs_mul, ← LinearMap.det_restrictScalars,
    ← a.det_comp ((F : V →ₗ[K] V).restrictScalars ℚ) b]
  rfl
end GlobalTheory.DegCnt.FixDisc
