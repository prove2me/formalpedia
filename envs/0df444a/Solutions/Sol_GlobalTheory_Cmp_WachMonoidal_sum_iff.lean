-- Prove2me | solution 1 for GlobalTheory.Cmp.WachMonoidal.sum_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:24:43.139556+00:00
-- url     : https://prove2.me/submissions/eba78420-ed9b-4397-ae4e-7be249c9277f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorLatticeUnitPart
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_UnitDualParts
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersCompleteDVR
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitSumTensorDualOfWachMonoidal
import Theorems.Thm_GlobalTheory_Cmp_WachMonoidal_isCrys_of_isSumLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cmp GlobalTheory.Cmp.WachMonoidal
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module
open GlobalTheory.IndefiniteRowSideFullHecke
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
variable {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
namespace GlobalTheory.Cmp.WachMonoidal
theorem _root_.solution : UnitDualParts.SumFor W ↔ TensorLatticeUnitPart.SumAt W := by
  constructor
  · intro h T T' T'' i i' hT hT' hs
    obtain ⟨σ, h1, h2, h3, h4⟩ := h T T' T'' hT hT' i i' hs
    refine ⟨isCrys_of_isSumLat i i' hT hT' hs, ?_, fun x y => ?_, fun g x y => ?_, fun z => ?_⟩
    · have : ⇑((W.map i).coprod (W.map i')) = σ := by
        funext p
        exact (h1 p.1 p.2).symm
      rw [this]
      exact σ.bijective
    · rw [← h1, ← h1, h2]
    · rw [← h1, ← h1, h3]
    · constructor
      · intro hz
        obtain ⟨⟨x, y⟩, rfl⟩ := σ.surjective z
        exact ⟨x, ((h4 x y).mp hz).1, y, ((h4 x y).mp hz).2, h1 x y⟩
      · rintro ⟨x, hx, y, hy, rfl⟩
        rw [← h1]
        exact (h4 x y).mpr ⟨hx, hy⟩
  · intro h T T' T'' hT hT' i i' hs
    obtain ⟨-, h1, h2, h3, h4⟩ := h T T' T'' i i' hT hT' hs
    refine ⟨LinearEquiv.ofBijective _ h1, fun x y => rfl, h2, h3, fun x y => ?_⟩
    refine (h4 _).trans ⟨?_, fun h => ⟨x, h.1, y, h.2, rfl⟩⟩
    rintro ⟨x', hx', y', hy', hxy⟩
    have : (x, y) = (x', y') := h1.1 hxy
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj this
    exact ⟨hx', hy'⟩
end GlobalTheory.Cmp.WachMonoidal
