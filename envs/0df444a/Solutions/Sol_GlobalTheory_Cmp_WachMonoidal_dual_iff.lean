-- Prove2me | solution 1 for GlobalTheory.Cmp.WachMonoidal.dual_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:02:11.507984+00:00
-- url     : https://prove2.me/submissions/a1f08888-4fc0-4e40-a516-65b83e380aaa

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorLatticeUnitPart
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_UnitDualParts
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersCompleteDVR
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitSumTensorDualOfWachMonoidal
import Theorems.Thm_GlobalTheory_Cmp_WachMonoidal_extPair_eq
import Theorems.Thm_GlobalTheory_Cmp_WachMonoidal_exists_dualEquiv

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
theorem _root_.solution (E : EtTie W RA RW inclR φR gR πA) :
    TensorLatticeUnitPart.DualAt W E ↔ UnitDualParts.DualFor E ∧ DualLatCrys PD LL O := by
  constructor
  · intro h
    refine ⟨fun T T' hT Pr hP => ?_, fun T T' Pr hT hP => (h T T' Pr hT hP).1⟩
    obtain ⟨-, PT, h0, β, h1, h2, h2', h3, h4, h5, h6⟩ := h T T' Pr hT hP
    refine ⟨PT, β, fun x y => (h0 x y).symm, fun x y => by rw [h1, extPair_eq], h2, h2', h3, h4, h5,
      exists_dualEquiv W.EE_inj _ _ β (fun y hy => (h5 y).mp hy) (fun y hy => ?_) h6⟩
    apply h2'.1
    rw [map_zero]
    exact (W.N_base T hT).algHom_ext _ _ fun x => hy x x.2
  · rintro ⟨h, hc⟩ T T' Pr hT hP
    obtain ⟨PT, β, h0, h1, h2, h2', h3, h4, h5, δ, hδ⟩ := h T T' hT Pr hP
    refine ⟨hc T T' Pr hT hP, PT, fun x y => (h0 x y).symm, β,
      fun x y => by rw [h1, extPair_eq], h2, h2', h3, h4, h5, fun f => ?_⟩
    obtain ⟨y, rfl⟩ := δ.surjective f
    exact ⟨y, y.2, fun x => hδ x y⟩
end GlobalTheory.Cmp.WachMonoidal
