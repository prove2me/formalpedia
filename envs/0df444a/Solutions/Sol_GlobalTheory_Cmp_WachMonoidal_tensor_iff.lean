-- Prove2me | solution 1 for GlobalTheory.Cmp.WachMonoidal.tensor_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:48:54.349184+00:00
-- url     : https://prove2.me/submissions/6c73d051-1816-462e-9d23-e835ae020aa3

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorLatticeUnitPart
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_UnitDualParts
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersCompleteDVR
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitSumTensorDualOfWachMonoidal
import Theorems.Thm_GlobalTheory_Cmp_WachMonoidal_extMul_eq
import Theorems.Thm_GlobalTheory_Cmp_WachMonoidal_isTensorLat_curry
import Theorems.Thm_GlobalTheory_Cmp_WachMonoidal_isTensorLat_ofBijective
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_C
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_C
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_X



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
    TensorLatticeUnitPart.TensorAt W E ↔ UnitDualParts.TensorFor E ∧ TensorLatCrys PD LL O := by
  constructor
  · intro h
    refine ⟨fun T T' T'' hT hT' m hm => ?_, fun T T' T'' b hT hT' hb => (h T T' T'' b hT hT' hb).1⟩
    obtain ⟨hl, hb⟩ := isTensorLat_curry m hm
    obtain ⟨-, β, h1, h2, h3, h4, -, βN, h5, h6⟩ := h T T' T'' _ hT hT' hb
    refine ⟨β, fun x y => ?_, h2, h3, h4, LinearEquiv.ofBijective _ h6, fun x y => ?_⟩
    · rw [h1, ← extMul_eq, hl]
    · rw [← h5]
      simp
  · rintro ⟨h, hc⟩ T T' T'' b hT hT' hb
    obtain ⟨μ, h1, h2, h3, h4, ν, hν⟩ := h T T' T'' hT hT' _ (isTensorLat_ofBijective b hb)
    refine ⟨hc T T' T'' b hT hT' hb, μ, fun x y => ?_, h2, h3, h4, ?_,
      TensorProduct.curry ν.toLinearMap, fun x y => hν x y, ?_⟩
    · rw [h1, ← extMul_eq]
      rfl
    · apply le_antisymm
      · intro z hz
        obtain ⟨w, hw⟩ := ν.surjective ⟨z, hz⟩
        have hz' : z = ((ν w : ↥(W.N T'')) : W.DD T'') := by rw [hw]
        rw [hz']
        clear hw hz' hz
        induction w using TensorProduct.induction_on with
        | zero => simp
        | tmul x y => rw [hν]; exact Submodule.subset_span ⟨x, x.2, y, y.2, rfl⟩
        | add a b ha hb => rw [map_add, Submodule.coe_add]; exact Submodule.add_mem _ ha hb
      · rw [Submodule.span_le]
        rintro z ⟨x, hx, y, hy, rfl⟩
        have := hν ⟨x, hx⟩ ⟨y, hy⟩
        simp only at this
        rw [← this]
        exact (ν _).2
    · have : TensorProduct.lift (TensorProduct.curry ν.toLinearMap) = ν.toLinearMap := by
        ext x y; simp
      rw [this]
      exact ν.bijective
end GlobalTheory.Cmp.WachMonoidal
