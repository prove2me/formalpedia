-- Prove2me | solution 1 for GlobalTheory.NL.Model.FilAt_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:03:46.124987+00:00
-- url     : https://prove2.me/submissions/731f4d2d-91d9-4d11-a377-41bb2a10de69

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NotFullBot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnramifiedSubfieldLeCyclotomicExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NL GlobalTheory.NL.Model
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.NL
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
open TensorProduct
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
namespace GlobalTheory.NL.Model
namespace _root_.GlobalTheory.NL.Model
theorem _root_.solution (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    _root_.GlobalTheory.NL.FilAt PD T τ (a + 1) ≤ _root_.GlobalTheory.NL.FilAt PD T τ a := by
  refine sup_le_sup_right ?_ _
  unfold _root_.Formalism.WeaklyAdmissibleFiltrations.FildR _root_.Formalism.WeaklyAdmissibleFiltrations.FilV
  refine inf_le_inf_left _ ?_
  rintro _ ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul w b => exact ⟨w ⊗ₜ ⟨b, PD.Fil_anti a b.2⟩, rfl⟩
  | add y z hy hz =>
    rw [map_add]
    exact Submodule.add_mem _ hy hz
end _root_.GlobalTheory.NL.Model
end GlobalTheory.NL.Model
