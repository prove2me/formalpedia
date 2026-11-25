-- Prove2me | solution 1 for GlobalTheory.NL.Model.pi_van_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:33:45.291568+00:00
-- url     : https://prove2.me/submissions/f33af0a5-aee7-46d3-b7f1-4b241255a956

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NotFullBot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnramifiedSubfieldLeCyclotomicExt
import Theorems.Thm_GlobalTheory_NL_Model_mem_van

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
theorem _root_.solution (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) (i : ZMod n) :
    (_root_.Formalism.BasicNotions.letπ : _root_.Formalism.BasicNotions.LetA O n) ∈ _root_.GlobalTheory.NL.van W i 1 1 ∧
      (_root_.Formalism.BasicNotions.letπ : _root_.Formalism.BasicNotions.LetA O n) ∉ _root_.GlobalTheory.NL.van W i 1 2 := by
  obtain ⟨E, h0, hd, hE⟩ := W.lev_π i 1 ⟨0, by simp⟩
  have hlev : W.lev i 1 _root_.Formalism.BasicNotions.letπ = E - 1 := by
    rw [map_one, one_mul] at hE
    rw [← hE]
    ring
  have h1 : PowerSeries.coeff 1 E = 1 := by
    have := congrArg (PowerSeries.coeff 0) hd
    simp only [PowerSeries.coeff_derivative] at this
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, h0] at this
    simpa using this
  simp only [_root_.GlobalTheory.NL.Model.mem_van, hlev]
  refine ⟨fun j hj => ?_, fun h => ?_⟩
  · obtain rfl : j = 0 := by omega
    simp [h0]
  · have := h 1 (by norm_num)
    simp [h1] at this
end _root_.GlobalTheory.NL.Model
end GlobalTheory.NL.Model
