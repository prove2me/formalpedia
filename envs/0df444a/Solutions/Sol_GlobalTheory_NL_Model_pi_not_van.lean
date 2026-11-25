-- Prove2me | solution 1 for GlobalTheory.NL.Model.pi_not_van
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:02:50.382508+00:00
-- url     : https://prove2.me/submissions/aec0ff3e-9fcf-412a-b30c-408bcf4df84c

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
namespace GlobalTheory.NL.Model
theorem _root_.solution (W : LocWach PD LL O v n) (i : ZMod n) (ζ : LL) (j : ℕ)
    (hζ : IsPrimitiveRoot ζ (PD.p ^ j)) (h1 : ζ ≠ 1) : (letπ : LetA O n) ∉ van W i ζ 1 := by
  obtain ⟨E, h0, -, h2⟩ := W.lev_π i ζ ⟨j, hζ⟩
  rw [mem_van]
  intro h
  have h3 := h 0 (by omega)
  have h4 := congrArg (PowerSeries.coeff 0) h2
  rw [map_add, h3] at h4
  simp [h0] at h4
  exact h1 h4.symm
end GlobalTheory.NL.Model
