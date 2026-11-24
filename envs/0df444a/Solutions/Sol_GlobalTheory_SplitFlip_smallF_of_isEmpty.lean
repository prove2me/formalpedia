-- Prove2me | solution 1 for GlobalTheory.SplitFlip.smallF_of_isEmpty
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:05.845509+00:00
-- url     : https://prove2.me/submissions/f8984da1-fecf-489e-b454-d0882e6e8acc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Theorems.Thm_GlobalTheory_SplitFlip_haarVol_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A A' D : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
variable [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.SplitFlip
theorem _root_.solution [IsEmpty A'] (ν : kˣ →* ℂˣ) (Ψ : Matrix A' D k → ℂ) (Y : Matrix A' D k) :
    smallF (haarVol (KO k A')) ν Ψ Y = Ψ 0 := by
  have h1 : (KO k A' : Set (GL A' k)) = Set.univ :=
    Set.eq_univ_of_forall fun g => Subsingleton.elim 1 g ▸ one_mem _
  have h2 := haarVol_self (k := k) (n := A') isOpen_KO le_rfl
  rw [h1] at h2
  have h3 : ∀ g : GL A' k, gdet g = 1 := fun g => Subsingleton.elim 1 g ▸ map_one _
  have h4 : ∀ g : GL A' k, g.val * Y = 0 := fun g => by ext i; exact isEmptyElim i
  simp [smallF, h3, h4, Measure.real, h2]
end GlobalTheory.SplitFlip
