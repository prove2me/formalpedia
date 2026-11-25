-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.isExactTriple_plus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:37:52.252988+00:00
-- url     : https://prove2.me/submissions/1d7a6fcc-263e-4578-ad66-41b48e0bf4c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TameDescentExtendedActionExtraVector
import Theorems.Thm_GlobalTheory_BK_PhiMod_plusInl_app
import Theorems.Thm_GlobalTheory_BK_PhiMod_plusProj_app
import Theorems.Thm_GlobalTheory_BK_mem_tot


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype μ] [DecidableEq μ] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
  [TameDescentExponentData K l e a]
open GlobalTheory.BK.PhiMod
omit [NeZero a] [TameDescentExponentData K l e a]
variable (P : PhiMod O K l e a ι)
variable {y : Vec K a ι} (hy : y ∈ P.Mext (invE l e (A O K)))
omit [NormedAlgebra ℚ_[l] K] [NeZero e]
namespace GlobalTheory.BK.PhiMod
theorem _root_.solution [NormedAlgebra ℚ_[l] K] [NeZero e] :
    IsExactTriple (P.plusInl hy) (P.plusProj hy) where
  inj v _ h := by
    rw [plusInl_app] at h
    exact funext fun τ => funext fun i => congrFun (congrFun h τ) (.inl i)
  exact v hv := by
    rw [← join_eta v, plusProj_app]
    constructor
    · intro h
      refine ⟨fun τ i => v τ (.inl i), mem_tot.2 fun τ i => mem_tot.1 hv τ (.inl i), ?_⟩
      refine (P.plusInl_app hy _).trans (congrArg _ ?_)
      exact funext fun τ => (congrFun (congrFun h τ) ()).symm
    · rintro ⟨w, -, hw⟩
      have := (P.plusInl_app hy w).symm.trans hw
      exact funext fun τ => funext fun _ => (congrFun (congrFun this τ) (.inr ())).symm
  finiteLength := by
    have : Subsingleton (P.plusProj hy).coker := Submodule.Quotient.subsingleton_iff.2 <|
      eq_top_iff.2 fun v _ => ⟨join 0 fun τ => v.1 τ (), (P.join_mem_Mext hy).2
        ⟨zero_mem _, fun τ => mem_tot.1 v.2 τ ()⟩, P.plusProj_app hy _ _⟩
    exact .of_subsingleton
end GlobalTheory.BK.PhiMod
