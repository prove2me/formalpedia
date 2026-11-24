-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.plus_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:39:00.042805+00:00
-- url     : https://prove2.me/submissions/dae991c3-d6a9-45cf-9b59-c3318136d608

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TameDescentExtendedActionExtraVector
import Theorems.Thm_GlobalTheory_BK_PhiMod_smul_mem_Mext_of_basis
import Theorems.Thm_GlobalTheory_BK_PhiMod_bas_inl
import Theorems.Thm_GlobalTheory_BK_PhiMod_bas_inr
import Theorems.Thm_GlobalTheory_BK_Hom_app_mem_M
import Theorems.Thm_GlobalTheory_BK_Hom_app_phi
import Theorems.Thm_GlobalTheory_BK_PhiMod_bas_mem_M
import Theorems.Thm_GlobalTheory_BK_PhiMod_phi_extension_generator_eq_add
import Theorems.Thm_GlobalTheory_BK_PhiMod_phi_mem_L


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
theorem _root_.solution {η : ℕ} (h : ∀ v ∈ P.L, E K l e ^ η • v ∈ P.M) (hη : y ∈ P.EM η) :
    ∀ v ∈ (P.plus hy).L, E K l e ^ η • v ∈ (P.plus hy).M := fun _ =>
  (P.plus hy).smul_mem_Mext_of_basis (by
    rintro (i | ⟨⟨⟩⟩)
    · rw [P.bas_inl hy, ← Hom.app_phi, ← map_smul]
      exact Hom.app_mem_M _ (h _ (P.phi_mem_L (P.bas_mem_M i)))
    · rw [bas_inr, phi_extension_generator_eq_add, smul_add, ← map_smul, ← bas_inr]
      exact add_mem ((P.plus hy).M.smul_mem (EIn l e (A O K) ^ η) ((P.plus hy).bas_mem_M _))
        (Hom.app_mem_M _ hη)) le_rfl
end GlobalTheory.BK.PhiMod
