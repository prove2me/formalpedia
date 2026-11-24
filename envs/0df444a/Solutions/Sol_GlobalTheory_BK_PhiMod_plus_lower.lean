-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.plus_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:39:11.028801+00:00
-- url     : https://prove2.me/submissions/5296171c-a1c2-49d1-9841-d6cb55590be3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TameDescentExtendedActionExtraVector
import Theorems.Thm_GlobalTheory_BK_PhiMod_smul_mem_ext_of_basis
import Theorems.Thm_GlobalTheory_BK_PhiMod_bas_inl
import Theorems.Thm_GlobalTheory_BK_PhiMod_bas_inr
import Theorems.Thm_GlobalTheory_BK_Hom_app_mem_ext
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
theorem _root_.solution {n : ℕ} (h : ∀ v ∈ P.M, E K l e ^ n • v ∈ P.L) (hn : E K l e ^ n • y ∈ P.L) :
    ∀ v ∈ (P.plus hy).M, E K l e ^ n • v ∈ (P.plus hy).L := fun _ =>
  (P.plus hy).smul_mem_ext_of_basis (by
    rintro (i | ⟨⟨⟩⟩)
    · rw [P.bas_inl hy, ← map_smul]
      exact Hom.app_mem_ext _ le_rfl (h _ (P.bas_mem_M i))
    · rw [bas_inr, eq_sub_of_add_eq (P.phi_extension_generator_eq_add hy).symm, smul_sub,
        ← map_smul (P.plusInl hy).app, ← bas_inr]
      exact sub_mem ((P.plus hy).L.smul_mem (EIn l e (A O K) ^ n)
        ((P.plus hy).phi_mem_L ((P.plus hy).bas_mem_M _))) (Hom.app_mem_ext _ le_rfl hn)) le_rfl
end GlobalTheory.BK.PhiMod
