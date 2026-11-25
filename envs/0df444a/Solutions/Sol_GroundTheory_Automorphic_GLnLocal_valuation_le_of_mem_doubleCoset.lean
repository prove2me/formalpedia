-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.valuation_le_of_mem_doubleCoset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:06:36.089868+00:00
-- url     : https://prove2.me/submissions/e93c8136-b047-4aba-bb07-37b4c95f8c59

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_mem_iwahori_iff
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_valuation_uniformizer_pos
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_affineWeylGL_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Matrix DoubleCoset ValuativeRel
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)
local notation "ϖ" => ((uniformizer F : 𝒪[F]) : F)
namespace GroundTheory.Automorphic.GLnLocal
theorem _root_.solution {w w' : ExtendedAffineWeyl n}
    (h : affineWeylGL F n w' ∈ doubleCoset (affineWeylGL F n w) (iwahori F n) (iwahori F n))
    (c : Fin n) :
    valuation F ϖ ^ (w'.left (w'.right c)).toAdd ≤ valuation F ϖ ^ (w.left (w.right c)).toAdd ∧
      (w.right c < w'.right c →
        valuation F ϖ ^ (w'.left (w'.right c)).toAdd <
          valuation F ϖ ^ (w.left (w.right c)).toAdd) := by
  classical
  obtain ⟨x, hx, y, hy, hxy⟩ := mem_doubleCoset.mp h
  have hy' : y⁻¹ ∈ iwahori F n := (iwahori F n).inv_mem hy
  have hmat : (x : Matrix (Fin n) (Fin n) F) * (affineWeylGL F n w : Matrix (Fin n) (Fin n) F) =
      (affineWeylGL F n w' : Matrix (Fin n) (Fin n) F) *
        ((y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    rw [← Units.val_mul, ← Units.val_mul, hxy]
    congr 1
    group
  have hent := congrFun (congrFun hmat (w'.right c)) c
  rw [mul_apply, Fintype.sum_eq_single (w.right c), mul_apply,
    Fintype.sum_eq_single c] at hent
  rotate_left
  · intro l hl
    rw [affineWeylGL_apply, if_neg, zero_mul]
    exact fun e => hl (w'.right.injective e).symm
  · intro l hl
    rw [affineWeylGL_apply, if_neg, mul_zero]
    exact hl
  rw [affineWeylGL_apply, if_pos rfl, affineWeylGL_apply, if_pos rfl] at hent
  have hv := congrArg (valuation F) hent
  rw [map_mul, map_mul, map_zpow₀, map_zpow₀, ((mem_iwahori_iff F n).mp hy').2.2 c, mul_one] at hv
  obtain ⟨hx1, hx2, -⟩ := (mem_iwahori_iff F n).mp hx
  have hpos : 0 < valuation F ϖ ^ (w.left (w.right c)).toAdd :=
    zpow_pos (valuation_uniformizer_pos F) _
  refine ⟨?_, fun hlt => ?_⟩
  · rw [← hv]
    calc valuation F (x (w'.right c) (w.right c)) * valuation F ϖ ^ (w.left (w.right c)).toAdd
        ≤ 1 * valuation F ϖ ^ (w.left (w.right c)).toAdd := mul_le_mul_of_nonneg_right
          (hx1 _ _) hpos.le
      _ = _ := one_mul _
  · rw [← hv]
    calc valuation F (x (w'.right c) (w.right c)) * valuation F ϖ ^ (w.left (w.right c)).toAdd
        < 1 * valuation F ϖ ^ (w.left (w.right c)).toAdd := mul_lt_mul_of_pos_right
          (hx2 _ _ hlt) hpos
      _ = _ := one_mul _
end GroundTheory.Automorphic.GLnLocal
