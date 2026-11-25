-- Prove2me | solution 1 for GroundTheory.PAdicHodge.NormTower.Fam.mul_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:30:02.204624+00:00
-- url     : https://prove2.me/submissions/17c2601c-b705-4c81-9b28-48b4b53d42e7

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsRing
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsField
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_Fam_toFrac_eq
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_Fam_equivFrac_mul
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_N_mul
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_mul
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_nonneg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.LocalField ValuativeRel Filter Topology
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] {p : ℕ}
open GroundTheory.PAdicHodge.NormTower
variable (t : NormTower K Ω p)
open GroundTheory.PAdicHodge.NormTower.Fam
variable {t}
namespace GroundTheory.PAdicHodge.NormTower.Fam
theorem _root_.solution (x y : t.Fam) (n : ℕ) : (x * y).1 n = x.1 n * y.1 n := by
  let xy : t.Fam := ⟨fun n ↦ x.1 n * y.1 n, fun n ↦ ⟨mul_mem (x.mem n) (y.mem n),
    by rw [t.N_mul, x.N_eq, y.N_eq]⟩⟩
  suffices h : x * y = xy by rw [h]
  apply (equivFrac t).injective
  rw [equivFrac_mul]
  obtain ⟨mx, hmx⟩ := exists_scale x
  obtain ⟨my, hmy⟩ := exists_scale y
  have hxy : t.value 0 ^ (mx + my) * nrm K (xy.1 0) ≤ 1 := by
    show t.value 0 ^ (mx + my) * nrm K (x.1 0 * y.1 0) ≤ 1
    rw [nrm_mul, pow_add]
    calc t.value 0 ^ mx * t.value 0 ^ my * (nrm K (x.1 0) * nrm K (y.1 0)) =
        (t.value 0 ^ mx * nrm K (x.1 0)) * (t.value 0 ^ my * nrm K (y.1 0)) := by ring
      _ ≤ 1 * 1 := mul_le_mul hmx hmy (mul_nonneg (pow_nonneg (t.value_pos 0).le _) (nrm_nonneg _))
          zero_le_one
      _ = 1 := one_mul 1
  show toFrac x * toFrac y = toFrac xy
  rw [toFrac_eq x mx hmx, toFrac_eq y my hmy, toFrac_eq xy (mx + my) hxy,
    ← IsLocalization.mk'_mul]
  congr 1
  · refine Subtype.ext (funext fun n ↦ ?_)
    change (Plus.unif t).1 n ^ mx * x.1 n * ((Plus.unif t).1 n ^ my * y.1 n) =
      (Plus.unif t).1 n ^ (mx + my) * (x.1 n * y.1 n)
    ring
  · exact Subtype.ext (pow_add _ _ _).symm
end GroundTheory.PAdicHodge.NormTower.Fam
