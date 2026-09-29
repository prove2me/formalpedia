-- Prove2me | solution 1 for LocalNewvector.gl2CongruenceSubgroup_le_padicK1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/3e24410c-dfcd-51a0-9b02-94437f4a9cf6

import Definitions.Def_LocalNewvector_ConductorDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LocalNewvector_gl2CongruenceSubgroup_le_padicK1

set_option autoImplicit false

noncomputable section

namespace LocalNewvector
p2m_export "LocalNewvector" "HasFiniteLevelFixed congruenceK1_le_congruenceK0 padicK0 padicK1"
p2m_open "LocalNewvector"

open FLT.SmoothVectors

variable (p : ℕ) [Fact p.Prime]

private theorem padicRadius_le_one (n : ℕ) : (p : ℝ) ^ (-(n : ℤ)) ≤ 1 := by
  refine zpow_le_one_of_nonpos₀ ?_ (neg_nonpos.mpr (Nat.cast_nonneg n))
  exact_mod_cast (Fact.out : p.Prime).one_le

variable {n : ℕ}

private def principalMat {g : GL (Fin 2) ℚ_[p]}
    (hg : g ∈ gl2CongruenceSubgroup p n) : Matrix (Fin 2) (Fin 2) ℤ_[p] :=
  fun i j => ⟨(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j,
    (norm_sub_one_entry_le_one_iff p).mp ((hg.1 i j).trans (padicRadius_le_one p n))⟩

private theorem coe_principalMat_apply {g : GL (Fin 2) ℚ_[p]}
    (hg : g ∈ gl2CongruenceSubgroup p n) (i j : Fin 2) :
    ((principalMat p hg i j : ℤ_[p]) : ℚ_[p])
      = (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j :=
  rfl

private theorem mapMatrix_principalMat {g : GL (Fin 2) ℚ_[p]}
    (hg : g ∈ gl2CongruenceSubgroup p n) :
    (algebraMap ℤ_[p] ℚ_[p]).mapMatrix (principalMat p hg)
      = (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) :=
  Matrix.ext fun i j => (PadicInt.algebraMap_apply _).trans (coe_principalMat_apply p hg i j)

private theorem mapMatrix_injective_padic :
    Function.Injective
      ((algebraMap ℤ_[p] ℚ_[p]).mapMatrix : Matrix (Fin 2) (Fin 2) ℤ_[p] → _) := by
  intro A B h
  ext i j
  have := congrFun (congrFun h i) j
  exact Subtype.coe_injective this

private def principalPreimage {g : GL (Fin 2) ℚ_[p]}
    (hg : g ∈ gl2CongruenceSubgroup p n) : GL (Fin 2) ℤ_[p] :=
  ⟨principalMat p hg, principalMat p (inv_mem hg),
    mapMatrix_injective_padic p (by
      rw [map_mul, mapMatrix_principalMat, mapMatrix_principalMat, map_one,
        ← Units.val_mul, mul_inv_cancel, Units.val_one]),
    mapMatrix_injective_padic p (by
      rw [map_mul, mapMatrix_principalMat, mapMatrix_principalMat, map_one,
        ← Units.val_mul, inv_mul_cancel, Units.val_one])⟩

private theorem coe_principalPreimage_apply {g : GL (Fin 2) ℚ_[p]}
    (hg : g ∈ gl2CongruenceSubgroup p n) (i j : Fin 2) :
    ((principalPreimage p hg : Matrix (Fin 2) (Fin 2) ℤ_[p]) i j : ℚ_[p])
      = (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j :=
  rfl

private theorem map_principalPreimage {g : GL (Fin 2) ℚ_[p]}
    (hg : g ∈ gl2CongruenceSubgroup p n) :
    Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[p] ℚ_[p])
      (principalPreimage p hg) = g :=
  Units.ext (mapMatrix_principalMat p hg)

theorem gl2CongruenceSubgroup_le_padicK1_impl (n : ℕ) :
    gl2CongruenceSubgroup p n ≤ padicK1 p n := by
  intro g hg
  refine ⟨principalPreimage p hg, map_principalPreimage p hg, ?_, ?_⟩
  · rw [← PadicInt.norm_le_pow_iff_mem_span_pow]
    have h10 : ((g : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) 1 0
        = (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 := by
      simp [Matrix.sub_apply]
    have hnorm : ‖((principalPreimage p hg : Matrix (Fin 2) (Fin 2) ℤ_[p]) 1 0 : ℚ_[p])‖
        = ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0‖ :=
      congrArg _ (coe_principalPreimage_apply p hg 1 0)
    calc ‖(principalPreimage p hg : Matrix (Fin 2) (Fin 2) ℤ_[p]) 1 0‖
        = ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0‖ := hnorm
      _ = ‖((g : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) 1 0‖ := by rw [h10]
      _ ≤ (p : ℝ) ^ (-(n : ℤ)) := hg.1 1 0
  · rw [← PadicInt.norm_le_pow_iff_mem_span_pow]
    have h11 : ((g : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) 1 1
        = (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1 - 1 := by
      simp [Matrix.sub_apply]
    have hnorm :
        ‖((principalPreimage p hg : Matrix (Fin 2) (Fin 2) ℤ_[p]) 1 1 - 1 : ℤ_[p])‖
          = ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1 - 1‖ := by
      rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one,
        coe_principalPreimage_apply p hg 1 1]
    calc ‖(principalPreimage p hg : Matrix (Fin 2) (Fin 2) ℤ_[p]) 1 1 - 1‖
        = ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1 - 1‖ := hnorm
      _ = ‖((g : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) 1 1‖ := by rw [h11]
      _ ≤ (p : ℝ) ^ (-(n : ℤ)) := hg.1 1 1

theorem gl2CongruenceSubgroup_le_padicK0_impl (n : ℕ) :
    gl2CongruenceSubgroup p n ≤ padicK0 p n :=
  (gl2CongruenceSubgroup_le_padicK1_impl p n).trans (congruenceK1_le_congruenceK0 _ _)

#print axioms LocalNewvector.gl2CongruenceSubgroup_le_padicK1_impl

end LocalNewvector

theorem solution (p : ℕ) [Fact p.Prime] (n : ℕ) :
    FLT.SmoothVectors.gl2CongruenceSubgroup p n ≤ LocalNewvector.padicK1 p n :=
  LocalNewvector.gl2CongruenceSubgroup_le_padicK1_impl (p := p) n

end
end S_LocalNewvector_gl2CongruenceSubgroup_le_padicK1
end P2MW
export P2MW.S_LocalNewvector_gl2CongruenceSubgroup_le_padicK1 (solution)
