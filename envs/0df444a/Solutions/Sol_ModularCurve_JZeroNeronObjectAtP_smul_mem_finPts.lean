-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.smul_mem_finPts
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/e4f2062a-4da1-5fe6-afa2-8e926df99dad

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_smul_mem_finPts

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_smul_mem_finPts.ModularCurve"

namespace ModularCurve p2m_export "ModularCurve" "JZeroNeronObjectAtP.LevelData JZeroNeronObjectAtP JZeroNeronObjectAtP.finPts heckeModuleBar JZero HeckeAlg" namespace JZeroNeronObjectAtP p2m_export "ModularCurve.JZeroNeronObjectAtP" "LevelData finPts hecke" end ModularCurve.JZeroNeronObjectAtP
p2m_open_scoped "ModularCurve ModularCurve.JZeroNeronObjectAtP" in

theorem ModularCurve.JZeroNeronObjectAtP.smul_mem_finPts'
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) (hm : 0 < m) :
    letI := heckeModuleBar (N₀ * p)
    ∀ (t : HeckeAlg), ∀ x ∈ O.finPts m, t • x ∈ O.finPts m := by
  letI := heckeModuleBar (N₀ * p)
  intro t x hx
  let T : JZero (N₀ * p) →+ JZero (N₀ * p) := DistribSMul.toAddMonoidHom (JZero (N₀ * p)) t
  have hT : ∀ y, T y = t • y := fun _ => rfl

  suffices h : O.finPts m ≤ (O.finPts m).comap T by
    have := h hx; rwa [AddSubgroup.mem_comap, hT] at this
  rw [JZeroNeronObjectAtP.finPts, AddSubgroup.closure_le]
  rintro y ⟨hy, ⟨s, hs⟩⟩
  rw [SetLike.mem_coe, AddSubgroup.mem_comap, hT]
  apply AddSubgroup.subset_closure
  obtain ⟨φ, -, hφ⟩ := O.hecke t
  refine ⟨?_, ⟨NeronModelInfra.schemeHomOverComp s φ, ?_⟩⟩
  ·
    change t • y ∈ (Submodule.torsionBy ℤ (JZero (N₀ * p)) (m : ℤ)).toAddSubgroup
    change y ∈ (Submodule.torsionBy ℤ (JZero (N₀ * p)) (m : ℤ)).toAddSubgroup at hy
    rw [Submodule.mem_toAddSubgroup, Submodule.mem_torsionBy_iff] at hy ⊢
    rw [smul_comm, hy, smul_zero]
  ·
    rw [hφ y, hs, NeronModelInfra.schemeHomOverComp_coe, Category.assoc]

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) (hm : 0 < m) :
    letI := heckeModuleBar (N₀ * p)
    ∀ (t : HeckeAlg), ∀ x ∈ O.finPts m, t • x ∈ O.finPts m :=
  ModularCurve.JZeroNeronObjectAtP.smul_mem_finPts' N₀ p hpN₀ A hA Λ hΛ O m hm

end S_ModularCurve_JZeroNeronObjectAtP_smul_mem_finPts
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_smul_mem_finPts (solution)
