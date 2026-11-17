-- Prove2me | solution 1 for N25.unitAnalytic25_gammaH
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:49:29.211204+00:00
-- url     : https://prove2.me/submissions/82fdb732-6d69-491d-a7fb-00f90a0a8807

import Mathlib
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_N25_unitAnalytic25_gamma1
import Theorems.Thm_N25_unitAnalytic25_A7
import Theorems.Thm_N25_GammaH25_invariant_of_generators
import Definitions.Def_N25

set_option autoImplicit false

namespace N25

/-- Invariance under Gamma1 and the literal residue-seven generator proves
full GammaH invariance of every original unpowered Siegel ratio. -/
theorem _root_.solution
    (i : Fin 5) (A : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hA : A ∈ CohCarrier.GammaH 25 N25.H25) (τ : UpperHalfPlane) :
    unitAnalytic25 i (A • τ) = unitAnalytic25 i τ := by
  let B : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    ⟨!![7,5;25,18], by norm_num [Matrix.det_fin_two]⟩
  let T : CongruenceSubgroup.Gamma0 25 := ⟨B, by
    apply CongruenceSubgroup.Gamma0_mem.mpr
    change ((25 : ℤ) : ZMod 25) = 0
    decide⟩
  have hT : CohCarrier.gamma0Units 25 T = (ZMod.unitOfCoprime 7 (by decide))⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    apply Units.ext
    change (18 : ZMod 25)*7 = 1
    decide
  exact GammaH25_invariant_of_generators T hT (unitAnalytic25 i)
    (fun C hC z => unitAnalytic25_gamma1 i C hC z)
    (fun z => unitAnalytic25_A7 i z) A hA τ

end N25
