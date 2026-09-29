-- Prove2me | solution 1 for HeckeEis.binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/a1f2509f-1d70-5f33-be78-8e47a990f76a

import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj

set_option autoImplicit false

namespace HeckeEis
p2m_export "HeckeEis" "heckeConjMat heckeUpper mem_heckeUpper heckeConjSL coe_heckeConjSL heckeConj binarySubst binarySubst_mul binaryFormRepSL binaryFormAlphaAdj"
p2m_open "HeckeEis"

open CongruenceSubgroup
open scoped MatrixGroups

theorem alphaAdjMat_mul_heckeConjMat {ℓ : ℕ} {g : Matrix (Fin 2) (Fin 2) ℤ} (hg : (ℓ : ℤ) ∣ g 0 1) :
    !![(ℓ : ℤ), 0; 0, 1] * heckeConjMat ℓ g = g * !![(ℓ : ℤ), 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, heckeConjMat, Int.mul_ediv_cancel' hg, mul_comm]

theorem SolMain.A1 (K : Type*) [CommRing K] (n N ℓ : ℕ) [NeZero ℓ]
    (u : ↥(heckeUpper N ℓ)) :
    binaryFormAlphaAdj K n ℓ ∘ₗ ((binaryFormRepSL K n).comp (Gamma0 N).subtype) (heckeConj N ℓ u)
      = ((binaryFormRepSL K n).comp (Gamma0 N).subtype) (u : Gamma0 N) ∘ₗ binaryFormAlphaAdj K n ℓ := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  change binarySubst K !![(ℓ : ℤ), 0; 0, 1]
      (binarySubst K ((heckeConjSL N ℓ u : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (v : MvPolynomial (Fin 2) K))
    = binarySubst K ((((u : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
      (binarySubst K !![(ℓ : ℤ), 0; 0, 1] (v : MvPolynomial (Fin 2) K))
  rw [← AlgHom.comp_apply, ← binarySubst_mul, ← AlgHom.comp_apply, ← binarySubst_mul, coe_heckeConjSL,
    alphaAdjMat_mul_heckeConjMat ((mem_heckeUpper N ℓ).mp u.2)]

end HeckeEis

open scoped MatrixGroups in
theorem solution (K : Type*) [CommRing K] (n N ℓ : ℕ) [NeZero ℓ]
    (u : ↥(HeckeEis.heckeUpper N ℓ)) :
    HeckeEis.binaryFormAlphaAdj K n ℓ ∘ₗ ((HeckeEis.binaryFormRepSL K n).comp (CongruenceSubgroup.Gamma0 N).subtype) (HeckeEis.heckeConj N ℓ u)
      = ((HeckeEis.binaryFormRepSL K n).comp (CongruenceSubgroup.Gamma0 N).subtype) (u : CongruenceSubgroup.Gamma0 N)
          ∘ₗ HeckeEis.binaryFormAlphaAdj K n ℓ :=
  HeckeEis.SolMain.A1 K n N ℓ u

#print axioms solution

end S_HeckeEis_binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj
end P2MW
export P2MW.S_HeckeEis_binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj (solution)
