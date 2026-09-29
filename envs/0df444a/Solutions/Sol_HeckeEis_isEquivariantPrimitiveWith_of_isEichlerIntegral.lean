-- Prove2me | solution 1 for HeckeEis.isEquivariantPrimitiveWith_of_isEichlerIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/bf4e4bdb-bcbc-5799-b4f4-d133245fc744

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral
import Theorems.Thm_HeckeEis_IsEichlerIntegral_slash
import Theorems.Thm_HeckeEis_IsEichlerIntegral_exists_sub_eq_const
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_isEquivariantPrimitiveWith_of_isEichlerIntegral

set_option autoImplicit false

noncomputable section

namespace HeckeEis
p2m_export "HeckeEis" "BinaryForm binaryFormRepSL IsEquivariantPrimitiveWith IsEichlerIntegral IsEichlerIntegral.slash IsEichlerIntegral.exists_sub_eq_const"
p2m_open "HeckeEis"

open UpperHalfPlane MvPolynomial ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm

theorem SolMain.p1b
    {n : ℕ} {Γ : Subgroup SL(2, ℤ)} {f : ℍ → ℂ} {F : ℍ → ↥(BinaryForm ℂ n)}
    (hF : IsEichlerIntegral n f F)
    (hf : ∀ γ ∈ Γ, (f ∣[((n : ℤ) + 2)] γ) = f) :
    IsEquivariantPrimitiveWith ((binaryFormRepSL ℂ n).comp Γ.subtype) F := by
  intro γ
  have hslash := hF.slash (γ : SL(2, ℤ))
  rw [hf _ γ.2] at hslash
  obtain ⟨v, hv⟩ := hslash.exists_sub_eq_const hF
  refine ⟨binaryFormRepSL ℂ n (γ : SL(2, ℤ)) v, fun τ => ?_⟩
  change F ((γ : SL(2, ℤ)) • τ) - binaryFormRepSL ℂ n (γ : SL(2, ℤ)) (F τ) = _
  rw [← hv τ, map_sub, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

end HeckeEis

end

open scoped MatrixGroups ModularForm in
theorem solution
    {n : ℕ} {Γ : Subgroup SL(2, ℤ)} {f : UpperHalfPlane → ℂ} {F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hF : HeckeEis.IsEichlerIntegral n f F)
    (hf : ∀ γ ∈ Γ, (f ∣[((n : ℤ) + 2)] γ) = f) :
    HeckeEis.IsEquivariantPrimitiveWith ((HeckeEis.binaryFormRepSL ℂ n).comp Γ.subtype) F :=
  HeckeEis.SolMain.p1b hF hf

#print axioms solution

end S_HeckeEis_isEquivariantPrimitiveWith_of_isEichlerIntegral
end P2MW
export P2MW.S_HeckeEis_isEquivariantPrimitiveWith_of_isEichlerIntegral (solution)
