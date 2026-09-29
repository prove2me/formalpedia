-- Prove2me | solution 1 for HeckeEis.IsEichlerIntegral.smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/1997260b-bede-50d9-8b6e-c7c1edb15fe5

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_IsEichlerIntegral_smul

set_option autoImplicit false

noncomputable section

namespace HeckeEis
p2m_export "HeckeEis" "BinaryForm IsEichlerIntegral"
p2m_open "HeckeEis"

open UpperHalfPlane MvPolynomial CongruenceSubgroup
open scoped MatrixGroups ModularForm

theorem SolMain.smul {n : ℕ} {f : ℍ → ℂ} {F : ℍ → ↥(BinaryForm ℂ n)}
    (hF : IsEichlerIntegral n f F) (c : ℂ) :
    IsEichlerIntegral n (c • f) (c • F) := by
  intro d τ
  have h := (hF d τ).const_mul c
  rw [← mul_assoc] at h
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
  simp only [Pi.smul_apply, Submodule.coe_smul, coeff_smul, smul_eq_mul]

end HeckeEis

end

open scoped MatrixGroups ModularForm in
theorem solution {n : ℕ} {f : UpperHalfPlane → ℂ} {F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hF : HeckeEis.IsEichlerIntegral n f F) (c : ℂ) :
    HeckeEis.IsEichlerIntegral n (c • f) (c • F) :=
  HeckeEis.SolMain.smul hF c

#print axioms solution

end S_HeckeEis_IsEichlerIntegral_smul
end P2MW
export P2MW.S_HeckeEis_IsEichlerIntegral_smul (solution)
