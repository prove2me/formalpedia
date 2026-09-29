-- Prove2me | solution 1 for HeckeEis.IsEquivariantPrimitiveWith.cocycle_sub_cocycle_mem_coeffCoboundaries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/b1164faf-7cb9-5165-a40e-c88725ea7200

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_IsEquivariantPrimitiveWith_cocycle_sub_cocycle_mem_coeffCoboundaries

set_option autoImplicit false

noncomputable section

namespace HeckeEis
p2m_export "HeckeEis" "coeffCoboundaries mem_coeffCoboundaries_iff IsEquivariantPrimitiveWith"
p2m_open "HeckeEis"

open UpperHalfPlane MvPolynomial ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm

theorem SolMain.cob
    {K : Type*} [CommRing K] {Γ : Subgroup SL(2, ℤ)} {V : Type*} [AddCommGroup V] [Module K V]
    {ρ : Representation K Γ V} {F G : ℍ → V}
    (hF : IsEquivariantPrimitiveWith ρ F) (hG : IsEquivariantPrimitiveWith ρ G)
    {v : V} (h : ∀ τ : ℍ, F τ - G τ = v) :
    hF.cocycle - hG.cocycle ∈ coeffCoboundaries ρ := by
  rw [mem_coeffCoboundaries_iff]
  refine ⟨-v, funext fun γ => ?_⟩
  change ρ γ (-v) - -v = (F ((γ : SL(2, ℤ)) • I) - ρ γ (F I)) - (G ((γ : SL(2, ℤ)) • I) - ρ γ (G I))
  rw [map_neg, sub_eq_iff_eq_add.mp (h ((γ : SL(2, ℤ)) • I)), sub_eq_iff_eq_add.mp (h I), map_add]
  abel

end HeckeEis

end

open scoped MatrixGroups ModularForm in
theorem solution
    {K : Type*} [CommRing K] {Γ : Subgroup SL(2, ℤ)} {V : Type*} [AddCommGroup V] [Module K V]
    {ρ : Representation K Γ V} {F G : UpperHalfPlane → V}
    (hF : HeckeEis.IsEquivariantPrimitiveWith ρ F) (hG : HeckeEis.IsEquivariantPrimitiveWith ρ G)
    {v : V} (h : ∀ τ : UpperHalfPlane, F τ - G τ = v) :
    hF.cocycle - hG.cocycle ∈ HeckeEis.coeffCoboundaries ρ :=
  HeckeEis.SolMain.cob hF hG h

#print axioms solution

end S_HeckeEis_IsEquivariantPrimitiveWith_cocycle_sub_cocycle_mem_coeffCoboundaries
end P2MW
export P2MW.S_HeckeEis_IsEquivariantPrimitiveWith_cocycle_sub_cocycle_mem_coeffCoboundaries (solution)
