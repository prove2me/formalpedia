-- Prove2me | solution 1 for HeckeEis.eichlerShimuraMap_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/4d19173a-6012-5772-91ac-1c1f519b9f58

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral
import Theorems.Thm_HeckeEis_exists_isEichlerIntegral_isParabolicCocycle
import Theorems.Thm_HeckeEis_eichlerShimuraMap_eq_coeffH1parMk
import Theorems.Thm_HeckeEis_IsEichlerIntegral_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_eichlerShimuraMap_smul

set_option autoImplicit false

noncomputable section

namespace HeckeEis
p2m_export "HeckeEis" "binaryFormRepSL IsParabolicCocycle IsEquivariantPrimitiveWith IsEichlerIntegral eichlerShimuraMap exists_isEichlerIntegral_isParabolicCocycle eichlerShimuraMap_eq_coeffH1parMk IsEichlerIntegral.smul"
p2m_open "HeckeEis"

open UpperHalfPlane MvPolynomial CongruenceSubgroup
open scoped MatrixGroups ModularForm

namespace EichlerLinAux

variable {K : Type*} [CommRing K] {Γ : Subgroup SL(2, ℤ)} {V : Type*} [AddCommGroup V] [Module K V]
  {ρ : Representation K Γ V} {F G : ℍ → V}

theorem add (hF : IsEquivariantPrimitiveWith ρ F) (hG : IsEquivariantPrimitiveWith ρ G) :
    IsEquivariantPrimitiveWith ρ (F + G) := fun γ =>
  ⟨hF.cocycle γ + hG.cocycle γ, fun τ => by
    rw [Pi.add_apply, Pi.add_apply, map_add, ← hF.sub_eq_cocycle γ τ, ← hG.sub_eq_cocycle γ τ]; abel⟩

theorem cocycle_add (hF : IsEquivariantPrimitiveWith ρ F) (hG : IsEquivariantPrimitiveWith ρ G) :
    (add hF hG).cocycle = hF.cocycle + hG.cocycle := by
  funext γ
  change (F + G) ((γ : SL(2, ℤ)) • I) - ρ γ ((F + G) I) = (F _ - ρ γ (F I)) + (G _ - ρ γ (G I))
  rw [Pi.add_apply, Pi.add_apply, map_add]
  abel

private theorem _root_.HeckeEis.EichlerLinAux.smul (hF : IsEquivariantPrimitiveWith ρ F) (c : K) :
    IsEquivariantPrimitiveWith ρ (c • F) := fun γ =>
  ⟨c • hF.cocycle γ, fun τ => by
    rw [Pi.smul_apply, Pi.smul_apply, map_smul, ← hF.sub_eq_cocycle γ τ, smul_sub]⟩

p2m_export "HeckeEis.EichlerLinAux" "smul"
theorem cocycle_smul (hF : IsEquivariantPrimitiveWith ρ F) (c : K) :
    (smul hF c).cocycle = c • hF.cocycle := by
  funext γ
  change (c • F) ((γ : SL(2, ℤ)) • I) - ρ γ ((c • F) I) = c • (F _ - ρ γ (F I))
  rw [Pi.smul_apply, Pi.smul_apply, map_smul, smul_sub]

end EichlerLinAux

open EichlerLinAux in

theorem SolMain.essmul (n N : ℕ) [NeZero N] (c : ℂ) (f : CuspForm (Gamma0 N) ((n : ℤ) + 2)) :
    eichlerShimuraMap n N ⇑(c • f) = c • eichlerShimuraMap n N f := by
  obtain ⟨F, hEF, hF, hpF⟩ := exists_isEichlerIntegral_isParabolicCocycle N n f

  have hEcF : IsEichlerIntegral n (⇑(c • f)) (c • F) := hEF.smul c
  have hpcF : IsParabolicCocycle ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) (smul hF c).cocycle := by
    intro γ hγ
    rw [cocycle_smul hF c, Pi.smul_apply]
    exact Submodule.smul_mem _ c (hpF γ hγ)
  rw [eichlerShimuraMap_eq_coeffH1parMk n N _ hEcF (smul hF c) hpcF,
    eichlerShimuraMap_eq_coeffH1parMk n N _ hEF hF hpF, ← map_smul]
  congr 1
  exact Subtype.ext (cocycle_smul hF c)

end HeckeEis

end

open scoped MatrixGroups ModularForm in
theorem solution (n N : ℕ) [NeZero N] (c : ℂ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2)) :
    HeckeEis.eichlerShimuraMap n N ⇑(c • f) = c • HeckeEis.eichlerShimuraMap n N f :=
  HeckeEis.SolMain.essmul n N c f

#print axioms solution

end S_HeckeEis_eichlerShimuraMap_smul
end P2MW
export P2MW.S_HeckeEis_eichlerShimuraMap_smul (solution)
