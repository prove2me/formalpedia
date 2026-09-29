-- Prove2me | solution 1 for LanglandsTunnell.exists_galoisTower_of_continuous_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/b3fe2855-426e-5e20-93ff-b1fe9ae84b1c

import Mathlib
import Definitions.Def_LanglandsTunnell_GalRep
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_galoisTower_of_continuous_surjective

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "galRep galRep_apply"
namespace P4
namespace TowerSol
p2m_open "LanglandsTunnell"

open scoped MatrixGroups

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
local notation "ℚbar" => AlgebraicClosure ℚ

variable (ρ : Γℚ →* GL (Fin 2) (ZMod 3))

theorem isClosed_ker (hcont : Continuous ρ) : IsClosed (ρ.ker : Set Γℚ) := by
  have : (ρ.ker : Set Γℚ) = ρ ⁻¹' {1} := by ext σ; exact MonoidHom.mem_ker
  rw [this]
  exact (isClosed_discrete _).preimage hcont

theorem isOpen_ker (hcont : Continuous ρ) : IsOpen (ρ.ker : Set Γℚ) := by
  have : (ρ.ker : Set Γℚ) = ρ ⁻¹' {1} := by ext σ; exact MonoidHom.mem_ker
  rw [this]
  exact (isOpen_discrete _).preimage hcont

def kerClosed (hcont : Continuous ρ) : ClosedSubgroup Γℚ := ⟨ρ.ker, isClosed_ker ρ hcont⟩

scoped instance kerClosed_normal (hcont : Continuous ρ) : (kerClosed ρ hcont).1.Normal :=
  inferInstanceAs ρ.ker.Normal

abbrev levelField (hcont : Continuous ρ) : IntermediateField ℚ ℚbar :=
  IntermediateField.fixedField (kerClosed ρ hcont).1

set_option backward.isDefEq.respectTransparency false in
theorem fixingSubgroup_levelField (hcont : Continuous ρ) :
    (levelField ρ hcont).fixingSubgroup = ρ.ker :=
  InfiniteGalois.fixingSubgroup_fixedField (kerClosed ρ hcont)

set_option backward.isDefEq.respectTransparency false in
theorem finiteDimensional_and_isGalois_levelField (hcont : Continuous ρ) :
    FiniteDimensional ℚ (levelField ρ hcont) ∧ IsGalois ℚ (levelField ρ hcont) := by
  rw [← InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois, fixingSubgroup_levelField]
  exact ⟨isOpen_ker ρ hcont, inferInstance⟩

scoped instance finiteDimensional_levelField (hcont : Continuous ρ) : FiniteDimensional ℚ (levelField ρ hcont) :=
  (finiteDimensional_and_isGalois_levelField ρ hcont).1

scoped instance isGalois_levelField (hcont : Continuous ρ) : IsGalois ℚ (levelField ρ hcont) :=
  (finiteDimensional_and_isGalois_levelField ρ hcont).2

scoped instance numberField_levelField (hcont : Continuous ρ) : NumberField (levelField ρ hcont) :=
  haveI : CharZero (levelField ρ hcont) := charZero_of_injective_algebraMap (algebraMap ℚ _).injective
  NumberField.mk

set_option backward.isDefEq.respectTransparency false in

def towerIso (hcont : Continuous ρ) (hsurj : Function.Surjective ρ) :
    ((levelField ρ hcont) ≃ₐ[ℚ] (levelField ρ hcont)) ≃* GL (Fin 2) (ZMod 3) :=
  (InfiniteGalois.normalAutEquivQuotient (kerClosed ρ hcont)).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective ρ hsurj)

set_option backward.isDefEq.respectTransparency false in

theorem galRep_towerIso (hcont : Continuous ρ) (hsurj : Function.Surjective ρ) :
    LanglandsTunnell.galRep (towerIso ρ hcont hsurj) = ρ := by
  ext1 σ
  rw [LanglandsTunnell.galRep_apply]
  show (QuotientGroup.quotientKerEquivOfSurjective ρ hsurj)
      ((InfiniteGalois.normalAutEquivQuotient (kerClosed ρ hcont)).symm
        (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) (levelField ρ hcont) σ)) = ρ σ
  rw [← InfiniteGalois.normalAutEquivQuotient_apply (kerClosed ρ hcont) σ, MulEquiv.symm_apply_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in

theorem exists_tower_of_continuous_surjective (hcont : Continuous ρ) (hsurj : Function.Surjective ρ) :
    ∃ (L : IntermediateField ℚ ℚbar) (_ : NumberField ↥L) (_ : IsGalois ℚ ↥L)
      (e : (↥L ≃ₐ[ℚ] ↥L) ≃* GL (Fin 2) (ZMod 3)), LanglandsTunnell.galRep e = ρ :=
  ⟨levelField ρ hcont, inferInstance, inferInstance, towerIso ρ hcont hsurj, galRep_towerIso ρ hcont hsurj⟩

end LanglandsTunnell.P4.TowerSol
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_galoisTower_of_continuous_surjective.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_galoisTower_of_continuous_surjective.LanglandsTunnell.P4 P2MW.S_LanglandsTunnell_exists_galoisTower_of_continuous_surjective.LanglandsTunnell.P4.TowerSol"
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_galoisTower_of_continuous_surjective.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_galoisTower_of_continuous_surjective.LanglandsTunnell.P4"
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_galoisTower_of_continuous_surjective.LanglandsTunnell"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_galoisTower_of_continuous_surjective.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_galoisTower_of_continuous_surjective.LanglandsTunnell.P4 P2MW.S_LanglandsTunnell_exists_galoisTower_of_continuous_surjective.LanglandsTunnell.P4.TowerSol"

set_option autoImplicit false

open scoped MatrixGroups

theorem solution
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) (ZMod 3))
    (hcont : Continuous ρ) (hsurj : Function.Surjective ρ) :
    ∃ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : NumberField ↥L) (_ : IsGalois ℚ ↥L)
      (e : (↥L ≃ₐ[ℚ] ↥L) ≃* GL (Fin 2) (ZMod 3)), LanglandsTunnell.galRep e = ρ :=
  LanglandsTunnell.P4.TowerSol.exists_tower_of_continuous_surjective ρ hcont hsurj

#print axioms solution

end S_LanglandsTunnell_exists_galoisTower_of_continuous_surjective
end P2MW
export P2MW.S_LanglandsTunnell_exists_galoisTower_of_continuous_surjective (solution)
