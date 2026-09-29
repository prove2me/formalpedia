-- Prove2me | solution 1 for HeckeEis.exists_coeffH1par_linearMap_coeffHeckeFun
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/424062d0-1ce2-5345-9953-29cf4d1db00e

import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology

import Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCocycles
import Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCoboundaries
import Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffParabolicCocycles
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_exists_coeffH1par_linearMap_coeffHeckeFun

set_option autoImplicit false

open scoped MatrixGroups

noncomputable section

namespace HeckeEis
p2m_export "HeckeEis" "heckeUpper heckeConj coeffCoboundaries coeffParabolicCocycles coeffH1par coeffH1parMk coeffHeckeFun coeffHeckeFun_apply coeffHeckeFun_mem_coeffCoboundaries coeffHeckeFun_mem_coeffParabolicCocycles"
namespace InducedHeckeSol
p2m_open "HeckeEis"

open CongruenceSubgroup
open scoped MatrixGroups

variable (N ℓ : ℕ) [NeZero ℓ] {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
variable (ρ : Representation K (Gamma0 N) V) (a : V →ₗ[K] V)

def coeffHeckeLin : (Gamma0 N → V) →ₗ[K] (Gamma0 N → V) where
  toFun := coeffHeckeFun N ℓ ρ a
  map_add' z w := by
    funext g
    simp only [coeffHeckeFun_apply, Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c z := by
    funext g
    simp only [coeffHeckeFun_apply, Pi.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum]

@[scoped simp] theorem coeffHeckeLin_apply (z : Gamma0 N → V) : coeffHeckeLin N ℓ ρ a z = coeffHeckeFun N ℓ ρ a z := rfl

variable {ρ a}

def parabolicHecke (ha : ∀ u : ↥(heckeUpper N ℓ), a ∘ₗ ρ (heckeConj N ℓ u) = ρ (u : Gamma0 N) ∘ₗ a) :
    ↥(coeffParabolicCocycles ρ) →ₗ[K] ↥(coeffParabolicCocycles ρ) :=
  (coeffHeckeLin N ℓ ρ a).restrict fun z hz => HeckeEis.coeffHeckeFun_mem_coeffParabolicCocycles N ℓ ρ a ha hz

theorem coe_parabolicHecke (ha : ∀ u : ↥(heckeUpper N ℓ), a ∘ₗ ρ (heckeConj N ℓ u) = ρ (u : Gamma0 N) ∘ₗ a)
    (z : ↥(coeffParabolicCocycles ρ)) :
    ((parabolicHecke N ℓ ha z : ↥(coeffParabolicCocycles ρ)) : Gamma0 N → V) = coeffHeckeFun N ℓ ρ a z := rfl

def heckeH1par (ha : ∀ u : ↥(heckeUpper N ℓ), a ∘ₗ ρ (heckeConj N ℓ u) = ρ (u : Gamma0 N) ∘ₗ a) :
    coeffH1par ρ →ₗ[K] coeffH1par ρ :=
  Submodule.mapQ ((coeffCoboundaries ρ).comap (coeffParabolicCocycles ρ).subtype)
    ((coeffCoboundaries ρ).comap (coeffParabolicCocycles ρ).subtype) (parabolicHecke N ℓ ha)
    (fun z hz => by
      show ((parabolicHecke N ℓ ha z : ↥(coeffParabolicCocycles ρ)) : Gamma0 N → V) ∈ coeffCoboundaries ρ
      rw [coe_parabolicHecke]
      exact HeckeEis.coeffHeckeFun_mem_coeffCoboundaries N ℓ ρ a ha hz)

theorem heckeH1par_mk (ha : ∀ u : ↥(heckeUpper N ℓ), a ∘ₗ ρ (heckeConj N ℓ u) = ρ (u : Gamma0 N) ∘ₗ a)
    (z : ↥(coeffParabolicCocycles ρ)) :
    heckeH1par N ℓ ha (coeffH1parMk ρ z) = coeffH1parMk ρ (parabolicHecke N ℓ ha z) :=
  rfl

end HeckeEis.InducedHeckeSol
p2m_reactivate "P2MW.S_HeckeEis_exists_coeffH1par_linearMap_coeffHeckeFun.HeckeEis P2MW.S_HeckeEis_exists_coeffH1par_linearMap_coeffHeckeFun.HeckeEis.InducedHeckeSol"
p2m_reactivate "P2MW.S_HeckeEis_exists_coeffH1par_linearMap_coeffHeckeFun.HeckeEis"

end
p2m_reactivate "P2MW.S_HeckeEis_exists_coeffH1par_linearMap_coeffHeckeFun.HeckeEis P2MW.S_HeckeEis_exists_coeffH1par_linearMap_coeffHeckeFun.HeckeEis.InducedHeckeSol"

open _root_.HeckeEis _root_.P2MW.S_HeckeEis_exists_coeffH1par_linearMap_coeffHeckeFun.HeckeEis HeckeEis.InducedHeckeSol CongruenceSubgroup in
theorem solution (N ℓ : ℕ) [NeZero ℓ]
    {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K (CongruenceSubgroup.Gamma0 N) V) (a : V →ₗ[K] V)
    (ha : ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
      a ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a) :
    ∃ T : HeckeEis.coeffH1par ρ →ₗ[K] HeckeEis.coeffH1par ρ,
      ∀ z : ↥(HeckeEis.coeffParabolicCocycles ρ), ∃ w : ↥(HeckeEis.coeffParabolicCocycles ρ),
        (w : CongruenceSubgroup.Gamma0 N → V) = HeckeEis.coeffHeckeFun N ℓ ρ a z ∧
          T (HeckeEis.coeffH1parMk ρ z) = HeckeEis.coeffH1parMk ρ w :=
  ⟨heckeH1par N ℓ ha, fun z => ⟨parabolicHecke N ℓ ha z, rfl, heckeH1par_mk N ℓ ha z⟩⟩

end S_HeckeEis_exists_coeffH1par_linearMap_coeffHeckeFun
end P2MW
export P2MW.S_HeckeEis_exists_coeffH1par_linearMap_coeffHeckeFun (solution)
