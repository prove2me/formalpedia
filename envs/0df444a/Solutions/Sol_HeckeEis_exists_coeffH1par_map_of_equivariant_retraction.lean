-- Prove2me | solution 1 for HeckeEis.exists_coeffH1par_map_of_equivariant_retraction
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/d1d90c80-dc33-5c0f-8550-0c93a4138e71

import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_exists_coeffH1par_map_of_equivariant_retraction

set_option autoImplicit false

open scoped MatrixGroups

noncomputable section

namespace HeckeEis
p2m_export "HeckeEis" "coeffCocycles coeffCoboundaryMap_apply coeffCoboundaries coeffParabolicCocycles coeffH1par coeffH1parMk coeffH1parMk_surjective coeffHeckeFun coeffHeckeFun_apply"
p2m_open "HeckeEis"
namespace C2b

open CongruenceSubgroup

section General
variable {Γ : Subgroup SL(2, ℤ)} {K : Type*} [CommRing K]
  {V V' : Type*} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
  (ρ : Representation K Γ V) (ρ' : Representation K Γ V')
  (i : V →ₗ[K] V') (hi : ∀ g : Γ, i ∘ₗ ρ g = ρ' g ∘ₗ i)

def post (i : V →ₗ[K] V') : (Γ → V) →ₗ[K] (Γ → V') where
  toFun z := i ∘ z
  map_add' z w := by funext g; simp
  map_smul' c z := by funext g; simp

@[scoped simp] theorem post_apply (i : V →ₗ[K] V') (z : Γ → V) (g : Γ) : post (Γ := Γ) i z g = i (z g) := rfl

theorem coe_post (i : V →ₗ[K] V') (z : Γ → V) : (post (Γ := Γ) i z : Γ → V') = i ∘ z := rfl

include hi in
theorem hi_apply (g : Γ) (v : V) : i (ρ g v) = ρ' g (i v) := by
  have := LinearMap.congr_fun (hi g) v
  simpa using this

include hi in
theorem post_mem_coeffCocycles {z : Γ → V} (hz : z ∈ coeffCocycles ρ) : i ∘ z ∈ coeffCocycles ρ' := by
  intro g h
  simp only [Function.comp_apply, hz g h, map_add, hi_apply ρ ρ' i hi]

include hi in
theorem post_mem_range {γ : Γ} {v : V} (hv : v ∈ LinearMap.range (ρ γ - 1)) :
    i v ∈ LinearMap.range (ρ' γ - 1) := by
  obtain ⟨u, rfl⟩ := hv
  refine ⟨i u, ?_⟩
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, hi_apply ρ ρ' i hi]

include hi in
theorem post_mem_coeffParabolicCocycles {z : Γ → V} (hz : z ∈ coeffParabolicCocycles ρ) :
    i ∘ z ∈ coeffParabolicCocycles ρ' :=
  ⟨post_mem_coeffCocycles ρ ρ' i hi hz.1, fun γ hγ => post_mem_range ρ ρ' i hi (hz.2 γ hγ)⟩

include hi in
theorem post_mem_coeffCoboundaries {z : Γ → V} (hz : z ∈ coeffCoboundaries ρ) :
    i ∘ z ∈ coeffCoboundaries ρ' := by
  obtain ⟨v, rfl⟩ := hz
  refine ⟨i v, ?_⟩
  funext g
  simp only [coeffCoboundaryMap_apply, Function.comp_apply, map_sub, hi_apply ρ ρ' i hi]

def push : ↥(coeffParabolicCocycles ρ) →ₗ[K] ↥(coeffParabolicCocycles ρ') :=
  ((post i).comp (coeffParabolicCocycles ρ).subtype).codRestrict (coeffParabolicCocycles ρ')
    (fun z => post_mem_coeffParabolicCocycles ρ ρ' i hi z.2)

theorem coe_push (z : ↥(coeffParabolicCocycles ρ)) :
    ((push ρ ρ' i hi z : ↥(coeffParabolicCocycles ρ')) : Γ → V') = i ∘ (z : Γ → V) := rfl

theorem push_le :
    (coeffCoboundaries ρ).comap (coeffParabolicCocycles ρ).subtype ≤
      ((coeffCoboundaries ρ').comap (coeffParabolicCocycles ρ').subtype).comap (push ρ ρ' i hi) := by
  intro z hz
  simp only [Submodule.mem_comap, Submodule.coe_subtype] at hz ⊢
  rw [coe_push]
  exact post_mem_coeffCoboundaries ρ ρ' i hi hz

def mapH1par : coeffH1par ρ →ₗ[K] coeffH1par ρ' :=
  Submodule.mapQ _ _ (push ρ ρ' i hi) (push_le ρ ρ' i hi)

theorem mapH1par_mk (z : ↥(coeffParabolicCocycles ρ)) :
    mapH1par ρ ρ' i hi (coeffH1parMk ρ z) = coeffH1parMk ρ' (push ρ ρ' i hi z) := rfl

end General

section Hecke
variable (N : ℕ) {K : Type*} [CommRing K]
  {V V' : Type*} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
  (ρ : Representation K (Gamma0 N) V) (ρ' : Representation K (Gamma0 N) V')
  (i : V →ₗ[K] V') (hi : ∀ g : Gamma0 N, i ∘ₗ ρ g = ρ' g ∘ₗ i)

include hi in

theorem comp_coeffHeckeFun (ℓ : ℕ) [NeZero ℓ] (a : V →ₗ[K] V) (a' : V' →ₗ[K] V') (hia : i ∘ₗ a = a' ∘ₗ i)
    (z : Gamma0 N → V) :
    i ∘ coeffHeckeFun N ℓ ρ a z = coeffHeckeFun N ℓ ρ' a' (i ∘ z) := by
  have hia' : ∀ v, i (a v) = a' (i v) := fun v => by
    have := LinearMap.congr_fun hia v
    simpa using this
  funext g
  simp only [Function.comp_apply, coeffHeckeFun_apply, map_sum, hi_apply ρ ρ' i hi, hia']

end Hecke

end C2b
p2m_reactivate "P2MW.S_HeckeEis_exists_coeffH1par_map_of_equivariant_retraction.HeckeEis.C2b"
end HeckeEis
p2m_reactivate "P2MW.S_HeckeEis_exists_coeffH1par_map_of_equivariant_retraction.HeckeEis.C2b P2MW.S_HeckeEis_exists_coeffH1par_map_of_equivariant_retraction.HeckeEis"

end
p2m_reactivate "P2MW.S_HeckeEis_exists_coeffH1par_map_of_equivariant_retraction.HeckeEis.C2b P2MW.S_HeckeEis_exists_coeffH1par_map_of_equivariant_retraction.HeckeEis"

open _root_.HeckeEis _root_.P2MW.S_HeckeEis_exists_coeffH1par_map_of_equivariant_retraction.HeckeEis HeckeEis.C2b CongruenceSubgroup in
theorem solution
    (N : ℕ) (K : Type*) [CommRing K]
    {V V' : Type*} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    (ρ : Representation K (CongruenceSubgroup.Gamma0 N) V)
    (ρ' : Representation K (CongruenceSubgroup.Gamma0 N) V')
    (i : V →ₗ[K] V') (r : V' →ₗ[K] V)
    (hi : ∀ g : CongruenceSubgroup.Gamma0 N, i ∘ₗ ρ g = ρ' g ∘ₗ i)
    (hr : ∀ g : CongruenceSubgroup.Gamma0 N, r ∘ₗ ρ' g = ρ g ∘ₗ r)
    (hri : r ∘ₗ i = LinearMap.id) :
    ∃ (I : HeckeEis.coeffH1par ρ →ₗ[K] HeckeEis.coeffH1par ρ')
      (R : HeckeEis.coeffH1par ρ' →ₗ[K] HeckeEis.coeffH1par ρ),
      R ∘ₗ I = LinearMap.id ∧
      (∀ z : ↥(HeckeEis.coeffParabolicCocycles ρ),
        ∃ z' : ↥(HeckeEis.coeffParabolicCocycles ρ'),
          (z' : CongruenceSubgroup.Gamma0 N → V') = i ∘ (z : CongruenceSubgroup.Gamma0 N → V) ∧
          I (HeckeEis.coeffH1parMk ρ z) = HeckeEis.coeffH1parMk ρ' z') ∧
      (∀ z' : ↥(HeckeEis.coeffParabolicCocycles ρ'),
        ∃ z : ↥(HeckeEis.coeffParabolicCocycles ρ),
          (z : CongruenceSubgroup.Gamma0 N → V) = r ∘ (z' : CongruenceSubgroup.Gamma0 N → V') ∧
          R (HeckeEis.coeffH1parMk ρ' z') = HeckeEis.coeffH1parMk ρ z) ∧
      (∀ (ℓ : ℕ) [NeZero ℓ] (a : V →ₗ[K] V) (a' : V' →ₗ[K] V'), i ∘ₗ a = a' ∘ₗ i →
        ∀ (T : HeckeEis.coeffH1par ρ →ₗ[K] HeckeEis.coeffH1par ρ)
          (T' : HeckeEis.coeffH1par ρ' →ₗ[K] HeckeEis.coeffH1par ρ'),
          (∀ z : ↥(HeckeEis.coeffParabolicCocycles ρ),
            ∃ w : ↥(HeckeEis.coeffParabolicCocycles ρ),
              (w : CongruenceSubgroup.Gamma0 N → V) = HeckeEis.coeffHeckeFun N ℓ ρ a z ∧
              T (HeckeEis.coeffH1parMk ρ z) = HeckeEis.coeffH1parMk ρ w) →
          (∀ z' : ↥(HeckeEis.coeffParabolicCocycles ρ'),
            ∃ w' : ↥(HeckeEis.coeffParabolicCocycles ρ'),
              (w' : CongruenceSubgroup.Gamma0 N → V') = HeckeEis.coeffHeckeFun N ℓ ρ' a' z' ∧
              T' (HeckeEis.coeffH1parMk ρ' z') = HeckeEis.coeffH1parMk ρ' w') →
          T' ∘ₗ I = I ∘ₗ T) := by
  refine ⟨mapH1par ρ ρ' i hi, mapH1par ρ' ρ r hr, ?_, ?_, ?_, ?_⟩
  ·
    apply LinearMap.ext
    intro x
    obtain ⟨z, rfl⟩ := coeffH1parMk_surjective ρ x
    rw [LinearMap.comp_apply, mapH1par_mk, mapH1par_mk, LinearMap.id_apply]
    congr 1
    apply Subtype.ext
    rw [coe_push, coe_push]
    funext g
    have := LinearMap.congr_fun hri ((z : CongruenceSubgroup.Gamma0 N → V) g)
    simpa using this
  · intro z
    exact ⟨push ρ ρ' i hi z, coe_push ρ ρ' i hi z, mapH1par_mk ρ ρ' i hi z⟩
  · intro z'
    exact ⟨push ρ' ρ r hr z', coe_push ρ' ρ r hr z', mapH1par_mk ρ' ρ r hr z'⟩
  · intro ℓ _ a a' hia T T' hT hT'
    apply LinearMap.ext
    intro x
    obtain ⟨z, rfl⟩ := coeffH1parMk_surjective ρ x
    obtain ⟨w, hw, hTw⟩ := hT z
    obtain ⟨w', hw', hT'w⟩ := hT' (push ρ ρ' i hi z)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hTw, mapH1par_mk, mapH1par_mk, hT'w]
    congr 1
    apply Subtype.ext
    rw [hw', coe_push, coe_push, hw]
    exact (comp_coeffHeckeFun N ρ ρ' i hi ℓ a a' hia z).symm

end S_HeckeEis_exists_coeffH1par_map_of_equivariant_retraction
end P2MW
export P2MW.S_HeckeEis_exists_coeffH1par_map_of_equivariant_retraction (solution)
