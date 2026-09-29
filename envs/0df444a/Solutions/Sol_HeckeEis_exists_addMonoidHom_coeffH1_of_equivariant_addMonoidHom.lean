-- Prove2me | solution 1 for HeckeEis.exists_addMonoidHom_coeffH1_of_equivariant_addMonoidHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/94aee178-370d-517b-ac66-7e9e1f4fc133

import Mathlib
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_exists_addMonoidHom_coeffH1_of_equivariant_addMonoidHom

set_option autoImplicit false

open CongruenceSubgroup HeckeEis

namespace CCChi

section

variable (N : ℕ) {R : Type} [CommRing R] {κ : Type} [CommRing κ] (f : R →+* κ)
    {Λ : Type} [AddCommGroup Λ] [Module R Λ] {Λ' : Type} [AddCommGroup Λ'] [Module κ Λ']
    (ρR : Representation R (Gamma0 N) Λ) (ρ' : Representation κ (Gamma0 N) Λ')
    (red : Λ →+ Λ') (hreds : ∀ (c : R) (x : Λ), red (c • x) = f c • red x)
    (hredρ : ∀ (g : Gamma0 N) (x : Λ), red (ρR g x) = ρ' g (red x))

include hredρ in
theorem carry_mem_coeffCocycles {z : Gamma0 N → Λ} (hz : z ∈ coeffCocycles ρR) : (fun g => red (z g)) ∈ coeffCocycles ρ' := by
  rw [mem_coeffCocycles_iff] at hz ⊢
  intro g h
  rw [hz g h, map_add, hredρ]

include hredρ in
theorem carry_mem_coeffCoboundaries {z : Gamma0 N → Λ} (hz : z ∈ coeffCoboundaries ρR) :
    (fun g => red (z g)) ∈ coeffCoboundaries ρ' := by
  rw [mem_coeffCoboundaries_iff] at hz ⊢
  obtain ⟨v, rfl⟩ := hz
  exact ⟨red v, funext fun g => by simp only [map_sub, hredρ]⟩

def carryZ : ↥(coeffCocycles ρR) →+ ↥(coeffCocycles ρ') where
  toFun z := ⟨fun g => red ((z : Gamma0 N → Λ) g), carry_mem_coeffCocycles N ρR ρ' red hredρ z.2⟩
  map_zero' := by ext g; simp
  map_add' z w := by ext g; simp

@[scoped simp] theorem coe_carryZ (z : ↥(coeffCocycles ρR)) (g : Gamma0 N) :
    (carryZ N ρR ρ' red hredρ z : Gamma0 N → Λ') g = red ((z : Gamma0 N → Λ) g) := rfl

theorem exists_push : ∃ Φ : coeffH1 ρR →+ coeffH1 ρ', ∀ z, Φ (coeffH1Mk ρR z) = coeffH1Mk ρ' (carryZ N ρR ρ' red hredρ z) := by

  let F : ↥(coeffCocycles ρR) →+ coeffH1 ρ' := (coeffH1Mk ρ').toAddMonoidHom.comp (carryZ N ρR ρ' red hredρ)
  have hF : ∀ z : ↥(coeffCocycles ρR), coeffH1Mk ρR z = 0 → F z = 0 := by
    intro z hz
    rw [coeffH1Mk_eq_zero_iff] at hz
    show coeffH1Mk ρ' (carryZ N ρR ρ' red hredρ z) = 0
    rw [coeffH1Mk_eq_zero_iff]
    exact carry_mem_coeffCoboundaries N ρR ρ' red hredρ hz

  have hker : (coeffH1Mk ρR).toAddMonoidHom.ker ≤ F.ker := fun z hz => hF z hz
  let e := QuotientAddGroup.quotientKerEquivOfSurjective (coeffH1Mk ρR).toAddMonoidHom (coeffH1Mk_surjective ρR)
  let Φ : coeffH1 ρR →+ coeffH1 ρ' := (QuotientAddGroup.lift _ F hker).comp e.symm.toAddMonoidHom
  refine ⟨Φ, fun z => ?_⟩
  have h1 : e.symm (coeffH1Mk ρR z) = QuotientAddGroup.mk z := by
    rw [AddEquiv.symm_apply_eq]
    rfl
  show QuotientAddGroup.lift _ F hker (e.symm (coeffH1Mk ρR z)) = _
  rw [h1, QuotientAddGroup.lift_mk]
  rfl

include hredρ in

theorem carry_coeffHeckeFun (ℓ : ℕ) [NeZero ℓ] (a : Λ →ₗ[R] Λ) (a' : Λ' →ₗ[κ] Λ')
    (hreda : ∀ x, red (a x) = a' (red x)) (z : Gamma0 N → Λ) (g : Gamma0 N) :
    red (coeffHeckeFun N ℓ ρR a z g) = coeffHeckeFun N ℓ ρ' a' (fun g => red (z g)) g := by
  letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  rw [coeffHeckeFun_apply, coeffHeckeFun_apply, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hredρ, hreda]

end

theorem main
    (N : ℕ) {R : Type} [CommRing R] {κ : Type} [CommRing κ] (f : R →+* κ)
    {Λ : Type} [AddCommGroup Λ] [Module R Λ] {Λ' : Type} [AddCommGroup Λ'] [Module κ Λ']
    (ρR : Representation R (Gamma0 N) Λ) (ρ' : Representation κ (Gamma0 N) Λ')
    (red : Λ →+ Λ') (hreds : ∀ (c : R) (x : Λ), red (c • x) = f c • red x)
    (hredρ : ∀ (g : Gamma0 N) (x : Λ), red (ρR g x) = ρ' g (red x))
    (a : ℕ → (Λ →ₗ[R] Λ)) (a' : ℕ → (Λ' →ₗ[κ] Λ')) (hreda : ∀ (ℓ : ℕ) (x : Λ), red (a ℓ x) = a' ℓ (red x)) :
    ∃ Φ : HeckeEis.coeffH1 ρR →+ HeckeEis.coeffH1 ρ',
      (∀ z : ↥(HeckeEis.coeffCocycles ρR), ∃ w : ↥(HeckeEis.coeffCocycles ρ'),
        (∀ g : Gamma0 N, (w : Gamma0 N → Λ') g = red ((z : Gamma0 N → Λ) g)) ∧
          Φ (HeckeEis.coeffH1Mk ρR z) = HeckeEis.coeffH1Mk ρ' w) ∧
      (∀ (c : R) (x : HeckeEis.coeffH1 ρR), Φ (c • x) = f c • Φ x) ∧
      (∀ (ℓ : ℕ) [NeZero ℓ] (T : HeckeEis.coeffH1 ρR →ₗ[R] HeckeEis.coeffH1 ρR)
          (T' : HeckeEis.coeffH1 ρ' →ₗ[κ] HeckeEis.coeffH1 ρ'),
        HeckeEis.IsCoeffHeckeOnH1 N ℓ ρR (a ℓ) T → HeckeEis.IsCoeffHeckeOnH1 N ℓ ρ' (a' ℓ) T' →
          ∀ x : HeckeEis.coeffH1 ρR, Φ (T x) = T' (Φ x)) ∧
      ∀ ϖ : R, Function.Surjective red → (∀ x : Λ, red x = 0 ↔ ∃ y : Λ, x = ϖ • y) → (∀ x : Λ, ϖ • x = 0 → x = 0) →
        ∀ x : HeckeEis.coeffH1 ρR, Φ x = 0 ↔ ∃ y : HeckeEis.coeffH1 ρR, x = ϖ • y := by
  classical
  obtain ⟨Φ, hΦ⟩ := exists_push N ρR ρ' red hredρ
  refine ⟨Φ, fun z => ⟨carryZ N ρR ρ' red hredρ z, fun g => rfl, hΦ z⟩, ?_, ?_, ?_⟩
  ·
    intro c x
    obtain ⟨z, rfl⟩ := coeffH1Mk_surjective ρR x
    rw [← map_smul, hΦ, hΦ, ← map_smul]
    congr 1
    ext g
    simp [hreds]
  ·
    intro ℓ _ T T' hT hT' x
    obtain ⟨z, rfl⟩ := coeffH1Mk_surjective ρR x
    obtain ⟨w, hw, hTw⟩ := hT z
    obtain ⟨w', hw', hTw'⟩ := hT' (carryZ N ρR ρ' red hredρ z)
    rw [hTw, hΦ, hΦ, hTw']
    congr 1
    apply Subtype.ext
    funext g
    rw [coe_carryZ, hw, hw', carry_coeffHeckeFun N ρR ρ' red hredρ ℓ (a ℓ) (a' ℓ) (hreda ℓ)]
    rfl
  ·
    intro ϖ hsurj hker hnzd x
    obtain ⟨z, rfl⟩ := coeffH1Mk_surjective ρR x
    constructor
    · intro h0
      rw [hΦ, coeffH1Mk_eq_zero_iff, mem_coeffCoboundaries_iff] at h0
      obtain ⟨v', hv'⟩ := h0
      obtain ⟨v, rfl⟩ := hsurj v'

      have hvals : ∀ g, ∃ y : Λ, (z : Gamma0 N → Λ) g - (ρR g v - v) = ϖ • y := by
        intro g
        apply (hker _).mp
        have := congrFun hv' g
        simp only [coe_carryZ] at this
        rw [map_sub, ← this, map_sub, hredρ, sub_self]
      choose y hy using hvals
      have hyz : y ∈ coeffCocycles ρR := by
        rw [mem_coeffCocycles_iff]
        intro g h
        have key : ϖ • y (g * h) = ϖ • (y g + ρR g (y h)) := by
          rw [smul_add, ← LinearMap.map_smul, ← hy, ← hy, ← hy, (mem_coeffCocycles_iff ρR _).mp z.2 g h, map_mul,
            Module.End.mul_apply, map_sub, map_sub]
          abel
        have := hnzd (y (g * h) - (y g + ρR g (y h))) (by rw [smul_sub, key, sub_self])
        exact sub_eq_zero.mp this
      refine ⟨coeffH1Mk ρR ⟨y, hyz⟩, ?_⟩
      rw [← map_smul, ← sub_eq_zero, ← map_sub, coeffH1Mk_eq_zero_iff, mem_coeffCoboundaries_iff]
      refine ⟨v, funext fun g => ?_⟩
      have := hy g
      rw [sub_eq_iff_eq_add] at this
      show ρR g v - v = (z : Gamma0 N → Λ) g - ϖ • y g
      rw [this]
      abel
    · rintro ⟨y, hy⟩
      obtain ⟨zy, rfl⟩ := coeffH1Mk_surjective ρR y
      rw [hy, ← map_smul, hΦ, coeffH1Mk_eq_zero_iff]
      have h0 : carryZ N ρR ρ' red hredρ (ϖ • zy) = 0 := by
        ext g
        simp only [coe_carryZ, Submodule.coe_smul, Pi.smul_apply, ZeroMemClass.coe_zero, Pi.zero_apply]
        exact (hker _).mpr ⟨_, rfl⟩
      rw [h0]
      exact Submodule.zero_mem _

end CCChi
p2m_reactivate "P2MW.S_HeckeEis_exists_addMonoidHom_coeffH1_of_equivariant_addMonoidHom.CCChi"

theorem solution
    (N : ℕ) {R : Type} [CommRing R] {κ : Type} [CommRing κ] (f : R →+* κ)
    {Λ : Type} [AddCommGroup Λ] [Module R Λ] {Λ' : Type} [AddCommGroup Λ'] [Module κ Λ']
    (ρR : Representation R (Gamma0 N) Λ) (ρ' : Representation κ (Gamma0 N) Λ')
    (red : Λ →+ Λ') (hreds : ∀ (c : R) (x : Λ), red (c • x) = f c • red x)
    (hredρ : ∀ (g : Gamma0 N) (x : Λ), red (ρR g x) = ρ' g (red x))
    (a : ℕ → (Λ →ₗ[R] Λ)) (a' : ℕ → (Λ' →ₗ[κ] Λ')) (hreda : ∀ (ℓ : ℕ) (x : Λ), red (a ℓ x) = a' ℓ (red x)) :
    ∃ Φ : HeckeEis.coeffH1 ρR →+ HeckeEis.coeffH1 ρ',
      (∀ z : ↥(HeckeEis.coeffCocycles ρR), ∃ w : ↥(HeckeEis.coeffCocycles ρ'),
        (∀ g : Gamma0 N, (w : Gamma0 N → Λ') g = red ((z : Gamma0 N → Λ) g)) ∧
          Φ (HeckeEis.coeffH1Mk ρR z) = HeckeEis.coeffH1Mk ρ' w) ∧
      (∀ (c : R) (x : HeckeEis.coeffH1 ρR), Φ (c • x) = f c • Φ x) ∧
      (∀ (ℓ : ℕ) [NeZero ℓ] (T : HeckeEis.coeffH1 ρR →ₗ[R] HeckeEis.coeffH1 ρR)
          (T' : HeckeEis.coeffH1 ρ' →ₗ[κ] HeckeEis.coeffH1 ρ'),
        HeckeEis.IsCoeffHeckeOnH1 N ℓ ρR (a ℓ) T → HeckeEis.IsCoeffHeckeOnH1 N ℓ ρ' (a' ℓ) T' →
          ∀ x : HeckeEis.coeffH1 ρR, Φ (T x) = T' (Φ x)) ∧
      ∀ ϖ : R, Function.Surjective red → (∀ x : Λ, red x = 0 ↔ ∃ y : Λ, x = ϖ • y) → (∀ x : Λ, ϖ • x = 0 → x = 0) →
        ∀ x : HeckeEis.coeffH1 ρR, Φ x = 0 ↔ ∃ y : HeckeEis.coeffH1 ρR, x = ϖ • y :=
  CCChi.main N f ρR ρ' red hreds hredρ a a' hreda

end S_HeckeEis_exists_addMonoidHom_coeffH1_of_equivariant_addMonoidHom
end P2MW
export P2MW.S_HeckeEis_exists_addMonoidHom_coeffH1_of_equivariant_addMonoidHom (solution)
