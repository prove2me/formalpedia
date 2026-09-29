-- Prove2me | solution 1 for LanglandsTunnell.P2.Artin.eq_finprod_artinFrob_pow_placeOrd_of_isAdjuster_one_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/2c0ba733-babc-5112-b88f-714cdb40a2fc

import Mathlib
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Theorems.Thm_HeckeCharacter_exists_isAdjuster
import Theorems.Thm_HeckeCharacter_count_coe_fadContentHom
import Theorems.Thm_HeckeCharacter_fadContentHom_mem_coprimeToModulus_iff
import Theorems.Thm_LanglandsTunnell_P2_Artin_artinSymbol_fadContentHom
import Theorems.Thm_LanglandsTunnell_P2_Artin_mem_unitIdeles_of_placeOrd_eq_zero_of_isAdjuster_one
import Theorems.Thm_HeckeCharacter_exists_isAdjuster_one_and_fadContentHom_projFin_eq
import Theorems.Thm_HeckeCharacter_fadContentHom_projFin_mem_coprimeToModulus_of_isAdjuster_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_P2_Artin_eq_finprod_artinFrob_pow_placeOrd_of_isAdjuster_one_of_dvd

set_option autoImplicit false
set_option maxHeartbeats 3200000
open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin M4aHerbrand
open scoped nonZeroDivisors IsMulCommutative

namespace B1Aux

variable (K : Type*) [Field K] [NumberField K]

noncomputable abbrev pr (α : Kˣ) : (AdeleRing (𝓞 K) K)ˣ :=
  Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) α

theorem pr_mul (α β : Kˣ) : pr K (α * β) = pr K α * pr K β := map_mul _ _ _

theorem pr_inv (α : Kˣ) : pr K α⁻¹ = (pr K α)⁻¹ := map_inv _ _

theorem pr_one : pr K 1 = 1 := map_one _

theorem snd_pr (α : Kˣ) :
    (((pr K α : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K)
      = algebraMap K (FiniteAdeleRing (𝓞 K) K) (α : K) := rfl

theorem projFin_apply (u : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ((projFin K u : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v
      = ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v := rfl

def adjOne (𝔣 : Ideal (𝓞 K)) : Subgroup (AdeleRing (𝓞 K) K)ˣ where
  carrier := {u | (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      Valued.v (((projFin K u : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v) = 1 ∧
      Valued.v (((projFin K u : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v - 1)
        ≤ WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors : ℤ))) ∧
    ∀ τ : K →+* ℝ, archSign K τ u}
  one_mem' := ⟨fun v _ => by
      refine ⟨by rw [map_one, Units.val_one, fad_one_apply, map_one], ?_⟩
      rw [map_one, Units.val_one, fad_one_apply, sub_self, map_zero]; exact zero_le',
    fun τ => archSign_one K τ⟩
  mul_mem' {u u'} hu hu' := by
    refine ⟨fun v hv => ?_, fun τ => (archSign_mul K τ u u').mpr (iff_of_true (hu.2 τ) (hu'.2 τ))⟩
    rw [map_mul, Units.val_mul, fad_mul_apply]
    exact unit_cong_mul K (hu.1 v hv).1 (hu.1 v hv).2 (hu'.1 v hv).1 (hu'.1 v hv).2
  inv_mem' {u} hu := by
    refine ⟨fun v hv => ?_, fun τ => (archSign_inv K τ u).mpr (hu.2 τ)⟩
    rw [map_inv, fad_units_inv_apply]
    refine ⟨by rw [map_inv₀, (hu.1 v hv).1, inv_one], ?_⟩
    have h := unit_cong_div K (a := (1 : v.adicCompletion K)) (by rw [sub_self, map_zero]; exact zero_le')
      (hu.1 v hv).1 (hu.1 v hv).2
    rwa [one_mul] at h

variable {K}

theorem mem_adjOne_iff {𝔣 : Ideal (𝓞 K)} {u : (AdeleRing (𝓞 K) K)ˣ} :
    u ∈ adjOne K 𝔣 ↔ (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      Valued.v (((projFin K u : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v) = 1 ∧
      Valued.v (((projFin K u : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v - 1)
        ≤ WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors : ℤ))) ∧
    ∀ τ : K →+* ℝ, archSign K τ u := Iff.rfl

theorem isAdjuster_iff_mem_adjOne {𝔣 : Ideal (𝓞 K)} {u : (AdeleRing (𝓞 K) K)ˣ} {α : Kˣ} :
    IsAdjuster K 𝔣 u α ↔ u * (pr K α)⁻¹ ∈ adjOne K 𝔣 :=
  ⟨fun h => ⟨h.cong, h.sign⟩, fun h => ⟨h.1, h.2⟩⟩

theorem isAdjuster_one_iff_mem_adjOne {𝔣 : Ideal (𝓞 K)} {u : (AdeleRing (𝓞 K) K)ˣ} :
    IsAdjuster K 𝔣 u 1 ↔ u ∈ adjOne K 𝔣 := by
  rw [isAdjuster_iff_mem_adjOne, show pr K 1 = 1 from map_one _, inv_one, mul_one]

theorem exp_neg_count_lt_one {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) {v : HeightOneSpectrum (𝓞 K)}
    (hv : v.asIdeal ∣ 𝔣) :
    WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors : ℤ)) < 1 := by
  have hne : (Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors ≠ 0 :=
    (Associates.count_ne_zero_iff_dvd h𝔣 v.irreducible).mpr hv
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

theorem valued_eq_one_of_sub_one_le {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) {v : HeightOneSpectrum (𝓞 K)}
    (hv : v.asIdeal ∣ 𝔣) {x : v.adicCompletion K}
    (hx : Valued.v (x - 1) ≤ WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors : ℤ))) :
    Valued.v x = 1 := by
  have hlt : Valued.v (x - 1) < 1 := lt_of_le_of_lt hx (exp_neg_count_lt_one h𝔣 hv)
  have h := Valuation.map_one_add_of_lt (Valued.v) hlt
  rwa [add_sub_cancel] at h

end B1Aux

namespace B1Aux
variable {K : Type*} [Field K] [NumberField K]

theorem adjOne_antitone {𝔣 𝔣' : Ideal (𝓞 K)} (h𝔣' : 𝔣' ≠ ⊥) (hdvd : 𝔣 ∣ 𝔣') :
    adjOne K 𝔣' ≤ adjOne K 𝔣 := by
  intro u hu
  refine ⟨fun v hv => ?_, hu.2⟩
  have hv' : v.asIdeal ∣ 𝔣' := dvd_trans hv hdvd
  refine ⟨(hu.1 v hv').1, (hu.1 v hv').2.trans ?_⟩
  rw [WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le]
  obtain ⟨c, hc⟩ := hdvd
  have h𝔣 : 𝔣 ≠ 0 := fun h => h𝔣' (by rw [hc, h, zero_mul]; rfl)
  have hc0 : c ≠ 0 := fun h => h𝔣' (by rw [hc, h, mul_zero]; rfl)
  rw [hc, ← Associates.mk_mul_mk, Associates.count_mul (Associates.mk_ne_zero.mpr h𝔣)
    (Associates.mk_ne_zero.mpr hc0) (Associates.irreducible_mk.mpr v.irreducible)]
  exact Nat.le_add_right _ _

end B1Aux

open B1Aux in
theorem solution
    (E F : Type*) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsMulCommutative (F ≃ₐ[E] F)]
    (𝔣 𝔣' : Ideal (𝓞 E)) (h𝔣' : 𝔣' ≠ ⊥) (hdvd : 𝔣 ∣ 𝔣')
    (hsupp : ∀ v : HeightOneSpectrum (𝓞 E), v.asIdeal ∣ 𝔣' → v.asIdeal ∣ 𝔣)
    (r : (AdeleRing (𝓞 E) E)ˣ →* (F ≃ₐ[E] F))
    (hprinc : M4aHerbrand.principalIdeles (𝓞 E) E ≤ r.ker) (hunits : unitIdeles E 𝔣 ≤ r.ker)
    (hiv' : ∀ u : (AdeleRing (𝓞 E) E)ˣ, IsAdjuster E 𝔣' u 1 →
      r u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E F v ^ placeOrd E (projFin E u) v)
    (u : (AdeleRing (𝓞 E) E)ˣ) (hu : IsAdjuster E 𝔣 u 1) :
    r u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E F v ^ placeOrd E (projFin E u) v := by
  classical
  have hanti := adjOne_antitone (K := E) h𝔣' hdvd

  let C : (AdeleRing (𝓞 E) E)ˣ →* (FractionalIdeal ((𝓞 E)⁰) E)ˣ := (fadContentHom E).comp (projFin E)
  have hC : ∀ y, C y = fadContentHom E (projFin E y) := fun _ => rfl
  have hcop : ∀ y : (AdeleRing (𝓞 E) E)ˣ, y ∈ adjOne E 𝔣 → C y ∈ coprimeToModulus E 𝔣 := fun y hy =>
    HeckeCharacter.fadContentHom_projFin_mem_coprimeToModulus_of_isAdjuster_one E 𝔣 y (isAdjuster_one_iff_mem_adjOne.mpr hy)
  have hT : ∀ (y : (AdeleRing (𝓞 E) E)ˣ) (hy : y ∈ adjOne E 𝔣),
      (∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E F v ^ placeOrd E (projFin E y) v)
        = artinSymbol E F 𝔣 ⟨C y, hcop y hy⟩ := fun y hy =>
    (LanglandsTunnell.P2.Artin.artinSymbol_fadContentHom E F 𝔣 y (hcop y hy)).symm

  obtain ⟨α, hα⟩ := HeckeCharacter.exists_isAdjuster E 𝔣' h𝔣' u
  have hu' : u * (pr E α)⁻¹ ∈ adjOne E 𝔣' := isAdjuster_iff_mem_adjOne.mp hα
  have hu'𝔣 : u * (pr E α)⁻¹ ∈ adjOne E 𝔣 := hanti hu'
  have hu𝔣 : u ∈ adjOne E 𝔣 := isAdjuster_one_iff_mem_adjOne.mp hu
  have hprα : pr E α ∈ adjOne E 𝔣 := by
    have h := Subgroup.mul_mem _ (Subgroup.inv_mem _ hu'𝔣) hu𝔣
    rwa [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one] at h

  have hru : r u = r (u * (pr E α)⁻¹) := by
    rw [map_mul, map_inv, show r (pr E α) = 1 from hprinc ⟨α, rfl⟩, inv_one, mul_one]

  have hcopα' : C (pr E α) ∈ coprimeToModulus E 𝔣' := by
    rw [hC, HeckeCharacter.fadContentHom_mem_coprimeToModulus_iff]
    intro w hw
    exact (placeOrd_eq_zero_iff E _ w).mpr ((hprα.1 w (hsupp w hw)).1)
  obtain ⟨x, hx1, -, hcx⟩ := HeckeCharacter.exists_isAdjuster_one_and_fadContentHom_projFin_eq E 𝔣' _ hcopα'
  have hx' : x ∈ adjOne E 𝔣' := isAdjuster_one_iff_mem_adjOne.mp hx1
  have hx : x ∈ adjOne E 𝔣 := hanti hx'

  have hz : pr E α * x⁻¹ ∈ adjOne E 𝔣 := Subgroup.mul_mem _ hprα (Subgroup.inv_mem _ hx)
  have hCz : C (pr E α * x⁻¹) = 1 := by
    rw [map_mul, map_inv, show C x = C (pr E α) from hcx, mul_inv_cancel]
  have hord : ∀ w : HeightOneSpectrum (𝓞 E), placeOrd E (projFin E (pr E α * x⁻¹)) w = 0 := by
    intro w
    rw [← HeckeCharacter.count_coe_fadContentHom, ← hC, hCz, Units.val_one, FractionalIdeal.count_one]
  have hzU := LanglandsTunnell.P2.Artin.mem_unitIdeles_of_placeOrd_eq_zero_of_isAdjuster_one E 𝔣 _ hord
    (isAdjuster_one_iff_mem_adjOne.mpr hz)
  have hrx : r x = 1 := by
    have h1 : r (pr E α) = 1 := hprinc ⟨α, rfl⟩
    have h2 : r (pr E α * x⁻¹) = 1 := hunits hzU
    rw [map_mul, map_inv, h1, one_mul, inv_eq_one] at h2
    exact h2
  have hstar : artinSymbol E F 𝔣 ⟨C (pr E α), hcop _ hprα⟩ = 1 := by
    rw [← hrx, hiv' x hx1, hT x hx]
    congr 1
    exact Subtype.ext hcx.symm

  rw [hru, hiv' _ (isAdjuster_one_iff_mem_adjOne.mpr hu'), hT _ hu'𝔣, hT _ hu𝔣]
  have e : (⟨C (u * (pr E α)⁻¹), hcop _ hu'𝔣⟩ : ↥(coprimeToModulus E 𝔣))
      = ⟨C u, hcop _ hu𝔣⟩ * (⟨C (pr E α), hcop _ hprα⟩)⁻¹ := by
    apply Subtype.ext
    show C (u * (pr E α)⁻¹) = C u * (C (pr E α))⁻¹
    rw [map_mul, map_inv]
  rw [e, map_mul, map_inv, hstar, inv_one, mul_one]

end S_LanglandsTunnell_P2_Artin_eq_finprod_artinFrob_pow_placeOrd_of_isAdjuster_one_of_dvd
end P2MW
export P2MW.S_LanglandsTunnell_P2_Artin_eq_finprod_artinFrob_pow_placeOrd_of_isAdjuster_one_of_dvd (solution)
