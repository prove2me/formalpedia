-- Prove2me | solution 1 for LanglandsTunnell.P2.Artin.exists_mulEquiv_quotient_normRaySubgroup_apply_eq_contents_of_anchors
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/287b6a57-7285-578f-ad52-d05a92d9962d

import Mathlib
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Theorems.Thm_HeckeCharacter_exists_isAdjuster
import Theorems.Thm_HeckeCharacter_mem_iff_forall_valued_algebraMap_finiteAdeleRing_le
import Theorems.Thm_HeckeCharacter_archSign_unitsMap_algebraMap_mul_iff
import Theorems.Thm_HeckeCharacter_fracRelNormUnit_fadContentHom_projFin_unitsMap_algebraMap
import Theorems.Thm_HeckeCharacter_count_coe_fadContentHom
import Theorems.Thm_HeckeCharacter_coe_fadContentHom_projFin_unitsMap_algebraMap
import Theorems.Thm_LanglandsTunnell_P2_Artin_mem_unitIdeles_of_placeOrd_eq_zero_of_isAdjuster_one
import Theorems.Thm_HeckeCharacter_exists_isAdjuster_one_and_fadContentHom_projFin_eq
import Theorems.Thm_HeckeCharacter_fadContentHom_projFin_mem_coprimeToModulus_of_isAdjuster_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_P2_Artin_exists_mulEquiv_quotient_normRaySubgroup_apply_eq_contents_of_anchors

set_option autoImplicit false
set_option maxHeartbeats 3200000
open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors

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

theorem fad_sub_apply (a b : FiniteAdeleRing (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)) :
    ((a - b : FiniteAdeleRing (𝓞 K) K) v : v.adicCompletion K) = a v - b v := rfl

theorem valued_algebraMap_of_sub_one_mem {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) {β : 𝓞 K} (hβ1 : β - 1 ∈ 𝔣)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal ∣ 𝔣) :
    Valued.v ((algebraMap K (FiniteAdeleRing (𝓞 K) K) (β : K)) v) = 1 ∧
    Valued.v ((algebraMap K (FiniteAdeleRing (𝓞 K) K) (β : K)) v - 1)
      ≤ WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors : ℤ)) := by
  have h := (HeckeCharacter.mem_iff_forall_valued_algebraMap_finiteAdeleRing_le K 𝔣 h𝔣 (β - 1)).mp hβ1 v hv
  have e : (algebraMap K (FiniteAdeleRing (𝓞 K) K) ((β - 1 : 𝓞 K) : K)) v
      = (algebraMap K (FiniteAdeleRing (𝓞 K) K) (β : K)) v - 1 := by
    rw [show ((β - 1 : 𝓞 K) : K) = (β : K) - 1 by push_cast; ring, map_sub, map_one, fad_sub_apply, fad_one_apply]
  rw [e] at h
  exact ⟨valued_eq_one_of_sub_one_le h𝔣 hv h, h⟩

theorem principalUnit_mem_narrowRaySet {𝔣 : Ideal (𝓞 K)} {x : 𝓞 K} (hx : x ≠ 0) (hx1 : x - 1 ∈ 𝔣)
    (hpos : ∀ τ : K →+* ℝ, 0 < τ (algebraMap (𝓞 K) K x)) :
    principalUnit K x hx ∈ narrowRaySet K 𝔣 :=
  ⟨x, hx, hx1, hpos, principalUnit_val K x hx⟩

theorem fadContentHom_pr_mem_narrowRaySubgroup {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) (γ : Kˣ)
    (hγ : pr K γ ∈ adjOne K 𝔣) :
    fadContentHom K (projFin K (pr K γ)) ∈ narrowRaySubgroup K 𝔣 := by
  classical
  have hval : ((fadContentHom K (projFin K (pr K γ)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) :
      FractionalIdeal ((𝓞 K)⁰) K) = FractionalIdeal.spanSingleton (𝓞 K)⁰ (γ : K) :=
    HeckeCharacter.coe_fadContentHom_projFin_unitsMap_algebraMap K γ

  have hγv : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      Valued.v ((algebraMap K (FiniteAdeleRing (𝓞 K) K) (γ : K)) v) = 1 ∧
      Valued.v ((algebraMap K (FiniteAdeleRing (𝓞 K) K) (γ : K)) v - 1)
        ≤ WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors : ℤ)) := by
    intro v hv
    have h := hγ.1 v hv
    rw [projFin_apply, snd_pr] at h
    exact h

  have hcnt : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (γ : K)) = 0 := by
    intro v hv
    rw [← hval, HeckeCharacter.count_coe_fadContentHom, placeOrd_eq_zero_iff, projFin_apply, snd_pr]
    exact (hγv v hv).1

  obtain ⟨β, hβ0, hβ1, a, ha⟩ := movingLemma K h𝔣 (γ : K) γ.ne_zero hcnt
  have hβK : (algebraMap (𝓞 K) K β) ≠ 0 := (map_ne_zero_iff (algebraMap (𝓞 K) K) (IsFractionRing.injective (𝓞 K) K)).mpr hβ0
  have haK : (algebraMap (𝓞 K) K a) ≠ 0 := by rw [ha]; exact mul_ne_zero hβK γ.ne_zero
  have ha0 : a ≠ 0 := fun h => haK (by rw [h, map_zero])
  have hβv : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      Valued.v ((algebraMap K (FiniteAdeleRing (𝓞 K) K) (β : K)) v) = 1 ∧
      Valued.v ((algebraMap K (FiniteAdeleRing (𝓞 K) K) (β : K)) v - 1)
        ≤ WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors : ℤ)) :=
    fun v hv => valued_algebraMap_of_sub_one_mem h𝔣 hβ1 hv

  have hγpos : ∀ τ : K →+* ℝ, 0 < τ (γ : K) := by
    intro τ
    have h := HeckeCharacter.archSign_unitsMap_algebraMap_mul_iff K τ γ 1
    rw [mul_one] at h
    exact (h.mp (hγ.2 τ)).mpr (archSign_one K τ)
  have hτβ : ∀ τ : K →+* ℝ, τ (algebraMap (𝓞 K) K β) ≠ 0 := fun τ h => hβK (τ.injective (by rw [h, map_zero]))

  have h1 : principalUnit K (β ^ 2) (pow_ne_zero 2 hβ0) ∈ narrowRaySet K 𝔣 := by
    refine principalUnit_mem_narrowRaySet _ ?_ fun τ => ?_
    · have e : β ^ 2 - 1 = (β + 1) * (β - 1) := by ring
      rw [e]; exact Ideal.mul_mem_left _ _ hβ1
    · have hne := hτβ τ
      rw [map_pow, map_pow]
      positivity

  have hβa0 : β * a ≠ 0 := mul_ne_zero hβ0 ha0
  have h2 : principalUnit K (β * a) hβa0 ∈ narrowRaySet K 𝔣 := by
    refine principalUnit_mem_narrowRaySet _ ?_ fun τ => ?_
    ·
      refine (HeckeCharacter.mem_iff_forall_valued_algebraMap_finiteAdeleRing_le K 𝔣 h𝔣 (β * a - 1)).mpr fun v hv => ?_
      have e : (algebraMap K (FiniteAdeleRing (𝓞 K) K) ((β * a - 1 : 𝓞 K) : K)) v
          = (algebraMap K (FiniteAdeleRing (𝓞 K) K) (β : K)) v *
            ((algebraMap K (FiniteAdeleRing (𝓞 K) K) (β : K)) v *
              (algebraMap K (FiniteAdeleRing (𝓞 K) K) (γ : K)) v) - 1 := by
        have : ((β * a - 1 : 𝓞 K) : K) = (β : K) * ((β : K) * (γ : K)) - 1 := by
          rw [RingOfIntegers.coe_eq_algebraMap, map_sub, map_one, map_mul, ha, ← RingOfIntegers.coe_eq_algebraMap]
        rw [this, map_sub, map_one, fad_sub_apply, fad_one_apply, map_mul, map_mul, fad_mul_apply, fad_mul_apply]
      rw [e]
      exact (unit_cong_mul K (hβv v hv).1 (hβv v hv).2
        (unit_cong_mul K (hβv v hv).1 (hβv v hv).2 (hγv v hv).1 (hγv v hv).2).1
        (unit_cong_mul K (hβv v hv).1 (hβv v hv).2 (hγv v hv).1 (hγv v hv).2).2).2
    · have hne := hτβ τ
      have hγ' := hγpos τ
      rw [map_mul, map_mul, ha, map_mul]
      have hsq : 0 < τ (algebraMap (𝓞 K) K β) * τ (algebraMap (𝓞 K) K β) := mul_self_pos.mpr (hτβ τ)
      calc (0 : ℝ) < τ (algebraMap (𝓞 K) K β) * τ (algebraMap (𝓞 K) K β) * τ (γ : K) := mul_pos hsq hγ'
        _ = τ (algebraMap (𝓞 K) K β) * (τ (algebraMap (𝓞 K) K β) * τ (γ : K)) := by ring

  have h3 : fadContentHom K (projFin K (pr K γ))
      = principalUnit K (β * a) hβa0 * (principalUnit K (β ^ 2) (pow_ne_zero 2 hβ0))⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    apply Units.ext
    rw [Units.val_mul, hval, principalUnit_val, principalUnit_val, FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton]
    congr 1
    rw [map_pow, map_mul, ha]
    ring
  rw [h3]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure h2) (Subgroup.inv_mem _ (Subgroup.subset_closure h1))

end B1Aux

open B1Aux in
theorem solution
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
    (Nrm : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 K) K)ˣ)
    (hA1 : ∀ {u : (AdeleRing (𝓞 L) L)ˣ} {α : Lˣ},
      HeckeCharacter.IsAdjuster L (HeckeCharacter.modulusExt K L 𝔣) u α →
        HeckeCharacter.IsAdjuster K 𝔣 (Nrm u) (Units.map (Algebra.norm K) α))
    (hA2 : ∀ u : (AdeleRing (𝓞 L) L)ˣ,
      HeckeCharacter.fadContentHom K (HeckeCharacter.projFin K (Nrm u)) =
        HeckeCharacter.fracRelNormUnit K L
          (HeckeCharacter.fadContentHom L (HeckeCharacter.projFin L u)))
    (hA3 : LanglandsTunnell.P2.Artin.unitIdeles K 𝔣 ≤ Nrm.range) :
    ∃ φ : (AdeleRing (𝓞 K) K)ˣ ⧸ (M4aHerbrand.principalIdeles (𝓞 K) K ⊔ Nrm.range) ≃*
        ↥(Deep.NTSupply.coprimeToModulus K 𝔣) ⧸ LanglandsTunnell.P2.Artin.normRaySubgroup K L 𝔣,
      ∀ (u : (AdeleRing (𝓞 K) K)ˣ) (hu : HeckeCharacter.IsAdjuster K 𝔣 u 1)
        (hc : HeckeCharacter.fadContentHom K (HeckeCharacter.projFin K u) ∈
          Deep.NTSupply.coprimeToModulus K 𝔣),
        φ (QuotientGroup.mk u) =
          QuotientGroup.mk ⟨HeckeCharacter.fadContentHom K (HeckeCharacter.projFin K u), hc⟩ := by
  classical

  let C : (AdeleRing (𝓞 K) K)ˣ →* (FractionalIdeal ((𝓞 K)⁰) K)ˣ := (fadContentHom K).comp (projFin K)
  have hC : ∀ u, C u = fadContentHom K (projFin K u) := fun _ => rfl
  let CL : (AdeleRing (𝓞 L) L)ˣ →* (FractionalIdeal ((𝓞 L)⁰) L)ˣ := (fadContentHom L).comp (projFin L)
  have hCL : ∀ u, CL u = fadContentHom L (projFin L u) := fun _ => rfl
  let S : Subgroup (AdeleRing (𝓞 K) K)ˣ := M4aHerbrand.principalIdeles (𝓞 K) K ⊔ Nrm.range

  have h𝔣L : HeckeCharacter.modulusExt K L 𝔣 ≠ ⊥ := by
    show 𝔣.map (algebraMap (𝓞 K) (𝓞 L)) ≠ ⊥
    exact fun h => h𝔣 ((Ideal.map_eq_bot_iff_of_injective
      (LanglandsTunnell.P2.Artin.algebraMap_ringOfIntegers_injective K L)).mp h)

  have hcop : ∀ z : (AdeleRing (𝓞 K) K)ˣ, z ∈ adjOne K 𝔣 → C z ∈ coprimeToModulus K 𝔣 := fun z hz =>
    HeckeCharacter.fadContentHom_projFin_mem_coprimeToModulus_of_isAdjuster_one K 𝔣 z (isAdjuster_one_iff_mem_adjOne.mpr hz)
  have hcopL : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ adjOne L (HeckeCharacter.modulusExt K L 𝔣) →
      CL z ∈ coprimeToModulus L (HeckeCharacter.modulusExt K L 𝔣) := fun z hz =>
    HeckeCharacter.fadContentHom_projFin_mem_coprimeToModulus_of_isAdjuster_one L _ z (isAdjuster_one_iff_mem_adjOne.mpr hz)

  let cls : ∀ z : (AdeleRing (𝓞 K) K)ˣ, z ∈ adjOne K 𝔣 →
      ↥(coprimeToModulus K 𝔣) ⧸ normRaySubgroup K L 𝔣 := fun z hz => QuotientGroup.mk ⟨C z, hcop z hz⟩
  have hcls : ∀ z hz, cls z hz = QuotientGroup.mk ⟨C z, hcop z hz⟩ := fun _ _ => rfl

  have hcls_eq : ∀ (z z' : (AdeleRing (𝓞 K) K)ˣ) (hz : z ∈ adjOne K 𝔣) (hz' : z' ∈ adjOne K 𝔣) (γ : Kˣ),
      z⁻¹ * z' = pr K γ → cls z hz = cls z' hz' := by
    intro z z' hz hz' γ hγ
    show (QuotientGroup.mk ⟨C z, hcop z hz⟩ : ↥(coprimeToModulus K 𝔣) ⧸ normRaySubgroup K L 𝔣)
      = QuotientGroup.mk ⟨C z', hcop z' hz'⟩
    rw [QuotientGroup.eq]
    have hmem : pr K γ ∈ adjOne K 𝔣 := hγ ▸ Subgroup.mul_mem _ (Subgroup.inv_mem _ hz) hz'
    have hnr := fadContentHom_pr_mem_narrowRaySubgroup h𝔣 γ hmem
    have e : (⟨C z, hcop z hz⟩ : ↥(coprimeToModulus K 𝔣))⁻¹ * ⟨C z', hcop z' hz'⟩
        = ⟨C (pr K γ), hcop _ hmem⟩ := by
      apply Subtype.ext
      show (C z)⁻¹ * C z' = C (pr K γ)
      rw [← hγ, map_mul, map_inv]
    rw [e]
    exact Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mpr hnr)
  have hcls_mul : ∀ (z z' : (AdeleRing (𝓞 K) K)ˣ) (hz : z ∈ adjOne K 𝔣) (hz' : z' ∈ adjOne K 𝔣),
      cls (z * z') (Subgroup.mul_mem _ hz hz') = cls z hz * cls z' hz' := by
    intro z z' hz hz'
    show (QuotientGroup.mk ⟨C (z * z'), hcop _ (Subgroup.mul_mem _ hz hz')⟩ : ↥(coprimeToModulus K 𝔣) ⧸ normRaySubgroup K L 𝔣)
      = QuotientGroup.mk ⟨C z, hcop z hz⟩ * QuotientGroup.mk ⟨C z', hcop z' hz'⟩
    rw [← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (map_mul C z z')

  have hadj : ∀ u : (AdeleRing (𝓞 K) K)ˣ, ∃ α : Kˣ, u * (pr K α)⁻¹ ∈ adjOne K 𝔣 := fun u => by
    obtain ⟨α, hα⟩ := HeckeCharacter.exists_isAdjuster K 𝔣 h𝔣 u
    exact ⟨α, isAdjuster_iff_mem_adjOne.mp hα⟩
  let adj : (AdeleRing (𝓞 K) K)ˣ → Kˣ := fun u => (hadj u).choose
  have hadjm : ∀ u, u * (pr K (adj u))⁻¹ ∈ adjOne K 𝔣 := fun u => (hadj u).choose_spec
  let ψ₀ : (AdeleRing (𝓞 K) K)ˣ → ↥(coprimeToModulus K 𝔣) ⧸ normRaySubgroup K L 𝔣 :=
    fun u => cls (u * (pr K (adj u))⁻¹) (hadjm u)

  have hψ_eq : ∀ (u : (AdeleRing (𝓞 K) K)ˣ) (α' : Kˣ) (h' : u * (pr K α')⁻¹ ∈ adjOne K 𝔣),
      ψ₀ u = cls (u * (pr K α')⁻¹) h' := by
    intro u α' h'
    refine hcls_eq _ _ (hadjm u) h' (adj u * α'⁻¹) ?_
    rw [pr_mul, pr_inv]
    group
  have hψ_mul : ∀ u u', ψ₀ (u * u') = ψ₀ u * ψ₀ u' := by
    intro u u'
    have e : u * u' * (pr K (adj u * adj u'))⁻¹ = (u * (pr K (adj u))⁻¹) * (u' * (pr K (adj u'))⁻¹) := by
      rw [pr_mul, mul_inv, mul_mul_mul_comm]
    have h : u * u' * (pr K (adj u * adj u'))⁻¹ ∈ adjOne K 𝔣 := by
      rw [e]; exact Subgroup.mul_mem _ (hadjm u) (hadjm u')
    rw [hψ_eq (u * u') (adj u * adj u') h]
    have h2 : cls (u * u' * (pr K (adj u * adj u'))⁻¹) h
        = cls ((u * (pr K (adj u))⁻¹) * (u' * (pr K (adj u'))⁻¹)) (Subgroup.mul_mem _ (hadjm u) (hadjm u')) := by
      congr 1
    rw [h2]
    exact hcls_mul _ _ (hadjm u) (hadjm u')
  let ψ : (AdeleRing (𝓞 K) K)ˣ →* ↥(coprimeToModulus K 𝔣) ⧸ normRaySubgroup K L 𝔣 := MonoidHom.mk' ψ₀ hψ_mul
  have hψ : ∀ u, ψ u = ψ₀ u := fun _ => rfl

  have hψ_adj : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (hz : z ∈ adjOne K 𝔣), ψ z = cls z hz := by
    intro z hz
    have h1 : z * (pr K 1)⁻¹ ∈ adjOne K 𝔣 := by rw [pr_one, inv_one, mul_one]; exact hz
    rw [hψ, hψ_eq z 1 h1]
    congr 1
    rw [pr_one, inv_one, mul_one]

  have hker_pr : ∀ α : Kˣ, ψ (pr K α) = 1 := by
    intro α
    have h1 : pr K α * (pr K α)⁻¹ ∈ adjOne K 𝔣 := by rw [mul_inv_cancel]; exact Subgroup.one_mem _
    rw [hψ, hψ_eq (pr K α) α h1]
    have h2 : cls (pr K α * (pr K α)⁻¹) h1 = cls 1 (Subgroup.one_mem _) := by congr 1; exact mul_inv_cancel _
    rw [h2]
    simp only [hcls]
    have : (⟨C 1, hcop 1 (Subgroup.one_mem _)⟩ : ↥(coprimeToModulus K 𝔣)) = 1 := Subtype.ext (map_one C)
    rw [this, QuotientGroup.mk_one]

  have hNrm_adj : ∀ (w : (AdeleRing (𝓞 L) L)ˣ), w ∈ adjOne L (HeckeCharacter.modulusExt K L 𝔣) →
      Nrm w ∈ adjOne K 𝔣 := by
    intro w hw
    have h := hA1 (isAdjuster_one_iff_mem_adjOne.mpr hw)
    rw [map_one] at h
    exact isAdjuster_one_iff_mem_adjOne.mp h
  have hker_Nrm_adj : ∀ (w : (AdeleRing (𝓞 L) L)ˣ) (hw : w ∈ adjOne L (HeckeCharacter.modulusExt K L 𝔣)),
      ψ (Nrm w) = 1 := by
    intro w hw
    rw [hψ_adj (Nrm w) (hNrm_adj w hw)]
    simp only [hcls]
    have e : (⟨C (Nrm w), hcop _ (hNrm_adj w hw)⟩ : ↥(coprimeToModulus K 𝔣))
        = relNormCTM K L 𝔣 ⟨CL w, hcopL w hw⟩ := by
      apply Subtype.ext
      show C (Nrm w) = fracRelNormUnit K L (CL w)
      rw [hC, hA2, hCL]
    rw [e, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_sup_right ⟨_, rfl⟩
  have hker_Nrm_pr : ∀ β : Lˣ, ψ (Nrm (pr L β)) = 1 := by
    intro β
    have hadjβ : HeckeCharacter.IsAdjuster L (HeckeCharacter.modulusExt K L 𝔣) (pr L β) β := by
      rw [isAdjuster_iff_mem_adjOne, mul_inv_cancel]; exact Subgroup.one_mem _
    have h := isAdjuster_iff_mem_adjOne.mp (hA1 hadjβ)
    rw [hψ, hψ_eq _ _ h]
    simp only [hcls]
    have e : (⟨C (Nrm (pr L β) * (pr K (Units.map (Algebra.norm K : L →* K) β))⁻¹), hcop _ h⟩ : ↥(coprimeToModulus K 𝔣)) = 1 := by
      apply Subtype.ext
      show C (Nrm (pr L β) * (pr K (Units.map (Algebra.norm K : L →* K) β))⁻¹) = 1
      rw [map_mul, map_inv, hC, hA2, ← hCL,
        show CL (pr L β) = fadContentHom L (projFin L (pr L β)) from rfl,
        HeckeCharacter.fracRelNormUnit_fadContentHom_projFin_unitsMap_algebraMap, ← hC, mul_inv_cancel]
    rw [e, QuotientGroup.mk_one]
  have hker_Nrm : ∀ w : (AdeleRing (𝓞 L) L)ˣ, ψ (Nrm w) = 1 := by
    intro w
    obtain ⟨β, hβ⟩ := HeckeCharacter.exists_isAdjuster L (HeckeCharacter.modulusExt K L 𝔣) h𝔣L w
    have hw' := isAdjuster_iff_mem_adjOne.mp hβ
    have e : w = (w * (pr L β)⁻¹) * pr L β := by rw [inv_mul_cancel_right]
    rw [e, map_mul, map_mul, hker_Nrm_adj _ hw', hker_Nrm_pr]
    exact one_mul (1 : ↥(coprimeToModulus K 𝔣) ⧸ normRaySubgroup K L 𝔣)
  have hSker : S ≤ ψ.ker := by
    refine sup_le ?_ ?_
    · rintro _ ⟨α, rfl⟩
      exact hker_pr α
    · rintro _ ⟨w, rfl⟩
      exact hker_Nrm w

  let φ₀ : (AdeleRing (𝓞 K) K)ˣ ⧸ S →* ↥(coprimeToModulus K 𝔣) ⧸ normRaySubgroup K L 𝔣 := QuotientGroup.lift S ψ hSker
  have hφ₀ : ∀ u, φ₀ (QuotientGroup.mk u) = ψ u := fun u => QuotientGroup.lift_mk S hSker u

  have hsurj : Function.Surjective φ₀ := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H J =>
      obtain ⟨x, hx1, -, hcx⟩ := HeckeCharacter.exists_isAdjuster_one_and_fadContentHom_projFin_eq K 𝔣 (J : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) J.2
      have hx := isAdjuster_one_iff_mem_adjOne.mp hx1
      refine ⟨QuotientGroup.mk x, ?_⟩
      rw [hφ₀, hψ_adj x hx]
      simp only [hcls]
      congr 1
      exact Subtype.ext hcx

  have hP : ∀ J : ↥(coprimeToModulus K 𝔣), J ∈ normRaySubgroup K L 𝔣 →
      ∃ z : (AdeleRing (𝓞 K) K)ˣ, z ∈ S ∧ z ∈ adjOne K 𝔣 ∧ C z = (J : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) := by
    intro J hJ
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp hJ

    have hPa : ∀ I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ, I ∈ narrowRaySubgroup K 𝔣 →
        ∃ z : (AdeleRing (𝓞 K) K)ˣ, z ∈ S ∧ z ∈ adjOne K 𝔣 ∧ C z = I := by
      intro I hI
      refine Subgroup.closure_induction (p := fun I _ => ∃ z : (AdeleRing (𝓞 K) K)ˣ, z ∈ S ∧ z ∈ adjOne K 𝔣 ∧ C z = I)
        ?_ ?_ ?_ ?_ hI
      · rintro I ⟨x, hx0, hx1, hpos, hIx⟩
        have hxK : (algebraMap (𝓞 K) K x) ≠ 0 := (map_ne_zero_iff (algebraMap (𝓞 K) K) (IsFractionRing.injective (𝓞 K) K)).mpr hx0
        refine ⟨pr K (Units.mk0 _ hxK), Subgroup.mem_sup_left ⟨_, rfl⟩, ?_, ?_⟩
        · refine ⟨fun v hv => ?_, fun τ => ?_⟩
          · rw [projFin_apply, snd_pr]
            exact valued_algebraMap_of_sub_one_mem h𝔣 hx1 hv
          · have h := HeckeCharacter.archSign_unitsMap_algebraMap_mul_iff K τ (Units.mk0 _ hxK) 1
            rw [mul_one] at h
            exact h.mpr (iff_of_true (hpos τ) (archSign_one K τ))
        · apply Units.ext
          rw [hC, HeckeCharacter.coe_fadContentHom_projFin_unitsMap_algebraMap, hIx, FractionalIdeal.coeIdeal_span_singleton]
          rfl
      · exact ⟨1, Subgroup.one_mem _, Subgroup.one_mem _, map_one C⟩
      · rintro I I' - - ⟨z, hzS, hz, rfl⟩ ⟨z', hz'S, hz', rfl⟩
        exact ⟨z * z', Subgroup.mul_mem _ hzS hz'S, Subgroup.mul_mem _ hz hz', map_mul C z z'⟩
      · rintro I - ⟨z, hzS, hz, rfl⟩
        exact ⟨z⁻¹, Subgroup.inv_mem _ hzS, Subgroup.inv_mem _ hz, map_inv C z⟩

    have hPb : ∃ z : (AdeleRing (𝓞 K) K)ˣ, z ∈ S ∧ z ∈ adjOne K 𝔣 ∧ C z = (b : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) := by
      obtain ⟨Y, rfl⟩ := hb
      obtain ⟨x, hx1, -, hcx⟩ := HeckeCharacter.exists_isAdjuster_one_and_fadContentHom_projFin_eq L _
        (Y : (FractionalIdeal ((𝓞 L)⁰) L)ˣ) Y.2
      have hx := isAdjuster_one_iff_mem_adjOne.mp hx1
      refine ⟨Nrm x, Subgroup.mem_sup_right ⟨x, rfl⟩, hNrm_adj x hx, ?_⟩
      rw [hC, hA2, hcx]
      rfl
    obtain ⟨za, hzaS, hza, hCa⟩ := hPa a (Subgroup.mem_subgroupOf.mp ha)
    obtain ⟨zb, hzbS, hzb, hCb⟩ := hPb
    refine ⟨za * zb, Subgroup.mul_mem _ hzaS hzbS, Subgroup.mul_mem _ hza hzb, ?_⟩
    rw [map_mul, hCa, hCb, ← hab]
    rfl

  have hinj : Function.Injective φ₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_lift, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    intro u hu
    rw [MonoidHom.mem_ker, hψ] at hu

    have hu1 := hadjm u
    have hmem : (⟨C (u * (pr K (adj u))⁻¹), hcop _ hu1⟩ : ↥(coprimeToModulus K 𝔣)) ∈ normRaySubgroup K L 𝔣 := by
      rw [← QuotientGroup.eq_one_iff]
      exact hu
    obtain ⟨z, hzS, hz, hCz⟩ := hP _ hmem

    have hw : z⁻¹ * (u * (pr K (adj u))⁻¹) ∈ adjOne K 𝔣 := Subgroup.mul_mem _ (Subgroup.inv_mem _ hz) hu1
    have hCw : C (z⁻¹ * (u * (pr K (adj u))⁻¹)) = 1 := by
      rw [map_mul, map_inv, hCz]
      exact inv_mul_cancel _
    have hord : ∀ w : HeightOneSpectrum (𝓞 K), placeOrd K (projFin K (z⁻¹ * (u * (pr K (adj u))⁻¹))) w = 0 := by
      intro w
      rw [← HeckeCharacter.count_coe_fadContentHom, ← hC, hCw, Units.val_one, FractionalIdeal.count_one]
    have hunit := LanglandsTunnell.P2.Artin.mem_unitIdeles_of_placeOrd_eq_zero_of_isAdjuster_one K 𝔣 _ hord
      (isAdjuster_one_iff_mem_adjOne.mpr hw)
    have hwS : z⁻¹ * (u * (pr K (adj u))⁻¹) ∈ S := Subgroup.mem_sup_right (hA3 hunit)
    have e : u = z * (z⁻¹ * (u * (pr K (adj u))⁻¹)) * pr K (adj u) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hzS hwS) (Subgroup.mem_sup_left ⟨_, rfl⟩)

  refine ⟨MulEquiv.ofBijective φ₀ ⟨hinj, hsurj⟩, fun u hu hc => ?_⟩
  have hu' := isAdjuster_one_iff_mem_adjOne.mp hu
  rw [MulEquiv.ofBijective_apply, hφ₀, hψ_adj u hu']
  rfl

end S_LanglandsTunnell_P2_Artin_exists_mulEquiv_quotient_normRaySubgroup_apply_eq_contents_of_anchors
end P2MW
export P2MW.S_LanglandsTunnell_P2_Artin_exists_mulEquiv_quotient_normRaySubgroup_apply_eq_contents_of_anchors (solution)
