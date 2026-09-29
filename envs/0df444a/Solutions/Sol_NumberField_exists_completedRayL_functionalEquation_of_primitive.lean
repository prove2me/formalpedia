-- Prove2me | solution 1 for NumberField.exists_completedRayL_functionalEquation_of_primitive
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/0ef2560e-0df7-5efb-bf7f-13e601ed0350

import Mathlib
import Definitions.Def_NumberField_CompletedRayL
import Definitions.Def_NumberField_RayCharacterData
import Theorems.Thm_M4aTorus_completedRayL_fe
import Theorems.Thm_NumberField_exists_completedDedekindZeta_package
import Theorems.Thm_NumberField_exists_isGaussDatum
import Theorems.Thm_NumberField_exists_completedRayL_functionalEquation_of_modulus_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_completedRayL_functionalEquation_of_primitive

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open NumberField NumberField.InfinitePlace IsDedekindDomain Deep.NTSupply Filter Topology
open scoped Classical nonZeroDivisors

universe u v

namespace HeckePrimFE

section Transport

variable {K : Type u} [Field K] [NumberField K] {L : Type v} [Field L] [NumberField L]
variable (e : K ≃+* L)

abbrev intEquiv : 𝓞 K ≃+* 𝓞 L := RingOfIntegers.mapRingEquiv e

theorem intEquiv_coe (x : 𝓞 K) : ((intEquiv e x : 𝓞 L) : L) = e (x : K) := rfl

theorem map_symm_map (I : Ideal (𝓞 K)) :
    (I.map (intEquiv e)).map (intEquiv e).symm = I :=
  Ideal.map_of_equiv (intEquiv e)

theorem map_map_symm (J : Ideal (𝓞 L)) :
    (J.map (intEquiv e).symm).map (intEquiv e) = J := by
  rw [Ideal.map_symm]
  exact Ideal.map_comap_of_surjective _ (intEquiv e).surjective _

theorem map_le_map_iff {I J : Ideal (𝓞 K)} :
    I.map (intEquiv e) ≤ J.map (intEquiv e) ↔ I ≤ J := by
  refine ⟨fun h => ?_, fun h => Ideal.map_mono h⟩
  have h' := Ideal.map_mono (f := (intEquiv e).symm) h
  rwa [map_symm_map, map_symm_map] at h'

theorem map_injective : Function.Injective (Ideal.map (intEquiv e) : Ideal (𝓞 K) → Ideal (𝓞 L)) :=
  fun I J h => le_antisymm ((map_le_map_iff e).mp h.le) ((map_le_map_iff e).mp h.ge)

theorem map_dvd_map_iff {I J : Ideal (𝓞 K)} :
    I.map (intEquiv e) ∣ J.map (intEquiv e) ↔ I ∣ J := by
  rw [Ideal.dvd_iff_le, Ideal.dvd_iff_le, map_le_map_iff]

theorem map_ne_bot_iff {I : Ideal (𝓞 K)} : I.map (intEquiv e) ≠ ⊥ ↔ I ≠ ⊥ :=
  (Ideal.map_eq_bot_iff_of_injective (intEquiv e).injective).not

theorem map_span_singleton (a : 𝓞 K) :
    (Ideal.span {a} : Ideal (𝓞 K)).map (intEquiv e) = Ideal.span {intEquiv e a} := by
  rw [Ideal.map_span, Set.image_singleton]

def idealEquiv : Ideal (𝓞 K) ≃ Ideal (𝓞 L) where
  toFun I := I.map (intEquiv e)
  invFun J := J.map (intEquiv e).symm
  left_inv I := map_symm_map e I
  right_inv J := map_map_symm e J

theorem absNorm_map (I : Ideal (𝓞 K)) :
    Ideal.absNorm (I.map (intEquiv e)) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv I (I.map (intEquiv e)) (intEquiv e) rfl).toEquiv).symm

def primeEquiv : HeightOneSpectrum (𝓞 K) ≃ HeightOneSpectrum (𝓞 L) where
  toFun v := ⟨v.asIdeal.map (intEquiv e), inferInstance, (map_ne_bot_iff e).mpr v.ne_bot⟩
  invFun w := ⟨w.asIdeal.map (intEquiv e).symm, inferInstance, by
    intro h
    apply w.ne_bot
    have := congrArg (Ideal.map (intEquiv e)) h
    rwa [map_map_symm, Ideal.map_bot] at this⟩
  left_inv v := by
    ext1
    exact map_symm_map e v.asIdeal
  right_inv w := by
    ext1
    exact map_map_symm e w.asIdeal

@[scoped simp] theorem primeEquiv_asIdeal (v : HeightOneSpectrum (𝓞 K)) :
    (primeEquiv e v).asIdeal = v.asIdeal.map (intEquiv e) := rfl

@[scoped simp] theorem primeEquiv_symm_asIdeal (w : HeightOneSpectrum (𝓞 L)) :
    ((primeEquiv e).symm w).asIdeal = w.asIdeal.map (intEquiv e).symm := rfl

theorem primeEquiv_symm_dvd_iff (w : HeightOneSpectrum (𝓞 L)) (I : Ideal (𝓞 K)) :
    ((primeEquiv e).symm w).asIdeal ∣ I ↔ w.asIdeal ∣ I.map (intEquiv e) := by
  rw [primeEquiv_symm_asIdeal, ← map_dvd_map_iff e, map_map_symm]

theorem count_coe_map (v : HeightOneSpectrum (𝓞 K)) {J : Ideal (𝓞 K)} (hJ : J ≠ ⊥) :
    FractionalIdeal.count L (primeEquiv e v)
        ((J.map (intEquiv e) : Ideal (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L) =
      FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K) := by
  have hJ0 : J ≠ 0 := hJ
  have hJ' : J.map (intEquiv e) ≠ ⊥ := (map_ne_bot_iff e).mpr hJ
  have hJ'0 : J.map (intEquiv e) ≠ 0 := hJ'
  rw [FractionalIdeal.count_coe L _ hJ'0, FractionalIdeal.count_coe K _ hJ0]
  congr 1
  refine eq_of_forall_le_iff fun k => ?_
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ'0)
      (primeEquiv e v).associates_irreducible,
    ← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ0) v.associates_irreducible,
    ← Associates.mk_pow, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd,
    Associates.mk_le_mk_iff_dvd, primeEquiv_asIdeal, ← Ideal.map_pow, map_dvd_map_iff]

theorem eq_of_count_eq {I J : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), FractionalIdeal.count K v I = FractionalIdeal.count K v J) :
    I = J := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ]
  exact finprod_congr fun v => by rw [h v]

theorem finprod_zpow_ne_zero (n : HeightOneSpectrum (𝓞 K) → ℤ) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 K), (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ n v) ≠ 0 := by
  refine finprod_induction (fun x : FractionalIdeal (𝓞 K)⁰ K => x ≠ 0) one_ne_zero
    (fun _ _ hx hy => mul_ne_zero hx hy) fun v => ?_
  exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)

theorem eventually_count_symm_eq_zero (u : FractionalIdeal (𝓞 K)⁰ K) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 L) in cofinite,
      FractionalIdeal.count K ((primeEquiv e).symm w) u = 0 := by
  have h := FractionalIdeal.finite_factors u
  rw [Filter.eventually_cofinite] at h ⊢
  refine (h.preimage (Set.injOn_of_injective (primeEquiv e).symm.injective)).subset ?_
  intro w hw
  exact hw

theorem eventually_count_eq_zero (u : FractionalIdeal (𝓞 L)⁰ L) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite,
      FractionalIdeal.count L (primeEquiv e v) u = 0 := by
  have h := FractionalIdeal.finite_factors u
  rw [Filter.eventually_cofinite] at h ⊢
  refine (h.preimage (Set.injOn_of_injective (primeEquiv e).injective)).subset ?_
  intro w hw
  exact hw

def fracMap (u : FractionalIdeal (𝓞 K)⁰ K) : FractionalIdeal (𝓞 L)⁰ L :=
  ∏ᶠ w : HeightOneSpectrum (𝓞 L),
    (w.asIdeal : FractionalIdeal (𝓞 L)⁰ L) ^ FractionalIdeal.count K ((primeEquiv e).symm w) u

def fracInv (u : FractionalIdeal (𝓞 L)⁰ L) : FractionalIdeal (𝓞 K)⁰ K :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K),
    (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ FractionalIdeal.count L (primeEquiv e v) u

theorem fracMap_ne_zero (u : FractionalIdeal (𝓞 K)⁰ K) : fracMap e u ≠ 0 :=
  finprod_zpow_ne_zero _

theorem fracInv_ne_zero (u : FractionalIdeal (𝓞 L)⁰ L) : fracInv e u ≠ 0 :=
  finprod_zpow_ne_zero _

theorem count_fracMap (u : FractionalIdeal (𝓞 K)⁰ K) (w : HeightOneSpectrum (𝓞 L)) :
    FractionalIdeal.count L w (fracMap e u) =
      FractionalIdeal.count K ((primeEquiv e).symm w) u :=
  FractionalIdeal.count_finprod L w _ (eventually_count_symm_eq_zero e u)

theorem count_fracMap' (u : FractionalIdeal (𝓞 K)⁰ K) (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count L (primeEquiv e v) (fracMap e u) = FractionalIdeal.count K v u := by
  rw [count_fracMap, Equiv.symm_apply_apply]

theorem count_fracInv (u : FractionalIdeal (𝓞 L)⁰ L) (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v (fracInv e u) = FractionalIdeal.count L (primeEquiv e v) u :=
  FractionalIdeal.count_finprod K v _ (eventually_count_eq_zero e u)

def unitEquiv : (FractionalIdeal (𝓞 K)⁰ K)ˣ ≃* (FractionalIdeal (𝓞 L)⁰ L)ˣ where
  toFun u := Units.mk0 (fracMap e u) (fracMap_ne_zero e u)
  invFun u := Units.mk0 (fracInv e u) (fracInv_ne_zero e u)
  left_inv u := by
    refine Units.ext ?_
    show fracInv e (fracMap e u) = u
    refine eq_of_count_eq (fracInv_ne_zero e _) u.ne_zero fun v => ?_
    rw [count_fracInv, count_fracMap']
  right_inv u := by
    refine Units.ext ?_
    show fracMap e (fracInv e u) = u
    refine eq_of_count_eq (K := L) (fracMap_ne_zero e _) u.ne_zero fun w => ?_
    rw [count_fracMap, count_fracInv, Equiv.apply_symm_apply]
  map_mul' u u' := by
    refine Units.ext ?_
    show fracMap e ((u * u' : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      fracMap e u * fracMap e u'
    refine eq_of_count_eq (K := L) (fracMap_ne_zero e _)
      (mul_ne_zero (fracMap_ne_zero e _) (fracMap_ne_zero e _)) fun w => ?_
    rw [FractionalIdeal.count_mul L w (fracMap_ne_zero e _) (fracMap_ne_zero e _),
      count_fracMap, count_fracMap, count_fracMap, Units.val_mul,
      FractionalIdeal.count_mul K _ u.ne_zero u'.ne_zero]

theorem unitEquiv_val (u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((unitEquiv e u : (FractionalIdeal (𝓞 L)⁰ L)ˣ) : FractionalIdeal (𝓞 L)⁰ L) = fracMap e u :=
  rfl

theorem count_unitEquiv (u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (w : HeightOneSpectrum (𝓞 L)) :
    FractionalIdeal.count L w ((unitEquiv e u : (FractionalIdeal (𝓞 L)⁰ L)ˣ) :
        FractionalIdeal (𝓞 L)⁰ L) =
      FractionalIdeal.count K ((primeEquiv e).symm w) (u : FractionalIdeal (𝓞 K)⁰ K) :=
  count_fracMap e u w

theorem unitEquiv_coeIdeal (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥) (u : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hu : (u : FractionalIdeal (𝓞 K)⁰ K) = (J : FractionalIdeal (𝓞 K)⁰ K)) :
    ((unitEquiv e u : (FractionalIdeal (𝓞 L)⁰ L)ˣ) : FractionalIdeal (𝓞 L)⁰ L) =
      ((J.map (intEquiv e) : Ideal (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L) := by
  have hJ' : ((J.map (intEquiv e) : Ideal (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr ((map_ne_bot_iff e).mpr hJ)
  refine eq_of_count_eq (K := L) (Units.ne_zero _) hJ' fun w => ?_
  rw [count_unitEquiv, hu, ← count_coe_map e ((primeEquiv e).symm w) hJ, Equiv.apply_symm_apply]

theorem unitEquiv_principalUnit (a : 𝓞 K) (ha : a ≠ 0) :
    unitEquiv e (principalUnit K a ha) =
      principalUnit L (intEquiv e a) ((map_ne_zero_iff _ (intEquiv e).injective).mpr ha) := by
  ext1
  rw [principalUnit_val, ← map_span_singleton]
  refine unitEquiv_coeIdeal e _ ?_ _ (principalUnit_val K a ha)
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact ha

theorem unitEquiv_mk0 (I : (Ideal (𝓞 K))⁰) :
    ((unitEquiv e (FractionalIdeal.mk0 K I) : (FractionalIdeal (𝓞 L)⁰ L)ˣ) :
        FractionalIdeal (𝓞 L)⁰ L) =
      (((I : Ideal (𝓞 K)).map (intEquiv e) : Ideal (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L) :=
  unitEquiv_coeIdeal e _ (nonZeroDivisors.ne_zero I.2) _ (FractionalIdeal.coe_mk0 K I)

variable (𝔣 : Ideal (𝓞 K))

theorem mem_coprimeToModulus_map_iff (u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    unitEquiv e u ∈ coprimeToModulus L (𝔣.map (intEquiv e)) ↔ u ∈ coprimeToModulus K 𝔣 := by
  rw [mem_coprimeToModulus_iff, mem_coprimeToModulus_iff]
  constructor
  · intro h v hv
    have := h (primeEquiv e v) ((map_dvd_map_iff e).mpr hv)
    rwa [count_unitEquiv, Equiv.symm_apply_apply] at this
  · intro h w hw
    rw [count_unitEquiv]
    exact h _ ((primeEquiv_symm_dvd_iff e w 𝔣).mpr hw)

def coprimeEquiv : ↥(coprimeToModulus K 𝔣) ≃* ↥(coprimeToModulus L (𝔣.map (intEquiv e))) where
  toFun y := ⟨unitEquiv e y, (mem_coprimeToModulus_map_iff e 𝔣 _).mpr y.2⟩
  invFun y := ⟨(unitEquiv e).symm y, by
    rw [← mem_coprimeToModulus_map_iff e 𝔣, MulEquiv.apply_symm_apply]
    exact y.2⟩
  left_inv y := by
    ext1
    exact (unitEquiv e).symm_apply_apply _
  right_inv y := by
    ext1
    exact (unitEquiv e).apply_symm_apply _
  map_mul' y y' := by
    ext1
    exact map_mul (unitEquiv e) _ _

@[scoped simp] theorem coprimeEquiv_coe (y : ↥(coprimeToModulus K 𝔣)) :
    ((coprimeEquiv e 𝔣 y : ↥(coprimeToModulus L (𝔣.map (intEquiv e)))) :
      (FractionalIdeal (𝓞 L)⁰ L)ˣ) = unitEquiv e y := rfl

theorem image_narrowRaySet :
    (unitEquiv e) '' narrowRaySet K 𝔣 = narrowRaySet L (𝔣.map (intEquiv e)) := by
  ext I'
  constructor
  · rintro ⟨I, ⟨α, hα0, hα1, hpos, hI⟩, rfl⟩
    refine ⟨intEquiv e α, (map_ne_zero_iff _ (intEquiv e).injective).mpr hα0, ?_, ?_, ?_⟩
    · have : intEquiv e (α - 1) ∈ 𝔣.map (intEquiv e) := Ideal.mem_map_of_mem _ hα1
      simpa using this
    · intro τ
      have := hpos (τ.comp e.toRingHom)
      simpa [intEquiv_coe] using this
    · rw [← map_span_singleton]
      refine unitEquiv_coeIdeal e _ ?_ _ hI
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact hα0
  · rintro ⟨α', hα0, hα1, hpos, hI'⟩
    obtain ⟨α, rfl⟩ := (intEquiv e).surjective α'
    have hα : α ≠ 0 := fun h => hα0 (by simp [h])
    refine ⟨(unitEquiv e).symm I', ⟨α, hα, ?_, ?_, ?_⟩, (unitEquiv e).apply_symm_apply _⟩
    · have h1 : intEquiv e (α - 1) ∈ 𝔣.map (intEquiv e) := by simpa using hα1
      exact Ideal.apply_mem_of_equiv_iff.mp h1
    · intro τ
      have := hpos (τ.comp e.symm.toRingHom)
      simpa [intEquiv_coe] using this
    · have hspan : (Ideal.span {α} : Ideal (𝓞 K)) ≠ ⊥ := by
        rw [Ne, Ideal.span_singleton_eq_bot]
        exact hα
      set u : (FractionalIdeal (𝓞 K)⁰ K)ˣ := Units.mk0
        ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
        (FractionalIdeal.coeIdeal_ne_zero.mpr hspan) with hu
      have h1 : unitEquiv e u = I' := by
        ext1
        rw [hI', ← map_span_singleton]
        exact unitEquiv_coeIdeal e _ hspan u rfl
      rw [← h1, MulEquiv.symm_apply_apply]
      rfl

theorem map_narrowRaySubgroup :
    (narrowRaySubgroup K 𝔣).map (unitEquiv e).toMonoidHom =
      narrowRaySubgroup L (𝔣.map (intEquiv e)) := by
  rw [narrowRaySubgroup, narrowRaySubgroup, MonoidHom.map_closure]
  congr 1
  exact image_narrowRaySet e 𝔣

theorem mem_narrowRaySubgroup_map_iff (u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    unitEquiv e u ∈ narrowRaySubgroup L (𝔣.map (intEquiv e)) ↔ u ∈ narrowRaySubgroup K 𝔣 := by
  rw [← map_narrowRaySubgroup e 𝔣, Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, hzu⟩
    have : z = u := (unitEquiv e).injective hzu
    exact this ▸ hz
  · intro hu
    exact ⟨u, hu, rfl⟩

theorem map_subgroupOf_eq :
    ((narrowRaySubgroup K 𝔣).subgroupOf (coprimeToModulus K 𝔣)).map
        ((coprimeEquiv e 𝔣 : ↥(coprimeToModulus K 𝔣) ≃*
          ↥(coprimeToModulus L (𝔣.map (intEquiv e)))) :
          ↥(coprimeToModulus K 𝔣) →* ↥(coprimeToModulus L (𝔣.map (intEquiv e)))) =
      (narrowRaySubgroup L (𝔣.map (intEquiv e))).subgroupOf
        (coprimeToModulus L (𝔣.map (intEquiv e))) := by
  ext y'
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_subgroupOf] at hy
    show unitEquiv e y ∈ _
    exact (mem_narrowRaySubgroup_map_iff e 𝔣 _).mpr hy
  · intro hy'
    refine ⟨(coprimeEquiv e 𝔣).symm y', ?_, MulEquiv.apply_symm_apply _ _⟩
    rw [Subgroup.mem_subgroupOf, ← mem_narrowRaySubgroup_map_iff e 𝔣]
    have : ((coprimeEquiv e 𝔣 ((coprimeEquiv e 𝔣).symm y') : ↥(coprimeToModulus L _)) :
        (FractionalIdeal (𝓞 L)⁰ L)ˣ) = y' := by
      rw [MulEquiv.apply_symm_apply]
    rw [coprimeEquiv_coe] at this
    rw [this]
    exact hy'

def rayEquiv : NarrowRayClassGroup K 𝔣 ≃* NarrowRayClassGroup L (𝔣.map (intEquiv e)) :=
  QuotientGroup.congr _ _ (coprimeEquiv e 𝔣) (map_subgroupOf_eq e 𝔣)

theorem rayEquiv_mk (y : ↥(coprimeToModulus K 𝔣)) :
    rayEquiv e 𝔣 (NarrowRayClassGroup.mk K 𝔣 y) =
      NarrowRayClassGroup.mk L (𝔣.map (intEquiv e)) (coprimeEquiv e 𝔣 y) :=
  QuotientGroup.congr_mk' _ _ (coprimeEquiv e 𝔣) (map_subgroupOf_eq e 𝔣) y

def nzdEquiv : ↥(Ideal (𝓞 K))⁰ ≃ ↥(Ideal (𝓞 L))⁰ :=
  (idealEquiv e).subtypeEquiv fun I => by
    rw [mem_nonZeroDivisors_iff_ne_zero, mem_nonZeroDivisors_iff_ne_zero]
    exact ((map_ne_bot_iff e (I := I)).symm : _)

@[scoped simp] theorem nzdEquiv_coe (I : ↥(Ideal (𝓞 K))⁰) :
    ((nzdEquiv e I : ↥(Ideal (𝓞 L))⁰) : Ideal (𝓞 L)) = (I : Ideal (𝓞 K)).map (intEquiv e) := rfl

theorem unitEquiv_mk0' (I : ↥(Ideal (𝓞 K))⁰) :
    unitEquiv e (FractionalIdeal.mk0 K I) = FractionalIdeal.mk0 L (nzdEquiv e I) := by
  refine Units.ext ?_
  rw [unitEquiv_mk0, FractionalIdeal.coe_mk0]
  rfl

theorem rayZetaCoeff_map (C : NarrowRayClassGroup K 𝔣) (n : ℕ) :
    M4aTorus.rayZetaCoeff L (𝔣.map (intEquiv e)) (rayEquiv e 𝔣 C) n =
      M4aTorus.rayZetaCoeff K 𝔣 C n := by
  unfold M4aTorus.rayZetaCoeff
  refine (Nat.card_congr ((nzdEquiv e).subtypeEquiv fun I => ?_)).symm
  show _ ↔ Ideal.absNorm ((nzdEquiv e I : ↥(Ideal (𝓞 L))⁰) : Ideal (𝓞 L)) = n ∧ _
  rw [nzdEquiv_coe, absNorm_map]
  refine and_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨hc, hC⟩
    have hc' : FractionalIdeal.mk0 L (nzdEquiv e I) ∈ coprimeToModulus L (𝔣.map (intEquiv e)) := by
      rw [← unitEquiv_mk0', mem_coprimeToModulus_map_iff]
      exact hc
    refine ⟨hc', ?_⟩
    rw [← hC, rayEquiv_mk]
    congr 1
    exact Subtype.ext (unitEquiv_mk0' e I).symm
  · rintro ⟨hc', hC'⟩
    have hc : FractionalIdeal.mk0 K I ∈ coprimeToModulus K 𝔣 := by
      rw [← mem_coprimeToModulus_map_iff e 𝔣, unitEquiv_mk0']
      exact hc'
    refine ⟨hc, (rayEquiv e 𝔣).injective ?_⟩
    rw [rayEquiv_mk, ← hC']
    congr 1
    exact Subtype.ext (unitEquiv_mk0' e I)

theorem rayZeta_map (C : NarrowRayClassGroup K 𝔣) (s : ℂ) :
    M4aTorus.rayZeta L (𝔣.map (intEquiv e)) (rayEquiv e 𝔣 C) s = M4aTorus.rayZeta K 𝔣 C s := by
  unfold M4aTorus.rayZeta
  simp_rw [rayZetaCoeff_map]

abbrev chiMap (χ : NarrowRayClassGroup K 𝔣 →* ℂ) :
    NarrowRayClassGroup L (𝔣.map (intEquiv e)) →* ℂ :=
  χ.comp (rayEquiv e 𝔣).symm.toMonoidHom

theorem chiMap_apply (χ : NarrowRayClassGroup K 𝔣 →* ℂ) (C : NarrowRayClassGroup K 𝔣) :
    chiMap e 𝔣 χ (rayEquiv e 𝔣 C) = χ C := by
  simp [chiMap]

theorem chiMap_eq_one_iff (χ : NarrowRayClassGroup K 𝔣 →* ℂ) : chiMap e 𝔣 χ = 1 ↔ χ = 1 := by
  constructor
  · intro h
    refine MonoidHom.ext fun C => ?_
    rw [← chiMap_apply e 𝔣 χ C, h, MonoidHom.one_apply, MonoidHom.one_apply]
  · intro h
    refine MonoidHom.ext fun C' => ?_
    simp [chiMap, h]

theorem chiMap_conj (χ : NarrowRayClassGroup K 𝔣 →* ℂ) :
    chiMap e 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) =
      (starRingEnd ℂ).toMonoidHom.comp (chiMap e 𝔣 χ) := rfl

theorem rayClassLSeries_map (χ : NarrowRayClassGroup K 𝔣 →* ℂ) (s : ℂ) :
    M4aTorus.rayClassLSeries L (𝔣.map (intEquiv e)) (chiMap e 𝔣 χ) s =
      M4aTorus.rayClassLSeries K 𝔣 χ s := by
  unfold M4aTorus.rayClassLSeries
  rw [← Equiv.tsum_eq (rayEquiv e 𝔣).toEquiv]
  refine tsum_congr fun C => ?_
  rw [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, chiMap_apply, rayZeta_map]

def ratAlgEquiv : K ≃ₐ[ℚ] L :=
  AlgEquiv.ofRingEquiv (f := e) fun q => by simp

include e in
theorem discr_eq : discr L = discr K :=
  (NumberField.discr_eq_discr_of_algEquiv K (ratAlgEquiv e)).symm

def placeEquiv : InfinitePlace K ≃ InfinitePlace L where
  toFun w := w.comap (e.symm : L →+* K)
  invFun w := w.comap (e : K →+* L)
  left_inv w := by
    show (w.comap (e.symm : L →+* K)).comap (e : K →+* L) = w
    rw [← comap_comp]
    have : (e.symm : L →+* K).comp (e : K →+* L) = RingHom.id K := by
      ext x
      simp
    rw [this, InfinitePlace.comap_id]
  right_inv w := by
    show (w.comap (e : K →+* L)).comap (e.symm : L →+* K) = w
    rw [← comap_comp]
    have : (e : K →+* L).comp (e.symm : L →+* K) = RingHom.id L := by
      ext x
      simp
    rw [this, InfinitePlace.comap_id]

@[scoped simp] theorem placeEquiv_apply (w : InfinitePlace K) :
    placeEquiv e w = w.comap (e.symm : L →+* K) := rfl

def realPlaceEquiv : {w : InfinitePlace K // w.IsReal} ≃ {w : InfinitePlace L // w.IsReal} :=
  (placeEquiv e).subtypeEquiv fun w => (isReal_comap_iff e.symm).symm

def complexPlaceEquiv :
    {w : InfinitePlace K // w.IsComplex} ≃ {w : InfinitePlace L // w.IsComplex} :=
  (placeEquiv e).subtypeEquiv fun w => by
    rw [← not_isReal_iff_isComplex, ← not_isReal_iff_isComplex, placeEquiv_apply,
      isReal_comap_iff]

include e in
theorem nrRealPlaces_eq : nrRealPlaces L = nrRealPlaces K :=
  (Fintype.card_congr (realPlaceEquiv e)).symm

include e in
theorem nrComplexPlaces_eq : nrComplexPlaces L = nrComplexPlaces K :=
  (Fintype.card_congr (complexPlaceEquiv e)).symm

abbrev sMap (S : Finset {w : InfinitePlace K // w.IsReal}) :
    Finset {w : InfinitePlace L // w.IsReal} :=
  S.map (realPlaceEquiv e).toEmbedding

theorem completedRayL_map (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
    (S : Finset {w : InfinitePlace K // w.IsReal}) (s : ℂ) :
    M4aTorus.completedRayL L (𝔣.map (intEquiv e)) (chiMap e 𝔣 χ) (sMap e S) s =
      M4aTorus.completedRayL K 𝔣 χ S s := by
  unfold M4aTorus.completedRayL
  rw [rayClassLSeries_map, Finset.card_map, absNorm_map, nrRealPlaces_eq e, nrComplexPlaces_eq e,
    discr_eq e]

theorem sign_map (w : {w : InfinitePlace K // w.IsReal}) (x : K) :
    SignType.sign (embedding_of_isReal (realPlaceEquiv e w).2 (e x)) =
      SignType.sign (embedding_of_isReal w.2 x) := by
  congr 1
  apply Complex.ofReal_injective
  rw [embedding_of_isReal_apply, embedding_of_isReal_apply]
  show ((w.1.comap (e.symm : L →+* K)).embedding) (e x) = w.1.embedding x
  rw [comap_embedding_of_isReal _ ((isReal_comap_iff e.symm).mpr w.2)]
  simp

theorem chiMap_mk_principalUnit (χ : NarrowRayClassGroup K 𝔣 →* ℂ) (α : 𝓞 K) (hα : α ≠ 0)
    (hc : principalUnit K α hα ∈ coprimeToModulus K 𝔣)
    (hα' : intEquiv e α ≠ 0)
    (hc' : principalUnit L (intEquiv e α) hα' ∈ coprimeToModulus L (𝔣.map (intEquiv e))) :
    chiMap e 𝔣 χ (NarrowRayClassGroup.mk L (𝔣.map (intEquiv e))
        ⟨principalUnit L (intEquiv e α) hα', hc'⟩) =
      χ (NarrowRayClassGroup.mk K 𝔣 ⟨principalUnit K α hα, hc⟩) := by
  have h : rayEquiv e 𝔣 (NarrowRayClassGroup.mk K 𝔣 ⟨principalUnit K α hα, hc⟩) =
      NarrowRayClassGroup.mk L (𝔣.map (intEquiv e)) ⟨principalUnit L (intEquiv e α) hα', hc'⟩ := by
    rw [rayEquiv_mk]
    congr 1
    exact Subtype.ext (unitEquiv_principalUnit e α hα)
  rw [← h, chiMap_apply]

theorem principalUnit_map_mem_iff (α : 𝓞 K) (hα : α ≠ 0) (hα' : intEquiv e α ≠ 0) :
    principalUnit L (intEquiv e α) hα' ∈ coprimeToModulus L (𝔣.map (intEquiv e)) ↔
      principalUnit K α hα ∈ coprimeToModulus K 𝔣 := by
  rw [← mem_coprimeToModulus_map_iff e 𝔣, unitEquiv_principalUnit]

theorem sub_one_mem_map_iff (α : 𝓞 K) (I : Ideal (𝓞 K)) :
    intEquiv e α - 1 ∈ I.map (intEquiv e) ↔ α - 1 ∈ I := by
  have : intEquiv e α - 1 = intEquiv e (α - 1) := by simp
  rw [this, Ideal.apply_mem_of_equiv_iff]

theorem totallyPositive_map_iff (α : 𝓞 K) :
    (∀ τ : L →+* ℝ, 0 < τ ((intEquiv e α : 𝓞 L) : L)) ↔ ∀ τ : K →+* ℝ, 0 < τ (α : K) := by
  constructor
  · intro h τ
    have := h (τ.comp (e.symm : L →+* K))
    simpa [intEquiv_coe] using this
  · intro h τ
    have := h (τ.comp (e : K →+* L))
    simpa [intEquiv_coe] using this

theorem parity_map (χ : NarrowRayClassGroup K 𝔣 →* ℂ) (S : Finset {w : InfinitePlace K // w.IsReal})
    (hpar : ∀ (α : 𝓞 K) (hα : α ≠ 0) (hc : principalUnit K α hα ∈ coprimeToModulus K 𝔣),
      α - 1 ∈ 𝔣 →
        χ (NarrowRayClassGroup.mk K 𝔣 ⟨principalUnit K α hα, hc⟩) =
          ∏ w ∈ S, ((SignType.sign (embedding_of_isReal w.2 (α : K)) : ℤ) : ℂ)) :
    ∀ (α : 𝓞 L) (hα : α ≠ 0)
      (hc : principalUnit L α hα ∈ coprimeToModulus L (𝔣.map (intEquiv e))),
      α - 1 ∈ 𝔣.map (intEquiv e) →
        chiMap e 𝔣 χ (NarrowRayClassGroup.mk L (𝔣.map (intEquiv e)) ⟨principalUnit L α hα, hc⟩) =
          ∏ w ∈ sMap e S, ((SignType.sign (embedding_of_isReal w.2 (α : L)) : ℤ) : ℂ) := by
  intro α' hα' hc' h1'
  obtain ⟨α, rfl⟩ := (intEquiv e).surjective α'
  have hα : α ≠ 0 := fun h => hα' (by simp [h])
  have hc : principalUnit K α hα ∈ coprimeToModulus K 𝔣 :=
    (principalUnit_map_mem_iff e 𝔣 α hα hα').mp hc'
  rw [chiMap_mk_principalUnit e 𝔣 χ α hα hc hα' hc', hpar α hα hc ((sub_one_mem_map_iff e α 𝔣).mp h1'),
    Finset.prod_map]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [Equiv.coe_toEmbedding, intEquiv_coe, sign_map]

theorem primitive_map (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
    (hprim : ∀ 𝔣' : Ideal (𝓞 K), 𝔣 ≤ 𝔣' → 𝔣' ≠ 𝔣 →
      ∃ (α : 𝓞 K) (hα : α ≠ 0) (hc : principalUnit K α hα ∈ coprimeToModulus K 𝔣),
        α - 1 ∈ 𝔣' ∧ (∀ τ : K →+* ℝ, 0 < τ (α : K)) ∧
          χ (NarrowRayClassGroup.mk K 𝔣 ⟨principalUnit K α hα, hc⟩) ≠ 1) :
    ∀ 𝔣' : Ideal (𝓞 L), 𝔣.map (intEquiv e) ≤ 𝔣' → 𝔣' ≠ 𝔣.map (intEquiv e) →
      ∃ (α : 𝓞 L) (hα : α ≠ 0)
        (hc : principalUnit L α hα ∈ coprimeToModulus L (𝔣.map (intEquiv e))),
        α - 1 ∈ 𝔣' ∧ (∀ τ : L →+* ℝ, 0 < τ (α : L)) ∧
          chiMap e 𝔣 χ (NarrowRayClassGroup.mk L (𝔣.map (intEquiv e))
            ⟨principalUnit L α hα, hc⟩) ≠ 1 := by
  intro 𝔣'' hle hne
  set 𝔣₁ : Ideal (𝓞 K) := 𝔣''.map (intEquiv e).symm with h𝔣₁
  have h𝔣₁' : 𝔣₁.map (intEquiv e) = 𝔣'' := map_map_symm e 𝔣''
  have hle₁ : 𝔣 ≤ 𝔣₁ := by
    rw [← map_le_map_iff e, h𝔣₁']
    exact hle
  have hne₁ : 𝔣₁ ≠ 𝔣 := by
    intro h
    apply hne
    rw [← h𝔣₁', h]
  obtain ⟨α, hα, hc, h1, hpos, hχ⟩ := hprim 𝔣₁ hle₁ hne₁
  have hα' : intEquiv e α ≠ 0 := (map_ne_zero_iff _ (intEquiv e).injective).mpr hα
  have hc' : principalUnit L (intEquiv e α) hα' ∈ coprimeToModulus L (𝔣.map (intEquiv e)) :=
    (principalUnit_map_mem_iff e 𝔣 α hα hα').mpr hc
  refine ⟨intEquiv e α, hα', hc', ?_, (totallyPositive_map_iff e α).mpr hpos, ?_⟩
  · rw [← h𝔣₁', sub_one_mem_map_iff]
    exact h1
  · rw [chiMap_mk_principalUnit e 𝔣 χ α hα hc hα' hc']
    exact hχ

end Transport

section SmallModel

variable {K : Type u} [Field K] [NumberField K] {L : Type v} [Field L]

theorem numberField_of_ringEquiv (e : K ≃+* L) : NumberField L := by
  haveI : CharZero L := charZero_of_injective_ringHom (f := (e : K →+* L)) e.injective
  let f : K ≃ₐ[ℚ] L := AlgEquiv.ofRingEquiv (f := e) fun q => by simp
  exact { to_charZero := inferInstance, to_finiteDimensional := f.toLinearEquiv.finiteDimensional }

variable (K) in

theorem countable_of_numberField : Countable K := by
  let b := Module.Free.chooseBasis ℚ K
  exact b.equivFun.toEquiv.countable_iff.mpr inferInstance

end SmallModel

section Aux

variable (K : Type u) [Field K] [NumberField K]

theorem exists_neg_pos (w₀ : {w : InfinitePlace K // w.IsReal}) :
    ∃ α : 𝓞 K, α ≠ 0 ∧ embedding_of_isReal w₀.2 (α : K) < 0 ∧
      ∀ w : {w : InfinitePlace K // w.IsReal}, w ≠ w₀ → 0 < embedding_of_isReal w.2 (α : K) := by
  set z : (v : InfinitePlace K) → WithAbs v.1 :=
    fun v => WithAbs.toAbs v.1 (if v = w₀.1 then (-1 : K) else 1) with hz
  obtain ⟨x, hx⟩ := (denseRange_algebraMap_pi K).exists_dist_lt z one_pos
  have hv : ∀ v : InfinitePlace K, v ((if v = w₀.1 then (-1 : K) else 1) - x) < 1 := by
    intro v
    have h1 := (dist_le_pi_dist z (algebraMap K _ x) v).trans_lt hx
    rw [dist_eq_norm, WithAbs.norm_eq_apply_ofAbs] at h1
    exact h1
  have hreal : ∀ w : {w : InfinitePlace K // w.IsReal},
      |(if w.1 = w₀.1 then (-1 : ℝ) else 1) - embedding_of_isReal w.2 x| < 1 := by
    intro w
    have h := hv w.1
    rw [← norm_embedding_of_isReal w.2, Real.norm_eq_abs, map_sub] at h
    convert h using 3
    split_ifs <;> simp
  have hneg : embedding_of_isReal w₀.2 x < 0 := by
    have h := hreal w₀
    rw [if_pos rfl, abs_sub_lt_iff] at h
    linarith [h.1, h.2]
  have hpos : ∀ w : {w : InfinitePlace K // w.IsReal}, w ≠ w₀ →
      0 < embedding_of_isReal w.2 x := by
    intro w hw
    have h := hreal w
    rw [if_neg (fun h' => hw (Subtype.ext h')), abs_sub_lt_iff] at h
    linarith [h.1, h.2]

  obtain ⟨⟨b, hb⟩, c, hc⟩ := IsLocalization.exists_integer_multiple (𝓞 K)⁰ x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : (b : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hb0
  have hcK : algebraMap (𝓞 K) K c = (b : K) * x := by
    have : algebraMap (𝓞 K) K c = ((⟨b, hb⟩ : (𝓞 K)⁰) : 𝓞 K) • x := hc
    rw [Algebra.smul_def] at this
    rw [this, RingOfIntegers.coe_eq_algebraMap]
  have hbcK : ((b * c : 𝓞 K) : K) = (b : K) ^ 2 * x := by
    rw [RingOfIntegers.coe_eq_algebraMap, map_mul, hcK, ← RingOfIntegers.coe_eq_algebraMap]
    ring
  have hsq : ∀ w : {w : InfinitePlace K // w.IsReal},
      0 < (embedding_of_isReal w.2 (b : K)) ^ 2 := fun w =>
    lt_of_le_of_ne (sq_nonneg _)
      (Ne.symm (pow_ne_zero 2 ((map_ne_zero_iff _ (embedding_of_isReal w.2).injective).mpr hbK)))
  refine ⟨b * c, ?_, ?_, ?_⟩
  · intro h
    have : (b : K) ^ 2 * x = 0 := by rw [← hbcK, h]; rfl
    rcases mul_eq_zero.mp this with h' | h'
    · exact pow_ne_zero 2 hbK h'
    · rw [h', map_zero] at hneg
      exact lt_irrefl _ hneg
  · rw [hbcK, map_mul, map_pow]
    exact mul_neg_of_pos_of_neg (hsq w₀) hneg
  · intro w hw
    rw [hbcK, map_mul, map_pow]
    exact mul_pos (hsq w) (hpos w hw)

theorem summable_card_absNorm {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) s := by
  have ht : Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ)) / n) atTop
      (𝓝 ((2 ^ nrRealPlaces K * (2 * Real.pi) ^ nrComplexPlaces K * Units.regulator K *
        classNumber K) / (Units.torsionOrder K * Real.sqrt |discr K|))) := by
    refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr
      fun n ↦ ?_
    simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
    congr
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by
        simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ Ideal.finite_setOf_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  set d : ℕ → ℝ := fun n ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) with hd
  have h1 := ht.isBigO_one ℝ
  have h2 : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, d k) =ᶠ[atTop]
      fun n : ℕ ↦ (∑ k ∈ Finset.Icc 1 n, d k) / n * n := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    field_simp
  have hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, d k) =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
    refine h2.trans_isBigO ?_
    refine (h1.mul (Asymptotics.isBigO_refl (fun n : ℕ ↦ (n : ℝ)) atTop)).congr_right fun n ↦ ?_
    rw [Real.rpow_one, one_mul]
  have h4 := LSeriesSummable_of_sum_norm_bigO_and_nonneg hO (fun n ↦ Nat.cast_nonneg _)
    zero_le_one (by simpa using hs)
  refine (LSeriesSummable_congr s fun {n} _ ↦ ?_).1 h4
  simp [hd]

variable {K}

theorem rayZetaCoeff_le (𝔣 : Ideal (𝓞 K)) (C : NarrowRayClassGroup K 𝔣) (n : ℕ) :
    M4aTorus.rayZetaCoeff K 𝔣 C n ≤ Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} := by
  haveI : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
    (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).to_subtype
  refine Nat.card_le_card_of_injective
    (fun I => (⟨(I.1 : Ideal (𝓞 K)), I.2.1⟩ : {I : Ideal (𝓞 K) // Ideal.absNorm I = n})) ?_
  intro I J h
  simp only [Subtype.mk.injEq] at h
  exact Subtype.ext (Subtype.ext h)

theorem summable_rayZetaCoeff (𝔣 : Ideal (𝓞 K)) (C : NarrowRayClassGroup K 𝔣) {s : ℂ}
    (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (M4aTorus.rayZetaCoeff K 𝔣 C n : ℂ)) s := by
  have h := summable_card_absNorm K hs
  rw [LSeriesSummable, ← summable_norm_iff] at h ⊢
  refine h.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun n ↦ ?_
  refine LSeries.norm_term_le s ?_
  simp only [Complex.norm_natCast, Nat.cast_le]
  exact rayZetaCoeff_le 𝔣 C n

def coeff (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ) (n : ℕ) : ℂ :=
  ∑' C : NarrowRayClassGroup K 𝔣, χ C * (M4aTorus.rayZetaCoeff K 𝔣 C n : ℂ)

theorem coeff_eq_sum {𝔣 : Ideal (𝓞 K)} [Fintype (NarrowRayClassGroup K 𝔣)]
    (χ : NarrowRayClassGroup K 𝔣 →* ℂ) :
    coeff 𝔣 χ = ∑ C : NarrowRayClassGroup K 𝔣,
      (χ C • fun n ↦ (M4aTorus.rayZetaCoeff K 𝔣 C n : ℂ)) := by
  funext n
  rw [coeff, tsum_fintype, Finset.sum_apply]
  rfl

theorem summable_coeff {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
    {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (coeff 𝔣 χ) s := by
  haveI : Finite (NarrowRayClassGroup K 𝔣) := Deep.NTSupply.finite K h𝔣
  haveI : Fintype (NarrowRayClassGroup K 𝔣) := Fintype.ofFinite _
  rw [coeff_eq_sum]
  exact LSeriesSummable.sum fun C _ ↦ (summable_rayZetaCoeff 𝔣 C hs).smul _

theorem rayClassLSeries_eq_LSeries {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥)
    (χ : NarrowRayClassGroup K 𝔣 →* ℂ) {s : ℂ} (hs : 1 < s.re) :
    M4aTorus.rayClassLSeries K 𝔣 χ s = LSeries (coeff 𝔣 χ) s := by
  haveI : Finite (NarrowRayClassGroup K 𝔣) := Deep.NTSupply.finite K h𝔣
  haveI : Fintype (NarrowRayClassGroup K 𝔣) := Fintype.ofFinite _
  rw [M4aTorus.rayClassLSeries, tsum_fintype, coeff_eq_sum,
    LSeries_sum fun C _ ↦ (summable_rayZetaCoeff 𝔣 C hs).smul _]
  refine Finset.sum_congr rfl fun C _ ↦ ?_
  rw [M4aTorus.rayZeta, LSeries_smul]

theorem rayZetaCoeff_one (𝔣 : Ideal (𝓞 K)) (C : NarrowRayClassGroup K 𝔣) :
    M4aTorus.rayZetaCoeff K 𝔣 C 1 = if C = 1 then 1 else 0 := by
  have htop : ((⊤ : Ideal (𝓞 K)) : Ideal (𝓞 K)) ∈ (Ideal (𝓞 K))⁰ :=
    mem_nonZeroDivisors_of_ne_zero (by simp)
  have hunit : FractionalIdeal.mk0 K (⟨⊤, htop⟩ : ↥(Ideal (𝓞 K))⁰) = 1 := by
    refine Units.ext ?_
    rw [FractionalIdeal.coe_mk0, Units.val_one]
    exact FractionalIdeal.coeIdeal_top (R := 𝓞 K) (S := (𝓞 K)⁰) (P := K)
  have hone : ∀ hc : FractionalIdeal.mk0 K (⟨⊤, htop⟩ : ↥(Ideal (𝓞 K))⁰) ∈ coprimeToModulus K 𝔣,
      NarrowRayClassGroup.mk K 𝔣 ⟨FractionalIdeal.mk0 K ⟨⊤, htop⟩, hc⟩ = 1 := by
    intro hc
    have : (⟨FractionalIdeal.mk0 K ⟨⊤, htop⟩, hc⟩ : ↥(coprimeToModulus K 𝔣)) = 1 :=
      Subtype.ext hunit
    rw [this, map_one]
  unfold M4aTorus.rayZetaCoeff
  split_ifs with hC
  · subst hC
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨⟨⊤, htop⟩, Ideal.absNorm_top, hunit ▸ one_mem _, hone _⟩, ?_⟩
    rintro ⟨I, hI, hc, hIC⟩
    have hI' : (I : Ideal (𝓞 K)) = ⊤ := Ideal.absNorm_eq_one_iff.mp hI
    exact Subtype.ext (Subtype.ext hI')
  · rw [Nat.card_eq_zero]
    left
    constructor
    rintro ⟨I, hI, hc, hIC⟩
    have hI' : (I : Ideal (𝓞 K)) = ⊤ := Ideal.absNorm_eq_one_iff.mp hI
    have hI'' : I = ⟨⊤, htop⟩ := Subtype.ext hI'
    subst hI''
    exact hC ((hone hc).symm.trans hIC).symm

theorem coeff_one {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) (χ : NarrowRayClassGroup K 𝔣 →* ℂ) :
    coeff 𝔣 χ 1 = 1 := by
  haveI : Finite (NarrowRayClassGroup K 𝔣) := Deep.NTSupply.finite K h𝔣
  haveI : Fintype (NarrowRayClassGroup K 𝔣) := Fintype.ofFinite _
  rw [coeff, tsum_fintype]
  simp_rw [rayZetaCoeff_one]
  simp

theorem exists_completedRayL_ne_zero {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥)
    (χ : NarrowRayClassGroup K 𝔣 →* ℂ) (S : Finset {w : InfinitePlace K // w.IsReal}) :
    ∃ t : ℝ, 1 < t ∧ M4aTorus.completedRayL K 𝔣 χ S t ≠ 0 := by
  have ha : LSeries.abscissaOfAbsConv (coeff 𝔣 χ) < ⊤ :=
    (summable_coeff h𝔣 χ (s := 2) (by norm_num)).abscissaOfAbsConv_le.trans_lt (by simp)
  have ht := LSeries.tendsto_atTop ha
  rw [coeff_one h𝔣] at ht
  obtain ⟨t, ht1, hne⟩ := ((eventually_gt_atTop (1 : ℝ)).and (ht.eventually_ne one_ne_zero)).exists
  refine ⟨t, ht1, ?_⟩
  have hre : 1 < (t : ℂ).re := by simpa using ht1
  have hre0 : 0 < (t : ℂ).re := by simp; linarith
  have hre1 : 0 < ((t : ℂ) + 1).re := by simp; linarith
  unfold M4aTorus.completedRayL
  rw [rayClassLSeries_eq_LSeries h𝔣 χ hre]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) hne
  · rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    left
    have h1 : (0 : ℝ) < |(discr K : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))
    have h2 : (0 : ℝ) < (Ideal.absNorm 𝔣 : ℝ) := by
      have : Ideal.absNorm 𝔣 ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff]
        exact h𝔣
      positivity
    exact_mod_cast (mul_pos h1 h2).ne'
  · exact pow_ne_zero _ (Complex.Gammaℝ_ne_zero_of_re_pos hre0)
  · exact pow_ne_zero _ (Complex.Gammaℝ_ne_zero_of_re_pos hre1)
  · refine pow_ne_zero _ ?_
    rw [← Complex.Gammaℝ_mul_Gammaℝ_add_one]
    exact mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hre0)
      (Complex.Gammaℝ_ne_zero_of_re_pos hre1)

def sigmaEquiv (n : ℕ) :
    (Σ C : NarrowRayClassGroup K ⊤, {I : ↥(Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) = n ∧
      ∃ hc : FractionalIdeal.mk0 K I ∈ coprimeToModulus K ⊤,
        NarrowRayClassGroup.mk K ⊤ ⟨FractionalIdeal.mk0 K I, hc⟩ = C}) ≃
    {I : ↥(Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) = n} where
  toFun x := ⟨x.2.1, x.2.2.1⟩
  invFun I := ⟨NarrowRayClassGroup.mk K ⊤ ⟨FractionalIdeal.mk0 K I.1, by
      rw [coprimeToModulus_top]; trivial⟩, I.1, I.2, by rw [coprimeToModulus_top]; trivial, rfl⟩
  left_inv := by
    rintro ⟨C, I, hn, hc, rfl⟩
    rfl
  right_inv I := rfl

theorem rayClassLSeries_top_one {s : ℂ} (hs : 1 < s.re) :
    M4aTorus.rayClassLSeries K ⊤ 1 s = dedekindZeta K s := by
  have htop : (⊤ : Ideal (𝓞 K)) ≠ ⊥ := by simp
  haveI : Finite (NarrowRayClassGroup K ⊤) := Deep.NTSupply.finite K htop
  haveI : Fintype (NarrowRayClassGroup K ⊤) := Fintype.ofFinite _
  rw [rayClassLSeries_eq_LSeries htop 1 hs, dedekindZeta]
  refine LSeries_congr (fun {n} hn ↦ ?_) s
  rw [coeff, tsum_fintype]
  simp only [MonoidHom.one_apply, one_mul]
  rw [← Nat.cast_sum, Nat.cast_inj]
  haveI : ∀ C : NarrowRayClassGroup K ⊤, Finite {I : ↥(Ideal (𝓞 K))⁰ //
      Ideal.absNorm (I : Ideal (𝓞 K)) = n ∧ ∃ hc : FractionalIdeal.mk0 K I ∈ coprimeToModulus K ⊤,
        NarrowRayClassGroup.mk K ⊤ ⟨FractionalIdeal.mk0 K I, hc⟩ = C} := by
    intro C
    haveI : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
      (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).to_subtype
    exact Finite.of_injective
      (fun I => (⟨(I.1 : Ideal (𝓞 K)), I.2.1⟩ : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}))
      (fun I J h => Subtype.ext (Subtype.ext (by simpa using h)))
  unfold M4aTorus.rayZetaCoeff
  rw [← Nat.card_sigma, Nat.card_congr (sigmaEquiv n)]
  refine Nat.card_congr ⟨fun I => ⟨I.1, I.2⟩, fun I => ⟨⟨I.1, mem_nonZeroDivisors_of_ne_zero ?_⟩, I.2⟩,
    fun I => rfl, fun I => rfl⟩
  intro h
  have := I.2
  rw [h, Submodule.zero_eq_bot, Ideal.absNorm_bot] at this
  exact hn this.symm

theorem completedRayL_top_one {s : ℂ} (hs : 1 < s.re) :
    M4aTorus.completedRayL K ⊤ 1 ∅ s =
      ((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2) * Complex.Gammaℝ s ^ nrRealPlaces K *
        Complex.Gammaℂ s ^ nrComplexPlaces K * dedekindZeta K s := by
  unfold M4aTorus.completedRayL
  rw [rayClassLSeries_top_one hs, Ideal.absNorm_top, Finset.card_empty, Nat.sub_zero, pow_zero,
    mul_one, Nat.cast_one, mul_one, ← Int.cast_abs, Complex.ofReal_intCast]

end Aux

section AuxZero

variable (K : Type) [Field K] [NumberField K]

theorem chi_ne_zero {𝔣 : Ideal (𝓞 K)} (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
    (g : NarrowRayClassGroup K 𝔣) : χ g ≠ 0 := by
  have h : χ g * χ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  exact left_ne_zero_of_mul_eq_one h

theorem chiIdeal_span_eq {𝔣 : Ideal (𝓞 K)} (χ : NarrowRayClassGroup K 𝔣 →* ℂ) (α : 𝓞 K)
    (hα : α ≠ 0) (hc : principalUnit K α hα ∈ coprimeToModulus K 𝔣) :
    M4aP2.chiIdeal K 𝔣 χ ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      χ (NarrowRayClassGroup.mk K 𝔣 ⟨principalUnit K α hα, hc⟩) := by
  have hne : ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.span_singleton_eq_bot]
    exact hα
  have hu : Units.mk0 _ hne = principalUnit K α hα :=
    Units.ext (by rw [Units.val_mk0, principalUnit_val])
  have hc' : Units.mk0 _ hne ∈ coprimeToModulus K 𝔣 := hu ▸ hc
  rw [M4aP2.chiIdeal, dif_pos hne, dif_pos hc']
  congr

theorem isParity_of {𝔣 : Ideal (𝓞 K)} (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
    (S : Finset {w : InfinitePlace K // w.IsReal})
    (hpar : ∀ (α : 𝓞 K) (hα : α ≠ 0) (hc : principalUnit K α hα ∈ coprimeToModulus K 𝔣),
      α - 1 ∈ 𝔣 →
        χ (NarrowRayClassGroup.mk K 𝔣 ⟨principalUnit K α hα, hc⟩) =
          ∏ w ∈ S, ((SignType.sign (embedding_of_isReal w.2 (α : K)) : ℤ) : ℂ)) :
    M4aP2.IsParity K 𝔣 χ S := by
  intro α hα h1
  have hc := principalUnit_mem_coprimeToModulus K hα h1
  rw [chiIdeal_span_eq K χ α hα hc, hpar α hα hc h1]
  rfl

theorem isPrimitiveMod_of {𝔣 : Ideal (𝓞 K)} (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
    (hprim : ∀ 𝔣' : Ideal (𝓞 K), 𝔣 ≤ 𝔣' → 𝔣' ≠ 𝔣 →
      ∃ (α : 𝓞 K) (hα : α ≠ 0) (hc : principalUnit K α hα ∈ coprimeToModulus K 𝔣),
        α - 1 ∈ 𝔣' ∧ (∀ τ : K →+* ℝ, 0 < τ (α : K)) ∧
          χ (NarrowRayClassGroup.mk K 𝔣 ⟨principalUnit K α hα, hc⟩) ≠ 1) :
    M4aP2.IsPrimitiveMod K 𝔣 χ := by
  intro 𝔣' hle hne
  obtain ⟨α, hα, hc, h1, hpos, hχ⟩ := hprim 𝔣' hle hne
  refine ⟨α, hα, h1, hpos, ?_, ?_⟩
  · rw [chiIdeal_span_eq K χ α hα hc]
    exact chi_ne_zero K χ _
  · rw [chiIdeal_span_eq K χ α hα hc]
    exact hχ

theorem eq_of_forall_ne {f g : ℂ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → f s = g s) : f = g := by
  have hd : Dense ((Set.univ : Set ℂ) \ {0, 1}) :=
    dense_univ.diff_finite (Set.toFinite _)
  refine Continuous.ext_on hd hf hg fun s hs => ?_
  simp only [Set.mem_diff, Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff,
    true_and, not_or] at hs
  exact h s hs.1 hs.2

theorem conj_comp_one {G : Type*} [Group G] :
    (starRingEnd ℂ).toMonoidHom.comp (1 : G →* ℂ) = 1 := by
  refine MonoidHom.ext fun g => ?_
  simp

theorem core (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
    (χ : NarrowRayClassGroup K 𝔣 →* ℂ) (S : Finset {w : InfinitePlace K // w.IsReal})
    (hpar : ∀ (α : 𝓞 K) (hα : α ≠ 0) (hc : principalUnit K α hα ∈ coprimeToModulus K 𝔣),
      α - 1 ∈ 𝔣 →
        χ (NarrowRayClassGroup.mk K 𝔣 ⟨principalUnit K α hα, hc⟩) =
          ∏ w ∈ S, ((SignType.sign (embedding_of_isReal w.2 (α : K)) : ℤ) : ℂ))
    (hprim : ∀ 𝔣' : Ideal (𝓞 K), 𝔣 ≤ 𝔣' → 𝔣' ≠ 𝔣 →
      ∃ (α : 𝓞 K) (hα : α ≠ 0) (hc : principalUnit K α hα ∈ coprimeToModulus K 𝔣),
        α - 1 ∈ 𝔣' ∧ (∀ τ : K →+* ℝ, 0 < τ (α : K)) ∧
          χ (NarrowRayClassGroup.mk K 𝔣 ⟨principalUnit K α hα, hc⟩) ≠ 1) :
    ∃ (W : ℂ) (Λ Λ' : ℂ → ℂ), W ≠ 0 ∧ Differentiable ℂ Λ ∧ Differentiable ℂ Λ' ∧
      (∀ s : ℂ, 1 < s.re →
        Λ s = (if χ = 1 then s * (s - 1) else 1) * M4aTorus.completedRayL K 𝔣 χ S s ∧
        Λ' s = (if χ = 1 then s * (s - 1) else 1) *
          M4aTorus.completedRayL K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S s) ∧
      (∀ s : ℂ, Λ (1 - s) = W * Λ' s) := by
  by_cases hχ : χ = 1
  ·
    subst hχ
    have htop : 𝔣 = ⊤ := by
      by_contra h
      obtain ⟨α, hα, hc, -, -, hne⟩ := hprim ⊤ le_top (Ne.symm h)
      exact hne (by rw [MonoidHom.one_apply])
    subst htop
    have hS : S = ∅ := by
      by_contra hS
      obtain ⟨w₀, hw₀⟩ := Finset.nonempty_iff_ne_empty.mpr hS
      obtain ⟨α, hα0, hneg, hpos⟩ := exists_neg_pos K w₀
      have hc : principalUnit K α hα0 ∈ coprimeToModulus K ⊤ := by
        rw [coprimeToModulus_top]; trivial
      have h := hpar α hα0 hc Submodule.mem_top
      rw [MonoidHom.one_apply, ← Finset.mul_prod_erase S _ hw₀, sign_neg hneg,
        Finset.prod_eq_one (fun w hw => by
          rw [sign_pos (hpos w (Finset.ne_of_mem_erase hw))]
          simp)] at h
      simp only [SignType.coe_neg_one, Int.cast_neg, Int.cast_one, mul_one] at h
      norm_num at h
    subst hS
    obtain ⟨Λ, -, hΛfe, hΛeq, ⟨ξ, hξd, hξeq, -⟩, -, -⟩ :=
      NumberField.exists_completedDedekindZeta_package K
    have hfe : ∀ s : ℂ, ξ (1 - s) = ξ s := by
      have := eq_of_forall_ne (f := fun s => ξ (1 - s)) (g := ξ)
        (hξd.continuous.comp (continuous_const.sub continuous_id)) hξd.continuous
        (fun s h0 h1 => by
          have h0' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
          have h1' : (1 : ℂ) - s ≠ 1 := by
            intro h; apply h0; simpa using h
          show ξ (1 - s) = ξ s
          rw [hξeq _ h0' h1', hξeq _ h0 h1, hΛfe s h0 h1]
          ring)
      exact fun s => congrFun this s
    refine ⟨1, ξ, ξ, one_ne_zero, hξd, hξd, fun s hs => ?_, fun s => by rw [one_mul, hfe]⟩
    have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
    have hs1 : s ≠ 1 := by rintro rfl; norm_num at hs
    rw [if_pos rfl, conj_comp_one, hξeq s hs0 hs1, hΛeq s hs, completedRayL_top_one hs]
    exact ⟨by ring, by ring⟩
  ·
    have hparity : M4aP2.IsParity K 𝔣 χ S := isParity_of K χ S hpar
    by_cases htop : 𝔣 = ⊤
    · subst htop
      obtain ⟨W, Λ, Λ', hW, hΛ, hΛ', heq, hfe⟩ :=
        NumberField.exists_completedRayL_functionalEquation_of_modulus_top K χ hχ S hparity
      refine ⟨W, Λ, Λ', hW, hΛ, hΛ', fun s hs => ?_, hfe⟩
      rw [if_neg hχ, one_mul, one_mul]
      exact heq s hs
    · obtain ⟨F, G, -, -, hFeq, hGeq, hfe, hent⟩ := M4aTorus.completedRayL_fe K 𝔣 χ S hparity
      obtain ⟨hFd, hGd⟩ := hent hχ
      obtain ⟨y₀, hy₀⟩ := NumberField.exists_isGaussDatum K 𝔣 h𝔣 χ
      have hprim' : M4aP2.IsPrimitiveMod K 𝔣 χ := isPrimitiveMod_of K χ hprim
      set W : ℂ := (-Complex.I) ^ S.card *
        (M4aP2.gaussSumAt K 𝔣 χ h𝔣 S y₀ / (Real.sqrt (Ideal.absNorm 𝔣) : ℂ)) with hWdef
      have hfe' : ∀ s : ℂ, F (1 - s) = W * G s := by
        have := eq_of_forall_ne (f := fun s => F (1 - s)) (g := fun s => W * G s)
          (hFd.continuous.comp (continuous_const.sub continuous_id))
          (continuous_const.mul hGd.continuous)
          (fun s h0 h1 => by
            show F (1 - s) = W * G s
            rw [hfe h𝔣 htop y₀ hy₀ hprim' s h0 h1, hWdef, mul_assoc])
        exact fun s => congrFun this s
      have hW : W ≠ 0 := by
        intro hW0
        obtain ⟨t, ht, hne⟩ := exists_completedRayL_ne_zero (K := K) h𝔣 χ S
        apply hne
        have h1 : F (t : ℂ) = 0 := by
          have := hfe' (1 - t)
          rwa [hW0, zero_mul, sub_sub_cancel] at this
        rw [← hFeq t (by simpa using ht)]
        exact h1
      refine ⟨W, F, G, hW, hFd, hGd, fun s hs => ?_, hfe'⟩
      rw [if_neg hχ, one_mul, one_mul]
      exact ⟨hFeq s hs, hGeq s hs⟩

end AuxZero

end HeckePrimFE
p2m_reactivate "P2MW.S_NumberField_exists_completedRayL_functionalEquation_of_primitive.HeckePrimFE"

open HeckePrimFE in
theorem solution
    (K : Type u) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
    (χ : NarrowRayClassGroup K 𝔣 →* ℂ) (S : Finset {w : InfinitePlace K // w.IsReal})
    (hpar : ∀ (α : 𝓞 K) (hα : α ≠ 0) (hc : principalUnit K α hα ∈ coprimeToModulus K 𝔣),
      α - 1 ∈ 𝔣 →
        χ (NarrowRayClassGroup.mk K 𝔣 ⟨principalUnit K α hα, hc⟩) =
          ∏ w ∈ S, ((SignType.sign (embedding_of_isReal w.2 (α : K)) : ℤ) : ℂ))
    (hprim : ∀ 𝔣' : Ideal (𝓞 K), 𝔣 ≤ 𝔣' → 𝔣' ≠ 𝔣 →
      ∃ (α : 𝓞 K) (hα : α ≠ 0) (hc : principalUnit K α hα ∈ coprimeToModulus K 𝔣),
        α - 1 ∈ 𝔣' ∧ (∀ τ : K →+* ℝ, 0 < τ (α : K)) ∧
          χ (NarrowRayClassGroup.mk K 𝔣 ⟨principalUnit K α hα, hc⟩) ≠ 1) :
    ∃ (W : ℂ) (Λ Λ' : ℂ → ℂ), W ≠ 0 ∧ Differentiable ℂ Λ ∧ Differentiable ℂ Λ' ∧
      (∀ s : ℂ, 1 < s.re →
        Λ s = (if χ = 1 then s * (s - 1) else 1) * M4aTorus.completedRayL K 𝔣 χ S s ∧
        Λ' s = (if χ = 1 then s * (s - 1) else 1) *
          M4aTorus.completedRayL K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S s) ∧
      (∀ s : ℂ, Λ (1 - s) = W * Λ' s) := by
  haveI : Countable K := countable_of_numberField K
  let L : Type := Shrink.{0} K
  let e : K ≃+* L := (Shrink.ringEquiv.{0} K).symm
  haveI : NumberField L := numberField_of_ringEquiv e
  have h𝔣' : 𝔣.map (intEquiv e) ≠ ⊥ := (map_ne_bot_iff e).mpr h𝔣
  obtain ⟨W, Λ, Λ', hW, hΛ, hΛ', heq, hfe⟩ :=
    core L (𝔣.map (intEquiv e)) h𝔣' (chiMap e 𝔣 χ) (sMap e S) (parity_map e 𝔣 χ S hpar)
      (primitive_map e 𝔣 χ hprim)
  refine ⟨W, Λ, Λ', hW, hΛ, hΛ', fun s hs => ?_, hfe⟩
  obtain ⟨h1, h2⟩ := heq s hs
  rw [completedRayL_map] at h1
  rw [← chiMap_conj, completedRayL_map] at h2
  by_cases hχ : χ = 1
  · have hχ' : chiMap e 𝔣 χ = 1 := (chiMap_eq_one_iff e 𝔣 χ).mpr hχ
    rw [if_pos hχ'] at h1 h2
    rw [if_pos hχ]
    exact ⟨h1, h2⟩
  · have hχ' : chiMap e 𝔣 χ ≠ 1 := fun h => hχ ((chiMap_eq_one_iff e 𝔣 χ).mp h)
    rw [if_neg hχ'] at h1 h2
    rw [if_neg hχ]
    exact ⟨h1, h2⟩

end
p2m_reactivate "P2MW.S_NumberField_exists_completedRayL_functionalEquation_of_primitive.HeckePrimFE"

end S_NumberField_exists_completedRayL_functionalEquation_of_primitive
end P2MW
export P2MW.S_NumberField_exists_completedRayL_functionalEquation_of_primitive (solution)
