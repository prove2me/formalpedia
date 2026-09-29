-- Prove2me | solution 1 for HeckeCharacter.fracRelNormUnit_fadContentHom_projFin_unitsMap_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/10d7ec26-7f03-5358-a9f5-1dcb0ad95d30

import Mathlib
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Theorems.Thm_HeckeCharacter_coe_fadContentHom_projFin_unitsMap_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeCharacter_fracRelNormUnit_fadContentHom_projFin_unitsMap_algebraMap

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors

namespace PrincNormAux

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

scoped instance liesOver_placeUnder' (w : HeightOneSpectrum (𝓞 L)) :
    w.asIdeal.LiesOver (placeUnder' K L w).asIdeal := ⟨rfl⟩

theorem relNorm_eq_finprod (J : Ideal (𝓞 L)) (hJ : J ≠ ⊥) :
    Ideal.relNorm (𝓞 K) J = ∏ᶠ w : HeightOneSpectrum (𝓞 L),
      ((placeUnder' K L w).asIdeal ^ ((placeUnder' K L w).asIdeal.inertiaDeg' w.asIdeal)) ^
        (Associates.mk w.asIdeal).count (Associates.mk J).factors := by
  have hJ0 : J ≠ 0 := by rwa [Ne, Submodule.zero_eq_bot]
  conv_lhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hJ0]
  rw [map_finprod (Ideal.relNorm (𝓞 K)) (Ideal.hasFiniteMulSupport hJ0)]
  refine finprod_congr fun w => ?_
  haveI := w.isMaximal
  haveI := (placeUnder' K L w).isMaximal
  rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, map_pow,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (placeUnder' K L w).asIdeal,
    Ideal.inertiaDeg'_eq_inertiaDeg (placeUnder' K L w).asIdeal w.asIdeal]

theorem coe_fracRelNormUnit_eq_coe_relNorm (J : (FractionalIdeal ((𝓞 L)⁰) L)ˣ) (I : Ideal (𝓞 L)) (hI : I ≠ ⊥)
    (hJ : (J : FractionalIdeal ((𝓞 L)⁰) L) = (I : FractionalIdeal ((𝓞 L)⁰) L)) :
    ((fracRelNormUnit K L J : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) =
      ((Ideal.relNorm (𝓞 K) I : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) := by
  have hI0 : I ≠ 0 := by rwa [Ne, Submodule.zero_eq_bot]
  show ((∏ᶠ w : HeightOneSpectrum (𝓞 L),
      (primeUnit K (placeUnder' K L w) ^ ((placeUnder' K L w).asIdeal.inertiaDeg' w.asIdeal)) ^
        FractionalIdeal.count L w (J : FractionalIdeal ((𝓞 L)⁰) L) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) :
      FractionalIdeal ((𝓞 K)⁰) K) = _
  rw [hJ, relNorm_eq_finprod K L I hI]
  have hmap := MonoidHom.map_finprod (Units.coeHom (FractionalIdeal ((𝓞 K)⁰) K))
    (hasFiniteMulSupport_raySymbol_factors L
      (fun w => primeUnit K (placeUnder' K L w) ^ ((placeUnder' K L w).asIdeal.inertiaDeg' w.asIdeal))
      (I : FractionalIdeal ((𝓞 L)⁰) L))
  simp only [Units.coeHom_apply] at hmap
  rw [hmap, FractionalIdeal.coeIdeal_finprod ((𝓞 K)⁰) K le_rfl]
  refine finprod_congr fun w => ?_
  rw [FractionalIdeal.count_coe L w hI0, zpow_natCast, Units.val_pow_eq_pow_val,
    Units.val_pow_eq_pow_val, primeUnit_val, FractionalIdeal.coeIdeal_pow, FractionalIdeal.coeIdeal_pow]

end PrincNormAux
p2m_reactivate "P2MW.S_HeckeCharacter_fracRelNormUnit_fadContentHom_projFin_unitsMap_algebraMap.PrincNormAux"

open PrincNormAux in
theorem solution
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (β : Lˣ) :
    fracRelNormUnit K L
        (fadContentHom L (projFin L (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) β))) =
      fadContentHom K (projFin K
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (Units.map (Algebra.norm K : L →* K) β))) := by
  set G : Lˣ →* (FractionalIdeal ((𝓞 K)⁰) K)ˣ := (fracRelNormUnit K L).comp ((fadContentHom L).comp
    ((projFin L).comp (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)))) with hG
  set H : Lˣ →* (FractionalIdeal ((𝓞 K)⁰) K)ˣ := (fadContentHom K).comp ((projFin K).comp
    ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).comp (Units.map (Algebra.norm K : L →* K)))) with hH
  change G β = H β

  have key : ∀ (b : 𝓞 L) (hb : (b : L) ≠ 0), G (Units.mk0 (b : L) hb) = H (Units.mk0 (b : L) hb) := by
    intro b hb
    rw [hG, hH]
    simp only [MonoidHom.comp_apply]
    have hb' : b ≠ 0 := fun h => hb (by rw [h]; rfl)
    have hb0 : (Ideal.span {b} : Ideal (𝓞 L)) ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact hb'
    apply Units.ext
    have hL : ((fadContentHom L (projFin L (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)
        (Units.mk0 (b : L) hb))) : (FractionalIdeal ((𝓞 L)⁰) L)ˣ) : FractionalIdeal ((𝓞 L)⁰) L) =
        ((Ideal.span {b} : Ideal (𝓞 L)) : FractionalIdeal ((𝓞 L)⁰) L) := by
      rw [HeckeCharacter.coe_fadContentHom_projFin_unitsMap_algebraMap, FractionalIdeal.coeIdeal_span_singleton]
      rfl
    rw [coe_fracRelNormUnit_eq_coe_relNorm K L _ (Ideal.span {b}) hb0 hL,
      HeckeCharacter.coe_fadContentHom_projFin_unitsMap_algebraMap, Ideal.relNorm_singleton,
      FractionalIdeal.coeIdeal_span_singleton, Units.coe_map, Units.val_mk0,
      Algebra.algebraMap_intNorm (K := K) (L := L)]

  obtain ⟨b, c, hc, hbc⟩ := IsFractionRing.div_surjective (A := 𝓞 L) (β : L)
  have hc0 : ((c : 𝓞 L) : L) ≠ 0 := by
    have : (c : 𝓞 L) ≠ 0 := nonZeroDivisors.ne_zero hc
    exact fun h => this (by exact_mod_cast h)
  have hb0 : ((b : 𝓞 L) : L) ≠ 0 := by
    intro h
    apply β.ne_zero
    rw [← hbc]
    change (b : L) / (c : L) = 0
    rw [h, zero_div]
  have hβ : β = Units.mk0 (b : L) hb0 / Units.mk0 (c : L) hc0 := by
    apply Units.ext
    rw [Units.val_div_eq_div_val, Units.val_mk0, Units.val_mk0]
    exact hbc.symm
  rw [hβ, map_div, map_div, key, key]

end S_HeckeCharacter_fracRelNormUnit_fadContentHom_projFin_unitsMap_algebraMap
end P2MW
export P2MW.S_HeckeCharacter_fracRelNormUnit_fadContentHom_projFin_unitsMap_algebraMap (solution)
