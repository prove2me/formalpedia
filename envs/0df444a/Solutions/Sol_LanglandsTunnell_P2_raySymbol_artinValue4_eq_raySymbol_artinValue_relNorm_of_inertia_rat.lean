-- Prove2me | solution 1 for LanglandsTunnell.P2.raySymbol_artinValue4_eq_raySymbol_artinValue_relNorm_of_inertia_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/b0603b73-d255-52c2-92ec-a2fd4f2110de

import Definitions.Def_LanglandsTunnell_C4Character
import Definitions.Def_LanglandsTunnell_ArtinFrobenius
import Theorems.Thm_AlgebraicCurve_relNorm_eq_pow_of_isMaximal_of_isSeparable
import Theorems.Thm_LanglandsTunnell_artinValue4_eq_artinValue_under_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_P2_raySymbol_artinValue4_eq_raySymbol_artinValue_relNorm_of_inertia_rat
p2m_attr_erase "instance" "FrobeniusDensity.isMaximal_ratPrimeIdeal"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false

p2m_open "NumberField IsDedekindDomain Deep.NTSupply LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_raySymbol_artinValue4_eq_raySymbol_artinValue_relNorm_of_inertia_rat.LanglandsTunnell.P2 LanglandsTunnell.P2.Artin LanglandsTunnell P2MW.S_LanglandsTunnell_P2_raySymbol_artinValue4_eq_raySymbol_artinValue_relNorm_of_inertia_rat.LanglandsTunnell"
open scoped nonZeroDivisors
open scoped Pointwise

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "artinValue4_eq_artinValue_under_pow"
namespace P2
p2m_export "LanglandsTunnell.P2" "c4H artinValue4 c8H artinValue"
namespace TransferSol
p2m_open "LanglandsTunnell.P2 LanglandsTunnell"

variable {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
  (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) {ζ : ℂ} (hζ : ζ ^ 4 = -1)

local notation3 "K″" => (FixedPoints.intermediateField (c4H e) : IntermediateField ℚ L)
local notation3 "K′" => (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L)

private theorem _root_.LanglandsTunnell.P2.TransferSol.artinValue4_eq_artinValue_under_pow
    (w : HeightOneSpectrum (𝓞 K″))
    (hw : (primeAbove K″ L w).inertia (L ≃ₐ[ℚ] L) = ⊥) :
    artinValue4 e hζ w
      = artinValue e hζ (w.under (𝓞 K′)) ^ ((w.under (𝓞 K′)).asIdeal.inertiaDeg' w.asIdeal) :=
  LanglandsTunnell.artinValue4_eq_artinValue_under_pow e hζ w hw

p2m_export "LanglandsTunnell.P2.TransferSol" "artinValue4_eq_artinValue_under_pow"
section P2Probe

private scoped instance (w : HeightOneSpectrum (𝓞 K″)) :
    w.asIdeal.LiesOver (w.under (𝓞 K′)).asIdeal := ⟨rfl⟩

omit [IsGalois ℚ L] in
private theorem relNorm_asIdeal_eq_pow_under (w : HeightOneSpectrum (𝓞 K″)) :
    Ideal.relNorm (𝓞 K′) w.asIdeal
      = (w.under (𝓞 K′)).asIdeal ^ ((w.under (𝓞 K′)).asIdeal.inertiaDeg' w.asIdeal) :=
  AlgebraicCurve.relNorm_eq_pow_of_isMaximal_of_isSeparable (S := 𝓞 K″) K′ K″
    w.asIdeal (w.under (𝓞 K′)).asIdeal

omit [IsGalois ℚ L] in
private theorem count_coe_relNorm_prime
    (w₀ : HeightOneSpectrum (𝓞 K″)) (v : HeightOneSpectrum (𝓞 K′))
    [Decidable (w₀.under (𝓞 K′) = v)] :
    FractionalIdeal.count K′ v
        ((Ideal.relNorm (𝓞 K′) w₀.asIdeal : Ideal (𝓞 K′)) : FractionalIdeal ((𝓞 K′)⁰) K′)
      = if w₀.under (𝓞 K′) = v then ((v.asIdeal.inertiaDeg' w₀.asIdeal : ℤ)) else 0 := by
  rw [relNorm_asIdeal_eq_pow_under e, FractionalIdeal.coeIdeal_pow, FractionalIdeal.count_pow,
    FractionalIdeal.count_maximal]
  split_ifs with h
  · rw [mul_one, h]
  · rw [mul_zero]

omit [IsGalois ℚ L] in
private scoped instance (v : HeightOneSpectrum (𝓞 K′)) :
    Finite {w : HeightOneSpectrum (𝓞 K″) // w.under (𝓞 K′) = v} := by
  have hfin : ((v.asIdeal).primesOver (𝓞 K″)).Finite :=
    Algebra.QuasiFinite.finite_primesOver (R := 𝓞 K′) (S := 𝓞 K″) v.asIdeal
  have himg : (HeightOneSpectrum.asIdeal ''
      {w : HeightOneSpectrum (𝓞 K″) | w.under (𝓞 K′) = v}) ⊆ (v.asIdeal).primesOver (𝓞 K″) := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨w.isPrime, ⟨congrArg HeightOneSpectrum.asIdeal hw.symm⟩⟩
  exact Set.Finite.to_subtype
    (((hfin.subset himg).of_finite_image
      (fun w _ w' _ h => HeightOneSpectrum.ext h)))

end P2Probe

omit [IsGalois ℚ L] in
private theorem count_coe_relNorm_eq_sum
    (I : Ideal (𝓞 K″)) (hI : I ≠ ⊥) (v : HeightOneSpectrum (𝓞 K′)) :
    FractionalIdeal.count K′ v
        (((Ideal.relNorm (𝓞 K′) I : Ideal (𝓞 K′)) : FractionalIdeal ((𝓞 K′)⁰) K′))
      = ∑ᶠ w : {w : HeightOneSpectrum (𝓞 K″) // w.under (𝓞 K′) = v},
          (v.asIdeal.inertiaDeg' w.1.asIdeal : ℤ) * FractionalIdeal.count K″ w.1
            ((I : Ideal (𝓞 K″)) : FractionalIdeal ((𝓞 K″)⁰) K″) := by
  classical
  revert hI
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact fun h => absurd rfl h
  | h₂ J hJ =>
    intro _
    obtain rfl : J = ⊤ := by rwa [Ideal.isUnit_iff] at hJ
    rw [Ideal.relNorm_top]
    simp only [FractionalIdeal.coeIdeal_top, FractionalIdeal.count_one, mul_zero, finsum_zero]
  | h₃ J p hJ0 hp IH =>
    intro _
    have hJ : J ≠ ⊥ := hJ0
    have hp0 : p ≠ ⊥ := hp.ne_zero
    let w₀ : HeightOneSpectrum (𝓞 K″) := ⟨p, Ideal.isPrime_of_prime hp, hp0⟩
    have hp_eq : p = w₀.asIdeal := rfl
    have hrJ : (Ideal.relNorm (𝓞 K′) J : Ideal (𝓞 K′)) ≠ ⊥ := by
      rwa [Ne, Ideal.relNorm_eq_bot_iff]
    have hrp : (Ideal.relNorm (𝓞 K′) p : Ideal (𝓞 K′)) ≠ ⊥ := by
      rwa [Ne, Ideal.relNorm_eq_bot_iff]
    rw [map_mul, FractionalIdeal.coeIdeal_mul,
      FractionalIdeal.count_mul K′ v (FractionalIdeal.coeIdeal_ne_zero.mpr hrp)
        (FractionalIdeal.coeIdeal_ne_zero.mpr hrJ),
      IH hJ, hp_eq, count_coe_relNorm_prime e w₀ v]
    rw [show ((w₀.asIdeal * J : Ideal (𝓞 K″)) : FractionalIdeal ((𝓞 K″)⁰) K″)
          = (w₀.asIdeal : FractionalIdeal ((𝓞 K″)⁰) K″)
            * (J : FractionalIdeal ((𝓞 K″)⁰) K″) from FractionalIdeal.coeIdeal_mul _ _]
    simp_rw [FractionalIdeal.count_mul K″ _
        (FractionalIdeal.coeIdeal_ne_zero.mpr w₀.ne_bot)
        (FractionalIdeal.coeIdeal_ne_zero.mpr hJ),
      mul_add, FractionalIdeal.count_maximal K″, mul_ite, mul_one, mul_zero]
    rw [finsum_add_distrib (Set.finite_univ.subset (Set.subset_univ _))
        (Set.finite_univ.subset (Set.subset_univ _))]
    congr 1
    by_cases hw₀v : w₀.under (𝓞 K′) = v
    · rw [if_pos hw₀v,
        finsum_eq_single _ (⟨w₀, hw₀v⟩ : {w : HeightOneSpectrum (𝓞 K″) // w.under (𝓞 K′) = v})
          (fun w hw => by rw [if_neg (fun hc => hw (Subtype.ext hc.symm))]),
        if_pos rfl]
    · rw [if_neg hw₀v, eq_comm]
      exact finsum_eq_zero_of_forall_eq_zero fun w =>
        if_neg fun hc => hw₀v (by rw [hc]; exact w.2)

end LanglandsTunnell.P2.TransferSol
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_raySymbol_artinValue4_eq_raySymbol_artinValue_relNorm_of_inertia_rat.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_raySymbol_artinValue4_eq_raySymbol_artinValue_relNorm_of_inertia_rat.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_raySymbol_artinValue4_eq_raySymbol_artinValue_relNorm_of_inertia_rat.LanglandsTunnell.P2.TransferSol"
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_raySymbol_artinValue4_eq_raySymbol_artinValue_relNorm_of_inertia_rat.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_raySymbol_artinValue4_eq_raySymbol_artinValue_relNorm_of_inertia_rat.LanglandsTunnell.P2"
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_raySymbol_artinValue4_eq_raySymbol_artinValue_relNorm_of_inertia_rat.LanglandsTunnell"

open LanglandsTunnell.P2.TransferSol in

theorem solution
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) {ζ : ℂ} (hζ : ζ ^ 4 = -1)
    (I : Ideal (𝓞 (FixedPoints.intermediateField (c4H e) : IntermediateField ℚ L))) (hI : I ≠ ⊥)
    (hIunr : ∀ w : HeightOneSpectrum (𝓞 (FixedPoints.intermediateField (c4H e) : IntermediateField ℚ L)),
      FractionalIdeal.count (FixedPoints.intermediateField (c4H e) : IntermediateField ℚ L) w
          ((I : Ideal (𝓞 (FixedPoints.intermediateField (c4H e) : IntermediateField ℚ L))) :
            FractionalIdeal
              ((𝓞 (FixedPoints.intermediateField (c4H e) : IntermediateField ℚ L))⁰)
              (FixedPoints.intermediateField (c4H e) : IntermediateField ℚ L)) ≠ 0 →
      (primeAbove (FixedPoints.intermediateField (c4H e) : IntermediateField ℚ L) L w).inertia
        (L ≃ₐ[ℚ] L) = ⊥) :
    raySymbol (FixedPoints.intermediateField (c4H e) : IntermediateField ℚ L) (artinValue4 e hζ)
        ((I : Ideal (𝓞 (FixedPoints.intermediateField (c4H e) : IntermediateField ℚ L))) :
          FractionalIdeal
            ((𝓞 (FixedPoints.intermediateField (c4H e) : IntermediateField ℚ L))⁰)
            (FixedPoints.intermediateField (c4H e) : IntermediateField ℚ L))
      = raySymbol (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) (artinValue e hζ)
        ((Ideal.relNorm (𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L)) I :
            Ideal (𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L))) :
          FractionalIdeal
            ((𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L))⁰)
            (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L)) := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hI
  | h₂ J hJ =>
    obtain rfl : J = ⊤ := by rwa [Ideal.isUnit_iff] at hJ
    simp only [Ideal.relNorm_top, FractionalIdeal.coeIdeal_top, raySymbol,
      FractionalIdeal.count_one, zpow_zero, finprod_one]
  | h₃ J p hJ0 hp IH =>
    have hpJ : p * J ≠ ⊥ := hI
    have hJ : J ≠ ⊥ := right_ne_zero_of_mul hpJ
    have hp0 : p ≠ ⊥ := left_ne_zero_of_mul hpJ
    let K'' : IntermediateField ℚ L := FixedPoints.intermediateField (c4H e)
    let w₀ : HeightOneSpectrum (𝓞 K'') := ⟨p, Ideal.isPrime_of_prime hp, hp0⟩
    have hJunr : ∀ w : HeightOneSpectrum (𝓞 K''),
        FractionalIdeal.count K'' w
            ((J : Ideal _) : FractionalIdeal _ _) ≠ 0 →
          (primeAbove _ L w).inertia (L ≃ₐ[ℚ] L) = ⊥ := fun w hw => by
      refine hIunr w (fun hc => hw ?_)
      rw [FractionalIdeal.coeIdeal_mul, FractionalIdeal.count_mul K'' _
        ((FractionalIdeal.coeIdeal_ne_zero).mpr hp0)
        ((FractionalIdeal.coeIdeal_ne_zero).mpr hJ)] at hc
      exact ((add_eq_zero_iff_of_nonneg (FractionalIdeal.count_coe_nonneg K'' w p)
        (FractionalIdeal.count_coe_nonneg K'' w J)).mp hc).2
    have hw₀unr : (primeAbove _ L w₀).inertia (L ≃ₐ[ℚ] L) = ⊥ := by
      refine hIunr w₀ (fun hc => ?_)
      rw [FractionalIdeal.coeIdeal_mul, FractionalIdeal.count_mul K'' _
        ((FractionalIdeal.coeIdeal_ne_zero).mpr hp0)
        ((FractionalIdeal.coeIdeal_ne_zero).mpr hJ)] at hc
      exact one_ne_zero ((FractionalIdeal.count_self K'' w₀) ▸
        ((add_eq_zero_iff_of_nonneg ((FractionalIdeal.count_self K'' w₀) ▸ zero_le_one)
          (FractionalIdeal.count_coe_nonneg K'' w₀ J)).mp hc).1)
    rw [FractionalIdeal.coeIdeal_mul,
      raySymbol_mul _ _ ((FractionalIdeal.coeIdeal_ne_zero).mpr hp0)
        ((FractionalIdeal.coeIdeal_ne_zero).mpr hJ),
      map_mul (Ideal.relNorm _), FractionalIdeal.coeIdeal_mul,
      raySymbol_mul _ _
        ((FractionalIdeal.coeIdeal_ne_zero).mpr (by rwa [Ne, Ideal.relNorm_eq_bot_iff]))
        ((FractionalIdeal.coeIdeal_ne_zero).mpr (by rwa [Ne, Ideal.relNorm_eq_bot_iff])),
      IH hJ hJunr]
    congr 1
    let K' : IntermediateField ℚ L := FixedPoints.intermediateField (c8H e)
    have hp_asI : p = w₀.asIdeal := rfl
    rw [hp_asI,
      show ((w₀.asIdeal : Ideal (𝓞 K'')) : FractionalIdeal ((𝓞 K'')⁰) K'')
        = ↑(primeUnit K'' w₀) from (primeUnit_val K'' w₀).symm,
      raySymbol_primeUnit,
      relNorm_asIdeal_eq_pow_under (e := e), FractionalIdeal.coeIdeal_pow,
      show (((w₀.under (𝓞 K')).asIdeal : Ideal (𝓞 K')) : FractionalIdeal ((𝓞 K')⁰) K')
        = ↑(primeUnit K' (w₀.under (𝓞 K'))) from (primeUnit_val K' (w₀.under (𝓞 K'))).symm,
      ← Units.val_pow_eq_pow_val,
      show raySymbol K' (artinValue e hζ) ↑((primeUnit K' (w₀.under (𝓞 K')))
          ^ (w₀.under (𝓞 K')).asIdeal.inertiaDeg' w₀.asIdeal)
        = raySymbolUnitsHom K' (artinValue e hζ) ((primeUnit K' (w₀.under (𝓞 K')))
          ^ (w₀.under (𝓞 K')).asIdeal.inertiaDeg' w₀.asIdeal) from rfl,
      map_pow, show raySymbolUnitsHom K' (artinValue e hζ) (primeUnit K' (w₀.under (𝓞 K')))
        = raySymbol K' (artinValue e hζ) ↑(primeUnit K' (w₀.under (𝓞 K'))) from rfl,
      raySymbol_primeUnit]
    exact TransferSol.artinValue4_eq_artinValue_under_pow e hζ w₀ hw₀unr

end
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_raySymbol_artinValue4_eq_raySymbol_artinValue_relNorm_of_inertia_rat.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_raySymbol_artinValue4_eq_raySymbol_artinValue_relNorm_of_inertia_rat.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_raySymbol_artinValue4_eq_raySymbol_artinValue_relNorm_of_inertia_rat.LanglandsTunnell.P2.TransferSol"

end S_LanglandsTunnell_P2_raySymbol_artinValue4_eq_raySymbol_artinValue_relNorm_of_inertia_rat
end P2MW
export P2MW.S_LanglandsTunnell_P2_raySymbol_artinValue4_eq_raySymbol_artinValue_relNorm_of_inertia_rat (solution)
