-- Prove2me | solution 1 for HeckeCharacter.exists_isAdjuster_one_and_fadContentHom_projFin_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/c2e54ae9-6101-569e-95d4-7963369881f7

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Theorems.Thm_HeckeCharacter_count_coe_fadContentHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeCharacter_exists_isAdjuster_one_and_fadContentHom_projFin_eq

set_option autoImplicit false
open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors IsMulCommutative

namespace AB3Aux

variable (K : Type*) [Field K] [NumberField K]

theorem eq_of_count_eq {I J : FractionalIdeal ((𝓞 K)⁰) K}
    (hI : I ≠ 0) (hJ : J ≠ 0) (h : ∀ v : HeightOneSpectrum (𝓞 K), FractionalIdeal.count K v I = FractionalIdeal.count K v J) :
    I = J := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ]
  exact finprod_congr fun v => by rw [h v]

noncomputable def unif (v : HeightOneSpectrum (𝓞 K)) : K :=
  Classical.choose (HeightOneSpectrum.valuation_exists_uniformizer K v)

theorem valuation_unif (v : HeightOneSpectrum (𝓞 K)) : v.valuation K (unif K v) = WithZero.exp (-1) :=
  Classical.choose_spec (HeightOneSpectrum.valuation_exists_uniformizer K v)

noncomputable def comp (n : HeightOneSpectrum (𝓞 K) → ℤ) (v : HeightOneSpectrum (𝓞 K)) : v.adicCompletion K :=
  ((algebraMap K (FiniteAdeleRing (𝓞 K) K) (unif K v)) v) ^ n v

theorem valued_comp (n : HeightOneSpectrum (𝓞 K) → ℤ) (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v (comp K n v) = WithZero.exp (-(n v)) := by
  unfold comp
  rw [map_zpow₀, FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    valuation_unif, ← WithZero.exp_zsmul, smul_neg, zsmul_one, Int.cast_id]

theorem comp_of_eq_zero (n : HeightOneSpectrum (𝓞 K) → ℤ) (v : HeightOneSpectrum (𝓞 K)) (hv : n v = 0) :
    comp K n v = 1 := by
  unfold comp; rw [hv, zpow_zero]

theorem comp_ne_zero (n : HeightOneSpectrum (𝓞 K) → ℤ) (v : HeightOneSpectrum (𝓞 K)) : comp K n v ≠ 0 := by
  intro h
  have := valued_comp K n v
  rw [h, map_zero] at this
  exact WithZero.exp_ne_zero this.symm

noncomputable def fad (n : HeightOneSpectrum (𝓞 K) → ℤ) (hn : ∀ᶠ v in Filter.cofinite, n v = 0) :
    FiniteAdeleRing (𝓞 K) K :=
  RestrictedProduct.mk (comp K n) (hn.mono fun v hv => by
    show comp K n v ∈ v.adicCompletionIntegers K
    rw [comp_of_eq_zero K n v hv]; exact one_mem _)

theorem fad_apply (n : HeightOneSpectrum (𝓞 K) → ℤ) (hn : ∀ᶠ v in Filter.cofinite, n v = 0)
    (v : HeightOneSpectrum (𝓞 K)) : fad K n hn v = comp K n v :=
  RestrictedProduct.mk_apply _ _ _ _ _

theorem isUnit_fad (n : HeightOneSpectrum (𝓞 K) → ℤ) (hn : ∀ᶠ v in Filter.cofinite, n v = 0) :
    IsUnit (fad K n hn) := by
  rw [FiniteAdeleRing.isUnit_iff]
  refine ⟨fun v => ?_, hn.mono fun v hv => ?_⟩
  · rw [fad_apply]; exact comp_ne_zero K n v
  · rw [fad_apply, comp_of_eq_zero K n v hv, map_one]

noncomputable def fadUnit (n : HeightOneSpectrum (𝓞 K) → ℤ) (hn : ∀ᶠ v in Filter.cofinite, n v = 0) :
    (FiniteAdeleRing (𝓞 K) K)ˣ :=
  (isUnit_fad K n hn).unit

theorem fadUnit_apply (n : HeightOneSpectrum (𝓞 K) → ℤ) (hn : ∀ᶠ v in Filter.cofinite, n v = 0)
    (v : HeightOneSpectrum (𝓞 K)) : ((fadUnit K n hn : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v = comp K n v := by
  rw [fadUnit, IsUnit.unit_spec, fad_apply]

theorem placeOrd_fadUnit (n : HeightOneSpectrum (𝓞 K) → ℤ) (hn : ∀ᶠ v in Filter.cofinite, n v = 0)
    (v : HeightOneSpectrum (𝓞 K)) : placeOrd K (fadUnit K n hn) v = n v := by
  unfold placeOrd
  rw [fadUnit_apply, valued_comp, WithZero.log_exp, neg_neg]

noncomputable def idele (n : HeightOneSpectrum (𝓞 K) → ℤ) (hn : ∀ᶠ v in Filter.cofinite, n v = 0) :
    (AdeleRing (𝓞 K) K)ˣ :=
  (MulEquiv.prodUnits (M := InfiniteAdeleRing K) (N := FiniteAdeleRing (𝓞 K) K)).symm (1, fadUnit K n hn)

theorem idele_fst (n : HeightOneSpectrum (𝓞 K) → ℤ) (hn : ∀ᶠ v in Filter.cofinite, n v = 0) :
    (idele K n hn : AdeleRing (𝓞 K) K).1 = 1 := rfl

theorem idele_snd (n : HeightOneSpectrum (𝓞 K) → ℤ) (hn : ∀ᶠ v in Filter.cofinite, n v = 0) :
    (idele K n hn : AdeleRing (𝓞 K) K).2 = fadUnit K n hn := rfl

theorem projFin_idele (n : HeightOneSpectrum (𝓞 K) → ℤ) (hn : ∀ᶠ v in Filter.cofinite, n v = 0) :
    projFin K (idele K n hn) = fadUnit K n hn :=
  Units.ext (idele_snd K n hn)

end AB3Aux

theorem solution
    (K : Type*) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (J : (FractionalIdeal ((𝓞 K)⁰) K)ˣ)
    (hJ : J ∈ coprimeToModulus K 𝔣) :
    ∃ x : (AdeleRing (𝓞 K) K)ˣ, IsAdjuster K 𝔣 x 1 ∧ (x : AdeleRing (𝓞 K) K).1 = 1 ∧
      fadContentHom K (projFin K x) = J := by
  set n : HeightOneSpectrum (𝓞 K) → ℤ := fun v => FractionalIdeal.count K v (J : FractionalIdeal ((𝓞 K)⁰) K) with hn_def
  have hn : ∀ᶠ v in Filter.cofinite, n v = 0 := FractionalIdeal.finite_factors (J : FractionalIdeal ((𝓞 K)⁰) K)
  refine ⟨AB3Aux.idele K n hn, ?_, AB3Aux.idele_fst K n hn, ?_⟩
  · have h1 : AB3Aux.idele K n hn * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) 1)⁻¹ =
        AB3Aux.idele K n hn := by
      rw [map_one, inv_one, mul_one]
    refine ⟨fun v hv => ?_, fun τ => ?_⟩
    · rw [h1, AB3Aux.idele_snd, AB3Aux.fadUnit_apply,
        AB3Aux.comp_of_eq_zero K n v ((mem_coprimeToModulus_iff K).mp hJ v hv), map_one, sub_self, map_zero]
      exact ⟨rfl, zero_le'⟩
    · rw [h1]
      exact archSign_of_fst_eq_one K τ (AB3Aux.idele_fst K n hn)
  · rw [AB3Aux.projFin_idele]
    refine Units.ext (AB3Aux.eq_of_count_eq K (Units.ne_zero _) (Units.ne_zero _) fun v => ?_)
    rw [HeckeCharacter.count_coe_fadContentHom, AB3Aux.placeOrd_fadUnit]

end S_HeckeCharacter_exists_isAdjuster_one_and_fadContentHom_projFin_eq
end P2MW
export P2MW.S_HeckeCharacter_exists_isAdjuster_one_and_fadContentHom_projFin_eq (solution)
