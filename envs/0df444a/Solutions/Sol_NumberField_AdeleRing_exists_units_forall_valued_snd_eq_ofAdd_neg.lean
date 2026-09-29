-- Prove2me | solution 1 for NumberField.AdeleRing.exists_units_forall_valued_snd_eq_ofAdd_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/da60f3aa-0931-56c4-b325-7aa3d4c841e8

import Mathlib
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdeleRing_exists_units_forall_valued_snd_eq_ofAdd_neg

set_option autoImplicit false
open IsDedekindDomain NumberField
open scoped NumberField.PlaceTransport

theorem solution
    (K : Type) [Field K] [NumberField K] (m : HeightOneSpectrum (𝓞 K) →₀ ℤ) :
    ∃ q : (AdeleRing (𝓞 K) K)ˣ, ∀ w : HeightOneSpectrum (𝓞 K),
      Valued.v (((q : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) =
        ((Multiplicative.ofAdd (-(m w)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  classical

  choose π hπ using fun w : HeightOneSpectrum (𝓞 K) => w.valuation_exists_uniformizer K
  have hπ0 : ∀ w, algebraMap K (w.adicCompletion K) (π w) ≠ 0 := fun w h => by
    have h' : π w = 0 := (map_eq_zero_iff _ (algebraMap K (w.adicCompletion K)).injective).1 h
    have := hπ w
    rw [h', map_zero] at this
    exact WithZero.coe_ne_zero this.symm
  have hπv : ∀ w, Valued.v (algebraMap K (w.adicCompletion K) (π w)) =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := fun w => by
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
    exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (π w)).trans (hπ w)

  let f : ∀ w : HeightOneSpectrum (𝓞 K), w.adicCompletion K := fun w => (algebraMap K (w.adicCompletion K) (π w)) ^ (m w : ℤ)
  let g : ∀ w : HeightOneSpectrum (𝓞 K), w.adicCompletion K := fun w => (algebraMap K (w.adicCompletion K) (π w)) ^ (-(m w) : ℤ)
  have hfg : ∀ w, f w * g w = 1 := fun w => by
    simp only [f, g, zpow_neg]
    exact mul_inv_cancel₀ (zpow_ne_zero _ (hπ0 w))
  have hpowv : ∀ (w : HeightOneSpectrum (𝓞 K)) (n : ℤ), Valued.v ((algebraMap K (w.adicCompletion K) (π w)) ^ n) =
      ((Multiplicative.ofAdd (-n) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := fun w n => by
    rw [map_zpow₀, hπv, ← WithZero.coe_zpow, ← ofAdd_zsmul, smul_eq_mul, mul_neg, mul_one]
  have hfv : ∀ w, Valued.v (f w) = ((Multiplicative.ofAdd (-(m w)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
    fun w => hpowv w (m w)
  have hgv : ∀ w, Valued.v (g w) = ((Multiplicative.ofAdd (m w) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
    fun w => by rw [hpowv, neg_neg]

  have hmem : ∀ (h : ∀ w : HeightOneSpectrum (𝓞 K), w.adicCompletion K), (∀ w, m w = 0 → h w = 1) →
      ∀ᶠ w in Filter.cofinite, h w ∈ (w.adicCompletionIntegers K : Set (w.adicCompletion K)) := by
    intro h hh
    rw [Filter.eventually_cofinite]
    refine m.hasFiniteSupport.subset fun w hw => ?_
    rw [Function.mem_support]
    intro h0
    apply hw
    rw [hh w h0]
    exact one_mem _
  have hf1 : ∀ w, m w = 0 → f w = 1 := fun w h0 => by simp only [f, h0, zpow_zero]
  have hg1 : ∀ w, m w = 0 → g w = 1 := fun w h0 => by simp only [g, h0, neg_zero, zpow_zero]
  let F : FiniteAdeleRing (𝓞 K) K := ⟨f, hmem f hf1⟩
  let G : FiniteAdeleRing (𝓞 K) K := ⟨g, hmem g hg1⟩
  have hFG : F * G = 1 := RestrictedProduct.ext _ _ fun w => hfg w
  have hGF : G * F = 1 := by rw [mul_comm]; exact hFG
  refine ⟨⟨((1 : InfiniteAdeleRing K), F), ((1 : InfiniteAdeleRing K), G), ?_, ?_⟩, fun w => ?_⟩
  · exact Prod.ext (mul_one _) hFG
  · exact Prod.ext (mul_one _) hGF
  · exact hfv w

end S_NumberField_AdeleRing_exists_units_forall_valued_snd_eq_ofAdd_neg
end P2MW
export P2MW.S_NumberField_AdeleRing_exists_units_forall_valued_snd_eq_ofAdd_neg (solution)
