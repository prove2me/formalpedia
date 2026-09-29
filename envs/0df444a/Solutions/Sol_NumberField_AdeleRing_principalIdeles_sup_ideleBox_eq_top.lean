-- Prove2me | solution 1 for NumberField.AdeleRing.principalIdeles_sup_ideleBox_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/1157578e-5fae-5a4b-863a-3484e19530b9

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_IdeleBox
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdeleRing_principalIdeles_sup_ideleBox_eq_top

set_option autoImplicit false

namespace P2mS26N2a

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {E : Type*} [Field E] [NumberField E]

noncomputable def P (s : Eˣ) : (AdeleRing (𝓞 E) E)ˣ :=
  Units.map (algebraMap E (AdeleRing (𝓞 E) E) : E →* AdeleRing (𝓞 E) E) s

theorem P_mem (s : Eˣ) : P s ∈ M4aHerbrand.principalIdeles (𝓞 E) E := ⟨s, rfl⟩

theorem val_P (s : Eˣ) : ((P s : (AdeleRing (𝓞 E) E)ˣ) : AdeleRing (𝓞 E) E) = algebraMap E (AdeleRing (𝓞 E) E) s := rfl

theorem P_inv (s : Eˣ) : (P s)⁻¹ = P s⁻¹ := by rw [P, P, map_inv]

theorem snd_P_apply (s : Eˣ) (v : HeightOneSpectrum (𝓞 E)) :
    (((P s : (AdeleRing (𝓞 E) E)ˣ) : AdeleRing (𝓞 E) E).2 : FiniteAdeleRing (𝓞 E) E) v
      = algebraMap E (v.adicCompletion E) (s : E) := by
  rw [val_P, NumberField.AdeleRing.algebraMap_snd_apply, IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
  rfl

theorem finiteUnitsComponent_P (s : Eˣ) (v : HeightOneSpectrum (𝓞 E)) :
    NumberField.AdeleRing.finiteUnitsComponent (𝓞 E) E v (P s)
      = Units.map (algebraMap E (v.adicCompletion E) : E →* v.adicCompletion E) s := by
  ext
  rw [NumberField.AdeleRing.val_finiteUnitsComponent, snd_P_apply]
  rfl

theorem v_snd_P (s : Eˣ) (v : HeightOneSpectrum (𝓞 E)) :
    Valued.v ((((P s : (AdeleRing (𝓞 E) E)ˣ) : AdeleRing (𝓞 E) E).2 : FiniteAdeleRing (𝓞 E) E) v)
      = v.valuation E (s : E) := by
  rw [val_P, NumberField.AdeleRing.algebraMap_snd_apply, valuedAdicCompletion_eq_valuation']

theorem v_snd_eq_one_iff (x : (AdeleRing (𝓞 E) E)ˣ) (v : HeightOneSpectrum (𝓞 E)) :
    Valued.v (((x : AdeleRing (𝓞 E) E).2 : FiniteAdeleRing (𝓞 E) E) v) = 1 ↔
      (Prod.snd (x : AdeleRing (𝓞 E) E) v ∈ v.adicCompletionIntegers E ∧
        Prod.snd (↑x⁻¹ : AdeleRing (𝓞 E) E) v ∈ v.adicCompletionIntegers E) :=
  (IsDedekindDomain.FiniteAdeleRing.integer_and_inv_integer_iff_valuation_eq_one v
    (NumberField.AdeleRing.finitePartUnits (𝓞 E) E x)).symm

theorem snd_mul_apply (x y : (AdeleRing (𝓞 E) E)ˣ) (v : HeightOneSpectrum (𝓞 E)) :
    (((x * y : (AdeleRing (𝓞 E) E)ˣ) : AdeleRing (𝓞 E) E).2 : FiniteAdeleRing (𝓞 E) E) v
      = ((x : AdeleRing (𝓞 E) E).2 : FiniteAdeleRing (𝓞 E) E) v * ((y : AdeleRing (𝓞 E) E).2 : FiniteAdeleRing (𝓞 E) E) v :=
  rfl

end P2mS26N2a

theorem solution
    (E : Type*) [Field E] [NumberField E]
    (S S' : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))) (hSS' : S ⊆ S')
    (hS : M4aHerbrand.principalIdeles (NumberField.RingOfIntegers E) E ⊔
      NumberField.AdeleRing.unitIdelesOutside (NumberField.RingOfIntegers E) E ↑S = ⊤)
    (H : (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) → Subgroup (v.adicCompletion E)ˣ)
    (hH : ∀ v ∈ S, H v = ⊤)
    (hsurj : ∀ x : (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) → (v.adicCompletion E)ˣ,
      (∀ v ∈ S', v ∉ S → Valued.v ((x v : (v.adicCompletion E)ˣ) : v.adicCompletion E) = 1) →
      ∃ s : Eˣ, (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E), v ∉ S →
          v.valuation E (s : E) = 1) ∧
        ∀ v ∈ S', v ∉ S →
          x v * (Units.map (algebraMap E (v.adicCompletion E) : E →* v.adicCompletion E) s)⁻¹ ∈ H v) :
    M4aHerbrand.principalIdeles (NumberField.RingOfIntegers E) E ⊔
      NumberField.AdeleRing.ideleBox (NumberField.RingOfIntegers E) E ↑S' H ⊤ = ⊤ := by
  classical
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ M4aHerbrand.principalIdeles (NumberField.RingOfIntegers E) E ⊔
      NumberField.AdeleRing.unitIdelesOutside (NumberField.RingOfIntegers E) E ↑S := by
    rw [hS]; exact Subgroup.mem_top x
  obtain ⟨e, he, y, hy, rfl⟩ := Subgroup.mem_sup.mp hx
  have hyout : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E), v ∉ S →
      (y : NumberField.AdeleRing (NumberField.RingOfIntegers E) E).2 v ∈ v.adicCompletionIntegers E ∧
        ((↑y⁻¹ : NumberField.AdeleRing (NumberField.RingOfIntegers E) E)).2 v ∈ v.adicCompletionIntegers E := by
    intro v hv
    rw [← NumberField.AdeleRing.ideleBox_top_top, NumberField.AdeleRing.mem_ideleBox_iff] at hy
    exact hy.1.2 v (fun h => hv (Finset.mem_coe.mp h))

  obtain ⟨s, hsS, hsH⟩ := hsurj
    (fun v => NumberField.AdeleRing.finiteUnitsComponent (NumberField.RingOfIntegers E) E v y)
    (fun v _ hvS => (P2mS26N2a.v_snd_eq_one_iff y v).mpr (hyout v hvS))
  refine Subgroup.mem_sup.mpr ⟨e * P2mS26N2a.P s, mul_mem he (P2mS26N2a.P_mem s), (P2mS26N2a.P s)⁻¹ * y, ?_,
    by rw [mul_assoc, mul_inv_cancel_left]⟩
  rw [NumberField.AdeleRing.mem_ideleBox_iff]
  refine ⟨⟨fun v hv => ?_, fun v hv => ?_⟩, fun w => Subgroup.mem_top _⟩
  ·
    by_cases hvS : v ∈ S
    · rw [hH v hvS]; exact Subgroup.mem_top _
    · have h := hsH v (Finset.mem_coe.mp hv) hvS
      rw [map_mul, map_inv, P2mS26N2a.finiteUnitsComponent_P, mul_comm]
      exact h
  ·
    have hvS : v ∉ S := fun h => hv (Finset.mem_coe.mpr (hSS' h))
    rw [← P2mS26N2a.v_snd_eq_one_iff, P2mS26N2a.snd_mul_apply, map_mul, P2mS26N2a.P_inv, P2mS26N2a.v_snd_P,
      (P2mS26N2a.v_snd_eq_one_iff y v).mpr (hyout v hvS), mul_one, Units.val_inv_eq_inv_val, map_inv₀, hsS v hvS, inv_one]

end S_NumberField_AdeleRing_principalIdeles_sup_ideleBox_eq_top
end P2MW
export P2MW.S_NumberField_AdeleRing_principalIdeles_sup_ideleBox_eq_top (solution)
