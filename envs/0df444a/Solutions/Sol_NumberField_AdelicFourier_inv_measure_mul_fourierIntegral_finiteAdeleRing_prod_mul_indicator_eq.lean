-- Prove2me | solution 1 for NumberField.AdelicFourier.inv_measure_mul_fourierIntegral_finiteAdeleRing_prod_mul_indicator_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/6a80fab1-08bc-5417-a95d-ce5c48c07a73

import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_EisensteinGeneral_Factorization_inv_measure_mul_setIntegral_integralOffSet_finprod_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_inv_measure_mul_fourierIntegral_finiteAdeleRing_prod_mul_indicator_eq

set_option autoImplicit false

open NumberField NumberField.AdelicFourier NumberField.AdelicBox IsDedekindDomain MeasureTheory
open scoped Classical

namespace AlphaAsm
variable {F : Type} [Field F] [NumberField F]
theorem mul_apply' (x y : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) : (x * y) v = x v * y v := rfl
theorem add_apply' (x y : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) : (x + y) v = x v + y v := rfl
theorem neg_apply' (x : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) : (-x) v = -(x v) := rfl

variable (F) in

def offBox (S : Finset (HeightOneSpectrum (𝓞 F))) : AddSubgroup (FiniteAdeleRing (𝓞 F) F) where
  carrier := {x | ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F}
  zero_mem' := fun v _ => by show (0 : FiniteAdeleRing (𝓞 F) F) v ∈ _; exact zero_mem _
  add_mem' := fun {a b} ha hb v hv => by rw [Set.mem_setOf_eq] at ha hb; rw [add_apply']; exact add_mem (ha v hv) (hb v hv)
  neg_mem' := fun {a} ha v hv => by rw [Set.mem_setOf_eq] at ha; rw [neg_apply']; exact neg_mem (ha v hv)

theorem measurableSet_offBox [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    MeasurableSet {x : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F} := by
  have hmem : ((offBox F S : AddSubgroup (FiniteAdeleRing (𝓞 F) F)) : Set (FiniteAdeleRing (𝓞 F) F)) ∈
      nhds (0 : FiniteAdeleRing (𝓞 F) F) := by
    refine Filter.mem_of_superset ((isOpen_integralFiniteAdeles F).mem_nhds (fun v => zero_mem _)) ?_
    intro x hx v _; exact hx v
  have hopen : IsOpen ((offBox F S : AddSubgroup (FiniteAdeleRing (𝓞 F) F)) : Set (FiniteAdeleRing (𝓞 F) F)) :=
    AddSubgroup.isOpen_of_mem_nhds _ hmem
  exact hopen.measurableSet

end AlphaAsm

theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μ v).IsAddHaarMeasure]
    (ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ) (hψf : Continuous ψf)
    (ψv : ∀ v : HeightOneSpectrum (𝓞 F), AddChar (v.adicCompletion F) ℂ) (hψv : ∀ v, Continuous (ψv v))
    (hprod : ∀ x : FiniteAdeleRing (𝓞 F) F, ψf x = ∏ᶠ v : HeightOneSpectrum (𝓞 F), ψv v (x v))
    (hunr : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ z : v.adicCompletion F, z ∈ v.adicCompletionIntegers F → ψv v z = 1)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (w : FiniteAdeleRing (𝓞 F) F) :
    ((ν.real (integralFiniteAdeles (𝓞 F) F) : ℂ))⁻¹ *
        fourierIntegral ψf ν
          (fun x => (∏ v ∈ S, h v (x v)) *
            (if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F then 1 else 0)) w
      = (∏ v ∈ S, (((μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ))⁻¹ *
            fourierIntegral (ψv v) (μ v) (h v) (w v)) *
        (if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
              ∀ z : v.adicCompletion F, z ∈ v.adicCompletionIntegers F → ψv v (z * w v) = 1
          then 1 else 0) := by
  by_cases hD : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
      ∀ z : v.adicCompletion F, z ∈ v.adicCompletionIntegers F → ψv v (z * w v) = 1
  · rw [if_pos hD, mul_one]

    set k : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ :=
      fun v => if v ∈ S then fun y => ψv v (-(y * w v)) * h v y else fun _ => 1 with hkdef
    have hk₁ : ∀ v ∉ S, ∀ y : v.adicCompletion F, y ∈ v.adicCompletionIntegers F → k v y = 1 := by
      intro v hv y _; simp only [hkdef, if_neg hv]
    have hkS : ∀ v ∈ S, k v = fun y => ψv v (-(y * w v)) * h v y := fun v hv => by simp only [hkdef, if_pos hv]

    have hint : ∀ x : FiniteAdeleRing (𝓞 F) F,
        ψf (-(x * w)) * ((∏ v ∈ S, h v (x v)) *
          (if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F then 1 else 0))
          = Set.indicator {x : FiniteAdeleRing (𝓞 F) F |
              ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F}
            (fun x => ∏ᶠ v : HeightOneSpectrum (𝓞 F), k v (x v)) x := by
      intro x
      by_cases hx : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F
      · rw [if_pos hx, mul_one, hprod]
        rw [Set.indicator_of_mem (by exact hx)]
        have hsupp : (Function.mulSupport fun v => ψv v ((-(x * w)) v)) ⊆ (S : Set (HeightOneSpectrum (𝓞 F))) := by
          intro v hv
          by_contra hvS
          apply hv
          show ψv v ((-(x * w)) v) = 1
          rw [AlphaAsm.neg_apply', AlphaAsm.mul_apply', ← neg_mul]
          exact hD v hvS _ (neg_mem (hx v hvS))
        have hsuppk : (Function.mulSupport fun v => k v (x v)) ⊆ (S : Set (HeightOneSpectrum (𝓞 F))) := by
          intro v hv
          by_contra hvS
          exact hv (hk₁ v hvS _ (hx v hvS))
        rw [finprod_eq_prod_of_mulSupport_subset _ hsupp, finprod_eq_prod_of_mulSupport_subset _ hsuppk,
          ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun v hv => ?_
        rw [hkS v hv, AlphaAsm.neg_apply', AlphaAsm.mul_apply']
      · rw [if_neg hx, mul_zero, mul_zero, Set.indicator_of_notMem (by exact hx)]
    rw [fourierIntegral_def]
    simp_rw [hint]
    rw [integral_indicator (AlphaAsm.measurableSet_offBox S),
      EisensteinGeneral.Factorization.inv_measure_mul_setIntegral_integralOffSet_finprod_eq F ν S μ k hk₁]
    refine Finset.prod_congr rfl fun v hv => ?_
    rw [hkS v hv, fourierIntegral_def]
  · rw [if_neg hD, mul_zero]
    push Not at hD
    obtain ⟨v₁, hv₁S, z₁, hz₁, hne⟩ := hD
    set z : FiniteAdeleRing (𝓞 F) F := AdelicDock.splice (𝓞 F) F v₁ 0 z₁ with hzdef
    have hzv : ∀ v, v ≠ v₁ → z v = 0 := fun v hv =>
      (AdelicDock.splice_apply_of_ne (𝓞 F) F v₁ (0 : FiniteAdeleRing (𝓞 F) F) z₁ hv).trans rfl
    have hzv₁ : z v₁ = z₁ := AdelicDock.splice_apply_self (𝓞 F) F v₁ (0 : FiniteAdeleRing (𝓞 F) F) z₁
    set Hf : FiniteAdeleRing (𝓞 F) F → ℂ := fun x => (∏ v ∈ S, h v (x v)) *
          (if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F then 1 else 0) with hHf
    have hHz : ∀ x, Hf (x + z) = Hf x := by
      intro x
      have h1 : ∀ v ∈ S, (x + z) v = x v := fun v hv => by
        rw [AlphaAsm.add_apply', hzv v (fun h => hv₁S (h ▸ hv)), add_zero]
      have h2 : (∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → (x + z) v ∈ v.adicCompletionIntegers F) ↔
          (∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F) := by
        refine forall₂_congr fun v _ => ?_
        rw [AlphaAsm.add_apply']
        by_cases hvv : v = v₁
        · subst hvv; rw [hzv₁]
          exact ⟨fun h => by simpa using sub_mem h hz₁, fun h => add_mem h hz₁⟩
        · rw [hzv v hvv, add_zero]
      simp only [hHf]
      rw [Finset.prod_congr rfl (fun v hv => by rw [h1 v hv])]
      simp only [h2]
    have hI : fourierIntegral ψf ν Hf w = ψf (-(z * w)) * fourierIntegral ψf ν Hf w := by
      rw [fourierIntegral_def, ← integral_const_mul]
      conv_lhs => rw [← integral_add_right_eq_self (μ := ν) (fun x => ψf (-(x * w)) * Hf x) z]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only
      rw [hHz, add_mul, neg_add, AddChar.map_add_eq_mul]
      ring
    have hψz : ψf (-(z * w)) ≠ 1 := by
      rw [hprod]
      rw [finprod_eq_single (fun v => ψv v ((-(z * w)) v)) v₁ (fun v hv => by
        show ψv v ((-(z * w)) v) = 1
        rw [AlphaAsm.neg_apply', AlphaAsm.mul_apply', hzv v hv, zero_mul, neg_zero, AddChar.map_zero_eq_one])]
      show ψv v₁ ((-(z * w)) v₁) ≠ 1
      rw [AlphaAsm.neg_apply', AlphaAsm.mul_apply', hzv₁, AddChar.map_neg_eq_inv]
      exact inv_ne_one.mpr hne
    have h3 : (1 - ψf (-(z * w))) * fourierIntegral ψf ν Hf w = 0 := by
      rw [sub_mul, one_mul, ← hI, sub_self]
    rcases mul_eq_zero.mp h3 with h0 | h0
    · exact absurd (sub_eq_zero.mp h0).symm hψz
    · show _ * fourierIntegral ψf ν Hf w = 0
      rw [h0, mul_zero]

end S_NumberField_AdelicFourier_inv_measure_mul_fourierIntegral_finiteAdeleRing_prod_mul_indicator_eq
end P2MW
export P2MW.S_NumberField_AdelicFourier_inv_measure_mul_fourierIntegral_finiteAdeleRing_prod_mul_indicator_eq (solution)
