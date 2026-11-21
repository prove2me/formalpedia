-- Prove2me | solution 1 for MasulloRH.radial_adelic_poisson_sign_invariance
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T02:08:14.555181+00:00
-- url     : https://prove2.me/submissions/f0ee7829-4aee-48e2-b55f-2cfc2968442f

import Mathlib
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Theorems.Thm_NumberField_AdelicFourier_tsum_translate_eq_inv_measure_mul_tsum_fourierIntegral
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology

set_option backward.isDefEq.respectTransparency.types false
open IsDedekindDomain NumberField NumberField.StandardAddChar NumberField.AdelicFourier MeasureTheory
open scoped NumberField.AdeleRing


private theorem haar_involution {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (e : G ≃ₜ+ G) (he : Function.Involutive e) (μ : Measure G) [μ.IsAddHaarMeasure] :
    MeasurePreserving e μ μ := by
  have hm : Measurable e := e.continuous.measurable
  let ν := μ.map e
  letI : ν.IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  have he2 : ν.map e = μ := by
    dsimp [ν]; rw [Measure.map_map hm hm, show (e ∘ e : G → G) = id from funext he,Measure.map_id]
  have hs := Measure.addHaarScalarFactor_map ν μ e
  have hs' : μ.addHaarScalarFactor ν = ν.addHaarScalarFactor μ := by
    simpa only [he2] using hs
  have h := Measure.addHaarScalarFactor_eq_mul μ ν μ
  rw [Measure.addHaarScalarFactor_self,hs'] at h
  have hh : (ν.addHaarScalarFactor μ : ℝ) = 1 := by
    have heq := congrArg NNReal.toReal h
    push_cast at heq
    nlinarith [NNReal.coe_nonneg (ν.addHaarScalarFactor μ)]
  have hh' : ν.addHaarScalarFactor μ = 1 := NNReal.coe_injective hh
  refine ⟨hm,?_⟩
  change ν = μ
  simpa only [hh',one_smul] using (Measure.isAddLeftInvariant_eq_smul ν μ)

private def unit_involution {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (u : A) (hu : u*u=1) : A ≃ₜ+ A where
  toFun := fun x => u*x
  invFun := fun x => u*x
  left_inv x := by change u*(u*x)=x; rw [←mul_assoc,hu,one_mul]
  right_inv x := by change u*(u*x)=x; rw [←mul_assoc,hu,one_mul]
  map_add' := mul_add u
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

private theorem finite_sign_rational (q : ℚ) :
    (psiQ.mulShift ((1,-1) : 𝔸[ℚ])) (algebraMap ℚ 𝔸[ℚ] q) = 1 ↔
      ∃ k : ℤ, 2*q = k := by
  change psiArch (1 * algebraMap ℚ (InfiniteAdeleRing ℚ) q) *
    psiFin ((-1) * algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q) = 1 ↔ _
  rw [one_mul,neg_one_mul,←map_neg,psiArch_algebraMap,psiFin_algebraMap,←Complex.exp_add]
  push_cast
  let c : ℂ := 2*(Real.pi:ℂ)*Complex.I
  have hc : c ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  change Complex.exp (c*(q:ℂ) + -c * -(q:ℂ)) = 1 ↔ _
  rw [show c*(q:ℂ)+ -c * -(q:ℂ)=(2*(q:ℂ))*c by ring,Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨k,hk⟩
    have heq : 2*(q:ℂ)=(k:ℂ) := mul_right_cancel₀ hc hk
    exact ⟨k,by exact_mod_cast heq⟩
  · rintro ⟨k,hk⟩
    have heq : 2*(q:ℂ)=(k:ℂ) := by exact_mod_cast hk
    exact ⟨k,congrArg (fun z : ℂ => z*c) heq⟩

theorem solution
    [MeasurableSpace 𝔸[ℚ]] [BorelSpace 𝔸[ℚ]]
    (μ : Measure 𝔸[ℚ]) [μ.IsAddHaarMeasure] (f : 𝔸[ℚ] → ℂ) (hf : f ∈ schwartzBruhat ℚ) :
    let u : 𝔸[ℚ] := (1,-1)
    let χ := psiQ.mulShift u
    (∀ q : ℚ, χ (algebraMap ℚ 𝔸[ℚ] q) = 1 ↔ ∃ k : ℤ, 2*q = k) ∧
    (∀ x : 𝔸[ℚ], (∑' q : ℚ, f (x + algebraMap ℚ 𝔸[ℚ] q)) =
       ((μ (AdelicBox.adelicBox ℚ)).toReal : ℂ)⁻¹ *
         ∑' q : ℚ, fourierIntegral χ μ f (u * algebraMap ℚ 𝔸[ℚ] q) *
           χ ((u * algebraMap ℚ 𝔸[ℚ] q)*x)) ∧
    ((∀ x : 𝔸[ℚ], f (u*x) = f x) →
       (∀ w : 𝔸[ℚ], fourierIntegral χ μ f w = fourierIntegral psiQ μ f w) ∧
       (∑' q : ℚ, f (algebraMap ℚ 𝔸[ℚ] q)) =
         ((μ (AdelicBox.adelicBox ℚ)).toReal : ℂ)⁻¹ *
           ∑' q : ℚ, fourierIntegral χ μ f (algebraMap ℚ 𝔸[ℚ] q)) := by
  classical
  let u : 𝔸[ℚ] := (1,-1)
  let χ := psiQ.mulShift u
  have hu : u*u=1 := by
    apply Prod.ext
    · change (1:InfiniteAdeleRing ℚ)*1=1; simp
    · change (-1:FiniteAdeleRing (𝓞 ℚ) ℚ)*(-1)=1; simp
  let J : 𝔸[ℚ] ≃ₜ+ 𝔸[ℚ] := unit_involution u hu
  letI := NumberField.AdeleRing.secondCountableTopology ℚ
  have hinv : Function.Involutive J := fun x => J.left_inv x
  have hJ := haar_involution J hinv μ
  have hgood := tsum_translate_eq_inv_measure_mul_tsum_fourierIntegral ℚ μ isGlobalAddChar_psiQ hf
  have hshift (w : 𝔸[ℚ]) : fourierIntegral χ μ f (u*w) = fourierIntegral psiQ μ f w := by
    unfold fourierIntegral
    apply integral_congr_ae <| Filter.Eventually.of_forall _
    intro v
    change psiQ (u * -(v * (u*w))) * f v = _
    rw [show u * -(v*(u*w)) = -(v*w) by rw [mul_neg,show u*(v*(u*w))=(u*u)*(v*w) by ring,hu,one_mul]]
  refine ⟨finite_sign_rational,?_,?_⟩
  · intro x
    apply (hgood x).trans
    congr 1
    apply tsum_congr
    intro q
    rw [hshift]
    change _ = _ * psiQ (u * ((u*algebraMap ℚ 𝔸[ℚ] q)*x))
    rw [show u*((u*algebraMap ℚ 𝔸[ℚ] q)*x) = (u*u)*(algebraMap ℚ 𝔸[ℚ] q*x) by ring,hu,one_mul]
  · intro heven
    have hF (w : 𝔸[ℚ]) : fourierIntegral χ μ f w = fourierIntegral psiQ μ f w := by
      have h := hJ.integral_comp J.toHomeomorph.measurableEmbedding (fun v => psiQ (-(v*w))*f v)
      apply Eq.trans _ h
      unfold fourierIntegral
      apply integral_congr_ae <| Filter.Eventually.of_forall _
      intro v
      change psiQ (u * -(v*w))*f v = psiQ (-((u*v)*w))*f (u*v)
      rw [heven,mul_neg,mul_assoc]
    refine ⟨hF,?_⟩
    change _ = _ * ∑' q : ℚ, fourierIntegral χ μ f (algebraMap ℚ 𝔸[ℚ] q)
    simp_rw [hF]
    simpa only [zero_add,mul_zero,AddChar.map_zero_eq_one,mul_one] using hgood 0

