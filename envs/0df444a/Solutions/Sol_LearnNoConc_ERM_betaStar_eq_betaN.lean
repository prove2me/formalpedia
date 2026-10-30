-- Prove2me | solution 1 for LearnNoConc.ERM.betaStar_eq_betaN
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-29T08:38:54.962985+00:00
-- url     : https://prove2.me/submissions/4a2abf72-afdb-49b5-8b75-6bef61b882bc

import Mathlib
import Definitions.Def_LearnNoConc_ERM_Setting
open MeasureTheory
open scoped ENNReal
namespace Queelius.SmallBallScale
open LearnNoConc.ERM
lemma shift_sup {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F : Set (Ω → ℝ)) (fstar : Ω → ℝ) (r : ℝ) (Φ : (Ω → ℝ) → ℝ≥0∞) :
    (⨆ f ∈ locBall μ F fstar r,Φ (f-fstar))=
      ⨆ h ∈ {h ∈ shift F fstar | eLpNorm h 2 μ ≤ ENNReal.ofReal r},Φ h := by
  apply le_antisymm
  · apply iSup_le
    intro f
    apply iSup_le
    intro hf
    exact le_iSup_of_le (f-fstar) (le_iSup_of_le ⟨⟨f,hf.1,rfl⟩,hf.2⟩ le_rfl)
  · apply iSup_le
    intro h
    apply iSup_le
    rintro ⟨⟨f,hf,rfl⟩,hn⟩
    exact le_iSup_of_le f (le_iSup_of_le ⟨hf,hn⟩ le_rfl)
lemma normalization (N : ℕ) (hN : 0 < N) :
    (Real.sqrt N)⁻¹=Real.sqrt N*(N:ℝ)⁻¹ := by
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hn
  have hsq := Real.sq_sqrt hn.le
  field_simp
  nlinarith
lemma process_scale {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F : Set (Ω → ℝ)) (fstar : Ω → ℝ) (N : ℕ) (hN : 0 < N) (r : ℝ) :
    (∫⁻ x,(2^N)⁻¹*∑ σ : Fin N → Bool,⨆ f ∈ locBall μ F fstar r,
      ‖(Real.sqrt N)⁻¹*∑ i,sgn σ i*(f (x i)-fstar (x i))‖ₑ
      ∂(Measure.pi fun _ : Fin N => μ))=
    ENNReal.ofReal (Real.sqrt N)*radSup μ {h ∈ shift F fstar | eLpNorm h 2 μ ≤ ENNReal.ofReal r} N := by
  have he (x : Fin N → Ω) (σ : Fin N → Bool) (f : Ω → ℝ) :
      ‖(Real.sqrt N)⁻¹*∑ i,sgn σ i*(f (x i)-fstar (x i))‖ₑ=
        ENNReal.ofReal (Real.sqrt N)*‖(N:ℝ)⁻¹*∑ i,sgn σ i*(f (x i)-fstar (x i))‖ₑ := by
    rw [normalization N hN,mul_assoc,enorm_mul,Real.enorm_of_nonneg (Real.sqrt_nonneg _)]
  simp_rw [he,← ENNReal.mul_iSup]
  have hs (x : Fin N → Ω) (σ : Fin N → Bool) :
      (⨆ f ∈ locBall μ F fstar r,‖(N:ℝ)⁻¹*∑ i,sgn σ i*(f (x i)-fstar (x i))‖ₑ)=
        ⨆ h ∈ {h ∈ shift F fstar | eLpNorm h 2 μ ≤ ENNReal.ofReal r},
          ‖(N:ℝ)⁻¹*∑ i,sgn σ i*h (x i)‖ₑ := by
    exact shift_sup μ F fstar r (fun h => ‖(N:ℝ)⁻¹*∑ i,sgn σ i*h (x i)‖ₑ)
  simp_rw [hs,← Finset.mul_sum]
  simp_rw [mul_left_comm ((2:ℝ≥0∞)^N)⁻¹ (ENNReal.ofReal (Real.sqrt N))]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rfl
lemma cast_le {a : ℝ≥0∞} {b : ℝ} (hb : 0 ≤ b) :
    (a:EReal) ≤ (b:EReal) ↔ a ≤ ENNReal.ofReal b := by
  have he : (ENNReal.ofReal b:EReal)=(b:EReal) := by
    rw [EReal.coe_ennreal_ofReal,max_eq_left hb]
  rw [← he,EReal.coe_ennreal_le_coe_ennreal_iff]
lemma scale_le (a : ℝ≥0∞) (c b : ℝ) (hc : 0 < c) (hb : 0 ≤ b) :
    ((ENNReal.ofReal c*a : ℝ≥0∞):EReal) ≤ ((c*b:ℝ):EReal) ↔ (a:EReal) ≤ (b:EReal) := by
  rw [cast_le (mul_nonneg hc.le hb),ENNReal.ofReal_mul hc.le,
    ENNReal.mul_le_mul_iff_right (ne_of_gt (ENNReal.ofReal_pos.mpr hc)) ENNReal.ofReal_ne_top,
    ← cast_le hb]
end Queelius.SmallBallScale

namespace LearnNoConc.ERM

open MeasureTheory
open scoped ENNReal

/-- §5, p. 20: `β*_N(γ) = β_N(F − f*, γ)`. -/
theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : Set (Ω → ℝ)) (fstar : Ω → ℝ) (N : ℕ) (hN : 0 < N)
    (γ : ℝ) (hγ : 0 < γ) :
    betaStar μ F fstar N γ = betaN μ (shift F fstar) N γ := by
  unfold betaStar betaN
  congr 1
  ext R
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hcoeff (r : ℝ) : γ*Real.sqrt N*r=Real.sqrt N*(γ*r) := by ring
  constructor
  · rintro ⟨r,hr,hR,hi⟩
    refine ⟨r,hr,hR,?_⟩
    rw [Queelius.SmallBallScale.process_scale μ F fstar N hN r,hcoeff] at hi
    exact (Queelius.SmallBallScale.scale_le _ _ _ hs (mul_nonneg hγ.le hr.le)).mp hi
  · rintro ⟨r,hr,hR,hi⟩
    refine ⟨r,hr,hR,?_⟩
    rw [Queelius.SmallBallScale.process_scale μ F fstar N hN r,hcoeff]
    exact (Queelius.SmallBallScale.scale_le _ _ _ hs (mul_nonneg hγ.le hr.le)).mpr hi

end LearnNoConc.ERM
