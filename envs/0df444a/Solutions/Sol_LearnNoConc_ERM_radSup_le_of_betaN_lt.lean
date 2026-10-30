-- Prove2me | solution 1 for LearnNoConc.ERM.radSup_le_of_betaN_lt
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-29T08:43:05.195358+00:00
-- url     : https://prove2.me/submissions/7bd3f79d-7687-48c4-ac91-3a24ca111ccc

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
theorem _root_.beta_equivalence_solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
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

namespace Queelius.SmallBallLocalization
open LearnNoConc.ERM
lemma rad_mono {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (G H : Set (Ω → ℝ)) (hGH : G ⊆ H) (N : ℕ) : radSup μ G N ≤ radSup μ H N := by
  unfold radSup
  apply lintegral_mono
  intro x
  apply mul_le_mul_right
  apply Finset.sum_le_sum
  intro σ _
  apply iSup_le
  intro h
  apply iSup_le
  intro hh
  exact le_iSup_of_le h (le_iSup_of_le (hGH hh) le_rfl)
lemma rad_scale {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (G : Set (Ω → ℝ)) (N : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    radSup μ ((fun h : Ω → ℝ => c • h) '' G) N=ENNReal.ofReal c*radSup μ G N := by
  unfold radSup
  simp_rw [iSup_image]
  have he (x : Fin N → Ω) (σ : Fin N → Bool) (h : Ω → ℝ) :
      ‖(N:ℝ)⁻¹*∑ i,sgn σ i*(c • h) (x i)‖ₑ=
        ENNReal.ofReal c*‖(N:ℝ)⁻¹*∑ i,sgn σ i*h (x i)‖ₑ := by
    have hs : (∑ i,sgn σ i*(c • h) (x i))=c*∑ i,sgn σ i*h (x i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Pi.smul_apply,smul_eq_mul]
      ring
    rw [hs,mul_left_comm (N:ℝ)⁻¹ c,enorm_mul,Real.enorm_of_nonneg hc]
  simp_rw [he,← ENNReal.mul_iSup,← Finset.mul_sum]
  simp_rw [mul_left_comm ((2:ℝ≥0∞)^N)⁻¹ (ENNReal.ofReal c)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
lemma feasible_mono {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (H : Set (Ω → ℝ)) (hH : StarShaped H) (N : ℕ) (γ : ℝ) (hγ : 0 ≤ γ)
    (s r : ℝ) (hs : 0 < s) (hsr : s ≤ r)
    (hbound : radSup μ {h ∈ H | eLpNorm h 2 μ ≤ ENNReal.ofReal s} N ≤ ENNReal.ofReal (γ*s)) :
    radSup μ {h ∈ H | eLpNorm h 2 μ ≤ ENNReal.ofReal r} N ≤ ENNReal.ofReal (γ*r) := by
  have hr : 0 < r := lt_of_lt_of_le hs hsr
  let c := s/r
  have hc : 0 < c := div_pos hs hr
  have hc1 : c ≤ 1 := (div_le_one hr).mpr hsr
  have hcr : c*r=s := div_mul_cancel₀ s hr.ne'
  have hinc : (fun h : Ω → ℝ => c • h) '' {h ∈ H | eLpNorm h 2 μ ≤ ENNReal.ofReal r} ⊆
      {h ∈ H | eLpNorm h 2 μ ≤ ENNReal.ofReal s} := by
    rintro _ ⟨h,hh,rfl⟩
    refine ⟨hH h hh.1 c hc hc1,?_⟩
    rw [eLpNorm_const_smul,Real.enorm_of_nonneg hc.le]
    calc
      _ ≤ ENNReal.ofReal c*ENNReal.ofReal r := mul_le_mul_right hh.2 _
      _ = ENNReal.ofReal s := by rw [← ENNReal.ofReal_mul hc.le,hcr]
  have hb : ENNReal.ofReal c*radSup μ {h ∈ H | eLpNorm h 2 μ ≤ ENNReal.ofReal r} N ≤
      ENNReal.ofReal c*ENNReal.ofReal (γ*r) := by
    calc
      _ = radSup μ ((fun h : Ω → ℝ => c • h) '' {h ∈ H | eLpNorm h 2 μ ≤ ENNReal.ofReal r}) N :=
        (rad_scale μ _ N c hc.le).symm
      _ ≤ radSup μ {h ∈ H | eLpNorm h 2 μ ≤ ENNReal.ofReal s} N := rad_mono μ _ _ hinc N
      _ ≤ ENNReal.ofReal (γ*s) := hbound
      _ = _ := by
        rw [← ENNReal.ofReal_mul hc.le]
        congr 1
        rw [mul_left_comm c γ,hcr]
  exact (ENNReal.mul_le_mul_iff_right (ne_of_gt (ENNReal.ofReal_pos.mpr hc)) ENNReal.ofReal_ne_top).mp hb
end Queelius.SmallBallLocalization

namespace LearnNoConc.ERM

open MeasureTheory
open scoped ENNReal

/-- §5, p. 20: if `H` is star-shaped around `0` and `r > β_N(H, γ)`, then
`E sup_{h ∈ H ∩ rD} |(1/N) ∑ ε_i h(X_i)| ≤ γ r`. -/
theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (H : Set (Ω → ℝ)) (hH : StarShaped H) (N : ℕ) (hN : 0 < N)
    (γ : ℝ) (hγ : 0 < γ) (r : ℝ) (hr : betaN μ H N γ < ENNReal.ofReal r) :
    radSup μ {h ∈ H | eLpNorm h 2 μ ≤ ENNReal.ofReal r} N ≤ ENNReal.ofReal (γ * r) := by
  obtain ⟨R,hR,hlt⟩ := sInf_lt_iff.mp hr
  obtain ⟨s,hs,rfl,hbound⟩ := hR
  obtain ⟨hsr,_⟩ := ENNReal.ofReal_lt_ofReal_iff'.mp hlt
  apply Queelius.SmallBallLocalization.feasible_mono μ H hH N γ hγ.le s r hs hsr.le
  exact (Queelius.SmallBallScale.cast_le (mul_nonneg hγ.le hs.le)).mp hbound

end LearnNoConc.ERM
