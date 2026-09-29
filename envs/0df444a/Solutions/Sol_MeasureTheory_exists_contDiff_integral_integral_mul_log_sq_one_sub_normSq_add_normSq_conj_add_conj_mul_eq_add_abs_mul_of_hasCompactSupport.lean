-- Prove2me | solution 1 for MeasureTheory.exists_contDiff_integral_integral_mul_log_sq_one_sub_normSq_add_normSq_conj_add_conj_mul_eq_add_abs_mul_of_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/77403bea-17a8-5f7f-aaee-22af2fea980c

import Mathlib
import Theorems.Thm_Complex_normSq_conj_add_conj_mul_eq_and_complete_square
import Theorems.Thm_MeasureTheory_exists_contDiff_integral_integral_mul_log_sq_linear_add_sq_mul_sq_eq_add_abs_mul_of_hasCompactSupport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_exists_contDiff_integral_integral_mul_log_sq_one_sub_normSq_add_normSq_conj_add_conj_mul_eq_add_abs_mul_of_hasCompactSupport

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory

noncomputable section

namespace InertCore

theorem fold_sq (a x y b ρ : ℝ) (ha : 0 < a) :
    a * ((x + 2 * b * y / a) ^ 2 + (ρ * Real.sqrt (y ^ 2 + a) / a) ^ 2) =
      (Real.sqrt a * x + (2 * b / Real.sqrt a) * y) ^ 2 + (ρ * (Real.sqrt (y ^ 2 + a) / Real.sqrt a)) ^ 2 := by
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 < s ∧ a = s ^ 2 := ⟨Real.sqrt a, Real.sqrt_pos.mpr ha, (Real.sq_sqrt ha.le).symm⟩
  rw [Real.sqrt_sq hs.le]
  set q := Real.sqrt (y ^ 2 + s ^ 2)
  have hs0 : s ≠ 0 := hs.ne'
  field_simp

section Split
variable {V : Type} [MeasurableSpace V] (μ : Measure V) [SFinite μ]

def TA : ℂ × V ≃ᵐ ℝ × (ℝ × V) :=
  (MeasurableEquiv.prodCongr Complex.measurableEquivRealProd (MeasurableEquiv.refl V)).trans MeasurableEquiv.prodAssoc

def TC : ℂ × V ≃ᵐ ℝ × (ℝ × V) :=
  (MeasurableEquiv.prodCongr (Complex.measurableEquivRealProd.trans MeasurableEquiv.prodComm)
    (MeasurableEquiv.refl V)).trans MeasurableEquiv.prodAssoc

omit μ in
theorem TA_apply (z : ℂ) (v : V) : (TA : ℂ × V ≃ᵐ ℝ × (ℝ × V)) (z, v) = (z.re, (z.im, v)) := rfl

omit μ in
theorem TC_apply (z : ℂ) (v : V) : (TC : ℂ × V ≃ᵐ ℝ × (ℝ × V)) (z, v) = (z.im, (z.re, v)) := rfl

theorem mpR : MeasurePreserving (Complex.measurableEquivRealProd : ℂ → ℝ × ℝ) (volume : Measure ℂ)
    ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
  have h := Complex.volume_preserving_equiv_real_prod
  rwa [Measure.volume_eq_prod] at h

theorem measurePreserving_TA :
    MeasurePreserving (TA : ℂ × V ≃ᵐ ℝ × (ℝ × V)) ((volume : Measure ℂ).prod μ)
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod μ)) :=
  (measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure ℝ) μ).comp
    (mpR.prod (MeasurePreserving.id μ))

theorem measurePreserving_TC :
    MeasurePreserving (TC : ℂ × V ≃ᵐ ℝ × (ℝ × V)) ((volume : Measure ℂ).prod μ)
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod μ)) :=
  (measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure ℝ) μ).comp
    (((Measure.measurePreserving_swap).comp mpR).prod (MeasurePreserving.id μ))

end Split

theorem chart
    {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure]
    (g : P × (ℂ × V) → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (wχ : P → ℝ) (hw : ContDiff ℝ (⊤ : ℕ∞) wχ)
    (a : P → ℝ) (ha : ContDiff ℝ (⊤ : ℕ∞) a) (ha0 : ∀ p, 0 < a p)
    (b : P → ℝ) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (re im : ℂ →L[ℝ] ℝ) (mk : ℝ × ℝ →L[ℝ] ℂ) (hmk : ∀ z : ℂ, mk (re z, im z) = z)
    (hre : ∀ s : ℝ × ℝ, re (mk s) = s.1) (him : ∀ s : ℝ × ℝ, im (mk s) = s.2)
    (T : ℂ × V ≃ᵐ ℝ × (ℝ × V))
    (hT : MeasurePreserving T ((volume : Measure ℂ).prod μ) ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod μ)))
    (hTapply : ∀ (z : ℂ) (v : V), T (z, v) = (re z, (im z, v))) :
    ∃ A₁ B₁ : P × ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) A₁ ∧ ContDiff ℝ (⊤ : ℕ∞) B₁ ∧
      ∀ (p : P) (ρ : ℝ),
        Integrable (fun zv : ℂ × V => ((wχ p : ℝ) : ℂ) * g (p, zv) *
          (Real.log ((Real.sqrt (a p) * re zv.1 + (2 * b p / Real.sqrt (a p)) * im zv.1) ^ 2 +
            (ρ * (Real.sqrt ((im zv.1) ^ 2 + a p) / Real.sqrt (a p))) ^ 2) : ℂ)) ((volume : Measure ℂ).prod μ) ∧
        ∫ zv : ℂ × V, ((wχ p : ℝ) : ℂ) * g (p, zv) *
          (Real.log ((Real.sqrt (a p) * re zv.1 + (2 * b p / Real.sqrt (a p)) * im zv.1) ^ 2 +
            (ρ * (Real.sqrt ((im zv.1) ^ 2 + a p) / Real.sqrt (a p))) ^ 2) : ℂ) ∂((volume : Measure ℂ).prod μ) =
          A₁ (p, ρ) + ((|ρ| : ℝ) : ℂ) * B₁ (p, ρ) := by

  have hΘc : Continuous fun q : P × (ℝ × (ℝ × V)) => (q.1, (mk (q.2.1, q.2.2.1), q.2.2.2)) := by fun_prop
  have hΘic : Continuous fun x : P × (ℂ × V) => (x.1, (re x.2.1, (im x.2.1, x.2.2))) := by fun_prop
  let Θ : P × (ℝ × (ℝ × V)) ≃ₜ P × (ℂ × V) :=
  { toFun := fun q => (q.1, (mk (q.2.1, q.2.2.1), q.2.2.2))
    invFun := fun x => (x.1, (re x.2.1, (im x.2.1, x.2.2)))
    left_inv := by
      rintro ⟨p, s, y, v⟩
      show (p, (re (mk (s, y)), (im (mk (s, y)), v))) = (p, (s, (y, v)))
      rw [hre, him]
    right_inv := by
      rintro ⟨p, z, v⟩
      show (p, (mk (re z, im z), v)) = (p, (z, v))
      rw [hmk]
    continuous_toFun := hΘc
    continuous_invFun := hΘic }

  have hsa : ContDiff ℝ (⊤ : ℕ∞) fun p => Real.sqrt (a p) := ha.sqrt fun p => (ha0 p).ne'
  have hsa0 : ∀ p, Real.sqrt (a p) ≠ 0 := fun p => (Real.sqrt_pos.mpr (ha0 p)).ne'
  set gθ : P × (ℝ × (ℝ × V)) → ℂ := fun q => ((wχ q.1 : ℝ) : ℂ) * g (q.1, (mk (q.2.1, q.2.2.1), q.2.2.2)) with hgθ
  have hgθs : ContDiff ℝ (⊤ : ℕ∞) gθ := by
    refine ((Complex.ofRealCLM.contDiff.comp (hw.comp contDiff_fst)).mul (hg.comp ?_))
    exact contDiff_fst.prodMk (((mk.contDiff.comp ((contDiff_fst.comp contDiff_snd).prodMk
      ((contDiff_fst.comp (contDiff_snd.comp contDiff_snd))))).prodMk (contDiff_snd.comp (contDiff_snd.comp contDiff_snd))))
  have hgθc : HasCompactSupport gθ := by
    have h1 : HasCompactSupport (fun x : P × (ℂ × V) => ((wχ x.1 : ℝ) : ℂ) * g x) := hgc.mul_left
    exact h1.comp_homeomorph Θ
  set φ : P → (ℝ × V →L[ℝ] ℝ) := fun p => (2 * b p / Real.sqrt (a p)) • ContinuousLinearMap.fst ℝ ℝ V with hφ
  have hφs : ContDiff ℝ (⊤ : ℕ∞) φ := ((contDiff_const.mul hb).div hsa hsa0).smul contDiff_const
  set θ : P × (ℝ × V) → ℝ := fun q => Real.sqrt (q.2.1 ^ 2 + a q.1) / Real.sqrt (a q.1) with hθ
  have hθs : ContDiff ℝ (⊤ : ℕ∞) θ := by
    refine ContDiff.div ?_ (hsa.comp contDiff_fst) fun q => hsa0 q.1
    refine (((contDiff_fst.comp contDiff_snd).pow 2).add (ha.comp contDiff_fst)).sqrt fun q => ?_
    exact (add_pos_of_nonneg_of_pos (sq_nonneg _) (ha0 q.1)).ne'
  have hθ0 : ∀ q, 0 ≤ θ q := fun q => div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  obtain ⟨A₁, B₁, hA₁, hB₁, hR⟩ :=
    MeasureTheory.exists_contDiff_integral_integral_mul_log_sq_linear_add_sq_mul_sq_eq_add_abs_mul_of_hasCompactSupport
      ((volume : Measure ℝ).prod μ) gθ hgθs hgθc (fun p => Real.sqrt (a p)) hsa hsa0 φ hφs θ hθs hθ0
  refine ⟨A₁, B₁, hA₁, hB₁, fun p ρ => ?_⟩
  obtain ⟨hI, hE⟩ := hR p ρ

  set G : ℝ × (ℝ × V) → ℂ := fun sv =>
    gθ (p, sv) * (Real.log ((Real.sqrt (a p) * sv.1 + φ p sv.2) ^ 2 + (ρ * θ (p, sv.2)) ^ 2) : ℂ) with hG
  have hcomp : (fun zv : ℂ × V => ((wχ p : ℝ) : ℂ) * g (p, zv) *
      (Real.log ((Real.sqrt (a p) * re zv.1 + (2 * b p / Real.sqrt (a p)) * im zv.1) ^ 2 +
        (ρ * (Real.sqrt ((im zv.1) ^ 2 + a p) / Real.sqrt (a p))) ^ 2) : ℂ)) = G ∘ T := by
    funext zv
    obtain ⟨z, v⟩ := zv
    show _ = G (T (z, v))
    rw [hTapply]
    show _ = ((wχ p : ℝ) : ℂ) * g (p, (mk (re z, im z), v)) *
      (Real.log ((Real.sqrt (a p) * re z + ((2 * b p / Real.sqrt (a p)) • ContinuousLinearMap.fst ℝ ℝ V) (im z, v)) ^ 2 +
        (ρ * (Real.sqrt ((im z) ^ 2 + a p) / Real.sqrt (a p))) ^ 2) : ℂ)
    rw [hmk, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_fst', smul_eq_mul]
  refine ⟨?_, ?_⟩
  · rw [hcomp]; exact (hT.integrable_comp_emb T.measurableEmbedding).mpr hI
  · rw [hcomp]
    rw [show (∫ zv, (G ∘ ⇑T) zv ∂((volume : Measure ℂ).prod μ)) = ∫ sv, G sv ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).prod μ))
      from hT.integral_comp' G]
    exact hE

end InertCore

end

open InertCore in
theorem solution
    {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure]
    (g : P × (ℂ × V) → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (ϱ : P → ℂ) (hϱ : ContDiff ℝ (⊤ : ℕ∞) ϱ) :
    ∃ A B : P → ℂ, ContDiff ℝ (⊤ : ℕ∞) A ∧ ContDiff ℝ (⊤ : ℕ∞) B ∧
      ∀ p : P,
        Integrable (fun zv : ℂ × V =>
          g (p, zv) * (Real.log ((1 - ‖ϱ p‖ ^ 2) ^ 2 +
            ‖(starRingEnd ℂ) zv.1 + (starRingEnd ℂ) (ϱ p) * zv.1‖ ^ 2) : ℂ)) ((volume : Measure ℂ).prod μ) ∧
        ∫ zv : ℂ × V, g (p, zv) * (Real.log ((1 - ‖ϱ p‖ ^ 2) ^ 2 +
            ‖(starRingEnd ℂ) zv.1 + (starRingEnd ℂ) (ϱ p) * zv.1‖ ^ 2) : ℂ) ∂((volume : Measure ℂ).prod μ) =
          A p + ((|1 - ‖ϱ p‖ ^ 2| : ℝ) : ℂ) * B p := by
  classical

  set Aq : P → ℝ := fun p => ‖1 + ϱ p‖ ^ 2 with hAq
  set Cq : P → ℝ := fun p => ‖1 - ϱ p‖ ^ 2 with hCq
  have hAqs : ContDiff ℝ (⊤ : ℕ∞) Aq := (contDiff_const.add hϱ).norm_sq ℝ
  have hCqs : ContDiff ℝ (⊤ : ℕ∞) Cq := (contDiff_const.sub hϱ).norm_sq ℝ
  have hsum : ∀ p, Aq p + Cq p = 2 * (1 + ‖ϱ p‖ ^ 2) := fun p =>
    (Complex.normSq_conj_add_conj_mul_eq_and_complete_square (ϱ p) 0).2.1
  have hST : ContDiff ℝ (⊤ : ℕ∞) Real.smoothTransition := Real.smoothTransition.contDiff
  set χA : P → ℝ := fun p => Real.smoothTransition (5 - 4 * Cq p) with hχA
  set χC : P → ℝ := fun p => 1 - χA p with hχC
  have hχAs : ContDiff ℝ (⊤ : ℕ∞) χA := hST.comp (contDiff_const.sub (contDiff_const.mul hCqs))
  have hχCs : ContDiff ℝ (⊤ : ℕ∞) χC := contDiff_const.sub hχAs
  set a : P → ℝ := fun p => Aq p + Real.smoothTransition (3 - 4 * Aq p) with ha
  set c : P → ℝ := fun p => Cq p + Real.smoothTransition (4 - 4 * Cq p) with hc
  have has : ContDiff ℝ (⊤ : ℕ∞) a := hAqs.add (hST.comp (contDiff_const.sub (contDiff_const.mul hAqs)))
  have hcs : ContDiff ℝ (⊤ : ℕ∞) c := hCqs.add (hST.comp (contDiff_const.sub (contDiff_const.mul hCqs)))
  have hAq0 : ∀ p, 0 ≤ Aq p := fun p => sq_nonneg _
  have hCq0 : ∀ p, 0 ≤ Cq p := fun p => sq_nonneg _
  have ha0 : ∀ p, 0 < a p := by
    intro p
    by_cases h : 3 - 4 * Aq p ≤ 0
    · have : (0 : ℝ) ≤ Real.smoothTransition (3 - 4 * Aq p) := Real.smoothTransition.nonneg _
      show 0 < Aq p + Real.smoothTransition (3 - 4 * Aq p)
      linarith
    · push Not at h
      have : 0 < Real.smoothTransition (3 - 4 * Aq p) := Real.smoothTransition.pos_of_pos h
      show 0 < Aq p + Real.smoothTransition (3 - 4 * Aq p)
      linarith [hAq0 p]
  have hc0 : ∀ p, 0 < c p := by
    intro p
    by_cases h : 4 - 4 * Cq p ≤ 0
    · have : (0 : ℝ) ≤ Real.smoothTransition (4 - 4 * Cq p) := Real.smoothTransition.nonneg _
      show 0 < Cq p + Real.smoothTransition (4 - 4 * Cq p)
      linarith
    · push Not at h
      have : 0 < Real.smoothTransition (4 - 4 * Cq p) := Real.smoothTransition.pos_of_pos h
      show 0 < Cq p + Real.smoothTransition (4 - 4 * Cq p)
      linarith [hCq0 p]

  have hchartA : ∀ p, χA p ≠ 0 → a p = ‖1 + ϱ p‖ ^ 2 ∧ ‖1 + ϱ p‖ ≠ 0 := by
    intro p hp
    have hC : Cq p < 5 / 4 := by
      by_contra h
      push Not at h
      exact hp (Real.smoothTransition.zero_of_nonpos (by show 5 - 4 * Cq p ≤ 0; linarith))
    have hA : 3 / 4 < Aq p := by have := hsum p; nlinarith [norm_nonneg (ϱ p)]
    refine ⟨?_, ?_⟩
    · show Aq p + Real.smoothTransition (3 - 4 * Aq p) = ‖1 + ϱ p‖ ^ 2
      rw [Real.smoothTransition.zero_of_nonpos (by linarith), add_zero]
    · intro h0
      have : Aq p = 0 := by show ‖1 + ϱ p‖ ^ 2 = 0; rw [h0]; ring
      linarith
  have hchartC : ∀ p, χC p ≠ 0 → c p = ‖1 - ϱ p‖ ^ 2 ∧ ‖1 - ϱ p‖ ≠ 0 := by
    intro p hp
    have hC : 1 < Cq p := by
      by_contra h
      push Not at h
      apply hp
      show 1 - Real.smoothTransition (5 - 4 * Cq p) = 0
      rw [Real.smoothTransition.one_of_one_le (by linarith), sub_self]
    refine ⟨?_, ?_⟩
    · show Cq p + Real.smoothTransition (4 - 4 * Cq p) = ‖1 - ϱ p‖ ^ 2
      rw [Real.smoothTransition.zero_of_nonpos (by linarith), add_zero]
    · intro h0
      have : Cq p = 0 := by show ‖1 - ϱ p‖ ^ 2 = 0; rw [h0]; ring
      linarith

  have hbs : ContDiff ℝ (⊤ : ℕ∞) fun p => (ϱ p).im := Complex.imCLM.contDiff.comp hϱ
  have hρs : ContDiff ℝ (⊤ : ℕ∞) fun p => 1 - ‖ϱ p‖ ^ 2 := contDiff_const.sub (hϱ.norm_sq ℝ)

  have hmkA : ∀ z : ℂ, (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ) (Complex.reCLM z, Complex.imCLM z) = z := by
    intro z; apply Complex.ext <;> simp
  have hmkC : ∀ z : ℂ, ((Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ).comp
      (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ : ℝ × ℝ →L[ℝ] ℝ × ℝ)) (Complex.imCLM z, Complex.reCLM z) = z := by
    intro z; apply Complex.ext <;> simp
  obtain ⟨A₁, B₁, hA₁, hB₁, hcA⟩ := chart μ g hg hgc χA hχAs a has ha0 (fun p => (ϱ p).im) hbs
    Complex.reCLM Complex.imCLM (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ) hmkA
    (fun s => by simp) (fun s => by simp)
    TA (measurePreserving_TA μ) (fun z v => TA_apply z v)
  obtain ⟨A₂, B₂, hA₂, hB₂, hcC⟩ := chart μ g hg hgc χC hχCs c hcs hc0 (fun p => (ϱ p).im) hbs
    Complex.imCLM Complex.reCLM
    (((Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ).comp
      (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ : ℝ × ℝ →L[ℝ] ℝ × ℝ))) hmkC
    (fun s => by simp) (fun s => by simp)
    TC (measurePreserving_TC μ) (fun z v => TC_apply z v)

  have hq : ContDiff ℝ (⊤ : ℕ∞) fun p : P => (p, 1 - ‖ϱ p‖ ^ 2) := contDiff_id.prodMk hρs
  refine ⟨fun p => A₁ (p, 1 - ‖ϱ p‖ ^ 2) + A₂ (p, 1 - ‖ϱ p‖ ^ 2),
    fun p => B₁ (p, 1 - ‖ϱ p‖ ^ 2) + B₂ (p, 1 - ‖ϱ p‖ ^ 2),
    (hA₁.comp hq).add (hA₂.comp hq), (hB₁.comp hq).add (hB₂.comp hq), fun p => ?_⟩
  set ρ : ℝ := 1 - ‖ϱ p‖ ^ 2 with hρ
  obtain ⟨hIA, hEA⟩ := hcA p ρ
  obtain ⟨hIC, hEC⟩ := hcC p ρ
  set f : ℂ × V → ℂ := fun zv => g (p, zv) * (Real.log ((1 - ‖ϱ p‖ ^ 2) ^ 2 +
      ‖(starRingEnd ℂ) zv.1 + (starRingEnd ℂ) (ϱ p) * zv.1‖ ^ 2) : ℂ) with hf
  set FA : ℂ × V → ℂ := fun zv => ((χA p : ℝ) : ℂ) * g (p, zv) *
      (Real.log ((Real.sqrt (a p) * Complex.reCLM zv.1 + (2 * (ϱ p).im / Real.sqrt (a p)) * Complex.imCLM zv.1) ^ 2 +
        (ρ * (Real.sqrt ((Complex.imCLM zv.1) ^ 2 + a p) / Real.sqrt (a p))) ^ 2) : ℂ) with hFA
  set FC : ℂ × V → ℂ := fun zv => ((χC p : ℝ) : ℂ) * g (p, zv) *
      (Real.log ((Real.sqrt (c p) * Complex.imCLM zv.1 + (2 * (ϱ p).im / Real.sqrt (c p)) * Complex.reCLM zv.1) ^ 2 +
        (ρ * (Real.sqrt ((Complex.reCLM zv.1) ^ 2 + c p) / Real.sqrt (c p))) ^ 2) : ℂ) with hFC

  have hFA_eq : ∀ zv, FA zv = ((χA p : ℝ) : ℂ) * f zv := by
    intro zv
    by_cases hp : χA p = 0
    · show ((χA p : ℝ) : ℂ) * g (p, zv) * _ = ((χA p : ℝ) : ℂ) * _
      rw [hp, Complex.ofReal_zero, zero_mul, zero_mul, zero_mul]
    · obtain ⟨hap, h1p⟩ := hchartA p hp
      have hk := (Complex.normSq_conj_add_conj_mul_eq_and_complete_square (ϱ p) zv.1).2.2.1 h1p
      show ((χA p : ℝ) : ℂ) * g (p, zv) * _ = ((χA p : ℝ) : ℂ) * (g (p, zv) * _)
      rw [mul_assoc]
      congr 2
      simp only [Complex.reCLM_apply, Complex.imCLM_apply]
      rw [hk, hap, fold_sq _ _ _ _ _ (by rw [← hap]; exact ha0 p)]
  have hFC_eq : ∀ zv, FC zv = ((χC p : ℝ) : ℂ) * f zv := by
    intro zv
    by_cases hp : χC p = 0
    · show ((χC p : ℝ) : ℂ) * g (p, zv) * _ = ((χC p : ℝ) : ℂ) * _
      rw [hp, Complex.ofReal_zero, zero_mul, zero_mul, zero_mul]
    · obtain ⟨hcp, h1p⟩ := hchartC p hp
      have hk := (Complex.normSq_conj_add_conj_mul_eq_and_complete_square (ϱ p) zv.1).2.2.2 h1p
      show ((χC p : ℝ) : ℂ) * g (p, zv) * _ = ((χC p : ℝ) : ℂ) * (g (p, zv) * _)
      rw [mul_assoc]
      congr 2
      simp only [Complex.reCLM_apply, Complex.imCLM_apply]
      rw [hk, hcp, fold_sq _ _ _ _ _ (by rw [← hcp]; exact hc0 p)]
  have hsumf : ∀ zv, f zv = FA zv + FC zv := by
    intro zv
    rw [hFA_eq, hFC_eq, ← add_mul]
    show f zv = (((χA p : ℝ) : ℂ) + (((1 - χA p : ℝ)) : ℂ)) * f zv
    push_cast
    ring
  refine ⟨?_, ?_⟩
  · exact (hIA.add hIC).congr (Filter.Eventually.of_forall fun zv => (hsumf zv).symm)
  · show ∫ zv, f zv ∂((volume : Measure ℂ).prod μ) = _
    rw [show (∫ zv, f zv ∂((volume : Measure ℂ).prod μ)) = ∫ zv, (FA zv + FC zv) ∂((volume : Measure ℂ).prod μ) from by
      congr 1; funext zv; exact hsumf zv]
    rw [integral_add hIA hIC]
    rw [show (∫ zv, FA zv ∂((volume : Measure ℂ).prod μ)) = A₁ (p, ρ) + ((|ρ| : ℝ) : ℂ) * B₁ (p, ρ) from hEA,
      show (∫ zv, FC zv ∂((volume : Measure ℂ).prod μ)) = A₂ (p, ρ) + ((|ρ| : ℝ) : ℂ) * B₂ (p, ρ) from hEC]
    ring

end S_MeasureTheory_exists_contDiff_integral_integral_mul_log_sq_one_sub_normSq_add_normSq_conj_add_conj_mul_eq_add_abs_mul_of_hasCompactSupport
end P2MW
export P2MW.S_MeasureTheory_exists_contDiff_integral_integral_mul_log_sq_one_sub_normSq_add_normSq_conj_add_conj_mul_eq_add_abs_mul_of_hasCompactSupport (solution)
