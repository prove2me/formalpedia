-- Prove2me | solution 1 for LanglandsTunnell.Converse.ArchDatumR.exists_W_diagOne_add_mul_W_diagOne_neg_ne_zero_of_one_le_weight
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/e3455251-c4e2-574d-b73e-fd00c4a74374

import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Mathlib.Analysis.MellinTransform
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_archDatumR_W_diagOne_add_eq_mul_mulConvGaussian_of_weightOne
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_archDatumR_W_diagOne_eq_mul_exp_and_eq_zero_of_discrete
import Theorems.Thm_LanglandsTunnell_mellin_mulConvGaussian_eq_archFactor_principal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_ArchDatumR_exists_W_diagOne_add_mul_W_diagOne_neg_ne_zero_of_one_le_weight
p2m_attr_erase "simp" "AutomorphicForm.iotaZsqrtdNegTwo_apply AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace Ws14TwoSheet

open LanglandsTunnell.Converse.ArchR

noncomputable def rotM (c d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![d / Real.sqrt (c ^ 2 + d ^ 2), -c / Real.sqrt (c ^ 2 + d ^ 2); c / Real.sqrt (c ^ 2 + d ^ 2), d / Real.sqrt (c ^ 2 + d ^ 2)]

theorem sqrt_pos_of {c d : ℝ} (h : c ≠ 0 ∨ d ≠ 0) : 0 < Real.sqrt (c ^ 2 + d ^ 2) := by
  apply Real.sqrt_pos.2
  rcases h with h | h
  · have := sq_pos_of_ne_zero h; positivity
  · have := sq_pos_of_ne_zero h; positivity

theorem det_rotM {c d : ℝ} (h : c ≠ 0 ∨ d ≠ 0) : (rotM c d).det = 1 := by
  have hr := sqrt_pos_of h
  have hr2 : Real.sqrt (c ^ 2 + d ^ 2) ^ 2 = c ^ 2 + d ^ 2 := Real.sq_sqrt (by positivity)
  rw [rotM, Matrix.det_fin_two_of]
  field_simp
  linarith [hr2]

noncomputable def rotGL {c d : ℝ} (h : c ≠ 0 ∨ d ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (rotM c d) (by rw [det_rotM h]; exact one_ne_zero)

theorem rotGL_coe {c d : ℝ} (h : c ≠ 0 ∨ d ≠ 0) : ((rotGL h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = rotM c d := rfl

theorem rotGL_mem {c d : ℝ} (h : c ≠ 0 ∨ d ≠ 0) : rotGL h ∈ rowIsometrySubgroup₀ ℝ := by
  have hr := sqrt_pos_of h
  have hr2 : Real.sqrt (c ^ 2 + d ^ 2) ^ 2 = c ^ 2 + d ^ 2 := Real.sq_sqrt (by positivity)
  rw [mem_rowIsometrySubgroup₀_iff]
  refine ⟨by rw [rotGL_coe, det_rotM h], ?_, ?_⟩
  · rw [rotGL_coe, det_rotM h, norm_one]
  · intro x y
    simp only [rotGL_coe, rotM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs]
    field_simp
    linear_combination (-(x ^ 2 + y ^ 2)) * hr2

theorem continuousOn_torus {P : RealArchParam} (D : ArchDatumR P) :
    ContinuousOn (fun τ : ℝ => D.W (diagOne τ)) {τ | τ ≠ 0} := by
  have hc : Continuous fun τ : ℝ => (fun i j => (!![τ, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) i j : Fin 2 → Fin 2 → ℝ) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  have hmaps : Set.MapsTo (fun τ : ℝ => (fun i j => (!![τ, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) i j : Fin 2 → Fin 2 → ℝ))
      {τ | τ ≠ 0} glSet := by
    intro τ hτ
    show (Matrix.of fun i j => (!![τ, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) i j).det ≠ 0
    rw [Matrix.det_fin_two]
    simpa using hτ
  have h := D.smooth.continuousOn.comp hc.continuousOn hmaps
  refine h.congr fun τ _ => ?_
  show D.W (diagOne τ) = D.W (Matrix.of fun i j => (!![τ, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) i j)
  rfl

theorem exists_torus_ne_zero {P : RealArchParam} (D : ArchDatumR P) (k : ℤ)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ k r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDnz : ∃ g : GL (Fin 2) ℝ, D.W (g : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0) :
    ∃ τ : ℝ, τ ≠ 0 ∧ D.W (diagOne τ) ≠ 0 := by
  obtain ⟨g, hg⟩ := hDnz
  set G : Matrix (Fin 2) (Fin 2) ℝ := (g : Matrix (Fin 2) (Fin 2) ℝ) with hG
  set c : ℝ := G 1 0 with hc
  set d : ℝ := G 1 1 with hd
  have hdet : G.det ≠ 0 := by
    rw [hG]; exact (Matrix.isUnits_det_units g).ne_zero
  have hcd : c ≠ 0 ∨ d ≠ 0 := by
    by_contra h
    push Not at h
    apply hdet
    rw [Matrix.det_fin_two, ← hc, ← hd, h.1, h.2]; ring
  set r : ℝ := Real.sqrt (c ^ 2 + d ^ 2) with hr
  have hr0 : 0 < r := sqrt_pos_of hcd
  have hr2 : r ^ 2 = c ^ 2 + d ^ 2 := Real.sq_sqrt (by positivity)

  set α : ℝ := (G 0 0 * d - G 0 1 * c) / r with hα
  set β : ℝ := (G 0 0 * c + G 0 1 * d) / r with hβ
  set Xm : Matrix (Fin 2) (Fin 2) ℝ := !![α, β; 0, r] with hXm
  have hXrot : Xm * rotM c d = G := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [hXm, rotM, Matrix.mul_apply, Fin.sum_univ_two, hα, hβ, ← hr]
      field_simp
      linear_combination (-(G 0 0)) * hr2
    · simp [hXm, rotM, Matrix.mul_apply, Fin.sum_univ_two, hα, hβ, ← hr]
      field_simp
      linear_combination (-(G 0 1)) * hr2
    · simp [hXm, rotM, Matrix.mul_apply, Fin.sum_univ_two, ← hr, ← hc]
      field_simp
    · simp [hXm, rotM, Matrix.mul_apply, Fin.sum_univ_two, ← hr, ← hd]
      field_simp
  have hαr : α * r ≠ 0 := by
    have h1 : Xm.det = α * r := by rw [hXm, Matrix.det_fin_two_of]; ring
    have h2 : Xm.det * (rotM c d).det = G.det := by rw [← Matrix.det_mul, hXrot]
    rw [det_rotM hcd, mul_one, h1] at h2
    rw [h2]; exact hdet
  have hα0 : α ≠ 0 := fun h => hαr (by rw [h, zero_mul])
  set Xg : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero Xm
    (by rw [hXm, Matrix.det_fin_two_of]; simpa using hαr) with hXg
  have hXg_coe : ((Xg : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = Xm := rfl

  have h1 : D.W G = (archWeightCharℝ k ⟨rotGL hcd, rotGL_mem hcd⟩ : ℂ) * D.W Xm := by
    have h := hDW ⟨rotGL hcd, rotGL_mem hcd⟩ Xg
    rw [hXg_coe] at h
    rw [← h]
    congr 1
    rw [Units.val_mul, hXg_coe]
    exact hXrot.symm

  have hXm_eq : Xm = r • (unip (β / r) * diagOne (α / r)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hXm, ArchR.unip, ArchR.diagOne, Matrix.smul_apply] <;>
      field_simp
  have h2 : D.W Xm = centralChar P r * ((|r| : ℝ) : ℂ) * (psi (β / r) * D.W (diagOne (α / r))) := by
    rw [hXm_eq, D.central_law r _ hr0.ne', D.unip_law]
  refine ⟨α / r, div_ne_zero hα0 hr0.ne', fun h0 => hg ?_⟩
  show D.W G = 0
  rw [h1, h2, h0, mul_zero, mul_zero, mul_zero]

noncomputable def G (p q : ℂ) (t : ℝ) : ℂ :=
  (4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
    ((r : ℂ) ^ p * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) * (((t / r : ℝ) : ℂ) ^ q * (Real.exp (-(Real.pi * (t / r) ^ 2)) : ℂ)) / (r : ℂ)

theorem archFactor_principal (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) (s : ℂ) :
    (RealArchParam.principal u₁ a₁ u₂ a₂).archFactor s =
      Complex.Gammaℝ (s + (u₁ + signShift a₁)) * Complex.Gammaℝ (s + (u₂ + signShift a₂)) := by
  simp [RealArchParam.archFactor, RealArchParam.gammaR, RealArchParam.gammaC]

theorem exists_G_ne_zero (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) :
    ∃ t : ℝ, 0 < t ∧ G (u₁ + signShift a₁) (u₂ + signShift a₂) t ≠ 0 := by
  by_contra hall
  push_neg at hall
  set σ : ℝ := max (1 - (u₁ + signShift a₁).re) (1 - (u₂ + signShift a₂).re) with hσ
  have h₁ : 0 < ((σ : ℂ) + (u₁ + signShift a₁)).re := by
    have : 1 - (u₁ + signShift a₁).re ≤ σ := le_max_left _ _
    simp only [Complex.add_re, Complex.ofReal_re] at this ⊢; linarith
  have h₂ : 0 < ((σ : ℂ) + (u₂ + signShift a₂)).re := by
    have : 1 - (u₂ + signShift a₂).re ≤ σ := le_max_right _ _
    simp only [Complex.add_re, Complex.ofReal_re] at this ⊢; linarith
  have hM := LanglandsTunnell.mellin_mulConvGaussian_eq_archFactor_principal u₁ a₁ u₂ a₂ (σ : ℂ) h₁ h₂
  have hz : mellin (fun y : ℝ => (4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
        ((t : ℂ) ^ (u₁ + signShift a₁) * (Real.exp (-(Real.pi * t ^ 2)) : ℂ)) *
          (((y / t : ℝ) : ℂ) ^ (u₂ + signShift a₂) * (Real.exp (-(Real.pi * (y / t) ^ 2)) : ℂ)) / (t : ℂ)) (σ : ℂ) = 0 := by
    rw [mellin]
    refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
    have := hall y hy
    rw [G] at this
    rw [this, smul_zero]
  rw [hz, archFactor_principal] at hM
  exact (mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos h₁) (Complex.Gammaℝ_ne_zero_of_re_pos h₂)) hM.symm

end Ws14TwoSheet

open Ws14TwoSheet LanglandsTunnell.Converse LanglandsTunnell.Converse.ArchR in
open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (huR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (huC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : ∀ v : InfinitePlace ℚ, v.IsReal →
      IsArchCompAt ℚ ω v
        ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
        ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), (kC w hw + 1))))
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (a : ℚ) (aInf : (InfiniteAdeleRing ℚ)ˣ)
    (haInf : (aInf : InfiniteAdeleRing ℚ) = algebraMap ℚ (InfiniteAdeleRing ℚ) a)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_add : MeasureTheory.Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2)) •
      MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume)
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (ha : a ≠ 0)
    (w₀ : InfinitePlace K) (h₀ : w₀.IsReal)
    (P₂ : RealArchParam)
    (hP₂ : ((∃ (w₁ w₂ : InfinitePlace K) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal),
          w₀ ≠ w₁ ∧ w₀ ≠ w₂ ∧ w₁ ≠ w₂ ∧ (∀ w : InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂) ∧
          P₂ = RealArchParam.principal (uR w₁ h₁) (aR w₁ h₁) (uR w₂ h₂) (aR w₂ h₂)) ∨
        (∃ (wC : InfinitePlace K) (hC : wC.IsComplex), (∀ w : InfinitePlace K, w = wC ∨ w = w₀) ∧
          ((∃ hk : kC wC hC ≠ 0, P₂ = RealArchParam.discrete (uC wC hC) (kC wC hC).natAbs (Int.natAbs_pos.mpr hk)) ∨
           (kC wC hC = 0 ∧ P₂ = RealArchParam.principal (uC wC hC) 0 (uC wC hC) 1)))))
    (D : ArchDatumR P₂) (k₀ : ℤ)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ k₀ r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDE : LanglandsTunnell.Converse.ArchCasimir.IsCasimirEigen D)
    (hDnz : ∃ g : GL (Fin 2) ℝ, D.W (g : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0)
    (hk₀min : (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P₂ = RealArchParam.principal u₁ a₁ u₂ a₂ →
        (k₀ = 0 ∨ k₀ = 1) ∧ ((k₀ : ZMod 2) = a₁ + a₂)) ∧
      (∀ (u : ℂ) (m : ℕ) (hm : 1 ≤ m), P₂ = RealArchParam.discrete u m hm → k₀ = (m : ℤ) + 1))
    (hk₀ : 1 ≤ k₀) (ε : ℂ) (hε : ε = 1 ∨ ε = -1) :
    ContinuousOn (fun τ : ℝ => D.W (ArchR.diagOne τ) + ε * D.W (ArchR.diagOne (-τ))) (Set.Ioi 0) ∧
      (∃ τ : ℝ, 0 < τ ∧ D.W (ArchR.diagOne τ) + ε * D.W (ArchR.diagOne (-τ)) ≠ 0) ∧
      0 < MeasureTheory.volume {τ : ℝ | 0 < τ ∧ D.W (ArchR.diagOne τ) + ε * D.W (ArchR.diagOne (-τ)) ≠ 0} := by

  have hcont : ContinuousOn (fun τ : ℝ => D.W (ArchR.diagOne τ) + ε * D.W (ArchR.diagOne (-τ))) (Set.Ioi 0) := by
    have hc := continuousOn_torus D
    have h1 : ContinuousOn (fun τ : ℝ => D.W (ArchR.diagOne τ)) (Set.Ioi 0) := hc.mono fun τ hτ => ne_of_gt hτ
    have h2 : ContinuousOn (fun τ : ℝ => D.W (ArchR.diagOne (-τ))) (Set.Ioi 0) :=
      hc.comp continuous_neg.continuousOn fun τ hτ => neg_ne_zero.mpr (ne_of_gt hτ)
    exact h1.add (continuousOn_const.mul h2)
  obtain ⟨τ₀, hτ₀, hne⟩ := exists_torus_ne_zero D k₀ hDW hDnz

  have hex : ∃ τ : ℝ, 0 < τ ∧ D.W (ArchR.diagOne τ) + ε * D.W (ArchR.diagOne (-τ)) ≠ 0 := by
    have hP₂' := hP₂

    have hprin : ∀ (u₁ u₂ : ℂ) (c₁ c₂ : ZMod 2), P₂ = RealArchParam.principal u₁ c₁ u₂ c₂ →
        ∃ τ : ℝ, 0 < τ ∧ D.W (ArchR.diagOne τ) + ε * D.W (ArchR.diagOne (-τ)) ≠ 0 := by
      intro u₁ u₂ c₁ c₂ hP
      obtain ⟨hk01, hsum⟩ := hk₀min.1 _ _ _ _ hP
      have hk1 : k₀ = 1 := by rcases hk01 with h | h <;> omega
      have hc : c₁ ≠ c₂ := by
        intro heq
        have h1 : c₁ + c₂ = 1 := by rw [← hsum, hk1]; simp
        rw [heq, CharTwo.add_self_eq_zero] at h1
        exact zero_ne_one h1
      obtain ⟨ρ, hρ⟩ := LanglandsTunnell.CubicInduction.exists_archDatumR_W_diagOne_add_eq_mul_mulConvGaussian_of_weightOne
        K hdeg μ hμ uR aR uC kC huR huC ω hω E hE a aInf haInf psiInf hpsiInf ν_add hν_add ν_mul ha
        w₀ h₀ P₂ hP₂ D k₀ hDW hDE hDnz hk₀min hk1 u₁ u₂ c₁ c₂ hP hc

      obtain ⟨b, hb⟩ : ∃ b : ZMod 2, ε = (-1 : ℂ) ^ b.val := by
        rcases hε with h | h
        · exact ⟨0, by rw [h]; simp⟩
        · exact ⟨1, by rw [h, ZMod.val_one]; simp⟩

      have hρ0 : ρ ≠ 0 := by
        intro h0
        have hv : ∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne τ) = 0 ∧ D.W (ArchR.diagOne (-τ)) = 0 := by
          intro τ hτ
          have e0 := hρ 0 τ hτ
          have e1 := hρ 1 τ hτ
          simp only [h0, zero_mul, ZMod.val_zero, pow_zero, one_mul, ZMod.val_one, pow_one, neg_mul] at e0 e1
          constructor
          · linear_combination (e0 + e1) / 2
          · linear_combination (e0 - e1) / 2
        apply hne
        rcases lt_or_gt_of_ne hτ₀ with hn | hp
        · have := (hv (-τ₀) (neg_pos.mpr hn)).2
          rwa [neg_neg] at this
        · exact (hv τ₀ hp).1
      obtain ⟨t, ht, hGt⟩ := exists_G_ne_zero u₁ u₂ (c₁ + b) (c₂ + b)
      refine ⟨t, ht, ?_⟩
      rw [hb, hρ b t ht]
      have : G (u₁ + signShift (c₁ + b)) (u₂ + signShift (c₂ + b)) t =
          (4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (u₁ + signShift (c₁ + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((t / r : ℝ) : ℂ) ^ (u₂ + signShift (c₂ + b)) * (Real.exp (-(Real.pi * (t / r) ^ 2)) : ℂ)) / (r : ℂ) := rfl
      rw [← this]
      exact mul_ne_zero (mul_ne_zero hρ0 (Complex.ofReal_ne_zero.mpr ht.ne')) hGt
    rcases hP₂' with ⟨w₁, w₂, h₁, h₂, -, -, -, -, hP⟩ | ⟨wC, hC, -, hP⟩
    · exact hprin _ _ _ _ hP
    · rcases hP with ⟨hk, hP⟩ | ⟨-, hP⟩
      ·
        obtain ⟨ρ, -, hneg⟩ := LanglandsTunnell.CubicInduction.exists_archDatumR_W_diagOne_eq_mul_exp_and_eq_zero_of_discrete
          K hdeg μ hμ uR aR uC kC huR huC ω hω E hE a aInf haInf psiInf hpsiInf ν_add hν_add ν_mul ha
          w₀ h₀ P₂ hP₂ D k₀ hDW hDE hDnz hk₀min _ _ _ hP
        have hp : 0 < τ₀ := by
          rcases lt_or_gt_of_ne hτ₀ with hn | hp
          · exfalso
            apply hne
            have := hneg (-τ₀) (neg_pos.mpr hn)
            rwa [neg_neg] at this
          · exact hp
        refine ⟨τ₀, hp, ?_⟩
        rw [hneg τ₀ hp, mul_zero, add_zero]
        exact hne
      · exact hprin _ _ _ _ hP

  refine ⟨hcont, hex, ?_⟩
  obtain ⟨τ₁, hτ₁, hne₁⟩ := hex
  have hopen : IsOpen (Set.Ioi (0 : ℝ) ∩ (fun τ : ℝ => D.W (ArchR.diagOne τ) + ε * D.W (ArchR.diagOne (-τ))) ⁻¹' {z | z ≠ 0}) :=
    hcont.isOpen_inter_preimage isOpen_Ioi isOpen_ne
  refine lt_of_lt_of_le (hopen.measure_pos MeasureTheory.volume ⟨τ₁, hτ₁, hne₁⟩) (MeasureTheory.measure_mono ?_)
  exact fun τ hτ => ⟨hτ.1, hτ.2⟩

#print axioms solution

end S_LanglandsTunnell_Converse_ArchDatumR_exists_W_diagOne_add_mul_W_diagOne_neg_ne_zero_of_one_le_weight
end P2MW
export P2MW.S_LanglandsTunnell_Converse_ArchDatumR_exists_W_diagOne_add_mul_W_diagOne_neg_ne_zero_of_one_le_weight (solution)
