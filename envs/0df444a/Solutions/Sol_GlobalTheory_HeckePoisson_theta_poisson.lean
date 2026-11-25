-- Prove2me | solution 1 for GlobalTheory.HeckePoisson.theta_poisson
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:02:12.525023+00:00
-- url     : https://prove2.me/submissions/da66fd28-09cb-4c47-a900-fba6e04d84a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EmbAApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierHarmonicMonomialMulGaussianComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierProdSingleCoordinateFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierCompCoordDilationByHalfExpStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeIdealEuclideanLatticeIsZLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianHarmonicProductKernelContinuousBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TsumRingEqSumIdealCosetsTsumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeThetaKernelPoissonSummation
import Theorems.Thm_GlobalTheory_HeckePoisson_norm_half_sq
import Theorems.Thm_GlobalTheory_HeckePoisson_gauss_dil_bound
import Theorems.Thm_GlobalTheory_HeckePoisson_poisson_coset
import Theorems.Thm_GlobalTheory_HeckePoisson_discrete_norm_ge
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_HeckePoisson_embA_apply
import Theorems.Thm_GlobalTheory_HeckePoisson_mem_lat
import Theorems.Thm_GlobalTheory_T_heckeIdealEuclideanLattice_isZLattice
import Theorems.Thm_GlobalTheory_T_tsum_ring_eq_sum_ideal_cosets_tsum
import Theorems.Thm_GlobalTheory_norm_cexp_two_pi_I
import Theorems.Thm_GlobalTheory_summable_lattice_exp_neg_mul_norm_sq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform
open GlobalTheory GlobalTheory.HeckePoisson
open GlobalTheory.HeckeTheta
variable {I : Type} [Fintype I]
namespace GlobalTheory.HeckePoisson
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I]
    (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ) (M : Ideal (NumberField.RingOfIntegers K))
    (F : NumberField.RingOfIntegers K → ℂ), M ≠ ⊥ → (∀ α μ : NumberField.RingOfIntegers K, μ ∈ M → F (α + μ) = F α) →
    ∃ (a : (I → ℂ) → ℂ) (κ : ℂ), (∀ ε : ℝ, 0 < ε → Summable (fun v => ‖a v‖ * Real.exp (-ε * ‖v‖ ^ 2))) ∧
      (∃ δ : ℝ, 0 < δ ∧ ∀ v, a v ≠ 0 → v ≠ 0 → δ ≤ ‖v‖) ∧
      ∀ y : I → ℝ, GlobalTheory.HeckeTheta.theta (fun α : NumberField.RingOfIntegers K => GlobalTheory.HeckeTheta.emb φ (α : K)) F n y =
        κ * (Real.exp (-∑ i, y i) : ℂ) * GlobalTheory.HeckeTheta.theta (fun v : I → ℂ => v) a n (-y) := by
  intro K _ _ _ I _ φ hφ n M F hM hF
  classical
  obtain ⟨hd, hz⟩ := GlobalTheory.T.heckeIdealEuclideanLattice_isZLattice K I φ hφ M hM
  haveI : Finite (𝓞 K ⧸ M) := Ideal.finiteQuotientOfFreeOfNeBot M hM
  letI : Fintype (𝓞 K ⧸ M) := Fintype.ofFinite _
  set L := lat φ M with hL
  set D := GlobalTheory.dualLattice L with hD
  have hI : Nonempty I := by
    obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
    obtain ⟨i, -, -⟩ := hφ σ
    exact ⟨i⟩
  have hinj : Function.Injective (embA φ) := by
    intro x x' h
    obtain ⟨i⟩ := hI
    have h2 := congrArg (fun z : EuclideanSpace ℂ I => z i) h
    simp only [embA_apply] at h2
    exact RingOfIntegers.ext ((φ i).injective h2)

  set u : 𝓞 K ⧸ M → EuclideanSpace ℂ I := fun c => embA φ (Quotient.out c) with hu
  set half : D → (I → ℂ) := fun l i => (l : EuclideanSpace ℂ I) i / 2 with hhalf_def
  have hhalf : Function.Injective half := by
    intro l l' h
    apply Subtype.ext
    ext i
    have := congrFun h i
    simp only [hhalf_def] at this
    linear_combination 2 * this
  set cov : ℂ := ((ZLattice.covolume L : ℝ) : ℂ) with hcov
  set A : D → ℂ := fun l => cov⁻¹ * ∑ c : 𝓞 K ⧸ M, F (Quotient.out c) *
    Complex.exp (2 * Real.pi * Complex.I * ((⟪(l : EuclideanSpace ℂ I), u c⟫ : ℝ) : ℂ)) with hA
  set a : (I → ℂ) → ℂ := fun v => if h : ∃ l : D, half l = v then A (Classical.choose h) else 0 with ha_def
  have ha_half : ∀ l, a (half l) = A l := by
    intro l
    have h : ∃ l' : D, half l' = half l := ⟨l, rfl⟩
    simp only [ha_def, dif_pos h]
    rw [hhalf (Classical.choose_spec h)]
  have ha_zero : ∀ v, v ∉ Set.range half → a v = 0 := by
    intro v hv
    have h : ¬ ∃ l : D, half l = v := fun ⟨l, hl⟩ => hv ⟨l, hl⟩
    simp only [ha_def, dif_neg h]
  set B : ℝ := ‖cov⁻¹‖ * ∑ c : 𝓞 K ⧸ M, ‖F (Quotient.out c)‖ with hB
  have hB0 : 0 ≤ B := by positivity
  have hAB : ∀ l, ‖A l‖ ≤ B := by
    intro l
    simp only [hA, hB, norm_mul]
    refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)) (norm_nonneg _)
    rw [norm_mul, GlobalTheory.norm_cexp_two_pi_I, mul_one]
  set cI : ℝ := (Fintype.card I : ℝ) with hcI
  have hcI0 : 0 ≤ cI := by positivity
  have hnorm : ∀ l : D, ‖(l : EuclideanSpace ℂ I)‖ ^ 2 ≤ (4 * cI + 1) * ‖half l‖ ^ 2 := by
    intro l
    have := norm_half_sq (l : EuclideanSpace ℂ I)
    nlinarith [sq_nonneg ‖half l‖]
  refine ⟨a, kappa n, ?_, ?_, ?_⟩
  ·
    intro ε hε
    have hpos : 0 < ε / (4 * cI + 1) := by positivity
    have key : Summable (fun l : D => ‖a (half l)‖ * Real.exp (-ε * ‖half l‖ ^ 2)) := by
      refine .of_nonneg_of_le (fun _ => by positivity) (fun l => ?_)
        ((GlobalTheory.summable_lattice_exp_neg_mul_norm_sq D hpos).mul_left B)
      rw [ha_half]
      refine mul_le_mul (hAB l) (Real.exp_le_exp.2 ?_) (by positivity) hB0
      have h1 := hnorm l
      have h2 : ε / (4 * cI + 1) * ‖(l : EuclideanSpace ℂ I)‖ ^ 2 ≤ ε * ‖half l‖ ^ 2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
      linarith
    exact (hhalf.summable_iff (f := fun v => ‖a v‖ * Real.exp (-ε * ‖v‖ ^ 2))
      (fun v hv => by simp [ha_zero v hv])).1 key
  ·
    obtain ⟨r, hr, hr'⟩ := discrete_norm_ge (GlobalTheory.dualLattice L)
    refine ⟨r / (4 * cI + 1), by positivity, fun v hav hv0 => ?_⟩
    by_cases hv : v ∈ Set.range half
    · obtain ⟨l, rfl⟩ := hv
      have hl0 : l ≠ 0 := by
        rintro rfl
        apply hv0
        funext i
        simp [hhalf_def]
      have h1 : r ≤ ‖(l : EuclideanSpace ℂ I)‖ := hr' ⟨l, l.2⟩ (fun h => hl0 (Subtype.ext (congrArg Subtype.val h)))
      have h2 := hnorm l
      have h3 : r ^ 2 ≤ ((4 * cI + 1) * ‖half l‖) ^ 2 := by
        have : r ^ 2 ≤ ‖(l : EuclideanSpace ℂ I)‖ ^ 2 := pow_le_pow_left₀ hr.le h1 2
        have h4 : (4 * cI + 1) * ‖half l‖ ^ 2 ≤ ((4 * cI + 1) * ‖half l‖) ^ 2 := by
          rw [mul_pow]
          have : (4 * cI + 1) ≤ (4 * cI + 1) ^ 2 := by nlinarith
          exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
        linarith
      have h5 : r ≤ (4 * cI + 1) * ‖half l‖ := (pow_le_pow_iff_left₀ hr.le (by positivity) two_ne_zero).1 h3
      rw [div_le_iff₀ (by positivity)]
      linarith
    · exact absurd (ha_zero v hv) hav
  ·
    intro y
    obtain ⟨hd', hz'⟩ := GlobalTheory.T.heckeIdealEuclideanLattice_isZLattice K I φ hφ ⊤ (by simp)
    obtain ⟨C, b, hC0, hb, hC⟩ := gauss_dil_bound n y
    set BF : ℝ := ∑ c : 𝓞 K ⧸ M, ‖F (Quotient.out c)‖ with hBF
    have hFc : ∀ α : 𝓞 K, F α = F (Quotient.out (Ideal.Quotient.mk M α)) := by
      intro α
      have hm : α - Quotient.out (Ideal.Quotient.mk M α) ∈ M := by
        rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out]
      have := hF (Quotient.out (Ideal.Quotient.mk M α)) _ hm
      rw [add_sub_cancel] at this
      exact this
    have hFB : ∀ α : 𝓞 K, ‖F α‖ ≤ BF := by
      intro α
      rw [hFc α]
      exact Finset.single_le_sum (f := fun c => ‖F (Quotient.out c)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ _)
    have hemb : ∀ α : 𝓞 K, emb φ (α : K) = WithLp.ofLp (embA φ α) := fun α => rfl
    have hsum : Summable (fun α : 𝓞 K => F α * gauss n (dil y (emb φ (α : K)))) := by
      have hT : Summable (fun x : lat φ ⊤ => BF * (C * Real.exp (-b * ‖(x : EuclideanSpace ℂ I)‖ ^ 2))) :=
        ((GlobalTheory.summable_lattice_exp_neg_mul_norm_sq (lat φ ⊤) hb).mul_left C).mul_left BF
      have hi : Function.Injective (fun α : 𝓞 K => (⟨embA φ α, mem_lat.2 ⟨α, Submodule.mem_top, rfl⟩⟩ : lat φ ⊤)) :=
        fun x x' h => hinj (congrArg Subtype.val h)
      refine Summable.of_norm_bounded (hT.comp_injective hi) (fun α => ?_)
      simp only [Function.comp_apply, norm_mul]
      exact mul_le_mul (hFB α) (hC (embA φ α)) (norm_nonneg _) (by positivity)

    let e : M ≃ L := Equiv.ofBijective (fun μ => (⟨embA φ μ, mem_lat.2 ⟨μ, μ.2, rfl⟩⟩ : L))
      ⟨fun x x' h => Subtype.ext (hinj (congrArg Subtype.val h)), fun x => by
        obtain ⟨μ, hμ, h⟩ := mem_lat.1 x.2
        exact ⟨⟨μ, hμ⟩, Subtype.ext h⟩⟩
    have hcoset : ∀ c : 𝓞 K ⧸ M, ∑' μ : M, F (Quotient.out c + μ) * gauss n (dil y (emb φ ((Quotient.out c + μ : 𝓞 K) : K))) =
        F (Quotient.out c) * (cov⁻¹ * ((Real.exp (-∑ i, y i) : ℂ) * kappa n) *
          ∑' l : D, Complex.exp (2 * Real.pi * Complex.I * ((⟪(l : EuclideanSpace ℂ I), u c⟫ : ℝ) : ℂ)) *
            gauss n (dil (-y) (half l))) := by
      intro c
      have h1 : ∀ μ : M, F (Quotient.out c + μ) * gauss n (dil y (emb φ ((Quotient.out c + μ : 𝓞 K) : K))) =
          F (Quotient.out c) * gauss n (dil y (WithLp.ofLp (((e μ : L) : EuclideanSpace ℂ I) + u c))) := by
        intro μ
        rw [hF _ _ μ.2]
        have hx : emb φ ((Quotient.out c + μ : 𝓞 K) : K) = WithLp.ofLp (((e μ : L) : EuclideanSpace ℂ I) + u c) := by
          funext i
          show φ i ((Quotient.out c + μ : 𝓞 K) : K) = (embA φ μ + embA φ (Quotient.out c)) i
          rw [PiLp.add_apply, embA_apply, embA_apply]
          push_cast
          rw [map_add, add_comm]
        rw [hx]
      rw [tsum_congr h1, tsum_mul_left,
        e.tsum_eq (fun x : L => gauss n (dil y (WithLp.ofLp ((x : EuclideanSpace ℂ I) + u c)))),
        (poisson_coset L n y (u c)).2]
    have hLHS := GlobalTheory.T.tsum_ring_eq_sum_ideal_cosets_tsum (𝓞 K) M _ hsum
    unfold GlobalTheory.HeckeTheta.theta
    rw [hLHS, Finset.sum_congr rfl (fun c _ => hcoset c)]

    have hsupp : Function.support (fun v : I → ℂ => a v * gauss n (dil (-y) v)) ⊆ Set.range half := by
      intro v hv
      by_contra h
      exact hv (by simp [ha_zero v h])
    rw [← hhalf.tsum_eq hsupp]
    simp only [ha_half, hA]
    have hsc : ∀ c ∈ (Finset.univ : Finset (𝓞 K ⧸ M)), Summable (fun l : D => cov⁻¹ * (F (Quotient.out c) *
        Complex.exp (2 * Real.pi * Complex.I * ((⟪(l : EuclideanSpace ℂ I), u c⟫ : ℝ) : ℂ))) * gauss n (dil (-y) (half l))) := by
      intro c _
      refine Summable.of_norm_bounded (((poisson_coset L n y (u c)).1).mul_left (‖cov⁻¹‖ * ‖F (Quotient.out c)‖)) (fun l => ?_)
      rw [norm_mul, norm_mul, norm_mul, GlobalTheory.norm_cexp_two_pi_I, mul_one]
    have hre : ∀ l : D, cov⁻¹ * (∑ c : 𝓞 K ⧸ M, F (Quotient.out c) *
        Complex.exp (2 * Real.pi * Complex.I * ((⟪(l : EuclideanSpace ℂ I), u c⟫ : ℝ) : ℂ))) * gauss n (dil (-y) (half l)) =
        ∑ c : 𝓞 K ⧸ M, cov⁻¹ * (F (Quotient.out c) *
        Complex.exp (2 * Real.pi * Complex.I * ((⟪(l : EuclideanSpace ℂ I), u c⟫ : ℝ) : ℂ))) * gauss n (dil (-y) (half l)) := by
      intro l
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [tsum_congr hre, Summable.tsum_finsetSum hsc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hre2 : ∀ l : D, cov⁻¹ * (F (Quotient.out c) *
        Complex.exp (2 * Real.pi * Complex.I * ((⟪(l : EuclideanSpace ℂ I), u c⟫ : ℝ) : ℂ))) * gauss n (dil (-y) (half l)) =
        (cov⁻¹ * F (Quotient.out c)) * (Complex.exp (2 * Real.pi * Complex.I * ((⟪(l : EuclideanSpace ℂ I), u c⟫ : ℝ) : ℂ)) *
          gauss n (dil (-y) (half l))) := fun l => by ring
    rw [tsum_congr hre2, tsum_mul_left]
    ring
end GlobalTheory.HeckePoisson
