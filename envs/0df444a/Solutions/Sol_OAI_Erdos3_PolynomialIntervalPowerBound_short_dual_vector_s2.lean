-- Prove2me | solution 1 for OAI.Erdos3.PolynomialIntervalPowerBound.short_dual_vector_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T11:24:43.982834+00:00
-- url     : https://prove2.me/submissions/2d9a04b4-cfd8-4937-a5f0-8a5d6e5c15e1

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B100
import Definitions.Def_OAIE3v2B137

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.WeightedFourierExtraction
namespace OAI

section

namespace Erdos3

theorem summable_weighted_unit_coefficients {ι : Type*} (w : ι → ℝ) (c : ι → ℂ)
    (hw : Summable w) (hwpos : ∀ i, 0 ≤ w i) (hc : ∀ i, ‖c i‖ ≤ 1) :
    Summable (fun i => (w i : ℂ) * c i) := by
  apply hw.of_norm_bounded
  intro i
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hwpos i)]
  exact mul_le_of_le_one_right (hwpos i) (hc i)

theorem exists_large_allowed_coefficient {ι : Type*} (w : ι → ℝ) (c : ι → ℂ)
    (allowed : ι → Prop) [DecidablePred allowed] (z : ι) {A δ τ : ℝ}
    (hw : Summable w) (hwpos : ∀ i, 0 ≤ w i) (hwz : w z = 1) (hcz : c z = 1)
    (hc : ∀ i, ‖c i‖ ≤ 1) (hδ : 0 ≤ δ) (hA : ∑' i, w i ≤ A)
    (htail : (∑' i, if allowed i then 0 else w i) ≤ τ)
    (hsmall : (∑' i, (w i : ℂ) * c i).re < 1 - δ * A - τ) :
    ∃ i, i ≠ z ∧ allowed i ∧ δ < ‖c i‖ := by
  classical
  by_contra! hnone
  let tail : ι → ℝ := fun i => if allowed i then 0 else w i
  have ht : Summable tail := by
    convert! hw.indicator {i | ¬ allowed i} using 1
    funext i
    simp only [tail, Set.indicator_apply, Set.mem_ofPred_eq, ite_not]
  have hsum := summable_weighted_unit_coefficients w c hw hwpos hc
  have hr : Summable (fun i => ((w i : ℂ) * c i).re) :=
    (Complex.hasSum_re hsum.hasSum).summable
  let f : ι → ℝ := fun i => ((w i : ℂ) * c i).re + δ * w i + tail i
  have hf : Summable f := (hr.add (hw.mul_left δ)).add ht
  have hnonneg (i : ι) : 0 ≤ f i := by
    have hre : -‖c i‖ ≤ (c i).re := (abs_le.mp (Complex.abs_re_le_norm (c i))).1
    by_cases hi : i = z
    · subst i
      simp only [f, hwz, hcz, Complex.ofReal_one, mul_one, Complex.one_re]
      have htz : 0 ≤ tail z := by simp only [tail]; split_ifs <;> positivity
      linarith
    · by_cases ha : allowed i
      · have hci := hnone i hi ha
        have he : 0 ≤ (c i).re + δ := by linarith
        have hm := mul_nonneg (hwpos i) he
        simpa only [f, tail, ha, ite_true, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero, add_zero] using (by nlinarith : 0 ≤ w i * (c i).re + δ * w i)
      · have he : 0 ≤ (c i).re + 1 := by linarith [hc i]
        have hm := mul_nonneg (hwpos i) he
        have hd := mul_nonneg hδ (hwpos i)
        simp only [f, tail, ha, ite_false, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero]
        nlinarith
  have hz : 1 ≤ f z := by
    have htz : 0 ≤ tail z := by simp only [tail]; split_ifs <;> positivity
    simp only [f, hwz, hcz, Complex.ofReal_one, mul_one, Complex.one_re]
    linarith
  have hone : 1 ≤ ∑' i, f i := hz.trans (hf.le_tsum z (fun i _ => hnonneg i))
  rw [show (∑' i, f i) = (∑' i, ((w i : ℂ) * c i).re) + δ * (∑' i, w i) + ∑' i, tail i by
    simp only [f, Summable.tsum_add (hr.add (hw.mul_left δ)) ht,
      Summable.tsum_add hr (hw.mul_left δ), tsum_mul_left]] at hone
  rw [← Complex.re_tsum hsum] at hone
  have hweight := mul_le_mul_of_nonneg_left hA hδ
  change (∑' i, tail i) ≤ τ at htail
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeHyperplaneBasis
namespace OAI

section

namespace Erdos3

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem latticeGaussianMass_pos (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    {t : ℝ} (ht : 0 < t) (x : E) : 0 < latticeGaussianMass Λ t x := by
  have h := (lattice_gaussian_summable Λ ht x).le_tsum (0 : Λ) (fun _ _ => (Real.exp_pos _).le)
  exact (Real.exp_pos _).trans_le h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.MonomialCharacterMean
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem continuous_euclideanCharacter (ξ : E) : Continuous (euclideanCharacter ξ) := by
  unfold euclideanCharacter CircleFourier.character
  fun_prop

theorem euclideanCharacter_eq_exp (ξ x : E) :
    euclideanCharacter ξ x = Complex.exp (2 * Real.pi * Complex.I * (inner ℝ ξ x : ℝ)) := by
  simpa only [euclideanCharacter, CircleFourier.character, fourier_apply,
    one_zsmul, Int.cast_one, Complex.ofReal_one, mul_one, div_one] using
    (fourier_coe_apply (T := (1 : ℝ)) (n := 1) (x := inner ℝ ξ x))

theorem euclideanCharacter_on_lattice (Λ : Submodule ℤ E) (ξ : E)
    (hξ : ξ ∈ euclideanDualLattice Λ) (m : Λ) : euclideanCharacter ξ m = 1 := by
  obtain ⟨n, hn⟩ := (mem_euclideanDualLattice Λ ξ).mp hξ m m.property
  rw [euclideanCharacter, hn]
  have hnzero : (((n : ℝ) : CircleFourier.Circle)) = 0 := by
    exact (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mpr ⟨n, by simp⟩
  rw [hnzero, CircleFourier.character_zero]

theorem euclideanCharacter_sub_lattice (Λ : Submodule ℤ E) (ξ : E)
    (hξ : ξ ∈ euclideanDualLattice Λ) (x : E) (m : Λ) :
    euclideanCharacter ξ (x - m) = euclideanCharacter ξ x := by
  rw [sub_eq_add_neg, euclideanCharacter_add, euclideanCharacter_neg,
    euclideanCharacter_on_lattice Λ ξ hξ m, star_one, mul_one]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Real
open scoped FourierTransform

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem gaussian_character_integrable {t : ℝ} (ht : 0 < t) (ξ : E) :
    Integrable (fun x : E => euclideanCharacter ξ x *
      (Real.exp (-Real.pi * t * ‖x‖ ^ 2) : ℂ)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (show 0 < ((Real.pi * t : ℝ) : ℂ).re by simpa using mul_pos Real.pi_pos ht)
    (2 * Real.pi * Complex.I) ξ
  convert h using 1
  ext x
  rw [euclideanCharacter_eq_exp, Complex.exp_add]
  push_cast
  rw [mul_comm]
  simp only [neg_mul]

theorem gaussian_fourier_prefactor {t : ℝ} (ht : 0 < t) (d : ℕ) :
    ((Real.pi : ℂ) / ((Real.pi * t : ℝ) : ℂ)) ^ ((d : ℂ) / 2) =
      (((Real.sqrt t) ^ d)⁻¹ : ℝ) := by
  have he : (Real.pi : ℂ) / ((Real.pi * t : ℝ) : ℂ) = ((t⁻¹ : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [he, ← Complex.ofReal_natCast, ← Complex.ofReal_ofNat, ← Complex.ofReal_div,
    ← Complex.ofReal_cpow (inv_nonneg.mpr ht.le), Real.inv_rpow ht.le]
  congr 2
  rw [show (d : ℝ) / 2 = (1 / 2 : ℝ) * d by ring,
    Real.rpow_mul_natCast ht.le, Real.sqrt_eq_rpow]

theorem gaussian_fourier_integral {t : ℝ} (ht : 0 < t) (ξ : E) :
    (∫ x : E, euclideanCharacter (-ξ) x * (Real.exp (-Real.pi * t * ‖x‖ ^ 2) : ℂ)) =
      ((((Real.sqrt t) ^ Module.finrank ℝ E)⁻¹ *
        Real.exp (-Real.pi / t * ‖ξ‖ ^ 2) : ℝ) : ℂ) := by
  have h := fourier_gaussian_innerProductSpace
    (show 0 < ((Real.pi * t : ℝ) : ℂ).re by simpa using mul_pos Real.pi_pos ht) ξ
  rw [gaussian_fourier_prefactor ht] at h
  calc
    _ = 𝓕 (fun v : E => Complex.exp (-((Real.pi * t : ℝ) : ℂ) * ‖v‖ ^ 2)) ξ := by
      simp only [fourier_eq', smul_eq_mul, euclideanCharacter_eq_exp, inner_neg_left]
      congr 1
      ext x
      rw [real_inner_comm x ξ]
      push_cast
      congr 2 <;> ring
    _ = _ := h
    _ = _ := by
      push_cast
      congr 1
      congr 1
      field_simp

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem monomialCharacterMean_norm_le_one (k : ℕ) (α : E) (N : ℕ) (ξ : E) :
    ‖monomialCharacterMean k α N ξ‖ ≤ 1 := by
  have hne : (Finset.Icc (-(N : ℤ)) (N : ℤ)).Nonempty := ⟨0, by simp⟩
  have hc : (0 : ℝ) < (Finset.Icc (-(N : ℤ)) (N : ℤ)).card := by
    exact_mod_cast hne.card_pos
  rw [monomialCharacterMean, norm_div, Complex.norm_natCast]
  apply (div_le_one hc).mpr
  calc
    _ ≤ ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖euclideanCharacter ξ ((n : ℝ) ^ k • α)‖ :=
      norm_sum_le _ _
    _ = _ := by simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeDualCoordinates
namespace OAI

section

namespace Erdos3

open Module

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

theorem latticeDualPoint_inner_basis (b : Basis ι ℤ Λ) (n : ι → ℤ) (i : ι) :
    inner ℝ (latticeDualPoint Λ b n) (b.ofZLatticeBasis ℝ Λ i) = (n i : ℝ) := by
  have h := congrFun ((latticeDualBasis Λ b).equivFun.apply_symm_apply (fun j => (n j : ℝ))) i
  simpa only [Basis.equivFun_apply, latticeDualBasis, latticeDualPoint,
    LinearMap.BilinForm.dualBasis_repr_apply, innerₗ_apply_apply] using h

theorem latticeDualPoint_inner_coordinates (b : Basis ι ℤ Λ) (n : ι → ℤ) (x : ι → ℝ) :
    inner ℝ (latticeDualPoint Λ b n) ((b.ofZLatticeBasis ℝ Λ).equivFun.symm x) =
      ∑ i, (n i : ℝ) * x i := by
  rw [Basis.equivFun_symm_apply, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_smul_right, latticeDualPoint_inner_basis, mul_comm]

theorem latticeDualPoint_character (b : Basis ι ℤ Λ) (n : ι → ℤ) (x : ι → ℝ) :
    euclideanCharacter (latticeDualPoint Λ b n) ((b.ofZLatticeBasis ℝ Λ).equivFun.symm x) =
      UnitAddTorus.mFourier n (fun i => (x i : UnitAddCircle)) := by
  rw [euclideanCharacter_eq_exp, latticeDualPoint_inner_coordinates]
  simp only [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum,
    UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_coe_apply]
  apply Finset.prod_congr rfl
  intro i _
  push_cast
  congr 1
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformIntegralSeries
namespace OAI

section

namespace Erdos3

open MeasureTheory Filter

theorem integral_tsum_of_uniform_domination {ι X V : Type*} [Countable ι]
    [MeasurableSpace X] [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (μ : Measure X) [IsFiniteMeasure μ] (f : ι → X → V) (C : ι → ℝ)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) (hC : Summable C)
    (hbound : ∀ i, ∀ᵐ x ∂μ, ‖f i x‖ ≤ C i) :
    (∫ x, ∑' i, f i x ∂μ) = ∑' i, ∫ x, f i x ∂μ := by
  symm
  apply HasSum.tsum_eq
  apply hasSum_integral_of_dominated_convergence (fun i _ => C i) hf hbound
  · exact Eventually.of_forall (fun _ => hC)
  · exact integrable_const _
  · filter_upwards [ae_all_iff.mpr hbound] with x hx
    exact (hC.of_norm_bounded hx).hasSum

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeGaussianCoefficient
namespace OAI

section

namespace Erdos3

open MeasureTheory Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem lattice_periodization_integral (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (μ : Measure E) [μ.IsAddHaarMeasure]
    (S : Set E) (hS : MeasurableSet S) (hfinite : μ S < ⊤)
    (hfund : IsAddFundamentalDomain Λ S μ) (f : E → ℂ)
    (hf : Continuous f) (hint : Integrable f μ) (C : Λ → ℝ) (hC : Summable C)
    (hbound : ∀ m : Λ, ∀ x ∈ S, ‖f (x - m)‖ ≤ C m) :
    (∫ x in S, ∑' m : Λ, f (x - m) ∂μ) = ∫ x, f x ∂μ := by
  let : VAddInvariantMeasure Λ E μ := inferInstanceAs (VAddInvariantMeasure Λ.toAddSubgroup E μ)
  let : IsFiniteMeasure (μ.restrict S) := ⟨by simpa using hfinite⟩
  rw [integral_tsum_of_uniform_domination (μ.restrict S)
    (fun (m : Λ) x => f (x - m)) C
    (fun m => (hf.comp (continuous_id.sub continuous_const)).aestronglyMeasurable) hC
    (fun m => ?_)]
  · have h := hfund.integral_eq_tsum' f hint
    simpa only [Submodule.vadd_def, vadd_eq_add, Submodule.coe_neg, sub_eq_add_neg, add_comm] using h.symm
  · filter_upwards [ae_restrict_mem hS] with x hx
    exact hbound m x hx

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem latticeGaussian_integral_character (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (S : Set E) (hS : MeasurableSet S) (hbounded : Bornology.IsBounded S)
    (hfund : IsAddFundamentalDomain Λ S volume) {t : ℝ} (ht : 0 < t)
    (ξ : E) (hξ : ξ ∈ euclideanDualLattice Λ) :
    (∫ x in S, euclideanCharacter (-ξ) x * (latticeGaussianMass Λ t x : ℂ)) =
      ((((Real.sqrt t) ^ Module.finrank ℝ E)⁻¹ *
        Real.exp (-Real.pi / t * ‖ξ‖ ^ 2) : ℝ) : ℂ) := by
  obtain ⟨R, hR, hball⟩ := hbounded.exists_pos_norm_le
  let f : E → ℂ := fun x => euclideanCharacter (-ξ) x *
    (Real.exp (-Real.pi * t * ‖x‖ ^ 2) : ℂ)
  let C : Λ → ℝ := fun m => Real.exp (Real.pi * t * R ^ 2) *
    Real.exp (-Real.pi * (t / 2) * ‖(0 : E) - m‖ ^ 2)
  have hC : Summable C := (lattice_gaussian_summable Λ (half_pos ht) 0).mul_left _
  have hf : Continuous f := (continuous_euclideanCharacter (-ξ)).mul (by fun_prop)
  have hbound (m : Λ) (x : E) (hx : x ∈ S) : ‖f (x - m)‖ ≤ C m := by
    simp only [f, C, norm_mul, norm_euclideanCharacter, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), zero_sub, norm_neg]
    exact gaussian_translate_bound t R ht.le hR.le x m (hball x hx)
  have hperiod (x : E) : (∑' m : Λ, f (x - m)) =
      euclideanCharacter (-ξ) x * (latticeGaussianMass Λ t x : ℂ) := by
    simp only [f, euclideanCharacter_sub_lattice Λ (-ξ) ((euclideanDualLattice Λ).neg_mem hξ)]
    rw [tsum_mul_left, ← Complex.ofReal_tsum]
    rfl
  have h := lattice_periodization_integral Λ volume S hS hbounded.measure_lt_top hfund
    f hf (gaussian_character_integrable ht (-ξ)) C hC hbound
  simp only [hperiod] at h
  exact h.trans (gaussian_fourier_integral ht ξ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeSheetHaar
namespace OAI

section

namespace Erdos3

open MeasureTheory Module

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] in
theorem basis_equivFun_measurePreserving (b : Basis ι ℝ E) :
    MeasurePreserving b.equivFunL b.addHaar volume := by
  classical
  refine ⟨b.equivFunL.continuous.measurable, ?_⟩
  rw [Basis.map_addHaar]
  have hb : b.map b.equivFun = Pi.basisFun ℝ ι := by
    ext i j
    simp [Basis.equivFun_self, Pi.basisFun_apply, Pi.single_apply, eq_comm]
  change (b.map b.equivFun).addHaar = volume
  rw [hb, Basis.addHaar_def, Basis.parallelepiped_basisFun,
    addHaarMeasure_eq_volume_pi]

theorem volume_eq_covolume_smul_basis_addHaar (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (b : Basis ι ℤ Λ) :
    (volume : Measure E) = ENNReal.ofReal (ZLattice.covolume Λ) •
      (b.ofZLatticeBasis ℝ Λ).addHaar := by
  let bR := b.ofZLatticeBasis ℝ Λ
  have hcov : ZLattice.covolume Λ = volume.real (parallelepiped bR) := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain Λ volume
      (ZLattice.isAddFundamentalDomain b volume)]
    exact measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped bR volume)
  have h := Measure.addHaarMeasure_unique (volume : Measure E) bR.parallelepiped
  have hfinite : volume (parallelepiped bR) ≠ ⊤ := by
    simpa only [Basis.coe_parallelepiped] using bR.parallelepiped.isCompact.measure_ne_top (μ := volume)
  rw [Basis.addHaar_def]
  rw [hcov, measureReal_def, ENNReal.ofReal_toReal hfinite]
  exact h

theorem latticeBasis_integral_cube (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (b : Basis ι ℤ Λ) (f : E → ℂ) :
    (ZLattice.covolume Λ : ℂ) *
        (∫ x : ι → ℝ in Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) 1),
          f ((b.ofZLatticeBasis ℝ Λ).equivFun.symm x)) =
      ∫ x in ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ Λ), f x := by
  let bR := b.ofZLatticeBasis ℝ Λ
  have hp := basis_equivFun_measurePreserving bR
  have hpre : bR.equivFunL ⁻¹' Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) 1) =
      ZSpan.fundamentalDomain bR := by
    ext x
    simp [ZSpan.fundamentalDomain]
  have hi := hp.setIntegral_preimage_emb bR.equivFunL.toHomeomorph.measurableEmbedding
    (f ∘ bR.equivFun.symm) (Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) 1))
  simp only [hpre, Function.comp_apply] at hi
  have hi' : (∫ x in ZSpan.fundamentalDomain bR, f x ∂bR.addHaar) =
      ∫ x : ι → ℝ in Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) 1), f (bR.equivFun.symm x) := by
    convert hi using 1
    congr 1
    funext x
    exact congrArg f (bR.equivFun.symm_apply_apply x).symm
  conv_rhs => rw [volume_eq_covolume_smul_basis_addHaar Λ b, Measure.restrict_smul,
    integral_smul_measure, ENNReal.toReal_ofReal (ZLattice.covolume_pos Λ volume).le]
  change _ = (ZLattice.covolume Λ : ℂ) * _
  rw [hi']

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem latticeGaussianNormalizer_pos (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] {t : ℝ} (ht : 0 < t) : 0 < latticeGaussianNormalizer Λ t :=
  mul_pos (pow_pos (Real.sqrt_pos.mpr ht) _) (ZLattice.covolume_pos Λ MeasureTheory.volume)

theorem normalizedLatticeGaussian_pos (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] {t : ℝ} (ht : 0 < t) (x : E) :
    0 < normalizedLatticeGaussian Λ t x :=
  mul_pos (latticeGaussianNormalizer_pos Λ ht) (latticeGaussianMass_pos Λ ht x)

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
theorem latticeGaussianMass_antitone (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (x : E) :
    latticeGaussianMass Λ t x ≤ latticeGaussianMass Λ s x := by
  apply (lattice_gaussian_summable Λ (hs.trans_le hst) x).tsum_le_tsum
    _ (lattice_gaussian_summable Λ hs x)
  intro m
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonpos_left hst (neg_nonpos.mpr Real.pi_pos.le)) (sq_nonneg _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.LatticeTorusFourierCoefficient
namespace OAI

section

namespace Erdos3

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

theorem latticeGaussianTorus_coe (b : Module.Basis ι ℤ Λ) {t : ℝ} (ht : 0 < t)
    (x : ι → ℝ) :
    latticeGaussianTorus Λ b ht (fun i => (x i : UnitAddCircle)) =
      (latticeGaussianMass Λ t ((b.ofZLatticeBasis ℝ Λ).equivFun.symm x) : ℂ) :=
  integerPeriodicTorusLift_coe (fun y =>
    (latticeGaussianMass Λ t ((b.ofZLatticeBasis ℝ Λ).equivFun.symm y) : ℂ))
    (fun y n => congrArg (fun z : ℝ => (z : ℂ)) (latticeGaussian_integer_periodic Λ b t y n)) x

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

theorem latticeGaussianTorus_coefficient (b : Basis ι ℤ Λ) {t : ℝ} (ht : 0 < t) (n : ι → ℤ) :
    (ZLattice.covolume Λ : ℂ) * UnitAddTorus.mFourierCoeff (latticeGaussianTorus Λ b ht) n =
      ((((Real.sqrt t) ^ Module.finrank ℝ E)⁻¹ *
        Real.exp (-Real.pi / t * ‖latticeDualPoint Λ b n‖ ^ 2) : ℝ) : ℂ) := by
  classical
  let bR := b.ofZLatticeBasis ℝ Λ
  let f : E → ℂ := fun x => euclideanCharacter (-latticeDualPoint Λ b n) x *
    (latticeGaussianMass Λ t x : ℂ)
  have hsets : Set.pi Set.univ (fun _ : ι => Set.Ioc (0 : ℝ) 1) =ᵐ[volume]
      Set.pi Set.univ (fun _ : ι => Set.Ico (0 : ℝ) 1) :=
    (Measure.ae_eq_set_pi (μ := fun _ : ι => (volume : Measure ℝ))
      (fun _ _ => Ico_ae_eq_Ioc)).symm
  have hcoeff : UnitAddTorus.mFourierCoeff (latticeGaussianTorus Λ b ht) n =
      ∫ x : ι → ℝ in Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) 1), f (bR.equivFun.symm x) := by
    rw [UnitAddTorus.mFourierCoeff_eq_integral _ _ (fun _ => 0)]
    simp only [zero_add, smul_eq_mul]
    have he : {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1} =
        Set.pi Set.univ (fun _ : ι => Set.Ioc (0 : ℝ) 1) := by ext; simp
    rw [he, setIntegral_congr_set hsets]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [latticeGaussianTorus_coe, ← latticeDualPoint_character Λ b (-n) x, latticeDualPoint_neg]
  rw [hcoeff, latticeBasis_integral_cube]
  exact latticeGaussian_integral_character Λ (ZSpan.fundamentalDomain bR)
    (ZSpan.fundamentalDomain_measurableSet bR) (ZSpan.fundamentalDomain_isBounded bR)
    (ZLattice.isAddFundamentalDomain b volume) ht _ (latticeDualPoint_mem Λ b n)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeGaussianPoisson
namespace OAI

section

namespace Erdos3

open Module

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

theorem latticeGaussianTorus_coefficient_eq (b : Basis ι ℤ Λ) {t : ℝ} (ht : 0 < t) (n : ι → ℤ) :
    UnitAddTorus.mFourierCoeff (latticeGaussianTorus Λ b ht) n =
      ((latticeGaussianNormalizer Λ t)⁻¹ *
        Real.exp (-Real.pi / t * ‖latticeDualPoint Λ b n‖ ^ 2) : ℝ) := by
  have hc : (ZLattice.covolume Λ : ℂ) ≠ 0 := by
    exact_mod_cast (ZLattice.covolume_pos Λ MeasureTheory.volume).ne'
  have hs : (((Real.sqrt t) ^ Module.finrank ℝ E : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero (Module.finrank ℝ E) (Real.sqrt_pos.mpr ht).ne'
  apply mul_left_cancel₀ hc
  rw [latticeGaussianTorus_coefficient, latticeGaussianNormalizer]
  push_cast
  field_simp

theorem summable_latticeGaussianTorus_coefficients (b : Basis ι ℤ Λ) {t : ℝ} (ht : 0 < t) :
    Summable (UnitAddTorus.mFourierCoeff (latticeGaussianTorus Λ b ht)) := by
  have hs := (lattice_gaussian_summable (euclideanDualLattice Λ) (inv_pos.mpr ht) 0).comp_injective
    (latticeDualEquiv Λ b).injective
  have hw : Summable (fun n : ι → ℤ => Real.exp (-Real.pi / t * ‖latticeDualPoint Λ b n‖ ^ 2)) := by
    simpa only [Function.comp_def, zero_sub, norm_neg, latticeDualEquiv_coe, div_eq_mul_inv] using hs
  change Summable (fun n : ι → ℤ => UnitAddTorus.mFourierCoeff (latticeGaussianTorus Λ b ht) n)
  simp_rw [latticeGaussianTorus_coefficient_eq Λ b ht]
  exact Complex.summable_ofReal.mpr (hw.mul_left _)

theorem normalizedLatticeGaussian_poisson_basis (b : Basis ι ℤ Λ) {t : ℝ} (ht : 0 < t) (x : E) :
    (normalizedLatticeGaussian Λ t x : ℂ) =
      ∑' ξ : euclideanDualLattice Λ,
        (Real.exp (-Real.pi / t * ‖(ξ : E)‖ ^ 2) : ℂ) * euclideanCharacter (ξ : E) x := by
  let bR := b.ofZLatticeBasis ℝ Λ
  have hseries := UnitAddTorus.hasSum_mFourier_series_apply_of_summable
    (summable_latticeGaussianTorus_coefficients Λ b ht)
    (fun i => (bR.equivFun x i : UnitAddCircle))
  have hn : (latticeGaussianNormalizer Λ t : ℂ) ≠ 0 := by
    exact_mod_cast (latticeGaussianNormalizer_pos Λ ht).ne'
  have hs : HasSum (fun n : ι → ℤ =>
      (Real.exp (-Real.pi / t * ‖latticeDualPoint Λ b n‖ ^ 2) : ℂ) *
        euclideanCharacter (latticeDualPoint Λ b n) x)
      (normalizedLatticeGaussian Λ t x : ℂ) := by
    convert! hseries.mul_left (latticeGaussianNormalizer Λ t : ℂ) using 1
    · funext n
      simp only [smul_eq_mul]
      rw [latticeGaussianTorus_coefficient_eq Λ b ht,
        ← latticeDualPoint_character Λ b n (bR.equivFun x)]
      change _ = (latticeGaussianNormalizer Λ t : ℂ) *
        (((latticeGaussianNormalizer Λ t)⁻¹ * Real.exp
          (-Real.pi / t * ‖latticeDualPoint Λ b n‖ ^ 2) : ℝ) *
          euclideanCharacter (latticeDualPoint Λ b n) (bR.equivFun.symm (bR.equivFun x)))
      rw [LinearEquiv.symm_apply_apply]
      push_cast
      field_simp
    · rw [latticeGaussianTorus_coe]
      change _ = (latticeGaussianNormalizer Λ t : ℂ) *
        (latticeGaussianMass Λ t (bR.equivFun.symm (bR.equivFun x)) : ℂ)
      rw [LinearEquiv.symm_apply_apply]
      simp only [normalizedLatticeGaussian, Complex.ofReal_mul]
  rw [← hs.tsum_eq]
  simpa only [latticeDualEquiv_coe] using (latticeDualEquiv Λ b).tsum_eq
    (fun ξ : euclideanDualLattice Λ =>
      (Real.exp (-Real.pi / t * ‖(ξ : E)‖ ^ 2) : ℂ) * euclideanCharacter (ξ : E) x)

omit [Fintype ι] in
theorem normalizedLatticeGaussian_poisson {t : ℝ} (ht : 0 < t) (x : E) :
    (normalizedLatticeGaussian Λ t x : ℂ) =
      ∑' ξ : euclideanDualLattice Λ,
        (Real.exp (-Real.pi / t * ‖(ξ : E)‖ ^ 2) : ℂ) * euclideanCharacter (ξ : E) x :=
  normalizedLatticeGaussian_poisson_basis Λ (Module.Free.chooseBasis ℤ Λ) ht x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.LatticeGaussianMeanFourier
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

omit [MeasurableSpace E] [BorelSpace E] in
theorem latticeGaussian_fourier_summable_norm {t : ℝ} (ht : 0 < t) (x : E) :
    Summable (fun ξ : euclideanDualLattice Λ =>
      ‖(Real.exp (-Real.pi / t * ‖(ξ : E)‖ ^ 2) : ℂ) * euclideanCharacter (ξ : E) x‖) := by
  simpa only [norm_mul, norm_euclideanCharacter, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), zero_sub, norm_neg, div_eq_mul_inv] using
    lattice_gaussian_summable (euclideanDualLattice Λ) (inv_pos.mpr ht) 0

omit [MeasurableSpace E] [BorelSpace E] in
theorem latticeGaussian_fourier_summable {t : ℝ} (ht : 0 < t) (x : E) :
    Summable (fun ξ : euclideanDualLattice Λ =>
      (Real.exp (-Real.pi / t * ‖(ξ : E)‖ ^ 2) : ℂ) * euclideanCharacter (ξ : E) x) :=
  (latticeGaussian_fourier_summable_norm Λ ht x).of_norm

theorem normalizedLatticeGaussian_zero_eq_dual {t : ℝ} (ht : 0 < t) :
    normalizedLatticeGaussian Λ t 0 = latticeGaussianMass (euclideanDualLattice Λ) t⁻¹ 0 := by
  apply Complex.ofReal_injective
  rw [normalizedLatticeGaussian_poisson Λ ht]
  simp only [euclideanCharacter_zero, mul_one, latticeGaussianMass, Complex.ofReal_tsum,
    zero_sub, norm_neg, div_eq_mul_inv]

theorem normalizedLatticeGaussian_origin_mono {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    normalizedLatticeGaussian Λ s 0 ≤ normalizedLatticeGaussian Λ t 0 := by
  rw [normalizedLatticeGaussian_zero_eq_dual Λ hs,
    normalizedLatticeGaussian_zero_eq_dual Λ (hs.trans_le hst)]
  exact latticeGaussianMass_antitone (euclideanDualLattice Λ) (inv_pos.mpr (hs.trans_le hst))
    (inv_le_inv₀ (hs.trans_le hst) hs |>.mpr hst) 0

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem latticeGaussianMean_fourier (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {t : ℝ} (ht : 0 < t) (k : ℕ) (α : E) (N : ℕ) :
    (latticeGaussianMean Λ t k α N : ℂ) =
      ∑' ξ : euclideanDualLattice Λ,
        (Real.exp (-Real.pi / t * ‖(ξ : E)‖ ^ 2) : ℂ) * monomialCharacterMean k α N ξ := by
  unfold monomialCharacterMean
  simp only [← mul_div_assoc, Finset.mul_sum]
  rw [tsum_div_const]
  rw [Summable.tsum_finsetSum (s := Finset.Icc (-(N : ℤ)) (N : ℤ))
    (fun (n : ℤ) _ => latticeGaussian_fourier_summable Λ ht ((n : ℝ) ^ k • α))]
  simp only [← normalizedLatticeGaussian_poisson Λ ht]
  simp only [latticeGaussianMean, Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_natCast]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.GaussianLatticeDistance
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

theorem latticeGaussianMass_quarter_temperature {t : ℝ} (ht : 0 < t) :
    latticeGaussianMass Λ (t / 4) 0 ≤
      (2 : ℝ) ^ Module.finrank ℝ E * latticeGaussianMass Λ t 0 := by
  have hmono := normalizedLatticeGaussian_origin_mono Λ (show 0 < t / 4 by positivity)
    (show t / 4 ≤ t by linarith)
  have hsqrt : Real.sqrt (t / 4) = Real.sqrt t / 2 := by
    rw [Real.sqrt_div ht.le]
    norm_num
  have hn := latticeGaussianNormalizer_pos Λ ht
  have htwo : (0 : ℝ) < 2 ^ Module.finrank ℝ E := by positivity
  have hnorm : latticeGaussianNormalizer Λ (t / 4) =
      latticeGaussianNormalizer Λ t / (2 : ℝ) ^ Module.finrank ℝ E := by
    unfold latticeGaussianNormalizer
    rw [hsqrt, div_pow]
    ring
  change latticeGaussianNormalizer Λ (t / 4) * latticeGaussianMass Λ (t / 4) 0 ≤
    latticeGaussianNormalizer Λ t * latticeGaussianMass Λ t 0 at hmono
  rw [hnorm, div_mul_eq_mul_div] at hmono
  have h := (div_le_iff₀ htwo).mp hmono
  nlinarith

omit [MeasurableSpace E] [BorelSpace E] [IsZLattice ℝ Λ] in
theorem latticeGaussianTail_summable {t : ℝ} (ht : 0 < t) (R : ℝ) :
    Summable (fun m : Λ => if R < ‖(m : E)‖ then Real.exp (-Real.pi * t * ‖(m : E)‖ ^ 2) else 0) := by
  classical
  convert! (lattice_gaussian_summable Λ ht 0).indicator {m : Λ | R < ‖(m : E)‖} using 1
  funext m
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, zero_sub, norm_neg]

theorem latticeGaussianTail_bound {t R : ℝ} (ht : 0 < t) (hR : 0 ≤ R) :
    latticeGaussianTail Λ t R ≤ Real.exp (-Real.pi * t * R ^ 2 / 2) *
      (2 : ℝ) ^ Module.finrank ℝ E * latticeGaussianMass Λ t 0 := by
  classical
  have hpoint (m : Λ) :
      (if R < ‖(m : E)‖ then Real.exp (-Real.pi * t * ‖(m : E)‖ ^ 2) else 0) ≤
        Real.exp (-Real.pi * t * R ^ 2 / 2) * Real.exp (-Real.pi * (t / 4) * ‖(m : E)‖ ^ 2) := by
    split_ifs with hm
    · rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hsq : R ^ 2 ≤ ‖(m : E)‖ ^ 2 := pow_le_pow_left₀ hR hm.le 2
      nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le ht.le) (sub_nonneg.mpr hsq),
        mul_nonneg (mul_nonneg Real.pi_pos.le ht.le) (sq_nonneg ‖(m : E)‖)]
    · positivity
  have hs := (lattice_gaussian_summable Λ (show 0 < t / 4 by positivity) 0).mul_left
    (Real.exp (-Real.pi * t * R ^ 2 / 2))
  simp only [zero_sub, norm_neg] at hs
  have h := (latticeGaussianTail_summable Λ ht R).tsum_le_tsum hpoint hs
  rw [tsum_mul_left] at h
  have h' : latticeGaussianTail Λ t R ≤ Real.exp (-Real.pi * t * R ^ 2 / 2) *
      latticeGaussianMass Λ (t / 4) 0 := by
    simpa only [latticeGaussianTail, latticeGaussianMass, zero_sub, norm_neg] using h
  exact h'.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (latticeGaussianMass_quarter_temperature Λ ht) (Real.exp_pos _).le)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GaussianTailRadius
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

theorem normalizedLatticeGaussian_origin_ge_one {t : ℝ} (ht : 0 < t) :
    1 ≤ normalizedLatticeGaussian Λ t 0 := by
  rw [normalizedLatticeGaussian_zero_eq_dual Λ ht]
  have h := (lattice_gaussian_summable (euclideanDualLattice Λ) (inv_pos.mpr ht) 0).le_tsum
    (0 : euclideanDualLattice Λ) (fun _ _ => (Real.exp_pos _).le)
  simpa only [latticeGaussianMass, Submodule.coe_zero, sub_zero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
    mul_zero, Real.exp_zero] using h

theorem exists_short_dual_correlation {t R : ℝ} (ht : 0 < t) (hR : 0 ≤ R)
    (k : ℕ) (α : E) (N : ℕ)
    (htail : Real.exp (-Real.pi / t * R ^ 2 / 2) * (2 : ℝ) ^ Module.finrank ℝ E *
      normalizedLatticeGaussian Λ t 0 ≤ 1 / 4)
    (hsmall : latticeGaussianMean Λ t k α N < 1 / 2) :
    ∃ ξ : E, ξ ∈ euclideanDualLattice Λ ∧ ξ ≠ 0 ∧ ‖ξ‖ ≤ R ∧
      (8 * normalizedLatticeGaussian Λ t 0)⁻¹ < ‖monomialCharacterMean k α N ξ‖ := by
  classical
  let A := normalizedLatticeGaussian Λ t 0
  let w : euclideanDualLattice Λ → ℝ := fun ξ => Real.exp (-Real.pi / t * ‖(ξ : E)‖ ^ 2)
  let c : euclideanDualLattice Λ → ℂ := fun ξ => monomialCharacterMean k α N (ξ : E)
  have hA : 0 < A := normalizedLatticeGaussian_pos Λ ht 0
  have hw : Summable w := by
    simpa only [w, zero_sub, norm_neg, div_eq_mul_inv] using
      lattice_gaussian_summable (euclideanDualLattice Λ) (inv_pos.mpr ht) 0
  have hwA : (∑' ξ, w ξ) = A := by
    rw [show A = latticeGaussianMass (euclideanDualLattice Λ) t⁻¹ 0 from
      normalizedLatticeGaussian_zero_eq_dual Λ ht]
    simp only [w, latticeGaussianMass, zero_sub, norm_neg, div_eq_mul_inv]
  have htailsum : (∑' ξ : euclideanDualLattice Λ, if ‖(ξ : E)‖ ≤ R then 0 else w ξ) ≤ (1 / 4 : ℝ) := by
    have h := latticeGaussianTail_bound (euclideanDualLattice Λ) (inv_pos.mpr ht) hR
    rw [← normalizedLatticeGaussian_zero_eq_dual Λ ht] at h
    have he : (∑' ξ : euclideanDualLattice Λ, if ‖(ξ : E)‖ ≤ R then 0 else w ξ) =
        latticeGaussianTail (euclideanDualLattice Λ) t⁻¹ R := by
      apply tsum_congr
      intro ξ
      simp only [w, ← not_lt, ite_not, div_eq_mul_inv]
    rw [he]
    exact h.trans (by simpa only [div_eq_mul_inv] using htail)
  have hδA : (8 * A)⁻¹ * A = (1 / 8 : ℝ) := by field_simp
  have hmean : (∑' ξ, (w ξ : ℂ) * c ξ).re = latticeGaussianMean Λ t k α N := by
    have h := congrArg Complex.re (latticeGaussianMean_fourier Λ ht k α N)
    simpa only [Complex.ofReal_re, w, c] using h.symm
  obtain ⟨ξ, hξ, hξR, hlarge⟩ := exists_large_allowed_coefficient w c
    (fun ξ => ‖(ξ : E)‖ ≤ R) (0 : euclideanDualLattice Λ)
    hw (fun ξ => (Real.exp_pos _).le) (by simp [w]) (by simp [c])
    (fun ξ => monomialCharacterMean_norm_le_one k α N ξ) (by positivity : 0 ≤ (8 * A)⁻¹)
    hwA.le htailsum (by rw [hmean, hδA]; linarith)
  refine ⟨ξ, ξ.property, ?_, hξR, hlarge⟩
  intro he
  exact hξ (Subtype.ext he)

end Erdos3

end

section

namespace Erdos3

theorem schmidtRadiusFactor_pos (d : ℕ) {A : ℝ} (hA : 1 ≤ A) :
    0 < schmidtRadiusFactor d A := by
  have hlog := Real.log_nonneg hA
  unfold schmidtRadiusFactor
  positivity

theorem gaussian_tail_radius_bound (d : ℕ) {A : ℝ} (hA : 1 ≤ A) :
    Real.exp (-Real.pi * (schmidtRadiusFactor d A) ^ 2 / 2) * (2 : ℝ) ^ d * A ≤ 1 / 4 := by
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hlog := Real.log_nonneg hA
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have htwo : (2 : ℝ) ^ d ≤ Real.exp (d : ℝ) := by
    have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) he d
    simpa only [← Real.exp_nat_mul, mul_one] using h
  have hexponent : -Real.pi * (schmidtRadiusFactor d A) ^ 2 / 2 + d + Real.log A ≤ -4 := by
    have hp : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hsq := mul_nonneg (sub_nonneg.mpr hp) (sq_nonneg (schmidtRadiusFactor d A))
    unfold schmidtRadiusFactor at *
    nlinarith [sq_nonneg ((d : ℝ) + Real.log A)]
  have hsmall : Real.exp (-4 : ℝ) ≤ 1 / 4 := by
    rw [Real.exp_neg]
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (Real.exp_pos 4)).mpr
    nlinarith [Real.add_one_le_exp (4 : ℝ)]
  calc
    _ ≤ Real.exp (-Real.pi * (schmidtRadiusFactor d A) ^ 2 / 2) * Real.exp (d : ℝ) * A :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htwo (Real.exp_pos _).le) hApos.le
    _ = Real.exp (-Real.pi * (schmidtRadiusFactor d A) ^ 2 / 2 + d + Real.log A) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log hApos]
    _ ≤ Real.exp (-4 : ℝ) := Real.exp_le_exp.mpr hexponent
    _ ≤ _ := hsmall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem exists_logarithmically_short_dual_correlation (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] {t : ℝ} (ht : 0 < t) (k : ℕ) (α : E) (N : ℕ)
    (hsmall : latticeGaussianMean Λ t k α N < 1 / 2) :
    ∃ ξ : E, ξ ∈ euclideanDualLattice Λ ∧ ξ ≠ 0 ∧
      ‖ξ‖ ≤ Real.sqrt t * schmidtRadiusFactor (Module.finrank ℝ E) (normalizedLatticeGaussian Λ t 0) ∧
      (8 * normalizedLatticeGaussian Λ t 0)⁻¹ < ‖monomialCharacterMean k α N ξ‖ := by
  have hA := normalizedLatticeGaussian_origin_ge_one Λ ht
  have hfactor := schmidtRadiusFactor_pos (Module.finrank ℝ E) hA
  apply exists_short_dual_correlation Λ ht (mul_nonneg (Real.sqrt_nonneg _) hfactor.le) k α N _ hsmall
  have h := gaussian_tail_radius_bound (Module.finrank ℝ E) hA
  have he : -Real.pi / t *
      (Real.sqrt t * schmidtRadiusFactor (Module.finrank ℝ E) (normalizedLatticeGaussian Λ t 0)) ^ 2 / 2 =
      -Real.pi * (schmidtRadiusFactor (Module.finrank ℝ E) (normalizedLatticeGaussian Λ t 0)) ^ 2 / 2 := by
    rw [mul_pow, Real.sq_sqrt ht.le]
    field_simp
  rwa [he]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SchmidtShortDualVector
namespace OAI

section

namespace Erdos3

open Polynomial CircleFourier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem PolynomialIntervalPowerBound.monomial_character_mean {k C d : ℕ}
    (hW : PolynomialIntervalPowerBound k C d) (α ξ : E) (N : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hsize : (C : ℝ) ≤ δ ^ d * (2 * N + 1))
    (hscore : δ ≤ ‖monomialCharacterMean k α N ξ‖) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ C / δ ^ d ∧ ∃ p : ℤ,
      |(q : ℝ) * inner ℝ ξ α - p| ≤ C / (δ ^ d * (2 * (N : ℝ) + 1) ^ k) := by
  let P : Polynomial ℝ := Polynomial.C (inner ℝ ξ α) * X ^ k
  have hP : P.natDegree ≤ k := natDegree_C_mul_X_pow_le _ _
  have hlength : (((N : ℤ) + 1 - -(N : ℤ)).toNat) = 2 * N + 1 := by omega
  have hset : Finset.Ico (-(N : ℤ)) ((N : ℤ) + 1) = Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    ext n
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  have hcard : (Finset.Icc (-(N : ℤ)) (N : ℤ)).card = 2 * N + 1 := by
    rw [← hset, Int.card_Ico, hlength]
  have hsum : (∑ n ∈ Finset.Ico (-(N : ℤ)) ((N : ℤ) + 1), character ((P.eval (n : ℝ) : ℝ) : CircleFourier.Circle)) =
      ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), euclideanCharacter ξ ((n : ℝ) ^ k • α) := by
    rw [hset]
    apply Finset.sum_congr rfl
    intro n _
    simp only [P, eval_mul, eval_C, eval_pow, eval_X, euclideanCharacter, inner_smul_right]
    rw [mul_comm (inner ℝ ξ α)]
  have hscore' : δ * ((N : ℤ) + 1 - -(N : ℤ)).toNat ≤
      ‖∑ n ∈ Finset.Ico (-(N : ℤ)) ((N : ℤ) + 1), character ((P.eval (n : ℝ) : ℝ) : CircleFourier.Circle)‖ := by
    rw [monomialCharacterMean, norm_div, Complex.norm_natCast, hcard] at hscore
    rw [hsum, hlength]
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < (2 * N + 1 : ℕ))).mp hscore
  obtain ⟨q, hq, hqbound, p, hp⟩ := hW P (-(N : ℤ)) ((N : ℤ) + 1) δ hP
    (by rw [hlength]; omega) hδ hδone (by simpa only [hlength, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one] using hsize) hscore'
  refine ⟨q, hq, hqbound, p, ?_⟩
  simpa only [P, coeff_C_mul_X_pow, ite_true, hlength, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_one] using hp

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem PolynomialIntervalPowerBound.short_dual_vector_s2_oai {k C d : ℕ}
    (hW : PolynomialIntervalPowerBound k C d)
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {t : ℝ} (ht : 0 < t) (α : E) (N : ℕ)
    (hsize : (C : ℝ) * (8 * normalizedLatticeGaussian Λ t 0) ^ d ≤ 2 * N + 1)
    (hsmall : latticeGaussianMean Λ t k α N < 1 / 2) :
    ∃ ξ : E, ξ ∈ euclideanDualLattice Λ ∧ ξ ≠ 0 ∧
      ‖ξ‖ ≤ Real.sqrt t * schmidtRadiusFactor (Module.finrank ℝ E) (normalizedLatticeGaussian Λ t 0) ∧
      ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ C * (8 * normalizedLatticeGaussian Λ t 0) ^ d ∧
        ∃ p : ℤ, |(q : ℝ) * inner ℝ ξ α - p| ≤
          C * (8 * normalizedLatticeGaussian Λ t 0) ^ d / (2 * (N : ℝ) + 1) ^ k := by
  obtain ⟨ξ, hξΛ, hξ, hnorm, hscore⟩ :=
    exists_logarithmically_short_dual_correlation Λ ht k α N hsmall
  have hA := normalizedLatticeGaussian_origin_ge_one Λ ht
  let B := 8 * normalizedLatticeGaussian Λ t 0
  have hB : 0 < B := by dsimp [B]; linarith
  have hBone : 1 ≤ B := by dsimp [B]; linarith
  have hδone : B⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hBone
  have hsize' : (C : ℝ) ≤ (B⁻¹) ^ d * (2 * N + 1) := by
    rw [inv_pow, inv_mul_eq_div]
    exact (le_div_iff₀ (pow_pos hB d)).mpr hsize
  obtain ⟨q, hq, hqbound, p, hp⟩ := hW.monomial_character_mean α ξ N (inv_pos.mpr hB) hδone
    hsize' hscore.le
  refine ⟨ξ, hξΛ, hξ, hnorm, q, hq, ?_, p, ?_⟩
  · simpa only [B, inv_pow, div_inv_eq_mul] using hqbound
  · simpa only [B, div_mul_eq_div_div, inv_pow, div_inv_eq_mul] using hp

end Erdos3

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Erdos3.PolynomialIntervalPowerBound.short_dual_vector_s2_oai.{u_1} := @OAI.Erdos3.PolynomialIntervalPowerBound.short_dual_vector_s2_oai.{u_1}
