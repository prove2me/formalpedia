-- Prove2me | solution 1 for OAI.Erdos3.PolynomialIntervalPowerBound.simultaneous_monomial_recurrence_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T11:25:13.983211+00:00
-- url     : https://prove2.me/submissions/b17a1635-6ce6-4e19-a308-865733ce1fad

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B100
import Definitions.Def_OAIE3v2B137
import Theorems.Thm_OAI_Erdos3_PolynomialIntervalPowerBound_gaussian_mean_iteration_s2
import Theorems.Thm_OAI_Erdos3_standardLatticeGaussian_origin_bound_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeHyperplaneBasis
namespace OAI

section

namespace Erdos3

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem latticeGaussianMass_nonneg (Λ : Submodule ℤ E) (t : ℝ) (x : E) :
    0 ≤ latticeGaussianMass Λ t x := tsum_nonneg (fun _ => (Real.exp_pos _).le)

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

theorem latticeGaussianNormalizer_nonneg (Λ : Submodule ℤ E) (t : ℝ) :
    0 ≤ latticeGaussianNormalizer Λ t :=
  mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) ENNReal.toReal_nonneg

theorem latticeGaussianNormalizer_pos (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] {t : ℝ} (ht : 0 < t) : 0 < latticeGaussianNormalizer Λ t :=
  mul_pos (pow_pos (Real.sqrt_pos.mpr ht) _) (ZLattice.covolume_pos Λ MeasureTheory.volume)

theorem normalizedLatticeGaussian_nonneg (Λ : Submodule ℤ E) (t : ℝ) (x : E) :
    0 ≤ normalizedLatticeGaussian Λ t x :=
  mul_nonneg (latticeGaussianNormalizer_nonneg Λ t) (latticeGaussianMass_nonneg Λ t x)

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GaussianNonzeroIndex
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem exists_nonzero_index_of_gaussian_mean (Λ : Submodule ℤ E) (t : ℝ)
    (α : E) (j N : ℕ) {D B : ℝ} (hD : 0 < D) (hB : 0 ≤ B)
    (hmean : 1 ≤ D * latticeGaussianMean Λ t (j + 1) α N)
    (hlength : 2 * D * normalizedLatticeGaussian Λ t 0 < 2 * (N : ℝ) + 1)
    (hsmall : 2 * D * B < 1) :
    ∃ n : ℤ, n ≠ 0 ∧ |n| ≤ (N : ℤ) ∧ B < normalizedLatticeGaussian Λ t ((n : ℝ) ^ (j + 1) • α) := by
  classical
  by_contra! hnone
  let s := Finset.Icc (-(N : ℤ)) (N : ℤ)
  let f := fun n : ℤ => normalizedLatticeGaussian Λ t ((n : ℝ) ^ (j + 1) • α)
  let A := normalizedLatticeGaussian Λ t 0
  have hpoint (n : ℤ) (hn : n ∈ s) : f n ≤ (if n = 0 then A else 0) + B := by
    by_cases hzero : n = 0
    · subst n
      simp only [f, Int.cast_zero, zero_pow (Nat.succ_ne_zero j), zero_smul, ite_true]
      dsimp [A]
      linarith
    · simp only [hzero, ite_false, zero_add]
      exact hnone n hzero (abs_le.mpr (Finset.mem_Icc.mp hn))
  have hsum := Finset.sum_le_sum hpoint
  have h0 : (0 : ℤ) ∈ s := by simp [s]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', h0, ite_true,
    Finset.sum_const, nsmul_eq_mul] at hsum
  have hc : (s.card : ℝ) = 2 * (N : ℝ) + 1 := by
    simp only [s, symmetricInterval_card, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  rw [hc] at hsum
  have hmean' : (2 * (N : ℝ) + 1) * latticeGaussianMean Λ t (j + 1) α N = ∑ n ∈ s, f n := by
    unfold latticeGaussianMean
    change (2 * (N : ℝ) + 1) * ((∑ n ∈ s, f n) / (s.card : ℝ)) = _
    rw [hc, mul_div_cancel₀ _ (by positivity : 2 * (N : ℝ) + 1 ≠ 0)]
  have hlower := mul_le_mul_of_nonneg_left hmean (show 0 ≤ 2 * (N : ℝ) + 1 by positivity)
  have hupper := mul_le_mul_of_nonneg_left hsum hD.le
  have htail := mul_lt_mul_of_pos_right hsmall (show 0 < 2 * (N : ℝ) + 1 by positivity)
  dsimp [A] at hupper
  nlinarith [hmean']

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

theorem normalizedLatticeGaussian_zero_eq_dual {t : ℝ} (ht : 0 < t) :
    normalizedLatticeGaussian Λ t 0 = latticeGaussianMass (euclideanDualLattice Λ) t⁻¹ 0 := by
  apply Complex.ofReal_injective
  rw [normalizedLatticeGaussian_poisson Λ ht]
  simp only [euclideanCharacter_zero, mul_one, latticeGaussianMass, Complex.ofReal_tsum,
    zero_sub, norm_neg, div_eq_mul_inv]

theorem normalizedLatticeGaussian_le_origin {t : ℝ} (ht : 0 < t) (x : E) :
    normalizedLatticeGaussian Λ t x ≤ normalizedLatticeGaussian Λ t 0 := by
  calc
    _ = ‖(normalizedLatticeGaussian Λ t x : ℂ)‖ := by
      simp only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (normalizedLatticeGaussian_nonneg Λ t x)]
    _ = ‖∑' ξ : euclideanDualLattice Λ,
        (Real.exp (-Real.pi / t * ‖(ξ : E)‖ ^ 2) : ℂ) * euclideanCharacter (ξ : E) x‖ := by
      rw [normalizedLatticeGaussian_poisson Λ ht]
    _ ≤ ∑' ξ : euclideanDualLattice Λ,
        ‖(Real.exp (-Real.pi / t * ‖(ξ : E)‖ ^ 2) : ℂ) * euclideanCharacter (ξ : E) x‖ :=
      norm_tsum_le_tsum_norm (latticeGaussian_fourier_summable_norm Λ ht x)
    _ = latticeGaussianMass (euclideanDualLattice Λ) t⁻¹ 0 := by
      simp only [norm_mul, norm_euclideanCharacter, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), latticeGaussianMass,
        zero_sub, norm_neg, div_eq_mul_inv]
    _ = _ := (normalizedLatticeGaussian_zero_eq_dual Λ ht).symm

theorem normalizedLatticeGaussian_origin_mono {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    normalizedLatticeGaussian Λ s 0 ≤ normalizedLatticeGaussian Λ t 0 := by
  rw [normalizedLatticeGaussian_zero_eq_dual Λ hs,
    normalizedLatticeGaussian_zero_eq_dual Λ (hs.trans_le hst)]
  exact latticeGaussianMass_antitone (euclideanDualLattice Λ) (inv_pos.mpr (hs.trans_le hst))
    (inv_le_inv₀ (hs.trans_le hst) hs |>.mpr hst) 0

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

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

theorem latticeGaussianMass_le_origin {t : ℝ} (ht : 0 < t) (x : E) :
    latticeGaussianMass Λ t x ≤ latticeGaussianMass Λ t 0 := by
  have h := normalizedLatticeGaussian_le_origin Λ ht x
  exact (mul_le_mul_iff_right₀ (latticeGaussianNormalizer_pos Λ ht)).mp h

theorem normalizedLatticeGaussian_le_of_far {t R : ℝ} (ht : 0 < t) (hR : 0 ≤ R)
    (x : E) (hfar : ∀ m : Λ, R ≤ ‖x - (m : E)‖) :
    normalizedLatticeGaussian Λ t x ≤ Real.exp (-Real.pi * t * R ^ 2 / 2) *
      (2 : ℝ) ^ Module.finrank ℝ E * normalizedLatticeGaussian Λ t 0 := by
  have hpoint (m : Λ) : Real.exp (-Real.pi * t * ‖x - (m : E)‖ ^ 2) ≤
      Real.exp (-Real.pi * t * R ^ 2 / 2) * Real.exp (-Real.pi * (t / 4) * ‖x - (m : E)‖ ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hsq := pow_le_pow_left₀ hR (hfar m) 2
    nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le ht.le) (sub_nonneg.mpr hsq),
      mul_nonneg (mul_nonneg Real.pi_pos.le ht.le) (sq_nonneg ‖x - (m : E)‖)]
  have hs := (lattice_gaussian_summable Λ (show 0 < t / 4 by positivity) x).mul_left
    (Real.exp (-Real.pi * t * R ^ 2 / 2))
  have hsum := (lattice_gaussian_summable Λ ht x).tsum_le_tsum hpoint hs
  rw [tsum_mul_left] at hsum
  have hmass : latticeGaussianMass Λ t x ≤ Real.exp (-Real.pi * t * R ^ 2 / 2) *
      ((2 : ℝ) ^ Module.finrank ℝ E * latticeGaussianMass Λ t 0) := by
    exact hsum.trans (mul_le_mul_of_nonneg_left
      ((latticeGaussianMass_le_origin Λ (by positivity : 0 < t / 4) x).trans
        (latticeGaussianMass_quarter_temperature Λ ht)) (Real.exp_pos _).le)
  have hnorm := mul_le_mul_of_nonneg_left hmass (latticeGaussianNormalizer_pos Λ ht).le
  change latticeGaussianNormalizer Λ t * latticeGaussianMass Λ t x ≤ _
  calc
    _ ≤ latticeGaussianNormalizer Λ t * (Real.exp (-Real.pi * t * R ^ 2 / 2) *
        ((2 : ℝ) ^ Module.finrank ℝ E * latticeGaussianMass Λ t 0)) := hnorm
    _ = _ := by change _ = _ * _ * (latticeGaussianNormalizer Λ t * latticeGaussianMass Λ t 0); ring

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

end Erdos3

end

section

namespace Erdos3

theorem schmidtRadiusFactor_pos (d : ℕ) {A : ℝ} (hA : 1 ≤ A) :
    0 < schmidtRadiusFactor d A := by
  have hlog := Real.log_nonneg hA
  unfold schmidtRadiusFactor
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MonomialSignedIndex
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_positive_monomial_index (Λ : Submodule ℤ E) (α : E) (k N : ℕ)
    (n : ℤ) (hn : n ≠ 0) (hnN : |n| ≤ (N : ℤ))
    (m : E) (hm : m ∈ Λ) {R : ℝ} (happrox : ‖(n : ℝ) ^ k • α - m‖ < R) :
    ∃ q : ℕ, 0 < q ∧ q ≤ N ∧ ∃ v ∈ Λ, ‖(q : ℝ) ^ k • α - v‖ < R := by
  by_cases hsign : 0 ≤ n
  · let q := n.toNat
    have hqZ : (q : ℤ) = n := Int.toNat_of_nonneg hsign
    have hqR : (q : ℝ) = (n : ℝ) := by exact_mod_cast hqZ
    refine ⟨q, by omega, ?_, m, hm, ?_⟩
    · rw [abs_of_nonneg hsign] at hnN
      omega
    · simpa only [hqR] using happrox
  · let q := (-n).toNat
    have hqZ : (q : ℤ) = -n := Int.toNat_of_nonneg (by omega)
    have hqR : (q : ℝ) = -(n : ℝ) := by exact_mod_cast hqZ
    have hv : (-1 : ℝ) ^ k • m ∈ Λ := by
      have h := Λ.smul_mem ((-1 : ℤ) ^ k) hm
      simpa only [← Int.cast_smul_eq_zsmul ℝ, Int.cast_pow, Int.cast_neg, Int.cast_one] using h
    refine ⟨q, by omega, ?_, (-1 : ℝ) ^ k • m, hv, ?_⟩
    · rw [abs_of_neg (by omega)] at hnN
      omega
    · rw [hqR, neg_eq_neg_one_mul, mul_pow, mul_smul, ← smul_sub, norm_smul]
      simpa only [norm_pow, norm_neg, norm_one, one_pow, one_mul] using happrox

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialCoordinatePartition
namespace OAI

section

namespace Erdos3

theorem schmidtStepFactor_bounds (C e d : ℕ) {A : ℝ} (hA : 1 ≤ A) :
    1 ≤ schmidtStepFactor C e d A ∧
    (C : ℝ) * (8 * A) ^ e ≤ schmidtStepFactor C e d A ∧
    (C : ℝ) * (8 * A) ^ e * (schmidtRadiusFactor d A * (Real.exp Real.pi * A)) ≤
      schmidtStepFactor C e d A ∧
    (C : ℝ) * (8 * A) ^ e * (Real.exp Real.pi * A) ≤
      ((d : ℝ) + 1)⁻¹ * schmidtStepFactor C e d A := by
  have hA0 : 0 ≤ A := by linarith
  have hB : 0 ≤ (C : ℝ) * (8 * A) ^ e := by positivity
  have hL : 1 ≤ schmidtRadiusFactor d A := by
    unfold schmidtRadiusFactor
    nlinarith [Real.log_nonneg hA, Nat.cast_nonneg (α := ℝ) d]
  have hS : 1 ≤ Real.exp Real.pi * A := by
    have he : 1 ≤ Real.exp Real.pi := by linarith [Real.add_one_le_exp Real.pi, Real.pi_pos]
    nlinarith
  have hR : 0 < (d : ℝ) + 1 := by positivity
  have hBS : 0 ≤ (C : ℝ) * (8 * A) ^ e * (Real.exp Real.pi * A) := by positivity
  have hQ : (C : ℝ) * (8 * A) ^ e * (schmidtRadiusFactor d A * (Real.exp Real.pi * A)) ≤
      schmidtStepFactor C e d A := by
    unfold schmidtStepFactor
    nlinarith [mul_nonneg hBS hR.le]
  refine ⟨?_, ?_, hQ, ?_⟩
  · unfold schmidtStepFactor
    have : 0 ≤ schmidtRadiusFactor d A + (d : ℝ) + 1 := by linarith
    nlinarith [mul_nonneg hBS this]
  · calc
      _ ≤ (C : ℝ) * (8 * A) ^ e * (Real.exp Real.pi * A) := le_mul_of_one_le_right hB hS
      _ ≤ ((C : ℝ) * (8 * A) ^ e * (Real.exp Real.pi * A)) * schmidtRadiusFactor d A :=
        le_mul_of_one_le_right hBS hL
      _ ≤ schmidtStepFactor C e d A := by nlinarith [hQ]
  · rw [inv_mul_eq_div]
    apply (le_div_iff₀ hR).mpr
    unfold schmidtStepFactor
    nlinarith [mul_nonneg hBS (by linarith : 0 ≤ schmidtRadiusFactor d A)]

end Erdos3

end

section

namespace Erdos3

theorem schmidtMassMultiplier_ge_one (d : ℕ) {A : ℝ} (hA : 1 ≤ A) :
    1 ≤ schmidtMassMultiplier d A := by
  have hZ : 1 ≤ (d : ℝ) + Real.log A + 1 := by
    have := Real.log_nonneg hA
    have := Nat.cast_nonneg (α := ℝ) d
    linarith
  have hsq : 1 ≤ ((d : ℝ) + Real.log A + 1) ^ 2 := one_le_pow₀ hZ
  have he : 1 ≤ Real.exp (10 : ℝ) := by linarith [Real.add_one_le_exp (10 : ℝ)]
  change 1 ≤ Real.exp 10 * ((d : ℝ) + Real.log A + 1) ^ 2
  nlinarith

theorem schmidtMassCeiling_ge (d : ℕ) {A : ℝ} (hA : 1 ≤ A) :
    A ≤ schmidtMassCeiling d A :=
  le_mul_of_one_le_right (by linarith) (one_le_pow₀ (schmidtMassMultiplier_ge_one d hA))

theorem schmidtMassBudget_closes (d : ℕ) {A : ℝ} (hA : 1 ≤ A) :
    Real.exp 1 * schmidtRadiusFactor d (schmidtMassCeiling d A) ≤
      schmidtMassMultiplier d A := by
  let Z := (d : ℝ) + Real.log A + 1
  have hApos : 0 < A := by linarith
  have hZ : 1 ≤ Z := by
    dsimp [Z]
    have := Real.log_nonneg hA
    have := Nat.cast_nonneg (α := ℝ) d
    linarith
  have hZpos : 0 < Z := by linarith
  have hDZ : (d : ℝ) ≤ Z := by dsimp [Z]; linarith [Real.log_nonneg hA]
  have hZsq : Z ≤ Z ^ 2 := by nlinarith
  have hDsq : (d : ℝ) ≤ Z ^ 2 := hDZ.trans hZsq
  have hDlog : (d : ℝ) * Real.log Z ≤ Z ^ 2 := by
    have h := mul_le_mul hDZ (Real.log_le_self hZpos.le) (Real.log_nonneg hZ) hZpos.le
    nlinarith
  have hMpos : 0 < schmidtMassMultiplier d A := by
    have := schmidtMassMultiplier_ge_one d hA
    linarith
  have hlogM : Real.log (schmidtMassMultiplier d A) = 10 + 2 * Real.log Z := by
    change Real.log (Real.exp 10 * Z ^ 2) = _
    rw [Real.log_mul (Real.exp_pos _).ne' (pow_pos hZpos 2).ne', Real.log_exp, Real.log_pow]
    norm_num
  have hlogU : Real.log (schmidtMassCeiling d A) = Real.log A + (d : ℝ) * (10 + 2 * Real.log Z) := by
    unfold schmidtMassCeiling
    rw [Real.log_mul hApos.ne' (pow_pos hMpos d).ne', Real.log_pow, hlogM]
  have hLU : schmidtRadiusFactor d (schmidtMassCeiling d A) ≤ 52 * Z ^ 2 := by
    unfold schmidtRadiusFactor
    rw [hlogU]
    have hZeq : (d : ℝ) + Real.log A + 1 = Z := rfl
    nlinarith
  have he : 52 * Real.exp (1 : ℝ) ≤ Real.exp (10 : ℝ) := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo 9
    rw [← Real.exp_nat_mul] at hpow
    norm_num at hpow
    calc
      _ ≤ Real.exp 9 * Real.exp 1 := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; norm_num
  calc
    _ ≤ Real.exp 1 * (52 * Z ^ 2) := mul_le_mul_of_nonneg_left hLU (Real.exp_pos _).le
    _ ≤ Real.exp 10 * Z ^ 2 := by nlinarith [mul_le_mul_of_nonneg_right he (sq_nonneg Z)]
    _ = _ := rfl

end Erdos3

end

section

namespace Erdos3

theorem schmidt_uniform_cost_bounds (C e d : ℕ) {U M : ℝ}
    (hU : 1 ≤ U) (hM : 1 ≤ M) (hLM : Real.exp 1 * schmidtRadiusFactor d U ≤ M) :
    let V := schmidtDegreeConstant C e * U ^ (e + 1) * M ^ 2
    2 ≤ V ∧ 4 * schmidtStepFactor C e d U + 1 ≤ V ∧
      2 * Real.exp (4 * Real.pi + 1) * schmidtRadiusFactor d U * schmidtStepFactor C e d U ≤ V := by
  let b := 2 * Real.exp Real.pi * (C : ℝ) * (8 : ℝ) ^ e
  let X := (1 + b) * U ^ (e + 1) * M
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hU0 : 0 ≤ U := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hL0 := (schmidtRadiusFactor_pos d hU).le
  have he1 : 1 ≤ Real.exp (1 : ℝ) := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hL : schmidtRadiusFactor d U ≤ M := by nlinarith
  have hd : (d : ℝ) + 1 ≤ schmidtRadiusFactor d U := by
    unfold schmidtRadiusFactor
    have := Real.log_nonneg hU
    have := Nat.cast_nonneg (α := ℝ) d
    linarith
  have hpow : 1 ≤ U ^ (e + 1) := one_le_pow₀ hU
  have hUM : 1 ≤ U ^ (e + 1) * M := by nlinarith
  have hX : 1 ≤ X := by dsimp [X]; nlinarith
  have hK : schmidtStepFactor C e d U ≤ X := by
    have hfactor : schmidtRadiusFactor d U + (d : ℝ) + 1 ≤ 2 * M := by linarith
    have hmult := mul_le_mul_of_nonneg_left hfactor
      (show 0 ≤ (C : ℝ) * (8 * U) ^ e * (Real.exp Real.pi * U) by positivity)
    have hid : (C : ℝ) * (8 * U) ^ e * (Real.exp Real.pi * U) * (2 * M) =
        b * (U ^ (e + 1) * M) := by dsimp [b]; rw [mul_pow, pow_succ]; ring
    rw [hid] at hmult
    dsimp [schmidtStepFactor, X]
    nlinarith
  have hXM : X ≤ X * M := le_mul_of_one_le_right (by linarith) hM
  have hXM0 : 0 ≤ X * M := by positivity
  have hVeq : schmidtDegreeConstant C e * U ^ (e + 1) * M ^ 2 =
      (10 + 8 * Real.exp (4 * Real.pi + 1)) * (X * M) := by
    dsimp [schmidtDegreeConstant, X, b]
    ring
  dsimp only
  rw [hVeq]
  have hVlarge : 5 * X ≤ (10 + 8 * Real.exp (4 * Real.pi + 1)) * (X * M) := by
    nlinarith [mul_nonneg (Real.exp_pos (4 * Real.pi + 1)).le hXM0]
  refine ⟨by linarith, by linarith, ?_⟩
  have hK0 := (schmidtStepFactor_bounds C e d hU).1.trans' (by norm_num : (0 : ℝ) ≤ 1)
  have hLK := mul_le_mul hL hK hK0 hM0
  have hscaled := mul_le_mul_of_nonneg_left hLK
    (show 0 ≤ 2 * Real.exp (4 * Real.pi + 1) by positivity)
  nlinarith [mul_nonneg (Real.exp_pos (4 * Real.pi + 1)).le hXM0]

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem PolynomialIntervalPowerBound.gaussian_mean_lower_bound {j C e : ℕ}
    (hW : PolynomialIntervalPowerBound (j + 1) C e)
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {t : ℝ} (ht : 0 < t) (α : E) (N : ℕ) :
    let A := normalizedLatticeGaussian Λ t 0
    let d := Module.finrank ℝ E
    let M := schmidtMassMultiplier d A
    1 ≤ (schmidtDegreeConstant C e * A ^ (e + 1) * M ^ (d * (e + 1) + 2)) ^ (d + 1) *
      latticeGaussianMean Λ t (j + 1) α N := by
  let A := normalizedLatticeGaussian Λ t 0
  let d := Module.finrank ℝ E
  let M := schmidtMassMultiplier d A
  let U := schmidtMassCeiling d A
  have hA : 1 ≤ A := normalizedLatticeGaussian_origin_ge_one Λ ht
  have hM : 1 ≤ M := schmidtMassMultiplier_ge_one d hA
  have hU : 1 ≤ U := hA.trans (schmidtMassCeiling_ge d hA)
  have hLM := schmidtMassBudget_closes d hA
  obtain ⟨hV, hKV, hTV⟩ := schmidt_uniform_cost_bounds C e d hU hM hLM
  have h := hW.gaussian_mean_iteration_s2 hM hU hLM hV hKV hTV d E Λ ht α N rfl le_rfl le_rfl
  have hid : schmidtDegreeConstant C e * U ^ (e + 1) * M ^ 2 =
      schmidtDegreeConstant C e * A ^ (e + 1) * M ^ (d * (e + 1) + 2) := by
    change schmidtDegreeConstant C e * (A * M ^ d) ^ (e + 1) * M ^ 2 = _
    rw [mul_pow, ← pow_mul, pow_add]
    ring
  rw [hid] at h
  exact h

end Erdos3

end

section

namespace Erdos3

theorem schmidtMeanDenominator_pos (C e d : ℕ) {A : ℝ} (hA : 1 ≤ A) :
    0 < schmidtMeanDenominator C e d A := by
  have hApos : 0 < A := by linarith
  have hMpos : 0 < schmidtMassMultiplier d A := by
    have := schmidtMassMultiplier_ge_one d hA
    linarith
  unfold schmidtMeanDenominator schmidtDegreeConstant
  positivity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem exists_positive_lattice_approx_of_gaussian_mean
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (α : E) (j N : ℕ) {t R D : ℝ} (ht : 0 < t) (hR : 0 ≤ R) (hD : 0 < D)
    (hmean : 1 ≤ D * latticeGaussianMean Λ t (j + 1) α N)
    (hlength : 2 * D * normalizedLatticeGaussian Λ t 0 < 2 * (N : ℝ) + 1)
    (htail : 2 * D * (Real.exp (-Real.pi * t * R ^ 2 / 2) *
      (2 : ℝ) ^ Module.finrank ℝ E * normalizedLatticeGaussian Λ t 0) < 1) :
    ∃ q : ℕ, 0 < q ∧ q ≤ N ∧ ∃ v ∈ Λ, ‖(q : ℝ) ^ (j + 1) • α - v‖ < R := by
  obtain ⟨n, hn, hnN, hscore⟩ := exists_nonzero_index_of_gaussian_mean Λ t α j N hD
    (show 0 ≤ Real.exp (-Real.pi * t * R ^ 2 / 2) *
      (2 : ℝ) ^ Module.finrank ℝ E * normalizedLatticeGaussian Λ t 0 from
      mul_nonneg (by positivity) (normalizedLatticeGaussian_nonneg Λ t 0)) hmean hlength htail
  have hnear : ∃ m : Λ, ‖(n : ℝ) ^ (j + 1) • α - (m : E)‖ < R := by
    by_contra! hfar
    exact (normalizedLatticeGaussian_le_of_far Λ ht hR _ hfar).not_gt hscore
  obtain ⟨m, hm⟩ := hnear
  exact exists_positive_monomial_index Λ α (j + 1) N n hn hnN (m : E) m.property hm

theorem PolynomialIntervalPowerBound.lattice_recurrence {j C e : ℕ}
    (hW : PolynomialIntervalPowerBound (j + 1) C e)
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (α : E) (N : ℕ) {t R : ℝ} (ht : 0 < t) (hR : 0 ≤ R)
    (hlength : 2 * schmidtMeanDenominator C e (Module.finrank ℝ E) (normalizedLatticeGaussian Λ t 0) *
      normalizedLatticeGaussian Λ t 0 < 2 * (N : ℝ) + 1)
    (htail : 2 * schmidtMeanDenominator C e (Module.finrank ℝ E) (normalizedLatticeGaussian Λ t 0) *
      (Real.exp (-Real.pi * t * R ^ 2 / 2) * (2 : ℝ) ^ Module.finrank ℝ E *
        normalizedLatticeGaussian Λ t 0) < 1) :
    ∃ q : ℕ, 0 < q ∧ q ≤ N ∧ ∃ v ∈ Λ, ‖(q : ℝ) ^ (j + 1) • α - v‖ < R := by
  exact exists_positive_lattice_approx_of_gaussian_mean Λ α j N ht hR
    (schmidtMeanDenominator_pos C e _ (normalizedLatticeGaussian_origin_ge_one Λ ht))
    (hW.gaussian_mean_lower_bound Λ ht α N) hlength htail

end Erdos3

end

section

namespace Erdos3

theorem schmidt_recurrence_mass_bounds (d : ℕ) {A X : ℝ}
    (hX : 2 ≤ X) (hd : (d : ℝ) + 1 ≤ X) (hconst : 121 * Real.exp 10 ≤ X)
    (hA : 1 ≤ A) (hAU : A ≤ (1 + 2 * X ^ 8) ^ d) :
    A ≤ X ^ (10 * d) ∧ schmidtMassMultiplier d A ≤ X ^ 5 := by
  have hX0 : 0 ≤ X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hX8 : 1 ≤ X ^ 8 := one_le_pow₀ hX1
  have hX2 : 3 ≤ X ^ 2 := by nlinarith
  have hbase : 1 + 2 * X ^ 8 ≤ X ^ 10 := by
    have h := mul_le_mul_of_nonneg_right hX2 (pow_nonneg hX0 8)
    have heq : X ^ 2 * X ^ 8 = X ^ 10 := by ring
    rw [heq] at h
    nlinarith
  have hAX : A ≤ X ^ (10 * d) := by
    calc
      A ≤ (1 + 2 * X ^ 8) ^ d := hAU
      _ ≤ (X ^ 10) ^ d := pow_le_pow_left₀ (by positivity) hbase d
      _ = _ := (pow_mul X 10 d).symm
  refine ⟨hAX, ?_⟩
  have hApos : 0 < A := by linarith
  have hlogA : Real.log A ≤ (10 * (d : ℝ)) * Real.log X := by
    have h := Real.log_le_log hApos hAX
    simpa only [Real.log_pow, Nat.cast_mul, Nat.cast_ofNat] using h
  have hdX : (d : ℝ) ≤ X := by linarith
  have hlogX0 := Real.log_nonneg hX1
  have hprod : (d : ℝ) * Real.log X ≤ X ^ 2 := by
    have h := mul_le_mul hdX (Real.log_le_self hX0) hlogX0 hX0
    nlinarith
  have hZ0 : 0 ≤ (d : ℝ) + Real.log A + 1 := by
    have := Real.log_nonneg hA
    positivity
  have hZ : (d : ℝ) + Real.log A + 1 ≤ 11 * X ^ 2 := by nlinarith
  have hsq := pow_le_pow_left₀ hZ0 hZ 2
  calc
    schmidtMassMultiplier d A ≤ Real.exp 10 * (11 * X ^ 2) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
    _ = (121 * Real.exp 10) * X ^ 4 := by ring
    _ ≤ X * X ^ 4 := mul_le_mul_of_nonneg_right hconst (pow_nonneg hX0 4)
    _ = X ^ 5 := by ring

theorem schmidt_recurrence_denominator_bound (C e d : ℕ) {A X : ℝ}
    (hX : 2 ≤ X) (hA : 1 ≤ A) (hc : schmidtDegreeConstant C e ≤ X)
    (hAX : A ≤ X ^ (10 * d)) (hMX : schmidtMassMultiplier d A ≤ X ^ 5) :
    2 * schmidtMeanDenominator C e d A * (2 : ℝ) ^ d * A ≤
      X ^ (schmidtRecurrenceExponent e * (d + 1) ^ 2) := by
  have hX0 : 0 ≤ X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hA0 : 0 ≤ A := by linarith
  have hc0 : 0 ≤ schmidtDegreeConstant C e := by unfold schmidtDegreeConstant; positivity
  have hM0 : 0 ≤ schmidtMassMultiplier d A := by unfold schmidtMassMultiplier; positivity
  have hinner : schmidtDegreeConstant C e * A ^ (e + 1) *
      schmidtMassMultiplier d A ^ (d * (e + 1) + 2) ≤ X ^ (15 * d * (e + 1) + 11) := by
    have hmul := mul_le_mul (mul_le_mul hc (pow_le_pow_left₀ hA0 hAX (e + 1))
      (pow_nonneg hA0 _) hX0)
      (pow_le_pow_left₀ hM0 hMX (d * (e + 1) + 2))
      (pow_nonneg hM0 _) (by positivity)
    calc
      _ ≤ X * (X ^ (10 * d)) ^ (e + 1) * (X ^ 5) ^ (d * (e + 1) + 2) := hmul
      _ = X ^ (15 * d * (e + 1) + 11) := by
        rw [← pow_mul, ← pow_mul, ← pow_succ', ← pow_add]
        congr 1
        ring
  have hD := pow_le_pow_left₀ (by positivity) hinner (d + 1)
  change schmidtMeanDenominator C e d A ≤ (X ^ (15 * d * (e + 1) + 11)) ^ (d + 1) at hD
  rw [← pow_mul] at hD
  have hD0 := (schmidtMeanDenominator_pos C e d hA).le
  have htwo := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hX d
  have htotal := mul_le_mul (mul_le_mul (mul_le_mul hX hD hD0 hX0) htwo
    (by positivity) (by positivity)) hAX hA0 (by positivity)
  calc
    _ ≤ X * X ^ ((15 * d * (e + 1) + 11) * (d + 1)) * X ^ d * X ^ (10 * d) := htotal
    _ = X ^ (((15 * d * (e + 1) + 11) * (d + 1) + 1) + d + 10 * d) := by
      rw [← pow_succ', ← pow_add, ← pow_add]
    _ ≤ _ := by
      apply pow_le_pow_right₀ hX1
      unfold schmidtRecurrenceExponent
      nlinarith

end Erdos3

end

section

namespace Erdos3

theorem monomial_recurrence_tail_budget (p d : ℕ) {X R : ℝ}
    (hX : 2 ≤ X) (hd : (d : ℝ) + 1 ≤ X) (hp : (p : ℝ) ≤ X)
    (hXR : 1 ≤ X * R) :
    X ^ (p * (d + 1) ^ 2) * Real.exp (-Real.pi * X ^ 8 * R ^ 2 / 2) < 1 := by
  have hX0 : 0 ≤ X := by linarith
  have hXpos : 0 < X := by linarith
  have hlog0 : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hlog : Real.log X ≤ X := Real.log_le_self hX0
  have hsq := pow_le_pow_left₀ (show 0 ≤ (d : ℝ) + 1 by positivity) hd 2
  have hdegree : (p : ℝ) * ((d : ℝ) + 1) ^ 2 ≤ X ^ 3 := by
    have h := mul_le_mul hp hsq (sq_nonneg _) hX0
    nlinarith
  have hexponent : ((p * (d + 1) ^ 2 : ℕ) : ℝ) * Real.log X ≤ X ^ 4 := by
    have h := mul_le_mul hdegree hlog hlog0 (pow_nonneg hX0 3)
    push_cast
    nlinarith
  have hpower : X ^ (p * (d + 1) ^ 2) ≤ Real.exp (X ^ 4) := by
    calc
      _ = Real.exp (((p * (d + 1) ^ 2 : ℕ) : ℝ) * Real.log X) := by
        rw [Real.exp_nat_mul, Real.exp_log hXpos]
      _ ≤ _ := Real.exp_le_exp.mpr hexponent
  have hXR2 : 1 ≤ (X * R) ^ 2 := one_le_pow₀ hXR
  have henergy : X ^ 6 ≤ X ^ 8 * R ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hXR2 (pow_nonneg hX0 6)
    nlinarith [show X ^ 6 * (X * R) ^ 2 = X ^ 8 * R ^ 2 by ring]
  have h6 : 4 * X ^ 4 ≤ X ^ 6 := by
    have hx2 : (4 : ℝ) ≤ X ^ 2 := by nlinarith
    have h := mul_le_mul_of_nonneg_right hx2 (pow_nonneg hX0 4)
    nlinarith [show X ^ 2 * X ^ 4 = X ^ 6 by ring]
  have hnegative : X ^ 4 + (-Real.pi * X ^ 8 * R ^ 2 / 2) < 0 := by
    have hE0 : 0 ≤ X ^ 8 * R ^ 2 := by positivity
    have hpi := mul_nonneg (show 0 ≤ Real.pi - 3 by linarith [Real.pi_gt_three]) hE0
    have h4 : 0 < X ^ 4 := pow_pos hXpos _
    nlinarith
  calc
    _ ≤ Real.exp (X ^ 4) * Real.exp (-Real.pi * X ^ 8 * R ^ 2 / 2) :=
      mul_le_mul_of_nonneg_right hpower (Real.exp_pos _).le
    _ = Real.exp (X ^ 4 + (-Real.pi * X ^ 8 * R ^ 2 / 2)) := (Real.exp_add _ _).symm
    _ < 1 := Real.exp_lt_one_iff.mpr hnegative

theorem schmidt_recurrence_numeric_conditions (C e d N : ℕ) {A X R : ℝ}
    (hX : 2 ≤ X) (hd : (d : ℝ) + 1 ≤ X) (hp : (schmidtRecurrenceExponent e : ℝ) ≤ X)
    (hconst : 121 * Real.exp 10 ≤ X) (hc : schmidtDegreeConstant C e ≤ X)
    (hXR : 1 ≤ X * R) (hA : 1 ≤ A) (hAU : A ≤ (1 + 2 * X ^ 8) ^ d)
    (hN : X ^ (schmidtRecurrenceExponent e * (d + 1) ^ 2) ≤ N) :
    2 * schmidtMeanDenominator C e d A * A < 2 * (N : ℝ) + 1 ∧
      2 * schmidtMeanDenominator C e d A *
        (Real.exp (-Real.pi * X ^ 8 * R ^ 2 / 2) * (2 : ℝ) ^ d * A) < 1 := by
  obtain ⟨hAX, hMX⟩ := schmidt_recurrence_mass_bounds d hX hd hconst hA hAU
  have hbound := schmidt_recurrence_denominator_bound C e d hX hA hc hAX hMX
  have hD0 := (schmidtMeanDenominator_pos C e d hA).le
  have hA0 : 0 ≤ A := by linarith
  constructor
  · have htwo : 1 ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    have hmul := mul_le_mul_of_nonneg_left htwo (show 0 ≤ 2 * schmidtMeanDenominator C e d A * A by positivity)
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  · have hmul := mul_le_mul_of_nonneg_right hbound
      (Real.exp_pos (-Real.pi * X ^ 8 * R ^ 2 / 2)).le
    have htail := monomial_recurrence_tail_budget (schmidtRecurrenceExponent e) d hX hd hp hXR
    nlinarith

end Erdos3

end

section

namespace Erdos3

theorem schmidtRecurrenceBase_bounds (C e : ℕ) :
    2 ≤ schmidtRecurrenceBase C e ∧ 121 * Real.exp 10 ≤ schmidtRecurrenceBase C e ∧
      schmidtDegreeConstant C e ≤ schmidtRecurrenceBase C e ∧
      (schmidtRecurrenceExponent e : ℝ) ≤ schmidtRecurrenceBase C e := by
  have hc : 0 ≤ schmidtDegreeConstant C e := by unfold schmidtDegreeConstant; positivity
  have hp : (0 : ℝ) ≤ schmidtRecurrenceExponent e := Nat.cast_nonneg _
  have he := (Real.exp_pos (10 : ℝ)).le
  unfold schmidtRecurrenceBase
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem PolynomialIntervalPowerBound.simultaneous_monomial_recurrence_at_scale
    {j C e : ℕ} (hW : PolynomialIntervalPowerBound (j + 1) C e)
    {ι : Type*} [Fintype ι] (α : ι → ℝ) (N : ℕ) {X R : ℝ}
    (hX : schmidtRecurrenceBase C e ≤ X) (hd : (Fintype.card ι : ℝ) + 1 ≤ X)
    (hR : 0 < R) (hXR : 1 ≤ X * R)
    (hN : X ^ (schmidtRecurrenceExponent e * (Fintype.card ι + 1) ^ 2) ≤ N) :
    ∃ q : ℕ, 0 < q ∧ q ≤ N ∧ ∃ m : ι → ℤ, ∀ i, |(q : ℝ) ^ (j + 1) * α i - m i| < R := by
  obtain ⟨h2, hconst, hc, hp⟩ := schmidtRecurrenceBase_bounds C e
  have hXpos : 0 < X := by linarith
  have ht : 0 < X ^ 8 := pow_pos hXpos _
  let a : EuclideanSpace ℝ ι := WithLp.toLp 2 α
  have hA := normalizedLatticeGaussian_origin_ge_one (standardEuclideanLattice ι) ht
  have hAU := standardLatticeGaussian_origin_bound_s2 ι ht
  obtain ⟨hlength, htail⟩ := schmidt_recurrence_numeric_conditions C e (Fintype.card ι) N
    (h2.trans hX) hd (hp.trans hX) (hconst.trans hX) (hc.trans hX) hXR hA hAU hN
  obtain ⟨q, hq, hqN, v, hv, hclose⟩ := hW.lattice_recurrence (standardEuclideanLattice ι) a N ht hR.le
    (by simpa only [finrank_euclideanSpace] using hlength)
    (by simpa only [finrank_euclideanSpace] using htail)
  choose m hm using (mem_standardEuclideanLattice ι v).mp hv
  refine ⟨q, hq, hqN, m, fun i => ?_⟩
  calc
    |(q : ℝ) ^ (j + 1) * α i - m i| = ‖((q : ℝ) ^ (j + 1) • a - v) i‖ := by
      change _ = |(q : ℝ) ^ (j + 1) * α i - v i|
      rw [hm i]
    _ ≤ ‖(q : ℝ) ^ (j + 1) • a - v‖ := PiLp.norm_apply_le _ i
    _ < R := hclose

theorem PolynomialIntervalPowerBound.simultaneous_monomial_recurrence_s2_oai
    {j C e : ℕ} (hW : PolynomialIntervalPowerBound (j + 1) C e)
    {ι : Type*} [Fintype ι] (α : ι → ℝ) (N : ℕ) {R : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1)
    (hN : (schmidtRecurrenceBase C e * ((Fintype.card ι : ℝ) + 1) / R) ^
      (schmidtRecurrenceExponent e * (Fintype.card ι + 1) ^ 2) ≤ N) :
    ∃ q : ℕ, 0 < q ∧ q ≤ N ∧ ∃ m : ι → ℤ, ∀ i, |(q : ℝ) ^ (j + 1) * α i - m i| < R := by
  have hK := (schmidtRecurrenceBase_bounds C e).1
  have hd : (1 : ℝ) ≤ (Fintype.card ι : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) (Fintype.card ι); linarith
  have hK0 : 0 ≤ schmidtRecurrenceBase C e := by linarith
  have hd0 : 0 ≤ (Fintype.card ι : ℝ) + 1 := by linarith
  have hbase : schmidtRecurrenceBase C e ≤
      schmidtRecurrenceBase C e * ((Fintype.card ι : ℝ) + 1) / R := by
    apply (le_div_iff₀ hR).mpr
    nlinarith
  have hdim : (Fintype.card ι : ℝ) + 1 ≤
      schmidtRecurrenceBase C e * ((Fintype.card ι : ℝ) + 1) / R := by
    apply (le_div_iff₀ hR).mpr
    nlinarith
  have hprod : 1 ≤ (schmidtRecurrenceBase C e * ((Fintype.card ι : ℝ) + 1) / R) * R := by
    rw [div_mul_cancel₀ _ hR.ne']
    nlinarith
  exact hW.simultaneous_monomial_recurrence_at_scale α N hbase hdim hR hprod hN

end Erdos3

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Erdos3.PolynomialIntervalPowerBound.simultaneous_monomial_recurrence_s2_oai.{u_1} := @OAI.Erdos3.PolynomialIntervalPowerBound.simultaneous_monomial_recurrence_s2_oai.{u_1}
