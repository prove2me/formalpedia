-- Prove2me | solution 1 for OAI.Erdos3.standardLatticeGaussian_origin_bound_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T10:41:34.164649+00:00
-- url     : https://prove2.me/submissions/e0445942-07ff-4115-b8c1-f40e79e2ed3d

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B070
import Definitions.Def_OAIE3v2B080
import Definitions.Def_OAIE3v2B085

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

theorem normalizedLatticeGaussian_zero_eq_dual {t : ℝ} (ht : 0 < t) :
    normalizedLatticeGaussian Λ t 0 = latticeGaussianMass (euclideanDualLattice Λ) t⁻¹ 0 := by
  apply Complex.ofReal_injective
  rw [normalizedLatticeGaussian_poisson Λ ht]
  simp only [euclideanCharacter_zero, mul_one, latticeGaussianMass, Complex.ofReal_tsum,
    zero_sub, norm_neg, div_eq_mul_inv]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerGaussianGeometric
namespace OAI

section

namespace Erdos3

theorem hasSum_geometric_natAbs {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun n : ℤ => r ^ n.natAbs) ((1 - r)⁻¹ + r * (1 - r)⁻¹) := by
  have h := hasSum_geometric_of_lt_one hr hr1
  apply HasSum.of_nat_of_neg_add_one
  · simpa using h
  · convert! h.mul_left r using 1
    funext n
    have hn : (-((n : ℤ) + 1)).natAbs = n + 1 := by
      rw [Int.natAbs_neg, show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by omega]
      rfl
    rw [hn, pow_succ, mul_comm]

theorem integer_geometric_sum_bound {t : ℝ} (ht : 0 < t) :
    (∑' n : ℤ, (Real.exp (-1 / t)) ^ n.natAbs) ≤ 1 + 2 * t := by
  let r := Real.exp (-1 / t)
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) ht)
  rw [(hasSum_geometric_natAbs hr.le hr1).tsum_eq]
  have hs : 0 < 1 - r := by linarith
  have he : r * Real.exp (1 / t) = 1 := by
    dsimp [r]
    rw [← Real.exp_add, show -1 / t + 1 / t = 0 by ring, Real.exp_zero]
  have hlin : t * r + r ≤ t := by
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (1 / t)) (mul_pos ht hr).le
    have hl : t * r * (1 / t + 1) = t * r + r := by field_simp; ring
    have hu : t * r * Real.exp (1 / t) = t := by rw [mul_assoc, he, mul_one]
    rwa [hl, hu] at h
  have hid : (1 - r)⁻¹ + r * (1 - r)⁻¹ = (1 + r) / (1 - r) := by ring
  rw [hid]
  apply (div_le_iff₀ hs).mpr
  nlinarith

theorem integer_gaussian_le_geometric (n : ℤ) {t : ℝ} (ht : 0 < t) :
    Real.exp (-Real.pi / t * (n : ℝ) ^ 2) ≤ (Real.exp (-1 / t)) ^ n.natAbs := by
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hn : (n.natAbs : ℝ) ≤ (n.natAbs : ℝ) ^ 2 := by
    exact_mod_cast (show n.natAbs ≤ n.natAbs ^ 2 by simpa only [pow_two] using Nat.le_mul_self n.natAbs)
  have habs : (n.natAbs : ℝ) = |(n : ℝ)| := by simp
  rw [habs, sq_abs] at hn
  have hpi : |(n : ℝ)| ≤ Real.pi * (n : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ Real.pi - 1 by linarith [Real.pi_gt_three]) (sq_nonneg (n : ℝ))]
  have hmul := mul_le_mul_of_nonneg_right hpi (inv_nonneg.mpr ht.le)
  rw [habs]
  simp only [div_eq_mul_inv] at hmul ⊢
  nlinarith

theorem integer_gaussian_sum_bound {t : ℝ} (ht : 0 < t) (s : Finset ℤ) :
    (∑ n ∈ s, Real.exp (-Real.pi / t * (n : ℝ) ^ 2)) ≤ 1 + 2 * t := by
  have hr0 : 0 ≤ Real.exp (-1 / t) := (Real.exp_pos _).le
  have hr1 : Real.exp (-1 / t) < 1 :=
    Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) ht)
  calc
    _ ≤ ∑ n ∈ s, (Real.exp (-1 / t)) ^ n.natAbs :=
      Finset.sum_le_sum fun n _ => integer_gaussian_le_geometric n ht
    _ ≤ ∑' n : ℤ, (Real.exp (-1 / t)) ^ n.natAbs :=
      (hasSum_geometric_natAbs hr0 hr1).summable.sum_le_tsum s (fun n _ => by positivity)
    _ ≤ _ := integer_geometric_sum_bound ht

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteProductMassBound
namespace OAI

section

namespace Erdos3

theorem finite_product_mass_bound {ι κ : Type*} [Fintype ι]
    (f : κ → ℝ) (hf : ∀ x, 0 ≤ f x) {B : ℝ}
    (hB : ∀ s : Finset κ, ∑ x ∈ s, f x ≤ B) (s : Finset (ι → κ)) :
    (∑ z ∈ s, ∏ i, f (z i)) ≤ B ^ Fintype.card ι := by
  classical
  let T := s.biUnion (fun z => Finset.univ.image z)
  have hsub : s ⊆ Fintype.piFinset (fun _ : ι => T) := by
    intro z hz
    apply Fintype.mem_piFinset.mpr
    intro i
    exact Finset.mem_biUnion.mpr ⟨z, hz, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  calc
    _ ≤ ∑ z ∈ Fintype.piFinset (fun _ : ι => T), ∏ i, f (z i) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => Finset.prod_nonneg fun i _ => hf (z i))
    _ = (∑ x ∈ T, f x) ^ Fintype.card ι := by
      rw [Finset.sum_prod_piFinset]
      simp only [Finset.prod_const, Finset.card_univ]
    _ ≤ _ := pow_le_pow_left₀ (Finset.sum_nonneg fun x _ => hf x) (hB T) _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.StandardLatticeGaussianBound
namespace OAI

section

namespace Erdos3

variable (ι : Type*) [Fintype ι]

theorem standardLatticeGaussian_mass_bound {t : ℝ} (ht : 0 < t) :
    latticeGaussianMass (standardEuclideanLattice ι) t⁻¹ 0 ≤ (1 + 2 * t) ^ Fintype.card ι := by
  classical
  have hpoint (z : ι → ℤ) :
      Real.exp (-Real.pi * t⁻¹ * ‖(0 : EuclideanSpace ℝ ι) -
          (standardEuclideanEquiv ι z : EuclideanSpace ℝ ι)‖ ^ 2) =
        ∏ i, Real.exp (-Real.pi / t * (z i : ℝ) ^ 2) := by
    change Real.exp (-Real.pi * t⁻¹ * ‖(0 : EuclideanSpace ℝ ι) -
      (standardEuclideanPoint ι z : EuclideanSpace ℝ ι)‖ ^ 2) = _
    rw [zero_sub, norm_neg, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum, Real.exp_sum]
    simp only [standardEuclideanPoint_apply, div_eq_mul_inv]
  unfold latticeGaussianMass
  rw [← (standardEuclideanEquiv ι).tsum_eq]
  simp_rw [hpoint]
  apply Real.tsum_le_of_sum_le
  · intro z
    exact Finset.prod_nonneg fun i _ => (Real.exp_pos _).le
  · intro s
    exact finite_product_mass_bound (fun n : ℤ => Real.exp (-Real.pi / t * (n : ℝ) ^ 2))
      (fun _ => (Real.exp_pos _).le) (integer_gaussian_sum_bound ht) s

theorem standardLatticeGaussian_origin_bound_s2_oai {t : ℝ} (ht : 0 < t) :
    normalizedLatticeGaussian (standardEuclideanLattice ι) t 0 ≤ (1 + 2 * t) ^ Fintype.card ι := by
  rw [normalizedLatticeGaussian_zero_eq_dual _ ht, standardEuclideanLattice_self_dual]
  exact standardLatticeGaussian_mass_bound ι ht

end Erdos3

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Erdos3.standardLatticeGaussian_origin_bound_s2_oai.{u_1} := @OAI.Erdos3.standardLatticeGaussian_origin_bound_s2_oai.{u_1}
