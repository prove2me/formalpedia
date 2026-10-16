-- Prove2me | solution 1 for OAI.Erdos3.exists_uniform_coordinate_partition_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-16T01:27:13.135426+00:00
-- url     : https://prove2.me/submissions/cae91340-4e5f-40fe-ab0f-27dc1df0659c

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B110
import Definitions.Def_OAIErdos3B1324
import Theorems.Thm_OAI_Erdos3_PolynomialIntervalPowerBound_lattice_recurrence

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonDenominatorMultiples
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem exists_common_denominator_subset (D : Finset ℤ) (q : ℤ → ℕ) {K : ℕ}
    (hK : 0 < K) (hq : ∀ h ∈ D, 0 < q h ∧ q h ≤ K)
    {μ : ℝ} (hsize : (K : ℝ) * μ ≤ D.card) :
    ∃ q₀ : ℕ, 0 < q₀ ∧ q₀ ≤ K ∧ ∃ E : Finset ℤ,
      E ⊆ D ∧ μ ≤ E.card ∧ ∀ h ∈ E, q h = q₀ := by
  have hmap : ∀ h ∈ D, q h ∈ Finset.Icc 1 K := by
    intro h hh
    exact Finset.mem_Icc.mpr ⟨(hq h hh).1, (hq h hh).2⟩
  have hnonempty : (Finset.Icc 1 K).Nonempty :=
    ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hK⟩⟩
  have hcard : (Finset.Icc 1 K).card = K := by simp
  obtain ⟨q₀, hq₀, hlarge⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    hmap hnonempty (by simpa only [hcard, nsmul_eq_mul] using hsize)
  refine ⟨q₀, (Finset.mem_Icc.mp hq₀).1, (Finset.mem_Icc.mp hq₀).2,
    D.filter (fun h => q h = q₀), Finset.filter_subset _ _, hlarge, ?_⟩
  intro h hh
  exact (Finset.mem_filter.mp hh).2

theorem varying_denominator_multiples_approximation (D : Finset ℤ)
    (q : ℤ → ℕ) (p : ℤ → ℤ) {H K Q : ℕ} {α ε ρ : ℝ}
    (hH : 0 < H) (hK : 0 < K) (hQ : 0 < Q) (hρ : 0 < ρ) (hε : 0 ≤ ε)
    (hρQ : 4 ≤ ρ * Q) (hρH : 4 ≤ ρ * H)
    (hsmall : 16 * ((Q : ℝ) * ε) ≤ ρ) (hcap : (Q : ℝ) * ε ≤ 1)
    (hsize : (K : ℝ) * (ρ * H) ≤ D.card)
    (hD : ∀ h ∈ D, |h| ≤ (H : ℤ))
    (hq : ∀ h ∈ D, 0 < q h ∧ q h ≤ K)
    (hclose : ∀ h ∈ D, |(q h : ℝ) * ((h : ℝ) * α) - p h| ≤ ε) :
    ∃ r : ℕ, 0 < r ∧ r ≤ Q * K ∧ ∃ m : ℤ,
      |(r : ℝ) * α - m| ≤ 24 * Q * ε / (ρ * H) := by
  obtain ⟨q₀, hq₀, hq₀K, E, hED, hE, hconstant⟩ :=
    exists_common_denominator_subset D q hK hq hsize
  have hclose' : ∀ h ∈ E, |(h : ℝ) * ((q₀ : ℝ) * α) - p h| ≤ ε := by
    intro h hh
    have he := hclose h (hED hh)
    rw [hconstant h hh] at he
    rw [mul_left_comm]
    exact he
  obtain ⟨r, hr, hrQ, m, hm⟩ := many_multiples_rational_approximation E p
    hH hQ hρ hε hρQ hρH hsmall hcap hE (fun h hh => hD h (hED hh)) hclose'
  refine ⟨r * q₀, Nat.mul_pos hr hq₀, Nat.mul_le_mul hrQ hq₀K, m, ?_⟩
  simpa only [Nat.cast_mul, mul_assoc] using hm

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProgressionPartitionComposition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

attribute [instance] FiniteProgressionPartition.labelFintype

namespace FiniteProgressionPartition

variable {N : ℕ} (P : FiniteProgressionPartition N)

end FiniteProgressionPartition
end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

namespace FiniteProgressionPartition

variable {N : ℕ} (P : FiniteProgressionPartition N)

theorem restrict_length_le (M : ℕ) (hMN : M ≤ N) (i : P.Label) :
    (P.restrict M hMN).length i ≤ P.length i := truncatedProgressionLength_le _ _ _ _

end FiniteProgressionPartition
end Erdos3

end

section

namespace Erdos3.FiniteProgressionPartition

end Erdos3.FiniteProgressionPartition

end

section

namespace Erdos3.FiniteProgressionPartition

variable {N : ℕ} (P : FiniteProgressionPartition N)

theorem bind_card (Q : ∀ i : P.Label, FiniteProgressionPartition (P.length i)) :
    Fintype.card (P.bind Q).Label = ∑ i : P.Label, Fintype.card (Q i).Label := Fintype.card_sigma

theorem bind_card_mul_le (Q : ∀ i : P.Label, FiniteProgressionPartition (P.length i))
    (H B : ℕ) (hQ : ∀ i, Fintype.card (Q i).Label * H ≤ B) :
    Fintype.card (P.bind Q).Label * H ≤ Fintype.card P.Label * B := by
  classical
  rw [P.bind_card, Finset.sum_mul]
  simpa using Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset P.Label)) => hQ i)

end Erdos3.FiniteProgressionPartition

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

open Module

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end Erdos3

end

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

section

namespace Erdos3

open MeasureTheory Module

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I]

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module _root_.Set

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I]

end Erdos3

end

section

namespace Erdos3

open Module Submodule MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module _root_.Set

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I]

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

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ShiftDifferenceCount
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem finite_support_shift_sum {V : Type*} [AddCommMonoid V]
    (Q T : Finset G) (f : G → V) (s : G)
    (hsupport : ∀ x, x ∉ Q → f x = 0)
    (hcover : ∀ x ∈ Q, x + s ∈ T) :
    (∑ x ∈ T, f (x - s)) = ∑ x ∈ Q, f x := by
  have hsub : Q.image (fun x => x + s) ⊆ T := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact hcover y hy
  calc
    _ = ∑ x ∈ Q.image (fun x => x + s), f (x - s) := by
      symm
      apply Finset.sum_subset hsub
      intro x _ hx
      apply hsupport
      intro hq
      exact hx (Finset.mem_image.mpr ⟨x - s, hq, sub_add_cancel x s⟩)
    _ = ∑ x ∈ Q, f x := by
      rw [Finset.sum_image (fun _ _ _ _ h => add_right_cancel h)]
      simp

theorem finite_support_shift_pair (Q T : Finset G) (f : G → ℂ) (s t : G)
    (hsupport : ∀ x, x ∉ Q → f x = 0)
    (hcover : ∀ x ∈ Q, x + s ∈ T) :
    (∑ x ∈ T, f (x - s) * star (f (x - t))) = shiftCorrelation Q f (s - t) := by
  have hid (x : G) : x - s + (s - t) = x - t := by abel
  simpa only [shiftCorrelation, hid] using finite_support_shift_sum Q T
    (fun x => f x * star (f (x + (s - t)))) s
    (fun x hx => by rw [hsupport x hx, zero_mul]) hcover

theorem norm_sum_sq_le_card_mul_sum_norm_sq {ι : Type*} (S : Finset ι) (f : ι → ℂ) :
    ‖∑ x ∈ S, f x‖ ^ 2 ≤ (S.card : ℝ) * ∑ x ∈ S, ‖f x‖ ^ 2 := by
  have hnorm := norm_sum_le S f
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun x => ‖f x‖) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans (by simpa only [mul_comm] using hcs)

theorem finite_shift_energy (Q T S : Finset G) (f : G → ℂ)
    (hsupport : ∀ x, x ∉ Q → f x = 0)
    (hcover : ∀ s ∈ S, ∀ x ∈ Q, x + s ∈ T) :
    (∑ x ∈ T, ‖∑ s ∈ S, f (x - s)‖ ^ 2) =
      ∑ s ∈ S, ∑ t ∈ S, (shiftCorrelation Q f (s - t)).re := by
  have heq : (∑ x ∈ T, (∑ s ∈ S, f (x - s)) * star (∑ t ∈ S, f (x - t))) =
      ∑ s ∈ S, ∑ t ∈ S, shiftCorrelation Q f (s - t) := by
    conv_rhs => rw [Finset.sum_comm]
    simp only [star_sum, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t ht
    exact finite_support_shift_pair Q T f t s hsupport (hcover t ht)
  simpa only [Complex.re_sum, mul_star_re_eq_norm_sq] using congrArg Complex.re heq

theorem finite_shift_cauchy (Q T S : Finset G) (f : G → ℂ)
    (hsupport : ∀ x, x ∉ Q → f x = 0)
    (hcover : ∀ s ∈ S, ∀ x ∈ Q, x + s ∈ T) :
    (S.card : ℝ) ^ 2 * ‖∑ x ∈ Q, f x‖ ^ 2 ≤
      (T.card : ℝ) * ∑ s ∈ S, ∑ t ∈ S, (shiftCorrelation Q f (s - t)).re := by
  have hsum : (∑ x ∈ T, ∑ s ∈ S, f (x - s)) = (S.card : ℂ) * ∑ x ∈ Q, f x := by
    rw [Finset.sum_comm]
    have hshift : ∀ s ∈ S, (∑ x ∈ T, f (x - s)) = ∑ x ∈ Q, f x :=
      fun s hs => finite_support_shift_sum Q T f s hsupport (hcover s hs)
    rw [Finset.sum_congr rfl hshift]
    simp
  have hcs := norm_sum_sq_le_card_mul_sum_norm_sq T (fun x => ∑ s ∈ S, f (x - s))
  rw [hsum, norm_mul, Complex.norm_natCast, mul_pow,
    finite_shift_energy Q T S f hsupport hcover] at hcs
  exact hcs

theorem finite_shift_cauchy_norm (Q T S : Finset G) (f : G → ℂ)
    (hsupport : ∀ x, x ∉ Q → f x = 0)
    (hcover : ∀ s ∈ S, ∀ x ∈ Q, x + s ∈ T) :
    (S.card : ℝ) ^ 2 * ‖∑ x ∈ Q, f x‖ ^ 2 ≤
      (T.card : ℝ) * ∑ s ∈ S, ∑ t ∈ S, ‖shiftCorrelation Q f (s - t)‖ := by
  apply (finite_shift_cauchy Q T S f hsupport hcover).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro s _
  exact Finset.sum_le_sum (fun t _ => Complex.re_le_norm _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem shiftCorrelation_norm_le (Q : Finset G) (f : G → ℂ)
    (hsupport : ∀ x, x ∉ Q → f x = 0) (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1) (h : G) :
    ‖shiftCorrelation Q f h‖ ≤ Q.card := by
  have hall (x : G) : ‖f x‖ ≤ 1 := by
    by_cases hx : x ∈ Q
    · exact hf x hx
    · simp only [hsupport x hx, norm_zero, zero_le_one]
  unfold shiftCorrelation
  calc
    _ ≤ ∑ x ∈ Q, ‖f x * star (f (x + h))‖ := norm_sum_le _ _
    _ ≤ ∑ _x ∈ Q, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      rw [norm_mul, norm_star]
      exact (mul_le_mul (hf x hx) (hall (x + h)) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ = (Q.card : ℝ) := by simp

theorem many_large_shift_pairs (Q T S : Finset G) (f : G → ℂ)
    (hQ : Q.Nonempty) (hsupport : ∀ x, x ∉ Q → f x = 0)
    (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1)
    (hcover : ∀ s ∈ S, ∀ x ∈ Q, x + s ∈ T)
    (hT : T.card ≤ 2 * Q.card)
    {δ : ℝ} (hδ : 0 < δ) (hshift : 8 ≤ δ ^ 2 * S.card)
    (hscore : δ * Q.card ≤ ‖∑ x ∈ Q, f x‖) :
    δ ^ 2 * (S.card : ℝ) ^ 2 / 8 ≤
      (((S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧
        δ ^ 2 * Q.card / 8 ≤ ‖shiftCorrelation Q f (p.1 - p.2)‖)).card : ℝ) := by
  let good := (S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧
    δ ^ 2 * Q.card / 8 ≤ ‖shiftCorrelation Q f (p.1 - p.2)‖)
  have hN : (0 : ℝ) < Q.card := by exact_mod_cast hQ.card_pos
  have hS : S.Nonempty := by
    by_contra hs
    rw [Finset.not_nonempty_iff_eq_empty.mp hs] at hshift
    norm_num at hshift
  have hH : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hTR : (T.card : ℝ) ≤ 2 * Q.card := by exact_mod_cast hT
  have hterm (p : G × G) : ‖shiftCorrelation Q f (p.1 - p.2)‖ ≤
      δ ^ 2 * Q.card / 8 +
        (if p.1 ≠ p.2 ∧ δ ^ 2 * Q.card / 8 ≤ ‖shiftCorrelation Q f (p.1 - p.2)‖
          then (Q.card : ℝ) else 0) +
        (if p.1 = p.2 then (Q.card : ℝ) else 0) := by
    have hbound := shiftCorrelation_norm_le Q f hsupport hf (p.1 - p.2)
    have hnonneg : 0 ≤ δ ^ 2 * Q.card / 8 := by positivity
    by_cases heq : p.1 = p.2
    · simp only [heq, ne_eq, not_true_eq_false, false_and, ite_false, ite_true]
      rw [heq] at hbound
      linarith
    · by_cases hlarge : δ ^ 2 * Q.card / 8 ≤ ‖shiftCorrelation Q f (p.1 - p.2)‖
      · simp only [heq, ne_eq, not_false_eq_true, hlarge, and_self, ite_true, ite_false]
        linarith
      · simp only [heq, ne_eq, not_false_eq_true, hlarge, and_false, ite_false]
        linarith
  have hgood : (∑ p ∈ S ×ˢ S,
      if p.1 ≠ p.2 ∧ δ ^ 2 * Q.card / 8 ≤ ‖shiftCorrelation Q f (p.1 - p.2)‖
        then (Q.card : ℝ) else 0) = good.card * (Q.card : ℝ) := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, good]
  have hdiag : (∑ p ∈ S ×ˢ S, if p.1 = p.2 then (Q.card : ℝ) else 0) =
      (S.card : ℝ) * Q.card := by
    rw [Finset.sum_product]
    simp only [Finset.sum_ite_eq]
    rw [Finset.sum_congr rfl (fun s hs => by rw [if_pos hs])]
    simp
  have hsum : (∑ s ∈ S, ∑ t ∈ S, ‖shiftCorrelation Q f (s - t)‖) ≤
      (S.card : ℝ) ^ 2 * (δ ^ 2 * Q.card / 8) + good.card * (Q.card : ℝ) + S.card * Q.card := by
    rw [← Finset.sum_product S S (fun p : G × G => ‖shiftCorrelation Q f (p.1 - p.2)‖)]
    apply (Finset.sum_le_sum (fun p (_ : p ∈ S ×ˢ S) => hterm p)).trans_eq
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hgood, hdiag]
    simp only [Finset.sum_const, Finset.card_product, Nat.cast_mul, nsmul_eq_mul]
    ring
  have hupper := (finite_shift_cauchy_norm Q T S f hsupport hcover).trans
    (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _))
  have hupper' := hupper.trans (mul_le_mul_of_nonneg_right hTR
    (show 0 ≤ (S.card : ℝ) ^ 2 * (δ ^ 2 * Q.card / 8) + good.card * (Q.card : ℝ) +
      S.card * Q.card by positivity))
  have hlower := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (mul_nonneg hδ.le hN.le) hscore 2) (sq_nonneg (S.card : ℝ))
  have hcombined := hlower.trans hupper'
  have hshift' := mul_le_mul_of_nonneg_right hshift
    (mul_nonneg hH.le (sq_nonneg (Q.card : ℝ)))
  change δ ^ 2 * (S.card : ℝ) ^ 2 / 8 ≤ (good.card : ℝ)
  by_contra hnone
  have hsmall := mul_lt_mul_of_pos_right (lt_of_not_ge hnone) (sq_pos_of_pos hN)
  have hpos : 0 < (S.card : ℝ) * (Q.card : ℝ) ^ 2 := mul_pos hH (sq_pos_of_pos hN)
  nlinarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem card_pairs_le_card_differences_mul (S : Finset G) (A : Finset (G × G))
    (hA : A ⊆ S ×ˢ S) :
    A.card ≤ (A.image (fun p => p.1 - p.2)).card * S.card := by
  let f (p : G × G) := (p.1 - p.2, p.2)
  have hf : Function.Injective f := by
    intro p q heq
    have hdiff := congrArg Prod.fst heq
    have hsecond := congrArg Prod.snd heq
    change p.1 - p.2 = q.1 - q.2 at hdiff
    change p.2 = q.2 at hsecond
    apply Prod.ext
    · rw [hsecond] at hdiff
      have := congrArg (fun x : G => x + q.2) hdiff
      simpa only [sub_add_cancel] using this
    · exact hsecond
  have hsub : A.image f ⊆ (A.image (fun p => p.1 - p.2)) ×ˢ S := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨q, hq, rfl⟩, (Finset.mem_product.mp (hA hq)).2⟩
  calc
    _ = (A.image f).card := (Finset.card_image_of_injective A hf).symm
    _ ≤ ((A.image (fun p => p.1 - p.2)) ×ˢ S).card := Finset.card_le_card hsub
    _ = _ := Finset.card_product _ _

theorem many_large_shift_differences (Q T S : Finset G) (f : G → ℂ)
    (hQ : Q.Nonempty) (hsupport : ∀ x, x ∉ Q → f x = 0)
    (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1)
    (hcover : ∀ s ∈ S, ∀ x ∈ Q, x + s ∈ T)
    (hT : T.card ≤ 2 * Q.card)
    {δ : ℝ} (hδ : 0 < δ) (hshift : 8 ≤ δ ^ 2 * S.card)
    (hscore : δ * Q.card ≤ ‖∑ x ∈ Q, f x‖) :
    ∃ D : Finset G, δ ^ 2 * S.card / 8 ≤ (D.card : ℝ) ∧
      ∀ h ∈ D, h ≠ 0 ∧ (∃ s ∈ S, ∃ t ∈ S, h = s - t) ∧
        δ ^ 2 * Q.card / 8 ≤ ‖shiftCorrelation Q f h‖ := by
  let good := (S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧
    δ ^ 2 * Q.card / 8 ≤ ‖shiftCorrelation Q f (p.1 - p.2)‖)
  let D := good.image (fun p => p.1 - p.2)
  have hS : S.Nonempty := by
    by_contra hs
    rw [Finset.not_nonempty_iff_eq_empty.mp hs] at hshift
    norm_num at hshift
  have hH : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hpairs : δ ^ 2 * (S.card : ℝ) ^ 2 / 8 ≤ (good.card : ℝ) :=
    many_large_shift_pairs Q T S f hQ hsupport hf hcover hT hδ hshift hscore
  have hcount : (good.card : ℝ) ≤ (D.card : ℝ) * S.card := by
    exact_mod_cast card_pairs_le_card_differences_mul S good (Finset.filter_subset _ _)
  refine ⟨D, ?_, ?_⟩
  · apply (mul_le_mul_iff_left₀ hH).mp
    calc
      _ = δ ^ 2 * (S.card : ℝ) ^ 2 / 8 := by ring
      _ ≤ (D.card : ℝ) * S.card := hpairs.trans hcount
  · intro h hh
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hh
    obtain ⟨hpS, hpne, hpbound⟩ := Finset.mem_filter.mp hp
    obtain ⟨hps, hpt⟩ := Finset.mem_product.mp hpS
    exact ⟨sub_ne_zero.mpr hpne, ⟨p.1, hps, p.2, hpt, rfl⟩, hpbound⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerIntervalReindex
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem sum_integerInterval_eq_range {M : Type*} [AddCommMonoid M]
    (f : ℤ → M) (u v : ℤ) :
    (∑ x ∈ Finset.Ico u v, f x) =
      ∑ n ∈ Finset.range (v - u).toNat, f (u + (n : ℤ)) := by
  symm
  apply Finset.sum_bij (fun (n : ℕ) _ => u + (n : ℤ))
  · intro n hn
    simp only [Finset.mem_range] at hn
    simp only [Finset.mem_Ico]
    omega
  · intro n hn m hm heq
    omega
  · intro x hx
    simp only [Finset.mem_Ico] at hx
    refine ⟨(x - u).toNat, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro n hn
    rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerIntervalShift
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem many_large_interval_shifts (f : ℤ → ℂ) {N H : ℕ}
    (hN : 0 < N) (hH : H ≤ N)
    (hsupport : ∀ x, x ∉ Finset.Ico (0 : ℤ) (N : ℤ) → f x = 0)
    (hf : ∀ x ∈ Finset.Ico (0 : ℤ) (N : ℤ), ‖f x‖ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hshift : 8 ≤ δ ^ 2 * H)
    (hscore : δ * N ≤ ‖∑ x ∈ Finset.Ico (0 : ℤ) (N : ℤ), f x‖) :
    ∃ D : Finset ℤ, δ ^ 2 * H / 8 ≤ (D.card : ℝ) ∧
      ∀ h ∈ D, h ≠ 0 ∧ |h| < (H : ℤ) ∧
        δ ^ 2 * N / 8 ≤ ‖shiftCorrelation (Finset.Ico (0 : ℤ) (N : ℤ)) f h‖ := by
  let Q := Finset.Ico (0 : ℤ) (N : ℤ)
  let S := Finset.Ico (0 : ℤ) (H : ℤ)
  let T := Finset.Ico (0 : ℤ) ((N + H : ℕ) : ℤ)
  have hQ : Q.Nonempty := Finset.nonempty_Ico.mpr (by exact_mod_cast hN)
  have hcover : ∀ s ∈ S, ∀ x ∈ Q, x + s ∈ T := by
    intro s hs x hx
    simp only [S, Q, T, Finset.mem_Ico, Nat.cast_add] at *
    omega
  have hT : T.card ≤ 2 * Q.card := by
    simp only [T, Q, Int.card_Ico, sub_zero, Int.toNat_natCast]
    omega
  obtain ⟨D, hD, hgood⟩ := many_large_shift_differences Q T S f hQ hsupport hf hcover hT
    hδ (by simpa only [S, Int.card_Ico, sub_zero, Int.toNat_natCast] using hshift)
    (by simpa only [Q, Int.card_Ico, sub_zero, Int.toNat_natCast] using hscore)
  refine ⟨D, ?_, ?_⟩
  · simpa only [S, Int.card_Ico, sub_zero, Int.toNat_natCast] using hD
  · intro h hh
    obtain ⟨hne, ⟨s, hs, t, ht, rfl⟩, hcorr⟩ := hgood h hh
    refine ⟨hne, ?_, ?_⟩
    · simp only [S, Finset.mem_Ico] at hs ht
      rw [abs_lt]
      omega
    · simpa only [Q, Int.card_Ico, sub_zero, Int.toNat_natCast] using hcorr

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.WeylStepScales
namespace OAI

section

namespace Erdos3

theorem weylNextBudget_bounds (k B K : ℕ) :
    2 * K ≤ weylNextBudget k B K ∧
    32 * B ^ 2 ≤ weylNextBudget k B K ∧
    128 * B ^ 2 * K ≤ weylNextBudget k B K ∧
    65536 * 2 ^ k * B ^ 4 * K ^ 3 ≤ weylNextBudget k B K ∧
    128 * (k + 1) * B ^ 2 * K ^ 2 ≤ weylNextBudget k B K ∧
    98304 * 2 ^ k * B ^ 4 * K ^ 3 ≤ weylNextBudget k B K := by
  unfold weylNextBudget
  omega

theorem weylBudget_pos (j : ℕ) {B : ℕ} (hB : 0 < B) : 0 < weylBudget j B := by
  cases j with
  | zero => exact hB
  | succ j =>
    have hb : 0 < 32 * B ^ 2 := by positivity
    exact lt_of_lt_of_le hb (weylNextBudget_bounds _ _ _).2.1

end Erdos3

end

section

namespace Erdos3

open Polynomial
open scoped BigOperators

theorem weylBudgetPolynomial_eval (j B : ℕ) :
    (weylBudgetPolynomial j).eval B = weylBudget j B := by
  induction j generalizing B with
  | zero => simp only [weylBudgetPolynomial, eval_X, weylBudget]
  | succ j ih =>
    simp only [weylBudgetPolynomial, eval_add, eval_mul, eval_pow, eval_C, eval_X,
      eval_comp, ih, weylBudget, weylNextBudget]

theorem natPolynomial_eval_le_one_mul_pow (P : Polynomial ℕ) {B : ℕ} (hB : 1 ≤ B) :
    P.eval B ≤ P.eval 1 * B ^ P.natDegree := by
  rw [eval_eq_sum_range, eval_eq_sum_range]
  simp only [one_pow, mul_one, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  exact Nat.mul_le_mul_left _ (pow_le_pow_right' hB (by simpa only [Finset.mem_range,
    Nat.lt_succ_iff] using hi))

theorem weylBudget_polynomial_bound (j : ℕ) :
    ∃ A d : ℕ, 0 < A ∧ 0 < d ∧ ∀ B : ℕ, 1 ≤ B → weylBudget j B ≤ A * B ^ d := by
  let P := weylBudgetPolynomial j
  refine ⟨P.eval 1, P.natDegree + 1, ?_, by omega, ?_⟩
  · change 0 < (weylBudgetPolynomial j).eval 1
    rw [weylBudgetPolynomial_eval]
    exact weylBudget_pos j (by decide)
  · intro B hB
    rw [← weylBudgetPolynomial_eval]
    exact (natPolynomial_eval_le_one_mul_pow P hB).trans
      (Nat.mul_le_mul_left _ (pow_le_pow_right' hB (by omega)))

end Erdos3

end

section

namespace Erdos3

theorem weylShiftDenom_pos {B K : ℕ} (hB : 0 < B) (hK : 0 < K) :
    0 < weylShiftDenom B K := by unfold weylShiftDenom; positivity

theorem weylShiftDensity_pos {B K : ℕ} (hB : 0 < B) (hK : 0 < K) :
    0 < weylShiftDensity B K := by unfold weylShiftDensity; positivity

theorem weylShiftDensity_le_one {B K : ℕ} (hB : 0 < B) (hK : 0 < K) :
    weylShiftDensity B K ≤ 1 := by
  have hBR : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
  unfold weylShiftDensity
  apply (div_le_one (by positivity : 0 < 32 * (B : ℝ) ^ 2 * K)).mpr
  have hsq : (1 : ℝ) ≤ (B : ℝ) ^ 2 := one_le_pow₀ hBR
  nlinarith only [mul_le_mul hsq hKR (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg (B : ℝ))]

theorem weylShiftDensity_mul_denom {B K : ℕ} (hB : 0 < B) (hK : 0 < K) :
    weylShiftDensity B K * weylShiftDenom B K = 4 := by
  unfold weylShiftDensity weylShiftDenom
  push_cast
  have hb : (B : ℝ) ≠ 0 := by positivity
  have hk : (K : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem weylShiftDensity_card_bound {N B K : ℕ} (hB : 0 < B) (hK : 0 < K)
    (hN : 2 ≤ N) :
    (K : ℝ) * (weylShiftDensity B K * N) ≤ (1 / (B : ℝ)) ^ 2 * (N / 2 : ℕ) / 8 := by
  have hb : (B : ℝ) ≠ 0 := by positivity
  have hk : (K : ℝ) ≠ 0 := by positivity
  have hn : (N : ℝ) ≤ 4 * (N / 2 : ℕ) := by exact_mod_cast (show N ≤ 4 * (N / 2) by omega)
  have hleft : (K : ℝ) * (weylShiftDensity B K * N) = (N : ℝ) / (32 * (B : ℝ) ^ 2) := by
    unfold weylShiftDensity
    field_simp
  have hright : (1 / (B : ℝ)) ^ 2 * (N / 2 : ℕ) / 8 =
      (4 * (N / 2 : ℕ) : ℝ) / (32 * (B : ℝ) ^ 2) := by field_simp; ring
  rw [hleft, hright]
  exact div_le_div_of_nonneg_right hn (by positivity)

theorem weylShiftError_small {k N B K : ℕ} (hk : 0 < k) (hB : 0 < B)
    (hK : 0 < K) (hN : 0 < N)
    (hlarge : 65536 * 2 ^ k * B ^ 4 * K ^ 3 ≤ N) :
    16 * ((weylShiftDenom B K : ℝ) * weylShiftError k N K) ≤ weylShiftDensity B K := by
  have hBR : (B : ℝ) ≠ 0 := by positivity
  have hKR : (K : ℝ) ≠ 0 := by positivity
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpower : (N : ℝ) ≤ (N : ℝ) ^ k := le_self_pow₀ hNR hk.ne'
  have hl : (65536 : ℝ) * 2 ^ k * (B : ℝ) ^ 4 * (K : ℝ) ^ 3 ≤ (N : ℝ) ^ k :=
    (by exact_mod_cast hlarge : (65536 : ℝ) * 2 ^ k * (B : ℝ) ^ 4 * (K : ℝ) ^ 3 ≤ N).trans hpower
  unfold weylShiftDensity
  apply (le_div_iff₀ (by positivity : 0 < 32 * (B : ℝ) ^ 2 * K)).mpr
  have hid : 16 * ((weylShiftDenom B K : ℝ) * weylShiftError k N K) *
      (32 * (B : ℝ) ^ 2 * K) =
      (65536 * (2 : ℝ) ^ k * (B : ℝ) ^ 4 * (K : ℝ) ^ 3) / (N : ℝ) ^ k := by
    unfold weylShiftDenom weylShiftError
    push_cast
    ring
  rw [hid]
  exact (div_le_one (by positivity : 0 < (N : ℝ) ^ k)).mpr hl

theorem weylShiftError_of_half_length {k N M K : ℕ} (hM : 0 < M) (hN : 0 < N)
    (hhalf : N ≤ 2 * M) :
    (K : ℝ) / (M : ℝ) ^ k ≤ weylShiftError k N K := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hh : (N : ℝ) ≤ 2 * (M : ℝ) := by exact_mod_cast hhalf
  have hp := pow_le_pow_left₀ hNR.le hh k
  rw [mul_pow] at hp
  unfold weylShiftError
  apply (div_le_div_iff₀ (by positivity : 0 < (M : ℝ) ^ k) (by positivity : 0 < (N : ℝ) ^ k)).mpr
  have hm := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (α := ℝ) K)
  nlinarith only [hm]

theorem weylShiftError_output (k N B K : ℕ) :
    24 * weylShiftDenom B K * weylShiftError k N K / (weylShiftDensity B K * N) =
      (98304 * (2 : ℝ) ^ k * (B : ℝ) ^ 4 * (K : ℝ) ^ 3) / (N : ℝ) ^ (k + 1) := by
  unfold weylShiftDenom weylShiftError weylShiftDensity
  push_cast
  rw [pow_succ]
  field_simp
  ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SchmidtShortDualVector
namespace OAI

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

theorem norm_linear_interval_sum (u v : ℤ) (a b : ℝ) :
    ‖∑ x ∈ Finset.Ico u v,
      character (((x : ℝ) * a + b : ℝ) : CircleFourier.Circle)‖ =
      ‖geometricCharacterSum (v - u).toNat (a : CircleFourier.Circle)‖ := by
  rw [sum_integerInterval_eq_range]
  have heq (n : ℕ) :
      character ((((u + (n : ℤ) : ℤ) : ℝ) * a + b : ℝ) : CircleFourier.Circle) =
        character (((u : ℝ) * a + b : ℝ) : CircleFourier.Circle) *
          character (n • (a : CircleFourier.Circle)) := by
    have hr : ((u + (n : ℤ) : ℤ) : ℝ) * a + b = (u : ℝ) * a + b + n • a := by
      simp only [Int.cast_add, Int.cast_natCast, nsmul_eq_mul]
      ring
    rw [hr, AddCircle.coe_add, AddCircle.coe_nsmul, character_add]
  simp_rw [heq]
  rw [← Finset.mul_sum, norm_mul, norm_character, one_mul]
  rfl

theorem linear_interval_inverse (u v : ℤ) (a b : ℝ) {S : ℝ} (hS : 0 < S)
    (hlarge : S ≤ ‖∑ x ∈ Finset.Ico u v,
      character (((x : ℝ) * a + b : ℝ) : CircleFourier.Circle)‖) :
    integerDistance (a : CircleFourier.Circle) ≤ 1 / (2 * S) := by
  rw [norm_linear_interval_sum] at hlarge
  have h := two_mul_integerDistance_mul_norm_geometricCharacterSum_le_one
    (v - u).toNat (a : CircleFourier.Circle)
  have hmul := mul_le_mul_of_nonneg_left hlarge
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (integerDistance_nonneg (a : CircleFourier.Circle)))
  apply (le_div_iff₀ (by positivity : 0 < 2 * S)).mpr
  nlinarith only [h, hmul]

theorem polynomial_linear_eval (P : Polynomial ℝ) (hP : P.natDegree ≤ 1) (x : ℝ) :
    P.eval x = x * P.coeff 1 + P.coeff 0 := by
  conv_lhs => rw [Polynomial.eq_X_add_C_of_natDegree_le_one hP]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  ring

theorem linear_polynomial_interval_inverse (P : Polynomial ℝ) (hP : P.natDegree ≤ 1)
    (u v : ℤ) {S : ℝ} (hS : 0 < S)
    (hlarge : S ≤ ‖∑ x ∈ Finset.Ico u v,
      character ((P.eval (x : ℝ) : ℝ) : CircleFourier.Circle)‖) :
    integerDistance (P.coeff 1 : CircleFourier.Circle) ≤ 1 / (2 * S) := by
  simp_rw [polynomial_linear_eval P hP] at hlarge
  exact linear_interval_inverse u v (P.coeff 1) (P.coeff 0) hS hlarge

end Erdos3

end

section

namespace Erdos3

open Polynomial
open scoped NNReal

theorem affine_comp_top_coeff (P : Polynomial ℝ) {k : ℕ} (hP : P.natDegree ≤ k)
    (a q : ℝ) (hq : q ≠ 0) :
    (P.comp (C q * X + C a)).coeff k = P.coeff k * q ^ k := by
  have hdeg : (P.comp (C q * X + C a)).natDegree = P.natDegree := by
    rw [natDegree_comp, natDegree_linear hq, mul_one]
  by_cases heq : P.natDegree = k
  · have hc := coeff_comp_degree_mul_degree (p := P) (q := C q * X + C a)
      (by rw [natDegree_linear hq]; decide)
    rw [natDegree_linear hq, mul_one, leadingCoeff_linear hq, heq] at hc
    simpa only [Polynomial.leadingCoeff, heq] using hc
  · have hlt : P.natDegree < k := lt_of_le_of_ne hP heq
    rw [coeff_eq_zero_of_natDegree_lt (hdeg ▸ hlt),
      coeff_eq_zero_of_natDegree_lt hlt, zero_mul]

theorem affinePhaseRemainder_degree (P : Polynomial ℝ) {k : ℕ}
    (hP : P.natDegree ≤ k + 1) (a q : ℝ) (hq : q ≠ 0) :
    (affinePhaseRemainder P (k + 1) a q).natDegree ≤ k := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  by_cases heq : n = k + 1
  · simp [affinePhaseRemainder, heq]
  · rw [affinePhaseRemainder, erase_ne _ heq]
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_comp, natDegree_linear hq, mul_one]
    omega

theorem affinePhaseRemainder_eval (P : Polynomial ℝ) {k : ℕ}
    (hP : P.natDegree ≤ k) (a q x : ℝ) (hq : q ≠ 0) :
    P.eval (a + q * x) = (affinePhaseRemainder P k a q).eval x +
      (P.coeff k * q ^ k) * x ^ k := by
  have heq := congrArg (fun Q : Polynomial ℝ => Q.eval x)
    (monomial_add_erase (P.comp (C q * X + C a)) k)
  rw [eval_add, eval_monomial, affine_comp_top_coeff P hP a q hq] at heq
  simpa only [affinePhaseRemainder, eval_comp, eval_add, eval_mul, eval_C, eval_X,
    add_comm (q * x) a, add_comm] using heq.symm

theorem affinePhaseRemainder_error (P : Polynomial ℝ) {k H : ℕ}
    (hP : P.natDegree ≤ k) (a q : ℝ) (hq : q ≠ 0) (m : ℤ) {τ : ℝ}
    (hτ : 0 ≤ τ) (happrox : |P.coeff k * q ^ k - m| ≤ τ)
    {j : ℕ} (hj : j < H) :
    |P.eval (a + q * j) -
      ((affinePhaseRemainder P k a q).eval (j : ℝ) + ((m * (j : ℤ) ^ k : ℤ) : ℝ))| ≤
      τ * (H : ℝ) ^ k := by
  have hjR : (j : ℝ) ≤ H := by exact_mod_cast hj.le
  calc
    _ = |(P.coeff k * q ^ k - m) * (j : ℝ) ^ k| := by
      rw [affinePhaseRemainder_eval P hP a q j hq]
      push_cast
      congr 1
      ring
    _ = |P.coeff k * q ^ k - m| * (j : ℝ) ^ k := by
      rw [abs_mul, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ j) k)]
    _ ≤ τ * (H : ℝ) ^ k :=
      mul_le_mul happrox (pow_le_pow_left₀ (Nat.cast_nonneg _) hjR k)
        (pow_nonneg (Nat.cast_nonneg _) _) hτ

end Erdos3

end

section

namespace Erdos3

open Polynomial

theorem polynomialShiftDifference_eval (P : Polynomial ℝ) (h x : ℝ) :
    (polynomialShiftDifference P h).eval x = P.eval x - P.eval (x + h) := by
  simp only [polynomialShiftDifference, eval_sub, eval_comp, eval_add, eval_X, eval_C]

theorem polynomialShiftDifference_degree (P : Polynomial ℝ) {k : ℕ}
    (hP : P.natDegree ≤ k + 1) (h : ℝ) :
    (polynomialShiftDifference P h).natDegree ≤ k := by
  have htop : (P.comp (X + C h)).coeff (k + 1) = P.coeff (k + 1) := by
    simpa only [C_1, one_mul, one_pow, mul_one] using
      affine_comp_top_coeff P hP h 1 one_ne_zero
  have hdeg : (P.comp (X + C h)).natDegree = P.natDegree := by
    rw [natDegree_comp, natDegree_X_add_C, mul_one]
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [polynomialShiftDifference, coeff_sub]
  by_cases heq : n = k + 1
  · rw [heq, htop, sub_self]
  · have hlt : P.natDegree < n := by omega
    rw [coeff_eq_zero_of_natDegree_lt hlt,
      coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt hlt), sub_self]

theorem affine_shift_next_coeff (P : Polynomial ℝ) {k : ℕ}
    (hP : P.natDegree ≤ k + 1) (h : ℝ) :
    (P.comp (X + C h)).coeff k = P.coeff k + (k + 1 : ℝ) * h * P.coeff (k + 1) := by
  have hD : (hasseDeriv k P).natDegree ≤ 1 := by
    apply (natDegree_hasseDeriv_le P k).trans
    omega
  rw [← taylor_apply, taylor_coeff]
  conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hD]
  simp only [eval_add, eval_mul, eval_C, eval_X, hasseDeriv_coeff, zero_add,
    Nat.choose_self, Nat.cast_one, one_mul]
  rw [Nat.add_comm 1 k, Nat.choose_succ_self_right]
  push_cast
  ring

theorem polynomialShiftDifference_top_coeff (P : Polynomial ℝ) {k : ℕ}
    (hP : P.natDegree ≤ k + 1) (h : ℝ) :
    (polynomialShiftDifference P h).coeff k = -(k + 1 : ℝ) * h * P.coeff (k + 1) := by
  rw [polynomialShiftDifference, coeff_sub, affine_shift_next_coeff P hP h]
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

theorem intervalPolynomialPhase_support (N : ℕ) (P : Polynomial ℝ) (x : ℤ)
    (hx : x ∉ Finset.Ico (0 : ℤ) (N : ℤ)) : intervalPolynomialPhase N P x = 0 := by
  simp only [intervalPolynomialPhase, if_neg hx]

theorem intervalPolynomialPhase_norm_le (N : ℕ) (P : Polynomial ℝ) (x : ℤ) :
    ‖intervalPolynomialPhase N P x‖ ≤ 1 := by
  unfold intervalPolynomialPhase
  split_ifs <;> simp only [norm_character, norm_zero, le_refl, zero_le_one]

theorem intervalPolynomialPhase_sum (N : ℕ) (P : Polynomial ℝ) :
    (∑ x ∈ Finset.Ico (0 : ℤ) (N : ℤ), intervalPolynomialPhase N P x) =
      ∑ x ∈ Finset.Ico (0 : ℤ) (N : ℤ), character ((P.eval (x : ℝ) : ℝ) : CircleFourier.Circle) := by
  apply Finset.sum_congr rfl
  intro x hx
  simp only [intervalPolynomialPhase, if_pos hx]

theorem integerInterval_overlap (N : ℕ) (h : ℤ) :
    (Finset.Ico (0 : ℤ) (N : ℤ)).filter (fun x => x + h ∈ Finset.Ico (0 : ℤ) (N : ℤ)) =
      Finset.Ico (max 0 (-h)) (min (N : ℤ) ((N : ℤ) - h)) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_Ico, max_le_iff, lt_min_iff]
  omega

theorem intervalPolynomialPhase_correlation (N : ℕ) (P : Polynomial ℝ) (h : ℤ) :
    shiftCorrelation (Finset.Ico (0 : ℤ) (N : ℤ)) (intervalPolynomialPhase N P) h =
      ∑ x ∈ Finset.Ico (max 0 (-h)) (min (N : ℤ) ((N : ℤ) - h)),
        character (((polynomialShiftDifference P (h : ℝ)).eval (x : ℝ) : ℝ) : CircleFourier.Circle) := by
  rw [← integerInterval_overlap, Finset.sum_filter]
  unfold shiftCorrelation
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hxh : x + h ∈ Finset.Ico (0 : ℤ) (N : ℤ)
  · simp only [intervalPolynomialPhase, if_pos hx, if_pos hxh,
      polynomialShiftDifference_eval, Int.cast_add]
    rw [AddCircle.coe_sub, sub_eq_add_neg, character_add, character_neg]
  · simp only [intervalPolynomialPhase, if_pos hx, if_neg hxh,
      star_zero, mul_zero]

theorem integerInterval_overlap_card_lower (N H : ℕ) (h : ℤ)
    (hh : |h| < (H : ℤ)) :
    N - H ≤ (Finset.Ico (max 0 (-h)) (min (N : ℤ) ((N : ℤ) - h))).card := by
  simp only [Int.card_Ico]
  have hbounds := abs_lt.mp hh
  omega

theorem many_polynomial_weyl_shifts (P : Polynomial ℝ) {k N H : ℕ}
    (hP : P.natDegree ≤ k + 1) (hN : 0 < N) (hH : H ≤ N)
    {δ : ℝ} (hδ : 0 < δ) (hshift : 8 ≤ δ ^ 2 * H)
    (hscore : δ * N ≤ ‖∑ x ∈ Finset.Ico (0 : ℤ) (N : ℤ),
      character ((P.eval (x : ℝ) : ℝ) : CircleFourier.Circle)‖) :
    ∃ D : Finset ℤ, δ ^ 2 * H / 8 ≤ (D.card : ℝ) ∧
      ∀ h ∈ D, h ≠ 0 ∧ |h| < (H : ℤ) ∧
        ∃ R : Polynomial ℝ, R.natDegree ≤ k ∧
          R.coeff k = -(k + 1 : ℝ) * (h : ℝ) * P.coeff (k + 1) ∧
          N - H ≤ (Finset.Ico (max 0 (-h)) (min (N : ℤ) ((N : ℤ) - h))).card ∧
          δ ^ 2 * N / 8 ≤ ‖∑ x ∈ Finset.Ico (max 0 (-h)) (min (N : ℤ) ((N : ℤ) - h)),
            character ((R.eval (x : ℝ) : ℝ) : CircleFourier.Circle)‖ := by
  obtain ⟨D, hD, hgood⟩ := many_large_interval_shifts (intervalPolynomialPhase N P)
    hN hH (intervalPolynomialPhase_support N P)
    (fun x _ => intervalPolynomialPhase_norm_le N P x) hδ hshift
    (by rwa [intervalPolynomialPhase_sum])
  refine ⟨D, hD, ?_⟩
  intro h hh
  obtain ⟨hne, hbound, hcorr⟩ := hgood h hh
  refine ⟨hne, hbound, polynomialShiftDifference P (h : ℝ),
    polynomialShiftDifference_degree P hP (h : ℝ),
    polynomialShiftDifference_top_coeff P hP (h : ℝ),
    integerInterval_overlap_card_lower N H h hbound, ?_⟩
  rwa [intervalPolynomialPhase_correlation] at hcorr

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open Polynomial CircleFourier

theorem polynomial_translate_degree (P : Polynomial ℝ) (u : ℝ) :
    (P.comp (X + C u)).natDegree = P.natDegree := by
  rw [natDegree_comp, natDegree_X_add_C, mul_one]

theorem polynomial_translate_top_coeff (P : Polynomial ℝ) {k : ℕ}
    (hP : P.natDegree ≤ k) (u : ℝ) :
    (P.comp (X + C u)).coeff k = P.coeff k := by
  simpa only [C_1, one_mul, one_pow, mul_one] using affine_comp_top_coeff P hP u 1 one_ne_zero

theorem polynomial_interval_sum_translate (P : Polynomial ℝ) (u v : ℤ) :
    (∑ x ∈ Finset.Ico u v, character ((P.eval (x : ℝ) : ℝ) : CircleFourier.Circle)) =
      ∑ x ∈ Finset.Ico (0 : ℤ) ((v - u).toNat : ℤ),
        character (((P.comp (X + C (u : ℝ))).eval (x : ℝ) : ℝ) : CircleFourier.Circle) := by
  rw [sum_integerInterval_eq_range, sum_integerInterval_eq_range]
  simp only [sub_zero, Int.toNat_natCast, zero_add]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Int.cast_add, Int.cast_natCast, eval_comp, eval_add, eval_X, eval_C]
  rw [add_comm (n : ℝ) (u : ℝ)]

theorem integerInterval_overlap_card_le (N : ℕ) (h : ℤ) :
    (Finset.Ico (max 0 (-h)) (min (N : ℤ) ((N : ℤ) - h))).card ≤ N := by
  rw [← integerInterval_overlap]
  have hh := Finset.card_filter_le (Finset.Ico (0 : ℤ) (N : ℤ))
    (fun x => x + h ∈ Finset.Ico (0 : ℤ) (N : ℤ))
  simpa only [Int.card_Ico, sub_zero, Int.toNat_natCast] using hh

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

theorem leadingWeylBound_one {B : ℕ} (hB : 1 ≤ B) : LeadingWeylBound 1 B B := by
  intro P hP N hN hBN hscore
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have h := linear_polynomial_interval_inverse P hP 0 N (div_pos hNR hBR) hscore
  rw [integerDistance_coe] at h
  refine ⟨1, by decide, hB, round (P.coeff 1), ?_⟩
  simp only [Nat.cast_one, one_mul, pow_one]
  calc
    _ ≤ 1 / (2 * ((N : ℝ) / B)) := h
    _ = (B : ℝ) / (2 * N) := by field_simp
    _ ≤ (B : ℝ) / N := div_le_div_of_nonneg_left hBR.le hNR (by linarith)

theorem LeadingWeylBound.on_integer_interval {k B K : ℕ} (hbound : LeadingWeylBound k B K)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ k) (u v : ℤ)
    (hM : 0 < (v - u).toNat) (hKM : K ≤ (v - u).toNat)
    (hscore : ((v - u).toNat : ℝ) / B ≤
      ‖∑ x ∈ Finset.Ico u v, character ((P.eval (x : ℝ) : ℝ) : CircleFourier.Circle)‖) :
    ∃ q : ℕ, 0 < q ∧ q ≤ K ∧ ∃ p : ℤ,
      |(q : ℝ) * P.coeff k - p| ≤ (K : ℝ) / ((v - u).toNat : ℝ) ^ k := by
  rw [polynomial_interval_sum_translate] at hscore
  obtain ⟨q, hq, hqK, p, hp⟩ := hbound (P.comp (Polynomial.X + Polynomial.C (u : ℝ)))
    (by rwa [polynomial_translate_degree]) (v - u).toNat hM hKM hscore
  rw [polynomial_translate_top_coeff P hP] at hp
  exact ⟨q, hq, hqK, p, hp⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

theorem LeadingWeylBound.step {k B K : ℕ} (hk : 0 < k) (hB : 2 ≤ B) (hK : 0 < K)
    (ih : LeadingWeylBound k (8 * B ^ 2) K) :
    LeadingWeylBound (k + 1) B (weylNextBudget k B K) := by
  classical
  intro P hP N hN hbudget hscore
  obtain ⟨hb₁, hb₂, hb₃, hb₄, hb₅, hb₆⟩ := weylNextBudget_bounds k B K
  have h₂K := hb₁.trans hbudget
  have h₃₂ := hb₂.trans hbudget
  have hQbound := hb₃.trans hbudget
  have hsmallbound := hb₄.trans hbudget
  have hBpos : 0 < B := by omega
  have hBsq : 0 < B ^ 2 := pow_pos hBpos 2
  have hN₂ : 2 ≤ N := by omega
  have hBR : (0 : ℝ) < B := Nat.cast_pos.mpr hBpos
  have hKR : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hδ : 0 < 1 / (B : ℝ) := one_div_pos.mpr hBR
  have hshift : 8 ≤ (1 / (B : ℝ)) ^ 2 * (N / 2 : ℕ) := by
    have hh : 8 * B ^ 2 ≤ N / 2 := by omega
    have hhR : (8 : ℝ) * (B : ℝ) ^ 2 ≤ (N / 2 : ℕ) := by exact_mod_cast hh
    calc
      8 ≤ (N / 2 : ℕ) / (B : ℝ) ^ 2 := (le_div_iff₀ (by positivity)).mpr hhR
      _ = (1 / (B : ℝ)) ^ 2 * (N / 2 : ℕ) := by field_simp
  have hscore' : (1 / (B : ℝ)) * N ≤ ‖polynomialExponentialSum P N‖ := by
    have hid : (1 / (B : ℝ)) * N = (N : ℝ) / B := by ring
    rwa [hid]
  obtain ⟨D, hDsize, hDgood⟩ := many_polynomial_weyl_shifts P hP hN (Nat.div_le_self N 2)
    hδ hshift hscore'
  let α : ℝ := -(k + 1 : ℝ) * P.coeff (k + 1)
  have hchoice : ∀ h : ℤ, ∃ (q : ℕ) (p : ℤ), (0 < q ∧ q ≤ K) ∧
      (h ∈ D → |(q : ℝ) * ((h : ℝ) * α) - p| ≤ weylShiftError k N K) := by
    intro h
    by_cases hh : h ∈ D
    · obtain ⟨hne, hshort, R, hR, hcoeff, hlength, hlarge⟩ := hDgood h hh
      let u := max 0 (-h)
      let v := min (N : ℤ) ((N : ℤ) - h)
      let M := (v - u).toNat
      have hML : N - N / 2 ≤ M := by
        simpa only [Int.card_Ico] using hlength
      have hKM : K ≤ M := by omega
      have hM : 0 < M := lt_of_lt_of_le hK hKM
      have hMN : M ≤ N := by
        simpa only [Int.card_Ico] using integerInterval_overlap_card_le N h
      have hMbias : (M : ℝ) / (8 * B ^ 2 : ℕ) ≤
          ‖∑ x ∈ Finset.Ico u v, character ((R.eval (x : ℝ) : ℝ) : CircleFourier.Circle)‖ := by
        calc
          _ ≤ (N : ℝ) / (8 * B ^ 2 : ℕ) :=
            div_le_div_of_nonneg_right (Nat.cast_le.mpr hMN) (by positivity)
          _ = (1 / (B : ℝ)) ^ 2 * N / 8 := by push_cast; field_simp
          _ ≤ _ := hlarge
      obtain ⟨q, hq, hqK, p, hp⟩ := ih.on_integer_interval R hR u v hM hKM hMbias
      refine ⟨q, p, ⟨hq, hqK⟩, fun _ => ?_⟩
      have hid : R.coeff k = (h : ℝ) * α := by rw [hcoeff]; dsimp [α]; ring
      rw [hid] at hp
      exact hp.trans (weylShiftError_of_half_length hM hN (by omega))
    · exact ⟨1, 0, ⟨by decide, hK⟩, fun hd => (hh hd).elim⟩
  choose q p hq hp using hchoice
  have hsmall := weylShiftError_small hk hBpos hK hN hsmallbound
  have hρ := weylShiftDensity_pos hBpos hK
  have hρone := weylShiftDensity_le_one hBpos hK
  have hρQ := weylShiftDensity_mul_denom hBpos hK
  have hρN : 4 ≤ weylShiftDensity B K * N := by
    rw [← hρQ]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hQbound) hρ.le
  obtain ⟨r, hr, hrQK, m, hm⟩ := varying_denominator_multiples_approximation D q p
    hN hK (weylShiftDenom_pos hBpos hK) hρ
    (by unfold weylShiftError; positivity) hρQ.ge hρN hsmall
    (by linarith only [hsmall, hρone])
    ((weylShiftDensity_card_bound hBpos hK hN₂).trans hDsize)
    (fun h hh => (hDgood h hh).2.1.le.trans (by exact_mod_cast Nat.div_le_self N 2))
    (fun h _ => hq h) hp
  refine ⟨(k + 1) * r, Nat.mul_pos (by omega) hr, ?_, -m, ?_⟩
  · calc
      (k + 1) * r ≤ (k + 1) * (weylShiftDenom B K * K) := Nat.mul_le_mul_left _ hrQK
      _ = 128 * (k + 1) * B ^ 2 * K ^ 2 := by unfold weylShiftDenom; ring
      _ ≤ _ := hb₅
  · have hid : (((k + 1) * r : ℕ) : ℝ) * P.coeff (k + 1) - ((-m : ℤ) : ℝ) =
        -((r : ℝ) * α - m) := by dsimp [α]; push_cast; ring
    rw [hid, abs_neg]
    apply hm.trans
    rw [weylShiftError_output]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast hb₆

end Erdos3

end

section

namespace Erdos3

theorem leadingWeylBound_all_degrees (j : ℕ) {B : ℕ} (hB : 2 ≤ B) :
    LeadingWeylBound (j + 1) B (weylBudget j B) := by
  induction j generalizing B with
  | zero => exact leadingWeylBound_one (by omega)
  | succ j ih =>
    have hB' : 2 ≤ 8 * B ^ 2 := by
      have : 0 < B ^ 2 := pow_pos (by omega) 2
      omega
    exact LeadingWeylBound.step (by omega) hB (weylBudget_pos j (by omega)) (ih hB')

theorem polynomial_weyl_inverse (j : ℕ) (P : Polynomial ℝ) {B N : ℕ}
    (hB : 2 ≤ B) (hP : P.natDegree ≤ j + 1) (hN : 0 < N)
    (hsize : weylBudget j B ≤ N)
    (hscore : (N : ℝ) / B ≤ ‖polynomialExponentialSum P N‖) :
    ∃ q : ℕ, 0 < q ∧ q ≤ weylBudget j B ∧ ∃ p : ℤ,
      |(q : ℝ) * P.coeff (j + 1) - p| ≤ (weylBudget j B : ℝ) / (N : ℝ) ^ (j + 1) :=
  leadingWeylBound_all_degrees j hB P hP N hN hsize hscore

end Erdos3

end

section

namespace Erdos3

theorem exists_reciprocal_bias_integer {δ : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) :
    ∃ B : ℕ, 2 ≤ B ∧ (B : ℝ) ≤ 3 / δ ∧ 1 ≤ δ * B := by
  let B := ⌈2 / δ⌉₊
  have hlo : 2 / δ ≤ (B : ℝ) := Nat.le_ceil _
  have hhi : (B : ℝ) < 2 / δ + 1 := Nat.ceil_lt_add_one (by positivity)
  have htwo : (2 : ℝ) ≤ 2 / δ := (le_div_iff₀ hδ).mpr (by linarith)
  refine ⟨B, by exact_mod_cast htwo.trans hlo, ?_, ?_⟩
  · have hb := mul_lt_mul_of_pos_right hhi hδ
    have hid : (2 / δ + 1) * δ = 2 + δ := by field_simp
    rw [hid] at hb
    apply (le_div_iff₀ hδ).mpr
    linarith
  · have hb := (div_le_iff₀ hδ).mp hlo
    nlinarith only [hb]

theorem polynomial_weyl_inverse_power_bound (j : ℕ) :
    ∃ C d : ℕ, 0 < C ∧ 0 < d ∧
      ∀ (P : Polynomial ℝ) (N : ℕ) (δ : ℝ),
        P.natDegree ≤ j + 1 → 0 < N → 0 < δ → δ ≤ 1 →
        (C : ℝ) ≤ δ ^ d * N →
        δ * N ≤ ‖polynomialExponentialSum P N‖ →
        ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ C / δ ^ d ∧ ∃ p : ℤ,
          |(q : ℝ) * P.coeff (j + 1) - p| ≤ C / (δ ^ d * (N : ℝ) ^ (j + 1)) := by
  obtain ⟨A, d, hA, hd, hbudget⟩ := weylBudget_polynomial_bound j
  refine ⟨A * 3 ^ d, d, by positivity, hd, ?_⟩
  intro P N δ hP hN hδ hδone hsize hscore
  obtain ⟨B, hB, hBupper, hBlower⟩ := exists_reciprocal_bias_integer hδ hδone
  have hBR : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hδd : 0 < δ ^ d := pow_pos hδ d
  have hbudgetR : (weylBudget j B : ℝ) ≤ (A * 3 ^ d : ℕ) / δ ^ d := by
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg B : (0 : ℝ) ≤ B) hBupper d
    have hbp : (weylBudget j B : ℝ) ≤ (A : ℝ) * (B : ℝ) ^ d := by
      exact_mod_cast hbudget B (by omega)
    apply hbp.trans
    have hm := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (α := ℝ) A)
    simpa only [div_pow, mul_div_assoc, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hm
  have hsizeB : weylBudget j B ≤ N := by
    have hs : ((A * 3 ^ d : ℕ) : ℝ) / δ ^ d ≤ N := (div_le_iff₀ hδd).mpr (by nlinarith only [hsize])
    exact_mod_cast hbudgetR.trans hs
  have hscoreB : (N : ℝ) / B ≤ ‖polynomialExponentialSum P N‖ := by
    apply le_trans _ hscore
    apply (div_le_iff₀ hBR).mpr
    have hm := mul_le_mul_of_nonneg_right hBlower hNR.le
    nlinarith only [hm]
  obtain ⟨q, hq, hqbound, p, hp⟩ := polynomial_weyl_inverse j P hB hP hN hsizeB hscoreB
  refine ⟨q, hq, (Nat.cast_le.mpr hqbound).trans hbudgetR, p, hp.trans ?_⟩
  calc
    (weylBudget j B : ℝ) / (N : ℝ) ^ (j + 1) ≤
        (((A * 3 ^ d : ℕ) : ℝ) / δ ^ d) / (N : ℝ) ^ (j + 1) :=
      div_le_div_of_nonneg_right hbudgetR (by positivity)
    _ = _ := by rw [div_div]

end Erdos3

end

section

namespace Erdos3

open Polynomial CircleFourier

theorem polynomial_weyl_inverse_power_interval (j : ℕ) :
    ∃ C d : ℕ, 0 < C ∧ 0 < d ∧ PolynomialIntervalPowerBound (j + 1) C d := by
  obtain ⟨C, d, hC, hd, hW⟩ := polynomial_weyl_inverse_power_bound j
  refine ⟨C, d, hC, hd, ?_⟩
  intro P u v δ hP hN hδ hδone hsize hscore
  rw [polynomial_interval_sum_translate] at hscore
  obtain ⟨q, hq, hqbound, p, hp⟩ := hW (P.comp (X + Polynomial.C (u : ℝ)))
    (v - u).toNat δ (by rwa [polynomial_translate_degree]) hN hδ hδone hsize hscore
  rw [polynomial_translate_top_coeff P hP] at hp
  exact ⟨q, hq, hqbound, p, hp⟩

end Erdos3

end

section

namespace Erdos3

open Polynomial CircleFourier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

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

theorem standardLatticeGaussian_origin_bound {t : ℝ} (ht : 0 < t) :
    normalizedLatticeGaussian (standardEuclideanLattice ι) t 0 ≤ (1 + 2 * t) ^ Fintype.card ι := by
  rw [normalizedLatticeGaussian_zero_eq_dual _ ht, standardEuclideanLattice_self_dual]
  exact standardLatticeGaussian_mass_bound ι ht

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPartitionBudget
namespace OAI

section

namespace Erdos3

theorem polynomial_partition_exponent_step (k p w d : ℕ) :
    (p * (d + 1) ^ (2 * k)) * ((k + 3) * w * (d + 1) ^ 2 + 1) ≤
      (p * ((k + 3) * w + 1)) * (d + 1) ^ (2 * (k + 1)) := by
  have hd : 1 ≤ (d + 1) ^ 2 := one_le_pow₀ (by omega)
  have hfactor : (k + 3) * w * (d + 1) ^ 2 + 1 ≤
      ((k + 3) * w + 1) * (d + 1) ^ 2 := by nlinarith
  have h := Nat.mul_le_mul_left (p * (d + 1) ^ (2 * k)) hfactor
  have hid : (p * (d + 1) ^ (2 * k)) * (((k + 3) * w + 1) * (d + 1) ^ 2) =
      (p * ((k + 3) * w + 1)) * (d + 1) ^ (2 * (k + 1)) := by
    rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]
    ring
  rwa [hid] at h

theorem polynomial_partition_error_step (k : ℕ) {L : ℝ} (hL : 0 ≤ L)
    {H T : ℕ} (hH : 0 < H) (hHT : H ≤ T) :
    L / T + (k : ℝ) * L / H ≤ ((k + 1 : ℕ) : ℝ) * L / H := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hHTR : (H : ℝ) ≤ T := by exact_mod_cast hHT
  have h := div_le_div_of_nonneg_left hL hHR hHTR
  calc
    _ ≤ L / H + (k : ℝ) * L / H := add_le_add h le_rfl
    _ = _ := by push_cast; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialCoordinatePartition
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

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

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

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
  have hAU := standardLatticeGaussian_origin_bound ι ht
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

theorem PolynomialIntervalPowerBound.simultaneous_monomial_recurrence
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

theorem simultaneous_monomial_recurrence (j : ℕ) :
    ∃ (K : ℝ) (p : ℕ), 1 ≤ K ∧ 0 < p ∧
      ∀ (ι : Type*) [Fintype ι] (α : ι → ℝ) (N : ℕ) (R : ℝ), 0 < R → R ≤ 1 →
        (K * ((Fintype.card ι : ℝ) + 1) / R) ^ (p * (Fintype.card ι + 1) ^ 2) ≤ N →
        ∃ q : ℕ, 0 < q ∧ q ≤ N ∧ ∃ m : ι → ℤ, ∀ i, |(q : ℝ) ^ (j + 1) * α i - m i| < R := by
  obtain ⟨C, e, hC, he, hW⟩ := polynomial_weyl_inverse_power_interval j
  refine ⟨schmidtRecurrenceBase C e, schmidtRecurrenceExponent e,
    (show 1 ≤ schmidtRecurrenceBase C e by linarith [(schmidtRecurrenceBase_bounds C e).1]), ?_, ?_⟩
  · unfold schmidtRecurrenceExponent
    omega
  · intro ι _ α N R hR hR1 hN
    exact hW.simultaneous_monomial_recurrence α N hR hR1 hN

end Erdos3

end

section

namespace Erdos3

open Polynomial

theorem PolynomialIntervalPowerBound.polynomial_coordinate_reduction
    {j C e : ℕ} (hW : PolynomialIntervalPowerBound (j + 1) C e)
    {ι : Type*} [Fintype ι] (P : ι → Polynomial ℝ)
    (hP : ∀ i, (P i).natDegree ≤ j + 1) (H : ℕ) (hH : 0 < H)
    (hsize : schmidtRecurrenceBase C e * ((Fintype.card ι : ℝ) + 1) ≤ H) :
    ∃ q : ℕ, 0 < q ∧
      q ≤ H ^ ((j + 3) * schmidtRecurrenceExponent e * (Fintype.card ι + 1) ^ 2) ∧
      ∃ m : ι → ℤ, ∀ a : ℝ, ∃ R : ι → Polynomial ℝ,
        (∀ i, (R i).natDegree ≤ j) ∧ ∀ n < H, ∀ i,
          |(P i).eval (a + q * n) -
            ((R i).eval (n : ℝ) + ((m i * (n : ℤ) ^ (j + 1) : ℤ) : ℝ))| ≤ 1 / (H : ℝ) := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  let τ := 1 / (H : ℝ) ^ (j + 2)
  let Q := H ^ ((j + 3) * schmidtRecurrenceExponent e * (Fintype.card ι + 1) ^ 2)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτ1 : τ ≤ 1 := by
    dsimp [τ]
    have hp : (1 : ℝ) ≤ (H : ℝ) ^ (j + 2) := one_le_pow₀ hH1
    simpa only [div_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hp
  have hbase : schmidtRecurrenceBase C e * ((Fintype.card ι : ℝ) + 1) / τ ≤ (H : ℝ) ^ (j + 3) := by
    dsimp [τ]
    rw [one_div, div_inv_eq_mul]
    exact (mul_le_mul_of_nonneg_right hsize (pow_nonneg hHR.le (j + 2))).trans_eq
      (pow_succ' (H : ℝ) (j + 2)).symm
  have hQ : (schmidtRecurrenceBase C e * ((Fintype.card ι : ℝ) + 1) / τ) ^
      (schmidtRecurrenceExponent e * (Fintype.card ι + 1) ^ 2) ≤ (Q : ℝ) := by
    have hnonneg : 0 ≤ schmidtRecurrenceBase C e * ((Fintype.card ι : ℝ) + 1) / τ := by
      have := (schmidtRecurrenceBase_bounds C e).1
      positivity
    have h := pow_le_pow_left₀ hnonneg hbase (schmidtRecurrenceExponent e * (Fintype.card ι + 1) ^ 2)
    simpa only [Q, Nat.cast_pow, ← pow_mul, Nat.mul_assoc] using h
  obtain ⟨q, hq, hqQ, m, hm⟩ := hW.simultaneous_monomial_recurrence
    (fun i => (P i).coeff (j + 1)) Q hτ hτ1 hQ
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  refine ⟨q, hq, hqQ, m, fun a => ⟨(fun i => affinePhaseRemainder (P i) (j + 1) a q),
    (fun i => affinePhaseRemainder_degree (P i) (hP i) a q hqR), ?_⟩⟩
  intro n hn i
  have hm' : |(P i).coeff (j + 1) * (q : ℝ) ^ (j + 1) - m i| ≤ τ := by
    simpa only [mul_comm] using (hm i).le
  have h := affinePhaseRemainder_error (P i) (hP i) a q hqR (m i) hτ.le hm' hn
  have hid : τ * (H : ℝ) ^ (j + 1) = 1 / (H : ℝ) := by
    dsimp [τ]
    rw [show j + 2 = (j + 1) + 1 by omega, pow_succ]
    field_simp
  simpa only [hid] using h

end Erdos3

end

section

namespace Erdos3

open Polynomial
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

universe u

open Polynomial

theorem polynomialCoordinatePartitionBound_zero : PolynomialCoordinatePartitionBound.{u} 0 1 1 := by
  intro ι _ P hP N H hH hscale hsize
  have hHN : H ≤ N := by simpa using hsize
  refine ⟨FiniteProgressionPartition.whole N, (fun _ j => (P j).coeff 0), (fun _ _ _ => 0), ?_, ?_⟩
  · have hcard : Fintype.card (FiniteProgressionPartition.whole N).Label = 1 := by
      let : Unique (FiniteProgressionPartition.whole N).Label := inferInstanceAs (Unique Unit)
      exact Fintype.card_unique
    rw [hcard]
    simpa using hHN
  · intro i n hn j
    have heq (x : ℝ) : (P j).eval x = (P j).coeff 0 := by
      simpa only [eval_C] using congrArg (fun Q : Polynomial ℝ => Q.eval x)
        (eq_C_of_natDegree_le_zero (hP j))
    rw [heq]
    simp

theorem PolynomialCoordinatePartitionBound.step {k p C e : ℕ} {K : ℝ}
    (hp : 0 < p) (hpartition : PolynomialCoordinatePartitionBound.{u} k K p)
    (hW : PolynomialIntervalPowerBound (k + 1) C e) :
    PolynomialCoordinatePartitionBound.{u} (k + 1) (max K (schmidtRecurrenceBase C e))
      (p * ((k + 3) * schmidtRecurrenceExponent e + 1)) := by
  intro ι _ P hP N H hH hscale hsize
  let d := Fintype.card ι
  let r := p * (d + 1) ^ (2 * k)
  let T := H ^ r
  have hr : 0 < r := Nat.mul_pos hp (pow_pos (by omega : 0 < d + 1) _)
  have hT : 0 < T := pow_pos hH _
  have hHT : H ≤ T := by
    simpa only [pow_one] using (show H ^ 1 ≤ H ^ r from pow_le_pow_right₀ (by omega) (by omega))
  have hscaleK : K * ((Fintype.card ι : ℝ) + 1) ≤ H :=
    (mul_le_mul_of_nonneg_right (le_max_left K _) (by positivity)).trans hscale
  have hscaleW : schmidtRecurrenceBase C e * ((Fintype.card ι : ℝ) + 1) ≤ T := by
    have h := (mul_le_mul_of_nonneg_right (le_max_right K _) (by positivity)).trans hscale
    exact h.trans (by exact_mod_cast hHT)
  have hsizeT : T ^ (((k + 3) * schmidtRecurrenceExponent e * (d + 1) ^ 2) + 1) ≤ N := by
    apply le_trans _ hsize
    change (H ^ r) ^ _ ≤ H ^ _
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by omega) (polynomial_partition_exponent_step k p (schmidtRecurrenceExponent e) d)
  obtain ⟨q, hq, hqbound, top, hreduce⟩ := hW.polynomial_coordinate_reduction P hP T hT hscaleW
  have hfit : q * T ≤ N := by
    calc
      _ ≤ T ^ ((k + 3) * schmidtRecurrenceExponent e * (d + 1) ^ 2) * T :=
        Nat.mul_le_mul_right T hqbound
      _ = T ^ (((k + 3) * schmidtRecurrenceExponent e * (d + 1) ^ 2) + 1) := (pow_succ _ _).symm
      _ ≤ N := hsizeT
  let B := FiniteProgressionPartition.blocks N q T hq hT
  have hBlength (i : B.Label) : B.length i ≤ T := truncatedProgressionLength_le _ _ _ _
  have hBcard : Fintype.card B.Label * T ≤ 2 * N := progressionBlock_label_count_mul_le_twice hfit
  choose R hRdegree hRerror using (fun i : B.Label => hreduce (B.start i : ℝ))
  have hlocal (i : B.Label) := hpartition ι (R i) (hRdegree i) T H hH hscaleK le_rfl
  choose Q z m hQcard hQerror using hlocal
  let child (i : B.Label) := (Q i).restrict (B.length i) (hBlength i)
  let result := B.bind child
  let index (i : result.Label) (n : ℕ) := (child i.1).start i.2 + (child i.1).step i.2 * n
  let integers (i : result.Label) (n : ℕ) (j : ι) : ℤ :=
    top j * (index i n : ℤ) ^ (k + 1) + m i.1 i.2 n j
  refine ⟨result, (fun i => z i.1 i.2), integers, ?_, ?_⟩
  · have hchild (i : B.Label) : Fintype.card (child i).Label * H ≤ 2 ^ k * T := hQcard i
    calc
      Fintype.card result.Label * H ≤ Fintype.card B.Label * (2 ^ k * T) :=
        B.bind_card_mul_le child H _ hchild
      _ = 2 ^ k * (Fintype.card B.Label * T) := by ring
      _ ≤ 2 ^ k * (2 * N) := Nat.mul_le_mul_left _ hBcard
      _ = 2 ^ (k + 1) * N := by rw [pow_succ]; ring
  · rintro ⟨i, j⟩ n hn a
    let s := index ⟨i, j⟩ n
    have hsB : s < B.length i := (child i).point_lt j hn
    have hsT : s < T := hsB.trans_le (hBlength i)
    have houter := hRerror i s hsT a
    have hnQ : n < (Q i).length j := hn.trans_le ((Q i).restrict_length_le _ (hBlength i) j)
    have hinner := hQerror i j n hnQ a
    change |(R i a).eval (s : ℝ) - m i j n a - z i j a| ≤ (k : ℝ) / H at hinner
    have hindex : result.start ⟨i, j⟩ + result.step ⟨i, j⟩ * n = B.start i + q * s := by
      change (B.start i + q * (child i).start j) + (q * (child i).step j) * n = _
      dsimp [s, index]
      ring
    rw [hindex]
    have houter' : |(P a).eval ((B.start i + q * s : ℕ) : ℝ) -
        ((R i a).eval (s : ℝ) + ((top a * (s : ℤ) ^ (k + 1) : ℤ) : ℝ))| ≤ 1 / (T : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_mul] using houter
    have hid : (P a).eval ((B.start i + q * s : ℕ) : ℝ) - integers ⟨i, j⟩ n a - z i j a =
        ((P a).eval ((B.start i + q * s : ℕ) : ℝ) -
          ((R i a).eval (s : ℝ) + ((top a * (s : ℤ) ^ (k + 1) : ℤ) : ℝ))) +
        ((R i a).eval (s : ℝ) - m i j n a - z i j a) := by
      dsimp [integers, s]
      push_cast
      ring
    rw [hid]
    calc
      _ ≤ |(P a).eval ((B.start i + q * s : ℕ) : ℝ) -
          ((R i a).eval (s : ℝ) + ((top a * (s : ℤ) ^ (k + 1) : ℤ) : ℝ))| +
          |(R i a).eval (s : ℝ) - m i j n a - z i j a| := abs_add_le _ _
      _ ≤ 1 / (T : ℝ) + (k : ℝ) / H := add_le_add houter' hinner
      _ ≤ _ := by simpa only [mul_one] using polynomial_partition_error_step k (by norm_num : (0 : ℝ) ≤ 1) hH hHT

theorem exists_polynomial_coordinate_partition_bound (k : ℕ) :
    ∃ (K : ℝ) (p : ℕ), 1 ≤ K ∧ 0 < p ∧ PolynomialCoordinatePartitionBound.{u} k K p := by
  induction k with
  | zero => exact ⟨1, 1, le_rfl, by decide, polynomialCoordinatePartitionBound_zero⟩
  | succ k ih =>
    obtain ⟨K, p, hK, hp, hpartition⟩ := ih
    obtain ⟨C, e, hC, he, hW⟩ := polynomial_weyl_inverse_power_interval k
    exact ⟨max K (schmidtRecurrenceBase C e), p * ((k + 3) * schmidtRecurrenceExponent e + 1),
      hK.trans (le_max_left _ _), Nat.mul_pos hp (by omega), hpartition.step hp hW⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UniformCoordinatePartition
namespace OAI

section

namespace Erdos3

universe u

theorem PolynomialCoordinatePartitionBound.mono {h p p' : ℕ} {K K' : ℝ}
    (hpartition : PolynomialCoordinatePartitionBound.{u} h K p)
    (hK : K ≤ K') (hp : p ≤ p') : PolynomialCoordinatePartitionBound.{u} h K' p' := by
  intro ι _ P hP N H hH hscale hsize
  apply hpartition ι P hP N H hH
  · exact (mul_le_mul_of_nonneg_right hK (by positivity)).trans hscale
  · exact (Nat.pow_le_pow_right hH (Nat.mul_le_mul_right _ hp)).trans hsize

theorem exists_uniform_coordinate_partition_bound_oai (s : ℕ) :
    ∃ (K : ℝ) (p : ℕ), 1 ≤ K ∧ 0 < p ∧
      ∀ h ≤ s, PolynomialCoordinatePartitionBound.{u} h K p := by
  induction s with
  | zero =>
    refine ⟨1, 1, le_rfl, by omega, ?_⟩
    intro h hh
    have heq : h = 0 := by omega
    subst h
    exact polynomialCoordinatePartitionBound_zero
  | succ s ih =>
    obtain ⟨K, p, hK, hp, hpart⟩ := ih
    obtain ⟨K', p', hK', hp', hpart'⟩ := exists_polynomial_coordinate_partition_bound.{u} (s + 1)
    refine ⟨max K K', p + p', hK.trans (le_max_left _ _), by omega, ?_⟩
    intro h hh
    by_cases hs : h ≤ s
    · exact (hpart h hs).mono (le_max_left _ _) (by omega)
    · have heq : h = s + 1 := by omega
      subst h
      exact hpart'.mono (le_max_right _ _) (by omega)

end Erdos3

end

end OAI

end

theorem solution.{u} : type_of% @OAI.Erdos3.exists_uniform_coordinate_partition_bound_oai.{u} := @OAI.Erdos3.exists_uniform_coordinate_partition_bound_oai.{u}
