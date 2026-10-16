-- Prove2me | solution 1 for OAI.Erdos3.PolynomialIntervalPowerBound.lattice_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-15T21:56:48.199441+00:00
-- url     : https://prove2.me/submissions/aef46e77-8f4e-4574-a64c-8fe0a85e4f43

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B110
import Definitions.Def_OAIErdos3B1324
import Theorems.Thm_OAI_Erdos3_exists_schmidt_dilated_mean_transfer

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeHyperplaneBasis
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem latticeHyperplane_span_top (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hspan : Submodule.span ℝ (Λ : Set E) = ⊤)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : f w = 1) :
    Submodule.span ℝ (latticeHyperplane Λ f : Set f.ker) = ⊤ := by
  let S := Submodule.span ℝ (latticeHyperplane Λ f : Set f.ker)
  have hall : ∀ x : E, hyperplaneRetraction f w hw x ∈ S := by
    intro x
    have hx : x ∈ Submodule.span ℝ (Λ : Set E) := by rw [hspan]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (hyperplaneRetraction_mem Λ f hint w hwΛ hw x hx)
    | zero => simpa only [map_zero] using S.zero_mem
    | add x y hx hy hpx hpy => simpa only [map_add] using S.add_mem hpx hpy
    | smul a x hx hpx => simpa only [map_smul] using S.smul_mem a hpx
  apply top_le_iff.mp
  intro x hx
  simpa only [hyperplaneRetraction_on_kernel] using hall (x : E)

theorem latticeHyperplane_isZLattice (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (f : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : f w = 1) :
    IsZLattice ℝ (latticeHyperplane Λ f) :=
  ⟨latticeHyperplane_span_top Λ f (IsZLattice.span_top (K := ℝ)) hint w hwΛ hw⟩

theorem hyperplane_finrank [FiniteDimensional ℝ E] (f : E →ₗ[ℝ] ℝ)
    (w : E) (hw : f w = 1) : Module.finrank ℝ f.ker + 1 = Module.finrank ℝ E := by
  have hsurj : Function.Surjective f := by
    intro a
    exact ⟨a • w, by simp only [map_smul, hw, smul_eq_mul, mul_one]⟩
  have h := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self] at h
  omega

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end Erdos3

end

section

namespace Erdos3

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem latticeGaussianMass_nonneg (Λ : Submodule ℤ E) (t : ℝ) (x : E) :
    0 ≤ latticeGaussianMass Λ t x := tsum_nonneg (fun _ => (Real.exp_pos _).le)

theorem latticeGaussianMass_pos (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    {t : ℝ} (ht : 0 < t) (x : E) : 0 < latticeGaussianMass Λ t x := by
  have h := (lattice_gaussian_summable Λ ht x).le_tsum (0 : Λ) (fun _ _ => (Real.exp_pos _).le)
  exact (Real.exp_pos _).trans_le h

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end Erdos3

end

section

namespace Erdos3

theorem integer_functional_image_generator {M : Type*} [AddCommGroup M] [Module ℤ M]
    (f : M →ₗ[ℤ] ℤ) (hf : f ≠ 0) :
    ∃ (m : ℤ) (w : M), m ≠ 0 ∧ f w = m ∧ ∀ x, ∃ n : ℤ, f x = n * m := by
  let m := Submodule.IsPrincipal.generator f.range
  have hspan : Submodule.span ℤ {m} = f.range := Submodule.IsPrincipal.span_singleton_generator _
  obtain ⟨w, hw⟩ := Submodule.IsPrincipal.generator_mem f.range
  have hm : m ≠ 0 := by
    intro hm
    have hz : f.range = ⊥ := by rw [← hspan, hm]; simp
    exact hf (LinearMap.range_eq_bot.mp hz)
  refine ⟨m, w, hm, hw, ?_⟩
  intro x
  have hx : f x ∈ Submodule.span ℤ {m} := by rw [hspan]; exact ⟨x, rfl⟩
  obtain ⟨n, hn⟩ := Submodule.mem_span_singleton.mp hx
  exact ⟨n, (by simpa only [smul_eq_mul] using hn.symm)⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem integralLatticeCoordinate_ne_zero (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hspan : Submodule.span ℝ (Λ : Set E) = ⊤)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ)) (hf : f ≠ 0) :
    integralLatticeCoordinate Λ f hint ≠ 0 := by
  intro hz
  apply hf
  apply LinearMap.ext_on hspan
  intro x hx
  have h := integralLatticeCoordinate_cast Λ f hint ⟨x, hx⟩
  rw [hz, LinearMap.zero_apply, Int.cast_zero] at h
  exact h.symm

theorem exists_primitive_lattice_functional (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hspan : Submodule.span ℝ (Λ : Set E) = ⊤)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ)) (hf : f ≠ 0) :
    ∃ (m : ℤ) (g : E →ₗ[ℝ] ℝ) (w : E), m ≠ 0 ∧
      f = (m : ℝ) • g ∧ (∀ x ∈ Λ, ∃ n : ℤ, g x = (n : ℝ)) ∧
      w ∈ Λ ∧ g w = 1 ∧ g.ker = f.ker := by
  obtain ⟨m, w, hm, hw, hmult⟩ := integer_functional_image_generator
    (integralLatticeCoordinate Λ f hint) (integralLatticeCoordinate_ne_zero Λ f hspan hint hf)
  let g : E →ₗ[ℝ] ℝ := (m : ℝ)⁻¹ • f
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hg (x : E) : g x = f x / m := by simp only [g, LinearMap.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hfw : f (w : E) = (m : ℝ) := by
    rw [← integralLatticeCoordinate_cast Λ f hint w, hw]
  refine ⟨m, g, w, hm, ?_, ?_, w.property, ?_, ?_⟩
  · ext x
    simp only [LinearMap.smul_apply, smul_eq_mul, hg]
    field_simp
  · intro x hx
    obtain ⟨n, hn⟩ := hmult ⟨x, hx⟩
    refine ⟨n, ?_⟩
    rw [hg, ← integralLatticeCoordinate_cast Λ f hint ⟨x, hx⟩, hn, Int.cast_mul]
    exact mul_div_cancel_right₀ (n : ℝ) hmR
  · rw [hg, hfw, div_self hmR]
  · ext x
    simp only [LinearMap.mem_ker, hg, div_eq_zero_iff, hmR, or_false]

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [FiniteDimensional ℝ E]

end Erdos3

end

section

namespace Erdos3

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GaussianScaledShortVectorBound
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem latticeGaussianMass_ge_multiples_at_temperature
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] (ξ : E) (hξΛ : ξ ∈ Λ) (hξ : ξ ≠ 0)
    {t : ℝ} (ht : 0 < t) (M : ℕ) (hM : (M : ℝ) * (Real.sqrt t * ‖ξ‖) ≤ 1) :
    ((M : ℝ) + 1) * Real.exp (-Real.pi) ≤ latticeGaussianMass Λ t 0 := by
  classical
  let v : ℕ → Λ := fun n => n • (⟨ξ, hξΛ⟩ : Λ)
  have hv (n : ℕ) : (v n : E) = (n : ℝ) • ξ := by
    rw [Nat.cast_smul_eq_nsmul]
    exact map_nsmul Λ.subtype n ⟨ξ, hξΛ⟩
  have hinj : Function.Injective v := by
    intro n m h
    have he := congrArg (fun x : Λ => (x : E)) h
    rw [hv, hv] at he
    exact Nat.cast_injective (smul_left_injective ℝ hξ he)
  have hterm (n : ℕ) (hn : n ∈ Finset.range (M + 1)) :
      Real.exp (-Real.pi) ≤ Real.exp (-Real.pi * t * ‖(0 : E) - (v n : E)‖ ^ 2) := by
    have hnM : (n : ℝ) ≤ M := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    have hnorm : Real.sqrt t * ‖(0 : E) - (v n : E)‖ ≤ 1 := by
      rw [zero_sub, norm_neg, hv, norm_smul, Real.norm_natCast]
      calc
        _ = (n : ℝ) * (Real.sqrt t * ‖ξ‖) := by ring
        _ ≤ (M : ℝ) * (Real.sqrt t * ‖ξ‖) :=
          mul_le_mul_of_nonneg_right hnM (by positivity)
        _ ≤ 1 := hM
    have hsq := pow_le_one₀ (by positivity : 0 ≤ Real.sqrt t * ‖(0 : E) - (v n : E)‖) hnorm (n := 2)
    rw [mul_pow, Real.sq_sqrt ht.le] at hsq
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hsq)]
  have hsum := Finset.sum_le_sum hterm
  have hbound := (lattice_gaussian_summable Λ ht 0).sum_le_tsum
    ((Finset.range (M + 1)).image v) (fun _ _ => (Real.exp_pos _).le)
  rw [Finset.sum_image (fun _ _ _ _ h => hinj h)] at hbound
  have hcount : (∑ _n ∈ Finset.range (M + 1), Real.exp (-Real.pi)) =
      ((M : ℝ) + 1) * Real.exp (-Real.pi) := by simp
  rw [hcount] at hsum
  exact hsum.trans hbound

theorem latticeGaussianMass_mul_scaled_norm_ge
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] (ξ : E) (hξΛ : ξ ∈ Λ) (hξ : ξ ≠ 0)
    {t : ℝ} (ht : 0 < t) :
    Real.exp (-Real.pi) ≤ (Real.sqrt t * ‖ξ‖) * latticeGaussianMass Λ t 0 := by
  have hn : 0 < Real.sqrt t * ‖ξ‖ := mul_pos (Real.sqrt_pos.mpr ht) (norm_pos_iff.mpr hξ)
  let M := ⌊(Real.sqrt t * ‖ξ‖)⁻¹⌋₊
  have hM : (M : ℝ) * (Real.sqrt t * ‖ξ‖) ≤ 1 := by
    calc
      _ ≤ (Real.sqrt t * ‖ξ‖)⁻¹ * (Real.sqrt t * ‖ξ‖) :=
        mul_le_mul_of_nonneg_right (Nat.floor_le (inv_nonneg.mpr hn.le)) hn.le
      _ = 1 := inv_mul_cancel₀ hn.ne'
  have hmass := latticeGaussianMass_ge_multiples_at_temperature Λ ξ hξΛ hξ ht M hM
  have hlarge : 1 ≤ (Real.sqrt t * ‖ξ‖) * ((M : ℝ) + 1) := by
    have h := mul_le_mul_of_nonneg_left (Nat.lt_floor_add_one (Real.sqrt t * ‖ξ‖)⁻¹).le hn.le
    rw [mul_inv_cancel₀ hn.ne'] at h
    exact h
  calc
    _ ≤ ((Real.sqrt t * ‖ξ‖) * ((M : ℝ) + 1)) * Real.exp (-Real.pi) :=
      le_mul_of_one_le_left (Real.exp_pos _).le hlarge
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hmass hn.le]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NormalizedLatticeSheet
namespace OAI

section

namespace Erdos3

open Module Submodule

variable {I E : Type*} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℝ E]

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem exists_primitive_lattice_normal (Λ : Submodule ℤ E)
    (hspan : Submodule.span ℝ (Λ : Set E) = ⊤) (ξ : E) (hξ : ξ ≠ 0)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, inner ℝ ξ x = (n : ℝ)) :
    ∃ (m : ℤ) (ζ w : E), m ≠ 0 ∧ ξ = (m : ℝ) • ζ ∧ ζ ≠ 0 ∧ ‖ζ‖ ≤ ‖ξ‖ ∧
      (∀ x ∈ Λ, ∃ n : ℤ, inner ℝ ζ x = (n : ℝ)) ∧ w ∈ Λ ∧ inner ℝ ζ w = 1 := by
  have hf : normalFunctional ξ ≠ 0 := by
    intro hz
    have he := congrArg (fun f : E →ₗ[ℝ] ℝ => f ξ) hz
    change inner ℝ ξ ξ = 0 at he
    rw [real_inner_self_eq_norm_sq] at he
    have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    nlinarith
  obtain ⟨m, g, w, hm, hfg, hgint, hwΛ, hwg, _⟩ :=
    exists_primitive_lattice_functional Λ (normalFunctional ξ) hspan hint hf
  let ζ := (m : ℝ)⁻¹ • ξ
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hg (x : E) : inner ℝ ζ x = g x := by
    have he := congrArg (fun f : E →ₗ[ℝ] ℝ => f x) hfg
    change inner ℝ ξ x = (m : ℝ) * g x at he
    simp only [ζ, real_inner_smul_left, he]
    field_simp
  have hsplit : ξ = (m : ℝ) • ζ := by
    simp only [ζ, smul_smul, mul_inv_cancel₀ hmR, one_smul]
  refine ⟨m, ζ, w, hm, hsplit, smul_ne_zero (inv_ne_zero hmR) hξ, ?_, ?_, hwΛ, ?_⟩
  · have ha : (1 : ℝ) ≤ |(m : ℝ)| := by
      have hmpos : (0 : ℤ) < |m| := abs_pos.mpr hm
      have hma : (1 : ℤ) ≤ |m| := by omega
      exact_mod_cast hma
    have hnorm : ‖ζ‖ = ‖ξ‖ / |(m : ℝ)| := by
      simp only [ζ, norm_smul, Real.norm_eq_abs, abs_inv, div_eq_mul_inv, mul_comm]
    rw [hnorm]
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one ha)).mpr
    exact le_mul_of_one_le_right (norm_nonneg _) ha
  · intro x hx
    rw [hg]
    exact hgint x hx
  · rw [hg]
    exact hwg

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [FiniteDimensional ℝ E]

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

end Erdos3

end

section

namespace Erdos3

open Submodule _root_.Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

end Erdos3

end

section

namespace Erdos3

variable (ι : Type*) [Fintype ι]

end Erdos3

end

section

namespace Erdos3

open Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

end Erdos3

end

section

namespace Erdos3

open Module Submodule

variable {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end Erdos3

end

section

namespace Erdos3

variable (J : Type*) [Fintype J]

end Erdos3

end

section

namespace Erdos3

open Module

variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

variable [Fintype I] [Fintype J]

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open MeasureTheory

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

theorem latticeGaussianNormalizer_nonneg (Λ : Submodule ℤ E) (t : ℝ) :
    0 ≤ latticeGaussianNormalizer Λ t :=
  mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) ENNReal.toReal_nonneg

theorem latticeGaussianNormalizer_pos (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] {t : ℝ} (ht : 0 < t) : 0 < latticeGaussianNormalizer Λ t :=
  mul_pos (pow_pos (Real.sqrt_pos.mpr ht) _) (ZLattice.covolume_pos Λ MeasureTheory.volume)

theorem normalizedLatticeGaussian_nonneg (Λ : Submodule ℤ E) (t : ℝ) (x : E) :
    0 ≤ normalizedLatticeGaussian Λ t x :=
  mul_nonneg (latticeGaussianNormalizer_nonneg Λ t) (latticeGaussianMass_nonneg Λ t x)

theorem normalizedLatticeGaussian_pos (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] {t : ℝ} (ht : 0 < t) (x : E) :
    0 < normalizedLatticeGaussian Λ t x :=
  mul_pos (latticeGaussianNormalizer_pos Λ ht) (latticeGaussianMass_pos Λ ht x)

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

theorem lattice_covolume_of_finrank_zero (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hd : Module.finrank ℝ E = 0) : ZLattice.covolume Λ = 1 := by
  classical
  let b := Module.Free.chooseBasis ℤ Λ
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ Λ) = 0 := by
    rw [← Module.finrank_eq_card_basis b, ZLattice.rank ℝ Λ, hd]
  let : IsEmpty (Module.Free.ChooseBasisIndex ℤ Λ) := Fintype.card_eq_zero_iff.mp hcard
  have h := lattice_covolume_sq_eq_gram Λ b
  rw [Matrix.det_isEmpty] at h
  nlinarith [ZLattice.covolume_pos Λ MeasureTheory.volume]

theorem normalizedLatticeGaussian_of_finrank_zero (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hd : Module.finrank ℝ E = 0) (t : ℝ) (x : E) :
    normalizedLatticeGaussian Λ t x = 1 := by
  let : Subsingleton E := Module.finrank_zero_iff.mp hd
  have hx : x = 0 := Subsingleton.elim _ _
  let : Unique Λ := ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩
  simp [normalizedLatticeGaussian, latticeGaussianNormalizer, hd,
    lattice_covolume_of_finrank_zero Λ hd, latticeGaussianMass, hx]
  exact Or.inr (Subsingleton.elim _ _)

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SchmidtGaussianMean
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem latticeGaussianMean_nonneg (Λ : Submodule ℤ E) (t : ℝ) (k : ℕ) (α : E) (N : ℕ) :
    0 ≤ latticeGaussianMean Λ t k α N := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact Finset.sum_nonneg fun _ _ => normalizedLatticeGaussian_nonneg Λ t _

theorem latticeGaussianMean_of_finrank_zero (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hd : Module.finrank ℝ E = 0) (t : ℝ) (k : ℕ) (α : E) (N : ℕ) :
    latticeGaussianMean Λ t k α N = 1 := by
  have hne : (Finset.Icc (-(N : ℤ)) (N : ℤ)).Nonempty := ⟨0, by simp⟩
  have hc : ((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hne
  simp only [latticeGaussianMean, normalizedLatticeGaussian_of_finrank_zero Λ hd,
    Finset.sum_const, nsmul_eq_mul, mul_one, div_self hc]

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

theorem latticeGaussianMean_zero_term (Λ : Submodule ℤ E) (t : ℝ) (j N : ℕ) (α : E) :
    normalizedLatticeGaussian Λ t 0 ≤
      (2 * (N : ℝ) + 1) * latticeGaussianMean Λ t (j + 1) α N := by
  have h := Finset.single_le_sum
    (f := fun n : ℤ => normalizedLatticeGaussian Λ t ((n : ℝ) ^ (j + 1) • α))
    (fun n _ => normalizedLatticeGaussian_nonneg Λ t _) (by simp : (0 : ℤ) ∈ Finset.Icc (-(N : ℤ)) (N : ℤ))
  simp only [Int.cast_zero, zero_pow (Nat.succ_ne_zero j), zero_smul] at h
  unfold latticeGaussianMean
  simp only [symmetricInterval_card, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  rw [mul_div_cancel₀ _ (by positivity : 2 * (N : ℝ) + 1 ≠ 0)]
  exact h

end Erdos3

end

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TemperaturePrimitiveNormal
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem dualLattice_sqrt_temperature_le (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (ζ : E) (hζ : ζ ≠ 0) (hζdual : ζ ∈ euclideanDualLattice Λ)
    {t : ℝ} (ht : 0 < t) :
    Real.sqrt t ≤ ‖ζ‖ * (Real.exp Real.pi * normalizedLatticeGaussian Λ t 0) := by
  have h := latticeGaussianMass_mul_scaled_norm_ge (euclideanDualLattice Λ)
    ζ hζdual hζ (inv_pos.mpr ht)
  rw [← normalizedLatticeGaussian_zero_eq_dual Λ ht, Real.sqrt_inv] at h
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hmul := mul_le_mul_of_nonneg_left h hs.le
  have hid : Real.sqrt t *
      (Real.sqrt t⁻¹ * ‖ζ‖ * normalizedLatticeGaussian Λ t 0) =
      ‖ζ‖ * normalizedLatticeGaussian Λ t 0 := by
    rw [Real.sqrt_inv]
    field_simp
  rw [Real.sqrt_inv] at hid
  rw [hid] at hmul
  have hh := mul_le_mul_of_nonneg_left hmul (Real.exp_pos Real.pi).le
  have he : Real.exp Real.pi * Real.exp (-Real.pi) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc
    _ = Real.exp Real.pi * (Real.sqrt t * Real.exp (-Real.pi)) := by rw [mul_left_comm, he, mul_one]
    _ ≤ Real.exp Real.pi * (‖ζ‖ * normalizedLatticeGaussian Λ t 0) := hh
    _ = _ := by ring

theorem exists_temperature_bounded_primitive_normal
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (ξ : E) (hξ : ξ ≠ 0) (hξdual : ξ ∈ euclideanDualLattice Λ)
    {t L : ℝ} (ht : 0 < t) (hL : 0 ≤ L) (hnorm : ‖ξ‖ ≤ Real.sqrt t * L) :
    ∃ (m : ℤ) (ζ w : E), m ≠ 0 ∧ ξ = (m : ℝ) • ζ ∧ ζ ≠ 0 ∧
      ‖ζ‖ ≤ Real.sqrt t * L ∧ ζ ∈ euclideanDualLattice Λ ∧
      w ∈ Λ ∧ inner ℝ ζ w = 1 ∧
      Real.sqrt t ≤ ‖ζ‖ * (Real.exp Real.pi * normalizedLatticeGaussian Λ t 0) ∧
      |(m : ℝ)| ≤ L * (Real.exp Real.pi * normalizedLatticeGaussian Λ t 0) := by
  obtain ⟨m, ζ, w, hm, hsplit, hζ, hζnorm, hint, hwΛ, hw⟩ :=
    exists_primitive_lattice_normal Λ (IsZLattice.span_top (K := ℝ)) ξ hξ
      ((mem_euclideanDualLattice Λ ξ).mp hξdual)
  have hζdual := (mem_euclideanDualLattice Λ ζ).mpr hint
  have hs := dualLattice_sqrt_temperature_le Λ ζ hζ hζdual ht
  refine ⟨m, ζ, w, hm, hsplit, hζ, hζnorm.trans hnorm, hζdual, hwΛ, hw, hs, ?_⟩
  have hbound : |(m : ℝ)| * ‖ζ‖ ≤
      (L * (Real.exp Real.pi * normalizedLatticeGaussian Λ t 0)) * ‖ζ‖ := by
    calc
      |(m : ℝ)| * ‖ζ‖ = ‖ξ‖ := by rw [hsplit, norm_smul, Real.norm_eq_abs]
      _ ≤ Real.sqrt t * L := hnorm
      _ ≤ (‖ζ‖ * (Real.exp Real.pi * normalizedLatticeGaussian Λ t 0)) * L :=
        mul_le_mul_of_nonneg_right hs hL
      _ = _ := by ring
  nlinarith [norm_pos_iff.mpr hζ]

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SchmidtShortDualVector
namespace OAI

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

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

open Polynomial

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
open Polynomial CircleFourier

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

end Erdos3

end

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

open Polynomial CircleFourier

end Erdos3

end

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

theorem PolynomialIntervalPowerBound.short_dual_vector {k C d : ℕ}
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

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SchmidtIntervalBudget
namespace OAI

section

namespace Erdos3

theorem exists_schmidt_shorter_interval {K : ℝ} (hK : 0 < K) (N : ℕ)
    (hN : 2 * K ≤ N) :
    ∃ H : ℕ, 0 < H ∧ K * H ≤ N ∧ (N : ℝ) ≤ 2 * K * H := by
  let H := ⌊(N : ℝ) / K⌋₊
  have hquot : 2 ≤ (N : ℝ) / K := (le_div_iff₀ hK).mpr (by nlinarith)
  have hH : 1 ≤ H := (Nat.le_floor_iff (by positivity)).mpr (by norm_num; linarith)
  have hupper : K * (H : ℝ) ≤ N := by
    have h := Nat.floor_le (show 0 ≤ (N : ℝ) / K by positivity)
    simpa only [mul_comm] using (le_div_iff₀ hK).mp h
  have hlower : (N : ℝ) < K * ((H : ℝ) + 1) := by
    exact (div_lt_iff₀ hK).mp (Nat.lt_floor_add_one ((N : ℝ) / K)) |>.trans_eq (by ring)
  refine ⟨H, by omega, hupper, ?_⟩
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  nlinarith

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

theorem schmidt_step_epsilon_bounds (d : ℕ) :
    0 < ((d : ℝ) + 1)⁻¹ ∧ ((d : ℝ) + 1)⁻¹ ≤ 1 := by
  have hd : (1 : ℝ) ≤ (d : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) d; linarith
  exact ⟨inv_pos.mpr (by positivity), inv_le_one_of_one_le₀ hd⟩

theorem schmidt_step_epsilon_budget {r d : ℕ} (hr : r ≤ d) :
    (r : ℝ) * ((d : ℝ) + 1)⁻¹ ≤ 1 := by
  rw [← div_eq_mul_inv]
  apply (div_le_iff₀ (by positivity : 0 < (d : ℝ) + 1)).mpr
  have hr' : (r : ℝ) ≤ d := by exact_mod_cast hr
  linarith

end Erdos3

end

section

namespace Erdos3

theorem schmidtRadiusFactor_mono {d D : ℕ} {A U : ℝ} (hd : d ≤ D)
    (hA : 0 < A) (hAU : A ≤ U) :
    schmidtRadiusFactor d A ≤ schmidtRadiusFactor D U := by
  have hlog := Real.log_le_log hA hAU
  have hd' : (d : ℝ) ≤ D := by exact_mod_cast hd
  unfold schmidtRadiusFactor
  linarith

theorem schmidtStepFactor_mono (C e : ℕ) {d D : ℕ} {A U : ℝ} (hd : d ≤ D)
    (hA : 1 ≤ A) (hAU : A ≤ U) :
    schmidtStepFactor C e d A ≤ schmidtStepFactor C e D U := by
  have hA0 : 0 ≤ A := by linarith
  have hU0 : 0 ≤ U := hA0.trans hAU
  have hL0 := (schmidtRadiusFactor_pos d hA).le
  have hL := schmidtRadiusFactor_mono hd (by linarith : 0 < A) hAU
  have hd' : (d : ℝ) ≤ D := by exact_mod_cast hd
  have hB := pow_le_pow_left₀ (by positivity : 0 ≤ 8 * A)
    (by linarith : 8 * A ≤ 8 * U) e
  have hC := mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg C : (0 : ℝ) ≤ C)
  have hS := mul_le_mul_of_nonneg_left hAU (Real.exp_pos Real.pi).le
  have hBS := mul_le_mul hC hS (by positivity) (by positivity)
  have hlast : schmidtRadiusFactor d A + (d : ℝ) + 1 ≤
      schmidtRadiusFactor D U + (D : ℝ) + 1 := by linarith
  unfold schmidtStepFactor
  exact add_le_add_right (mul_le_mul hBS hlast (by positivity) (by positivity)) 1

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

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem PolynomialIntervalPowerBound.dimension_reduction {j C e : ℕ}
    (hW : PolynomialIntervalPowerBound (j + 1) C e)
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {t : ℝ} (ht : 0 < t) (α : E) (N : ℕ)
    (hN : 2 * schmidtStepFactor C e (Module.finrank ℝ E) (normalizedLatticeGaussian Λ t 0) ≤ N)
    (hsmall : latticeGaussianMean Λ t (j + 1) α N < 1 / 2) :
    let A := normalizedLatticeGaussian Λ t 0
    let d := Module.finrank ℝ E
    let L := schmidtRadiusFactor d A
    let K := schmidtStepFactor C e d A
    let ε := ((d : ℝ) + 1)⁻¹
    ∃ (ζ : E) (H : ℕ) (β : (normalFunctional ζ).ker),
      ζ ≠ 0 ∧ ζ ∈ euclideanDualLattice Λ ∧
      IsZLattice ℝ (latticeHyperplane Λ (normalFunctional ζ)) ∧
      Module.finrank ℝ (normalFunctional ζ).ker + 1 = d ∧
      0 < H ∧ K * H ≤ N ∧ (N : ℝ) ≤ 2 * K * H ∧
      latticeGaussianMean (latticeHyperplane Λ (normalFunctional ζ))
          (t * (1 + ε) ^ 2) (j + 1) β H ≤
        (2 * Real.exp (4 * Real.pi + 1) * L * K) * latticeGaussianMean Λ t (j + 1) α N ∧
      normalizedLatticeGaussian (latticeHyperplane Λ (normalFunctional ζ))
          (t * (1 + ε) ^ 2) 0 ≤ Real.exp 1 * L * A := by
  let A := normalizedLatticeGaussian Λ t 0
  let d := Module.finrank ℝ E
  let L := schmidtRadiusFactor d A
  let K := schmidtStepFactor C e d A
  let ε := ((d : ℝ) + 1)⁻¹
  let B := (C : ℝ) * (8 * A) ^ e
  let S := Real.exp Real.pi * A
  have hA : 1 ≤ A := normalizedLatticeGaussian_origin_ge_one Λ ht
  have hA0 : 0 ≤ A := by linarith
  have hL : 0 < L := schmidtRadiusFactor_pos d hA
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  obtain ⟨hK, hBK, hQK, hSK⟩ := schmidtStepFactor_bounds C e d hA
  change 1 ≤ K at hK
  change B ≤ K at hBK
  change B * (L * S) ≤ K at hQK
  change B * S ≤ ε * K at hSK
  change 2 * K ≤ N at hN
  have hKpos : 0 < K := by linarith
  have hNpos : 0 < N := by
    have : (0 : ℝ) < N := by linarith
    exact_mod_cast this
  have hsize : B ≤ 2 * (N : ℝ) + 1 := by linarith
  obtain ⟨ξ, hξdual, hξ, hξnorm, q, hq, hqB, p, hp⟩ :=
    hW.short_dual_vector Λ ht α N hsize hsmall
  obtain ⟨m, ζ, w, hm, hsplit, hζ, hζnorm, hζdual, hwΛ, hw, hs, hmLS⟩ :=
    exists_temperature_bounded_primitive_normal Λ ξ hξ hξdual ht hL.le hξnorm
  change Real.sqrt t ≤ ‖ζ‖ * S at hs
  change |(m : ℝ)| ≤ L * S at hmLS
  have hqB' : (q : ℝ) ≤ B := hqB
  have ha : |(((q : ℤ) * m : ℤ) : ℝ)| ≤ B * (L * S) := by
    rw [Int.cast_mul, Int.cast_natCast, abs_mul, Nat.abs_cast]
    exact mul_le_mul hqB' hmLS (abs_nonneg _) hB
  obtain ⟨H, hH, hHN, hNH⟩ := exists_schmidt_shorter_interval hKpos N hN
  have hHQ : (H : ℝ) * (B * (L * S)) ≤ N := by
    have hh := mul_le_mul_of_nonneg_left hQK (Nat.cast_nonneg H : (0 : ℝ) ≤ H)
    nlinarith [hh]
  obtain ⟨hε, hεone⟩ := schmidt_step_epsilon_bounds d
  have hHBS : (H : ℝ) * B * S ≤ ε * N := by
    have hh := mul_le_mul_of_nonneg_left hSK (Nat.cast_nonneg H : (0 : ℝ) ≤ H)
    have hh' := mul_le_mul_of_nonneg_left hHN hε.le
    nlinarith [hh, hh']
  have hdim : Module.finrank ℝ (normalFunctional ζ).ker + 1 = d :=
    hyperplane_finrank (normalFunctional ζ) w hw
  have hbudget : (Module.finrank ℝ (normalFunctional ζ).ker : ℝ) * ε ≤ 1 :=
    schmidt_step_epsilon_budget (by omega : Module.finrank ℝ (normalFunctional ζ).ker ≤ d)
  have hΓ := latticeHyperplane_isZLattice Λ (normalFunctional ζ)
    ((mem_euclideanDualLattice Λ ζ).mp hζdual) w hwΛ hw
  obtain ⟨β, hmean, hmass⟩ := exists_schmidt_dilated_mean_transfer Λ α ξ ζ w m p q j H N
    hm hq hsplit hζ hζdual hwΛ hw hNpos ht (by positivity) hB hS hL.le
    hε.le hεone hbudget hs hζnorm ha hp hHQ hHBS hK hNH
  exact ⟨ζ, H, β, hζ, hζdual, hΓ, hdim, hH, hHN, hNH, hmean, hmass⟩

end Erdos3

end

section

namespace Erdos3

theorem one_le_power_mul_of_one_le_mul {V F : ℝ} (hV : 1 ≤ V) (hF : 0 ≤ F)
    (h : 1 ≤ V * F) (d : ℕ) : 1 ≤ V ^ (d + 1) * F := by
  calc
    1 ≤ V * F := h
    _ ≤ V ^ d * (V * F) :=
      le_mul_of_one_le_left (mul_nonneg (by linarith) hF) (one_le_pow₀ hV)
    _ = V ^ (d + 1) * F := by rw [pow_succ]; ring

theorem PolynomialIntervalPowerBound.gaussian_mean_iteration
    {j C e D : ℕ} (hW : PolynomialIntervalPowerBound (j + 1) C e)
    {M U V : ℝ} (hM : 1 ≤ M) (hU : 1 ≤ U)
    (hLM : Real.exp 1 * schmidtRadiusFactor D U ≤ M)
    (hV : 2 ≤ V) (hKV : 4 * schmidtStepFactor C e D U + 1 ≤ V)
    (hTV : 2 * Real.exp (4 * Real.pi + 1) * schmidtRadiusFactor D U *
      schmidtStepFactor C e D U ≤ V) (d : ℕ) :
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
      (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
      {t : ℝ}, 0 < t → ∀ (α : E) (N : ℕ),
      Module.finrank ℝ E = d → d ≤ D →
      normalizedLatticeGaussian Λ t 0 * M ^ d ≤ U →
      1 ≤ V ^ (d + 1) * latticeGaussianMean Λ t (j + 1) α N := by
  have hVone : 1 ≤ V := by linarith
  have hV0 : 0 ≤ V := by linarith
  have hM0 : 0 ≤ M := by linarith
  induction d with
  | zero =>
    intro E _ _ _ _ _ Λ _ _ t ht α N hdim hd hmass
    rw [latticeGaussianMean_of_finrank_zero Λ hdim]
    simpa using hVone
  | succ d ih =>
    intro E _ _ _ _ _ Λ _ _ t ht α N hdim hd hmass
    have hA := normalizedLatticeGaussian_origin_ge_one Λ ht
    have hA0 : 0 ≤ normalizedLatticeGaussian Λ t 0 := by linarith
    have hAU : normalizedLatticeGaussian Λ t 0 ≤ U := by
      exact (le_mul_of_one_le_right hA0 (one_le_pow₀ hM)).trans hmass
    have hdimD : Module.finrank ℝ E ≤ D := by omega
    have hL := schmidtRadiusFactor_mono hdimD (by linarith : 0 < normalizedLatticeGaussian Λ t 0) hAU
    have hK := schmidtStepFactor_mono C e hdimD hA hAU
    have hF0 := latticeGaussianMean_nonneg Λ t (j + 1) α N
    by_cases hsmall : latticeGaussianMean Λ t (j + 1) α N < 1 / 2
    · by_cases hN : 2 * schmidtStepFactor C e (Module.finrank ℝ E)
          (normalizedLatticeGaussian Λ t 0) ≤ (N : ℝ)
      · obtain ⟨ζ, H, β, hζ, hζdual, hΓ, hdrop, hH, hHN, hNH, hmean, hmass'⟩ :=
          hW.dimension_reduction Λ ht α N hN hsmall
        let : IsZLattice ℝ (latticeHyperplane Λ (normalFunctional ζ)) := hΓ
        have hdim' : Module.finrank ℝ (normalFunctional ζ).ker = d := by omega
        have ht' : 0 < t * (1 + ((Module.finrank ℝ E : ℝ) + 1)⁻¹) ^ 2 := by positivity
        have hLM' : Real.exp 1 * schmidtRadiusFactor (Module.finrank ℝ E)
            (normalizedLatticeGaussian Λ t 0) ≤ M :=
          (mul_le_mul_of_nonneg_left hL (Real.exp_pos 1).le).trans hLM
        have hmassM := hmass'.trans (mul_le_mul_of_nonneg_right hLM' hA0)
        have hinvariant : normalizedLatticeGaussian (latticeHyperplane Λ (normalFunctional ζ))
            (t * (1 + ((Module.finrank ℝ E : ℝ) + 1)⁻¹) ^ 2) 0 * M ^ d ≤ U := by
          calc
            _ ≤ (M * normalizedLatticeGaussian Λ t 0) * M ^ d :=
              mul_le_mul_of_nonneg_right hmassM (pow_nonneg hM0 _)
            _ = normalizedLatticeGaussian Λ t 0 * M ^ (d + 1) := by rw [pow_succ]; ring
            _ ≤ U := hmass
        have hih := ih (normalFunctional ζ).ker (latticeHyperplane Λ (normalFunctional ζ))
          ht' β H hdim' (by omega) hinvariant
        have hT : 2 * Real.exp (4 * Real.pi + 1) *
            schmidtRadiusFactor (Module.finrank ℝ E) (normalizedLatticeGaussian Λ t 0) *
            schmidtStepFactor C e (Module.finrank ℝ E) (normalizedLatticeGaussian Λ t 0) ≤ V := by
          apply le_trans _ hTV
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hL (by positivity)
          · exact hK
          · exact (schmidtStepFactor_bounds C e (Module.finrank ℝ E) hA).1.trans' (by norm_num)
          · have := (schmidtRadiusFactor_pos D hU).le; positivity
        have hmeanV := hmean.trans (mul_le_mul_of_nonneg_right hT hF0)
        calc
          1 ≤ V ^ (d + 1) * latticeGaussianMean (latticeHyperplane Λ (normalFunctional ζ))
              (t * (1 + ((Module.finrank ℝ E : ℝ) + 1)⁻¹) ^ 2) (j + 1) β H := hih
          _ ≤ V ^ (d + 1) * (V * latticeGaussianMean Λ t (j + 1) α N) :=
            mul_le_mul_of_nonneg_left hmeanV (pow_nonneg hV0 _)
          _ = V ^ (d + 1 + 1) * latticeGaussianMean Λ t (j + 1) α N := by rw [pow_succ]; ring
      · have hzero := hA.trans (latticeGaussianMean_zero_term Λ t j N α)
        have hNV : 2 * (N : ℝ) + 1 ≤ V := by linarith
        have hVF := hzero.trans (mul_le_mul_of_nonneg_right hNV hF0)
        exact one_le_power_mul_of_one_le_mul hVone hF0 hVF (d + 1)
    · have hVF : 1 ≤ V * latticeGaussianMean Λ t (j + 1) α N := by nlinarith
      exact one_le_power_mul_of_one_le_mul hVone hF0 hVF (d + 1)

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
  have h := hW.gaussian_mean_iteration hM hU hLM hV hKV hTV d E Λ ht α N rfl le_rfl le_rfl
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

end Erdos3

end

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

open Polynomial

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

end Erdos3

end

end OAI

end

theorem solution.{u_1} : type_of% @OAI.Erdos3.PolynomialIntervalPowerBound.lattice_recurrence.{u_1} := @OAI.Erdos3.PolynomialIntervalPowerBound.lattice_recurrence.{u_1}
