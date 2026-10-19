-- Prove2me | solution 1 for OAI.Erdos3.PolynomialIntervalPowerBound.gaussian_mean_iteration_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T11:24:43.280232+00:00
-- url     : https://prove2.me/submissions/b6089fc7-97d8-4f0c-88b5-8a32e4ad7527

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B100
import Definitions.Def_OAIE3v2B137
import Theorems.Thm_OAI_Erdos3_PolynomialIntervalPowerBound_short_dual_vector_s2
import Theorems.Thm_OAI_Erdos3_exists_schmidt_dilated_mean_transfer_s2

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

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem latticeGaussianMass_nonneg (Λ : Submodule ℤ E) (t : ℝ) (x : E) :
    0 ≤ latticeGaussianMass Λ t x := tsum_nonneg (fun _ => (Real.exp_pos _).le)

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GaussianScaledShortVectorBound
namespace OAI

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
    hW.short_dual_vector_s2 Λ ht α N hsize hsmall
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
  obtain ⟨β, hmean, hmass⟩ := exists_schmidt_dilated_mean_transfer_s2 Λ α ξ ζ w m p q j H N
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

theorem PolynomialIntervalPowerBound.gaussian_mean_iteration_s2_oai
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

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Erdos3.PolynomialIntervalPowerBound.gaussian_mean_iteration_s2_oai.{u_1} := @OAI.Erdos3.PolynomialIntervalPowerBound.gaussian_mean_iteration_s2_oai.{u_1}
