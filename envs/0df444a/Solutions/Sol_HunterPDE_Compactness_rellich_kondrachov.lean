-- Prove2me | solution 1 for HunterPDE.Compactness.rellich_kondrachov
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-17T21:35:35.755979+00:00
-- url     : https://prove2.me/submissions/16099a21-ccc8-4386-a1fc-c8327a6290d3

-- Licensed under Apache 2.0. Complete Rellich–Kondrachov theorem.
import Mathlib
import Definitions.Def_HunterPDE_Compactness_Sobolev

open MeasureTheory
open scoped ENNReal NNReal


open MeasureTheory
open HunterPDE.Shared HunterPDE.Compactness

namespace RellichProof

 theorem multiDeriv_zero {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    multiDeriv f 0 = f := by
  have h : multiIndexList (0 : Fin n → ℕ) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro i _
    simp
  simp only [multiDeriv, h, iteratedPartial]

 private theorem flatMap_single_index {α : Type*} [DecidableEq α] (i : α)
    (l : List α) (hl : l.Nodup) :
    l.flatMap (fun j => List.replicate ((Pi.single i 1 : α → ℕ) j) j) =
      if i ∈ l then [i] else [] := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have htail : l.Nodup := (List.nodup_cons.mp hl).2
    have ha : a ∉ l := (List.nodup_cons.mp hl).1
    rw [List.flatMap_cons, ih htail]
    by_cases hai : a = i
    · subst a
      simp [ha]
    · simp [hai, Ne.symm hai]

 theorem multiDeriv_single {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (i : Fin n) :
    multiDeriv f (Pi.single i 1) = partialDeriv f i := by
  have h := flatMap_single_index i (List.finRange n) (List.nodup_finRange n)
  simp only [List.mem_finRange, ite_true] at h
  simp only [multiDeriv, multiIndexList, h, iteratedPartial]

 theorem zero_mem_multiIndices (n : ℕ) : (0 : Fin n → ℕ) ∈ multiIndicesLe n 1 := by
  simp [multiIndicesLe]

 theorem single_mem_multiIndices {n : ℕ} (i : Fin n) :
    Pi.single i 1 ∈ multiIndicesLe n 1 := by
  simp only [multiIndicesLe, Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · intro j
    simp only [Finset.mem_range, Pi.single_apply]
    split_ifs <;> omega
  · simp

 theorem multiIndices_one_cases {n : ℕ} {α : Fin n → ℕ}
    (hα : α ∈ multiIndicesLe n 1) : α = 0 ∨ ∃ i, α = Pi.single i 1 := by
  have hs : ∑ i, α i ≤ 1 := (Finset.mem_filter.mp hα).2
  by_cases hz : α = 0
  · exact Or.inl hz
  · right
    obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
      by_contra h
      push Not at h
      exact hz (funext h)
    have hile : α i ≤ ∑ j, α j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hi1 : α i = 1 := by omega
    refine ⟨i, ?_⟩
    funext j
    by_cases hji : j = i
    · subst j
      simp [hi1]
    · have hj0 : α j = 0 := by
        by_contra hj
        have hh := Finset.sum_le_one_iff.mp hs i j (Finset.mem_univ i)
          (Finset.mem_univ j) hi hj
        exact hji hh.1.symm
      simp [hji, hj0]

end RellichProof


open MeasureTheory
open scoped ContDiff
open HunterPDE.Shared

namespace RellichProof

variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
variable {f g : EuclideanSpace ℝ (Fin n) → ℝ}

 theorem test_sub (hf : IsTestFunction Ω f) (hg : IsTestFunction Ω g) :
    IsTestFunction Ω (f - g) := by
  refine ⟨hf.1.sub hg.1, hf.2.1.sub hg.2.1, ?_⟩
  exact (tsupport_sub f g).trans (Set.union_subset hf.2.2 hg.2.2)

 theorem test_partial (hf : IsTestFunction Ω f) (i : Fin n) :
    IsTestFunction Ω (partialDeriv f i) := by
  refine ⟨?_, hf.2.1.fderiv_apply ℝ _, ?_⟩
  · exact (hf.1.fderiv_right (by simp)).clm_apply contDiff_const
  · exact (tsupport_fderiv_apply_subset ℝ _).trans hf.2.2

 theorem test_iterated (hf : IsTestFunction Ω f) (l : List (Fin n)) :
    IsTestFunction Ω (iteratedPartial f l) := by
  induction l with
  | nil => exact hf
  | cons i l ih => exact test_partial ih i

 theorem test_multiDeriv (hf : IsTestFunction Ω f) (α : Fin n → ℕ) :
    IsTestFunction Ω (multiDeriv f α) := test_iterated hf _

 theorem integrable_mul_test (hf : LocallyIntegrableOn f Ω volume)
    (hg : IsTestFunction Ω g) : Integrable (fun x => f x * g x) volume := by
  have hK : IsCompact (tsupport g) := hg.2.1
  have hi := (hf.integrableOn_compact_subset hg.2.2 hK).mul_continuousOn
    hg.1.continuous.continuousOn hK
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hi
  intro x hx
  apply subset_tsupport g
  exact (mul_ne_zero_iff.mp hx).2

 theorem integral_mul_test_restrict (hf : IsTestFunction Ω f)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ x in Ω, g x * f x) = ∫ x, g x * f x := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hz : f x = 0 := by
    by_contra hn
    exact hx (hf.2.2 (subset_tsupport f hn))
  simp only [hz, mul_zero]

end RellichProof


open MeasureTheory Filter
open HunterPDE.Shared

namespace RellichProof

variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
variable {α : Fin n → ℕ} {f g h k : EuclideanSpace ℝ (Fin n) → ℝ}

 theorem weak_unique (hΩ : IsOpen Ω) (hg : HasWeakDeriv Ω α f g)
    (hh : HasWeakDeriv Ω α f h) : g =ᵐ[volume.restrict Ω] h := by
  have hz : ∀ᵐ x ∂volume, x ∈ Ω → g x - h x = 0 := by
    apply hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hg.2.1.sub hh.2.1)
    intro φ hφ hcompact hsupp
    have ht : IsTestFunction Ω φ := ⟨hφ, hcompact, hsupp⟩
    have hgint := integrable_mul_test hg.2.1 ht
    have hhint := integrable_mul_test hh.2.1 ht
    have heq : (∫ x, g x * φ x) = ∫ x, h x * φ x := by
      rw [← integral_mul_test_restrict ht g, ← integral_mul_test_restrict ht h,
        hg.2.2 φ ht, hh.2.2 φ ht]
    have he : (fun x => φ x • (g x - h x)) =
        (fun x => g x * φ x - h x * φ x) := by
      funext x
      simp only [smul_eq_mul]
      ring
    simp only [Pi.sub_apply]
    rw [he, integral_sub hgint hhint, heq, sub_self]
  change ∀ᵐ x ∂volume.restrict Ω, g x = h x
  rw [ae_restrict_iff' hΩ.measurableSet]
  filter_upwards [hz] with x hx hxin
  exact sub_eq_zero.mp (hx hxin)

 theorem weak_sub (hf : HasWeakDeriv Ω α f g) (hh : HasWeakDeriv Ω α h k) :
    HasWeakDeriv Ω α (f - h) (g - k) := by
  refine ⟨hf.1.sub hh.1, hf.2.1.sub hh.2.1, ?_⟩
  intro φ hφ
  have hg := (integrable_mul_test hf.2.1 hφ).integrableOn (s := Ω)
  have hk := (integrable_mul_test hh.2.1 hφ).integrableOn (s := Ω)
  have hfp := (integrable_mul_test hf.1 (test_multiDeriv hφ α)).integrableOn (s := Ω)
  have hhp := (integrable_mul_test hh.1 (test_multiDeriv hφ α)).integrableOn (s := Ω)
  simp only [Pi.sub_apply, sub_mul]
  rw [integral_sub hg hk, integral_sub hfp hhp, hf.2.2 φ hφ, hh.2.2 φ hφ]
  ring

 theorem weak_zero (hf : LocallyIntegrableOn f Ω volume) : HasWeakDeriv Ω 0 f f := by
  refine ⟨hf, hf, ?_⟩
  intro φ _
  simp only [multiDeriv_zero, Pi.zero_apply, Finset.sum_const_zero, pow_zero, one_mul]

 theorem weak_chosen (hf : ∃ g, HasWeakDeriv Ω α f g) :
    HasWeakDeriv Ω α f (weakDeriv Ω α f) := by
  simp only [weakDeriv, dif_pos hf]
  exact Classical.choose_spec hf

 theorem weak_chosen_eq (hΩ : IsOpen Ω) (hf : HasWeakDeriv Ω α f g) :
    weakDeriv Ω α f =ᵐ[volume.restrict Ω] g :=
  weak_unique hΩ (weak_chosen ⟨g, hf⟩) hf

end RellichProof


open MeasureTheory
open scoped ContDiff ENNReal
open HunterPDE.Shared HunterPDE.Compactness

namespace RellichProof

variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}

 theorem test_weak_partial (hf : IsTestFunction Ω f) (i : Fin n) :
    HasWeakDeriv Ω (Pi.single i 1) f (partialDeriv f i) := by
  have hdf := test_partial hf i
  refine ⟨hf.1.continuous.locallyIntegrable.locallyIntegrableOn Ω,
    hdf.1.continuous.locallyIntegrable.locallyIntegrableOn Ω, ?_⟩
  intro φ hφ
  have hdφ := test_partial hφ i
  have h1 := integrable_mul_test
    (hdf.1.continuous.locallyIntegrable.locallyIntegrableOn Ω) hφ
  have h2 := integrable_mul_test
    (hf.1.continuous.locallyIntegrable.locallyIntegrableOn Ω) hdφ
  have h3 := integrable_mul_test
    (hf.1.continuous.locallyIntegrable.locallyIntegrableOn Ω) hφ
  have he := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3
    (fun _ _ => (hf.1.differentiable (by simp)).differentiableAt)
    (fun _ _ => (hφ.1.differentiable (by simp)).differentiableAt)
  rw [integral_mul_test_restrict hφ, multiDeriv_single,
    integral_mul_test_restrict hdφ]
  have hi : (∑ j : Fin n, (Pi.single i 1 : Fin n → ℕ) j) = 1 := by simp
  rw [hi, pow_one, neg_one_mul]
  change (∫ x, partialDeriv f i x * φ x) = -(∫ x, f x * partialDeriv φ i x)
  change (∫ x, f x * partialDeriv φ i x) = -(∫ x, partialDeriv f i x * φ x) at he
  linarith

 theorem test_memW (hf : IsTestFunction Ω f) (p : ℝ≥0∞) : MemW 1 p Ω f := by
  intro α hα
  rcases multiIndices_one_cases hα with rfl | ⟨i, rfl⟩
  · refine ⟨f, weak_zero (hf.1.continuous.locallyIntegrable.locallyIntegrableOn Ω), ?_⟩
    exact (hf.1.continuous.memLp_of_hasCompactSupport hf.2.1).mono_measure
      Measure.restrict_le_self
  · have hdf := test_partial hf i
    refine ⟨partialDeriv f i, test_weak_partial hf i, ?_⟩
    exact (hdf.1.continuous.memLp_of_hasCompactSupport hdf.2.1).mono_measure
      Measure.restrict_le_self

 theorem memW_sub {g : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℝ≥0∞}
    (hf : MemW 1 p Ω f) (hg : MemW 1 p Ω g) : MemW 1 p Ω (f - g) := by
  intro α hα
  obtain ⟨df, hdf, hfLp⟩ := hf α hα
  obtain ⟨dg, hdg, hgLp⟩ := hg α hα
  exact ⟨df - dg, weak_sub hdf hdg, hfLp.sub hgLp⟩

 theorem memW0_sub_test {p : ℝ≥0∞} (hf : MemW0 1 p Ω f)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : IsTestFunction Ω φ) :
    MemW0 1 p Ω (f - φ) := by
  refine ⟨memW_sub hf.1 (test_memW hφ p), ?_⟩
  intro ε hε
  obtain ⟨ψ, hψ, he⟩ := hf.2 ε hε
  refine ⟨ψ - φ, test_sub hψ hφ, ?_⟩
  have hh : f - φ - (ψ - φ) = f - ψ := by
    funext x
    simp only [Pi.sub_apply]
    ring
  rw [hh]
  exact he

end RellichProof


open MeasureTheory
open scoped ENNReal
open HunterPDE.Shared HunterPDE.Compactness

namespace RellichProof

variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}

 theorem component_le_norm {p : ℝ} (hp : 0 < p) {α : Fin n → ℕ}
    (hα : α ∈ multiIndicesLe n 1) :
    eLpNorm (weakDeriv Ω α f) (ENNReal.ofReal p) (volume.restrict Ω) ≤
      sobolevNorm 1 (ENNReal.ofReal p) Ω f := by
  unfold sobolevNorm
  rw [if_neg ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le]
  have hs := Finset.single_le_sum (fun β (_ : β ∈ multiIndicesLe n 1) =>
    (bot_le : (0 : ℝ≥0∞) ≤ eLpNorm (weakDeriv Ω β f) (ENNReal.ofReal p)
      (volume.restrict Ω) ^ p)) hα
  have hh := ENNReal.rpow_le_rpow hs (by positivity : 0 ≤ 1 / p)
  simpa only [← ENNReal.rpow_mul, mul_one_div_cancel hp.ne', ENNReal.rpow_one] using hh

 theorem memW_chosen_memLp {p : ℝ≥0∞} (hΩ : IsOpen Ω) (hf : MemW 1 p Ω f)
    {α : Fin n → ℕ} (hα : α ∈ multiIndicesLe n 1) :
    MemLp (weakDeriv Ω α f) p (volume.restrict Ω) := by
  obtain ⟨g, hg, hgp⟩ := hf α hα
  exact MemLp.ae_eq (weak_chosen_eq hΩ hg).symm hgp

 theorem memW_zero_memLp {p : ℝ≥0∞} (hΩ : IsOpen Ω) (hf : MemW 1 p Ω f) :
    MemLp f p (volume.restrict Ω) := by
  obtain ⟨g, hg, hgp⟩ := hf 0 (zero_mem_multiIndices n)
  exact MemLp.ae_eq (weak_unique hΩ hg (weak_zero hg.1)) hgp

 theorem zero_le_norm (hΩ : IsOpen Ω) {p : ℝ} (hp : 0 < p)
    (hf : MemW 1 (ENNReal.ofReal p) Ω f) :
    eLpNorm f (ENNReal.ofReal p) (volume.restrict Ω) ≤
      sobolevNorm 1 (ENNReal.ofReal p) Ω f := by
  obtain ⟨g, hg, _⟩ := hf 0 (zero_mem_multiIndices n)
  have he := weak_chosen_eq hΩ (weak_zero hg.1)
  rw [← eLpNorm_congr_ae he]
  exact component_le_norm hp (zero_mem_multiIndices n)

 theorem test_partial_le_norm (hΩ : IsOpen Ω) {p : ℝ} (hp : 0 < p)
    (hf : IsTestFunction Ω f) (i : Fin n) :
    eLpNorm (partialDeriv f i) (ENNReal.ofReal p) (volume.restrict Ω) ≤
      sobolevNorm 1 (ENNReal.ofReal p) Ω f := by
  rw [← eLpNorm_congr_ae (weak_chosen_eq hΩ (test_weak_partial hf i))]
  exact component_le_norm hp (single_mem_multiIndices i)

 theorem test_indicator (hf : IsTestFunction Ω f) : Ω.indicator f = f := by
  apply Set.indicator_eq_self.2
  exact (subset_tsupport f).trans hf.2.2

 theorem test_eLpNorm_restrict (hf : IsTestFunction Ω f) (p : ℝ≥0∞) :
    eLpNorm f p (volume.restrict Ω) = eLpNorm f p volume := by
  exact eLpNorm_restrict_eq_of_support_subset ((subset_tsupport f).trans hf.2.2)

end RellichProof


open MeasureTheory
open scoped ENNReal
open HunterPDE.Shared HunterPDE.Compactness

namespace RellichProof

 theorem norm_clm_le_sum {n : ℕ} (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
    ‖L‖ ≤ ∑ i, ‖L (EuclideanSpace.single i 1)‖ := by
  apply L.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro x
  have hx := (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr x
  have he : L x = ∑ i, x i • L (EuclideanSpace.single i 1) := by
    conv_lhs => rw [← hx]
    simp only [map_sum, map_smul, EuclideanSpace.basisFun_repr,
      EuclideanSpace.basisFun_apply]
  rw [he, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le x i) (norm_nonneg _)

 theorem smooth_fderiv_le_norm {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : IsTestFunction Ω f) {p : ℝ} (hp : 1 ≤ p) :
    eLpNorm (fderiv ℝ f) (ENNReal.ofReal p) volume ≤
      (n : ℝ≥0∞) * sobolevNorm 1 (ENNReal.ofReal p) Ω f := by
  have hm : eLpNorm (fderiv ℝ f) (ENNReal.ofReal p) volume ≤
      eLpNorm (∑ i : Fin n, fun x => ‖partialDeriv f i x‖) (ENNReal.ofReal p) volume := by
    apply eLpNorm_mono_real
    intro x
    simpa only [Finset.sum_apply, partialDeriv] using norm_clm_le_sum (fderiv ℝ f x)
  have hs := eLpNorm_sum_le (μ := volume) (p := ENNReal.ofReal p)
    (s := Finset.univ) (f := fun i : Fin n => fun x => ‖partialDeriv f i x‖)
    (fun i _ => (test_partial hf i).1.continuous.norm.aestronglyMeasurable)
    (by simpa using ENNReal.ofReal_le_ofReal hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p)
  apply (hm.trans hs).trans
  calc
    (∑ i : Fin n, eLpNorm (fun x => ‖partialDeriv f i x‖) (ENNReal.ofReal p) volume)
      = ∑ i : Fin n, eLpNorm (partialDeriv f i) (ENNReal.ofReal p) (volume.restrict Ω) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [eLpNorm_norm, test_eLpNorm_restrict (test_partial hf i)]
    _ ≤ ∑ _i : Fin n, sobolevNorm 1 (ENNReal.ofReal p) Ω f :=
      Finset.sum_le_sum fun i _ => test_partial_le_norm hΩ (lt_of_lt_of_le zero_lt_one hp) hf i
    _ = _ := by simp [nsmul_eq_mul]

end RellichProof


open MeasureTheory
open scoped ENNReal
open HunterPDE.Shared HunterPDE.Compactness

namespace RellichProof

 theorem conjugate_pos {n : ℕ} {p : ℝ} (hp : 1 ≤ p) (hpn : p < n) :
    0 < sobolevConjugate n p := by
  unfold sobolevConjugate
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  exact div_pos (mul_pos (hp0.trans hpn) hp0) (sub_pos.mpr hpn)

 theorem smooth_sobolev_derivative_bound {n : ℕ} {p : ℝ} (hp : 1 ≤ p) (hpn : p < n) :
    ∃ C : NNReal, ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) f → HasCompactSupport f →
      eLpNorm f (ENNReal.ofReal (sobolevConjugate n p)) volume ≤
        C * eLpNorm (fderiv ℝ f) (ENNReal.ofReal p) volume := by
  let P : NNReal := ⟨p, le_trans zero_le_one hp⟩
  let R : NNReal := ⟨sobolevConjugate n p, (conjugate_pos hp hpn).le⟩
  let C : NNReal := SNormLESNormFDerivOfEqConst ℝ
    (volume : Measure (EuclideanSpace ℝ (Fin n))) P
  refine ⟨C, ?_⟩
  intro f hf hfc
  have hn : 0 < n := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hp).trans hpn
  have hi : (R : ℝ)⁻¹ = (P : ℝ)⁻¹ -
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ)⁻¹ := by
    simp only [finrank_euclideanSpace, Fintype.card_fin]
    change (sobolevConjugate n p)⁻¹ = p⁻¹ - (n : ℝ)⁻¹
    unfold sobolevConjugate
    have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    field_simp
  have hh := eLpNorm_le_eLpNorm_fderiv_of_eq
    (volume : Measure (EuclideanSpace ℝ (Fin n)))
    (hf.of_le (by simp) : ContDiff ℝ 1 f) hfc
    (p := P) (p' := R) (by exact_mod_cast hp)
    (by simpa using hn) hi
  have hP : (P : ℝ≥0∞) = ENNReal.ofReal p := by
    exact ENNReal.coe_nnreal_eq P
  have hR : (R : ℝ≥0∞) = ENNReal.ofReal (sobolevConjugate n p) :=
    ENNReal.coe_nnreal_eq R
  rw [hP, hR] at hh
  exact hh

 theorem smooth_sobolev_bound {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) {p : ℝ} (hp : 1 ≤ p) (hpn : p < n) :
    ∃ C : NNReal, ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, IsTestFunction Ω f →
      eLpNorm f (ENNReal.ofReal (sobolevConjugate n p)) volume ≤
        C * sobolevNorm 1 (ENNReal.ofReal p) Ω f := by
  obtain ⟨C, hC⟩ := smooth_sobolev_derivative_bound hp hpn
  refine ⟨C * n, fun f hf => (hC f hf.1 hf.2.1).trans ?_⟩
  simpa only [ENNReal.coe_mul, ENNReal.coe_natCast, mul_assoc] using
    mul_le_mul_right (smooth_fderiv_le_norm hΩ hf hp) (C : ℝ≥0∞)

end RellichProof


open MeasureTheory Filter Topology
open scoped ENNReal

namespace RellichProof

 theorem eLpNorm_bound_of_approximation {E : Type*} [MeasurableSpace E]
    {μ : Measure E} {p r : ℝ≥0∞} (hp : p ≠ 0) {f : E → ℝ}
    {u : ℕ → E → ℝ} (hu : ∀ j, AEStronglyMeasurable (u j) μ)
    (hf : AEStronglyMeasurable f μ)
    (hconv : Tendsto (fun j => eLpNorm (u j - f) p μ) atTop (𝓝 0))
    {b : ℕ → ℝ≥0∞} {B : ℝ≥0∞} (hb : Tendsto b atTop (𝓝 B))
    (hbound : ∀ j, eLpNorm (u j) r μ ≤ b j) : eLpNorm f r μ ≤ B := by
  obtain ⟨σ, hσ, hae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm hp hu hf hconv).exists_seq_tendsto_ae
  apply (Lp.eLpNorm_lim_le_liminf_eLpNorm (fun j => hu (σ j)) f hae).trans
  have hm := Filter.liminf_le_liminf (f := atTop)
    (Filter.Eventually.of_forall (fun j => hbound (σ j)))
  exact hm.trans_eq (hb.comp hσ.tendsto_atTop).liminf_eq

end RellichProof


open MeasureTheory
open scoped ENNReal
open HunterPDE.Shared HunterPDE.Compactness

namespace RellichProof

variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
variable {f φ : EuclideanSpace ℝ (Fin n) → ℝ}

 theorem test_component_le_comparison (hΩ : IsOpen Ω) {p : ℝ} (hp : 1 ≤ p)
    (hf : MemW 1 (ENNReal.ofReal p) Ω f) (hφ : IsTestFunction Ω φ)
    {α : Fin n → ℕ} (hα : α ∈ multiIndicesLe n 1) :
    eLpNorm (weakDeriv Ω α φ) (ENNReal.ofReal p) (volume.restrict Ω) ≤
      sobolevNorm 1 (ENNReal.ofReal p) Ω f +
      sobolevNorm 1 (ENNReal.ofReal p) Ω (f - φ) := by
  have hd := memW_sub hf (test_memW hφ (ENNReal.ofReal p))
  obtain ⟨df, hdf, _⟩ := hf α hα
  obtain ⟨dd, hdd, _⟩ := hd α hα
  have hs := weak_sub (weak_chosen ⟨df, hdf⟩) (weak_chosen ⟨dd, hdd⟩)
  have hid : f - (f - φ) = φ := by funext x; simp
  rw [hid] at hs
  rw [eLpNorm_congr_ae (weak_chosen_eq hΩ hs)]
  have hmeasf := (memW_chosen_memLp hΩ hf hα).aestronglyMeasurable
  have hmeasd := (memW_chosen_memLp hΩ hd hα).aestronglyMeasurable
  have hh : eLpNorm (weakDeriv Ω α f - weakDeriv Ω α (f - φ))
      (ENNReal.ofReal p) (volume.restrict Ω) ≤
      eLpNorm (weakDeriv Ω α f) (ENNReal.ofReal p) (volume.restrict Ω) +
      eLpNorm (weakDeriv Ω α (f - φ)) (ENNReal.ofReal p) (volume.restrict Ω) := by
    simpa only [sub_eq_add_neg, eLpNorm_neg] using
      eLpNorm_add_le hmeasf hmeasd.neg
        (by simpa using ENNReal.ofReal_le_ofReal hp)
  exact hh.trans (add_le_add
    (component_le_norm (lt_of_lt_of_le zero_lt_one hp) hα)
    (component_le_norm (lt_of_lt_of_le zero_lt_one hp) hα))

 theorem test_fderiv_le_comparison (hΩ : IsOpen Ω) {p : ℝ} (hp : 1 ≤ p)
    (hf : MemW 1 (ENNReal.ofReal p) Ω f) (hφ : IsTestFunction Ω φ) :
    eLpNorm (fderiv ℝ φ) (ENNReal.ofReal p) volume ≤
      (n : ℝ≥0∞) * (sobolevNorm 1 (ENNReal.ofReal p) Ω f +
      sobolevNorm 1 (ENNReal.ofReal p) Ω (f - φ)) := by
  have hm : eLpNorm (fderiv ℝ φ) (ENNReal.ofReal p) volume ≤
      eLpNorm (∑ i : Fin n, fun x => ‖partialDeriv φ i x‖) (ENNReal.ofReal p) volume := by
    apply eLpNorm_mono_real
    intro x
    simpa only [Finset.sum_apply, partialDeriv] using norm_clm_le_sum (fderiv ℝ φ x)
  have hs := eLpNorm_sum_le (μ := volume) (p := ENNReal.ofReal p)
    (s := Finset.univ) (f := fun i : Fin n => fun x => ‖partialDeriv φ i x‖)
    (fun i _ => (test_partial hφ i).1.continuous.norm.aestronglyMeasurable)
    (by simpa using ENNReal.ofReal_le_ofReal hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p)
  apply (hm.trans hs).trans
  calc
    _ = ∑ i : Fin n, eLpNorm (weakDeriv Ω (Pi.single i 1) φ)
        (ENNReal.ofReal p) (volume.restrict Ω) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [eLpNorm_norm, ← test_eLpNorm_restrict (test_partial hφ i),
        eLpNorm_congr_ae (weak_chosen_eq hΩ (test_weak_partial hφ i))]
    _ ≤ ∑ _i : Fin n, (sobolevNorm 1 (ENNReal.ofReal p) Ω f +
        sobolevNorm 1 (ENNReal.ofReal p) Ω (f - φ)) :=
      Finset.sum_le_sum fun i _ => test_component_le_comparison hΩ hp hf hφ
        (single_mem_multiIndices i)
    _ = _ := by simp [nsmul_eq_mul, mul_add]

 theorem smooth_comparison_bound (hΩ : IsOpen Ω) {p : ℝ} (hp : 1 ≤ p) (hpn : p < n) :
    ∃ C : NNReal, ∀ f φ : EuclideanSpace ℝ (Fin n) → ℝ,
      MemW 1 (ENNReal.ofReal p) Ω f → IsTestFunction Ω φ →
      eLpNorm φ (ENNReal.ofReal (sobolevConjugate n p)) volume ≤
        C * (sobolevNorm 1 (ENNReal.ofReal p) Ω f +
          sobolevNorm 1 (ENNReal.ofReal p) Ω (f - φ)) := by
  obtain ⟨C, hC⟩ := smooth_sobolev_derivative_bound hp hpn
  refine ⟨C * n, fun f φ hf hφ => (hC φ hφ.1 hφ.2.1).trans ?_⟩
  simpa only [ENNReal.coe_mul, ENNReal.coe_natCast, mul_assoc] using
    mul_le_mul_right (test_fderiv_le_comparison hΩ hp hf hφ) (C : ℝ≥0∞)

end RellichProof


open MeasureTheory Filter Topology
open scoped ENNReal
open HunterPDE.Shared HunterPDE.Compactness

namespace RellichProof

 theorem exists_test_sequence {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {p : ℝ≥0∞} {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemW0 1 p Ω f) :
    ∃ φ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ, (∀ j, IsTestFunction Ω (φ j)) ∧
      ∀ j, sobolevNorm 1 p Ω (f - φ j) ≤ (((j + 1 : ℕ) : ℝ≥0∞)⁻¹) := by
  have hpos (j : ℕ) : 0 < (((j + 1 : ℕ) : ℝ≥0∞)⁻¹) :=
    ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top (j + 1))
  choose φ hφ he using fun j => hf.2 _ (hpos j)
  exact ⟨φ, hφ, fun j => (he j).le⟩

 theorem test_error_norm {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) {p : ℝ} (hp : 0 < p)
    {f φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : MemW 1 (ENNReal.ofReal p) Ω f) (hφ : IsTestFunction Ω φ) :
    eLpNorm (φ - Ω.indicator f) (ENNReal.ofReal p) volume ≤
      sobolevNorm 1 (ENNReal.ofReal p) Ω (f - φ) := by
  have he : φ - Ω.indicator f = -(Ω.indicator (f - φ)) := by
    funext x
    by_cases hx : x ∈ Ω
    · simp only [Pi.sub_apply, Pi.neg_apply, Set.indicator_of_mem hx, neg_sub]
    · have hz : φ x = 0 := by
        by_contra h
        exact hx (hφ.2.2 (subset_tsupport _ h))
      simp only [Pi.sub_apply, Pi.neg_apply, Set.indicator_of_notMem hx, hz, sub_zero, neg_zero]
  rw [he, eLpNorm_neg, eLpNorm_indicator_eq_eLpNorm_restrict hΩ.measurableSet]
  exact zero_le_norm hΩ hp (memW_sub hf (test_memW hφ _))

 theorem inverse_error_tendsto {a : ℕ → ℝ≥0∞}
    (ha : ∀ j, a j ≤ (((j + 1 : ℕ) : ℝ≥0∞)⁻¹)) : Tendsto a atTop (𝓝 0) := by
  have he : Tendsto (fun j : ℕ => (((j + 1 : ℕ) : ℝ≥0∞)⁻¹)) atTop (𝓝 0) :=
    ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds he
    (fun _ => bot_le) ha

 theorem scaled_error_tendsto (C : NNReal) (A : ℝ≥0∞) :
    Tendsto (fun j : ℕ => (C : ℝ≥0∞) * (A + (((j + 1 : ℕ) : ℝ≥0∞)⁻¹)))
      atTop (𝓝 ((C : ℝ≥0∞) * A)) := by
  have he : Tendsto (fun j : ℕ => (((j + 1 : ℕ) : ℝ≥0∞)⁻¹)) atTop (𝓝 0) :=
    ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  have ha : Tendsto (fun j : ℕ => A + (((j + 1 : ℕ) : ℝ≥0∞)⁻¹))
      atTop (𝓝 (A + 0)) := tendsto_const_nhds.add he
  have hh := ENNReal.Tendsto.const_mul (a := (C : ℝ≥0∞)) ha (Or.inr ENNReal.coe_ne_top)
  simpa only [add_zero] using hh

 theorem memW_indicator_measurable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) {p : ℝ≥0∞} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : MemW 1 p Ω f) : AEStronglyMeasurable (Ω.indicator f) volume := by
  have hmem : MemLp (Ω.indicator f) p volume :=
    (memLp_indicator_iff_restrict hΩ.measurableSet).2 (memW_zero_memLp hΩ hf)
  exact hmem.aestronglyMeasurable

 theorem test_sequence_tendsto {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) {p : ℝ} (hp : 0 < p) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : MemW 1 (ENNReal.ofReal p) Ω f) (φ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hφ : ∀ j, IsTestFunction Ω (φ j))
    (hc : ∀ j, sobolevNorm 1 (ENNReal.ofReal p) Ω (f - φ j) ≤
      (((j + 1 : ℕ) : ℝ≥0∞)⁻¹)) :
    Tendsto (fun j => eLpNorm (φ j - Ω.indicator f) (ENNReal.ofReal p) volume)
      atTop (𝓝 0) := by
  apply inverse_error_tendsto
  intro j
  exact (test_error_norm hΩ hp hf (hφ j)).trans (hc j)

 theorem native_bound_from_smooth_comparison {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) {p : ℝ} (hp : 0 < p) {r : ℝ≥0∞}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemW0 1 (ENNReal.ofReal p) Ω f)
    (C : NNReal)
    (hC : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ, IsTestFunction Ω φ →
      eLpNorm φ r volume ≤ C * (sobolevNorm 1 (ENNReal.ofReal p) Ω f +
        sobolevNorm 1 (ENNReal.ofReal p) Ω (f - φ))) :
    eLpNorm (Ω.indicator f) r volume ≤ C * sobolevNorm 1 (ENNReal.ofReal p) Ω f := by
  obtain ⟨φ, hφ, hclose⟩ := exists_test_sequence hf
  have hmeas : AEStronglyMeasurable (Ω.indicator f) volume := memW_indicator_measurable hΩ hf.1
  have hconv := test_sequence_tendsto hΩ hp hf.1 φ hφ hclose
  let A : ℝ≥0∞ := sobolevNorm 1 (ENNReal.ofReal p) Ω f
  let b : ℕ → ℝ≥0∞ := fun j => (C : ℝ≥0∞) * (A + (((j + 1 : ℕ) : ℝ≥0∞)⁻¹))
  have hb : Tendsto b atTop (𝓝 ((C : ℝ≥0∞) * A)) := scaled_error_tendsto C A
  have hbound : ∀ j, eLpNorm (φ j) r volume ≤ b j := by
    intro j
    exact (hC (φ j) (hφ j)).trans
      (mul_le_mul_right (add_le_add_right (hclose j) A) (C : ℝ≥0∞))
  exact eLpNorm_bound_of_approximation (μ := volume) (p := ENNReal.ofReal p)
    (r := r) (f := Ω.indicator f) (u := φ) (b := b) (B := (C : ℝ≥0∞) * A)
    (ENNReal.ofReal_ne_zero_iff.mpr hp)
    (fun j => (hφ j).1.continuous.aestronglyMeasurable) hmeas hconv hb hbound

 theorem native_sobolev_bound {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) {p : ℝ} (hp : 1 ≤ p) (hpn : p < n) :
    ∃ C : NNReal, ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
      MemW0 1 (ENNReal.ofReal p) Ω f →
      eLpNorm (Ω.indicator f) (ENNReal.ofReal (sobolevConjugate n p)) volume ≤
        C * sobolevNorm 1 (ENNReal.ofReal p) Ω f := by
  obtain ⟨C, hC⟩ := smooth_comparison_bound (n := n) (Ω := Ω) (p := p) hΩ hp hpn
  refine ⟨C, ?_⟩
  intro f hf
  exact native_bound_from_smooth_comparison hΩ (lt_of_lt_of_le zero_lt_one hp) hf C
    (fun φ hφ => hC f φ hf.1 hφ)

end RellichProof


open MeasureTheory
open scoped ENNReal
open HunterPDE.Shared HunterPDE.Compactness

namespace RellichProof

 theorem restricted_exponent_bound {G : Type*} [NormedAddCommGroup G] {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩb : Bornology.IsBounded Ω) {q r : ℝ≥0∞} (hq : 0 < q)
    (hqr : q ≤ r) (hr : r ≠ ⊤) :
    ∃ K : NNReal, ∀ f : EuclideanSpace ℝ (Fin n) → G,
      AEStronglyMeasurable f (volume.restrict Ω) →
      eLpNorm f q (volume.restrict Ω) ≤ K * eLpNorm f r (volume.restrict Ω) := by
  have hqt : q ≠ ⊤ := (lt_of_le_of_lt hqr (lt_top_iff_ne_top.mpr hr)).ne
  have he : 0 ≤ 1 / q.toReal - 1 / r.toReal := by
    apply sub_nonneg.mpr
    exact one_div_le_one_div_of_le (ENNReal.toReal_pos hq.ne' hqt)
      (ENNReal.toReal_mono hr hqr)
  let k : ℝ≥0∞ := volume Ω ^ (1 / q.toReal - 1 / r.toReal)
  have hk : k ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg he hΩb.measure_lt_top.ne
  refine ⟨k.toNNReal, ?_⟩
  intro f hf
  have hh := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hqr hf
  simpa only [Measure.restrict_apply_univ, ENNReal.coe_toNNReal hk, mul_comm] using hh

 theorem native_q_bound {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) {p : ℝ}
    (hp : 1 ≤ p) (hpn : p < n) {q : ℝ≥0∞} (hq : 0 < q)
    (hqr : q ≤ ENNReal.ofReal (sobolevConjugate n p)) :
    ∃ C : NNReal, ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
      MemW0 1 (ENNReal.ofReal p) Ω f →
      eLpNorm (Ω.indicator f) q volume ≤
        C * sobolevNorm 1 (ENNReal.ofReal p) Ω f := by
  obtain ⟨K, hK⟩ := restricted_exponent_bound (G := ℝ) hΩb hq hqr ENNReal.ofReal_ne_top
  obtain ⟨C, hC⟩ := native_sobolev_bound hΩ hp hpn
  refine ⟨K * C, ?_⟩
  intro f hf
  have hh := hK f (memW_zero_memLp hΩ hf.1).aestronglyMeasurable
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict hΩ.measurableSet,
    ← eLpNorm_indicator_eq_eLpNorm_restrict hΩ.measurableSet] at hh
  apply hh.trans
  simpa only [ENNReal.coe_mul, mul_assoc] using
    mul_le_mul_right (hC f hf) (K : ℝ≥0∞)

 theorem native_q_memLp {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) {p : ℝ}
    (hp : 1 ≤ p) (hpn : p < n) {q : ℝ≥0∞} (hq : 0 < q)
    (hqr : q ≤ ENNReal.ofReal (sobolevConjugate n p))
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemW0 1 (ENNReal.ofReal p) Ω f)
    (hfin : sobolevNorm 1 (ENNReal.ofReal p) Ω f < ⊤) :
    MemLp (Ω.indicator f) q volume := by
  obtain ⟨C, hC⟩ := native_q_bound hΩ hΩb hp hpn hq hqr
  refine ⟨((memLp_indicator_iff_restrict hΩ.measurableSet).2
    (memW_zero_memLp hΩ hf.1)).aestronglyMeasurable, ?_⟩
  exact (hC f hf).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hfin)

end RellichProof


open MeasureTheory
open scoped ENNReal
open HunterPDE.Shared HunterPDE.Compactness

namespace RellichProof

 theorem native_approximation {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) {p : ℝ}
    (hp : 1 ≤ p) (hpn : p < n) {q : ℝ≥0∞} (hq : 0 < q)
    (hqr : q ≤ ENNReal.ofReal (sobolevConjugate n p)) (M : NNReal) :
    ∃ C : NNReal, 0 < C ∧ ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
      MemW0 1 (ENNReal.ofReal p) Ω f → sobolevNorm 1 (ENNReal.ofReal p) Ω f ≤ M →
      ∀ δ : ℝ≥0∞, 0 < δ → ∃ φ, IsTestFunction Ω φ ∧
        eLpNorm (Ω.indicator f - φ) q volume < δ ∧
        eLpNorm φ 1 volume ≤ C ∧ eLpNorm (fderiv ℝ φ) 1 volume ≤ C ∧
        eLpNorm φ (ENNReal.ofReal (sobolevConjugate n p)) volume ≤ C := by
  obtain ⟨Q, hQ⟩ := native_q_bound hΩ hΩb hp hpn hq hqr
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp
  obtain ⟨K, hK⟩ := restricted_exponent_bound (G := ℝ) hΩb zero_lt_one hp1
    ENNReal.ofReal_ne_top
  obtain ⟨D, hD⟩ := restricted_exponent_bound
    (G := EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) hΩb zero_lt_one hp1 ENNReal.ofReal_ne_top
  obtain ⟨S, hS⟩ := smooth_comparison_bound hΩ hp hpn
  let C : NNReal := 1 + K * (M + 1) + D * n * (M + 1) + S * (M + 1)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro f hf hMf δ hδ
  obtain ⟨η, hη, hηδ⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (a := (Q : ℝ≥0∞)) ENNReal.coe_ne_top hδ.ne'
  obtain ⟨φ, hφ, herr⟩ := hf.2 (↑(min η 1 : NNReal)) (by exact_mod_cast lt_min hη zero_lt_one)
  have he1 : sobolevNorm 1 (ENNReal.ofReal p) Ω (f - φ) ≤ 1 :=
    herr.le.trans (by exact_mod_cast min_le_right η 1)
  have heη : sobolevNorm 1 (ENNReal.ofReal p) Ω (f - φ) ≤ (η : ℝ≥0∞) :=
    herr.le.trans (by exact_mod_cast min_le_left η 1)
  have hs : sobolevNorm 1 (ENNReal.ofReal p) Ω f +
      sobolevNorm 1 (ENNReal.ofReal p) Ω (f - φ) ≤ ((M + 1 : NNReal) : ℝ≥0∞) := by
    simpa only [ENNReal.coe_add, ENNReal.coe_one] using add_le_add hMf he1
  have hid : Ω.indicator f - φ = Ω.indicator (f - φ) := by
    rw [← test_indicator hφ]
    ext x
    by_cases hx : x ∈ Ω <;> simp [hx]
  refine ⟨φ, hφ, ?_, ?_, ?_, ?_⟩
  · rw [hid]
    exact ((hQ (f - φ) (memW0_sub_test hf hφ)).trans
      (mul_le_mul_right heη _)).trans_lt (by simpa only [mul_comm] using hηδ)
  · have hzero : eLpNorm φ (ENNReal.ofReal p) (volume.restrict Ω) ≤
        ((M + 1 : NNReal) : ℝ≥0∞) := by
      have hh := test_component_le_comparison hΩ hp hf.1 hφ (zero_mem_multiIndices n)
      rw [eLpNorm_congr_ae (weak_chosen_eq hΩ
        (weak_zero (hφ.1.continuous.locallyIntegrable.locallyIntegrableOn Ω)))] at hh
      exact hh.trans hs
    rw [← test_eLpNorm_restrict hφ]
    apply ((hK φ hφ.1.continuous.aestronglyMeasurable).trans
      (mul_le_mul_right hzero _)).trans
    change ((K * (M + 1) : NNReal) : ℝ≥0∞) ≤ (C : ℝ≥0∞)
    exact_mod_cast (show K * (M + 1) ≤ C by
      dsimp [C]
      exact (le_add_of_nonneg_left (show (0 : NNReal) ≤ 1 from zero_le_one)).trans
        ((le_add_of_nonneg_right (show (0 : NNReal) ≤ D * n * (M + 1) from bot_le)).trans
          (le_add_of_nonneg_right bot_le)))
  · have hsupp : Function.support (fderiv ℝ φ) ⊆ Ω :=
      (subset_tsupport _).trans ((tsupport_fderiv_subset ℝ).trans hφ.2.2)
    have hrestrict := eLpNorm_restrict_eq_of_support_subset (p := (1 : ℝ≥0∞))
      (μ := volume) (f := fderiv ℝ φ) hsupp
    rw [← hrestrict]
    have hder := (test_fderiv_le_comparison hΩ hp hf.1 hφ).trans (mul_le_mul_right hs n)
    rw [← eLpNorm_restrict_eq_of_support_subset (p := ENNReal.ofReal p)
      (μ := volume) (f := fderiv ℝ φ) hsupp] at hder
    apply ((hD (fderiv ℝ φ) (hφ.1.continuous_fderiv (by simp)).aestronglyMeasurable).trans
      (mul_le_mul_right hder _)).trans
    have hc : ((D * n * (M + 1) : NNReal) : ℝ≥0∞) ≤ (C : ℝ≥0∞) := by
      exact_mod_cast (show D * n * (M + 1) ≤ C by
        dsimp [C]
        exact (le_add_of_nonneg_left (show (0 : NNReal) ≤ 1 + K * (M + 1) from bot_le)).trans
          (le_add_of_nonneg_right bot_le))
    simpa only [ENNReal.coe_mul, ENNReal.coe_natCast, mul_assoc] using hc
  · apply ((hS f φ hf.1 hφ).trans (mul_le_mul_right hs _)).trans
    change ((S * (M + 1) : NNReal) : ℝ≥0∞) ≤ (C : ℝ≥0∞)
    exact_mod_cast (show S * (M + 1) ≤ C by
      dsimp [C]
      exact le_add_of_nonneg_left bot_le)

end RellichProof


namespace RellichProof

open Set Metric

theorem totallyBounded_of_approximations {E : Type*} [PseudoMetricSpace E] (S : Set E)
    (h : ∀ ε : ℝ, 0 < ε → ∃ T : Set E, TotallyBounded T ∧
      ∀ x ∈ S, ∃ y ∈ T, dist x y < ε) : TotallyBounded S := by
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨T, hT, ha⟩ := h (ε / 2) (half_pos hε)
  obtain ⟨U, hU, hcover⟩ := Metric.totallyBounded_iff.mp hT (ε / 2) (half_pos hε)
  refine ⟨U, hU, ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := ha x hx
  obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.mp (hcover hy)
  apply Set.mem_iUnion₂.mpr
  refine ⟨z, hz, ?_⟩
  change dist x z < ε
  have := dist_triangle x y z
  change dist y z < ε / 2 at hyz
  linarith

theorem compact_closure_of_approximations {E : Type*} [MetricSpace E] [CompleteSpace E]
    (S : Set E)
    (h : ∀ ε : ℝ, 0 < ε → ∃ T : Set E, IsCompact T ∧
      ∀ x ∈ S, ∃ y ∈ T, dist x y < ε) : IsCompact (closure S) := by
  apply TotallyBounded.isCompact_of_isClosed _ isClosed_closure
  apply TotallyBounded.closure
  apply totallyBounded_of_approximations S
  intro ε hε
  obtain ⟨T, hT, ha⟩ := h ε hε
  exact ⟨T, hT.totallyBounded, ha⟩

end RellichProof


open MeasureTheory

namespace RellichProof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem segment_derivative {u : E → ℝ} (hu : ContDiff ℝ 1 u) (x h : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => u (x + s • h)) (fderiv ℝ u (x + t • h) h) t := by
  convert (hu.differentiable one_ne_zero (x + t • h)).hasFDerivAt.comp_hasDerivAt t
    (((hasDerivAt_id t).smul_const h).const_add x) using 1 <;>
    first | rfl | simp only [one_smul]

theorem segment_integral {u : E → ℝ} (hu : ContDiff ℝ 1 u) (x h : E) :
    (∫ t : ℝ in 0..1, fderiv ℝ u (x + t • h) h) = u (x + h) - u x := by
  have hc : Continuous (fun t : ℝ => fderiv ℝ u (x + t • h) h) :=
    ((hu.continuous_fderiv one_ne_zero).comp (continuous_const.add
      (continuous_id.smul continuous_const))).clm_apply continuous_const
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => segment_derivative hu x h t) (hc.intervalIntegrable 0 1)

theorem segment_norm_bound {u : E → ℝ} (hu : ContDiff ℝ 1 u) (x h : E) :
    ‖u (x + h) - u x‖ ≤
      (∫ t : ℝ in 0..1, ‖fderiv ℝ u (x + t • h)‖) * ‖h‖ := by
  have hc : Continuous (fun t : ℝ => fderiv ℝ u (x + t • h)) :=
    (hu.continuous_fderiv one_ne_zero).comp
      (continuous_const.add (continuous_id.smul continuous_const))
  rw [← segment_integral hu x h]
  calc
    _ ≤ ∫ t : ℝ in 0..1, ‖fderiv ℝ u (x + t • h) h‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ t : ℝ in 0..1, ‖fderiv ℝ u (x + t • h)‖ * ‖h‖ :=
      intervalIntegral.integral_mono_on (by norm_num)
        ((hc.clm_apply (continuous_const : Continuous (fun _ : ℝ => h))).norm.intervalIntegrable 0 1)
        ((hc.norm.mul continuous_const).intervalIntegrable 0 1)
        (fun t _ => (fderiv ℝ u (x + t • h)).le_opNorm h)
    _ = _ := intervalIntegral.integral_mul_const _ _

end RellichProof


open MeasureTheory Set

namespace RellichProof

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

theorem integrable_translate {g : E → ℝ} (hg : Continuous g)
    (hs : HasCompactSupport g) (h : E) : Integrable (fun x => g (x + h)) :=
  (hg.comp (continuous_add_const h)).integrable_of_hasCompactSupport
    (hs.comp_homeomorph (Homeomorph.addRight h))

theorem translation_average_integrable {g : E → ℝ} (hg : Continuous g)
    (hs : HasCompactSupport g) (h : E) :
    Integrable (fun p : E × ℝ => g (p.1 + p.2 • h))
      (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  have hc : Continuous (fun p : E × ℝ => g (p.1 + p.2 • h)) :=
    hg.comp (continuous_fst.add (continuous_snd.smul continuous_const))
  apply (integrable_prod_iff' hc.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall fun t => integrable_translate hg hs (t • h)
  · have he : (fun t : ℝ => ∫ x : E, ‖g (x + t • h)‖) =
        fun _ => ∫ x : E, ‖g x‖ := by
      funext t
      exact integral_add_right_eq_self (fun x : E => ‖g x‖) (t • h)
    rw [he]
    exact integrable_const _

theorem translation_average_integral {g : E → ℝ} (hg : Continuous g)
    (hs : HasCompactSupport g) (h : E) :
    (∫ x : E, ∫ t : ℝ in 0..1, g (x + t • h)) = ∫ x : E, g x := by
  simp only [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  rw [integral_integral_swap (translation_average_integrable hg hs h)]
  simp only [integral_add_right_eq_self]
  simp

theorem translation_l1_bound {u : E → ℝ} (hu : ContDiff ℝ 1 u)
    (hs : HasCompactSupport u) (h : E) :
    (∫ x : E, ‖u (x + h) - u x‖) ≤ (∫ x : E, ‖fderiv ℝ u x‖) * ‖h‖ := by
  have hd := hu.continuous_fderiv one_ne_zero
  have hds := hs.fderiv ℝ
  have hj := translation_average_integrable hd.norm hds.norm h
  have hi : Integrable (fun x : E => ∫ t : ℝ in 0..1, ‖fderiv ℝ u (x + t • h)‖) := by
    simpa only [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using
      hj.integral_prod_left
  calc
    _ ≤ ∫ x : E, (∫ t : ℝ in 0..1, ‖fderiv ℝ u (x + t • h)‖) * ‖h‖ :=
      integral_mono ((integrable_translate hu.continuous hs h).sub
        (hu.continuous.integrable_of_hasCompactSupport hs)).norm
        (hi.mul_const _) (fun x => segment_norm_bound hu x h)
    _ = _ := by rw [integral_mul_const, translation_average_integral hd.norm hds.norm h]

end RellichProof


open MeasureTheory

namespace RellichProof

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

noncomputable def smoothAverage (κ u : E → ℝ) (x : E) : ℝ :=
  ∫ y, κ (x - y) * u y

theorem smoothAverage_integrand {κ u : E → ℝ} (hκ : Continuous κ)
    (hu : Continuous u) (hs : HasCompactSupport u) (x : E) :
    Integrable (fun y => κ (x-y) * u y) := by
  exact ((hκ.comp (continuous_const.sub continuous_id)).mul hu).integrable_of_hasCompactSupport
    hs.mul_left

theorem smoothAverage_bound {κ u : E → ℝ} (hκ : Continuous κ)
    (hu : Continuous u) (hs : HasCompactSupport u) {B : ℝ}
    (hB : ∀ x, ‖κ x‖ ≤ B) (x : E) :
    ‖smoothAverage κ u x‖ ≤ B * ∫ y, ‖u y‖ := by
  have hi : Integrable u := hu.integrable_of_hasCompactSupport hs
  calc
    _ ≤ ∫ y, ‖κ (x-y) * u y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, B * ‖u y‖ := integral_mono
      (smoothAverage_integrand hκ hu hs x).norm (hi.norm.const_mul B)
      (fun y => by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _))
    _ = _ := integral_const_mul _ _

theorem smoothAverage_difference {κ u : E → ℝ} (hκ : Continuous κ)
    (hu : Continuous u) (hs : HasCompactSupport u) {L : ℝ}
    (hL : ∀ x y, ‖κ x - κ y‖ ≤ L * ‖x-y‖) (x z : E) :
    ‖smoothAverage κ u x - smoothAverage κ u z‖ ≤
      (L * ∫ y, ‖u y‖) * ‖x-z‖ := by
  have hi : Integrable u := hu.integrable_of_hasCompactSupport hs
  have hx := smoothAverage_integrand hκ hu hs x
  have hz := smoothAverage_integrand hκ hu hs z
  rw [smoothAverage, smoothAverage, ← integral_sub hx hz]
  calc
    _ ≤ ∫ y, ‖κ (x-y) * u y - κ (z-y) * u y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, (L * ‖x-z‖) * ‖u y‖ := integral_mono (hx.sub hz).norm
      (hi.norm.const_mul _) (fun y => by
        rw [← sub_mul, norm_mul]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        simpa only [sub_sub_sub_cancel_right] using hL (x-y) (z-y))
    _ = _ := by rw [integral_const_mul]; ring

end RellichProof


open MeasureTheory ContinuousLinearMap
open scoped Convolution

namespace RellichProof

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

theorem smoothAverage_eq {κ u : E → ℝ} (x : E) :
    smoothAverage κ u x = ∫ y, κ y * u (x-y) := by
  have h := convolution_lsmul_swap (μ := (volume : Measure E)) (f := κ) (g := u) (x := x)
  simpa only [smoothAverage, convolution_lsmul, smul_eq_mul] using h.symm

theorem defect_integrable {κ u : E → ℝ} (hκ : Integrable κ) (hu : Integrable u) :
    Integrable (fun z : E × E => κ z.2 * (u (z.1-z.2) - u z.1))
      (volume.prod volume) := by
  have h1 := hκ.convolution_integrand (lsmul ℝ ℝ) hu
  have h2 := hu.mul_prod hκ
  convert h1.sub h2 using 1
  funext z
  simp only [Pi.sub_apply, lsmul_apply, smul_eq_mul, mul_sub]
  ring

theorem mollifier_l1_error {κ u : E → ℝ} (hκ : Continuous κ)
    (hκs : HasCompactSupport κ) (hκ0 : ∀ y, 0 ≤ κ y) (hκ1 : ∫ y, κ y = 1)
    (hu : ContDiff ℝ 1 u) (hus : HasCompactSupport u) :
    (∫ x, ‖smoothAverage κ u x - u x‖) ≤
      (∫ y, κ y * ‖y‖) * (∫ x, ‖fderiv ℝ u x‖) := by
  have hki : Integrable κ := hκ.integrable_of_hasCompactSupport hκs
  have hui : Integrable u := hu.continuous.integrable_of_hasCompactSupport hus
  have hd := defect_integrable hki hui
  have hpoint (x : E) : smoothAverage κ u x - u x =
      ∫ y, κ y * (u (x-y) - u x) := by
    simp_rw [mul_sub]
    rw [smoothAverage_eq, integral_sub]
    · simp only [integral_mul_const, hκ1, one_mul]
    · exact (hκs.convolutionExists_left_of_continuous_right (lsmul ℝ ℝ)
        hki.locallyIntegrable hu.continuous x)
    · exact hki.mul_const _
  have hbound (y : E) : (∫ x, ‖κ y * (u (x-y) - u x)‖) ≤
      κ y * ‖y‖ * (∫ x, ‖fderiv ℝ u x‖) := by
    simp only [norm_mul, Real.norm_of_nonneg (hκ0 y), integral_const_mul]
    have h := translation_l1_bound hu hus (-y)
    simp only [← sub_eq_add_neg, norm_neg] at h
    nlinarith [mul_le_mul_of_nonneg_left h (hκ0 y)]
  have hmoment : Integrable (fun y => κ y * ‖y‖) :=
    (hκ.mul continuous_norm).integrable_of_hasCompactSupport hκs.mul_right
  calc
    _ ≤ ∫ x, ∫ y, ‖κ y * (u (x-y) - u x)‖ := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun x => norm_nonneg _
      · exact hd.norm.integral_prod_left
      · exact Filter.Eventually.of_forall fun x => by dsimp only; rw [hpoint]; exact norm_integral_le_integral_norm _
    _ = ∫ y, ∫ x, ‖κ y * (u (x-y) - u x)‖ := integral_integral_swap hd.norm
    _ ≤ ∫ y, (κ y * ‖y‖) * (∫ x, ‖fderiv ℝ u x‖) :=
      integral_mono hd.norm.integral_prod_right (hmoment.mul_const _) hbound
    _ = _ := integral_mul_const _ _

end RellichProof


open Set Metric Filter BoundedContinuousFunction
open scoped Topology

namespace RellichProof

variable {E : Type*} [MetricSpace E]

theorem supported_totallyBounded (K : Set E) (hK : IsCompact K)
    (A : Set (E →ᵇ ℝ)) (B L : ℝ)
    (hs : ∀ f ∈ A, ∀ x ∉ K, f x = 0)
    (hb : ∀ f ∈ A, ∀ x, ‖f x‖ ≤ B)
    (hl : ∀ f ∈ A, ∀ x y, dist (f x) (f y) ≤ L * dist x y) :
    TotallyBounded A := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let R : A → (K →ᵇ ℝ) := fun f => f.1.compContinuous ⟨Subtype.val, continuous_subtype_val⟩
  have hiso : Isometry R := by
    apply Isometry.of_dist_eq
    intro f g
    apply le_antisymm
    · exact (BoundedContinuousFunction.dist_le dist_nonneg).mpr fun x =>
        BoundedContinuousFunction.dist_coe_le_dist x.1
    · apply (BoundedContinuousFunction.dist_le dist_nonneg).mpr
      intro x
      by_cases hx : x ∈ K
      · exact BoundedContinuousFunction.dist_coe_le_dist (f := R f) (g := R g) ⟨x,hx⟩
      · rw [hs f.1 f.2 x hx, hs g.1 g.2 x hx, dist_self]
        exact dist_nonneg
  have heq : Equicontinuous ((↑) : range R → K → ℝ) := by
    apply UniformEquicontinuous.equicontinuous
    apply Metric.uniformEquicontinuous_of_continuity_modulus (fun t => L*t)
      (by simpa only [mul_zero] using (show Continuous (fun t : ℝ => L*t) from continuous_const.mul continuous_id).tendsto (0 : ℝ))
    intro x y f
    obtain ⟨g,hg⟩ := f.2
    rw [← hg]
    exact hl g.1 g.2 x.1 y.1
  have hcompact : IsCompact (closure (range R)) :=
    BoundedContinuousFunction.arzela_ascoli (closedBall 0 B) (isCompact_closedBall 0 B)
      (range R) (by
        intro f x hf
        obtain ⟨g,rfl⟩ := hf
        rw [mem_closedBall, dist_zero_right]
        change ‖g.1 x.1‖ ≤ B
        exact hb g.1 g.2 x.1) heq
  have ht : TotallyBounded (Set.univ : Set A) :=
    (totallyBounded_image_iff hiso.isUniformInducing).mp
      (by simpa only [image_univ] using hcompact.totallyBounded.subset subset_closure)
  simpa only [Subtype.range_coe_subtype, image_univ, ofPred_mem_eq] using
    ht.image (f := (Subtype.val : A → (E →ᵇ ℝ))) uniformContinuous_subtype_val

end RellichProof


open MeasureTheory Set BoundedContinuousFunction

namespace RellichProof

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

theorem cutoff_integrable (K : Set E) (hK : IsCompact K) (f : E →ᵇ ℝ) :
    Integrable (K.indicator f) :=
  (integrable_indicator_iff hK.measurableSet).mpr
    (f.continuous.continuousOn.integrableOn_compact hK)

noncomputable def cutoffL1 (K : Set E) (hK : IsCompact K) (f : E →ᵇ ℝ) :
    Lp ℝ 1 (volume : Measure E) := (cutoff_integrable K hK f).toL1 (K.indicator f)

theorem cutoffL1_dist (K : Set E) (hK : IsCompact K) (f g : E →ᵇ ℝ) :
    dist (cutoffL1 K hK f) (cutoffL1 K hK g) ≤ volume.real K * dist f g := by
  rw [L1.dist_eq_integral_dist]
  have he : (fun x => dist (cutoffL1 K hK f x) (cutoffL1 K hK g x)) =ᵐ[volume]
      K.indicator (fun x => dist (f x) (g x)) := by
    filter_upwards [(cutoff_integrable K hK f).coeFn_toL1,
      (cutoff_integrable K hK g).coeFn_toL1] with x hx hy
    change dist ((cutoff_integrable K hK f).toL1 _ x)
      ((cutoff_integrable K hK g).toL1 _ x) = _
    rw [hx,hy]
    by_cases h : x ∈ K <;> simp [h]
  rw [integral_congr_ae he, integral_indicator hK.measurableSet]
  calc
    _ ≤ ∫ _ in K, dist f g := integral_mono
      ((f.continuous.dist g.continuous).continuousOn.integrableOn_compact hK)
      (integrableOn_const hK.measure_lt_top.ne)
      (fun x => BoundedContinuousFunction.dist_coe_le_dist x)
    _ = _ := by simp [Measure.real, mul_comm]

theorem cutoffL1_uniformContinuous (K : Set E) (hK : IsCompact K) :
    UniformContinuous (cutoffL1 K hK) := by
  have h : LipschitzWith ⟨volume.real K, ENNReal.toReal_nonneg⟩ (cutoffL1 K hK) :=
    LipschitzWith.of_dist_le_mul (cutoffL1_dist K hK)
  exact h.uniformContinuous

end RellichProof


open MeasureTheory
open scoped ENNReal

namespace RellichProof

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem integral_power_interpolation {f : X → ℝ} (hf : AEStronglyMeasurable f μ)
    {r a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) (hr : 0 ≤ r) :
    (∫⁻ x, ‖f x‖ₑ ^ (a+r*b) ∂μ) ≤
      (∫⁻ x, ‖f x‖ₑ ∂μ)^a * (∫⁻ x, ‖f x‖ₑ ^ r ∂μ)^b := by
  have h := ENNReal.lintegral_mul_norm_pow_le hf.enorm (hf.enorm.pow_const r) ha hb hab
  convert h using 1
  apply lintegral_congr
  intro x
  rw [← ENNReal.rpow_mul]
  exact ENNReal.rpow_add_of_nonneg _ _ ha (mul_nonneg hr hb)

theorem seminorm_interpolation {f : X → ℝ} (hf : AEStronglyMeasurable f μ)
    {q r a b : ℝ} (hq : 0 < q) (hr : 0 < r)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) (he : q=a+r*b) :
    eLpNorm' f q μ ≤ eLpNorm' f 1 μ ^ (a/q) * eLpNorm' f r μ ^ (r*b/q) := by
  rw [eLpNorm'_eq_lintegral_enorm, eLpNorm'_eq_lintegral_enorm,
    eLpNorm'_eq_lintegral_enorm]
  simp only [div_one, ENNReal.rpow_one]
  calc
    _ ≤ ((∫⁻ x, ‖f x‖ₑ ∂μ)^a * (∫⁻ x, ‖f x‖ₑ ^ r ∂μ)^b)^(1/q) := by
      apply ENNReal.rpow_le_rpow _ (by positivity)
      rw [he]
      exact integral_power_interpolation hf ha hb hab hr.le
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      congr 2 <;> field_simp

end RellichProof


open MeasureTheory Set Metric

namespace RellichProof

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

theorem compact_function_bound {G : Type*} [NormedAddCommGroup G]
    {f : E → G} (hf : Continuous f) (hs : HasCompactSupport f) :
    ∃ B : NNReal, ∀ x, ‖f x‖ ≤ B := by
  obtain ⟨B,hB⟩ := hs.bddAbove_image hf.norm.continuousOn
  refine ⟨⟨max B 0, le_max_right _ _⟩, fun x => ?_⟩
  by_cases hx : x ∈ tsupport f
  · exact (hB ⟨x,hx,rfl⟩).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
    exact le_max_right _ _

theorem exists_kernel {ε : ℝ} (hε : 0 < ε) :
    ∃ κ : E → ℝ, ContDiff ℝ 1 κ ∧ HasCompactSupport κ ∧
      (∀ x, 0 ≤ κ x) ∧ (∫ x, κ x = 1) ∧
      (∀ x, ε ≤ ‖x‖ → κ x = 0) ∧
      ∃ B L : NNReal, (∀ x, ‖κ x‖ ≤ B) ∧
        (∀ x y, ‖κ x - κ y‖ ≤ L * ‖x-y‖) ∧
        (∫ x, κ x * ‖x‖) ≤ ε := by
  let b : ContDiffBump (0 : E) := ⟨ε/2, ε, by positivity, by linarith⟩
  let κ := b.normed (volume : Measure E)
  have hc : ContDiff ℝ 1 κ := b.contDiff_normed
  have hs : HasCompactSupport κ := b.hasCompactSupport_normed
  have hn : ∀ x, 0 ≤ κ x := b.nonneg_normed
  have hi : ∫ x, κ x = 1 := b.integral_normed
  have hz (x : E) (hx : ε ≤ ‖x‖) : κ x = 0 := by
    apply Function.notMem_support.mp
    rw [b.support_normed_eq]
    simpa only [mem_ball, dist_zero_right, b] using not_lt.mpr hx
  obtain ⟨B,hB⟩ := compact_function_bound hc.continuous hs
  obtain ⟨L,hL⟩ := compact_function_bound (hc.continuous_fderiv one_ne_zero) (hs.fderiv ℝ)
  have hLip : LipschitzWith L κ := lipschitzWith_of_nnnorm_fderiv_le
    (hc.differentiable one_ne_zero) (fun x => hL x)
  refine ⟨κ,hc,hs,hn,hi,hz,B,L,hB,?_,?_⟩
  · intro x y
    simpa only [dist_eq_norm] using hLip.dist_le_mul x y
  · calc
      _ ≤ ∫ x, κ x * ε := integral_mono
        ((hc.continuous.mul continuous_norm).integrable_of_hasCompactSupport hs.mul_right)
        ((hc.continuous.integrable_of_hasCompactSupport hs).mul_const ε) (fun x => by
          change κ x * ‖x‖ ≤ κ x * ε
          by_cases hx : ε ≤ ‖x‖
          · simp only [hz x hx, zero_mul, le_refl]
          · exact mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hx)) (hn x))
      _ = ε := by rw [integral_mul_const,hi,one_mul]

end RellichProof


open MeasureTheory ContinuousLinearMap Set
open scoped Convolution Pointwise

namespace RellichProof
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

theorem smoothAverage_convolution (κ u : E → ℝ) :
    smoothAverage κ u = κ ⋆[lsmul ℝ ℝ, volume] u := by
  funext x
  exact (convolution_lsmul_swap (μ := (volume : Measure E)) (f := κ) (g := u) (x := x)).symm

theorem smoothAverage_continuous {κ u : E → ℝ} (hκ : Continuous κ)
    (hκs : HasCompactSupport κ) (hu : Continuous u) :
    Continuous (smoothAverage κ u) := by
  rw [smoothAverage_convolution]
  exact hκs.continuous_convolution_left (lsmul ℝ ℝ) hκ hu.locallyIntegrable

theorem smoothAverage_support {κ u : E → ℝ} {K J : Set E}
    (hκ : Function.support κ ⊆ J) (hu : Function.support u ⊆ K) :
    Function.support (smoothAverage κ u) ⊆ J+K := by
  rw [smoothAverage_convolution]
  exact (support_convolution_subset (lsmul ℝ ℝ)).trans (Set.add_subset_add hκ hu)

theorem smoothAverage_compactSupport {κ u : E → ℝ}
    (hκ : HasCompactSupport κ) (hu : HasCompactSupport u) :
    HasCompactSupport (smoothAverage κ u) := by
  rw [smoothAverage_convolution]
  exact hκ.convolution (lsmul ℝ ℝ) hu

end RellichProof


open MeasureTheory Set Metric BoundedContinuousFunction
open scoped Pointwise

namespace RellichProof
variable {n : ℕ} {I : Type*}
local notation "E" => EuclideanSpace ℝ (Fin n)

theorem smooth_family_l1_totallyBounded (u : I → E → ℝ)
    (hu : ∀ i, ContDiff ℝ 1 (u i)) (hc : ∀ i, HasCompactSupport (u i))
    (K : Set E) (hK : IsCompact K) (hs : ∀ i, Function.support (u i) ⊆ K)
    (C : ℝ) (hC : 0 ≤ C)
    (hn : ∀ i, (∫ x, ‖u i x‖) ≤ C)
    (hd : ∀ i, (∫ x, ‖fderiv ℝ (u i) x‖) ≤ C) :
    TotallyBounded (range (fun i =>
      ((hu i).continuous.integrable_of_hasCompactSupport (μ := volume) (hc i)).toL1 (u i))) := by
  let U : I → Lp ℝ 1 (volume : Measure E) := fun i =>
    ((hu i).continuous.integrable_of_hasCompactSupport (μ := volume) (hc i)).toL1 (u i)
  apply totallyBounded_of_approximations
  intro ε hε
  let δ := ε / (2*(C+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨κ,hκ,hκs,hκ0,hκ1,hκout,B,L,hB,hL,hmoment⟩ := exists_kernel (n := n) hδ
  let J : Set E := closedBall 0 δ + K
  have hJ : IsCompact J := (isCompact_closedBall 0 δ).add hK
  have hκsupp : Function.support κ ⊆ closedBall 0 δ := by
    intro x hx
    apply mem_closedBall.mpr
    rw [dist_zero_right]
    by_contra h
    exact hx (hκout x (le_of_lt (lt_of_not_ge h)))
  let v : I → (E →ᵇ ℝ) := fun i => ofNormedAddCommGroup (smoothAverage κ (u i))
    (smoothAverage_continuous hκ.continuous hκs (hu i).continuous) (B*C)
    (fun x => (smoothAverage_bound hκ.continuous (hu i).continuous (hc i) hB x).trans
      (mul_le_mul_of_nonneg_left (hn i) B.coe_nonneg))
  have hvs : ∀ i, Function.support (v i : E → ℝ) ⊆ J := fun i =>
    smoothAverage_support hκsupp (hs i)
  have ht : TotallyBounded (range v) := supported_totallyBounded J hJ (range v) (B*C) (L*C)
    (by rintro f ⟨i,rfl⟩ x hx; exact Function.notMem_support.mp (fun h => hx (hvs i h)))
    (by rintro f ⟨i,rfl⟩ x; exact (v i).norm_coe_le_norm x |>.trans (by
      exact norm_ofNormedAddCommGroup_le (smoothAverage_continuous hκ.continuous hκs (hu i).continuous)
        (mul_nonneg B.coe_nonneg hC) _))
    (by rintro f ⟨i,rfl⟩ x y
        change ‖smoothAverage κ (u i) x - smoothAverage κ (u i) y‖ ≤ (L*C)*dist x y
        rw [dist_eq_norm]
        exact (smoothAverage_difference hκ.continuous (hu i).continuous (hc i) hL x y).trans
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hn i) L.coe_nonneg) (norm_nonneg _)))
  refine ⟨cutoffL1 J hJ '' range v, ht.image (cutoffL1_uniformContinuous J hJ), ?_⟩
  rintro x ⟨i,rfl⟩
  refine ⟨cutoffL1 J hJ (v i), ⟨v i, mem_range_self i,rfl⟩, ?_⟩
  have he : (J.indicator (v i)) = (smoothAverage κ (u i)) := by
    funext x
    by_cases hx : x ∈ J
    · simp only [indicator_of_mem hx]; rfl
    · rw [indicator_of_notMem hx]
      exact (Function.notMem_support.mp (fun h => hx (hvs i h))).symm
  have hdist : dist (U i) (cutoffL1 J hJ (v i)) =
      ∫ x, ‖smoothAverage κ (u i) x - u i x‖ := by
    rw [L1.dist_eq_integral_dist]
    apply integral_congr_ae
    filter_upwards [((hu i).continuous.integrable_of_hasCompactSupport (μ := volume) (hc i)).coeFn_toL1,
      (cutoff_integrable J hJ (v i)).coeFn_toL1] with x hx hy
    dsimp only [U, cutoffL1]
    rw [hx,hy,he,dist_eq_norm,norm_sub_rev]
  change dist (U i) (cutoffL1 J hJ (v i)) < ε
  rw [hdist]
  calc
    _ ≤ (∫ y, κ y * ‖y‖) * (∫ x, ‖fderiv ℝ (u i) x‖) :=
      mollifier_l1_error hκ.continuous hκs hκ0 hκ1 (hu i) (hc i)
    _ ≤ δ*C := mul_le_mul hmoment (hd i) (integral_nonneg (fun x => norm_nonneg _)) hδ.le
    _ < ε := by dsimp [δ]; rw [div_mul_eq_mul_div]; apply (div_lt_iff₀ (by positivity : 0 < 2*(C+1))).mpr; nlinarith

end RellichProof


open Set Metric

namespace RellichProof

theorem totallyBounded_range_transfer {I X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : I → X) (g : I → Y) (hf : TotallyBounded (range f))
    (h : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ i j, dist (f i) (f j) < δ → dist (g i) (g j) < ε) :
    TotallyBounded (range g) := by
  classical
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨δ,hδ,hcontrol⟩ := h ε hε
  obtain ⟨t,ht,htfin,hcover⟩ := Metric.finite_approx_of_totallyBounded hf δ hδ
  let : Fintype t := htfin.fintype
  choose j hj using fun x : t => ht x.2
  refine ⟨range (fun x : t => g (j x)), finite_range _, ?_⟩
  rintro y ⟨i,rfl⟩
  obtain ⟨x,hx,hix⟩ := mem_iUnion₂.mp (hcover (mem_range_self i))
  apply mem_iUnion₂.mpr
  refine ⟨g (j ⟨x,hx⟩), mem_range_self (f := fun x : t => g (j x)) ⟨x,hx⟩, ?_⟩
  apply hcontrol
  rw [hj ⟨x,hx⟩]
  exact hix

end RellichProof


open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace RellichProof
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem subcritical_norm_control {q r : ℝ} (hq : 1 ≤ q) (hqr : q < r)
    {D ε : ℝ≥0∞} (hD : D ≠ ⊤) (hε : 0 < ε) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ f : X → ℝ, AEStronglyMeasurable f μ →
      eLpNorm f 1 μ < δ → eLpNorm f (ENNReal.ofReal r) μ ≤ D →
      eLpNorm f (ENNReal.ofReal q) μ < ε := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hr0 : 0 < r := hq0.trans hqr
  have hr1 : 0 < r-1 := by linarith
  let a := (r-q)/(r-1)
  let b := (q-1)/(r-1)
  have ha : 0 < a := div_pos (sub_pos.mpr hqr) hr1
  have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hq) hr1.le
  have hab : a+b=1 := by dsimp [a,b]; field_simp; ring
  have he : q=a+r*b := by dsimp [a,b]; field_simp; ring
  have hθ : 0 < a/q := div_pos ha hq0
  have hγ : 0 ≤ r*b/q := by positivity
  have ht := ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos
    (ENNReal.rpow_ne_top_of_nonneg hγ hD) hθ
  have hev : ∀ᶠ t : ℝ≥0∞ in nhds 0, D^(r*b/q)*t^(a/q) < ε :=
    ht.eventually (Iio_mem_nhds hε)
  obtain ⟨δ,hδ,hδbound⟩ := ENNReal.nhds_zero_basis.mem_iff.mp hev
  refine ⟨δ,hδ,fun f hf hsmall hbound => ?_⟩
  have hi := seminorm_interpolation hf hq0 hr0 ha.le hb hab he
  have hqz : ENNReal.ofReal q ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hq0)
  have hrz : ENNReal.ofReal r ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hr0)
  have hqeq : eLpNorm f (ENNReal.ofReal q) μ = eLpNorm' f q μ := by
    rw [eLpNorm_eq_eLpNorm' hqz ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hq0.le]
  have hreq : eLpNorm f (ENNReal.ofReal r) μ = eLpNorm' f r μ := by
    rw [eLpNorm_eq_eLpNorm' hrz ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hr0.le]
  have hone : eLpNorm f 1 μ = eLpNorm' f 1 μ := by
    rw [eLpNorm_eq_eLpNorm' one_ne_zero ENNReal.one_ne_top, ENNReal.toReal_one]
  rw [← hqeq, ← hreq, ← hone] at hi
  have hm : D^(r*b/q)*(eLpNorm f 1 μ)^(a/q) < ε := hδbound hsmall
  exact (hi.trans (mul_le_mul_right (ENNReal.rpow_le_rpow hbound hγ) _)).trans_lt
    (by simpa only [mul_comm] using hm)

end RellichProof


open MeasureTheory Set Metric
open scoped ENNReal

namespace RellichProof
variable {X I : Type*} [MeasurableSpace X] {μ : Measure X}

theorem lq_totallyBounded_of_l1 (f : I → X → ℝ) {q r : ℝ}
    (hq : 1 ≤ q) (hqr : q < r) [Fact (1 ≤ ENNReal.ofReal q)]
    (h1 : ∀ i, MemLp (f i) 1 μ) (hqf : ∀ i, MemLp (f i) (ENNReal.ofReal q) μ)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) (hbound : ∀ i, eLpNorm (f i) (ENNReal.ofReal r) μ ≤ C)
    (ht : TotallyBounded (range (fun i => (h1 i).toLp (f i)))) :
    TotallyBounded (range (fun i => (hqf i).toLp (f i))) := by
  apply totallyBounded_range_transfer (fun i => (h1 i).toLp (f i))
    (fun i => (hqf i).toLp (f i)) ht
  intro ε hε
  obtain ⟨δ,hδ,hcontrol⟩ := subcritical_norm_control (μ := μ) hq hqr
    (D := C+C) (ENNReal.add_ne_top.mpr ⟨hC,hC⟩) (ENNReal.ofReal_pos.mpr hε)
  obtain ⟨η,hη,hηδ⟩ := ENNReal.lt_iff_exists_add_pos_lt.mp hδ
  simp only [zero_add] at hηδ
  refine ⟨η, by exact_mod_cast hη, fun i j hij => ?_⟩
  apply edist_lt_ofReal.mp
  rw [Lp.edist_toLp_toLp]
  apply hcontrol (f i - f j) ((h1 i).1.sub (h1 j).1)
  · have he := edist_lt_ofReal.mpr hij
    rw [Lp.edist_toLp_toLp, ENNReal.ofReal_coe_nnreal] at he
    exact he.trans hηδ
  · exact (eLpNorm_sub_le (h1 i).1 (h1 j).1
      (by simpa using ENNReal.ofReal_le_ofReal (hq.trans hqr.le))).trans (add_le_add (hbound i) (hbound j))

end RellichProof


open MeasureTheory Set
open scoped ENNReal

namespace RellichProof
variable {n : ℕ} {I : Type*}
local notation "E" => EuclideanSpace ℝ (Fin n)

theorem smooth_family_lq_totallyBounded (u : I → E → ℝ)
    (hu : ∀ i, ContDiff ℝ 1 (u i)) (hc : ∀ i, HasCompactSupport (u i))
    (K : Set E) (hK : IsCompact K) (hs : ∀ i, Function.support (u i) ⊆ K)
    (C : NNReal) (hn : ∀ i, eLpNorm (u i) 1 volume ≤ C)
    (hd : ∀ i, eLpNorm (fderiv ℝ (u i)) 1 volume ≤ C)
    {q : ℝ≥0∞} [Fact (1 ≤ q)] {r : ℝ} (hr : 0 < r) (hqr : q < ENNReal.ofReal r)
    (hb : ∀ i, eLpNorm (u i) (ENNReal.ofReal r) volume ≤ C) :
    TotallyBounded (range (fun i =>
      ((hu i).continuous.memLp_of_hasCompactSupport (μ := volume) (hc i) (p := q)).toLp (u i))) := by
  have hqtop : q ≠ ⊤ := ne_top_of_lt hqr
  have hq1 : (1 : ℝ) ≤ q.toReal := by
    exact_mod_cast (ENNReal.toReal_mono hqtop (Fact.out : 1 ≤ q))
  have hqr' : q.toReal < r := by
    simpa only [ENNReal.toReal_ofReal hr.le] using
      (ENNReal.toReal_lt_toReal hqtop ENNReal.ofReal_ne_top).mpr hqr
  have hqeq : ENNReal.ofReal q.toReal = q := ENNReal.ofReal_toReal hqtop
  generalize hqreal : q.toReal = Q at hqeq hq1 hqr'
  subst q
  have hn' (i : I) : (∫ x, ‖u i x‖) ≤ C := by
    have hi : Integrable (u i) := (hu i).continuous.integrable_of_hasCompactSupport (hc i)
    have he : eLpNorm (u i) 1 volume = ENNReal.ofReal (∫ x, ‖u i x‖) := by
      rw [eLpNorm_one_eq_lintegral_enorm, ofReal_integral_norm_eq_lintegral_enorm hi]
    have hh := hn i
    rw [he] at hh
    exact (ENNReal.ofReal_le_coe).mp hh
  have hd' (i : I) : (∫ x, ‖fderiv ℝ (u i) x‖) ≤ C := by
    have hi : Integrable (fderiv ℝ (u i)) :=
      ((hu i).continuous_fderiv one_ne_zero).integrable_of_hasCompactSupport ((hc i).fderiv ℝ)
    have he : eLpNorm (fderiv ℝ (u i)) 1 volume = ENNReal.ofReal (∫ x, ‖fderiv ℝ (u i) x‖) := by
      rw [eLpNorm_one_eq_lintegral_enorm, ofReal_integral_norm_eq_lintegral_enorm hi]
    have hh := hd i
    rw [he] at hh
    exact (ENNReal.ofReal_le_coe).mp hh
  have ht := smooth_family_l1_totallyBounded u hu hc K hK hs C C.coe_nonneg hn' hd'
  have hh := lq_totallyBounded_of_l1 u hq1 hqr'
    (fun i => (hu i).continuous.memLp_of_hasCompactSupport (μ := volume) (hc i))
    (fun i => (hu i).continuous.memLp_of_hasCompactSupport (μ := volume) (hc i))
    ENNReal.coe_ne_top hb ht
  exact hh

end RellichProof


open MeasureTheory
open scoped ENNReal NNReal

namespace HunterPDE.Compactness

/-- Theorem 3.45 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 73 (Rellich–Kondrachov): let
`Ω` be a bounded open set in `ℝⁿ`, `1 ≤ p < n` and `1 ≤ q < p* = np/(n − p)`. If `F` is a bounded
set in `W^{1,p}_0(Ω)`, then `F` is precompact in `L^q(ℝⁿ)`.
Elements of `F` are functions `ℝⁿ → ℝ` in `W^{1,p}_0(Ω)` (closure of `C_c^∞(Ω)` in the
`W^{1,p}(Ω)` norm) with a common bound on `‖f‖_{W^{1,p}(Ω)}`; they are placed in `L^q(ℝⁿ)` by
extension by zero outside `Ω` (`Ω.indicator f`). The conclusion says every extension lies in
`L^q(ℝⁿ)` and the set of their classes has compact closure in `L^q(ℝⁿ)`. -/
theorem rellich_kondrachov_proved {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (p : ℝ) (hp : 1 ≤ p) (hpn : p < n)
    (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq : q < ENNReal.ofReal (sobolevConjugate n p))
    (F : Set (EuclideanSpace ℝ (Fin n) → ℝ))
    (hF : ∀ f ∈ F, MemW0 1 (ENNReal.ofReal p) Ω f)
    (hFb : ∃ M : ℝ≥0, ∀ f ∈ F, sobolevNorm 1 (ENNReal.ofReal p) Ω f ≤ (M : ℝ≥0∞)) :
    (∀ f ∈ F, MemLp (Ω.indicator f) q volume) ∧
      IsCompact (closure {u : Lp ℝ q (volume : Measure (EuclideanSpace ℝ (Fin n))) |
        ∃ f ∈ F, (u : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume] Ω.indicator f}) := by
  obtain ⟨M,hM⟩ := hFb
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ q)
  have hm : ∀ f ∈ F, MemLp (Ω.indicator f) q volume := fun f hf =>
    RellichProof.native_q_memLp hΩ hΩb hp hpn hq0 hq.le (hF f hf)
      ((hM f hf).trans_lt ENNReal.coe_lt_top)
  refine ⟨hm, ?_⟩
  obtain ⟨C,hC,happrox⟩ := RellichProof.native_approximation hΩ hΩb hp hpn hq0 hq.le M
  let I := {φ : EuclideanSpace ℝ (Fin n) → ℝ |
    HunterPDE.Shared.IsTestFunction Ω φ ∧ eLpNorm φ 1 volume ≤ C ∧
      eLpNorm (fderiv ℝ φ) 1 volume ≤ C ∧
      eLpNorm φ (ENNReal.ofReal (sobolevConjugate n p)) volume ≤ C}
  let U : I → Lp ℝ q (volume : Measure (EuclideanSpace ℝ (Fin n))) := fun φ =>
    (φ.2.1.1.continuous.memLp_of_hasCompactSupport (μ := volume) φ.2.1.2.1).toLp φ.1
  have ht : TotallyBounded (Set.range U) := RellichProof.smooth_family_lq_totallyBounded
    (fun φ : I => φ.1) (fun φ => φ.2.1.1.of_le (by simp))
    (fun φ => φ.2.1.2.1) (closure Ω) hΩb.isCompact_closure
    (fun φ => (subset_tsupport _).trans (φ.2.1.2.2.trans subset_closure)) C
    (fun φ => φ.2.2.1) (fun φ => φ.2.2.2.1)
    (RellichProof.conjugate_pos hp hpn) hq (fun φ => φ.2.2.2.2)
  apply TotallyBounded.isCompact_of_isClosed _ isClosed_closure
  apply TotallyBounded.closure
  apply RellichProof.totallyBounded_of_approximations
  intro ε hε
  refine ⟨Set.range U, ht, ?_⟩
  rintro u ⟨f,hf,he⟩
  obtain ⟨φ,hφ,herror,h1,hd,hr⟩ := happrox f (hF f hf) (hM f hf)
    (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
  let i : I := ⟨φ,hφ,h1,hd,hr⟩
  refine ⟨U i, Set.mem_range_self i, ?_⟩
  apply edist_lt_ofReal.mp
  rw [Lp.edist_def]
  have hcoe : (U i : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume] φ :=
    (hφ.1.continuous.memLp_of_hasCompactSupport (μ := volume) hφ.2.1).coeFn_toLp
  exact (eLpNorm_congr_ae (he.sub hcoe)).trans_lt herror


end HunterPDE.Compactness


open MeasureTheory
open scoped ENNReal NNReal

namespace HunterPDE.Compactness

/-- Theorem 3.45 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 73 (Rellich–Kondrachov): let
`Ω` be a bounded open set in `ℝⁿ`, `1 ≤ p < n` and `1 ≤ q < p* = np/(n − p)`. If `F` is a bounded
set in `W^{1,p}_0(Ω)`, then `F` is precompact in `L^q(ℝⁿ)`.
Elements of `F` are functions `ℝⁿ → ℝ` in `W^{1,p}_0(Ω)` (closure of `C_c^∞(Ω)` in the
`W^{1,p}(Ω)` norm) with a common bound on `‖f‖_{W^{1,p}(Ω)}`; they are placed in `L^q(ℝⁿ)` by
extension by zero outside `Ω` (`Ω.indicator f`). The conclusion says every extension lies in
`L^q(ℝⁿ)` and the set of their classes has compact closure in `L^q(ℝⁿ)`. -/
theorem rellich_kondrachov {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (p : ℝ) (hp : 1 ≤ p) (hpn : p < n)
    (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq : q < ENNReal.ofReal (sobolevConjugate n p))
    (F : Set (EuclideanSpace ℝ (Fin n) → ℝ))
    (hF : ∀ f ∈ F, MemW0 1 (ENNReal.ofReal p) Ω f)
    (hFb : ∃ M : ℝ≥0, ∀ f ∈ F, sobolevNorm 1 (ENNReal.ofReal p) Ω f ≤ (M : ℝ≥0∞)) :
    (∀ f ∈ F, MemLp (Ω.indicator f) q volume) ∧
      IsCompact (closure {u : Lp ℝ q (volume : Measure (EuclideanSpace ℝ (Fin n))) |
        ∃ f ∈ F, (u : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume] Ω.indicator f}) := by
  exact rellich_kondrachov_proved Ω hΩ hΩb p hp hpn q hq F hF hFb

end HunterPDE.Compactness

open HunterPDE.Compactness

theorem solution {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (p : ℝ) (hp : 1 ≤ p) (hpn : p < n)
    (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq : q < ENNReal.ofReal (sobolevConjugate n p))
    (F : Set (EuclideanSpace ℝ (Fin n) → ℝ))
    (hF : ∀ f ∈ F, MemW0 1 (ENNReal.ofReal p) Ω f)
    (hFb : ∃ M : ℝ≥0, ∀ f ∈ F, sobolevNorm 1 (ENNReal.ofReal p) Ω f ≤ (M : ℝ≥0∞)) :
    (∀ f ∈ F, MemLp (Ω.indicator f) q volume) ∧
      IsCompact (closure {u : Lp ℝ q (volume : Measure (EuclideanSpace ℝ (Fin n))) |
        ∃ f ∈ F, (u : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume] Ω.indicator f}) := HunterPDE.Compactness.rellich_kondrachov Ω hΩ hΩb p hp hpn q hq F hF hFb
