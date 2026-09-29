-- Prove2me | solution 1 for NumberField.TateGlobal.apply_one_ne_zero_of_differentiable_of_eq_partialEulerProduct_of_sq_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/95e0d1c5-fb2d-5eb0-869e-fef342ac15e7

import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Theorems.Thm_NumberField_exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero
import Theorems.Thm_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_lSeries_card_ideal_of_forall_dvd
import Theorems.Thm_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta
import Theorems.Thm_NumberField_multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_apply_one_ne_zero_of_differentiable_of_eq_partialEulerProduct_of_sq_eq_one

set_option autoImplicit false

open NumberField IsDedekindDomain NumberField.TateGlobal AutomorphicForm
open Filter Topology Complex LSeries
open scoped ComplexOrder

noncomputable section

namespace N3Landau

open scoped LSeries.notation

variable (K : Type) [Field K] [NumberField K]

abbrev nC (v : HeightOneSpectrum (𝓞 K)) : ℂ := ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)

theorem one_lt_absNorm (v : HeightOneSpectrum (𝓞 K)) : 1 < Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

theorem norm_cpow_neg_lt_one {s : ℂ} (hs : 0 < s.re) (v : HeightOneSpectrum (𝓞 K)) :
    ‖nC K v ^ (-s)‖ < 1 := by
  have hlt := one_lt_absNorm K v
  rw [norm_natCast_cpow_of_pos (by omega), neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hlt) (by linarith)

theorem one_sub_mul_cpow_ne_zero {s : ℂ} (hs : 0 < s.re) (v : HeightOneSpectrum (𝓞 K)) {z : ℂ}
    (hz : ‖z‖ ≤ 1) : 1 - z * nC K v ^ (-s) ≠ 0 := by
  intro h
  have h1 : z * nC K v ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  have h2 : ‖z * nC K v ^ (-s)‖ < 1 := by
    rw [norm_mul]
    calc ‖z‖ * ‖nC K v ^ (-s)‖ ≤ 1 * ‖nC K v ^ (-s)‖ := by gcongr
      _ < 1 := by rw [one_mul]; exact norm_cpow_neg_lt_one K hs v
  rw [h1, norm_one] at h2
  exact lt_irrefl _ h2

theorem cpow_neg_two_mul (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    nC K v ^ (-(2 * s)) = (nC K v ^ (-s)) ^ 2 := by
  rw [show -(2 * s) = ((2 : ℕ) : ℂ) * (-s) by push_cast; ring, cpow_nat_mul]

theorem factor_split {c X X2 : ℂ} (hc : c = 0 ∨ c = 1 ∨ c = -1) (hX2 : X2 = X ^ 2) :
    (1 - X)⁻¹ * (1 - c * X)⁻¹ =
      (if c ≠ -1 then (1 - X)⁻¹ else 1) * (if c = 1 then (1 - X)⁻¹ else 1) *
        (if c = -1 then (1 - X2)⁻¹ else 1) := by
  rcases hc with rfl | rfl | rfl
  · norm_num
  · norm_num
  · simp only [ne_eq, not_true_eq_false, ↓reduceIte, one_mul]
    rw [if_neg (by norm_num), one_mul, hX2, ← mul_inv]
    congr 1
    ring

abbrev rc (p : HeightOneSpectrum (𝓞 K) → Prop) : ℕ → ℂ := fun n =>
  (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n ∧ ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ I → p v} : ℂ)

theorem rc_nonneg (p : HeightOneSpectrum (𝓞 K) → Prop) (n : ℕ) : 0 ≤ rc K p n := by
  simp only [rc]
  exact_mod_cast Nat.zero_le _

theorem rc_one (p : HeightOneSpectrum (𝓞 K) → Prop) : rc K p 1 = 1 := by
  simp only [rc]
  have : Unique {I : Ideal (𝓞 K) // Ideal.absNorm I = 1 ∧ ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ I → p v} :=
    { default := ⟨⊤, by rw [Ideal.absNorm_eq_one_iff], fun v hv => by
        exfalso
        rw [Ideal.dvd_iff_le, top_le_iff] at hv
        exact v.isPrime.ne_top hv⟩
      uniq := fun I => Subtype.ext (Ideal.absNorm_eq_one_iff.mp I.2.1) }
  rw [Nat.card_unique, Nat.cast_one]

def onSq (a : ℕ → ℂ) : ℕ → ℂ := fun m => if IsSquare m then a (Nat.sqrt m) else 0

theorem onSq_nonneg {a : ℕ → ℂ} (ha : ∀ n, 0 ≤ a n) (m : ℕ) : 0 ≤ onSq a m := by
  unfold onSq; split_ifs
  · exact ha _
  · exact le_rfl

theorem onSq_one (a : ℕ → ℂ) : onSq a 1 = a 1 := by
  simp [onSq, Nat.sqrt_one]

theorem term_sq_comp_onSq (a : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    term (onSq a) s (n ^ 2) = term a (2 * s) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [term_zero]
  · rw [term_of_ne_zero (pow_ne_zero 2 hn), term_of_ne_zero hn]
    have hsq : onSq a (n ^ 2) = a n := by
      simp [onSq, IsSquare.sq n, Nat.sqrt_eq']
    rw [hsq]
    congr 1
    push_cast
    rw [sq, natCast_mul_natCast_cpow, two_mul, cpow_add _ _ (Nat.cast_ne_zero.mpr hn)]

theorem term_sq_of_not_isSquare (a : ℕ → ℂ) (s : ℂ) {m : ℕ} (hm : ¬ IsSquare m) :
    term (onSq a) s m = 0 := by
  rcases eq_or_ne m 0 with rfl | h0
  · exact term_zero _ _
  · rw [term_of_ne_zero h0]
    simp [onSq, hm]

theorem lSeriesSummable_sq_and_lSeries_sq {a : ℕ → ℂ} {s : ℂ} (h : LSeriesSummable a (2 * s)) :
    LSeriesSummable (onSq a) s ∧ LSeries (onSq a) s = LSeries a (2 * s) := by
  have hinj : Function.Injective (fun n : ℕ => n ^ 2) := Nat.pow_left_injective two_ne_zero
  have hoff : ∀ m ∉ Set.range (fun n : ℕ => n ^ 2), term (onSq a) s m = 0 := by
    intro m hm
    refine term_sq_of_not_isSquare a s fun ⟨r, hr⟩ => hm ⟨r, ?_⟩
    simp only [hr, sq]
  have hcomp : (term (onSq a) s ∘ fun n : ℕ => n ^ 2) = term a (2 * s) := by
    funext n; exact term_sq_comp_onSq a s n
  have hHas : LSeriesHasSum a (2 * s) (LSeries a (2 * s)) := h.LSeriesHasSum
  have h1 : HasSum (term (onSq a) s) (LSeries a (2 * s)) := by
    rw [← hinj.hasSum_iff hoff, hcomp]
    exact hHas
  exact ⟨h1.summable, h1.tsum_eq⟩

theorem convolution_nonneg {f g : ℕ → ℂ} (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (n : ℕ) :
    0 ≤ (f ⍟ g) n := by
  rw [convolution_def]
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hf _) (hg _)

theorem convolution_apply_one (f g : ℕ → ℂ) : (f ⍟ g) 1 = f 1 * g 1 := by
  rw [convolution_def]
  simp

theorem multipliable_eulerProduct {z : HeightOneSpectrum (𝓞 K) → ℂ} (hz : ∀ v, ‖z v‖ ≤ 1) {s : ℂ}
    (hs : 1 < s.re) : Multipliable fun v : HeightOneSpectrum (𝓞 K) => (1 - z v * nC K v ^ (-s))⁻¹ := by
  have h := (NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one K ∅
    (fun v => z v.1) (fun v => hz v.1)).1 s hs
  let e : {v : HeightOneSpectrum (𝓞 K) // v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 K)))} ≃
      HeightOneSpectrum (𝓞 K) := Equiv.subtypeUnivEquiv fun v => Finset.notMem_empty v
  exact (Equiv.multipliable_iff e).mp h

theorem exists_lSeries_eq_dedekindZeta_mul_tprod (c : HeightOneSpectrum (𝓞 K) → ℂ)
    (hc : ∀ v, c v = 0 ∨ c v = 1 ∨ c v = -1) :
    ∃ A : ℕ → ℂ, (∀ n, 0 ≤ A n) ∧ A 1 = 1 ∧ ∀ s : ℂ, 1 < s.re →
      LSeriesSummable A s ∧
        NumberField.dedekindZeta K s * ∏' v : HeightOneSpectrum (𝓞 K), (1 - c v * nC K v ^ (-s))⁻¹ =
          LSeries A s := by
  classical

  let a1 : ℕ → ℂ := rc K (fun v => c v ≠ -1)
  let a2 : ℕ → ℂ := rc K (fun v => c v = 1)
  let a3 : ℕ → ℂ := rc K (fun v => c v = -1)
  refine ⟨a1 ⍟ (a2 ⍟ onSq a3), ?_, ?_, ?_⟩
  · exact convolution_nonneg (rc_nonneg K _) (convolution_nonneg (rc_nonneg K _) (onSq_nonneg (rc_nonneg K _)))
  · rw [convolution_apply_one, convolution_apply_one, onSq_one]
    simp only [a1, a2, a3, rc_one, mul_one]
  intro s hs
  have hs0 : 0 < s.re := by linarith
  have h2s : 1 < (2 * s).re := by simp only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]; linarith

  obtain ⟨hS1, hP1⟩ := NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_lSeries_card_ideal_of_forall_dvd K
    (fun v => c v ≠ -1) s hs
  obtain ⟨hS2, hP2⟩ := NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_lSeries_card_ideal_of_forall_dvd K
    (fun v => c v = 1) s hs
  obtain ⟨hS3, hP3⟩ := NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_lSeries_card_ideal_of_forall_dvd K
    (fun v => c v = -1) (2 * s) h2s
  obtain ⟨hS3', hL3⟩ := lSeriesSummable_sq_and_lSeries_sq (a := a3) hS3
  refine ⟨hS1.convolution (hS2.convolution hS3'), ?_⟩

  let f : HeightOneSpectrum (𝓞 K) → ℂ := fun v => (1 - nC K v ^ (-s))⁻¹
  let g : HeightOneSpectrum (𝓞 K) → ℂ := fun v => (1 - nC K v ^ (-(2 * s)))⁻¹
  have hQ1 : HasProd ({v | c v ≠ -1}.mulIndicator f) (LSeries a1 s) :=
    (hasProd_subtype_iff_mulIndicator (s := {v | c v ≠ -1}) (f := f)).mp hP1
  have hQ2 : HasProd ({v | c v = 1}.mulIndicator f) (LSeries a2 s) :=
    (hasProd_subtype_iff_mulIndicator (s := {v | c v = 1}) (f := f)).mp hP2
  have hQ3 : HasProd ({v | c v = -1}.mulIndicator g) (LSeries a3 (2 * s)) :=
    (hasProd_subtype_iff_mulIndicator (s := {v | c v = -1}) (f := g)).mp hP3
  have hQ := (hQ1.mul hQ2).mul hQ3

  have hZ := NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta K s hs
  have hMc : Multipliable fun v : HeightOneSpectrum (𝓞 K) => (1 - c v * nC K v ^ (-s))⁻¹ := by
    refine multipliable_eulerProduct K (fun v => ?_) hs
    rcases hc v with h | h | h <;> simp [h]

  have hterm : ∀ v : HeightOneSpectrum (𝓞 K),
      (1 - nC K v ^ (-s))⁻¹ * (1 - c v * nC K v ^ (-s))⁻¹ =
        {v | c v ≠ -1}.mulIndicator f v * {v | c v = 1}.mulIndicator f v * {v | c v = -1}.mulIndicator g v := by
    intro v
    simp only [Set.mulIndicator_apply, Set.mem_setOf_eq, f, g]
    exact factor_split (hc v) (cpow_neg_two_mul K v s)
  calc NumberField.dedekindZeta K s * ∏' v : HeightOneSpectrum (𝓞 K), (1 - c v * nC K v ^ (-s))⁻¹
      = (∏' v : HeightOneSpectrum (𝓞 K), (1 - nC K v ^ (-s))⁻¹) *
          ∏' v : HeightOneSpectrum (𝓞 K), (1 - c v * nC K v ^ (-s))⁻¹ := by rw [hZ.tprod_eq]
    _ = ∏' v : HeightOneSpectrum (𝓞 K), ((1 - nC K v ^ (-s))⁻¹ * (1 - c v * nC K v ^ (-s))⁻¹) :=
          (hZ.multipliable.tprod_mul hMc).symm
    _ = ∏' v : HeightOneSpectrum (𝓞 K),
          ({v | c v ≠ -1}.mulIndicator f v * {v | c v = 1}.mulIndicator f v * {v | c v = -1}.mulIndicator g v) :=
          tprod_congr hterm
    _ = LSeries a1 s * LSeries a2 s * LSeries a3 (2 * s) := hQ.tprod_eq
    _ = LSeries (a1 ⍟ (a2 ⍟ onSq a3)) s := by
          rw [LSeries_convolution' hS1 (hS2.convolution hS3'), LSeries_convolution' hS2 hS3', hL3, mul_assoc]

theorem units_val_eq_one_or_eq_neg_one_of_sq_eq_one {G : Type} [Group G] (χ : G →* ℂˣ) (h2 : χ ^ 2 = 1)
    (x : G) : ((χ x : ℂˣ) : ℂ) = 1 ∨ ((χ x : ℂˣ) : ℂ) = -1 := by
  have h : (χ x) ^ 2 = 1 := by rw [← MonoidHom.pow_apply, h2, MonoidHom.one_apply]
  have h' : ((χ x : ℂˣ) : ℂ) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  exact sq_eq_one_iff.mp h'

end N3Landau

end

open N3Landau in
open scoped ComplexOrder in
open scoped Classical in
theorem solution (K : Type) [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hχ : IsIdeleClassChar (𝓞 K) K χ) (hχc : Continuous χ)
    (hχu : IsUnitaryChar (𝓞 K) K χ) (h2 : χ ^ 2 = 1) (h1 : χ ≠ 1)
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (L : ℂ → ℂ) (hL : Differentiable ℂ L)
    (hLE : ∀ s : ℂ, 1 < s.re →
      L s = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) :
    L 1 ≠ 0 := by
  intro hL1

  let c : HeightOneSpectrum (𝓞 K) → ℂ := fun v =>
    if v ∉ T then (if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) else 0
  have hc : ∀ v, c v = 0 ∨ c v = 1 ∨ c v = -1 := by
    intro v
    by_cases hvT : v ∉ T
    · by_cases hu : IsUnramifiedCharAt χ v
      · have hcv : c v = ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) := by simp [c, hvT, hu]
        rw [hcv]
        exact Or.inr (units_val_eq_one_or_eq_neg_one_of_sq_eq_one χ h2 (uniformizerIdele K v))
      · exact Or.inl (by simp [c, hu])
    · exact Or.inl (by simp [c, hvT])

  have hLE' : ∀ s : ℂ, 1 < s.re → L s = ∏' v : HeightOneSpectrum (𝓞 K), (1 - c v * nC K v ^ (-s))⁻¹ := by
    intro s hs
    rw [hLE s hs]
    have hsupp : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 K) => (1 - c v * nC K v ^ (-s))⁻¹) ⊆
        {v | v ∉ T} := by
      intro v hv
      by_contra hvT
      simp only [Set.mem_setOf_eq, not_not] at hvT
      apply hv
      simp [c, hvT]
    rw [← tprod_subtype_eq_of_mulSupport_subset hsupp]
    refine tprod_congr fun v => ?_
    simp [c, v.2]

  obtain ⟨A, hA0, hA1, hA⟩ := exists_lSeries_eq_dedekindZeta_mul_tprod K c hc
  obtain ⟨R, hRd, -, hRζ, hR2⟩ :=
    NumberField.exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero K

  let H : ℂ → ℂ := Function.update (fun s => (L s - L 1) / (s - 1)) 1 (deriv L 1)
  have hHne : ∀ s : ℂ, s ≠ 1 → DifferentiableAt ℂ H s := by
    intro s hs
    apply DifferentiableAt.congr_of_eventuallyEq (f := fun s => (L s - L 1) / (s - 1))
    · exact ((hL s).sub_const _).div (differentiableAt_id.sub_const _) (sub_ne_zero.mpr hs)
    · filter_upwards [eventually_ne_nhds hs] with t ht using Function.update_of_ne ht ..
  have hHd : Differentiable ℂ H := by
    intro s
    rcases ne_or_eq s 1 with hs | rfl
    · exact hHne s hs
    · refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
      · filter_upwards [self_mem_nhdsWithin] with t ht using hHne t ht
      · exact (hL 1).hasDerivAt.continuousAt_div
  let F : ℂ → ℂ := fun s => R s * H s
  have hFd : Differentiable ℂ F := hRd.mul hHd
  have hFeq : {s : ℂ | 1 < s.re}.EqOn F (LSeries A) := by
    intro s hs
    have hs1 : s ≠ 1 := by
      rintro rfl
      simp at hs
    have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    show R s * Function.update (fun s => (L s - L 1) / (s - 1)) 1 (deriv L 1) s = LSeries A s
    rw [Function.update_of_ne hs1, hL1, sub_zero, hRζ s hs, ← (hA s hs).2, hLE' s hs]
    field_simp
  have habs : abscissaOfAbsConv A ≤ (1 : ℝ) :=
    abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      (hA y (by simpa using hy)).1
  have hpos : 0 < F ((-2 : ℝ) : ℂ) :=
    positive_of_differentiable_of_eqOn (a := A) (fun n => hA0 n) (by rw [hA1]; exact zero_lt_one) hFd habs
      hFeq (-2)
  have hF2 : F ((-2 : ℝ) : ℂ) = 0 := by
    have := hR2 0
    simp only [Nat.cast_zero, zero_add, mul_one] at this
    show R _ * H _ = 0
    rw [show ((-2 : ℝ) : ℂ) = -2 by push_cast; ring, this, zero_mul]
  rw [hF2] at hpos
  exact lt_irrefl _ hpos

end S_NumberField_TateGlobal_apply_one_ne_zero_of_differentiable_of_eq_partialEulerProduct_of_sq_eq_one
end P2MW
export P2MW.S_NumberField_TateGlobal_apply_one_ne_zero_of_differentiable_of_eq_partialEulerProduct_of_sq_eq_one (solution)
