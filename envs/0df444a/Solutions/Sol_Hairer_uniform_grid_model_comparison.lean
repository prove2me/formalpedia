-- Prove2me | solution 1 for Hairer.uniform_grid_model_comparison
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T20:55:02.365225+00:00
-- url     : https://prove2.me/submissions/55c4fe3b-a1d8-49dd-a0ed-2ce15606d47e

import Definitions.Def_Hairer_Model
open BigOperators Hairer
noncomputable section






set_option autoImplicit false

open scoped Classical

noncomputable section

open Hairer

namespace HairerAux

/-! ### A one-dimensional smooth partition of unity -/

/-- The smooth bump `χ(t) = σ(t+1) - σ(t)` built from Mathlib's smooth transition
function `σ`.  It is supported in `[-1,1]`, and its integer translates sum to `1`
by telescoping. -/
def chi (t : ℝ) : ℝ := Real.smoothTransition (t + 1) - Real.smoothTransition t

theorem chi_contDiff : ContDiff ℝ (⊤ : ℕ∞) chi :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).sub
    Real.smoothTransition.contDiff

theorem chi_eq_zero_of_one_le_abs {t : ℝ} (ht : 1 ≤ |t|) : chi t = 0 := by
  rcases le_or_gt 1 t with h | h
  · have h1 : Real.smoothTransition (t + 1) = 1 :=
      Real.smoothTransition.one_of_one_le (by linarith)
    have h2 : Real.smoothTransition t = 1 := Real.smoothTransition.one_of_one_le h
    simp [chi, h1, h2]
  · have ht' : t ≤ -1 := by
      rcases abs_cases t with ⟨he, _⟩ | ⟨he, _⟩
      · linarith [ht, he]
      · linarith [ht, he]
    have h1 : Real.smoothTransition (t + 1) = 0 :=
      Real.smoothTransition.zero_of_nonpos (by linarith)
    have h2 : Real.smoothTransition t = 0 :=
      Real.smoothTransition.zero_of_nonpos (by linarith)
    simp [chi, h1, h2]

/-- Telescoping partition of unity: `∑_{j=0}^{2N} χ(t - (j - N)) = 1` whenever `|t| ≤ N`. -/
theorem chi_sum_eq_one (t : ℝ) (N : ℕ) (ht : |t| ≤ (N : ℝ)) :
    ∑ j ∈ Finset.range (2 * N + 1), chi (t - ((j : ℝ) - (N : ℝ))) = 1 := by
  have habs := abs_le.mp ht
  set F : ℕ → ℝ := fun j => Real.smoothTransition (t + (N : ℝ) + 1 - (j : ℝ)) with hF
  have key : ∀ j ∈ Finset.range (2 * N + 1),
      chi (t - ((j : ℝ) - (N : ℝ))) = F j - F (j + 1) := by
    intro j _
    have e2 : t - ((j : ℝ) - (N : ℝ)) = t + (N : ℝ) + 1 - (((j + 1 : ℕ)) : ℝ) := by
      push_cast; ring
    have e3 : t + (N : ℝ) + 1 - (((j + 1 : ℕ)) : ℝ) + 1 = t + (N : ℝ) + 1 - (j : ℝ) := by
      push_cast; ring
    simp only [chi, hF, e2, e3]
  rw [Finset.sum_congr rfl key, Finset.sum_range_sub' F (2 * N + 1)]
  have h1 : F 0 = 1 := by
    simp only [hF]
    apply Real.smoothTransition.one_of_one_le
    push_cast
    linarith [habs.1]
  have h2 : F (2 * N + 1) = 0 := by
    simp only [hF]
    apply Real.smoothTransition.zero_of_nonpos
    push_cast
    linarith [habs.2]
  rw [h1, h2, sub_zero]

/-! ### Boxes and the `d`-dimensional bump -/

/-- The closed box `{y : ∀ i, |yᵢ| ≤ c}`. -/
def boxSet (d : ℕ) (c : ℝ) : Set (Pt d) := {z | ∀ i, |z i| ≤ c}

theorem isCompact_boxSet (d : ℕ) (c : ℝ) : IsCompact (boxSet d c) := by
  have h : boxSet d c = Set.univ.pi (fun _ : Fin d => Set.Icc (-c) c) := by
    ext z
    simp only [boxSet, Set.mem_ofPred_eq, Set.mem_univ_pi, Set.mem_Icc, abs_le]
  rw [h]
  exact isCompact_univ_pi fun _ => isCompact_Icc

/-- The `d`-dimensional bump `W z = ∏ᵢ χ(zᵢ)`, supported in the unit box. -/
def bumpBox {d : ℕ} (z : Pt d) : ℝ := ∏ i, chi (z i)

theorem bumpBox_contDiff {d : ℕ} : ContDiff ℝ (⊤ : ℕ∞) (bumpBox (d := d)) := by
  apply contDiff_prod
  intro i _
  exact chi_contDiff.comp (contDiff_apply ℝ ℝ i)

theorem bumpBox_eq_zero {d : ℕ} {z : Pt d} (h : ∃ i, 1 ≤ |z i|) : bumpBox z = 0 := by
  obtain ⟨i, hi⟩ := h
  exact Finset.prod_eq_zero (Finset.mem_univ i) (chi_eq_zero_of_one_le_abs hi)

theorem bumpBox_hasCompactSupport {d : ℕ} : HasCompactSupport (bumpBox (d := d)) := by
  apply HasCompactSupport.intro (isCompact_boxSet d 1)
  intro z hz
  apply bumpBox_eq_zero
  simp only [boxSet, Set.mem_ofPred_eq, not_forall, not_le] at hz
  obtain ⟨i, hi⟩ := hz
  exact ⟨i, hi.le⟩

/-! ### Uniform bounds on iterated derivatives -/

/-- A smooth, compactly supported function has all its derivatives up to a given order
bounded by one constant. -/
theorem exists_deriv_bound {d : ℕ} {g : Pt d → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hsupp : HasCompactSupport g) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m ≤ r, ∀ y, ‖iteratedFDeriv ℝ m g y‖ ≤ C := by
  induction r with
  | zero =>
    obtain ⟨C, hC⟩ := (hsupp.iteratedFDeriv 0).exists_bound_of_continuous
      (hg.continuous_iteratedFDeriv (by exact_mod_cast le_top))
    refine ⟨max C 0, le_max_right _ _, ?_⟩
    intro m hm y
    obtain rfl : m = 0 := Nat.le_zero.mp hm
    exact (hC y).trans (le_max_left _ _)
  | succ k ih =>
    obtain ⟨C, hC0, hC⟩ := ih
    obtain ⟨D, hD⟩ := (hsupp.iteratedFDeriv (k + 1)).exists_bound_of_continuous
      (hg.continuous_iteratedFDeriv (by exact_mod_cast le_top))
    refine ⟨max C D, le_trans hC0 (le_max_left _ _), ?_⟩
    intro m hm y
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hm) with h | rfl
    · exact (hC m (Nat.lt_succ_iff.mp h) y).trans (le_max_left _ _)
    · exact (hD y).trans (le_max_right _ _)

/-! ### The diagonal scaling as a continuous linear map -/

/-- The diagonal scaling `z ↦ (aᵢ zᵢ)ᵢ` as a continuous linear map. -/
def scaleCLM {d : ℕ} (a : Fin d → ℝ) : Pt d →L[ℝ] Pt d :=
  ContinuousLinearMap.pi fun i => (a i) • (ContinuousLinearMap.proj i : Pt d →L[ℝ] ℝ)

@[simp] theorem scaleCLM_apply {d : ℕ} (a : Fin d → ℝ) (z : Pt d) :
    scaleCLM a z = fun i => a i * z i := rfl

theorem scaleCLM_norm_le_one {d : ℕ} {a : Fin d → ℝ} (ha : ∀ i, |a i| ≤ 1) :
    ‖scaleCLM a‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  rw [one_mul, scaleCLM_apply, pi_norm_le_iff_of_nonneg (norm_nonneg z)]
  intro i
  calc ‖a i * z i‖ = |a i| * |z i| := by simp
    _ ≤ 1 * ‖z‖ :=
        mul_le_mul (ha i) (by simpa using norm_le_pi_norm z i) (abs_nonneg _) zero_le_one
    _ = ‖z‖ := one_mul _

/-- Derivatives of `w ↦ φ(x + a·w)` are bounded by those of `φ` when `|aᵢ| ≤ 1`. -/
theorem comp_scale_deriv_bound {d : ℕ} {φ : Pt d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    {Φ : ℝ} {r : ℕ} (hΦ : ∀ m ≤ r, ∀ y, ‖iteratedFDeriv ℝ m φ y‖ ≤ Φ)
    (x : Pt d) {a : Fin d → ℝ} (ha : ∀ i, |a i| ≤ 1) {m : ℕ} (hm : m ≤ r) (z : Pt d) :
    ‖iteratedFDeriv ℝ m (fun w : Pt d => φ (x + scaleCLM a w)) z‖ ≤ Φ := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun v : Pt d => φ (x + v)) :=
    hφ.comp (contDiff_const.add contDiff_id)
  have hcomp : (fun w : Pt d => φ (x + scaleCLM a w))
      = (fun v : Pt d => φ (x + v)) ∘ (scaleCLM a) := rfl
  rw [hcomp,
    ContinuousLinearMap.iteratedFDeriv_comp_right (scaleCLM a) hg z (by exact_mod_cast le_top)]
  refine le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _) ?_
  have h1 : iteratedFDeriv ℝ m (fun v : Pt d => φ (x + v)) (scaleCLM a z)
      = iteratedFDeriv ℝ m φ (x + scaleCLM a z) := iteratedFDeriv_comp_add_left m x _
  rw [h1]
  have h2 : ∏ _i : Fin m, ‖scaleCLM a‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => scaleCLM_norm_le_one ha)
  calc ‖iteratedFDeriv ℝ m φ (x + scaleCLM a z)‖ * ∏ _i : Fin m, ‖scaleCLM a‖
      ≤ Φ * 1 := by
        refine mul_le_mul (hΦ m hm _) h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) ?_
        exact le_trans (norm_nonneg _) (hΦ m hm (x + scaleCLM a z))
    _ = Φ := mul_one Φ

/-- The localized, rescaled piece `w ↦ φ(x + a·w)·W(w)` has `C^r` norm at most
`2^r Φ Ω`. -/
theorem localized_deriv_bound {d : ℕ} {φ : Pt d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    {Φ Ω : ℝ} {r : ℕ} (hΦ : ∀ m ≤ r, ∀ y, ‖iteratedFDeriv ℝ m φ y‖ ≤ Φ) (hΦ0 : 0 ≤ Φ)
    (hΩ : ∀ m ≤ r, ∀ z, ‖iteratedFDeriv ℝ m (bumpBox (d := d)) z‖ ≤ Ω) (hΩ0 : 0 ≤ Ω)
    (x : Pt d) {a : Fin d → ℝ} (ha : ∀ i, |a i| ≤ 1) {m : ℕ} (hm : m ≤ r) (z : Pt d) :
    ‖iteratedFDeriv ℝ m (fun w : Pt d => φ (x + scaleCLM a w) * bumpBox w) z‖
      ≤ 2 ^ r * Φ * Ω := by
  have hu : ContDiff ℝ (⊤ : ℕ∞) (fun w : Pt d => φ (x + scaleCLM a w)) :=
    (hφ.comp (contDiff_const.add contDiff_id)).comp (scaleCLM a).contDiff
  have hstep := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) hu (bumpBox_contDiff (d := d)) z
    (n := m) (by exact_mod_cast le_top)
  refine hstep.trans ?_
  have hterm : ∀ i ∈ Finset.range (m + 1),
      (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun w : Pt d => φ (x + scaleCLM a w)) z‖ *
        ‖iteratedFDeriv ℝ (m - i) (bumpBox (d := d)) z‖ ≤ (m.choose i : ℝ) * Φ * Ω := by
    intro i hi
    have hib : i ≤ r := le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hm
    have h1 := comp_scale_deriv_bound hφ hΦ x ha hib z
    have h2 := hΩ (m - i) (le_trans (Nat.sub_le m i) hm) z
    have hc : (0:ℝ) ≤ (m.choose i : ℝ) := by positivity
    have step1 : (m.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun w : Pt d => φ (x + scaleCLM a w)) z‖ *
          ‖iteratedFDeriv ℝ (m - i) (bumpBox (d := d)) z‖
        ≤ (m.choose i : ℝ) * Φ * ‖iteratedFDeriv ℝ (m - i) (bumpBox (d := d)) z‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hc) (norm_nonneg _)
    have step2 : (m.choose i : ℝ) * Φ * ‖iteratedFDeriv ℝ (m - i) (bumpBox (d := d)) z‖
        ≤ (m.choose i : ℝ) * Φ * Ω :=
      mul_le_mul_of_nonneg_left h2 (mul_nonneg hc hΦ0)
    exact step1.trans step2
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have hsum : ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Φ * Ω
      = (2 ^ m : ℝ) * Φ * Ω := by
    have : ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) = (2 ^ m : ℝ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (Nat.sum_range_choose m)
    calc ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Φ * Ω
        = (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ)) * Φ * Ω := by
          rw [Finset.sum_mul, Finset.sum_mul]
      _ = (2 ^ m : ℝ) * Φ * Ω := by rw [this]
  rw [hsum]
  have : (2 : ℝ) ^ m ≤ 2 ^ r := by
    apply pow_le_pow_right₀ (by norm_num) hm
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hΦ0) hΩ0

end HairerAux



set_option autoImplicit false
open HairerAux
noncomputable section
namespace Hairer

/-- Uniform derivative bounds for a product, with the binomial loss explicit. -/
theorem mul_deriv_bound {d r : ℕ} {f g : Pt d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {F G : ℝ} (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hfB : ∀ m ≤ r, ∀ z, ‖iteratedFDeriv ℝ m f z‖ ≤ F)
    (hgB : ∀ m ≤ r, ∀ z, ‖iteratedFDeriv ℝ m g z‖ ≤ G)
    {m : ℕ} (hm : m ≤ r) (z : Pt d) :
    ‖iteratedFDeriv ℝ m (fun w ↦ f w * g w) z‖ ≤ 2 ^ r * F * G := by
  refine (norm_iteratedFDeriv_mul_le (𝕜 := ℝ) hf hg z
    (n := m) (by exact_mod_cast le_top)).trans ?_
  have ht : ∀ i ∈ Finset.range (m + 1),
      (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i f z‖ *
        ‖iteratedFDeriv ℝ (m - i) g z‖ ≤ (m.choose i : ℝ) * F * G := by
    intro i hi
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left
        (hfB i ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans hm) z) (by positivity)
    · exact hgB (m - i) ((Nat.sub_le m i).trans hm) z
    · exact norm_nonneg _
    · positivity
  refine (Finset.sum_le_sum ht).trans ?_
  have hsum : ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) = (2 : ℝ) ^ m := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (Nat.sum_range_choose m)
  rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hm) hF) hG

/-- Normalize a smooth function supported in the unit coordinate box. -/
theorem isTestBall_div_const {d r : ℕ} (s : Fin d → ℕ) {g : Pt d → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hzero : ∀ z, (∃ i, 1 ≤ |z i|) → g z = 0)
    {C : ℝ} (hC : 0 < C)
    (hB : ∀ m ≤ r, ∀ z, ‖iteratedFDeriv ℝ m g z‖ ≤ C) :
    IsTestBall s r (fun z ↦ g z / C) := by
  have hsmooth := hg.div_const C
  have hz : ∀ z, (∃ i, 1 ≤ |z i|) → g z / C = 0 := by
    intro z hi
    simp [hzero z hi]
  have hsupp : HasCompactSupport (fun z ↦ g z / C) := by
    apply HasCompactSupport.intro (isCompact_boxSet d 1)
    intro z hn
    simp only [boxSet, Set.mem_ofPred_eq, not_forall, not_le] at hn
    obtain ⟨i, hi⟩ := hn
    exact hz z ⟨i, hi.le⟩
  refine ⟨hsmooth, hsupp, ?_, ?_⟩
  · have hsub : tsupport (fun z ↦ g z / C) ⊆ boxSet d 1 := by
      apply closure_minimal _ (isCompact_boxSet d 1).isClosed
      intro z hn
      by_contra hn'
      simp only [boxSet, Set.mem_ofPred_eq, not_forall, not_le] at hn'
      obtain ⟨i, hi⟩ := hn'
      exact hn (hz z ⟨i, hi.le⟩)
    intro z hz'
    apply Real.iSup_le _ zero_le_one
    intro i
    exact Real.rpow_le_one (abs_nonneg _) (hsub hz' i) (by positivity)
  · intro m hm z
    have heq : (fun z ↦ g z / C) = C⁻¹ • g := by
      ext w
      simp [smul_eq_mul, div_eq_inv_mul]
    rw [heq, iteratedFDeriv_const_smul_apply
      (hg.of_le (by exact_mod_cast le_top)).contDiffAt, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hC)]
    calc C⁻¹ * ‖iteratedFDeriv ℝ m g z‖ ≤ C⁻¹ * C :=
        mul_le_mul_of_nonneg_left (hB m hm z) (inv_nonneg.mpr hC.le)
      _ = 1 := inv_mul_cancel₀ hC.ne'

/-- A fixed test admits one normalization constant for all overlaps of two
contractively rescaled grid bumps, independent of their centres. -/
theorem exists_overlap_test_normalization {d : ℕ} (s : Fin d → ℕ) (r : ℕ)
    {φ : Pt d → ℝ} (hφ : φ ∈ testFunctions d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x u : Pt d) (a b : Fin d → ℝ),
      (∀ i, |a i| ≤ 1) → (∀ i, |b i| ≤ 1) →
      IsTestBall s r (fun z ↦
        (φ (x + scaleCLM a z) * bumpBox (u + scaleCLM b z) * bumpBox z) / C) := by
  obtain ⟨F, hF, hfB⟩ := exists_deriv_bound hφ.1 hφ.2 r
  obtain ⟨G, hG, hgB⟩ := exists_deriv_bound
    (bumpBox_contDiff (d := d)) bumpBox_hasCompactSupport r
  let B : ℝ := 2 ^ r * (2 ^ r * F * G) * G
  refine ⟨B + 1, by dsimp [B]; positivity, ?_⟩
  intro x u a b ha hb
  have hfa : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ φ (x + scaleCLM a z)) :=
    (hφ.1.comp (contDiff_const.add contDiff_id)).comp (scaleCLM a).contDiff
  have hgb : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ bumpBox (u + scaleCLM b z)) :=
    (bumpBox_contDiff.comp (contDiff_const.add contDiff_id)).comp (scaleCLM b).contDiff
  apply isTestBall_div_const s ((hfa.mul hgb).mul bumpBox_contDiff)
  · intro z hz
    simp [bumpBox_eq_zero hz]
  · dsimp [B]
    positivity
  · intro m hm z
    have hab : ∀ n ≤ r, ∀ w,
        ‖iteratedFDeriv ℝ n (fun v ↦ φ (x + scaleCLM a v) *
          bumpBox (u + scaleCLM b v)) w‖ ≤ 2 ^ r * F * G := by
      intro n hn w
      exact mul_deriv_bound hfa hgb hF hG
        (fun q hq v ↦ comp_scale_deriv_bound hφ.1 hfB x ha hq v)
        (fun q hq v ↦ comp_scale_deriv_bound bumpBox_contDiff hgB u hb hq v) hn w
    exact (mul_deriv_bound (hfa.mul hgb) bumpBox_contDiff (by positivity) hG
      hab hgB hm z).trans (by dsimp [B]; linarith)

end Hairer


set_option autoImplicit false
open HairerAux
noncomputable section
namespace Hairer

/-- A product of fine and coarse grid weights is a scaled overlap test with
coefficient equal to its normalization constant times the anisotropic volume. -/
theorem overlap_rescaling {d : ℕ} (s : Fin d → ℕ) {δ : ℝ} (hδ : 0 < δ)
    (c : Fin d → ℝ) (hc : ∀ i, c i ≠ 0)
    (j k : Fin d → ℤ) (φ : Pt d → ℝ) {C : ℝ} (hC : C ≠ 0) :
    let a : Fin d → ℝ := fun i ↦ δ ^ s i
    let x : Pt d := fun i ↦ a i * (j i : ℝ)
    let u : Pt d := fun i ↦ x i / c i - (k i : ℝ)
    let b : Fin d → ℝ := fun i ↦ a i / c i
    ∀ y : Pt d,
      bumpBox (fun i ↦ y i / a i - (j i : ℝ)) *
        bumpBox (fun i ↦ y i / c i - (k i : ℝ)) * φ y =
        (C * δ ^ (scaleDim s : ℝ)) * scaledTest s δ x
          (fun z ↦ (φ (x + scaleCLM a z) * bumpBox (u + scaleCLM b z) * bumpBox z) / C) y := by
  intro a x u b y
  let z : Pt d := fun i ↦ (y i - x i) / δ ^ s i
  have ha (i : Fin d) : a i ≠ 0 := pow_ne_zero _ hδ.ne'
  have hx : x + scaleCLM a z = y := by
    funext i
    change a i * (j i : ℝ) + a i * ((y i - a i * (j i : ℝ)) / a i) = y i
    field_simp [ha i]
    ring
  have hfine : z = fun i ↦ y i / a i - (j i : ℝ) := by
    funext i
    change (y i - a i * (j i : ℝ)) / a i = _
    field_simp [ha i]
  have hcoarse : u + scaleCLM b z = fun i ↦ y i / c i - (k i : ℝ) := by
    funext i
    change a i * (j i : ℝ) / c i - (k i : ℝ) +
      (a i / c i) * ((y i - a i * (j i : ℝ)) / a i) = _
    field_simp [ha i, hc i]
    ring
  have hvolume : δ ^ (scaleDim s : ℝ) * δ ^ (-(scaleDim s : ℝ)) = 1 := by
    rw [← Real.rpow_add hδ, add_neg_cancel, Real.rpow_zero]
  change _ = (C * δ ^ (scaleDim s : ℝ)) * (δ ^ (-(scaleDim s : ℝ)) *
    ((φ (x + scaleCLM a z) * bumpBox (u + scaleCLM b z) * bumpBox z) / C))
  rw [hx, hcoarse, hfine]
  calc
    _ = (δ ^ (scaleDim s : ℝ) * δ ^ (-(scaleDim s : ℝ))) *
        (φ y * bumpBox (fun i ↦ y i / c i - (k i : ℝ)) *
          bumpBox (fun i ↦ y i / a i - (j i : ℝ))) := by rw [hvolume]; ring
    _ = _ := by field_simp [hC]

end Hairer


set_option autoImplicit false
open HairerAux
noncomputable section
open Hairer

/-- All fine/coarse grid overlaps of a fixed compactly supported test have a
common normalization constant. Each coefficient scales as the fine cell volume. -/
theorem overlap_decomposition_aux {d : ℕ} (s : Fin d → ℕ) (r : ℕ)
    {φ : Pt d → ℝ} (hφ : φ ∈ testFunctions d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
      ∀ (c : Fin d → ℝ), (∀ i, δ ^ s i ≤ c i) →
      ∀ (j k : Fin d → ℤ), ∃ η : Pt d → ℝ, IsTestBall s r η ∧
        ∀ y : Pt d,
          bumpBox (fun i ↦ y i / δ ^ s i - (j i : ℝ)) *
            bumpBox (fun i ↦ y i / c i - (k i : ℝ)) * φ y =
          (C * δ ^ (scaleDim s : ℝ)) *
            scaledTest s δ (fun i ↦ δ ^ s i * (j i : ℝ)) η y := by
  obtain ⟨C, hC, hnorm⟩ := exists_overlap_test_normalization s r hφ
  refine ⟨C, hC, ?_⟩
  intro δ hδ hδ1 c hc j k
  let a : Fin d → ℝ := fun i ↦ δ ^ s i
  let x : Pt d := fun i ↦ a i * (j i : ℝ)
  let u : Pt d := fun i ↦ x i / c i - (k i : ℝ)
  let b : Fin d → ℝ := fun i ↦ a i / c i
  have ha0 (i : Fin d) : 0 < a i := pow_pos hδ _
  have hc0 (i : Fin d) : 0 < c i := (ha0 i).trans_le (hc i)
  have ha (i : Fin d) : |a i| ≤ 1 := by
    rw [abs_of_pos (ha0 i)]
    exact pow_le_one₀ hδ.le hδ1
  have hb (i : Fin d) : |b i| ≤ 1 := by
    rw [abs_of_pos (div_pos (ha0 i) (hc0 i))]
    exact (div_le_one (hc0 i)).mpr (hc i)
  refine ⟨fun z ↦ (φ (x + scaleCLM a z) * bumpBox (u + scaleCLM b z) *
    bumpBox z) / C, hnorm x u a b ha hb, ?_⟩
  exact overlap_rescaling s hδ c (fun i ↦ (hc0 i).ne') j k φ hC.ne'


open Hairer

theorem Hairer.grid_overlap_decomposition_scaledTest {d : ℕ} (s : Fin d → ℕ) (r : ℕ)
    {φ : Pt d → ℝ} (hφ : φ ∈ testFunctions d) :
    let W : Pt d → ℝ := fun z ↦ ∏ i,
      (Real.smoothTransition (z i + 1) - Real.smoothTransition (z i))
    ∃ C : ℝ, 0 < C ∧ ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
      ∀ (c : Fin d → ℝ), (∀ i, δ ^ s i ≤ c i) →
      ∀ (j k : Fin d → ℤ), ∃ η : Pt d → ℝ, IsTestBall s r η ∧
        ∀ y : Pt d,
          W (fun i ↦ y i / δ ^ s i - (j i : ℝ)) *
            W (fun i ↦ y i / c i - (k i : ℝ)) * φ y =
          (C * δ ^ (scaleDim s : ℝ)) *
            scaledTest s δ (fun i ↦ δ ^ s i * (j i : ℝ)) η y := by
  exact overlap_decomposition_aux s r hφ




set_option autoImplicit false
open BigOperators

noncomputable section

namespace Hairer

/-- The scaled distance is nonnegative, including in dimension zero. -/
theorem snorm_nonneg {d : ℕ} (s : Fin d → ℕ) (x : Pt d) : 0 ≤ snorm s x := by
  cases isEmpty_or_nonempty (Fin d) with
  | inl h =>
    let _ := h
    simp [snorm]
  | inr h =>
    let _ := h
    let i : Fin d := Classical.choice h
    unfold snorm
    exact (Real.rpow_nonneg (abs_nonneg (x i)) ((1 : ℝ) / (s i : ℝ))).trans
      (le_ciSup (Set.finite_range (fun j : Fin d ↦
        |x j| ^ ((1 : ℝ) / (s j : ℝ)))).bddAbove i)

/-- A triangular reexpansion preserves truncation below a fixed homogeneity. -/
theorem IsRegularityStructure.map_vanishing
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {Γ : ModelSpace A E ≃ₗ[ℝ] ModelSpace A E} (hΓ : Γ ∈ G)
    {γ : ℝ} {v : ModelSpace A E}
    (hv : ∀ a : A, γ ≤ (a : ℝ) → proj a v = 0) :
    ∀ b : A, γ ≤ (b : ℝ) → proj b (Γ v) = 0 := by
  classical
  intro b hb
  have hsum : ∑ a ∈ v.support, incl a (proj a v) = v := DirectSum.sum_support_of v
  have heq := congrArg (fun w ↦ proj b (Γ w)) hsum
  rw [← heq]
  simp only [map_sum]
  apply Finset.sum_eq_zero
  intro a ha
  have hne : proj a v ≠ 0 := DFinsupp.mem_support_iff.mp ha
  have haγ : (a : ℝ) < γ := lt_of_not_ge fun h ↦ hne (hv a h)
  have hab : (a : ℝ) < (b : ℝ) := haγ.trans_le hb
  have hneq : a ≠ b := fun h ↦ (ne_of_lt hab) (congrArg Subtype.val h)
  have ht := hT.triangular Γ hΓ a b (proj a v) hab.le
  simpa [map_sub, proj, incl, DirectSum.component.of, hneq] using ht

/-- Model germs tested at scale `δ` agree to order `γ` when their base points
are at distance at most a fixed multiple of `δ`. The separate unit-distance
hypothesis is precisely the range of the modelled increment bound. -/
theorem model_germ_coherence_multiple
    {d : ℕ} {s : Fin d → ℕ} {γ : ℝ}
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f)
    (L : ℝ) (hL : 0 ≤ L) :
    ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ K, ∀ y ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        snorm s (x - y) ≤ 1 → snorm s (x - y) ≤ L * δ →
        ∀ η : Pt d → ℝ, IsTestBall s r η →
          |(Pi x (f x) - Pi y (f y)).eval (scaledTest s δ x η)| ≤ C * δ ^ γ := by
  classical
  have hfinite : {a : A | (a : ℝ) ≤ γ}.Finite := by
    simpa only [Set.preimage_ofPred_eq, Subtype.coe_prop, true_and] using
      (hT.locallyFinite γ).preimage (f := fun a : A ↦ (a : ℝ))
        Subtype.val_injective.injOn
  let J := hfinite.toFinset
  intro K hK
  obtain ⟨Cp, hp⟩ := hmod.pi_bound (max γ 1) (lt_of_lt_of_le zero_lt_one (le_max_right γ 1)) K hK
  obtain ⟨Cf, _, hfbound⟩ := hf.bound K hK
  let B : ℝ := max Cp 0 * max Cf 0
  have hB : 0 ≤ B := mul_nonneg (le_max_right _ _) (le_max_right _ _)
  refine ⟨B * ∑ a ∈ J, L ^ (γ - (a : ℝ)),
    mul_nonneg hB (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg hL _), ?_⟩
  intro x hx y hy δ hδ hδone hxyone hxy η hη
  let v := f x - Gam x y (f y)
  have hvan (a : A) (ha : γ ≤ (a : ℝ)) : proj a v = 0 := by
    change proj a (f x - Gam x y (f y)) = 0
    rw [map_sub, hf.vanishing x a ha,
      hT.map_vanishing (hmod.gam_mem x y) (hf.vanishing y) a ha, sub_self]
  have hlt (a : A) (ha : a ∈ v.support) : (a : ℝ) < γ := by
    have hne : proj a v ≠ 0 := DFinsupp.mem_support_iff.mp ha
    exact lt_of_not_ge fun h ↦ hne (hvan a h)
  have hsupport : v.support ⊆ J := by
    intro a ha
    exact hfinite.mem_toFinset.mpr (hlt a ha).le
  let φ := scaledTest s δ x η
  have hφ : φ ∈ testFunctions d := scaledTest_mem s hδ x ⟨hη.smooth, hη.compactSupport⟩
  have hsum : ∑ a ∈ v.support, incl a (proj a v) = v := DirectSum.sum_support_of v
  have heval : (Pi x (f x) - Pi y (f y)).eval φ =
      ∑ a ∈ v.support, (Pi x (incl a (proj a v))).eval φ := by
    rw [hmod.pi_comp x y (f y), ← map_sub]
    simp only [Distrib.eval, dif_pos hφ]
    simpa only [map_sum, LinearMap.sum_apply] using
      (congrArg (fun w ↦ (Pi x w) ⟨φ, hφ⟩) hsum).symm
  have hterm (a : A) (ha : a ∈ v.support) :
      |(Pi x (incl a (proj a v))).eval φ| ≤ B * L ^ (γ - (a : ℝ)) * δ ^ γ := by
    have haγ := hlt a ha
    have hn : ‖proj a v‖ ≤ max Cf 0 * (L * δ) ^ (γ - (a : ℝ)) := by
      calc
        _ ≤ Cf * snorm s (x - y) ^ (γ - (a : ℝ)) :=
          hfbound x hx y hy hxyone a haγ
        _ ≤ max Cf 0 * (L * δ) ^ (γ - (a : ℝ)) :=
          mul_le_mul (le_max_left Cf 0)
            (Real.rpow_le_rpow (snorm_nonneg s (x - y)) hxy (sub_nonneg.mpr haγ.le))
            (Real.rpow_nonneg (snorm_nonneg s (x - y)) _) (le_max_right Cf 0)
    calc
      _ ≤ Cp * ‖proj a v‖ * δ ^ (a : ℝ) :=
        hp a (haγ.trans_le (le_max_left γ 1)) _ x hx δ hδ hδone η hη
      _ ≤ max Cp 0 * (max Cf 0 * (L * δ) ^ (γ - (a : ℝ))) * δ ^ (a : ℝ) := by
        have hc := le_max_left Cp 0
        have hc0 := le_max_right Cp 0
        gcongr
      _ = B * L ^ (γ - (a : ℝ)) * δ ^ γ := by
        rw [Real.mul_rpow hL hδ.le]
        simp only [B, mul_assoc, ← Real.rpow_add hδ, sub_add_cancel]
  rw [heval]
  calc
    _ ≤ ∑ a ∈ v.support, |(Pi x (incl a (proj a v))).eval φ| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ v.support, B * L ^ (γ - (a : ℝ)) * δ ^ γ := Finset.sum_le_sum hterm
    _ ≤ ∑ a ∈ J, B * L ^ (γ - (a : ℝ)) * δ ^ γ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsupport
        (fun a _ _ ↦ mul_nonneg (mul_nonneg hB (Real.rpow_nonneg hL _))
          (Real.rpow_nonneg hδ.le _))
    _ = (B * ∑ a ∈ J, L ^ (γ - (a : ℝ))) * δ ^ γ := by
      rw [Finset.mul_sum, Finset.sum_mul]

end Hairer


set_option autoImplicit false
noncomputable section
namespace Hairer

/-- Coordinate control implies control of the anisotropic quasi-norm. -/
theorem snorm_le_of_coord_pow_le {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s)
    {R : ℝ} (hR : 0 ≤ R) {x : Pt d} (hx : ∀ i, |x i| ≤ R ^ s i) :
    snorm s x ≤ R := by
  apply Real.iSup_le _ hR
  intro i
  calc
    |x i| ^ ((1 : ℝ) / (s i : ℝ)) ≤ (R ^ s i) ^ ((1 : ℝ) / (s i : ℝ)) :=
      Real.rpow_le_rpow (abs_nonneg _) (hx i) (by positivity)
    _ = R := by
      rw [one_div, Real.pow_rpow_inv_natCast hR (by have := hs i; omega)]

/-- Overlapping coordinate boxes at scales `δ ≤ ρ` have centres at scaled
distance at most `2ρ`. -/
theorem snorm_sub_le_of_box_overlap {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s)
    {δ ρ : ℝ} (hδ : 0 ≤ δ) (hδρ : δ ≤ ρ) {x z w : Pt d}
    (hx : ∀ i, |w i - x i| ≤ δ ^ s i)
    (hz : ∀ i, |w i - z i| ≤ ρ ^ s i) :
    snorm s (x - z) ≤ 2 * ρ := by
  have hρ : 0 ≤ ρ := hδ.trans hδρ
  apply snorm_le_of_coord_pow_le hs (mul_nonneg (by norm_num) hρ)
  intro i
  have hsum : |x i - z i| ≤ |w i - x i| + |w i - z i| := by
    have h := abs_add_le (x i - w i) (w i - z i)
    rw [sub_add_sub_cancel, abs_sub_comm (x i) (w i)] at h
    exact h
  change |x i - z i| ≤ (2 * ρ) ^ s i
  calc
    _ ≤ δ ^ s i + ρ ^ s i := hsum.trans (add_le_add (hx i) (hz i))
    _ ≤ ρ ^ s i + ρ ^ s i := add_le_add (pow_le_pow_left₀ hδ hδρ _) le_rfl
    _ = 2 * ρ ^ s i := by ring
    _ ≤ 2 ^ s i * ρ ^ s i := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hρ _)
      have h := pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) (hs i)
      simpa using h
    _ = (2 * ρ) ^ s i := (mul_pow _ _ _).symm

end Hairer

open Hairer

/-- The fine-scale germ estimate for two overlapping boxes at adjacent dyadic
scales. This applies directly to the support geometry of grid-weight products. -/
theorem Hairer.model_germ_bound_of_dyadic_overlap
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s) {γ : ℝ}
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f) :
    ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ K, ∀ z ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
        (∃ w : Pt d, (∀ i, |w i - x i| ≤ δ ^ s i) ∧
          (∀ i, |w i - z i| ≤ (2 * δ) ^ s i)) →
        ∀ η : Pt d → ℝ, IsTestBall s r η →
          |(Pi x (f x) - Pi z (f z)).eval (scaledTest s δ x η)| ≤ C * δ ^ γ := by
  intro K hK
  obtain ⟨C, hC, hbound⟩ := model_germ_coherence_multiple hT hmod hf 4 (by norm_num) K hK
  refine ⟨C, hC, ?_⟩
  rintro x hx z hz δ hδ hδsmall ⟨w, hwx, hwz⟩ η hη
  have hdist : snorm s (x - z) ≤ 4 * δ := by
    have h := snorm_sub_le_of_box_overlap hs hδ.le
      (show δ ≤ 2 * δ by linarith) hwx hwz
    linarith
  exact hbound x hx z hz δ hδ (by linarith) (hdist.trans (by linarith)) hdist η hη




set_option autoImplicit false
noncomputable section
open Hairer

/-- A fine coordinate box meets at most `5^d` coarse grid boxes when its widths
are no greater than the coarse widths. The bound is independent of scale. -/
theorem Hairer.grid_overlap_count {d : ℕ} (x : Pt d) (a c : Fin d → ℝ)
    (hc : ∀ i, 0 < c i) (hac : ∀ i, a i ≤ c i) :
    ∃ S : Finset (Fin d → ℤ), S.card ≤ 5 ^ d ∧
      ∀ k : Fin d → ℤ, (∃ y : Pt d, (∀ i, |y i - x i| < a i) ∧
        (∀ i, |y i / c i - (k i : ℝ)| < 1)) → k ∈ S := by
  classical
  let n : Fin d → ℤ := fun i ↦ ⌊x i / c i⌋
  let S : Finset (Fin d → ℤ) :=
    Fintype.piFinset (fun i ↦ Finset.Icc (n i - 2) (n i + 2))
  refine ⟨S, ?_, ?_⟩
  · have hcard (i : Fin d) : (Finset.Icc (n i - 2) (n i + 2)).card = 5 := by
      rw [Int.card_Icc]
      omega
    dsimp [S]
    rw [Fintype.card_piFinset]
    simp only [hcard, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact le_rfl
  · rintro k ⟨y, hy, hk⟩
    apply Fintype.mem_piFinset.mpr
    intro i
    have hdist : |y i / c i - x i / c i| < 1 := by
      rw [← sub_div, abs_div, abs_of_pos (hc i)]
      exact (div_lt_one (hc i)).mpr ((hy i).trans_le (hac i))
    have hnear : |x i / c i - (k i : ℝ)| < 2 := by
      have ht := abs_add_le (x i / c i - y i / c i) (y i / c i - (k i : ℝ))
      rw [sub_add_sub_cancel] at ht
      rw [abs_sub_comm] at hdist
      linarith [hk i]
    have hnlo : (n i : ℝ) ≤ x i / c i := Int.floor_le _
    have hnhi : x i / c i < (n i : ℝ) + 1 := Int.lt_floor_add_one _
    have hlo : ((n i - 2 : ℤ) : ℝ) ≤ (k i : ℝ) := by
      push_cast
      linarith [(abs_lt.mp hnear).1, (abs_lt.mp hnear).2]
    have hhi : (k i : ℝ) < ((n i + 3 : ℤ) : ℝ) := by
      push_cast
      linarith [(abs_lt.mp hnear).1, (abs_lt.mp hnear).2]
    rw [Finset.mem_Icc]
    have hlo' : n i - 2 ≤ k i := by exact_mod_cast hlo
    have hhi' : k i < n i + 3 := by exact_mod_cast hhi
    omega




set_option autoImplicit false
open BigOperators
noncomputable section
namespace Hairer

def gridBump {d : ℕ} (z : Pt d) : ℝ :=
  ∏ i, (Real.smoothTransition (z i + 1) - Real.smoothTransition (z i))

def gridWeightAt {d : ℕ} (s : Fin d → ℕ) (δ : ℝ) (j : Fin d → ℤ) (y : Pt d) : ℝ :=
  gridBump (fun i ↦ y i / δ ^ s i - (j i : ℝ))

def gridCentre {d : ℕ} (s : Fin d → ℕ) (δ : ℝ) (j : Fin d → ℤ) : Pt d :=
  fun i ↦ δ ^ s i * (j i : ℝ)

theorem gridBump_ne_zero_coord {d : ℕ} {z : Pt d} (h : gridBump z ≠ 0)
    (i : Fin d) : |z i| < 1 := by
  by_contra! hi
  have hz : Real.smoothTransition (z i + 1) - Real.smoothTransition (z i) = 0 := by
    rcases le_or_gt 1 (z i) with h1 | h1
    · rw [Real.smoothTransition.one_of_one_le (by linarith),
        Real.smoothTransition.one_of_one_le h1, sub_self]
    · have h2 : z i ≤ -1 := by
        rcases le_or_gt 0 (z i) with h2 | h2
        · rw [abs_of_nonneg h2] at hi
          linarith
        · rw [abs_of_neg h2] at hi
          linarith
      rw [Real.smoothTransition.zero_of_nonpos (by linarith),
        Real.smoothTransition.zero_of_nonpos (by linarith), sub_self]
  exact h (Finset.prod_eq_zero (Finset.mem_univ i) hz)

theorem gridWeightAt_ne_zero_coord {d : ℕ} (s : Fin d → ℕ) {δ : ℝ} (hδ : 0 < δ)
    {j : Fin d → ℤ} {y : Pt d} (h : gridWeightAt s δ j y ≠ 0) (i : Fin d) :
    |y i - gridCentre s δ j i| < δ ^ s i := by
  have hpow : 0 < δ ^ s i := pow_pos hδ _
  have hi := gridBump_ne_zero_coord h i
  change |y i - δ ^ s i * (j i : ℝ)| < δ ^ s i
  have heq : y i / δ ^ s i - (j i : ℝ) =
      (y i - δ ^ s i * (j i : ℝ)) / δ ^ s i := by field_simp
  rw [heq, abs_div, abs_of_pos hpow] at hi
  exact (div_lt_one hpow).mp hi

/-- The number of active fine cells times their volume is uniformly bounded
when their supports meet a fixed coordinate box. -/
theorem grid_active_volume_bound {d : ℕ} (s : Fin d → ℕ) {R : ℝ} (hR : 0 ≤ R)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (S : Finset (Fin d → ℤ))
    (hS : ∀ j ∈ S, ∃ y : Pt d, (∀ i, |y i| ≤ R) ∧ gridWeightAt s δ j y ≠ 0) :
    (S.card : ℝ) * δ ^ (scaleDim s : ℝ) ≤ (2 * R + 5) ^ d := by
  classical
  let N : Fin d → ℕ := fun i ↦ ⌈R / δ ^ s i⌉₊ + 1
  let U : Finset (Fin d → ℤ) :=
    Fintype.piFinset (fun i ↦ Finset.Icc (-(N i : ℤ)) (N i : ℤ))
  have hpow (i : Fin d) : 0 < δ ^ s i := pow_pos hδ _
  have hpow1 (i : Fin d) : δ ^ s i ≤ 1 := pow_le_one₀ hδ.le hδ1
  have hNlo (i : Fin d) : R / δ ^ s i + 1 ≤ (N i : ℝ) := by
    dsimp [N]
    push_cast
    linarith [Nat.le_ceil (R / δ ^ s i)]
  have hNhi (i : Fin d) : (N i : ℝ) ≤ R / δ ^ s i + 2 := by
    dsimp [N]
    push_cast
    have h := Nat.ceil_lt_add_one (a := R / δ ^ s i) (div_nonneg hR (hpow i).le)
    linarith
  have hSU : S ⊆ U := by
    intro j hj
    obtain ⟨y, hy, hw⟩ := hS j hj
    apply Fintype.mem_piFinset.mpr
    intro i
    have hnear := gridBump_ne_zero_coord hw i
    have hydiv : |y i / δ ^ s i| ≤ R / δ ^ s i := by
      rw [abs_div, abs_of_pos (hpow i)]
      exact div_le_div_of_nonneg_right (hy i) (hpow i).le
    have hjbound : |(j i : ℝ)| ≤ (N i : ℝ) := by
      have ht' := abs_add_le ((j i : ℝ) - y i / δ ^ s i) (y i / δ ^ s i)
      rw [sub_add_cancel, abs_sub_comm (j i : ℝ)] at ht'
      linarith [hNlo i]
    rw [Finset.mem_Icc]
    constructor
    · exact_mod_cast (abs_le.mp hjbound).1
    · exact_mod_cast (abs_le.mp hjbound).2
  have hcardi (i : Fin d) :
      ((Finset.Icc (-(N i : ℤ)) (N i : ℤ)).card : ℝ) ≤ (2 * R + 5) / δ ^ s i := by
    have heq : (Finset.Icc (-(N i : ℤ)) (N i : ℤ)).card = 2 * N i + 1 := by
      rw [Int.card_Icc]
      omega
    rw [heq]
    push_cast
    apply (le_div_iff₀ (hpow i)).mpr
    have hN := hNhi i
    have hstep : (2 * (N i : ℝ) + 1) * δ ^ s i ≤ 2 * R + 5 * δ ^ s i := by
      have heq' : (2 * (R / δ ^ s i + 2) + 1) * δ ^ s i =
          2 * R + 5 * δ ^ s i := by field_simp; ring
      calc
        _ ≤ (2 * (R / δ ^ s i + 2) + 1) * δ ^ s i := by gcongr
        _ = _ := heq'
    nlinarith [hpow1 i]
  have hcard : (S.card : ℝ) ≤ (2 * R + 5) ^ d / δ ^ scaleDim s := by
    calc
      _ ≤ (U.card : ℝ) := by exact_mod_cast Finset.card_le_card hSU
      _ = ∏ i, ((Finset.Icc (-(N i : ℤ)) (N i : ℤ)).card : ℝ) := by
        simp [U, Fintype.card_piFinset, Nat.cast_prod]
      _ ≤ ∏ i, ((2 * R + 5) / δ ^ s i) :=
        Finset.prod_le_prod (fun _ _ ↦ by positivity) (fun i _ ↦ hcardi i)
      _ = _ := by
        rw [Finset.prod_div_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum]
        simp [scaleDim]
  rw [Real.rpow_natCast]
  exact (le_div_iff₀ (pow_pos hδ (scaleDim s))).mp hcard

/-- Only a uniformly bounded number of coarse cells can contribute for each fine cell. -/
theorem grid_pair_sum_bound {d : ℕ} (s : Fin d → ℕ) {R : ℝ} (hR : 0 ≤ R)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (S T : Finset (Fin d → ℤ))
    (φ : Pt d → ℝ) (hφ : ∀ y, φ y ≠ 0 → ∀ i, |y i| ≤ R)
    (b : (Fin d → ℤ) → (Fin d → ℤ) → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ j ∈ S, ∀ k ∈ T, b j k ≤ B * δ ^ (scaleDim s : ℝ))
    (hz : ∀ j ∈ S, ∀ k ∈ T,
      (∀ y, gridWeightAt s δ j y * gridWeightAt s (2 * δ) k y * φ y = 0) →
      b j k = 0) :
    ∑ j ∈ S, ∑ k ∈ T, b j k ≤ (2 * R + 5) ^ d * (5 : ℝ) ^ d * B := by
  classical
  let U := S.filter (fun j ↦ ∃ y, gridWeightAt s δ j y * φ y ≠ 0)
  have hU : (U.card : ℝ) * δ ^ (scaleDim s : ℝ) ≤ (2 * R + 5) ^ d := by
    apply grid_active_volume_bound s hR hδ hδ1
    intro j hj
    obtain ⟨y, hy⟩ := (Finset.mem_filter.mp hj).2
    exact ⟨y, hφ y (mul_ne_zero_iff.mp hy).2, (mul_ne_zero_iff.mp hy).1⟩
  have hinner (j : Fin d → ℤ) (hj : j ∈ S) :
      ∑ k ∈ T, b j k ≤ (5 : ℝ) ^ d * (B * δ ^ (scaleDim s : ℝ)) := by
    let V := T.filter (fun k ↦ ∃ y,
      gridWeightAt s δ j y * gridWeightAt s (2 * δ) k y * φ y ≠ 0)
    obtain ⟨N, hN, hcover⟩ := grid_overlap_count (gridCentre s δ j)
      (fun i ↦ δ ^ s i) (fun i ↦ (2 * δ) ^ s i)
      (fun i ↦ pow_pos (by linarith) _) (fun i ↦ pow_le_pow_left₀ hδ.le (by linarith) _)
    have hVN : V ⊆ N := by
      intro k hk
      obtain ⟨y, hy⟩ := (Finset.mem_filter.mp hk).2
      have hw := mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hy).1
      exact hcover k ⟨y, gridWeightAt_ne_zero_coord s hδ hw.1,
        gridBump_ne_zero_coord hw.2⟩
    calc
      _ = ∑ k ∈ V, b j k := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro k hk hkv
        apply hz j hj k hk
        intro y
        by_contra hy
        exact hkv (Finset.mem_filter.mpr ⟨hk, y, hy⟩)
      _ ≤ ∑ _k ∈ V, B * δ ^ (scaleDim s : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        exact hb j hj k (Finset.mem_filter.mp hk).1
      _ = (V.card : ℝ) * (B * δ ^ (scaleDim s : ℝ)) := by simp
      _ ≤ (5 : ℝ) ^ d * (B * δ ^ (scaleDim s : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg hB (Real.rpow_nonneg hδ.le _))
        exact_mod_cast (Finset.card_le_card hVN).trans hN
  calc
    _ = ∑ j ∈ U, ∑ k ∈ T, b j k := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j hj hju
      apply Finset.sum_eq_zero
      intro k hk
      apply hz j hj k hk
      intro y
      have hw : gridWeightAt s δ j y * φ y = 0 := by
        by_contra hw
        exact hju (Finset.mem_filter.mpr ⟨hj, y, hw⟩)
      calc
        _ = (gridWeightAt s δ j y * φ y) * gridWeightAt s (2 * δ) k y := by ring
        _ = 0 := by rw [hw, zero_mul]
    _ ≤ ∑ _j ∈ U, (5 : ℝ) ^ d * (B * δ ^ (scaleDim s : ℝ)) := by
      exact Finset.sum_le_sum (fun j hj ↦ hinner j (Finset.mem_filter.mp hj).1)
    _ = ((U.card : ℝ) * δ ^ (scaleDim s : ℝ)) * (5 : ℝ) ^ d * B := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hU (by positivity)) hB

theorem grid_eval_const_mul {d : ℕ} (ξ : Distrib d) (c : ℝ)
    {φ : Pt d → ℝ} (hφ : φ ∈ testFunctions d) :
    ξ.eval (fun y ↦ c * φ y) = c * ξ.eval φ := by
  have hc : (fun y ↦ c * φ y) ∈ testFunctions d := (testFunctions d).smul_mem c hφ
  simp only [Distrib.eval, dif_pos hφ, dif_pos hc]
  change ξ (c • (⟨φ, hφ⟩ : testFunctions d)) = _
  exact ξ.map_smul c ⟨φ, hφ⟩

theorem grid_eval_zero {d : ℕ} (ξ : Distrib d) : ξ.eval (fun _ ↦ 0) = 0 := by
  rw [Distrib.eval, dif_pos (show (fun _ : Pt d ↦ (0 : ℝ)) ∈ testFunctions d from
    (testFunctions d).zero_mem)]
  exact ξ.map_zero

/-- Absolute fine/coarse overlap pairings of model germs have a summable dyadic
bound when the modelled regularity is positive. The estimate itself holds for any γ. -/
theorem model_germ_grid_sum_bound
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s) {γ : ℝ}
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f)
    (K : Set (Pt d)) (hK : IsCompact K) (φ : Pt d → ℝ) (hφ : φ ∈ testFunctions d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
      ∀ S T : Finset (Fin d → ℤ),
      (∀ j ∈ S, gridCentre s δ j ∈ K) →
      (∀ k ∈ T, gridCentre s (2 * δ) k ∈ K) →
      ∑ j ∈ S, ∑ k ∈ T,
        |(Pi (gridCentre s δ j) (f (gridCentre s δ j)) -
          Pi (gridCentre s (2 * δ) k) (f (gridCentre s (2 * δ) k))).eval
          (fun y ↦ gridWeightAt s δ j y * gridWeightAt s (2 * δ) k y * φ y)|
        ≤ C * δ ^ γ := by
  classical
  obtain ⟨R, hRpos, hR⟩ := hφ.2.isCompact.isBounded.subset_closedBall_lt 0 0
  have hφR : ∀ y, φ y ≠ 0 → ∀ i, |y i| ≤ R := by
    intro y hy i
    have hyR : ‖y‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hR (subset_tsupport φ hy)
    exact (show |y i| ≤ ‖y‖ by simpa using norm_le_pi_norm y i).trans hyR
  obtain ⟨L, hL, hnorm⟩ := grid_overlap_decomposition_scaledTest s r hφ
  obtain ⟨M, hM, hgerm⟩ := model_germ_bound_of_dyadic_overlap hs hT hmod hf K hK
  refine ⟨(2 * R + 5) ^ d * (5 : ℝ) ^ d * (L * M), by positivity, ?_⟩
  intro δ hδ hδsmall S T hS hTcentres
  have hδ1 : δ ≤ 1 := by linarith
  have hscale (i : Fin d) : δ ^ s i ≤ (2 * δ) ^ s i :=
    pow_le_pow_left₀ hδ.le (by linarith) _
  let P := fun j k y ↦ gridWeightAt s δ j y * gridWeightAt s (2 * δ) k y * φ y
  let ξ := fun j k ↦ Pi (gridCentre s δ j) (f (gridCentre s δ j)) -
    Pi (gridCentre s (2 * δ) k) (f (gridCentre s (2 * δ) k))
  have hzero (j k : Fin d → ℤ) (hz : ∀ y, P j k y = 0) :
      |(ξ j k).eval (P j k)| = 0 := by
    rw [show P j k = fun _ ↦ 0 from funext hz, grid_eval_zero, abs_zero]
  have hpair (j : Fin d → ℤ) (hj : j ∈ S) (k : Fin d → ℤ) (hk : k ∈ T) :
      |(ξ j k).eval (P j k)| ≤ (L * M * δ ^ γ) * δ ^ (scaleDim s : ℝ) := by
    by_cases hz : ∀ y, P j k y = 0
    · rw [hzero j k hz]
      positivity
    push Not at hz
    obtain ⟨w, hw⟩ := hz
    have hw' := mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hw).1
    obtain ⟨η, hη, heq⟩ := hnorm δ hδ hδ1 (fun i ↦ (2 * δ) ^ s i) hscale j k
    have hP : P j k = fun y ↦ (L * δ ^ (scaleDim s : ℝ)) *
        scaledTest s δ (gridCentre s δ j) η y := funext heq
    have hηtest := scaledTest_mem s hδ (gridCentre s δ j) ⟨hη.smooth, hη.compactSupport⟩
    have hbound := hgerm (gridCentre s δ j) (hS j hj)
      (gridCentre s (2 * δ) k) (hTcentres k hk) δ hδ hδsmall
      ⟨w, fun i ↦ (gridWeightAt_ne_zero_coord s hδ hw'.1 i).le,
        fun i ↦ (gridWeightAt_ne_zero_coord s (by linarith) hw'.2 i).le⟩ η hη
    rw [hP, grid_eval_const_mul _ _ hηtest, abs_mul,
      abs_of_nonneg (show 0 ≤ L * δ ^ (scaleDim s : ℝ) by positivity)]
    calc
      _ ≤ (L * δ ^ (scaleDim s : ℝ)) * (M * δ ^ γ) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = _ := by ring
  have hsum := grid_pair_sum_bound s hRpos.le hδ hδ1 S T φ hφR
    (fun j k ↦ |(ξ j k).eval (P j k)|)
    (B := L * M * δ ^ γ) (by positivity) hpair
    (fun j _ k _ hz ↦ hzero j k hz)
  calc
    _ ≤ (2 * R + 5) ^ d * (5 : ℝ) ^ d * (L * M * δ ^ γ) := hsum
    _ = _ := by ring

end Hairer

open Hairer

theorem Hairer.dyadic_grid_germ_sum_bound
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s) {γ : ℝ}
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f)
    (K : Set (Pt d)) (hK : IsCompact K) (φ : Pt d → ℝ) (hφ : φ ∈ testFunctions d) :
    let W : Pt d → ℝ := fun z ↦
      ∏ i, (Real.smoothTransition (z i + 1) - Real.smoothTransition (z i))
    let ψ := fun (δ : ℝ) (j : Fin d → ℤ) (y : Pt d) ↦
      W (fun i ↦ y i / δ ^ s i - (j i : ℝ))
    let X := fun (δ : ℝ) (j : Fin d → ℤ) (i : Fin d) ↦ δ ^ s i * (j i : ℝ)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
      ∀ S T : Finset (Fin d → ℤ),
      (∀ j ∈ S, X δ j ∈ K) →
      (∀ k ∈ T, X (2 * δ) k ∈ K) →
      ∑ j ∈ S, ∑ k ∈ T,
        |(Pi (X δ j) (f (X δ j)) -
          Pi (X (2 * δ) k) (f (X (2 * δ) k))).eval
          (fun y ↦ ψ δ j y * ψ (2 * δ) k y * φ y)|
        ≤ C * δ ^ γ := by
  exact model_germ_grid_sum_bound hs hT hmod hf K hK φ hφ



set_option autoImplicit false
open BigOperators

noncomputable section

namespace Hairer

/-- Multiplication by a smooth function preserves compactly supported tests. -/
def mulTest {d : ℕ} (ψ : Pt d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    testFunctions d →ₗ[ℝ] testFunctions d where
  toFun φ := ⟨ψ * φ, hψ.mul φ.property.1, φ.property.2.mul_left⟩
  map_add' φ χ := by
    apply Subtype.ext
    funext y
    exact mul_add _ _ _
  map_smul' c φ := by
    apply Subtype.ext
    funext y
    change ψ y * (c * φ.val y) = c * (ψ y * φ.val y)
    ring

@[simp] theorem mulTest_apply {d : ℕ} (ψ : Pt d → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (φ : testFunctions d) (y : Pt d) :
    (mulTest ψ hψ φ).val y = ψ y * φ.val y := rfl

/-- Two smooth localizations commute, including as bundled test functions. -/
theorem mulTest_comm {d : ℕ} (ψ χ : Pt d → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (φ : testFunctions d) :
    mulTest ψ hψ (mulTest χ hχ φ) = mulTest χ hχ (mulTest ψ hψ φ) := by
  apply Subtype.ext
  funext y
  change ψ y * (χ y * φ.val y) = χ y * (ψ y * φ.val y)
  ring

/-- A partition need only sum to one where the test is nonzero. -/
theorem sum_mulTest {d : ℕ} {ι : Type*} (S : Finset ι)
    (ψ : ι → Pt d → ℝ) (hψ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (ψ i))
    (φ : testFunctions d)
    (hpart : ∀ y, φ.val y ≠ 0 → ∑ i ∈ S, ψ i y = 1) :
    ∑ i ∈ S, mulTest (ψ i) (hψ i) φ = φ := by
  apply Subtype.ext
  funext y
  simp only [Submodule.coe_sum, Finset.sum_apply, mulTest_apply]
  rw [← Finset.sum_mul]
  by_cases hy : φ.val y = 0
  · simp [hy]
  · rw [hpart y hy, one_mul]

/-- Glue finitely many local distributions using smooth weights.
This is a linear distribution for every choice of the weights. -/
def finiteGluing {d : ℕ} {ι : Type*} (S : Finset ι)
    (ψ : ι → Pt d → ℝ) (hψ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (ψ i))
    (F : ι → Distrib d) : Distrib d :=
  ∑ i ∈ S, (F i).comp (mulTest (ψ i) (hψ i))

@[simp] theorem finiteGluing_apply {d : ℕ} {ι : Type*} (S : Finset ι)
    (ψ : ι → Pt d → ℝ) (hψ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (ψ i))
    (F : ι → Distrib d) (φ : testFunctions d) :
    finiteGluing S ψ hψ F φ = ∑ i ∈ S, F i (mulTest (ψ i) (hψ i) φ) := by
  simp [finiteGluing]

/-- Refining both partitions expresses the change of gluing entirely through
differences of local distributions on products of their weights. -/
theorem finiteGluing_sub_eq {d : ℕ} {ι κ : Type*}
    (S : Finset ι) (T : Finset κ)
    (ψ : ι → Pt d → ℝ) (χ : κ → Pt d → ℝ)
    (hψ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (ψ i))
    (hχ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (χ j))
    (F : ι → Distrib d) (H : κ → Distrib d) (φ : testFunctions d)
    (hpartψ : ∀ y, φ.val y ≠ 0 → ∑ i ∈ S, ψ i y = 1)
    (hpartχ : ∀ y, φ.val y ≠ 0 → ∑ j ∈ T, χ j y = 1) :
    finiteGluing S ψ hψ F φ - finiteGluing T χ hχ H φ =
      ∑ i ∈ S, ∑ j ∈ T,
        (F i - H j) (mulTest (ψ i) (hψ i) (mulTest (χ j) (hχ j) φ)) := by
  have hleft (i : ι) :
      F i (mulTest (ψ i) (hψ i) φ) =
        ∑ j ∈ T, F i (mulTest (ψ i) (hψ i) (mulTest (χ j) (hχ j) φ)) := by
    rw [← map_sum, ← map_sum, sum_mulTest T χ hχ φ hpartχ]
  have hright (j : κ) :
      H j (mulTest (χ j) (hχ j) φ) =
        ∑ i ∈ S, H j (mulTest (ψ i) (hψ i) (mulTest (χ j) (hχ j) φ)) := by
    have hp : ∀ y, (mulTest (χ j) (hχ j) φ).val y ≠ 0 →
        ∑ i ∈ S, ψ i y = 1 := by
      intro y hy
      exact hpartψ y (fun hz ↦ hy (by simp [hz]))
    rw [← map_sum, sum_mulTest S ψ hψ _ hp]
  simp only [finiteGluing_apply]
  simp_rw [hleft, hright, LinearMap.sub_apply]
  rw [Finset.sum_comm (s := T) (t := S)]
  simp only [Finset.sum_sub_distrib]

/-- Local bounds on overlapping partition pieces control the change of gluing. -/
theorem abs_finiteGluing_sub_le {d : ℕ} {ι κ : Type*}
    (S : Finset ι) (T : Finset κ)
    (ψ : ι → Pt d → ℝ) (χ : κ → Pt d → ℝ)
    (hψ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (ψ i))
    (hχ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (χ j))
    (F : ι → Distrib d) (H : κ → Distrib d) (φ : testFunctions d)
    (hpartψ : ∀ y, φ.val y ≠ 0 → ∑ i ∈ S, ψ i y = 1)
    (hpartχ : ∀ y, φ.val y ≠ 0 → ∑ j ∈ T, χ j y = 1)
    (B : ι → κ → ℝ)
    (hB : ∀ i ∈ S, ∀ j ∈ T,
      |(F i - H j) (mulTest (ψ i) (hψ i) (mulTest (χ j) (hχ j) φ))| ≤ B i j) :
    |finiteGluing S ψ hψ F φ - finiteGluing T χ hχ H φ| ≤
      ∑ i ∈ S, ∑ j ∈ T, B i j := by
  rw [finiteGluing_sub_eq S T ψ χ hψ hχ F H φ hpartψ hpartχ]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro i hi
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun j hj ↦ hB i hi j hj)

end Hairer


set_option autoImplicit false
open BigOperators

noncomputable section

namespace Hairer

/-- Only finitely many weights in a locally finite family can act nontrivially
on a compactly supported test. -/
theorem finite_support_mulTest {d : ℕ} {ι : Type*}
    (ψ : ι → Pt d → ℝ) (hψ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (ψ i))
    (hloc : LocallyFinite (fun i ↦ Function.support (ψ i)))
    (φ : testFunctions d) :
    (Function.support (fun i ↦ mulTest (ψ i) (hψ i) φ)).Finite := by
  apply (hloc.finite_nonempty_inter_compact φ.property.2).subset
  intro i hi
  have hne : mulTest (ψ i) (hψ i) φ ≠ 0 := hi
  have hex : ∃ y, ψ i y * φ.val y ≠ 0 := by
    by_contra! h
    apply hne
    apply Subtype.ext
    funext y
    exact h y
  obtain ⟨y, hy⟩ := hex
  exact ⟨y, (mul_ne_zero_iff.mp hy).1,
    subset_tsupport _ ((mul_ne_zero_iff.mp hy).2)⟩

/-- Evaluation by arbitrary local distributions retains finite support in
the partition index. No continuity of the distributions is needed. -/
theorem finite_support_localPairing {d : ℕ} {ι : Type*}
    (ψ : ι → Pt d → ℝ) (hψ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (ψ i))
    (hloc : LocallyFinite (fun i ↦ Function.support (ψ i)))
    (F : ι → Distrib d) (φ : testFunctions d) :
    (Function.support (fun i ↦ F i (mulTest (ψ i) (hψ i) φ))).Finite := by
  apply (finite_support_mulTest ψ hψ hloc φ).subset
  intro i hi
  exact fun hz ↦ hi (by simp [hz])

/-- A locally finite family of smooth weights glues local distributions into
one linear functional on all compactly supported tests. -/
def locallyFiniteGluing {d : ℕ} {ι : Type*}
    (ψ : ι → Pt d → ℝ) (hψ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (ψ i))
    (hloc : LocallyFinite (fun i ↦ Function.support (ψ i)))
    (F : ι → Distrib d) : Distrib d where
  toFun φ := ∑ᶠ i, F i (mulTest (ψ i) (hψ i) φ)
  map_add' φ χ := by
    simp only [map_add]
    exact finsum_add_distrib (finite_support_localPairing ψ hψ hloc F φ)
      (finite_support_localPairing ψ hψ hloc F χ)
  map_smul' c φ := by
    simp only [map_smul, RingHom.id_apply, smul_eq_mul]
    exact (mul_finsum _ c).symm

/-- Any finite set containing all active localizations computes the same
global gluing. Thus finite truncation is independent of the chosen set. -/
theorem locallyFiniteGluing_eq_finiteGluing {d : ℕ} {ι : Type*}
    (ψ : ι → Pt d → ℝ) (hψ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (ψ i))
    (hloc : LocallyFinite (fun i ↦ Function.support (ψ i)))
    (F : ι → Distrib d) (φ : testFunctions d) (S : Finset ι)
    (hS : Function.support (fun i ↦ mulTest (ψ i) (hψ i) φ) ⊆ S) :
    locallyFiniteGluing ψ hψ hloc F φ = finiteGluing S ψ hψ F φ := by
  rw [finiteGluing_apply]
  apply finsum_eq_sum_of_support_subset
  intro i hi
  apply hS
  exact fun hz ↦ hi (by simp [hz])

end Hairer


set_option autoImplicit false
open BigOperators

noncomputable section

namespace Hairer

/-- Integer translates of the tensor-product bump from the checked community
test decomposition. -/
def gridWeight {d : ℕ} (j : Fin d → ℤ) (y : Pt d) : ℝ :=
  HairerAux.bumpBox (fun i ↦ y i - (j i : ℝ))

theorem gridWeight_contDiff {d : ℕ} (j : Fin d → ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) (gridWeight j) :=
  HairerAux.bumpBox_contDiff.comp
    (contDiff_pi.mpr fun i ↦ (contDiff_apply ℝ ℝ i).sub contDiff_const)

/-- A nonzero grid weight has its centre strictly within one in every coordinate. -/
theorem gridWeight_ne_zero_coord {d : ℕ} {j : Fin d → ℤ} {y : Pt d}
    (h : gridWeight j y ≠ 0) (i : Fin d) :
    |y i - (j i : ℝ)| < 1 := by
  by_contra! hi
  exact h (HairerAux.bumpBox_eq_zero ⟨i, hi⟩)

/-- The integer translates of the compact bump form a locally finite family.
The argument includes dimension zero. -/
theorem gridWeight_locallyFinite {d : ℕ} :
    LocallyFinite (fun j : Fin d → ℤ ↦ Function.support (gridWeight j)) := by
  classical
  intro x
  let N : ℕ := ⌈‖x‖ + 2⌉₊
  let S : Finset (Fin d → ℤ) :=
    Fintype.piFinset (fun _ ↦ Finset.Icc (-(N : ℤ)) (N : ℤ))
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x zero_lt_one, S.finite_toSet.subset ?_⟩
  rintro j ⟨y, hy, hyx⟩
  apply Fintype.mem_piFinset.mpr
  intro i
  have hyx' : ‖y - x‖ < 1 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hyx
  have hyNorm : ‖y‖ < ‖x‖ + 1 := by
    have htri := norm_add_le (y - x) x
    rw [sub_add_cancel] at htri
    linarith
  have hcoord := gridWeight_ne_zero_coord hy i
  have hiNorm : |y i| ≤ ‖y‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm y i
  have hj : |(j i : ℝ)| ≤ (N : ℝ) := by
    have htri := abs_add_le ((j i : ℝ) - y i) (y i)
    rw [sub_add_cancel, abs_sub_comm] at htri
    have hN : ‖x‖ + 2 ≤ (N : ℝ) := Nat.le_ceil _
    linarith
  rw [Finset.mem_Icc]
  have hj' := abs_le.mp hj
  constructor
  · exact_mod_cast hj'.1
  · exact_mod_cast hj'.2

/-- Coordinate rescaling of the integer-grid weights. -/
def scaledGridWeight {d : ℕ} (a : Fin d → ℝ) (j : Fin d → ℤ) (y : Pt d) : ℝ :=
  gridWeight j (fun i ↦ y i / a i)

theorem scaledGridWeight_contDiff {d : ℕ} (a : Fin d → ℝ) (j : Fin d → ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) (scaledGridWeight a j) :=
  (gridWeight_contDiff j).comp
    (contDiff_pi.mpr fun i ↦ (contDiff_apply ℝ ℝ i).div_const (a i))

theorem scaledGridWeight_locallyFinite {d : ℕ} (a : Fin d → ℝ) :
    LocallyFinite (fun j : Fin d → ℤ ↦ Function.support (scaledGridWeight a j)) :=
  (gridWeight_locallyFinite (d := d)).preimage_continuous
    (g := fun y : Pt d ↦ fun i ↦ y i / a i)
    ((contDiff_pi.mpr fun i ↦
      (contDiff_apply ℝ ℝ i).div_const (a i)) :
      ContDiff ℝ (⊤ : ℕ∞) (fun y : Pt d ↦ fun i ↦ y i / a i)).continuous

/-- A scaled weight is supported within one grid spacing of its centre. -/
theorem scaledGridWeight_ne_zero_coord {d : ℕ} {a : Fin d → ℝ}
    (ha : ∀ i, 0 < a i) {j : Fin d → ℤ} {y : Pt d}
    (h : scaledGridWeight a j y ≠ 0) (i : Fin d) :
    |y i - a i * (j i : ℝ)| < a i := by
  have hi := gridWeight_ne_zero_coord h i
  have heq : y i - a i * (j i : ℝ) = a i * (y i / a i - (j i : ℝ)) := by
    field_simp [(ha i).ne']
  rw [heq, abs_mul, abs_of_pos (ha i)]
  simpa only [mul_one] using mul_lt_mul_of_pos_left hi (ha i)

/-- Centres of overlapping grid weights are separated by less than two
grid spacings in each coordinate. -/
theorem scaledGridWeight_overlap_coord {d : ℕ} {a : Fin d → ℝ}
    (ha : ∀ i, 0 < a i) {j k : Fin d → ℤ} {y : Pt d}
    (hj : scaledGridWeight a j y ≠ 0) (hk : scaledGridWeight a k y ≠ 0)
    (i : Fin d) :
    |a i * (j i : ℝ) - a i * (k i : ℝ)| < 2 * a i := by
  have hj' := scaledGridWeight_ne_zero_coord ha hj i
  have hk' := scaledGridWeight_ne_zero_coord ha hk i
  have htri := abs_add_le (a i * (j i : ℝ) - y i) (y i - a i * (k i : ℝ))
  rw [sub_add_sub_cancel, abs_sub_comm (a i * (j i : ℝ)) (y i)] at htri
  linarith

/-- The grid approximation is a single linear distribution on all tests. -/
def gridGluing {d : ℕ} (a : Fin d → ℝ) (F : Pt d → Distrib d) : Distrib d :=
  locallyFiniteGluing (scaledGridWeight a) (scaledGridWeight_contDiff a)
    (scaledGridWeight_locallyFinite a) (fun j ↦ F (fun i ↦ a i * (j i : ℝ)))

end Hairer


set_option autoImplicit false
open BigOperators

noncomputable section

namespace Hairer

/-- The one-dimensional telescoping identity, indexed by integer centres. -/
theorem chi_sum_Icc (t : ℝ) (N : ℕ) (ht : |t| ≤ (N : ℝ)) :
    ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), HairerAux.chi (t - (j : ℝ)) = 1 := by
  have heq :
      ∑ n ∈ Finset.range (2 * N + 1),
        HairerAux.chi (t - ((n : ℝ) - (N : ℝ))) =
      ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), HairerAux.chi (t - (j : ℝ)) := by
    apply Finset.sum_bij (fun (n : ℕ) _ ↦ (n : ℤ) - (N : ℤ))
    · intro n hn
      simp only [Finset.mem_range] at hn
      simp only [Finset.mem_Icc]
      omega
    · intro n hn m hm hnm
      omega
    · intro j hj
      simp only [Finset.mem_Icc] at hj
      refine ⟨(j + (N : ℤ)).toNat, ?_, ?_⟩
      · simp only [Finset.mem_range]
        omega
      · omega
    · intro n hn
      simp only [Int.cast_sub, Int.cast_natCast]
  rw [← heq]
  exact HairerAux.chi_sum_eq_one t N ht

/-- On a coordinate box, the finite tensor-product grid is a partition of unity. -/
theorem gridWeight_sum_box {d : ℕ} (y : Pt d) (N : ℕ)
    (hy : ∀ i, |y i| ≤ (N : ℝ)) :
    ∑ j ∈ Fintype.piFinset (fun _ : Fin d ↦ Finset.Icc (-(N : ℤ)) (N : ℤ)),
      gridWeight j y = 1 := by
  simp only [gridWeight, HairerAux.bumpBox]
  rw [← Finset.prod_univ_sum
    (fun _ : Fin d ↦ Finset.Icc (-(N : ℤ)) (N : ℤ))
    (fun i (j : ℤ) ↦ HairerAux.chi (y i - (j : ℝ)))]
  exact Finset.prod_eq_one (fun i _ ↦ chi_sum_Icc (y i) N (hy i))

/-- Every nonzero weight at a point in the coordinate box has its centre in
the corresponding finite integer box. -/
theorem gridWeight_support_subset_box {d : ℕ} (y : Pt d) (N : ℕ)
    (hy : ∀ i, |y i| ≤ (N : ℝ)) :
    Function.support (fun j : Fin d → ℤ ↦ gridWeight j y) ⊆
      Fintype.piFinset (fun _ : Fin d ↦ Finset.Icc (-(N : ℤ)) (N : ℤ)) := by
  intro j hj
  apply Fintype.mem_piFinset.mpr
  intro i
  have hdist := abs_lt.mp (gridWeight_ne_zero_coord hj i)
  have hyi := abs_le.mp (hy i)
  have hlow : (-(N : ℤ) - 1) < j i := by
    have h : -(N : ℝ) - 1 < (j i : ℝ) := by linarith
    exact_mod_cast h
  have hupp : j i < (N : ℤ) + 1 := by
    have h : (j i : ℝ) < (N : ℝ) + 1 := by linarith
    exact_mod_cast h
  simp only [Finset.mem_Icc]
  omega

/-- All integer translates of the tensor-product bump sum to one. -/
theorem gridWeight_finsum {d : ℕ} (y : Pt d) :
    ∑ᶠ j : Fin d → ℤ, gridWeight j y = 1 := by
  let N : ℕ := ⌈‖y‖⌉₊
  have hy : ∀ i, |y i| ≤ (N : ℝ) := by
    intro i
    exact (show |y i| ≤ ‖y‖ by simpa using norm_le_pi_norm y i).trans (Nat.le_ceil _)
  rw [finsum_eq_sum_of_support_subset _ (gridWeight_support_subset_box y N hy)]
  exact gridWeight_sum_box y N hy

/-- Coordinate rescaling preserves the partition identity. -/
theorem scaledGridWeight_finsum {d : ℕ} (a : Fin d → ℝ) (y : Pt d) :
    ∑ᶠ j : Fin d → ℤ, scaledGridWeight a j y = 1 :=
  gridWeight_finsum (fun i ↦ y i / a i)

end Hairer


set_option autoImplicit false
open BigOperators

noncomputable section

namespace Hairer

/-- A global partition identity restricts to any finite set containing the
localizations active on a given test. -/
theorem partition_sum_on_test {d : ℕ} {ι : Type*}
    (ψ : ι → Pt d → ℝ) (hψ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (ψ i))
    (hpart : ∀ y, ∑ᶠ i, ψ i y = 1)
    (φ : testFunctions d) (S : Finset ι)
    (hS : Function.support (fun i ↦ mulTest (ψ i) (hψ i) φ) ⊆ S) :
    ∀ y, φ.val y ≠ 0 → ∑ i ∈ S, ψ i y = 1 := by
  intro y hy
  rw [← hpart y]
  symm
  apply finsum_eq_sum_of_support_subset
  intro i hi
  apply hS
  intro hz
  have he := congrArg (fun χ : testFunctions d ↦ χ.val y) hz
  change ψ i y * φ.val y = 0 at he
  exact (mul_ne_zero hi hy) he

/-- Gluing the same distribution on every patch recovers that distribution. -/
theorem locallyFiniteGluing_const {d : ℕ} {ι : Type*}
    (ψ : ι → Pt d → ℝ) (hψ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (ψ i))
    (hloc : LocallyFinite (fun i ↦ Function.support (ψ i)))
    (hpart : ∀ y, ∑ᶠ i, ψ i y = 1) (ξ : Distrib d) :
    locallyFiniteGluing ψ hψ hloc (fun _ ↦ ξ) = ξ := by
  classical
  apply LinearMap.ext
  intro φ
  let S := (finite_support_mulTest ψ hψ hloc φ).toFinset
  have hS : Function.support (fun i ↦ mulTest (ψ i) (hψ i) φ) ⊆ S :=
    fun _ hi ↦ (finite_support_mulTest ψ hψ hloc φ).mem_toFinset.mpr hi
  rw [locallyFiniteGluing_eq_finiteGluing ψ hψ hloc (fun _ ↦ ξ) φ S hS,
    finiteGluing_apply, ← map_sum,
    sum_mulTest S ψ hψ φ (partition_sum_on_test ψ hψ hpart φ S hS)]

/-- In particular, every grid approximation is exact on constant model germs. -/
theorem gridGluing_const {d : ℕ} (a : Fin d → ℝ) (ξ : Distrib d) :
    gridGluing a (fun _ ↦ ξ) = ξ :=
  locallyFiniteGluing_const (scaledGridWeight a) (scaledGridWeight_contDiff a)
    (scaledGridWeight_locallyFinite a) (scaledGridWeight_finsum a) ξ

/-- The global gluing comparison reduces to the same finite double sum for
any finite sets containing the active localizations of both partitions. -/
theorem locallyFiniteGluing_sub_eq {d : ℕ} {ι κ : Type*}
    (ψ : ι → Pt d → ℝ) (χ : κ → Pt d → ℝ)
    (hψ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (ψ i))
    (hχ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (χ j))
    (hlocψ : LocallyFinite (fun i ↦ Function.support (ψ i)))
    (hlocχ : LocallyFinite (fun j ↦ Function.support (χ j)))
    (hpartψ : ∀ y, ∑ᶠ i, ψ i y = 1)
    (hpartχ : ∀ y, ∑ᶠ j, χ j y = 1)
    (F : ι → Distrib d) (H : κ → Distrib d) (φ : testFunctions d)
    (S : Finset ι) (T : Finset κ)
    (hS : Function.support (fun i ↦ mulTest (ψ i) (hψ i) φ) ⊆ S)
    (hT : Function.support (fun j ↦ mulTest (χ j) (hχ j) φ) ⊆ T) :
    locallyFiniteGluing ψ hψ hlocψ F φ - locallyFiniteGluing χ hχ hlocχ H φ =
      ∑ i ∈ S, ∑ j ∈ T,
        (F i - H j) (mulTest (ψ i) (hψ i) (mulTest (χ j) (hχ j) φ)) := by
  rw [locallyFiniteGluing_eq_finiteGluing ψ hψ hlocψ F φ S hS,
    locallyFiniteGluing_eq_finiteGluing χ hχ hlocχ H φ T hT]
  exact finiteGluing_sub_eq S T ψ χ hψ hχ F H φ
    (partition_sum_on_test ψ hψ hpartψ φ S hS)
    (partition_sum_on_test χ hχ hpartχ φ T hT)

end Hairer


set_option autoImplicit false
open BigOperators Filter
open scoped Topology

noncomputable section

namespace Hairer

/-- The finite increment series telescopes to the current approximation. -/
theorem distrib_increment_sum {d : ℕ} (R : ℕ → Distrib d)
    (φ : testFunctions d) (n : ℕ) :
    R 0 φ + ∑ k ∈ Finset.range n, (R (k + 1) - R k) φ = R n φ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    simp only [LinearMap.sub_apply]
    simp only [LinearMap.sub_apply] at ih
    linarith

/-- Summable increments of linear approximations define a distribution.
Summability is required separately on every test function. -/
def distribLimit {d : ℕ} (R : ℕ → Distrib d)
    (hR : ∀ φ : testFunctions d, Summable (fun n ↦ (R (n + 1) - R n) φ)) :
    Distrib d where
  toFun φ := R 0 φ + ∑' n, (R (n + 1) - R n) φ
  map_add' φ ψ := by
    simp only [map_add]
    rw [(hR φ).tsum_add (hR ψ)]
    ring
  map_smul' c φ := by
    simp only [map_smul, smul_eq_mul, RingHom.id_apply]
    rw [tsum_mul_left]
    ring

/-- The distribution defined by the increment series is the pointwise limit
of the original approximations. -/
theorem tendsto_distribLimit {d : ℕ} (R : ℕ → Distrib d)
    (hR : ∀ φ : testFunctions d, Summable (fun n ↦ (R (n + 1) - R n) φ))
    (φ : testFunctions d) :
    Tendsto (fun n ↦ R n φ) atTop (𝓝 (distribLimit R hR φ)) := by
  have h := (tendsto_const_nhds (x := R 0 φ)).add (hR φ).hasSum.tendsto_sum_nat
  simpa only [distrib_increment_sum, distribLimit, LinearMap.coe_mk, AddHom.coe_mk] using h

/-- The error after any approximation is precisely the remaining increment series. -/
theorem distribLimit_sub_eq_tsum {d : ℕ} (R : ℕ → Distrib d)
    (hR : ∀ φ : testFunctions d, Summable (fun n ↦ (R (n + 1) - R n) φ))
    (φ : testFunctions d) (n : ℕ) :
    distribLimit R hR φ - R n φ = ∑' k, (R (k + n + 1) - R (k + n)) φ := by
  have hsum := (hR φ).sum_add_tsum_nat_add n
  have htel := distrib_increment_sum R φ n
  change R 0 φ + (∑' k, (R (k + 1) - R k) φ) - R n φ = _
  linarith

/-- A summable majorant for the remaining increments gives a quantitative
error bound for the limiting distribution. -/
theorem abs_distribLimit_sub_le {d : ℕ} (R : ℕ → Distrib d)
    (hR : ∀ φ : testFunctions d, Summable (fun n ↦ (R (n + 1) - R n) φ))
    (φ : testFunctions d) (n : ℕ) {b : ℕ → ℝ} {B : ℝ}
    (hb : HasSum b B)
    (hbound : ∀ k, |(R (k + n + 1) - R (k + n)) φ| ≤ b k) :
    |distribLimit R hR φ - R n φ| ≤ B := by
  rw [distribLimit_sub_eq_tsum]
  simpa only [Real.norm_eq_abs] using tsum_of_norm_bounded hb
    (fun k ↦ (show ‖(R (k + n + 1) - R (k + n)) φ‖ ≤ b k by
      simpa only [Real.norm_eq_abs] using hbound k))

end Hairer


set_option autoImplicit false
open BigOperators Filter
open scoped Topology
noncomputable section
namespace Hairer

/-- A grid cell acting on a test supported in a fixed box has its centre in a
slightly larger box, uniformly for grid spacings at most one. -/
theorem active_grid_centre_mem {d : ℕ} (a : Fin d → ℝ)
    (ha : ∀ i, 0 < a i) (ha1 : ∀ i, a i ≤ 1)
    (φ : testFunctions d) {R : ℝ} (hR : 0 ≤ R)
    (hφR : ∀ y, φ.val y ≠ 0 → ∀ i, |y i| ≤ R)
    {j : Fin d → ℤ}
    (hj : mulTest (scaledGridWeight a j) (scaledGridWeight_contDiff a j) φ ≠ 0) :
    (fun i ↦ a i * (j i : ℝ)) ∈ Metric.closedBall (0 : Pt d) (R + 1) := by
  have hex : ∃ y, scaledGridWeight a j y * φ.val y ≠ 0 := by
    by_contra! h
    apply hj
    apply Subtype.ext
    funext y
    exact h y
  obtain ⟨y, hy⟩ := hex
  have hw := mul_ne_zero_iff.mp hy
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by linarith : 0 ≤ R + 1)).mpr
  intro i
  have hc := scaledGridWeight_ne_zero_coord ha hw.1 i
  have ht := abs_add_le (a i * (j i : ℝ) - y i) (y i)
  rw [sub_add_cancel, abs_sub_comm (a i * (j i : ℝ))] at ht
  rw [Real.norm_eq_abs]
  linarith [hφR y hw.2 i, ha1 i]

/-- The overlap estimate controls the difference of the actual global grid
approximations on each fixed test. -/
theorem model_grid_increment_bound
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s) {γ : ℝ}
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f)
    (φ : testFunctions d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
      |gridGluing (fun i ↦ δ ^ s i) (fun x ↦ Pi x (f x)) φ -
        gridGluing (fun i ↦ (2 * δ) ^ s i) (fun x ↦ Pi x (f x)) φ| ≤ C * δ ^ γ := by
  classical
  obtain ⟨R, hRpos, hR⟩ := φ.property.2.isCompact.isBounded.subset_closedBall_lt 0 0
  have hφR : ∀ y, φ.val y ≠ 0 → ∀ i, |y i| ≤ R := by
    intro y hy i
    have hyR : ‖y‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hR (subset_tsupport φ.val hy)
    exact (show |y i| ≤ ‖y‖ by simpa using norm_le_pi_norm y i).trans hyR
  let K := Metric.closedBall (0 : Pt d) (R + 1)
  obtain ⟨C, hC, hbound⟩ := model_germ_grid_sum_bound hs hT hmod hf K
    (isCompact_closedBall _ _) φ.val φ.property
  refine ⟨C, hC, ?_⟩
  intro δ hδ hδsmall
  let a := fun i ↦ δ ^ s i
  let c := fun i ↦ (2 * δ) ^ s i
  let ψ := scaledGridWeight a
  let χ := scaledGridWeight c
  let hψ := scaledGridWeight_contDiff a
  let hχ := scaledGridWeight_contDiff c
  let finS := finite_support_mulTest ψ hψ (scaledGridWeight_locallyFinite a) φ
  let finT := finite_support_mulTest χ hχ (scaledGridWeight_locallyFinite c) φ
  let S := finS.toFinset
  let T := finT.toFinset
  have hS : Function.support (fun j ↦ mulTest (ψ j) (hψ j) φ) ⊆ S :=
    fun _ hj ↦ finS.mem_toFinset.mpr hj
  have hT' : Function.support (fun j ↦ mulTest (χ j) (hχ j) φ) ⊆ T :=
    fun _ hj ↦ finT.mem_toFinset.mpr hj
  have hcentS : ∀ j ∈ S, gridCentre s δ j ∈ K := by
    intro j hj
    exact active_grid_centre_mem a (fun i ↦ pow_pos hδ _) (fun i ↦
      pow_le_one₀ hδ.le (by linarith)) φ hRpos.le hφR (finS.mem_toFinset.mp hj)
  have hcentT : ∀ k ∈ T, gridCentre s (2 * δ) k ∈ K := by
    intro k hk
    exact active_grid_centre_mem c (fun i ↦ pow_pos (by linarith) _) (fun i ↦
      pow_le_one₀ (by linarith) (by linarith)) φ hRpos.le hφR (finT.mem_toFinset.mp hk)
  have hid := locallyFiniteGluing_sub_eq ψ χ hψ hχ
    (scaledGridWeight_locallyFinite a) (scaledGridWeight_locallyFinite c)
    (scaledGridWeight_finsum a) (scaledGridWeight_finsum c)
    (fun j ↦ Pi (gridCentre s δ j) (f (gridCentre s δ j)))
    (fun k ↦ Pi (gridCentre s (2 * δ) k) (f (gridCentre s (2 * δ) k))) φ S T hS hT'
  change |locallyFiniteGluing ψ hψ _
    (fun j ↦ Pi (gridCentre s δ j) (f (gridCentre s δ j))) φ -
    locallyFiniteGluing χ hχ _
    (fun k ↦ Pi (gridCentre s (2 * δ) k) (f (gridCentre s (2 * δ) k))) φ| ≤ _
  rw [hid]
  have hp (j k : Fin d → ℤ) :
      (Pi (gridCentre s δ j) (f (gridCentre s δ j)) -
        Pi (gridCentre s (2 * δ) k) (f (gridCentre s (2 * δ) k)))
        (mulTest (ψ j) (hψ j) (mulTest (χ k) (hχ k) φ)) =
      (Pi (gridCentre s δ j) (f (gridCentre s δ j)) -
        Pi (gridCentre s (2 * δ) k) (f (gridCentre s (2 * δ) k))).eval
        (fun y ↦ gridWeightAt s δ j y * gridWeightAt s (2 * δ) k y * φ.val y) := by
    let η := mulTest (ψ j) (hψ j) (mulTest (χ k) (hχ k) φ)
    have heq : (fun y ↦ gridWeightAt s δ j y * gridWeightAt s (2 * δ) k y * φ.val y) =
        η.val := by
      funext y
      change gridWeightAt s δ j y * gridWeightAt s (2 * δ) k y * φ.val y =
        gridWeightAt s δ j y * (gridWeightAt s (2 * δ) k y * φ.val y)
      exact mul_assoc _ _ _
    rw [heq, Distrib.eval, dif_pos η.property]
  simp_rw [hp]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_sum (fun j _ ↦ Finset.abs_sum_le_sum_abs _ _)).trans
      (hbound δ hδ hδsmall S T hcentS hcentT))

/-- Grid approximations start at scale one quarter and halve at each step. -/
def dyadicGridApprox {d : ℕ} (s : Fin d → ℕ) (F : Pt d → Distrib d) (n : ℕ) :
    Distrib d := gridGluing (fun i ↦ ((1 / 2 : ℝ) ^ (n + 2)) ^ s i) F

theorem dyadic_grid_increment_bound
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s) {γ : ℝ}
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f)
    (φ : testFunctions d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      |(dyadicGridApprox s (fun x ↦ Pi x (f x)) (n + 1) -
        dyadicGridApprox s (fun x ↦ Pi x (f x)) n) φ| ≤
        C * ((1 / 2 : ℝ) ^ γ) ^ (n + 3) := by
  obtain ⟨C, hC, hb⟩ := model_grid_increment_bound hs hT hmod hf φ
  refine ⟨C, hC, ?_⟩
  intro n
  have hδ : 0 < (1 / 2 : ℝ) ^ (n + 3) := pow_pos (by norm_num) _
  have hδsmall : (1 / 2 : ℝ) ^ (n + 3) ≤ 1 / 4 := by
    rw [show n + 3 = (n + 1) + 2 by omega, pow_add]
    have h := pow_le_one₀ (n := n + 1) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1)
    norm_num
    linarith
  have htwice : 2 * (1 / 2 : ℝ) ^ (n + 3) = (1 / 2 : ℝ) ^ (n + 2) := by
    rw [show n + 3 = (n + 2) + 1 by omega, pow_succ]
    ring
  have h := hb ((1 / 2 : ℝ) ^ (n + 3)) hδ hδsmall
  rw [htwice, ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 1 / 2)] at h
  simpa only [dyadicGridApprox, LinearMap.sub_apply, Nat.add_assoc] using h

/-- For positive modelled regularity, the grid approximations converge to a
single linear distribution, with a geometric error bound on every test. -/
theorem exists_dyadic_grid_limit
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s) {γ : ℝ} (hγ : 0 < γ)
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f) :
    ∃ R : Distrib d,
      (∀ φ : testFunctions d, Tendsto
        (fun n ↦ dyadicGridApprox s (fun x ↦ Pi x (f x)) n φ) atTop (𝓝 (R φ))) ∧
      ∀ φ : testFunctions d, ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
        |R φ - dyadicGridApprox s (fun x ↦ Pi x (f x)) n φ| ≤
          C * ((1 / 2 : ℝ) ^ γ) ^ n := by
  let q : ℝ := (1 / 2 : ℝ) ^ γ
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hγ
  have hgeom := hasSum_geometric_of_norm_lt_one
    (show ‖q‖ < 1 by rwa [Real.norm_eq_abs, abs_of_nonneg hq0])
  let Rn := dyadicGridApprox s (fun x ↦ Pi x (f x))
  have hinc : ∀ φ : testFunctions d, ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      |(Rn (n + 1) - Rn n) φ| ≤ C * q ^ (n + 3) :=
    dyadic_grid_increment_bound hs hT hmod hf
  have hsum : ∀ φ : testFunctions d, Summable (fun n ↦ (Rn (n + 1) - Rn n) φ) := by
    intro φ
    obtain ⟨C, _, hb⟩ := hinc φ
    apply ((summable_nat_add_iff 3).mpr (hgeom.summable.mul_left C)).of_norm_bounded
    intro n
    simpa only [Real.norm_eq_abs] using hb n
  refine ⟨distribLimit Rn hsum, tendsto_distribLimit Rn hsum, ?_⟩
  intro φ
  obtain ⟨C, hC, hb⟩ := hinc φ
  refine ⟨C * q ^ 3 * (1 - q)⁻¹, by positivity, ?_⟩
  intro n
  have htail : |distribLimit Rn hsum φ - Rn n φ| ≤
      (C * q ^ (n + 3)) * (1 - q)⁻¹ := by
    apply abs_distribLimit_sub_le Rn hsum φ n (hgeom.mul_left (C * q ^ (n + 3)))
    intro k
    calc
      _ ≤ C * q ^ ((k + n) + 3) := hb (k + n)
      _ = (C * q ^ (n + 3)) * q ^ k := by
        rw [show k + n + 3 = (n + 3) + k by omega, pow_add]
        ring
  calc
    _ ≤ (C * q ^ (n + 3)) * (1 - q)⁻¹ := htail
    _ = _ := by rw [pow_add]; ring

/-- The bundled grid distribution agrees with the explicit finite-support sum
of localized pairings. -/
theorem gridGluing_apply_finsum {d : ℕ} (a : Fin d → ℝ) (F : Pt d → Distrib d)
    (φ : testFunctions d) :
    gridGluing a F φ = ∑ᶠ j : Fin d → ℤ,
      (F (fun i ↦ a i * (j i : ℝ))).eval (fun y ↦ scaledGridWeight a j y * φ.val y) := by
  change (∑ᶠ j : Fin d → ℤ,
    F (fun i ↦ a i * (j i : ℝ))
      (mulTest (scaledGridWeight a j) (scaledGridWeight_contDiff a j) φ)) = _
  apply finsum_congr
  intro j
  let η := mulTest (scaledGridWeight a j) (scaledGridWeight_contDiff a j) φ
  change F (fun i ↦ a i * (j i : ℝ)) η =
    (F (fun i ↦ a i * (j i : ℝ))).eval η.val
  rw [Distrib.eval, dif_pos η.property]

end Hairer

open BigOperators Filter Hairer
open scoped Topology
noncomputable section
theorem Hairer.dyadic_grid_limit_exists
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s) {γ : ℝ} (hγ : 0 < γ)
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f) :
    let W : Pt d → ℝ := fun z ↦
      ∏ i, (Real.smoothTransition (z i + 1) - Real.smoothTransition (z i))
    let δ : ℕ → ℝ := fun n ↦ (1 / 2 : ℝ) ^ (n + 2)
    let X := fun (n : ℕ) (j : Fin d → ℤ) (i : Fin d) ↦ δ n ^ s i * (j i : ℝ)
    let Rn := fun (n : ℕ) (φ : testFunctions d) ↦ ∑ᶠ j : Fin d → ℤ,
      (Pi (X n j) (f (X n j))).eval
        (fun y ↦ W (fun i ↦ y i / δ n ^ s i - (j i : ℝ)) * φ.val y)
    ∃ R : Distrib d,
      (∀ φ : testFunctions d, Tendsto
        (fun n ↦ Rn n φ) atTop (𝓝 (R φ))) ∧
      ∀ φ : testFunctions d, ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
        |R φ - Rn n φ| ≤
          C * ((1 / 2 : ℝ) ^ γ) ^ n := by
  simpa only [dyadicGridApprox, gridGluing_apply_finsum, scaledGridWeight,
    gridWeight, HairerAux.bumpBox, HairerAux.chi] using
    exists_dyadic_grid_limit hs hγ hT hmod hf




set_option autoImplicit false
open BigOperators HairerAux
noncomputable section
namespace Hairer

/-- One normalization constant works for every smooth function with unit
bounds on derivatives through order `r`, and every contractive overlap. -/
theorem uniform_overlap_test_normalization {d : ℕ} (s : Fin d → ℕ) (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ φ : Pt d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ →
      (∀ m ≤ r, ∀ y, ‖iteratedFDeriv ℝ m φ y‖ ≤ 1) →
      ∀ (x u : Pt d) (a b : Fin d → ℝ),
      (∀ i, |a i| ≤ 1) → (∀ i, |b i| ≤ 1) →
      IsTestBall s r (fun z ↦
        (φ (x + scaleCLM a z) * bumpBox (u + scaleCLM b z) * bumpBox z) / C) := by
  obtain ⟨G, hG, hgB⟩ := exists_deriv_bound
    (bumpBox_contDiff (d := d)) bumpBox_hasCompactSupport r
  let B : ℝ := 2 ^ r * (2 ^ r * 1 * G) * G
  refine ⟨B + 1, by dsimp [B]; positivity, ?_⟩
  intro φ hφ hfB x u a b ha hb
  have hfa : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ φ (x + scaleCLM a z)) :=
    (hφ.comp (contDiff_const.add contDiff_id)).comp (scaleCLM a).contDiff
  have hgb : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ bumpBox (u + scaleCLM b z)) :=
    (bumpBox_contDiff.comp (contDiff_const.add contDiff_id)).comp (scaleCLM b).contDiff
  apply isTestBall_div_const s ((hfa.mul hgb).mul bumpBox_contDiff)
  · intro z hz
    simp [bumpBox_eq_zero hz]
  · dsimp [B]
    positivity
  · intro m hm z
    have hab : ∀ n ≤ r, ∀ w,
        ‖iteratedFDeriv ℝ n (fun v ↦ φ (x + scaleCLM a v) *
          bumpBox (u + scaleCLM b v)) w‖ ≤ 2 ^ r * 1 * G := by
      intro n hn w
      exact mul_deriv_bound hfa hgb (by norm_num) hG
        (fun q hq v ↦ comp_scale_deriv_bound hφ hfB x ha hq v)
        (fun q hq v ↦ comp_scale_deriv_bound bumpBox_contDiff hgB u hb hq v) hn w
    exact (mul_deriv_bound (hfa.mul hgb) bumpBox_contDiff (by positivity) hG
      hab hgB hm z).trans (by dsimp [B]; linarith)

/-- A grid overlap against any normalized test at scale `ρ ≥ δ` can be
normalized at the fine scale with the exact relative-volume coefficient. -/
theorem grid_overlap_scaled_test_normalization {d : ℕ} (s : Fin d → ℕ) (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ δ : ℝ), 0 < δ → δ ≤ ρ →
      ∀ (c : Fin d → ℝ), (∀ i, δ ^ s i ≤ c i) →
      ∀ (x : Pt d) (j k : Fin d → ℤ) (η : Pt d → ℝ), IsTestBall s r η →
      ∃ θ : Pt d → ℝ, IsTestBall s r θ ∧ ∀ y,
        gridWeightAt s δ j y *
          gridBump (fun i ↦ y i / c i - (k i : ℝ)) * scaledTest s ρ x η y =
        (C * δ ^ (scaleDim s : ℝ) * ρ ^ (-(scaleDim s : ℝ))) *
          scaledTest s δ (gridCentre s δ j) θ y := by
  obtain ⟨C, hC, hnorm⟩ := uniform_overlap_test_normalization s r
  refine ⟨C, hC, ?_⟩
  intro ρ δ hδ hδρ c hc x j k η hη
  have hρ : 0 < ρ := hδ.trans_le hδρ
  let a : Fin d → ℝ := fun i ↦ δ ^ s i
  let z0 := gridCentre s δ j
  let v : Pt d := fun i ↦ (z0 i - x i) / ρ ^ s i
  let b : Fin d → ℝ := fun i ↦ a i / ρ ^ s i
  let u : Pt d := fun i ↦ z0 i / c i - (k i : ℝ)
  let e : Fin d → ℝ := fun i ↦ a i / c i
  have ha0 (i : Fin d) : 0 < a i := pow_pos hδ _
  have hc0 (i : Fin d) : 0 < c i := (ha0 i).trans_le (hc i)
  have hb (i : Fin d) : |b i| ≤ 1 := by
    rw [abs_of_pos (div_pos (ha0 i) (pow_pos hρ _))]
    exact (div_le_one (pow_pos hρ _)).mpr (pow_le_pow_left₀ hδ.le hδρ _)
  have he (i : Fin d) : |e i| ≤ 1 := by
    rw [abs_of_pos (div_pos (ha0 i) (hc0 i))]
    exact (div_le_one (hc0 i)).mpr (hc i)
  let θ : Pt d → ℝ := fun z ↦
    (η (v + scaleCLM b z) * bumpBox (u + scaleCLM e z) * bumpBox z) / C
  refine ⟨θ, hnorm η hη.smooth hη.derivBound v u b e hb he, ?_⟩
  intro y
  let z : Pt d := fun i ↦ (y i - z0 i) / δ ^ s i
  have hfine : z = fun i ↦ y i / δ ^ s i - (j i : ℝ) := by
    funext i
    change (y i - δ ^ s i * (j i : ℝ)) / δ ^ s i = _
    field_simp
  have htest : v + scaleCLM b z = fun i ↦ (y i - x i) / ρ ^ s i := by
    funext i
    change (z0 i - x i) / ρ ^ s i +
      (a i / ρ ^ s i) * ((y i - z0 i) / a i) = _
    field_simp [(ha0 i).ne', (pow_pos hρ (s i)).ne']
    ring
  have hcoarse : u + scaleCLM e z = fun i ↦ y i / c i - (k i : ℝ) := by
    funext i
    change z0 i / c i - (k i : ℝ) +
      (a i / c i) * ((y i - z0 i) / a i) = _
    field_simp [(ha0 i).ne', (hc0 i).ne']
    ring
  have hvolume : δ ^ (scaleDim s : ℝ) * δ ^ (-(scaleDim s : ℝ)) = 1 := by
    rw [← Real.rpow_add hδ, add_neg_cancel, Real.rpow_zero]
  change _ = (C * δ ^ (scaleDim s : ℝ) * ρ ^ (-(scaleDim s : ℝ))) *
    (δ ^ (-(scaleDim s : ℝ)) *
      ((η (v + scaleCLM b z) * bumpBox (u + scaleCLM e z) * bumpBox z) / C))
  rw [htest, hcoarse, hfine]
  change _ * _ * (ρ ^ (-(scaleDim s : ℝ)) * _) = _
  calc
    _ = (δ ^ (scaleDim s : ℝ) * δ ^ (-(scaleDim s : ℝ))) *
      (ρ ^ (-(scaleDim s : ℝ)) *
        (η (fun i ↦ (y i - x i) / ρ ^ s i) *
          bumpBox (fun i ↦ y i / c i - (k i : ℝ)) *
          bumpBox (fun i ↦ y i / δ ^ s i - (j i : ℝ)))) := by
      rw [hvolume]
      simp only [gridWeightAt, gridBump, bumpBox, chi]
      ring
    _ = _ := by field_simp [hC.ne']

/-- Translating and rescaling the active-cell count gives a bound proportional
to the volume of the test support, uniformly in its centre. -/
theorem grid_active_relative_volume_bound {d : ℕ} (s : Fin d → ℕ)
    {δ ρ : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ) (x : Pt d)
    (S : Finset (Fin d → ℤ))
    (hS : ∀ j ∈ S, ∃ y : Pt d, (∀ i, |y i - x i| ≤ ρ ^ s i) ∧
      gridWeightAt s δ j y ≠ 0) :
    (S.card : ℝ) * δ ^ (scaleDim s : ℝ) ≤ (9 : ℝ) ^ d * ρ ^ (scaleDim s : ℝ) := by
  classical
  have hρ : 0 < ρ := hδ.trans_le hδρ
  let m : Fin d → ℤ := fun i ↦ ⌊x i / δ ^ s i⌋
  let shift := fun j : Fin d → ℤ ↦ fun i ↦ j i - m i
  let T := S.image shift
  have hcard : T.card = S.card := Finset.card_image_of_injective _ (by
    intro j k hjk
    funext i
    have hi := congrFun hjk i
    change j i - m i = k i - m i at hi
    omega)
  have hT : ∀ j ∈ T, ∃ y : Pt d, (∀ i, |y i| ≤ 2) ∧
      gridWeightAt s (δ / ρ) j y ≠ 0 := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨y, hy, hw⟩ := hS k hk
    let z : Pt d := fun i ↦ (y i - δ ^ s i * (m i : ℝ)) / ρ ^ s i
    have ha (i : Fin d) : 0 < δ ^ s i := pow_pos hδ _
    have hb (i : Fin d) : 0 < ρ ^ s i := pow_pos hρ _
    have hrem (i : Fin d) : |x i - δ ^ s i * (m i : ℝ)| ≤ δ ^ s i := by
      have hlo := Int.floor_le (x i / δ ^ s i)
      have hhi := Int.lt_floor_add_one (x i / δ ^ s i)
      change (m i : ℝ) ≤ x i / δ ^ s i at hlo
      change x i / δ ^ s i < (m i : ℝ) + 1 at hhi
      have hlo' := (le_div_iff₀ (ha i)).mp hlo
      have hhi' := (div_lt_iff₀ (ha i)).mp hhi
      rw [abs_of_nonneg (by nlinarith : 0 ≤ x i - δ ^ s i * (m i : ℝ))]
      nlinarith
    have hz : ∀ i, |z i| ≤ 2 := by
      intro i
      dsimp [z]
      rw [abs_div, abs_of_pos (hb i)]
      apply (div_le_iff₀ (hb i)).mpr
      have ht := abs_add_le (y i - x i) (x i - δ ^ s i * (m i : ℝ))
      rw [sub_add_sub_cancel] at ht
      have hab := pow_le_pow_left₀ hδ.le hδρ (s i)
      linarith [hy i, hrem i]
    refine ⟨z, hz, ?_⟩
    have heq : gridWeightAt s (δ / ρ) (shift k) z = gridWeightAt s δ k y := by
      unfold gridWeightAt
      congr 1
      funext i
      dsimp [z, shift]
      rw [div_pow, Int.cast_sub]
      field_simp [(ha i).ne', (hb i).ne']
      ring
    rwa [heq]
  have hbound := grid_active_volume_bound s (by norm_num : (0 : ℝ) ≤ 2)
    (div_pos hδ hρ) ((div_le_one hρ).mpr hδρ) T hT
  rw [hcard, Real.div_rpow hδ.le hρ.le] at hbound
  norm_num only [show (2 * (2 : ℝ) + 5) = 9 by norm_num] at hbound
  have heq : (S.card : ℝ) * (δ ^ (scaleDim s : ℝ) / ρ ^ (scaleDim s : ℝ)) =
      ((S.card : ℝ) * δ ^ (scaleDim s : ℝ)) / ρ ^ (scaleDim s : ℝ) := by ring
  rw [heq] at hbound
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hρ _)).mp hbound

theorem grid_relative_pair_sum_bound {d : ℕ} (s : Fin d → ℕ) {δ ρ : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ) (x : Pt d) (S T : Finset (Fin d → ℤ))
    (φ : Pt d → ℝ) (hφ : ∀ y, φ y ≠ 0 → ∀ i, |y i - x i| ≤ ρ ^ s i)
    (b : (Fin d → ℤ) → (Fin d → ℤ) → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ j ∈ S, ∀ k ∈ T, b j k ≤ B * δ ^ (scaleDim s : ℝ))
    (hz : ∀ j ∈ S, ∀ k ∈ T,
      (∀ y, gridWeightAt s δ j y * gridWeightAt s (2 * δ) k y * φ y = 0) →
      b j k = 0) :
    ∑ j ∈ S, ∑ k ∈ T, b j k ≤ ((9 : ℝ) ^ d * ρ ^ (scaleDim s : ℝ)) * (5 : ℝ) ^ d * B := by
  classical
  let U := S.filter (fun j ↦ ∃ y, gridWeightAt s δ j y * φ y ≠ 0)
  have hU : (U.card : ℝ) * δ ^ (scaleDim s : ℝ) ≤ ((9 : ℝ) ^ d * ρ ^ (scaleDim s : ℝ)) := by
    apply grid_active_relative_volume_bound s hδ hδρ x
    intro j hj
    obtain ⟨y, hy⟩ := (Finset.mem_filter.mp hj).2
    exact ⟨y, hφ y (mul_ne_zero_iff.mp hy).2, (mul_ne_zero_iff.mp hy).1⟩
  have hinner (j : Fin d → ℤ) (hj : j ∈ S) :
      ∑ k ∈ T, b j k ≤ (5 : ℝ) ^ d * (B * δ ^ (scaleDim s : ℝ)) := by
    let V := T.filter (fun k ↦ ∃ y,
      gridWeightAt s δ j y * gridWeightAt s (2 * δ) k y * φ y ≠ 0)
    obtain ⟨N, hN, hcover⟩ := grid_overlap_count (gridCentre s δ j)
      (fun i ↦ δ ^ s i) (fun i ↦ (2 * δ) ^ s i)
      (fun i ↦ pow_pos (by linarith) _) (fun i ↦ pow_le_pow_left₀ hδ.le (by linarith) _)
    have hVN : V ⊆ N := by
      intro k hk
      obtain ⟨y, hy⟩ := (Finset.mem_filter.mp hk).2
      have hw := mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hy).1
      exact hcover k ⟨y, gridWeightAt_ne_zero_coord s hδ hw.1,
        gridBump_ne_zero_coord hw.2⟩
    calc
      _ = ∑ k ∈ V, b j k := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro k hk hkv
        apply hz j hj k hk
        intro y
        by_contra hy
        exact hkv (Finset.mem_filter.mpr ⟨hk, y, hy⟩)
      _ ≤ ∑ _k ∈ V, B * δ ^ (scaleDim s : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        exact hb j hj k (Finset.mem_filter.mp hk).1
      _ = (V.card : ℝ) * (B * δ ^ (scaleDim s : ℝ)) := by simp
      _ ≤ (5 : ℝ) ^ d * (B * δ ^ (scaleDim s : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg hB (Real.rpow_nonneg hδ.le _))
        exact_mod_cast (Finset.card_le_card hVN).trans hN
  calc
    _ = ∑ j ∈ U, ∑ k ∈ T, b j k := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j hj hju
      apply Finset.sum_eq_zero
      intro k hk
      apply hz j hj k hk
      intro y
      have hw : gridWeightAt s δ j y * φ y = 0 := by
        by_contra hw
        exact hju (Finset.mem_filter.mpr ⟨hj, y, hw⟩)
      calc
        _ = (gridWeightAt s δ j y * φ y) * gridWeightAt s (2 * δ) k y := by ring
        _ = 0 := by rw [hw, zero_mul]
    _ ≤ ∑ _j ∈ U, (5 : ℝ) ^ d * (B * δ ^ (scaleDim s : ℝ)) := by
      exact Finset.sum_le_sum (fun j hj ↦ hinner j (Finset.mem_filter.mp hj).1)
    _ = ((U.card : ℝ) * δ ^ (scaleDim s : ℝ)) * (5 : ℝ) ^ d * B := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hU (by positivity)) hB


/-- A normalized scaled test is supported in its anisotropic coordinate box. -/
theorem scaledTest_ne_zero_coord {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s)
    {r : ℕ} {ρ : ℝ} (hρ : 0 < ρ) {x y : Pt d} {η : Pt d → ℝ}
    (hη : IsTestBall s r η) (hy : scaledTest s ρ x η y ≠ 0) (i : Fin d) :
    |y i - x i| ≤ ρ ^ s i := by
  let z : Pt d := fun i ↦ (y i - x i) / ρ ^ s i
  have hz : η z ≠ 0 := (mul_ne_zero_iff.mp hy).2
  have hnorm : snorm s z ≤ 1 := hη.support (subset_tsupport η hz)
  have hi : |z i| ^ ((1 : ℝ) / (s i : ℝ)) ≤ 1 :=
    (le_ciSup (Finite.bddAbove_range _) i).trans hnorm
  have hexp : 0 < (1 : ℝ) / (s i : ℝ) := by
    have hsi : 0 < s i := by have := hs i; omega
    positivity
  have hz1 : |z i| ≤ 1 := (Real.rpow_le_rpow_iff (abs_nonneg _) zero_le_one hexp).mp
    (by simpa using hi)
  change |(y i - x i) / ρ ^ s i| ≤ 1 at hz1
  rw [abs_div, abs_of_pos (pow_pos hρ _)] at hz1
  exact (div_le_one (pow_pos hρ _)).mp hz1

/-- The dyadic overlap sum has one bound for all normalized tests at every
larger test scale. The relative-volume factors cancel exactly. -/
theorem model_germ_scaled_grid_sum_bound
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s) {γ : ℝ}
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f)
    (K : Set (Pt d)) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ δ : ℝ), 0 < δ → δ ≤ ρ → δ ≤ 1 / 4 →
      ∀ (x : Pt d) (η : Pt d → ℝ), IsTestBall s r η →
      ∀ S T : Finset (Fin d → ℤ),
      (∀ j ∈ S, gridCentre s δ j ∈ K) →
      (∀ k ∈ T, gridCentre s (2 * δ) k ∈ K) →
      ∑ j ∈ S, ∑ k ∈ T,
        |(Pi (gridCentre s δ j) (f (gridCentre s δ j)) -
          Pi (gridCentre s (2 * δ) k) (f (gridCentre s (2 * δ) k))).eval
          (fun y ↦ gridWeightAt s δ j y * gridWeightAt s (2 * δ) k y *
            scaledTest s ρ x η y)| ≤ C * δ ^ γ := by
  classical
  obtain ⟨L, hL, hnorm⟩ := grid_overlap_scaled_test_normalization (d := d) s r
  obtain ⟨M, hM, hgerm⟩ := model_germ_bound_of_dyadic_overlap hs hT hmod hf K hK
  refine ⟨(9 : ℝ) ^ d * (5 : ℝ) ^ d * (L * M), by positivity, ?_⟩
  intro ρ δ hδ hδρ hδsmall x η hη S T hS hTcentres
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hscale (i : Fin d) : δ ^ s i ≤ (2 * δ) ^ s i :=
    pow_le_pow_left₀ hδ.le (by linarith) _
  let φ := scaledTest s ρ x η
  let P := fun j k y ↦ gridWeightAt s δ j y * gridWeightAt s (2 * δ) k y * φ y
  let ξ := fun j k ↦ Pi (gridCentre s δ j) (f (gridCentre s δ j)) -
    Pi (gridCentre s (2 * δ) k) (f (gridCentre s (2 * δ) k))
  let B := L * M * δ ^ γ * ρ ^ (-(scaleDim s : ℝ))
  have hzero (j k : Fin d → ℤ) (hz : ∀ y, P j k y = 0) :
      |(ξ j k).eval (P j k)| = 0 := by
    rw [show P j k = fun _ ↦ 0 from funext hz, grid_eval_zero, abs_zero]
  have hpair (j : Fin d → ℤ) (hj : j ∈ S) (k : Fin d → ℤ) (hk : k ∈ T) :
      |(ξ j k).eval (P j k)| ≤ B * δ ^ (scaleDim s : ℝ) := by
    by_cases hz : ∀ y, P j k y = 0
    · rw [hzero j k hz]
      dsimp [B]
      positivity
    push Not at hz
    obtain ⟨w, hw⟩ := hz
    have hw' := mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hw).1
    obtain ⟨θ, hθ, heq⟩ := hnorm ρ δ hδ hδρ (fun i ↦ (2 * δ) ^ s i)
      hscale x j k η hη
    have hP : P j k = fun y ↦ (L * δ ^ (scaleDim s : ℝ) * ρ ^ (-(scaleDim s : ℝ))) *
        scaledTest s δ (gridCentre s δ j) θ y := funext heq
    have hθtest := scaledTest_mem s hδ (gridCentre s δ j) ⟨hθ.smooth, hθ.compactSupport⟩
    have hbound := hgerm (gridCentre s δ j) (hS j hj)
      (gridCentre s (2 * δ) k) (hTcentres k hk) δ hδ hδsmall
      ⟨w, fun i ↦ (gridWeightAt_ne_zero_coord s hδ hw'.1 i).le,
        fun i ↦ (gridWeightAt_ne_zero_coord s (by linarith) hw'.2 i).le⟩ θ hθ
    rw [hP, grid_eval_const_mul _ _ hθtest, abs_mul,
      abs_of_nonneg (show 0 ≤ L * δ ^ (scaleDim s : ℝ) * ρ ^ (-(scaleDim s : ℝ))
        by positivity)]
    calc
      _ ≤ (L * δ ^ (scaleDim s : ℝ) * ρ ^ (-(scaleDim s : ℝ))) * (M * δ ^ γ) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = _ := by dsimp [B]; ring
  have hsum := grid_relative_pair_sum_bound s hδ hδρ x S T φ
    (fun y hy i ↦ scaledTest_ne_zero_coord hs hρ hη hy i)
    (fun j k ↦ |(ξ j k).eval (P j k)|) (B := B) (by dsimp [B]; positivity)
    hpair (fun j _ k _ hz ↦ hzero j k hz)
  have hvolume : ρ ^ (scaleDim s : ℝ) * ρ ^ (-(scaleDim s : ℝ)) = 1 := by
    rw [← Real.rpow_add hρ, add_neg_cancel, Real.rpow_zero]
  calc
    _ ≤ ((9 : ℝ) ^ d * ρ ^ (scaleDim s : ℝ)) * (5 : ℝ) ^ d * B := hsum
    _ = ((9 : ℝ) ^ d * (5 : ℝ) ^ d * (L * M) * δ ^ γ) *
        (ρ ^ (scaleDim s : ℝ) * ρ ^ (-(scaleDim s : ℝ))) := by dsimp [B]; ring
    _ = _ := by rw [hvolume, mul_one]

/-- Adjacent grid approximations satisfy a uniform bound on all normalized
rescaled tests centred in a compact set. -/
theorem model_grid_scaled_increment_bound
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s) {γ : ℝ}
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f)
    (K : Set (Pt d)) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      ∀ η : Pt d → ℝ, IsTestBall s r η →
      ∀ δ : ℝ, 0 < δ → δ ≤ ρ → δ ≤ 1 / 4 →
      |(gridGluing (fun i ↦ δ ^ s i) (fun z ↦ Pi z (f z))).eval (scaledTest s ρ x η) -
        (gridGluing (fun i ↦ (2 * δ) ^ s i) (fun z ↦ Pi z (f z))).eval
          (scaledTest s ρ x η)| ≤ C * δ ^ γ := by
  classical
  obtain ⟨R, hRpos, hR⟩ := hK.isBounded.subset_closedBall_lt 0 0
  let K' := Metric.closedBall (0 : Pt d) ((R + 1) + 1)
  obtain ⟨C, hC, hbound⟩ := model_germ_scaled_grid_sum_bound hs hT hmod hf K'
    (isCompact_closedBall _ _)
  refine ⟨C, hC, ?_⟩
  intro x hx ρ hρ hρ1 η hη δ hδ hδρ hδsmall
  let φ : testFunctions d := ⟨scaledTest s ρ x η,
    scaledTest_mem s hρ x ⟨hη.smooth, hη.compactSupport⟩⟩
  have hxR : ‖x‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hR hx
  have hφR : ∀ y, φ.val y ≠ 0 → ∀ i, |y i| ≤ R + 1 := by
    intro y hy i
    have hdist := scaledTest_ne_zero_coord hs hρ hη hy i
    have hpow : ρ ^ s i ≤ 1 := pow_le_one₀ hρ.le hρ1
    have hxcoord : |x i| ≤ R :=
      (show |x i| ≤ ‖x‖ by simpa using norm_le_pi_norm x i).trans hxR
    have ht := abs_add_le (y i - x i) (x i)
    rw [sub_add_cancel] at ht
    linarith
  change |(gridGluing (fun i ↦ δ ^ s i) (fun z ↦ Pi z (f z))).eval φ.val -
    (gridGluing (fun i ↦ (2 * δ) ^ s i) (fun z ↦ Pi z (f z))).eval φ.val| ≤ _
  simp only [Distrib.eval, dif_pos φ.property]
  let a := fun i ↦ δ ^ s i
  let c := fun i ↦ (2 * δ) ^ s i
  let ψ := scaledGridWeight a
  let χ := scaledGridWeight c
  let hψ := scaledGridWeight_contDiff a
  let hχ := scaledGridWeight_contDiff c
  let finS := finite_support_mulTest ψ hψ (scaledGridWeight_locallyFinite a) φ
  let finT := finite_support_mulTest χ hχ (scaledGridWeight_locallyFinite c) φ
  let S := finS.toFinset
  let T := finT.toFinset
  have hS : Function.support (fun j ↦ mulTest (ψ j) (hψ j) φ) ⊆ S :=
    fun _ hj ↦ finS.mem_toFinset.mpr hj
  have hT' : Function.support (fun j ↦ mulTest (χ j) (hχ j) φ) ⊆ T :=
    fun _ hj ↦ finT.mem_toFinset.mpr hj
  have hcentS : ∀ j ∈ S, gridCentre s δ j ∈ K' := by
    intro j hj
    exact active_grid_centre_mem a (fun i ↦ pow_pos hδ _) (fun i ↦
      pow_le_one₀ hδ.le (by linarith)) φ (by linarith : 0 ≤ R + 1) hφR (finS.mem_toFinset.mp hj)
  have hcentT : ∀ k ∈ T, gridCentre s (2 * δ) k ∈ K' := by
    intro k hk
    exact active_grid_centre_mem c (fun i ↦ pow_pos (by linarith) _) (fun i ↦
      pow_le_one₀ (by linarith) (by linarith)) φ (by linarith : 0 ≤ R + 1) hφR (finT.mem_toFinset.mp hk)
  have hid := locallyFiniteGluing_sub_eq ψ χ hψ hχ
    (scaledGridWeight_locallyFinite a) (scaledGridWeight_locallyFinite c)
    (scaledGridWeight_finsum a) (scaledGridWeight_finsum c)
    (fun j ↦ Pi (gridCentre s δ j) (f (gridCentre s δ j)))
    (fun k ↦ Pi (gridCentre s (2 * δ) k) (f (gridCentre s (2 * δ) k))) φ S T hS hT'
  change |locallyFiniteGluing ψ hψ _
    (fun j ↦ Pi (gridCentre s δ j) (f (gridCentre s δ j))) φ -
    locallyFiniteGluing χ hχ _
    (fun k ↦ Pi (gridCentre s (2 * δ) k) (f (gridCentre s (2 * δ) k))) φ| ≤ _
  rw [hid]
  have hp (j k : Fin d → ℤ) :
      (Pi (gridCentre s δ j) (f (gridCentre s δ j)) -
        Pi (gridCentre s (2 * δ) k) (f (gridCentre s (2 * δ) k)))
        (mulTest (ψ j) (hψ j) (mulTest (χ k) (hχ k) φ)) =
      (Pi (gridCentre s δ j) (f (gridCentre s δ j)) -
        Pi (gridCentre s (2 * δ) k) (f (gridCentre s (2 * δ) k))).eval
        (fun y ↦ gridWeightAt s δ j y * gridWeightAt s (2 * δ) k y * φ.val y) := by
    let η := mulTest (ψ j) (hψ j) (mulTest (χ k) (hχ k) φ)
    have heq : (fun y ↦ gridWeightAt s δ j y * gridWeightAt s (2 * δ) k y * φ.val y) =
        η.val := by
      funext y
      change gridWeightAt s δ j y * gridWeightAt s (2 * δ) k y * φ.val y =
        gridWeightAt s δ j y * (gridWeightAt s (2 * δ) k y * φ.val y)
      exact mul_assoc _ _ _
    rw [heq, Distrib.eval, dif_pos η.property]
  simp_rw [hp]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_sum (fun j _ ↦ Finset.abs_sum_le_sum_abs _ _)).trans
      (hbound ρ δ hδ hδρ hδsmall x η hη S T hcentS hcentT))


theorem gridGluing_eval_finsum {d : ℕ} (a : Fin d → ℝ) (F : Pt d → Distrib d)
    {φ : Pt d → ℝ} (hφ : φ ∈ testFunctions d) :
    (gridGluing a F).eval φ = ∑ᶠ j : Fin d → ℤ,
      (F (fun i ↦ a i * (j i : ℝ))).eval (fun y ↦ scaledGridWeight a j y * φ y) := by
  rw [Distrib.eval, dif_pos hφ]
  exact gridGluing_apply_finsum a F ⟨φ, hφ⟩

end Hairer

open BigOperators Hairer
noncomputable section
theorem Hairer.uniform_scaled_grid_increment_bound
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s) {γ : ℝ}
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f)
    (K : Set (Pt d)) (hK : IsCompact K) :
    let W : Pt d → ℝ := fun z ↦
      ∏ i, (Real.smoothTransition (z i + 1) - Real.smoothTransition (z i))
    let X := fun (δ : ℝ) (j : Fin d → ℤ) (i : Fin d) ↦ δ ^ s i * (j i : ℝ)
    let R := fun (δ : ℝ) (φ : Pt d → ℝ) ↦ ∑ᶠ j : Fin d → ℤ,
      (Pi (X δ j) (f (X δ j))).eval
        (fun y ↦ W (fun i ↦ y i / δ ^ s i - (j i : ℝ)) * φ y)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      ∀ η : Pt d → ℝ, IsTestBall s r η →
      ∀ δ : ℝ, 0 < δ → δ ≤ ρ → δ ≤ 1 / 4 →
      |R δ (scaledTest s ρ x η) -
        R (2 * δ)
          (scaledTest s ρ x η)| ≤ C * δ ^ γ := by
  obtain ⟨C, hC, hb⟩ := model_grid_scaled_increment_bound hs hT hmod hf K hK
  refine ⟨C, hC, ?_⟩
  intro x hx ρ hρ hρ1 η hη δ hδ hδρ hδsmall
  have h := hb x hx ρ hρ hρ1 η hη δ hδ hδρ hδsmall
  have hφ := scaledTest_mem s hρ x ⟨hη.smooth, hη.compactSupport⟩
  rw [gridGluing_eval_finsum _ _ hφ, gridGluing_eval_finsum _ _ hφ] at h
  exact h



set_option autoImplicit false
open BigOperators HairerAux
noncomputable section
namespace Hairer

/-- Localizing a normalized test to one finer grid cell has a uniform
normalization constant and the exact relative-volume coefficient. -/
theorem grid_single_scaled_test_normalization {d : ℕ} (s : Fin d → ℕ) (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ δ : ℝ), 0 < δ → δ ≤ ρ →
      ∀ (x : Pt d) (j : Fin d → ℤ) (η : Pt d → ℝ), IsTestBall s r η →
      ∃ θ : Pt d → ℝ, IsTestBall s r θ ∧ ∀ y,
        gridWeightAt s δ j y * scaledTest s ρ x η y =
        (C * δ ^ (scaleDim s : ℝ) * ρ ^ (-(scaleDim s : ℝ))) *
          scaledTest s δ (gridCentre s δ j) θ y := by
  obtain ⟨C, hC, hnorm⟩ := uniform_overlap_test_normalization s r
  refine ⟨C, hC, ?_⟩
  intro ρ δ hδ hδρ x j η hη
  have hρ : 0 < ρ := hδ.trans_le hδρ
  let a : Fin d → ℝ := fun i ↦ δ ^ s i
  let z0 := gridCentre s δ j
  let v : Pt d := fun i ↦ (z0 i - x i) / ρ ^ s i
  let b : Fin d → ℝ := fun i ↦ a i / ρ ^ s i
  have ha0 (i : Fin d) : 0 < a i := pow_pos hδ _
  have hb (i : Fin d) : |b i| ≤ 1 := by
    rw [abs_of_pos (div_pos (ha0 i) (pow_pos hρ _))]
    exact (div_le_one (pow_pos hρ _)).mpr (pow_le_pow_left₀ hδ.le hδρ _)
  have hbump (z : Pt d) : bumpBox ((0 : Pt d) + scaleCLM 0 z) = 1 := by
    simp [bumpBox, chi, scaleCLM_apply]
  let θ : Pt d → ℝ := fun z ↦ (η (v + scaleCLM b z) * bumpBox z) / C
  have hθ : IsTestBall s r θ := by
    have h := hnorm η hη.smooth hη.derivBound v 0 b 0 hb (by simp)
    simpa only [hbump, mul_one] using h
  refine ⟨θ, hθ, ?_⟩
  intro y
  let z : Pt d := fun i ↦ (y i - z0 i) / δ ^ s i
  have hfine : z = fun i ↦ y i / δ ^ s i - (j i : ℝ) := by
    funext i
    change (y i - δ ^ s i * (j i : ℝ)) / δ ^ s i = _
    field_simp
  have htest : v + scaleCLM b z = fun i ↦ (y i - x i) / ρ ^ s i := by
    funext i
    change (z0 i - x i) / ρ ^ s i +
      (a i / ρ ^ s i) * ((y i - z0 i) / a i) = _
    field_simp [(ha0 i).ne', (pow_pos hρ (s i)).ne']
    ring
  have hvolume : δ ^ (scaleDim s : ℝ) * δ ^ (-(scaleDim s : ℝ)) = 1 := by
    rw [← Real.rpow_add hδ, add_neg_cancel, Real.rpow_zero]
  change _ = (C * δ ^ (scaleDim s : ℝ) * ρ ^ (-(scaleDim s : ℝ))) *
    (δ ^ (-(scaleDim s : ℝ)) * ((η (v + scaleCLM b z) * bumpBox z) / C))
  rw [htest, hfine]
  change gridWeightAt s δ j y *
    (ρ ^ (-(scaleDim s : ℝ)) * η (fun i ↦ (y i - x i) / ρ ^ s i)) = _
  calc
    _ = (δ ^ (scaleDim s : ℝ) * δ ^ (-(scaleDim s : ℝ))) *
      (ρ ^ (-(scaleDim s : ℝ)) *
        (η (fun i ↦ (y i - x i) / ρ ^ s i) *
          bumpBox (fun i ↦ y i / δ ^ s i - (j i : ℝ)))) := by
      rw [hvolume]
      simp only [gridWeightAt, gridBump, bumpBox, chi]
      ring
    _ = _ := by field_simp [hC.ne']

/-- A partition of unity compares the glued distribution with a constant
germ through the finite sum of localized germ differences. -/
theorem gridGluing_sub_const_eq {d : ℕ} (a : Fin d → ℝ) (F : Pt d → Distrib d)
    (ξ : Distrib d) (φ : testFunctions d) (S : Finset (Fin d → ℤ))
    (hS : Function.support (fun j ↦
      mulTest (scaledGridWeight a j) (scaledGridWeight_contDiff a j) φ) ⊆ S) :
    gridGluing a F φ - ξ φ = ∑ j ∈ S,
      (F (fun i ↦ a i * (j i : ℝ)) - ξ)
        (mulTest (scaledGridWeight a j) (scaledGridWeight_contDiff a j) φ) := by
  rw [gridGluing, locallyFiniteGluing_eq_finiteGluing _ _ _ _ φ S hS,
    finiteGluing_apply]
  have hsum := sum_mulTest S (scaledGridWeight a) (scaledGridWeight_contDiff a) φ
    (partition_sum_on_test _ _ (scaledGridWeight_finsum a) φ S hS)
  have hξ : ξ φ = ∑ j ∈ S, ξ (mulTest (scaledGridWeight a j)
      (scaledGridWeight_contDiff a j) φ) := by
    conv_lhs => rw [← hsum, map_sum]
  rw [hξ]
  simp only [LinearMap.sub_apply, Finset.sum_sub_distrib]

theorem grid_model_comparable_scale_bound
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s) {γ : ℝ}
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f)
    (K : Set (Pt d)) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ρ δ : ℝ, 0 < δ → δ ≤ ρ →
      ρ ≤ 2 * δ → ρ ≤ 1 / 2 → ∀ η : Pt d → ℝ, IsTestBall s r η →
      |(gridGluing (fun i ↦ δ ^ s i) (fun z ↦ Pi z (f z))).eval
          (scaledTest s ρ x η) - (Pi x (f x)).eval (scaledTest s ρ x η)| ≤
        C * δ ^ γ := by
  classical
  obtain ⟨R, hRpos, hR⟩ := hK.isBounded.subset_closedBall_lt 0 0
  let K' := Metric.closedBall (0 : Pt d) ((R + 1) + 1)
  obtain ⟨M, hM, hbound⟩ := model_germ_coherence_multiple hT hmod hf 4 (by norm_num)
    K' (isCompact_closedBall _ _)
  obtain ⟨L, hL, hnorm⟩ := grid_single_scaled_test_normalization s r
  refine ⟨9 ^ d * (L * M), by positivity, ?_⟩
  intro x hx ρ δ hδ hδρ hρδ hρsmall η hη
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hδ1 : δ ≤ 1 := by linarith
  let φ : testFunctions d := ⟨scaledTest s ρ x η,
    scaledTest_mem s hρ x ⟨hη.smooth, hη.compactSupport⟩⟩
  have hxR : ‖x‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hR hx
  have hxK : x ∈ K' := by
    change dist x 0 ≤ (R + 1) + 1
    rw [dist_zero_right]
    linarith
  have hφR : ∀ y, φ.val y ≠ 0 → ∀ i, |y i| ≤ R + 1 := by
    intro y hy i
    have hd := scaledTest_ne_zero_coord hs hρ hη hy i
    have hp : ρ ^ s i ≤ 1 := pow_le_one₀ hρ.le (by linarith)
    have hc : |x i| ≤ R :=
      (show |x i| ≤ ‖x‖ by simpa using norm_le_pi_norm x i).trans hxR
    have ht := abs_add_le (y i - x i) (x i)
    rw [sub_add_cancel] at ht
    linarith
  let a := fun i ↦ δ ^ s i
  let ψ := scaledGridWeight a
  let hψ := scaledGridWeight_contDiff a
  let finS := finite_support_mulTest ψ hψ (scaledGridWeight_locallyFinite a) φ
  let S := finS.toFinset
  have hS : Function.support (fun j ↦ mulTest (ψ j) (hψ j) φ) ⊆ S :=
    fun _ hj ↦ finS.mem_toFinset.mpr hj
  have hwitness : ∀ j ∈ S, ∃ y, gridWeightAt s δ j y ≠ 0 ∧ φ.val y ≠ 0 := by
    intro j hj
    have hn := finS.mem_toFinset.mp hj
    have he : ∃ y, ψ j y * φ.val y ≠ 0 := by
      by_contra! h
      apply hn
      apply Subtype.ext
      funext y
      exact h y
    obtain ⟨y, hy⟩ := he
    exact ⟨y, (mul_ne_zero_iff.mp hy).1, (mul_ne_zero_iff.mp hy).2⟩
  have hcard := grid_active_relative_volume_bound s hδ hδρ x S (by
    intro j hj
    obtain ⟨y, hw, hy⟩ := hwitness j hj
    exact ⟨y, scaledTest_ne_zero_coord hs hρ hη hy, hw⟩)
  have hterm : ∀ j ∈ S,
      |(Pi (gridCentre s δ j) (f (gridCentre s δ j)) - Pi x (f x))
        (mulTest (ψ j) (hψ j) φ)| ≤
      (L * M * δ ^ γ * ρ ^ (-(scaleDim s : ℝ))) * δ ^ (scaleDim s : ℝ) := by
    intro j hj
    have hjK : gridCentre s δ j ∈ K' :=
      active_grid_centre_mem a (fun i ↦ pow_pos hδ _) (fun i ↦
        pow_le_one₀ hδ.le hδ1) φ (by linarith : 0 ≤ R + 1) hφR
        (finS.mem_toFinset.mp hj)
    obtain ⟨y, hw, hy⟩ := hwitness j hj
    have hdist := snorm_sub_le_of_box_overlap hs hδ.le hδρ
      (fun i ↦ (gridWeightAt_ne_zero_coord s hδ hw i).le)
      (scaledTest_ne_zero_coord hs hρ hη hy)
    obtain ⟨θ, hθ, heq⟩ := hnorm ρ δ hδ hδρ x j η hη
    have hb := hbound (gridCentre s δ j) hjK x hxK δ hδ hδ1
      (by linarith : snorm s (gridCentre s δ j - x) ≤ 1)
      (by linarith : snorm s (gridCentre s δ j - x) ≤ 4 * δ) θ hθ
    let ξ := Pi (gridCentre s δ j) (f (gridCentre s δ j)) - Pi x (f x)
    let χ := mulTest (ψ j) (hψ j) φ
    have hid : ξ χ = ξ.eval (fun y ↦ gridWeightAt s δ j y * scaledTest s ρ x η y) := by
      change ξ χ = ξ.eval χ.val
      rw [Distrib.eval, dif_pos χ.property]
    change |ξ χ| ≤ _
    rw [hid, funext heq, grid_eval_const_mul ξ _
      (scaledTest_mem s hδ _ ⟨hθ.smooth, hθ.compactSupport⟩), abs_mul,
      abs_of_pos (by positivity : 0 < L * δ ^ (scaleDim s : ℝ) *
        ρ ^ (-(scaleDim s : ℝ)))]
    calc
      _ ≤ (L * δ ^ (scaleDim s : ℝ) * ρ ^ (-(scaleDim s : ℝ))) *
          (M * δ ^ γ) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by ring
  change |(gridGluing a (fun z ↦ Pi z (f z))).eval φ.val -
    (Pi x (f x)).eval φ.val| ≤ _
  simp only [Distrib.eval, dif_pos φ.property]
  rw [gridGluing_sub_const_eq a _ _ φ S hS]
  have hv : ρ ^ (scaleDim s : ℝ) * ρ ^ (-(scaleDim s : ℝ)) = 1 := by
    rw [← Real.rpow_add hρ, add_neg_cancel, Real.rpow_zero]
  calc
    _ ≤ ∑ j ∈ S, |(Pi (gridCentre s δ j) (f (gridCentre s δ j)) - Pi x (f x))
        (mulTest (ψ j) (hψ j) φ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ S, (L * M * δ ^ γ * ρ ^ (-(scaleDim s : ℝ))) *
        δ ^ (scaleDim s : ℝ) := Finset.sum_le_sum hterm
    _ = ((S.card : ℝ) * δ ^ (scaleDim s : ℝ)) *
        (L * M * δ ^ γ * ρ ^ (-(scaleDim s : ℝ))) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ (9 ^ d * ρ ^ (scaleDim s : ℝ)) *
        (L * M * δ ^ γ * ρ ^ (-(scaleDim s : ℝ))) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (9 ^ d * (L * M)) * δ ^ γ := by
      calc
        _ = (9 ^ d * (L * M) * δ ^ γ) *
            (ρ ^ (scaleDim s : ℝ) * ρ ^ (-(scaleDim s : ℝ))) := by ring
        _ = _ := by rw [hv, mul_one]

end Hairer

open BigOperators Hairer
theorem solution
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s) {γ : ℝ}
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f)
    (K : Set (Pt d)) (hK : IsCompact K) :
    let W : Pt d → ℝ := fun z ↦
      ∏ i, (Real.smoothTransition (z i + 1) - Real.smoothTransition (z i))
    let X := fun (δ : ℝ) (j : Fin d → ℤ) (i : Fin d) ↦ δ ^ s i * (j i : ℝ)
    let R := fun (δ : ℝ) (φ : Pt d → ℝ) ↦ ∑ᶠ j : Fin d → ℤ,
      (Pi (X δ j) (f (X δ j))).eval
        (fun y ↦ W (fun i ↦ y i / δ ^ s i - (j i : ℝ)) * φ y)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ρ δ : ℝ, 0 < δ → δ ≤ ρ →
      ρ ≤ 2 * δ → ρ ≤ 1 / 2 → ∀ η : Pt d → ℝ, IsTestBall s r η →
      |R δ (scaledTest s ρ x η) - (Pi x (f x)).eval (scaledTest s ρ x η)| ≤
        C * δ ^ γ := by
  obtain ⟨C, hC, hb⟩ := Hairer.grid_model_comparable_scale_bound hs hT hmod hf K hK
  refine ⟨C, hC, ?_⟩
  intro x hx ρ δ hδ hδρ hρδ hρsmall η hη
  have h := hb x hx ρ δ hδ hδρ hρδ hρsmall η hη
  rw [Hairer.gridGluing_eval_finsum _ _
    (scaledTest_mem s (hδ.trans_le hδρ) x ⟨hη.smooth, hη.compactSupport⟩)] at h
  exact h

#print axioms solution
