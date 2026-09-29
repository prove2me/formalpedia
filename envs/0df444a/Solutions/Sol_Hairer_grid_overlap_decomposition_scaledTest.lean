-- Prove2me | solution 1 for Hairer.grid_overlap_decomposition_scaledTest
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T20:07:47.544658+00:00
-- url     : https://prove2.me/submissions/41d75d37-7dc1-4819-8351-6b08d41b973c

import Definitions.Def_Hairer_TestFunctions

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

theorem solution {d : ℕ} (s : Fin d → ℕ) (r : ℕ)
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


#print axioms solution
