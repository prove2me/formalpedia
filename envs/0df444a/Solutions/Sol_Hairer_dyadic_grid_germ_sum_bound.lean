-- Prove2me | solution 1 for Hairer.dyadic_grid_germ_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T20:27:11.210148+00:00
-- url     : https://prove2.me/submissions/012484db-7a62-4e1a-b5fa-51fb5010222f

import Definitions.Def_Hairer_Model


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

#print axioms solution
