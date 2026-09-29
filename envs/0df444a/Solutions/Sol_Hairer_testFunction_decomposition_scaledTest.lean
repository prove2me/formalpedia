-- Prove2me | solution 1 for Hairer.testFunction_decomposition_scaledTest
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-19T06:21:12.166715+00:00
-- url     : https://prove2.me/submissions/dfc96f88-26b5-46f6-9175-7cf1dffafc2f

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

open HairerAux

/-- **Anisotropic partition of unity at scale `δ`.** -/
theorem solution
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s) (r : ℕ)
    {φ : Pt d → ℝ} (hφ : φ ∈ testFunctions d) :
    ∃ (K : Set (Pt d)) (M : ℝ), IsCompact K ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        ∃ (n : ℕ) (x : Fin n → Pt d) (c : Fin n → ℝ) (η : Fin n → (Pt d → ℝ)),
          (∀ i, x i ∈ K) ∧ (∀ i, IsTestBall s r (η i)) ∧
          (∑ i, |c i|) ≤ M ∧
          ∀ y : Pt d, φ y = ∑ i, c i * scaledTest s δ (x i) (η i) y := by
  obtain ⟨hsm, hcs⟩ := hφ
  obtain ⟨Φ, hΦ0, hΦ⟩ := exists_deriv_bound hsm hcs r
  obtain ⟨Ω, hΩ0, hΩ⟩ := exists_deriv_bound (bumpBox_contDiff (d := d))
    (bumpBox_hasCompactSupport (d := d)) r
  -- the normalising constant
  set Λ : ℝ := 2 ^ r * Φ * Ω + 1 with hΛdef
  have hΛ1 : (1 : ℝ) ≤ Λ := by
    have : (0:ℝ) ≤ 2 ^ r * Φ * Ω := by positivity
    linarith
  have hΛ0 : (0 : ℝ) < Λ := lt_of_lt_of_le zero_lt_one hΛ1
  -- a box containing the support of `φ`
  obtain ⟨R, hR0, hR⟩ : ∃ R : ℝ, 0 ≤ R ∧ ∀ y : Pt d, φ y ≠ 0 → ∀ i, |y i| ≤ R := by
    obtain ⟨R, hR⟩ := (hcs.isCompact.isBounded).subset_closedBall 0
    refine ⟨max R 0, le_max_right _ _, ?_⟩
    intro y hy i
    have hmem : y ∈ tsupport φ := subset_tsupport φ hy
    have : ‖y‖ ≤ R := by simpa [Metric.mem_closedBall] using hR hmem
    calc |y i| ≤ ‖y‖ := by simpa using norm_le_pi_norm y i
      _ ≤ max R 0 := le_trans this (le_max_left _ _)
  refine ⟨boxSet d (R + 1), Λ * (2 * R + 3) ^ d, isCompact_boxSet d (R + 1), ?_⟩
  intro δ hδ0 hδ1
  -- the number of boxes in direction `i`
  set N : Fin d → ℕ := fun i => ⌈R / δ ^ (s i)⌉₊ with hNdef
  have hδpow : ∀ i, 0 < δ ^ (s i) := fun i => pow_pos hδ0 _
  have hδpow1 : ∀ i, δ ^ (s i) ≤ 1 := fun i => pow_le_one₀ hδ0.le hδ1
  have hNge : ∀ i, R / δ ^ (s i) ≤ (N i : ℝ) := fun i => Nat.le_ceil _
  have hNlt : ∀ i, (N i : ℝ) ≤ R / δ ^ (s i) + 1 := by
    intro i
    have := Nat.ceil_lt_add_one (a := R / δ ^ (s i)) (by positivity)
    linarith
  -- the index set
  set S : Finset (Fin d → ℕ) := Fintype.piFinset (fun i => Finset.range (2 * N i + 1)) with hSdef
  set a : Fin d → ℝ := fun i => δ ^ (s i) with hadef
  have ha : ∀ i, |a i| ≤ 1 := by
    intro i
    rw [hadef, abs_of_pos (hδpow i)]
    exact hδpow1 i
  set center : (Fin d → ℕ) → Pt d := fun j i => δ ^ (s i) * ((j i : ℝ) - (N i : ℝ)) with hcdef
  set eta : (Fin d → ℕ) → (Pt d → ℝ) :=
    fun j z => (φ (center j + scaleCLM a z) * bumpBox z) / Λ with hetadef
  set coef : ℝ := Λ * δ ^ ((scaleDim s : ℝ)) with hcoefdef
  -- transfer from the finset `S` to `Fin S.card`
  set nn : ℕ := S.card with hnn
  set e : Fin nn ≃ {x // x ∈ S} := (S.equivFin).symm with he
  refine ⟨nn, fun i => center (e i), fun _ => coef, fun i => eta (e i), ?_, ?_, ?_, ?_⟩
  · -- the centres lie in the box
    intro i k
    have hmem : (e i : Fin d → ℕ) ∈ S := (e i).2
    have hk : (e i : Fin d → ℕ) k ∈ Finset.range (2 * N k + 1) :=
      Fintype.mem_piFinset.mp hmem k
    have hkle : ((e i : Fin d → ℕ) k : ℝ) ≤ 2 * (N k : ℝ) := by
      have := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      exact_mod_cast this
    have habs : |((e i : Fin d → ℕ) k : ℝ) - (N k : ℝ)| ≤ (N k : ℝ) := by
      rw [abs_le]
      constructor
      · have : (0 : ℝ) ≤ ((e i : Fin d → ℕ) k : ℝ) := Nat.cast_nonneg _
        linarith
      · linarith
    have : |center (e i) k| = δ ^ (s k) * |((e i : Fin d → ℕ) k : ℝ) - (N k : ℝ)| := by
      rw [hcdef, abs_mul, abs_of_pos (hδpow k)]
    rw [this]
    calc δ ^ (s k) * |((e i : Fin d → ℕ) k : ℝ) - (N k : ℝ)|
        ≤ δ ^ (s k) * (N k : ℝ) := by
          exact mul_le_mul_of_nonneg_left habs (hδpow k).le
      _ ≤ δ ^ (s k) * (R / δ ^ (s k) + 1) :=
          mul_le_mul_of_nonneg_left (hNlt k) (hδpow k).le
      _ = R + δ ^ (s k) := by field_simp
      _ ≤ R + 1 := by linarith [hδpow1 k]
  · -- each `η` is an admissible test function
    intro i
    set j : Fin d → ℕ := (e i : Fin d → ℕ) with hj
    have hFsmooth : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : Pt d => φ (center j + scaleCLM a z) * bumpBox z) :=
      ((hsm.comp (contDiff_const.add contDiff_id)).comp (scaleCLM a).contDiff).mul
        bumpBox_contDiff
    have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (eta j) := by
      rw [hetadef]
      exact hFsmooth.div_const Λ
    have hzero : ∀ z : Pt d, (∃ k, 1 ≤ |z k|) → eta j z = 0 := by
      intro z hz
      rw [hetadef]
      simp [bumpBox_eq_zero hz]
    have hsupp : HasCompactSupport (eta j) := by
      apply HasCompactSupport.intro (isCompact_boxSet d 1)
      intro z hz
      apply hzero
      simp only [boxSet, Set.mem_ofPred_eq, not_forall, not_le] at hz
      obtain ⟨k, hk⟩ := hz
      exact ⟨k, hk.le⟩
    refine ⟨hsmooth, hsupp, ?_, ?_⟩
    · -- support inside the unit ball of the scaled quasi-norm
      have hsub : tsupport (eta j) ⊆ boxSet d 1 := by
        apply closure_minimal _ (isCompact_boxSet d 1).isClosed
        intro z hz
        by_contra hcon
        simp only [boxSet, Set.mem_ofPred_eq, not_forall, not_le] at hcon
        obtain ⟨k, hk⟩ := hcon
        exact hz (hzero z ⟨k, hk.le⟩)
      intro z hz
      have hz1 : ∀ k, |z k| ≤ 1 := hsub hz
      have : snorm s z ≤ 1 := by
        apply Real.iSup_le _ zero_le_one
        intro k
        apply Real.rpow_le_one (abs_nonneg _) (hz1 k)
        positivity
      exact this
    · -- the derivative bound
      intro m hm z
      show ‖iteratedFDeriv ℝ m (eta j) z‖ ≤ 1
      have hconst : eta j
          = (Λ⁻¹ : ℝ) • (fun w : Pt d => φ (center j + scaleCLM a w) * bumpBox w) := by
        funext w
        simp [hetadef, smul_eq_mul, div_eq_inv_mul]
      rw [hconst, iteratedFDeriv_const_smul_apply
        (hFsmooth.of_le (by exact_mod_cast le_top)).contDiffAt, norm_smul]
      have hb := localized_deriv_bound hsm hΦ hΦ0 hΩ hΩ0 (center j) ha hm z
      have hinv : ‖(Λ⁻¹ : ℝ)‖ = Λ⁻¹ := by
        rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [hinv]
      calc Λ⁻¹ * ‖iteratedFDeriv ℝ m
            (fun w : Pt d => φ (center j + scaleCLM a w) * bumpBox w) z‖
          ≤ Λ⁻¹ * (2 ^ r * Φ * Ω) := by
            exact mul_le_mul_of_nonneg_left hb (by positivity)
        _ ≤ 1 := by
            rw [inv_mul_le_iff₀ hΛ0, mul_one, hΛdef]
            linarith
  · -- the total coefficient mass
    have hcard : (S.card : ℝ) = ∏ i, ((2 * N i + 1 : ℕ) : ℝ) := by
      rw [hSdef, Fintype.card_piFinset]
      push_cast
      simp
    have hsum : ∑ _i : Fin nn, |coef| = (S.card : ℝ) * |coef| := by
      simp [hnn, Finset.sum_const, nsmul_eq_mul]
    rw [hsum]
    have hcoefabs : |coef| = Λ * δ ^ ((scaleDim s : ℝ)) := by
      rw [hcoefdef, abs_of_pos (by positivity)]
    rw [hcoefabs, hcard]
    -- bound the number of boxes
    have hbox : ∀ i, ((2 * N i + 1 : ℕ) : ℝ) ≤ (2 * R + 3) / δ ^ (s i) := by
      intro i
      have h1 : ((2 * N i + 1 : ℕ) : ℝ) = 2 * (N i : ℝ) + 1 := by push_cast; ring
      rw [h1]
      have h2 : (N i : ℝ) ≤ R / δ ^ (s i) + 1 := hNlt i
      have h3 : (2 : ℝ) * (N i : ℝ) + 1 ≤ 2 * (R / δ ^ (s i)) + 3 := by linarith
      have h4 : (2 : ℝ) * (R / δ ^ (s i)) + 3 ≤ (2 * R + 3) / δ ^ (s i) := by
        rw [le_div_iff₀ (hδpow i)]
        have hx : (2 * (R / δ ^ (s i)) + 3) * δ ^ (s i) = 2 * R + 3 * δ ^ (s i) := by
          field_simp
        rw [hx]
        nlinarith [hδpow1 i, hδpow i]
      linarith
    have hprod : ∏ i, ((2 * N i + 1 : ℕ) : ℝ) ≤ ∏ i, ((2 * R + 3) / δ ^ (s i)) := by
      apply Finset.prod_le_prod
      · intro i _
        positivity
      · intro i _
        exact hbox i
    have hprodeq : ∏ i, ((2 * R + 3) / δ ^ (s i)) = (2 * R + 3) ^ d / δ ^ (scaleDim s) := by
      rw [Finset.prod_div_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum]
      simp [scaleDim]
    have hδrpow : δ ^ ((scaleDim s : ℝ)) = δ ^ (scaleDim s) := by
      rw [← Real.rpow_natCast δ (scaleDim s)]
    rw [hδrpow]
    have hpos : (0:ℝ) < δ ^ (scaleDim s) := pow_pos hδ0 _
    calc (∏ i, ((2 * N i + 1 : ℕ) : ℝ)) * (Λ * δ ^ (scaleDim s))
        ≤ ((2 * R + 3) ^ d / δ ^ (scaleDim s)) * (Λ * δ ^ (scaleDim s)) := by
          apply mul_le_mul_of_nonneg_right (le_trans hprod (le_of_eq hprodeq))
          positivity
      _ = Λ * (2 * R + 3) ^ d := by field_simp
  · -- the decomposition identity
    intro y
    have hterm : ∀ j : Fin d → ℕ,
        coef * scaledTest s δ (center j) (eta j) y
          = φ y * ∏ i, chi (y i / δ ^ (s i) - ((j i : ℝ) - (N i : ℝ))) := by
      intro j
      have hz : ∀ i, (y i - center j i) / δ ^ (s i)
          = y i / δ ^ (s i) - ((j i : ℝ) - (N i : ℝ)) := by
        intro i
        rw [hcdef]
        field_simp
      set z : Pt d := fun i => (y i - center j i) / δ ^ (s i) with hzdef
      have hrec : center j + scaleCLM a z = y := by
        funext i
        rw [scaleCLM_apply]
        simp only [Pi.add_apply, hzdef, hadef]
        field_simp
        ring
      have hscaled : scaledTest s δ (center j) (eta j) y
          = δ ^ (-(scaleDim s : ℝ)) * eta j z := by
        rw [scaledTest]
      rw [hscaled, hcoefdef, hetadef]
      have hcancel : δ ^ ((scaleDim s : ℝ)) * δ ^ (-(scaleDim s : ℝ)) = 1 := by
        rw [← Real.rpow_add hδ0]
        simp
      have : Λ * δ ^ ((scaleDim s : ℝ)) * (δ ^ (-(scaleDim s : ℝ)) *
          ((φ (center j + scaleCLM a z) * bumpBox z) / Λ))
          = (δ ^ ((scaleDim s : ℝ)) * δ ^ (-(scaleDim s : ℝ))) *
            (Λ / Λ) * (φ (center j + scaleCLM a z) * bumpBox z) := by
        field_simp
      rw [this, hcancel, div_self hΛ0.ne', hrec]
      simp only [one_mul, bumpBox]
      congr 1
      refine Finset.prod_congr rfl (fun i _ => ?_)
      show chi ((y i - center j i) / δ ^ (s i)) = _
      rw [hz i]
    have hsum : ∑ i : Fin nn, coef * scaledTest s δ (center (e i)) (eta (e i)) y
        = ∑ j ∈ S, coef * scaledTest s δ (center j) (eta j) y := by
      rw [Fintype.sum_equiv e (fun i => coef * scaledTest s δ (center (e i)) (eta (e i)) y)
        (fun p : {x // x ∈ S} => coef * scaledTest s δ (center (p : Fin d → ℕ))
          (eta (p : Fin d → ℕ)) y) (fun i => rfl)]
      exact Finset.sum_attach S (fun j => coef * scaledTest s δ (center j) (eta j) y)
    rw [hsum]
    rw [Finset.sum_congr rfl (fun j _ => hterm j)]
    rw [← Finset.mul_sum]
    have hfactor : ∑ j ∈ S, ∏ i, chi (y i / δ ^ (s i) - ((j i : ℝ) - (N i : ℝ)))
        = ∏ i, ∑ k ∈ Finset.range (2 * N i + 1),
            chi (y i / δ ^ (s i) - ((k : ℝ) - (N i : ℝ))) := by
      rw [hSdef, Finset.prod_univ_sum]
    rw [hfactor]
    by_cases hy : φ y = 0
    · simp [hy]
    · have hbound : ∀ i, |y i / δ ^ (s i)| ≤ (N i : ℝ) := by
        intro i
        rw [abs_div, abs_of_pos (hδpow i)]
        calc |y i| / δ ^ (s i) ≤ R / δ ^ (s i) := by
              have hnum : |y i| ≤ R := hR y hy i
              gcongr
          _ ≤ (N i : ℝ) := hNge i
      have : ∏ i, ∑ k ∈ Finset.range (2 * N i + 1),
          chi (y i / δ ^ (s i) - ((k : ℝ) - (N i : ℝ))) = 1 := by
        apply Finset.prod_eq_one
        intro i _
        exact chi_sum_eq_one _ _ (hbound i)
      rw [this, mul_one]
