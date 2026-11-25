-- Prove2me | solution 1 for KallMayerSLP.NormalCC.theorem_2_5
-- status  : ACCEPTED   (prove)
-- author  : @ytako6706
-- created : 2026-11-25T07:40:47.4718+00:00
-- url     : https://prove2.me/submissions/dd3a23db-8ab9-4775-81dd-d72e270f6213

import Mathlib
import Definitions.Def_KallMayerSLP_NormalCC_IsMultivariateNormal
import Definitions.Def_KallMayerSLP_NormalCC_levelSet

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

/-- Part A1: law of `c * g` for a standard Gaussian `g`. -/
lemma kmA_map_const_mul {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {g : Ω → ℝ}
    (hg : Measurable g) (hlaw : P.map g = gaussianReal 0 1) (c : ℝ) :
    P.map (fun ω => c * g ω) = gaussianReal 0 ⟨c ^ 2, sq_nonneg c⟩ := by
  have : (fun ω => c * g ω) = (fun x => c * x) ∘ g := rfl
  rw [this, ← Measure.map_map (measurable_const_mul c) hg, hlaw, gaussianReal_map_const_mul]
  congr 1
  · ring
  · rw [mul_one]; rfl

/-- Part A2: a finite linear combination of independent standard Gaussians is Gaussian with
variance the sum of squared coefficients. -/
lemma kmA_map_finset_sum {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {s : ℕ} {g : Fin s → Ω → ℝ} (hg : ∀ j, Measurable (g j)) (hind : iIndepFun g P)
    (hlaw : ∀ j, P.map (g j) = gaussianReal 0 1) (c : Fin s → ℝ) (S : Finset (Fin s)) :
    P.map (fun ω => ∑ j ∈ S, c j * g j ω) =
      gaussianReal 0 ⟨∑ j ∈ S, c j ^ 2, Finset.sum_nonneg (fun j _ => sq_nonneg (c j))⟩ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [Measure.map_const, measure_univ, one_smul]
    exact (gaussianReal_zero_var (0 : ℝ)).symm
  | insert k S hk ih =>
    have hind' : iIndepFun (fun j ω => c j * g j ω) P :=
      hind.comp (fun j x => c j * x) (fun j => measurable_const_mul (c j))
    have hmeas : ∀ j, Measurable (fun ω => c j * g j ω) :=
      fun j => (hg j).const_mul (c j)
    have hI : IndepFun (∑ j ∈ S, fun ω => c j * g j ω) (fun ω => c k * g k ω) P :=
      hind'.indepFun_finsetSum_of_notMem hmeas hk
    have hsumfun : (∑ j ∈ S, fun ω => c j * g j ω) = fun ω => ∑ j ∈ S, c j * g j ω := by
      ext ω; simp [Finset.sum_apply]
    rw [hsumfun] at hI
    have h := gaussianReal_add_gaussianReal_of_indepFun hI ih (kmA_map_const_mul (hg k) (hlaw k) (c k))
    have hfun : (fun ω => ∑ j ∈ insert k S, c j * g j ω) =
        (fun ω => ∑ j ∈ S, c j * g j ω) + (fun ω => c k * g k ω) := by
      ext ω; simp [Finset.sum_insert hk, add_comm]
    rw [hfun, h]
    congr 1
    · ring
    · apply Subtype.ext
      change (∑ j ∈ S, c j ^ 2) + c k ^ 2 = ∑ j ∈ insert k S, c j ^ 2
      rw [Finset.sum_insert hk, add_comm]

/-- Part C1: an upper half-line `[c, ∞)` with `c > 0` has standard Gaussian mass `< 1/2`. -/
lemma kmC_Ici_lt_half {c : ℝ} (hc : 0 < c) : (gaussianReal 0 1).real (Set.Ici c) < 1 / 2 := by
  set γ := gaussianReal 0 1 with hγ
  have hsym : γ.real (Set.Iic (-c)) = γ.real (Set.Ici c) := by
    have hneg : γ.map (fun x => -x) = γ := by
      rw [hγ, gaussianReal_map_neg]; simp
    have : γ.real (Set.Ici c) = (γ.map (fun x => -x)).real (Set.Ici c) := by rw [hneg]
    rw [this, map_measureReal_apply measurable_neg measurableSet_Ici]
    congr 1
    ext x; simp [neg_le]
  have hpos : 0 < γ.real (Set.Ioo (-c) c) := by
    have hne : γ (Set.Ioo (-c) c) ≠ 0 := by
      intro h0
      have := gaussianReal_absolutelyContinuous' (0 : ℝ) (v := 1) one_ne_zero h0
      rw [Real.volume_Ioo] at this
      simp at this
      linarith
    exact ENNReal.toReal_pos hne (measure_ne_top _ _)
  have hsplit : γ.real (Set.Iic (-c)) + γ.real (Set.Ioo (-c) c) + γ.real (Set.Ici c) = 1 := by
    have h1 : Set.Iic (-c) ∪ Set.Ioo (-c) c = Set.Iio c := by
      ext x; simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ioo, Set.mem_Iio]
      constructor
      · rintro (h | h) <;> [linarith; exact h.2]
      · intro h; by_cases hx : x ≤ -c
        · exact Or.inl hx
        · exact Or.inr ⟨by linarith, h⟩
    rw [← measureReal_union (Set.disjoint_left.mpr fun x hx hx' => by
          simp only [Set.mem_Iic, Set.mem_Ioo] at hx hx'; linarith) measurableSet_Ioo, h1,
      ← measureReal_union (Set.disjoint_left.mpr fun x hx hx' => by
          simp only [Set.mem_Iio, Set.mem_Ici] at hx hx'; linarith) measurableSet_Ici,
      Set.Iio_union_Ici, probReal_univ]
  linarith

/-- The event `{z | 0 ≤ b + σ z}`. -/
def kmA (b σ : ℝ) : Set ℝ := {z | 0 ≤ b + σ * z}

/-- Part C2: if the standard Gaussian mass of `{0 ≤ b + σ z}` is at least `1/2`, then `b ≥ 0`. -/
lemma kmC_nonneg {b σ : ℝ} (hσ : 0 ≤ σ) (h : 1 / 2 ≤ (gaussianReal 0 1).real (kmA b σ)) :
    0 ≤ b := by
  by_contra hb
  push_neg at hb
  rcases hσ.lt_or_eq with hσ | hσ
  · have hsub : kmA b σ ⊆ Set.Ici (-b / σ) := by
      intro z hz
      simp only [kmA, Set.mem_setOf_eq] at hz
      simp only [Set.mem_Ici]
      rw [div_le_iff₀ hσ]; linarith
    have h2 := measureReal_mono hsub (μ := gaussianReal 0 1)
    have h3 := kmC_Ici_lt_half (c := -b / σ) (div_pos (by linarith) hσ)
    linarith
  · have hempty : kmA b σ = ∅ := by
      ext z; simp only [kmA, ← hσ, zero_mul, add_zero, Set.mem_setOf_eq,
        Set.mem_empty_iff_false, iff_false, not_le]; exact hb
    rw [hempty] at h; simp at h; linarith

/-- Part C3: the convexity step. -/
lemma kmC_convex_step {b₀ b₁ σ₀ σ₁ σ a c α : ℝ} (h₀ : 0 ≤ σ₀) (h₁ : 0 ≤ σ₁) (hσ : 0 ≤ σ)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hac : a + c = 1) (hσle : σ ≤ a * σ₀ + c * σ₁)
    (hα : 1 / 2 ≤ α)
    (hx₀ : α ≤ (gaussianReal 0 1).real (kmA b₀ σ₀))
    (hx₁ : α ≤ (gaussianReal 0 1).real (kmA b₁ σ₁)) :
    α ≤ (gaussianReal 0 1).real (kmA (a * b₀ + c * b₁) σ) := by
  have hb₀ := kmC_nonneg h₀ (hα.trans hx₀)
  have hb₁ := kmC_nonneg h₁ (hα.trans hx₁)
  have hup : ∀ {b s : ℝ}, 0 ≤ s → IsUpperSet (kmA b s) := by
    intro b s hs x y hxy hx
    simp only [kmA, Set.mem_setOf_eq] at hx ⊢
    nlinarith
  have hinter : kmA b₀ σ₀ ∩ kmA b₁ σ₁ ⊆ kmA (a * b₀ + c * b₁) σ := by
    intro z ⟨hz₀, hz₁⟩
    simp only [kmA, Set.mem_setOf_eq] at hz₀ hz₁ ⊢
    rcases le_or_gt 0 z with hz | hz
    · nlinarith
    · nlinarith
  refine le_trans ?_ (measureReal_mono hinter)
  rcases (hup h₀ (b := b₀)).total (hup h₁ (b := b₁)) with hs | hs
  · rw [Set.inter_eq_left.mpr hs]; exact hx₀
  · rw [Set.inter_eq_right.mpr hs]; exact hx₁

/-- Part B1: `(u, v) ⬝ (x, -1) = u ⬝ x - v`. -/
lemma kmB_snoc_dot {n : ℕ} (u x : Fin n → ℝ) (v : ℝ) :
    (Fin.snoc (α := fun _ => ℝ) u v) ⬝ᵥ (Fin.snoc (α := fun _ => ℝ) x (-1)) = u ⬝ᵥ x - v := by
  simp [dotProduct, Fin.sum_univ_castSucc]
  ring

/-- Part B2: the standard Gaussian mass of `{0 ≤ z + d}` under `N(0, σ²)` is that of
`{0 ≤ d + σ z}` under `N(0,1)`. -/
lemma kmB_gauss_rescale (d σ : ℝ) (hσ : 0 ≤ σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) :
    (gaussianReal 0 v).real {z | 0 ≤ z + d} = (gaussianReal 0 1).real (kmA d σ) := by
  have h := gaussianReal_map_const_mul (μ := 0) (v := 1) σ
  have h' : (gaussianReal 0 1).map (fun x => σ * x) = gaussianReal 0 v := by
    rw [h, mul_zero]
    congr 1
    exact NNReal.eq (by simp [hv])
  have hm : MeasurableSet {z : ℝ | 0 ≤ z + d} :=
    measurableSet_le measurable_const (measurable_id.add_const _)
  rw [← h', map_measureReal_apply (measurable_const_mul σ) hm]
  congr 1
  ext z; simp [kmA, add_comm]

theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (η : Ω → Fin n → ℝ) (ξ : Ω → ℝ)
    (hζ : KallMayerSLP.NormalCC.IsMultivariateNormal P
      (fun ω => Fin.snoc (α := fun _ => ℝ) (η ω) (ξ ω)))
    (α : ℝ) (hα : 1 / 2 ≤ α) :
    Convex ℝ (KallMayerSLP.NormalCC.levelSet P η ξ α) := by
  obtain ⟨s, B, μ, g, ⟨hgm, hind, hlaw⟩, hae⟩ := hζ
  set w : (Fin n → ℝ) → Fin (n + 1) → ℝ := fun x => Fin.snoc (α := fun _ => ℝ) x (-1) with hw
  set cf : (Fin n → ℝ) → Fin s → ℝ := fun x => w x ᵥ* B with hcf
  set df : (Fin n → ℝ) → ℝ := fun x => μ ⬝ᵥ w x with hdf
  set σf : (Fin n → ℝ) → ℝ := fun x => Real.sqrt (∑ j, cf x j ^ 2) with hσf
  have hkey : ∀ x, KallMayerSLP.NormalCC.probFun P η ξ x =
      (gaussianReal 0 1).real (kmA (df x) (σf x)) := by
    intro x
    set S : Ω → ℝ := fun ω => ∑ j ∈ Finset.univ, cf x j * g j ω with hS
    have hSm : Measurable S := Finset.measurable_sum _ (fun j _ => (hgm j).const_mul _)
    have hrep : ∀ᵐ ω ∂P, η ω ⬝ᵥ x - ξ ω = S ω + df x := by
      filter_upwards [hae] with ω hω
      rw [← kmB_snoc_dot, hω, add_dotProduct, dotProduct_comm, dotProduct_mulVec]
      simp [hS, hdf, hcf, dotProduct, hw]
    have hset : {ω | 0 ≤ η ω ⬝ᵥ x - ξ ω} =ᵐ[P] {ω | 0 ≤ S ω + df x} := by
      filter_upwards [hrep] with ω hω
      change (0 ≤ η ω ⬝ᵥ x - ξ ω) = (0 ≤ S ω + df x)
      rw [hω]
    unfold KallMayerSLP.NormalCC.probFun
    rw [measureReal_congr hset]
    have hpre : {ω | 0 ≤ S ω + df x} = S ⁻¹' {z | 0 ≤ z + df x} := rfl
    have hmS : MeasurableSet {z : ℝ | 0 ≤ z + df x} :=
      measurableSet_le measurable_const (measurable_id.add_const _)
    rw [hpre, ← map_measureReal_apply hSm hmS, hS, kmA_map_finset_sum hgm hind hlaw (cf x) Finset.univ]
    exact kmB_gauss_rescale (df x) (σf x) (Real.sqrt_nonneg _) _
      (by simp [hσf, Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg (cf x j)))]; rfl)
  intro x₀ hx₀ x₁ hx₁ a c ha hc hac
  simp only [KallMayerSLP.NormalCC.levelSet, Set.mem_setOf_eq, hkey] at hx₀ hx₁ ⊢
  have hwlin : w (a • x₀ + c • x₁) = a • w x₀ + c • w x₁ := by
    funext i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simp [hw]; linarith
    · simp [hw]
  have hclin : cf (a • x₀ + c • x₁) = a • cf x₀ + c • cf x₁ := by
    funext j
    simp only [hcf, hwlin, vecMul, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      add_mul, Finset.sum_add_distrib, mul_assoc, Finset.mul_sum]
  have hdlin : df (a • x₀ + c • x₁) = a * df x₀ + c * df x₁ := by
    simp only [hdf, hwlin, dotProduct_add, dotProduct_smul, smul_eq_mul]
  have hnorm : ∀ y : Fin s → ℝ, Real.sqrt (∑ j, y j ^ 2) = ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin s))‖ := by
    intro y
    rw [EuclideanSpace.norm_eq]
    simp [Real.norm_eq_abs, sq_abs]
  have hσlin : σf (a • x₀ + c • x₁) ≤ a * σf x₀ + c * σf x₁ := by
    simp only [hσf, hnorm, hclin]
    rw [WithLp.toLp_add, WithLp.toLp_smul, WithLp.toLp_smul]
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hc]
  rw [hdlin]
  exact kmC_convex_step (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    ha hc hac hσlin hα hx₀ hx₁
