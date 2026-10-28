-- Prove2me | solution 1 for OAI.ScalarConductivity.finite_field_scalarization
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:25:00.282514+00:00
-- url     : https://prove2.me/submissions/933a83d7-0551-432b-a2e9-3d0da2b4e5a3

import Mathlib
import Definitions.Def_OAIQ059C008
import Theorems.Thm_OAI_ScalarConductivity_fine_global_scalar_tensor_approximation

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_VariationalDN
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

lemma convexComb_lt {θ η x y z : ℝ} (hθ : 0 ≤ θ) (hη : 0 ≤ η)
    (hsum : θ + η = 1) (hx : x < z) (hy : y < z) : θ * x + η * y < z := by
  rcases eq_or_lt_of_le hθ with h | h
  · subst θ
    have : η = 1 := by simpa using hsum
    simpa [this] using hy
  · calc
      θ * x + η * y < θ * z + η * z :=
        add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hx h)
          (mul_le_mul_of_nonneg_left hy.le hη)
      _ = z := by rw [← add_mul, hsum, one_mul]

lemma lt_convexComb {θ η x y z : ℝ} (hθ : 0 ≤ θ) (hη : 0 ≤ η)
    (hsum : θ + η = 1) (hx : z < x) (hy : z < y) : z < θ * x + η * y := by
  have hh := convexComb_lt hθ hη hsum (neg_lt_neg hx) (neg_lt_neg hy)
  nlinarith

lemma harmonic_mean_bounds {a b x y θ : ℝ} (ha : 0 < a)
    (hx : a < x ∧ x < b) (hy : a < y ∧ y < b) (hθ : 0 ≤ θ ∧ θ ≤ 1) :
    a < (θ / x + (1 - θ) / y)⁻¹ ∧ (θ / x + (1 - θ) / y)⁻¹ < b := by
  have hx0 : 0 < x := lt_trans ha hx.1
  have hy0 : 0 < y := lt_trans ha hy.1
  have hb : 0 < b := lt_trans hx0 hx.2
  have hs : 0 < θ / x + (1 - θ) / y := by
    rcases lt_or_eq_of_le hθ.1 with hθ0 | rfl
    · exact add_pos_of_pos_of_nonneg (div_pos hθ0 hx0) (div_nonneg (sub_nonneg.mpr hθ.2) hy0.le)
    · simp [hy0]
  have hl : θ / x + (1 - θ) / y < a⁻¹ := by
    have hxi : x⁻¹ < a⁻¹ := (inv_lt_inv₀ hx0 ha).2 hx.1
    have hyi : y⁻¹ < a⁻¹ := (inv_lt_inv₀ hy0 ha).2 hy.1
    have he := convexComb_lt hθ.1 (sub_nonneg.mpr hθ.2) (by ring : θ + (1-θ) = 1) hxi hyi
    simpa [div_eq_mul_inv] using he
  have hu : b⁻¹ < θ / x + (1 - θ) / y := by
    have hxi : b⁻¹ < x⁻¹ := (inv_lt_inv₀ hb hx0).2 hx.2
    have hyi : b⁻¹ < y⁻¹ := (inv_lt_inv₀ hb hy0).2 hy.2
    have he := lt_convexComb hθ.1 (sub_nonneg.mpr hθ.2) (by ring : θ + (1-θ) = 1) hxi hyi
    simpa [div_eq_mul_inv] using he
  constructor
  · have hh := (inv_lt_inv₀ (inv_pos.mpr ha) hs).2 hl
    simpa using hh
  · have hh := (inv_lt_inv₀ hs (inv_pos.mpr hb)).2 hu
    simpa using hh

lemma coordinateJoin_bounds {a b : ℝ} (ha : 0 < a) {α β : DiagonalTriple}
    (hα : ∀ j, a < α j ∧ α j < b) (hβ : ∀ j, a < β j ∧ β j < b)
    (i : Fin 3) {θ : ℝ} (hθ : 0 ≤ θ ∧ θ ≤ 1) :
    ∀ j, a < coordinateJoin i θ α β j ∧ coordinateJoin i θ α β j < b := by
  intro j
  by_cases hji : j = i
  · simpa [coordinateJoin, hji] using harmonic_mean_bounds ha (hα j) (hβ j) hθ
  · simp only [coordinateJoin, ite_eq_right hji]
    constructor
    · have he := lt_convexComb hθ.1 (sub_nonneg.mpr hθ.2)
        (by ring : θ + (1-θ) = 1) (hα j).1 (hβ j).1
      simpa using he
    · have he := convexComb_lt hθ.1 (sub_nonneg.mpr hθ.2)
        (by ring : θ + (1-θ) = 1) (hα j).2 (hβ j).2
      simpa using he

lemma IsFiniteLaminate.bounds {a b : ℝ} (ha : 0 < a) {α : DiagonalTriple}
    (h : IsFiniteLaminate a b α) : ∀ j, a < α j ∧ α j < b := by
  induction h with
  | scalar s has hsb => exact fun _ => ⟨has, hsb⟩
  | join i θ hθ₀ hθ₁ hα hβ ihα ihβ =>
    exact coordinateJoin_bounds ha ihα ihβ i ⟨hθ₀, hθ₁⟩

lemma half_harmonic_eq_mul {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x + y = 2) : ((1 / 2 : ℝ) / x + (1 - 1 / 2) / y)⁻¹ = x * y := by
  have h : (1 / 2 : ℝ) / x + (1 - 1 / 2) / y = (x * y)⁻¹ := by
    field_simp
    nlinarith
  rw [h, inv_inv]

lemma coordinateJoin_half_smul (i : Fin 3) (v : DiagonalTriple) {x y : ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y = 2) :
    coordinateJoin i (1/2) (x • v) (y • v) =
      fun j => if j = i then x * y * v j else v j := by
  ext j
  by_cases hji : j = i
  · simp only [coordinateJoin, hji, ite_true, Pi.smul_apply, smul_eq_mul]
    have hden : (1 / 2 : ℝ) / (x * v j) + (1 - 1 / 2) / (y * v j) =
        ((1 / 2 : ℝ) / x + (1 - 1 / 2) / y) / v j := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [hji] at hden
    rw [hden, div_eq_mul_inv, mul_inv_rev, inv_inv, half_harmonic_eq_mul hx hy hxy]
    ring
  · simp only [coordinateJoin, hji, ite_false, Pi.smul_apply, smul_eq_mul]
    calc
      (1 / 2 : ℝ) * (x * v j) + (1 - 1 / 2) * (y * v j) = (x + y) / 2 * v j := by ring
      _ = v j := by rw [hxy]; ring

lemma productFactor_spec {M : ℝ} (hM : 0 < M) (α : DiagonalTriple) (i : Fin 3)
    (hα : 0 < α i ∧ α i < M) :
    0 < productFactorMinus M α i ∧ 0 < productFactorPlus M α i ∧
    productFactorMinus M α i + productFactorPlus M α i = 2 ∧
    productFactorMinus M α i * productFactorPlus M α i = α i / M := by
  have hq : 0 < α i / M := div_pos hα.1 hM
  have hq1 : α i / M < 1 := (div_lt_one hM).2 hα.2
  have hs0 := Real.sqrt_nonneg (1 - α i / M)
  have hs2 := Real.sq_sqrt (show 0 ≤ 1 - α i / M by linarith)
  dsimp [productFactorMinus, productFactorPlus]
  constructor
  · nlinarith
  constructor
  · linarith
  constructor
  · ring
  · nlinarith

lemma IsFiniteLaminate.half_smul {a b : ℝ} (i : Fin 3) (v : DiagonalTriple)
    {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y = 2)
    (hxl : IsFiniteLaminate a b (x • v)) (hyl : IsFiniteLaminate a b (y • v)) :
    IsFiniteLaminate a b (fun j => if j = i then x * y * v j else v j) := by
  rw [← coordinateJoin_half_smul i v hx hy hxy]
  exact IsFiniteLaminate.join i (1/2) (by norm_num) (by norm_num) hxl hyl

theorem product_eight_leaf_laminate {a b M : ℝ} (x y : Fin 3 → ℝ)
    (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0) (hsum : ∀ i, x i + y i = 2)
    (hleaf : ∀ t₀ t₁ t₂ : ℝ, (t₀ = x 0 ∨ t₀ = y 0) →
      (t₁ = x 1 ∨ t₁ = y 1) → (t₂ = x 2 ∨ t₂ = y 2) →
      a < M * t₀ * t₁ * t₂ ∧ M * t₀ * t₁ * t₂ < b) :
    IsFiniteLaminate a b (fun i => M * x i * y i) := by
  have h₀ (t₁ t₂ : ℝ) (ht₁ : t₁ = x 1 ∨ t₁ = y 1)
      (ht₂ : t₂ = x 2 ∨ t₂ = y 2) :
      IsFiniteLaminate a b ![M * x 0 * y 0 * t₁ * t₂, M * t₁ * t₂, M * t₁ * t₂] := by
    let v : DiagonalTriple := fun _ => M * t₁ * t₂
    have hp : IsFiniteLaminate a b (x 0 • v) := by
      have hh := hleaf (x 0) t₁ t₂ (Or.inl rfl) ht₁ ht₂
      change IsFiniteLaminate a b (fun _ => x 0 * (M * t₁ * t₂))
      convert IsFiniteLaminate.scalar (M * x 0 * t₁ * t₂) hh.1 hh.2 using 1
      all_goals try with_reducible_and_instances rfl
      ext j
      ring
    have hm : IsFiniteLaminate a b (y 0 • v) := by
      have hh := hleaf (y 0) t₁ t₂ (Or.inr rfl) ht₁ ht₂
      change IsFiniteLaminate a b (fun _ => y 0 * (M * t₁ * t₂))
      convert IsFiniteLaminate.scalar (M * y 0 * t₁ * t₂) hh.1 hh.2 using 1
      all_goals try with_reducible_and_instances rfl
      ext j
      ring
    convert IsFiniteLaminate.half_smul 0 v (hx 0) (hy 0) (hsum 0) hp hm using 1
    all_goals try with_reducible_and_instances rfl
    ext j
    fin_cases j <;> simp [v, mul_assoc, mul_comm, mul_left_comm]
  have h₁ (t₂ : ℝ) (ht₂ : t₂ = x 2 ∨ t₂ = y 2) :
      IsFiniteLaminate a b ![M * x 0 * y 0 * t₂, M * x 1 * y 1 * t₂, M * t₂] := by
    let v : DiagonalTriple := ![M * x 0 * y 0 * t₂, M * t₂, M * t₂]
    have hp : IsFiniteLaminate a b (x 1 • v) := by
      convert h₀ (x 1) t₂ (Or.inl rfl) ht₂ using 1
      all_goals try with_reducible_and_instances rfl
      ext j
      fin_cases j <;> simp [v, mul_assoc, mul_comm, mul_left_comm]
    have hm : IsFiniteLaminate a b (y 1 • v) := by
      convert h₀ (y 1) t₂ (Or.inr rfl) ht₂ using 1
      all_goals try with_reducible_and_instances rfl
      ext j
      fin_cases j <;> simp [v, mul_assoc, mul_comm, mul_left_comm]
    convert IsFiniteLaminate.half_smul 1 v (hx 1) (hy 1) (hsum 1) hp hm using 1
    all_goals try with_reducible_and_instances rfl
    ext j
    fin_cases j <;> simp [v, mul_assoc, mul_comm, mul_left_comm]
  let v : DiagonalTriple := ![M * x 0 * y 0, M * x 1 * y 1, M]
  have hp : IsFiniteLaminate a b (x 2 • v) := by
    convert h₁ (x 2) (Or.inl rfl) using 1
    all_goals try with_reducible_and_instances rfl
    ext j
    fin_cases j <;> simp [v, mul_assoc, mul_comm, mul_left_comm]
  have hm : IsFiniteLaminate a b (y 2 • v) := by
    convert h₁ (y 2) (Or.inr rfl) using 1
    all_goals try with_reducible_and_instances rfl
    ext j
    fin_cases j <;> simp [v, mul_assoc, mul_comm, mul_left_comm]
  convert IsFiniteLaminate.half_smul 2 v (hx 2) (hy 2) (hsum 2) hp hm using 1
  all_goals try with_reducible_and_instances rfl
  ext j
  fin_cases j <;> simp [v, mul_comm, mul_left_comm]

theorem uniform_laminate_coverage {c C : ℝ} (hc : 0 < c) (hcC : c ≤ C) :
    0 < laminateLower c C ∧ laminateLower c C < laminateUpper C ∧
    ∀ α : DiagonalTriple, (∀ i, c ≤ α i ∧ α i ≤ C) →
      IsFiniteLaminate (laminateLower c C) (laminateUpper C) α := by
  let M := 2 * C
  let ℓ := 1 - Real.sqrt (1 - c / M)
  have hC : 0 < C := lt_of_lt_of_le hc hcC
  have hM : 0 < M := by dsimp [M]; positivity
  have hcM : c < M := by dsimp [M]; linarith
  have hℓ : 0 < ℓ :=
    (productFactor_spec hM (fun _ => c) 0 ⟨hc, hcM⟩).1
  have hℓ1 : ℓ ≤ 1 := by dsimp [ℓ]; linarith [Real.sqrt_nonneg (1 - c / M)]
  have hℓ3 : ℓ ^ 3 ≤ 1 := by
    calc ℓ ^ 3 ≤ 1 ^ 3 := pow_le_pow_left₀ hℓ.le hℓ1 3
         _ = 1 := by norm_num
  have hbase : 0 < M * ℓ ^ 3 := mul_pos hM (pow_pos hℓ 3)
  change 0 < M * ℓ ^ 3 / 2 ∧ M * ℓ ^ 3 / 2 < 16 * M ∧ _
  refine ⟨by positivity, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hℓ3 hM.le]
  intro α hα
  let x := productFactorMinus M α
  let y := productFactorPlus M α
  have hspec (i : Fin 3) : 0 < x i ∧ 0 < y i ∧ x i + y i = 2 ∧ x i * y i = α i / M := by
    apply productFactor_spec hM α i
    constructor
    · exact lt_of_lt_of_le hc (hα i).1
    · dsimp [M]
      linarith [(hα i).2]
  have hx (i : Fin 3) : ℓ ≤ x i ∧ x i ≤ 2 := by
    dsimp [ℓ, x, productFactorMinus]
    constructor
    · have hh : 1 - α i / M ≤ 1 - c / M := by
        linarith [div_le_div_of_nonneg_right (hα i).1 hM.le]
      linarith [Real.sqrt_le_sqrt hh]
    · linarith [Real.sqrt_nonneg (1 - α i / M)]
  have hy (i : Fin 3) : ℓ ≤ y i ∧ y i ≤ 2 := by
    constructor
    · calc ℓ ≤ 1 := hℓ1
           _ ≤ y i := by
             dsimp [y, productFactorPlus]
             linarith [Real.sqrt_nonneg (1 - α i / M)]
    · have hs := hspec i
      linarith [hs.1, hs.2.2.1]
  have heq : (fun i => M * x i * y i) = α := by
    ext i
    rw [mul_assoc, (hspec i).2.2.2]
    exact mul_div_cancel₀ _ hM.ne'
  rw [← heq]
  apply product_eight_leaf_laminate x y (fun i => (hspec i).1.ne')
    (fun i => (hspec i).2.1.ne') (fun i => (hspec i).2.2.1)
  intro t₀ t₁ t₂ ht₀ ht₁ ht₂
  have hb₀ : ℓ ≤ t₀ ∧ t₀ ≤ 2 := ht₀.elim (fun h => h ▸ hx 0) (fun h => h ▸ hy 0)
  have hb₁ : ℓ ≤ t₁ ∧ t₁ ≤ 2 := ht₁.elim (fun h => h ▸ hx 1) (fun h => h ▸ hy 1)
  have hb₂ : ℓ ≤ t₂ ∧ t₂ ≤ 2 := ht₂.elim (fun h => h ▸ hx 2) (fun h => h ▸ hy 2)
  have ht₀0 : 0 ≤ t₀ := hℓ.le.trans hb₀.1
  have ht₁0 : 0 ≤ t₁ := hℓ.le.trans hb₁.1
  have ht₂0 : 0 ≤ t₂ := hℓ.le.trans hb₂.1
  have hlo : M * ℓ ^ 3 ≤ M * t₀ * t₁ * t₂ := by
    calc M * ℓ ^ 3 = M * ℓ * ℓ * ℓ := by ring
         _ ≤ M * t₀ * t₁ * t₂ := by gcongr <;> linarith
  have hhi : M * t₀ * t₁ * t₂ ≤ 8 * M := by
    calc M * t₀ * t₁ * t₂ ≤ M * 2 * 2 * 2 := by gcongr <;> linarith
         _ = 8 * M := by ring
  change M * ℓ ^ 3 / 2 < M * t₀ * t₁ * t₂ ∧ M * t₀ * t₁ * t₂ < 16 * M
  constructor <;> nlinarith

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PreliminaryQ
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology

lemma exists_orthogonal_diagonalization {A : Mat3} (hA : A.IsHermitian) :
    ∃ Q ∈ orthogonalFrames, ∃ α : Fin 3 → ℝ, A = Q * diagonal α * Qᵀ := by
  refine ⟨hA.eigenvectorUnitary, ⟨?_, ?_⟩, hA.eigenvalues, ?_⟩
  · simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_star_mul_self hA.eigenvectorUnitary
  · simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      Unitary.coe_star] using Unitary.coe_mul_star_self hA.eigenvectorUnitary
  · simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id,
      Function.id_comp] using hA.spectral_theorem

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_SymmetricCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

open Filter Topology Set TopologicalSpace

theorem dense_continuityPoints_of_closed_ball_preimages
    {X Y : Type*} [TopologicalSpace X] [BaireSpace X]
    [PseudoMetricSpace Y] [SeparableSpace Y] [Nonempty Y]
    (f : X → Y)
    (hclosed : ∀ y r, IsClosed (f ⁻¹' Metric.closedBall y r)) :
    Dense {x | ContinuousAt f x} := by
  let q : ℕ → Y := denseSeq Y
  have hq : DenseRange q := denseRange_denseSeq Y
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hr : ∀ n, 0 < r n := fun n => div_pos zero_lt_one (Nat.cast_add_one_pos n)
  let V : ℕ → Set X := fun n => ⋃ k, interior (f ⁻¹' Metric.closedBall (q k) (r n))
  have hVo : ∀ n, IsOpen (V n) := fun _ => isOpen_iUnion fun _ => isOpen_interior
  have hVd : ∀ n, Dense (V n) := by
    intro n
    apply dense_iUnion_interior_of_closed (fun k => hclosed (q k) (r n))
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨k, hk⟩ := hq.exists_dist_lt (f x) (hr n)
    exact Set.mem_iUnion.mpr ⟨k, hk.le⟩
  refine (dense_iInter_of_isOpen_nat hVo hVd).mono ?_
  intro x hx
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hε)
  have hrε : 2 * r n < ε := by dsimp only [r]; linarith
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (Set.mem_iInter.mp hx n)
  have hxf : dist (f x) (q k) ≤ r n :=
    interior_subset (s := f ⁻¹' Metric.closedBall (q k) (r n)) hk
  filter_upwards [isOpen_interior.mem_nhds hk] with y hy
  have hyf : dist (f y) (q k) ≤ r n :=
    interior_subset (s := f ⁻¹' Metric.closedBall (q k) (r n)) hy
  calc
    dist (f y) (f x) ≤ dist (f y) (q k) + dist (q k) (f x) := dist_triangle _ _ _
    _ ≤ r n + r n := add_le_add hyf (by rwa [dist_comm])
    _ < ε := by linarith

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_TwoFluxColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

theorem smooth_integration_by_parts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (v : E) (f g : SmoothScalar E) (hf : HasCompactSupport f.val) :
    (∫ x, f.val x * (smoothDirection v g).val x ∂μ) =
      -(∫ x, (smoothDirection v f).val x * g.val x ∂μ) := by
  have hc (a b : SmoothScalar E) (ha : HasCompactSupport a.val) :
      Integrable (fun x => a.val x * b.val x) μ :=
    ((smoothScalar_contDiff a).continuous.mul (smoothScalar_contDiff b).continuous).integrable_of_hasCompactSupport ha.mul_right
  exact integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ ℝ)
    (hc (smoothDirection v f) g (compactSupport_smoothDirection v hf))
    (hc f (smoothDirection v g) hf) (hc f g hf)
    (fun x _ => ((smoothScalar_contDiff f).differentiable (by simp) x).hasFDerivAt)
    (fun x _ => ((smoothScalar_contDiff g).differentiable (by simp) x).hasFDerivAt)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_SmoothFluxIntegrable
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise ENNReal

lemma CompactGlobalUpdate.preserves_harmonic
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A)
    (hint : SmoothFluxIntegrable μ U (conductivityFlux u A))
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0) :
    SmoothFluxIntegrable μ U (conductivityFlux (fun x => u x+R.du x) R.tensor) ∧
    ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux (fun x => u x+R.du x) R.tensor x).col j) ∂μ) = 0 := by
  have he : ∀ j (ψ : Coord3 → ℝ),
      (fun x => fderiv ℝ ψ x ((conductivityFlux (fun x => u x+R.du x) R.tensor x).col j)) =
      (fun x => fderiv ℝ ψ x ((conductivityFlux u A x).col j) + fderiv ℝ ψ x ((R.dF x).col j)) := by
    intro j ψ
    funext x
    rw [R.constitutive x]
    change fderiv ℝ ψ x (((conductivityFlux u A x).col j) + (R.dF x).col j) = _
    exact map_add _ _ _
  constructor
  · intro j ψ hψ hc hs
    rw [he]
    exact (hint j ψ hψ hc hs).add (smooth_flux_integrable_pairing μ
      (fun x => (R.dF x).col j) (smooth_matrix_column R.smooth_dF j).continuous (compact_matrix_column R.compact_dF j) ψ hψ)
  · intro j ψ hψ hc hs
    rw [he,integral_add (hint j ψ hψ hc hs) (smooth_flux_integrable_pairing μ
      (fun x => (R.dF x).col j) (smooth_matrix_column R.smooth_dF j).continuous (compact_matrix_column R.compact_dF j) ψ hψ),
      hdiv j ψ hψ hc hs,R.cauchy_dF j ψ hψ,add_zero]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_LpEllipticBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open MeasureTheory Set Filter Topology
open scoped ENNReal

lemma Lp_elliptic_bounds
    {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure X) (E F : Lp V 2 μ) {a b : ℝ} (_ha : 0 < a) (hb : 0 ≤ b)
    (h : ∀ᵐ x ∂μ, a * ‖E x‖^2 ≤ inner ℝ (E x) (F x) ∧
      ‖F x‖^2 ≤ b^2 * ‖E x‖^2) :
    a * ‖E‖^2 ≤ inner ℝ E F ∧ ‖F‖ ≤ b * ‖E‖ := by
  constructor
  · rw [← real_inner_self_eq_norm_sq,L2.inner_def,L2.inner_def,← integral_const_mul]
    apply integral_mono_ae ((L2.integrable_inner E E).const_mul a) (L2.integrable_inner E F)
    filter_upwards [h] with x hx
    simpa only [real_inner_self_eq_norm_sq] using hx.1
  · have hn : ∀ᵐ x ∂μ, ‖F x‖ ≤ ‖b • E x‖ := by
      filter_upwards [h] with x hx
      rw [norm_smul,Real.norm_of_nonneg hb]
      nlinarith [norm_nonneg (F x), norm_nonneg (E x),mul_nonneg hb (norm_nonneg (E x))]
    have hLp : ∀ᵐ x ∂μ, ‖F x‖ ≤ ‖(b • E : Lp V 2 μ) x‖ := by
      filter_upwards [hn,Lp.coeFn_smul b E] with x hx hy
      simpa only [hy,Pi.smul_apply] using hx
    have hp := Lp.norm_le_norm_of_ae_le hLp
    simpa only [norm_smul,Real.norm_of_nonneg hb] using hp

lemma elliptic_energy_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (E F E₀ : H) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hell : a * ‖E‖^2 ≤ inner ℝ E F) (hflux : ‖F‖ ≤ b * ‖E‖)
    (horth : inner ℝ (E-E₀) F = 0) :
    ‖E‖ ≤ (b/a) * ‖E₀‖ ∧ ‖F‖ ≤ (b^2/a) * ‖E₀‖ := by
  have he : inner ℝ E F = inner ℝ E₀ F := by
    rw [inner_sub_left] at horth
    linarith
  have hi : a * ‖E‖^2 ≤ ‖E₀‖ * (b * ‖E‖) := by
    calc
      _ ≤ inner ℝ E₀ F := he ▸ hell
      _ ≤ ‖E₀‖ * ‖F‖ := real_inner_le_norm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hflux (norm_nonneg _)
  have hbound : ‖E‖ ≤ (b/a) * ‖E₀‖ := by
    by_cases hz : ‖E‖ = 0
    · rw [hz]; positivity
    · have hp : 0 < ‖E‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      have hh : a * ‖E‖ ≤ b * ‖E₀‖ := by nlinarith
      have hd : ‖E‖ ≤ (b * ‖E₀‖) / a := (le_div_iff₀ ha).mpr (by nlinarith)
      convert hd using 1 <;> first | rfl | ring
  refine ⟨hbound,hflux.trans ?_⟩
  calc
    _ ≤ b * ((b/a)*‖E₀‖) := mul_le_mul_of_nonneg_left hbound hb
    _ = (b^2/a)*‖E₀‖ := by ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_FieldVector
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix Set MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise

lemma orthogonal_dotProduct {Q : Mat3} (hQ : Q ∈ orthogonalFrames) (v w : Coord3) :
    (Q *ᵥ v) ⬝ᵥ (Q *ᵥ w) = v ⬝ᵥ w := by
  rw [show Q = Qᵀᵀ by simp, dotProduct_transpose_mulVec]
  rw [transpose_transpose, mulVec_mulVec, hQ.1, one_mulVec]
  exact dotProduct_comm _ _

lemma conjugateDiagonal_quadratic (Q : Mat3) (d : DiagonalTriple) (v : Coord3) :
    v ⬝ᵥ ((Q * diagonal d * Qᵀ) *ᵥ v) =
      ∑ i, d i * (Qᵀ *ᵥ v) i ^ 2 := by
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  rw [show Q = Qᵀᵀ by simp, dotProduct_transpose_mulVec]
  simp only [transpose_transpose, mulVec_diagonal, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma matrixFiniteLaminate_quadratic_bounds {a b : ℝ} (ha : 0 < a)
    {A : Symmetric3} (hA : A ∈ matrixFiniteLaminate a b) (v : Coord3) :
    a * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A.val *ᵥ v) ∧
      v ⬝ᵥ (A.val *ᵥ v) ≤ b * (v ⬝ᵥ v) := by
  obtain ⟨Q,hQ,d,hd,he⟩ := hA
  have hsq : ∑ i, (Qᵀ *ᵥ v) i ^ 2 = v ⬝ᵥ v := by
    simpa only [dotProduct,pow_two] using orthogonal_dotProduct ⟨by simpa using hQ.2,by simpa using hQ.1⟩ v v
  rw [he,conjugateDiagonal_quadratic,← hsq]
  constructor
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hd.bounds ha i).1.le (sq_nonneg _)
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hd.bounds ha i).2.le (sq_nonneg _)

lemma matrixFiniteLaminate_flux_bound {a b : ℝ} (ha : 0 < a)
    {A : Symmetric3} (hA : A ∈ matrixFiniteLaminate a b) (v : Coord3) :
    (A.val *ᵥ v) ⬝ᵥ (A.val *ᵥ v) ≤ b^2 * (v ⬝ᵥ v) := by
  obtain ⟨Q,hQ,d,hd,he⟩ := hA
  rw [he,← mulVec_mulVec,← mulVec_mulVec,orthogonal_dotProduct hQ]
  have hv := orthogonal_dotProduct (Q := Qᵀ) ⟨by simpa using hQ.2,by simpa using hQ.1⟩ v v
  rw [← hv]
  simp only [dotProduct,mulVec_diagonal,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hdi := hd.bounds ha i
  have hs : (d i)^2 ≤ b^2 := pow_le_pow_left₀ (ha.le.trans hdi.1.le) hdi.2.le 2
  nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg ((Qᵀ *ᵥ v) i))]

lemma fieldVector_inner (E F : Matrix (Fin 3) (Fin 2) ℝ) :
    inner ℝ (fieldVector E) (fieldVector F) = ∑ j, E.col j ⬝ᵥ F.col j := by
  simp only [fieldVector,PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  simp only [col_apply]
  ring

lemma fieldVector_quadratic_bounds {a b : ℝ} (ha : 0 < a)
    {A : Symmetric3} (hA : A ∈ matrixFiniteLaminate a b)
    (E : Matrix (Fin 3) (Fin 2) ℝ) :
    a * ‖fieldVector E‖^2 ≤ inner ℝ (fieldVector E) (fieldVector (A.val*E)) ∧
      inner ℝ (fieldVector E) (fieldVector (A.val*E)) ≤ b * ‖fieldVector E‖^2 := by
  rw [← real_inner_self_eq_norm_sq,fieldVector_inner,fieldVector_inner]
  change a * (∑ j, E.col j ⬝ᵥ E.col j) ≤ ∑ j, E.col j ⬝ᵥ (A.val *ᵥ E.col j) ∧
    (∑ j, E.col j ⬝ᵥ (A.val *ᵥ E.col j)) ≤ b * (∑ j, E.col j ⬝ᵥ E.col j)
  constructor
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => (matrixFiniteLaminate_quadratic_bounds ha hA (E.col j)).1
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => (matrixFiniteLaminate_quadratic_bounds ha hA (E.col j)).2

lemma fieldVector_flux_bound {a b : ℝ} (ha : 0 < a)
    {A : Symmetric3} (hA : A ∈ matrixFiniteLaminate a b)
    (E : Matrix (Fin 3) (Fin 2) ℝ) :
    ‖fieldVector (A.val*E)‖^2 ≤ b^2 * ‖fieldVector E‖^2 := by
  rw [← real_inner_self_eq_norm_sq,← real_inner_self_eq_norm_sq,fieldVector_inner,fieldVector_inner]
  change (∑ j, (A.val *ᵥ E.col j) ⬝ᵥ (A.val *ᵥ E.col j)) ≤ b^2 * (∑ j, E.col j ⬝ᵥ E.col j)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => matrixFiniteLaminate_flux_bound ha hA (E.col j)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_FieldVectorCLM
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise ENNReal

lemma tsupport_voltageGradient {u : Coord3 → Fin 2 → ℝ} :
    tsupport (voltageGradient u) ⊆ tsupport u := by
  apply closure_minimal _ (isClosed_tsupport u)
  intro x hx
  by_contra hn
  exact hx (by simp only [voltageGradient,fderiv_of_notMem_tsupport ℝ hn,map_zero])

lemma regularRegion_differentiable {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    {U : Set Coord3} {x : Coord3} (hx : x ∈ regularRegion u A U) : DifferentiableAt ℝ u x := by
  obtain ⟨V,hVU,hV,hxV⟩ := mem_regularRegion_iff.mp hx
  exact (hV.2.1.differentiableOn (by simp) x hxV).differentiableAt (hV.1.mem_nhds hxV)

lemma voltageGradient_pairing (u : Coord3 → Fin 2 → ℝ)
    (hu : Differentiable ℝ u) (F : Coord3 → Matrix (Fin 3) (Fin 2) ℝ) (x : Coord3) :
    inner ℝ (voltageGradient u x) (fieldVector (F x)) =
      ∑ j, fderiv ℝ (fun y => u y j) x ((F x).col j) := by
  rw [show voltageGradient u x = fieldVector (gradientColumns (fderiv ℝ u x)) by rfl,
    fieldVector_inner]
  apply Finset.sum_congr rfl
  intro j _
  have hf : fderiv ℝ (fun y => u y j) x = (ContinuousLinearMap.proj j).comp (fderiv ℝ u x) :=
    ((ContinuousLinearMap.proj j : (Fin 2 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp x (hu x).hasFDerivAt).fderiv
  rw [hf]
  change ((gradientColumns (fderiv ℝ u x))ᵀ *ᵥ (F x).col j) j = fderiv ℝ u x ((F x).col j) j
  rw [gradientColumns_apply]

lemma CompactGlobalUpdate.gradient_pairing_zero
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A)
    (hint : SmoothFluxIntegrable μ U (conductivityFlux u A))
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0) :
    (∫ x, inner ℝ (voltageGradient R.du x)
      (voltageFlux (fun y => u y+R.du y) R.tensor x) ∂μ) = 0 := by
  obtain ⟨hni,hnd⟩ := R.preserves_harmonic μ hint hdiv
  have hcomp : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => R.du x j) :=
    fun j => (contDiff_apply ℝ ℝ j).comp R.smooth_du
  have hc : ∀ j, HasCompactSupport (fun x => R.du x j) :=
    fun j => R.compact_du.comp_left (g := fun v : Fin 2 → ℝ => v j) rfl
  have hs : ∀ j, tsupport (fun x => R.du x j) ⊆ U := by
    intro j
    exact (tsupport_comp_subset (g := fun v : Fin 2 → ℝ => v j) rfl R.du).trans R.support_du
  simp_rw [voltageFlux,voltageGradient_pairing R.du (R.smooth_du.differentiable (by simp))]
  rw [integral_finsetSum _ (fun j _ => hni j _ (hcomp j) (hc j) (hs j))]
  simp only [hnd _ _ (hcomp _) (hc _) (hs _),Finset.sum_const_zero]

end ScalarConductivity

namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise ENNReal

lemma CompactGlobalUpdate.gradient_add_ae
    (μ : Measure Coord3) {U : Set Coord3} (hUm : MeasurableSet U)
    {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A) (hreg : μ (U \ regularRegion u A U) = 0) :
    voltageGradient (fun x => u x+R.du x) =ᵐ[μ.restrict U]
      (fun x => voltageGradient u x+voltageGradient R.du x) := by
  apply (ae_restrict_iff' hUm).mpr
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hreg] with x hx hxU
  exact voltageGradient_add (regularRegion_differentiable (show x ∈ regularRegion u A U from by by_contra hn; exact hx ⟨hxU,hn⟩))
    (R.smooth_du.differentiable (by simp) x)

lemma CompactGlobalUpdate.fields_memLp
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} (hUm : MeasurableSet U)
    {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A) (hreg : μ (U \ regularRegion u A U) = 0)
    (hE : MemLp (voltageGradient u) 2 (μ.restrict U))
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U)) :
    MemLp (voltageGradient (fun x => u x+R.du x)) 2 (μ.restrict U) ∧
      MemLp (voltageFlux (fun x => u x+R.du x) R.tensor) 2 (μ.restrict U) := by
  constructor
  · exact (hE.add ((memLp_voltageGradient_smooth_compact μ R.smooth_du R.compact_du).restrict U)).ae_eq
      (R.gradient_add_ae μ hUm hreg).symm
  · have hdF : MemLp (fun x => fieldVector (R.dF x)) 2 (μ.restrict U) :=
      ((R.smooth_dF.continuous.memLp_of_hasCompactSupport R.compact_dF).continuousLinearMap_comp fieldVectorCLM).restrict U
    apply (hF.add hdF).ae_eq
    exact Eventually.of_forall fun x => by
      simp only [Pi.add_apply,voltageFlux,R.constitutive x,fieldVector_add]

lemma CompactGlobalUpdate.Lp_energy_bound
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} (hUm : MeasurableSet U)
    {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A) (hreg : μ (U \ regularRegion u A U) = 0)
    (hE : MemLp (voltageGradient u) 2 (μ.restrict U))
    (hE' : MemLp (voltageGradient (fun x => u x+R.du x)) 2 (μ.restrict U))
    (hF' : MemLp (voltageFlux (fun x => u x+R.du x) R.tensor) 2 (μ.restrict U))
    (hint : SmoothFluxIntegrable μ U (conductivityFlux u A))
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hgraph : ∀ᵐ x ∂μ, x ∈ U → R.tensor x ∈ matrixFiniteLaminate a b) :
    ‖hE'.toLp _‖ ≤ (b/a)*‖hE.toLp _‖ ∧ ‖hF'.toLp _‖ ≤ (b^2/a)*‖hE.toLp _‖ := by
  let E := hE'.toLp _
  let F := hF'.toLp _
  let E₀ := hE.toLp _
  have hg : ∀ᵐ x ∂μ.restrict U, R.tensor x ∈ matrixFiniteLaminate a b :=
    (ae_restrict_iff' hUm).mpr hgraph
  have hpoint : ∀ᵐ x ∂μ.restrict U, a * ‖E x‖^2 ≤ inner ℝ (E x) (F x) ∧
      ‖F x‖^2 ≤ b^2 * ‖E x‖^2 := by
    filter_upwards [hE'.coeFn_toLp,hF'.coeFn_toLp,hg] with x hxE hxF hxg
    change a * ‖hE'.toLp _ x‖^2 ≤ _ ∧ _
    rw [hxE,hxF]
    exact ⟨(fieldVector_quadratic_bounds ha hxg _).1,fieldVector_flux_bound ha hxg _⟩
  obtain ⟨hell,hflux⟩ := Lp_elliptic_bounds (μ.restrict U) E F ha (ha.le.trans hab.le) hpoint
  apply elliptic_energy_bound E F E₀ ha (ha.le.trans hab.le) hell hflux
  rw [L2.inner_def]
  have heq : (fun x => inner ℝ ((E-E₀) x) (F x)) =ᵐ[μ.restrict U]
      (fun x => inner ℝ (voltageGradient R.du x) (voltageFlux (fun y => u y+R.du y) R.tensor x)) := by
    filter_upwards [Lp.coeFn_sub E E₀,hE'.coeFn_toLp,hE.coeFn_toLp,hF'.coeFn_toLp,
      R.gradient_add_ae μ hUm hreg] with x hx hxE hxE₀ hxF hadd
    rw [hx]
    change inner ℝ (E x-E₀ x) (F x) = _
    rw [hxE,hxE₀,hxF,hadd,add_sub_cancel_left]
  rw [integral_congr_ae heq,setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact R.gradient_pairing_zero μ hint hdiv
  · intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (R.support_du (tsupport_voltageGradient hh))),inner_zero_left]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_SmoothDirectionIntegral
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma smooth_direction_integral_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (v : E) (f : SmoothScalar E) (hf : HasCompactSupport f.val) :
    (∫ x, (smoothDirection v f).val x ∂μ) = 0 := by
  have hh := smooth_integration_by_parts μ v f (1 : SmoothScalar E) hf
  simpa using hh

lemma compact_flux_mean_zero
    (μ : Measure Coord3) [μ.IsAddHaarMeasure] (F : Coord3 → Coord3)
    (hdiv : ∀ ψ : Coord3 → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
      (∫ x, fderiv ℝ ψ x (F x) ∂μ) = 0) (i : Fin 3) :
    (∫ x, F x i ∂μ) = 0 := by
  let L : Coord3 →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hh := hdiv L L.contDiff
  simpa only [L.fderiv, L, ContinuousLinearMap.proj_apply] using hh

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_FieldMean
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped ENNReal Matrix.Norms.Elementwise

lemma integral_fieldVector_eq_zero
    (μ : Measure Coord3) [IsFiniteMeasureOnCompacts μ]
    (F : Coord3 → Matrix (Fin 3) (Fin 2) ℝ)
    (hF : Continuous F) (hc : HasCompactSupport F)
    (hmean : ∀ i j, (∫ x, F x i j ∂μ) = 0) :
    (∫ x, fieldVector (F x) ∂μ) = 0 := by
  have hi : Integrable (fun x => fieldVector (F x)) μ :=
    (fieldVectorCLM.continuous.comp hF).integrable_of_hasCompactSupport
      (hc.comp_left (map_zero fieldVectorCLM))
  ext ij
  have h := (EuclideanSpace.proj ij).integral_comp_comm hi
  exact h.symm.trans (hmean ij.1 ij.2)

lemma voltageGradient_mean_zero
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {u : Coord3 → Fin 2 → ℝ}
    (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u) (hc : HasCompactSupport u) :
    (∫ x, voltageGradient u x ∂μ) = 0 := by
  have hi : Integrable (voltageGradient u) μ :=
    (continuous_voltageGradient hu).integrable_of_hasCompactSupport (compact_voltageGradient hc)
  ext ij
  have h := (EuclideanSpace.proj ij).integral_comp_comm hi
  change (EuclideanSpace.proj ij) (∫ x, voltageGradient u x ∂μ) = 0
  rw [← h]
  let v : Coord3 := Pi.single ij.1 1
  let f : SmoothScalar Coord3 := ⟨fun x => u x ij.2, (contDiff_apply ℝ ℝ ij.2).comp hu⟩
  have hf : HasCompactSupport f.val := hc.comp_left (g := fun w : Fin 2 → ℝ => w ij.2) rfl
  have hm := smooth_direction_integral_zero μ v f hf
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    have hd : fderiv ℝ f.val x = (ContinuousLinearMap.proj ij.2).comp (fderiv ℝ u x) :=
      ((ContinuousLinearMap.proj ij.2 : (Fin 2 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp x
        (hu.differentiable (by simp) x).hasFDerivAt).fderiv
    change (gradientColumns (fderiv ℝ u x)) ij.1 ij.2 = fderiv ℝ f.val x v
    rw [hd]
    simp only [gradientColumns,transpose_apply,LinearMap.toMatrix'_apply,
      ContinuousLinearMap.coe_coe,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply]
    rfl

lemma CompactGlobalUpdate.flux_mean_zero
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A) :
    (∫ x, fieldVector (R.dF x) ∂μ) = 0 := by
  apply integral_fieldVector_eq_zero μ R.dF R.smooth_dF.continuous R.compact_dF
  intro i j
  exact compact_flux_mean_zero μ (fun x => (R.dF x).col j) (R.cauchy_dF j) i

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_CompactUpdateLp
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped ENNReal Matrix.Norms.Elementwise

lemma voltageGradient_sum
    {I : Type*} [Fintype I] (u : I → Coord3 → Fin 2 → ℝ)
    (hu : ∀ i, Differentiable ℝ (u i)) (x : Coord3) :
    voltageGradient (fun y => ∑ i, u i y) x = ∑ i, voltageGradient (u i) x := by
  classical
  unfold voltageGradient
  rw [fderiv_fun_sum (fun i _ => hu i x),map_sum]

lemma CompactGlobalUpdate.gradient_toLp_eq
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} (hUm : MeasurableSet U)
    {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A) (hreg : μ (U \ regularRegion u A U) = 0)
    (hE : MemLp (voltageGradient u) 2 (μ.restrict U))
    (hE' : MemLp (voltageGradient (fun x => u x+R.du x)) 2 (μ.restrict U)) :
    hE'.toLp _ = hE.toLp _ + (R.memLp_gradient_correction μ).toLp _ := by
  rw [← MemLp.toLp_add]
  exact hE'.toLp_congr _ (R.gradient_add_ae μ hUm hreg)

lemma CompactGlobalUpdate.flux_toLp_eq
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A)
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U))
    (hF' : MemLp (voltageFlux (fun x => u x+R.du x) R.tensor) 2 (μ.restrict U)) :
    hF'.toLp _ = hF.toLp _ + (R.memLp_flux_correction μ).toLp _ := by
  rw [← MemLp.toLp_add]
  apply hF'.toLp_congr
  exact Eventually.of_forall fun x => by
    simp only [voltageFlux,R.constitutive x,fieldVector_add,Pi.add_apply]

lemma norm_correction_bound_of_add
    {V : Type*} [NormedAddCommGroup V] (E E₀ dE : V) (M : ℝ)
    (he : E = E₀ + dE) (hbound : ‖E‖ ≤ M) : ‖dE‖ ≤ M + ‖E₀‖ := by
  have hd : dE = E - E₀ := by rw [he, add_sub_cancel_left]
  rw [hd]
  exact (norm_sub_le _ _).trans (add_le_add hbound le_rfl)

lemma CompactGlobalUpdate.correction_energy_bound
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} (hUm : MeasurableSet U)
    {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A) (hreg : μ (U \ regularRegion u A U) = 0)
    (hE : MemLp (voltageGradient u) 2 (μ.restrict U))
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U))
    (hint : SmoothFluxIntegrable μ U (conductivityFlux u A))
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hgraph : ∀ᵐ x ∂μ, x ∈ U → R.tensor x ∈ matrixFiniteLaminate a b) :
    ‖(R.memLp_gradient_correction μ).toLp _‖ ≤ (b/a+1)*‖hE.toLp _‖ ∧
      ‖(R.memLp_flux_correction μ).toLp _‖ ≤ (b^2/a)*‖hE.toLp _‖+‖hF.toLp _‖ := by
  obtain ⟨hE',hF'⟩ := R.fields_memLp μ hUm hreg hE hF
  obtain ⟨hEB,hFB⟩ := R.Lp_energy_bound μ hUm hreg hE hE' hF' hint hdiv ha hab hgraph
  have he := R.gradient_toLp_eq μ hUm hreg hE hE'
  have hf := R.flux_toLp_eq μ hF hF'
  constructor
  · have h := norm_correction_bound_of_add _ _ _ _ he hEB
    simpa only [add_mul, one_mul] using h
  · exact norm_correction_bound_of_add _ _ _ _ hf hFB

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_VoltageFluxConstraints
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open MeasureTheory Set Filter Topology Matrix
open scoped ENNReal Matrix.Norms.Elementwise

lemma CompactGlobalUpdate.fluxCorrection_pairing
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A)
    {v : Coord3 → Fin 2 → ℝ} (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (hvg : MemLp (voltageGradient v) 2 (μ.restrict U)) :
    inner ℝ (hvg.toLp _) ((R.memLp_flux_correction μ).toLp _) = 0 := by
  rw [L2.inner_def]
  have he : (∫ x, inner ℝ ((hvg.toLp _) x) (((R.memLp_flux_correction μ).toLp _) x) ∂μ.restrict U) =
      ∫ x, inner ℝ (voltageGradient v x) (fieldVector (R.dF x)) ∂μ.restrict U := by
    apply integral_congr_ae
    filter_upwards [hvg.coeFn_toLp,(R.memLp_flux_correction μ).coeFn_toLp] with x hx hy
    rw [hx,hy]
  rw [he,setIntegral_eq_integral_of_forall_compl_eq_zero]
  · simp_rw [voltageGradient_pairing v (hv.differentiable (by simp))]
    have hvc : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => v x j) :=
      fun j => (contDiff_apply ℝ ℝ j).comp hv
    have hint : ∀ j, Integrable (fun x => fderiv ℝ (fun y => v y j) x ((R.dF x).col j)) μ := by
      intro j
      apply smooth_flux_integrable_pairing μ _
        ((continuous_pi (fun i => (continuous_apply j).comp (continuous_apply i))).comp R.smooth_dF.continuous)
        (R.compact_dF.comp_left (g := fun M : Matrix (Fin 3) (Fin 2) ℝ => M.col j) rfl)
        _ (hvc j)
    rw [integral_finsetSum _ (fun j _ => hint j)]
    simp only [R.cauchy_dF _ _ (hvc _),Finset.sum_const_zero]
  · intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hs => hx (R.support_dF hs))]
    simp only [show fieldVector 0 = 0 from map_zero fieldVectorCLM,inner_zero_right]

lemma CompactGlobalUpdate.fluxCorrection_mem_orthogonal
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A) :
    (R.memLp_flux_correction μ).toLp _ ∈ (allVoltageGradients μ U)ᗮ := by
  let F := (R.memLp_flux_correction μ).toLp _
  let L : Lp FieldVector 2 (μ.restrict U) →L[ℝ] ℝ := innerSL ℝ F
  have hker : allVoltageGradients μ U ≤ L.ker := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨v,hv,hvg,rfl⟩
      change inner ℝ F (hvg.toLp _) = 0
      rw [real_inner_comm]
      exact R.fluxCorrection_pairing μ hv hvg
    · exact L.isClosed_ker
  intro z hz
  rw [real_inner_comm]
  exact hker hz

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Scalarization_ScalarRelationStrongClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ScalarConductivity
open Filter Topology

theorem scalar_relation_strong_closed
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a b : ℝ} {E F : V} {En Fn : ℕ → V} {sn : ℕ → ℝ}
    (hs : ∀ n, sn n ∈ Set.Icc a b)
    (hE : Tendsto En atTop (𝓝 E)) (hF : Tendsto Fn atTop (𝓝 F))
    (hres : Tendsto (fun n => Fn n - sn n • En n) atTop (𝓝 0)) :
    ∃ s ∈ Set.Icc a b, F = s • E := by
  obtain ⟨s, hs', φ, hφ, hlim⟩ :=
    tendsto_subseq_of_bounded (Metric.isBounded_Icc a b) hs
  have hsmem : s ∈ Set.Icc a b := by
    simpa only [isClosed_Icc.closure_eq] using hs'
  refine ⟨s, hsmem, ?_⟩
  have hlim' : Tendsto (fun n => Fn (φ n) - sn (φ n) • En (φ n))
      atTop (𝓝 (F - s • E)) :=
    (hF.comp hφ.tendsto_atTop).sub (hlim.smul (hE.comp hφ.tendsto_atTop))
  have hz : F - s • E = 0 :=
    tendsto_nhds_unique hlim' (hres.comp hφ.tendsto_atTop)
  exact sub_eq_zero.mp hz

end ScalarConductivity

namespace ScalarConductivity
open Filter Topology

theorem commonScalar_of_relation {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {a b s : ℝ} {E F : V}
    (hab : a ≤ b) (hs : s ∈ Set.Icc a b) (hF : F = s • E) :
    commonScalar a E F ∈ Set.Icc a b ∧ F = commonScalar a E F • E := by
  subst F
  by_cases hE : E = 0
  · simp [commonScalar, hE, hab]
  · have hn : ‖E‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hE)
    have hval : commonScalar a E (s • E) = s := by
      simp only [commonScalar, ite_eq_right hE, inner_smul_right, real_inner_self_eq_norm_sq]
      exact mul_div_cancel_right₀ s hn
    simpa only [hval, and_true] using hs

theorem measurable_commonScalar
    {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V] {E F : X → V} (a : ℝ)
    (hE : Measurable E) (hF : Measurable F) :
    Measurable (fun x => commonScalar a (E x) (F x)) := by
  classical
  exact Measurable.ite (measurableSet_eq_fun hE measurable_const) measurable_const
    ((hE.inner hF).div (hE.norm.pow_const 2))

theorem scalar_relation_ae_strong_closed
    {X V : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {a b : ℝ} (hab : a ≤ b) {E F : X → V}
    (hEm : Measurable E) (hFm : Measurable F)
    {En Fn : ℕ → X → V} {sn : ℕ → X → ℝ}
    (hs : ∀ n, ∀ᵐ x ∂μ, sn n x ∈ Set.Icc a b)
    (hE : ∀ᵐ x ∂μ, Tendsto (fun n => En n x) atTop (𝓝 (E x)))
    (hF : ∀ᵐ x ∂μ, Tendsto (fun n => Fn n x) atTop (𝓝 (F x)))
    (hres : ∀ᵐ x ∂μ,
      Tendsto (fun n => Fn n x - sn n x • En n x) atTop (𝓝 0)) :
    ∃ s : X → ℝ, Measurable s ∧
      (∀ᵐ x ∂μ, s x ∈ Set.Icc a b ∧ F x = s x • E x) := by
  refine ⟨fun x => commonScalar a (E x) (F x),
    measurable_commonScalar a hEm hFm, ?_⟩
  filter_upwards [ae_all_iff.mpr hs, hE, hF, hres] with x hsx hEx hFx hrx
  obtain ⟨s, hs', hrel⟩ := scalar_relation_strong_closed hsx hEx hFx hrx
  exact commonScalar_of_relation hab hs' hrel

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Scalarization_ScalarRelationLpStrongClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity
open Filter Topology Set TopologicalSpace

theorem scalar_relation_Lp_strong_closed
    {X V : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {a b : ℝ} (hab : a ≤ b)
    {E F : Lp V 2 μ} {En Fn : ℕ → Lp V 2 μ} {sn : ℕ → X → ℝ}
    (hs : ∀ n, ∀ᵐ x ∂μ, sn n x ∈ Set.Icc a b)
    (hE : Tendsto En atTop (𝓝 E)) (hF : Tendsto Fn atTop (𝓝 F))
    (hres : TendstoInMeasure μ (fun n x => Fn n x - sn n x • En n x)
      atTop (fun _ => 0)) :
    ∃ s : X → ℝ, Measurable s ∧
      (∀ᵐ x ∂μ, s x ∈ Set.Icc a b ∧ F x = s x • E x) := by
  obtain ⟨φ, hφ, hElim⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hE).exists_seq_tendsto_ae
  obtain ⟨ψ, hψ, hFlim⟩ :=
    ((tendstoInMeasure_of_tendsto_Lp hF).comp hφ.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨ξ, hξ, hrlim⟩ :=
    ((hres.comp hφ.tendsto_atTop).comp hψ.tendsto_atTop).exists_seq_tendsto_ae
  apply scalar_relation_ae_strong_closed hab (Lp.stronglyMeasurable E).measurable
    (Lp.stronglyMeasurable F).measurable (En := fun n => En (φ (ψ (ξ n))))
    (Fn := fun n => Fn (φ (ψ (ξ n)))) (sn := fun n => sn (φ (ψ (ξ n))))
  · exact fun n => hs _
  · filter_upwards [hElim] with x hx
    exact (hx.comp hψ.tendsto_atTop).comp hξ.tendsto_atTop
  · filter_upwards [hFlim] with x hx
    exact hx.comp hξ.tendsto_atTop
  · exact hrlim

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_DenseWeakStrongContinuityPoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity
open Filter Topology Set TopologicalSpace

theorem dense_weakToStrong_continuityPoints
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [SeparableSpace V] (Z : Set (WeakSpace ℝ V)) (hZ : IsCompact Z) :
    Dense {z : Z | ContinuousAt
      (fun w : Z => (toWeakSpace ℝ V).symm w.val) z} := by
  have : CompactSpace Z := isCompact_iff_compactSpace.mp hZ
  apply dense_continuityPoints_of_closed_ball_preimages
  intro y r
  have hclosed : IsClosed ((toWeakSpace ℝ V) '' Metric.closedBall y r) := by
    apply closure_eq_iff_isClosed.mp
    rw [← (convex_closedBall y r).toWeakSpace_closure ℝ,
      Metric.isClosed_closedBall.closure_eq]
  convert hclosed.preimage continuous_subtype_val using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · intro hz
    exact ⟨(toWeakSpace ℝ V).symm z.val, hz, (toWeakSpace ℝ V).apply_symm_apply _⟩
  · rintro ⟨x, hx, heq⟩
    simpa only [← heq, LinearEquiv.symm_apply_apply] using hx

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Scalarization_ApproxScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory
open scoped ENNReal
noncomputable section
open Matrix Filter Topology
namespace ScalarConductivity
open Filter Topology Set TopologicalSpace

lemma tendstoInMeasure_of_small_exceptional_sets
    {X V : Type*} [MeasurableSpace X] [SeminormedAddCommGroup V]
    (μ : Measure X) (f : ℕ → X → V) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ n, μ {x | ε n ≤ ‖f n x‖} ≤ ENNReal.ofReal (ε n)) :
    TendstoInMeasure μ f atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro δ hδ
  simp only [sub_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hε)
  · exact Filter.Eventually.of_forall (fun _ => bot_le)
  · filter_upwards [(tendsto_order.1 hε).2 δ hδ] with n hn
    exact (measure_mono (fun x hx => hn.le.trans hx)).trans (hbound n)

theorem exact_scalar_of_weak_density
    {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V] (μ : Measure X)
    [SeparableSpace (Lp V 2 μ)] {a b : ℝ} (hab : a ≤ b)
    (K : Set (WeakSpace ℝ (Lp V 2 μ × Lp V 2 μ)))
    (hK : IsCompact K) (hKn : K.Nonempty)
    (hdense : ∀ ε > 0, Dense {z : K | ApproxScalar μ a b ε
      ((toWeakSpace ℝ (Lp V 2 μ × Lp V 2 μ)).symm z.val)}) :
    ∃ (Z : Lp V 2 μ × Lp V 2 μ) (s : X → ℝ),
      toWeakSpace ℝ (Lp V 2 μ × Lp V 2 μ) Z ∈ K ∧ Measurable s ∧
      (∀ᵐ x ∂μ, s x ∈ Icc a b ∧ Z.2 x = s x • Z.1 x) := by
  classical
  let : Nonempty K := hKn.to_subtype
  let φ : K → Lp V 2 μ × Lp V 2 μ :=
    fun z => (toWeakSpace ℝ (Lp V 2 μ × Lp V 2 μ)).symm z.val
  obtain ⟨z, hz⟩ := (dense_weakToStrong_continuityPoints K hK).nonempty
  change ContinuousAt φ z at hz
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεp : ∀ n, 0 < ε n := fun n => div_pos zero_lt_one (Nat.cast_add_one_pos n)
  have hεt : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε] using tendsto_one_div_add_atTop_nhds_zero_nat
  have hn : ∀ n, ∃ w : K, ApproxScalar μ a b (ε n) (φ w) ∧ dist (φ w) (φ z) < ε n := by
    intro n
    have hnbr : {w : K | dist (φ w) (φ z) < ε n} ∈ 𝓝 z :=
      hz.preimage_mem_nhds (Metric.ball_mem_nhds _ (hεp n))
    obtain ⟨w, hw, hw'⟩ := (hdense (ε n) (hεp n)).inter_nhds_nonempty hnbr
    exact ⟨w, hw, hw'⟩
  choose w hw hd using hn
  have hwt : Tendsto (fun n => φ (w n)) atTop (𝓝 (φ z)) := by
    apply tendsto_iff_dist_tendsto_zero.2
    exact squeeze_zero (fun n => dist_nonneg) (fun n => (hd n).le) hεt
  choose s hsm hsb hsr using hw
  obtain ⟨σ, hσm, hσ⟩ := scalar_relation_Lp_strong_closed hab hsb
    (continuous_fst.tendsto _ |>.comp hwt) (continuous_snd.tendsto _ |>.comp hwt)
    (tendstoInMeasure_of_small_exceptional_sets μ
      (fun n x => (φ (w n)).2 x - s n x • (φ (w n)).1 x) ε hεt hsr)
  refine ⟨φ z, σ, ?_, hσm, hσ⟩
  simpa only [φ, LinearEquiv.apply_symm_apply] using z.property

end ScalarConductivity

end
end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Scalarization_DefectMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal

lemma defect_tendstoInMeasure_of_small_exceptions
    {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (μ : Measure X) (E : ℕ → Lp V 2 μ) (r : ℕ → X → V)
    (η : ℕ → ℝ) (hη : ∀ n, 0 ≤ η n) (hηt : Tendsto η atTop (𝓝 0))
    (B : ℕ → Set X) (hB : Tendsto (fun n => μ (B n)) atTop (𝓝 0))
    {C : ℝ} (hC : 0 ≤ C) (hEC : ∀ n, ‖E n‖ ≤ C)
    (hdef : ∀ n, ∀ᵐ x ∂μ, x ∉ B n → ‖r n x‖ ≤ η n * ‖E n x‖) :
    TendstoInMeasure μ r atTop (fun _ => 0) := by
  let Z : ℕ → Lp V 2 μ := fun n => η n • E n
  have hZ : Tendsto Z atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _) _ (by simpa using hηt.mul_const C)
    intro n
    change ‖η n • E n‖ ≤ η n * C
    rw [norm_smul, Real.norm_of_nonneg (hη n)]
    simpa only [mul_comm] using mul_le_mul (hEC n) le_rfl (hη n) hC
  have hZI : TendstoInMeasure μ (fun n x => Z n x) atTop (fun _ => 0) := by
    have hh := tendstoInMeasure_of_tendsto_Lp hZ
    apply hh.congr_right
    filter_upwards [Lp.coeFn_zero (E := V) (p := 2) (μ := μ)] with x hx
    exact hx
  rw [tendstoInMeasure_iff_norm] at hZI ⊢
  intro ε hε
  simp only [sub_zero] at hZI ⊢
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [add_zero] using hB.add (hZI ε hε))
  · exact Eventually.of_forall (fun _ => bot_le)
  · apply Eventually.of_forall
    intro n
    have hs : ∀ᵐ x ∂μ, x ∈ {x | ε ≤ ‖r n x‖} → x ∈ B n ∪ {x | ε ≤ ‖Z n x‖} := by
      filter_upwards [hdef n, Lp.coeFn_smul (η n) (E n)] with x hx hz
      intro hr
      by_cases hb : x ∈ B n
      · exact Or.inl hb
      · right
        have he : ‖Z n x‖ = η n * ‖E n x‖ := by
          change ‖(η n • E n : Lp V 2 μ) x‖ = _
          rw [hz, Pi.smul_apply, norm_smul, Real.norm_of_nonneg (hη n)]
        exact (hr.trans (hx hb)).trans_eq he.symm
    exact (measure_mono_ae hs).trans (measure_union_le _ _)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Scalarization_UpdateFieldPair
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open MeasureTheory Set Filter Topology

lemma CompactGlobalUpdate.fieldPair_eq
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} (hUm : MeasurableSet U)
    {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A) (hreg : μ (U \ regularRegion u A U) = 0)
    (hE : MemLp (voltageGradient u) 2 (μ.restrict U))
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U))
    (hE' : MemLp (voltageGradient (fun x => u x+R.du x)) 2 (μ.restrict U))
    (hF' : MemLp (voltageFlux (fun x => u x+R.du x) R.tensor) 2 (μ.restrict U)) :
    R.fieldPair μ hE hF = (hE'.toLp _,hF'.toLp _) := by
  exact Prod.ext (R.gradient_toLp_eq μ hUm hreg hE hE').symm
    (R.flux_toLp_eq μ hF hF').symm

lemma CompactGlobalUpdate.fieldPair_ae
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} (hUm : MeasurableSet U)
    {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A) (hreg : μ (U \ regularRegion u A U) = 0)
    (hE : MemLp (voltageGradient u) 2 (μ.restrict U))
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U)) :
    ∀ᵐ x ∂μ.restrict U,
      (R.fieldPair μ hE hF).1 x = voltageGradient (fun y => u y+R.du y) x ∧
      (R.fieldPair μ hE hF).2 x = voltageFlux (fun y => u y+R.du y) R.tensor x := by
  obtain ⟨hE',hF'⟩ := R.fields_memLp μ hUm hreg hE hF
  rw [R.fieldPair_eq μ hUm hreg hE hF hE' hF']
  exact hE'.coeFn_toLp.and hF'.coeFn_toLp

lemma CompactGlobalUpdate.fieldPair_energy_bound
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} (hUm : MeasurableSet U)
    {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A) (hreg : μ (U \ regularRegion u A U) = 0)
    (hE : MemLp (voltageGradient u) 2 (μ.restrict U))
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U))
    (hint : SmoothFluxIntegrable μ U (conductivityFlux u A))
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hgraph : ∀ᵐ x ∂μ, x ∈ U → R.tensor x ∈ matrixFiniteLaminate a b) :
    ‖(R.fieldPair μ hE hF).1‖ ≤ (b/a)*‖hE.toLp _‖ ∧
      ‖(R.fieldPair μ hE hF).2‖ ≤ (b^2/a)*‖hE.toLp _‖ := by
  obtain ⟨hE',hF'⟩ := R.fields_memLp μ hUm hreg hE hF
  rw [R.fieldPair_eq μ hUm hreg hE hF hE' hF']
  exact R.Lp_energy_bound μ hUm hreg hE hE' hF' hint hdiv ha hab hgraph

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Matrix Set MeasureTheory
open scoped Matrix.Norms.Elementwise

lemma diagonal_conjugate_smul_sub {Q : Mat3} (hQ : Q ∈ orthogonalFrames)
    (d : DiagonalTriple) (s : ℝ) :
    Q * diagonal d * Qᵀ - s • (1 : Mat3) = Q * diagonal (d - fun _ => s) * Qᵀ := by
  change Q * diagonal d * Qᵀ - s • (1 : Mat3) = Q * diagonal (fun i => d i - s) * Qᵀ
  rw [← diagonal_sub, Matrix.mul_sub, Matrix.sub_mul]
  have he : diagonal (fun _ : Fin 3 => s) = s • (1 : Mat3) := by
    ext i j
    change (if i = j then s else 0) = s * (if i = j then 1 else 0)
    split_ifs <;> simp
  rw [he, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hQ.2]

lemma diagonal_conjugate_dot_bound {Q : Mat3} (hQ : Q ∈ orthogonalFrames)
    {d : DiagonalTriple} {c : ℝ} (hc : 0 ≤ c) (hd : ∀ i, |d i| ≤ c) (v : Coord3) :
    ((Q * diagonal d * Qᵀ) *ᵥ v) ⬝ᵥ ((Q * diagonal d * Qᵀ) *ᵥ v) ≤
      c^2 * (v ⬝ᵥ v) := by
  rw [← mulVec_mulVec,← mulVec_mulVec,orthogonal_dotProduct hQ]
  have hv := orthogonal_dotProduct (Q := Qᵀ) ⟨by simpa using hQ.2,by simpa using hQ.1⟩ v v
  rw [← hv]
  simp only [dotProduct,mulVec_diagonal,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hs : (d i)^2 ≤ c^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hc).mpr (hd i)
  nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg ((Qᵀ *ᵥ v) i))]

lemma diagonal_conjugate_field_bound {Q : Mat3} (hQ : Q ∈ orthogonalFrames)
    {d : DiagonalTriple} {c : ℝ} (hc : 0 ≤ c) (hd : ∀ i, |d i| ≤ c)
    (E : Matrix (Fin 3) (Fin 2) ℝ) :
    ‖fieldVector ((Q * diagonal d * Qᵀ)*E)‖ ≤ c * ‖fieldVector E‖ := by
  have hs : ‖fieldVector ((Q * diagonal d * Qᵀ)*E)‖^2 ≤ c^2 * ‖fieldVector E‖^2 := by
    rw [← real_inner_self_eq_norm_sq,← real_inner_self_eq_norm_sq,fieldVector_inner,fieldVector_inner]
    change (∑ j, ((Q * diagonal d * Qᵀ) *ᵥ E.col j) ⬝ᵥ ((Q * diagonal d * Qᵀ) *ᵥ E.col j)) ≤
      c^2 * (∑ j, E.col j ⬝ᵥ E.col j)
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => diagonal_conjugate_dot_bound hQ hc hd (E.col j)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mp
  simpa only [mul_pow] using hs

lemma matrixFiniteLaminate_diagonal_bounds {a b : ℝ} (ha : 0 < a)
    {A : Symmetric3} (hA : A ∈ matrixFiniteLaminate a b) (i : Fin 3) :
    A.val i i ∈ Icc a b := by
  have h := matrixFiniteLaminate_quadratic_bounds ha hA (Pi.single i 1)
  simpa [dotProduct, Matrix.mulVec, Pi.single_apply] using h

lemma scalarNeighbourhood_defect_bound {a b η : ℝ} (hη : 0 ≤ η)
    {A : Symmetric3} (hA : A ∈ spectralExtension (scalarNeighbourhood a b η))
    (E : Matrix (Fin 3) (Fin 2) ℝ) :
    ‖fieldVector (A.val*E) - (A.val 0 0) • fieldVector E‖ ≤ (2*η) * ‖fieldVector E‖ := by
  obtain ⟨Q,hQ,d,⟨hd,s,hs⟩,he⟩ := hA
  have hds : ∀ i, |d i - s| ≤ η := by
    intro i
    exact (norm_le_pi_norm (d - fun _ => s) i).trans hs.le
  have hshift : A.val - s • (1 : Mat3) = Q * diagonal (d - fun _ => s) * Qᵀ := by
    rw [he]
    exact diagonal_conjugate_smul_sub hQ d s
  have hnorm : ∀ F : Matrix (Fin 3) (Fin 2) ℝ,
      ‖fieldVector (A.val*F) - s • fieldVector F‖ ≤ η * ‖fieldVector F‖ := by
    intro F
    have hb := diagonal_conjugate_field_bound (d := d - fun _ => s) hQ hη hds F
    rw [← hshift, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul] at hb
    exact hb
  have hssq : |A.val 0 0 - s| ≤ η := by
    have hb := diagonal_conjugate_dot_bound (d := d - fun _ => s) hQ hη hds (Pi.single 0 1)
    rw [← hshift] at hb
    have hl : (A.val 0 0 - s)^2 ≤
        ((A.val - s • (1 : Mat3)) *ᵥ Pi.single 0 1) ⬝ᵥ
        ((A.val - s • (1 : Mat3)) *ᵥ Pi.single 0 1) := by
      have he0 : ((A.val - s • (1 : Mat3)) *ᵥ Pi.single 0 1) 0 = A.val 0 0 - s := by
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [← he0]
      simpa only [dotProduct,pow_two] using
        Finset.single_le_sum (fun i _ => mul_self_nonneg (((A.val - s • (1 : Mat3)) *ᵥ Pi.single 0 1) i))
          (Finset.mem_univ (0 : Fin 3))
    have hr : (A.val 0 0 - s)^2 ≤ η^2 := hl.trans (by simpa [dotProduct, Pi.single_apply] using hb)
    exact (sq_le_sq₀ (abs_nonneg _) hη).mp (by simpa only [sq_abs] using hr)
  have hsplit : fieldVector (A.val*E) - A.val 0 0 • fieldVector E =
      (fieldVector (A.val*E) - s • fieldVector E) + (s-A.val 0 0) • fieldVector E := by
    rw [sub_smul]
    abel
  rw [hsplit]
  calc
    _ ≤ ‖fieldVector (A.val*E) - s • fieldVector E‖ + ‖(s-A.val 0 0) • fieldVector E‖ := norm_add_le _ _
    _ ≤ η * ‖fieldVector E‖ + η * ‖fieldVector E‖ := add_le_add (hnorm E) (by
      rw [norm_smul,Real.norm_eq_abs,abs_sub_comm]
      exact mul_le_mul_of_nonneg_right hssq (norm_nonneg _))
    _ = _ := by ring

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Scalarization_WeakCellFast
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal

lemma integral_norm_le_L2_const
    {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V]
    (μ : Measure X) [IsFiniteMeasure μ] {f : X → V} (hf : MemLp f 2 μ) :
    (∫ x, ‖f x‖ ∂μ) ≤ ‖(memLp_const (p := 2) (μ := μ) (1 : ℝ)).toLp _‖ * ‖hf.toLp _‖ := by
  let oneLp := (memLp_const (p := 2) (μ := μ) (1 : ℝ)).toLp _
  let nLp := hf.norm.toLp _
  have heq : (∫ x, ‖f x‖ ∂μ) = inner ℝ oneLp nLp := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(memLp_const (p := 2) (μ := μ) (1 : ℝ)).coeFn_toLp,hf.norm.coeFn_toLp] with x hx hy
    change ‖f x‖ = inner ℝ (oneLp x) (nLp x)
    rw [hx,hy,real_inner_comm]
    simp
  rw [heq]
  calc
    _ ≤ |inner ℝ oneLp nLp| := le_abs_self _
    _ ≤ ‖oneLp‖ * ‖nLp‖ := abs_real_inner_le_norm _ _
    _ = _ := by
      rw [show ‖nLp‖ = ‖hf.toLp _‖ by
        simp only [nLp, Lp.norm_toLp, eLpNorm_norm f]]

lemma compact_inner_right
    {X V : Type*} [TopologicalSpace X] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {f : X → V} (hc : HasCompactSupport f) (φ : X → V) :
    HasCompactSupport (fun x => inner ℝ (φ x) (f x)) := by
  apply hc.mono
  intro x hx hn
  exact hx (by change inner ℝ (φ x) (f x) = 0; rw [hn,inner_zero_right])

lemma vector_pairing_bound_of_zero_mean
    {X V : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (f φ : X → V) (hf : Continuous f) (hc : HasCompactSupport f)
    (hφ : Continuous φ) (hmean : (∫ x, f x ∂μ) = 0)
    {c : V} {ω : ℝ} (hosc : ∀ x ∈ tsupport f, ‖φ x-c‖ ≤ ω) :
    |∫ x, inner ℝ (φ x) (f x) ∂μ| ≤ ω * ∫ x, ‖f x‖ ∂μ := by
  have hfi : Integrable f μ := hf.integrable_of_hasCompactSupport hc
  have h1 : Integrable (fun x => inner ℝ (φ x) (f x)) μ :=
    (hφ.inner hf).integrable_of_hasCompactSupport (compact_inner_right hc _)
  have h2 : Integrable (fun x => inner ℝ (φ x-c) (f x)) μ :=
    ((hφ.sub continuous_const).inner hf).integrable_of_hasCompactSupport (compact_inner_right hc _)
  have he : (∫ x, inner ℝ (φ x) (f x) ∂μ) = ∫ x, inner ℝ (φ x-c) (f x) ∂μ := by
    simp_rw [inner_sub_left]
    rw [integral_sub h1 (hfi.const_inner c),integral_inner hfi c,hmean,inner_zero_right,sub_zero]
  rw [he]
  calc
    _ ≤ ∫ x, |inner ℝ (φ x-c) (f x)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, ω * ‖f x‖ ∂μ := by
      apply integral_mono_ae h2.abs (hfi.norm.const_mul ω)
      exact Eventually.of_forall fun x => by
        change |inner ℝ (φ x-c) (f x)| ≤ ω * ‖f x‖
        by_cases hx : x ∈ tsupport f
        · exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hosc x hx) (norm_nonneg _))
        · rw [image_eq_zero_of_notMem_tsupport hx,inner_zero_right,norm_zero,abs_zero,mul_zero]
    _ = _ := integral_const_mul _ _

lemma norm_finite_disjoint_sum
    {ι X V : Type*} [Fintype ι] [TopologicalSpace X] [NormedAddCommGroup V]
    (f : ι → X → V) (hd : Pairwise (fun i j => Disjoint (tsupport (f i)) (tsupport (f j)))) (x : X) :
    ‖∑ i, f i x‖ = ∑ i, ‖f i x‖ := by
  classical
  by_cases h : ∃ i, f i x ≠ 0
  · obtain ⟨i,hi⟩ := h
    have hz : ∀ j, j ≠ i → f j x = 0 := by
      intro j hji
      by_contra hj
      exact Set.disjoint_left.mp (hd hji) (subset_closure hj) (subset_closure hi)
    rw [Finset.sum_eq_single i,Finset.sum_eq_single i]
    · intro j _ hji; rw [hz j hji,norm_zero]
    · simp
    · intro j _ hji; exact hz j hji
    · simp
  · push Not at h
    simp only [h,Finset.sum_const_zero,norm_zero]

lemma finite_cell_pairing_bound
    {ι X V : Type*} [Fintype ι] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (f : ι → X → V) (φ : X → V)
    (hf : ∀ i, Continuous (f i)) (hc : ∀ i, HasCompactSupport (f i))
    (hφ : Continuous φ) (hmean : ∀ i, (∫ x, f i x ∂μ) = 0)
    (hd : Pairwise (fun i j => Disjoint (tsupport (f i)) (tsupport (f j))))
    (c : ι → V) {ω : ℝ} (hosc : ∀ i x, x ∈ tsupport (f i) → ‖φ x-c i‖ ≤ ω) :
    |∫ x, inner ℝ (φ x) (∑ i, f i x) ∂μ| ≤ ω * ∫ x, ‖∑ i, f i x‖ ∂μ := by
  classical
  simp_rw [inner_sum]
  rw [integral_finsetSum _ (fun i _ => (hφ.inner (hf i)).integrable_of_hasCompactSupport (compact_inner_right (hc i) _))]
  calc
    _ ≤ ∑ i, |∫ x, inner ℝ (φ x) (f i x) ∂μ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ω * ∫ x, ‖f i x‖ ∂μ := Finset.sum_le_sum fun i _ =>
      vector_pairing_bound_of_zero_mean μ (f i) φ (hf i) (hc i) hφ (hmean i) (hosc i)
    _ = _ := by
      rw [← Finset.mul_sum,← integral_finsetSum _ (fun i _ => ((hf i).integrable_of_hasCompactSupport (hc i)).norm)]
      simp_rw [norm_finite_disjoint_sum f hd]

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal

lemma fine_cell_pairing_bound
    {X V : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    {K : Set X} (hK : IsCompact K) (φ : X → V) (hφ : Continuous φ)
    {ω : ℝ} (hω : 0 < ω) :
    ∃ δ > 0, ∀ (N : ℕ) (f : Fin N → X → V) (center : Fin N → X),
      (∀ i, Continuous (f i)) → (∀ i, HasCompactSupport (f i)) →
      (∀ i, (∫ x, f i x ∂μ) = 0) →
      Pairwise (fun i j => Disjoint (tsupport (f i)) (tsupport (f j))) →
      (∀ i, tsupport (f i) ⊆ K) →
      (∀ i, tsupport (f i) ⊆ Metric.ball (center i) δ) →
      |∫ x, inner ℝ (φ x) (∑ i, f i x) ∂μ| ≤ ω * ∫ x, ‖∑ i, f i x‖ ∂μ := by
  classical
  obtain ⟨d,hd,hcont⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hφ.continuousOn) ω hω
  refine ⟨d/2,by positivity,?_⟩
  intro N f center hf hc hmean hdis hsK hsball
  have hex : ∀ i, ∃ c : V, ∀ x ∈ tsupport (f i), ‖φ x-c‖ ≤ ω := by
    intro i
    by_cases hi : (tsupport (f i)).Nonempty
    · obtain ⟨z,hz⟩ := hi
      refine ⟨φ z,fun x hx => ?_⟩
      have hdist : dist x z < d := by
        have h1 := hsball i hx
        have h2 := hsball i hz
        rw [Metric.mem_ball] at h1 h2
        have hh := dist_triangle_right x z (center i)
        linarith
      have hh : ‖φ x - φ z‖ < ω := by
        simpa only [dist_eq_norm] using hcont x (hsK i hx) z (hsK i hz) hdist
      exact hh.le
    · exact ⟨0,fun x hx => (hi ⟨x,hx⟩).elim⟩
  choose c hc' using hex
  exact finite_cell_pairing_bound μ f φ hf hc hφ hmean hdis c hc'

lemma inner_tendsto_zero_of_dense_tests
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (T : W → V) (hT : DenseRange T) (z : ℕ → V)
    {C : ℝ} (hC : 0 ≤ C) (hz : ∀ n, ‖z n‖ ≤ C)
    (ht : ∀ w, Tendsto (fun n => inner ℝ (T w) (z n)) atTop (𝓝 0)) :
    ∀ v, Tendsto (fun n => inner ℝ v (z n)) atTop (𝓝 0) := by
  intro v
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨w,hw⟩ := hT.exists_dist_lt v (show 0 < ε/(2*(C+1)) by positivity)
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (ht w) (ε/2) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have he : inner ℝ v (z n) = inner ℝ (v-T w) (z n) + inner ℝ (T w) (z n) := by
    rw [inner_sub_left]; ring
  rw [Real.dist_eq, sub_zero, he]
  calc
    _ ≤ |inner ℝ (v-T w) (z n)| + |inner ℝ (T w) (z n)| := abs_add_le _ _
    _ ≤ ‖v-T w‖ * C + |inner ℝ (T w) (z n)| := by
      gcongr
      exact (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (hz n) (norm_nonneg _))
    _ < ε := by
      have htest : |inner ℝ (T w) (z n)| < ε/2 := by
        simpa only [Real.dist_eq,sub_zero] using hN n hn
      rw [dist_eq_norm] at hw
      have hmul := mul_le_mul_of_nonneg_right hw.le hC
      have hd : ε/(2*(C+1))*C < ε/2 := by
        have hpos : 0 < 2*(C+1) := by positivity
        have hdiv := (div_lt_iff₀ hpos).mpr (show ε*C < (ε/2)*(2*(C+1)) by nlinarith)
        simpa only [div_mul_eq_mul_div] using hdiv
      linarith

lemma fine_cells_continuous_pairing_tendsto_zero
    {X V : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (μ : Measure X) [IsFiniteMeasure μ]
    {K : Set X} (hK : IsCompact K)
    (N : ℕ → ℕ) (f : (n : ℕ) → Fin (N n) → X → V)
    (center : (n : ℕ) → Fin (N n) → X)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hf : ∀ n i, Continuous (f n i)) (hc : ∀ n i, HasCompactSupport (f n i))
    (hmean : ∀ n i, (∫ x, f n i x ∂μ) = 0)
    (hdis : ∀ n, Pairwise (fun i j => Disjoint (tsupport (f n i)) (tsupport (f n j))))
    (hsK : ∀ n i, tsupport (f n i) ⊆ K)
    (hsball : ∀ n i, tsupport (f n i) ⊆ Metric.ball (center n i) (δ n))
    (hLp : ∀ n, MemLp (fun x => ∑ i, f n i x) 2 μ)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ n, ‖(hLp n).toLp _‖ ≤ C)
    (φ : X → V) (hφ : Continuous φ) :
    Tendsto (fun n => ∫ x, inner ℝ (φ x) (∑ i, f n i x) ∂μ) atTop (𝓝 0) := by
  let M : ℝ := ‖(memLp_const (p := 2) (μ := μ) (1 : ℝ)).toLp _‖
  have hM : 0 ≤ M := norm_nonneg _
  rw [Metric.tendsto_atTop]
  intro ε hε
  let ω := ε/(M*C+1)
  have hω : 0 < ω := div_pos hε (by positivity)
  obtain ⟨d,hd,hfine⟩ := fine_cell_pairing_bound μ hK φ hφ hω
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp ((tendsto_order.mp hδ).2 d hd)
  refine ⟨n₀,fun n hn => ?_⟩
  have hs : ∀ i, tsupport (f n i) ⊆ Metric.ball (center n i) d := fun i x hx =>
    (Metric.ball_subset_ball (hn₀ n hn).le) (hsball n i hx)
  have hp := hfine (N n) (f n) (center n) (hf n) (hc n) (hmean n) (hdis n) (hsK n) hs
  have hl : (∫ x, ‖∑ i, f n i x‖ ∂μ) ≤ M*C :=
    (integral_norm_le_L2_const μ (hLp n)).trans
      (mul_le_mul_of_nonneg_left (hbound n) hM)
  rw [Real.dist_eq,sub_zero]
  apply lt_of_le_of_lt (hp.trans (mul_le_mul_of_nonneg_left hl hω.le))
  change ε/(M*C+1)*(M*C) < ε
  have hpos : 0 < M*C+1 := by positivity
  have hdiv := (div_lt_iff₀ hpos).mpr (show ε*(M*C) < ε*(M*C+1) by nlinarith)
  simpa only [div_mul_eq_mul_div] using hdiv

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Scalarization_WeakDensityLp
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

lemma weak_tendsto_zero_of_inner_tendsto_zero
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (z : ℕ → V) (hz : ∀ v, Tendsto (fun n => inner ℝ v (z n)) atTop (𝓝 0)) :
    Tendsto (fun n => toWeakSpace ℝ V (z n)) atTop (𝓝 0) := by
  have hB : Function.Injective ((topDualPairing ℝ V).flip) := by
    intro x y h
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
    intro L
    exact LinearMap.congr_fun h L
  apply (WeakBilin.tendsto_iff_forall_eval_tendsto (topDualPairing ℝ V).flip hB).mpr
  intro L
  change Tendsto (fun n => L (z n)) atTop (𝓝 (L 0))
  simpa only [InnerProductSpace.toDual_symm_apply, map_zero]
    using hz ((InnerProductSpace.toDual ℝ V).symm L)

lemma fine_cells_weak_L2_tendsto_zero
    {X V : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopologyEither X V]
    (μ : Measure X) [IsFiniteMeasure μ] [μ.WeaklyRegular]
    {K : Set X} (hK : IsCompact K)
    (N : ℕ → ℕ) (f : (n : ℕ) → Fin (N n) → X → V)
    (center : (n : ℕ) → Fin (N n) → X)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hf : ∀ n i, Continuous (f n i)) (hc : ∀ n i, HasCompactSupport (f n i))
    (hmean : ∀ n i, (∫ x, f n i x ∂μ) = 0)
    (hdis : ∀ n, Pairwise (fun i j => Disjoint (tsupport (f n i)) (tsupport (f n j))))
    (hsK : ∀ n i, tsupport (f n i) ⊆ K)
    (hsball : ∀ n i, tsupport (f n i) ⊆ Metric.ball (center n i) (δ n))
    (hLp : ∀ n, MemLp (fun x => ∑ i, f n i x) 2 μ)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ n, ‖(hLp n).toLp _‖ ≤ C) :
    Tendsto (fun n => toWeakSpace ℝ (Lp V 2 μ) ((hLp n).toLp _)) atTop (𝓝 0) := by
  apply weak_tendsto_zero_of_inner_tendsto_zero
  apply inner_tendsto_zero_of_dense_tests
    (BoundedContinuousFunction.toLp 2 μ ℝ : (X →ᵇ V) →L[ℝ] Lp V 2 μ)
    (BoundedContinuousFunction.toLp_denseRange V μ ℝ (by simp)) _ hC hbound
  intro φ
  have h := fine_cells_continuous_pairing_tendsto_zero μ hK N f center δ hδ
    hf hc hmean hdis hsK hsball hLp hC hbound φ φ.continuous
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [φ.coeFn_toLp 2 μ ℝ, (hLp n).coeFn_toLp] with x hx hy
  rw [hx,hy]

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped ENNReal Matrix.Norms.Elementwise

lemma CompactGlobalUpdate.gradient_mean_zero_on_superset
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {O U : Set Coord3} (hOU : O ⊆ U)
    {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ O u A) :
    (∫ x, voltageGradient R.du x ∂μ.restrict U) = 0 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact voltageGradient_mean_zero μ R.smooth_du R.compact_du
  · intro x hx
    exact image_eq_zero_of_notMem_tsupport
      (fun hs => hx (hOU (R.support_du (tsupport_voltageGradient hs))))

lemma CompactGlobalUpdate.flux_mean_zero_on_superset
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {O U : Set Coord3} (hOU : O ⊆ U)
    {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ O u A) :
    (∫ x, fieldVector (R.dF x) ∂μ.restrict U) = 0 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact R.flux_mean_zero μ
  · intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hs => hx (hOU (R.support_dF hs)))]
    exact map_zero fieldVectorCLM

lemma fine_updates_weak_tendsto_zero
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} (hUb : Bornology.IsBounded U)
    [IsFiniteMeasure (μ.restrict U)] [(μ.restrict U).WeaklyRegular]
    {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (N : ℕ → ℕ) (O : (n : ℕ) → Fin (N n) → Set Coord3)
    (center : (n : ℕ) → Fin (N n) → Coord3)
    (R : ∀ n i, CompactGlobalUpdate μ (O n i) u A)
    (S : ℕ → CompactGlobalUpdate μ U u A)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hOU : ∀ n i, O n i ⊆ U)
    (hsmall : ∀ n i, O n i ⊆ Metric.ball (center n i) (δ n))
    (hdis : ∀ n, Pairwise (fun i j => Disjoint (O n i) (O n j)))
    (hsu : ∀ n, (S n).du = fun x => ∑ i, (R n i).du x)
    (hsF : ∀ n, (S n).dF = fun x => ∑ i, (R n i).dF x)
    {CE CF : ℝ} (hCE : 0 ≤ CE) (hCF : 0 ≤ CF)
    (hbE : ∀ n, ‖((S n).memLp_gradient_correction μ).toLp _‖ ≤ CE)
    (hbF : ∀ n, ‖((S n).memLp_flux_correction μ).toLp _‖ ≤ CF) :
    Tendsto (fun n => toWeakSpace ℝ (Lp FieldVector 2 (μ.restrict U))
      (((S n).memLp_gradient_correction μ).toLp _)) atTop (𝓝 0) ∧
    Tendsto (fun n => toWeakSpace ℝ (Lp FieldVector 2 (μ.restrict U))
      (((S n).memLp_flux_correction μ).toLp _)) atTop (𝓝 0) := by
  classical
  have heq : ∀ n, voltageGradient (S n).du = fun x => ∑ i, voltageGradient (R n i).du x := by
    intro n
    rw [hsu n]
    exact funext (voltageGradient_sum _ (fun i => (R n i).smooth_du.differentiable (by simp)))
  have hfq : ∀ n, (fun x => fieldVector ((S n).dF x)) =
      fun x => ∑ i, fieldVector ((R n i).dF x) := by
    intro n
    funext x
    rw [hsF n]
    exact map_sum fieldVectorCLM _ _
  have hsE : ∀ n i, tsupport (voltageGradient (R n i).du) ⊆ O n i :=
    fun n i => tsupport_voltageGradient.trans (R n i).support_du
  have hsF' : ∀ n i, tsupport (fun x => fieldVector ((R n i).dF x)) ⊆ O n i :=
    fun n i => (tsupport_comp_subset (map_zero fieldVectorCLM) _).trans (R n i).support_dF
  constructor
  · have hLp : ∀ n, MemLp (fun x => ∑ i, voltageGradient (R n i).du x) 2 (μ.restrict U) := by
      intro n
      rw [← heq n]
      exact (S n).memLp_gradient_correction μ
    have ht := fine_cells_weak_L2_tendsto_zero (μ.restrict U) hUb.isCompact_closure
      N (fun n i => voltageGradient (R n i).du) center δ hδ
      (fun n i => continuous_voltageGradient (R n i).smooth_du)
      (fun n i => compact_voltageGradient (R n i).compact_du)
      (fun n i => (R n i).gradient_mean_zero_on_superset μ (hOU n i))
      (fun n i j hij => (hdis n hij).mono (hsE n i) (hsE n j))
      (fun n i => (hsE n i).trans ((hOU n i).trans subset_closure))
      (fun n i => (hsE n i).trans (hsmall n i)) hLp hCE
      (fun n => by simpa only [← heq n] using hbE n)
    simpa only [← heq] using ht
  · have hLp : ∀ n, MemLp (fun x => ∑ i, fieldVector ((R n i).dF x)) 2 (μ.restrict U) := by
      intro n
      rw [← hfq n]
      exact (S n).memLp_flux_correction μ
    have ht := fine_cells_weak_L2_tendsto_zero (μ.restrict U) hUb.isCompact_closure
      N (fun n i x => fieldVector ((R n i).dF x)) center δ hδ
      (fun n i => fieldVectorCLM.continuous.comp (R n i).smooth_dF.continuous)
      (fun n i => (R n i).compact_dF.comp_left (map_zero fieldVectorCLM))
      (fun n i => (R n i).flux_mean_zero_on_superset μ (hOU n i))
      (fun n i j hij => (hdis n hij).mono (hsF' n i) (hsF' n j))
      (fun n i => (hsF' n i).trans ((hOU n i).trans subset_closure))
      (fun n i => (hsF' n i).trans (hsmall n i)) hLp hCF
      (fun n => by simpa only [← hfq n] using hbF n)
    simpa only [← hfq] using ht

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_WeakCompactHilbert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology

lemma continuous_weakDual_to_weakHilbert
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] :
    Continuous (fun L : WeakDual ℝ V =>
      toWeakSpace ℝ V ((InnerProductSpace.toDual ℝ V).symm (WeakDual.toStrongDual L))) := by
  apply WeakBilin.continuous_of_continuous_eval
  intro T
  have h := WeakDual.eval_continuous (𝕜 := ℝ)
    ((InnerProductSpace.toDual ℝ V).symm T)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext L
  change T ((InnerProductSpace.toDual ℝ V).symm (WeakDual.toStrongDual L)) =
    (WeakDual.toStrongDual L) ((InnerProductSpace.toDual ℝ V).symm T)
  rw [← InnerProductSpace.toDual_symm_apply,real_inner_comm,
    InnerProductSpace.toDual_symm_apply]

lemma isCompact_weak_closedBall
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (x : V) (r : ℝ) :
    IsCompact (toWeakSpace ℝ V '' Metric.closedBall x r) := by
  have hc := (WeakDual.isCompact_closedBall (InnerProductSpace.toDual ℝ V x) r).image
    (continuous_weakDual_to_weakHilbert (V := V))
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  ext y
  constructor
  · rintro ⟨z,hz,rfl⟩
    refine ⟨StrongDual.toWeakDual (InnerProductSpace.toDual ℝ V z),?_,?_⟩
    · change dist ((InnerProductSpace.toDual ℝ V) z) ((InnerProductSpace.toDual ℝ V) x) ≤ r
      simpa only [LinearIsometryEquiv.dist_map] using (Metric.mem_closedBall.mp hz)
    · exact congrArg (toWeakSpace ℝ V) ((InnerProductSpace.toDual ℝ V).symm_apply_apply z)
  · rintro ⟨L,hL,rfl⟩
    refine ⟨(InnerProductSpace.toDual ℝ V).symm (WeakDual.toStrongDual L),?_,rfl⟩
    change dist ((InnerProductSpace.toDual ℝ V).symm (WeakDual.toStrongDual L)) x ≤ r
    rw [← (InnerProductSpace.toDual ℝ V).symm_apply_apply x,
      LinearIsometryEquiv.dist_map]
    exact hL

lemma continuous_weak_pair
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] :
    Continuous (fun p : WeakSpace ℝ V × WeakSpace ℝ W =>
      toWeakSpace ℝ (V × W) ((toWeakSpace ℝ V).symm p.1,(toWeakSpace ℝ W).symm p.2)) := by
  apply WeakBilin.continuous_of_continuous_eval
  intro L
  let LV := L.comp (ContinuousLinearMap.inl ℝ V W)
  let LW := L.comp (ContinuousLinearMap.inr ℝ V W)
  have hV := (WeakBilin.eval_continuous (topDualPairing ℝ V).flip LV).comp (continuous_fst : Continuous (Prod.fst : WeakSpace ℝ V × WeakSpace ℝ W → WeakSpace ℝ V))
  have hW := (WeakBilin.eval_continuous (topDualPairing ℝ W).flip LW).comp (continuous_snd : Continuous (Prod.snd : WeakSpace ℝ V × WeakSpace ℝ W → WeakSpace ℝ W))
  convert hV.add hW using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  change L ((toWeakSpace ℝ V).symm p.1,(toWeakSpace ℝ W).symm p.2) =
    L ((toWeakSpace ℝ V).symm p.1,0) + L (0,(toWeakSpace ℝ W).symm p.2)
  rw [← map_add]
  simp

lemma isCompact_weak_product_closedBalls
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    (r s : ℝ) :
    IsCompact (toWeakSpace ℝ (V × W) ''
      (Metric.closedBall (0 : V) r ×ˢ Metric.closedBall (0 : W) s)) := by
  have h := ((isCompact_weak_closedBall (0 : V) r).prod
    (isCompact_weak_closedBall (0 : W) s)).image (continuous_weak_pair (V := V) (W := W))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  constructor
  · rintro ⟨⟨x,y⟩,⟨hx,hy⟩,rfl⟩
    exact ⟨(toWeakSpace ℝ V x,toWeakSpace ℝ W y),⟨⟨x,hx,rfl⟩,⟨y,hy,rfl⟩⟩,rfl⟩
  · rintro ⟨⟨x,y⟩,⟨⟨a,ha,rfl⟩,⟨b,hb,rfl⟩⟩,rfl⟩
    exact ⟨(a,b),⟨ha,hb⟩,rfl⟩

lemma isCompact_weak_closure_of_pair_bounds
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    (S : Set (V × W)) {r s : ℝ}
    (hS : ∀ z ∈ S, ‖z.1‖ ≤ r ∧ ‖z.2‖ ≤ s) :
    IsCompact (closure (toWeakSpace ℝ (V × W) '' S)) := by
  let K := toWeakSpace ℝ (V × W) ''
    (Metric.closedBall (0 : V) r ×ˢ Metric.closedBall (0 : W) s)
  have hk : IsCompact K := isCompact_weak_product_closedBalls r s
  apply hk.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hk.isClosed
  rintro _ ⟨z,hz,rfl⟩
  exact ⟨z,by simpa only [mem_prod,Metric.mem_closedBall,dist_zero_right] using hS z hz,rfl⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Scalarization_FineScalarSequence
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open MeasureTheory Set Filter Topology Matrix
open scoped ENNReal Matrix.Norms.Elementwise

lemma eventually_ApproxScalar_of_tendstoInMeasure
    {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (μ : Measure X) (Z : ℕ → Lp V 2 μ × Lp V 2 μ) (s : ℕ → X → ℝ)
    {a b : ℝ} (hsm : ∀ n, Measurable (s n))
    (hsb : ∀ n, ∀ᵐ x ∂μ, s n x ∈ Icc a b)
    (ht : TendstoInMeasure μ (fun n x => (Z n).2 x-s n x • (Z n).1 x) atTop (fun _ => 0)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ApproxScalar μ a b ε (Z n) := by
  intro ε hε
  have hh := (tendstoInMeasure_iff_norm.mp ht) ε hε
  simp only [sub_zero] at hh
  filter_upwards [hh.eventually (eventually_le_nhds (ENNReal.ofReal_pos.mpr hε))] with n hn
  exact ⟨s n,hsm n,hsb n,hn⟩

lemma measurable_matrix_diagonal {X : Type*} [MeasurableSpace X]
    {A : X → Symmetric3} (hA : Measurable A) (i : Fin 3) :
    Measurable (fun x => (A x).val i i) := by
  have hc : Continuous (fun q : Symmetric3 => q.val i i) :=
    (continuous_apply i).comp ((continuous_apply i).comp continuous_subtype_val)
  exact hc.measurable.comp hA

theorem exists_fine_scalar_sequence
    (μ : Measure Coord3) [μ.IsAddHaarMeasure] [Measure.InnerRegularCompactLTTop μ]
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {U : Set Coord3} (hUb : Bornology.IsBounded U) (hUm : MeasurableSet U)
    [IsFiniteMeasure (μ.restrict U)] [(μ.restrict U).WeaklyRegular]
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3) (hAm : Measurable A)
    (hE : MemLp (voltageGradient u) 2 (μ.restrict U))
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U))
    (hint : SmoothFluxIntegrable μ U (conductivityFlux u A))
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    (hreg : μ (U \ regularRegion u A U) = 0)
    (hgraph : ∀ᵐ x ∂μ, x ∈ U → A x ∈ matrixFiniteLaminate a b) :
    ∃ S : ℕ → CompactGlobalUpdate μ U u A,
      (∀ n, μ (U \ regularRegion (fun x => u x+(S n).du x) (S n).tensor U) = 0) ∧
      (∀ n, ∀ᵐ x ∂μ, x ∈ U → (S n).tensor x ∈ matrixFiniteLaminate a b) ∧
      Tendsto (fun n => toWeakSpace ℝ _ ((S n).fieldPair μ hE hF)) atTop
        (𝓝 (toWeakSpace ℝ _ (hE.toLp _,hF.toLp _))) ∧
      (∀ ε > 0, ∀ᶠ n in atTop, ApproxScalar (μ.restrict U) a b ε ((S n).fieldPair μ hE hF)) := by
  classical
  let η : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hηp : ∀ n, 0 < η n := fun n => div_pos zero_lt_one (Nat.cast_add_one_pos n)
  have hηt : Tendsto η atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose N O center R S hcell hdis hsu hsF hregS hgraphS hbad using
    fun n => fine_global_scalar_tensor_approximation μ ha hab hUb u A hAm hint hdiv
      hreg hgraph (hηp n) (hηp n) (hηp n)
  have hBnd := fun n => (S n).correction_energy_bound μ hUm hreg hE hF hint hdiv ha hab (hgraphS n)
  have hCE : 0 ≤ (b/a+1)*‖hE.toLp _‖ := by have hb := ha.trans hab; positivity
  have hCF : 0 ≤ (b^2/a)*‖hE.toLp _‖+‖hF.toLp _‖ := by positivity
  obtain ⟨hwE,hwF⟩ := fine_updates_weak_tendsto_zero μ hUb N O center R S η hηt
    (fun n i => subset_closure.trans (hcell n i).2.1)
    (fun n i => subset_closure.trans (hcell n i).2.2) hdis hsu hsF hCE hCF
    (fun n => (hBnd n).1) (fun n => (hBnd n).2)
  have hw : Tendsto (fun n => toWeakSpace ℝ _ ((S n).fieldPair μ hE hF)) atTop
      (𝓝 (toWeakSpace ℝ _ (hE.toLp _,hF.toLp _))) := by
    have ht := continuous_weak_pair.tendsto (0,0) |>.comp (hwE.prodMk_nhds hwF)
    have ht' := ht.const_add (toWeakSpace ℝ _ (hE.toLp _,hF.toLp _))
    simpa [CompactGlobalUpdate.fieldPair,Function.comp_def,← map_add] using ht'
  let Z := fun n => (S n).fieldPair μ hE hF
  let s : ℕ → Coord3 → ℝ := fun n x => ((S n).tensor x).val 0 0
  have hsm : ∀ n, Measurable (s n) := fun n => measurable_matrix_diagonal (S n).measurable_tensor 0
  have hsb : ∀ n, ∀ᵐ x ∂μ.restrict U, s n x ∈ Icc a b := by
    intro n
    filter_upwards [(ae_restrict_iff' hUm).mpr (hgraphS n)] with x hx
    exact matrixFiniteLaminate_diagonal_bounds ha hx 0
  let B := fun n => U \ (S n).tensor ⁻¹' spectralExtension (scalarNeighbourhood a b (η n))
  have hBt : Tendsto (fun n => (μ.restrict U) (B n)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa using ENNReal.tendsto_ofReal hηt)
    · exact Eventually.of_forall fun _ => bot_le
    · exact Eventually.of_forall fun n => (Measure.restrict_apply_le U (B n)).trans (hbad n)
  have hdef : ∀ n, ∀ᵐ x ∂μ.restrict U, x ∉ B n →
      ‖(Z n).2 x-s n x • (Z n).1 x‖ ≤ 2*η n * ‖(Z n).1 x‖ := by
    intro n
    filter_upwards [(S n).fieldPair_ae μ hUm hreg hE hF,ae_restrict_mem hUm] with x hx hxU
    intro hxB
    have hxG : (S n).tensor x ∈ spectralExtension (scalarNeighbourhood a b (η n)) := by
      by_contra hn
      exact hxB ⟨hxU,hn⟩
    dsimp only [Z,s]
    rw [hx.1,hx.2]
    exact scalarNeighbourhood_defect_bound (hηp n).le hxG _
  have hr := defect_tendstoInMeasure_of_small_exceptions (μ.restrict U)
    (fun n => (Z n).1) (fun n x => (Z n).2 x-s n x • (Z n).1 x)
    (fun n => 2*η n) (fun n => mul_nonneg (by norm_num) (hηp n).le)
    (by simpa using hηt.const_mul 2) B hBt
    (show 0 ≤ (b/a)*‖hE.toLp _‖ by have hb := ha.trans hab; positivity)
    (fun n => ((S n).fieldPair_energy_bound μ hUm hreg hE hF hint hdiv ha hab (hgraphS n)).1) hdef
  exact ⟨S,hregS,hgraphS,hw,eventually_ApproxScalar_of_tendstoInMeasure (μ.restrict U) Z s hsm hsb hr⟩

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open MeasureTheory Set Filter Topology

lemma CompactGlobalUpdate.fieldPair_trans
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} (hUm : MeasurableSet U)
    {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A)
    (S : CompactGlobalUpdate μ U (fun x => u x+R.du x) R.tensor)
    (hreg : μ (U \ regularRegion u A U) = 0)
    (hreg' : μ (U \ regularRegion (fun x => u x+R.du x) R.tensor U) = 0)
    (hE : MemLp (voltageGradient u) 2 (μ.restrict U))
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U))
    (hE' : MemLp (voltageGradient (fun x => u x+R.du x)) 2 (μ.restrict U))
    (hF' : MemLp (voltageFlux (fun x => u x+R.du x) R.tensor) 2 (μ.restrict U)) :
    (R.trans μ S).fieldPair μ hE hF = S.fieldPair μ hE' hF' := by
  have he : (fun x => u x+(R.trans μ S).du x) =
      (fun x => (u x+R.du x)+S.du x) := by
    funext x
    exact (add_assoc _ _ _).symm
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [(R.trans μ S).fieldPair_ae μ hUm hreg hE hF,
      S.fieldPair_ae μ hUm hreg' hE' hF'] with x hx hy
    rw [hx.1,hy.1,he]
  · apply Lp.ext
    filter_upwards [(R.trans μ S).fieldPair_ae μ hUm hreg hE hF,
      S.fieldPair_ae μ hUm hreg' hE' hF'] with x hx hy
    rw [hx.2,hy.2,he]
    rfl

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Scalarization_DenseClosureApprox
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology

lemma dense_property_in_closure
    {X : Type*} [TopologicalSpace X] (S : Set X) (P : X → Prop)
    (h : ∀ x ∈ S, ∃ z : ℕ → X, Tendsto z atTop (𝓝 x) ∧
      (∀ n, z n ∈ S) ∧ ∀ᶠ n in atTop, P (z n)) :
    Dense {x : closure S | P x.val} := by
  rw [Subtype.dense_iff]
  apply closure_minimal _ isClosed_closure
  intro x hx
  obtain ⟨z,hz,hzS,hzP⟩ := h x hx
  apply mem_closure_of_tendsto hz
  filter_upwards [hzP] with n hn
  exact ⟨⟨z n,subset_closure (hzS n)⟩,hn,rfl⟩

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal

lemma finiteUpdatePairs_nonempty
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (hAm : Measurable A)
    (hE : MemLp (voltageGradient u) 2 (μ.restrict U))
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U)) {a b : ℝ}
    (hreg : μ (U \ regularRegion u A U) = 0)
    (hgraph : ∀ᵐ x ∂μ, x ∈ U → A x ∈ matrixFiniteLaminate a b) :
    (finiteUpdatePairs μ U u A hE hF a b).Nonempty := by
  refine ⟨(CompactGlobalUpdate.refl μ U u A hAm).fieldPair μ hE hF,
    CompactGlobalUpdate.refl μ U u A hAm,?_,hgraph,rfl⟩
  simpa only [CompactGlobalUpdate.refl,Pi.zero_apply,add_zero] using hreg

lemma dense_ApproxScalar_in_finiteUpdateClosure
    (μ : Measure Coord3) [μ.IsAddHaarMeasure] [Measure.InnerRegularCompactLTTop μ]
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {U : Set Coord3} (hUb : Bornology.IsBounded U) (hUm : MeasurableSet U)
    [IsFiniteMeasure (μ.restrict U)] [(μ.restrict U).WeaklyRegular]
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3)
    (hE : MemLp (voltageGradient u) 2 (μ.restrict U))
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U))
    (hint : SmoothFluxIntegrable μ U (conductivityFlux u A))
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    (hreg : μ (U \ regularRegion u A U) = 0) {ε : ℝ} (hε : 0 < ε) :
    Dense {z : closure (toWeakSpace ℝ _ '' finiteUpdatePairs μ U u A hE hF a b) |
      ApproxScalar (μ.restrict U) a b ε ((toWeakSpace ℝ _).symm z.val)} := by
  apply dense_property_in_closure
  rintro _ ⟨Z,⟨R,hregR,hgraphR,rfl⟩,rfl⟩
  obtain ⟨hER,hFR⟩ := R.fields_memLp μ hUm hreg hE hF
  obtain ⟨hintR,hdivR⟩ := R.preserves_harmonic μ hint hdiv
  obtain ⟨S,hregS,hgraphS,hw,happrox⟩ := exists_fine_scalar_sequence μ ha hab hUb hUm
    (fun x => u x+R.du x) R.tensor R.measurable_tensor hER hFR hintR hdivR hregR hgraphR
  have he : ∀ n, (R.trans μ (S n)).fieldPair μ hE hF = (S n).fieldPair μ hER hFR :=
    fun n => R.fieldPair_trans μ hUm (S n) hreg hregR hE hF hER hFR
  refine ⟨fun n => toWeakSpace ℝ _ ((R.trans μ (S n)).fieldPair μ hE hF),?_,?_,?_⟩
  · simpa only [he,R.fieldPair_eq μ hUm hreg hE hF hER hFR] using hw
  · intro n
    refine ⟨_,⟨R.trans μ (S n),?_,hgraphS n,rfl⟩,rfl⟩
    simpa only [CompactGlobalUpdate.trans,Pi.add_apply,add_assoc] using hregS n
  · filter_upwards [happrox ε hε] with n hn
    change ApproxScalar (μ.restrict U) a b ε ((R.trans μ (S n)).fieldPair μ hE hF)
    rwa [he n]

theorem exact_scalar_in_finiteUpdateClosure
    (μ : Measure Coord3) [μ.IsAddHaarMeasure] [Measure.InnerRegularCompactLTTop μ]
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {U : Set Coord3} (hUb : Bornology.IsBounded U) (hUm : MeasurableSet U)
    [IsFiniteMeasure (μ.restrict U)] [(μ.restrict U).WeaklyRegular]
    [SeparableSpace (Lp FieldVector 2 (μ.restrict U))]
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3) (hAm : Measurable A)
    (hE : MemLp (voltageGradient u) 2 (μ.restrict U))
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U))
    (hint : SmoothFluxIntegrable μ U (conductivityFlux u A))
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    (hreg : μ (U \ regularRegion u A U) = 0)
    (hgraph : ∀ᵐ x ∂μ, x ∈ U → A x ∈ matrixFiniteLaminate a b) :
    ∃ (Z : Lp FieldVector 2 (μ.restrict U) × Lp FieldVector 2 (μ.restrict U))
      (s : Coord3 → ℝ),
      toWeakSpace ℝ _ Z ∈ closure (toWeakSpace ℝ _ '' finiteUpdatePairs μ U u A hE hF a b) ∧
      Measurable s ∧ (∀ᵐ x ∂μ.restrict U, s x ∈ Icc a b ∧ Z.2 x = s x • Z.1 x) := by
  apply exact_scalar_of_weak_density (μ.restrict U) hab.le
  · apply isCompact_weak_closure_of_pair_bounds
    rintro Z ⟨R,hregR,hgraphR,rfl⟩
    exact R.fieldPair_energy_bound μ hUm hreg hE hF hint hdiv ha hab hgraphR
  · exact ((finiteUpdatePairs_nonempty μ hAm hE hF hreg hgraph).image _).closure
  · intro ε hε
    exact dense_ApproxScalar_in_finiteUpdateClosure μ ha hab hUb hUm u A hE hF hint hdiv hreg hε

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_VoltagePoincare
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open MeasureTheory Set Filter Topology Matrix
open scoped ENNReal NNReal

lemma gradientCoordinateConstant_bound (D : Coord3 →L[ℝ] (Fin 2 → ℝ)) :
    ‖D‖ ≤ gradientCoordinateConstant * ‖gradientVectorCLM D‖ :=
  exists_gradientCoordinateConstant.choose_spec.2 D

lemma compact_voltage_poincare
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} (hUb : Bornology.IsBounded U)
    {v : Coord3 → Fin 2 → ℝ} (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (hvc : HasCompactSupport v) (hvs : tsupport v ⊆ U) :
    (eLpNorm v 2 (μ.restrict U)).toReal ≤
      (eLpNormLESNormFDerivOfLeConst (Fin 2 → ℝ) μ U 2 2 *
        gradientCoordinateConstant : ℝ≥0) *
      (eLpNorm (voltageGradient v) 2 (μ.restrict U)).toReal := by
  have hvm : MemLp (voltageGradient v) 2 μ := memLp_voltageGradient_smooth_compact μ hv hvc
  have he := eLpNorm_le_eLpNorm_fderiv μ
    (hv.of_le (by simp) : ContDiff ℝ 1 v) ((subset_tsupport v).trans hvs)
    (p := 2) (by norm_num) (by norm_num [Coord3,Module.finrank_pi]) hUb
  have hder : eLpNorm (fderiv ℝ v) 2 μ ≤
      gradientCoordinateConstant * eLpNorm (voltageGradient v) 2 μ :=
    eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
      (Eventually.of_forall fun point => by
        exact_mod_cast gradientCoordinateConstant_bound (fderiv ℝ v point)) 2
  have hall : eLpNorm v 2 μ ≤
      (eLpNormLESNormFDerivOfLeConst (Fin 2 → ℝ) μ U 2 2 : ℝ≥0∞) *
      (gradientCoordinateConstant * eLpNorm (voltageGradient v) 2 μ) := by
    exact he.trans (mul_le_mul le_rfl hder (by positivity) (by positivity))
  have hfin : (eLpNormLESNormFDerivOfLeConst (Fin 2 → ℝ) μ U 2 2 : ℝ≥0∞) *
      (gradientCoordinateConstant * eLpNorm (voltageGradient v) 2 μ) ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.mul_ne_top ENNReal.coe_ne_top hvm.eLpNorm_ne_top)
  have ht := ENNReal.toReal_mono hfin hall
  rw [eLpNorm_restrict_eq_of_support_subset
      ((subset_tsupport v).trans hvs),
    eLpNorm_restrict_eq_of_support_subset
      ((subset_tsupport _).trans (tsupport_voltageGradient.trans hvs))]
  simpa only [ENNReal.toReal_mul,ENNReal.coe_toReal,NNReal.coe_mul,mul_assoc] using ht

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_VoltageJetCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

lemma zeroVoltageJets_poincare
    (μ : Measure Coord3) [μ.IsAddHaarMeasure] {U : Set Coord3}
    (hUb : Bornology.IsBounded U) {z : VoltageJetSpace μ U} (hz : z ∈ zeroVoltageJets μ U) :
    ‖z.1‖ ≤ (eLpNormLESNormFDerivOfLeConst (Fin 2 → ℝ) μ U 2 2 *
      gradientCoordinateConstant : ℝ≥0) * ‖z.2‖ := by
  apply closure_minimal (s := compactVoltageJets μ U) ?_ ?_ hz
  · rintro _ ⟨v,hv,hvc,hvs,hvm,hvg,rfl⟩
    change ‖hvm.toLp _‖ ≤ _ * ‖hvg.toLp _‖
    rw [Lp.norm_toLp,Lp.norm_toLp]
    exact compact_voltage_poincare μ hUb hv hvc hvs
  · exact isClosed_le continuous_fst.norm (continuous_const.mul continuous_snd.norm)

lemma zeroVoltageGradientMap_closed_range
    (μ : Measure Coord3) [μ.IsAddHaarMeasure] {U : Set Coord3}
    (hUb : Bornology.IsBounded U) : IsClosed (Set.range (zeroVoltageGradientMap μ U)) := by
  let C : ℝ≥0 := eLpNormLESNormFDerivOfLeConst (Fin 2 → ℝ) μ U 2 2 * gradientCoordinateConstant
  apply ((zeroVoltageGradientMap μ U).antilipschitz_of_bound (K := C+1) ?_).isClosed_range
    (zeroVoltageGradientMap μ U).uniformContinuous
  intro z
  change ‖z.val‖ ≤ ((C+1 : ℝ≥0) : ℝ) * ‖z.val.2‖
  rw [Prod.norm_def,max_le_iff]
  constructor
  · exact (zeroVoltageJets_poincare μ hUb z.property).trans
      (by change (C : ℝ) * _ ≤ _; push_cast; nlinarith [norm_nonneg z.val.2])
  · have hC : 0 ≤ (C : ℝ) := C.coe_nonneg
    push_cast
    nlinarith [norm_nonneg z.val.2]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_AffineWeakConstraints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set

lemma constraint_of_mem_weak_closure
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {S T : Set V} (hT : IsClosed T) (hc : Convex ℝ T) (hST : S ⊆ T)
    {z : V} (hz : toWeakSpace ℝ V z ∈ closure (toWeakSpace ℝ V '' S)) : z ∈ T := by
  have hz' := closure_mono (image_mono hST) hz
  rw [← hc.toWeakSpace_closure ℝ,hT.closure_eq] at hz'
  obtain ⟨x,hx,hxz⟩ := hz'
  exact (toWeakSpace ℝ V).injective hxz ▸ hx

lemma submodule_constraint_of_mem_weak_closure
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (M : Submodule ℝ W) (hM : IsClosed (M : Set W))
    (L : V →L[ℝ] W) (w : W) {S : Set V}
    (hS : ∀ z ∈ S, L z-w ∈ M) {z : V}
    (hz : toWeakSpace ℝ V z ∈ closure (toWeakSpace ℝ V '' S)) : L z-w ∈ M := by
  apply constraint_of_mem_weak_closure
    (T := {z : V | L z-w ∈ M}) _ _ hS hz
  · exact hM.preimage (L.continuous.sub continuous_const)
  · convert ((M.convex.translate_preimage_left (-w)).linear_preimage L.toLinearMap) using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [mem_ofPred_eq,mem_preimage,ContinuousLinearMap.coe_coe,sub_eq_add_neg,SetLike.mem_coe]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Scalarization_ScalarizationAffineLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal

lemma CompactGlobalUpdate.gradientCorrection_mem_range
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A) :
    (R.memLp_gradient_correction μ).toLp _ ∈ (zeroVoltageGradientMap μ U).range := by
  let hv : MemLp R.du 2 (μ.restrict U) :=
    (R.smooth_du.continuous.memLp_of_hasCompactSupport R.compact_du).restrict U
  let z : VoltageJetSpace μ U := (hv.toLp _,(R.memLp_gradient_correction μ).toLp _)
  have hz : z ∈ compactVoltageJetModule μ U :=
    ⟨R.du,R.smooth_du,R.compact_du,R.support_du,hv,R.memLp_gradient_correction μ,rfl⟩
  exact ⟨⟨z,(compactVoltageJetModule μ U).le_topologicalClosure hz⟩,rfl⟩

lemma finiteUpdateClosure_affine_constraints
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} (hUb : Bornology.IsBounded U)
    {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (hE : MemLp (voltageGradient u) 2 (μ.restrict U))
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U)) {a b : ℝ}
    {Z : Lp FieldVector 2 (μ.restrict U) × Lp FieldVector 2 (μ.restrict U)}
    (hZ : toWeakSpace ℝ _ Z ∈ closure (toWeakSpace ℝ _ '' finiteUpdatePairs μ U u A hE hF a b)) :
    (∃ v : zeroVoltageJets μ U, Z.1 = hE.toLp _ + v.val.2) ∧
      Z.2-hF.toLp _ ∈ (allVoltageGradients μ U)ᗮ := by
  constructor
  · have hg := submodule_constraint_of_mem_weak_closure
      (zeroVoltageGradientMap μ U).range (zeroVoltageGradientMap_closed_range μ hUb)
      (ContinuousLinearMap.fst ℝ _ _) (hE.toLp _)
      (S := finiteUpdatePairs μ U u A hE hF a b) (z := Z) ?_ hZ
    · obtain ⟨v,hv⟩ := hg
      refine ⟨v,?_⟩
      change v.val.2 = Z.1 - hE.toLp _ at hv
      rw [hv,add_sub_cancel]
    · rintro _ ⟨R,hreg,hgraph,rfl⟩
      change hE.toLp _ + (R.memLp_gradient_correction μ).toLp _ - hE.toLp _ ∈ _
      rw [add_sub_cancel_left]
      exact R.gradientCorrection_mem_range μ
  · apply submodule_constraint_of_mem_weak_closure
      ((allVoltageGradients μ U)ᗮ) (Submodule.isClosed_orthogonal _)
      (ContinuousLinearMap.snd ℝ _ _) (hF.toLp _) (S := finiteUpdatePairs μ U u A hE hF a b) ?_ hZ
    rintro _ ⟨R,hreg,hgraph,rfl⟩
    change hF.toLp _ + (R.memLp_flux_correction μ).toLp _ - hF.toLp _ ∈ _
    rw [add_sub_cancel_left]
    exact R.fluxCorrection_mem_orthogonal μ

theorem exact_scalarization_Cauchy_flux
    (μ : Measure Coord3) [μ.IsAddHaarMeasure] [Measure.InnerRegularCompactLTTop μ]
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {U : Set Coord3} (hUb : Bornology.IsBounded U) (hUm : MeasurableSet U)
    [IsFiniteMeasure (μ.restrict U)] [(μ.restrict U).WeaklyRegular]
    [SeparableSpace (Lp FieldVector 2 (μ.restrict U))]
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3) (hAm : Measurable A)
    (hE : MemLp (voltageGradient u) 2 (μ.restrict U))
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U))
    (hint : SmoothFluxIntegrable μ U (conductivityFlux u A))
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    (hreg : μ (U \ regularRegion u A U) = 0)
    (hgraph : ∀ᵐ x ∂μ, x ∈ U → A x ∈ matrixFiniteLaminate a b) :
    ∃ (v : zeroVoltageJets μ U) (F : Lp FieldVector 2 (μ.restrict U)) (s : Coord3 → ℝ),
      Measurable s ∧
      (∀ᵐ x ∂μ.restrict U, s x ∈ Icc a b ∧ F x = s x • ((hE.toLp _ + v.val.2) x)) ∧
      (∀ W ∈ allVoltageGradients μ U, inner ℝ W F = inner ℝ W (hF.toLp _)) := by
  obtain ⟨Z,s,hZ,hsm,hs⟩ := exact_scalar_in_finiteUpdateClosure μ ha hab hUb hUm u A hAm
    hE hF hint hdiv hreg hgraph
  obtain ⟨⟨v,hv⟩,hFv⟩ := finiteUpdateClosure_affine_constraints μ hUb hE hF hZ
  refine ⟨v,Z.2,s,hsm,?_,?_⟩
  · simpa only [hv] using hs
  · intro W hW
    have he := (Submodule.mem_orthogonal _ _).mp hFv W hW
    rw [inner_sub_right] at he
    exact sub_eq_zero.mp he

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_VoltageH1Completion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open MeasureTheory Set Filter Topology TopologicalSpace Matrix
open scoped ENNReal Matrix.Norms.Elementwise

lemma zeroVoltageJets_le_H1 (μ : Measure Coord3) (U : Set Coord3) :
    zeroVoltageJets μ U ≤ voltageH1Jets μ U := by
  apply Submodule.topologicalClosure_minimal
  · rintro _ ⟨v,hv,hvc,hvs,hvm,hvg,rfl⟩
    apply (Submodule.span ℝ (smoothVoltageJets μ U)).le_topologicalClosure
    exact Submodule.subset_span ⟨v,hv,hvm,hvg,rfl⟩
  · exact Submodule.isClosed_topologicalClosure _

lemma voltageH1_gradient_mem (μ : Measure Coord3) (U : Set Coord3)
    {z : VoltageJetSpace μ U} (hz : z ∈ voltageH1Jets μ U) :
    z.2 ∈ allVoltageGradients μ U := by
  have hs : voltageH1Jets μ U ≤
      (allVoltageGradients μ U).comap (ContinuousLinearMap.snd ℝ _ _).toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨v,hv,hvm,hvg,rfl⟩
      apply (Submodule.span ℝ (smoothVoltageGradients μ U)).le_topologicalClosure
      exact Submodule.subset_span ⟨v,hv,hvg,rfl⟩
    · exact (Submodule.isClosed_topologicalClosure _).preimage continuous_snd
  exact hs hz

lemma divergence_pairing_compact_voltage
    (μ : Measure Coord3) {U : Set Coord3}
    {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U))
    (hint : SmoothFluxIntegrable μ U (conductivityFlux u A))
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    {z : VoltageJetSpace μ U} (hz : z ∈ compactVoltageJets μ U) :
    inner ℝ z.2 (hF.toLp _) = 0 := by
  obtain ⟨v,hv,hvc,hvs,hvm,hvg,rfl⟩ := hz
  rw [L2.inner_def]
  have he : (∫ x, inner ℝ ((hvg.toLp _) x) ((hF.toLp _) x) ∂μ.restrict U) =
      ∫ x, inner ℝ (voltageGradient v x) (voltageFlux u A x) ∂μ.restrict U := by
    apply integral_congr_ae
    filter_upwards [hvg.coeFn_toLp,hF.coeFn_toLp] with x hx hy
    rw [hx,hy]
  rw [he,setIntegral_eq_integral_of_forall_compl_eq_zero]
  · have hvc' (j) : HasCompactSupport (fun x => v x j) :=
      hvc.comp_left (g := fun v : Fin 2 → ℝ => v j) rfl
    have hvs' (j) : tsupport (fun x => v x j) ⊆ U :=
      (tsupport_comp_subset (g := fun v : Fin 2 → ℝ => v j) rfl v).trans hvs
    have hv' (j) : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => v x j) :=
      (contDiff_apply ℝ ℝ j).comp hv
    simp_rw [voltageFlux,voltageGradient_pairing v (hv.differentiable (by simp))]
    rw [integral_finsetSum _ (fun j _ => hint j _ (hv' j) (hvc' j) (hvs' j))]
    simp only [hdiv _ _ (hv' _) (hvc' _) (hvs' _),Finset.sum_const_zero]
  · intro x hx
    have hg : voltageGradient v x = 0 := image_eq_zero_of_notMem_tsupport
      (fun hs => hx (hvs (tsupport_voltageGradient hs)))
    rw [hg,inner_zero_left]

lemma divergence_pairing_zeroVoltageJets
    (μ : Measure Coord3) {U : Set Coord3}
    {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U))
    (hint : SmoothFluxIntegrable μ U (conductivityFlux u A))
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    {z : VoltageJetSpace μ U} (hz : z ∈ zeroVoltageJets μ U) :
    inner ℝ z.2 (hF.toLp _) = 0 := by
  apply closure_minimal (s := compactVoltageJets μ U) ?_ ?_ hz
  · exact fun z hz => divergence_pairing_compact_voltage μ hF hint hdiv hz
  · exact isClosed_eq (continuous_snd.inner continuous_const) continuous_const

theorem exact_scalarization_H1
    (μ : Measure Coord3) [μ.IsAddHaarMeasure] [Measure.InnerRegularCompactLTTop μ]
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {U : Set Coord3} (hUb : Bornology.IsBounded U) (hUm : MeasurableSet U)
    [IsFiniteMeasure (μ.restrict U)] [(μ.restrict U).WeaklyRegular]
    [SeparableSpace (Lp FieldVector 2 (μ.restrict U))]
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3) (hAm : Measurable A)
    (hu : MemLp u 2 (μ.restrict U))
    (hE : MemLp (voltageGradient u) 2 (μ.restrict U))
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U))
    (huH1 : (hu.toLp _,hE.toLp _) ∈ voltageH1Jets μ U)
    (hint : SmoothFluxIntegrable μ U (conductivityFlux u A))
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    (hreg : μ (U \ regularRegion u A U) = 0)
    (hgraph : ∀ᵐ x ∂μ, x ∈ U → A x ∈ matrixFiniteLaminate a b) :
    ∃ (z : voltageH1Jets μ U) (F : Lp FieldVector 2 (μ.restrict U)) (s : Coord3 → ℝ),
      Measurable s ∧ MemLp s ∞ (μ.restrict U) ∧
      z.val-(hu.toLp _,hE.toLp _) ∈ zeroVoltageJets μ U ∧
      (∀ᵐ x ∂μ.restrict U, s x ∈ Icc a b ∧ F x = s x • (z.val.2 x)) ∧
      (∀ W : voltageH1Jets μ U, inner ℝ W.val.2 F = inner ℝ W.val.2 (hF.toLp _)) ∧
      (∀ W : zeroVoltageJets μ U, inner ℝ W.val.2 F = 0) := by
  obtain ⟨v,F,s,hsm,hs,hC⟩ := exact_scalarization_Cauchy_flux μ ha hab hUb hUm u A hAm
    hE hF hint hdiv hreg hgraph
  let z : voltageH1Jets μ U := ⟨(hu.toLp _,hE.toLp _) + v.val,
    (voltageH1Jets μ U).add_mem huH1 (zeroVoltageJets_le_H1 μ U v.property)⟩
  refine ⟨z,F,s,hsm,?_,?_,hs,?_,?_⟩
  · apply memLp_top_of_bound hsm.aestronglyMeasurable b
    filter_upwards [hs] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (ha.le.trans hx.1.1)]
    exact hx.1.2
  · change (hu.toLp _,hE.toLp _) + v.val - (hu.toLp _,hE.toLp _) ∈ _
    rw [add_sub_cancel_left]
    exact v.property
  · intro W
    exact hC _ (voltageH1_gradient_mem μ U W.property)
  · intro W
    rw [hC _ (voltageH1_gradient_mem μ U (zeroVoltageJets_le_H1 μ U W.property))]
    exact divergence_pairing_zeroVoltageJets μ hF hint hdiv W.property

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Scalarization_UniformMatrixScalarization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open MeasureTheory Set Filter Topology TopologicalSpace Matrix
open scoped ENNReal Matrix.Norms.Elementwise

lemma uniform_matrix_laminate_coverage {c C : ℝ} (hc : 0 < c) (hcC : c ≤ C)
    (A : Symmetric3)
    (hA : ∀ v : Coord3, c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A.val *ᵥ v) ∧
      v ⬝ᵥ (A.val *ᵥ v) ≤ C * (v ⬝ᵥ v)) :
    A ∈ matrixFiniteLaminate (laminateLower c C) (laminateUpper C) := by
  obtain ⟨Q,hQ,α,he⟩ := exists_orthogonal_diagonalization A.property
  refine ⟨Q,hQ,α,(uniform_laminate_coverage hc hcC).2.2 α ?_,he⟩
  intro i
  let v : Coord3 := Pi.single i 1
  have hnorm : (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v) = 1 := by
    rw [orthogonal_dotProduct hQ]
    simp [v,dotProduct,Pi.single_apply]
  have hback : Qᵀ *ᵥ (Q *ᵥ v) = v := by
    rw [mulVec_mulVec,hQ.1,one_mulVec]
  have hval : (Q *ᵥ v) ⬝ᵥ (A.val *ᵥ (Q *ᵥ v)) = α i := by
    rw [he,conjugateDiagonal_quadratic,hback]
    simp [v,Pi.single_apply]
  simpa only [hnorm,hval,mul_one] using hA (Q *ᵥ v)

theorem finite_field_scalarization_oai
    (μ : Measure Coord3) [μ.IsAddHaarMeasure] [Measure.InnerRegularCompactLTTop μ]
    {c C : ℝ} (hc : 0 < c) (hcC : c ≤ C)
    {U : Set Coord3} (hUb : Bornology.IsBounded U) (hUm : MeasurableSet U)
    [IsFiniteMeasure (μ.restrict U)] [(μ.restrict U).WeaklyRegular]
    [SeparableSpace (Lp FieldVector 2 (μ.restrict U))]
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3) (hAm : Measurable A)
    (hu : MemLp u 2 (μ.restrict U))
    (hE : MemLp (voltageGradient u) 2 (μ.restrict U))
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U))
    (huH1 : (hu.toLp _,hE.toLp _) ∈ voltageH1Jets μ U)
    (hint : SmoothFluxIntegrable μ U (conductivityFlux u A))
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    (hreg : μ (U \ regularRegion u A U) = 0)
    (hbound : ∀ᵐ x ∂μ, x ∈ U → ∀ v : Coord3,
      c * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((A x).val *ᵥ v) ∧
      v ⬝ᵥ ((A x).val *ᵥ v) ≤ C * (v ⬝ᵥ v)) :
    ∃ (z : voltageH1Jets μ U) (F : Lp FieldVector 2 (μ.restrict U)) (s : Coord3 → ℝ),
      Measurable s ∧ MemLp s ∞ (μ.restrict U) ∧
      z.val-(hu.toLp _,hE.toLp _) ∈ zeroVoltageJets μ U ∧
      (∀ᵐ x ∂μ.restrict U, s x ∈ Icc (laminateLower c C) (laminateUpper C) ∧
        F x = s x • (z.val.2 x)) ∧
      (∀ W : voltageH1Jets μ U, inner ℝ W.val.2 F = inner ℝ W.val.2 (hF.toLp _)) ∧
      (∀ W : zeroVoltageJets μ U, inner ℝ W.val.2 F = 0) := by
  apply exact_scalarization_H1 μ (uniform_laminate_coverage hc hcC).1
    (uniform_laminate_coverage hc hcC).2.1 hUb hUm u A hAm hu hE hF huH1 hint hdiv hreg
  filter_upwards [hbound] with x hx hxU
  exact uniform_matrix_laminate_coverage hc hcC (A x) (hx hxU)

end ScalarConductivity

end
end

end OAI
end

theorem solution : type_of% @OAI.ScalarConductivity.finite_field_scalarization_oai := @OAI.ScalarConductivity.finite_field_scalarization_oai
