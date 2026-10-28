-- Prove2me | solution 1 for OAI.ScalarConductivity.fine_global_scalar_tensor_approximation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:04:55.476522+00:00
-- url     : https://prove2.me/submissions/f6e8159c-45f0-4d98-b1b8-809d68b06832

import Mathlib
import Definitions.Def_OAIQ059C007
import Theorems.Thm_OAI_ScalarConductivity_exists_local_split_on_subpatch_retained

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

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_ProductFactorSpec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity
open Filter Topology

lemma productFactor_spec_le {M : ℝ} (hM : 0 < M) (α : DiagonalTriple) (i : Fin 3)
    (hα : 0 < α i ∧ α i ≤ M) :
    0 < productFactorMinus M α i ∧ 0 < productFactorPlus M α i ∧
      productFactorMinus M α i + productFactorPlus M α i = 2 ∧
      productFactorMinus M α i * productFactorPlus M α i = α i / M := by
  have hq : 0 < α i / M := div_pos hα.1 hM
  have hq1 : α i / M ≤ 1 := (div_le_one hM).mpr hα.2
  have hr : Real.sqrt (1 - α i / M) < 1 := by
    apply (Real.sqrt_lt' (by norm_num)).mpr
    linarith
  have hr0 := Real.sqrt_nonneg (1 - α i / M)
  have hrs := Real.sq_sqrt (sub_nonneg.mpr hq1)
  dsimp [productFactorMinus, productFactorPlus]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> nlinarith

lemma scalar_mem_interior_finiteLaminate {a b s : ℝ} (ha : 0 < a)
    (has : a < s) (hsb : s < b) :
    (fun _ : Fin 3 => s) ∈ interior {α : DiagonalTriple | IsFiniteLaminate a b α} := by
  let c : DiagonalTriple := fun _ => s
  let M : DiagonalTriple → ℝ := fun α => s + ‖α - c‖
  have hs : 0 < s := ha.trans has
  have hM (α : DiagonalTriple) : 0 < M α := by
    dsimp [M]
    positivity
  have halpha (α : DiagonalTriple) (i : Fin 3) : α i ≤ M α := by
    have hh : |α i - s| ≤ ‖α - c‖ := by
      simpa [c, Real.norm_eq_abs] using norm_le_pi_norm (α - c) i
    dsimp [M]
    linarith [le_abs_self (α i - s)]
  have hMc : M c = s := by simp [M]
  have hMc_cont : ContinuousAt M c := by
    fun_prop
  have hx (i : Fin 3) : ContinuousAt (fun α => productFactorMinus (M α) α i) c := by
    unfold productFactorMinus
    exact continuousAt_const.sub ((continuousAt_const.sub
      ((continuous_apply i).continuousAt.div hMc_cont (by rw [hMc]; exact hs.ne'))).sqrt)
  have hy (i : Fin 3) : ContinuousAt (fun α => productFactorPlus (M α) α i) c := by
    unfold productFactorPlus
    exact continuousAt_const.add ((continuousAt_const.sub
      ((continuous_apply i).continuousAt.div hMc_cont (by rw [hMc]; exact hs.ne'))).sqrt)
  let t : (Fin 3 → Bool) → DiagonalTriple → Fin 3 → ℝ :=
    fun σ α i => if σ i then productFactorPlus (M α) α i else productFactorMinus (M α) α i
  have htcont (σ : Fin 3 → Bool) (i : Fin 3) : ContinuousAt (fun α => t σ α i) c := by
    dsimp [t]
    split <;> [exact hy i; exact hx i]
  have htc (σ : Fin 3 → Bool) (i : Fin 3) : t σ c i = 1 := by
    simp [t, productFactorPlus, productFactorMinus, hMc, c, hs.ne']
  have hleaves (σ : Fin 3 → Bool) : ∀ᶠ α in 𝓝 c,
      a < M α * t σ α 0 * t σ α 1 * t σ α 2 ∧
        M α * t σ α 0 * t σ α 1 * t σ α 2 < b := by
    have hh := ((hMc_cont.mul (htcont σ 0)).mul (htcont σ 1)).mul (htcont σ 2)
    have hv : M c * t σ c 0 * t σ c 1 * t σ c 2 = s := by rw [hMc, htc, htc, htc]; ring
    exact hh.preimage_mem_nhds (isOpen_Ioo.mem_nhds (by
      change a < _ ∧ _ < b
      simp only [Pi.mul_apply, hv]
      exact ⟨has, hsb⟩))
  have hpos (i : Fin 3) : ∀ᶠ α : DiagonalTriple in 𝓝 c, 0 < α i :=
    (continuous_apply i).continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds hs)
  rw [mem_interior_iff_mem_nhds]
  filter_upwards [Filter.eventually_all.mpr hleaves, Filter.eventually_all.mpr hpos] with α hleaf hα
  have hspec (i : Fin 3) := productFactor_spec_le (hM α) α i ⟨hα i, halpha α i⟩
  have heq : (fun i => M α * productFactorMinus (M α) α i * productFactorPlus (M α) α i) = α := by
    ext i
    rw [mul_assoc, (hspec i).2.2.2]
    exact mul_div_cancel₀ _ (hM α).ne'
  rw [← heq]
  apply product_eight_leaf_laminate _ _ (fun i => (hspec i).1.ne')
    (fun i => (hspec i).2.1.ne') (fun i => (hspec i).2.2.1)
  intro t₀ t₁ t₂ ht₀ ht₁ ht₂
  rcases ht₀ with rfl | rfl <;> rcases ht₁ with rfl | rfl <;> rcases ht₂ with rfl | rfl
  · simpa [t] using hleaf ![false, false, false]
  · simpa [t] using hleaf ![false, false, true]
  · simpa [t] using hleaf ![false, true, false]
  · simpa [t] using hleaf ![false, true, true]
  · simpa [t] using hleaf ![true, false, false]
  · simpa [t] using hleaf ![true, false, true]
  · simpa [t] using hleaf ![true, true, false]
  · simpa [t] using hleaf ![true, true, true]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_RecoverJoinChild
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity
open Filter Topology

lemma div_self_div_eq (θ t : ℝ) (hθ : θ ≠ 0) : θ / (θ / t) = t := by
  by_cases ht : t = 0
  · simp [ht]
  · field_simp

lemma recoverJoinChild_join (i : Fin 3) {θ : ℝ} (hθ : θ ≠ 0)
    (α β : DiagonalTriple) : recoverJoinChild i θ β (coordinateJoin i θ α β) = α := by
  ext j
  by_cases hj : j = i
  · simp only [recoverJoinChild, coordinateJoin, hj, ite_true, inv_inv, add_sub_cancel_right]
    exact div_self_div_eq _ _ hθ
  · simp only [recoverJoinChild, coordinateJoin, hj, ite_false, add_sub_cancel_right]
    exact mul_div_cancel_left₀ _ hθ

lemma coordinateJoin_recoverJoinChild (i : Fin 3) {θ : ℝ} (hθ : θ ≠ 0)
    (β δ : DiagonalTriple) : coordinateJoin i θ (recoverJoinChild i θ β δ) β = δ := by
  ext j
  by_cases hj : j = i
  · simp only [recoverJoinChild, coordinateJoin, hj, ite_true]
    rw [div_self_div_eq _ _ hθ, sub_add_cancel, inv_inv]
  · simp only [recoverJoinChild, coordinateJoin, hj, ite_false]
    rw [mul_div_cancel₀ _ hθ, sub_add_cancel]

lemma continuousAt_recoverJoinChild (i : Fin 3) {θ : ℝ} (hθ : θ ≠ 0)
    (α β : DiagonalTriple) (hα : α i ≠ 0)
    (hjoin : coordinateJoin i θ α β i ≠ 0) :
    ContinuousAt (recoverJoinChild i θ β) (coordinateJoin i θ α β) := by
  apply continuousAt_pi.mpr
  intro j
  by_cases hj : j = i
  · subst j
    simp only [recoverJoinChild, ite_true]
    apply continuousAt_const.div
    · exact ((continuous_apply i).continuousAt.inv₀ hjoin).sub continuousAt_const
    · simp only [coordinateJoin, ite_true, inv_inv, add_sub_cancel_right]
      exact div_ne_zero hθ hα
  · simp only [recoverJoinChild, ite_eq_right hj]
    have hc : Continuous (fun δ : DiagonalTriple => δ j) := continuous_apply j
    exact (hc.continuousAt.sub continuousAt_const).div continuousAt_const hθ

lemma coordinateJoin_zero (i : Fin 3) (α β : DiagonalTriple) : coordinateJoin i 0 α β = β := by
  ext j
  simp [coordinateJoin]

lemma coordinateJoin_one (i : Fin 3) (α β : DiagonalTriple) : coordinateJoin i 1 α β = α := by
  ext j
  simp [coordinateJoin]

theorem isOpen_finiteLaminate {a b : ℝ} (ha : 0 < a) :
    IsOpen {α : DiagonalTriple | IsFiniteLaminate a b α} := by
  apply isOpen_iff_mem_nhds.mpr
  intro α hα
  induction hα with
  | scalar s has hsb =>
    exact mem_interior_iff_mem_nhds.mp (scalar_mem_interior_finiteLaminate ha has hsb)
  | @join i θ hθ₀ hθ₁ α β hα hβ ihα ihβ =>
    by_cases hθ : θ = 0
    · simpa [hθ, coordinateJoin_zero] using ihβ
    · let δ := coordinateJoin i θ α β
      have hαi : α i ≠ 0 := (ha.trans (hα.bounds ha i).1).ne'
      have hδi : δ i ≠ 0 :=
        (ha.trans (coordinateJoin_bounds ha (hα.bounds ha) (hβ.bounds ha) i ⟨hθ₀, hθ₁⟩ i).1).ne'
      have hc := continuousAt_recoverJoinChild i hθ α β hαi hδi
      have he : recoverJoinChild i θ β δ = α := recoverJoinChild_join i hθ α β
      have hm : ∀ᶠ δ' in 𝓝 δ, IsFiniteLaminate a b (recoverJoinChild i θ β δ') :=
        hc.preimage_mem_nhds (by rw [he]; exact ihα)
      filter_upwards [hm] with δ' hδ'
      have hj := IsFiniteLaminate.join i θ hθ₀ hθ₁ hδ' hβ
      simpa only [coordinateJoin_recoverJoinChild i hθ β δ'] using hj

lemma IsFiniteLaminate.permute {a b : ℝ} {α : DiagonalTriple}
    (h : IsFiniteLaminate a b α) (e : Equiv.Perm (Fin 3)) :
    IsFiniteLaminate a b (α ∘ e) := by
  induction h with
  | scalar s has hsb => exact .scalar s has hsb
  | @join i θ hθ₀ hθ₁ α β hα hβ ihα ihβ =>
    convert IsFiniteLaminate.join (e.symm i) θ hθ₀ hθ₁ ihα ihβ using 1
    all_goals try with_reducible_and_instances rfl
    ext j
    simp only [Function.comp_apply, coordinateJoin]
    congr 1
    exact propext ⟨fun h => by simpa using congrArg e.symm h,
      fun h => by simpa using congrArg e h⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_JoinHull
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
open Set Filter Topology

lemma subset_joinHull (U : Set DiagonalTriple) : U ⊆ joinHull U := fun _ => Or.inl

lemma joinHull_subset_laminate {a b : ℝ} {U : Set DiagonalTriple}
    (hU : ∀ α ∈ U, IsFiniteLaminate a b α) :
    ∀ α ∈ joinHull U, IsFiniteLaminate a b α := by
  rintro δ (hδ | ⟨i, θ, α, β, hθ₀, hθ₁, hα, hβ, rfl⟩)
  · exact hU δ hδ
  · exact .join i θ hθ₀ hθ₁ (hU α hα) (hU β hβ)

lemma isOpen_joinHull {a b : ℝ} (ha : 0 < a) {U : Set DiagonalTriple}
    (hU : IsOpen U) (hsub : ∀ α ∈ U, IsFiniteLaminate a b α) : IsOpen (joinHull U) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro δ (hδ | ⟨i, θ, α, β, hθ₀, hθ₁, hα, hβ, rfl⟩)
  · exact mem_of_superset (hU.mem_nhds hδ) (subset_joinHull U)
  · by_cases hθ : θ = 0
    · rw [hθ, coordinateJoin_zero]
      exact mem_of_superset (hU.mem_nhds hβ) (subset_joinHull U)
    · have hαi : α i ≠ 0 := (ha.trans ((hsub α hα).bounds ha i).1).ne'
      have hδi : coordinateJoin i θ α β i ≠ 0 :=
        (ha.trans (coordinateJoin_bounds ha ((hsub α hα).bounds ha)
          ((hsub β hβ).bounds ha) i ⟨hθ₀, hθ₁⟩ i).1).ne'
      have hc := continuousAt_recoverJoinChild i hθ α β hαi hδi
      have he := recoverJoinChild_join i hθ α β
      have hm : ∀ᶠ δ' in 𝓝 (coordinateJoin i θ α β), recoverJoinChild i θ β δ' ∈ U :=
        hc.preimage_mem_nhds (by rw [he]; exact hU.mem_nhds hα)
      filter_upwards [hm] with δ' hδ'
      exact Or.inr ⟨i, θ, recoverJoinChild i θ β δ', β,
        hθ₀, hθ₁, hδ', hβ, coordinateJoin_recoverJoinChild i hθ β δ'⟩

lemma joinHull_permute {U : Set DiagonalTriple}
    (hU : ∀ α ∈ U, ∀ e : Equiv.Perm (Fin 3), α ∘ e ∈ U) :
    ∀ α ∈ joinHull U, ∀ e : Equiv.Perm (Fin 3), α ∘ e ∈ joinHull U := by
  rintro δ (hδ | ⟨i, θ, α, β, hθ₀, hθ₁, hα, hβ, rfl⟩) e
  · exact Or.inl (hU δ hδ e)
  · refine Or.inr ⟨e.symm i, θ, α ∘ e, β ∘ e, hθ₀, hθ₁, hU α hα e, hU β hβ e, ?_⟩
    ext j
    simp only [Function.comp_apply, coordinateJoin]
    congr 1
    exact propext ⟨fun h => by simpa using congrArg e h,
      fun h => by simpa using congrArg e.symm h⟩

lemma depthClass_subset_succ (U : Set DiagonalTriple) (n : ℕ) :
    depthClass U n ⊆ depthClass U (n+1) := subset_joinHull _

lemma depthClass_mono (U : Set DiagonalTriple) : Monotone (depthClass U) :=
  monotone_nat_of_le_succ (depthClass_subset_succ U)

lemma depthClass_subset_laminate {a b : ℝ} {U : Set DiagonalTriple}
    (hU : ∀ α ∈ U, IsFiniteLaminate a b α) (n : ℕ) :
    ∀ α ∈ depthClass U n, IsFiniteLaminate a b α := by
  induction n with
  | zero => exact hU
  | succ n ih => exact joinHull_subset_laminate ih

lemma isOpen_depthClass {a b : ℝ} (ha : 0 < a) {U : Set DiagonalTriple}
    (hU : IsOpen U) (hsub : ∀ α ∈ U, IsFiniteLaminate a b α) (n : ℕ) :
    IsOpen (depthClass U n) := by
  induction n with
  | zero => exact hU
  | succ n ih => exact isOpen_joinHull ha ih (depthClass_subset_laminate hsub n)

lemma depthClass_permute {U : Set DiagonalTriple}
    (hU : ∀ α ∈ U, ∀ e : Equiv.Perm (Fin 3), α ∘ e ∈ U) (n : ℕ) :
    ∀ α ∈ depthClass U n, ∀ e : Equiv.Perm (Fin 3), α ∘ e ∈ depthClass U n := by
  induction n with
  | zero => exact hU
  | succ n ih => exact joinHull_permute ih

theorem IsFiniteLaminate.mem_some_depth {a b : ℝ} {U : Set DiagonalTriple}
    (hU : ∀ s, a < s → s < b → (fun _ => s) ∈ U)
    {α : DiagonalTriple} (hα : IsFiniteLaminate a b α) :
    ∃ n, α ∈ depthClass U n := by
  induction hα with
  | scalar s has hsb => exact ⟨0, hU s has hsb⟩
  | @join i θ hθ₀ hθ₁ α β hα hβ ihα ihβ =>
    obtain ⟨n, hn⟩ := ihα
    obtain ⟨m, hm⟩ := ihβ
    exact ⟨max n m + 1, Or.inr ⟨i, θ, α, β, hθ₀, hθ₁,
      depthClass_mono U (le_max_left n m) hn,
      depthClass_mono U (le_max_right n m) hm, rfl⟩⟩

theorem depthClass_plan {a b : ℝ} {U : Set DiagonalTriple}
    (hsub : ∀ α ∈ U, IsFiniteLaminate a b α) {n : ℕ} {δ : DiagonalTriple}
    (hδ : δ ∈ depthClass U (n+1)) (hn : δ ∉ depthClass U n) :
    ∃ i θ α β, 0 < θ ∧ θ < 1 ∧ α ∈ depthClass U n ∧ β ∈ depthClass U n ∧
      coordinateJoin i θ α β = δ ∧
      ∀ t ∈ Icc (0 : ℝ) 1, IsFiniteLaminate a b (coordinateJoin i t α β) := by
  rcases hδ with hδ | ⟨i, θ, α, β, hθ₀, hθ₁, hα, hβ, rfl⟩
  · exact (hn hδ).elim
  have hθne : θ ≠ 0 := by
    intro he
    apply hn
    simpa [he, coordinateJoin_zero] using hβ
  have hθne' : θ ≠ 1 := by
    intro he
    apply hn
    simpa [he, coordinateJoin_one] using hα
  refine ⟨i, θ, α, β, lt_of_le_of_ne hθ₀ (Ne.symm hθne),
    lt_of_le_of_ne hθ₁ hθne', hα, hβ, rfl, ?_⟩
  intro t ht
  exact .join i t ht.1 ht.2
    (depthClass_subset_laminate hsub n α hα) (depthClass_subset_laminate hsub n β hβ)

lemma isOpen_scalarNeighbourhood {a b ε : ℝ} (ha : 0 < a) :
    IsOpen (scalarNeighbourhood a b ε) := by
  have he : IsOpen {α : DiagonalTriple | ∃ s : ℝ, ‖α - (fun _ => s)‖ < ε} := by
    simp only [ofPred_exists]
    apply isOpen_iUnion
    intro s
    exact isOpen_lt (continuous_id.sub continuous_const).norm continuous_const
  exact (isOpen_finiteLaminate ha).inter he

lemma scalar_mem_scalarNeighbourhood {a b ε s : ℝ} (hε : 0 < ε)
    (has : a < s) (hsb : s < b) : (fun _ => s) ∈ scalarNeighbourhood a b ε := by
  refine ⟨.scalar s has hsb, s, ?_⟩
  simpa using hε

lemma scalarNeighbourhood_permute {a b ε : ℝ} {α : DiagonalTriple}
    (hα : α ∈ scalarNeighbourhood a b ε) (e : Equiv.Perm (Fin 3)) :
    α ∘ e ∈ scalarNeighbourhood a b ε := by
  rcases hα with ⟨hα, s, hs⟩
  refine ⟨hα.permute e, s, ?_⟩
  have he : ‖(α - (fun _ => s)) ∘ e‖ = ‖α - (fun _ => s)‖ :=
    le_antisymm
      ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
        (fun i => norm_le_pi_norm (α - fun _ => s) (e i)))
      ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 (fun i => by
        simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
          norm_le_pi_norm ((α - fun _ => s) ∘ e) (e.symm i)))
  change ‖(α - (fun _ => s)) ∘ e‖ < ε
  rw [he]
  exact hs

lemma isOpen_endpointGraph {P X : Type*} [TopologicalSpace P] [T1Space P]
    [TopologicalSpace X] (a b : P) {G U V : Set X}
    (hG : IsOpen G) (hU : IsOpen U) (hV : IsOpen V) :
    IsOpen (endpointGraph a b G U V) := by
  exact (hG.preimage continuous_snd).inter
    (((isOpen_ne.preimage continuous_fst).union
      (hU.preimage continuous_snd)).inter
      ((isOpen_ne.preimage continuous_fst).union
      (hV.preimage continuous_snd)))

lemma path_mem_endpointGraph {P X : Type*} (a b : P) (C : P → X)
    {K : Set P} {G U V : Set X} (hG : ∀ p ∈ K, C p ∈ G)
    (ha : C a ∈ U) (hb : C b ∈ V) :
    ∀ p ∈ K, (p, C p) ∈ endpointGraph a b G U V := by
  intro p hp
  refine ⟨hG p hp, ?_, ?_⟩
  · by_cases h : p = a
    · exact Or.inr (h ▸ ha)
    · exact Or.inl h
  · by_cases h : p = b
    · exact Or.inr (h ▸ hb)
    · exact Or.inl h

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PreliminaryQ
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

open MeasureTheory
open scoped ENNReal
section

lemma harmonic_parent_pos {x y θ : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hθ : 0 < θ) (hθ' : θ < 1) : 0 < (θ / x + (1 - θ) / y)⁻¹ := by
  exact inv_pos.mpr (add_pos (div_pos hθ hx) (div_pos (sub_pos.mpr hθ') hy))

theorem preliminary_fractions {x y θ : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hθ : 0 < θ) (hθ' : θ < 1) :
    let A := (θ / x + (1 - θ) / y)⁻¹
    let q_plus := x / A
    let q_minus := y / A
    let η_plus := θ / q_plus
    let η_minus := (1 - θ) / q_minus
    0 < q_plus ∧ 0 < q_minus ∧ 0 < η_plus ∧ 0 < η_minus ∧
      η_plus + η_minus = 1 ∧ η_plus * q_plus + η_minus * q_minus = 1 := by
  dsimp only
  have hA := harmonic_parent_pos hx hy hθ hθ'
  have hq_plus := div_pos hx hA
  have hq_minus := div_pos hy hA
  refine ⟨hq_plus, hq_minus, div_pos hθ hq_plus, div_pos (sub_pos.mpr hθ') hq_minus, ?_, ?_⟩
  · have hd : θ / x + (1 - θ) / y ≠ 0 := (inv_pos.mp hA).ne'
    rw [div_div_eq_mul_div, div_div_eq_mul_div]
    calc
      θ * (θ / x + (1 - θ) / y)⁻¹ / x +
          (1 - θ) * (θ / x + (1 - θ) / y)⁻¹ / y =
          (θ / x + (1 - θ) / y)⁻¹ * (θ / x + (1 - θ) / y) := by ring
      _ = 1 := inv_mul_cancel₀ hd
  · rw [div_mul_cancel₀ _ hq_plus.ne', div_mul_cancel₀ _ hq_minus.ne']
    ring

theorem preliminary_matrix_mean (i : Fin 3) {α β : DiagonalTriple} {θ : ℝ}
    (hα : 0 < α i) (hβ : 0 < β i) (hθ : 0 < θ) (hθ' : θ < 1) :
    let A := coordinateJoin i θ α β
    let η_plus := θ / preliminaryQ i A α
    let η_minus := (1 - θ) / preliminaryQ i A β
    η_plus • preliminaryB i A α + η_minus • preliminaryB i A β = A := by
  dsimp only
  let A := coordinateJoin i θ α β
  have hAi : 0 < A i := by simpa [A, coordinateJoin] using harmonic_parent_pos hα hβ hθ hθ'
  have hqα : preliminaryQ i A α ≠ 0 := (div_pos hα hAi).ne'
  have hqβ : preliminaryQ i A β ≠ 0 := (div_pos hβ hAi).ne'
  have hm : θ / preliminaryQ i A α + (1 - θ) / preliminaryQ i A β = 1 := by
    simpa [preliminaryQ, A, coordinateJoin] using
      (preliminary_fractions hα hβ hθ hθ').2.2.2.2.1
  ext j
  change (θ / preliminaryQ i A α) * preliminaryB i A α j +
    ((1 - θ) / preliminaryQ i A β) * preliminaryB i A β j = A j
  by_cases hj : j = i
  · simp only [preliminaryB, ite_eq_left hj]
    rw [← add_mul, hm, one_mul, hj]
  · simp only [preliminaryB, ite_eq_right hj]
    rw [← mul_assoc, div_mul_cancel₀ _ hqα, ← mul_assoc, div_mul_cancel₀ _ hqβ]
    exact (ite_eq_right hj).symm

theorem synchronized_path_is_join (i : Fin 3) {α β : DiagonalTriple} {θ τ : ℝ}
    (hα : 0 < α i) (hβ : 0 < β i) (hθ : 0 < θ) (hθ' : θ < 1)
    (hτ : 0 ≤ τ) (hτ' : τ ≤ 1) :
    let A := coordinateJoin i θ α β
    let q_plus := preliminaryQ i A α
    let q_minus := preliminaryQ i A β
    let q := τ * q_plus + (1 - τ) * q_minus
    let B := τ • preliminaryB i A α + (1 - τ) • preliminaryB i A β
    let w := τ * q_plus / q
    0 < q ∧ 0 ≤ w ∧ w ≤ 1 ∧
      stretchedDiagonal i q B = coordinateJoin i w α β := by
  dsimp only
  let A := coordinateJoin i θ α β
  let q_plus := preliminaryQ i A α
  let q_minus := preliminaryQ i A β
  let q := τ * q_plus + (1 - τ) * q_minus
  let w := τ * q_plus / q
  have hAi : 0 < A i := by simpa [A, coordinateJoin] using harmonic_parent_pos hα hβ hθ hθ'
  have hqp : 0 < q_plus := div_pos hα hAi
  have hqm : 0 < q_minus := div_pos hβ hAi
  have hq : 0 < q := by
    rcases eq_or_lt_of_le hτ with rfl | hτ
    · simpa [q] using hqm
    · exact add_pos_of_pos_of_nonneg (mul_pos hτ hqp)
        (mul_nonneg (sub_nonneg.mpr hτ') hqm.le)
  have hwp : 0 ≤ w := div_nonneg (mul_nonneg hτ hqp.le) hq.le
  have hwm : w ≤ 1 := (div_le_one hq).mpr (by dsimp [q]; nlinarith)
  refine ⟨hq, hwp, hwm, ?_⟩
  have hw : 1 - w = (1 - τ) * q_minus / q := by dsimp [w]; field_simp; dsimp [q]; ring
  ext j
  change stretchedDiagonal i q (τ • preliminaryB i A α +
    (1 - τ) • preliminaryB i A β) j = coordinateJoin i w α β j
  by_cases hj : j = i
  · subst j
    simp only [stretchedDiagonal, coordinateJoin, preliminaryB, ite_true, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    rw [hw]
    have he : w / α i + ((1 - τ) * q_minus / q) / β i = (q * A i)⁻¹ := by
      dsimp [w, q_plus, q_minus, preliminaryQ]
      field_simp
      ring
    rw [he, inv_inv]
    ring
  · simp only [stretchedDiagonal, coordinateJoin, preliminaryB, ite_eq_right hj,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hw]
    dsimp [w, q_plus, q_minus]
    ring

end
open Matrix Filter Topology

lemma isClosed_orthogonalFrames : IsClosed orthogonalFrames := by
  apply IsClosed.inter
  · exact isClosed_eq (by fun_prop) continuous_const
  · exact isClosed_eq (by fun_prop) continuous_const

lemma orthogonalFrames_entry_bound {Q : Mat3} (hQ : Q ∈ orthogonalFrames) (i j : Fin 3) :
    |Q i j| ≤ 1 := by
  have hsum : ∑ k, Q i k ^ 2 = 1 := by
    have hh := congrArg (fun A : Mat3 => A i i) hQ.2
    simpa [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using hh
  have hh : Q i j ^ 2 ≤ ∑ k, Q i k ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (Q i k)) (Finset.mem_univ j)
  rw [hsum] at hh
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

lemma isCompact_orthogonalFrames : IsCompact orthogonalFrames := by
  apply (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1)).matrix.of_isClosed_subset
    isClosed_orthogonalFrames
  intro Q hQ i j
  exact abs_le.mp (orthogonalFrames_entry_bound hQ i j)

lemma roots_charpoly_diagonal (α : Fin 3 → ℝ) :
    (diagonal α).charpoly.roots = Finset.univ.val.map α := by
  rw [Matrix.charpoly_diagonal]
  simpa only [Multiset.map_map, Function.comp_def, Finset.prod] using
    (Polynomial.roots_multiset_prod_X_sub_C (Finset.univ.val.map α))

lemma same_multiset_permutation {α β : Fin 3 → ℝ}
    (h : Finset.univ.val.map α = Finset.univ.val.map β) :
    ∃ e : Equiv.Perm (Fin 3), ∀ i, β (e i) = α i := by
  classical
  have hc (c : ℝ) : Fintype.card { i // α i = c } = Fintype.card { i // β i = c } := by
    have hd := congrArg (Multiset.count c) h
    simp only [Multiset.count_map] at hd
    simpa only [Fintype.card_subtype, Finset.card, Finset.filter_val, eq_comm] using hd
  let ef (c : ℝ) := Fintype.equivOfCardEq (hc c)
  exact ⟨Equiv.ofFiberEquiv ef, Equiv.ofFiberEquiv_map ef⟩

lemma diagonalizations_permute {A : Mat3} {α β : Fin 3 → ℝ} {Q R : Mat3}
    (hQ : Q ∈ orthogonalFrames) (hR : R ∈ orthogonalFrames)
    (hA : A = Q * diagonal α * Qᵀ) (hB : A = R * diagonal β * Rᵀ) :
    ∃ e : Equiv.Perm (Fin 3), ∀ i, β (e i) = α i := by
  have ha : A.charpoly = (diagonal α).charpoly := by
    rw [hA, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hQ.1, Matrix.one_mul]
  have hb : A.charpoly = (diagonal β).charpoly := by
    rw [hB, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hR.1, Matrix.one_mul]
  apply same_multiset_permutation
  rw [← roots_charpoly_diagonal, ← roots_charpoly_diagonal, ← ha, ← hb]

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

lemma diagonalization_pullback {A Q : Mat3} {α : Fin 3 → ℝ}
    (hQ : Q ∈ orthogonalFrames) (hA : A = Q * diagonal α * Qᵀ) :
    Qᵀ * A * Q = diagonal α := by
  rw [hA]
  calc
    Qᵀ * (Q * diagonal α * Qᵀ) * Q = (Qᵀ * Q) * diagonal α * (Qᵀ * Q) := by
      noncomm_ring
    _ = diagonal α := by rw [hQ.1, Matrix.one_mul, Matrix.mul_one]

lemma spectralExtension_rep_mem {U : Set (Fin 3 → ℝ)}
    (hperm : ∀ α ∈ U, ∀ e : Equiv.Perm (Fin 3), α ∘ e ∈ U)
    {A : Symmetric3} (hA : A ∈ spectralExtension U) {Q : Mat3} {α : Fin 3 → ℝ}
    (hQ : Q ∈ orthogonalFrames) (hrep : A.val = Q * diagonal α * Qᵀ) : α ∈ U := by
  obtain ⟨R, hR, β, hβ, hβrep⟩ := hA
  obtain ⟨e, he⟩ := diagonalizations_permute hR hQ hβrep hrep
  have h := hperm β hβ e.symm
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext i
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using (he (e.symm i))

lemma continuous_diagonal_pullback :
    Continuous (fun p : Mat3 × Mat3 => Matrix.diag (p.1ᵀ * p.2 * p.1)) :=
  ((continuous_fst.matrix_transpose.matrix_mul continuous_snd).matrix_mul
    continuous_fst).matrix_diag

lemma continuous_diagonal_pushforward :
    Continuous (fun p : Mat3 × (Fin 3 → ℝ) => p.1 * diagonal p.2 * p.1ᵀ) :=
  (continuous_fst.matrix_mul continuous_snd.matrix_diagonal).matrix_mul
    continuous_fst.matrix_transpose

lemma tendsto_diagonal_pullback {Qn An : ℕ → Mat3} {Q A : Mat3}
    {αn : ℕ → Fin 3 → ℝ} (hQn : ∀ n, Qn n ∈ orthogonalFrames)
    (hrepn : ∀ n, An n = Qn n * diagonal (αn n) * (Qn n)ᵀ)
    (hQ : Tendsto Qn atTop (𝓝 Q)) (hA : Tendsto An atTop (𝓝 A)) :
    Tendsto αn atTop (𝓝 (Matrix.diag (Qᵀ * A * Q))) := by
  have hh := continuous_diagonal_pullback.continuousAt.tendsto.comp (hQ.prodMk_nhds hA)
  change Tendsto (fun n => Matrix.diag ((Qn n)ᵀ * An n * Qn n)) atTop
    (𝓝 (Matrix.diag (Qᵀ * A * Q))) at hh
  simpa only [diagonalization_pullback (hQn _) (hrepn _), Matrix.diag_diagonal] using hh

lemma limit_diagonal_rep {Qn An : ℕ → Mat3} {Q A : Mat3}
    {αn : ℕ → Fin 3 → ℝ} {α : Fin 3 → ℝ}
    (hrepn : ∀ n, An n = Qn n * diagonal (αn n) * (Qn n)ᵀ)
    (hQ : Tendsto Qn atTop (𝓝 Q)) (hA : Tendsto An atTop (𝓝 A))
    (hα : Tendsto αn atTop (𝓝 α)) : A = Q * diagonal α * Qᵀ := by
  have hh := continuous_diagonal_pushforward.continuousAt.tendsto.comp (hQ.prodMk_nhds hα)
  change Tendsto (fun n => Qn n * diagonal (αn n) * (Qn n)ᵀ) atTop
    (𝓝 (Q * diagonal α * Qᵀ)) at hh
  simp only [← hrepn] at hh
  exact tendsto_nhds_unique hA hh

theorem isOpen_spectralExtension {U : Set (Fin 3 → ℝ)} (hU : IsOpen U)
    (hperm : ∀ α ∈ U, ∀ e : Equiv.Perm (Fin 3), α ∘ e ∈ U) :
    IsOpen (spectralExtension U) := by
  let : FirstCountableTopology Mat3 := inferInstanceAs
    (FirstCountableTopology (Fin 3 → Fin 3 → ℝ))
  suffices hc : IsClosed (spectralExtension U)ᶜ by
    simpa only [compl_compl] using hc.isOpen_compl
  apply IsSeqClosed.isClosed
  intro An A hAn hlim hA
  choose Qn hQn αn hrepn using fun n => exists_orthogonal_diagonalization (An n).property
  obtain ⟨Q, hQ, φ, hφ, hQlim⟩ := isCompact_orthogonalFrames.tendsto_subseq hQn
  have hAlim : Tendsto (fun n => (An (φ n)).val) atTop (𝓝 A.val) :=
    (continuous_subtype_val.tendsto A).comp (hlim.comp hφ.tendsto_atTop)
  let α := Matrix.diag (Qᵀ * A.val * Q)
  have hαlim : Tendsto (fun n => αn (φ n)) atTop (𝓝 α) :=
    tendsto_diagonal_pullback (fun n => hQn (φ n)) (fun n => hrepn (φ n)) hQlim hAlim
  have hrep : A.val = Q * diagonal α * Qᵀ :=
    limit_diagonal_rep (fun n => hrepn (φ n)) hQlim hAlim hαlim
  have hα : α ∈ U := spectralExtension_rep_mem hperm hA hQ hrep
  have hev : ∀ᶠ n in atTop, αn (φ n) ∈ U := hαlim (hU.mem_nhds hα)
  obtain ⟨n, hn⟩ := hev.exists
  exact hAn (φ n) ⟨Qn (φ n), hQn (φ n), αn (φ n), hn, hrepn (φ n)⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_Symmetrize
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
open Matrix Set Filter Topology
open scoped Matrix.Norms.Elementwise

lemma gram_det_ne_zero {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (E : Matrix m n ℝ) (hE : LinearIndependent ℝ E.col) : (Eᵀ * E).det ≠ 0 := by
  have hinj : Function.Injective E.mulVec := Matrix.mulVec_injective_iff.mpr hE
  have hker : LinearMap.ker (Eᵀ * E).mulVecLin = ⊥ := by
    rw [Matrix.ker_mulVecLin_transpose_mul_self]
    exact LinearMap.ker_eq_bot.mpr hinj
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_injective_iff_isUnit.mp (LinearMap.ker_eq_bot.mp hker)))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CrossingHxx
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3
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

open Matrix Set Filter Topology
open scoped Matrix.Norms.Elementwise

lemma pushGradient_rank {m : Type*} [Fintype m] (J : Mat3)
    (hJ : J.det ≠ 0) (E : Matrix (Fin 3) m ℝ) (hE : LinearIndependent ℝ E.col) :
    LinearIndependent ℝ (pushGradient J E).col := by
  apply Matrix.mulVec_injective_iff.mp
  intro v w hvw
  apply Matrix.mulVec_injective_iff.mpr hE
  have h := congrArg Jᵀ.mulVec hvw
  simpa only [Matrix.mulVec_mulVec, pushGradient_leftInverse J hJ E] using h

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_UniformNormBound
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

section
open Filter Topology

lemma scalar_cutoff_segment {a b c z : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c ∧ c ≤ 1) (hz : -a ≤ z ∧ z ≤ b) :
    -a ≤ c * z ∧ c * z ≤ b := by
  constructor
  · calc
      -a ≤ c * (-a) := by nlinarith [mul_nonneg (sub_nonneg.mpr hc.2) ha]
      _ ≤ c * z := mul_le_mul_of_nonneg_left hz.1 hc.1
  · calc
      c * z ≤ c * b := mul_le_mul_of_nonneg_left hz.2 hc.1
      _ ≤ b := by nlinarith [mul_nonneg (sub_nonneg.mpr hc.2) hb]

end

open Set Filter Topology

lemma lineShiftGradientOperator_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (d : E) (c : ℝ) (L : E →L[ℝ] ℝ) :
    lineShiftGradientOperator d c L = c • L.smulRight d := rfl

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_LocalPullback
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
open Set Filter Topology

lemma localPullback_support {E V : Type*} [TopologicalSpace E] [Zero V]
    (X : OpenPartialHomeomorph E E) (f : E → V) :
    Function.support (localPullback X f) ⊆ X.symm '' (Function.support f ∩ X.target) := by
  intro x hx
  have hxs : x ∈ X.source := by
    by_contra hn
    exact hx (by simp [localPullback, hn])
  refine ⟨X x, ⟨?_, X.map_source hxs⟩, X.left_inv hxs⟩
  simpa only [Function.mem_support, localPullback, ite_eq_left hxs] using hx

lemma localPullback_tsupport {E V : Type*} [TopologicalSpace E] [T2Space E] [Zero V]
    (X : OpenPartialHomeomorph E E) (f : E → V) (hf : HasCompactSupport f)
    (hs : tsupport f ⊆ X.target) :
    HasCompactSupport (localPullback X f) ∧
      tsupport (localPullback X f) ⊆ X.symm '' tsupport f ∧
      tsupport (localPullback X f) ⊆ X.source := by
  have hK := hf.image_of_continuousOn (X.symm.continuousOn.mono hs)
  have hsub : Function.support (localPullback X f) ⊆ X.symm '' tsupport f :=
    (localPullback_support X f).trans (image_mono (fun _ hx => subset_closure hx.1))
  have ht : tsupport (localPullback X f) ⊆ X.symm '' tsupport f :=
    closure_minimal hsub hK.isClosed
  refine ⟨HasCompactSupport.of_support_subset_isCompact hK hsub, ht, ?_⟩
  rintro x hx
  obtain ⟨y, hy, rfl⟩ := ht hx
  exact X.map_target (hs hy)

lemma localPullback_contDiff {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (X : OpenPartialHomeomorph E E) (hX : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X X.source)
    (f : E → V) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ X.target) : ContDiff ℝ (↑(⊤ : ℕ∞)) (localPullback X f) := by
  apply contDiff_of_contDiffOn_tsupport X.open_source _
    (localPullback_tsupport X f hfc hfs).2.2
  intro x hx
  have hxs := hx
  have heq : localPullback X f =ᶠ[𝓝 x] f ∘ X := by
    filter_upwards [X.open_source.mem_nhds hxs] with y hy
    simp only [localPullback, ite_eq_left hy, Function.comp_apply]
  exact ((hf.contDiffAt.comp x ((hX x hxs).contDiffAt
    (X.open_source.mem_nhds hxs))).congr_of_eventuallyEq heq).contDiffWithinAt

lemma localPullback_bounds {E : Type*} [TopologicalSpace E]
    (X : OpenPartialHomeomorph E E) (f : E → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    ∀ x, 0 ≤ localPullback X f x ∧ localPullback X f x ≤ 1 := by
  intro x
  by_cases hx : x ∈ X.source
  · simpa only [localPullback, ite_eq_left hx] using hf (X x)
  · simp only [localPullback, ite_eq_right hx, le_refl, zero_le_one, and_self]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_DerivativeEquiv
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
section

lemma piolaFlux_hasCompactSupport {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : E ≃ E) (hX : Differentiable ℝ X) (hXi : Differentiable ℝ X.symm)
    (F : E → E) (hF : HasCompactSupport F) : HasCompactSupport (piolaFlux X F) := by
  apply (hF.comp_homeomorph (smoothEquivHomeomorph X hX hXi).symm).mono
  intro y hy
  contrapose! hy
  simp only [Function.mem_support, not_not] at hy ⊢
  change F (X.symm y) = 0 at hy
  simp only [piolaFlux, hy, map_zero, smul_zero]

lemma piolaFlux_zero_pairing {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (X : E ≃ E) (hX : ContDiff ℝ (↑(⊤ : ℕ∞)) X)
    (hXi : ContDiff ℝ (↑(⊤ : ℕ∞)) X.symm) (F : E → E)
    (hF : ∀ ψ : E → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
      (∫ x, fderiv ℝ ψ x (F x) ∂μ) = 0)
    (ψ : E → ℝ) (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ) :
    (∫ y, fderiv ℝ ψ y (piolaFlux X F y) ∂μ) = 0 := by
  rw [piolaFlux_pairing μ X (hX.differentiable (by simp))
    (fderiv_equiv_det_ne_zero X (hX.differentiable (by simp)) (hXi.differentiable (by simp)))
    F ψ (hψ.differentiable (by simp))]
  exact hF _ (hψ.comp hX)

lemma equiv_mapsTo_of_fixed_compl {E : Type*} (X : E ≃ E) (Q : Set E)
    (hX : ∀ x ∉ Q, X x = x) : Set.MapsTo X Q Q ∧ Set.MapsTo X.symm Q Q := by
  have hi : ∀ x ∉ Q, X.symm x = x := by
    intro x hx
    exact (X.symm_apply_eq).2 (hX x hx).symm
  constructor
  · intro x hx
    by_contra hn
    have he : X (X x) = X x := hX (X x) hn
    exact hn ((X.injective he).symm ▸ hx)
  · intro x hx
    by_contra hn
    have he : X.symm (X.symm x) = X.symm x := hi (X.symm x) hn
    exact hn ((X.symm.injective he).symm ▸ hx)

end

open Set MeasureTheory Filter Topology
open scoped BigOperators

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_SynchronizedChartWaves
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3
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

open Matrix Set Filter Topology
open scoped Matrix.Norms.Elementwise

lemma operatorMatrix_inverse_fderiv (X : Coord3 ≃ Coord3)
    (hX : Differentiable ℝ X) (hXi : Differentiable ℝ X.symm) (x : Coord3) :
    operatorMatrix (fderiv ℝ X.symm (X x)) = (operatorMatrix (fderiv ℝ X x))⁻¹ := by
  have h := fderiv_equiv_symm_comp X hX hXi x
  have hm := congrArg operatorMatrix h
  rw [operatorMatrix_comp, operatorMatrix_id] at hm
  exact Matrix.inv_eq_left_inv hm |>.symm

lemma gradientColumns_recomposition (X : Coord3 ≃ Coord3)
    (hX : Differentiable ℝ X) (hXi : Differentiable ℝ X.symm)
    (u : Coord3 → Fin 2 → ℝ) (hu : Differentiable ℝ u) (x : Coord3) :
    gradientColumns (fderiv ℝ (u ∘ X.symm) (X x)) =
      pushGradient (operatorMatrix (fderiv ℝ X x)) (gradientColumns (fderiv ℝ u x)) := by
  rw [fderiv_comp (X x) (hu _) (hXi _), X.symm_apply_apply]
  change (operatorMatrix ((fderiv ℝ u x).comp (fderiv ℝ X.symm (X x))))ᵀ = _
  rw [operatorMatrix_comp, Matrix.transpose_mul, operatorMatrix_inverse_fderiv X hX hXi]
  rfl

lemma piolaFlux_columns (X : Coord3 ≃ Coord3) (F : Coord3 → Matrix (Fin 3) (Fin 2) ℝ)
    {x : Coord3} (hdet : 0 < (fderiv ℝ X x).det) (j : Fin 2) :
    piolaFlux X (fun y => (F y).col j) (X x) =
      (pushFlux (operatorMatrix (fderiv ℝ X x)) (F x)).col j := by
  simp only [piolaFlux, X.symm_apply_apply, pushFlux, operatorMatrix_det,
    abs_of_pos hdet]
  congr 1
  exact (operatorMatrix_mulVec (fderiv ℝ X x) ((F x).col j)).symm

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_DetIdAddRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

theorem det_id_add_rankOne {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (d : E) (L : E →L[ℝ] ℝ) :
    (ContinuousLinearMap.id ℝ E + L.smulRight d).det = 1 + L d := by
  let b := Module.finBasis ℝ E
  change LinearMap.det (LinearMap.id + L.toLinearMap.smulRight d) = _
  rw [← LinearMap.det_toMatrix b, map_add, LinearMap.toMatrix_id,
    LinearMap.toMatrix_smulRight, Matrix.vecMulVec_eq Unit,
    Matrix.det_one_add_replicateCol_mul_replicateRow]
  congr 1
  conv_rhs => rw [← b.sum_repr d, map_sum]
  simp only [dotProduct, Function.comp_apply, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  change L (b i) * (b.repr d) i = (b.repr d) i * L (b i)
  ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_NormalStretch
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3
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

section
open Matrix Set
open scoped Matrix.Norms.Elementwise

lemma splitJacobian_det (d : Coord3) (L : Coord3 →L[ℝ] ℝ)
    (hLd : L d = 1) (c z : ℝ) : (splitJacobian d L c z).det = 1 + c*z := by
  rw [splitJacobian, operatorMatrix_det]
  have he : lineShiftGradientOperator d c (z • L) = ((c*z) • L).smulRight d := by
    ext v j
    simp [lineShiftGradientOperator_apply]
    ring
  rw [he, det_id_add_rankOne]
  simp [hLd]

lemma normalStretch_det (i : Fin 3) (q : ℝ) : (normalStretch i q).det = q := by
  rw [normalStretch, Matrix.det_diagonal]
  simp

lemma normalStretch_push (i : Fin 3) {q : ℝ} (hq : q ≠ 0) (B : DiagonalTriple) :
    (normalStretch i q).det⁻¹ • (normalStretch i q * Matrix.diagonal B *
      (normalStretch i q)ᵀ) = Matrix.diagonal (stretchedDiagonal i q B) := by
  rw [normalStretch_det, normalStretch, Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
  congr 1
  ext j
  by_cases hj : j = i
  · simp [stretchedDiagonal, hj]
    field_simp
  · simp [stretchedDiagonal, hj, div_eq_mul_inv]
    ring

lemma preliminary_segment (i : Fin 3) {α β : DiagonalTriple} {θ : ℝ}
    (hα : 0 < α i) (hβ : 0 < β i) (hθ : 0 < θ) (hθ' : θ < 1) (z : ℝ) :
    let A := coordinateJoin i θ α β
    let qp := preliminaryQ i A α
    let qm := preliminaryQ i A β
    let ep := θ / qp
    let em := (1-θ) / qm
    A + z • (preliminaryB i A α - preliminaryB i A β) =
      (z+ep) • preliminaryB i A α + (1-(z+ep)) • preliminaryB i A β ∧
    1+z*(qp-qm) = (z+ep)*qp + (1-(z+ep))*qm ∧ ep+em=1 := by
  let A := coordinateJoin i θ α β
  let qp := preliminaryQ i A α
  let qm := preliminaryQ i A β
  let ep := θ / qp
  let em := (1-θ) / qm
  let P := preliminaryB i A α
  let M := preliminaryB i A β
  change A + z • (P-M) = (z+ep) • P + (1-(z+ep)) • M ∧
    1+z*(qp-qm) = (z+ep)*qp + (1-(z+ep))*qm ∧ ep+em=1
  have hf := preliminary_fractions hα hβ hθ hθ'
  have he : ep+em=1 := by
    simpa [ep, em, qp, qm, A, preliminaryQ, coordinateJoin] using hf.2.2.2.2.1
  have hq : ep*qp + em*qm=1 := by
    simpa [ep, em, qp, qm, A, preliminaryQ, coordinateJoin] using hf.2.2.2.2.2
  have hmeans : ep • P + em • M = A := preliminary_matrix_mean i hα hβ hθ hθ'
  have he' : em = 1-ep := by linarith only [he]
  refine ⟨?_, ?_, he⟩
  · ext j
    have hj := congrFun hmeans j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hj ⊢
    rw [he'] at hj
    linear_combination -hj
  · rw [he'] at hq
    linear_combination -hq

theorem affine_synchronized_path (i : Fin 3) {α β : DiagonalTriple} {θ : ℝ}
    (hα : 0 < α i) (hβ : 0 < β i) (hθ : 0 < θ) (hθ' : θ < 1) :
    let A := coordinateJoin i θ α β
    let qp := preliminaryQ i A α
    let qm := preliminaryQ i A β
    let ep := θ / qp
    let em := (1-θ) / qm
    ∀ z ∈ Icc (-ep) em,
      0 < 1+z*(qp-qm) ∧ ∃ w ∈ Icc (0 : ℝ) 1,
        stretchedDiagonal i (1+z*(qp-qm))
          (A + z • (preliminaryB i A α - preliminaryB i A β)) =
          coordinateJoin i w α β := by
  dsimp only
  intro z hz
  have he := preliminary_segment i hα hβ hθ hθ' z
  have hτ₀ : 0 ≤ z + θ / preliminaryQ i (coordinateJoin i θ α β) α := by linarith [hz.1]
  have hτ₁ : z + θ / preliminaryQ i (coordinateJoin i θ α β) α ≤ 1 := by
    linarith [hz.2, he.2.2]
  have hp := synchronized_path_is_join i hα hβ hθ hθ' hτ₀ hτ₁
  rw [he.1, he.2.1]
  exact ⟨hp.1, _, ⟨hp.2.1, hp.2.2.1⟩, hp.2.2.2⟩

end

open MeasureTheory Set Filter Topology

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_MatrixOperator
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3
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
open Matrix Set
open scoped Matrix.Norms.Elementwise

lemma rotated_normalization {Q : Mat3} (hQ : Q ∈ orthogonalFrames) (i : Fin 3) :
    rotatedPhase Q i (rotatedDirection Q i) = 1 := by
  change (Qᵀ *ᵥ (Q *ᵥ Pi.single i 1)) i = 1
  rw [Matrix.mulVec_mulVec, hQ.1, Matrix.one_mulVec]
  simp

lemma rotatedDirection_apply (Q : Mat3) (i j : Fin 3) :
    rotatedDirection Q i j = Q j i := by
  simp [rotatedDirection]

lemma rotatedPhase_single (Q : Mat3) (i j : Fin 3) :
    rotatedPhase Q i (Pi.single j 1) = Q j i := by
  simp [rotatedPhase, matrixOperator, Matrix.toLin'_apply]

lemma normalStretch_decomposition (i : Fin 3) (t : ℝ) :
    normalStretch i (1+t) = 1 + t • Matrix.diagonal (Pi.single i 1) := by
  ext j k
  by_cases hj : j = i <;> by_cases hk : j = k <;>
    simp_all [normalStretch]

lemma rotated_diagonal_single (Q : Mat3) (i : Fin 3) (j k : Fin 3) :
    ((Q * Matrix.diagonal (Pi.single i 1) * Qᵀ) : Mat3) j k = Q j i * Q k i := by
  rw [Matrix.mul_apply]
  simp [Matrix.mul_diagonal, Pi.single_apply, mul_ite]

lemma splitJacobian_rotated {Q : Mat3} (hQ : Q ∈ orthogonalFrames)
    (i : Fin 3) (c z : ℝ) :
    splitJacobian (rotatedDirection Q i) (rotatedPhase Q i) c z =
      Q * normalStretch i (1+c*z) * Qᵀ := by
  rw [normalStretch_decomposition, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_one, hQ.2, Matrix.mul_smul, Matrix.smul_mul]
  ext j k
  simp only [splitJacobian, operatorMatrix, LinearMap.toMatrix'_apply,
    ContinuousLinearMap.coe_coe, _root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.id_apply, lineShiftGradientOperator_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul,
    rotatedPhase_single, Matrix.add_apply,
    Matrix.smul_apply, rotated_diagonal_single]
  simp only [Matrix.one_apply]
  by_cases hjk : j = k <;> simp [hjk, rotatedDirection_apply] <;> ring

lemma det_orthogonal_conjugate {Q : Mat3} (hQ : Q ∈ orthogonalFrames) (D : Mat3) :
    (Q * D * Qᵀ).det = D.det := by
  have he := congrArg Matrix.det hQ.2
  simp only [Matrix.det_mul, Matrix.det_one] at he
  rw [Matrix.det_mul, Matrix.det_mul]
  calc
    Q.det * D.det * Qᵀ.det = D.det * (Q.det * Qᵀ.det) := by ring
    _ = D.det := by rw [he, mul_one]

lemma conjugated_push {Q : Mat3} (hQ : Q ∈ orthogonalFrames) (D B : Mat3) :
    (Q * D * Qᵀ).det⁻¹ •
      ((Q * D * Qᵀ) * (Q * B * Qᵀ) * (Q * D * Qᵀ)ᵀ) =
      Q * (D.det⁻¹ • (D * B * Dᵀ)) * Qᵀ := by
  rw [det_orthogonal_conjugate hQ]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc
    Q * D * Qᵀ * (Q * B * Qᵀ) * (Q * (Dᵀ * Qᵀ)) =
      Q * D * (Qᵀ * Q) * B * (Qᵀ * Q) * Dᵀ * Qᵀ := by noncomm_ring
    _ = Q * (D * B * Dᵀ) * Qᵀ := by rw [hQ.1]; simp [Matrix.mul_assoc]

lemma rotated_increment_annihilates {Q : Mat3} (hQ : Q ∈ orthogonalFrames)
    (i : Fin 3) {P M : DiagonalTriple} (hn : P i = M i) :
    ∀ v, rotatedPhase Q i ((Q * Matrix.diagonal (P-M) * Qᵀ) *ᵥ v) = 0 := by
  intro v
  change (Qᵀ *ᵥ ((Q * Matrix.diagonal (P-M) * Qᵀ) *ᵥ v)) i = 0
  rw [Matrix.mulVec_mulVec]
  have he : Qᵀ * (Q * Matrix.diagonal (P-M) * Qᵀ) = Matrix.diagonal (P-M) * Qᵀ := by
    calc
      _ = (Qᵀ * Q) * Matrix.diagonal (P-M) * Qᵀ := by noncomm_ring
      _ = _ := by rw [hQ.1, Matrix.one_mul]
  rw [he, ← Matrix.mulVec_mulVec]
  simp [Matrix.mulVec_diagonal, hn]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PairedPotential
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
open Set

lemma exists_coordinate_nonzero {L : Coord3 →L[ℝ] ℝ} (hL : L ≠ 0) :
    ∃ i, L (Pi.single i 1) ≠ 0 := by
  by_contra hn
  have hz : ∀ i, L (Pi.single i 1) = 0 := by simpa only [not_exists, not_not] using hn
  apply hL
  ext x
  have hx : x = ∑ i : Fin 3, x i • Pi.single i 1 := by
    ext j
    simp [Pi.single_apply]
  rw [hx, map_sum]
  simp [hz]

lemma pairedPotential_hasFDerivAt {u : Coord3 → ℝ} {p : Coord3}
    {L : Coord3 →L[ℝ] ℝ} (hu : HasFDerivAt u L p) (j : Fin 3) :
    HasFDerivAt (pairedPotential u j) (pairedFunctional L j) p := by
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hu
  · exact (ContinuousLinearMap.proj j : Coord3 →L[ℝ] ℝ).hasFDerivAt

lemma pairedFunctional_surjective {L : Coord3 →L[ℝ] ℝ} {i j : Fin 3}
    (hi : L (Pi.single i 1) ≠ 0) (hij : i ≠ j) :
    Function.Surjective (pairedFunctional L j) := by
  intro v
  let x : Coord3 := ((v 0 - L (Pi.single j 1) * v 1) / L (Pi.single i 1)) •
    Pi.single i 1 + v 1 • Pi.single j 1
  refine ⟨x, ?_⟩
  ext k
  fin_cases k
  · change L x = v 0
    simp only [x, map_add, map_smul, smul_eq_mul]
    field_simp
    ring
  · change x j = v 1
    simp [x, Ne.symm hij]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_QuantitativeLocalTwoFieldSplit
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3
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
open Matrix Set Filter Topology
open scoped Matrix.Norms.Elementwise

lemma contDiffAt_matrix_det {X n : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Fintype n] [DecidableEq n] {k : WithTop ℕ∞} {A : X → Matrix n n ℝ} {x : X}
    (hA : ContDiffAt ℝ k A x) : ContDiffAt ℝ k (fun y => (A y).det) x := by
  simp_rw [Matrix.det_apply']
  exact ContDiffAt.sum (fun σ _ => contDiffAt_const.mul
    (contDiffAt_prod (fun i _ => contDiffAt_pi.mp (contDiffAt_pi.mp hA (σ i)) i)))

lemma contDiffAt_matrix_inv {X n : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Fintype n] [DecidableEq n] {k : WithTop ℕ∞} {A : X → Matrix n n ℝ} {x : X}
    (hA : ContDiffAt ℝ k A x) (hd : (A x).det ≠ 0) :
    ContDiffAt ℝ k (fun y => (A y)⁻¹) x := by
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv]
  apply ((contDiffAt_matrix_det hA).inv hd).smul
  apply contDiffAt_pi.mpr; intro i
  apply contDiffAt_pi.mpr; intro j
  simp_rw [Matrix.adjugate_apply]
  apply contDiffAt_matrix_det
  apply contDiffAt_pi.mpr; intro l
  apply contDiffAt_pi.mpr; intro r
  by_cases hl : l = j
  · subst l; simpa only [Matrix.updateRow_self] using
      (contDiffAt_const : ContDiffAt ℝ k (fun _ : X => (Pi.single i (1:ℝ) : n → ℝ) r) x)
  · simpa only [Matrix.updateRow_ne hl] using
      (contDiffAt_pi.mp (contDiffAt_pi.mp hA l) r)

lemma contDiffAt_repairError {X m : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Fintype m] [DecidableEq m] {k : WithTop ℕ∞}
    (A : X → Symmetric3) (E R : X → Matrix (Fin 3) m ℝ) {x : X}
    (hA : ContDiffAt ℝ k (fun y => (A y).val) x)
    (hE : ContDiffAt ℝ k E x) (hR : ContDiffAt ℝ k R x)
    (hi : LinearIndependent ℝ (E x).col) :
    ContDiffAt ℝ k (fun y => (repairError (A y) (E y) (R y)).val) x := by
  have hL := contDiffAt_matrix_mul
    (contDiffAt_matrix_inv (contDiffAt_matrix_mul (contDiffAt_matrix_transpose hE) hE)
      (gram_det_ne_zero (E x) hi)) (contDiffAt_matrix_transpose hE)
  have hD := ((contDiffAt_matrix_mul hR hL).add
    (contDiffAt_matrix_mul (contDiffAt_matrix_transpose hL) (contDiffAt_matrix_transpose hR))).sub
      (contDiffAt_matrix_mul (contDiffAt_matrix_mul
        (contDiffAt_matrix_transpose hL) (contDiffAt_matrix_mul (contDiffAt_matrix_transpose hE) hR)) hL)
  change ContDiffAt ℝ k (fun y => (A y).val +
    (1/2 : ℝ) • (symmetricCorrection (E y) (R y) (((E y)ᵀ * E y)⁻¹ * (E y)ᵀ) +
      (symmetricCorrection (E y) (R y) (((E y)ᵀ * E y)⁻¹ * (E y)ᵀ))ᵀ)) x
  apply hA.add
  apply ContDiffAt.const_smul
  exact hD.add (contDiffAt_matrix_transpose hD)

lemma contDiffAt_repairPushed {X m : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Fintype m] [DecidableEq m] {k : WithTop ℕ∞}
    (A : X → Symmetric3) (J : X → Mat3) (E F : X → Matrix (Fin 3) m ℝ) {x : X}
    (hA : ContDiffAt ℝ k (fun y => (A y).val) x) (hJ : ContDiffAt ℝ k J x)
    (hE : ContDiffAt ℝ k E x) (hF : ContDiffAt ℝ k F x)
    (hdet : (J x).det ≠ 0) (hi : LinearIndependent ℝ (E x).col) :
    ContDiffAt ℝ k (fun y => (repairPushed (A y) (J y) (E y) (F y)).val) x := by
  have hG : ContDiffAt ℝ k (fun y => pushGradient (J y) (E y)) x :=
    contDiffAt_matrix_mul (contDiffAt_matrix_transpose (contDiffAt_matrix_inv hJ hdet)) hE
  have hP : ContDiffAt ℝ k (fun y => pushFlux (J y) (F y)) x :=
    ((contDiffAt_matrix_det hJ).inv hdet).smul (contDiffAt_matrix_mul hJ hF)
  exact contDiffAt_repairError _ _ _ hA hG (hP.sub (contDiffAt_matrix_mul hA hG))
    (pushGradient_rank (J x) hdet (E x) hi)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_OpenDisjointify
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
open Set MeasureTheory Metric
open scoped ENNReal Topology

lemma openDisjointify_subset {E : Type*} [TopologicalSpace E] {n : ℕ}
    (U : Fin n → Set E) (i : Fin n) : openDisjointify U i ⊆ U i := sdiff_subset

lemma openDisjointify_isOpen {E : Type*} [TopologicalSpace E] {n : ℕ}
    (U : Fin n → Set E) (hU : ∀ i, IsOpen (U i)) (i : Fin n) :
    IsOpen (openDisjointify U i) := by
  apply (hU i).sdiff
  exact isClosed_biUnion_finset (fun _ _ => isClosed_closure)

lemma openDisjointify_pairwise {E : Type*} [TopologicalSpace E] {n : ℕ}
    (U : Fin n → Set E) : Pairwise (fun i j => Disjoint (openDisjointify U i) (openDisjointify U j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact hxj.2 (mem_iUnion₂.mpr ⟨i, Finset.mem_Iio.mpr hij, subset_closure hxi.1⟩)
  · exact hxi.2 (mem_iUnion₂.mpr ⟨j, Finset.mem_Iio.mpr hji, subset_closure hxj.1⟩)

lemma openDisjointify_cover {E : Type*} [TopologicalSpace E] {n : ℕ}
    (U : Fin n → Set E) (hU : ∀ i, IsOpen (U i)) :
    (⋃ i, U i) \ (⋃ i, openDisjointify U i) ⊆ ⋃ i, frontier (U i) := by
  classical
  intro x hx
  by_contra hn
  obtain ⟨j, hj⟩ := mem_iUnion.mp hx.1
  let s : Finset (Fin n) := Finset.univ.filter (fun i => x ∈ U i)
  have hsn : s.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  let i := s.min' hsn
  have hi : x ∈ U i := (Finset.mem_filter.mp (Finset.min'_mem s hsn)).2
  apply hx.2
  apply mem_iUnion.mpr
  refine ⟨i, hi, ?_⟩
  intro hc
  obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hc
  have hfront : x ∉ frontier (U j) := fun h => hn (mem_iUnion.mpr ⟨j, h⟩)
  have hin : x ∈ U j := by
    by_contra hnot
    apply hfront
    rw [frontier, (hU j).interior_eq]
    exact ⟨hxj, hnot⟩
  have hmin : i ≤ j := Finset.min'_le s j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hin⟩)
  exact not_lt_of_ge hmin (Finset.mem_Iio.mp hj)

lemma openDisjointify_ae_cover {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    (μ : Measure E) {n : ℕ} (U : Fin n → Set E) (hU : ∀ i, IsOpen (U i))
    (hf : ∀ i, μ (frontier (U i)) = 0) :
    μ ((⋃ i, U i) \ ⋃ i, openDisjointify U i) = 0 := by
  exact measure_mono_null (openDisjointify_cover U hU) (measure_iUnion_null hf)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_PiolaFluxContDiff
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

lemma piolaFlux_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Y : E ≃ E)
    (hY : ContDiff ℝ (↑(⊤ : ℕ∞)) Y) (hi : ContDiff ℝ (↑(⊤ : ℕ∞)) Y.symm)
    (F : E → E) (hF : ContDiff ℝ (↑(⊤ : ℕ∞)) F) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (piolaFlux Y F) := by
  rw [contDiff_iff_contDiffAt]; intro x
  have hd := (hY.contDiffAt.fderiv_right (by simp)).comp x hi.contDiffAt
  have hn := fderiv_equiv_det_ne_zero Y (hY.differentiable (by simp))
    (hi.differentiable (by simp)) (Y.symm x)
  have hdet := ((contDiff_clm_det (E := E) (↑(⊤ : ℕ∞))).contDiffAt.comp x hd).abs hn
  exact (hdet.inv (abs_ne_zero.mpr hn)).smul (hd.clm_apply (hF.contDiffAt.comp x hi.contDiffAt))

lemma equiv_symm_eq_off {E : Type*} (Y : E ≃ E) {K : Set E}
    (hY : ∀ x ∉ K, Y x = x) : ∀ x ∉ K, Y.symm x = x := by
  intro x hx
  exact Y.symm_apply_eq.mpr (hY x hx).symm

lemma fderiv_equiv_eq_id_off {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : E ≃ E) {K : Set E} (hK : IsClosed K) (hY : ∀ x ∉ K, Y x = x)
    {x : E} (hx : x ∉ K) : fderiv ℝ Y x = ContinuousLinearMap.id ℝ E := by
  have he : Y =ᶠ[𝓝 x] id := by
    filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy
    exact hY y hy
  rw [he.fderiv_eq]
  exact fderiv_id

lemma tsupport_comp_equiv_sub {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [AddGroup V] [TopologicalSpace V] (Y : E ≃ E) {K : Set E} (hK : IsClosed K)
    (hY : ∀ x ∉ K, Y x = x) (f : E → V) : tsupport (fun x => f (Y x)-f x) ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra hn
  exact hx (by change f (Y x)-f x=0; rw [hY x hn, sub_self])

lemma piolaFlux_eq_off {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Y : E ≃ E) {K : Set E} (hK : IsClosed K)
    (hY : ∀ x ∉ K, Y x = x) (F : E → E) {x : E} (hx : x ∉ K) :
    piolaFlux Y F x = F x := by
  rw [piolaFlux, equiv_symm_eq_off Y hY x hx, fderiv_equiv_eq_id_off Y hK hY hx]
  change |(LinearMap.id : E →ₗ[ℝ] E).det|⁻¹ • F x = F x
  simp

theorem compact_piola_Cauchy_difference
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (Y : E ≃ E)
    (hY : ContDiff ℝ (↑(⊤ : ℕ∞)) Y) (hi : ContDiff ℝ (↑(⊤ : ℕ∞)) Y.symm)
    {K U : Set E} (hK : IsCompact K) (hKU : K ⊆ U) (hoff : ∀ x ∉ K, Y x = x)
    (F : E → E) (hF : ContDiff ℝ (↑(⊤ : ℕ∞)) F) (hc : HasCompactSupport F)
    (hdiv : ∀ ψ : E → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x (F x) ∂μ) = 0) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => piolaFlux Y F x - F x) ∧
    HasCompactSupport (fun x => piolaFlux Y F x - F x) ∧
    tsupport (fun x => piolaFlux Y F x - F x) ⊆ K ∧
    ∀ ψ : E → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
      (∫ x, fderiv ℝ ψ x (piolaFlux Y F x - F x) ∂μ) = 0 := by
  have hG := piolaFlux_contDiff Y hY hi F hF
  have hGc := piolaFlux_hasCompactSupport Y (hY.differentiable (by simp))
    (hi.differentiable (by simp)) F hc
  have hs : tsupport (fun x => piolaFlux Y F x - F x) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hn
    exact hx (by change piolaFlux Y F x - F x = 0
                 rw [piolaFlux_eq_off Y hK.isClosed hoff F hn, sub_self])
  refine ⟨hG.sub hF, hK.of_isClosed_subset isClosed_closure hs, hs, ?_⟩
  intro ψ hψ
  have hψY := hψ.comp hY
  have htest := tsupport_comp_equiv_sub Y hK.isClosed hoff ψ
  have hz := hdiv (fun x => ψ (Y x)-ψ x) (hψY.sub hψ)
    (hK.of_isClosed_subset isClosed_closure htest) (htest.trans hKU)
  have h1 := smooth_flux_integrable_pairing μ F hF.continuous hc ψ hψ
  have h2 := smooth_flux_integrable_pairing μ F hF.continuous hc (ψ ∘ Y) hψY
  have h3 := smooth_flux_integrable_pairing μ (piolaFlux Y F) hG.continuous hGc ψ hψ
  simp only [map_sub]
  rw [integral_sub h3 h1, piolaFlux_pairing μ Y (hY.differentiable (by simp))
    (fderiv_equiv_det_ne_zero Y (hY.differentiable (by simp)) (hi.differentiable (by simp)))
      F ψ (hψ.differentiable (by simp))]
  simp_rw [show (fun x => ψ (Y x) - ψ x) = (ψ ∘ Y) - ψ from rfl] at hz
  simp_rw [fderiv_sub (hψY.differentiable (by simp) _) (hψ.differentiable (by simp) _),
    _root_.sub_apply] at hz
  rw [integral_sub h2 h1] at hz
  exact hz

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_SmoothCompactExtension
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
open scoped Manifold

lemma exists_smooth_compact_extension
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {U K : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hK : IsCompact K) (hKU : K ⊆ U) (f : E → V)
    (hf : ContDiffOn ℝ (↑(⊤ : ℕ∞)) f U) :
    ∃ (g : E → V) (W : Set E), ContDiff ℝ (↑(⊤ : ℕ∞)) g ∧
      HasCompactSupport g ∧ IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧ EqOn g f W := by
  obtain ⟨χ, hχ₀, hχ₁, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (𝓘(ℝ, E)) hU.isClosed_compl hK.isClosed
      (disjoint_left.mpr (fun x hx hxK => hx (hKU hxK))) (n := ⊤)
  have hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) (χ : E → ℝ) := contMDiff_iff_contDiff.mp χ.contMDiff
  let g : E → V := fun x => χ x • f x
  have hzero (x : E) (hx : x ∉ U) : g =ᶠ[𝓝 x] (fun _ => 0) := by
    have hh : ∀ᶠ z in 𝓝 x, χ z = 0 := hχ₀.filter_mono (nhds_le_nhdsSet hx)
    filter_upwards [hh] with z hz
    simp [g, hz]
  have hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g := by
    rw [contDiff_iff_contDiffAt]; intro x
    by_cases hx : x ∈ U
    · exact hχ.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds hx))
    · exact contDiffAt_const.congr_of_eventuallyEq (hzero x hx)
  have hs : tsupport g ⊆ U := by
    intro x hx
    by_contra hn
    exact (notMem_tsupport_iff_eventuallyEq.mpr (hzero x hn)) hx
  let W : Set E := U ∩ interior {x | χ x = 1}
  refine ⟨g, W, hg, hUb.isCompact_closure.of_isClosed_subset isClosed_closure
    (hs.trans subset_closure), hU.inter isOpen_interior, ?_, inter_subset_left, ?_⟩
  · intro x hx
    refine ⟨hKU hx, mem_interior_iff_mem_nhds.mpr ?_⟩
    exact hχ₁.filter_mono (nhds_le_nhdsSet hx)
  · intro x hx
    have hone : χ x = 1 := (interior_subset (s := {x | χ x = 1})) hx.2
    simp [g, hone]

lemma derivative_test_integral_congr
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace E]
    (μ : Measure E) (ψ : E → V) (F G : E → E) (hFG : EqOn F G (tsupport ψ)) :
    (∫ x, fderiv ℝ ψ x (F x) ∂μ) = ∫ x, fderiv ℝ ψ x (G x) ∂μ := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    by_cases hx : x ∈ tsupport ψ
    · change fderiv ℝ ψ x (F x) = fderiv ℝ ψ x (G x)
      rw [hFG hx]
    · simp only [fderiv_of_notMem_tsupport ℝ hx, _root_.zero_apply]

theorem local_compact_piola_Cauchy_difference
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (Y : E ≃ E)
    (hY : ContDiff ℝ (↑(⊤ : ℕ∞)) Y) (hi : ContDiff ℝ (↑(⊤ : ℕ∞)) Y.symm)
    {K U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hK : IsCompact K) (hKU : K ⊆ U) (hoff : ∀ x ∉ K, Y x = x)
    (F : E → E) (hF : ContDiffOn ℝ (↑(⊤ : ℕ∞)) F U)
    (hdiv : ∀ ψ : E → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x (F x) ∂μ) = 0) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => piolaFlux Y F x - F x) ∧
    HasCompactSupport (fun x => piolaFlux Y F x - F x) ∧
    tsupport (fun x => piolaFlux Y F x - F x) ⊆ K ∧
    ∀ ψ : E → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
      (∫ x, fderiv ℝ ψ x (piolaFlux Y F x - F x) ∂μ) = 0 := by
  obtain ⟨G, W, hG, hcG, _, hKW, hWU, he⟩ :=
    exists_smooth_compact_extension hU hUb hK hKU F hF
  have hdivG : ∀ ψ : E → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → (∫ x, fderiv ℝ ψ x (G x) ∂μ) = 0 := by
    intro ψ hψ hc hs
    rw [derivative_test_integral_congr μ ψ G F (he.mono hs)]
    exact hdiv ψ hψ hc (hs.trans hWU)
  have hp := compact_piola_Cauchy_difference μ Y hY hi hK hKW hoff G hG hcG hdivG
  have hsame : (fun x => piolaFlux Y F x - F x) = (fun x => piolaFlux Y G x - G x) := by
    funext x
    by_cases hx : x ∈ K
    · have hix : Y.symm x ∈ K := by
        by_contra hn
        have hz := hoff (Y.symm x) hn
        rw [Y.apply_symm_apply] at hz
        exact hn (hz ▸ hx)
      dsimp only [piolaFlux]
      rw [he (hKW hx), he (hKW hix)]
    · rw [piolaFlux_eq_off Y hK.isClosed hoff F hx,
        piolaFlux_eq_off Y hK.isClosed hoff G hx, sub_self, sub_self]
  refine ⟨hsame ▸ hp.1, hsame ▸ hp.2.1, hsame ▸ hp.2.2.1, ?_⟩
  intro ψ hψ
  have hh := hp.2.2.2 ψ hψ
  simpa only [congrFun hsame] using hh

end ScalarConductivity

namespace ScalarConductivity
open Set MeasureTheory Metric
open scoped ENNReal Topology

lemma null_frontier_union {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    (μ : Measure E) {s t : Set E} (hs : μ (frontier s) = 0) (ht : μ (frontier t) = 0) :
    μ (frontier (s ∪ t)) = 0 := by
  apply measure_mono_null ((frontier_union_subset s t).trans ?_) (measure_union_null hs ht)
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl hx.1
  · exact Or.inr hx.2

lemma null_frontier_biUnion_finset {E I : Type*} [TopologicalSpace E] [MeasurableSpace E]
    (μ : Measure E) (s : Finset I) (U : I → Set E) (hU : ∀ i ∈ s, μ (frontier (U i)) = 0) :
    μ (frontier (⋃ i ∈ s, U i)) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.set_biUnion_insert]
      exact null_frontier_union μ (hU i (Finset.mem_insert_self _ _))
        (ih fun j hj => hU j (Finset.mem_insert_of_mem hj))

lemma openDisjointify_null_frontier {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    (μ : Measure E) {n : ℕ} (U : Fin n → Set E)
    (hf : ∀ i, μ (frontier (U i)) = 0) (i : Fin n) :
    μ (frontier (openDisjointify U i)) = 0 := by
  unfold openDisjointify
  rw [sdiff_eq]
  apply null_frontier_inter (hf i)
  rw [frontier_compl]
  apply null_frontier_biUnion_finset
  intro j _
  exact measure_mono_null frontier_closure_subset (hf j)

theorem finite_disjoint_localization_null
    {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] [Measure.InnerRegularCompactLTTop μ]
    {A : Set E} (hA : MeasurableSet A) (hμA : μ A ≠ ∞)
    (U : I → Set E) (hU : ∀ i, IsOpen (U i)) (hc : A ⊆ ⋃ i, U i)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ (n : ℕ) (Q : Fin n → Set E) (tag : Fin n → I),
      (∀ i, IsOpen (Q i) ∧ IsCompact (closure (Q i)) ∧ closure (Q i) ⊆ U (tag i) ∧ μ (frontier (Q i)) = 0) ∧
      Pairwise (fun i j => Disjoint (Q i) (Q j)) ∧ μ (A \ ⋃ i, Q i) < ε := by
  classical
  obtain ⟨K, hKA, hK, hKμ⟩ := hA.exists_isCompact_sdiff_lt hμA hε
  have hb : ∀ x : K, ∃ i : I, ∃ r : ℝ, 0 < r ∧ closedBall x.val r ⊆ U i := by
    intro x
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hc (hKA x.property))
    obtain ⟨r, hr, hri⟩ := Metric.isOpen_iff.mp (hU i) x.val hi
    refine ⟨i, r/2, by positivity, ?_⟩
    intro y hy
    exact hri (show dist y x.val < r from (mem_closedBall.mp hy).trans_lt (by linarith))
  choose tag r hr hri using hb
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => Metric.ball x.val (r x))
    (fun _ => isOpen_ball) (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩, mem_ball_self (hr ⟨x,hx⟩)⟩)
  let T := {x : K // x ∈ t}
  let n := Fintype.card T
  let e : Fin n ≃ T := (Fintype.equivFin T).symm
  let B : Fin n → Set E := fun i => Metric.ball (e i).val.val (r (e i).val)
  have hKB : K ⊆ ⋃ i, B i := by
    intro x hx
    obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.mp (ht hx)
    let z : T := ⟨y, hyt⟩
    exact mem_iUnion.mpr ⟨e.symm z, by simpa only [B, Equiv.apply_symm_apply] using hxy⟩
  have hBo : ∀ i, IsOpen (B i) := fun _ => isOpen_ball
  have hBf : ∀ i, μ (frontier (B i)) = 0 := by
    intro i
    exact measure_mono_null frontier_ball_subset_sphere (Measure.addHaar_sphere μ _ _)
  refine ⟨n, openDisjointify B, fun i => tag (e i).val, ?_, openDisjointify_pairwise B, ?_⟩
  · intro i
    have hcl : closure (openDisjointify B i) ⊆ closedBall (e i).val.val (r (e i).val) :=
      (closure_mono (openDisjointify_subset B i)).trans closure_ball_subset_closedBall
    exact ⟨openDisjointify_isOpen B hBo i,
      (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hcl, hcl.trans (hri (e i).val),
      openDisjointify_null_frontier μ B hBf i⟩
  · have hsub : A \ (⋃ i, openDisjointify B i) ⊆
        (A \ K) ∪ ((⋃ i, B i) \ ⋃ i, openDisjointify B i) := by
      intro x hx
      by_cases hxK : x ∈ K
      · exact Or.inr ⟨hKB hxK, hx.2⟩
      · exact Or.inl ⟨hx.1, hxK⟩
    calc
      μ (A \ ⋃ i, openDisjointify B i) ≤
          μ (A \ K) + μ ((⋃ i, B i) \ ⋃ i, openDisjointify B i) :=
        (measure_mono hsub).trans (measure_union_le _ _)
      _ = μ (A \ K) := by rw [openDisjointify_ae_cover μ B hBo hBf, add_zero]
      _ < ε := hKμ

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_PiolaFluxAdd
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3
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

lemma piolaFlux_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : E ≃ E) (F G : E → E) :
    piolaFlux Y (fun x => F x + G x) = fun x => piolaFlux Y F x + piolaFlux Y G x := by
  funext x
  simp only [piolaFlux, map_add, smul_add]

lemma piolaFlux_tsupport_subset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : E ≃ E) {K : Set E} (hK : IsClosed K) (hoff : ∀ x ∉ K, Y x = x)
    (F : E → E) (hF : tsupport F ⊆ K) : tsupport (piolaFlux Y F) ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra hn
  have hi := equiv_symm_eq_off Y hoff x hn
  have hz : F x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hn (hF h))
  apply hx
  simp only [piolaFlux, hi, hz, map_zero, smul_zero]

theorem local_compact_recomposition_difference
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Y : E ≃ E) (hi : ContDiff ℝ (↑(⊤ : ℕ∞)) Y.symm)
    {K U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hK : IsCompact K) (hKU : K ⊆ U) (hoff : ∀ x ∉ K, Y x = x)
    (u : E → V) (hu : ContDiffOn ℝ (↑(⊤ : ℕ∞)) u U) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => u (Y.symm x)-u x) ∧
    HasCompactSupport (fun x => u (Y.symm x)-u x) ∧
    tsupport (fun x => u (Y.symm x)-u x) ⊆ K := by
  obtain ⟨v, W, hv, _, _, hKW, _, he⟩ := exists_smooth_compact_extension hU hUb hK hKU u hu
  have heq : (fun x => u (Y.symm x)-u x) = fun x => v (Y.symm x)-v x := by
    funext x
    by_cases hx : x ∈ K
    · have hix := (equiv_mapsTo_of_fixed_compl Y K hoff).2 hx
      rw [he (hKW hx), he (hKW hix)]
    · rw [equiv_symm_eq_off Y hoff x hx]
      simp
  have hs : tsupport (fun x => u (Y.symm x)-u x) ⊆ K :=
    tsupport_comp_equiv_sub Y.symm hK.isClosed (equiv_symm_eq_off Y hoff) u
  refine ⟨?_, hK.of_isClosed_subset isClosed_closure hs, hs⟩
  rw [heq]
  exact (hv.comp hi).sub hv

theorem local_compact_updated_flux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (Y : E ≃ E)
    (hY : ContDiff ℝ (↑(⊤ : ℕ∞)) Y) (hi : ContDiff ℝ (↑(⊤ : ℕ∞)) Y.symm)
    {K U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hK : IsCompact K) (hKU : K ⊆ U) (hoff : ∀ x ∉ K, Y x = x)
    (F δ : E → E) (hF : ContDiffOn ℝ (↑(⊤ : ℕ∞)) F U)
    (hdiv : ∀ ψ : E → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x (F x) ∂μ) = 0)
    (hδ : ContDiff ℝ (↑(⊤ : ℕ∞)) δ) (hsδ : tsupport δ ⊆ K)
    (hδdiv : ∀ ψ : E → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
      (∫ x, fderiv ℝ ψ x (δ x) ∂μ) = 0) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => piolaFlux Y (fun z => F z+δ z) x-F x) ∧
    HasCompactSupport (fun x => piolaFlux Y (fun z => F z+δ z) x-F x) ∧
    tsupport (fun x => piolaFlux Y (fun z => F z+δ z) x-F x) ⊆ K ∧
    ∀ ψ : E → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
      (∫ x, fderiv ℝ ψ x (piolaFlux Y (fun z => F z+δ z) x-F x) ∂μ) = 0 := by
  obtain ⟨hs, hc, hsk, hpair⟩ := local_compact_piola_Cauchy_difference μ Y hY hi
    hU hUb hK hKU hoff F hF hdiv
  have hp := piolaFlux_contDiff Y hY hi δ hδ
  have hps := piolaFlux_tsupport_subset Y hK.isClosed hoff δ hsδ
  have hpc : HasCompactSupport (piolaFlux Y δ) := hK.of_isClosed_subset isClosed_closure hps
  have heq : (fun x => piolaFlux Y (fun z => F z+δ z) x-F x) =
      fun x => (piolaFlux Y F x-F x)+piolaFlux Y δ x := by
    rw [piolaFlux_add]
    funext x; simp only [sub_eq_add_neg]; ac_rfl
  have htotal : tsupport (fun x => piolaFlux Y (fun z => F z+δ z) x-F x) ⊆ K := by
    rw [heq]
    exact (tsupport_add (fun x => piolaFlux Y F x-F x) (piolaFlux Y δ)).trans (union_subset hsk hps)
  refine ⟨?_, hK.of_isClosed_subset isClosed_closure htotal, htotal, ?_⟩
  · rw [heq]
    exact hs.add hp
  · intro ψ hψ
    simp_rw [congrFun heq, map_add]
    rw [integral_add (smooth_flux_integrable_pairing μ _ hs.continuous hc ψ hψ)
      (smooth_flux_integrable_pairing μ _ hp.continuous hpc ψ hψ), hpair ψ hψ,
      piolaFlux_zero_pairing μ Y hY hi δ hδdiv ψ hψ, zero_add]

end ScalarConductivity

namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

lemma conductivityFlux_contDiffOn (u : Coord3 → Fin 2 → ℝ)
    (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u) (A : Coord3 → Symmetric3)
    {U : Set Coord3} (hU : IsOpen U)
    (hA : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x => (A x).val) U) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (conductivityFlux u A) U := by
  intro x hx
  exact (contDiffAt_matrix_mul ((hA x hx).contDiffAt (hU.mem_nhds hx))
    (contDiff_gradientColumns u hu).contDiffAt).contDiffWithinAt

lemma tsupport_matrix_subset {X m n : Type*} [TopologicalSpace X]
    [Fintype m] [Fintype n] (F : X → Matrix m n ℝ) {K : Set X} (hK : IsClosed K)
    (hF : ∀ j, tsupport (fun x => (F x).col j) ⊆ K) : tsupport F ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra hn
  apply hx
  ext i j
  exact congrFun (image_eq_zero_of_notMem_tsupport (fun hk => hn (hF j hk))) i

theorem synchronized_compact_replacement
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    (u : Coord3 → Fin 2 → ℝ) (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (A : Coord3 → Symmetric3) {U O K : Set Coord3}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hOU : O ⊆ U)
    (hK : IsCompact K) (hKO : K ⊆ O)
    (hA : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x => (A x).val) U)
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    (Y : Coord3 ≃ Coord3) (hY : ContDiff ℝ (↑(⊤ : ℕ∞)) Y)
    (hYi : ContDiff ℝ (↑(⊤ : ℕ∞)) Y.symm) (hoff : ∀ x ∉ K, Y x = x)
    (z : Coord3 → ℝ) (hz : ContDiff ℝ (↑(⊤ : ℕ∞)) z)
    (C : ℝ → Symmetric3)
    (hC : ∀ x ∈ O, ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun t => (C t).val) (z x))
    (δ : Fin 2 → Coord3 → Coord3)
    (hδ : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (δ j))
    (hsδ : ∀ j, tsupport (δ j) ⊆ K)
    (hδdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
      (∫ x, fderiv ℝ ψ x (δ j x) ∂μ) = 0)
    (hstate : ∀ x ∈ O,
      let E := gradientColumns (fderiv ℝ u x)
      let Ft := conductivityFlux u A x + Matrix.of (fun i j => δ j x i)
      let J := operatorMatrix (fderiv ℝ Y x)
      let At := repairPushed (C (z x)) J E Ft
      0 < J.det ∧ LinearIndependent ℝ E.col ∧
        At.val * gradientColumns (fderiv ℝ (u ∘ Y.symm) (Y x)) = pushFlux J Ft) :
    ∃ R : CompactTwoFieldReplacement μ O u A, ∀ x ∈ O,
      R.tensor (Y x) = repairPushed (C (z x)) (operatorMatrix (fderiv ℝ Y x))
        (gradientColumns (fderiv ℝ u x))
        (conductivityFlux u A x + Matrix.of (fun i j => δ j x i)) := by
  classical
  let Ft : Coord3 → Matrix (Fin 3) (Fin 2) ℝ :=
    fun x => conductivityFlux u A x + Matrix.of (fun i j => δ j x i)
  let G : Coord3 → Matrix (Fin 3) (Fin 2) ℝ :=
    fun x => Matrix.of (fun i j => piolaFlux Y (fun t => (Ft t).col j) x i)
  let dF : Coord3 → Matrix (Fin 3) (Fin 2) ℝ := fun x => G x - conductivityFlux u A x
  let B : Coord3 → Symmetric3 := fun x => repairPushed (C (z x))
    (operatorMatrix (fderiv ℝ Y x)) (gradientColumns (fderiv ℝ u x)) (Ft x)
  let du : Coord3 → Fin 2 → ℝ := fun x => u (Y.symm x)-u x
  have heq : (fun x => u x+du x) = u ∘ Y.symm := by
    funext x; simp only [du, Function.comp_apply]; abel
  have him : MapsTo Y.symm O O := (equiv_mapsTo_of_fixed_compl Y O
    (fun x hx => hoff x (fun hk => hx (hKO hk)))).2
  have hF := conductivityFlux_contDiffOn u hu A hU hA
  have hcol (j : Fin 2) : ContDiffOn ℝ (↑(⊤ : ℕ∞))
      (fun x => (conductivityFlux u A x).col j) U := by
    apply contDiffOn_pi.mpr; intro i
    exact contDiffOn_pi.mp (contDiffOn_pi.mp hF i) j
  have hdcol (j : Fin 2) := local_compact_updated_flux μ Y hY hYi hU hUb hK
    (hKO.trans hOU) hoff (fun x => (conductivityFlux u A x).col j) (δ j)
    (hcol j) (hdiv j) (hδ j) (hsδ j) (hδdiv j)
  have hdFe (j : Fin 2) : (fun x => (dF x).col j) =
      fun x => piolaFlux Y (fun t => (conductivityFlux u A t).col j + δ j t) x -
        (conductivityFlux u A x).col j := by rfl
  have hdFs : ContDiff ℝ (↑(⊤ : ℕ∞)) dF := by
    apply contDiff_pi.mpr; intro i
    apply contDiff_pi.mpr; intro j
    exact contDiff_pi.mp (hdFe j ▸ (hdcol j).1) i
  have hdsupp : tsupport dF ⊆ K := tsupport_matrix_subset dF hK.isClosed
    (fun j => hdFe j ▸ (hdcol j).2.2.1)
  have hdu := local_compact_recomposition_difference Y hYi hU hUb hK
    (hKO.trans hOU) hoff u hu.contDiffOn
  have hBs : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x => (B x).val) O := by
    intro x hx
    have hd := (hstate x hx).1.ne'
    have hi := (hstate x hx).2.1
    have hFt : ContDiffAt ℝ (↑(⊤ : ℕ∞)) Ft x := by
      apply ((hF x (hOU hx)).contDiffAt (hU.mem_nhds (hOU hx))).add
      apply contDiffAt_pi.mpr; intro i
      apply contDiffAt_pi.mpr; intro j
      exact contDiffAt_pi.mp (hδ j).contDiffAt i
    exact (contDiffAt_repairPushed (fun x => C (z x)) _ _ _
      ((hC x hx).comp x hz.contDiffAt)
      ((operatorMatrix_contDiff (m := Fin 3) (n := Fin 3)).contDiffAt.comp x (hY.contDiffAt.fderiv_right (by simp)))
      (contDiff_gradientColumns u hu).contDiffAt hFt hd hi).contDiffWithinAt
  refine ⟨{
    du := du, dF := dF, tensor := B ∘ Y.symm
    smooth_du := hdu.1, compact_du := hdu.2.1, support_du := hdu.2.2.trans hKO
    smooth_dF := hdFs, compact_dF := hK.of_isClosed_subset isClosed_closure hdsupp
    support_dF := hdsupp.trans hKO
    cauchy_dF := ?_
    smooth_tensor := hBs.comp hYi.contDiffOn him
    rank := ?_
    constitutive := ?_ }, ?_⟩
  · intro j ψ hψ
    simpa only [congrFun (hdFe j)] using (hdcol j).2.2.2 ψ hψ
  · intro x hx
    rw [heq, ← Y.apply_symm_apply x, gradientColumns_recomposition Y
      (hY.differentiable (by simp)) (hYi.differentiable (by simp)) u (hu.differentiable (by simp))]
    exact pushGradient_rank _ (hstate (Y.symm x) (him hx)).1.ne' _
      (hstate (Y.symm x) (him hx)).2.1
  · intro x hx
    rw [heq]
    have hh := (hstate (Y.symm x) (him hx)).2.2
    rw [Y.apply_symm_apply] at hh
    change (B (Y.symm x)).val * gradientColumns (fderiv ℝ (u ∘ Y.symm) x) =
      conductivityFlux u A x + dF x
    rw [hh]
    have he : conductivityFlux u A x+dF x=G x := by simp only [dF]; abel
    rw [he]
    ext i j
    have hd : 0 < (fderiv ℝ Y (Y.symm x)).det := by
      rw [← operatorMatrix_det]; exact (hstate (Y.symm x) (him hx)).1
    have hp := piolaFlux_columns Y Ft hd j
    rw [Y.apply_symm_apply] at hp
    exact congrFun hp.symm i
  · intro x _
    simp only [Function.comp_apply, Y.symm_apply_apply, B, Ft]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_TsupportFiniteSumSubset
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
open scoped Matrix.Norms.Elementwise

lemma tsupport_finite_sum_subset {X V I : Type*} [TopologicalSpace X] [AddCommMonoid V]
    [Fintype I] (f : I → X → V) :
    tsupport (fun x => ∑ i, f i x) ⊆ ⋃ i, tsupport (f i) := by
  apply closure_minimal _ (isClosed_iUnion_of_finite (fun i => isClosed_tsupport (f i)))
  intro x hx
  by_contra hn
  apply hx
  apply Finset.sum_eq_zero
  intro i _
  exact image_eq_zero_of_notMem_tsupport (fun hi => hn (mem_iUnion.mpr ⟨i, hi⟩))

lemma supported_sum_eq_on {X V I : Type*} [TopologicalSpace X] [AddCommMonoid V]
    [Fintype I] [DecidableEq I] (O : I → Set X)
    (hd : Pairwise (fun i j => Disjoint (O i) (O j))) (f : I → X → V)
    (hs : ∀ i, tsupport (f i) ⊆ O i) (i : I) :
    EqOn (fun x => ∑ j, f j x) (f i) (O i) := by
  intro x hx
  apply Finset.sum_eq_single i
  · intro j _ hji
    exact image_eq_zero_of_notMem_tsupport
      (fun hj => Set.disjoint_left.mp (hd hji) (hs j hj) hx)
  · simp

lemma supported_sum_eq_zero_off {X V I : Type*} [TopologicalSpace X] [AddCommMonoid V]
    [Fintype I] (O : I → Set X) (f : I → X → V) (hs : ∀ i, tsupport (f i) ⊆ O i)
    {x : X} (hx : x ∉ ⋃ i, O i) : (∑ i, f i x) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact image_eq_zero_of_notMem_tsupport (fun hi => hx (mem_iUnion.mpr ⟨i, hs i hi⟩))

lemma finite_sum_cauchy_preserving
    (μ : Measure Coord3) [μ.IsAddHaarMeasure] {I : Type*} [Fintype I]
    (F : I → Coord3 → Matrix (Fin 3) (Fin 2) ℝ)
    (hF : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (F i))
    (hc : ∀ i, HasCompactSupport (F i))
    (hpair : ∀ i j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
      (∫ x, fderiv ℝ ψ x ((F i x).col j) ∂μ) = 0) :
    ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
      (∫ x, fderiv ℝ ψ x ((∑ i, F i x).col j) ∂μ) = 0 := by
  intro j ψ hψ
  have he (x : Coord3) : fderiv ℝ ψ x ((∑ i, F i x).col j) =
      ∑ i, fderiv ℝ ψ x ((F i x).col j) := by
    rw [← map_sum]
    congr 1
    ext k
    simp only [col, transpose_apply, Matrix.sum_apply, Finset.sum_apply]
  simp_rw [he]
  rw [integral_finsetSum]
  · simp only [hpair _ j ψ hψ, Finset.sum_const_zero]
  · intro i _
    apply smooth_flux_integrable_pairing μ _ _ _ ψ hψ
    · apply continuous_pi; intro k
      exact continuous_apply j |>.comp (continuous_apply k |>.comp (hF i).continuous)
    · apply (hc i).mono
      intro x hx hn
      apply hx
      change (F i x).col j = 0
      rw [hn]; rfl

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_MeasurableDisjointGluing
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
open scoped Matrix.Norms.Elementwise

lemma exists_measurable_disjoint_gluing
    {X Y I : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [Fintype I] (O : I → Set X) (hO : ∀ i, IsOpen (O i))
    (hd : Pairwise (fun i j => Disjoint (O i) (O j)))
    (A : X → Y) (hA : Measurable A) (B : I → X → Y)
    (hB : ∀ i, ContinuousOn (B i) (O i)) (y₀ : Y) :
    ∃ T : X → Y, Measurable T ∧ (∀ i, EqOn T (B i) (O i)) ∧
      EqOn T A (⋃ i, O i)ᶜ := by
  classical
  let P : Option I → Set X := fun i => match i with
    | none => (⋃ i, O i)ᶜ
    | some j => O j
  let G : Option I → X → Y := fun i => match i with
    | none => A
    | some j => (O j).piecewise (B j) (fun _ => y₀)
  have hP : ∀ i, MeasurableSet (P i) := by
    rintro (_ | i)
    · exact (MeasurableSet.iUnion (fun i => (hO i).measurableSet)).compl
    · exact (hO i).measurableSet
  have hG : ∀ i, Measurable (G i) := by
    rintro (_ | i)
    · exact hA
    · exact (hB i).measurable_piecewise continuousOn_const (hO i).measurableSet
  obtain ⟨T, hT, hTP⟩ := exists_measurable_piecewise P hP G hG (by
    rintro (_ | i) (_ | j) hij x ⟨hxi, hxj⟩
    · exact (hij rfl).elim
    · exact (hxi (mem_iUnion.mpr ⟨j, hxj⟩)).elim
    · exact (hxj (mem_iUnion.mpr ⟨i, hxi⟩)).elim
    · exact (Set.disjoint_left.mp (hd (fun e => hij (congrArg some e))) hxi hxj).elim)
  refine ⟨T, hT, ?_, hTP none⟩
  intro i x hx
  simpa only [G, Set.piecewise_eq_of_mem (O i) (B i) (fun _ => y₀) hx] using hTP (some i) hx

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_CompactSplitSubpatch
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3
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
open scoped Matrix.Norms.Elementwise

theorem exists_compact_split_on_subpatch
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    (u : Coord3 → Fin 2 → ℝ) (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (A : Coord3 → Symmetric3) {p : Coord3} (hAp : ContinuousAt A p)
    {U : Set Coord3} (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hpU : p ∈ U)
    (hA : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x => (A x).val) U)
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    (hD : Function.Surjective (fderiv ℝ u p))
    (d : Coord3) (L : Coord3 →L[ℝ] ℝ) (hLd : L d = 1)
    (B : Mat3) (hB : B.IsSymm) (hBn : ∀ v, L (B *ᵥ v) = 0)
    {θ c m : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hm : 0 < m) (hpath : ∀ z ∈ Icc (-θ) (1-θ), m ≤ 1+c*z)
    (C : ℝ → Symmetric3) (hC : ∀ z ∈ Icc (-θ) (1-θ), ContinuousAt C z)
    (hCs : ∀ z ∈ Icc (-θ) (1-θ), ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun t => (C t).val) z)
    (hdet : ∀ z ∈ Icc (-θ) (1-θ), 0 < (splitJacobian d L c z).det)
    (hconstit : ∀ z ∈ Icc (-θ) (1-θ),
      (C z).val = (splitJacobian d L c z).det⁻¹ •
        (splitJacobian d L c z * ((A p).val + z • B) * (splitJacobian d L c z)ᵀ))
    {G : Set (ℝ × Symmetric3)} (hG : IsOpen G)
    (hCG : ∀ z ∈ Icc (-θ) (1-θ), (z, C z) ∈ G) :
    ∃ W : Set Coord3, IsOpen W ∧ p ∈ W ∧ closure W ⊆ U ∧ IsCompact (closure W) ∧
      ∀ O : Set Coord3, IsOpen O → O ⊆ W → ∀ ε : ℝ, 0 < ε →
      ∃ (R : CompactTwoFieldReplacement μ O u A) (q : Coord3 → ℝ),
        ContDiff ℝ (↑(⊤ : ℕ∞)) q ∧
        (∀ x, q x ∈ Icc (-θ) (1-θ)) ∧
        (∀ x ∈ O, (q x, R.tensor x) ∈ G) ∧
        μ {x | x ∈ O ∧ q x ≠ -θ ∧ q x ≠ 1-θ} ≤ ENNReal.ofReal ε := by
  obtain ⟨X, W, hW, hpW, hWU, hWc, hWX, hX, hXi, hop⟩ :=
    exists_local_split_on_subpatch_retained μ u hu A hAp hD d L hLd B hB hBn
      hθ hθ1 hm hpath C hC hdet hconstit hG hCG hU hpU
  refine ⟨W, hW, hpW, hWU, hWc, ?_⟩
  intro O hO hOW ε hε
  have hOU : O ⊆ U := hOW.trans (subset_closure.trans hWU)
  have hOX : O ⊆ X.source := hOW.trans hWX
  obtain ⟨χ, H, F, hχc, hχO, hχb, hHr, hF, hFs, hFdiv, hn⟩ := hop O hO hOW ε hε
  obtain ⟨n, hn⟩ := hn.exists
  obtain ⟨Y, hY, hYi, hoffO, _, hform, hpure, hstate⟩ := hn
  have hχt : tsupport χ.val ⊆ X.target := hχO.trans (by
    rintro y ⟨x, hx, rfl⟩; exact X.map_source (hOX hx))
  let K := X.symm '' tsupport χ.val
  have hK : IsCompact K := hχc.image_of_continuousOn (X.symm.continuousOn.mono hχt)
  have hKO : K ⊆ O := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨t, ht, rfl⟩ := hχO hy
    simpa only [X.left_inv (hOX ht)] using ht
  have hχp := localPullback_tsupport X χ.val hχc hχt
  have hoff : ∀ x ∉ K, Y x = x := by
    intro x hx
    have hz := image_eq_zero_of_notMem_tsupport (fun h => hx (hχp.2.1 h))
    rw [hform x, hz, mul_zero, zero_mul, zero_smul, add_zero]
  let z : Coord3 → ℝ := fun x => localPullback X χ.val x *
    (smoothDirection 1 H).val ((n+1 : ℝ) * L (X x))
  have hz : ContDiff ℝ (↑(⊤ : ℕ∞)) z :=
    (localPullback_contDiff X hX.contDiffOn χ.val (smoothScalar_contDiff χ) hχc hχt).mul
      ((smoothScalar_contDiff (smoothDirection 1 H)).comp
        (contDiff_const.mul (L.contDiff.comp hX)))
  have hzr : ∀ x, z x ∈ Icc (-θ) (1-θ) := fun x =>
    scalar_cutoff_segment hθ.le (by linarith) (localPullback_bounds X χ.val hχb x) (hHr _)
  obtain ⟨R, hRt⟩ := synchronized_compact_replacement μ u hu A hU hUb hOU hK hKO hA hdiv
    Y hY hYi hoff z hz C (fun x _ => hCs _ (hzr x)) (F (n+1 : ℝ))
    (hF _) (fun j => (hFs _ j).2.2) (hFdiv _) (fun x hx =>
      ⟨(hstate x hx).1, (hstate x hx).2.1, (hstate x hx).2.2.2⟩)
  let q : Coord3 → ℝ := z ∘ Y.symm
  have him : MapsTo Y.symm O O := (equiv_mapsTo_of_fixed_compl Y O hoffO).2
  refine ⟨R, q, hz.comp hYi, fun x => hzr _, ?_, hpure⟩
  intro x hx
  have ht := hRt (Y.symm x) (him hx)
  rw [Y.apply_symm_apply] at ht
  rw [ht]
  exact (hstate (Y.symm x) (him hx)).2.2.1

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_ChangeOld
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3
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
open scoped Matrix.Norms.Elementwise

theorem exists_locally_smooth_compact_split
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3) {p : Coord3}
    {U : Set Coord3} (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hpU : p ∈ U)
    (hu : ContDiffOn ℝ (↑(⊤ : ℕ∞)) u U)
    (hA : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x => (A x).val) U)
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    (hD : Function.Surjective (fderiv ℝ u p))
    (d : Coord3) (L : Coord3 →L[ℝ] ℝ) (hLd : L d = 1)
    (B : Mat3) (hB : B.IsSymm) (hBn : ∀ v, L (B *ᵥ v) = 0)
    {θ c m : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hm : 0 < m) (hpath : ∀ z ∈ Icc (-θ) (1-θ), m ≤ 1+c*z)
    (C : ℝ → Symmetric3) (hC : ∀ z ∈ Icc (-θ) (1-θ), ContinuousAt C z)
    (hCs : ∀ z ∈ Icc (-θ) (1-θ), ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun t => (C t).val) z)
    (hdet : ∀ z ∈ Icc (-θ) (1-θ), 0 < (splitJacobian d L c z).det)
    (hconstit : ∀ z ∈ Icc (-θ) (1-θ),
      (C z).val = (splitJacobian d L c z).det⁻¹ •
        (splitJacobian d L c z * ((A p).val + z • B) * (splitJacobian d L c z)ᵀ))
    {G : Set (ℝ × Symmetric3)} (hG : IsOpen G)
    (hCG : ∀ z ∈ Icc (-θ) (1-θ), (z, C z) ∈ G) :
    ∃ W : Set Coord3, IsOpen W ∧ p ∈ W ∧ closure W ⊆ U ∧ IsCompact (closure W) ∧
      ∀ O : Set Coord3, IsOpen O → O ⊆ W → ∀ ε : ℝ, 0 < ε →
      ∃ (R : CompactTwoFieldReplacement μ O u A) (q : Coord3 → ℝ),
        ContDiff ℝ (↑(⊤ : ℕ∞)) q ∧ (∀ x, q x ∈ Icc (-θ) (1-θ)) ∧
        (∀ x ∈ O, (q x, R.tensor x) ∈ G) ∧
        μ {x | x ∈ O ∧ q x ≠ -θ ∧ q x ≠ 1-θ} ≤ ENNReal.ofReal ε := by
  obtain ⟨v, V, hv, _, hV, hpV, hVU, he⟩ := exists_smooth_compact_extension
    hU hUb isCompact_singleton (singleton_subset_iff.mpr hpU) u hu
  have hep : fderiv ℝ v p = fderiv ℝ u p := fderiv_eq_of_eqOn_open hV he (hpV (mem_singleton p))
  have hAp : ContinuousAt A p :=
    Topology.IsInducing.subtypeVal.continuousAt_iff.mpr
      (hA.continuousOn.continuousAt (hU.mem_nhds hpU))
  have hdivv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ V → (∫ x, fderiv ℝ ψ x ((conductivityFlux v A x).col j) ∂μ) = 0 := by
    intro j ψ hψ hc hs
    rw [derivative_test_integral_congr μ ψ _ (fun x => (conductivityFlux u A x).col j) (by
      intro x hx
      simp only [conductivityFlux, fderiv_eq_of_eqOn_open hV he (hs hx)])]
    exact hdiv j ψ hψ hc (hs.trans hVU)
  obtain ⟨W, hW, hpW, hWV, hWc, hw⟩ := exists_compact_split_on_subpatch μ v hv A hAp
    hV (hUb.subset hVU) (hpV (mem_singleton p)) (hA.mono hVU) hdivv (hep ▸ hD)
    d L hLd B hB hBn hθ hθ1 hm hpath C hC hCs hdet hconstit hG hCG
  refine ⟨W, hW, hpW, hWV.trans hVU, hWc, ?_⟩
  intro O hO hOW ε hε
  obtain ⟨R, q, hq, hqr, hqG, hqm⟩ := hw O hO hOW ε hε
  exact ⟨R.changeOld hO (he.mono (hOW.trans (subset_closure.trans hWV))) (fun _ _ => rfl),
    q, hq, hqr, hqG, hqm⟩

end ScalarConductivity

namespace ScalarConductivity
open Set MeasureTheory Filter Topology

theorem local_compact_piola_difference_regular
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Y : E ≃ E) (hY : ContDiff ℝ (↑(⊤ : ℕ∞)) Y)
    (hi : ContDiff ℝ (↑(⊤ : ℕ∞)) Y.symm)
    {K U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hK : IsCompact K) (hKU : K ⊆ U) (hoff : ∀ x ∉ K, Y x = x)
    (F : E → E) (hF : ContDiffOn ℝ (↑(⊤ : ℕ∞)) F U) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => piolaFlux Y F x-F x) ∧
    HasCompactSupport (fun x => piolaFlux Y F x-F x) ∧
    tsupport (fun x => piolaFlux Y F x-F x) ⊆ K := by
  obtain ⟨G, W, hG, _, _, hKW, _, he⟩ := exists_smooth_compact_extension hU hUb hK hKU F hF
  have hsame : (fun x => piolaFlux Y F x-F x) = fun x => piolaFlux Y G x-G x := by
    funext x
    by_cases hx : x ∈ K
    · have hix := (equiv_mapsTo_of_fixed_compl Y K hoff).2 hx
      dsimp only [piolaFlux]
      rw [he (hKW hx), he (hKW hix)]
    · rw [piolaFlux_eq_off Y hK.isClosed hoff F hx,
        piolaFlux_eq_off Y hK.isClosed hoff G hx, sub_self, sub_self]
  have hs : tsupport (fun x => piolaFlux Y F x-F x) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hn
    exact hx (by dsimp only; rw [piolaFlux_eq_off Y hK.isClosed hoff F hn, sub_self])
  refine ⟨?_, hK.of_isClosed_subset isClosed_closure hs, hs⟩
  rw [hsame]
  exact (piolaFlux_contDiff Y hY hi G hG).sub hG

theorem local_compact_updated_flux_regular
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Y : E ≃ E) (hY : ContDiff ℝ (↑(⊤ : ℕ∞)) Y)
    (hi : ContDiff ℝ (↑(⊤ : ℕ∞)) Y.symm)
    {K U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hK : IsCompact K) (hKU : K ⊆ U) (hoff : ∀ x ∉ K, Y x = x)
    (F δ : E → E) (hF : ContDiffOn ℝ (↑(⊤ : ℕ∞)) F U)
    (hδ : ContDiff ℝ (↑(⊤ : ℕ∞)) δ) (hsδ : tsupport δ ⊆ K) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => piolaFlux Y (fun z => F z+δ z) x-F x) ∧
    HasCompactSupport (fun x => piolaFlux Y (fun z => F z+δ z) x-F x) ∧
    tsupport (fun x => piolaFlux Y (fun z => F z+δ z) x-F x) ⊆ K := by
  obtain ⟨hs, _, hsk⟩ := local_compact_piola_difference_regular Y hY hi hU hUb hK hKU hoff F hF
  have hp := piolaFlux_contDiff Y hY hi δ hδ
  have hps := piolaFlux_tsupport_subset Y hK.isClosed hoff δ hsδ
  have heq : (fun x => piolaFlux Y (fun z => F z+δ z) x-F x) =
      fun x => (piolaFlux Y F x-F x)+piolaFlux Y δ x := by
    rw [piolaFlux_add]
    funext x; simp only [sub_eq_add_neg]; ac_rfl
  have htotal : tsupport (fun x => piolaFlux Y (fun z => F z+δ z) x-F x) ⊆ K := by
    rw [heq]
    exact (tsupport_add _ _).trans (union_subset hsk hps)
  refine ⟨?_, hK.of_isClosed_subset isClosed_closure htotal, htotal⟩
  rw [heq]
  exact hs.add hp

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CompactSelectedReplacement
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3
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
open scoped Matrix.Norms.Elementwise

theorem synchronized_selected_replacement
    (J : Set (Fin 2))
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    (u : Coord3 → Fin 2 → ℝ) (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (A : Coord3 → Symmetric3) {U O K : Set Coord3}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hOU : O ⊆ U)
    (hK : IsCompact K) (hKO : K ⊆ O)
    (hA : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x => (A x).val) U)
    (hdiv : ∀ j ∈ J, ∀ (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    (Y : Coord3 ≃ Coord3) (hY : ContDiff ℝ (↑(⊤ : ℕ∞)) Y)
    (hYi : ContDiff ℝ (↑(⊤ : ℕ∞)) Y.symm) (hoff : ∀ x ∉ K, Y x = x)
    (z : Coord3 → ℝ) (hz : ContDiff ℝ (↑(⊤ : ℕ∞)) z)
    (C : ℝ → Symmetric3)
    (hC : ∀ x ∈ O, ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun t => (C t).val) (z x))
    (δ : Fin 2 → Coord3 → Coord3)
    (hδ : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (δ j))
    (hsδ : ∀ j, tsupport (δ j) ⊆ K)
    (hδdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
      (∫ x, fderiv ℝ ψ x (δ j x) ∂μ) = 0)
    (hstate : ∀ x ∈ O,
      let E := gradientColumns (fderiv ℝ u x)
      let Ft := conductivityFlux u A x + Matrix.of (fun i j => δ j x i)
      let J := operatorMatrix (fderiv ℝ Y x)
      let At := repairPushed (C (z x)) J E Ft
      0 < J.det ∧ LinearIndependent ℝ E.col ∧
        At.val * gradientColumns (fderiv ℝ (u ∘ Y.symm) (Y x)) = pushFlux J Ft) :
    ∃ R : CompactSelectedReplacement J μ O u A, ∀ x ∈ O,
      R.tensor (Y x) = repairPushed (C (z x)) (operatorMatrix (fderiv ℝ Y x))
        (gradientColumns (fderiv ℝ u x))
        (conductivityFlux u A x + Matrix.of (fun i j => δ j x i)) := by
  classical
  let Ft : Coord3 → Matrix (Fin 3) (Fin 2) ℝ :=
    fun x => conductivityFlux u A x + Matrix.of (fun i j => δ j x i)
  let G : Coord3 → Matrix (Fin 3) (Fin 2) ℝ :=
    fun x => Matrix.of (fun i j => piolaFlux Y (fun t => (Ft t).col j) x i)
  let dF : Coord3 → Matrix (Fin 3) (Fin 2) ℝ := fun x => G x - conductivityFlux u A x
  let B : Coord3 → Symmetric3 := fun x => repairPushed (C (z x))
    (operatorMatrix (fderiv ℝ Y x)) (gradientColumns (fderiv ℝ u x)) (Ft x)
  let du : Coord3 → Fin 2 → ℝ := fun x => u (Y.symm x)-u x
  have heq : (fun x => u x+du x) = u ∘ Y.symm := by
    funext x; simp only [du, Function.comp_apply]; abel
  have him : MapsTo Y.symm O O := (equiv_mapsTo_of_fixed_compl Y O
    (fun x hx => hoff x (fun hk => hx (hKO hk)))).2
  have hF := conductivityFlux_contDiffOn u hu A hU hA
  have hcol (j : Fin 2) : ContDiffOn ℝ (↑(⊤ : ℕ∞))
      (fun x => (conductivityFlux u A x).col j) U := by
    apply contDiffOn_pi.mpr; intro i
    exact contDiffOn_pi.mp (contDiffOn_pi.mp hF i) j
  have hdcol (j : Fin 2) := local_compact_updated_flux_regular Y hY hYi hU hUb hK
    (hKO.trans hOU) hoff (fun x => (conductivityFlux u A x).col j) (δ j)
    (hcol j) (hδ j) (hsδ j)
  have hdFe (j : Fin 2) : (fun x => (dF x).col j) =
      fun x => piolaFlux Y (fun t => (conductivityFlux u A t).col j + δ j t) x -
        (conductivityFlux u A x).col j := by rfl
  have hdFs : ContDiff ℝ (↑(⊤ : ℕ∞)) dF := by
    apply contDiff_pi.mpr; intro i
    apply contDiff_pi.mpr; intro j
    exact contDiff_pi.mp (hdFe j ▸ (hdcol j).1) i
  have hdsupp : tsupport dF ⊆ K := tsupport_matrix_subset dF hK.isClosed
    (fun j => hdFe j ▸ (hdcol j).2.2)
  have hdu := local_compact_recomposition_difference Y hYi hU hUb hK
    (hKO.trans hOU) hoff u hu.contDiffOn
  have hBs : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x => (B x).val) O := by
    intro x hx
    have hd := (hstate x hx).1.ne'
    have hi := (hstate x hx).2.1
    have hFt : ContDiffAt ℝ (↑(⊤ : ℕ∞)) Ft x := by
      apply ((hF x (hOU hx)).contDiffAt (hU.mem_nhds (hOU hx))).add
      apply contDiffAt_pi.mpr; intro i
      apply contDiffAt_pi.mpr; intro j
      exact contDiffAt_pi.mp (hδ j).contDiffAt i
    exact (contDiffAt_repairPushed (fun x => C (z x)) _ _ _
      ((hC x hx).comp x hz.contDiffAt)
      ((operatorMatrix_contDiff (m := Fin 3) (n := Fin 3)).contDiffAt.comp x (hY.contDiffAt.fderiv_right (by simp)))
      (contDiff_gradientColumns u hu).contDiffAt hFt hd hi).contDiffWithinAt
  refine ⟨{
    du := du, dF := dF, tensor := B ∘ Y.symm
    smooth_du := hdu.1, compact_du := hdu.2.1, support_du := hdu.2.2.trans hKO
    smooth_dF := hdFs, compact_dF := hK.of_isClosed_subset isClosed_closure hdsupp
    support_dF := hdsupp.trans hKO
    cauchy_dF := ?_
    smooth_tensor := hBs.comp hYi.contDiffOn him
    rank := ?_
    constitutive := ?_ }, ?_⟩
  · intro j hj ψ hψ
    have hh := local_compact_updated_flux μ Y hY hYi hU hUb hK (hKO.trans hOU) hoff
      (fun x => (conductivityFlux u A x).col j) (δ j) (hcol j) (hdiv j hj)
      (hδ j) (hsδ j) (hδdiv j)
    simpa only [congrFun (hdFe j)] using hh.2.2.2 ψ hψ
  · intro x hx
    rw [heq, ← Y.apply_symm_apply x, gradientColumns_recomposition Y
      (hY.differentiable (by simp)) (hYi.differentiable (by simp)) u (hu.differentiable (by simp))]
    exact pushGradient_rank _ (hstate (Y.symm x) (him hx)).1.ne' _
      (hstate (Y.symm x) (him hx)).2.1
  · intro x hx
    rw [heq]
    have hh := (hstate (Y.symm x) (him hx)).2.2
    rw [Y.apply_symm_apply] at hh
    change (B (Y.symm x)).val * gradientColumns (fderiv ℝ (u ∘ Y.symm) x) =
      conductivityFlux u A x + dF x
    rw [hh]
    have he : conductivityFlux u A x+dF x=G x := by simp only [dF]; abel
    rw [he]
    ext i j
    have hd : 0 < (fderiv ℝ Y (Y.symm x)).det := by
      rw [← operatorMatrix_det]; exact (hstate (Y.symm x) (him hx)).1
    have hp := piolaFlux_columns Y Ft hd j
    rw [Y.apply_symm_apply] at hp
    exact congrFun hp.symm i
  · intro x _
    simp only [Function.comp_apply, Y.symm_apply_apply, B, Ft]

theorem exists_selected_split_on_subpatch
    (J : Set (Fin 2))
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    (u : Coord3 → Fin 2 → ℝ) (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (A : Coord3 → Symmetric3) {p : Coord3} (hAp : ContinuousAt A p)
    {U : Set Coord3} (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hpU : p ∈ U)
    (hA : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x => (A x).val) U)
    (hdiv : ∀ j ∈ J, ∀ (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    (hD : Function.Surjective (fderiv ℝ u p))
    (d : Coord3) (L : Coord3 →L[ℝ] ℝ) (hLd : L d = 1)
    (B : Mat3) (hB : B.IsSymm) (hBn : ∀ v, L (B *ᵥ v) = 0)
    {θ c m : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hm : 0 < m) (hpath : ∀ z ∈ Icc (-θ) (1-θ), m ≤ 1+c*z)
    (C : ℝ → Symmetric3) (hC : ∀ z ∈ Icc (-θ) (1-θ), ContinuousAt C z)
    (hCs : ∀ z ∈ Icc (-θ) (1-θ), ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun t => (C t).val) z)
    (hdet : ∀ z ∈ Icc (-θ) (1-θ), 0 < (splitJacobian d L c z).det)
    (hconstit : ∀ z ∈ Icc (-θ) (1-θ),
      (C z).val = (splitJacobian d L c z).det⁻¹ •
        (splitJacobian d L c z * ((A p).val + z • B) * (splitJacobian d L c z)ᵀ))
    {G : Set (ℝ × Symmetric3)} (hG : IsOpen G)
    (hCG : ∀ z ∈ Icc (-θ) (1-θ), (z, C z) ∈ G) :
    ∃ W : Set Coord3, IsOpen W ∧ p ∈ W ∧ closure W ⊆ U ∧ IsCompact (closure W) ∧
      ∀ O : Set Coord3, IsOpen O → O ⊆ W → ∀ ε : ℝ, 0 < ε →
      ∃ (R : CompactSelectedReplacement J μ O u A) (q : Coord3 → ℝ),
        ContDiff ℝ (↑(⊤ : ℕ∞)) q ∧
        (∀ x, q x ∈ Icc (-θ) (1-θ)) ∧
        (∀ x ∈ O, (q x, R.tensor x) ∈ G) ∧
        μ {x | x ∈ O ∧ q x ≠ -θ ∧ q x ≠ 1-θ} ≤ ENNReal.ofReal ε := by
  obtain ⟨X, W, hW, hpW, hWU, hWc, hWX, hX, hXi, hop⟩ :=
    exists_local_split_on_subpatch_retained μ u hu A hAp hD d L hLd B hB hBn
      hθ hθ1 hm hpath C hC hdet hconstit hG hCG hU hpU
  refine ⟨W, hW, hpW, hWU, hWc, ?_⟩
  intro O hO hOW ε hε
  have hOU : O ⊆ U := hOW.trans (subset_closure.trans hWU)
  have hOX : O ⊆ X.source := hOW.trans hWX
  obtain ⟨χ, H, F, hχc, hχO, hχb, hHr, hF, hFs, hFdiv, hn⟩ := hop O hO hOW ε hε
  obtain ⟨n, hn⟩ := hn.exists
  obtain ⟨Y, hY, hYi, hoffO, _, hform, hpure, hstate⟩ := hn
  have hχt : tsupport χ.val ⊆ X.target := hχO.trans (by
    rintro y ⟨x, hx, rfl⟩; exact X.map_source (hOX hx))
  let K := X.symm '' tsupport χ.val
  have hK : IsCompact K := hχc.image_of_continuousOn (X.symm.continuousOn.mono hχt)
  have hKO : K ⊆ O := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨t, ht, rfl⟩ := hχO hy
    simpa only [X.left_inv (hOX ht)] using ht
  have hχp := localPullback_tsupport X χ.val hχc hχt
  have hoff : ∀ x ∉ K, Y x = x := by
    intro x hx
    have hz := image_eq_zero_of_notMem_tsupport (fun h => hx (hχp.2.1 h))
    rw [hform x, hz, mul_zero, zero_mul, zero_smul, add_zero]
  let z : Coord3 → ℝ := fun x => localPullback X χ.val x *
    (smoothDirection 1 H).val ((n+1 : ℝ) * L (X x))
  have hz : ContDiff ℝ (↑(⊤ : ℕ∞)) z :=
    (localPullback_contDiff X hX.contDiffOn χ.val (smoothScalar_contDiff χ) hχc hχt).mul
      ((smoothScalar_contDiff (smoothDirection 1 H)).comp
        (contDiff_const.mul (L.contDiff.comp hX)))
  have hzr : ∀ x, z x ∈ Icc (-θ) (1-θ) := fun x =>
    scalar_cutoff_segment hθ.le (by linarith) (localPullback_bounds X χ.val hχb x) (hHr _)
  obtain ⟨R, hRt⟩ := synchronized_selected_replacement J μ u hu A hU hUb hOU hK hKO hA hdiv
    Y hY hYi hoff z hz C (fun x _ => hCs _ (hzr x)) (F (n+1 : ℝ))
    (hF _) (fun j => (hFs _ j).2.2) (hFdiv _) (fun x hx =>
      ⟨(hstate x hx).1, (hstate x hx).2.1, (hstate x hx).2.2.2⟩)
  let q : Coord3 → ℝ := z ∘ Y.symm
  have him : MapsTo Y.symm O O := (equiv_mapsTo_of_fixed_compl Y O hoffO).2
  refine ⟨R, q, hz.comp hYi, fun x => hzr _, ?_, hpure⟩
  intro x hx
  have ht := hRt (Y.symm x) (him hx)
  rw [Y.apply_symm_apply] at ht
  rw [ht]
  exact (hstate (Y.symm x) (him hx)).2.2.1

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CompactCompatibleReplacement
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3
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
open scoped Matrix.Norms.Elementwise

lemma CompactSelectedReplacement.affineTransfer_relation
    {μ : Measure Coord3} {O : Set Coord3} (hO : IsOpen O)
    {u v : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    {l κ : Fin 2 → ℝ}
    (he : ∀ x ∈ O, ∀ j, u x j = l j * v x 0 + κ j)
    (hv : ContDiffOn ℝ (↑(⊤ : ℕ∞)) v O)
    (R : CompactSelectedReplacement {0} μ O v A) :
    ∀ x ∈ O, ∀ j, (u x + (R.affineTransfer hO he hv).du x) j =
      l j * (v x + R.du x) 0 + κ j := by
  intro x hx j
  change u x j + l j * R.du x 0 = _
  rw [he x hx j]
  simp only [Pi.add_apply]
  ring

end ScalarConductivity

namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

theorem exists_locally_smooth_selected_split
    (J : Set (Fin 2))
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3) {p : Coord3}
    {U : Set Coord3} (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hpU : p ∈ U)
    (hu : ContDiffOn ℝ (↑(⊤ : ℕ∞)) u U)
    (hA : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x => (A x).val) U)
    (hdiv : ∀ j ∈ J, ∀ (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    (hD : Function.Surjective (fderiv ℝ u p))
    (d : Coord3) (L : Coord3 →L[ℝ] ℝ) (hLd : L d = 1)
    (B : Mat3) (hB : B.IsSymm) (hBn : ∀ v, L (B *ᵥ v) = 0)
    {θ c m : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hm : 0 < m) (hpath : ∀ z ∈ Icc (-θ) (1-θ), m ≤ 1+c*z)
    (C : ℝ → Symmetric3) (hC : ∀ z ∈ Icc (-θ) (1-θ), ContinuousAt C z)
    (hCs : ∀ z ∈ Icc (-θ) (1-θ), ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun t => (C t).val) z)
    (hdet : ∀ z ∈ Icc (-θ) (1-θ), 0 < (splitJacobian d L c z).det)
    (hconstit : ∀ z ∈ Icc (-θ) (1-θ),
      (C z).val = (splitJacobian d L c z).det⁻¹ •
        (splitJacobian d L c z * ((A p).val + z • B) * (splitJacobian d L c z)ᵀ))
    {G : Set (ℝ × Symmetric3)} (hG : IsOpen G)
    (hCG : ∀ z ∈ Icc (-θ) (1-θ), (z, C z) ∈ G) :
    ∃ W : Set Coord3, IsOpen W ∧ p ∈ W ∧ closure W ⊆ U ∧ IsCompact (closure W) ∧
      ∀ O : Set Coord3, IsOpen O → O ⊆ W → ∀ ε : ℝ, 0 < ε →
      ∃ (R : CompactSelectedReplacement J μ O u A) (q : Coord3 → ℝ),
        ContDiff ℝ (↑(⊤ : ℕ∞)) q ∧ (∀ x, q x ∈ Icc (-θ) (1-θ)) ∧
        (∀ x ∈ O, (q x, R.tensor x) ∈ G) ∧
        μ {x | x ∈ O ∧ q x ≠ -θ ∧ q x ≠ 1-θ} ≤ ENNReal.ofReal ε := by
  obtain ⟨v, V, hv, _, hV, hpV, hVU, he⟩ := exists_smooth_compact_extension
    hU hUb isCompact_singleton (singleton_subset_iff.mpr hpU) u hu
  have hep : fderiv ℝ v p = fderiv ℝ u p := fderiv_eq_of_eqOn_open hV he (hpV (mem_singleton p))
  have hAp : ContinuousAt A p :=
    Topology.IsInducing.subtypeVal.continuousAt_iff.mpr
      (hA.continuousOn.continuousAt (hU.mem_nhds hpU))
  have hdivv : ∀ j ∈ J, ∀ (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ V → (∫ x, fderiv ℝ ψ x ((conductivityFlux v A x).col j) ∂μ) = 0 := by
    intro j hj ψ hψ hc hs
    rw [derivative_test_integral_congr μ ψ _ (fun x => (conductivityFlux u A x).col j) (by
      intro x hx
      simp only [conductivityFlux, fderiv_eq_of_eqOn_open hV he (hs hx)])]
    exact hdiv j hj ψ hψ hc (hs.trans hVU)
  obtain ⟨W, hW, hpW, hWV, hWc, hw⟩ := exists_selected_split_on_subpatch J μ v hv A hAp
    hV (hUb.subset hVU) (hpV (mem_singleton p)) (hA.mono hVU) hdivv (hep ▸ hD)
    d L hLd B hB hBn hθ hθ1 hm hpath C hC hCs hdet hconstit hG hCG
  refine ⟨W, hW, hpW, hWV.trans hVU, hWc, ?_⟩
  intro O hO hOW ε hε
  obtain ⟨R, q, hq, hqr, hqG, hqm⟩ := hw O hO hOW ε hε
  exact ⟨R.changeOld hO (he.mono (hOW.trans (subset_closure.trans hWV))) (fun _ _ => rfl),
    q, hq, hqr, hqG, hqm⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_MatrixFiniteLaminate
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
namespace ScalarConductivity

theorem isOpen_matrixFiniteLaminate {a b : ℝ} (ha : 0 < a) :
    IsOpen (matrixFiniteLaminate a b) :=
  isOpen_spectralExtension (isOpen_finiteLaminate ha) (fun _ h e => h.permute e)

open Set Filter Topology

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_ConjugateDiagonal
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3
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
open Matrix Set Filter Topology
open scoped Matrix.Norms.Elementwise

lemma conjugateDiagonal_continuous (Q : Mat3) : Continuous (conjugateDiagonal Q) := by
  apply Continuous.subtype_mk
  exact continuous_const.matrix_mul (continuous_pi (fun i => continuous_pi (fun j => by
    by_cases hij : i = j
    · subst j; simpa only [Matrix.diagonal_apply_eq] using continuous_apply i
    · simpa only [Matrix.diagonal_apply_ne _ hij] using
        (continuous_const : Continuous (fun _ : DiagonalTriple => (0:ℝ)))))) |>.matrix_mul continuous_const

lemma conjugateDiagonal_spectral {Q : Mat3} (hQ : Q ∈ orthogonalFrames)
    {α : DiagonalTriple} {T : Set DiagonalTriple} (hα : α ∈ T) :
    conjugateDiagonal Q α ∈ spectralExtension T := ⟨Q, hQ, α, hα, rfl⟩

lemma stretched_preliminary (i : Fin 3) {A α : DiagonalTriple}
    (hq : preliminaryQ i A α ≠ 0) (hA : A i ≠ 0) :
    stretchedDiagonal i (preliminaryQ i A α) (preliminaryB i A α) = α := by
  ext j
  by_cases hj : j = i
  · subst j
    simp [stretchedDiagonal, preliminaryB, preliminaryQ, hA]
  · simp [stretchedDiagonal, preliminaryB, hj, hq]

lemma continuousAt_stretchedDiagonal {i : Fin 3} {q : ℝ → ℝ} {D : ℝ → DiagonalTriple}
    {z : ℝ} (hq : ContinuousAt q z) (hD : ContinuousAt D z) (hn : q z ≠ 0) :
    ContinuousAt (fun t => stretchedDiagonal i (q t) (D t)) z := by
  apply continuousAt_pi.mpr; intro j
  have hj := continuousAt_pi.mp hD j
  by_cases hji : j = i
  · change ContinuousAt (fun y => if j = i then q y * D y j else D y j / q y) z
    simp only [ite_eq_left hji]
    exact hq.mul hj
  · change ContinuousAt (fun y => if j = i then q y * D y j else D y j / q y) z
    simp only [ite_eq_right hji]
    exact hj.div hq hn

lemma contDiffAt_stretchedDiagonal {i : Fin 3} {q : ℝ → ℝ} {D : ℝ → DiagonalTriple}
    {z : ℝ} {k : WithTop ℕ∞} (hq : ContDiffAt ℝ k q z) (hD : ContDiffAt ℝ k D z)
    (hn : q z ≠ 0) : ContDiffAt ℝ k (fun t => stretchedDiagonal i (q t) (D t)) z := by
  apply contDiffAt_pi.mpr; intro j
  have hj := contDiffAt_pi.mp hD j
  by_cases hji : j = i
  · change ContDiffAt ℝ k (fun y => if j = i then q y * D y j else D y j / q y) z
    simp only [ite_eq_left hji]
    exact hq.mul hj
  · change ContDiffAt ℝ k (fun y => if j = i then q y * D y j else D y j / q y) z
    simp only [ite_eq_right hji]
    exact hj.div hq hn

lemma conjugateDiagonal_contDiff (Q : Mat3) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun α : DiagonalTriple => (conjugateDiagonal Q α).val) := by
  rw [contDiff_iff_contDiffAt]; intro α
  apply contDiffAt_matrix_mul _ contDiffAt_const
  apply contDiffAt_matrix_mul contDiffAt_const
  apply contDiffAt_pi.mpr; intro i
  apply contDiffAt_pi.mpr; intro j
  by_cases hij : i = j
  · subst j; simpa only [Matrix.diagonal_apply_eq, id_eq] using
      (contDiffAt_pi.mp (contDiffAt_id (x := α)) i)
  · simpa only [Matrix.diagonal_apply_ne _ hij] using
      (contDiffAt_const : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun _ : DiagonalTriple => (0:ℝ)) α)

theorem spectral_join_plan {a b : ℝ} (ha : 0 < a) {T : Set DiagonalTriple}
    (hT : ∀ α ∈ T, IsFiniteLaminate a b α)
    (i : Fin 3) {α β : DiagonalTriple} (hα : α ∈ T) (hβ : β ∈ T)
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    {Q : Mat3} (hQ : Q ∈ orthogonalFrames) :
    let A := conjugateDiagonal Q (coordinateJoin i θ α β)
    ∃ (d : Coord3) (L : Coord3 →L[ℝ] ℝ) (B : Mat3) (η c m : ℝ)
      (C : ℝ → Symmetric3),
      L d = 1 ∧ B.IsSymm ∧ (∀ v, L (B *ᵥ v) = 0) ∧
      0 < η ∧ η < 1 ∧ 0 < m ∧
      (∀ z ∈ Icc (-η) (1-η), m ≤ 1+c*z) ∧
      (∀ z ∈ Icc (-η) (1-η), ContinuousAt C z) ∧
      (∀ z ∈ Icc (-η) (1-η), ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun t => (C t).val) z) ∧
      (∀ z ∈ Icc (-η) (1-η), 0 < (splitJacobian d L c z).det) ∧
      (∀ z ∈ Icc (-η) (1-η), (C z).val =
        (splitJacobian d L c z).det⁻¹ •
          (splitJacobian d L c z * (A.val + z • B) * (splitJacobian d L c z)ᵀ)) ∧
      (∀ z ∈ Icc (-η) (1-η), C z ∈ matrixFiniteLaminate a b) ∧
      C (-η) ∈ spectralExtension T ∧ C (1-η) ∈ spectralExtension T := by
  let A := coordinateJoin i θ α β
  let P := preliminaryB i A α
  let N := preliminaryB i A β
  let qp := preliminaryQ i A α
  let qm := preliminaryQ i A β
  let η := θ/qp
  have hαi : 0 < α i := ha.trans ((hT α hα).bounds ha i).1
  have hβi : 0 < β i := ha.trans ((hT β hβ).bounds ha i).1
  have hf : 0 < qp ∧ 0 < qm ∧ 0 < η ∧ 0 < (1-θ)/qm ∧
    η+(1-θ)/qm=1 ∧ η*qp+((1-θ)/qm)*qm=1 := by
    simpa [qp, qm, η, A, preliminaryQ, coordinateJoin] using
      preliminary_fractions hαi hβi hθ hθ1
  have hη1 : η < 1 := by linarith [hf.2.2.2.1, hf.2.2.2.2.1]
  let c := qp-qm
  let q : ℝ → ℝ := fun z => 1+c*z
  let D : ℝ → DiagonalTriple := fun z => A + z • (P-N)
  let C : ℝ → Symmetric3 := fun z => conjugateDiagonal Q (stretchedDiagonal i (q z) (D z))
  have hs (z : ℝ) :
      q z = (z+η)*qp+(1-(z+η))*qm ∧
      D z = (z+η) • P + (1-(z+η)) • N := by
    have hh := preliminary_segment i hαi hβi hθ hθ1 z
    refine ⟨?_, hh.1⟩
    change 1 + (qp-qm)*z = _
    have heq : 1+z*(qp-qm)=(z+η)*qp+(1-(z+η))*qm := hh.2.1
    linarith only [heq]
  have hq (z : ℝ) (hz : z ∈ Icc (-η) (1-η)) : min qp qm ≤ q z := by
    rw [(hs z).1]
    have ht : 0 ≤ z+η := by linarith [hz.1]
    have ht' : 0 ≤ 1-(z+η) := by linarith [hz.2]
    have h1 := mul_le_mul_of_nonneg_left (min_le_left qp qm) ht
    have h2 := mul_le_mul_of_nonneg_left (min_le_right qp qm) ht'
    nlinarith
  have hm : 0 < min qp qm := lt_min hf.1 hf.2.1
  have hqpos (z : ℝ) (hz : z ∈ Icc (-η) (1-η)) : 0 < q z := hm.trans_le (hq z hz)
  have hP : P i = N i := by simp [P, N, preliminaryB]
  refine ⟨rotatedDirection Q i, rotatedPhase Q i, Q * Matrix.diagonal (P-N) * Qᵀ,
    η, c, min qp qm, C, rotated_normalization hQ i, ?_,
    rotated_increment_annihilates hQ i hP, hf.2.2.1, hη1, hm, hq, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Matrix.isHermitian_iff_isSymm.mp (conjugateDiagonal Q (P-N)).property
  · intro z hz
    exact (conjugateDiagonal_continuous Q).continuousAt.comp
      (continuousAt_stretchedDiagonal (continuous_const.add
        (continuous_const.mul continuous_id)).continuousAt
        (continuous_const.add (continuous_id.smul continuous_const)).continuousAt (hqpos z hz).ne')
  · intro z hz
    exact (conjugateDiagonal_contDiff Q).contDiffAt.comp z
      (contDiffAt_stretchedDiagonal (contDiffAt_const.add
        (contDiffAt_const.mul contDiffAt_id))
        (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)) (hqpos z hz).ne')
  · intro z hz
    rw [splitJacobian_det _ _ (rotated_normalization hQ i)]
    exact hqpos z hz
  · intro z hz
    rw [splitJacobian_rotated hQ]
    change Q * Matrix.diagonal (stretchedDiagonal i (q z) (D z)) * Qᵀ = _
    have he : (conjugateDiagonal Q A).val + z • (Q * Matrix.diagonal (P-N) * Qᵀ) =
        Q * Matrix.diagonal (D z) * Qᵀ := by
      change Q * Matrix.diagonal A * Qᵀ + z • (Q * Matrix.diagonal (P-N) * Qᵀ) =
        Q * Matrix.diagonal (A + z • (P-N)) * Qᵀ
      have hd : Matrix.diagonal (A+z • (P-N)) =
          Matrix.diagonal A + z • Matrix.diagonal (P-N) := by
        ext j k
        by_cases hjk : j = k
        · subst k; simp
        · simp [hjk]
      rw [hd, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [he, conjugated_push hQ, normalStretch_push i (hqpos z hz).ne']
  · intro z hz
    have hz' : z ∈ Icc (-η) ((1-θ)/qm) := by
      constructor; exact hz.1; linarith [hz.2, hf.2.2.2.2.1]
    obtain ⟨_, w, hw, he⟩ := affine_synchronized_path i hαi hβi hθ hθ1 z hz'
    have hd : stretchedDiagonal i (q z) (D z) = coordinateJoin i w α β := by
      simpa only [q, c, mul_comm] using he
    change conjugateDiagonal Q _ ∈ spectralExtension _
    rw [hd]
    exact conjugateDiagonal_spectral hQ (.join i w hw.1 hw.2 (hT α hα) (hT β hβ))
  · have he := hs (-η)
    have eq : q (-η) = qm := by simpa using he.1
    have ed : D (-η) = N := by simpa using he.2
    change conjugateDiagonal Q (stretchedDiagonal i (q (-η)) (D (-η))) ∈ _
    rw [eq, ed, stretched_preliminary i hf.2.1.ne']
    · exact conjugateDiagonal_spectral hQ hβ
    · simpa [A, coordinateJoin] using (harmonic_parent_pos hαi hβi hθ hθ1).ne'
  · have he := hs (1-η)
    have eq : q (1-η) = qp := by simpa using he.1
    have ed : D (1-η) = P := by simpa using he.2
    change conjugateDiagonal Q (stretchedDiagonal i (q (1-η)) (D (1-η))) ∈ _
    rw [eq, ed, stretched_preliminary i hf.1.ne']
    · exact conjugateDiagonal_spectral hQ hα
    · simpa [A, coordinateJoin] using (harmonic_parent_pos hαi hβi hθ hθ1).ne'

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CompactDepthReductionTwo
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3
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
open scoped Matrix.Norms.Elementwise

theorem exists_compact_depth_reduction_two
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3)
    {U : Set Coord3} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hu : ContDiffOn ℝ (↑(⊤ : ℕ∞)) u U)
    (hA : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x => (A x).val) U)
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    {a b : ℝ} (ha : 0 < a) {T : Set DiagonalTriple}
    (hT : IsOpen T) (hsub : ∀ d ∈ T, IsFiniteLaminate a b d)
    (hperm : ∀ d ∈ T, ∀ e : Equiv.Perm (Fin 3), d ∘ e ∈ T)
    {p : Coord3} (hpU : p ∈ U)
    (hD : Function.Surjective (fderiv ℝ u p)) {n : ℕ}
    (hp : A p ∈ spectralExtension (depthClass T (n+1)))
    (hn : A p ∉ spectralExtension (depthClass T n)) :
    ∃ W : Set Coord3, IsOpen W ∧ p ∈ W ∧ closure W ⊆ U ∧ IsCompact (closure W) ∧
      ∀ O : Set Coord3, IsOpen O → O ⊆ W → ∀ ε : ℝ, 0 < ε →
      ∃ R : CompactTwoFieldReplacement μ O u A,
        (∀ x ∈ O, R.tensor x ∈ matrixFiniteLaminate a b) ∧
        μ {x | x ∈ O ∧ R.tensor x ∉ spectralExtension (depthClass T n)} ≤ ENNReal.ofReal ε := by
  obtain ⟨Q, hQ, d, hd, hrep⟩ := hp
  have hdn : d ∉ depthClass T n := fun h => hn ⟨Q, hQ, d, h, hrep⟩
  obtain ⟨i, θ, α, β, hθ, hθ1, hα, hβ, he, _⟩ := depthClass_plan hsub hd hdn
  have hre : conjugateDiagonal Q (coordinateJoin i θ α β) = A p := by
    apply Subtype.ext
    simpa only [conjugateDiagonal, he] using hrep.symm
  obtain ⟨v, L, B, η, c, m, C, hLv, hB, hBn, hη, hη1, hm, hpath, hC, hCs,
    hdet, hconst, hCG, hCa, hCb⟩ := spectral_join_plan ha
      (depthClass_subset_laminate hsub n) i hα hβ hθ hθ1 hQ
  rw [hre] at hconst
  have hTo : IsOpen (spectralExtension (depthClass T n)) :=
    isOpen_spectralExtension (isOpen_depthClass ha hT hsub n) (depthClass_permute hperm n)
  let G := endpointGraph (-η) (1-η) (matrixFiniteLaminate a b)
    (spectralExtension (depthClass T n)) (spectralExtension (depthClass T n))
  have hGo : IsOpen G := isOpen_endpointGraph _ _ (isOpen_matrixFiniteLaminate ha) hTo hTo
  have hGC : ∀ z ∈ Icc (-η) (1-η), (z, C z) ∈ G :=
    path_mem_endpointGraph _ _ C hCG hCa hCb
  obtain ⟨W, hW, hpW, hWU, hWc, hop⟩ := exists_locally_smooth_compact_split μ u A
    hU hUb hpU hu hA hdiv hD v L hLv B hB hBn hη hη1 hm hpath C hC hCs hdet hconst hGo hGC
  refine ⟨W, hW, hpW, hWU, hWc, ?_⟩
  intro O hO hOW ε hε
  obtain ⟨R, q, _, _, hqG, hqm⟩ := hop O hO hOW ε hε
  refine ⟨R, fun x hx => (hqG x hx).1, le_trans (measure_mono ?_) hqm⟩
  intro x hx
  refine ⟨hx.1, ?_, ?_⟩
  · exact (hqG x hx.1).2.1.resolve_right hx.2
  · exact (hqG x hx.1).2.2.resolve_right hx.2

end ScalarConductivity

namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

theorem exists_compact_depth_reduction_selected
    (J : Set (Fin 2))
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3)
    {U : Set Coord3} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hu : ContDiffOn ℝ (↑(⊤ : ℕ∞)) u U)
    (hA : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x => (A x).val) U)
    (hdiv : ∀ j ∈ J, ∀ (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    {a b : ℝ} (ha : 0 < a) {T : Set DiagonalTriple}
    (hT : IsOpen T) (hsub : ∀ d ∈ T, IsFiniteLaminate a b d)
    (hperm : ∀ d ∈ T, ∀ e : Equiv.Perm (Fin 3), d ∘ e ∈ T)
    {p : Coord3} (hpU : p ∈ U)
    (hD : Function.Surjective (fderiv ℝ u p)) {n : ℕ}
    (hp : A p ∈ spectralExtension (depthClass T (n+1)))
    (hn : A p ∉ spectralExtension (depthClass T n)) :
    ∃ W : Set Coord3, IsOpen W ∧ p ∈ W ∧ closure W ⊆ U ∧ IsCompact (closure W) ∧
      ∀ O : Set Coord3, IsOpen O → O ⊆ W → ∀ ε : ℝ, 0 < ε →
      ∃ R : CompactSelectedReplacement J μ O u A,
        (∀ x ∈ O, R.tensor x ∈ matrixFiniteLaminate a b) ∧
        μ {x | x ∈ O ∧ R.tensor x ∉ spectralExtension (depthClass T n)} ≤ ENNReal.ofReal ε := by
  obtain ⟨Q, hQ, d, hd, hrep⟩ := hp
  have hdn : d ∉ depthClass T n := fun h => hn ⟨Q, hQ, d, h, hrep⟩
  obtain ⟨i, θ, α, β, hθ, hθ1, hα, hβ, he, _⟩ := depthClass_plan hsub hd hdn
  have hre : conjugateDiagonal Q (coordinateJoin i θ α β) = A p := by
    apply Subtype.ext
    simpa only [conjugateDiagonal, he] using hrep.symm
  obtain ⟨v, L, B, η, c, m, C, hLv, hB, hBn, hη, hη1, hm, hpath, hC, hCs,
    hdet, hconst, hCG, hCa, hCb⟩ := spectral_join_plan ha
      (depthClass_subset_laminate hsub n) i hα hβ hθ hθ1 hQ
  rw [hre] at hconst
  have hTo : IsOpen (spectralExtension (depthClass T n)) :=
    isOpen_spectralExtension (isOpen_depthClass ha hT hsub n) (depthClass_permute hperm n)
  let G := endpointGraph (-η) (1-η) (matrixFiniteLaminate a b)
    (spectralExtension (depthClass T n)) (spectralExtension (depthClass T n))
  have hGo : IsOpen G := isOpen_endpointGraph _ _ (isOpen_matrixFiniteLaminate ha) hTo hTo
  have hGC : ∀ z ∈ Icc (-η) (1-η), (z, C z) ∈ G :=
    path_mem_endpointGraph _ _ C hCG hCa hCb
  obtain ⟨W, hW, hpW, hWU, hWc, hop⟩ := exists_locally_smooth_selected_split J μ u A
    hU hUb hpU hu hA hdiv hD v L hLv B hB hBn hη hη1 hm hpath C hC hCs hdet hconst hGo hGC
  refine ⟨W, hW, hpW, hWU, hWc, ?_⟩
  intro O hO hOW ε hε
  obtain ⟨R, q, _, _, hqG, hqm⟩ := hop O hO hOW ε hε
  refine ⟨R, fun x hx => (hqG x hx).1, le_trans (measure_mono ?_) hqm⟩
  intro x hx
  refine ⟨hx.1, ?_, ?_⟩
  · exact (hqG x hx.1).2.1.resolve_right hx.2
  · exact (hqG x hx.1).2.2.resolve_right hx.2

end ScalarConductivity

namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

lemma exists_independent_pairedPotential_at {u : Coord3 → ℝ} {p : Coord3}
    (hu : DifferentiableAt ℝ u p) (hp : fderiv ℝ u p ≠ 0) :
    ∃ j : Fin 3, Function.Surjective (fderiv ℝ (pairedPotential u j) p) := by
  obtain ⟨i, hi⟩ := exists_coordinate_nonzero hp
  obtain ⟨j, hji⟩ := exists_ne i
  refine ⟨j, ?_⟩
  rw [(pairedPotential_hasFDerivAt hu.hasFDerivAt j).fderiv]
  exact pairedFunctional_surjective hi hji.symm

lemma pairedPotential_contDiffOn {u : Coord3 → ℝ} {O : Set Coord3}
    (hu : ContDiffOn ℝ (↑(⊤ : ℕ∞)) u O) (j : Fin 3) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (pairedPotential u j) O := by
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact hu
  · exact (contDiff_apply ℝ ℝ j).contDiffOn

lemma column_derivative_ne_zero_of_independent {O : Set Coord3} (hO : IsOpen O)
    {v : Coord3 → Fin 2 → ℝ} (hv : DifferentiableOn ℝ v O)
    {x : Coord3} (hx : x ∈ O)
    (hr : LinearIndependent ℝ (gradientColumns (fderiv ℝ v x)).col) (j : Fin 2) :
    fderiv ℝ (fun y => v y j) x ≠ 0 := by
  intro hz
  have hh := ((ContinuousLinearMap.proj j).hasFDerivAt.comp x
    ((hv x hx).differentiableAt (hO.mem_nhds hx)).hasFDerivAt).fderiv
  have hzero : (gradientColumns (fderiv ℝ v x)).col j = 0 := by
    ext i
    have h := congrArg (fun L : Coord3 →L[ℝ] ℝ => L (Pi.single i 1)) (hh.symm.trans hz)
    exact h
  exact (hr.ne_zero j) hzero

lemma conductivityFlux_affine_column {O : Set Coord3} (hO : IsOpen O)
    {u v : Coord3 → Fin 2 → ℝ} {l κ : Fin 2 → ℝ} (A : Coord3 → Symmetric3)
    (he : ∀ x ∈ O, ∀ j, u x j = l j * v x 0 + κ j)
    (hv : DifferentiableOn ℝ v O) {x : Coord3} (hx : x ∈ O) (j : Fin 2) :
    (conductivityFlux u A x).col j = l j • (conductivityFlux v A x).col 0 := by
  ext i
  change (∑ k, (A x).val i k * gradientColumns (fderiv ℝ u x) k j) =
    l j * ∑ k, (A x).val i k * gradientColumns (fderiv ℝ v x) k 0
  simp_rw [gradientColumns_affine_column hO he hv hx]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma active_flux_harmonic_of_affine
    (μ : Measure Coord3) {O : Set Coord3} (hO : IsOpen O)
    {u v : Coord3 → Fin 2 → ℝ} {l κ : Fin 2 → ℝ} (A : Coord3 → Symmetric3)
    (he : ∀ x ∈ O, ∀ j, u x j = l j * v x 0 + κ j)
    (hv : DifferentiableOn ℝ v O) {j : Fin 2} (hj : l j ≠ 0)
    (hdiv : ∀ (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ O → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0) :
    ∀ (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ O → (∫ x, fderiv ℝ ψ x ((conductivityFlux v A x).col 0) ∂μ) = 0 := by
  intro ψ hψ hc hs
  have heq : (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) =
      l j * ∫ x, fderiv ℝ ψ x ((conductivityFlux v A x).col 0) ∂μ := by
    rw [derivative_test_integral_congr μ ψ _
      (fun x => l j • (conductivityFlux v A x).col 0)
      (fun x hx => conductivityFlux_affine_column hO A he hv (hs hx) j)]
    simp_rw [map_smul, smul_eq_mul]
    exact integral_const_mul _ _
  exact (mul_eq_zero.mp (heq.symm.trans (hdiv ψ hψ hc hs))).resolve_left hj

lemma TwoFieldRankRegular.mono {u : Coord3 → Fin 2 → ℝ} {O W : Set Coord3}
    (h : TwoFieldRankRegular u O) (hW : W ⊆ O) : TwoFieldRankRegular u W := by
  rcases h with h | h | ⟨κ, hκ⟩
  · exact Or.inl (fun x hx => h x (hW hx))
  · obtain ⟨v, l, κ, hv, hl, hd, he⟩ := h
    exact Or.inr (Or.inl ⟨v, l, κ, hv.mono hW, hl, fun x hx => hd x (hW hx),
      fun x hx => he x (hW hx)⟩)
  · exact Or.inr (Or.inr ⟨κ, fun x hx => hκ x (hW hx)⟩)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_Unchanged
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3
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
open scoped Matrix.Norms.Elementwise

lemma exists_precompact_open_inside {U : Set Coord3} (hU : IsOpen U)
    {p : Coord3} (hp : p ∈ U) :
    ∃ W : Set Coord3, IsOpen W ∧ p ∈ W ∧ closure W ⊆ U ∧ IsCompact (closure W) := by
  obtain ⟨K, hpK, hKU, hK⟩ := local_compact_nhds (hU.mem_nhds hp)
  have he : closure (interior K) ⊆ K := hK.isClosed.closure_subset_iff.mpr interior_subset
  exact ⟨interior K, isOpen_interior, mem_interior_iff_mem_nhds.mpr hpK,
    he.trans hKU, hK.of_isClosed_subset isClosed_closure he⟩

lemma spectral_depth_subset {a b : ℝ} {T : Set DiagonalTriple}
    (hsub : ∀ d ∈ T, IsFiniteLaminate a b d) (n : ℕ) :
    spectralExtension (depthClass T n) ⊆ matrixFiniteLaminate a b := by
  rintro S ⟨Q, hQ, d, hd, hre⟩
  exact ⟨Q, hQ, d, depthClass_subset_laminate hsub n d hd, hre⟩

theorem exists_compact_depth_reduction_regular_nontrivial
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3)
    {U : Set Coord3} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hu : ContDiffOn ℝ (↑(⊤ : ℕ∞)) u U)
    (hA : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x => (A x).val) U)
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    (hr : TwoFieldRankRegular u U)
    {a b : ℝ} (ha : 0 < a) {T : Set DiagonalTriple}
    (hT : IsOpen T) (hsub : ∀ d ∈ T, IsFiniteLaminate a b d)
    (hperm : ∀ d ∈ T, ∀ e : Equiv.Perm (Fin 3), d ∘ e ∈ T)
    {p : Coord3} (hpU : p ∈ U) {n : ℕ}
    (hp : A p ∈ spectralExtension (depthClass T (n+1)))
    (hn : A p ∉ spectralExtension (depthClass T n))
    (hsc : (spectralExtension (depthClass T n)).Nonempty) :
    ∃ W : Set Coord3, IsOpen W ∧ p ∈ W ∧ closure W ⊆ U ∧ IsCompact (closure W) ∧
      ∀ O : Set Coord3, IsOpen O → O ⊆ W → ∀ ε : ℝ, 0 < ε →
      ∃ R : CompactCompatibleReplacement μ O u A,
        TwoFieldRankRegular (fun x => u x+R.du x) O ∧
        (∀ x ∈ O, R.tensor x ∈ matrixFiniteLaminate a b) ∧
        μ {x | x ∈ O ∧ R.tensor x ∉ spectralExtension (depthClass T n)} ≤ ENNReal.ofReal ε := by
  rcases hr with hr | hr | ⟨κ, hκ⟩
  · obtain ⟨W, hW, hpW, hWU, hWc, hop⟩ := exists_compact_depth_reduction_two μ u A
      hU hUb hu hA hdiv ha hT hsub hperm hpU
      (gradientColumns_surjective _ (hr p hpU)) hp hn
    refine ⟨W, hW, hpW, hWU, hWc, ?_⟩
    intro O hO hOW ε hε
    obtain ⟨R, hRG, hbad⟩ := hop O hO hOW ε hε
    exact ⟨R.forgetRank, Or.inl R.rank, hRG, hbad⟩
  · obtain ⟨v, l, κ, hv, ⟨j, hj⟩, hvd, he⟩ := hr
    obtain ⟨i, hi⟩ := exists_independent_pairedPotential_at
      ((hv.differentiableOn (by simp) p hpU).differentiableAt (hU.mem_nhds hpU)) (hvd p hpU)
    let V := pairedPotential v i
    have hV : ContDiffOn ℝ (↑(⊤ : ℕ∞)) V U := pairedPotential_contDiffOn hv i
    have heV : ∀ x ∈ U, ∀ j, u x j = l j * V x 0 + κ j := he
    have hdivV : ∀ k ∈ ({0} : Set (Fin 2)), ∀ (ψ : Coord3 → ℝ),
        ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        (∫ x, fderiv ℝ ψ x ((conductivityFlux V A x).col k) ∂μ) = 0 := by
      intro k hk
      have hk0 : k = 0 := Set.mem_singleton_iff.mp hk
      subst k
      exact active_flux_harmonic_of_affine μ hU A heV (hV.differentiableOn (by simp)) hj (hdiv j)
    obtain ⟨W, hW, hpW, hWU, hWc, hop⟩ := exists_compact_depth_reduction_selected {0} μ V A
      hU hUb hV hA hdivV ha hT hsub hperm hpU hi hp hn
    refine ⟨W, hW, hpW, hWU, hWc, ?_⟩
    intro O hO hOW ε hε
    obtain ⟨R, hRG, hbad⟩ := hop O hO hOW ε hε
    have hOU := hOW.trans (subset_closure.trans hWU)
    have hVO := hV.mono hOU
    have heO : ∀ x ∈ O, ∀ j, u x j = l j * V x 0 + κ j := fun x hx => heV x (hOU hx)
    let P := R.affineTransfer hO heO hVO
    refine ⟨P, Or.inr (Or.inl ⟨fun x => (V x+R.du x) 0, l, κ,
      contDiffOn_pi.mp (hVO.add R.smooth_du.contDiffOn) 0, ⟨j, hj⟩, ?_, ?_⟩), hRG, hbad⟩
    · intro x hx
      exact column_derivative_ne_zero_of_independent hO
        ((hVO.add R.smooth_du.contDiffOn).differentiableOn (by simp)) hx (R.rank x hx) 0
    · exact R.affineTransfer_relation hO heO hVO
  · obtain ⟨W, hW, hpW, hWU, hWc⟩ := exists_precompact_open_inside hU hpU
    obtain ⟨S, hS⟩ := hsc
    refine ⟨W, hW, hpW, hWU, hWc, ?_⟩
    intro O hO hOW ε _
    have hOU := hOW.trans (subset_closure.trans hWU)
    let R := CompactCompatibleReplacement.constantRank μ hO u A
      (fun x hx => hκ x (hOU hx)) S
    refine ⟨R, ?_, fun _ _ => spectral_depth_subset hsub n hS, ?_⟩
    · exact Or.inr (Or.inr ⟨κ, fun x hx => by
        change u x + 0 = κ
        rw [add_zero, hκ x (hOU hx)]⟩)
    · have he : {x | x ∈ O ∧ R.tensor x ∉ spectralExtension (depthClass T n)} = ∅ := by
        ext x
        simp only [R, CompactCompatibleReplacement.constantRank, hS, not_true_eq_false,
          and_false, mem_ofPred_eq, mem_empty_iff_false]
      rw [he, measure_empty]
      exact bot_le

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CompactDepthReductionRegular
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3
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
open scoped Matrix.Norms.Elementwise

theorem exists_compact_depth_reduction_regular
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3)
    {U : Set Coord3} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hu : ContDiffOn ℝ (↑(⊤ : ℕ∞)) u U)
    (hA : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x => (A x).val) U)
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    (hr : TwoFieldRankRegular u U)
    {a b : ℝ} (ha : 0 < a) {T : Set DiagonalTriple}
    (hT : IsOpen T) (hsub : ∀ d ∈ T, IsFiniteLaminate a b d)
    (hperm : ∀ d ∈ T, ∀ e : Equiv.Perm (Fin 3), d ∘ e ∈ T)
    {p : Coord3} (hpU : p ∈ U) {n : ℕ}
    (hp : A p ∈ spectralExtension (depthClass T (n+1)))
    (hsc : (spectralExtension (depthClass T n)).Nonempty) :
    ∃ W : Set Coord3, IsOpen W ∧ p ∈ W ∧ closure W ⊆ U ∧ IsCompact (closure W) ∧
      ∀ O : Set Coord3, IsOpen O → O ⊆ W → ∀ ε : ℝ, 0 < ε →
      ∃ R : CompactCompatibleReplacement μ O u A,
        TwoFieldRankRegular (fun x => u x+R.du x) O ∧
        (∀ x ∈ O, R.tensor x ∈ matrixFiniteLaminate a b) ∧
        μ {x | x ∈ O ∧ R.tensor x ∉ spectralExtension (depthClass T n)} ≤ ENNReal.ofReal ε := by
  classical
  by_cases hn : A p ∈ spectralExtension (depthClass T n)
  · have hTo := isOpen_spectralExtension (isOpen_depthClass ha hT hsub n) (depthClass_permute hperm n)
    have hAc : ContinuousAt A p := Topology.IsInducing.subtypeVal.continuousAt_iff.mpr
      (hA.continuousOn.continuousAt (hU.mem_nhds hpU))
    have hev : ∀ᶠ x in 𝓝 p, x ∈ U ∧ A x ∈ spectralExtension (depthClass T n) :=
      Filter.Eventually.and (hU.mem_nhds hpU) (hAc.preimage_mem_nhds (hTo.mem_nhds hn))
    obtain ⟨V, hVs, hV, hpV⟩ := mem_nhds_iff.mp hev
    obtain ⟨W, hW, hpW, hWV, hWc⟩ := exists_precompact_open_inside hV hpV
    have hVU : V ⊆ U := fun x hx => (hVs hx).1
    refine ⟨W, hW, hpW, hWV.trans hVU, hWc, ?_⟩
    intro O hO hOW ε _
    have hOV := hOW.trans (subset_closure.trans hWV)
    have hOU := hOV.trans hVU
    let R := CompactCompatibleReplacement.unchanged μ O u A (hA.mono hOU)
    refine ⟨R, ?_, fun x hx => spectral_depth_subset hsub n (hVs (hOV hx)).2, ?_⟩
    · simpa only [R, CompactCompatibleReplacement.unchanged, Pi.zero_apply, add_zero] using hr.mono hOU
    · have he : {x | x ∈ O ∧ R.tensor x ∉ spectralExtension (depthClass T n)} = ∅ := by
        ext x
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_not]
        intro hx
        exact (hVs (hOV hx)).2
      rw [he, measure_empty]
      exact bot_le
  · exact exists_compact_depth_reduction_regular_nontrivial μ u A hU hUb hu hA hdiv hr
      ha hT hsub hperm hpU hp hn hsc

end ScalarConductivity

namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

theorem assemble_compatible_replacements
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {I : Type*} [Fintype I] [DecidableEq I]
    (O : I → Set Coord3) (hO : ∀ i, IsOpen (O i))
    (hd : Pairwise (fun i j => Disjoint (O i) (O j)))
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3)
    (R : ∀ i, CompactCompatibleReplacement μ (O i) u A) :
    ∃ (du : Coord3 → Fin 2 → ℝ) (dF : Coord3 → Matrix (Fin 3) (Fin 2) ℝ),
      ContDiff ℝ (↑(⊤ : ℕ∞)) du ∧ HasCompactSupport du ∧ tsupport du ⊆ ⋃ i, O i ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) dF ∧ HasCompactSupport dF ∧ tsupport dF ⊆ ⋃ i, O i ∧
      (∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
        (∫ x, fderiv ℝ ψ x ((dF x).col j) ∂μ) = 0) ∧
      (∀ i, EqOn du (R i).du (O i) ∧ EqOn dF (R i).dF (O i) ∧
        ∀ x ∈ O i,
          fderiv ℝ (fun y => u y+du y) x = fderiv ℝ (fun y => u y+(R i).du y) x) ∧
      (∀ x ∉ ⋃ i, O i, du x = 0 ∧ dF x = 0) := by
  let du : Coord3 → Fin 2 → ℝ := fun x => ∑ i, (R i).du x
  let dF : Coord3 → Matrix (Fin 3) (Fin 2) ℝ := fun x => ∑ i, (R i).dF x
  have heu : ∀ i, EqOn du (R i).du (O i) :=
    supported_sum_eq_on O hd (fun i => (R i).du) (fun i => (R i).support_du)
  have heF : ∀ i, EqOn dF (R i).dF (O i) :=
    supported_sum_eq_on O hd (fun i => (R i).dF) (fun i => (R i).support_dF)
  have hcdu : HasCompactSupport du := by
    simpa only [du, ← Finset.sum_apply] using
      (HasCompactSupport.finset_sum (s := Finset.univ) (fun i _ => (R i).compact_du))
  have hcdF : HasCompactSupport dF := by
    simpa only [dF, ← Finset.sum_apply] using
      (HasCompactSupport.finset_sum (s := Finset.univ) (fun i _ => (R i).compact_dF))
  refine ⟨du, dF, ContDiff.sum (fun i _ => (R i).smooth_du),
    hcdu,
    (tsupport_finite_sum_subset _).trans (iUnion_mono (fun i => (R i).support_du)),
    ContDiff.sum (fun i _ => (R i).smooth_dF),
    hcdF,
    (tsupport_finite_sum_subset _).trans (iUnion_mono (fun i => (R i).support_dF)), ?_, ?_, ?_⟩
  · exact finite_sum_cauchy_preserving μ (fun i => (R i).dF)
      (fun i => (R i).smooth_dF) (fun i => (R i).compact_dF) (fun i => (R i).cauchy_dF)
  · intro i
    refine ⟨heu i, heF i, ?_⟩
    intro x hx
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [(hO i).mem_nhds hx] with y hy
    rw [heu i hy]
  · intro x hx
    exact ⟨supported_sum_eq_zero_off O _ (fun i => (R i).support_du) hx,
      supported_sum_eq_zero_off O _ (fun i => (R i).support_dF) hx⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_AssembleCompatibleTensors
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
open scoped Matrix.Norms.Elementwise

theorem assemble_compatible_tensors
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {I : Type*} [Fintype I] [DecidableEq I]
    (O : I → Set Coord3) (hO : ∀ i, IsOpen (O i))
    (hd : Pairwise (fun i j => Disjoint (O i) (O j)))
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3) (hA : Measurable A)
    (R : ∀ i, CompactCompatibleReplacement μ (O i) u A) :
    ∃ (du : Coord3 → Fin 2 → ℝ) (dF : Coord3 → Matrix (Fin 3) (Fin 2) ℝ)
      (T : Coord3 → Symmetric3),
      ContDiff ℝ (↑(⊤ : ℕ∞)) du ∧ HasCompactSupport du ∧ tsupport du ⊆ ⋃ i, O i ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) dF ∧ HasCompactSupport dF ∧ tsupport dF ⊆ ⋃ i, O i ∧
      (∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
        (∫ x, fderiv ℝ ψ x ((dF x).col j) ∂μ) = 0) ∧ Measurable T ∧
      (∀ i, EqOn du (R i).du (O i) ∧ EqOn dF (R i).dF (O i) ∧
        EqOn T (R i).tensor (O i)) ∧ EqOn T A (⋃ i, O i)ᶜ ∧
      (∀ x, conductivityFlux (fun y => u y+du y) T x = conductivityFlux u A x+dF x) := by
  obtain ⟨du, dF, hus, huc, hUs, hFs, hFc, hFS, hpair, heq, hoff⟩ :=
    assemble_compatible_replacements μ O hO hd u A R
  have hB (i : I) : ContinuousOn (R i).tensor (O i) :=
    Topology.IsInducing.subtypeVal.continuousOn_iff.mpr (R i).smooth_tensor.continuousOn
  obtain ⟨T, hT, hTon, hToff⟩ := exists_measurable_disjoint_gluing O hO hd A hA
    (fun i => (R i).tensor) hB (A 0)
  refine ⟨du, dF, T, hus, huc, hUs, hFs, hFc, hFS, hpair, hT,
    fun i => ⟨(heq i).1, (heq i).2.1, hTon i⟩, hToff, ?_⟩
  intro x
  by_cases hx : x ∈ ⋃ i, O i
  · obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    simp only [conductivityFlux, hTon i hxi, (heq i).2.2 x hxi, (heq i).2.1 hxi]
    exact (R i).constitutive x hxi
  · have hxu : x ∉ tsupport du := fun hu => hx (hUs hu)
    have hder : fderiv ℝ (fun y => u y+du y) x = fderiv ℝ u x := by
      apply Filter.EventuallyEq.fderiv_eq
      filter_upwards [(isClosed_tsupport du).isOpen_compl.mem_nhds hxu] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy, add_zero]
    simp only [conductivityFlux, hToff hx, hder, (hoff x hx).2, add_zero]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_RegularPatch
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3
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
open scoped Matrix.Norms.Elementwise

lemma TwoFieldRankRegular.congr {u v : Coord3 → Fin 2 → ℝ} {O : Set Coord3}
    (hO : IsOpen O) (h : TwoFieldRankRegular u O) (he : EqOn v u O) :
    TwoFieldRankRegular v O := by
  rcases h with h | h | ⟨κ,hκ⟩
  · left
    intro x hx
    rw [fderiv_eq_of_eqOn_open hO he hx]
    exact h x hx
  · right; left
    obtain ⟨w,l,κ,hw,hl,hwd,hrel⟩ := h
    exact ⟨w,l,κ,hw,hl,hwd,fun x hx j => by rw [he hx]; exact hrel x hx j⟩
  · exact Or.inr (Or.inr ⟨κ,fun x hx => (he hx).trans (hκ x hx)⟩)

lemma RegularPatch.mono {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    {O W : Set Coord3} (h : RegularPatch u A O) (hW : IsOpen W) (hWO : W ⊆ O) :
    RegularPatch u A W :=
  ⟨hW,h.2.1.mono hWO,h.2.2.1.mono hWO,h.2.2.2.mono hWO⟩

lemma RegularPatch.congr {u v : Coord3 → Fin 2 → ℝ} {A B : Coord3 → Symmetric3}
    {O : Set Coord3} (h : RegularPatch u A O) (hu : EqOn v u O) (hA : EqOn B A O) :
    RegularPatch v B O := by
  exact ⟨h.1,h.2.1.congr hu,h.2.2.1.congr (fun x hx => congrArg Subtype.val (hA hx)),
    h.2.2.2.congr h.1 hu⟩

lemma isOpen_regularRegion (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3)
    (U : Set Coord3) : IsOpen (regularRegion u A U) := by
  exact isOpen_iUnion (fun O => isOpen_iUnion (fun _ => isOpen_iUnion (fun h => h.1)))

lemma regularRegion_subset (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3)
    (U : Set Coord3) : regularRegion u A U ⊆ U := by
  intro x hx
  obtain ⟨O,hx⟩ := mem_iUnion.mp hx
  obtain ⟨hOU,hx⟩ := mem_iUnion.mp hx
  obtain ⟨_,hx⟩ := mem_iUnion.mp hx
  exact hOU hx

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_OpenRegularTensorTarget
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3
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

lemma isOpen_regular_tensor_target (u : Coord3 → Fin 2 → ℝ)
    (A : Coord3 → Symmetric3) (U : Set Coord3) {T : Set Symmetric3} (hT : IsOpen T) :
    IsOpen (regularRegion u A U ∩ A ⁻¹' T) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨O,hOU,hO,hxO⟩ := mem_regularRegion_iff.mp hx.1
  have hAc : ContinuousAt A x := Topology.IsInducing.subtypeVal.continuousAt_iff.mpr
    (hO.2.2.1.continuousOn.continuousAt (hO.1.mem_nhds hxO))
  exact Filter.inter_mem ((isOpen_regularRegion u A U).mem_nhds hx.1)
    (hAc.preimage_mem_nhds (hT.mem_nhds hx.2))

theorem finite_regular_depth_reduction
    (μ : Measure Coord3) [μ.IsAddHaarMeasure] [Measure.InnerRegularCompactLTTop μ]
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3)
    {U : Set Coord3} (hUb : Bornology.IsBounded U)
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    {a b : ℝ} (ha : 0 < a) {T : Set DiagonalTriple}
    (hT : IsOpen T) (hsub : ∀ d ∈ T, IsFiniteLaminate a b d)
    (hperm : ∀ d ∈ T, ∀ e : Equiv.Perm (Fin 3), d ∘ e ∈ T)
    {n : ℕ} (hsc : (spectralExtension (depthClass T n)).Nonempty)
    {G : Set Coord3} (hGm : MeasurableSet G)
    (hG : G ⊆ regularRegion u A U ∩ A ⁻¹' spectralExtension (depthClass T (n+1)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (O : Fin N → Set Coord3) (R : ∀ i, CompactCompatibleReplacement μ (O i) u A),
      (∀ i, IsOpen (O i) ∧ IsCompact (closure (O i)) ∧ closure (O i) ⊆ U ∧ μ (frontier (O i)) = 0) ∧
      Pairwise (fun i j => Disjoint (O i) (O j)) ∧
      (∀ i, RegularPatch (fun x => u x+(R i).du x) (R i).tensor (O i)) ∧
      (∀ i x, x ∈ O i → (R i).tensor x ∈ matrixFiniteLaminate a b) ∧
      μ (G \ ⋃ i, O i) +
        ∑ i, μ {x | x ∈ O i ∧ (R i).tensor x ∉ spectralExtension (depthClass T n)}
          ≤ ENNReal.ofReal ε := by
  classical
  have hlocal : ∀ p : G, ∃ W : Set Coord3,
      IsOpen W ∧ p.val ∈ W ∧ closure W ⊆ U ∧ IsCompact (closure W) ∧
      ∀ O : Set Coord3, IsOpen O → O ⊆ W → ∀ δ : ℝ, 0 < δ →
      ∃ R : CompactCompatibleReplacement μ O u A,
        RegularPatch (fun x => u x+R.du x) R.tensor O ∧
        (∀ x ∈ O, R.tensor x ∈ matrixFiniteLaminate a b) ∧
        μ {x | x ∈ O ∧ R.tensor x ∉ spectralExtension (depthClass T n)} ≤ ENNReal.ofReal δ := by
    intro p
    obtain ⟨V,hVU,hV,hpV⟩ := mem_regularRegion_iff.mp (hG p.property).1
    obtain ⟨W,hW,hpW,hWV,hWc,hop⟩ := exists_compact_depth_reduction_regular μ u A
      hV.1 (hUb.subset hVU) hV.2.1 hV.2.2.1
      (fun j ψ hs hc ht => hdiv j ψ hs hc (ht.trans hVU)) hV.2.2.2
      ha hT hsub hperm hpV (hG p.property).2 hsc
    refine ⟨W,hW,hpW,hWV.trans hVU,hWc,?_⟩
    intro O hO hOW δ hδ
    obtain ⟨R,hr,hRG,hbad⟩ := hop O hO hOW δ hδ
    exact ⟨R,⟨hO,(hV.2.1.mono (hOW.trans (subset_closure.trans hWV))).add R.smooth_du.contDiffOn,
      R.smooth_tensor,hr⟩,hRG,hbad⟩
  choose W hWo hpW hWU hWc hop using hlocal
  have hμG : μ G ≠ ∞ := (hUb.subset (hG.trans (inter_subset_left.trans (regularRegion_subset u A U)))).measure_lt_top.ne
  have hcover : G ⊆ ⋃ p : G, W p := fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,hpW ⟨x,hx⟩⟩
  obtain ⟨N,O,tag,hO,hd,hmiss⟩ := finite_disjoint_localization_null μ hGm hμG W hWo hcover
    (ENNReal.ofReal_pos.mpr (by linarith : 0 < ε/2)).ne'
  let δ : ℝ := (ε/2) / (N+1)
  have hδ : 0 < δ := div_pos (by linarith) (by positivity)
  choose R hR hRG hbad using fun i => hop (tag i) (O i) (hO i).1
    (subset_closure.trans (hO i).2.2.1) δ hδ
  refine ⟨N,O,R,fun i => ⟨(hO i).1,(hO i).2.1,(hO i).2.2.1.trans (subset_closure.trans (hWU (tag i))),
    (hO i).2.2.2⟩,hd,hR,hRG,?_⟩
  have hsum : (∑ i : Fin N, μ {x | x ∈ O i ∧ (R i).tensor x ∉ spectralExtension (depthClass T n)})
      ≤ ENNReal.ofReal (ε/2) := by
    calc
      _ ≤ ∑ _i : Fin N, ENNReal.ofReal δ := Finset.sum_le_sum (fun i _ => hbad i)
      _ = ENNReal.ofReal ((N : ℝ) * δ) := by simp [ENNReal.ofReal_mul]
      _ ≤ ENNReal.ofReal (ε/2) := ENNReal.ofReal_le_ofReal (by
        dsimp [δ]
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (by positivity : (0:ℝ) < N+1)).mpr
        nlinarith)
  calc
    _ ≤ ENNReal.ofReal (ε/2) + ENNReal.ofReal (ε/2) := add_le_add hmiss.le hsum
    _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; congr 1; ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_RegularRegionFiniteGluing
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3
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
open scoped Matrix.Norms.Elementwise

lemma regularRegion_finite_gluing
    {I : Type*} [Fintype I]
    {u v : Coord3 → Fin 2 → ℝ} {A B : Coord3 → Symmetric3} {U : Set Coord3}
    (O : I → Set Coord3) (hOU : ∀ i, O i ⊆ U)
    (hnew : ∀ i, RegularPatch v B (O i))
    (hu : EqOn v u (⋃ i, O i)ᶜ) (hA : EqOn B A (⋃ i, O i)ᶜ) :
    regularRegion u A U \ (⋃ i, frontier (O i)) ⊆ regularRegion v B U := by
  intro x hx
  by_cases hxi : x ∈ ⋃ i, O i
  · obtain ⟨i,hi⟩ := mem_iUnion.mp hxi
    exact mem_regularRegion_iff.mpr ⟨O i,hOU i,hnew i,hi⟩
  · obtain ⟨V,hVU,hV,hxV⟩ := mem_regularRegion_iff.mp hx.1
    let W := V \ ⋃ i, closure (O i)
    have hclosed : IsClosed (⋃ i, closure (O i)) := isClosed_iUnion_of_finite (fun _ => isClosed_closure)
    have hW : IsOpen W := hV.1.sdiff hclosed
    have hxW : x ∈ W := by
      refine ⟨hxV,?_⟩
      intro hxc
      obtain ⟨i,hi⟩ := mem_iUnion.mp hxc
      apply hx.2
      refine mem_iUnion.mpr ⟨i,?_⟩
      rw [frontier, (hnew i).1.interior_eq]
      exact ⟨hi,fun hh => hxi (mem_iUnion.mpr ⟨i,hh⟩)⟩
    have hWoff : W ⊆ (⋃ i, O i)ᶜ := by
      intro y hy hi
      apply hy.2
      obtain ⟨i,hyi⟩ := mem_iUnion.mp hi
      exact mem_iUnion.mpr ⟨i,subset_closure hyi⟩
    exact mem_regularRegion_iff.mpr ⟨W,sdiff_subset.trans hVU,
      (hV.mono hW sdiff_subset).congr (hu.mono hWoff) (hA.mono hWoff),hxW⟩

lemma regularRegion_finite_gluing_ae
    (μ : Measure Coord3) {I : Type*} [Fintype I]
    {u v : Coord3 → Fin 2 → ℝ} {A B : Coord3 → Symmetric3} {U : Set Coord3}
    (hold : μ (U \ regularRegion u A U) = 0)
    (O : I → Set Coord3) (hOU : ∀ i, O i ⊆ U)
    (hnew : ∀ i, RegularPatch v B (O i))
    (hu : EqOn v u (⋃ i, O i)ᶜ) (hA : EqOn B A (⋃ i, O i)ᶜ)
    (hnull : ∀ i, μ (frontier (O i)) = 0) :
    μ (U \ regularRegion v B U) = 0 := by
  have hs : U \ regularRegion v B U ⊆
      (U \ regularRegion u A U) ∪ (⋃ i, frontier (O i)) := by
    intro x hx
    by_cases hr : x ∈ regularRegion u A U
    · right
      by_contra hf
      exact hx.2 (regularRegion_finite_gluing O hOU hnew hu hA ⟨hr,hf⟩)
    · exact Or.inl ⟨hx.1,hr⟩
  exact measure_mono_null hs (measure_union_null hold (measure_iUnion_null hnull))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CompactGlobalUpdate
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

theorem global_regular_depth_reduction
    (μ : Measure Coord3) [μ.IsAddHaarMeasure] [Measure.InnerRegularCompactLTTop μ]
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3) (hAm : Measurable A)
    {U : Set Coord3} (hUb : Bornology.IsBounded U)
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    (hreg : μ (U \ regularRegion u A U) = 0)
    {a b : ℝ} (ha : 0 < a) {T : Set DiagonalTriple}
    (hT : IsOpen T) (hsub : ∀ d ∈ T, IsFiniteLaminate a b d)
    (hperm : ∀ d ∈ T, ∀ e : Equiv.Perm (Fin 3), d ∘ e ∈ T)
    (hgraph : ∀ᵐ x ∂μ, x ∈ U → A x ∈ matrixFiniteLaminate a b)
    {n : ℕ} (hsc : (spectralExtension (depthClass T n)).Nonempty)
    {G : Set Coord3} (hGm : MeasurableSet G)
    (hG : G ⊆ regularRegion u A U ∩ A ⁻¹' spectralExtension (depthClass T (n+1)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : CompactGlobalUpdate μ U u A,
      μ (U \ regularRegion (fun x => u x+R.du x) R.tensor U) = 0 ∧
      (∀ᵐ x ∂μ, x ∈ U → R.tensor x ∈ matrixFiniteLaminate a b) ∧
      μ (U \ R.tensor ⁻¹' spectralExtension (depthClass T n)) ≤ μ (U \ G) + ENNReal.ofReal ε := by
  classical
  obtain ⟨N,O,P,hO,hd,hP,hPG,hloss⟩ := finite_regular_depth_reduction μ u A hUb hdiv
    ha hT hsub hperm hsc hGm hG hε
  obtain ⟨du,dF,B,hus,huc,hUs,hFs,hFc,hFS,hpair,hB,heq,hoff,hconst⟩ :=
    assemble_compatible_tensors μ O (fun i => (hO i).1) hd u A hAm P
  have hOU : (⋃ i, O i) ⊆ U := iUnion_subset (fun i => subset_closure.trans (hO i).2.2.1)
  let R : CompactGlobalUpdate μ U u A := ⟨du,dF,B,hus,huc,hUs.trans hOU,
    hFs,hFc,hFS.trans hOU,hpair,hB,hconst⟩
  have hnew : ∀ i, RegularPatch (fun x => u x+du x) B (O i) := by
    intro i
    exact (hP i).congr (fun x hx => by rw [(heq i).1 hx]) (heq i).2.2
  have huo : EqOn (fun x => u x+du x) u (⋃ i, O i)ᶜ := by
    intro x hx
    change u x+du x = u x
    rw [image_eq_zero_of_notMem_tsupport (fun hs => hx (hUs hs)),add_zero]
  refine ⟨R,regularRegion_finite_gluing_ae μ hreg O
    (fun i => subset_closure.trans (hO i).2.2.1) hnew huo hoff (fun i => (hO i).2.2.2),?_,?_⟩
  · filter_upwards [hgraph] with x hx
    intro hxU
    change B x ∈ matrixFiniteLaminate a b
    by_cases hxin : x ∈ ⋃ i, O i
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hxin
      rw [(heq i).2.2 hi]
      exact hPG i x hi
    · rw [hoff hxin]
      exact hx hxU
  · let bad : Fin N → Set Coord3 := fun i =>
      {x | x ∈ O i ∧ (P i).tensor x ∉ spectralExtension (depthClass T n)}
    have hset : U \ B ⁻¹' spectralExtension (depthClass T n) ⊆
        (U \ G) ∪ ((G \ ⋃ i, O i) ∪ (⋃ i, bad i)) := by
      intro x hx
      by_cases hxG : x ∈ G
      · right
        by_cases hxO : x ∈ ⋃ i, O i
        · right
          obtain ⟨i,hi⟩ := mem_iUnion.mp hxO
          exact mem_iUnion.mpr ⟨i,hi,by rw [← (heq i).2.2 hi]; exact hx.2⟩
        · exact Or.inl ⟨hxG,hxO⟩
      · exact Or.inl ⟨hx.1,hxG⟩
    calc
      μ (U \ R.tensor ⁻¹' spectralExtension (depthClass T n)) ≤
          μ (U \ G) + (μ (G \ ⋃ i, O i) + μ (⋃ i, bad i)) :=
        (measure_mono hset).trans ((measure_union_le _ _).trans
          (add_le_add le_rfl (measure_union_le _ _)))
      _ ≤ μ (U \ G) + (μ (G \ ⋃ i, O i) + ∑ i, μ (bad i)) :=
        add_le_add le_rfl (add_le_add le_rfl (measure_iUnion_fintype_le μ bad))
      _ ≤ μ (U \ G) + ENNReal.ofReal ε := add_le_add le_rfl hloss

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_MeasurableDisjointGluingMeasurable
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
open scoped Matrix.Norms.Elementwise

lemma exists_measurable_disjoint_gluing_measurable
    {X Y I : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Fintype I] (O : I → Set X) (hO : ∀ i, MeasurableSet (O i))
    (hd : Pairwise (fun i j => Disjoint (O i) (O j)))
    (A : X → Y) (hA : Measurable A) (B : I → X → Y)
    (hB : ∀ i, Measurable (B i)) :
    ∃ T : X → Y, Measurable T ∧ (∀ i, EqOn T (B i) (O i)) ∧
      EqOn T A (⋃ i, O i)ᶜ := by
  classical
  let P : Option I → Set X := fun i => match i with
    | none => (⋃ i, O i)ᶜ
    | some j => O j
  let G : Option I → X → Y := fun i => match i with
    | none => A
    | some j => B j
  have hP : ∀ i, MeasurableSet (P i) := by
    rintro (_ | i)
    · exact (MeasurableSet.iUnion hO).compl
    · exact hO i
  have hG : ∀ i, Measurable (G i) := by
    rintro (_ | i)
    · exact hA
    · exact hB i
  obtain ⟨T,hT,hTP⟩ := exists_measurable_piecewise P hP G hG (by
    rintro (_ | i) (_ | j) hij x ⟨hxi,hxj⟩
    · exact (hij rfl).elim
    · exact (hxi (mem_iUnion.mpr ⟨j,hxj⟩)).elim
    · exact (hxj (mem_iUnion.mpr ⟨i,hxi⟩)).elim
    · exact (Set.disjoint_left.mp (hd (fun e => hij (congrArg some e))) hxi hxj).elim)
  exact ⟨T,hT,fun i => hTP (some i),hTP none⟩

theorem assemble_global_updates
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {I : Type*} [Fintype I] [DecidableEq I]
    {U : Set Coord3} (O : I → Set Coord3) (hO : ∀ i, IsOpen (O i))
    (hOU : ∀ i, O i ⊆ U) (hd : Pairwise (fun i j => Disjoint (O i) (O j)))
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3) (hA : Measurable A)
    (R : ∀ i, CompactGlobalUpdate μ (O i) u A) :
    ∃ S : CompactGlobalUpdate μ U u A,
      (S.du = fun x => ∑ i, (R i).du x) ∧
      (S.dF = fun x => ∑ i, (R i).dF x) ∧
      (∀ i, EqOn S.du (R i).du (O i) ∧ EqOn S.dF (R i).dF (O i) ∧
        EqOn S.tensor (R i).tensor (O i)) ∧ EqOn S.tensor A (⋃ i, O i)ᶜ := by
  let du : Coord3 → Fin 2 → ℝ := fun x => ∑ i, (R i).du x
  let dF : Coord3 → Matrix (Fin 3) (Fin 2) ℝ := fun x => ∑ i, (R i).dF x
  have heu : ∀ i, EqOn du (R i).du (O i) :=
    supported_sum_eq_on O hd (fun i => (R i).du) (fun i => (R i).support_du)
  have heF : ∀ i, EqOn dF (R i).dF (O i) :=
    supported_sum_eq_on O hd (fun i => (R i).dF) (fun i => (R i).support_dF)
  have hus : tsupport du ⊆ ⋃ i, O i :=
    (tsupport_finite_sum_subset _).trans (iUnion_mono (fun i => (R i).support_du))
  have hFs : tsupport dF ⊆ ⋃ i, O i :=
    (tsupport_finite_sum_subset _).trans (iUnion_mono (fun i => (R i).support_dF))
  obtain ⟨T,hT,hTon,hToff⟩ := exists_measurable_disjoint_gluing_measurable O
    (fun i => (hO i).measurableSet) hd A hA (fun i => (R i).tensor) (fun i => (R i).measurable_tensor)
  let S : CompactGlobalUpdate μ U u A := {
    du := du
    dF := dF
    tensor := T
    smooth_du := ContDiff.sum (fun i _ => (R i).smooth_du)
    compact_du := by
      simpa only [du, ← Finset.sum_apply] using
        (HasCompactSupport.finset_sum (s := Finset.univ) (fun i _ => (R i).compact_du))
    support_du := hus.trans (iUnion_subset hOU)
    smooth_dF := ContDiff.sum (fun i _ => (R i).smooth_dF)
    compact_dF := by
      simpa only [dF, ← Finset.sum_apply] using
        (HasCompactSupport.finset_sum (s := Finset.univ) (fun i _ => (R i).compact_dF))
    support_dF := hFs.trans (iUnion_subset hOU)
    cauchy_dF := finite_sum_cauchy_preserving μ (fun i => (R i).dF)
      (fun i => (R i).smooth_dF) (fun i => (R i).compact_dF) (fun i => (R i).cauchy_dF)
    measurable_tensor := hT
    constitutive := by
      intro x
      by_cases hx : x ∈ ⋃ i, O i
      · obtain ⟨i,hxi⟩ := mem_iUnion.mp hx
        have he : fderiv ℝ (fun y => u y+du y) x = fderiv ℝ (fun y => u y+(R i).du y) x := by
          apply Filter.EventuallyEq.fderiv_eq
          filter_upwards [(hO i).mem_nhds hxi] with y hy
          rw [heu i hy]
        simp only [conductivityFlux,hTon i hxi,he,heF i hxi]
        exact (R i).constitutive x
      · have hxu : x ∉ tsupport du := fun hu => hx (hus hu)
        have hder : fderiv ℝ (fun y => u y+du y) x = fderiv ℝ u x := by
          apply Filter.EventuallyEq.fderiv_eq
          filter_upwards [(isClosed_tsupport du).isOpen_compl.mem_nhds hxu] with y hy
          rw [image_eq_zero_of_notMem_tsupport hy,add_zero]
        simp only [conductivityFlux,hToff hx,hder,image_eq_zero_of_notMem_tsupport (fun hy => hx (hFs hy)),add_zero]
  }
  exact ⟨S,rfl,rfl,fun i => ⟨heu i,heF i,hTon i⟩,hToff⟩

end ScalarConductivity

namespace ScalarConductivity
open Set MeasureTheory Metric
open scoped ENNReal

theorem finite_disjoint_localization_fine
    {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] [Measure.InnerRegularCompactLTTop μ]
    {A : Set E} (hA : MeasurableSet A) (hμA : μ A ≠ ∞)
    (U : I → Set E) (hU : ∀ i, IsOpen (U i)) (hc : A ⊆ ⋃ i, U i)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (n : ℕ) (Q : Fin n → Set E) (tag : Fin n → I) (center : Fin n → E),
      (∀ i, IsOpen (Q i) ∧ IsCompact (closure (Q i)) ∧ closure (Q i) ⊆ U (tag i) ∧
        μ (frontier (Q i)) = 0 ∧ closure (Q i) ⊆ Metric.ball (center i) δ) ∧
      Pairwise (fun i j => Disjoint (Q i) (Q j)) ∧ μ (A \ ⋃ i, Q i) < ε := by
  let V : I × E → Set E := fun p => U p.1 ∩ Metric.ball p.2 δ
  have hV : ∀ p, IsOpen (V p) := fun p => (hU p.1).inter isOpen_ball
  have hcover : A ⊆ ⋃ p, V p := by
    intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hc hx)
    exact mem_iUnion.mpr ⟨(i,x),hi,mem_ball_self hδ⟩
  obtain ⟨n,Q,tag,hQ,hd,hmiss⟩ := finite_disjoint_localization_null μ hA hμA V hV hcover hε
  exact ⟨n,Q,fun i => (tag i).1,fun i => (tag i).2,
    fun i => ⟨(hQ i).1,(hQ i).2.1,(hQ i).2.2.1.trans inter_subset_left,
      (hQ i).2.2.2,(hQ i).2.2.1.trans inter_subset_right⟩,hd,hmiss⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_SmoothFluxIntegrable
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
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_SpectralExtensionMono
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3
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

lemma spectralExtension_mono {T S : Set DiagonalTriple} (h : T ⊆ S) :
    spectralExtension T ⊆ spectralExtension S := by
  rintro A ⟨Q,hQ,d,hd,he⟩
  exact ⟨Q,hQ,d,h hd,he⟩

lemma spectral_depth_mono (T : Set DiagonalTriple) :
    Monotone (fun n => spectralExtension (depthClass T n)) := by
  intro m n h
  exact spectralExtension_mono (depthClass_mono T h)

lemma matrixFiniteLaminate_mem_some_depth {a b : ℝ} {T : Set DiagonalTriple}
    (hT : ∀ s, a < s → s < b → (fun _ => s) ∈ T)
    {A : Symmetric3} (hA : A ∈ matrixFiniteLaminate a b) :
    ∃ n, A ∈ spectralExtension (depthClass T n) := by
  obtain ⟨Q,hQ,d,hd,he⟩ := hA
  obtain ⟨n,hn⟩ := hd.mem_some_depth hT
  exact ⟨n,Q,hQ,d,hn,he⟩

attribute [local instance] OAI.ScalarConductivity.spectralExtensionMonoMeasurableSpaceMat3
local instance spectralExtensionMonoBorelSpaceMat3 : BorelSpace Mat3 :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))

lemma exists_finite_depth_loss
    (μ : Measure Coord3) (A : Coord3 → Symmetric3) (hA : Measurable A)
    {U : Set Coord3} (hU : MeasurableSet U) (hμU : μ U ≠ ∞)
    {a b : ℝ} (ha : 0 < a) {T : Set DiagonalTriple}
    (hT : IsOpen T) (hsub : ∀ d ∈ T, IsFiniteLaminate a b d)
    (hperm : ∀ d ∈ T, ∀ e : Equiv.Perm (Fin 3), d ∘ e ∈ T)
    (hscalar : ∀ s, a < s → s < b → (fun _ => s) ∈ T)
    (hgraph : ∀ᵐ x ∂μ, x ∈ U → A x ∈ matrixFiniteLaminate a b)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ n, μ (U \ A ⁻¹' spectralExtension (depthClass T n)) < ε := by
  let B : ℕ → Set Coord3 := fun n => U \ A ⁻¹' spectralExtension (depthClass T n)
  have hB : ∀ n, MeasurableSet (B n) := fun n => hU.diff
    ((isOpen_spectralExtension (isOpen_depthClass ha hT hsub n) (depthClass_permute hperm n)).measurableSet.preimage hA)
  have hmono : Antitone B := fun _ _ h => sdiff_subset_sdiff_right
    (preimage_mono (spectral_depth_mono T h))
  have hnull : μ (⋂ n, B n) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hgraph] with x hx hin
    have h0 := mem_iInter.mp hin 0
    obtain ⟨n,hn⟩ := matrixFiniteLaminate_mem_some_depth hscalar (hx h0.1)
    exact (mem_iInter.mp hin n).2 hn
  have ht : Tendsto (fun n => μ (B n)) atTop (𝓝 0) := by
    rw [← hnull]
    exact tendsto_measure_iInter_atTop (fun n => (hB n).nullMeasurableSet) hmono
      ⟨0, ((measure_mono sdiff_subset).trans_lt (lt_top_iff_ne_top.mpr hμU)).ne⟩
  exact (ht.eventually (gt_mem_nhds hε)).exists

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_Refl
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

lemma spectral_depth_nonempty {T : Set DiagonalTriple}
    (hT : (spectralExtension T).Nonempty) (n : ℕ) :
    (spectralExtension (depthClass T n)).Nonempty := by
  obtain ⟨A,hA⟩ := hT
  exact ⟨A,spectral_depth_mono T (Nat.zero_le n) hA⟩

theorem global_finite_depth_iteration
    (μ : Measure Coord3) [μ.IsAddHaarMeasure] [Measure.InnerRegularCompactLTTop μ]
    {a b : ℝ} (ha : 0 < a) {T : Set DiagonalTriple}
    (hT : IsOpen T) (hsub : ∀ d ∈ T, IsFiniteLaminate a b d)
    (hperm : ∀ d ∈ T, ∀ e : Equiv.Perm (Fin 3), d ∘ e ∈ T)
    (hsc : (spectralExtension T).Nonempty)
    {U : Set Coord3} (hUb : Bornology.IsBounded U) (n : ℕ)
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3) (hAm : Measurable A)
    (hint : SmoothFluxIntegrable μ U (conductivityFlux u A))
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    (hreg : μ (U \ regularRegion u A U) = 0)
    (hgraph : ∀ᵐ x ∂μ, x ∈ U → A x ∈ matrixFiniteLaminate a b)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : CompactGlobalUpdate μ U u A,
      μ (U \ regularRegion (fun x => u x+R.du x) R.tensor U) = 0 ∧
      (∀ᵐ x ∂μ, x ∈ U → R.tensor x ∈ matrixFiniteLaminate a b) ∧
      μ (U \ R.tensor ⁻¹' spectralExtension T) ≤
        μ (U \ A ⁻¹' spectralExtension (depthClass T n)) + ENNReal.ofReal ε := by
  induction n generalizing u A ε with
  | zero =>
    refine ⟨CompactGlobalUpdate.refl μ U u A hAm,?_,hgraph,?_⟩
    · simpa only [CompactGlobalUpdate.refl,Pi.zero_apply,add_zero] using hreg
    · change μ (U \ A ⁻¹' spectralExtension T) ≤ μ (U \ A ⁻¹' spectralExtension T) + ENNReal.ofReal ε
      exact le_add_right le_rfl
  | succ n ih =>
    let G := regularRegion u A U ∩ A ⁻¹' spectralExtension (depthClass T (n+1))
    have hGm : MeasurableSet G := (isOpen_regular_tensor_target u A U
      (isOpen_spectralExtension (isOpen_depthClass ha hT hsub (n+1)) (depthClass_permute hperm (n+1)))).measurableSet
    obtain ⟨R,hRreg,hRG,hRloss⟩ := global_regular_depth_reduction μ u A hAm hUb hdiv hreg
      ha hT hsub hperm hgraph (spectral_depth_nonempty hsc n) hGm (Subset.rfl) (by linarith : 0 < ε/2)
    obtain ⟨hRint,hRdiv⟩ := R.preserves_harmonic μ hint hdiv
    obtain ⟨S,hSreg,hSG,hSloss⟩ := ih (fun x => u x+R.du x) R.tensor R.measurable_tensor
      hRint hRdiv hRreg hRG (by linarith : 0 < ε/2)
    refine ⟨R.trans μ S,?_,hSG,?_⟩
    · simpa only [CompactGlobalUpdate.trans,Pi.add_apply,← add_assoc] using hSreg
    · have hGbad : μ (U \ G) ≤ μ (U \ A ⁻¹' spectralExtension (depthClass T (n+1))) := by
        have hs : U \ G ⊆ (U \ regularRegion u A U) ∪
            (U \ A ⁻¹' spectralExtension (depthClass T (n+1))) := by
          intro x hx
          by_cases hr : x ∈ regularRegion u A U
          · exact Or.inr ⟨hx.1,fun ht => hx.2 ⟨hr,ht⟩⟩
          · exact Or.inl ⟨hx.1,hr⟩
        simpa only [hreg,zero_add] using (measure_mono (μ := μ) hs).trans (measure_union_le _ _)
      calc
        μ (U \ (R.trans μ S).tensor ⁻¹' spectralExtension T) ≤
            μ (U \ R.tensor ⁻¹' spectralExtension (depthClass T n)) + ENNReal.ofReal (ε/2) := hSloss
        _ ≤ (μ (U \ G) + ENNReal.ofReal (ε/2)) + ENNReal.ofReal (ε/2) := add_le_add hRloss le_rfl
        _ ≤ (μ (U \ A ⁻¹' spectralExtension (depthClass T (n+1))) + ENNReal.ofReal (ε/2)) + ENNReal.ofReal (ε/2) :=
          add_le_add (add_le_add hGbad le_rfl) le_rfl
        _ = μ (U \ A ⁻¹' spectralExtension (depthClass T (n+1))) + ENNReal.ofReal ε := by
          rw [add_assoc,← ENNReal.ofReal_add (by linarith) (by linarith)]
          congr 2
          ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_SpectralExtensionNonemptyNonempty
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

lemma spectralExtension_nonempty_of_nonempty {T : Set DiagonalTriple} (hT : T.Nonempty) :
    (spectralExtension T).Nonempty := by
  obtain ⟨d,hd⟩ := hT
  have hQ : (1 : Mat3) ∈ orthogonalFrames := by simp [orthogonalFrames]
  exact ⟨conjugateDiagonal 1 d,conjugateDiagonal_spectral hQ hd⟩

attribute [local instance] OAI.ScalarConductivity.spectralExtensionNonemptyMeasurableSpaceMat3
local instance spectralExtensionNonemptyBorelSpaceMat3 : BorelSpace Mat3 :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))

theorem global_scalar_tensor_approximation
    (μ : Measure Coord3) [μ.IsAddHaarMeasure] [Measure.InnerRegularCompactLTTop μ]
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {U : Set Coord3} (hUm : MeasurableSet U) (hUb : Bornology.IsBounded U)
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3) (hAm : Measurable A)
    (hint : SmoothFluxIntegrable μ U (conductivityFlux u A))
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    (hreg : μ (U \ regularRegion u A U) = 0)
    (hgraph : ∀ᵐ x ∂μ, x ∈ U → A x ∈ matrixFiniteLaminate a b)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ R : CompactGlobalUpdate μ U u A,
      μ (U \ regularRegion (fun x => u x+R.du x) R.tensor U) = 0 ∧
      (∀ᵐ x ∂μ, x ∈ U → R.tensor x ∈ matrixFiniteLaminate a b) ∧
      μ (U \ R.tensor ⁻¹' spectralExtension (scalarNeighbourhood a b η)) ≤ ENNReal.ofReal ε := by
  let T := scalarNeighbourhood a b η
  have hTo : IsOpen T := isOpen_scalarNeighbourhood ha
  have hsub : ∀ d ∈ T, IsFiniteLaminate a b d := fun _ hd => hd.1
  have hperm : ∀ d ∈ T, ∀ e : Equiv.Perm (Fin 3), d ∘ e ∈ T := fun _ hd e => scalarNeighbourhood_permute hd e
  have hscalar : ∀ s, a < s → s < b → (fun _ => s) ∈ T := fun _ hs ht => scalar_mem_scalarNeighbourhood hη hs ht
  have hsc : (spectralExtension T).Nonempty := spectralExtension_nonempty_of_nonempty
    ⟨fun _ => (a+b)/2,hscalar _ (by linarith) (by linarith)⟩
  have hAmSubtype : @Measurable Coord3 Symmetric3 _ Subtype.instMeasurableSpace A := by
    change @Measurable Coord3 Symmetric3 _ (borel Symmetric3) A at hAm
    rw [borel_comap, ← BorelSpace.measurable_eq (α := Mat3)] at hAm
    exact hAm
  obtain ⟨n,hn⟩ := exists_finite_depth_loss μ A hAmSubtype hUm hUb.measure_lt_top.ne ha hTo hsub
    hperm hscalar hgraph (ENNReal.ofReal_pos.mpr (by linarith : 0 < ε/2))
  obtain ⟨R,hRreg,hRG,hRloss⟩ := global_finite_depth_iteration μ ha hTo hsub hperm hsc hUb n
    u A hAm hint hdiv hreg hgraph (by linarith : 0 < ε/2)
  refine ⟨R,hRreg,hRG,hRloss.trans ?_⟩
  calc
    _ ≤ ENNReal.ofReal (ε/2) + ENNReal.ofReal (ε/2) := add_le_add hn.le le_rfl
    _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; congr 1; ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_RegularRegionCongrSubset
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

lemma regularRegion_congr_subset {u v : Coord3 → Fin 2 → ℝ}
    {A B : Coord3 → Symmetric3} {O U : Set Coord3} (hOU : O ⊆ U)
    (hu : EqOn v u O) (hA : EqOn B A O) :
    regularRegion u A O ⊆ regularRegion v B U := by
  intro x hx
  obtain ⟨V,hVO,hV,hxV⟩ := mem_regularRegion_iff.mp hx
  exact mem_regularRegion_iff.mpr ⟨V,hVO.trans hOU,hV.congr (hu.mono hVO) (hA.mono hVO),hxV⟩

lemma regularRegion_piecewise_ae
    (μ : Measure Coord3) {I : Type*} [Fintype I]
    {u v : Coord3 → Fin 2 → ℝ} {A B : Coord3 → Symmetric3} {U : Set Coord3}
    (O : I → Set Coord3) (hO : ∀ i, IsOpen (O i)) (hOU : ∀ i, O i ⊆ U)
    (old : μ (U \ regularRegion u A U) = 0)
    (localgood : ∀ i, μ (O i \ regularRegion v B (O i)) = 0)
    (hu : EqOn v u (⋃ i, O i)ᶜ) (hA : EqOn B A (⋃ i, O i)ᶜ)
    (hnull : ∀ i, μ (frontier (O i)) = 0) :
    μ (U \ regularRegion v B U) = 0 := by
  have hs : U \ regularRegion v B U ⊆ (U \ regularRegion u A U) ∪
      (⋃ i, O i \ regularRegion v B (O i)) ∪ (⋃ i, frontier (O i)) := by
    intro x hx
    by_cases hr : x ∈ regularRegion u A U
    · by_cases hi : x ∈ ⋃ i, O i
      · obtain ⟨i,hi⟩ := mem_iUnion.mp hi
        exact Or.inl (Or.inr (mem_iUnion.mpr ⟨i,hi,fun hh => hx.2
          (regularRegion_congr_subset (hOU i) (fun _ _ => rfl) (fun _ _ => rfl) hh)⟩))
      · by_cases hf : x ∈ ⋃ i, frontier (O i)
        · exact Or.inr hf
        · exfalso
          apply hx.2
          obtain ⟨V,hVU,hV,hxV⟩ := mem_regularRegion_iff.mp hr
          let W := V \ ⋃ i, closure (O i)
          have hW : IsOpen W := hV.1.sdiff (isClosed_iUnion_of_finite (fun _ => isClosed_closure))
          have hxW : x ∈ W := by
            refine ⟨hxV,?_⟩
            intro hh
            obtain ⟨i,hi'⟩ := mem_iUnion.mp hh
            apply hf
            refine mem_iUnion.mpr ⟨i,?_⟩
            rw [frontier,(hO i).interior_eq]
            exact ⟨hi',fun hh => hi (mem_iUnion.mpr ⟨i,hh⟩)⟩
          have hWoff : W ⊆ (⋃ i, O i)ᶜ := by
            intro y hy hh
            obtain ⟨i,hyi⟩ := mem_iUnion.mp hh
            exact hy.2 (mem_iUnion.mpr ⟨i,subset_closure hyi⟩)
          exact mem_regularRegion_iff.mpr ⟨W,sdiff_subset.trans hVU,
            (hV.mono hW sdiff_subset).congr (hu.mono hWoff) (hA.mono hWoff),hxW⟩
    · exact Or.inl (Or.inl ⟨hx.1,hr⟩)
  exact measure_mono_null hs (measure_union_null (measure_union_null old
    (measure_iUnion_null localgood)) (measure_iUnion_null hnull))

end ScalarConductivity

namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise ENNReal

lemma regularRegion_restrict_open {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    {U O : Set Coord3} (hO : IsOpen O) :
    O ∩ regularRegion u A U ⊆ regularRegion u A O := by
  intro x hx
  obtain ⟨V,hVU,hV,hxV⟩ := mem_regularRegion_iff.mp hx.2
  exact mem_regularRegion_iff.mpr ⟨V ∩ O,inter_subset_right,
    hV.mono (hV.1.inter hO) inter_subset_left,hxV,hx.1⟩

theorem fine_global_scalar_tensor_approximation_oai
    (μ : Measure Coord3) [μ.IsAddHaarMeasure] [Measure.InnerRegularCompactLTTop μ]
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {U : Set Coord3} (hUb : Bornology.IsBounded U)
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3) (hAm : Measurable A)
    (hint : SmoothFluxIntegrable μ U (conductivityFlux u A))
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    (hreg : μ (U \ regularRegion u A U) = 0)
    (hgraph : ∀ᵐ x ∂μ, x ∈ U → A x ∈ matrixFiniteLaminate a b)
    {η ε δ : ℝ} (hη : 0 < η) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ (N : ℕ) (O : Fin N → Set Coord3) (center : Fin N → Coord3)
      (R : ∀ i, CompactGlobalUpdate μ (O i) u A) (S : CompactGlobalUpdate μ U u A),
      (∀ i, IsOpen (O i) ∧ closure (O i) ⊆ U ∧ closure (O i) ⊆ Metric.ball (center i) δ) ∧
      Pairwise (fun i j => Disjoint (O i) (O j)) ∧
      S.du = (fun x => ∑ i, (R i).du x) ∧ S.dF = (fun x => ∑ i, (R i).dF x) ∧
      μ (U \ regularRegion (fun x => u x+S.du x) S.tensor U) = 0 ∧
      (∀ᵐ x ∂μ, x ∈ U → S.tensor x ∈ matrixFiniteLaminate a b) ∧
      μ (U \ S.tensor ⁻¹' spectralExtension (scalarNeighbourhood a b η)) ≤ ENNReal.ofReal ε := by
  classical
  let G := regularRegion u A U
  have hGo : IsOpen G := isOpen_regularRegion u A U
  have hGU : G ⊆ U := regularRegion_subset u A U
  obtain ⟨N,O,tag,center,hO,hd,hmiss⟩ := finite_disjoint_localization_fine μ hGo.measurableSet
    (hUb.subset hGU).measure_lt_top.ne (fun _ : Unit => G) (fun _ => hGo)
    (fun x hx => mem_iUnion.mpr ⟨(),hx⟩)
    (ENNReal.ofReal_pos.mpr (by linarith : 0 < ε/2)).ne' hδ
  have hOU : ∀ i, O i ⊆ U := fun i => subset_closure.trans ((hO i).2.2.1.trans hGU)
  have hOr : ∀ i, μ (O i \ regularRegion u A (O i)) = 0 := by
    intro i
    have hs : O i ⊆ regularRegion u A (O i) := fun x hx =>
      regularRegion_restrict_open (hO i).1 ⟨hx,(hO i).2.2.1 (subset_closure hx)⟩
    simp only [sdiff_eq_empty.mpr hs,measure_empty]
  let ρ : ℝ := (ε/2)/(N+1)
  have hρ : 0 < ρ := div_pos (by linarith) (by positivity)
  have hlocal : ∀ i, ∃ R : CompactGlobalUpdate μ (O i) u A,
      μ (O i \ regularRegion (fun x => u x+R.du x) R.tensor (O i)) = 0 ∧
      (∀ᵐ x ∂μ, x ∈ O i → R.tensor x ∈ matrixFiniteLaminate a b) ∧
      μ (O i \ R.tensor ⁻¹' spectralExtension (scalarNeighbourhood a b η)) ≤ ENNReal.ofReal ρ := by
    intro i
    apply global_scalar_tensor_approximation μ ha hab (hO i).1.measurableSet (hUb.subset (hOU i)) u A hAm
      (fun j ψ hs hc ht => hint j ψ hs hc (ht.trans (hOU i)))
      (fun j ψ hs hc ht => hdiv j ψ hs hc (ht.trans (hOU i))) (hOr i)
    · filter_upwards [hgraph] with x hx
      exact fun hi => hx (hOU i hi)
    · exact hη
    · exact hρ
  choose R hRreg hRG hRbad using hlocal
  obtain ⟨S,hsu,hsF,hS,hSoff⟩ := assemble_global_updates μ O (fun i => (hO i).1) hOU hd u A hAm R
  have hsuoff : EqOn (fun x => u x+S.du x) u (⋃ i, O i)ᶜ := by
    intro x hx
    change u x+S.du x = u x
    rw [hsu]
    change u x+(∑ i, (R i).du x) = u x
    rw [supported_sum_eq_zero_off O _ (fun i => (R i).support_du) hx,add_zero]
  have hregS : μ (U \ regularRegion (fun x => u x+S.du x) S.tensor U) = 0 := by
    apply regularRegion_piecewise_ae μ O (fun i => (hO i).1) hOU hreg _ hsuoff hSoff
      (fun i => (hO i).2.2.2.1)
    intro i
    apply measure_mono_null _ (hRreg i)
    exact sdiff_subset_sdiff_right (regularRegion_congr_subset Subset.rfl
      (fun x hx => by rw [(hS i).1 hx]) (hS i).2.2)
  refine ⟨N,O,center,R,S,fun i => ⟨(hO i).1,(hO i).2.2.1.trans hGU,(hO i).2.2.2.2⟩,
    hd,hsu,hsF,hregS,?_,?_⟩
  · have hRGall : ∀ᵐ x ∂μ, ∀ i, x ∈ O i → (R i).tensor x ∈ matrixFiniteLaminate a b :=
      (ae_all_iff).mpr hRG
    filter_upwards [hgraph,hRGall] with x hx hRx
    intro hxU
    by_cases hi : x ∈ ⋃ i, O i
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hi
      rw [(hS i).2.2 hi]
      exact hRx i hi
    · rw [hSoff hi]
      exact hx hxU
  · let T := spectralExtension (scalarNeighbourhood a b η)
    let bad : Fin N → Set Coord3 := fun i => O i \ (R i).tensor ⁻¹' T
    have hs : U \ S.tensor ⁻¹' T ⊆ (U \ G) ∪ ((G \ ⋃ i, O i) ∪ ⋃ i, bad i) := by
      intro x hx
      by_cases hxG : x ∈ G
      · right
        by_cases hxO : x ∈ ⋃ i, O i
        · right
          obtain ⟨i,hi⟩ := mem_iUnion.mp hxO
          exact mem_iUnion.mpr ⟨i,hi,fun ht => hx.2 (by change S.tensor x ∈ T; rw [(hS i).2.2 hi]; exact ht)⟩
        · exact Or.inl ⟨hxG,hxO⟩
      · exact Or.inl ⟨hx.1,hxG⟩
    have hsum : (∑ i : Fin N, μ (bad i)) ≤ ENNReal.ofReal (ε/2) := by
      calc
        _ ≤ ∑ _i : Fin N, ENNReal.ofReal ρ := Finset.sum_le_sum (fun i _ => hRbad i)
        _ = ENNReal.ofReal ((N : ℝ)*ρ) := by simp [ENNReal.ofReal_mul]
        _ ≤ ENNReal.ofReal (ε/2) := ENNReal.ofReal_le_ofReal (by
          dsimp [ρ]
          rw [← mul_div_assoc]
          apply (div_le_iff₀ (by positivity : (0:ℝ) < N+1)).mpr
          nlinarith)
    calc
      _ ≤ μ (U \ G) + (μ (G \ ⋃ i, O i) + ∑ i, μ (bad i)) :=
        (measure_mono (μ := μ) hs).trans ((measure_union_le _ _).trans
          (add_le_add le_rfl ((measure_union_le _ _).trans (add_le_add le_rfl (measure_iUnion_fintype_le μ bad)))))
      _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal (ε/2) := by
        rw [hreg,zero_add]
        exact add_le_add hmiss.le hsum
      _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
        congr 1
        ring

end ScalarConductivity

end

end OAI
end

theorem solution : type_of% @OAI.ScalarConductivity.fine_global_scalar_tensor_approximation_oai := @OAI.ScalarConductivity.fine_global_scalar_tensor_approximation_oai
