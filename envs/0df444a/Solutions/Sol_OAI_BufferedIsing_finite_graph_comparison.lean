-- Prove2me | solution 1 for OAI.BufferedIsing.finite_graph_comparison
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:08:03.988894+00:00
-- url     : https://prove2.me/submissions/0367e8c7-8871-490e-8714-889587514e81

-- Generated from openai/math@1581d4c lean/OAI/Probability/Ising/Main.lean:L71-L87
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.BufferedIsing.finite_graph_comparison.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_BufferedIsing_finite_graph_comparison) verbatim and is proved by it.
import Mathlib
import Definitions.Def_BufferedIsing
import Definitions.Def_OAI_Probability_Ising_Basic
import Definitions.Def_OAI_Probability_Ising_Colorings
import Definitions.Def_OAI_Probability_Ising_EdwardsSokal
import Definitions.Def_OAI_Probability_Ising_TwoSpin
import Definitions.Def_OAI_Probability_Ising_SpinCorrelation
import Definitions.Def_OAI_Probability_Ising_Marginals
import Definitions.Def_OAI_Probability_Ising_PinnedMarginal
import Definitions.Def_OAI_Probability_Ising_Covariance
import Definitions.Def_OAI_Probability_Ising_Contraction
import Definitions.Def_OAI_Probability_Ising_GibbsMeasure
import Definitions.Def_OAI_Probability_Ising_Interpolation
import Definitions.Def_OAI_Probability_Ising_FieldUpdate
import Definitions.Def_OAI_Probability_Ising_Influence
import Definitions.Def_OAI_Probability_Ising_Main
import Theorems.Thm_OAI_BufferedIsing_DSS_covariance_le_zero_field
import Theorems.Thm_OAI_BufferedIsing_comparison_empty_preserves_I
import Theorems.Thm_OAI_BufferedIsing_contractedInteraction_energy
import Theorems.Thm_OAI_BufferedIsing_covarianceBound_iff_effectiveCouplingBound
import Theorems.Thm_OAI_BufferedIsing_extremeLogOdds_eq_actualCoupling
import Theorems.Thm_OAI_BufferedIsing_extreme_rectangle
import Theorems.Thm_OAI_BufferedIsing_interactionGraph_coupling
import Theorems.Thm_OAI_BufferedIsing_jointWeight_logSupermodular
import Theorems.Thm_OAI_BufferedIsing_jointWeight_pos
import Theorems.Thm_OAI_BufferedIsing_mixture_ratio_of_pointwise
import Theorems.Thm_OAI_BufferedIsing_normalized_ratio_of_rectangles
import Theorems.Thm_OAI_BufferedIsing_pairTable_quotient

-- ---- from OAI.Probability.Ising.Basic ----
namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

lemma weight_pos {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (σ : Spins n) : 0 < weight G h σ := Real.exp_pos _

lemma constrainedSum_pos {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (P : Spins n → Prop) (σ : Spins n) (hσ : P σ) :
    0 < constrainedSum G h P := by
  classical
  apply lt_of_lt_of_le (weight_pos G h σ)
  unfold constrainedSum
  exact Finset.single_le_sum (fun τ _ => by
    split_ifs
    · exact (weight_pos G h τ).le
    · exact le_rfl) (Finset.mem_univ σ) |>.trans' (by simp [hσ])

end BufferedIsing

end OAI

-- ---- from OAI.Probability.Ising.Colorings ----
namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

lemma spin_not (s : Bool) : spin (!s) = -spin s := by
  cases s <;> norm_num [spin]

lemma spin_sq (s : Bool) : spin s * spin s = 1 := by
  cases s <;> norm_num [spin]

lemma card_colorings {V : Type*} [Fintype V] (S : Setoid V) :
    Fintype.card (Colorings S) = 2 ^ Nat.card (Quotient S) := by
  classical
  rw [Fintype.card_congr (componentColoringEquiv S), Fintype.card_fun]
  simp [Nat.card_eq_fintype_card]

lemma flipAt_apply {V : Type*} (x y : V) (σ : V → Bool) :
    flipAt x σ y = if y = x then !(σ y) else σ y := by
  classical
  rfl

lemma sum_spin_product {V : Type*} [Fintype V] [DecidableEq V] (x y : V) :
    (∑ σ : V → Bool, spin (σ x) * spin (σ y)) =
      if x = y then (2 : ℝ) ^ Fintype.card V else 0 := by
  classical
  by_cases hxy : x = y
  · subst y
    simp [spin_sq]
  · simp only [hxy, ite_false]
    have H := (flipAt x).sum_comp (fun σ => spin (σ x) * spin (σ y))
    have hf : ∀ σ, spin (flipAt x σ x) * spin (flipAt x σ y) =
        -(spin (σ x) * spin (σ y)) := by
      intro σ
      simp [flipAt_apply, Ne.symm hxy, spin_not]
    simp only [hf, Finset.sum_neg_distrib] at H
    linarith

lemma sum_if_respects {V : Type*} [Fintype V] [DecidableEq V] (S : Setoid V) (f : (V → Bool) → ℝ) :
    (∑ σ, if Respects S σ then f σ else 0) = ∑ σ : Colorings S, f σ.val := by
  classical
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) f

lemma sum_respects_one {V : Type*} [Fintype V] [DecidableEq V] (S : Setoid V) :
    (∑ σ : V → Bool, if Respects S σ then (1 : ℝ) else 0) =
      2 ^ Nat.card (Quotient S) := by
  classical
  rw [sum_if_respects]
  simp [card_colorings]

lemma sum_respects_spin_product {V : Type*} [Fintype V] [DecidableEq V]
    (S : Setoid V) (x y : V) :
    (∑ σ : V → Bool, if Respects S σ then spin (σ x) * spin (σ y) else 0) =
      if S.r x y then (2 : ℝ) ^ Nat.card (Quotient S) else 0 := by
  classical
  rw [sum_if_respects]
  rw [Fintype.sum_equiv (componentColoringEquiv S)
    (fun σ : Colorings S => spin (σ.val x) * spin (σ.val y))
    (fun c => spin (c (Quotient.mk S x)) * spin (c (Quotient.mk S y))) (by intro σ; rfl)]
  simpa only [Nat.card_eq_fintype_card, Quotient.eq] using
    sum_spin_product (Quotient.mk S x) (Quotient.mk S y)

lemma respects_eqvGen {V : Type*} (R : V → V → Prop) (σ : V → Bool) :
    Respects (Relation.EqvGen.setoid R) σ ↔ ∀ x y, R x y → σ x = σ y := by
  constructor
  · intro h x y hxy
    exact h x y (Relation.EqvGen.rel x y hxy)
  · intro h x y hxy
    induction hxy with
    | rel x y hxy => exact h x y hxy
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

end BufferedIsing

end OAI

-- ---- from OAI.Probability.Ising.EdwardsSokal ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

lemma sum_jointColorWeight {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (ω : Finset (Fin m)) :
    (∑ σ, jointColorWeight G I J F ω σ) = fkWeight G I J F ω := by
  calc
    _ = fkEdgeWeight G F ω * ∑ σ : KeptVertex F → Bool,
        if Respects (comparisonSetoid G I J F ω) σ then 1 else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      simp only [jointColorWeight]
      split_ifs <;> simp
    _ = _ := by
      rw [sum_respects_one]
      exact mul_comm _ _

lemma sum_jointColorWeight_spin_product {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (ω : Finset (Fin m)) (i j : KeptVertex F) :
    (∑ σ, jointColorWeight G I J F ω σ * spin (σ i) * spin (σ j)) =
      if (comparisonSetoid G I J F ω).r i j then fkWeight G I J F ω else 0 := by
  calc
    _ = fkEdgeWeight G F ω * ∑ σ : KeptVertex F → Bool,
        if Respects (comparisonSetoid G I J F ω) σ then spin (σ i) * spin (σ j)
        else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      simp only [jointColorWeight]
      split_ifs <;> ring
    _ = _ := by
      rw [sum_respects_spin_product]
      split_ifs
      · exact mul_comm _ _
      · exact mul_zero _

lemma sum_comparisonSpinWeight {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) :
    (∑ σ, comparisonSpinWeight G I J F σ) =
      ∑ ω ∈ (keptEdges G F).powerset, fkWeight G I J F ω := by
  unfold comparisonSpinWeight
  rw [Finset.sum_comm]
  simp only [sum_jointColorWeight]

lemma sum_comparisonSpinWeight_spin_product {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (i j : KeptVertex F) :
    (∑ σ, comparisonSpinWeight G I J F σ * spin (σ i) * spin (σ j)) =
      ∑ ω ∈ (keptEdges G F).powerset,
        if (comparisonSetoid G I J F ω).r i j then fkWeight G I J F ω else 0 := by
  unfold comparisonSpinWeight
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [sum_jointColorWeight_spin_product]

/-- Finite Edwards–Sokal color averaging after vertex deletion and separate terminal contraction. -/
lemma qZero_eq_color_correlation {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (i j : KeptVertex F) :
    qZero G I J F i j =
      (∑ σ, comparisonSpinWeight G I J F σ * spin (σ i) * spin (σ j)) /
        ∑ σ, comparisonSpinWeight G I J F σ := by
  rw [sum_comparisonSpinWeight_spin_product, sum_comparisonSpinWeight]
  rfl

lemma sum_subsets_product {E : Type*} [DecidableEq E] (s : Finset E)
    (f g : E → ℝ) :
    (∑ ω ∈ s.powerset, ∏ e ∈ s, if e ∈ ω then f e else g e) =
      ∏ e ∈ s, (f e + g e) := by
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro ω hω
  have hsub := Finset.mem_powerset.mp hω
  rw [Finset.prod_ite]
  have hf : s.filter (fun e => e ∈ ω) = ω := by
    ext e
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun he => ⟨hsub he, he⟩⟩
  have hg : s.filter (fun e => e ∉ ω) = s \ ω := by
    ext e
    simp
  rw [hf, hg]

lemma respects_comparison_iff {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (ω : Finset (Fin m)) (hω : ω ⊆ keptEdges G F)
    (σ : KeptVertex F → Bool) :
    Respects (comparisonSetoid G I J F ω) σ ↔
      Respects (comparisonSetoid G I J F ∅) σ ∧ BondCompatible G F σ ω := by
  simp only [comparisonSetoid, respects_eqvGen]
  constructor
  · intro H
    constructor
    · intro u v huv
      rcases huv with hi | hj | ⟨e, he, _⟩
      · exact H u v (Or.inl hi)
      · exact H u v (Or.inr (Or.inl hj))
      · exact (Finset.notMem_empty e he).elim
    · intro e he
      have hk := (Finset.mem_filter.mp (hω he)).2
      let u : KeptVertex F := ⟨G.left e, hk.1⟩
      let v : KeptVertex F := ⟨G.right e, hk.2⟩
      have He := H u v (Or.inr (Or.inr ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩))
      simpa only [← extendKept_apply F σ u, ← extendKept_apply F σ v] using He
  · rintro ⟨H, Hω⟩ u v huv
    rcases huv with hi | hj | ⟨e, he, huv | hvu⟩
    · exact H u v (Or.inl hi)
    · exact H u v (Or.inr (Or.inl hj))
    · have He := Hω e he
      rw [huv.1, huv.2] at He
      simpa only [extendKept_apply] using He
    · have He := Hω e he
      rw [hvu.1, hvu.2] at He
      simpa only [extendKept_apply] using He.symm

lemma prod_conditioned_subset {E : Type*} [DecidableEq E] (s ω : Finset E)
    (hω : ω ⊆ s) (P : E → Prop) [DecidablePred P] (f g : E → ℝ) :
    (if ∀ e ∈ ω, P e then ∏ e ∈ s, if e ∈ ω then f e else g e else 0) =
      ∏ e ∈ s, if e ∈ ω then (if P e then f e else 0) else g e := by
  by_cases H : ∀ e ∈ ω, P e
  · rw [ite_eq_left H]
    apply Finset.prod_congr rfl
    intro e _
    by_cases he : e ∈ ω
    · simp only [he, H e he, ite_true]
    · simp only [he, ite_false]
  · rw [ite_eq_right H]
    push Not at H
    obtain ⟨e, he, hP⟩ := H
    symm
    apply Finset.prod_eq_zero (hω he)
    simp only [he, hP, ite_true, ite_false]

lemma jointColorWeight_expansion {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (ω : Finset (Fin m)) (hω : ω ⊆ keptEdges G F)
    (σ : KeptVertex F → Bool) :
    jointColorWeight G I J F ω σ =
      if Respects (comparisonSetoid G I J F ∅) σ then
        ∏ e ∈ keptEdges G F, if e ∈ ω then
          (if extendKept F σ (G.left e) = extendKept F σ (G.right e)
            then 1 - Real.exp (-2 * G.coupling e) else 0)
          else Real.exp (-2 * G.coupling e)
      else 0 := by
  unfold jointColorWeight
  rw [respects_comparison_iff G I J F ω hω σ]
  by_cases H : Respects (comparisonSetoid G I J F ∅) σ
  · simp only [H, true_and, ite_true]
    have hP := prod_conditioned_subset (keptEdges G F) ω hω
      (fun e => extendKept F σ (G.left e) = extendKept F σ (G.right e))
      (fun e => 1 - Real.exp (-2 * G.coupling e))
      (fun e => Real.exp (-2 * G.coupling e))
    unfold BondCompatible fkEdgeWeight
    by_cases Hω : ∀ e ∈ ω, extendKept F σ (G.left e) = extendKept F σ (G.right e)
    · rw [ite_eq_left Hω] at hP ⊢
      exact hP
    · rw [ite_eq_right Hω] at hP ⊢
      exact hP
  · simp only [H, false_and, ite_false]

lemma comparisonSpinWeight_product {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (σ : KeptVertex F → Bool) :
    comparisonSpinWeight G I J F σ =
      if Respects (comparisonSetoid G I J F ∅) σ then
        ∏ e ∈ keptEdges G F,
          ((if extendKept F σ (G.left e) = extendKept F σ (G.right e)
            then 1 - Real.exp (-2 * G.coupling e) else 0) +
              Real.exp (-2 * G.coupling e))
      else 0 := by
  unfold comparisonSpinWeight
  by_cases H : Respects (comparisonSetoid G I J F ∅) σ
  · simp only [H, ite_true]
    calc
      _ = ∑ ω ∈ (keptEdges G F).powerset, ∏ e ∈ keptEdges G F,
          if e ∈ ω then
            (if extendKept F σ (G.left e) = extendKept F σ (G.right e)
              then 1 - Real.exp (-2 * G.coupling e) else 0)
            else Real.exp (-2 * G.coupling e) := by
        apply Finset.sum_congr rfl
        intro ω hω
        rw [jointColorWeight_expansion G I J F ω (Finset.mem_powerset.mp hω) σ]
        simp only [H, ite_true]
      _ = _ := sum_subsets_product _ _ _
  · simp only [H, ite_false]
    apply Finset.sum_eq_zero
    intro ω hω
    rw [jointColorWeight_expansion G I J F ω (Finset.mem_powerset.mp hω) σ]
    simp only [H, ite_false]

lemma es_one_edge_identity (K : ℝ) (s t : Bool) :
    ((if s = t then 1 - Real.exp (-2 * K) else 0) + Real.exp (-2 * K)) =
      Real.exp (-K) * Real.exp (K * spin s * spin t) := by
  rw [← Real.exp_add]
  cases s <;> cases t <;> simp [spin] <;> ring

lemma comparisonSpinWeight_eq_Ising {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (σ : KeptVertex F → Bool) :
    comparisonSpinWeight G I J F σ =
      Real.exp (-(∑ e ∈ keptEdges G F, G.coupling e)) * contractedZeroWeight G I J F σ := by
  rw [comparisonSpinWeight_product]
  unfold contractedZeroWeight
  split_ifs
  · simp only [es_one_edge_identity, Finset.prod_mul_distrib, ← Real.exp_sum,
      Finset.sum_neg_distrib]
    rfl
  · exact (mul_zero _).symm

/-- The zero-field FK/Ising identity with vertex deletion, separate terminal contractions, and parallel edges. -/
lemma qZero_eq_zero_field_correlation {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (i j : KeptVertex F) :
    qZero G I J F i j =
      (∑ σ, contractedZeroWeight G I J F σ * spin (σ i) * spin (σ j)) /
        ∑ σ, contractedZeroWeight G I J F σ := by
  rw [qZero_eq_color_correlation]
  simp only [comparisonSpinWeight_eq_Ising, mul_assoc, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ (Real.exp_ne_zero _)

end BufferedIsing

end OAI

-- ---- from OAI.Probability.Ising.TwoSpin ----
namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

lemma table_expansion (w : Bool → Bool → ℝ) (hw : ∀ s t, 0 < w s t) (s t : Bool) :
    w s t = Real.exp (tableConstant w + tableCoupling w * spin s * spin t +
      tableFieldLeft w * spin s + tableFieldRight w * spin t) := by
  have H : tableConstant w + tableCoupling w * spin s * spin t +
      tableFieldLeft w * spin s + tableFieldRight w * spin t = Real.log (w s t) := by
    cases s <;> cases t <;>
      simp only [tableConstant, tableCoupling, tableFieldLeft, tableFieldRight, spin_true, spin_false] <;>
      ring
  rw [H, Real.exp_log (hw s t)]

lemma balancedTable_eq (w : Bool → Bool → ℝ) (hw : ∀ s t, 0 < w s t) (s t : Bool) :
    balancedTable w s t = Real.exp (tableConstant w + tableCoupling w * spin s * spin t) := by
  rw [balancedTable, table_expansion w hw s t, ← Real.exp_add]
  congr 1
  ring

lemma balancedTable_correlation (w : Bool → Bool → ℝ) (hw : ∀ s t, 0 < w s t) :
    tableExpectation (balancedTable w) (fun s t => spin s * spin t) =
      Real.tanh (tableCoupling w) := by
  simp [tableExpectation, balancedTable_eq w hw, spin, Real.exp_add]
  rw [Real.tanh_eq]
  have hC := (Real.exp_pos (tableConstant w)).ne'
  have hK := (add_pos (Real.exp_pos (tableCoupling w))
    (Real.exp_pos (-tableCoupling w))).ne'
  field_simp
  ring

end BufferedIsing

end OAI

-- ---- from OAI.Probability.Ising.SpinCorrelation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

lemma pairTable_sum {V : Type*} [Fintype V] [DecidableEq V] (W : (V → Bool) → ℝ)
    (i j : V) (f : Bool → Bool → ℝ) :
    (∑ s, ∑ t, pairTable W i j s t * f s t) =
      ∑ σ, W σ * f (σ i) (σ j) := by
  classical
  simp only [pairTable, Finset.sum_mul]
  calc
    _ = ∑ s, ∑ σ, ∑ t, (if σ i = s ∧ σ j = t then W σ else 0) * f s t := by
      apply Finset.sum_congr rfl
      intro s _
      exact Finset.sum_comm
    _ = ∑ σ, ∑ s, ∑ t, (if σ i = s ∧ σ j = t then W σ else 0) * f s t :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro σ _
      cases σ i <;> cases σ j <;> simp

lemma pairTable_expectation {V : Type*} [Fintype V] [DecidableEq V] (W : (V → Bool) → ℝ)
    (i j : V) (f : Bool → Bool → ℝ) :
    tableExpectation (pairTable W i j) f =
      (∑ σ, W σ * f (σ i) (σ j)) / ∑ σ, W σ := by
  unfold tableExpectation
  rw [pairTable_sum]
  have H := pairTable_sum W i j (fun _ _ => 1)
  simp only [mul_one] at H
  rw [H]

lemma pairTable_flip {V : Type*} [Fintype V] [DecidableEq V] (W : (V → Bool) → ℝ)
    (hW : ∀ σ, W (fun v => !σ v) = W σ) (i j : V) (s t : Bool) :
    pairTable W i j (!s) (!t) = pairTable W i j s t := by
  classical
  unfold pairTable
  rw [← Equiv.sum_comp (spinFlipEquiv V)
    (fun σ => if σ i = !s ∧ σ j = !t then W σ else 0)]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [spinFlipEquiv, Equiv.coe_fn_mk, Bool.not_inj_iff, hW]

lemma symmetricTable_balanced (w : Bool → Bool → ℝ)
    (hw : ∀ s t, w (!s) (!t) = w s t) : balancedTable w = w := by
  have h₁ := hw true true
  have h₂ := hw true false
  simp only [Bool.not_true, Bool.not_false] at h₁ h₂
  have hf : tableFieldLeft w = 0 ∧ tableFieldRight w = 0 := by
    constructor <;> dsimp only [tableFieldLeft, tableFieldRight] <;> rw [h₁, h₂] <;> ring
  funext s t
  simp only [balancedTable, hf.1, hf.2, neg_zero, zero_mul, sub_zero,
    Real.exp_zero, mul_one]

lemma symmetricTable_correlation (w : Bool → Bool → ℝ) (hw : ∀ s t, 0 < w s t)
    (hsym : ∀ s t, w (!s) (!t) = w s t) :
    tableExpectation w (fun s t => spin s * spin t) = Real.tanh (tableCoupling w) := by
  have H := balancedTable_correlation w hw
  rw [symmetricTable_balanced w hsym] at H
  exact H

lemma respects_spinFlip {V : Type*} (S : Setoid V) (σ : V → Bool) :
    Respects S (fun v => !σ v) ↔ Respects S σ := by
  unfold Respects
  simp only [Bool.not_inj_iff]

lemma deletedEnergy_spinFlip {n m : ℕ} (G : FiniteGraph n m)
    (F : Finset (Fin n)) (σ : KeptVertex F → Bool) :
    deletedEnergy G F (fun v => !σ v) = deletedEnergy G F σ := by
  unfold deletedEnergy
  apply Finset.sum_congr rfl
  intro e he
  obtain ⟨hl, hr⟩ := (Finset.mem_filter.mp he).2
  have hleft (σ : KeptVertex F → Bool) :
      extendKept F σ (G.left e) = σ ⟨G.left e, hl⟩ := by
    exact extendKept_apply F σ ⟨G.left e, hl⟩
  have hright (σ : KeptVertex F → Bool) :
      extendKept F σ (G.right e) = σ ⟨G.right e, hr⟩ := by
    exact extendKept_apply F σ ⟨G.right e, hr⟩
  rw [hleft, hright, hleft, hright, spin_not, spin_not]
  ring

lemma contractedZeroWeight_spinFlip {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (σ : KeptVertex F → Bool) :
    contractedZeroWeight G I J F (fun v => !σ v) = contractedZeroWeight G I J F σ := by
  unfold contractedZeroWeight
  rw [respects_spinFlip, deletedEnergy_spinFlip]

lemma contractedZeroWeight_nonneg {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (σ : KeptVertex F → Bool) :
    0 ≤ contractedZeroWeight G I J F σ := by
  unfold contractedZeroWeight
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

lemma contractedZero_pairTable_pos {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (hIJ : Disjoint I J)
    (i j : KeptVertex F) (hi : i.val ∈ I) (hj : j.val ∈ J) (s t : Bool) :
    0 < pairTable (contractedZeroWeight G I J F) i j s t := by
  classical
  let σ : KeptVertex F → Bool := fun v => if v.val ∈ I then s else t
  have hjI : j.val ∉ I := fun hjI => Finset.disjoint_left.mp hIJ hjI hj
  have hσi : σ i = s := by simp only [σ, ite_eq_left hi]
  have hσj : σ j = t := by simp only [σ, ite_eq_right hjI]
  have hresp : Respects (comparisonSetoid G I J F ∅) σ := by
    intro x y hxy
    have hI := comparison_empty_preserves_I G I J F hIJ x y hxy
    simp only [σ, hI]
  unfold pairTable
  apply Finset.sum_pos'
  · intro τ _
    split_ifs
    · exact contractedZeroWeight_nonneg G I J F τ
    · exact le_rfl
  · refine ⟨σ, Finset.mem_univ _, ?_⟩
    rw [ite_eq_left ⟨hσi, hσj⟩, contractedZeroWeight, ite_eq_left hresp]
    exact Real.exp_pos _

/-- The FK terminal connection probability is the hyperbolic tangent of the zero-field effective coupling. -/
lemma qZero_eq_tanh_effective {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (hIJ : Disjoint I J)
    (i j : KeptVertex F) (hi : i.val ∈ I) (hj : j.val ∈ J) :
    qZero G I J F i j =
      Real.tanh (tableCoupling (pairTable (contractedZeroWeight G I J F) i j)) := by
  rw [← symmetricTable_correlation _ (contractedZero_pairTable_pos G I J F hIJ i j hi hj)
    (pairTable_flip _ (contractedZeroWeight_spinFlip G I J F) i j)]
  rw [pairTable_expectation, qZero_eq_zero_field_correlation]
  simp only [mul_assoc]

lemma artanh_qZero_eq_effective {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (hIJ : Disjoint I J)
    (i j : KeptVertex F) (hi : i.val ∈ I) (hj : j.val ∈ J) :
    Real.artanh (qZero G I J F i j) =
      tableCoupling (pairTable (contractedZeroWeight G I J F) i j) := by
  rw [qZero_eq_tanh_effective G I J F hIJ i j hi hj, Real.artanh_tanh]

end BufferedIsing

end OAI

-- ---- from OAI.Probability.Ising.Marginals ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

/-- The extreme-rectangle bound for the arbitrary-field Ising marginal with common pins. -/
lemma marginal_extreme_rectangle {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n))
    (hIJ : Disjoint I J) (hIF : Disjoint I F) (hJF : Disjoint J F)
    (τ a a' b b' : Spins n) :
    |Real.log (jointWeight G h I J F τ a b) +
        Real.log (jointWeight G h I J F τ a' b') -
        Real.log (jointWeight G h I J F τ a b') -
        Real.log (jointWeight G h I J F τ a' b)| ≤
      Real.log (jointWeight G h I J F τ ⊤ ⊤) +
        Real.log (jointWeight G h I J F τ ⊥ ⊥) -
        Real.log (jointWeight G h I J F τ ⊤ ⊥) -
        Real.log (jointWeight G h I J F τ ⊥ ⊤) := by
  apply extreme_rectangle (fun u v => Real.log (jointWeight G h I J F τ u v)) _ a a' b b'
  intro u v s t huv hst
  have H := jointWeight_logSupermodular G h I J F τ u v t s
  rw [inf_eq_left.mpr huv, sup_eq_right.mpr huv,
    inf_eq_right.mpr hst, sup_eq_left.mpr hst] at H
  have hp := jointWeight_pos G h I J F hIJ hIF hJF τ
  have HL := Real.log_le_log (mul_pos (hp u t) (hp v s)) H
  simpa only [Real.log_mul (hp u t).ne' (hp v s).ne',
    Real.log_mul (hp u s).ne' (hp v t).ne'] using HL

lemma agreesOn_iff_restrict_eq {n : ℕ} (I : Finset (Fin n)) (σ a : Spins n) :
    AgreesOn I σ a ↔ restrictSpin I σ = restrictSpin I a := by
  constructor
  · intro H
    funext v
    exact H v.val v.property
  · intro H v hv
    exact congrFun H ⟨v, hv⟩

lemma jointWeight_extend_restrict {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n)) (τ a b : Spins n) :
    jointWeight G h I J F τ (extendSpin I (restrictSpin I a)) b =
      jointWeight G h I J F τ a b := by
  simp only [jointWeight, constrainedSum, agreesOn_iff_restrict_eq, restrict_extend]

lemma sum_jointWeight_eq_denominator {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n)) (τ b : Spins n) :
    (∑ a : I → Bool, jointWeight G h I J F τ (extendSpin I a) b) =
      constrainedSum G h (fun σ => AgreesOn J σ b ∧ AgreesOn F σ τ) := by
  classical
  unfold jointWeight constrainedSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases hσ : AgreesOn J σ b ∧ AgreesOn F σ τ
  · simp only [hσ, and_true, ite_true]
    simp only [agreesOn_iff_restrict_eq, restrict_extend]
    simp
  · simp only [hσ, and_false, ite_false, Finset.sum_const_zero]

/-- The normalized conditional probability ratio is bounded by the extreme log odds. -/
lemma conditional_ratio_extreme {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n))
    (hIJ : Disjoint I J) (hIF : Disjoint I F) (hJF : Disjoint J F)
    (τ a b b' : Spins n) :
    Real.exp (-extremeLogOdds G h I J F τ) ≤
        conditionalProb G h I J F a b τ / conditionalProb G h I J F a b' τ ∧
      conditionalProb G h I J F a b τ / conditionalProb G h I J F a b' τ ≤
        Real.exp (extremeLogOdds G h I J F τ) := by
  have H := normalized_ratio_of_rectangles
    (fun (α : I → Bool) β => jointWeight G h I J F τ (extendSpin I α) β)
    (fun α β => jointWeight_pos G h I J F hIJ hIF hJF τ (extendSpin I α) β)
    (extremeLogOdds G h I J F τ)
    (fun α α' β β' => marginal_extreme_rectangle G h I J F hIJ hIF hJF τ
      (extendSpin I α) (extendSpin I α') β β')
    (restrictSpin I a) b b'
  simp only [sum_jointWeight_eq_denominator, jointWeight_extend_restrict] at H
  simpa only [jointWeight, conditionalProb] using H

lemma conditionalProb_pos {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n))
    (hIJ : Disjoint I J) (hIF : Disjoint I F) (hJF : Disjoint J F)
    (a b τ : Spins n) : 0 < conditionalProb G h I J F a b τ := by
  apply div_pos (jointWeight_pos G h I J F hIJ hIF hJF τ a b)
  apply constrainedSum_pos G h _ (fun v => if v ∈ J then b v else τ v)
  constructor
  · intro v hv
    simp [hv]
  · intro v hv
    have hvJ : v ∉ J := fun hvJ => Finset.disjoint_left.mp hJF hvJ hv
    simp [hvJ]

lemma mixture_ratio_extreme {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n))
    (hIJ : Disjoint I J) (hIF : Disjoint I F) (hJF : Disjoint J F)
    (a τ : Spins n) (mix mix' : Spins n → ℝ)
    (hmix : ∀ b, 0 ≤ mix b) (hmix' : ∀ b, 0 ≤ mix' b)
    (hmixsum : ∑ b, mix b = 1) (hmix'sum : ∑ b, mix' b = 1) :
    Real.exp (-extremeLogOdds G h I J F τ) ≤
        mixtureProb G h I J F a τ mix / mixtureProb G h I J F a τ mix' ∧
      mixtureProb G h I J F a τ mix / mixtureProb G h I J F a τ mix' ≤
        Real.exp (extremeLogOdds G h I J F τ) :=
  mixture_ratio_of_pointwise
    (fun b => conditionalProb G h I J F a b τ)
    (fun b => conditionalProb_pos G h I J F hIJ hIF hJF a b τ) _ _
    (fun b b' => conditional_ratio_extreme G h I J F hIJ hIF hJF τ a b b')
    mix mix' hmix hmix' hmixsum hmix'sum

end BufferedIsing

end OAI

-- ---- from OAI.Probability.Ising.Contraction ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

lemma quotientField_zero {V : Type*} [Fintype V] (S : Setoid V) :
    quotientField S (fun _ => 0) = fun _ => 0 := by
  funext q
  simp [quotientField]

lemma contractedZero_pairTable_quotient {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (i j : KeptVertex F) (s t : Bool) :
    pairTable (contractedZeroWeight G I J F) i j s t =
      pairTable (interactionWeight (contractedInteraction G I J F) (fun _ => 0))
        (Quotient.mk _ i) (Quotient.mk _ j) s t := by
  unfold contractedZeroWeight
  rw [pairTable_quotient]
  have H := contractedInteraction_energy G I J F (fun _ => 0)
  have He : ∀ c : ContractedVertex G I J F → Bool,
      interactionEnergy (contractedInteraction G I J F) (fun _ => 0) c =
        deletedEnergy G F (fun v => c (Quotient.mk _ v)) := by
    intro c
    simpa only [quotientField_zero, zero_mul, Finset.sum_const_zero, add_zero] using H c
  have hw : (fun c : ContractedVertex G I J F → Bool =>
      Real.exp (deletedEnergy G F (fun v => c (Quotient.mk _ v)))) =
      interactionWeight (contractedInteraction G I J F) (fun _ => 0) := by
    funext c
    rw [interactionWeight, He]
  rw [hw]

lemma contractedTerminal_ne {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (hIJ : Disjoint I J)
    (i j : KeptVertex F) (hi : i.val ∈ I) (hj : j.val ∈ J) :
    Quotient.mk (comparisonSetoid G I J F ∅) i ≠ Quotient.mk _ j := by
  intro H
  exact Finset.disjoint_left.mp hIJ
    ((comparison_empty_preserves_I G I J F hIJ i j (Quotient.exact H)).mp hi) hj

lemma actualTerminal_ne {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (hIJ : Disjoint I J)
    (i j : KeptVertex F) (hi : i.val ∈ I) (hj : j.val ∈ J) :
    actualTerminal G I J F i ≠ actualTerminal G I J F j := by
  intro H
  exact contractedTerminal_ne G I J F hIJ i j hi hj ((Fintype.equivFin _).injective H)

/-- The inverse hyperbolic tangent of the FK connection probability equals the zero-field coupling on the deleted, separately contracted graph. -/
lemma artanh_qZero_eq_actualCoupling {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (hIJ : Disjoint I J)
    (i j : KeptVertex F) (hi : i.val ∈ I) (hj : j.val ∈ J) :
    Real.artanh (qZero G I J F i j) = tableCoupling (pairTable
      (weight (actualComparisonGraph G I J F) (fun _ => 0))
      (actualTerminal G I J F i) (actualTerminal G I J F j)) := by
  classical
  rw [artanh_qZero_eq_effective G I J F hIJ i j hi hj]
  have H : pairTable (contractedZeroWeight G I J F) i j =
      pairTable (interactionWeight (contractedInteraction G I J F) (fun _ => 0))
        (Quotient.mk _ i) (Quotient.mk _ j) := by
    funext s t
    exact contractedZero_pairTable_quotient G I J F i j s t
  rw [H]
  exact (interactionGraph_coupling _ (fun _ => 0) _ _
    (contractedTerminal_ne G I J F hIJ i j hi hj)).symm

end BufferedIsing

end OAI

-- ---- from OAI.Probability.Ising.Main ----
namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

noncomputable section

lemma dssMatrix_nonneg {n m : ℕ} (G : FiniteGraph n m) (u v : Fin n) :
    0 ≤ dssMatrix G u v := by
  apply Finset.sum_nonneg
  intro e _
  split_ifs <;> first | exact G.coupling_nonneg e | exact le_rfl

lemma dss_hamiltonian_eq {n m : ℕ} (G : FiniteGraph n m) (h : Fin n → ℝ)
    (σ : Spins n) : DSS.hamiltonian (dssMatrix G) h σ = energy G h σ := by
  unfold DSS.hamiltonian energy dssMatrix
  change ((∑ u, ∑ v, (∑ e, if G.left e = u then if G.right e = v then
    G.coupling e else 0 else 0) * spin (σ u) * spin (σ v)) + _) = _
  congr 1
  simp only [Finset.sum_mul]
  calc
    _ = ∑ u, ∑ e, ∑ v, (if G.left e = u then if G.right e = v then
        G.coupling e else 0 else 0) * spin (σ u) * spin (σ v) := by
      apply Finset.sum_congr rfl
      intro u _
      exact Finset.sum_comm
    _ = ∑ e, ∑ u, ∑ v, (if G.left e = u then if G.right e = v then
        G.coupling e else 0 else 0) * spin (σ u) * spin (σ v) := Finset.sum_comm
    _ = _ := by simp [ite_mul, Finset.sum_ite_irrel]

lemma dss_mass_eq {n m : ℕ} (G : FiniteGraph n m) (h : Fin n → ℝ)
    (σ : Spins n) : DSS.mass (dssMatrix G) h σ = weight G h σ := by
  rw [DSS.mass, weight, dss_hamiltonian_eq]

lemma dss_average_eq {n m : ℕ} (G : FiniteGraph n m) (h : Fin n → ℝ)
    (f : Spins n → ℝ) : DSS.average (dssMatrix G) h f = expectation G h f := by
  simp only [DSS.average, DSS.part, dss_mass_eq, expectation]
  congr!

/-- The arbitrary-field covariance bound for the finite edge-list Gibbs law, including equal sites. -/
theorem arbitraryFieldCovarianceBound : ArbitraryFieldCovarianceBound := by
  intro n m G h u v
  have H := DSS.covariance_le_zero_field (dssMatrix G) (dssMatrix_nonneg G) h u v
  simp only [DSS.correlation, DSS.mean, dss_average_eq] at H
  convert H using 1 <;> congr!

theorem effectiveCouplingBound : EffectiveCouplingBound :=
  covarianceBound_iff_effectiveCouplingBound.mp arbitraryFieldCovarianceBound

lemma extremeLogOdds_le_zero {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n))
    (hIJ : Disjoint I J) (hIF : Disjoint I F) (hJF : Disjoint J F)
    (i j : KeptVertex F) (hi : i.val ∈ I) (hj : j.val ∈ J) (τ : Spins n) :
    extremeLogOdds G h I J F τ ≤ 4 * Real.artanh (qZero G I J F i j) := by
  rw [extremeLogOdds_eq_actualCoupling G h I J F hIJ hIF hJF i j hi hj τ,
    artanh_qZero_eq_actualCoupling G I J F hIJ i j hi hj]
  exact mul_le_mul_of_nonneg_left
    (effectiveCouplingBound _ _ (actualComparisonGraph G I J F)
      (actualComparisonField G h I J F τ) _ _
      (actualTerminal_ne G I J F hIJ i j hi hj)) (by norm_num)

/-- Finite-graph comparison for arbitrary probability mixtures on both sides. Dirac mixtures recover the conditional laws. -/
theorem finite_graph_comparison {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n))
    (hIJ : Disjoint I J) (hIF : Disjoint I F) (hJF : Disjoint J F)
    (i j : KeptVertex F) (hi : i.val ∈ I) (hj : j.val ∈ J)
    (a τ : Spins n) (mix mix' : Spins n → ℝ)
    (hmix : ∀ b, 0 ≤ mix b) (hmix' : ∀ b, 0 ≤ mix' b)
    (hmixsum : ∑ b, mix b = 1) (hmix'sum : ∑ b, mix' b = 1) :
    Real.exp (-4 * Real.artanh (qZero G I J F i j)) ≤
        mixtureProb G h I J F a τ mix / mixtureProb G h I J F a τ mix' ∧
      mixtureProb G h I J F a τ mix / mixtureProb G h I J F a τ mix' ≤
        Real.exp (4 * Real.artanh (qZero G I J F i j)) := by
  have H := mixture_ratio_extreme G h I J F hIJ hIF hJF a τ mix mix'
    hmix hmix' hmixsum hmix'sum
  have HB := extremeLogOdds_le_zero G h I J F hIJ hIF hJF i j hi hj τ
  exact ⟨(Real.exp_le_exp.mpr (by linarith)).trans H.1,
    H.2.trans (Real.exp_le_exp.mpr HB)⟩

end

end BufferedIsing

end OAI

-- ---- mission target ----
open OAI OAI.BufferedIsing
open scoped BigOperators Classical

theorem solution {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n))
    (hIJ : Disjoint I J) (hIF : Disjoint I F) (hJF : Disjoint J F)
    (i j : KeptVertex F) (hi : i.val ∈ I) (hj : j.val ∈ J)
    (a τ : Spins n) (mix mix' : Spins n → ℝ)
    (hmix : ∀ b, 0 ≤ mix b) (hmix' : ∀ b, 0 ≤ mix' b)
    (hmixsum : ∑ b, mix b = 1) (hmix'sum : ∑ b, mix' b = 1) :
    Real.exp (-4 * Real.artanh (qZero G I J F i j)) ≤
        mixtureProb G h I J F a τ mix / mixtureProb G h I J F a τ mix' ∧
      mixtureProb G h I J F a τ mix / mixtureProb G h I J F a τ mix' ≤
        Real.exp (4 * Real.artanh (qZero G I J F i j)) := by
  first
    | exact OAI.BufferedIsing.finite_graph_comparison G h I J F hIJ hIF hJF i j hi hj a τ mix mix' hmix hmix' hmixsum hmix'sum
    | exact OAI.BufferedIsing.finite_graph_comparison
    | (apply OAI.BufferedIsing.finite_graph_comparison <;> assumption)
    | (intros; apply OAI.BufferedIsing.finite_graph_comparison <;> assumption)
