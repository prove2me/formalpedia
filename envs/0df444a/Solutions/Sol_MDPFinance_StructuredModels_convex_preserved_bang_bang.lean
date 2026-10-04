-- Prove2me | solution 1 for MDPFinance.StructuredModels.convex_preserved_bang_bang
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:13:39.596904+00:00
-- url     : https://prove2.me/submissions/c608896d-f79c-40a8-a417-62e67e77b570

import Mathlib
import Definitions.Def_MDPFinance_StructuredModels_BoundingFunction
import Definitions.Def_MDPFinance_StructuredModels_Model
import Definitions.Def_MDPFinance_StructuredModels_Policy
import Definitions.Def_MDPFinance_StructuredModels_Operators
import Definitions.Def_MDPFinance_StructuredModels_ConvexAnalysis

open MeasureTheory ProbabilityTheory MDPFinance.StructuredModels

namespace BangBangCex

/-- `ℝ` as a real vector space, but with the indiscrete topology (so `univ` is compact). -/
def A0 : Type := ℝ

instance : AddCommGroup A0 := inferInstanceAs (AddCommGroup ℝ)
instance : Module ℝ A0 := inferInstanceAs (Module ℝ ℝ)
instance : MeasurableSpace A0 := inferInstanceAs (MeasurableSpace ℝ)
instance : TopologicalSpace A0 := ⊤

def a0 : A0 := (0 : ℝ)

noncomputable def M0 : MarkovDecisionModel ℝ A0 1 where
  D := fun _ => Set.univ
  hD_meas := fun _ _ => MeasurableSet.univ
  hD_sel := fun _ _ => ⟨fun _ => a0, measurable_const, fun _ => Set.mem_univ _⟩
  Q := fun _ => Kernel.const _ (Measure.dirac (0 : ℝ))
  hQ_prob := fun _ _ _ => by
    simp only [Kernel.const_apply]
    infer_instance
  r := fun _ _ => 0
  hr_meas := fun _ _ => measurable_const
  g := fun _ => 0
  hg_meas := measurable_const

theorem const_le (c : EReal) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    c ≤ (a : EReal) * c + (b : EReal) * c := by
  rcases eq_or_lt_of_le ha with h0 | hapos
  · subst h0
    have : b = 1 := by linarith
    subst this
    simp
  rcases eq_or_lt_of_le hb with h0 | hbpos
  · subst h0
    have : a = 1 := by linarith
    subst this
    simp
  induction c using EReal.rec with
  | bot => simp [EReal.coe_mul_bot_of_pos hapos, EReal.coe_mul_bot_of_pos hbpos]
  | top => simp [EReal.coe_mul_top_of_pos hapos, EReal.coe_mul_top_of_pos hbpos]
  | coe x =>
    have : a * x + b * x = x := by rw [← add_mul, hab, one_mul]
    rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, this]

theorem convex_const {X : Type} [AddCommGroup X] [Module ℝ X] (c : EReal) :
    ConvexOnEReal (Set.univ : Set X) (fun _ => c) :=
  ⟨convex_univ, fun _ _ _ _ _ _ ha hb hab => const_le c ha hb hab⟩

def u0 : A0 := (1 : ℝ)

theorem extreme_empty : (Set.univ : Set A0).extremePoints ℝ = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have h := hx.2 (x₁ := x - u0) (x₂ := x + u0) (Set.mem_univ _) (Set.mem_univ _) ?_
  · have h1 : x - u0 = x := h
    rw [sub_eq_self] at h1
    exact one_ne_zero (α := ℝ) h1
  · refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    rw [smul_sub, smul_add, sub_add_add_cancel, ← add_smul]
    norm_num

end BangBangCex

open BangBangCex in
theorem solution : ¬ (∀ {E A : Type} [MeasurableSpace E] [MeasurableSpace A]
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace A] [AddCommGroup A] [Module ℝ A]
    {N : ℕ} (M : MarkovDecisionModel E A N) (b : E → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb) (n : ℕ) (hn : n < N)
    (v : E → EReal) (hv : v ∈ IBbPlus b)
    (hDn : M.D n = Set.univ)
    (hL_convex_x : ∀ a : A, ConvexOnEReal Set.univ (fun x => L M n v (x, a))),
    ConvexOnEReal Set.univ (T M n v) ∧
      (IsCompact (Set.univ : Set A) → Convex ℝ (Set.univ : Set A) →
        ((Set.univ : Set A).extremePoints ℝ).Finite →
        (∀ x : E, ConvexOnEReal Set.univ (fun a => L M n v (x, a))) →
        ∃ f : E → A, IsMaximizer M n v f ∧
          ∀ x : E, f x ∈ (Set.univ : Set A).extremePoints ℝ)) := by
  intro h
  have hb : IsUpperBoundingFunction M0 (fun _ => 0) 0 0 0 :=
    { hb_meas := measurable_const
      hb_nonneg := fun _ => le_rfl
      hcr := le_rfl
      hcg := le_rfl
      hαb := le_rfl
      hr := fun _ _ _ _ => by simp [M0]
      hg := fun _ => by simp [M0]
      hQ := fun _ _ _ _ => by simp }
  have hv : (fun _ : ℝ => (0 : EReal)) ∈ IBbPlus (fun _ : ℝ => (0 : ℝ)) :=
    ⟨measurable_const, fun _ => EReal.zero_ne_top, 0, le_rfl, fun _ => by simp⟩
  have hLc : ∀ x a, L M0 0 (fun _ => 0) (x, a) = L M0 0 (fun _ => 0) (0, a0) := fun _ _ => rfl
  obtain ⟨_, h2⟩ := h M0 (fun _ => 0) 0 0 0 hb 0 Nat.zero_lt_one (fun _ => 0) hv rfl
    (fun a => by simp only [hLc]; exact convex_const _)
  obtain ⟨f, _, hf⟩ := h2 isCompact_univ convex_univ (by rw [extreme_empty]; exact Set.finite_empty)
    (fun x => by simp only [hLc]; exact convex_const _)
  have := hf 0
  rw [extreme_empty] at this
  exact this

#print axioms solution
