-- Prove2me | solution 1 for MDPFinance.StructuredModels.convex_structure_theorem
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:10:43.196058+00:00
-- url     : https://prove2.me/submissions/f80998a6-cebf-43d5-b7f5-909169031990

import Mathlib
import Definitions.Def_MDPFinance_StructuredModels_Model
import Definitions.Def_MDPFinance_StructuredModels_Policy
import Definitions.Def_MDPFinance_StructuredModels_Operators
import Definitions.Def_MDPFinance_StructuredModels_BoundingFunction
import Definitions.Def_MDPFinance_StructuredModels_StructureAssumption
import Definitions.Def_MDPFinance_StructuredModels_ConvexAnalysis

open MeasureTheory ProbabilityTheory MDPFinance.StructuredModels

namespace ConvexSANCex

/-- `ℝ` with the trivial σ-algebra `⊥`, so that `id : E0 → ℝ` is not measurable. -/
def E0 : Type := ℝ

instance : AddCommGroup E0 := inferInstanceAs (AddCommGroup ℝ)
instance : Module ℝ E0 := inferInstanceAs (Module ℝ ℝ)
instance : MeasurableSpace E0 := ⊥

def z0 : E0 := (0 : ℝ)

def toR : E0 → ℝ := fun x => x

noncomputable def M0 : MarkovDecisionModel E0 ℝ 1 where
  D := fun _ => Set.univ
  hD_meas := fun _ _ => MeasurableSet.univ
  hD_sel := fun _ _ => ⟨fun _ => 0, measurable_const, fun _ => Set.mem_univ _⟩
  Q := fun _ => Kernel.const _ (Measure.dirac z0)
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

theorem convex_const (c : EReal) : ConvexOnEReal (Set.univ : Set E0) (fun _ => c) :=
  ⟨convex_univ, fun _ _ _ _ _ _ ha hb hab => const_le c ha hb hab⟩

theorem not_meas : ¬ Measurable toR := by
  intro h
  have hs := h (measurableSet_singleton (0 : ℝ))
  rw [MeasurableSpace.measurableSet_bot_iff] at hs
  rcases hs with hs | hs
  · have : z0 ∈ toR ⁻¹' {0} := rfl
    rw [hs] at this
    exact this
  · have : ((1 : ℝ) : E0) ∈ toR ⁻¹' {0} := by rw [hs]; trivial
    exact one_ne_zero (α := ℝ) this

end ConvexSANCex

open ConvexSANCex in
theorem solution : ¬ (∀ {E A : Type} [MeasurableSpace E] [MeasurableSpace A]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup A] [Module ℝ A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (b : E → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb) (Deltas : ℕ → Set (E → A))
    (hEconvex : Convex ℝ (Set.univ : Set E))
    (hDn : ∀ n < N, M.D n = Set.univ)
    (hQ_convex : ∀ n < N, ∀ v ∈ IBbPlus b, ConvexOnEReal Set.univ v →
      ∀ a : A, ConvexOnEReal Set.univ (fun x => erealIntegral (M.Q n (x, a)) v))
    (hr_convex : ∀ n < N, ∀ a : A, ConvexOn ℝ Set.univ (fun x => M.r n (x, a)))
    (hg_convex : ConvexOn ℝ Set.univ M.g)
    (hmax : ∀ n < N, ∀ v ∈ IBbPlus b, ConvexOnEReal Set.univ v →
      ∃ f ∈ Deltas n, IsMaximizer M n v f),
    StructureAssumption M (fun n => {v ∈ IBbPlus b | ConvexOnEReal Set.univ v}) Deltas) := by
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
  have hS := h M0 (fun _ => 0) 0 0 0 hb (fun _ => Set.univ) convex_univ (fun _ _ => rfl)
    (fun n _ v _ _ a => by
      show ConvexOnEReal _ (fun _ => erealIntegral (Measure.dirac z0) v)
      exact convex_const _) (fun _ _ _ => convexOn_const 0 convex_univ)
    (convexOn_const 0 convex_univ) ?_
  · have h2 := hS.2.1 0 Nat.zero_lt_one (Set.mem_univ toR)
    exact not_meas h2.1
  · intro n _ v _ _
    refine ⟨fun _ => 0, Set.mem_univ _, ⟨measurable_const, fun _ => Set.mem_univ _⟩, ?_⟩
    funext x
    show L M0 n v (x, 0) = ⨆ a ∈ M0.Dx n x, L M0 n v (x, a)
    have hc : ∀ a, L M0 n v (x, a) = L M0 n v (x, 0) := fun _ => rfl
    simp only [hc]
    exact (biSup_const ⟨0, Set.mem_univ _⟩).symm

#print axioms solution
