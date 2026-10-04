-- Prove2me | solution 1 for MDPFinance.StructuredModels.monotone_structure_theorem
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:12:06.558359+00:00
-- url     : https://prove2.me/submissions/ac0244da-bdc1-4be0-b37d-6ca7d423adf3

import Mathlib
import Definitions.Def_MDPFinance_StructuredModels_Model
import Definitions.Def_MDPFinance_StructuredModels_Policy
import Definitions.Def_MDPFinance_StructuredModels_Operators
import Definitions.Def_MDPFinance_StructuredModels_BoundingFunction
import Definitions.Def_MDPFinance_StructuredModels_StructureAssumption

open MeasureTheory ProbabilityTheory MDPFinance.StructuredModels

namespace MonoSANCex

/-- `ℝ` with the trivial σ-algebra `⊥`, so that `id : E0 → ℝ` is not measurable. -/
def E0 : Type := ℝ

instance : AddCommGroup E0 := inferInstanceAs (AddCommGroup ℝ)
instance : Module ℝ E0 := inferInstanceAs (Module ℝ ℝ)
instance : Preorder E0 := inferInstanceAs (Preorder ℝ)
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

end MonoSANCex

open MonoSANCex in
theorem solution : ¬ (∀ {E A : Type} [MeasurableSpace E] [MeasurableSpace A]
    [Preorder E] [Preorder A] {N : ℕ} (M : MarkovDecisionModel E A N) (b : E → ℝ)
    (cr cg αb : ℝ) (hb : IsUpperBoundingFunction M b cr cg αb) (Deltas : ℕ → Set (E → A))
    (hD : ∀ n < N, Monotone (M.Dx n))
    (hQ : ∀ n < N, ∀ a, ∀ v ∈ IBbPlus b, Monotone v →
      MonotoneOn (fun x' => erealIntegral (M.Q n (x', a)) v) {x' | a ∈ M.Dx n x'})
    (hr : ∀ n < N, ∀ a, MonotoneOn (fun x => M.r n (x, a)) {x | a ∈ M.Dx n x})
    (hg : Monotone M.g)
    (hmax : ∀ n < N, ∀ v ∈ IBbPlus b, Monotone v → ∃ f ∈ Deltas n, IsMaximizer M n v f),
    StructureAssumption M (fun n => {v ∈ IBbPlus b | Monotone v}) Deltas) := by
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
  have hS := h M0 (fun _ => 0) 0 0 0 hb (fun _ => Set.univ) (fun n _ => show Monotone (fun _ : E0 => (Set.univ : Set ℝ)) from monotone_const)
    (fun n _ a v _ _ => by
      show MonotoneOn (fun _ => erealIntegral (Measure.dirac z0) v) _
      exact monotone_const.monotoneOn _)
    (fun _ _ _ => monotone_const.monotoneOn _) monotone_const ?_
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
