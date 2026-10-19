-- Prove2me | solution 2 for OAI.CriticalZ3.zero_one_of_finite_alteration
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:10:05.705986+00:00
-- url     : https://prove2.me/submissions/189805b0-68af-40a2-b8f6-541feee860c1

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/Basic.lean:L399-L440
-- (upload_full_project.md Phase 4): solution for node OAI.CriticalZ3.zero_one_of_finite_alteration. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic

-- ---- from OAI.Probability.CriticalZ3.Basic ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
private theorem Measurable.of_eval {α δ : Type*} {X : δ → Type*}
    [MeasurableSpace α] [∀ a, MeasurableSpace (X a)] {f : α → ∀ a, X a}
    (hf : ∀ a, Measurable fun c => f c a) : Measurable f :=
  measurable_pi_lambda f hf
end Lean433MeasurableOfEval

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uE uOmega uV

-- [generator] trimmed: open MeasureTheory ProbabilityTheory
open _root_.MeasureTheory ProbabilityTheory

namespace CriticalZ3

/-! Finite alterations, tail invariance, and the infinite seed limit. -/

open Filter
open scoped Topology

/-- Kolmogorov zero-one law in the finite-alteration form needed here. This
is proved for arbitrary independent bit coordinates, not assumed for clusters. -/
theorem zero_one_of_finite_alteration {E : Type uE} (μ : Measure (E → Bool))
    (hi : iIndepFun (fun e (ω : E → Bool) => ω e) μ)
    (A : Set (E → Bool)) (hA : MeasurableSet A)
    (hinv : ∀ (J : Finset E) (ω ω' : E → Bool),
      (∀ e ∉ J, ω' e = ω e) → (ω' ∈ A ↔ ω ∈ A)) : μ A = 0 ∨ μ A = 1 := by
  classical
  let M : E → MeasurableSpace (E → Bool) :=
    fun e => MeasurableSpace.comap (fun ω => ω e) inferInstance
  have hM : ∀ e, M e ≤ (inferInstance : MeasurableSpace (E → Bool)) := fun e => (measurable_pi_apply e).comap_le
  have hmi : iIndep M μ := (iIndepFun_iff_iIndep _ _ _).mp hi
  have htail : MeasurableSet[limsup M cofinite] A := by
    rw [Filter.limsup_eq_iInf_iSup]
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro s
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro hs
    have hc : sᶜ.Finite := Filter.mem_cofinite.mp hs
    let f : (E → Bool) → (E → Bool) := fun ω e => if e ∈ s then ω e else false
    have hf : @Measurable (E → Bool) (E → Bool) (⨆ e ∈ s, M e) inferInstance f := by
      apply @Measurable.of_eval (E → Bool) E (fun _ => Bool) (⨆ e ∈ s, M e) _ f
      intro e
      by_cases he : e ∈ s
      · simp only [f,ite_eq_left he]
        exact Measurable.of_comap_le (le_iSup_of_le e (le_iSup_of_le he le_rfl))
      · simp only [f,ite_eq_right he]
        exact measurable_const
    have heq : f ⁻¹' A = A := by
      ext ω
      apply hinv hc.toFinset ω (f ω)
      intro e he
      have hes : e ∈ s := by simpa only [Set.Finite.mem_toFinset,Set.mem_compl_iff,not_not] using he
      simp only [f,ite_eq_left hes]
    rw [← heq]
    exact hf hA
  apply measure_zero_or_one_of_measurableSet_limsup hM hmi
    (p := fun s : Set E => s.Finite) (ns := fun J : Finset E => (J : Set E))
    (fun s hs => Filter.mem_cofinite.mpr (by simpa only [compl_compl] using hs)) _
    (fun J => J.finite_toSet) (fun e => ⟨{e},by simp⟩) htail
  intro J K
  exact ⟨J ∪ K, by simp, by simp⟩

end CriticalZ3

end OAI

-- ---- platform node ----
open OAI OAI.CriticalZ3
open MeasureTheory ProbabilityTheory
open Filter
open scoped Topology


theorem solution.{uE} : type_of% @_root_.OAI.CriticalZ3.zero_one_of_finite_alteration.{uE} := @_root_.OAI.CriticalZ3.zero_one_of_finite_alteration.{uE}
