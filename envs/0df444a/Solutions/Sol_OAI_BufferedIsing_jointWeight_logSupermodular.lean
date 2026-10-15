-- Prove2me | solution 1 for OAI.BufferedIsing.jointWeight_logSupermodular
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T22:35:09.872658+00:00
-- url     : https://prove2.me/submissions/5fc7b5fe-5e7f-47b7-b006-a08f9b69335d

-- Generated from openai/math@1581d4c lean/OAI/Probability/Ising/Marginals.lean:L13-L59
-- (upload_full_project.md Phase 4): solution for node OAI.BufferedIsing.jointWeight_logSupermodular. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_BufferedIsing
import Definitions.Def_OAI_Probability_Ising_Basic
import Definitions.Def_OAI_Probability_Ising_Colorings
import Definitions.Def_OAI_Probability_Ising_EdwardsSokal
import Definitions.Def_OAI_Probability_Ising_TwoSpin
import Definitions.Def_OAI_Probability_Ising_SpinCorrelation
import Definitions.Def_OAI_Probability_Ising_Marginals

-- ---- from OAI.Probability.Ising.Basic ----
namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

lemma weight_pos {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (σ : Spins n) : 0 < weight G h σ := Real.exp_pos _

lemma spin_modular (a b : Bool) :
    spin a + spin b = spin (a ⊓ b) + spin (a ⊔ b) := by
  cases a <;> cases b <;> norm_num [spin]

lemma spin_product_supermodular (a b c d : Bool) :
    spin a * spin b + spin c * spin d ≤
      spin (a ⊓ c) * spin (b ⊓ d) + spin (a ⊔ c) * spin (b ⊔ d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> norm_num [spin]

lemma energy_supermodular {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (σ ρ : Spins n) :
    energy G h σ + energy G h ρ ≤ energy G h (σ ⊓ ρ) + energy G h (σ ⊔ ρ) := by
  have he : (∑ e, (G.coupling e * spin (σ (G.left e)) * spin (σ (G.right e)) +
      G.coupling e * spin (ρ (G.left e)) * spin (ρ (G.right e)))) ≤
      ∑ e, (G.coupling e * spin ((σ ⊓ ρ) (G.left e)) * spin ((σ ⊓ ρ) (G.right e)) +
      G.coupling e * spin ((σ ⊔ ρ) (G.left e)) * spin ((σ ⊔ ρ) (G.right e))) := by
    apply Finset.sum_le_sum
    intro e _
    have H := mul_le_mul_of_nonneg_left
      (spin_product_supermodular (σ (G.left e)) (σ (G.right e))
        (ρ (G.left e)) (ρ (G.right e))) (G.coupling_nonneg e)
    simpa only [Pi.inf_apply, Pi.sup_apply, mul_add, mul_assoc] using H
  have hv : (∑ v, (h v * spin (σ v) + h v * spin (ρ v))) =
      ∑ v, (h v * spin ((σ ⊓ ρ) v) + h v * spin ((σ ⊔ ρ) v)) := by
    apply Finset.sum_congr rfl
    intro v _
    simpa only [Pi.inf_apply, Pi.sup_apply, mul_add] using
      congrArg (fun x => h v * x) (spin_modular (σ v) (ρ v))
  dsimp [energy]
  simp only [Finset.sum_add_distrib] at he hv
  dsimp at he hv
  linarith

lemma weight_logSupermodular {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (σ ρ : Spins n) :
    weight G h σ * weight G h ρ ≤ weight G h (σ ⊓ ρ) * weight G h (σ ⊔ ρ) := by
  unfold weight
  rw [← Real.exp_add, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (energy_supermodular G h σ ρ)

lemma agreesOn_inf {n : ℕ} {S : Finset (Fin n)} {σ ρ a b : Spins n}
    (ha : AgreesOn S σ a) (hb : AgreesOn S ρ b) : AgreesOn S (σ ⊓ ρ) (a ⊓ b) := by
  intro v hv
  simp only [Pi.inf_apply, ha v hv, hb v hv]

lemma agreesOn_sup {n : ℕ} {S : Finset (Fin n)} {σ ρ a b : Spins n}
    (ha : AgreesOn S σ a) (hb : AgreesOn S ρ b) : AgreesOn S (σ ⊔ ρ) (a ⊔ b) := by
  intro v hv
  simp only [Pi.sup_apply, ha v hv, hb v hv]

end BufferedIsing

end OAI

-- ---- from OAI.Probability.Ising.Marginals ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

/-- The four functions theorem preserves log-supermodularity under marginalization. -/
lemma jointWeight_logSupermodular {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n)) (τ a a' b b' : Spins n) :
    jointWeight G h I J F τ a b * jointWeight G h I J F τ a' b' ≤
      jointWeight G h I J F τ (a ⊓ a') (b ⊓ b') *
      jointWeight G h I J F τ (a ⊔ a') (b ⊔ b') := by
  classical
  unfold jointWeight constrainedSum
  apply four_functions_theorem_univ
  · intro σ
    dsimp only [Pi.zero_apply]
    split_ifs
    · exact (weight_pos G h σ).le
    · exact le_rfl
  · intro σ
    dsimp only [Pi.zero_apply]
    split_ifs
    · exact (weight_pos G h σ).le
    · exact le_rfl
  · intro σ
    dsimp only [Pi.zero_apply]
    split_ifs
    · exact (weight_pos G h σ).le
    · exact le_rfl
  · intro σ
    dsimp only [Pi.zero_apply]
    split_ifs
    · exact (weight_pos G h σ).le
    · exact le_rfl
  · intro σ ρ
    dsimp only
    by_cases hσ : AgreesOn I σ a ∧ AgreesOn J σ b ∧ AgreesOn F σ τ
    · by_cases hρ : AgreesOn I ρ a' ∧ AgreesOn J ρ b' ∧ AgreesOn F ρ τ
      · have hmin : AgreesOn I (σ ⊓ ρ) (a ⊓ a') ∧
            AgreesOn J (σ ⊓ ρ) (b ⊓ b') ∧ AgreesOn F (σ ⊓ ρ) τ := by
          exact ⟨agreesOn_inf hσ.1 hρ.1, agreesOn_inf hσ.2.1 hρ.2.1,
            by simpa using agreesOn_inf hσ.2.2 hρ.2.2⟩
        have hmax : AgreesOn I (σ ⊔ ρ) (a ⊔ a') ∧
            AgreesOn J (σ ⊔ ρ) (b ⊔ b') ∧ AgreesOn F (σ ⊔ ρ) τ := by
          exact ⟨agreesOn_sup hσ.1 hρ.1, agreesOn_sup hσ.2.1 hρ.2.1,
            by simpa using agreesOn_sup hσ.2.2 hρ.2.2⟩
        simpa only [ite_eq_left hσ, ite_eq_left hρ, ite_eq_left hmin, ite_eq_left hmax] using
          weight_logSupermodular G h σ ρ
      · simp only [ite_eq_right hρ, mul_zero]
        apply mul_nonneg <;> split_ifs <;> first | exact (weight_pos G h _).le | exact le_rfl
    · simp only [ite_eq_right hσ, zero_mul]
      apply mul_nonneg <;> split_ifs <;> first | exact (weight_pos G h _).le | exact le_rfl

end BufferedIsing

end OAI

-- ---- platform node ----
open OAI OAI.BufferedIsing
open scoped BigOperators Classical

theorem solution {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n)) (τ a a' b b' : Spins n) :
    jointWeight G h I J F τ a b * jointWeight G h I J F τ a' b' ≤
      jointWeight G h I J F τ (a ⊓ a') (b ⊓ b') *
      jointWeight G h I J F τ (a ⊔ a') (b ⊔ b') := by
  first
    | exact OAI.BufferedIsing.jointWeight_logSupermodular G h I J F τ a a' b b'
    | exact OAI.BufferedIsing.jointWeight_logSupermodular
    | (apply OAI.BufferedIsing.jointWeight_logSupermodular <;> assumption)
    | (intros; apply OAI.BufferedIsing.jointWeight_logSupermodular <;> assumption)
