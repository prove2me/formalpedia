-- Prove2me | solution 1 for OAI.BufferedIsing.DSS.mean_mono
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T22:52:54.751984+00:00
-- url     : https://prove2.me/submissions/031c2fd6-deee-462c-9c2e-daddcdbc0cff

-- Generated from openai/math@1581d4c lean/OAI/Probability/Ising/GibbsMeasure.lean:L124-L160
-- (upload_full_project.md Phase 4): solution for node OAI.BufferedIsing.DSS.mean_mono. The node keeps its source
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
import Definitions.Def_OAI_Probability_Ising_PinnedMarginal
import Definitions.Def_OAI_Probability_Ising_Covariance
import Definitions.Def_OAI_Probability_Ising_Contraction
import Definitions.Def_OAI_Probability_Ising_GibbsMeasure

-- ---- from OAI.Probability.Ising.GibbsMeasure ----
namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing.DSS

noncomputable section

variable {V : Type*} [Fintype V]

lemma mass_pos (J : V → V → ℝ) (h : V → ℝ) (σ : V → Bool) : 0 < mass J h σ :=
  Real.exp_pos _

lemma part_pos (J : V → V → ℝ) (h : V → ℝ) : 0 < part J h := by
  classical
  exact Finset.sum_pos (fun σ _ => mass_pos J h σ) Finset.univ_nonempty

lemma neg_one_le_sgn (b : Bool) : -1 ≤ sgn b := by cases b <;> norm_num [sgn]
lemma sgn_mono : Monotone sgn := by
  intro a b hab
  cases a <;> cases b <;> norm_num [sgn] at *
  exact (by decide : ¬ (true : Bool) ≤ false) hab

lemma average_add (J : V → V → ℝ) (h : V → ℝ) (f g : (V → Bool) → ℝ) :
    average J h (fun σ => f σ + g σ) = average J h f + average J h g := by
  simp [average, mul_add, Finset.sum_add_distrib, add_div]

lemma average_const (J : V → V → ℝ) (h : V → ℝ) (c : ℝ) :
    average J h (fun _ => c) = c := by
  unfold average
  rw [← Finset.sum_mul]
  exact mul_div_cancel_left₀ c (part_pos J h).ne'

lemma sgn_modular (a b : Bool) : sgn a + sgn b = sgn (a ⊓ b) + sgn (a ⊔ b) := by
  cases a <;> cases b <;> norm_num [sgn]

lemma sgn_product_supermodular (a b c d : Bool) :
    sgn a * sgn b + sgn c * sgn d ≤
      sgn (a ⊓ c) * sgn (b ⊓ d) + sgn (a ⊔ c) * sgn (b ⊔ d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> norm_num [sgn]

lemma mass_lattice (J : V → V → ℝ) (hJ : ∀ u v, 0 ≤ J u v) (h : V → ℝ)
    (σ τ : V → Bool) : mass J h σ * mass J h τ ≤ mass J h (σ ⊓ τ) * mass J h (σ ⊔ τ) := by
  rw [mass, mass, mass, mass, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have he : (∑ u, ∑ v, (J u v * sgn (σ u) * sgn (σ v) +
      J u v * sgn (τ u) * sgn (τ v))) ≤
      ∑ u, ∑ v, (J u v * sgn ((σ ⊓ τ) u) * sgn ((σ ⊓ τ) v) +
      J u v * sgn ((σ ⊔ τ) u) * sgn ((σ ⊔ τ) v)) := by
    apply Finset.sum_le_sum
    intro u _
    apply Finset.sum_le_sum
    intro v _
    have := mul_le_mul_of_nonneg_left
      (sgn_product_supermodular (σ u) (σ v) (τ u) (τ v)) (hJ u v)
    simpa only [Pi.inf_apply, Pi.sup_apply, mul_add, mul_assoc] using this
  have hf : (∑ v, (h v * sgn (σ v) + h v * sgn (τ v))) =
      ∑ v, (h v * sgn ((σ ⊓ τ) v) + h v * sgn ((σ ⊔ τ) v)) := by
    apply Finset.sum_congr rfl
    intro v _
    simpa only [Pi.inf_apply, Pi.sup_apply, mul_add] using
      congrArg (fun x => h v * x) (sgn_modular (σ v) (τ v))
  simp only [Finset.sum_add_distrib] at he hf
  dsimp at he hf
  dsimp [hamiltonian]
  linarith

lemma hamiltonian_field_add (J : V → V → ℝ) (h k : V → ℝ) (σ : V → Bool) :
    hamiltonian J (h + k) σ = hamiltonian J h σ + ∑ v, k v * sgn (σ v) := by
  simp only [hamiltonian, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

lemma mass_field_add (J : V → V → ℝ) (h k : V → ℝ) (σ : V → Bool) :
    mass J (h + k) σ = mass J h σ * Real.exp (∑ v, k v * sgn (σ v)) := by
  simp only [mass, hamiltonian_field_add, Real.exp_add]

lemma mean_mono (J : V → V → ℝ) (hJ : ∀ u v, 0 ≤ J u v)
    (h k : V → ℝ) (hhk : h ≤ k) (o : V) : mean J h o ≤ mean J k o := by
  classical
  let w := mass J h
  let r : (V → Bool) → ℝ := fun σ => Real.exp (∑ v, (k v - h v) * sgn (σ v))
  let f : (V → Bool) → ℝ := fun σ => sgn (σ o) + 1
  have hf0 : ∀ σ, 0 ≤ f σ := fun σ => by dsimp [f]; linarith [neg_one_le_sgn (σ o)]
  have hf : Monotone f := fun σ τ hστ => by
    dsimp [f]
    linarith [sgn_mono (hστ o)]
  have hr : Monotone r := by
    intro σ τ hστ
    apply Real.exp_le_exp.mpr
    apply Finset.sum_le_sum
    intro v _
    exact mul_le_mul_of_nonneg_left (sgn_mono (hστ v)) (sub_nonneg.mpr (hhk v))
  have H := fkg f r w (fun σ => (mass_pos J h σ).le) hf0
    (fun σ => (Real.exp_pos _).le) hf hr (mass_lattice J hJ h)
  have hw : ∀ σ, mass J k σ = w σ * r σ := by
    intro σ
    have hk : k = h + (k - h) := by ext v; simp
    conv_lhs => rw [hk, mass_field_add]
    rfl
  have hz : (∑ σ, w σ * r σ) = part J k := by simp_rw [← hw]; rfl
  have H' : average J h f ≤ average J k f := by
    rw [average, average, div_le_div_iff₀ (part_pos J h) (part_pos J k)]
    rw [← hz]
    have hn : (∑ σ, mass J k σ * f σ) = ∑ σ, w σ * (f σ * r σ) := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [hw]
      ring
    rw [hn]
    simpa only [w, part, mul_comm] using H
  dsimp [f] at H'
  rw [average_add, average_add, average_const, average_const] at H'
  exact (add_le_add_iff_right 1).mp H'

end

end BufferedIsing.DSS

end OAI

-- ---- platform node ----
open OAI OAI.BufferedIsing OAI.BufferedIsing.DSS
open scoped BigOperators Classical
variable {V : Type*} [Fintype V]

theorem solution (J : V → V → ℝ) (hJ : ∀ u v, 0 ≤ J u v)
    (h k : V → ℝ) (hhk : h ≤ k) (o : V) : mean J h o ≤ mean J k o := by
  first
    | exact OAI.BufferedIsing.DSS.mean_mono J hJ h k hhk o
    | exact OAI.BufferedIsing.DSS.mean_mono
    | (apply OAI.BufferedIsing.DSS.mean_mono <;> assumption)
    | (intros; apply OAI.BufferedIsing.DSS.mean_mono <;> assumption)
