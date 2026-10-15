-- Prove2me | solution 1 for OAI.BufferedIsing.interactionGraph_coupling
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T22:49:57.337666+00:00
-- url     : https://prove2.me/submissions/e1ceac47-cc9c-45fd-8999-24973bfd1e13

-- Generated from openai/math@1581d4c lean/OAI/Probability/Ising/Contraction.lean:L274-L290
-- (upload_full_project.md Phase 4): solution for node OAI.BufferedIsing.interactionGraph_coupling. The node keeps its source
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

-- ---- from OAI.Probability.Ising.Colorings ----
namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

lemma spin_sq (s : Bool) : spin s * spin s = 1 := by
  cases s <;> norm_num [spin]

end BufferedIsing

end OAI

-- ---- from OAI.Probability.Ising.Contraction ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

lemma sum_nonloop {V E : Type*} [Fintype E] (P : PairInteraction V E) (f : E → ℝ) :
    (∑ e : NonloopEdge P, f e.val) = ∑ e : E, if P.left e ≠ P.right e then f e else 0 := by
  classical
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (fun e => by simp only [Finset.mem_filter,
    Finset.mem_univ, true_and]) f).symm

lemma interactionEnergy_relabel {V E : Type*} [Fintype V] [Fintype E]
    (P : PairInteraction V E) (h : V → ℝ) (σ : V → Bool) :
    energy (interactionGraph P) (fun v => h ((Fintype.equivFin V).symm v))
      (fun v => σ ((Fintype.equivFin V).symm v)) =
      interactionEnergy P h σ - interactionLoopConstant P := by
  classical
  unfold energy interactionGraph interactionEnergy interactionLoopConstant
  simp only [Equiv.symm_apply_apply]
  rw [(Fintype.equivFin (NonloopEdge P)).symm.sum_comp (fun e : NonloopEdge P =>
      P.coupling e.val * spin (σ (P.left e.val)) * spin (σ (P.right e.val))),
    (Fintype.equivFin V).symm.sum_comp (fun v => h v * spin (σ v))]
  rw [sum_nonloop P (fun e => P.coupling e * spin (σ (P.left e)) * spin (σ (P.right e)))]
  have he : (∑ e : E, P.coupling e * spin (σ (P.left e)) * spin (σ (P.right e))) =
      (∑ e : E, if P.left e ≠ P.right e then
        P.coupling e * spin (σ (P.left e)) * spin (σ (P.right e)) else 0) +
        ∑ e : E, if P.left e = P.right e then P.coupling e else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : P.left e = P.right e
    · simp only [he, ne_eq, not_true_eq_false, ite_false, ite_true, zero_add]
      rw [mul_assoc, spin_sq, mul_one]
    · simp [he]
  rw [he]
  ring

lemma interactionWeight_relabel {V E : Type*} [Fintype V] [Fintype E]
    (P : PairInteraction V E) (h : V → ℝ) (σ : V → Bool) :
    weight (interactionGraph P) (fun v => h ((Fintype.equivFin V).symm v))
      (fun v => σ ((Fintype.equivFin V).symm v)) =
      Real.exp (-interactionLoopConstant P) * interactionWeight P h σ := by
  unfold weight interactionWeight
  rw [interactionEnergy_relabel, ← Real.exp_add]
  congr 1
  ring

/-- Marginal tables commute with a bijective change of vertex labels. -/
lemma pairTable_relabel {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (e : V ≃ W) (f : (V → Bool) → ℝ)
    (u v : V) (s t : Bool) :
    pairTable (fun σ : W → Bool => f (fun x => σ (e x))) (e u) (e v) s t =
      pairTable f u v s t := by
  classical
  unfold pairTable
  let E : (V → Bool) ≃ (W → Bool) := Equiv.arrowCongr e (Equiv.refl Bool)
  rw [← E.sum_comp]
  simp only [E, Equiv.arrowCongr_apply, Function.comp_apply, Equiv.refl_apply,
    Equiv.symm_apply_apply]

lemma pairTable_scale {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → Bool) → ℝ) (c : ℝ) (u v : V) (s t : Bool) :
    pairTable (fun σ => c * f σ) u v s t = c * pairTable f u v s t := by
  classical
  unfold pairTable
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs <;> simp

lemma tableCoupling_scale (w : Bool → Bool → ℝ) (hw : ∀ s t, 0 < w s t)
    (c : ℝ) (hc : 0 < c) : tableCoupling (fun s t => c * w s t) = tableCoupling w := by
  simp only [tableCoupling, Real.log_mul hc.ne' (hw _ _).ne']
  ring

lemma pairTable_pos_of_weight_pos {V : Type*} [Fintype V] [DecidableEq V]
    (W : (V → Bool) → ℝ) (hW : ∀ σ, 0 < W σ) (u v : V) (huv : u ≠ v)
    (s t : Bool) : 0 < pairTable W u v s t := by
  classical
  unfold pairTable
  apply Finset.sum_pos'
  · intro σ _
    split_ifs
    · exact (hW σ).le
    · exact le_rfl
  · refine ⟨fun x => if x = u then s else t, Finset.mem_univ _, ?_⟩
    simp only [ite_eq_right (Ne.symm huv), and_self, ite_true]
    exact hW _

lemma interactionGraph_pairTable {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (P : PairInteraction V E) (h : V → ℝ) (u v : V) (s t : Bool) :
    pairTable (weight (interactionGraph P) (fun x => h ((Fintype.equivFin V).symm x)))
      (Fintype.equivFin V u) (Fintype.equivFin V v) s t =
      Real.exp (-interactionLoopConstant P) * pairTable (interactionWeight P h) u v s t := by
  classical
  have H := pairTable_relabel (Fintype.equivFin V).symm
    (weight (interactionGraph P) (fun x => h ((Fintype.equivFin V).symm x)))
    (Fintype.equivFin V u) (Fintype.equivFin V v) s t
  simp only [Equiv.symm_apply_apply] at H
  rw [← H]
  simp_rw [interactionWeight_relabel]
  exact pairTable_scale _ _ _ _ _ _

lemma interactionGraph_coupling {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (P : PairInteraction V E) (h : V → ℝ) (u v : V) (huv : u ≠ v) :
    tableCoupling (pairTable
      (weight (interactionGraph P) (fun x => h ((Fintype.equivFin V).symm x)))
      (Fintype.equivFin V u) (Fintype.equivFin V v)) =
      tableCoupling (pairTable (interactionWeight P h) u v) := by
  classical
  have H : pairTable
      (weight (interactionGraph P) (fun x => h ((Fintype.equivFin V).symm x)))
      (Fintype.equivFin V u) (Fintype.equivFin V v) =
      fun s t => Real.exp (-interactionLoopConstant P) *
        pairTable (interactionWeight P h) u v s t := by
    funext s t
    exact interactionGraph_pairTable P h u v s t
  rw [H]
  exact tableCoupling_scale _
    (pairTable_pos_of_weight_pos _ (fun σ => Real.exp_pos _) u v huv) _ (Real.exp_pos _)

end BufferedIsing

end OAI

-- ---- platform node ----
open OAI OAI.BufferedIsing
open scoped BigOperators Classical

theorem solution {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (P : PairInteraction V E) (h : V → ℝ) (u v : V) (huv : u ≠ v) :
    tableCoupling (pairTable
      (weight (interactionGraph P) (fun x => h ((Fintype.equivFin V).symm x)))
      (Fintype.equivFin V u) (Fintype.equivFin V v)) =
      tableCoupling (pairTable (interactionWeight P h) u v) := by
  first
    | exact OAI.BufferedIsing.interactionGraph_coupling P h u v huv
    | exact OAI.BufferedIsing.interactionGraph_coupling
    | (apply OAI.BufferedIsing.interactionGraph_coupling <;> assumption)
    | (intros; apply OAI.BufferedIsing.interactionGraph_coupling <;> assumption)
