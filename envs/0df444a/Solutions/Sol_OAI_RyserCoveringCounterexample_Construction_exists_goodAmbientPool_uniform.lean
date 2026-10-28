-- Prove2me | solution 1 for OAI.RyserCoveringCounterexample.Construction.exists_goodAmbientPool_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T04:29:01.607645+00:00
-- url     : https://prove2.me/submissions/0225419c-709c-462d-85b7-d65ac0d5d774

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIW2RY002
import Theorems.Thm_OAI_RyserCoveringCounterexample_LineCover_goodLineCover_of_goodCounts_goodTuples
import Theorems.Thm_OAI_RyserCoveringCounterexample_Selection_compatible_selection_uniform

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_AmbientDeletionNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.Construction

theorem ambientDeletionDelta_pos (s K : ℕ) : 0 < ambientDeletionDelta s K :=
  Real.exp_pos _

end RyserCoveringCounterexample.Construction

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_LinearPlacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {F : Type*} [Field F]

namespace PlaneLinearMap

theorem apply_injective (M : PlaneLinearMap F) : Function.Injective M.apply :=
  M.toEquiv.injective

end PlaneLinearMap

section Subfield

variable {k : Type*} [Field k]

theorem mapPoint_injective (σ : k →+* F) : Function.Injective (mapPoint σ) := by
  intro p q hpq
  apply Prod.ext
  · exact σ.injective (congrArg Prod.fst hpq)
  · exact σ.injective (congrArg Prod.snd hpq)

end Subfield

end RyserCoveringCounterexample.Construction

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Probability_Finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample

namespace FiniteLaw

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem expectation_add (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    μ.expectation (fun ω => f ω + g ω) = μ.expectation f + μ.expectation g := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

theorem expectation_sub (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    μ.expectation (fun ω => f ω - g ω) = μ.expectation f - μ.expectation g := by
  simp [expectation, mul_sub, Finset.sum_sub_distrib]

theorem prob_nonneg (μ : FiniteLaw Ω) (P : Ω → Prop) : 0 ≤ μ.prob P := by
  classical
  exact Finset.sum_nonneg fun ω _ => by split_ifs <;> simp [μ.nonneg]

theorem prob_mono (μ : FiniteLaw Ω) {P Q : Ω → Prop} (hPQ : ∀ ω, P ω → Q ω) :
    μ.prob P ≤ μ.prob Q := by
  classical
  apply Finset.sum_le_sum
  intro ω _
  by_cases hp : P ω
  · simp [hp, hPQ ω hp]
  · by_cases hq : Q ω <;> simp [hp, hq, μ.nonneg ω]

theorem prob_union_le (μ : FiniteLaw Ω) (P Q : Ω → Prop) :
    μ.prob (fun ω => P ω ∨ Q ω) ≤ μ.prob P + μ.prob Q := by
  classical
  rw [prob, prob, prob, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hp : P ω <;> by_cases hq : Q ω <;> simp [hp, hq, μ.nonneg]

theorem eq_uniform_of_weight_eq [Nonempty Ω] (mu : FiniteLaw Ω)
    (h : ∀ x y, mu.weight x = mu.weight y) : mu = uniform Ω := by
  apply ext_weight
  funext x
  change mu.weight x = (Fintype.card Ω : ℝ)⁻¹
  have hN : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hsum : (Fintype.card Ω : ℝ) * mu.weight x = 1 := by
    calc
      _ = ∑ y : Ω, mu.weight x := by simp
      _ = ∑ y : Ω, mu.weight y :=
        Finset.sum_congr rfl (fun y _ => (h y x).symm)
      _ = 1 := mu.total
  calc
    mu.weight x = (Fintype.card Ω : ℝ)⁻¹ *
        ((Fintype.card Ω : ℝ) * mu.weight x) := by
      rw [← mul_assoc, inv_mul_cancel₀ hN, one_mul]
    _ = (Fintype.card Ω : ℝ)⁻¹ := by rw [hsum, mul_one]

end FiniteLaw

end RyserCoveringCounterexample

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_DeletionDefinitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

variable {P : Type*} [DecidableEq P]

variable {shapes : Finset (Finset P)} {D n : ℕ}

variable [instFintypeP : Fintype P]

theorem mem_survivors_active {ignore : Finset (Finset P)}
    {ω : Fin n → Outcome shapes D} {x : P} :
    x ∈ survivors ignore ω ↔ ∀ L ∈ selected ω \ ignore, x ∉ L := by
  rw [mem_survivors]
  constructor
  · intro h L hL hxL
    rcases Finset.mem_sdiff.mp hL with ⟨hsel, hI⟩
    rcases mem_selected.mp hsel with ⟨i, s, hs, rfl⟩
    exact h i (mem_deleted.mpr ⟨s, hs, hI, hxL⟩)
  · intro h i hx
    rcases mem_deleted.mp hx with ⟨s, hs, hI, hxs⟩
    exact h s.val (Finset.mem_sdiff.mpr
      ⟨mem_selected.mpr ⟨i, s, hs, rfl⟩, hI⟩) hxs

theorem survivors_mono_ignore {ignore larger : Finset (Finset P)}
    (h : ignore ⊆ larger) (ω : Fin n → Outcome shapes D) :
    survivors ignore ω ⊆ survivors larger ω := by
  intro x hx
  apply mem_survivors.mpr
  intro i hxi
  rcases mem_deleted.mp hxi with ⟨s, hs, hnot, hxs⟩
  exact mem_survivors.mp hx i
    (mem_deleted.mpr ⟨s, hs, fun hI => hnot (h hI), hxs⟩)

theorem survivors_insert_eq_of_not_selected
    {ignore : Finset (Finset P)} {ω : Fin n → Outcome shapes D}
    {L : Finset P} (hL : L ∉ selected ω) :
    survivors (insert L ignore) ω = survivors ignore ω := by
  ext x
  rw [mem_survivors_active, mem_survivors_active,
    Finset.sdiff_insert_of_notMem hL ignore]

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Probability_Product
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.FiniteLaw

section ProductCoordinates

variable {I : Type*} [Fintype I] [DecidableEq I]
  {A : I → Type*} [∀ i, Fintype (A i)]

theorem expectation_pi_coordinate (μ : ∀ i, FiniteLaw (A i))
    (i : I) (f : A i → ℝ) :
    (pi μ).expectation (fun ω => f (ω i)) = (μ i).expectation f := by
  classical
  let g : ∀ j, A j → ℝ := fun j a => if h : j = i then f (h ▸ a) else 1
  have hg (ω : ∀ j, A j) : (∏ j, g j (ω j)) = f (ω i) := by
    dsimp only [g]
    simp only [Fintype.prod_dite_eq']
  have he (j : I) : (μ j).expectation (g j) =
      if h : j = i then (μ i).expectation f else 1 := by
    by_cases h : j = i
    · subst j
      simp [g]
    · simp [g, h, expectation_const]
  calc
    _ = (pi μ).expectation (fun ω => ∏ j, g j (ω j)) := by
      congr 1
      funext ω
      exact (hg ω).symm
    _ = ∏ j, (μ j).expectation (g j) := expectation_pi_product μ g
    _ = _ := by simp_rw [he]; simp

theorem prob_pi_coordinate (μ : ∀ i, FiniteLaw (A i))
    (i : I) (P : A i → Prop) :
    (pi μ).prob (fun ω => P (ω i)) = (μ i).prob P := by
  classical
  rw [prob_eq_expectation, prob_eq_expectation]
  exact expectation_pi_coordinate μ i (fun a => if P a then 1 else 0)

end ProductCoordinates

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem map_weight_eq_prob (μ : FiniteLaw Ω) (f : Ω → Γ) (γ : Γ) :
    (map μ f).weight γ = μ.prob (fun ω => f ω = γ) := rfl

theorem map_uniform_equiv [Nonempty Ω] [Nonempty Γ] (e : Ω ≃ Γ) :
    (uniform Ω).map e = uniform Γ := by
  classical
  apply ext_weight
  funext y
  simp [map, uniform, ← e.eq_symm_apply, Fintype.card_congr e]

theorem pi_uniform {I : Type*} [Fintype I] [DecidableEq I] {A : I → Type*}
    [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] :
    pi (fun i => uniform (A i)) = uniform (∀ i, A i) :=
  eq_uniform_of_weight_eq (pi (fun i => uniform (A i))) (fun _ _ => rfl)

end RyserCoveringCounterexample.FiniteLaw

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_Process
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {shapes : Finset (Finset (Point F))} {D n : ℕ}

namespace DeletionProcess

variable {δ : ℝ} (process : DeletionProcess F D δ)

theorem point_survival_ge (x : Point F) :
    δ ≤ process.law.prob (fun ω => x ∈ process.survivorSet ω) := by
  change δ ≤ (FiniteLaw.pi process.trials).prob (fun ω => x ∈ survivors ∅ ω)
  rw [process.uniformSurvival]
  exact process.survivalLower

end DeletionProcess
end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_GroupPlacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [Fintype k]

theorem groupAltered_card (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (i : ConfigurationGroup σ) :
    (groupAltered σ u v huv i).card = Fintype.card k - 1 :=
  card_alteredDirections σ _

theorem embeddedDirections_card (σ : k →+* F) :
    (embeddedDirections σ).card = Fintype.card k + 1 := by
  rw [embeddedDirections, Finset.card_image_of_injective _ (mapDirection_injective σ),
    Finset.card_univ, Fintype.card_option]

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_GroupBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F]
variable [instDecidableEqk : DecidableEq k] [instDecidableEqF : DecidableEq F] [Fintype k]

theorem groupConflict_card_le (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (i : ConfigurationGroup σ) :
    (groupConflict σ u v huv i).card ≤ Fintype.card k + 1 := by
  classical
  cases i with
  | none => exact le_of_eq (embeddedDirections_card σ)
  | some c =>
      by_cases hc : c = 1
      · simpa [groupConflict, hc] using le_of_eq (embeddedDirections_card σ)
      · simp only [groupConflict, ite_eq_right hc, groupAltered_card]
        omega

theorem groupPoints_card (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (i : ConfigurationGroup σ) :
    (groupPoints σ u v huv i).card = Fintype.card k ^ 2 := by
  have hinj : Function.Injective
      (fun w : Point k => (groupPlacement σ u v huv i).apply (mapPoint σ w)) :=
    (groupPlacement σ u v huv i).apply_injective.comp (mapPoint_injective σ)
  rw [groupPoints, Finset.card_image_of_injective _ hinj, Finset.card_univ]
  exact card_point

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Probability_ProductMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace RyserCoveringCounterexample.FiniteLaw

theorem map_map {Ω Γ Λ : Type*} [Fintype Ω] [Fintype Γ] [Fintype Λ]
    (mu : FiniteLaw Ω) (f : Ω → Γ) (g : Γ → Λ) :
    (mu.map f).map g = mu.map (g ∘ f) := by
  apply ext_weight
  funext z
  simp only [map_weight_eq_prob, prob_map, Function.comp_apply]

theorem map_pi {I : Type*} [Fintype I] [DecidableEq I]
    {A B : I → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (mu : ∀ i, FiniteLaw (A i)) (f : ∀ i, A i → B i) :
    (pi mu).map (fun a i => f i (a i)) = pi (fun i => (mu i).map (f i)) := by
  apply ext_weight
  funext b
  rw [map_weight_eq_prob]
  calc
    (pi mu).prob (fun a => (fun i => f i (a i)) = b) =
        (pi mu).prob (fun a => ∀ i, f i (a i) = b i) := by
      congr 1
      funext a
      exact propext ⟨fun h i => congrFun h i, fun h => funext h⟩
    _ = ∏ i, (mu i).prob (fun a => f i a = b i) :=
      prob_pi mu (fun i a => f i a = b i)
    _ = (pi (fun i => (mu i).map (f i))).weight b := by
      simp only [pi_weight, map_weight_eq_prob]

end RyserCoveringCounterexample.FiniteLaw

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_PoolThinGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {F : Type*} [Field F] [Fintype F] [instDecidableEqF : DecidableEq F]

theorem badShifts_eq_biUnion (W : Finset (Point F)) (S : Finset (Direction F))
    (p : Point F) (ell : AffineLine F) :
    badShifts W S p ell = W.biUnion (fun w => S.biUnion (fun d =>
      (linePoints ell ∩ linePoints (lineThrough d p)).image (fun y => y - w))) := by
  ext b
  constructor
  · intro hb
    obtain ⟨w, hw, d, hd, hbell, hbd⟩ := (mem_badShifts W S p ell b).mp hb
    apply Finset.mem_biUnion.mpr
    refine ⟨w, hw, Finset.mem_biUnion.mpr ⟨d, hd, ?_⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨b + w, Finset.mem_inter.mpr ⟨?_, ?_⟩, by simp⟩
    · exact (mem_linePoints _ _).mpr hbell
    · exact (mem_linePoints _ _).mpr hbd
  · intro hb
    obtain ⟨w, hw, hb⟩ := Finset.mem_biUnion.mp hb
    obtain ⟨d, hd, hb⟩ := Finset.mem_biUnion.mp hb
    obtain ⟨y, hy, hyb⟩ := Finset.mem_image.mp hb
    apply (mem_badShifts W S p ell b).mpr
    have hby : b + w = y := by rw [← hyb]; simp
    refine ⟨w, hw, d, hd, ?_, ?_⟩
    · rw [hby]
      exact (mem_linePoints _ _).mp (Finset.mem_inter.mp hy).1
    · rw [hby]
      exact (mem_linePoints _ _).mp (Finset.mem_inter.mp hy).2

theorem badShifts_card_le (W : Finset (Point F)) (S : Finset (Direction F))
    (p : Point F) (ell : AffineLine F) (hp : ¬ Incidence p ell) :
    (badShifts W S p ell).card ≤ W.card * S.card := by
  have hpoint (d : Direction F) :
      (linePoints ell ∩ linePoints (lineThrough d p)).card ≤ 1 := by
    apply card_linePoints_inter_le_one
    intro heq
    exact hp (heq.symm ▸ incidence_lineThrough d p)
  rw [badShifts_eq_biUnion]
  calc
    _ ≤ ∑ w ∈ W, (S.biUnion (fun d =>
        (linePoints ell ∩ linePoints (lineThrough d p)).image (fun y => y - w))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ W, S.card := by
      apply Finset.sum_le_sum
      intro w hw
      calc
        _ ≤ ∑ d ∈ S,
            ((linePoints ell ∩ linePoints (lineThrough d p)).image (fun y => y - w)).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _d ∈ S, 1 := Finset.sum_le_sum fun d _ =>
          Finset.card_image_le.trans (hpoint d)
        _ = S.card := by simp
    _ = W.card * S.card := by simp

theorem uniform_prob_shiftHits_le (W : Finset (Point F)) (S : Finset (Direction F))
    (p : Point F) (ell : AffineLine F) (hp : ¬ Incidence p ell) :
    (FiniteLaw.uniform (Point F)).prob (ShiftHits W S p ell) ≤
      (W.card : ℝ) * S.card / (Fintype.card F : ℝ) ^ 2 := by
  classical
  rw [FiniteLaw.uniform_prob]
  change ((badShifts W S p ell).card : ℝ) / Fintype.card (Point F) ≤ _
  rw [card_point, Nat.cast_pow]
  apply div_le_div_of_nonneg_right
  · exact_mod_cast badShifts_card_le W S p ell hp
  · positivity

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_PoolThinProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Construction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

variable {G : Type*} [Fintype G] [DecidableEq G] {K : ℕ}

theorem uniform_prob_poolGroupBad_le
    (W : Finset (Point F)) (S : Finset (Direction F))
    (p : Point F) (ell : AffineLine F) (hp : ¬ Incidence p ell) :
    (FiniteLaw.uniform (Fin K → Point F)).prob (poolGroupBad W S p ell) ≤
      (K : ℝ) * W.card * S.card / (Fintype.card F : ℝ) ^ 2 := by
  calc
    _ ≤ ∑ j : Fin K, (FiniteLaw.uniform (Fin K → Point F)).prob
        (fun a => ShiftHits W S p ell (a j)) :=
      FiniteLaw.prob_exists_le _ _
    _ = ∑ _j : Fin K, (FiniteLaw.uniform (Point F)).prob
        (ShiftHits W S p ell) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← FiniteLaw.pi_uniform]
      exact FiniteLaw.prob_pi_coordinate
        (fun _ : Fin K => FiniteLaw.uniform (Point F)) j (ShiftHits W S p ell)
    _ ≤ ∑ _j : Fin K,
        (W.card : ℝ) * S.card / (Fintype.card F : ℝ) ^ 2 :=
      Finset.sum_le_sum (fun _ _ => uniform_prob_shiftHits_le W S p ell hp)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

theorem uniform_prob_poolGroupBad_le_of_card
    (W : Finset (Point F)) (S : Finset (Direction F))
    (w s : ℕ) (hW : W.card ≤ w) (hS : S.card ≤ s)
    (p : Point F) (ell : AffineLine F) (hp : ¬ Incidence p ell) :
    (FiniteLaw.uniform (Fin K → Point F)).prob (poolGroupBad W S p ell) ≤
      (K : ℝ) * w * s / (Fintype.card F : ℝ) ^ 2 := by
  refine (uniform_prob_poolGroupBad_le W S p ell hp).trans ?_
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  exact_mod_cast Nat.mul_le_mul (Nat.mul_le_mul_left K hW) hS

theorem poolThinLaw_prob_all_bad_le
    (W : G → Finset (Point F)) (S : G → Finset (Direction F))
    (w s : ℕ) (hW : ∀ i, (W i).card ≤ w) (hS : ∀ i, (S i).card ≤ s)
    (p : Point F) (ell : AffineLine F) (hp : ¬ Incidence p ell) (T : Finset G) :
    (poolThinLaw (F := F) G K).prob
        (fun ω => ∀ i ∈ T, poolGroupBad (W i) (S i) p ell (ω i)) ≤
      ((K : ℝ) * w * s / (Fintype.card F : ℝ) ^ 2) ^ T.card := by
  let b : ℝ := (K : ℝ) * w * s / (Fintype.card F : ℝ) ^ 2
  change (FiniteLaw.pi (fun _ : G => FiniteLaw.uniform (Fin K → Point F))).prob
    (fun ω => ∀ i, i ∈ T → poolGroupBad (W i) (S i) p ell (ω i)) ≤ b ^ T.card
  rw [FiniteLaw.prob_pi (fun _ : G => FiniteLaw.uniform (Fin K → Point F))
    (fun i a => i ∈ T → poolGroupBad (W i) (S i) p ell a)]
  calc
    _ ≤ ∏ i : G, if i ∈ T then b else 1 := by
      apply Finset.prod_le_prod
      · intro i _
        exact FiniteLaw.prob_nonneg _ _
      · intro i _
        by_cases hi : i ∈ T
        · simpa [hi] using
            uniform_prob_poolGroupBad_le_of_card (K := K)
              (W i) (S i) w s (hW i) (hS i) p ell hp
        · simp [hi]
    _ = b ^ T.card := by
      rw [Finset.prod_ite_mem_eq]
      exact Finset.prod_const b

theorem poolThinLaw_prob_six_bad_le
    (W : G → Finset (Point F)) (S : G → Finset (Direction F))
    (w s : ℕ) (hW : ∀ i, (W i).card ≤ w) (hS : ∀ i, (S i).card ≤ s)
    (p : Point F) (ell : AffineLine F) (hp : ¬ Incidence p ell) :
    (poolThinLaw (F := F) G K).prob
        (fun ω => 6 ≤ (poolBadGroups W S p ell ω).card) ≤
      (Fintype.card G : ℝ) ^ 6 *
        ((K : ℝ) * w * s / (Fintype.card F : ℝ) ^ 2) ^ 6 := by
  let b : ℝ := (K : ℝ) * w * s / (Fintype.card F : ℝ) ^ 2
  have hb : 0 ≤ b := by dsimp [b]; positivity
  let C : Finset (Finset G) := (Finset.univ : Finset G).powersetCard 6
  change (poolThinLaw (F := F) G K).prob
    (fun ω => 6 ≤ (poolBadGroups W S p ell ω).card) ≤
      (Fintype.card G : ℝ) ^ 6 * b ^ 6
  calc
    _ ≤ (poolThinLaw (F := F) G K).prob
        (fun ω => ∃ T : ↥C, ∀ i ∈ T.val, poolGroupBad (W i) (S i) p ell (ω i)) := by
      apply FiniteLaw.prob_mono
      intro ω hω
      obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq hω
      refine ⟨⟨T, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩⟩, ?_⟩
      intro i hi
      exact (Finset.mem_filter.mp (hT hi)).2
    _ ≤ ∑ T : ↥C, (poolThinLaw (F := F) G K).prob
        (fun ω => ∀ i ∈ T.val, poolGroupBad (W i) (S i) p ell (ω i)) :=
      FiniteLaw.prob_exists_le _ _
    _ ≤ ∑ _T : ↥C, b ^ 6 := by
      apply Finset.sum_le_sum
      intro T _
      have hT := poolThinLaw_prob_all_bad_le (K := K) W S w s hW hS p ell hp T.val
      have hcard : T.val.card = 6 := (Finset.mem_powersetCard.mp T.property).2
      simpa only [hcard] using hT
    _ = ((Fintype.card G).choose 6 : ℝ) * b ^ 6 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
        C, Finset.card_powersetCard, nsmul_eq_mul]
    _ ≤ (Fintype.card G : ℝ) ^ 6 * b ^ 6 := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hb _)
      exact_mod_cast Nat.choose_le_pow (Fintype.card G) 6

theorem prob_not_poolThin_le
    (W : G → Finset (Point F)) (S : G → Finset (Direction F))
    (w s : ℕ) (hW : ∀ i, (W i).card ≤ w) (hS : ∀ i, (S i).card ≤ s) :
    (poolThinLaw (F := F) G K).prob (fun ω => ¬ PoolThin W S ω) ≤
      (Fintype.card F : ℝ) ^ 3 * ((Fintype.card F : ℝ) + 1) *
        (Fintype.card G : ℝ) ^ 6 *
          ((K : ℝ) * w * s / (Fintype.card F : ℝ) ^ 2) ^ 6 := by
  let b : ℝ := (K : ℝ) * w * s / (Fintype.card F : ℝ) ^ 2
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hB : 0 ≤ (Fintype.card G : ℝ) ^ 6 * b ^ 6 := by positivity
  change (poolThinLaw (F := F) G K).prob (fun ω => ¬ PoolThin W S ω) ≤
    (Fintype.card F : ℝ) ^ 3 * ((Fintype.card F : ℝ) + 1) *
      (Fintype.card G : ℝ) ^ 6 * b ^ 6
  calc
    _ ≤ (poolThinLaw (F := F) G K).prob
        (fun ω => ∃ z : Point F × AffineLine F,
          ¬ Incidence z.1 z.2 ∧ 6 ≤ (poolBadGroups W S z.1 z.2 ω).card) := by
      apply FiniteLaw.prob_mono
      intro ω hω
      by_contra hn
      apply hω
      intro p ell hp
      by_contra hcard
      apply hn
      refine ⟨(p, ell), hp, ?_⟩
      change 6 ≤ (poolBadGroups W S p ell ω).card
      omega
    _ ≤ ∑ z : Point F × AffineLine F, (poolThinLaw (F := F) G K).prob
        (fun ω => ¬ Incidence z.1 z.2 ∧
          6 ≤ (poolBadGroups W S z.1 z.2 ω).card) :=
      FiniteLaw.prob_exists_le _ _
    _ ≤ ∑ _z : Point F × AffineLine F, (Fintype.card G : ℝ) ^ 6 * b ^ 6 := by
      apply Finset.sum_le_sum
      intro z _
      by_cases hp : Incidence z.1 z.2
      · simpa [hp] using hB
      · simpa [hp] using
          poolThinLaw_prob_six_bad_le (K := K) W S w s hW hS z.1 z.2 hp
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        card_direction, Nat.cast_mul,
        Nat.cast_add, Nat.cast_one, nsmul_eq_mul]
      ring

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_PoolLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Selection

variable (F : Type*) [instFieldF : Field F] [instFintypeF : Fintype F] [instDecidableEqF : DecidableEq F] (n K : ℕ)

theorem poolLaw_eq_uniform : poolLaw F n K = FiniteLaw.uniform (Pool F n K) := let _ := instDecidableEqF;
  FiniteLaw.pi_uniform

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_AmbientDeletionPoolLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F] [instFintypeK : Fintype k] [Fintype F]
  [instDecidableEqK : DecidableEq k] [DecidableEq F]

theorem poolThinLaw_map_ambientFlatPoolEquiv (σ : k →+* F) (K : ℕ) :
    (poolThinLaw (F := F) (ConfigurationGroup σ) K).map (ambientFlatPoolEquiv σ K) =
      Selection.poolLaw F (Fintype.card (ConfigurationGroup σ)) K :=
  let _ := instFintypeK; let _ := instDecidableEqK; by
  rw [poolThinLaw, FiniteLaw.pi_uniform, FiniteLaw.map_uniform_equiv,
    Selection.poolLaw_eq_uniform]

theorem poolThinLaw_map_ambientPoolConfig (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ) :
    (poolThinLaw (F := F) (ConfigurationGroup σ) K).map
        (ambientPoolConfig σ u v huv a ha K) =
      FiniteLaw.pi (ambientTrials σ u v huv a ha K) := by
  let f : (Fin (ambientTrialCount σ K) → Point F) →
      (Fin (ambientTrialCount σ K) →
        LineCover.Outcome (ambientShapes F) (ambientDeletionConstant (Fintype.card k) K)) :=
    fun b t => ambientTrialOutcome σ
      (groupPlacement σ u v huv (ambientPosition σ K t).1) a ha K (b t)
  have hconfig : ambientPoolConfig σ u v huv a ha K = f ∘ ambientPoolTrialEquiv σ K := rfl
  rw [hconfig, ← FiniteLaw.map_map]
  have hreindex : (poolThinLaw (F := F) (ConfigurationGroup σ) K).map
      (ambientPoolTrialEquiv σ K) =
      FiniteLaw.pi (fun _ : Fin (ambientTrialCount σ K) => FiniteLaw.uniform (Point F)) := by
    rw [poolThinLaw, FiniteLaw.pi_uniform, FiniteLaw.map_uniform_equiv, FiniteLaw.pi_uniform]
  rw [hreindex]
  exact FiniteLaw.map_pi (fun _ => FiniteLaw.uniform (Point F))
    (fun t => ambientTrialOutcome σ
      (groupPlacement σ u v huv (ambientPosition σ K t).1) a ha K)

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_GroupSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [Fintype k] [Fintype F]

theorem card_groups_le_two_mul_card (σ : k →+* F)
    (hs : 2 ≤ Fintype.card k) :
    Fintype.card (ConfigurationGroup σ) ≤ 2 * Fintype.card F := by
  have hfactor : 1 ≤ Fintype.card k - 1 := by omega
  have hle : Fintype.card (ConfigurationGroup σ) ≤
      Fintype.card (ConfigurationGroup σ) * (Fintype.card k - 1) := by
    simpa only [Nat.mul_one] using
      Nat.mul_le_mul_left (Fintype.card (ConfigurationGroup σ)) hfactor
  exact hle.trans (card_groups_mul_sub_one_le σ)

theorem groupSelectionData_direction_multiplicity_le_two
    (σ : k →+* F) (u v : k) (huv : u ≠ v) (d : Direction F) :
    (Finset.univ.filter (fun i => d ∈ (groupSelectionData σ u v huv).dirs i)).card ≤ 2 := by
  classical
  let e := Fintype.equivFin (ConfigurationGroup σ)
  let I := Finset.univ.filter (fun i => d ∈ (groupSelectionData σ u v huv).dirs i)
  let J := Finset.univ.filter (fun i => d ∈ groupConflict σ u v huv i)
  have hsub : I.image e.symm ⊆ J := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ e.symm.injective] at hc
  exact hc.trans (groupConflict_multiplicity_le_two σ u v huv d)

theorem groupSelectionData_bounded (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (hs : 2 ≤ Fintype.card k) :
    Selection.Bounded (groupSelectionConstant (Fintype.card k))
      (groupSelectionData σ u v huv) := by
  classical
  have htwo : 2 ≤ groupSelectionConstant (Fintype.card k) := by
    unfold groupSelectionConstant
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (card_groups_le_two_mul_card σ hs).trans
      (Nat.mul_le_mul_right (Fintype.card F) htwo)
  · intro i
    change (groupPoints σ u v huv
      ((Fintype.equivFin (ConfigurationGroup σ)).symm i)).card ≤ _
    rw [groupPoints_card]
    unfold groupSelectionConstant
    omega
  · intro i
    have hc := groupConflict_card_le σ u v huv
      ((Fintype.equivFin (ConfigurationGroup σ)).symm i)
    change (groupConflict σ u v huv
      ((Fintype.equivFin (ConfigurationGroup σ)).symm i)).card ≤ _
    unfold groupSelectionConstant
    omega
  · intro d
    exact (groupSelectionData_direction_multiplicity_le_two σ u v huv d).trans htwo

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_PoolThinAsymptotic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology
open scoped Classical
noncomputable section

namespace RyserCoveringCounterexample.Construction

theorem thinFailureBound_le (s K N : ℕ) {q : ℝ} (hq : 1 ≤ q)
    (hN : (N : ℝ) * (s - 1 : ℕ) ≤ 2 * q) :
    q ^ 3 * (q + 1) * (N : ℝ) ^ 6 *
        ((K : ℝ) * (s ^ 2 : ℕ) * (s - 1 : ℕ) / q ^ 2) ^ 6 ≤
      thinFailureConstant s K / q ^ 2 := by
  have hqpos : 0 < q := by linarith
  have hqne : q ≠ 0 := hqpos.ne'
  have hbase : (N : ℝ) * ((K : ℝ) * (s ^ 2 : ℕ) * (s - 1 : ℕ) / q ^ 2) ≤
      2 * (K : ℝ) * (s : ℝ) ^ 2 / q := by
    calc
      _ = (K : ℝ) * (s : ℝ) ^ 2 * ((N : ℝ) * (s - 1 : ℕ)) / q ^ 2 := by
        push_cast
        ring
      _ ≤ (K : ℝ) * (s : ℝ) ^ 2 * (2 * q) / q ^ 2 := by
        apply div_le_div_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hN (by positivity)
        · positivity
      _ = 2 * (K : ℝ) * (s : ℝ) ^ 2 / q := by
        field_simp [hqne]
  have hfactor : q ^ 3 * (q + 1) ≤ 2 * q ^ 4 := by
    calc
      _ ≤ q ^ 3 * (2 * q) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 2 * q ^ 4 := by ring
  calc
    _ = q ^ 3 * (q + 1) *
        ((N : ℝ) * ((K : ℝ) * (s ^ 2 : ℕ) * (s - 1 : ℕ) / q ^ 2)) ^ 6 := by
      rw [mul_pow]
      ring
    _ ≤ q ^ 3 * (q + 1) * (2 * (K : ℝ) * (s : ℝ) ^ 2 / q) ^ 6 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase 6) (by positivity)
    _ ≤ 2 * q ^ 4 * (2 * (K : ℝ) * (s : ℝ) ^ 2 / q) ^ 6 :=
      mul_le_mul_of_nonneg_right hfactor (by positivity)
    _ = thinFailureConstant s K / q ^ 2 := by
      unfold thinFailureConstant
      field_simp [hqne]
      ring

theorem tendsto_thinFailureBound (s K : ℕ) :
    Tendsto (fun q : ℕ => thinFailureConstant s K / (q : ℝ) ^ 2) atTop (𝓝 0) := by
  have h : Tendsto (fun q : ℝ => thinFailureConstant s K / q ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0))
  exact h.comp tendsto_natCast_atTop_atTop

theorem exists_thinFailure_cutoff (s K : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → thinFailureConstant s K / (q : ℝ) ^ 2 ≤ η := by
  exact Filter.eventually_atTop.mp ((tendsto_thinFailureBound s K).eventually_le_const hη)

variable {k F : Type*} [Field k] [Field F] [Fintype k] [Fintype F]
variable [DecidableEq k] [DecidableEq F]

theorem prob_groupPoolThin_ge (σ : k →+* F) (u v : k) (huv : u ≠ v) (K : ℕ) :
    1 - thinFailureConstant (Fintype.card k) K / (Fintype.card F : ℝ) ^ 2 ≤
      (poolThinLaw (F := F) (ConfigurationGroup σ) K).prob
        (PoolThin (groupPoints σ u v huv) (groupAltered σ u v huv)) := by
  have hraw := prob_not_poolThin_le (K := K)
    (groupPoints σ u v huv) (groupAltered σ u v huv)
    (Fintype.card k ^ 2) (Fintype.card k - 1)
    (fun i => le_of_eq (groupPoints_card σ u v huv i))
    (fun i => le_of_eq (groupAltered_card σ u v huv i))
  have hq : (1 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos (α := F)))
  have hN : (Fintype.card (ConfigurationGroup σ) : ℝ) * (Fintype.card k - 1 : ℕ) ≤
      2 * (Fintype.card F : ℝ) := by
    exact_mod_cast card_groups_mul_sub_one_le σ
  have hbound := hraw.trans
    (thinFailureBound_le (Fintype.card k) K (Fintype.card (ConfigurationGroup σ)) hq hN)
  rw [FiniteLaw.prob_compl] at hbound
  linarith

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_Deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

variable {P : Type*} [DecidableEq P]
  {shapes : Finset (Finset P)} {D n : ℕ}

theorem contribution_card_le (ignore : Finset (Finset P)) (test : Finset P)
    (a : Outcome shapes D) (H : ℕ)
    (hshape : ∀ L ∈ shapes, L ∉ ignore → (L ∩ test).card ≤ H) :
    (contribution ignore test a).card ≤ D * H := by
  let A := a.val.filter (fun L => L.val ∉ ignore)
  change (A.biUnion Subtype.val ∩ test).card ≤ D * H
  rw [Finset.biUnion_inter]
  calc
    _ ≤ ∑ L ∈ A, (L.val ∩ test).card := Finset.card_biUnion_le
    _ ≤ ∑ _L ∈ A, H := Finset.sum_le_sum fun L hL =>
      hshape L.val L.property (Finset.mem_filter.mp hL).2
    _ = A.card * H := by simp
    _ ≤ D * H := Nat.mul_le_mul_right H
      ((Finset.card_filter_le a.val _).trans a.property)

private theorem card_sub_card_le_card_of_sdiff_subset
    {A B K : Finset P} (h : A \ B ⊆ K) :
    (A.card : ℝ) - (B.card : ℝ) ≤ (K.card : ℝ) := by
  have hc : A.card ≤ K.card + B.card :=
    (Finset.card_le_card_sdiff_add_card (s := A) (t := B)).trans
      (Nat.add_le_add_right (Finset.card_le_card h) B.card)
  have hr : (A.card : ℝ) ≤ (K.card : ℝ) + (B.card : ℝ) := by
    exact_mod_cast hc
  linarith

variable [instFintypeP : Fintype P]

theorem survivors_update_sdiff_subset (ignore : Finset (Finset P))
    (test : Finset P) (ω : Fin n → Outcome shapes D) (i : Fin n)
    (a : Outcome shapes D) :
    (survivors ignore (Function.update ω i a) ∩ test) \
        (survivors ignore ω ∩ test) ⊆ contribution ignore test (ω i) := by
  intro x hx
  rcases Finset.mem_sdiff.mp hx with ⟨hxnew, hxold⟩
  rcases Finset.mem_inter.mp hxnew with ⟨hxs, hxP⟩
  refine Finset.mem_inter.mpr ⟨?_, hxP⟩
  by_contra hxi
  apply hxold
  refine Finset.mem_inter.mpr ⟨mem_survivors.mpr ?_, hxP⟩
  intro j
  by_cases hji : j = i
  · subst j
    exact hxi
  · have hj := mem_survivors.mp hxs j
    simpa only [Function.update_of_ne hji] using hj

theorem survivors_sdiff_update_subset (ignore : Finset (Finset P))
    (test : Finset P) (ω : Fin n → Outcome shapes D) (i : Fin n)
    (a : Outcome shapes D) :
    (survivors ignore ω ∩ test) \
        (survivors ignore (Function.update ω i a) ∩ test) ⊆
      contribution ignore test a := by
  intro x hx
  rcases Finset.mem_sdiff.mp hx with ⟨hxold, hxnew⟩
  rcases Finset.mem_inter.mp hxold with ⟨hxs, hxP⟩
  refine Finset.mem_inter.mpr ⟨?_, hxP⟩
  by_contra hxa
  apply hxnew
  refine Finset.mem_inter.mpr ⟨mem_survivors.mpr ?_, hxP⟩
  intro j
  by_cases hji : j = i
  · subst j
    simpa only [Function.update_self] using hxa
  · have hj := mem_survivors.mp hxs j
    simpa only [Function.update_of_ne hji] using hj

theorem retainedCount_update_bounds (ignore : Finset (Finset P))
    (test : Finset P) (ω : Fin n → Outcome shapes D) (i : Fin n)
    (a : Outcome shapes D) :
    -((contribution ignore test a).card : ℝ) ≤
        retainedCount ignore test (Function.update ω i a) - retainedCount ignore test ω ∧
      retainedCount ignore test (Function.update ω i a) - retainedCount ignore test ω ≤
        ((contribution ignore test (ω i)).card : ℝ) := by
  have hup := card_sub_card_le_card_of_sdiff_subset
    (survivors_update_sdiff_subset ignore test ω i a)
  have hdown := card_sub_card_le_card_of_sdiff_subset
    (survivors_sdiff_update_subset ignore test ω i a)
  change -((contribution ignore test a).card : ℝ) ≤
      ((survivors ignore (Function.update ω i a) ∩ test).card : ℝ) -
        ((survivors ignore ω ∩ test).card : ℝ) ∧ _
  exact ⟨by linarith, hup⟩

theorem retainedCount_update_abs_le (ignore : Finset (Finset P))
    (test : Finset P) (ω : Fin n → Outcome shapes D) (i : Fin n)
    (a : Outcome shapes D) :
    |retainedCount ignore test (Function.update ω i a) - retainedCount ignore test ω| ≤
      ((contribution ignore test (ω i)).card : ℝ) +
        ((contribution ignore test a).card : ℝ) := by
  obtain ⟨hlo, hhi⟩ := retainedCount_update_bounds ignore test ω i a
  have ho : 0 ≤ ((contribution ignore test (ω i)).card : ℝ) := Nat.cast_nonneg _
  have hn : 0 ≤ ((contribution ignore test a).card : ℝ) := Nat.cast_nonneg _
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem retainedCount_empty_bounds (ignore : Finset (Finset P))
    (test : Finset P) (ω : Fin n → Outcome shapes D) (i : Fin n) :
    0 ≤ retainedCount ignore test (Function.update ω i (emptyOutcome shapes D)) -
        retainedCount ignore test ω ∧
      retainedCount ignore test (Function.update ω i (emptyOutcome shapes D)) -
        retainedCount ignore test ω ≤ ((contribution ignore test (ω i)).card : ℝ) := by
  simpa only [contribution_emptyOutcome, Finset.card_empty, Nat.cast_zero, neg_zero]
    using retainedCount_update_bounds ignore test ω i (emptyOutcome shapes D)

theorem retainedCount_empty_abs_le (ignore : Finset (Finset P))
    (test : Finset P) (ω : Fin n → Outcome shapes D) (i : Fin n) :
    |retainedCount ignore test ω -
        retainedCount ignore test (Function.update ω i (emptyOutcome shapes D))| ≤
      ((contribution ignore test (ω i)).card : ℝ) := by
  obtain ⟨hlo, hhi⟩ := retainedCount_empty_bounds ignore test ω i
  rw [abs_sub_comm, abs_of_nonneg hlo]
  exact hhi

theorem not_rare_retainedCount_eq (ignore : Finset (Finset P))
    (test : Finset P) (ω : Fin n → Outcome shapes D) (i : Fin n)
    (h : ¬ rare ignore test (ω i)) :
    retainedCount ignore test ω =
      retainedCount ignore test (Function.update ω i (emptyOutcome shapes D)) := by
  have he : contribution ignore test (ω i) = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp h
  obtain ⟨hlo, hhi⟩ := retainedCount_empty_bounds ignore test ω i
  rw [he, Finset.card_empty, Nat.cast_zero] at hhi
  linarith

theorem retainedCount_empty_abs_le_mul (ignore : Finset (Finset P))
    (test : Finset P) (H : ℕ)
    (hshape : ∀ L ∈ shapes, L ∉ ignore → (L ∩ test).card ≤ H)
    (ω : Fin n → Outcome shapes D) (i : Fin n) :
    |retainedCount ignore test ω -
        retainedCount ignore test (Function.update ω i (emptyOutcome shapes D))| ≤
      (D : ℝ) * (H : ℝ) := by
  apply (retainedCount_empty_abs_le ignore test ω i).trans
  exact_mod_cast contribution_card_le ignore test (ω i) H hshape

section FiniteExpectations

variable {Ω : Type*} [Fintype Ω]

theorem expectation_card_inter (μ : FiniteLaw Ω) (S : Ω → Finset P)
    (test : Finset P) :
    μ.expectation (fun ω => ((S ω ∩ test).card : ℝ)) =
      ∑ x ∈ test, μ.prob (fun ω => x ∈ S ω) := let _ := instFintypeP; by
  have hc (ω : Ω) : ((S ω ∩ test).card : ℝ) =
      ∑ x ∈ test, if x ∈ S ω then (1 : ℝ) else 0 := by
    simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_comm]
  simp only [FiniteLaw.expectation, hc, Finset.mul_sum,
    FiniteLaw.prob, mul_ite, mul_one, mul_zero]
  calc
    _ = ∑ x ∈ test, ∑ ω, if x ∈ S ω then μ.weight ω else (0 : ℝ) :=
      Finset.sum_comm (s := Finset.univ) (t := test)
        (f := fun (ω : Ω) (x : P) => if x ∈ S ω then μ.weight ω else (0 : ℝ))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hx : x ∈ S ω <;> simp only [hx, ite_true, ite_false]

theorem prob_nonempty_inter_le (μ : FiniteLaw Ω) (S : Ω → Finset P)
    (test : Finset P) :
    μ.prob (fun ω => (S ω ∩ test).Nonempty) ≤
      ∑ x ∈ test, μ.prob (fun ω => x ∈ S ω) := by
  rw [← expectation_card_inter μ S test]
  apply μ.prob_le_expectation
  · intro ω
    exact Nat.cast_nonneg _
  · intro ω hω
    exact Nat.one_le_cast.mpr (Finset.one_le_card.mpr hω)

end FiniteExpectations

theorem prob_rare_le (μ : FiniteLaw (Outcome shapes D))
    (ignore : Finset (Finset P)) (test : Finset P) :
    μ.prob (rare ignore test) ≤
      ∑ x ∈ test, μ.prob (fun a => x ∈ deleted ignore a) :=
  prob_nonempty_inter_le μ (deleted ignore) test

theorem expectation_retainedCount (μ : Fin n → FiniteLaw (Outcome shapes D))
    (ignore : Finset (Finset P)) (test : Finset P) :
    (FiniteLaw.pi μ).expectation (retainedCount ignore test) =
      ∑ x ∈ test, (FiniteLaw.pi μ).prob (fun ω => x ∈ survivors ignore ω) :=
  expectation_card_inter (FiniteLaw.pi μ) (survivors ignore) test

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Probability_Exponential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.FiniteLaw

lemma expectation_mul_left_real {Ω : Type*} [Fintype Ω]
    (p : FiniteLaw Ω) (c : ℝ) (f : Ω → ℝ) :
    p.expectation (fun a => c * f a) = c * p.expectation f := by
  classical
  unfold expectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring

lemma exp_le_one_add_add_sq {x : ℝ} (hx : |x| ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 := by
  have h := (le_abs_self (Real.exp x - 1 - x)).trans
    (Real.abs_exp_sub_one_sub_id_le hx)
  linarith

lemma expectation_exp_le_of_mean_zero {Ω : Type*} [Fintype Ω]
    (p : FiniteLaw Ω) (z : Ω → ℝ) (M v θ : ℝ)
    (hz : p.expectation z = 0)
    (hbound : ∀ a, |z a| ≤ M)
    (hsecond : p.expectation (fun a => (z a) ^ 2) ≤ v)
    (hθ : |θ| * M ≤ 1) :
    p.expectation (fun a => Real.exp (θ * z a)) ≤
      Real.exp (θ ^ 2 * v) := by
  classical
  have hpoint (a : Ω) :
      Real.exp (θ * z a) ≤ 1 + θ * z a + θ ^ 2 * (z a) ^ 2 := by
    have habs : |θ * z a| ≤ 1 := calc
      |θ * z a| = |θ| * |z a| := abs_mul _ _
      _ ≤ |θ| * M := mul_le_mul_of_nonneg_left (hbound a) (abs_nonneg θ)
      _ ≤ 1 := hθ
    have he := exp_le_one_add_add_sq habs
    nlinarith [he]
  have hlin :
      (∑ a, p.weight a * (θ * z a)) = θ * p.expectation z := by
    exact expectation_mul_left_real p θ z
  have hquad :
      (∑ a, p.weight a * (θ ^ 2 * (z a) ^ 2)) =
        θ ^ 2 * p.expectation (fun a => (z a) ^ 2) := by
    exact expectation_mul_left_real p (θ ^ 2) (fun a => (z a) ^ 2)
  calc
    p.expectation (fun a => Real.exp (θ * z a)) ≤
        p.expectation (fun a => 1 + θ * z a + θ ^ 2 * (z a) ^ 2) := by
      unfold expectation
      exact Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_left (hpoint a) (p.nonneg a)
    _ = 1 + θ * p.expectation z +
        θ ^ 2 * p.expectation (fun a => (z a) ^ 2) := by
      change (∑ a, p.weight a * (1 + θ * z a + θ ^ 2 * (z a) ^ 2)) = _
      simp only [mul_add, mul_one, Finset.sum_add_distrib]
      rw [p.total, hlin, hquad]
    _ = 1 + θ ^ 2 * p.expectation (fun a => (z a) ^ 2) := by
      rw [hz]
      ring
    _ ≤ 1 + θ ^ 2 * v :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hsecond (sq_nonneg θ))
    _ ≤ Real.exp (θ ^ 2 * v) := by
      simpa only [add_comm] using Real.add_one_le_exp (θ ^ 2 * v)

lemma iterated_centered_mgf_le
    {A B : Type*} [Fintype A] [Fintype B]
    (p : FiniteLaw A) (q : A → FiniteLaw B)
    (f : A → B → ℝ) (head : A → ℝ)
    (center θ v V : ℝ)
    (hhead : p.expectation (fun a => Real.exp (θ * (head a - center))) ≤
      Real.exp (θ ^ 2 * v))
    (htail : ∀ a, (q a).expectation
        (fun b => Real.exp (θ * (f a b - head a))) ≤ Real.exp (θ ^ 2 * V)) :
    p.expectation (fun a => (q a).expectation
      (fun b => Real.exp (θ * (f a b - center)))) ≤
        Real.exp (θ ^ 2 * (v + V)) := by
  classical
  have hsplit (a : A) :
      (q a).expectation (fun b => Real.exp (θ * (f a b - center))) =
        Real.exp (θ * (head a - center)) *
          (q a).expectation (fun b => Real.exp (θ * (f a b - head a))) := by
    rw [← expectation_mul_left_real]
    congr 1
    funext b
    rw [← Real.exp_add]
    congr 1
    ring
  have hinner (a : A) :
      (q a).expectation (fun b => Real.exp (θ * (f a b - center))) ≤
        Real.exp (θ ^ 2 * V) * Real.exp (θ * (head a - center)) := by
    rw [hsplit]
    have h := mul_le_mul_of_nonneg_left (htail a)
      (Real.exp_pos (θ * (head a - center))).le
    simpa only [mul_comm] using h
  calc
    p.expectation (fun a => (q a).expectation
        (fun b => Real.exp (θ * (f a b - center)))) ≤
        p.expectation (fun a =>
          Real.exp (θ ^ 2 * V) * Real.exp (θ * (head a - center))) := by
      unfold expectation
      exact Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_left (hinner a) (p.nonneg a)
    _ = Real.exp (θ ^ 2 * V) *
        p.expectation (fun a => Real.exp (θ * (head a - center))) :=
      expectation_mul_left_real p _ _
    _ ≤ Real.exp (θ ^ 2 * V) * Real.exp (θ ^ 2 * v) :=
      mul_le_mul_of_nonneg_left hhead (Real.exp_pos _).le
    _ = Real.exp (θ ^ 2 * (v + V)) := by
      rw [← Real.exp_add]
      congr 1
      ring

lemma chernoff_upper {Ω : Type*} [Fintype Ω]
    (p : FiniteLaw Ω) (f : Ω → ℝ) (u θ : ℝ) (hθ : 0 ≤ θ) :
    p.prob (fun a => u ≤ f a) ≤
      Real.exp (-θ * u) * p.expectation (fun a => Real.exp (θ * f a)) := by
  classical
  unfold prob expectation
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  by_cases huf : u ≤ f a
  · simp only [ite_eq_left huf]
    have he : 1 ≤ Real.exp (-θ * u) * Real.exp (θ * f a) := calc
      1 = Real.exp 0 := (Real.exp_zero).symm
      _ ≤ Real.exp (-θ * u + θ * f a) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg hθ (sub_nonneg.mpr huf)]
      _ = Real.exp (-θ * u) * Real.exp (θ * f a) := Real.exp_add _ _
    calc
      p.weight a = p.weight a * 1 := by ring
      _ ≤ p.weight a * (Real.exp (-θ * u) * Real.exp (θ * f a)) :=
        mul_le_mul_of_nonneg_left he (p.nonneg a)
      _ = Real.exp (-θ * u) * (p.weight a * Real.exp (θ * f a)) := by ring
  · simp only [ite_eq_right huf]
    exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (p.nonneg a) (Real.exp_pos _).le)

lemma chernoff_upper_of_mgf {Ω : Type*} [Fintype Ω]
    (p : FiniteLaw Ω) (f : Ω → ℝ) (u θ V : ℝ)
    (hθ : 0 ≤ θ)
    (hmgf : p.expectation (fun a => Real.exp (θ * f a)) ≤
      Real.exp (θ ^ 2 * V)) :
    p.prob (fun a => u ≤ f a) ≤ Real.exp (θ ^ 2 * V - θ * u) := by
  calc
    p.prob (fun a => u ≤ f a) ≤
        Real.exp (-θ * u) * p.expectation (fun a => Real.exp (θ * f a)) :=
      chernoff_upper p f u θ hθ
    _ ≤ Real.exp (-θ * u) * Real.exp (θ ^ 2 * V) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = Real.exp (θ ^ 2 * V - θ * u) := by
      rw [← Real.exp_add]
      congr 1
      ring

lemma bernstein_scalar_optimization
    (M V u P : ℝ)
    (hM : 0 < M) (hV : 0 < V) (hu : 0 < u)
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 / M →
      P ≤ Real.exp (t ^ 2 * V - t * u)) :
    P ≤ Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
  by_cases hcut : u / (2 * V) ≤ 1 / M
  · have ht : 0 < u / (2 * V) :=
      div_pos hu (mul_pos (by norm_num) hV)
    have hexp :
        (u / (2 * V)) ^ 2 * V - (u / (2 * V)) * u =
          -(1 / 4 : ℝ) * (u ^ 2 / V) := by
      field_simp [ne_of_gt hV]; ring
    calc
      P ≤ Real.exp ((u / (2 * V)) ^ 2 * V - (u / (2 * V)) * u) :=
        h _ ht hcut
      _ ≤ Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
        apply Real.exp_le_exp.mpr
        rw [hexp]
        nlinarith [min_le_left (u ^ 2 / V) (u / M)]
  · have hcross : 2 * V < u * M := by
      have ht : 1 / M < u / (2 * V) := lt_of_not_ge hcut
      have ht' :=
        (div_lt_div_iff₀ hM (mul_pos (by norm_num) hV)).mp ht
      simpa using ht'
    have hnum : V - u * M ≤ -(u * M) / 4 := by
      nlinarith [mul_pos hu hM]
    have hexp :
        (1 / M) ^ 2 * V - (1 / M) * u ≤
          -(1 / 4 : ℝ) * (u / M) := by
      calc
        (1 / M) ^ 2 * V - (1 / M) * u =
            (V - u * M) / M ^ 2 := by
          field_simp [ne_of_gt hM]
        _ ≤ (-(u * M) / 4) / M ^ 2 :=
          div_le_div_of_nonneg_right hnum (sq_nonneg M)
        _ = -(1 / 4 : ℝ) * (u / M) := by
          field_simp [ne_of_gt hM]
    calc
      P ≤ Real.exp ((1 / M) ^ 2 * V - (1 / M) * u) :=
        h _ (div_pos (by norm_num) hM) le_rfl
      _ ≤ Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
        apply Real.exp_le_exp.mpr
        have hmin :
            -(1 / 4 : ℝ) * (u / M) ≤
              -(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M) := by
          nlinarith [min_le_right (u ^ 2 / V) (u / M)]
        exact hexp.trans hmin

lemma prob_abs_ge_le_add {Ω : Type*} [Fintype Ω]
    (p : FiniteLaw Ω) (f : Ω → ℝ) (u : ℝ) :
    p.prob (fun a => u ≤ |f a|) ≤
      p.prob (fun a => u ≤ f a) + p.prob (fun a => u ≤ -f a) := by
  classical
  unfold prob
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a ha
  change (if u ≤ |f a| then p.weight a else 0) ≤
    (if u ≤ f a then p.weight a else 0) + (if u ≤ -f a then p.weight a else 0)
  by_cases hs : 0 ≤ f a
  · rw [abs_of_nonneg hs]
    split_ifs <;> linarith [p.nonneg a]
  · rw [abs_of_nonpos (le_of_not_ge hs)]
    split_ifs <;> linarith [p.nonneg a]

lemma bernstein_abs_tail_of_mgf {Ω : Type*} [Fintype Ω]
    (p : FiniteLaw Ω) (f : Ω → ℝ) (M V u : ℝ)
    (hM : 0 < M) (hV : 0 < V) (hu : 0 < u)
    (hmgf : ∀ θ : ℝ, |θ| * M ≤ 1 →
      p.expectation (fun a => Real.exp (θ * f a)) ≤
        Real.exp (θ ^ 2 * V)) :
    p.prob (fun a => u ≤ |f a|) ≤
      2 * Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
  have upper : p.prob (fun a => u ≤ f a) ≤
      Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
    apply bernstein_scalar_optimization M V u _ hM hV hu
    intro θ hθ hθM
    have hadm : |θ| * M ≤ 1 := by
      rw [abs_of_pos hθ]
      exact (le_div_iff₀ hM).mp hθM
    exact chernoff_upper_of_mgf p f u θ V hθ.le (hmgf θ hadm)
  have lower : p.prob (fun a => u ≤ -f a) ≤
      Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
    apply bernstein_scalar_optimization M V u _ hM hV hu
    intro θ hθ hθM
    have hadm : |θ| * M ≤ 1 := by
      rw [abs_of_pos hθ]
      exact (le_div_iff₀ hM).mp hθM
    have hadmneg : |-θ| * M ≤ 1 := by
      simpa only [abs_neg] using hadm
    have hneg : p.expectation (fun a => Real.exp (θ * (-f a))) ≤
        Real.exp (θ ^ 2 * V) := by
      simpa only [neg_mul, mul_neg, neg_sq] using hmgf (-θ) hadmneg
    exact chernoff_upper_of_mgf p (fun a => -f a) u θ V hθ.le hneg
  calc
    p.prob (fun a => u ≤ |f a|) ≤
        p.prob (fun a => u ≤ f a) + p.prob (fun a => u ≤ -f a) :=
      prob_abs_ge_le_add p f u
    _ ≤ Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) +
        Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) :=
      add_le_add upper lower
    _ = 2 * Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by ring

end RyserCoveringCounterexample.FiniteLaw

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Probability_RareAnchor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample

lemma rareAnchor_centering_raw
    {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω)
    (htotal : (∑ ω, w ω) = 1)
    (g : Ω → ℝ) (b C r : ℝ)
    (E : Ω → Prop) [DecidablePred E]
    (hbound : ∀ ω, |g ω - b| ≤ C)
    (houtside : ∀ ω, ¬ E ω → g ω = b)
    (hrare : (∑ ω, if E ω then w ω else 0) ≤ r) :
    let m := ∑ ω, w ω * g ω
    (∑ ω, w ω * (g ω - m)) = 0 ∧
      (∀ ω, |g ω - m| ≤ 2 * C) ∧
      (∑ ω, w ω * (g ω - m) ^ 2) ≤ C ^ 2 * r := by
  classical
  let m : ℝ := ∑ ω, w ω * g ω
  change
    (∑ ω, w ω * (g ω - m)) = 0 ∧
      (∀ ω, |g ω - m| ≤ 2 * C) ∧
      (∑ ω, w ω * (g ω - m) ^ 2) ≤ C ^ 2 * r

  have hconst (a : ℝ) : (∑ ω, w ω * a) = a := by
    rw [← Finset.sum_mul, htotal, one_mul]

  have hmlo : b - C ≤ m := by
    calc
      b - C = ∑ ω, w ω * (b - C) := (hconst _).symm
      _ ≤ ∑ ω, w ω * g ω := by
        apply Finset.sum_le_sum
        intro ω _
        apply mul_le_mul_of_nonneg_left _ (hw ω)
        have hlo := (abs_le.mp (hbound ω)).1
        linarith
      _ = m := rfl

  have hmhi : m ≤ b + C := by
    calc
      m = ∑ ω, w ω * g ω := rfl
      _ ≤ ∑ ω, w ω * (b + C) := by
        apply Finset.sum_le_sum
        intro ω _
        apply mul_le_mul_of_nonneg_left _ (hw ω)
        have hhi := (abs_le.mp (hbound ω)).2
        linarith
      _ = b + C := hconst _

  have hmean0 : (∑ ω, w ω * (g ω - m)) = 0 := by
    calc
      (∑ ω, w ω * (g ω - m)) =
          (∑ ω, w ω * g ω) - (∑ ω, w ω * m) := by
        simp only [mul_sub, Finset.sum_sub_distrib]
      _ = m - m := by
        change m - (∑ ω, w ω * m) = m - m
        rw [hconst m]
      _ = 0 := sub_self m

  have hcenterBound : ∀ ω, |g ω - m| ≤ 2 * C := by
    intro ω
    rcases abs_le.mp (hbound ω) with ⟨hlo, hhi⟩
    apply abs_le.mpr
    constructor <;> linarith

  have hsqBound : ∀ ω, (g ω - b) ^ 2 ≤ C ^ 2 := by
    intro ω
    rcases abs_le.mp (hbound ω) with ⟨hlo, hhi⟩
    have hminus : 0 ≤ C - (g ω - b) := by
      linarith
    have hplus : 0 ≤ C + (g ω - b) := by
      linarith
    have hprod := mul_nonneg hminus hplus
    nlinarith

  have hanchor :
      (∑ ω, w ω * (g ω - b) ^ 2) ≤ C ^ 2 * r := by
    calc
      (∑ ω, w ω * (g ω - b) ^ 2) ≤
          ∑ ω, (if E ω then w ω else 0) * C ^ 2 := by
        apply Finset.sum_le_sum
        intro ω _
        by_cases hE : E ω
        · simp only [ite_eq_left hE]
          exact mul_le_mul_of_nonneg_left (hsqBound ω) (hw ω)
        · simp [hE, houtside ω hE]
      _ = (∑ ω, if E ω then w ω else 0) * C ^ 2 := by
        rw [Finset.sum_mul]
      _ ≤ r * C ^ 2 :=
        mul_le_mul_of_nonneg_right hrare (sq_nonneg C)
      _ = C ^ 2 * r := mul_comm _ _

  have hvariance :
      (∑ ω, w ω * (g ω - b) ^ 2) =
        (∑ ω, w ω * (g ω - m) ^ 2) + (m - b) ^ 2 := by
    calc
      (∑ ω, w ω * (g ω - b) ^ 2) =
          ∑ ω,
            (w ω * (g ω - m) ^ 2 +
              (w ω * (g ω - m)) * (2 * (m - b)) +
              w ω * (m - b) ^ 2) := by
        apply Finset.sum_congr rfl
        intro ω _
        ring
      _ = (∑ ω, w ω * (g ω - m) ^ 2) +
            (∑ ω, w ω * (g ω - m)) * (2 * (m - b)) +
            (∑ ω, w ω) * (m - b) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.sum_mul, ← Finset.sum_mul]
      _ = (∑ ω, w ω * (g ω - m) ^ 2) + (m - b) ^ 2 := by
        simp only [hmean0, htotal, zero_mul, one_mul, add_zero]

  refine ⟨hmean0, hcenterBound, ?_⟩
  have hshiftNonneg := sq_nonneg (m - b)
  linarith [hvariance, hanchor]

lemma FiniteLaw.rareAnchor_centering
    {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω)
    (g : Ω → ℝ) (b C r : ℝ)
    (E : Ω → Prop) [DecidablePred E]
    (hbound : ∀ ω, |g ω - b| ≤ C)
    (houtside : ∀ ω, ¬ E ω → g ω = b)
    (hrare : μ.prob E ≤ r) :
    μ.expectation (fun ω => g ω - μ.expectation g) = 0 ∧
      (∀ ω, |g ω - μ.expectation g| ≤ 2 * C) ∧
      μ.expectation (fun ω => (g ω - μ.expectation g) ^ 2)
        ≤ C ^ 2 * r := by
  exact @rareAnchor_centering_raw Ω _
    μ.weight μ.nonneg μ.total g b C r E
    (fun ω => Classical.propDecidable (E ω))
    hbound houtside hrare

end RyserCoveringCounterexample

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Probability_Exposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Exposure

open scoped BigOperators

variable {Omega : Type*} [instFintypeOmega : Fintype Omega]

theorem cons_head_tail {n : Nat} (w : Fin (n + 1) → Omega) :
    Fin.cons (w 0) (fun i => w i.succ) = w := let _ := instFintypeOmega;
  (splitConfig n).left_inv w

theorem expectation_pi_succ {n : Nat}
    (mu : Fin (n + 1) → FiniteLaw Omega)
    (f : (Fin (n + 1) → Omega) → ℝ) :
    (FiniteLaw.pi mu).expectation f =
      (mu 0).expectation (headMean mu f) := by
  classical
  change (∑ w, (∏ i, (mu i).weight (w i)) * f w) =
    ∑ x, (mu 0).weight x *
      (∑ tail : Fin n → Omega,
        (∏ i, (mu i.succ).weight (tail i)) * f (Fin.cons x tail))
  calc
    _ = ∑ p : Omega × (Fin n → Omega),
        ((mu 0).weight p.1 * ∏ i, (mu i.succ).weight (p.2 i)) *
          f (Fin.cons p.1 p.2) := by
      refine Fintype.sum_equiv (splitConfig n) _ _ ?_
      intro w
      change (∏ i, (mu i).weight (w i)) * f w =
        ((mu 0).weight (w 0) * ∏ i : Fin n, (mu i.succ).weight (w i.succ)) *
          f (Fin.cons (w 0) (fun i => w i.succ))
      rw [cons_head_tail, Fin.prod_univ_succ]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro tail _
      ring

theorem mean_difference_bound {A : Type*} [Fintype A]
    (p : FiniteLaw A) (f g : A → ℝ) (C : ℝ)
    (h : ∀ a, |f a - g a| ≤ C) :
    |p.expectation f - p.expectation g| ≤ C := by
  have hlo : p.expectation (fun a => g a - C) ≤ p.expectation f := by
    apply p.expectation_mono
    intro a
    have hh := (abs_le.mp (h a)).1
    linarith
  have hhi : p.expectation f ≤ p.expectation (fun a => g a + C) := by
    apply p.expectation_mono
    intro a
    have hh := (abs_le.mp (h a)).2
    linarith
  rw [FiniteLaw.expectation_sub, FiniteLaw.expectation_const] at hlo
  rw [FiniteLaw.expectation_add, FiniteLaw.expectation_const] at hhi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem second_moment_le {A : Type*} [Fintype A]
    (p : FiniteLaw A) (f : A → ℝ) (C : ℝ)
    (h : ∀ a, |f a| ≤ C) :
    p.expectation (fun a => (f a) ^ 2) ≤ C ^ 2 := by
  calc
    _ ≤ p.expectation (fun _ => C ^ 2) := by
      apply p.expectation_mono
      intro a
      rcases abs_le.mp (h a) with ⟨hl, hu⟩
      have hp : 0 ≤ (C - f a) * (C + f a) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    _ = C ^ 2 := p.expectation_const _

theorem update_cons_zero {n : Nat} (x y : Omega) (tail : Fin n → Omega) :
    Function.update
        (Fin.cons (n := let _ := instFintypeOmega; n) (α := fun _ : Fin (n + 1) => Omega) x tail) 0 y =
      Fin.cons (n := n) (α := fun _ : Fin (n + 1) => Omega) y tail :=
  Fin.update_cons_zero (n := n) (α := fun _ : Fin (n + 1) => Omega) x tail y

theorem cons_update {n : Nat} (x y : Omega) (tail : Fin n → Omega) (i : Fin n) :
    Fin.cons (n := let _ := instFintypeOmega; n) (α := fun _ : Fin (n + 1) => Omega) x
        (Function.update tail i y) =
      Function.update
        (Fin.cons (n := n) (α := fun _ : Fin (n + 1) => Omega) x tail) i.succ y :=
  Fin.cons_update (n := n) (α := fun _ : Fin (n + 1) => Omega) x tail i y

theorem exposureBounds_of_coordinateBound (M : ℝ) (n : Nat)
    (mu : Fin n → FiniteLaw Omega) (f : (Fin n → Omega) → ℝ)
    (c : Fin n → ℝ)
    (hcoord : ∀ i w x, |f (Function.update w i x) - f w| ≤ c i)
    (hM : ∀ i, c i ≤ M) :
    ExposureBounds M n mu f (fun i => (c i) ^ 2) := by
  classical
  induction n with
  | zero => trivial
  | succ n ih =>
    have hdiam (x y : Omega) :
        |headMean mu f x - headMean mu f y| ≤ c 0 := by
      apply mean_difference_bound
      intro tail
      simpa only [update_cons_zero] using hcoord 0 (Fin.cons y tail) x
    have hcenter (x : Omega) :
        |headMean mu f x - (mu 0).expectation (headMean mu f)| ≤ c 0 := by
      have hh := mean_difference_bound (mu 0) (fun _ => headMean mu f x)
        (headMean mu f) (c 0) (hdiam x)
      simpa only [FiniteLaw.expectation_const] using hh
    refine ⟨fun x => (hcenter x).trans (hM 0), ?_, ?_⟩
    · exact second_moment_le (mu 0)
        (fun x => headMean mu f x - (mu 0).expectation (headMean mu f))
        (c 0) hcenter
    · intro x
      refine ih (fun i => mu i.succ) (fun tail => f (Fin.cons x tail))
        (fun i => c i.succ) ?_ (fun i => hM i.succ)
      intro i tail y
      simpa only [cons_update] using hcoord i.succ (Fin.cons x tail) y

theorem exposureBounds_of_rareAnchor (M : ℝ) (n : Nat)
    (mu : Fin n → FiniteLaw Omega) (f : (Fin n → Omega) → ℝ)
    (e : Omega) (C r : Fin n → ℝ) (rare : Fin n → Omega → Prop)
    (hanchor : ∀ i w, |f w - f (Function.update w i e)| ≤ C i)
    (houtside : ∀ i w, ¬ rare i (w i) → f w = f (Function.update w i e))
    (hrare : ∀ i, (mu i).prob (rare i) ≤ r i)
    (hM : ∀ i, 2 * C i ≤ M) :
    ExposureBounds M n mu f (fun i => (C i) ^ 2 * r i) := by
  classical
  induction n with
  | zero => trivial
  | succ n ih =>
    have hhead (x : Omega) :
        |headMean mu f x - headMean mu f e| ≤ C 0 := by
      apply mean_difference_bound
      intro tail
      simpa only [update_cons_zero] using hanchor 0 (Fin.cons x tail)
    have hheadoutside (x : Omega) (hx : ¬ rare 0 x) :
        headMean mu f x = headMean mu f e := by
      apply congrArg ((FiniteLaw.pi (fun i : Fin n => mu i.succ)).expectation)
      funext tail
      simpa only [update_cons_zero] using houtside 0 (Fin.cons x tail) hx
    rcases FiniteLaw.rareAnchor_centering (mu 0) (headMean mu f)
      (headMean mu f e) (C 0) (r 0) (rare 0) hhead hheadoutside (hrare 0)
      with ⟨hzero, hcenter, hsecond⟩
    refine ⟨fun x => (hcenter x).trans (hM 0), hsecond, ?_⟩
    intro x
    refine ih (fun i => mu i.succ) (fun tail => f (Fin.cons x tail))
      (fun i => C i.succ) (fun i => r i.succ) (fun i => rare i.succ)
      ?_ ?_ (fun i => hrare i.succ) (fun i => hM i.succ)
    · intro i tail
      simpa only [cons_update] using hanchor i.succ (Fin.cons x tail)
    · intro i tail hnot
      simpa only [cons_update] using houtside i.succ (Fin.cons x tail) hnot

end RyserCoveringCounterexample.Exposure

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Probability_Concentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Concentration

open scoped BigOperators
open Exposure

variable {Omega : Type*} [Fintype Omega]

theorem exposure_mgf (M : ℝ) (n : Nat)
    (mu : Fin n → FiniteLaw Omega) (f : (Fin n → Omega) → ℝ)
    (v : Fin n → ℝ) (theta : ℝ)
    (hb : ExposureBounds M n mu f v) (htheta : |theta| * M ≤ 1) :
    (FiniteLaw.pi mu).expectation
      (fun w => Real.exp (theta * (f w - (FiniteLaw.pi mu).expectation f)))
      ≤ Real.exp (theta ^ 2 * ∑ i, v i) := by
  classical
  induction n with
  | zero =>
    have hf : f = fun _ => f (fun i => Fin.elim0 i) := by
      funext w
      apply congrArg f
      funext i
      exact Fin.elim0 i
    rw [hf]
    simp [FiniteLaw.expectation_const]
  | succ n ih =>
    rcases hb with ⟨hbound, hsecond, hrec⟩
    have hzero : (mu 0).expectation
        (fun x => headMean mu f x - (mu 0).expectation (headMean mu f)) = 0 := by
      rw [FiniteLaw.expectation_sub, FiniteLaw.expectation_const, sub_self]
    have hhead := FiniteLaw.expectation_exp_le_of_mean_zero (mu 0)
      (fun x => headMean mu f x - (mu 0).expectation (headMean mu f))
      M (v 0) theta hzero hbound hsecond htheta
    have htail (x : Omega) :
        (FiniteLaw.pi (fun i : Fin n => mu i.succ)).expectation
          (fun w => Real.exp (theta * (f (Fin.cons x w) - headMean mu f x)))
          ≤ Real.exp (theta ^ 2 * ∑ i : Fin n, v i.succ) := by
      exact ih (fun i => mu i.succ) (fun w => f (Fin.cons x w))
        (fun i => v i.succ) (hrec x)
    calc
      _ = (mu 0).expectation (fun x =>
          (FiniteLaw.pi (fun i : Fin n => mu i.succ)).expectation
            (fun w => Real.exp (theta *
              (f (Fin.cons x w) - (FiniteLaw.pi mu).expectation f)))) :=
        expectation_pi_succ (n := n) mu
          (fun w : Fin (n + 1) → Omega =>
            Real.exp (theta * (f w - (FiniteLaw.pi mu).expectation f)))
      _ = (mu 0).expectation (fun x =>
          (FiniteLaw.pi (fun i : Fin n => mu i.succ)).expectation
            (fun w => Real.exp (theta *
              (f (Fin.cons x w) - (mu 0).expectation (headMean mu f))))) := by
        rw [expectation_pi_succ mu f]
      _ ≤ Real.exp (theta ^ 2 * (v 0 + ∑ i : Fin n, v i.succ)) :=
        FiniteLaw.iterated_centered_mgf_le (mu 0)
          (fun _ => FiniteLaw.pi (fun i : Fin n => mu i.succ))
          (fun x w => f (Fin.cons x w)) (headMean mu f)
          ((mu 0).expectation (headMean mu f)) theta (v 0)
          (∑ i : Fin n, v i.succ) hhead htail
      _ = _ := by rw [Fin.sum_univ_succ]

theorem concentration (n : Nat)
    (mu : Fin n → FiniteLaw Omega) (f : (Fin n → Omega) → ℝ)
    (v : Fin n → ℝ) (M V u : ℝ)
    (hM : 0 < M) (hV : 0 < V) (hu : 0 < u)
    (hb : ExposureBounds M n mu f v) (hv : (∑ i, v i) ≤ V) :
    (FiniteLaw.pi mu).prob
        (fun w => u ≤ |f w - (FiniteLaw.pi mu).expectation f|) ≤
      2 * Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
  apply FiniteLaw.bernstein_abs_tail_of_mgf (FiniteLaw.pi mu)
    (fun w => f w - (FiniteLaw.pi mu).expectation f) M V u hM hV hu
  intro theta htheta
  exact (exposure_mgf M n mu f v theta hb htheta).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hv (sq_nonneg theta)))

theorem coordinate_concentration (n : Nat)
    (mu : Fin n → FiniteLaw Omega) (f : (Fin n → Omega) → ℝ)
    (c : Fin n → ℝ) (M V u : ℝ)
    (hM : 0 < M) (hV : 0 < V) (hu : 0 < u)
    (hcoord : ∀ i w x, |f (Function.update w i x) - f w| ≤ c i)
    (hcM : ∀ i, c i ≤ M) (hcV : (∑ i, (c i) ^ 2) ≤ V) :
    (FiniteLaw.pi mu).prob
        (fun w => u ≤ |f w - (FiniteLaw.pi mu).expectation f|) ≤
      2 * Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
  exact concentration n mu f (fun i => (c i) ^ 2) M V u hM hV hu
    (exposureBounds_of_coordinateBound M n mu f c hcoord hcM) hcV

theorem rare_anchor_concentration (n : Nat)
    (mu : Fin n → FiniteLaw Omega) (f : (Fin n → Omega) → ℝ)
    (e : Omega) (C r : Fin n → ℝ) (rare : Fin n → Omega → Prop)
    (M V u : ℝ) (hM : 0 < M) (hV : 0 < V) (hu : 0 < u)
    (hanchor : ∀ i w, |f w - f (Function.update w i e)| ≤ C i)
    (houtside : ∀ i w, ¬ rare i (w i) → f w = f (Function.update w i e))
    (hrare : ∀ i, (mu i).prob (rare i) ≤ r i)
    (hCM : ∀ i, 2 * C i ≤ M)
    (hCV : (∑ i, (C i) ^ 2 * r i) ≤ V) :
    (FiniteLaw.pi mu).prob
        (fun w => u ≤ |f w - (FiniteLaw.pi mu).expectation f|) ≤
      2 * Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
  exact concentration n mu f (fun i => (C i) ^ 2 * r i) M V u hM hV hu
    (exposureBounds_of_rareAnchor M n mu f e C r rare hanchor houtside hrare hCM)
    hCV

end RyserCoveringCounterexample.Concentration

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_CountConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

variable {P : Type*} [Fintype P] [DecidableEq P]
  {shapes : Finset (Finset P)} {D n : ℕ}

theorem prob_rare_le_of_pointwise (μ : FiniteLaw (Outcome shapes D))
    (ignore : Finset (Finset P)) (test : Finset P) (p₀ : ℝ)
    (hpoint : ∀ x ∈ test, μ.prob (fun a => x ∈ deleted ignore a) ≤ p₀) :
    μ.prob (rare ignore test) ≤ (test.card : ℝ) * p₀ := by
  calc
    _ ≤ ∑ x ∈ test, μ.prob (fun a => x ∈ deleted ignore a) :=
      prob_rare_le μ ignore test
    _ ≤ ∑ _x ∈ test, p₀ := Finset.sum_le_sum fun x hx => hpoint x hx
    _ = (test.card : ℝ) * p₀ := by simp

theorem retainedCount_coordinate_concentration
    (μ : Fin n → FiniteLaw (Outcome shapes D))
    (ignore : Finset (Finset P)) (test : Finset P) (H : ℕ)
    (hshape : ∀ L ∈ shapes, L ∉ ignore → (L ∩ test).card ≤ H)
    (M V u : ℝ) (hM : 0 < M) (hV : 0 < V) (hu : 0 < u)
    (hCM : 2 * (D : ℝ) * (H : ℝ) ≤ M)
    (hCV : (n : ℝ) * (2 * (D : ℝ) * (H : ℝ)) ^ 2 ≤ V) :
    (FiniteLaw.pi μ).prob (fun ω => u ≤
        |retainedCount ignore test ω -
          (FiniteLaw.pi μ).expectation (retainedCount ignore test)|) ≤
      2 * Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
  apply Concentration.coordinate_concentration n μ (retainedCount ignore test)
    (fun _ => 2 * (D : ℝ) * (H : ℝ)) M V u hM hV hu
  · intro i ω a
    have hold : ((contribution ignore test (ω i)).card : ℝ) ≤
        (D : ℝ) * (H : ℝ) := by
      exact_mod_cast contribution_card_le ignore test (ω i) H hshape
    have hnew : ((contribution ignore test a).card : ℝ) ≤
        (D : ℝ) * (H : ℝ) := by
      exact_mod_cast contribution_card_le ignore test a H hshape
    apply (retainedCount_update_abs_le ignore test ω i a).trans
    linarith
  · intro i
    exact hCM
  · simpa using hCV

theorem retainedCount_rare_concentration
    (μ : Fin n → FiniteLaw (Outcome shapes D))
    (ignore : Finset (Finset P)) (test : Finset P) (H : ℕ)
    (hshape : ∀ L ∈ shapes, L ∉ ignore → (L ∩ test).card ≤ H)
    (p₀ : ℝ)
    (hpoint : ∀ i x, x ∈ test → (μ i).prob (fun a => x ∈ deleted ignore a) ≤ p₀)
    (M V u : ℝ) (hM : 0 < M) (hV : 0 < V) (hu : 0 < u)
    (hCM : 2 * (D : ℝ) * (H : ℝ) ≤ M)
    (hCV : (n : ℝ) * ((D : ℝ) * (H : ℝ)) ^ 2 *
      ((test.card : ℝ) * p₀) ≤ V) :
    (FiniteLaw.pi μ).prob (fun ω => u ≤
        |retainedCount ignore test ω -
          (FiniteLaw.pi μ).expectation (retainedCount ignore test)|) ≤
      2 * Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
  apply Concentration.rare_anchor_concentration n μ (retainedCount ignore test)
    (emptyOutcome shapes D) (fun _ => (D : ℝ) * (H : ℝ))
    (fun _ => (test.card : ℝ) * p₀) (fun _ => rare ignore test)
    M V u hM hV hu
  · intro i ω
    exact retainedCount_empty_abs_le_mul ignore test H hshape ω i
  · intro i ω h
    exact not_rare_retainedCount_eq ignore test ω i h
  · intro i
    exact prob_rare_le_of_pointwise (μ i) ignore test p₀ (hpoint i)
  · intro i
    simpa only [mul_assoc] using hCM
  · simpa [mul_assoc] using hCV

theorem prob_lt_le_prob_centered {Ω : Type*} [Fintype Ω]
    (ν : FiniteLaw Ω) (f : Ω → ℝ) (u : ℝ)
    (hmean : 2 * u ≤ ν.expectation f) :
    ν.prob (fun ω => f ω < u) ≤
      ν.prob (fun ω => u ≤ |f ω - ν.expectation f|) := by
  apply ν.prob_mono
  intro ω hω
  have hneg := neg_le_abs (f ω - ν.expectation f)
  linarith

theorem retainedCount_rare_lower_tail
    (μ : Fin n → FiniteLaw (Outcome shapes D))
    (ignore : Finset (Finset P)) (test : Finset P) (H : ℕ)
    (hshape : ∀ L ∈ shapes, L ∉ ignore → (L ∩ test).card ≤ H)
    (p₀ : ℝ)
    (hpoint : ∀ i x, x ∈ test → (μ i).prob (fun a => x ∈ deleted ignore a) ≤ p₀)
    (M V u : ℝ) (hM : 0 < M) (hV : 0 < V) (hu : 0 < u)
    (hCM : 2 * (D : ℝ) * (H : ℝ) ≤ M)
    (hCV : (n : ℝ) * ((D : ℝ) * (H : ℝ)) ^ 2 *
      ((test.card : ℝ) * p₀) ≤ V)
    (hmean : 2 * u ≤ (FiniteLaw.pi μ).expectation (retainedCount ignore test)) :
    (FiniteLaw.pi μ).prob (fun ω => retainedCount ignore test ω < u) ≤
      2 * Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) :=
  (prob_lt_le_prob_centered (FiniteLaw.pi μ) (retainedCount ignore test) u hmean).trans
    (retainedCount_rare_concentration μ ignore test H hshape p₀ hpoint M V u
      hM hV hu hCM hCV)

theorem expectation_retainedCount_ge_of_base_survival
    (μ : Fin n → FiniteLaw (Outcome shapes D))
    (ignore : Finset (Finset P)) (test : Finset P) (δ : ℝ)
    (hbase : ∀ x ∈ test,
      δ ≤ (FiniteLaw.pi μ).prob (fun ω => x ∈ survivors ∅ ω)) :
    δ * (test.card : ℝ) ≤
      (FiniteLaw.pi μ).expectation (retainedCount ignore test) := by
  rw [expectation_retainedCount]
  calc
    δ * (test.card : ℝ) = ∑ _x ∈ test, δ := by simp [mul_comm]
    _ ≤ ∑ x ∈ test, (FiniteLaw.pi μ).prob (fun ω => x ∈ survivors ignore ω) := by
      apply Finset.sum_le_sum
      intro x hx
      apply (hbase x hx).trans
      apply (FiniteLaw.pi μ).prob_mono
      intro ω hω
      exact survivors_mono_ignore (Finset.empty_subset ignore) ω hω

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_MeanCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover.DeletionProcess

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {D : ℕ} {δ : ℝ} (process : DeletionProcess F D δ)

theorem expectation_base_count (test : Finset (Point F)) :
    process.law.expectation (retainedCount ∅ test) =
      process.survival * (test.card : ℝ) := by
  change (FiniteLaw.pi process.trials).expectation (retainedCount ∅ test) = _
  rw [expectation_retainedCount]
  simp_rw [process.uniformSurvival]
  simp [mul_comm]

theorem expectation_totalCount :
    process.law.expectation
        (retainedCount ∅ (Finset.univ : Finset (Point F))) =
      process.survival * (Fintype.card F : ℝ) ^ 2 := by
  rw [process.expectation_base_count]
  simp only [Finset.card_univ, card_point, Nat.cast_pow]

theorem expectation_base_lineCount (l : AffineLine F) :
    process.law.expectation (retainedCount ∅ (linePoints l)) =
      process.survival * (Fintype.card F : ℝ) := by
  simpa only [card_linePoints] using process.expectation_base_count (linePoints l)

theorem prob_selected_line_le (l : AffineLine F) :
    process.law.prob (fun ω => linePoints l ∈ selected ω) ≤
      (D : ℝ) / (Fintype.card F : ℝ) := by
  change (FiniteLaw.pi process.trials).prob
      (fun ω => linePoints l ∈ selected ω) ≤ _
  calc
    _ = (FiniteLaw.pi process.trials).prob
        (fun ω => ∃ i, ∃ S ∈ (ω i).val, S.val = linePoints l) := by
      congr 1
      funext ω
      exact propext mem_selected
    _ ≤ ∑ i, (FiniteLaw.pi process.trials).prob
        (fun ω => ∃ S ∈ (ω i).val, S.val = linePoints l) :=
      FiniteLaw.prob_exists_le (FiniteLaw.pi process.trials)
        (fun i ω => ∃ S ∈ (ω i).val, S.val = linePoints l)
    _ = ∑ i, (process.trials i).prob
        (fun a => ∃ S ∈ a.val, S.val = linePoints l) := by
      apply Finset.sum_congr rfl
      intro i _
      exact FiniteLaw.prob_pi_coordinate process.trials i
        (fun a => ∃ S ∈ a.val, S.val = linePoints l)
    _ ≤ (D : ℝ) / (Fintype.card F : ℝ) := process.lineCap l

theorem mem_ignored_line_survivors_imp (l : AffineLine F)
    (ω : process.Config) (x : Point F)
    (hx : x ∈ survivors {linePoints l} ω) :
    x ∈ survivors ∅ ω ∨ linePoints l ∈ selected ω := by
  by_cases hselected : linePoints l ∈ selected ω
  · exact Or.inr hselected
  · left
    have heq := survivors_insert_eq_of_not_selected
      (ignore := ∅) (ω := ω) hselected
    simp only [Finset.insert_empty] at heq
    exact heq ▸ hx

theorem prob_mem_ignored_line_le (l : AffineLine F) (x : Point F) :
    process.law.prob (fun ω => x ∈ survivors {linePoints l} ω) ≤
      process.survival + (D : ℝ) / (Fintype.card F : ℝ) := by
  calc
    _ ≤ process.law.prob
        (fun ω => x ∈ survivors ∅ ω ∨ linePoints l ∈ selected ω) :=
      process.law.prob_mono
        (fun ω hx => process.mem_ignored_line_survivors_imp l ω x hx)
    _ ≤ process.law.prob (fun ω => x ∈ survivors ∅ ω) +
        process.law.prob (fun ω => linePoints l ∈ selected ω) :=
      process.law.prob_union_le _ _
    _ ≤ process.survival + (D : ℝ) / (Fintype.card F : ℝ) :=
      add_le_add (process.uniformSurvival x).le (process.prob_selected_line_le l)

theorem expectation_ignored_lineCount_bounds (l : AffineLine F) :
    process.survival * (Fintype.card F : ℝ) ≤
        process.law.expectation (retainedCount {linePoints l} (linePoints l)) ∧
      process.law.expectation (retainedCount {linePoints l} (linePoints l)) ≤
        process.survival * (Fintype.card F : ℝ) + (D : ℝ) := by
  constructor
  · rw [← process.expectation_base_lineCount l]
    apply process.law.expectation_mono
    intro ω
    change ((survivors ∅ ω ∩ linePoints l).card : ℝ) ≤
      ((survivors {linePoints l} ω ∩ linePoints l).card : ℝ)
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hs, hl⟩
    exact Finset.mem_inter.mpr
      ⟨survivors_mono_ignore (Finset.empty_subset {linePoints l}) ω hs, hl⟩
  · change (FiniteLaw.pi process.trials).expectation
        (retainedCount {linePoints l} (linePoints l)) ≤ _
    rw [expectation_retainedCount]
    calc
      _ ≤ ∑ _x ∈ linePoints l,
          (process.survival + (D : ℝ) / (Fintype.card F : ℝ)) :=
        Finset.sum_le_sum fun x _ => process.prob_mem_ignored_line_le l x
      _ = (Fintype.card F : ℝ) *
          (process.survival + (D : ℝ) / (Fintype.card F : ℝ)) := by
        simp only [Finset.sum_const, nsmul_eq_mul, card_linePoints]
      _ = process.survival * (Fintype.card F : ℝ) + (D : ℝ) := by
        have hq : (Fintype.card F : ℝ) ≠ 0 := by
          exact_mod_cast (Fintype.card_ne_zero (α := F))
        rw [mul_add, mul_div_cancel₀ (D : ℝ) hq,
          mul_comm (Fintype.card F : ℝ) process.survival]

end RyserCoveringCounterexample.LineCover.DeletionProcess

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_CountEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover.DeletionProcess

variable {F : Type*} [Field F] [Fintype F] [instDecidableEqF : DecidableEq F]
  {D : ℕ} {δ : ℝ} (process : DeletionProcess F D δ)

private theorem fieldCard_pos_real : 0 < (Fintype.card F : ℝ) := let _ := instDecidableEqF; by
  exact_mod_cast Fintype.card_pos (α := F)

theorem total_count_concentration (hD : 0 < D) (u : ℝ) (hu : 0 < u) :
    process.law.prob (fun ω => u ≤
        |retainedCount ∅ Finset.univ ω -
          process.survival * (Fintype.card F : ℝ) ^ 2|) ≤
      2 * Real.exp (-(1 / 4 : ℝ) *
        min (u ^ 2 / (4 * (D : ℝ) ^ 5 * (Fintype.card F : ℝ) ^ 3))
          (u / (2 * (D : ℝ) ^ 2 * (Fintype.card F : ℝ)))) := by
  have hDr : 0 < (D : ℝ) := by exact_mod_cast hD
  have hq := fieldCard_pos_real (F := F)
  have hn : (process.trialsCount : ℝ) ≤ (D : ℝ) * (Fintype.card F : ℝ) := by
    exact_mod_cast process.trialsCount_le
  have hC : 2 * (D : ℝ) * ((D * Fintype.card F : ℕ) : ℝ) =
      2 * (D : ℝ) ^ 2 * (Fintype.card F : ℝ) := by
    rw [Nat.cast_mul]
    ring
  have hV : (process.trialsCount : ℝ) *
      (2 * (D : ℝ) * ((D * Fintype.card F : ℕ) : ℝ)) ^ 2 ≤
        4 * (D : ℝ) ^ 5 * (Fintype.card F : ℝ) ^ 3 := by
    rw [hC]
    calc
      _ ≤ ((D : ℝ) * (Fintype.card F : ℝ)) *
          (2 * (D : ℝ) ^ 2 * (Fintype.card F : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_right hn (sq_nonneg _)
      _ = _ := by ring
  have h := retainedCount_coordinate_concentration process.trials ∅ Finset.univ
    (D * Fintype.card F)
    (fun S hS _ => by simpa using process.shapeSize S hS)
    (2 * (D : ℝ) ^ 2 * (Fintype.card F : ℝ))
    (4 * (D : ℝ) ^ 5 * (Fintype.card F : ℝ) ^ 3) u
    (by positivity) (by positivity) hu hC.le hV
  change process.law.prob (fun ω => u ≤
      |retainedCount ∅ Finset.univ ω -
        process.law.expectation (retainedCount ∅ Finset.univ)|) ≤ _ at h
  rw [process.expectation_totalCount] at h
  exact h

theorem ignored_line_count_concentration (hD : 0 < D) (l : AffineLine F)
    (u : ℝ) (hu : 0 < u) :
    process.law.prob (fun ω => u ≤
        |retainedCount {linePoints l} (linePoints l) ω -
          process.law.expectation (retainedCount {linePoints l} (linePoints l))|) ≤
      2 * Real.exp (-(1 / 4 : ℝ) *
        min (u ^ 2 / (4 * (D : ℝ) ^ 5 * (Fintype.card F : ℝ)))
          (u / (2 * (D : ℝ) ^ 2))) := by
  have hDr : 0 < (D : ℝ) := by exact_mod_cast hD
  have hq := fieldCard_pos_real (F := F)
  have hn : (process.trialsCount : ℝ) ≤ (D : ℝ) * (Fintype.card F : ℝ) := by
    exact_mod_cast process.trialsCount_le
  have hC : 2 * (D : ℝ) * (D : ℝ) = 2 * (D : ℝ) ^ 2 := by ring
  have hV : (process.trialsCount : ℝ) * (2 * (D : ℝ) * (D : ℝ)) ^ 2 ≤
      4 * (D : ℝ) ^ 5 * (Fintype.card F : ℝ) := by
    calc
      _ ≤ ((D : ℝ) * (Fintype.card F : ℝ)) *
          (2 * (D : ℝ) * (D : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_right hn (sq_nonneg _)
      _ = _ := by ring
  exact retainedCount_coordinate_concentration process.trials {linePoints l}
    (linePoints l) D
    (fun S hS hnot => process.sparse S hS l (by simpa using hnot))
    (2 * (D : ℝ) ^ 2) (4 * (D : ℝ) ^ 5 * (Fintype.card F : ℝ)) u
    (by positivity) (by positivity) hu hC.le hV

end RyserCoveringCounterexample.LineCover.DeletionProcess

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_TailNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.LineCover

open Filter Topology

theorem tendsto_log_pow_mul_rpow_neg_atTop (k : ℕ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun q : ℝ => (Real.log q) ^ k * q ^ (-a)) atTop (𝓝 0) := by
  have hdiv : Tendsto (fun q : ℝ => (Real.log q) ^ k / q ^ a) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (s := a) (k : ℝ) ha).tendsto_div_nhds_zero
  refine hdiv.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with q hq
  simp only [Real.rpow_neg hq, div_eq_mul_inv]

theorem tendsto_rpow_mul_exp_neg_rpow_atTop (r : ℝ) {a c : ℝ}
    (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun q : ℝ => q ^ r * Real.exp (-c * q ^ a)) atTop (𝓝 0) := by
  refine ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (r / a) c hc).comp (tendsto_rpow_atTop ha)).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with q hq
  dsimp only [Function.comp_apply]
  rw [← Real.rpow_mul hq, mul_div_cancel₀ r ha.ne']

theorem tendsto_polynomial_mul_exp_neg_rpow_atTop (p : Polynomial ℝ) {a c : ℝ}
    (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun q : ℝ => p.eval q * Real.exp (-c * q ^ a)) atTop (𝓝 0) := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr =>
      simpa only [Polynomial.eval_add, add_mul, add_zero] using hp.add hr
  | monomial k b =>
      simpa only [Polynomial.eval_monomial, Real.rpow_natCast, mul_assoc, mul_zero] using
        (tendsto_rpow_mul_exp_neg_rpow_atTop (k : ℝ) ha hc).const_mul b

theorem tendsto_count_failure_atTop {D ε : ℝ} (hD : 0 < D) (hε : 0 < ε) :
    Tendsto (fun q : ℝ =>
      2 * (1 + q * (q + 1)) * Real.exp (-q ^ (2 * ε) / (16 * D ^ 5)))
      atTop (𝓝 0) := by
  have hc : 0 < (16 * D ^ 5)⁻¹ := by positivity
  have ha : 0 < 2 * ε := by positivity
  have h := tendsto_polynomial_mul_exp_neg_rpow_atTop
    (2 * (1 + Polynomial.X * (Polynomial.X + 1)) : Polynomial ℝ) ha hc
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h

theorem tendsto_logarithmicSampleSize_atTop {A : ℝ} (hA : 0 < A) :
    Tendsto (fun q : ℝ => (logarithmicSampleSize A q : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono (fun q => Nat.le_ceil (A * Real.log q))
  exact Real.tendsto_log_atTop.const_mul_atTop hA

theorem tendsto_sampleSize_pow_mul_rpow_neg_atTop (k : ℕ) {A a : ℝ}
    (hA : 0 < A) (ha : 0 < a) :
    Tendsto (fun q : ℝ => (logarithmicSampleSize A q : ℝ) ^ k * q ^ (-a))
      atTop (𝓝 0) := by
  have hbound : Tendsto
      (fun q : ℝ => (A + 1) ^ k * ((Real.log q) ^ k * q ^ (-a)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_log_pow_mul_rpow_neg_atTop k ha).const_mul
      ((A + 1) ^ k)
  apply squeeze_zero' ?_ ?_ hbound
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with q hq
    exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg hq _)
  · filter_upwards [eventually_ge_atTop (0 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop 1] with q hq hlog
    have harg : 0 ≤ A * Real.log q := mul_nonneg hA.le (by linarith)
    have hceil : (logarithmicSampleSize A q : ℝ) ≤ A * Real.log q + 1 :=
      (Nat.ceil_lt_add_one harg).le
    have hs : (logarithmicSampleSize A q : ℝ) ≤ (A + 1) * Real.log q := by
      nlinarith
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg (logarithmicSampleSize A q)) hs k
    simpa only [mul_pow, mul_assoc] using
      mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hq (-a))

theorem log_affine_line_count_le {q : ℝ} (hq : 4 ≤ q) :
    Real.log (q * (q + 1)) ≤ (5 / 2 : ℝ) * Real.log q := by
  have hq0 : 0 < q := by linarith
  have hq1 : 0 < q + 1 := by linarith
  have hsmall := Real.log_le_log hq1 (show q + 1 ≤ 2 * q by linarith)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hq0.ne'] at hsmall
  have hlarge := Real.log_le_log
    (show 0 < (2 : ℝ) ^ 2 by norm_num) (show (2 : ℝ) ^ 2 ≤ q by nlinarith)
  rw [Real.log_pow] at hlarge
  norm_num only [Nat.cast_ofNat] at hlarge
  rw [Real.log_mul hq0.ne' hq1.ne']
  nlinarith

theorem tuple_failure_le_envelope {q A c0 : ℝ} (t : ℕ) (hq : 4 ≤ q)
    (hA : 0 < A) (ht : A * Real.log q ≤ (t : ℝ)) :
    2 * (q * (q + 1)) ^ (2 * t) * Real.exp (-c0 * (t : ℝ) ^ 2) ≤
      2 * Real.exp (-(c0 - 5 / A) * (t : ℝ) ^ 2) := by
  have hq0 : 0 < q := by linarith
  have hb : 0 < q * (q + 1) := mul_pos hq0 (by linarith)
  have hlog := log_affine_line_count_le hq
  have hcount : (q * (q + 1)) ^ (2 * t) ≤
      Real.exp (5 * (t : ℝ) * Real.log q) := by
    rw [← Real.exp_log (pow_pos hb (2 * t))]
    apply Real.exp_le_exp.mpr
    rw [Real.log_pow]
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg t)]
  have hlogDiv : Real.log q ≤ (t : ℝ) / A :=
    (le_div_iff₀ hA).2 (by nlinarith [ht])
  have hexponent : 5 * (t : ℝ) * Real.log q - c0 * (t : ℝ) ^ 2 ≤
      -(c0 - 5 / A) * (t : ℝ) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hlogDiv
      (show 0 ≤ 5 * (t : ℝ) by positivity)
    simp only [div_eq_mul_inv] at hmul ⊢
    nlinarith
  calc
    2 * (q * (q + 1)) ^ (2 * t) * Real.exp (-c0 * (t : ℝ) ^ 2) ≤
        2 * Real.exp (5 * (t : ℝ) * Real.log q) *
          Real.exp (-c0 * (t : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcount (by norm_num)) (Real.exp_pos _).le
    _ = 2 * Real.exp (5 * (t : ℝ) * Real.log q - c0 * (t : ℝ) ^ 2) := by
      rw [mul_assoc, ← Real.exp_add, sub_eq_add_neg, neg_mul]
    _ ≤ 2 * Real.exp (-(c0 - 5 / A) * (t : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (by norm_num)

theorem tendsto_tuple_failure_atTop {A c0 : ℝ} (hc0 : 0 < c0) (hA : 5 / c0 < A) :
    Tendsto (fun q : ℝ =>
      2 * (q * (q + 1)) ^ (2 * logarithmicSampleSize A q) *
        Real.exp (-c0 * (logarithmicSampleSize A q : ℝ) ^ 2)) atTop (𝓝 0) := by
  have hA0 : 0 < A := lt_trans (div_pos (by norm_num) hc0) hA
  have hfive : 5 < A * c0 := (div_lt_iff₀ hc0).mp hA
  have hcoefficient : 0 < c0 - 5 / A := by
    have hdiv : 5 / A < c0 := (div_lt_iff₀ hA0).2 (by nlinarith)
    linarith
  have hsquare : Tendsto
      (fun q : ℝ => (logarithmicSampleSize A q : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp
      (tendsto_logarithmicSampleSize_atTop hA0)
  have henvelope : Tendsto
      (fun q : ℝ => 2 * Real.exp (-(c0 - 5 / A) *
        (logarithmicSampleSize A q : ℝ) ^ 2)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Real.rpow_zero, one_mul, mul_zero] using
      ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        0 (c0 - 5 / A) hcoefficient).comp hsquare).const_mul (2 : ℝ)
  apply squeeze_zero' ?_ ?_ henvelope
  · filter_upwards [eventually_ge_atTop (4 : ℝ)] with q hq
    have hq0 : 0 ≤ q := by linarith
    positivity
  · filter_upwards [eventually_ge_atTop (4 : ℝ)] with q hq
    exact tuple_failure_le_envelope (logarithmicSampleSize A q) hq hA0
      (Nat.le_ceil (A * Real.log q))

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_CountTailNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.LineCover

theorem count_variance_ratio {q D ε k : ℝ} (hq : 0 < q) (hD : D ≠ 0) :
    (q ^ (k + 1 / 2 + ε)) ^ 2 / (4 * D ^ 5 * q ^ (2 * k + 1)) =
      q ^ (2 * ε) / (4 * D ^ 5) := by
  have hp : (q ^ (k + 1 / 2 + ε)) ^ 2 =
      q ^ (2 * ε) * q ^ (2 * k + 1) := by
    calc
      _ = q ^ ((k + 1 / 2 + ε) * (2 : ℝ)) := by
        rw [Real.rpow_mul hq.le, Real.rpow_two]
      _ = q ^ (2 * ε + (2 * k + 1)) := by congr 1; ring
      _ = _ := Real.rpow_add hq _ _
  rw [hp]
  have hpow : q ^ (2 * k + 1) ≠ 0 := (Real.rpow_pos_of_pos hq _).ne'
  field_simp [hD, hpow]

theorem count_coordinate_ratio {q D ε k : ℝ} (hq : 0 < q) (hD : D ≠ 0) :
    q ^ (k + 1 / 2 + ε) / (2 * D ^ 2 * q ^ k) =
      q ^ (1 / 2 + ε) / (2 * D ^ 2) := by
  rw [show k + 1 / 2 + ε = (1 / 2 + ε) + k by ring, Real.rpow_add hq]
  have hpow : q ^ k ≠ 0 := (Real.rpow_pos_of_pos hq _).ne'
  field_simp [hD, hpow]

theorem count_variance_ratio_le_coordinate {q D ε : ℝ}
    (hq : 1 ≤ q) (hD : 1 ≤ D) (hε : ε ≤ 1 / 2) :
    q ^ (2 * ε) / (4 * D ^ 5) ≤ q ^ (1 / 2 + ε) / (2 * D ^ 2) := by
  have hD0 : 0 < D := lt_of_lt_of_le (by norm_num) hD
  have hq0 : 0 ≤ q := le_trans (by norm_num) hq
  have hp : q ^ (2 * ε) ≤ q ^ (1 / 2 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hq (by linarith)
  have hDpow : D ^ 2 ≤ D ^ 5 := by
    calc
      D ^ 2 = D ^ 2 * 1 := by ring
      _ ≤ D ^ 2 * D ^ 3 := mul_le_mul_of_nonneg_left (one_le_pow₀ hD) (sq_nonneg D)
      _ = D ^ 5 := by ring
  have hden : 2 * D ^ 2 ≤ 4 * D ^ 5 := by nlinarith [sq_nonneg D]
  exact div_le_div₀ (Real.rpow_nonneg hq0 _) hp (by positivity) hden

theorem count_tail_le_stretched_exp {q D ε k : ℝ}
    (hq : 1 ≤ q) (hD : 1 ≤ D) (hε : ε ≤ 1 / 2) :
    2 * Real.exp (-(1 / 4 : ℝ) *
      min ((q ^ (k + 1 / 2 + ε)) ^ 2 / (4 * D ^ 5 * q ^ (2 * k + 1)))
        (q ^ (k + 1 / 2 + ε) / (2 * D ^ 2 * q ^ k))) ≤
      2 * Real.exp (-q ^ (2 * ε) / (16 * D ^ 5)) := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hD0 : D ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hD)
  rw [count_variance_ratio hq0 hD0, count_coordinate_ratio hq0 hD0,
    min_eq_left (count_variance_ratio_le_coordinate hq hD hε)]
  have hexponent : -(1 / 4 : ℝ) * (q ^ (2 * ε) / (4 * D ^ 5)) =
      -q ^ (2 * ε) / (16 * D ^ 5) := by
    field_simp [hD0]
    ring
  rw [hexponent]

theorem total_count_tail_le_stretched_exp {q ε : ℝ} {D : ℕ}
    (hq : 1 ≤ q) (hD : 1 ≤ D) (hε : ε ≤ 1 / 2) :
    2 * Real.exp (-(1 / 4 : ℝ) *
      min ((q ^ (3 / 2 + ε)) ^ 2 / (4 * (D : ℝ) ^ 5 * q ^ 3))
        (q ^ (3 / 2 + ε) / (2 * (D : ℝ) ^ 2 * q))) ≤
      2 * Real.exp (-q ^ (2 * ε) / (16 * (D : ℝ) ^ 5)) := by
  have hDr : 1 ≤ (D : ℝ) := by exact_mod_cast hD
  simpa only [one_add_one_eq_two, mul_one, Real.rpow_one,
    show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num,
    show (2 : ℝ) + 1 = (3 : ℕ) by norm_num, Real.rpow_natCast] using
    (count_tail_le_stretched_exp (q := q) (D := (D : ℝ)) (ε := ε) (k := 1) hq hDr hε)

theorem line_count_tail_le_stretched_exp {q ε : ℝ} {D : ℕ}
    (hq : 1 ≤ q) (hD : 1 ≤ D) (hε : ε ≤ 1 / 2) :
    2 * Real.exp (-(1 / 4 : ℝ) *
      min ((q ^ (1 / 2 + ε)) ^ 2 / (4 * (D : ℝ) ^ 5 * q))
        (q ^ (1 / 2 + ε) / (2 * (D : ℝ) ^ 2))) ≤
      2 * Real.exp (-q ^ (2 * ε) / (16 * (D : ℝ) ^ 5)) := by
  have hDr : 1 ≤ (D : ℝ) := by exact_mod_cast hD
  simpa only [mul_zero, zero_add, Real.rpow_zero, Real.rpow_one, mul_one] using
    (count_tail_le_stretched_exp (q := q) (D := (D : ℝ)) (ε := ε) (k := 0) hq hDr hε)

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_GoodCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {D : ℕ} {δ : ℝ}

namespace DeletionProcess

variable (process : DeletionProcess F D δ)

theorem prob_not_goodCounts (ε : ℝ) (hD : 1 ≤ D)
    (_hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    process.law.prob (fun ω => ¬ GoodCounts process ε ω) ≤
      2 * (1 + (Fintype.card F : ℝ) * ((Fintype.card F : ℝ) + 1)) *
        Real.exp (-(Fintype.card F : ℝ) ^ (2 * ε) / (16 * (D : ℝ) ^ 5)) := by
  have hqNat : 1 ≤ Fintype.card F :=
    Nat.succ_le_iff.mpr (Fintype.card_pos (α := F))
  have hq : 1 ≤ (Fintype.card F : ℝ) := by exact_mod_cast hqNat
  have hq0 : 0 < (Fintype.card F : ℝ) := lt_of_lt_of_le zero_lt_one hq
  have hD0 : 0 < D := lt_of_lt_of_le Nat.zero_lt_one hD
  let T : process.Config → Prop := fun ω =>
    (Fintype.card F : ℝ) ^ ((3 : ℝ) / 2 + ε) ≤
      |((survivors ∅ ω).card : ℝ) - process.survival * (Fintype.card F : ℝ) ^ 2|
  let L : AffineLine F → process.Config → Prop := fun l ω =>
    (Fintype.card F : ℝ) ^ ((1 : ℝ) / 2 + ε) ≤
      |retainedCount {linePoints l} (linePoints l) ω -
        process.law.expectation (retainedCount {linePoints l} (linePoints l))|
  let B : ℝ := 2 * Real.exp
    (-(Fintype.card F : ℝ) ^ (2 * ε) / (16 * (D : ℝ) ^ 5))
  have htotal : process.law.prob T ≤ B := by
    have h := (process.total_count_concentration hD0
      ((Fintype.card F : ℝ) ^ ((3 : ℝ) / 2 + ε))
      (Real.rpow_pos_of_pos hq0 _)).trans
        (total_count_tail_le_stretched_exp hq hD hεhalf)
    simpa only [T, B, retainedCount, Finset.inter_univ] using h
  have hline (l : AffineLine F) : process.law.prob (L l) ≤ B := by
    exact (process.ignored_line_count_concentration hD0 l
      ((Fintype.card F : ℝ) ^ ((1 : ℝ) / 2 + ε))
      (Real.rpow_pos_of_pos hq0 _)).trans
        (line_count_tail_le_stretched_exp hq hD hεhalf)
  have hcover : ∀ ω, ¬ GoodCounts process ε ω → T ω ∨ ∃ l, L l ω := by
    intro ω hbad
    by_cases ht : T ω
    · exact Or.inl ht
    · right
      by_contra hlines
      apply hbad
      refine ⟨?_, ?_⟩
      · exact (lt_of_not_ge ht).le
      · intro l
        have hl : ¬ L l ω := fun h => hlines ⟨l, h⟩
        have habs :
            |retainedCount {linePoints l} (linePoints l) ω -
              process.law.expectation (retainedCount {linePoints l} (linePoints l))| ≤
            (Fintype.card F : ℝ) ^ ((1 : ℝ) / 2 + ε) := (lt_of_not_ge hl).le
        obtain ⟨hlo, hhi⟩ := abs_le.mp habs
        obtain ⟨hmlo, hmhi⟩ := process.expectation_ignored_lineCount_bounds l
        constructor <;> linarith
  calc
    _ ≤ process.law.prob (fun ω => T ω ∨ ∃ l, L l ω) :=
      process.law.prob_mono hcover
    _ ≤ process.law.prob T + process.law.prob (fun ω => ∃ l, L l ω) :=
      process.law.prob_union_le T (fun ω => ∃ l, L l ω)
    _ ≤ B + ∑ l, process.law.prob (L l) :=
      add_le_add htotal (FiniteLaw.prob_exists_le process.law L)
    _ ≤ B + ∑ _l : AffineLine F, B :=
      add_le_add le_rfl (Finset.sum_le_sum fun l _ => hline l)
    _ = (1 + (Fintype.card (AffineLine F) : ℝ)) * B := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ = _ := by
      simp only [card_affineLine, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      dsimp only [B]
      ring

end DeletionProcess
end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_TupleConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

theorem countTailConstant_pos {D H : ℕ} {δ : ℝ}
    (hD : 0 < D) (hH : 0 < H) (hδ : 0 < δ) :
    0 < countTailConstant D H δ := by
  have hDr : 0 < (D : ℝ) := by exact_mod_cast hD
  have hHr : 0 < (H : ℝ) := by exact_mod_cast hH
  unfold countTailConstant
  apply lt_min <;> positivity

theorem tupleTailConstant_pos {D h : ℕ} {δ : ℝ}
    (hD : 0 < D) (hh : 0 < h) (hδ : 0 < δ) :
    0 < tupleTailConstant D h δ :=
  countTailConstant_pos hD
    (Nat.mul_pos (Nat.mul_pos (by decide) hD) hh) hδ

private theorem variance_budget_real (n D q C t : ℝ)
    (hD : 0 ≤ D) (hq : 0 < q) (hn : n ≤ D * q) :
    n * C ^ 2 * (t ^ 2 * (D / q)) ≤ D ^ 2 * C ^ 2 * t ^ 2 := by
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hscale : 0 ≤ C ^ 2 * (t ^ 2 * (D / q)) :=
    mul_nonneg (sq_nonneg C)
      (mul_nonneg (sq_nonneg t) (div_nonneg hD (le_of_lt hq)))
  calc
    n * C ^ 2 * (t ^ 2 * (D / q)) =
        n * (C ^ 2 * (t ^ 2 * (D / q))) := by ring
    _ ≤ (D * q) * (C ^ 2 * (t ^ 2 * (D / q))) :=
      mul_le_mul_of_nonneg_right hn hscale
    _ = D ^ 2 * C ^ 2 * t ^ 2 := by
      field_simp [hq0]

private theorem tail_exponent_identity (D C T δ : ℝ)
    (hD : 0 < D) (hC : 0 < C) (hT : 0 < T) :
    -(1 / 4 : ℝ) *
        min (((δ * T ^ 2 / 2) ^ 2) / (D ^ 2 * C ^ 2 * T ^ 2))
          ((δ * T ^ 2 / 2) / (2 * C)) =
      -(min (δ ^ 2 / (16 * D ^ 2 * C ^ 2))
          (δ / (16 * C))) * T ^ 2 := by
  let a : ℝ := δ ^ 2 / (16 * D ^ 2 * C ^ 2)
  let b : ℝ := δ / (16 * C)
  have hA :
      ((δ * T ^ 2 / 2) ^ 2) / (D ^ 2 * C ^ 2 * T ^ 2) =
        4 * a * T ^ 2 := by
    dsimp [a]
    field_simp [ne_of_gt hD, ne_of_gt hC, ne_of_gt hT]; ring
  have hB : (δ * T ^ 2 / 2) / (2 * C) = 4 * b * T ^ 2 := by
    dsimp [b]
    field_simp [ne_of_gt hC]; ring
  change -(1 / 4 : ℝ) * min _ _ = -(min a b) * T ^ 2
  rw [hA, hB]
  rcases le_total a b with h | h
  · have hs : 4 * a * T ^ 2 ≤ 4 * b * T ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 4))
        (sq_nonneg T)
    rw [min_eq_left hs, min_eq_left h]
    ring
  · have hs : 4 * b * T ^ 2 ≤ 4 * a * T ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 4))
        (sq_nonneg T)
    rw [min_eq_right hs, min_eq_right h]
    ring

section General

variable {P : Type*} [Fintype P] [DecidableEq P]
  {shapes : Finset (Finset P)} {D n : ℕ}

theorem retainedCount_square_lower_tail
    (μ : Fin n → FiniteLaw (Outcome shapes D))
    (ignore : Finset (Finset P)) (test : Finset P) (H q t : ℕ) (δ : ℝ)
    (hD : 0 < D) (hH : 0 < H) (hq : 0 < q) (ht : 0 < t) (hδ : 0 < δ)
    (hn : n ≤ D * q) (hcard : test.card = t * t)
    (hshape : ∀ L ∈ shapes, L ∉ ignore → (L ∩ test).card ≤ H)
    (hpoint : ∀ i x, x ∈ test →
      (μ i).prob (fun a => x ∈ deleted ∅ a) ≤ (D : ℝ) / (q : ℝ))
    (hbase : ∀ x ∈ test,
      δ ≤ (FiniteLaw.pi μ).prob (fun ω => x ∈ survivors ∅ ω)) :
    (FiniteLaw.pi μ).prob
        (fun ω => retainedCount ignore test ω < δ * (t : ℝ) ^ 2 / 2) ≤
      2 * Real.exp (-(countTailConstant D H δ) * (t : ℝ) ^ 2) := by
  let C : ℝ := (D : ℝ) * (H : ℝ)
  have hDr : 0 < (D : ℝ) := by exact_mod_cast hD
  have hHr : 0 < (H : ℝ) := by exact_mod_cast hH
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hq
  have htr : 0 < (t : ℝ) := by exact_mod_cast ht
  have hC : 0 < C := mul_pos hDr hHr
  have hnr : (n : ℝ) ≤ (D : ℝ) * (q : ℝ) := by exact_mod_cast hn
  have hcardReal : (test.card : ℝ) = (t : ℝ) ^ 2 := by
    rw [hcard, Nat.cast_mul, pow_two]
  have hpointIgnore : ∀ i x, x ∈ test →
      (μ i).prob (fun a => x ∈ deleted ignore a) ≤ (D : ℝ) / (q : ℝ) := by
    intro i x hx
    calc
      _ ≤ (μ i).prob (fun a => x ∈ deleted ∅ a) := by
        apply (μ i).prob_mono
        intro a hxa
        rcases mem_deleted.mp hxa with ⟨L, hL, hnot, hxL⟩
        exact mem_deleted.mpr ⟨L, hL, by simp, hxL⟩
      _ ≤ _ := hpoint i x hx
  have hCV : (n : ℝ) * C ^ 2 * ((test.card : ℝ) * ((D : ℝ) / (q : ℝ))) ≤
      (D : ℝ) ^ 2 * C ^ 2 * (t : ℝ) ^ 2 := by
    rw [hcardReal]
    exact variance_budget_real (n : ℝ) (D : ℝ) (q : ℝ) C (t : ℝ)
      hDr.le hqr hnr
  have hmean0 := expectation_retainedCount_ge_of_base_survival μ ignore test δ hbase
  rw [hcardReal] at hmean0
  have hmean : 2 * (δ * (t : ℝ) ^ 2 / 2) ≤
      (FiniteLaw.pi μ).expectation (retainedCount ignore test) := by
    calc
      _ = δ * (t : ℝ) ^ 2 := by ring
      _ ≤ _ := hmean0
  have htail := retainedCount_rare_lower_tail μ ignore test H hshape
    ((D : ℝ) / (q : ℝ)) hpointIgnore
    (2 * C) ((D : ℝ) ^ 2 * C ^ 2 * (t : ℝ) ^ 2)
    (δ * (t : ℝ) ^ 2 / 2)
    (by positivity) (by positivity) (by positivity)
    (le_of_eq (by dsimp [C]; ring)) hCV hmean
  apply htail.trans_eq
  apply congrArg (fun z : ℝ => 2 * Real.exp z)
  simpa only [countTailConstant, C] using
    tail_exponent_identity (D : ℝ) C (t : ℝ) δ hDr hC htr

end General

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {shapes : Finset (Finset (Point F))} {D n h t : ℕ}

theorem admissibleTuple_lower_tail
    (μ : Fin n → FiniteLaw (Outcome shapes D))
    (a : LineTuple F t) (ha : AdmissibleTuple shapes D h a)
    (δ : ℝ) (hD : 0 < D) (hh : 0 < h) (ht : 0 < t) (hδ : 0 < δ)
    (hn : n ≤ D * Fintype.card F)
    (hpoint : ∀ i x,
      (μ i).prob (fun b => x ∈ deleted ∅ b) ≤ (D : ℝ) / (Fintype.card F : ℝ))
    (hbase : ∀ x,
      δ ≤ (FiniteLaw.pi μ).prob (fun ω => x ∈ survivors ∅ ω)) :
    (FiniteLaw.pi μ).prob (fun ω =>
        retainedCount (tupleShapes a) (crossPoints a) ω < δ * (t : ℝ) ^ 2 / 2) ≤
      2 * Real.exp (-(tupleTailConstant D h δ) * (t : ℝ) ^ 2) := by
  have hH : 0 < 2 * D * h := Nat.mul_pos (Nat.mul_pos (by decide) hD) hh
  have hq : 0 < Fintype.card F := Fintype.card_pos_iff.mpr ⟨0⟩
  simpa only [tupleTailConstant] using retainedCount_square_lower_tail
    μ (tupleShapes a) (crossPoints a) (2 * D * h) (Fintype.card F) t δ
    hD hH hq ht hδ hn ha.2.1 ha.2.2
    (fun i x _ => hpoint i x) (fun x _ => hbase x)

theorem prob_exists_admissibleTuple_bad_le
    (μ : Fin n → FiniteLaw (Outcome shapes D))
    (δ : ℝ) (hD : 0 < D) (hh : 0 < h) (ht : 0 < t) (hδ : 0 < δ)
    (hn : n ≤ D * Fintype.card F)
    (hpoint : ∀ i x,
      (μ i).prob (fun b => x ∈ deleted ∅ b) ≤ (D : ℝ) / (Fintype.card F : ℝ))
    (hbase : ∀ x,
      δ ≤ (FiniteLaw.pi μ).prob (fun ω => x ∈ survivors ∅ ω)) :
    (FiniteLaw.pi μ).prob (fun ω => ∃ a : LineTuple F t,
        AdmissibleTuple shapes D h a ∧
          retainedCount (tupleShapes a) (crossPoints a) ω < δ * (t : ℝ) ^ 2 / 2) ≤
      2 * (Fintype.card (LineTuple F t) : ℝ) *
        Real.exp (-(tupleTailConstant D h δ) * (t : ℝ) ^ 2) := by
  classical
  calc
    _ ≤ ∑ a : LineTuple F t, (FiniteLaw.pi μ).prob (fun ω =>
        AdmissibleTuple shapes D h a ∧
          retainedCount (tupleShapes a) (crossPoints a) ω < δ * (t : ℝ) ^ 2 / 2) :=
      (FiniteLaw.pi μ).prob_exists_le _
    _ ≤ ∑ _a : LineTuple F t,
        2 * Real.exp (-(tupleTailConstant D h δ) * (t : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro a _
      by_cases ha : AdmissibleTuple shapes D h a
      · calc
          _ ≤ (FiniteLaw.pi μ).prob (fun ω =>
              retainedCount (tupleShapes a) (crossPoints a) ω <
                δ * (t : ℝ) ^ 2 / 2) := by
            apply (FiniteLaw.pi μ).prob_mono
            intro ω hω
            exact hω.2
          _ ≤ _ := admissibleTuple_lower_tail μ a ha δ hD hh ht hδ hn hpoint hbase
      · simp only [ha, false_and, FiniteLaw.prob_false]
        positivity
    _ = _ := by simp [mul_assoc, mul_comm]

theorem card_lineTuple_le (F : Type*) [Field F] [Fintype F]
    [DecidableEq F] (t : ℕ) :
    Fintype.card (LineTuple F t) ≤
      (Fintype.card F * (Fintype.card F + 1)) ^ (2 * t) := by
  classical
  calc
    Fintype.card (LineTuple F t) ≤
        Fintype.card ((Fin t ⊕ Fin t) → AffineLine F) :=
      Fintype.card_le_of_injective
        (fun a : LineTuple F t =>
          (a : (Fin t ⊕ Fin t) → AffineLine F))
        Function.Embedding.coe_injective
    _ = _ := by
      rw [Fintype.card_fun]
      simp [AffineLine, Direction, two_mul, Nat.mul_comm]

theorem prob_exists_admissibleTuple_bad_le_card_bound
    (μ : Fin n → FiniteLaw (Outcome shapes D))
    (δ : ℝ) (hD : 0 < D) (hh : 0 < h) (ht : 0 < t) (hδ : 0 < δ)
    (hn : n ≤ D * Fintype.card F)
    (hpoint : ∀ i x,
      (μ i).prob (fun b => x ∈ deleted ∅ b) ≤ (D : ℝ) / (Fintype.card F : ℝ))
    (hbase : ∀ x,
      δ ≤ (FiniteLaw.pi μ).prob (fun ω => x ∈ survivors ∅ ω)) :
    (FiniteLaw.pi μ).prob (fun ω => ∃ a : LineTuple F t,
        AdmissibleTuple shapes D h a ∧
          retainedCount (tupleShapes a) (crossPoints a) ω < δ * (t : ℝ) ^ 2 / 2) ≤
      2 * ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) + 1)) ^ (2 * t) *
        Real.exp (-(tupleTailConstant D h δ) * (t : ℝ) ^ 2) := by
  have hcard : (Fintype.card (LineTuple F t) : ℝ) ≤
      ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) + 1)) ^ (2 * t) := by
    exact_mod_cast card_lineTuple_le F t
  apply (prob_exists_admissibleTuple_bad_le μ δ hD hh ht hδ hn hpoint hbase).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcard (by norm_num : (0 : ℝ) ≤ 2))
    (Real.exp_pos _).le

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_GoodTuples
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {D : ℕ} {δ : ℝ}

theorem not_goodTuples_iff (process : DeletionProcess F D δ) (h t : ℕ)
    (ω : process.Config) :
    ¬ GoodTuples process h t ω ↔
      ∃ a : LineTuple F t, AdmissibleTuple process.shapes D h a ∧
        retainedCount (tupleShapes a) (crossPoints a) ω < δ * (t : ℝ) ^ 2 / 2 := by
  classical
  simp only [GoodTuples, not_forall, not_le, exists_prop]

theorem DeletionProcess.prob_not_goodTuples (process : DeletionProcess F D δ)
    (h t : ℕ) (hD : 0 < D) (hh : 0 < h) (ht : 0 < t) (hδ : 0 < δ) :
    process.law.prob (fun ω => ¬ GoodTuples process h t ω) ≤
      2 * ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) + 1)) ^ (2 * t) *
        Real.exp (-(tupleTailConstant D h δ) * (t : ℝ) ^ 2) := by
  calc
    _ ≤ process.law.prob (fun ω => ∃ a : LineTuple F t,
        AdmissibleTuple process.shapes D h a ∧
          retainedCount (tupleShapes a) (crossPoints a) ω < δ * (t : ℝ) ^ 2 / 2) := by
      apply process.law.prob_mono
      intro ω hω
      exact (not_goodTuples_iff process h t ω).mp hω
    _ ≤ _ := prob_exists_admissibleTuple_bad_le_card_bound process.trials δ
      hD hh ht hδ process.trialsCount_le process.pointCap
      (fun x => process.point_survival_ge x)

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_Parameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Incidence
noncomputable section
open Filter Topology

theorem savingExponent_lt_tenth : savingExponent < 1 / 10 := by
  norm_num [savingExponent]

end
end RyserCoveringCounterexample.Incidence

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_FailureNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.LineCover

open Filter Topology

theorem low_occupancy_decay_pos (D : ℕ) {κ : ℝ} (hκ : κ ≤ 1) :
    0 < ((10 * (D + 1) : ℕ) : ℝ) * (1 / 2 - κ / 4) - D := by
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hmul := mul_nonneg (by positivity : 0 ≤ (D : ℝ) + 1)
    (sub_nonneg.mpr hκ)
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  nlinarith

theorem high_occupancy_decay_pos (D : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    0 < ((10 * (D + 1) : ℕ) : ℝ) * (1 / 2 + κ / 4) - D := by
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hmul := mul_pos (by positivity : 0 < (D : ℝ) + 1) hκ
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  nlinarith

theorem tendsto_lowFailureEnvelope_atTop (D : ℕ) (δ : ℝ) {A κ : ℝ}
    (hA : 0 < A) (hκ : 0 < κ) (hκone : κ ≤ 1) :
    Tendsto (lowFailureEnvelope D δ A κ) atTop (𝓝 0) := by
  have hfirst := (tendsto_rpow_neg_atTop
    (by positivity : 0 < 7 * κ / 30)).const_mul ((D : ℝ) + 4)
  have hsecond := tendsto_rpow_neg_atTop (by positivity : 0 < 3 * κ / 4)
  have hsurvivors := (hfirst.add hsecond).const_mul (16 / δ)
  have hdecay : 0 < (1 / 2 : ℝ) - κ / 4 := by linarith
  have hparallel := (tendsto_sampleSize_pow_mul_rpow_neg_atTop 2 hA hdecay).const_mul
    (16 : ℝ)
  have hconcurrent := (tendsto_sampleSize_pow_mul_rpow_neg_atTop 3 hA hdecay).const_mul
    (32 : ℝ)
  have hoccupancy := (tendsto_sampleSize_pow_mul_rpow_neg_atTop
    (2 * (10 * (D + 1))) hA (low_occupancy_decay_pos D hκone)).const_mul
      ((D : ℝ) * (8 * (D : ℝ)) ^ (10 * (D + 1)))
  unfold lowFailureEnvelope
  simpa only [mul_zero, add_zero] using
    (hsurvivors.add (hparallel.add hconcurrent)).add hoccupancy

theorem tendsto_highFailureEnvelope_atTop (D : ℕ) (δ ρ : ℝ) {A κ : ℝ}
    (hA : 0 < A) (hκ : 0 < κ) :
    Tendsto (highFailureEnvelope D δ ρ A κ) atTop (𝓝 0) := by
  have hsurvivors := (tendsto_rpow_neg_atTop
    (by positivity : 0 < 3 * κ / 20)).const_mul (4 * ((D : ℝ) + 4) / (δ * ρ))
  have hdecay : 0 < (1 / 2 : ℝ) + κ / 4 := by positivity
  have hgeometry := (tendsto_sampleSize_pow_mul_rpow_neg_atTop 2 hA hdecay).add
    (tendsto_sampleSize_pow_mul_rpow_neg_atTop 3 hA hdecay)
  have hoccupancy := (tendsto_sampleSize_pow_mul_rpow_neg_atTop
    (2 * (10 * (D + 1))) hA (high_occupancy_decay_pos D hκ)).const_mul
      ((D : ℝ) * (4 * (D : ℝ)) ^ (10 * (D + 1)))
  unfold highFailureEnvelope
  simpa only [mul_zero, add_zero] using
    (hsurvivors.add hgeometry).add hoccupancy

theorem eventually_lowFailureEnvelope_lt_one (D : ℕ) (δ : ℝ) {A κ : ℝ}
    (hA : 0 < A) (hκ : 0 < κ) (hκone : κ ≤ 1) :
    ∀ᶠ q : ℝ in atTop, lowFailureEnvelope D δ A κ q < 1 :=
  (tendsto_order.mp (tendsto_lowFailureEnvelope_atTop D δ hA hκ hκone)).2 1
    (by norm_num)

theorem eventually_highFailureEnvelope_lt_one (D : ℕ) (δ ρ : ℝ) {A κ : ℝ}
    (hA : 0 < A) (hκ : 0 < κ) :
    ∀ᶠ q : ℝ in atTop, highFailureEnvelope D δ ρ A κ q < 1 :=
  (tendsto_order.mp (tendsto_highFailureEnvelope_atTop D δ ρ hA hκ)).2 1
    (by norm_num)

theorem eventually_sampleSize_le_mul_rpow {A a c : ℝ}
    (hA : 0 < A) (ha : 0 < a) (hc : 0 < c) :
    ∀ᶠ q : ℝ in atTop, (logarithmicSampleSize A q : ℝ) ≤ c * q ^ a := by
  have hlim := tendsto_sampleSize_pow_mul_rpow_neg_atTop 1 hA ha
  filter_upwards [(tendsto_order.mp hlim).2 c hc,
    eventually_gt_atTop (0 : ℝ)] with q hsmall hq
  rw [pow_one, Real.rpow_neg hq.le, ← div_eq_mul_inv] at hsmall
  exact ((div_lt_iff₀ (Real.rpow_pos_of_pos hq _)).mp hsmall).le

theorem eventually_sampling_size_bounds (D : ℕ) {A ρ κ : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hκ : 0 < κ) :
    ∀ᶠ q : ℝ in atTop,
      8 ≤ q ∧
      10 * (D + 1) ≤ logarithmicSampleSize A q ∧
      (4 * (10 * (D + 1)) : ℝ) ≤ q / 2 ∧
      2 * (logarithmicSampleSize A q : ℝ) ≤ q / 2 ∧
      2 * (logarithmicSampleSize A q : ℝ) ≤ q ^ (1 / 2 + κ / 4) ∧
      2 * (logarithmicSampleSize A q : ℝ) ≤ ρ * q / 2 := by
  have hlog := (tendsto_logarithmicSampleSize_atTop hA).eventually_ge_atTop
    (((10 * (D + 1) : ℕ) : ℝ))
  have hlinear := eventually_sampleSize_le_mul_rpow hA (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1 / 4)
  have hpencil := eventually_sampleSize_le_mul_rpow hA
    (by positivity : 0 < (1 / 2 : ℝ) + κ / 4) (by norm_num : (0 : ℝ) < 1 / 2)
  have hcomplement := eventually_sampleSize_le_mul_rpow hA (by norm_num : (0 : ℝ) < 1)
    (by positivity : 0 < ρ / 4)
  filter_upwards [eventually_ge_atTop (8 : ℝ), hlog, hlinear, hpencil, hcomplement,
    eventually_ge_atTop (8 * (10 * ((D : ℝ) + 1)))] with
      q hq ht hlo hhi hco hlarge
  have htNat : 10 * (D + 1) ≤ logarithmicSampleSize A q := by exact_mod_cast ht
  rw [Real.rpow_one] at hlo hco
  refine ⟨hq, htNat, ?_, ?_, ?_, ?_⟩ <;> nlinarith

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_RigidityNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.LineCover

open Filter Topology

theorem rigidityBudget_le (D : ℕ) {κ q : ℝ} (hκ : 0 ≤ κ) (hq : 1 ≤ q) :
    rigidityBudget D κ q ≤ ((D : ℝ) + 4) * q ^ (3 / 2 + κ / 10) := by
  have hpow : q ≤ q ^ (3 / 2 + κ / 10) := by
    calc
      q = q ^ (1 : ℝ) := (Real.rpow_one q).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hq (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ (D : ℝ) + 2 by positivity)
  unfold rigidityBudget
  nlinarith only [hmul]

private theorem eventually_mul_rpow_le_mul (C c a b : ℝ)
    (hc : 0 < c) (hab : a < b) :
    ∀ᶠ q : ℝ in atTop, C * q ^ a ≤ c * q ^ b := by
  have hgap : 0 < b - a := sub_pos.mpr hab
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop hgap).eventually_ge_atTop (C / c)] with q hq hlarge
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hC : C ≤ q ^ (b - a) * c := (div_le_iff₀ hc).mp hlarge
  calc
    C * q ^ a ≤ (q ^ (b - a) * c) * q ^ a :=
      mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hqpos.le _)
    _ = c * q ^ b := by
      rw [mul_comm (q ^ (b - a)) c, mul_assoc, ← Real.rpow_add hqpos]
      rw [show b - a + a = b by ring]

private theorem eventually_rigidityBudget_div_le (D : ℕ) {δ c κ : ℝ}
    (hδ : 0 < δ) (hc : 0 < c) (hκ : 0 ≤ κ) (hκmax : κ ≤ 1 / 10) :
    ∀ᶠ q : ℝ in atTop, rigidityBudget D κ q / (δ * q) ≤ c * q / 2 := by
  have hsmall := eventually_mul_rpow_le_mul ((D : ℝ) + 4) (δ * c / 2)
    (3 / 2 + κ / 10) 2 (by positivity) (by linarith)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hsmall] with q hq hsmallq
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  apply (div_le_iff₀ (mul_pos hδ hqpos)).2
  calc
    rigidityBudget D κ q ≤ ((D : ℝ) + 4) * q ^ (3 / 2 + κ / 10) :=
      rigidityBudget_le D hκ hq
    _ ≤ (δ * c / 2) * q ^ (2 : ℝ) := hsmallq
    _ = (c * q / 2) * (δ * q) := by rw [Real.rpow_two]; ring

theorem eventually_rigidityBudget_div_le_min (D : ℕ) {δ ρ κ : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hκ : 0 < κ) (hκmax : κ ≤ 1 / 10) :
    ∀ᶠ q : ℝ in atTop,
      rigidityBudget D κ q / (δ * q) ≤ min (q / 2) (ρ * q / 2) := by
  filter_upwards [eventually_rigidityBudget_div_le D hδ zero_lt_one hκ.le hκmax,
    eventually_rigidityBudget_div_le D hδ hρ hκ.le hκmax] with q hleft hright
  exact le_min (by simpa only [one_mul] using hleft) hright

theorem eventually_rigidity_heavy_bounds (D : ℕ) {κ : ℝ}
    (hκ : 0 < κ) (hκmax : κ ≤ 1 / 10) :
    ∀ᶠ q : ℝ in atTop,
      1 < q ^ (1 / 2 - κ / 3) ∧
        rigidityBudget D κ q / (q ^ (1 / 2 - κ / 3) - 1) ≤ q ^ (1 + κ) := by
  have hd : 0 < (1 / 2 : ℝ) - κ / 3 := by linarith
  have hgap : (3 / 2 : ℝ) + κ / 10 < (1 + κ) + (1 / 2 - κ / 3) := by
    linarith
  have hsmall := eventually_mul_rpow_le_mul (2 * ((D : ℝ) + 4)) 1
    (3 / 2 + κ / 10) ((1 + κ) + (1 / 2 - κ / 3)) zero_lt_one hgap
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop hd).eventually_ge_atTop 2, hsmall]
      with q hq hT hsmallq
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  rw [one_mul, Real.rpow_add hqpos (1 + κ) (1 / 2 - κ / 3)] at hsmallq
  have hscaled := mul_le_mul_of_nonneg_left hT
    (Real.rpow_nonneg hqpos.le (1 + κ))
  constructor
  · linarith
  · apply (div_le_iff₀ (by linarith : 0 < q ^ (1 / 2 - κ / 3) - 1)).2
    calc
      rigidityBudget D κ q ≤ ((D : ℝ) + 4) * q ^ (3 / 2 + κ / 10) :=
        rigidityBudget_le D hκ.le hq
      _ ≤ q ^ (1 + κ) * (q ^ (1 / 2 - κ / 3) - 1) := by
        nlinarith only [hsmallq, hscaled]

theorem eventually_line_error_le_half {δ κ : ℝ}
    (hδ : 0 < δ) (hκmax : κ ≤ 1 / 10) :
    ∀ᶠ q : ℝ in atTop, q ^ (1 / 2 + κ / 10) ≤ δ * q / 2 := by
  have hsmall := eventually_mul_rpow_le_mul 1 (δ / 2) (1 / 2 + κ / 10) 1
    (by positivity) (by linarith)
  filter_upwards [hsmall] with q hsmallq
  calc
    q ^ (1 / 2 + κ / 10) ≤ (δ / 2) * q ^ (1 : ℝ) := by
      simpa only [one_mul] using hsmallq
    _ = δ * q / 2 := by rw [Real.rpow_one]; ring

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_RigidityParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.LineCover

open Filter Topology

theorem eventually_rigidityParameters (D : ℕ) {δ ρ A κ : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hA : 0 < A) (hκ : 0 < κ)
    (hκsmall : κ ≤ 1 / 10) :
    ∀ᶠ q : ℝ in atTop, RigidityParameters D δ ρ A κ q := by
  have hsizes := eventually_sampling_size_bounds D hA hρ hκ
  have hgaps := eventually_rigidityBudget_div_le_min D hδ hρ hκ hκsmall
  have hheavy := eventually_rigidity_heavy_bounds D hκ hκsmall
  have hlow := eventually_lowFailureEnvelope_lt_one D δ hA hκ
    (show κ ≤ 1 by linarith)
  have hhigh := eventually_highFailureEnvelope_lt_one D δ ρ hA hκ
  have hline := eventually_line_error_le_half hδ hκsmall
  filter_upwards [hsizes, hgaps, hheavy, hlow, hhigh, hline] with
    q hsize hgap hheavyq hlo hhi hlin
  rcases hsize with ⟨hq, hht, hmh, hmt, hrt, hnt⟩
  have hhtR : ((10 * (D + 1) : ℕ) : ℝ) ≤ (logarithmicSampleSize A q : ℝ) := by
    exact_mod_cast hht
  have ht0 : (0 : ℝ) ≤ logarithmicSampleSize A q := Nat.cast_nonneg _
  refine {
    q_one := by linarith
    m_four := by linarith
    m_h := ?_
    m_t := hmt
    h_t := hht
    r_t := by linarith
    r_h := by linarith
    n_t := by linarith
    n_h := by linarith
    T_one := hheavyq.1
    gap_half := hgap.trans (min_le_left _ _)
    gap_rho := hgap.trans (min_le_right _ _)
    heavy := hheavyq.2
    low := hlo
    high := hhi
    lineerror := hlin }
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] using hmh

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology
open scoped Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

universe u

theorem prob_not_goodLineCover_le
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {D : ℕ} {δ ρ A : ℝ} (process : DeletionProcess F D δ)
    (hD : 0 < D) (hδ : 0 < δ) (hρ : 0 < ρ)
    (hq : Incidence.incidenceThreshold ≤ Fintype.card F)
    (hsub : Incidence.SmallProperSubfields F)
    (params : RigidityParameters D δ ρ A Incidence.savingExponent (Fintype.card F)) :
    process.law.prob (fun ω => ¬ GoodLineCover δ ρ ω) ≤
      linecoverFailureBound D δ A (Fintype.card F) := by
  let h := 10 * (D + 1)
  let t := logarithmicSampleSize A (Fintype.card F)
  have hh : 0 < h := by dsimp [h]; omega
  have ht : 0 < t := lt_of_lt_of_le hh params.h_t
  have hε : 0 < Incidence.savingExponent / 10 := by
    exact div_pos Incidence.savingExponent_pos (by norm_num)
  have hεhalf : Incidence.savingExponent / 10 ≤ 1 / 2 := by
    linarith [Incidence.savingExponent_lt_tenth]
  have hcounts := process.prob_not_goodCounts (Incidence.savingExponent / 10)
    (by omega : 1 ≤ D) hε hεhalf
  have htuples := process.prob_not_goodTuples h t hD hh ht hδ
  have hbad : process.law.prob (fun ω => ¬ GoodLineCover δ ρ ω) ≤
      process.law.prob (fun ω =>
        ¬ GoodCounts process (Incidence.savingExponent / 10) ω ∨
        ¬ GoodTuples process h t ω) := by
    apply process.law.prob_mono
    intro ω hnot
    by_cases hc : GoodCounts process (Incidence.savingExponent / 10) ω
    · right
      intro htup
      exact hnot (goodLineCover_of_goodCounts_goodTuples process hδ hρ hq hsub
        params ω hc htup)
    · exact Or.inl hc
  exact hbad.trans ((process.law.prob_union_le _ _).trans (add_le_add hcounts htuples))

theorem tendsto_linecoverFailureBound (D : ℕ) {δ A : ℝ}
    (hD : 0 < D) (hδ : 0 < δ)
    (hA : 5 / tupleTailConstant D (10 * (D + 1)) δ < A) :
    Tendsto (linecoverFailureBound D δ A) atTop (𝓝 0) := by
  have hDr : 0 < (D : ℝ) := by exact_mod_cast hD
  have hc0 := tupleTailConstant_pos hD
    (show 0 < 10 * (D + 1) by omega) hδ
  have hc := tendsto_count_failure_atTop hDr
    (show 0 < Incidence.savingExponent / 10 from
      div_pos Incidence.savingExponent_pos (by norm_num))
  have ht := tendsto_tuple_failure_atTop hc0 hA
  unfold linecoverFailureBound
  simpa only [add_zero] using hc.add ht

theorem uniform_linecover_probability (D : ℕ) (δ ρ : ℝ)
    (hD : 0 < D) (hδ : 0 < δ) (hρ : 0 < ρ) (η : ℝ) (hη : 0 < η) :
    ∃ Q : ℕ, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      Q ≤ Fintype.card F → Incidence.SmallProperSubfields F →
      ∀ process : DeletionProcess F D δ,
        1 - η ≤ process.law.prob (GoodLineCover δ ρ) := by
  let c0 := tupleTailConstant D (10 * (D + 1)) δ
  have hc0 : 0 < c0 := tupleTailConstant_pos hD (by omega) hδ
  let A := 6 / c0
  have hA : 0 < A := div_pos (by norm_num) hc0
  have hA5 : 5 / c0 < A := div_lt_div_of_pos_right (by norm_num) hc0
  have hnumeric := eventually_rigidityParameters D hδ hρ hA
    Incidence.savingExponent_pos Incidence.savingExponent_lt_tenth.le
  have hfailure : ∀ᶠ q : ℝ in atTop, linecoverFailureBound D δ A q ≤ η :=
    (tendsto_linecoverFailureBound D hD hδ hA5).eventually_le_const hη
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp (hnumeric.and hfailure)
  refine ⟨max ⌈R⌉₊ Incidence.incidenceThreshold, ?_⟩
  intro F instField instFintype instDecidable hQ hsub process
  have hRcard : R ≤ (Fintype.card F : ℝ) :=
    (Nat.le_ceil R).trans (by
      exact_mod_cast (le_max_left ⌈R⌉₊ Incidence.incidenceThreshold).trans hQ)
  have hq : Incidence.incidenceThreshold ≤ Fintype.card F :=
    (le_max_right ⌈R⌉₊ Incidence.incidenceThreshold).trans hQ
  obtain ⟨params, hbound⟩ := hR (Fintype.card F) hRcard
  have hprob := (prob_not_goodLineCover_le process hD hδ hρ hq hsub params).trans hbound
  rw [process.law.prob_compl] at hprob
  linarith

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_AmbientPoolExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical

namespace RyserCoveringCounterexample.Construction

universe uk uf

variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]

theorem exists_goodAmbientPool_uniform_oai
    (u v : k) (huv : u ≠ v) (a : GadgetOutcome k) (ha : OriginalLineDensity a)
    (hs : 2 ≤ Fintype.card k) :
    ∃ K Q : ℕ, 6 ≤ K ∧
      ∀ (F : Type uf) [Field F] [Fintype F] [DecidableEq F] (σ : k →+* F),
        Q ≤ Fintype.card F → Incidence.SmallProperSubfields F →
        (1 + ambientDeletionDelta (Fintype.card k) K / 10 * Fintype.card F <
          ambientDeletionDelta (Fintype.card k) K * Fintype.card F / 2) ∧
        ∃ pool : AmbientPool σ K, GoodAmbientPool σ u v huv a ha K pool := by
  classical
  let s := Fintype.card k
  let D := groupSelectionConstant s
  have hD : 1 ≤ D := by dsimp [D, groupSelectionConstant]; omega
  obtain ⟨K, hK, hselection⟩ := Selection.compatible_selection_uniform.{uf} D hD
  obtain ⟨QS, hQS⟩ := hselection (1 / 4) (by norm_num)
  let δ := ambientDeletionDelta s K
  let ρ := δ / 10
  let DA := ambientDeletionConstant s K
  have hδ : 0 < δ := ambientDeletionDelta_pos s K
  have hρ : 0 < ρ := div_pos hδ (by norm_num)
  have hDA : 0 < DA := lt_of_lt_of_le (by decide : 0 < 2)
    (ambientDeletionConstant_two_le s K)
  obtain ⟨QL, hQL⟩ := LineCover.uniform_linecover_probability.{uf}
    DA δ ρ hDA hδ hρ (1 / 4) (by norm_num)
  obtain ⟨QT, hQT⟩ := exists_thinFailure_cutoff s K (η := 1 / 4) (by norm_num)
  let QF : ℕ := ⌈10 / δ⌉₊ + 1
  refine ⟨K, QS + QL + QT + 2 * (s - 1) ^ 2 + QF, hK, ?_⟩
  intro F instField instFintype instDecidable σ hq hsub
  have hqS : QS ≤ Fintype.card F := by omega
  have hqL : QL ≤ Fintype.card F := by omega
  have hqT : QT ≤ Fintype.card F := by omega
  have hsmall : 2 * (Fintype.card k - 1) ^ 2 ≤ Fintype.card F := by
    change 2 * (s - 1) ^ 2 ≤ Fintype.card F
    omega
  have hqF : QF ≤ Fintype.card F := by omega
  have hqFreal : (QF : ℝ) ≤ Fintype.card F := by exact_mod_cast hqF
  have hforce : 1 + ρ * Fintype.card F < δ * Fintype.card F / 2 := by
    have hceil : 10 / δ ≤ (⌈10 / δ⌉₊ : ℝ) := Nat.le_ceil _
    have hlarge : 10 / δ < (Fintype.card F : ℝ) := by
      dsimp [QF] at hqFreal
      push_cast at hqFreal
      linarith
    have hproduct : 10 < (Fintype.card F : ℝ) * δ := (div_lt_iff₀ hδ).mp hlarge
    dsimp [ρ]
    nlinarith
  refine ⟨hforce, ?_⟩
  let μ := poolThinLaw (F := F) (ConfigurationGroup σ) K
  let Selected : AmbientPool σ K → Prop := fun pool =>
    Selection.HasCompatibleChoice (groupSelectionData σ u v huv)
      (ambientFlatPoolEquiv σ K pool)
  let Rigid : AmbientPool σ K → Prop := fun pool =>
    LineCover.GoodLineCover δ ρ (ambientPoolConfig σ u v huv a ha K pool)
  let Thin : AmbientPool σ K → Prop :=
    PoolThin (groupPoints σ u v huv) (groupAltered σ u v huv)
  have hselect : 1 - (1 / 4 : ℝ) ≤ μ.prob Selected := by
    have h := hQS F (Fintype.card (ConfigurationGroup σ)) (groupSelectionData σ u v huv)
      (groupSelectionData_bounded σ u v huv hs) hqS
    rw [← poolThinLaw_map_ambientFlatPoolEquiv σ K, FiniteLaw.prob_map] at h
    exact h
  have hrigid : 1 - (1 / 4 : ℝ) ≤ μ.prob Rigid := by
    have h := hQL F hqL hsub (ambientDeletionProcess σ u v huv a ha K hs hsmall)
    change 1 - (1 / 4 : ℝ) ≤ (FiniteLaw.pi (ambientTrials σ u v huv a ha K)).prob
      (LineCover.GoodLineCover δ ρ) at h
    rw [← poolThinLaw_map_ambientPoolConfig σ u v huv a ha K, FiniteLaw.prob_map] at h
    exact h
  have hthin : 1 - (1 / 4 : ℝ) ≤ μ.prob Thin := by
    have h := prob_groupPoolThin_ge σ u v huv K
    have htail := hQT (Fintype.card F) hqT
    exact (sub_le_sub_left htail 1).trans h
  have hex : ∃ pool : AmbientPool σ K, Selected pool ∧ Rigid pool ∧ Thin pool := by
    by_contra hnot
    have himp : ∀ pool, Selected pool → ¬ Rigid pool ∨ ¬ Thin pool := by
      intro pool hselected
      by_cases hr : Rigid pool
      · exact Or.inr (fun ht => hnot ⟨pool, hselected, hr, ht⟩)
      · exact Or.inl hr
    have hmono := (μ.prob_mono himp).trans (μ.prob_union_le (fun pool => ¬ Rigid pool)
      (fun pool => ¬ Thin pool))
    rw [μ.prob_compl, μ.prob_compl] at hmono
    linarith
  obtain ⟨pool, hselected, hrigid', hthin'⟩ := hex
  exact ⟨pool, hselected, hrigid', hthin'⟩

end RyserCoveringCounterexample.Construction

end

end OAI
end

theorem solution.{uk, uf} : type_of% @OAI.RyserCoveringCounterexample.Construction.exists_goodAmbientPool_uniform_oai.{uk, uf} := @OAI.RyserCoveringCounterexample.Construction.exists_goodAmbientPool_uniform_oai.{uk, uf}
