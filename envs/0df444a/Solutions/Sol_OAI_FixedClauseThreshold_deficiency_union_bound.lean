-- Prove2me | solution 1 for OAI.FixedClauseThreshold.deficiency_union_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:35:48.930721+00:00
-- url     : https://prove2.me/submissions/70caf0ef-dc32-4fb9-a074-7c5e6f0ea209

-- Generated from openai/math@1581d4c lean/OAI/Probability/RandomSAT/CenterBounds.lean:L322-L367
-- (upload_full_project.md Phase 4): solution for node OAI.FixedClauseThreshold.deficiency_union_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FixedClauseThreshold
import Definitions.Def_OAI_Probability_RandomSAT_Clauses
import Definitions.Def_OAI_Probability_RandomSAT_Replacement
import Definitions.Def_OAI_Probability_RandomSAT_FiniteMean
import Definitions.Def_OAI_Probability_RandomSAT_ClauseProcess
import Definitions.Def_OAI_Probability_RandomSAT_Binomial
import Definitions.Def_OAI_Probability_RandomSAT_Forcing
import Definitions.Def_OAI_Probability_RandomSAT_Variance
import Definitions.Def_OAI_Probability_RandomSAT_Concentration
import Definitions.Def_OAI_Probability_RandomSAT_CenterBounds
import Theorems.Thm_OAI_FixedClauseThreshold_killFraction_le_pow
import Theorems.Thm_OAI_FixedClauseThreshold_uniformProbability_exists_le

-- ---- from OAI.Probability.RandomSAT.Clauses ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
Signed variable sets, clause cardinalities, and the exact probability of killing
a nonempty solution set.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem nonempty_properClause {n k : ℕ} (hkn : k ≤ n) :
    Nonempty (ProperClause n k) := by
  apply Fintype.card_pos_iff.mp
  rw [card_properClause]
  exact Nat.mul_pos (Nat.choose_pos hkn) (by positivity)

theorem uniformProbability_nonneg {α : Type*} [Fintype α] (p : α → Prop) :
    0 ≤ uniformProbability p := by
  unfold uniformProbability
  positivity

theorem uniformProbability_mono {α : Type*} [Fintype α] {p q : α → Prop}
    (hpq : ∀ a, p a → q a) : uniformProbability p ≤ uniformProbability q := by
  classical
  unfold uniformProbability
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Fintype.card_le_of_injective
    (fun a : {a // p a} => (⟨a.val, hpq a.val a.property⟩ : {a // q a}))
    (fun _ _ h => Subtype.ext (congrArg (fun t : {a // q a} => t.val) h))

end

end FixedClauseThreshold

end OAI

-- ---- from OAI.Probability.RandomSAT.Replacement ----
namespace OAI

/-!
Quantitative comparison of a shorter clause with a block of independent proper
clauses, uniformly over the background solution set.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem uniformProbability_congr {α : Type*} [Fintype α] {p q : α → Prop}
    (h : ∀ a, p a ↔ q a) : uniformProbability p = uniformProbability q := by
  unfold uniformProbability
  rw [Fintype.card_congr (Equiv.subtypeEquivRight h)]

theorem uniformProbability_not {α : Type*} [Fintype α] [Nonempty α] (p : α → Prop) :
    uniformProbability (fun a => ¬ p a) = 1 - uniformProbability p := by
  unfold uniformProbability
  rw [Fintype.card_subtype_compl, Nat.cast_sub (Fintype.card_subtype_le p), sub_div,
    div_self (by exact_mod_cast Fintype.card_ne_zero)]

end

end FixedClauseThreshold

end OAI

-- ---- from OAI.Probability.RandomSAT.FiniteMean ----
namespace OAI

/-!
Uniform finite expectations and variances.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem uniformProbability_eq_mean {α : Type*} [Fintype α] (p : α → Prop) :
    uniformProbability p = uniformMean (fun a => if p a then 1 else 0) := by
  classical
  unfold uniformProbability uniformMean
  congr 1
  simp [Fintype.card_subtype]

end

end FixedClauseThreshold

end OAI

-- ---- from OAI.Probability.RandomSAT.CenterBounds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
Finite union bounds, a matching criterion for satisfiability, and positive finite
bounds for the normalized centers.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem uniformProbability_forall_fintype {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (p : α → Prop) :
    uniformProbability (fun f : β → α => ∀ b, p (f b)) = uniformProbability p ^ Fintype.card β := by
  unfold uniformProbability
  have hc : Fintype.card {f : β → α // ∀ b, p (f b)} =
      Fintype.card (β → {a : α // p a}) :=
    Fintype.card_congr (Equiv.subtypePiEquivPi (p := fun _ : β => p))
  simp only [← Nat.card_eq_fintype_card] at hc ⊢
  rw [hc]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Nat.cast_pow, div_pow]

theorem satisfiable_of_matching {n k m : ℕ} (F : Formula n k m)
    (f : Fin m → Fin n) (hf : Function.Injective f)
    (hmem : ∀ j, f j ∈ clauseSupport (F j)) : Satisfiable F := by
  let b : Fin m → Bool := fun j => ((F j).val (f j)).getD false
  let σ : Assignment n := fun i => if h : ∃ j, f j = i then b (Classical.choose h) else false
  refine ⟨σ, fun j => ⟨f j, ?_⟩⟩
  have he : ∃ j', f j' = f j := ⟨j, rfl⟩
  have hc : Classical.choose he = j := hf (Classical.choose_spec he)
  have hs : σ (f j) = b j := by simp [σ, he, hc]
  rw [hs]
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ((mem_clauseSupport _ _).mp (hmem j))
  simp [b, hv]

theorem unsatisfiable_deficiency {n k m : ℕ} (F : Formula n k m) (hF : ¬Satisfiable F) :
    ∃ J : Finset (Fin m), (J.biUnion fun j => clauseSupport (F j)).card < J.card := by
  by_contra h
  push Not at h
  obtain ⟨f, hf, hmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective (fun j => clauseSupport (F j))).mp h
  exact hF (satisfiable_of_matching F f hf hmem)

theorem uniformProbability_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (p : β → Prop) :
    uniformProbability (fun a => p (e a)) = uniformProbability p := by
  unfold uniformProbability
  rw [Fintype.card_congr (Equiv.subtypeEquiv e (fun _ => Iff.rfl)), Fintype.card_congr e]

theorem uniformProbability_prod_first {α β : Type*} [Fintype α] [Fintype β] [Nonempty β]
    (p : α → Prop) : uniformProbability (fun x : α × β => p x.1) = uniformProbability p := by
  let e : {x : α × β // p x.1} ≃ {a : α // p a} × β := {
    toFun := fun x => (⟨x.val.1, x.property⟩, x.val.2)
    invFun := fun x => ⟨(x.1.val, x.2), x.1.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  unfold uniformProbability
  simp only [← Nat.card_eq_fintype_card]
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod, Nat.cast_mul, Nat.cast_mul]
  have hb : (Nat.card β : ℝ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_ne_zero (α := β)
  field_simp

theorem uniformProbability_forall_mem {α β : Type*} [Fintype α] [Nonempty α] [Fintype β] [DecidableEq β]
    (J : Finset β) (p : α → Prop) :
    uniformProbability (fun f : β → α => ∀ j ∈ J, p (f j)) = uniformProbability p ^ J.card := by
  let e := Equiv.piEquivPiSubtypeProd (fun j => j ∈ J) (fun _ : β => α)
  calc
    _ = uniformProbability (fun f : β → α => ∀ j : ↥J, p ((e f).1 j)) :=
      uniformProbability_congr (fun f => by simp [e])
    _ = uniformProbability (fun f : (↥J → α) × ({j : β // j ∉ J} → α) =>
        ∀ j, p (f.1 j)) := uniformProbability_equiv
          (α := β → α) (β := (↥J → α) × ({j : β // j ∉ J} → α)) e
          (fun f => ∀ j, p (f.1 j))
    _ = uniformProbability (fun f : ↥J → α => ∀ j, p (f j)) :=
      uniformProbability_prod_first (α := ↥J → α) (β := {j : β // j ∉ J} → α)
        (fun f : ↥J → α => ∀ j, p (f j))
    _ = _ := by
      have h := uniformProbability_forall_fintype (α := α) (β := ↥J) p
      simpa only [Fintype.card_coe] using h

theorem uniformMean_support {n k : ℕ} (f : Finset (Fin n) → ℝ) :
    uniformMean (fun C : ProperClause n k => f (clauseSupport C)) =
      uniformMean (fun s : VariableSet n k => f s.val) := by
  have he := uniformMean_equiv (properClauseEquiv n k) (fun s => f s.1.val)
  change uniformMean (fun C : ProperClause n k => f (clauseSupport C)) = _ at he
  rw [he]
  have hc (s : VariableSet n k) : Fintype.card (↥s.val → Bool) = 2^k := by
    simp [(Finset.mem_powersetCard.mp s.property).2]
  simp only [uniformMean, Fintype.sum_sigma, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Fintype.card_sigma, hc, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [← Finset.mul_sum]
  have h2 : (2 : ℝ)^k ≠ 0 := by positivity
  push_cast
  field_simp

theorem uniformProbability_support_subset {n k : ℕ} (T : Finset (Fin n)) :
    uniformProbability (fun C : ProperClause n k => clauseSupport C ⊆ T) =
      (T.card.choose k : ℝ) / n.choose k := by
  have hm := uniformMean_support (k := k) (fun S => if S ⊆ T then (1 : ℝ) else 0)
  have hp : uniformProbability (fun C : ProperClause n k => clauseSupport C ⊆ T) =
      uniformProbability (fun s : VariableSet n k => s.val ⊆ T) := by
    rw [uniformProbability_eq_mean, uniformProbability_eq_mean]
    calc
      _ = uniformMean (fun C : ProperClause n k =>
          if clauseSupport C ⊆ T then (1 : ℝ) else 0) := by
            apply uniformMean_congr
            intro C
            by_cases h : clauseSupport C ⊆ T <;> simp only [h, ite_true, ite_false]
      _ = _ := hm
      _ = _ := by
        apply uniformMean_congr
        intro C
        by_cases h : C.val ⊆ T <;> simp only [h, ite_true, ite_false]
  rw [hp]
  let e : {s : VariableSet n k // s.val ⊆ T} ≃ ↥(T.powersetCard k) := {
    toFun := fun s => ⟨s.val.val, Finset.mem_powersetCard.mpr
      ⟨s.property, (Finset.mem_powersetCard.mp s.val.property).2⟩⟩
    invFun := fun s => ⟨⟨s.val, Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, (Finset.mem_powersetCard.mp s.property).2⟩⟩,
        (Finset.mem_powersetCard.mp s.property).1⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  unfold uniformProbability
  simp only [← Nat.card_eq_fintype_card]
  rw [Nat.card_congr e]
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

theorem choose_quotient_le_pow {b n k : ℕ} (hbn : b ≤ n) (hkn : k ≤ n) (hn : 0 < n) :
    (b.choose k : ℝ) / n.choose k ≤ ((b : ℝ) / n)^k := by
  have h := mul_le_mul_of_nonneg_right (killFraction_le_pow hbn hkn hn)
    (by positivity : (0 : ℝ) ≤ 2^k)
  have h2 : (2 : ℝ)^k ≠ 0 := by positivity
  calc
    _ = killFraction b n k * 2^k := by
      unfold killFraction
      field_simp
    _ ≤ ((b : ℝ) / (2 * n))^k * 2^k := h
    _ = _ := by
      rw [← mul_pow]
      congr 1
      field_simp

theorem clause_subset_bound {n k : ℕ} (hkn : k ≤ n) (hn : 0 < n) (T : Finset (Fin n)) :
    uniformProbability (fun C : ProperClause n k => clauseSupport C ⊆ T) ≤
      ((T.card : ℝ) / n)^k := by
  rw [uniformProbability_support_subset]
  exact choose_quotient_le_pow (by simpa using Finset.card_le_univ T) hkn hn

theorem unsatisfiable_container {n k m : ℕ} (hmn : m ≤ n) (F : Formula n k m)
    (hF : ¬Satisfiable F) :
    ∃ t : Fin m, ∃ J : VariableSet m (t.val + 1), ∃ T : VariableSet n (t.val + 1),
      ∀ j ∈ J.val, clauseSupport (F j) ⊆ T.val := by
  obtain ⟨J, hdef⟩ := unsatisfiable_deficiency F hF
  have ht : 0 < J.card := lt_of_le_of_lt (Nat.zero_le _) hdef
  have htm : J.card ≤ m := by simpa using Finset.card_le_univ J
  obtain ⟨T, hUT, _, hT⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ (J.biUnion fun j => clauseSupport (F j))) hdef.le
      (show J.card ≤ (Finset.univ : Finset (Fin n)).card by simpa using htm.trans hmn)
  have hts : J.card - 1 + 1 = J.card := Nat.sub_add_cancel ht
  refine ⟨⟨J.card - 1, by omega⟩,
    ⟨J, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hts.symm⟩⟩,
    ⟨T, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hT.trans hts.symm⟩⟩, ?_⟩
  intro j hj i hi
  exact hUT (Finset.mem_biUnion.mpr ⟨j, hj, hi⟩)

theorem deficiency_union_bound {n k m : ℕ} (hkn : k ≤ n) (hn : 0 < n) (hmn : m ≤ n) :
    1 - properSATProbability n k m ≤
      ∑ t ∈ Finset.range m, (m.choose (t + 1) : ℝ) * n.choose (t + 1) *
        (((t + 1 : ℕ) : ℝ) / n)^(k * (t + 1)) := by
  let : Nonempty (ProperClause n k) := nonempty_properClause hkn
  let E (F : Formula n k m) (t : Fin m) (J : VariableSet m (t.val + 1))
      (T : VariableSet n (t.val + 1)) : Prop := ∀ j ∈ J.val, clauseSupport (F j) ⊆ T.val
  have hsat : 1 - properSATProbability n k m =
      uniformProbability (fun F : Formula n k m => ¬Satisfiable F) :=
    (uniformProbability_not (fun F : Formula n k m => Satisfiable F)).symm
  have hE (t : Fin m) (J : VariableSet m (t.val + 1)) (T : VariableSet n (t.val + 1)) :
      uniformProbability (fun F : Formula n k m => E F t J T) ≤
        (((t.val + 1 : ℕ) : ℝ) / n)^(k * (t.val + 1)) := by
    dsimp [E]
    rw [uniformProbability_forall_mem (α := ProperClause n k) (β := Fin m) J.val
      (fun C => clauseSupport C ⊆ T.val)]
    have ht := (Finset.mem_powersetCard.mp T.property).2
    have hj := (Finset.mem_powersetCard.mp J.property).2
    rw [hj]
    have h := pow_le_pow_left₀ (uniformProbability_nonneg _)
      (clause_subset_bound hkn hn T.val) (t.val + 1)
    rwa [ht, ← pow_mul] at h
  rw [hsat]
  calc
    _ ≤ uniformProbability (fun F : Formula n k m => ∃ t, ∃ J, ∃ T, E F t J T) :=
      uniformProbability_mono (fun F hF => unsatisfiable_container hmn F hF)
    _ ≤ ∑ t : Fin m, uniformProbability (fun F : Formula n k m => ∃ J, ∃ T, E F t J T) :=
      uniformProbability_exists_le _
    _ ≤ ∑ t : Fin m, ∑ J : VariableSet m (t.val + 1),
        ∑ T : VariableSet n (t.val + 1),
          uniformProbability (fun F : Formula n k m => E F t J T) := by
      apply Finset.sum_le_sum
      intro t _
      apply (uniformProbability_exists_le _).trans
      apply Finset.sum_le_sum
      intro J _
      exact uniformProbability_exists_le _
    _ ≤ ∑ t : Fin m, ∑ _ : VariableSet m (t.val + 1), ∑ _ : VariableSet n (t.val + 1),
        (((t.val + 1 : ℕ) : ℝ) / n)^(k * (t.val + 1)) := by
      gcongr with t _ J _ T _
      exact hE t J T
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, card_variableSet, nsmul_eq_mul]
      simp only [← mul_assoc]
      exact Fin.sum_univ_eq_sum_range (fun t => (m.choose (t+1) : ℝ) * n.choose (t+1) *
        (((t+1 : ℕ) : ℝ) / n)^(k*(t+1))) m

end

end FixedClauseThreshold

end OAI

-- ---- platform node ----
open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.FixedClauseThreshold.deficiency_union_bound := @_root_.OAI.FixedClauseThreshold.deficiency_union_bound
