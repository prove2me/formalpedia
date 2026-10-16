-- Prove2me | solution 1 for OAI.RandomKSAT.rootRewards_square_density
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T19:33:43.91823+00:00
-- url     : https://prove2.me/submissions/6b3865c8-3782-4335-8d6c-ee4c11ba97df

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/SupportProbabilities.lean:L232-L249
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.rootRewards_square_density. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiniteVariance
import Definitions.Def_OAI_Probability_SATVariance_LifetimePotential
import Definitions.Def_OAI_Probability_SATVariance_RootDisintegration__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiberRefresh
import Definitions.Def_OAI_Probability_SATVariance_PairEvolution
import Definitions.Def_OAI_Probability_SATVariance_HiddenTests
import Definitions.Def_OAI_Probability_SATVariance_WeightedRewards
import Definitions.Def_OAI_Probability_SATVariance_CountMoments
import Definitions.Def_OAI_Probability_SATVariance_SupportProbabilities__SATVariance
import Theorems.Thm_OAI_RandomKSAT_rootRewards_square_avg

-- ---- from OAI.Probability.SATVariance.ClauseCombinatorics ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma support_card (n k : ℕ) :
    Fintype.card {s : Finset (Fin n) // s.card = k} = n.choose k := by
  classical
  rw [Fintype.card_of_subtype ((Finset.univ : Finset (Fin n)).powersetCard k)
    (by intro s; simp)]
  simp

lemma clause_card (n k : ℕ) : Fintype.card (Clause n k) = n.choose k * 2 ^ k := by
  classical
  change Fintype.card ((s : {s : Finset (Fin n) // s.card = k}) × (s.1 → Bool)) = _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
  trans ∑ _ : {s : Finset (Fin n) // s.card = k}, 2 ^ k
  · apply Finset.sum_congr rfl
    intro s _
    rw [s.property]
  · rw [Finset.sum_const, Finset.card_univ, support_card, smul_eq_mul]

lemma clause_nonempty (n k : ℕ) (hkn : k ≤ n) : Nonempty (Clause n k) := by
  rw [← Fintype.card_pos_iff, clause_card]
  exact Nat.mul_pos (Nat.choose_pos hkn) (pow_pos (by decide) _)

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.MarkovReplacement ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma favg_mono.{u_1} {α : Type u_1} [Fintype α] {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    favg f ≤ favg g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => h a) (by positivity)

lemma favg_const.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (c : ℝ) :
    favg (fun _ : α => c) = c := by
  simp [favg, Fintype.card_ne_zero]

lemma favg_equiv.{u_1, u_2} {α : Type u_1} {β : Type u_2} [Fintype α] [Fintype β] (e : α ≃ β) (f : β → ℝ) :
    favg (fun a => f (e a)) = favg f := by
  rw [favg, favg, e.sum_comp f, Fintype.card_congr e]

lemma favg_mul.{u_1} {α : Type u_1} [Fintype α] (c : ℝ) (f : α → ℝ) :
    favg (fun a => c*f a) = c*favg f := by
  simp only [favg, ← Finset.mul_sum]
  ring

lemma favg_nonneg.{u_1} {α : Type u_1} [Fintype α] {f : α → ℝ} (h : ∀ a, 0 ≤ f a) :
    0 ≤ favg f := by
  exact div_nonneg (Finset.sum_nonneg fun a _ => h a) (by positivity)

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.FiniteVariance ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma favg_sum.{u_1, u_2} {α : Type u_1} {ι : Type u_2} [Fintype α] (s : Finset ι) (f : ι → α → ℝ) :
    favg (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, favg (f i) := by
  simp only [favg, Finset.sum_div]
  exact Finset.sum_comm

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.CountMoments ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma hitProbability_nonneg.{u_1} {α : Type u_1} [Fintype α] (p : α → Prop) :
    0 ≤ hitProbability p := favg_nonneg fun _ => by split <;> norm_num

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.SupportProbabilities ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma mem_renameClause {n m k : ℕ} (e : Fin n ≃ Fin m) (c : Clause n k) (v : Fin m) :
    v ∈ (renameClause e c).1.1 ↔ e.symm v ∈ c.1.1 := by simp [renameClause]

lemma renameClauseEquiv_apply {n m k : ℕ} (e : Fin n ≃ Fin m) (c : Clause n k) :
    renameClauseEquiv e c = renameClause e c := rfl

lemma support_probability_uniform {n k : ℕ} (v w : Fin n) :
    favg (fun c : Clause n k => if v ∈ c.1.1 then (1 : ℝ) else 0) =
    favg (fun c : Clause n k => if w ∈ c.1.1 then (1 : ℝ) else 0) := by
  have hh := favg_equiv (renameClauseEquiv (k := k) (Equiv.swap v w))
    (fun c : Clause n k => if w ∈ c.1.1 then (1 : ℝ) else 0)
  simpa only [renameClauseEquiv_apply, mem_renameClause, Equiv.symm_swap, Equiv.swap_apply_right] using hh

lemma support_probability_scaled {n k : ℕ} (hkn : k ≤ n) (v : Fin n) :
    (n : ℝ)*favg (fun c : Clause n k => if v ∈ c.1.1 then (1 : ℝ) else 0) = k := by
  let := clause_nonempty n k hkn
  have he (c : Clause n k) : (∑ w : Fin n, if w ∈ c.1.1 then (1 : ℝ) else 0) = k := by
    simp only [Finset.sum_boole]
    have hh : Finset.univ.filter (fun w => w ∈ c.1.1) = c.1.1 := by ext w; simp
    rw [hh, c.1.2]
  have hh : favg (fun c : Clause n k => ∑ w : Fin n, if w ∈ c.1.1 then (1 : ℝ) else 0) = k := by
    simp only [he, favg_const]
  rw [favg_sum] at hh
  have hew (w : Fin n) := support_probability_uniform (k := k) w v
  simp only [hew, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  exact hh

lemma support_pair_probability_uniform {n k : ℕ} (v w z : Fin n) (hw : w ≠ v) (hz : z ≠ v) :
    favg (fun c : Clause n k => if v ∈ c.1.1 ∧ w ∈ c.1.1 then (1 : ℝ) else 0) =
    favg (fun c : Clause n k => if v ∈ c.1.1 ∧ z ∈ c.1.1 then (1 : ℝ) else 0) := by
  have hh := favg_equiv (renameClauseEquiv (k := k) (Equiv.swap w z))
    (fun c : Clause n k => if v ∈ c.1.1 ∧ z ∈ c.1.1 then (1 : ℝ) else 0)
  simpa only [renameClauseEquiv_apply, mem_renameClause, Equiv.symm_swap, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne (Ne.symm hw) (Ne.symm hz)] using hh

lemma support_pair_probability_scaled {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (v w : Fin n) (hw : w ≠ v) :
    ((n : ℝ)-1)*favg (fun c : Clause n k => if v ∈ c.1.1 ∧ w ∈ c.1.1 then (1 : ℝ) else 0) =
      ((k : ℝ)-1)*favg (fun c : Clause n k => if v ∈ c.1.1 then (1 : ℝ) else 0) := by
  have he (c : Clause n k) :
      (∑ z ∈ (Finset.univ.erase v), if v ∈ c.1.1 ∧ z ∈ c.1.1 then (1 : ℝ) else 0) =
      ((k : ℝ)-1)*(if v ∈ c.1.1 then 1 else 0) := by
    by_cases hv : v ∈ c.1.1
    · simp only [hv, true_and, ite_true, mul_one, Finset.sum_boole]
      have hh : (Finset.univ.erase v).filter (fun z => z ∈ c.1.1) = c.1.1.erase v := by ext z; simp
      rw [hh, Finset.card_erase_of_mem hv, c.1.2, Nat.cast_sub hk, Nat.cast_one]
    · simp [hv]
  have hh := congrArg (fun f : Clause n k → ℝ => favg f) (funext he)
  rw [favg_sum, favg_mul] at hh
  have hs : (∑ z ∈ (Finset.univ.erase v),
      favg (fun c : Clause n k => if v ∈ c.1.1 ∧ z ∈ c.1.1 then (1 : ℝ) else 0)) =
      ((n : ℝ)-1)*favg (fun c : Clause n k => if v ∈ c.1.1 ∧ w ∈ c.1.1 then (1 : ℝ) else 0) := by
    trans ∑ _z ∈ (Finset.univ.erase v), favg (fun c : Clause n k => if v ∈ c.1.1 ∧ w ∈ c.1.1 then (1 : ℝ) else 0)
    · apply Finset.sum_congr rfl
      intro z hz
      exact support_pair_probability_uniform v z w (Finset.mem_erase.mp hz).1 hw
    · simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
  rwa [hs] at hh

lemma support_pair_probability_bound {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n)
    (v w : Fin n) (hw : w ≠ v) :
    (n : ℝ)^2*favg (fun c : Clause n k => if v ∈ c.1.1 ∧ w ∈ c.1.1 then (1 : ℝ) else 0) ≤
      2*(k : ℝ)^2 := by
  let P := favg (fun c : Clause n k => if v ∈ c.1.1 ∧ w ∈ c.1.1 then (1 : ℝ) else 0)
  let p := favg (fun c : Clause n k => if v ∈ c.1.1 then (1 : ℝ) else 0)
  have hP : 0 ≤ P := favg_nonneg fun _ => by split <;> norm_num
  have hh := support_pair_probability_scaled hk hkn v w hw
  have hp := support_probability_scaled hkn v
  change ((n : ℝ)-1)*P = ((k : ℝ)-1)*p at hh
  change (n : ℝ)*p = k at hp
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hm : (n : ℝ)*((n : ℝ)-1)*P = ((k : ℝ)-1)*k := by
    calc
      _ = (n : ℝ)*(((n : ℝ)-1)*P) := by ring
      _ = (n : ℝ)*(((k : ℝ)-1)*p) := by rw [hh]
      _ = ((k : ℝ)-1)*((n : ℝ)*p) := by ring
      _ = _ := by rw [hp]
  have hmul := mul_nonneg (show 0 ≤ (n : ℝ)-2 by linarith) (mul_nonneg (Nat.cast_nonneg n) hP)
  change (n : ℝ)^2*P ≤ _
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

lemma incidence_indicator_le {n k : ℕ} (R : Finset (Fin n)) (c : Clause n k) :
    (if clauseOverlap R c ≠ 0 then (1 : ℝ) else 0) ≤
      ∑ v ∈ R, if v ∈ c.1.1 then (1 : ℝ) else 0 := by
  split_ifs with h
  · obtain ⟨v,hv⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h)
    have hRv := (Finset.mem_inter.mp hv).1
    have hcv := (Finset.mem_inter.mp hv).2
    have hh := Finset.single_le_sum (f := fun v => if v ∈ c.1.1 then (1 : ℝ) else 0)
      (fun w _ => by split <;> norm_num) hRv
    simpa only [ite_eq_left hcv] using hh
  · exact Finset.sum_nonneg fun _ _ => by split <;> norm_num

lemma collision_indicator_le {n k : ℕ} (R : Finset (Fin n)) (c : Clause n k) :
    (if 2 ≤ clauseOverlap R c then (1 : ℝ) else 0) ≤
      ∑ v ∈ R, ∑ w ∈ R, if v ≠ w ∧ v ∈ c.1.1 ∧ w ∈ c.1.1 then (1 : ℝ) else 0 := by
  have hnn (v : Fin n) : 0 ≤ ∑ w ∈ R,
      if v ≠ w ∧ v ∈ c.1.1 ∧ w ∈ c.1.1 then (1 : ℝ) else 0 :=
    Finset.sum_nonneg fun _ _ => by split <;> norm_num
  split_ifs with h
  · obtain ⟨v,hv,w,hw,hvw⟩ := Finset.one_lt_card.mp (by change 2 ≤ (R ∩ c.1.1).card at h; omega : 1 < (R ∩ c.1.1).card)
    have hh := Finset.single_le_sum
      (f := fun w => if v ≠ w ∧ v ∈ c.1.1 ∧ w ∈ c.1.1 then (1 : ℝ) else 0)
      (fun w _ => by split <;> norm_num) (Finset.mem_inter.mp hw).1
    have hh' := Finset.single_le_sum (fun v _ => hnn v) (Finset.mem_inter.mp hv).1
    apply le_trans _ hh'
    have hp : v ≠ w ∧ v ∈ c.1.1 ∧ w ∈ c.1.1 :=
      ⟨hvw,(Finset.mem_inter.mp hv).2,(Finset.mem_inter.mp hw).2⟩
    simpa only [ite_eq_left hp] using hh
  · exact Finset.sum_nonneg fun v _ => hnn v

lemma incidence_probability_scaled {n k : ℕ} (hkn : k ≤ n) (R : Finset (Fin n)) :
    (n : ℝ)*favg (fun c : Clause n k => if clauseOverlap R c ≠ 0 then (1 : ℝ) else 0) ≤
      (R.card : ℝ)*k := by
  have hh := favg_mono (fun c : Clause n k => incidence_indicator_le R c)
  rw [favg_sum] at hh
  have hm := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (α := ℝ) n)
  rw [Finset.mul_sum] at hm
  simp only [support_probability_scaled hkn, Finset.sum_const, nsmul_eq_mul] at hm
  exact hm

lemma collision_probability_scaled {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n)
    (R : Finset (Fin n)) :
    (n : ℝ)^2*favg (fun c : Clause n k => if 2 ≤ clauseOverlap R c then (1 : ℝ) else 0) ≤
      2*(R.card : ℝ)^2*(k : ℝ)^2 := by
  let := clause_nonempty n k hkn
  have hh := favg_mono (fun c : Clause n k => collision_indicator_le R c)
  simp_rw [favg_sum] at hh
  calc
    _ ≤ (n : ℝ)^2*∑ v ∈ R, ∑ w ∈ R,
        favg (fun c : Clause n k => if v ≠ w ∧ v ∈ c.1.1 ∧ w ∈ c.1.1 then (1 : ℝ) else 0) :=
      mul_le_mul_of_nonneg_left hh (sq_nonneg _)
    _ = ∑ v ∈ R, ∑ w ∈ R, (n : ℝ)^2*
        favg (fun c : Clause n k => if v ≠ w ∧ v ∈ c.1.1 ∧ w ∈ c.1.1 then (1 : ℝ) else 0) := by
      simp_rw [Finset.mul_sum]
    _ ≤ ∑ _v ∈ R, ∑ _w ∈ R, 2*(k : ℝ)^2 := by
      apply Finset.sum_le_sum
      intro v _
      apply Finset.sum_le_sum
      intro w _
      by_cases hvw : v = w
      · simp only [hvw, ne_eq, not_true_eq_false, false_and, ite_false, favg_const, mul_zero]
        positivity
      · simp only [ne_eq, hvw, not_false_eq_true, true_and]
        exact support_pair_probability_bound hn hk hkn v w (Ne.symm hvw)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

lemma rootVariables_card {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n) :
    (rootVariables e).card = k := by
  rw [rootVariables, Finset.card_image_of_injective _ (fun _ _ h => Sum.inl.inj (e.injective h))]
  simp

lemma clauseOverlap_merge {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n)
    (p : RootData u k) : clauseOverlap (rootVariables e) (mergeClause e p.1 p.2) = rootSize p.1 := by
  have he : rootVariables e ∩ (mergeClause e p.1 p.2).1.1 =
      (rootSupport p.1).image (fun j => e (Sum.inl j)) := by
    ext v
    obtain ⟨z,rfl⟩ := e.surjective v
    cases z <;> simp [rootVariables, mergeClause, rootSupport]
  simp only [clauseOverlap, he, Finset.card_image_of_injective _ (fun _ _ h => Sum.inl.inj (e.injective h)), rootSize]

lemma rootIncident_scaled {n k u : ℕ} (hkn : k ≤ n) (e : Fin k ⊕ Fin u ≃ Fin n) :
    (n : ℝ)*hitProbability (rootIncident (u := u) (k := k)) ≤ (k : ℝ)^2 := by
  have he := favg_equiv (splitClauseEquiv e)
    (fun c : Clause n k => if clauseOverlap (rootVariables e) c ≠ 0 then (1 : ℝ) else 0)
  have hh := incidence_probability_scaled hkn (rootVariables e)
  change favg (fun p : RootData u k => if clauseOverlap (rootVariables e) (mergeClause e p.1 p.2) ≠ 0 then (1 : ℝ) else 0) = _ at he
  simp only [clauseOverlap_merge] at he
  rw [← he, rootVariables_card] at hh
  convert hh using 1
  · unfold hitProbability
    congr 2
    funext p
    unfold rootIncident
    split_ifs <;> rfl
  · ring

lemma rootCollision_scaled {n k u : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k)
    (hkn : k ≤ n) (e : Fin k ⊕ Fin u ≃ Fin n) :
    (n : ℝ)^2*hitProbability (rootCollision (u := u) (k := k)) ≤ 2*(k : ℝ)^4 := by
  have he := favg_equiv (splitClauseEquiv e)
    (fun c : Clause n k => if 2 ≤ clauseOverlap (rootVariables e) c then (1 : ℝ) else 0)
  have hh := collision_probability_scaled hn hk hkn (rootVariables e)
  change favg (fun p : RootData u k => if 2 ≤ clauseOverlap (rootVariables e) (mergeClause e p.1 p.2) then (1 : ℝ) else 0) = _ at he
  simp only [clauseOverlap_merge] at he
  rw [← he, rootVariables_card] at hh
  change _ ≤ 2*(k : ℝ)^2*(k : ℝ)^2 at hh
  convert hh using 1
  · unfold hitProbability
    congr 2
    funext p
    unfold rootCollision
    split_ifs <;> rfl
  · ring

lemma rootRewards_square_density {n u r M : ℕ} (hr : 2 ≤ r) (hru : r+1 ≤ u)
    (e : Fin (r+1) ⊕ Fin u ≃ Fin n) (a : Assignment (r+1))
    {B : ℝ} (hB : 0 ≤ B) (hM : (M : ℝ) ≤ B*n) :
    favg (fun ps : Fin M → RootData u (r+1) => (dataRewards (forcedReward a) Finset.univ ps)^2) ≤
      deletionMomentC (r+1) (B*(r+1 : ℕ)^2) (2*B^2*(r+1 : ℕ)^4)*durationLog (r+1) M := by
  have hn : r+1+u = n := by
    have hh := Fintype.card_congr e
    simpa only [Fintype.card_sum, Fintype.card_fin] using hh
  apply rootRewards_square_avg hr hru a
  · have hp := rootIncident_scaled (by omega : r+1 ≤ n) e
    have hm := mul_le_mul_of_nonneg_right hM (hitProbability_nonneg (rootIncident (u := u) (k := r+1)))
    have hb := mul_le_mul_of_nonneg_left hp hB
    nlinarith
  · have hq := rootCollision_scaled (by omega : 2 ≤ n) (by omega : 1 ≤ r+1) (by omega) e
    have hm := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) M) hM 2
    have hm' := mul_le_mul_of_nonneg_right hm (hitProbability_nonneg (rootCollision (u := u) (k := r+1)))
    have hb := mul_le_mul_of_nonneg_left hq (sq_nonneg B)
    nlinarith

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.rootRewards_square_density := @_root_.OAI.RandomKSAT.rootRewards_square_density
