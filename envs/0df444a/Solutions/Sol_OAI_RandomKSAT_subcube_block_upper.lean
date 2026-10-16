-- Prove2me | solution 1 for OAI.RandomKSAT.subcube_block_upper
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T15:38:02.312898+00:00
-- url     : https://prove2.me/submissions/60e31216-314e-4a08-ada0-24b4923a3a5b

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/Subcube.lean:L173-L206
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.subcube_block_upper. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SATSharpness
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement
import Definitions.Def_OAI_Probability_SATVariance_RootDisintegration
import Definitions.Def_OAI_Probability_SATVariance_SupportProbabilities
import Definitions.Def_OAI_Probability_SATVariance_Subcube
import Theorems.Thm_OAI_RandomKSAT_blockKill_iterate
import Theorems.Thm_OAI_RandomKSAT_clauseStep_iterate_avg
import Theorems.Thm_OAI_RandomKSAT_favg_pi_on
import Theorems.Thm_OAI_RandomKSAT_support_probability_scaled

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

lemma killing_card {n k : ℕ} {S : Finset (Assignment n)} (hS : S.Nonempty) :
    Fintype.card {c : Clause n k // Kills S c} = (frozen S).card.choose k := by
  classical
  obtain ⟨a₀, ha₀⟩ := hS
  rw [Fintype.card_congr (killingEquiv ha₀)]
  rw [Fintype.card_of_subtype ((frozen S).powersetCard k) (by intro s; simp)]
  exact Finset.card_powersetCard _ _

lemma count_set_fintype.{u_1} {α : Type u_1} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype α] (s : Set α) :
    Measure.count s = (Fintype.card s : ℝ≥0∞) := by
  rw [Measure.count_apply (Set.toFinite s).measurableSet,
    Set.encard_eq_coe_toFinset_card]
  simp

lemma clauseLaw_kills {n k : ℕ} {S : Finset (Assignment n)} (hS : S.Nonempty) :
    clauseLaw n k {c | Kills S c} =
      ((frozen S).card.choose k : ℝ≥0∞) / ((n.choose k : ℝ≥0∞) * 2 ^ k) := by
  rw [clauseLaw, uniformOn_univ, count_set_fintype]
  have hc : Fintype.card ↑{c : Clause n k | Kills S c} = (frozen S).card.choose k := by
    simpa only [Fintype.card_subtype, Set.mem_ofPred_eq] using (killing_card hS)
  rw [hc, clause_card]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.BlockKilling ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma clauseLaw_kills_toReal {u s : ℕ} {S : Finset (Assignment u)} (hS : S.Nonempty) :
    (clauseLaw u s {c | Kills S c}).toReal = killRatio u (frozen S).card s := by
  rw [clauseLaw_kills hS]
  simp [killRatio, ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_pow, mul_comm]

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

lemma favg_add.{u_1} {α : Type u_1} [Fintype α] (f g : α → ℝ) :
    favg (fun a => f a + g a) = favg f + favg g := by
  simp only [favg, Finset.sum_add_distrib, add_div]

lemma favg_sub.{u_1} {α : Type u_1} [Fintype α] (f g : α → ℝ) :
    favg (fun a => f a - g a) = favg f - favg g := by
  simp only [favg, Finset.sum_sub_distrib, sub_div]

lemma favg_equiv.{u_1, u_2} {α : Type u_1} {β : Type u_2} [Fintype α] [Fintype β] (e : α ≃ β) (f : β → ℝ) :
    favg (fun a => f (e a)) = favg f := by
  rw [favg, favg, e.sum_comp f, Fintype.card_congr e]

lemma favg_prod.{u_1, u_2} {α : Type u_1} {β : Type u_2} [Fintype α] [Fintype β] (f : α × β → ℝ) :
    favg f = favg (fun a => favg fun b => f (a,b)) := by
  simp only [favg, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div]
  ring

lemma uniformOn_real.{u_1} {α : Type u_1} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (s : Set α) :
    (uniformOn Set.univ s).toReal = favg (fun a => if a ∈ s then 1 else 0) := by
  rw [uniformOn_univ, count_set_fintype]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, favg]
  congr 1
  simp [Fintype.card_subtype]

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

-- ---- from OAI.Probability.SATVariance.FiberRefresh ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma favg_pi_eval.{u_1, u_2} {ι : Type u_1} {α : Type u_2} [Fintype ι] [DecidableEq ι] [Fintype α] [Nonempty α]
    (i : ι) (f : α → ℝ) : favg (fun x : ι → α => f (x i)) = favg f := by
  classical
  have he := favg_equiv (Equiv.funSplitAt i α).symm (fun x : ι → α => f (x i))
  rw [← he, favg_prod]
  simp only [Equiv.funSplitAt_symm_apply]
  simp only [dite_true]
  simp_rw [favg_const]

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.Subcube ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal Topology

namespace RandomKSAT

lemma mem_subcube {u b : ℕ} {a : Assignment u} :
    a ∈ subcube u b ↔ ∀ v : Fin u, (v : ℕ) < b → a v = false := by
  simp [subcube]

lemma subcube_nonempty (u b : ℕ) : (subcube u b).Nonempty := by
  exact ⟨fun _ => false, mem_subcube.mpr (by simp)⟩

lemma subcube_sat_of_disjoint.{u_1} {u b k : ℕ} {ι : Type u_1} [Fintype ι]
    (cs : ι → Clause u k)
    (hkill : ∀ i, ¬ Kills (subcube u b) (cs i))
    (hdisj : ∀ i j, i ≠ j → ∀ v : Fin u, b ≤ (v : ℕ) →
      v ∈ (cs i).1.1 → v ∉ (cs j).1.1) :
    ∃ a ∈ subcube u b, ∀ i, Satisfies (cs i) a := by
  have hw : ∀ i, ∃ a ∈ subcube u b, Satisfies (cs i) a := by
    intro i
    simpa only [Kills, not_forall, exists_prop, not_not] using hkill i
  choose a ha hv using hw
  choose v hv using hv
  let x : Assignment u := fun w =>
    if h : b ≤ (w : ℕ) ∧ ∃ i, w ∈ (cs i).1.1 then
      a h.2.choose w else false
  refine ⟨x, mem_subcube.mpr ?_, ?_⟩
  · intro w hw
    simp [x, show ¬ b ≤ (w : ℕ) by omega]
  · intro i
    refine ⟨v i, ?_⟩
    by_cases hb : (v i : Fin u).val < b
    · have hfalse := mem_subcube.mp (ha i) (v i) hb
      have hv' := hv i
      rw [hfalse] at hv'
      simpa [x, show ¬ b ≤ (v i : Fin u).val by omega] using hv'
    · have hh : b ≤ (v i : Fin u).val ∧ ∃ j, (v i : Fin u) ∈ (cs j).1.1 :=
        ⟨by omega, i, (v i).property⟩
      have he : hh.2.choose = i := by
        by_contra hn
        exact hdisj i hh.2.choose (Ne.symm hn) (v i) hh.1 (v i).property hh.2.choose_spec
      simp only [x, dite_eq_left hh]
      rw [he]
      exact hv i

lemma frozen_subcube (u b : ℕ) :
    frozen (subcube u b) = Finset.univ.filter (fun v : Fin u => (v : ℕ) < b) := by
  ext v
  simp only [frozen, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    by_contra hn
    let a : Assignment u := fun w => if w = v then true else false
    have ha : a ∈ subcube u b := by
      apply mem_subcube.mpr
      intro w hw
      have hwv : w ≠ v := by rintro rfl; exact hn hw
      simp [a, hwv]
    have h0 : (fun _ : Fin u => false) ∈ subcube u b := mem_subcube.mpr (by simp)
    have hh := h _ h0 a ha
    simp [a] at hh
  · intro hv a ha c hc
    exact (mem_subcube.mp ha v hv).trans (mem_subcube.mp hc v hv).symm

lemma frozen_subcube_card {u b : ℕ} (hbu : b ≤ u) :
    (frozen (subcube u b)).card = b := by
  let e : {v : Fin u // (v : ℕ) < b} ≃ Fin b :=
    { toFun := fun v => ⟨v.1.val, v.2⟩
      invFun := fun v => ⟨⟨v.val, v.isLt.trans_le hbu⟩, v.isLt⟩
      left_inv := by intro v; rfl
      right_inv := by intro v; rfl }
  rw [frozen_subcube]
  simpa only [Fintype.card_subtype, Fintype.card_fin] using Fintype.card_congr e

lemma subcube_killing_indicator {u b k t : ℕ} (cs : Fin t → Clause u k) :
    (if ¬ (residual (subcube u b) cs).Nonempty then (1 : ℝ) else 0) ≤
      (∑ i, if Kills (subcube u b) (cs i) then (1 : ℝ) else 0) +
      ∑ i, ∑ j ∈ Finset.univ.erase i, ∑ v : Fin u,
        if v ∈ (cs i).1.1 ∧ v ∈ (cs j).1.1 then (1 : ℝ) else 0 := by
  by_cases hs : (residual (subcube u b) cs).Nonempty
  · rw [ite_eq_right (not_not.mpr hs)]
    positivity
  rw [ite_eq_left hs]
  have hex : (∃ i, Kills (subcube u b) (cs i)) ∨
      ∃ i j, i ≠ j ∧ ∃ v : Fin u, v ∈ (cs i).1.1 ∧ v ∈ (cs j).1.1 := by
    by_contra hn
    push Not at hn
    have hh := subcube_sat_of_disjoint cs hn.1 (by
      intro i j hij v _ hv
      exact hn.2 i j hij v hv)
    obtain ⟨a, ha, hcs⟩ := hh
    exact hs ⟨a, by simp only [residual, Finset.mem_filter]; exact ⟨ha, hcs⟩⟩
  rcases hex with ⟨i, hi⟩ | ⟨i, j, hij, v, hv, hw⟩
  · have h := Finset.single_le_sum (s := (Finset.univ : Finset (Fin t)))
      (f := fun j => if Kills (subcube u b) (cs j) then (1 : ℝ) else 0)
      (fun _ _ => by positivity) (Finset.mem_univ i)
    simp only [ite_eq_left hi] at h
    exact h.trans (le_add_of_nonneg_right (by positivity))
  · have h1 := Finset.single_le_sum (s := (Finset.univ : Finset (Fin u)))
      (f := fun w => if w ∈ (cs i).1.1 ∧ w ∈ (cs j).1.1 then (1 : ℝ) else 0)
      (fun _ _ => by positivity) (Finset.mem_univ v)
    rw [ite_eq_left ⟨hv,hw⟩] at h1
    have h2 := Finset.single_le_sum (s := Finset.univ.erase i)
      (f := fun j => ∑ v : Fin u,
        if v ∈ (cs i).1.1 ∧ v ∈ (cs j).1.1 then (1 : ℝ) else 0)
      (fun _ _ => by positivity) (by simp [Ne.symm hij] : j ∈ Finset.univ.erase i)
    have h3 := Finset.single_le_sum (s := (Finset.univ : Finset (Fin t)))
      (f := fun i => ∑ j ∈ Finset.univ.erase i, ∑ v : Fin u,
        if v ∈ (cs i).1.1 ∧ v ∈ (cs j).1.1 then (1 : ℝ) else 0)
      (fun _ _ => by positivity) (Finset.mem_univ i)
    exact (h1.trans (h2.trans h3)).trans (le_add_of_nonneg_left (by positivity))

lemma favg_pi_pair.{u_1, u_2} {ι : Type u_1} {α : Type u_2} [Fintype ι] [DecidableEq ι]
    [Fintype α] [Nonempty α] (i j : ι) (hij : i ≠ j) (f : α → ℝ) :
    favg (fun cs : ι → α => f (cs i) * f (cs j)) = (favg f)^2 := by
  simpa [hij] using favg_pi_on ({i,j} : Finset ι) f

lemma support_probability {u k : ℕ} (hu : 0 < u) (hku : k ≤ u) (v : Fin u) :
    favg (fun c : Clause u k => if v ∈ c.1.1 then (1 : ℝ) else 0) = (k : ℝ)/u := by
  have h := support_probability_scaled hku v
  exact (eq_div_iff (by positivity)).mpr (by linarith)

lemma overlap_favg {u k t : ℕ} (hu : 0 < u) (hku : k ≤ u)
    (i j : Fin t) (hij : i ≠ j) :
    favg (fun cs : Fin t → Clause u k => ∑ v : Fin u,
      if v ∈ (cs i).1.1 ∧ v ∈ (cs j).1.1 then (1 : ℝ) else 0) = (k : ℝ)^2/u := by
  let := clause_nonempty u k hku
  rw [favg_sum]
  have hh (v : Fin u) :
      favg (fun cs : Fin t → Clause u k =>
        if v ∈ (cs i).1.1 ∧ v ∈ (cs j).1.1 then (1 : ℝ) else 0) = ((k : ℝ)/u)^2 := by
    have he (cs : Fin t → Clause u k) :
        (if v ∈ (cs i).1.1 ∧ v ∈ (cs j).1.1 then (1 : ℝ) else 0) =
        (if v ∈ (cs i).1.1 then (1 : ℝ) else 0) *
          (if v ∈ (cs j).1.1 then (1 : ℝ) else 0) := by
      split_ifs <;> simp_all
    simp only [he]
    rw [favg_pi_pair i j hij (fun c : Clause u k => if v ∈ c.1.1 then (1 : ℝ) else 0),
      support_probability hu hku v]
  simp only [hh, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

lemma blockKill_favg {u k t : ℕ} (hku : k ≤ u) (S : Finset (Assignment u)) :
    blockKill u k S t =
      favg (fun cs : Fin t → Clause u k => if ¬(residual S cs).Nonempty then (1 : ℝ) else 0) := by
  let := clause_nonempty u k hku
  rw [blockKill_iterate hku, clauseStep_iterate_avg]
  have he : (fun cs : Fin t → Clause u k => if ¬(residual S cs).Nonempty then (1 : ℝ) else 0) =
      (fun cs => 1 - alive u (residual S cs)) := by
    funext cs
    simp only [alive]
    split_ifs <;> simp_all
  rw [he, favg_sub, favg_const]

lemma subcube_block_upper {u b k : ℕ} (hu : 0 < u) (hbu : b ≤ u) (hku : k ≤ u)
    (t : ℕ) :
    blockKill u k (subcube u b) t ≤
      (t : ℝ) * killRatio u b k + (t : ℝ)^2 * (k : ℝ)^2 / u := by
  let := clause_nonempty u k hku
  rw [blockKill_favg hku]
  have hh := favg_mono (subcube_killing_indicator (u := u) (b := b) (k := k) (t := t))
  apply hh.trans
  rw [favg_add, favg_sum, favg_sum]
  have hsingle (i : Fin t) :
      favg (fun cs : Fin t → Clause u k => if Kills (subcube u b) (cs i) then (1 : ℝ) else 0) =
        killRatio u b k := by
    rw [favg_pi_eval i (fun c : Clause u k => if Kills (subcube u b) c then (1 : ℝ) else 0)]
    have hp := clauseLaw_kills_toReal (subcube_nonempty u b) (s := k)
    rw [clauseLaw, uniformOn_real, frozen_subcube_card hbu] at hp
    exact hp
  simp only [hsingle, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  apply add_le_add le_rfl
  have hpair (i : Fin t) :
      favg (fun cs : Fin t → Clause u k => ∑ j ∈ Finset.univ.erase i, ∑ v : Fin u,
        if v ∈ (cs i).1.1 ∧ v ∈ (cs j).1.1 then (1 : ℝ) else 0) ≤
        (t : ℝ) * ((k : ℝ)^2/u) := by
    rw [favg_sum]
    calc
      _ = ∑ _j ∈ Finset.univ.erase i, (k : ℝ)^2/u := by
        apply Finset.sum_congr rfl
        intro j hj
        exact overlap_favg hu hku i j (Ne.symm (Finset.mem_erase.mp hj).1)
      _ ≤ ∑ _j : Fin t, (k : ℝ)^2/u :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (by intros; positivity)
      _ = _ := by simp
  calc
    _ ≤ ∑ _i : Fin t, (t : ℝ) * ((k : ℝ)^2/u) := Finset.sum_le_sum fun i _ => hpair i
    _ = _ := by simp; ring

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal Topology


theorem solution : type_of% @_root_.OAI.RandomKSAT.subcube_block_upper := @_root_.OAI.RandomKSAT.subcube_block_upper
