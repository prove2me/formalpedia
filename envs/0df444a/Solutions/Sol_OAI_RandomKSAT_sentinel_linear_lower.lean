-- Prove2me | solution 1 for OAI.RandomKSAT.sentinel_linear_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:08:14.547201+00:00
-- url     : https://prove2.me/submissions/12b6332a-ffeb-4a3a-a198-51a4f7fcb176

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/FailureWindows.lean:L189-L242
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.sentinel_linear_lower. The node keeps its source
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
import Definitions.Def_OAI_Probability_SATVariance_OmissionCompression
import Definitions.Def_OAI_Probability_SATVariance_CapBridge
import Definitions.Def_OAI_Probability_SATVariance_ShuffleAverages
import Definitions.Def_OAI_Probability_SATVariance_BystanderStops
import Definitions.Def_OAI_Probability_SATVariance_InsertionVariance
import Definitions.Def_OAI_Probability_SATVariance_IsolatedSupports
import Definitions.Def_OAI_Probability_SATVariance_BystanderVariance
import Theorems.Thm_OAI_RandomKSAT_floor_window_bounds
import Theorems.Thm_OAI_RandomKSAT_hall_probability_bound
import Theorems.Thm_OAI_RandomKSAT_lt_firstFailure_iff
import Theorems.Thm_OAI_RandomKSAT_lt_listStop_iff
import Theorems.Thm_OAI_RandomKSAT_min_isolate_mean_lower
import Theorems.Thm_OAI_RandomKSAT_selected_variance

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

lemma clauseLaw_probability (n k : ℕ) (hkn : k ≤ n) :
    IsProbabilityMeasure (clauseLaw n k) := by
  let := clause_nonempty n k hkn
  unfold clauseLaw
  infer_instance

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

lemma frozen_singleton {n : ℕ} (a : Assignment n) : frozen {a} = Finset.univ := by
  ext v
  simp [frozen]

lemma clauseLaw_not_satisfies {n k : ℕ} (hkn : k ≤ n) (a : Assignment n) :
    clauseLaw n k {c | ¬ Satisfies c a} = ((2 : ℝ≥0∞) ^ k)⁻¹ := by
  have he : {c : Clause n k | ¬ Satisfies c a} = {c | Kills {a} c} := by
    ext c
    simp [Kills]
  rw [he, clauseLaw_kills (Finset.singleton_nonempty a), frozen_singleton,
    Finset.card_univ, Fintype.card_fin]
  have hc : (n.choose k : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hkn).ne'
  rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inl hc)
    (Or.inl (ENNReal.natCast_ne_top _)), ← mul_assoc,
    ENNReal.mul_inv_cancel hc (ENNReal.natCast_ne_top _), one_mul]

lemma clauseLaw_satisfies {n k : ℕ} (hkn : k ≤ n) (a : Assignment n) :
    clauseLaw n k {c | Satisfies c a} = 1 - ((2 : ℝ≥0∞) ^ k)⁻¹ := by
  let := clauseLaw_probability n k hkn
  have he : {c : Clause n k | Satisfies c a} = {c | ¬ Satisfies c a}ᶜ := by
    ext c
    simp
  rw [he, measure_compl (Set.toFinite _).measurableSet (measure_ne_top _ _),
    measure_univ, clauseLaw_not_satisfies hkn]

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.FirstFailure ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma assignment_survival {n k : ℕ} (hkn : k ≤ n) (a : Assignment n) (m : ℕ) :
    streamLaw n k {ω | ∀ i < m, Satisfies (ω i) a} =
      (1 - ((2 : ℝ≥0∞) ^ k)⁻¹) ^ m := by
  let := clauseLaw_probability n k hkn
  have he : {ω : Stream n k | ∀ i < m, Satisfies (ω i) a} =
      Set.pi (Finset.range m) (fun _ => {c : Clause n k | Satisfies c a}) := by
    ext ω
    simp
  rw [he, streamLaw, Measure.infinitePi_pi]
  · simp [clauseLaw_satisfies hkn]
  · intro i _
    exact (Set.toFinite _).measurableSet

lemma first_moment_tail {n k : ℕ} (hkn : k ≤ n) (m : ℕ) :
    streamLaw n k {ω | (m : ℕ∞) < firstFailure ω} ≤
      (2 : ℝ≥0∞) ^ n * (1 - ((2 : ℝ≥0∞) ^ k)⁻¹) ^ m := by
  have he : {ω : Stream n k | (m : ℕ∞) < firstFailure ω} =
      ⋃ a : Assignment n, {ω | ∀ i < m, Satisfies (ω i) a} := by
    ext ω
    simp [lt_firstFailure_iff, PrefixSAT]
  rw [he]
  calc
    _ ≤ ∑ a : Assignment n, streamLaw n k {ω | ∀ i < m, Satisfies (ω i) a} :=
      measure_iUnion_fintype_le _ _
    _ = _ := by simp [assignment_survival hkn]

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.BlockKilling ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma rate_toReal (s : ℕ) :
    (1-((2 : ℝ≥0∞)^s)⁻¹).toReal = 1-((2 : ℝ)^s)⁻¹ := by
  rw [ENNReal.toReal_sub_of_le (ENNReal.inv_le_one.mpr (one_le_pow₀ (by norm_num)))
    (by simp)]
  simp

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

lemma prefixLaw {u s : ℕ} (hsu : s ≤ u) (m : ℕ) :
    (streamLaw u s).map (fun ω (i : Fin m) => ω i) =
      uniformOn (Set.univ : Set (Fin m → Clause u s)) := by
  let := clauseLaw_probability u s hsu
  rw [streamLaw, Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective,
    Measure.infinitePi_eq_pi]
  simpa only [Set.pi_univ, clauseLaw] using
    (uniformOn_pi (f := fun _ : Fin m => (Set.univ : Set (Clause u s)))).symm

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

lemma finiteSAT_stream {n k L m : ℕ} (ω : Stream n k) (hm : m ≤ L) :
    finiteSAT (fun j : Fin L => ω j) m ↔ PrefixSAT ω m := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, fun j hj => ha ⟨j, hj.trans_le hm⟩ hj⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, fun j hj => ha j hj⟩

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

lemma favg_pi_product.{u_1, u_2} {ι : Type u_1} {α : Type u_2} [Fintype ι] [DecidableEq ι] [Fintype α]
    (f : ι → α → ℝ) :
    favg (fun x : ι → α => ∏ i, f i (x i)) = ∏ i, favg (f i) := by
  classical
  unfold favg
  rw [← Fintype.prod_sum, Finset.prod_div_distrib]
  simp

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.SupportProbabilities ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.OmissionCompression ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma favg_insertNth.{u_1} {α : Type u_1} [Fintype α] {M : ℕ} (i : Fin (M+1))
    (f : (Fin (M+1) → α) → ℝ) :
    favg f = favg (fun c : α => favg (fun w : Fin M → α => f (i.insertNth c w))) := by
  rw [← favg_equiv (Fin.insertNthEquiv (fun _ => α) i) f, favg_prod]
  rfl

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.IsolatedSupports ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma avoidance_probability_lower {n k : ℕ} (hkn : k ≤ n) (hn : 0 < n)
    (c : Clause n k) :
    1-(k:ℝ)^2/n ≤ favg (fun d : Clause n k => if Disjoint c.1.1 d.1.1 then (1:ℝ) else 0) := by
  let := clause_nonempty n k hkn
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hp (v : Fin n) : favg (fun d : Clause n k => if v ∈ d.1.1 then (1:ℝ) else 0) = (k:ℝ)/n := by
    apply (eq_div_iff hn0).mpr
    nlinarith [support_probability_scaled hkn v]
  calc
    _ = favg (fun d : Clause n k => 1-∑ v ∈ c.1.1, if v ∈ d.1.1 then (1:ℝ) else 0) := by
      rw [favg_sub,favg_const,favg_sum]
      simp only [hp,Finset.sum_const,c.1.2,nsmul_eq_mul]
      ring
    _ ≤ _ := favg_mono (fun d => by
      by_cases h : Disjoint c.1.1 d.1.1
      · rw [ite_eq_left h]
        have hs : (∑ v ∈ c.1.1, if v ∈ d.1.1 then (1:ℝ) else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro v hv
          simp [Finset.disjoint_left.mp h hv]
        rw [hs]
        norm_num
      · rw [ite_eq_right h]
        obtain ⟨v,hv,hd⟩ := Finset.not_disjoint_iff.mp h
        have hh := Finset.single_le_sum (f := fun v : Fin n => if v ∈ d.1.1 then (1:ℝ) else 0)
          (fun _ _ => by positivity) hv
        rw [ite_eq_left hd] at hh
        linarith)

lemma log_one_sub_lower {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1/2) :
    -2*x ≤ Real.log (1-x) := by
  have hp : 0 < 1-x := by linarith
  have hi : (1-x)⁻¹ ≤ 1+2*x := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hp).mpr
    nlinarith
  linarith [Real.one_sub_inv_le_log_of_pos hp]

lemma slow_geometric_lower {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1/2) (J : ℕ) :
    Real.exp (-2*x*J) ≤ (1-x)^J := by
  have hp : 0 < 1-x := by linarith
  rw [←Real.exp_log hp,←Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have := mul_le_mul_of_nonneg_right (log_one_sub_lower hx hx') (show (0:ℝ) ≤ J by positivity)
  nlinarith

lemma isolated_insertNth {n k M : ℕ} (i : Fin (M+1)) (c : Clause n k) (w : Fin M → Clause n k) :
    isolated (i.insertNth c w) i ↔ ∀ j : Fin M, Disjoint c.1.1 (w j).1.1 := by
  unfold isolated
  rw [Fin.forall_iff_succAbove i]
  simp only [Fin.insertNth_apply_same, ne_eq, not_true_eq_false, false_implies, true_and,
    Fin.succAbove_ne, not_false_eq_true,true_implies,Fin.insertNth_apply_succAbove]

lemma favg_all.{u_1, u_2} {ι : Type u_1} {α : Type u_2} [Fintype ι] [DecidableEq ι] [Fintype α] (p : α → Prop) :
    favg (fun w : ι → α => if ∀ i, p (w i) then (1:ℝ) else 0) =
      (favg (fun a => if p a then (1:ℝ) else 0))^(Fintype.card ι) := by
  have he (w : ι → α) : (if ∀ i, p (w i) then (1:ℝ) else 0) =
      ∏ i, if p (w i) then (1:ℝ) else 0 := by simp only [Finset.prod_boole,Finset.mem_univ,true_implies]
  simp only [he]
  rw [favg_pi_product (fun _ a => if p a then (1:ℝ) else 0)]
  simp

lemma isolate_probability_lower {n k M R : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (hn : 2*k^2 ≤ n) (hM : M ≤ 2*R*n) (i : Fin (M+1)) :
    Real.exp (-4*(R:ℝ)*k^2) ≤ favg (fun w : Fin (M+1) → Clause n k => if isolated w i then (1:ℝ) else 0) := by
  let := clause_nonempty n k hkn
  have hn' : 0 < n := by omega
  have hnR : (0:ℝ) < n := by exact_mod_cast hn'
  have hx : 0 ≤ (k:ℝ)^2/n := by positivity
  have hx' : (k:ℝ)^2/n ≤ 1/2 := by
    apply (div_le_iff₀ hnR).mpr
    have hnR' : 2*(k:ℝ)^2 ≤ n := by exact_mod_cast hn
    linarith
  have he : Real.exp (-4*(R:ℝ)*k^2) ≤ (1-(k:ℝ)^2/n)^M := by
    apply le_trans ?_ (slow_geometric_lower hx hx' M)
    apply Real.exp_le_exp.mpr
    have hMR : (M:ℝ) ≤ 2*R*n := by exact_mod_cast hM
    have hh := mul_le_mul_of_nonneg_right hMR hx
    have hd : (2*(R:ℝ)*n)*((k:ℝ)^2/n) = 2*R*k^2 := by field_simp
    rw [hd] at hh
    nlinarith
  rw [favg_insertNth i]
  simp only [isolated_insertNth]
  have hm (c : Clause n k) :
      favg (fun w : Fin M → Clause n k => if ∀ j, Disjoint c.1.1 (w j).1.1 then (1:ℝ) else 0) =
      (favg (fun d : Clause n k => if Disjoint c.1.1 d.1.1 then (1:ℝ) else 0))^M := by
    have hh := favg_all (ι := Fin M) (fun d : Clause n k => Disjoint c.1.1 d.1.1)
    simp only [Fintype.card_fin] at hh
    convert hh using 1
    · congr 1
      funext w
      by_cases h : ∀ j : Fin M, Disjoint c.1.1 (w j).1.1 <;> simp [h]
    · congr 2
      funext d
      by_cases h : Disjoint c.1.1 d.1.1 <;> simp [h]
  simp only [hm]
  rw [←favg_const (α := Clause n k) (Real.exp (-4*(R:ℝ)*k^2))]
  exact favg_mono (fun c => he.trans (pow_le_pow_left₀ (by linarith)
    (avoidance_probability_lower hkn hn' c) M))

lemma isolate_count_lower {n k M R : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (hn : 2*k^2 ≤ n) (hM : M ≤ 2*R*n) :
    (M:ℝ)*Real.exp (-4*(R:ℝ)*k^2) ≤
      favg (fun w : Fin M → Clause n k => ((isolateSet w).card:ℝ)) := by
  have he (w : Fin M → Clause n k) : ((isolateSet w).card:ℝ) =
      ∑ i, if isolated w i then (1:ℝ) else 0 := by simp [isolateSet]
  simp only [he]
  rw [favg_sum]
  calc
    _ = ∑ _ : Fin M, Real.exp (-4*(R:ℝ)*k^2) := by simp
    _ ≤ _ := Finset.sum_le_sum (fun i _ => by
      cases M with
      | zero => exact i.elim0
      | succ M => exact isolate_probability_lower hk hkn hn (by omega) i)

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.SentinelBridge ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma mem_take_ofFn.{u_1} {α : Type u_1} {M m : ℕ} (w : Fin M → α) (c : α) :
    c ∈ (List.ofFn w).take m ↔ ∃ i : Fin M, i.val < m ∧ w i = c := by
  rw [List.mem_take_iff_getElem]
  constructor
  · rintro ⟨j,hj,he⟩
    have hj' : j < min m M := by simpa only [List.length_ofFn] using hj
    refine ⟨⟨j,lt_of_lt_of_le hj' (min_le_right _ _)⟩,lt_of_lt_of_le hj' (min_le_left _ _),?_⟩
    simpa only [List.getElem_ofFn] using he
  · rintro ⟨i,hi,he⟩
    refine ⟨i.val,?_,?_⟩
    · simpa only [List.length_ofFn,lt_min_iff] using And.intro hi i.isLt
    · simpa only [List.getElem_ofFn] using he

lemma listSAT_take_ofFn {n k M m : ℕ} (w : Fin M → Clause n k) :
    listSAT ((List.ofFn w).take m) ↔ finiteSAT w m := by
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a,fun i hi => ha (w i) ((mem_take_ofFn w _).mpr ⟨i,hi,rfl⟩)⟩
  · rintro ⟨a,ha⟩
    refine ⟨a,fun c hc => ?_⟩
    obtain ⟨i,hi,rfl⟩ := (mem_take_ofFn w c).mp hc
    exact ha i hi

lemma lt_listStop_ofFn_iff {n k M m : ℕ} (w : Fin M → Clause n k) (hm : m ≤ M) :
    m < listStop (List.ofFn w) ↔ finiteSAT w m := by
  rw [lt_listStop_iff,List.length_ofFn,and_iff_right hm,listSAT_take_ofFn]

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.FailureWindows ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
private theorem Measurable.of_eval {α δ : Type*} {X : δ → Type*}
    [MeasurableSpace α] [∀ a, MeasurableSpace (X a)] {f : α → ∀ a, X a}
    (hf : ∀ a, Measurable fun c => f c a) : Measurable f :=
  measurable_pi_lambda f hf
end Lean433MeasurableOfEval

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma finiteSAT_probability {n k M m : ℕ} (hkn : k ≤ n) (hm : m ≤ M) :
    favg (fun w : Fin M → Clause n k => if finiteSAT w m then (1:ℝ) else 0) =
      (streamLaw n k {ω | PrefixSAT ω m}).toReal := by
  have hp : Measurable (fun ω : Stream n k => fun j : Fin M => ω j) :=
    Measurable.of_eval (fun j => measurable_pi_apply j.val)
  have he : favg (fun w : Fin M → Clause n k => if finiteSAT w m then (1:ℝ) else 0) =
      (uniformOn Set.univ {w : Fin M → Clause n k | finiteSAT w m}).toReal := by
    simpa only [Set.mem_ofPred_eq] using
      (uniformOn_real {w : Fin M → Clause n k | finiteSAT w m}).symm
  rw [he,← prefixLaw hkn M,Measure.map_apply hp (Set.toFinite _).measurableSet]
  congr 2
  ext ω
  exact finiteSAT_stream ω hm

lemma finiteNotSAT_probability {n k M m : ℕ} (hkn : k ≤ n) (hm : m ≤ M) :
    favg (fun w : Fin M → Clause n k => if ¬finiteSAT w m then (1:ℝ) else 0) =
      (streamLaw n k {ω | ¬PrefixSAT ω m}).toReal := by
  have hp : Measurable (fun ω : Stream n k => fun j : Fin M => ω j) :=
    Measurable.of_eval (fun j => measurable_pi_apply j.val)
  have he : favg (fun w : Fin M → Clause n k => if ¬finiteSAT w m then (1:ℝ) else 0) =
      (uniformOn Set.univ {w : Fin M → Clause n k | ¬finiteSAT w m}).toReal := by
    rw [uniformOn_real]
    congr 1
    funext w
    by_cases h : finiteSAT w m <;> simp [h]
  rw [he,← prefixLaw hkn M,Measure.map_apply hp (Set.toFinite _).measurableSet]
  congr 2
  ext ω
  exact not_congr (finiteSAT_stream ω hm)

lemma finiteSAT_high_tail {n k M m : ℕ} (hkn : k ≤ n) (hm : m ≤ M) :
    favg (fun w : Fin M → Clause n k => if finiteSAT w m then (1:ℝ) else 0) ≤
      (2:ℝ)^n*(1-((2:ℝ)^k)⁻¹)^m := by
  rw [finiteSAT_probability hkn hm]
  have hh := ENNReal.toReal_mono (by finiteness) (first_moment_tail hkn m)
  simpa only [lt_firstFailure_iff,ENNReal.toReal_mul,ENNReal.toReal_pow,
    ENNReal.toReal_ofNat,rate_toReal] using hh

lemma finiteSAT_low_tail {n k M m : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) (hm : m ≤ M)
    {a : ℝ} (ha : 0 ≤ a) (ha' : Real.exp 2*a ≤ 1/2) (hm' : (m:ℝ) ≤ a*n) :
    favg (fun w : Fin M → Clause n k => if ¬finiteSAT w m then (1:ℝ) else 0) ≤ 2*a := by
  rw [finiteNotSAT_probability hkn hm,← finiteNotSAT_probability hkn (le_refl m)]
  exact hall_probability_bound hk hkn ha ha' hm'

lemma outsideWindow_bound {n k M Q V : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n)
    (hQ : 2*Q ≤ M) (hV : V ≤ M) {a : ℝ} (ha : 0 ≤ a)
    (ha' : Real.exp 2*a ≤ 1/2) (hQa : (2*Q:ℕ) ≤ a*n) :
    favg (fun w : Fin M → Clause n k => outsideWindow Q V (List.ofFn w)) ≤
      2*a+(2:ℝ)^n*(1-((2:ℝ)^k)⁻¹)^V := by
  have hh (w : Fin M → Clause n k) : outsideWindow Q V (List.ofFn w) ≤
      (if ¬finiteSAT w (2*Q) then (1:ℝ) else 0)+(if finiteSAT w V then 1 else 0) := by
    have hlow := lt_listStop_ofFn_iff w hQ
    have hhigh := lt_listStop_ofFn_iff w hV
    by_cases ha : finiteSAT w (2*Q) <;> by_cases hb : finiteSAT w V <;>
      simp only [outsideWindow,ha,hb,not_true_eq_false,not_false_eq_true,ite_true,ite_false] <;>
      split_ifs <;> norm_num
    simp_all
    omega
  have havg := favg_mono hh
  rw [favg_add] at havg
  exact havg.trans (add_le_add (finiteSAT_low_tail hk hkn hQ ha ha' hQa)
    (finiteSAT_high_tail hkn hV))

lemma sentinel_linear_lower {n k R : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n)
    (hR : 1 ≤ R) (hn : 2*k^2 ≤ n) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (haHall : Real.exp 2*a ≤ 1/2) (haβ : 2*a ≤ Real.exp (-4*(R:ℝ)*k^2)/4)
    (hlarge : 8 ≤ a*n)
    (hhigh : (2*(1-((2:ℝ)^k)⁻¹)^R)^n ≤ Real.exp (-4*(R:ℝ)*k^2)/4) :
    (a/(16*((2*R:ℕ)+1:ℝ)^2))*a*Real.exp (-4*(R:ℝ)*k^2)/16*n ≤
      fvariance (fun w : Fin (2*R*n) → Clause n k => (listStop (List.ofFn w):ℝ)) := by
  let M := 2*R*n
  let V := R*n
  let Q := ⌊a*n/4⌋₊
  let β := Real.exp (-4*(R:ℝ)*k^2)
  let γ := a/(16*((2*R:ℕ)+1:ℝ)^2)
  let p := (Q:ℝ)*((M:ℝ)+1-Q-V)/((M:ℝ)+1)^2
  have hβ : 0 < β := Real.exp_pos _
  have hγ : 0 < γ := by dsimp [γ]; positivity
  obtain ⟨hQlo,hQup,h2Q,hQV,hQM,hcoef⟩ := floor_window_bounds ha ha1 hR hlarge
  change a*n/8 ≤ (Q:ℝ) at hQlo
  change (Q:ℝ) ≤ a*n/4 at hQup
  change 2*Q ≤ M at h2Q
  change Q+V ≤ M+1 at hQV
  change Q ≤ M at hQM
  have hcoef' : γ ≤ p := by simpa only [γ,p,M,V,Nat.cast_mul,Nat.cast_ofNat] using hcoef
  have hp : 0 ≤ p := hγ.le.trans hcoef'
  have hn0 : 0 < n := by omega
  have hM0 : 0 < M := by dsimp [M]; positivity
  have hV : V ≤ M := by dsimp [V,M]; nlinarith
  have hsel := selected_variance (by omega : 1 ≤ k) hkn Q V hQV
  change p*favg (fun w : Fin M → Clause n k => (min Q (isolateSet w).card:ℝ)) ≤
    fvariance (fun w : Fin M → Clause n k => (listStop (List.ofFn w):ℝ))+
      p*Q*favg (fun w : Fin M → Clause n k => outsideWindow Q V (List.ofFn w)) at hsel
  have hmean := isolate_count_lower (by omega : 1 ≤ k) hkn hn (R := R) (M := M) (le_refl M)
  have hmin := min_isolate_mean_lower hM0 hQM hmean
  change (Q:ℝ)*β ≤ favg (fun w : Fin M → Clause n k => (min Q (isolateSet w).card:ℝ)) at hmin
  have hout := outsideWindow_bound hk hkn h2Q hV ha.le haHall (by
    push_cast
    nlinarith [mul_nonneg ha.le (show (0:ℝ) ≤ n by positivity)])
  have hpow : (2:ℝ)^n*(1-((2:ℝ)^k)⁻¹)^V = (2*(1-((2:ℝ)^k)⁻¹)^R)^n := by
    dsimp [V]
    rw [pow_mul,mul_pow]
  rw [hpow] at hout
  have hbad : favg (fun w : Fin M → Clause n k => outsideWindow Q V (List.ofFn w)) ≤ β/2 := by
    dsimp only [β]
    linarith
  have htotal := mul_le_mul_of_nonneg_left hmin hp
  have herror := mul_le_mul_of_nonneg_left hbad (mul_nonneg hp (show (0:ℝ) ≤ Q by positivity))
  have hs : p*Q*β/2 ≤ fvariance (fun w : Fin M → Clause n k => (listStop (List.ofFn w):ℝ)) := by
    nlinarith
  have hl := mul_le_mul hcoef' hQlo (by positivity) hp
  have hl' := mul_le_mul_of_nonneg_right hl (div_nonneg hβ.le (by norm_num : (0:ℝ) ≤ 2))
  calc
    _ = γ*(a*n/8)*(β/2) := by dsimp [γ,β]; ring
    _ ≤ p*Q*(β/2) := hl'
    _ = p*Q*β/2 := by ring
    _ ≤ _ := hs

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.sentinel_linear_lower := @_root_.OAI.RandomKSAT.sentinel_linear_lower
