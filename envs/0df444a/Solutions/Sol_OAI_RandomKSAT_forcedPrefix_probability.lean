-- Prove2me | solution 1 for OAI.RandomKSAT.forcedPrefix_probability
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T19:20:30.131934+00:00
-- url     : https://prove2.me/submissions/acbf734d-9dd5-419d-9e01-dfe2741e8f66

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/HiddenTests.lean:L116-L167
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.forcedPrefix_probability. The node keeps its source
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
import Theorems.Thm_OAI_RandomKSAT_favg_pi_restrict
import Theorems.Thm_OAI_RandomKSAT_forcedPrefix_testKills

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

lemma streamLaw_probability (n k : ℕ) (hkn : k ≤ n) :
    IsProbabilityMeasure (streamLaw n k) := by
  let := clauseLaw_probability n k hkn
  unfold streamLaw
  infer_instance

lemma count_set_fintype.{u_1} {α : Type u_1} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype α] (s : Set α) :
    Measure.count s = (Fintype.card s : ℝ≥0∞) := by
  rw [Measure.count_apply (Set.toFinite s).measurableSet,
    Set.encard_eq_coe_toFinset_card]
  simp

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.BlockKilling ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma measurableSet_setSAT (u s : ℕ) (S : Finset (Assignment u)) (g : ℕ) :
    MeasurableSet {ω : Stream u s | SetSAT S ω g} := by
  simp only [SetSAT, Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro a
  by_cases ha : a ∈ S
  · simp only [ha, true_and, Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro _
    exact (Set.toFinite {c : Clause u s | Satisfies c a}).measurableSet.preimage
      (measurable_pi_apply i)
  · simp only [ha, false_and, Set.ofPred_false]
    exact MeasurableSet.empty

lemma blockKill_compl {u s : ℕ} (hsu : s ≤ u) (S : Finset (Assignment u)) (g : ℕ) :
    blockKill u s S g = 1 - (streamLaw u s {ω | SetSAT S ω g}).toReal := by
  let := streamLaw_probability u s hsu
  have he : {ω : Stream u s | ¬ SetSAT S ω g} = {ω | SetSAT S ω g}ᶜ := rfl
  rw [blockKill, he, measure_compl (measurableSet_setSAT u s S g) (measure_ne_top _ _),
    measure_univ, ENNReal.toReal_sub_of_le prob_le_one (by simp), ENNReal.toReal_one]

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

lemma residual_cons {u s m : ℕ} (S : Finset (Assignment u)) (c : Clause u s)
    (cs : Fin m → Clause u s) :
    residual S (Fin.cons c cs) = residual (S.filter (Satisfies c)) cs := by
  ext a
  simp [residual, Fin.forall_fin_succ, and_assoc]

lemma clauseStep_iterate_avg (u s m : ℕ) (f : Finset (Assignment u) → ℝ)
    (S : Finset (Assignment u)) :
    (clauseStep u s)^[m] f S = favg (fun cs : Fin m → Clause u s => f (residual S cs)) := by
  induction m generalizing S with
  | zero => simp [residual, favg]
  | succ m ih =>
    rw [Function.iterate_succ_apply', clauseStep]
    simp_rw [ih]
    rw [← favg_prod (fun p : Clause u s × (Fin m → Clause u s) =>
      f (residual (S.filter (Satisfies p.1)) p.2)),
      ← favg_equiv (Fin.consEquiv (fun _ : Fin (m+1) => Clause u s))]
    congr 1
    funext p
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, residual_cons]

lemma blockKill_iterate {u s : ℕ} (hsu : s ≤ u) (S : Finset (Assignment u)) (m : ℕ) :
    blockKill u s S m = 1 - (clauseStep u s)^[m] (alive u) S := by
  rw [blockKill_compl hsu, clauseStep_iterate_avg]
  congr 1
  have he : {ω : Stream u s | SetSAT S ω m} =
      (fun ω (i : Fin m) => ω i) ⁻¹' {cs | (residual S cs).Nonempty} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, SetSAT, residual,
      Finset.Nonempty, Finset.mem_filter]
    exact exists_congr fun a => and_congr_right fun _ => (Fin.forall_iff (p := fun i : Fin m => Satisfies (ω i) a)).symm
  rw [he, ← Measure.map_apply (by fun_prop) (Set.toFinite _).measurableSet, prefixLaw hsu,
    uniformOn_real]
  simp only [alive, Set.mem_ofPred_eq]
  congr 1
  funext cs
  split_ifs <;> rfl

lemma favg_mul.{u_1} {α : Type u_1} [Fintype α] (c : ℝ) (f : α → ℝ) :
    favg (fun a => c*f a) = c*favg f := by
  simp only [favg, ← Finset.mul_sum]
  ring

lemma favg_nonneg.{u_1} {α : Type u_1} [Fintype α] {f : α → ℝ} (h : ∀ a, 0 ≤ f a) :
    0 ≤ favg f := by
  exact div_nonneg (Finset.sum_nonneg fun a _ => h a) (by positivity)

lemma alive_nonneg (u : ℕ) (S : Finset (Assignment u)) : 0 ≤ alive u S := by
  unfold alive
  split_ifs <;> norm_num

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

-- ---- from OAI.Probability.SATVariance.PairEvolution ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma rootSatisfies_zero {k : ℕ} (t : RootType k) (h : rootSize t = 0) (a : Assignment k) :
    ¬ RootSatisfies t a := by
  rintro ⟨j,hj⟩
  have hm : j ∈ rootSupport t := by simp [rootSupport, hj]
  have he : rootSupport t = ∅ := Finset.card_eq_zero.mp h
  rw [he] at hm
  exact Finset.notMem_empty j hm

lemma satisfies_cast {u s t : ℕ} (h : s = t) (c : Clause u s) (b : Assignment u) :
    Satisfies (clauseCastEquiv h c) b ↔ Satisfies c b := by
  subst t
  rfl

lemma forcedReward_le_alive {u k : ℕ} (a : Assignment k) (S : PairState u k) :
    forcedReward a S ≤ alive u (fibre a S) := by
  unfold forcedReward
  split_ifs with h
  · obtain ⟨x,hx⟩ := h.1
    have hf : (fibre a S).Nonempty := by
      refine ⟨x.2, ?_⟩
      have he : (a,x.2) = x := by rw [← h.2 x hx]
      simp [fibre, he, hx]
    simp [alive, hf]
  · exact alive_nonneg _ _

lemma dataSatisfies_refresh_fixed {u k : ℕ} (a : Assignment k) (p : RootData u k)
    (z : RefreshNoise u k) (b : Assignment u) :
    DataSatisfies (refreshData a p z) (a,b) ↔
      if rootSize p.1 = 0 then Satisfies z.1 b else DataSatisfies p (a,b) := by
  by_cases h : rootSize p.1 = 0
  · simp [DataSatisfies, refreshData, refreshPart, h, rootSatisfies_zero p.1 h a,
      satisfies_cast]
  · by_cases ht : rootSize p.1 = 1 ∧ RootSatisfies p.1 a
    · simp [DataSatisfies, refreshData, refreshPart, ht]
    · simp [DataSatisfies, refreshData, refreshPart, h, ht]

lemma fibre_pairPrefix_refresh {u k M : ℕ} (a : Assignment k) (env : Fin M → RootData u k)
    (o : Fin M → Clause u k) (ys : Fin k → Fin M → Clause u (k-1)) (m : ℕ) :
    fibre a (pairPrefix Finset.univ (fun i => refreshData a (env i) (o i, fun j => ys j i)) m) =
      fibrePrefix a env o m := by
  ext b
  simp only [fibre, pairPrefix, fibrePrefix, Finset.mem_filter, Finset.mem_univ, true_and,
    dataSatisfies_refresh_fixed]

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.HiddenTests ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
private abbrev Finset.prod_le_prod₀ := @Finset.prod_le_prod

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma familyKill_nonneg.{u_1} {u s : ℕ} {ι : Type u_1} [Fintype ι]
    (S : Finset (Assignment u)) (cs : ι → Clause u s) : 0 ≤ familyKill S cs := by
  unfold familyKill
  split <;> norm_num

lemma familyKill_residual.{u_1} {u s : ℕ} {ι : Type u_1} [Fintype ι]
    (S : Finset (Assignment u)) (cs : ι → Clause u s) :
    familyKill S cs = 1-alive u (residual S cs) := by
  have he : (residual S cs).Nonempty ↔ ∃ b ∈ S, ∀ i, Satisfies (cs i) b := by
    simp only [Finset.Nonempty, residual, Finset.mem_filter]
  unfold familyKill alive
  simp only [he]
  split <;> norm_num

lemma familyKill_equiv.{u_1, u_2} {u s : ℕ} {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ]
    (S : Finset (Assignment u)) (cs : κ → Clause u s) (e : ι ≃ κ) :
    familyKill S (fun i => cs (e i)) = familyKill S cs := by
  have he : (∃ b ∈ S, ∀ i, Satisfies (cs (e i)) b) ↔ ∃ b ∈ S, ∀ i, Satisfies (cs i) b := by
    constructor
    · rintro ⟨b,hb,hi⟩
      exact ⟨b,hb, fun j => by simpa using hi (e.symm j)⟩
    · rintro ⟨b,hb,hi⟩
      exact ⟨b,hb, fun j => hi (e j)⟩
  simp only [familyKill, he]

lemma familyKill_avg_fin {u s : ℕ} (hsu : s ≤ u) (S : Finset (Assignment u)) (m : ℕ) :
    favg (fun cs : Fin m → Clause u s => familyKill S cs) = blockKill u s S m := by
  let := clause_nonempty u s hsu
  simp_rw [familyKill_residual]
  rw [favg_sub, favg_const, blockKill_iterate hsu, clauseStep_iterate_avg]

lemma familyKill_avg.{u_1} {u s : ℕ} {ι : Type u_1} [Fintype ι] (hsu : s ≤ u)
    (S : Finset (Assignment u)) :
    favg (fun cs : ι → Clause u s => familyKill S cs) = blockKill u s S (Fintype.card ι) := by
  let e := (Fintype.equivFin ι).symm.arrowCongr (Equiv.refl (Clause u s))
  rw [← favg_equiv e]
  have he (cs : Fin (Fintype.card ι) → Clause u s) :
      familyKill S (e cs) = familyKill S cs :=
    familyKill_equiv S cs (Fintype.equivFin ι)
  simp_rw [he]
  exact familyKill_avg_fin hsu S _

lemma blockKill_mono_length {u s : ℕ} (hsu : s ≤ u) (S : Finset (Assignment u)) :
    Monotone (blockKill u s S) := by
  let := streamLaw_probability u s hsu
  intro m d hmd
  unfold blockKill
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro ω hm hd
  rcases hd with ⟨b,hb,ht⟩
  exact hm ⟨b,hb,fun i hi => ht i (lt_of_lt_of_le hi hmd)⟩

lemma restricted_familyKill_avg.{u_1} {u s : ℕ} {ι : Type u_1} [Fintype ι] [DecidableEq ι]
    (hsu : s ≤ u) (S : Finset (Assignment u)) (A : Finset ι) :
    favg (fun cs : ι → Clause u s => familyKill S (fun i : A => cs i)) =
      blockKill u s S A.card := by
  let := clause_nonempty u s hsu
  rw [favg_pi_restrict (fun i => i ∈ A) (familyKill S)]
  convert (familyKill_avg (ι := A) hsu S) using 1
  · congr 1
    exact Subsingleton.elim _ _
  · rw [Fintype.card_coe]

lemma forcedPrefix_familyKill {u k M : ℕ} (a : Assignment k) (env : Fin M → RootData u k)
    (o : Fin M → Clause u k) (ys : Fin k → Fin M → Clause u (k-1)) (m : ℕ)
    (hforced : ∀ x ∈ pairPrefix Finset.univ
      (fun i => refreshData a (env i) (o i, fun j => ys j i)) m, x.1 = a)
    (j : Fin k) (hj : Available a env j) :
    familyKill (fibrePrefix a env o m) (fun i : testIndices a env m j => ys j i) = 1 := by
  unfold familyKill
  rw [ite_eq_right]
  rintro ⟨b,hb,ht⟩
  apply forcedPrefix_testKills a env o ys m hforced j hj
  refine ⟨b,hb,fun i hi hit => ?_⟩
  exact ht ⟨i, by simp [testIndices, hi, hit]⟩

lemma prod_filter_indicator.{u_1} {ι : Type u_1} [Fintype ι] [DecidableEq ι] (A : Finset ι) (q : ℝ) :
    (∏ j : ι, if j ∈ A then q else 1) = q^A.card := by
  classical
  rw [← Finset.prod_filter]
  simp

lemma forcedPrefix_probability {u k M d : ℕ} (hku : k ≤ u) (a : Assignment k)
    (env : Fin M → RootData u k) (o : Fin M → Clause u k) (m : ℕ)
    (J : Finset (Fin k)) (hJ : ∀ j ∈ J, Available a env j)
    (hd : ∀ j, (testIndices a env m j).card ≤ d) :
    favg (fun ys : Fin k → Fin M → Clause u (k-1) =>
      forcedReward a (pairPrefix Finset.univ
        (fun i => refreshData a (env i) (o i, fun j => ys j i)) m)) ≤
          alive u (fibrePrefix a env o m) * blockKill u (k-1) (fibrePrefix a env o m) d ^ J.card := by
  let := clause_nonempty u (k-1) (by omega)
  let S := fibrePrefix a env o m
  let q := blockKill u (k-1) S d
  let F (j : Fin k) (w : Fin M → Clause u (k-1)) : ℝ :=
    if j ∈ J then familyKill S (fun i : testIndices a env m j => w i) else 1
  have hF : ∀ j w, 0 ≤ F j w := by
    intro j w
    dsimp only [F]
    split
    · exact familyKill_nonneg _ _
    · norm_num
  have hp (ys : Fin k → Fin M → Clause u (k-1)) :
      forcedReward a (pairPrefix Finset.univ
        (fun i => refreshData a (env i) (o i, fun j => ys j i)) m) ≤
          alive u S * ∏ j, F j (ys j) := by
    unfold forcedReward
    split_ifs with h
    · have hprod : (∏ j, F j (ys j)) = 1 := by
        apply Finset.prod_eq_one
        intro j _
        dsimp only [F]
        split_ifs with hj
        · exact forcedPrefix_familyKill a env o ys m h.2 j (hJ j hj)
        · rfl
      rw [hprod, mul_one]
      have hh := forcedReward_le_alive a (pairPrefix Finset.univ
        (fun i => refreshData a (env i) (o i, fun j => ys j i)) m)
      rw [fibre_pairPrefix_refresh] at hh
      simpa only [forcedReward, ite_eq_left h] using hh
    · exact mul_nonneg (alive_nonneg _ _) (Finset.prod_nonneg fun j _ => hF j _)
  have havg (j : Fin k) : favg (F j) ≤ if j ∈ J then q else 1 := by
    by_cases hj : j ∈ J
    · simp only [F, ite_eq_left hj]
      rw [restricted_familyKill_avg (by omega)]
      exact blockKill_mono_length (by omega) S (hd j)
    · simp only [F, ite_eq_right hj, favg_const, le_refl]
  calc
    _ ≤ favg (fun ys : Fin k → Fin M → Clause u (k-1) => alive u S * ∏ j, F j (ys j)) :=
      favg_mono hp
    _ = alive u S * ∏ j, favg (F j) := by rw [favg_mul, favg_pi_product]
    _ ≤ alive u S * ∏ j : Fin k, if j ∈ J then q else 1 := by
      apply mul_le_mul_of_nonneg_left _ (alive_nonneg _ _)
      exact Finset.prod_le_prod₀ (fun j _ => favg_nonneg (hF j)) (fun j _ => havg j)
    _ = _ := by rw [prod_filter_indicator]

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.forcedPrefix_probability := @_root_.OAI.RandomKSAT.forcedPrefix_probability
