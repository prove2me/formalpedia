-- Prove2me | solution 1 for OAI.RandomKSAT.selected_variance
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T19:58:09.741465+00:00
-- url     : https://prove2.me/submissions/f34894b9-5ea7-4193-84e7-fd5eea36e112

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/BystanderVariance.lean:L181-L212
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.selected_variance. The node keeps its source
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
import Theorems.Thm_OAI_RandomKSAT_favg_shuffle
import Theorems.Thm_OAI_RandomKSAT_harmless_private
import Theorems.Thm_OAI_RandomKSAT_insertVar_stop_lower
import Theorems.Thm_OAI_RandomKSAT_listStop_insert
import Theorems.Thm_OAI_RandomKSAT_selected_perm

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

lemma favg_add.{u_1} {α : Type u_1} [Fintype α] (f g : α → ℝ) :
    favg (fun a => f a + g a) = favg f + favg g := by
  simp only [favg, Finset.sum_add_distrib, add_div]

lemma favg_sub.{u_1} {α : Type u_1} [Fintype α] (f g : α → ℝ) :
    favg (fun a => f a - g a) = favg f - favg g := by
  simp only [favg, Finset.sum_sub_distrib, sub_div]

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

lemma favg_sq_sub_const.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (f : α → ℝ) (c : ℝ) :
    favg (fun a => (f a-c)^2) = favg (fun a => (f a)^2) - 2*c*favg f + c^2 := by
  have he : (fun a => (f a-c)^2) = (fun a => (f a)^2 - (2*c)*f a + c^2) := by
    funext a; ring
  rw [he, favg_add, favg_sub, favg_mul, favg_const]

lemma fvariance_centered.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (f : α → ℝ) :
    fvariance f = favg (fun a => (f a-favg f)^2) := by
  rw [favg_sq_sub_const, fvariance]; ring

lemma fvariance_nonneg.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (f : α → ℝ) :
    0 ≤ fvariance f := by
  rw [fvariance_centered]
  exact favg_nonneg fun a => sq_nonneg _

lemma favg_sq_le.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (f : α → ℝ) :
    (favg f)^2 ≤ favg (fun a => (f a)^2) := sub_nonneg.mp (fvariance_nonneg f)

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.ShuffleAverages ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma listAvg_eq_favg.{u_1} {α : Type u_1} (l : List α) (f : α → ℝ) :
    listAvg l f = favg (fun i : Fin l.length => f (l.get i)) := by
  simp only [listAvg, favg, Fintype.card_fin]
  congr 1
  have he : List.ofFn (fun i : Fin l.length => f (l.get i)) = l.map f := by
    change List.ofFn (f ∘ l.get) = l.map f
    rw [← List.map_ofFn, List.ofFn_get]
  rw [← he]
  exact List.sum_ofFn

lemma listAvg_const.{u_1} {α : Type u_1} {l : List α} (hl : l ≠ []) (c : ℝ) :
    listAvg l (fun _ => c) = c := by
  rw [listAvg_eq_favg]
  have : Nonempty (Fin l.length) := Fin.pos_iff_nonempty.mp (List.length_pos_iff.mpr hl)
  exact favg_const c

lemma listAvg_congr.{u_1} {α : Type u_1} {l : List α} {f g : α → ℝ}
    (h : ∀ a ∈ l, f a = g a) : listAvg l f = listAvg l g := by
  unfold listAvg
  rw [List.map_congr_left h]

lemma listAvg_perm.{u_1} {α : Type u_1} {l r : List α} (h : l.Perm r) (f : α → ℝ) :
    listAvg l f = listAvg r f := by
  unfold listAvg
  rw [h.length_eq, (h.map f).sum_eq]

lemma listAvg_mono.{u_1} {α : Type u_1} {l : List α} {f g : α → ℝ}
    (h : ∀ a ∈ l, f a ≤ g a) : listAvg l f ≤ listAvg l g := by
  rw [listAvg_eq_favg, listAvg_eq_favg]
  exact favg_mono fun i => h _ (List.get_mem _ _)

lemma listAvg_nonneg.{u_1} {α : Type u_1} {l : List α} {f : α → ℝ}
    (h : ∀ a ∈ l, 0 ≤ f a) : 0 ≤ listAvg l f := by
  rw [listAvg_eq_favg]
  exact favg_nonneg fun i => h _ (List.get_mem _ _)

lemma listAvg_add.{u_1} {α : Type u_1} (l : List α) (f g : α → ℝ) :
    listAvg l (fun a => f a+g a) = listAvg l f+listAvg l g := by
  simp only [listAvg_eq_favg, favg_add]

lemma listAvg_sub.{u_1} {α : Type u_1} (l : List α) (f g : α → ℝ) :
    listAvg l (fun a => f a-g a) = listAvg l f-listAvg l g := by
  simp only [listAvg_eq_favg, favg_sub]

lemma listAvg_mul.{u_1} {α : Type u_1} (l : List α) (c : ℝ) (f : α → ℝ) :
    listAvg l (fun a => c*f a) = c*listAvg l f := by
  simp only [listAvg_eq_favg, favg_mul]

lemma listAvg_sq_le.{u_1} {α : Type u_1} {l : List α} (hl : l ≠ []) (f : α → ℝ) :
    (listAvg l f)^2 ≤ listAvg l (fun a => (f a)^2) := by
  simp only [listAvg_eq_favg]
  have : Nonempty (Fin l.length) := Fin.pos_iff_nonempty.mp (List.length_pos_iff.mpr hl)
  exact favg_sq_le _

lemma listAvg_flatMap.{u_1, u_2} {α : Type u_1} {β : Type u_2} (l : List α) (g : α → List β) (f : β → ℝ)
    (d : ℕ) (_hd : 0 < d) (h : ∀ a ∈ l, (g a).length = d) :
    listAvg (l.flatMap g) f = listAvg l (fun a => listAvg (g a) f) := by
  have hlen : (l.flatMap g).length = l.length*d := by
    rw [List.length_flatMap]
    calc
      _ = (l.map (fun _ => d)).sum := by congr 1; exact List.map_congr_left h
      _ = _ := by simp [List.sum_replicate, Nat.mul_comm]
  unfold listAvg
  have hsum (r : List α) : (r.flatMap (fun a => List.map f (g a))).sum =
      (r.map (fun a => (List.map f (g a)).sum)).sum := by
    induction r with
    | nil => simp
    | cons a r ih => simp [ih]
  rw [List.map_flatMap, hsum, hlen, Nat.cast_mul]
  have he : (l.map (fun a => (List.map f (g a)).sum / ((g a).length : ℝ))).sum =
      (l.map (fun a => (List.map f (g a)).sum)).sum / d := by
    calc
      _ = (l.map (fun a => (List.map f (g a)).sum / (d : ℝ))).sum := by
        congr 1
        exact List.map_congr_left (fun a ha => by rw [h a ha])
      _ = _ := by
        have hdiv (r : List α) : (r.map (fun a => (List.map f (g a)).sum / (d : ℝ))).sum =
            (r.map (fun a => (List.map f (g a)).sum)).sum / d := by
          induction r with
          | nil => simp
          | cons a r ih => simp [ih, add_div]
        exact hdiv l
  rw [he]
  ring

lemma permutations'_length.{u_1} {α : Type u_1} (l : List α) : l.permutations'.length = l.length.factorial := by
  rw [← (List.permutations_perm_permutations' l).length_eq, List.length_permutations]

lemma permutations'_ne_nil.{u_1} {α : Type u_1} (l : List α) : l.permutations' ≠ [] := by
  have hh : 0 < l.permutations'.length := by rw [permutations'_length]; exact Nat.factorial_pos _
  exact List.length_pos_iff.mp hh

lemma shuffleAvg_const.{u_1} {α : Type u_1} (l : List α) (c : ℝ) : shuffleAvg l (fun _ => c) = c :=
  listAvg_const (permutations'_ne_nil l) c

lemma shuffleAvg_perm.{u_1} {α : Type u_1} {l r : List α} (h : l.Perm r) (f : List α → ℝ) :
    shuffleAvg l f = shuffleAvg r f := listAvg_perm h.permutations' f

lemma shuffleAvg_congr.{u_1} {α : Type u_1} {l : List α} {f g : List α → ℝ}
    (h : ∀ r, r.Perm l → f r = g r) : shuffleAvg l f = shuffleAvg l g :=
  listAvg_congr fun _ hr => h _ (List.mem_permutations'.mp hr)

lemma shuffleAvg_mono.{u_1} {α : Type u_1} {l : List α} {f g : List α → ℝ}
    (h : ∀ r, r.Perm l → f r ≤ g r) : shuffleAvg l f ≤ shuffleAvg l g :=
  listAvg_mono fun _ hr => h _ (List.mem_permutations'.mp hr)

lemma shuffleAvg_nonneg.{u_1} {α : Type u_1} {l : List α} {f : List α → ℝ}
    (h : ∀ r, r.Perm l → 0 ≤ f r) : 0 ≤ shuffleAvg l f :=
  listAvg_nonneg fun _ hr => h _ (List.mem_permutations'.mp hr)

lemma shuffleAvg_add.{u_1} {α : Type u_1} (l : List α) (f g : List α → ℝ) :
    shuffleAvg l (fun r => f r+g r) = shuffleAvg l f+shuffleAvg l g := listAvg_add _ _ _
lemma shuffleAvg_sub.{u_1} {α : Type u_1} (l : List α) (f g : List α → ℝ) :
    shuffleAvg l (fun r => f r-g r) = shuffleAvg l f-shuffleAvg l g := listAvg_sub _ _ _
lemma shuffleAvg_mul.{u_1} {α : Type u_1} (l : List α) (c : ℝ) (f : List α → ℝ) :
    shuffleAvg l (fun r => c*f r) = c*shuffleAvg l f := listAvg_mul _ _ _

lemma shuffleAvg_sq_le.{u_1} {α : Type u_1} (l : List α) (f : List α → ℝ) :
    (shuffleAvg l f)^2 ≤ shuffleAvg l (fun r => (f r)^2) :=
  listAvg_sq_le (permutations'_ne_nil l) f

lemma listAvg_permutationsAux.{u_1} {α : Type u_1} (l : List α) (c : α) (f : List α → ℝ) :
    listAvg (List.permutations'Aux c l) f =
      favg (fun i : Fin (l.length+1) => f (l.insertIdx i c)) := by
  rw [listAvg_eq_favg]
  have he := favg_equiv (finCongr (List.length_permutations'Aux l c)).symm
    (fun i : Fin (List.permutations'Aux c l).length => f ((List.permutations'Aux c l).get i))
  rw [← he]
  congr 1
  funext i
  change f ((List.permutations'Aux c l).get ⟨i.val,_⟩) = _
  rw [List.get_permutations'Aux]

lemma shuffleAvg_cons.{u_1} {α : Type u_1} (l : List α) (c : α) (f : List α → ℝ) :
    shuffleAvg (c::l) f =
      shuffleAvg l (fun r => favg (fun i : Fin (l.length+1) => f (r.insertIdx i c))) := by
  unfold shuffleAvg
  rw [List.permutations', listAvg_flatMap _ _ _ (l.length+1) (by omega)
    (fun r hr => by rw [List.length_permutations'Aux, (List.mem_permutations'.mp hr).length_eq])]
  apply listAvg_congr
  intro r hr
  rw [listAvg_permutationsAux]
  have he := (List.mem_permutations'.mp hr).length_eq
  have hh := favg_equiv (finCongr (congrArg (fun x => x+1) he))
    (fun i : Fin (l.length+1) => f (r.insertIdx i c))
  exact hh

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.InsertionVariance ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma inserts_perm.{u_1} {α : Type u_1} {b l r : List α} (h : Inserts b l r) : r.Perm (b++l) := by
  induction h with
  | nil => simp
  | cons c h i hi ih => exact (List.perm_insertIdx c _ hi).trans (ih.cons c)

lemma insertAvg_congr.{u_1} {α : Type u_1} (b l : List α) {f g : List α → ℝ}
    (h : ∀ r, Inserts b l r → f r = g r) : insertAvg b l f = insertAvg b l g := by
  induction b generalizing f g with
  | nil => exact h l (Inserts.nil l)
  | cons c b ih =>
    apply ih
    intro r hr
    unfold insertKernel
    congr 1
    funext i
    exact h _ (Inserts.cons c hr i (by omega))

lemma insertAvg_mono.{u_1} {α : Type u_1} (b l : List α) {f g : List α → ℝ}
    (h : ∀ r, Inserts b l r → f r ≤ g r) : insertAvg b l f ≤ insertAvg b l g := by
  induction b generalizing f g with
  | nil => exact h l (Inserts.nil l)
  | cons c b ih =>
    apply ih
    intro r hr
    exact favg_mono (fun i => h _ (Inserts.cons c hr i (by omega)))

lemma insertAvg_const.{u_1} {α : Type u_1} (b l : List α) (a : ℝ) :
    insertAvg b l (fun _ => a) = a := by
  induction b with
  | nil => rfl
  | cons c b ih =>
    change insertAvg b l (fun r => favg (fun _ : Fin (r.length+1) => a)) = a
    simp only [favg_const,ih]

lemma insertAvg_sq_le.{u_1} {α : Type u_1} (b l : List α) (f : List α → ℝ) :
    (insertAvg b l f)^2 ≤ insertAvg b l (fun r => (f r)^2) := by
  induction b generalizing f with
  | nil => exact le_refl _
  | cons c b ih =>
    apply (ih (insertKernel c f)).trans
    apply insertAvg_mono
    intro r _
    exact favg_sq_le _

lemma shuffleAvg_cons_kernel.{u_1} {α : Type u_1} (l : List α) (c : α) (f : List α → ℝ) :
    shuffleAvg (c::l) f = shuffleAvg l (insertKernel c f) := by
  rw [shuffleAvg_cons]
  apply shuffleAvg_congr
  intro r hr
  unfold insertKernel
  exact favg_equiv (finCongr (congrArg (fun x => x+1) hr.length_eq).symm)
    (fun i : Fin (r.length+1) => f (r.insertIdx i c))

lemma shuffleAvg_append.{u_1} {α : Type u_1} (b l : List α) (f : List α → ℝ) :
    shuffleAvg (b++l) f = shuffleAvg l (fun r => insertAvg b r f) := by
  induction b generalizing f with
  | nil => rfl
  | cons c b ih =>
    rw [List.cons_append, shuffleAvg_cons_kernel, ih]
    rfl

lemma insertVar_nonneg.{u_1} {α : Type u_1} (b l : List α) (f : List α → ℝ) : 0 ≤ insertVar b l f :=
  sub_nonneg.mpr (insertAvg_sq_le b l f)

lemma private_perm {n k : ℕ} {c : Clause n k} {l r : List (Clause n k)}
    (h : l.Perm r) (hc : Private c l) : Private c r := by
  obtain ⟨v,hv⟩ := hc
  exact ⟨v,fun d hd => hv d (h.mem_iff.mpr hd)⟩

lemma private_harmless {n k : ℕ} {c : Clause n k} {l : List (Clause n k)}
    (hc : Private c l) : Harmless c l := by
  obtain ⟨v,hv⟩ := hc
  exact harmless_private c l v hv

lemma inserts_stop_bounds {n k : ℕ} {b l r : List (Clause n k)} (hb : Bystanders b l)
    (h : Inserts b l r) : listStop l ≤ listStop r ∧ listStop r ≤ listStop l+b.length := by
  induction h with
  | nil => simp
  | @cons c b l r h i hi ih =>
    have hh : Harmless c r := private_harmless (private_perm (inserts_perm h).symm hb.1)
    rw [listStop_insert c r hh i hi]
    have ht := ih hb.2
    simp only [List.length_cons]
    split_ifs <;> omega

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.BystanderVariance ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma bystanders_perm_right {n k : ℕ} {b l r : List (Clause n k)}
    (hb : Bystanders b l) (h : l.Perm r) : Bystanders b r := by
  induction b with
  | nil => trivial
  | cons c b ih =>
    exact ⟨private_perm (h.append_left b) hb.1,ih hb.2⟩

lemma shuffleVar_perm.{u_1} {α : Type u_1} {l r : List α} (h : l.Perm r) (f : List α → ℝ) :
    shuffleVar l f = shuffleVar r f := by
  unfold shuffleVar
  rw [shuffleAvg_perm h,shuffleAvg_perm h]

lemma shuffleVar_append_lower.{u_1} {α : Type u_1} (b l : List α) (f : List α → ℝ) :
    shuffleAvg l (fun r => insertVar b r f) ≤ shuffleVar (b++l) f := by
  simp only [shuffleVar,shuffleAvg_append,insertVar]
  rw [shuffleAvg_sub]
  have hh := shuffleAvg_sq_le l (fun r => insertAvg b r f)
  linarith

lemma favg_shuffleVar_lower.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (M : ℕ) (f : List α → ℝ) :
    favg (fun w : Fin M → α => shuffleVar (List.ofFn w) f) ≤
      fvariance (fun w : Fin M → α => f (List.ofFn w)) := by
  simp only [shuffleVar,fvariance,favg_sub,favg_shuffle]
  have hh := favg_sq_le (fun w : Fin M → α => shuffleAvg (List.ofFn w) f)
  rw [favg_shuffle] at hh
  linarith

lemma outsideWindow_nonneg {n k : ℕ} (Q V : ℕ) (r : List (Clause n k)) :
    0 ≤ outsideWindow Q V r := by unfold outsideWindow; positivity

lemma bystander_variance {n k : ℕ} {b l : List (Clause n k)} (hb : Bystanders b l)
    (Q V M : ℕ) (hlen : b.length+l.length = M) (hbQ : b.length ≤ Q)
    (hQV : Q+V ≤ M+1) :
    ((Q:ℝ)*((M:ℝ)+1-Q-V)/((M:ℝ)+1)^2)*b.length ≤
      shuffleVar (b++l) (fun r => (listStop r:ℝ)) +
      ((Q:ℝ)*((M:ℝ)+1-Q-V)/((M:ℝ)+1)^2)*b.length*
        shuffleAvg (b++l) (outsideWindow Q V) := by
  let p : ℝ := (Q:ℝ)*((M:ℝ)+1-Q-V)/((M:ℝ)+1)^2
  have hC : 0 ≤ (M:ℝ)+1-Q-V := by
    have hh : (Q:ℝ)+V ≤ M+1 := by exact_mod_cast hQV
    linarith
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hbl : (b.length:ℝ)+(l.length:ℝ) = M := by exact_mod_cast hlen
  have hq : (b.length:ℝ) ≤ Q := by exact_mod_cast hbQ
  have hlocal (r : List (Clause n k)) (hr : r.Perm l) :
      p*b.length ≤ insertVar b r (fun s => (listStop s:ℝ)) +
        p*b.length*insertAvg b r (outsideWindow Q V) := by
    have hb' : Bystanders b r := bystanders_perm_right hb hr.symm
    have hrlen : (r.length:ℝ) = l.length := by exact_mod_cast hr.length_eq
    by_cases ht : Q ≤ listStop r ∧ listStop r ≤ V
    · have hv := insertVar_stop_lower hb' hC (by positivity : (0:ℝ) < (M:ℝ)+1)
        (by exact_mod_cast ht.1 : (Q:ℝ) ≤ listStop r)
        (show (M:ℝ)+1-Q-V ≤ (r.length:ℝ)+1-listStop r by
          have htv : (listStop r:ℝ) ≤ V := by exact_mod_cast ht.2
          linarith)
        (show (b.length:ℝ)+r.length+1 ≤ (M:ℝ)+1 by linarith)
      have hn : 0 ≤ insertAvg b r (outsideWindow Q V) := by
        rw [←insertAvg_const b r 0]
        exact insertAvg_mono b r (fun s _ => outsideWindow_nonneg Q V s)
      have hh : 0 ≤ p*b.length*insertAvg b r (outsideWindow Q V) := by positivity
      dsimp [p] at hv ⊢
      nlinarith
    · have hout : insertAvg b r (outsideWindow Q V) = 1 := by
        rw [←insertAvg_const b r 1]
        apply insertAvg_congr
        intro s hs
        have hst := inserts_stop_bounds hb' hs
        have hh : listStop s < 2*Q ∨ V < listStop s := by omega
        simp [outsideWindow,hh]
      rw [hout,mul_one]
      linarith [insertVar_nonneg b r (fun s => (listStop s:ℝ))]
  have hh := shuffleAvg_mono (l := l) hlocal
  rw [shuffleAvg_const,shuffleAvg_add,shuffleAvg_mul] at hh
  have hv := shuffleVar_append_lower b l (fun r => (listStop r:ℝ))
  rw [shuffleAvg_append]
  change p*b.length ≤ _ + p*b.length*_
  linarith

lemma bystanders_map {n k M : ℕ} (hk : 1 ≤ k) (w : Fin M → Clause n k)
    {is js : List (Fin M)} (hnd : is.Nodup)
    (hi : ∀ i ∈ is, isolated w i) (hd : ∀ i ∈ is, i ∉ js) :
    Bystanders (is.map w) (js.map w) := by
  induction is with
  | nil => trivial
  | cons i is ih =>
    have hnd' := List.nodup_cons.mp hnd
    have hic := hi i (by simp)
    have hid := hd i (by simp)
    constructor
    · have hn : (w i).1.1.Nonempty := Finset.card_pos.mp (by rw [(w i).1.2]; omega)
      obtain ⟨v,hv⟩ := hn
      refine ⟨⟨v,hv⟩,?_⟩
      intro d hd'
      rcases List.mem_append.mp hd' with hd' | hd'
      · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hd'
        have hji : j ≠ i := by intro he; subst j; exact hnd'.1 hj
        exact Finset.disjoint_left.mp (hic j hji) hv
      · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hd'
        have hji : j ≠ i := by intro he; subst j; exact hid hj
        exact Finset.disjoint_left.mp (hic j hji) hv
    · exact ih hnd'.2 (fun j hj => hi j (by simp [hj])) (fun j hj => hd j (by simp [hj]))

lemma chosenIsolates_subset {n k M : ℕ} (Q : ℕ) (w : Fin M → Clause n k) :
    chosenIsolates Q w ⊆ isolateSet w :=
  (Classical.choose_spec (Finset.exists_subset_card_eq
    (s := isolateSet w) (min_le_right Q (isolateSet w).card))).1

lemma chosenIsolates_card {n k M : ℕ} (Q : ℕ) (w : Fin M → Clause n k) :
    (chosenIsolates Q w).card = min Q (isolateSet w).card :=
  (Classical.choose_spec (Finset.exists_subset_card_eq
    (s := isolateSet w) (min_le_right Q (isolateSet w).card))).2

lemma selected_bystanders {n k M : ℕ} (hk : 1 ≤ k) (Q : ℕ) (w : Fin M → Clause n k) :
    Bystanders (bystanderList Q w) (activeList Q w) := by
  apply bystanders_map hk w (Finset.nodup_toList _)
  · intro i hi
    exact (Finset.mem_filter.mp (chosenIsolates_subset Q w (Finset.mem_toList.mp hi))).2
  · intro i hi
    simp only [Finset.mem_toList,Finset.mem_sdiff,Finset.mem_univ,true_and,not_not]
    exact Finset.mem_toList.mp hi

lemma bystanderList_length {n k M : ℕ} (Q : ℕ) (w : Fin M → Clause n k) :
    (bystanderList Q w).length = min Q (isolateSet w).card := by
  simp only [bystanderList,List.length_map,Finset.length_toList,chosenIsolates_card]

lemma selected_lengths {n k M : ℕ} (Q : ℕ) (w : Fin M → Clause n k) :
    (bystanderList Q w).length+(activeList Q w).length = M := by
  have := (selected_perm Q w).length_eq
  simpa only [List.length_append,List.length_ofFn] using this

lemma selected_variance {n k M : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (Q V : ℕ) (hQV : Q+V ≤ M+1) :
    ((Q:ℝ)*((M:ℝ)+1-Q-V)/((M:ℝ)+1)^2)*
      favg (fun w : Fin M → Clause n k => (min Q (isolateSet w).card : ℝ)) ≤
    fvariance (fun w : Fin M → Clause n k => (listStop (List.ofFn w):ℝ)) +
      ((Q:ℝ)*((M:ℝ)+1-Q-V)/((M:ℝ)+1)^2)*Q*
        favg (fun w : Fin M → Clause n k => outsideWindow Q V (List.ofFn w)) := by
  let := clause_nonempty n k hkn
  let p : ℝ := (Q:ℝ)*((M:ℝ)+1-Q-V)/((M:ℝ)+1)^2
  have hC : 0 ≤ (M:ℝ)+1-Q-V := by
    have hh : (Q:ℝ)+V ≤ M+1 := by exact_mod_cast hQV
    linarith
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hh (w : Fin M → Clause n k) :
      p*(min Q (isolateSet w).card:ℝ) ≤
      shuffleVar (List.ofFn w) (fun r => (listStop r:ℝ)) + p*Q*
        shuffleAvg (List.ofFn w) (outsideWindow Q V) := by
    have ht := bystander_variance (selected_bystanders hk Q w) Q V M (selected_lengths Q w)
      (by rw [bystanderList_length]; exact min_le_left _ _) hQV
    rw [shuffleVar_perm (selected_perm Q w),shuffleAvg_perm (selected_perm Q w),bystanderList_length] at ht
    have hmin : (min Q (isolateSet w).card:ℝ) ≤ Q := by exact_mod_cast min_le_left Q (isolateSet w).card
    have hnon := shuffleAvg_nonneg (l := List.ofFn w) (fun r _ => outsideWindow_nonneg Q V r)
    have he := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmin hp) hnon
    simp only [Nat.cast_min] at ht
    apply ht.trans
    dsimp only [p] at he
    linarith
  have hh' := favg_mono hh
  simp only [favg_mul,favg_add,favg_shuffle] at hh'
  have hv := favg_shuffleVar_lower M (fun r : List (Clause n k) => (listStop r:ℝ))
  change p*_ ≤ _ + p*Q*_
  linarith

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.selected_variance := @_root_.OAI.RandomKSAT.selected_variance
