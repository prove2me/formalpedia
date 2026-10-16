-- Prove2me | solution 1 for OAI.RandomKSAT.favg_shuffle
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T19:46:05.776665+00:00
-- url     : https://prove2.me/submissions/779ddf16-d7e5-433c-a5b3-6e49c7c853d7

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/ShuffleAverages.lean:L180-L218
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.favg_shuffle. The node keeps its source
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

-- ---- from OAI.Probability.SATVariance.MarkovReplacement ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma favg_const.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (c : ℝ) :
    favg (fun _ : α => c) = c := by
  simp [favg, Fintype.card_ne_zero]

lemma favg_equiv.{u_1, u_2} {α : Type u_1} {β : Type u_2} [Fintype α] [Fintype β] (e : α ≃ β) (f : β → ℝ) :
    favg (fun a => f (e a)) = favg f := by
  rw [favg, favg, e.sum_comp f, Fintype.card_congr e]

lemma favg_comm.{u_1, u_2} {α : Type u_1} {β : Type u_2} [Fintype α] [Fintype β] (f : α → β → ℝ) :
    favg (fun a => favg (f a)) = favg (fun b => favg (fun a => f a b)) := by
  simp only [favg, ← Finset.sum_div]
  rw [Finset.sum_comm]
  ring

lemma favg_prod.{u_1, u_2} {α : Type u_1} {β : Type u_2} [Fintype α] [Fintype β] (f : α × β → ℝ) :
    favg f = favg (fun a => favg fun b => f (a,b)) := by
  simp only [favg, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div]
  ring

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

lemma favg_cons.{u_1} {α : Type u_1} [Fintype α] {m : ℕ} (f : (Fin (m+1) → α) → ℝ) :
    favg f = favg (fun t : Fin m → α => favg (fun a : α => f (Fin.cons a t))) := by
  rw [← favg_equiv (Fin.consEquiv (fun _ : Fin (m+1) => α)) f, favg_prod, favg_comm]
  rfl

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

lemma listAvg_congr.{u_1} {α : Type u_1} {l : List α} {f g : α → ℝ}
    (h : ∀ a ∈ l, f a = g a) : listAvg l f = listAvg l g := by
  unfold listAvg
  rw [List.map_congr_left h]

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

lemma shuffleAvg_congr.{u_1} {α : Type u_1} {l : List α} {f g : List α → ℝ}
    (h : ∀ r, r.Perm l → f r = g r) : shuffleAvg l f = shuffleAvg l g :=
  listAvg_congr fun _ hr => h _ (List.mem_permutations'.mp hr)

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

lemma ofFn_insertNth.{u_1} {α : Type u_1} {m : ℕ} (w : Fin m → α) (c : α) (i : Fin (m+1)) :
    List.ofFn (i.insertNth c w) = (List.ofFn w).insertIdx i.val c := by
  induction m with
  | zero =>
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    simp [Fin.insertNth_zero']
  | succ m ih =>
    obtain ⟨⟨a,w⟩,rfl⟩ := (Fin.consEquiv (fun _ : Fin (m+1) => α)).surjective w
    change List.ofFn (i.insertNth c (Fin.cons a w)) = (List.ofFn (Fin.cons a w)).insertIdx i.val c
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Fin.insertNth_zero']
    · rw [Fin.insertNth_succ_cons, List.ofFn_cons, List.ofFn_cons, Fin.val_succ,
        List.insertIdx_succ_cons, ih]

lemma favg_shuffle.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (m : ℕ) (f : List α → ℝ) :
    favg (fun w : Fin m → α => shuffleAvg (List.ofFn w) f) =
      favg (fun w : Fin m → α => f (List.ofFn w)) := by
  induction m generalizing f with
  | zero =>
    have he : ∀ w : Fin 0 → α, List.ofFn w = [] := fun _ => rfl
    simp only [he, shuffleAvg, List.permutations', listAvg]
    simp [favg_const]
  | succ m ih =>
    calc
      _ = favg (fun c : α => favg (fun w : Fin m → α =>
          shuffleAvg (c::List.ofFn w) f)) := by
        rw [favg_cons, favg_comm]
        simp only [List.ofFn_cons]
      _ = favg (fun c : α => favg (fun w : Fin m → α =>
          favg (fun i : Fin (m+1) => f ((List.ofFn w).insertIdx i c)))) := by
        congr 1
        funext c
        have hc (w : Fin m → α) : shuffleAvg (c :: List.ofFn w) f =
            shuffleAvg (List.ofFn w) (fun r => favg (fun i : Fin (m+1) => f (r.insertIdx i c))) := by
          rw [shuffleAvg_cons]
          apply shuffleAvg_congr
          intro r _
          exact favg_equiv (finCongr (congrArg (fun x => x+1) (List.length_ofFn (f := w))))
            (fun i : Fin (m+1) => f (r.insertIdx i c))
        simp only [hc]
        exact ih (fun r => favg (fun i : Fin (m+1) => f (r.insertIdx i c)))
      _ = favg (fun i : Fin (m+1) => favg (fun c : α => favg (fun w : Fin m → α =>
          f ((List.ofFn w).insertIdx i c)))) := by
        simp_rw [favg_comm (fun w : Fin m → α => fun i : Fin (m+1) =>
          f ((List.ofFn w).insertIdx i _))]
        exact favg_comm _
      _ = _ := by
        simp_rw [← ofFn_insertNth]
        have he (i : Fin (m+1)) :
            favg (fun c : α => favg (fun w : Fin m → α => f (List.ofFn (i.insertNth c w)))) =
            favg (fun v : Fin (m+1) → α => f (List.ofFn v)) :=
          (favg_insertNth i (fun v => f (List.ofFn v))).symm
        simp only [he, favg_const]

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.favg_shuffle := @_root_.OAI.RandomKSAT.favg_shuffle
