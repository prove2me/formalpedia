-- Prove2me | solution 1 for OAI.RandomKSAT.forcedPrefix_testKills
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T19:18:42.640152+00:00
-- url     : https://prove2.me/submissions/f7e87f3a-90d9-4bdb-a0f2-a25cc81eb203

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/PairEvolution.lean:L289-L322
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.forcedPrefix_testKills. The node keeps its source
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

-- ---- from OAI.Probability.SATVariance.FiberRefresh ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma trueRoot_spec {k : ℕ} (t : RootType k) (a : Assignment k) (h : RootSatisfies t a) :
    t (trueRoot t a h) = some (a (trueRoot t a h)) := h.choose_spec

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.PairEvolution ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

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

lemma flipRoot_ne {k : ℕ} (a : Assignment k) (j : Fin k) : flipRoot a j ≠ a := by
  intro h
  have hh := congrFun h j
  simp only [flipRoot, Function.update_self] at hh
  cases ha : a j <;> simp_all

lemma rootSatisfies_flip {k : ℕ} (t : RootType k) (a : Assignment k) (j : Fin k)
    (h : RootSatisfies t a) (hn : ¬ UniqueTrue t a j) : RootSatisfies t (flipRoot a j) := by
  obtain ⟨l,hl⟩ := h
  by_cases hlj : l = j
  · subst l
    have he : ∃ l, l ≠ j ∧ t l = some (a l) := by
      by_contra hh
      apply hn
      refine ⟨hl, ?_⟩
      intro l hlj hl
      exact hh ⟨l,hlj,hl⟩
    obtain ⟨l,hlj,hl⟩ := he
    exact ⟨l, by simpa [flipRoot, Function.update_of_ne hlj] using hl⟩
  · exact ⟨l, by simpa [flipRoot, Function.update_of_ne hlj] using hl⟩

lemma rootSize_one_unique {k : ℕ} (t : RootType k) (h : rootSize t = 1)
    {i j : Fin k} (hi : (t i).isSome) (hj : (t j).isSome) : i = j := by
  have hcard : (rootSupport t).card ≤ 1 := h.le
  exact Finset.card_le_one.mp hcard i (by simpa [rootSupport] using hi)
    j (by simpa [rootSupport] using hj)

lemma trueRoot_eq {k : ℕ} (t : RootType k) (a : Assignment k)
    (h : RootSatisfies t a) (hs : rootSize t = 1) {j : Fin k} (hj : t j = some (a j)) :
    trueRoot t a h = j := by
  apply rootSize_one_unique t hs
  · simp [trueRoot_spec t a h]
  · simp [hj]

lemma refreshPart_test {u k : ℕ} (a : Assignment k) (p : RootData u k)
    (j : Fin k) (h : TestAt a p j) (z : RefreshNoise u k) (b : Assignment u) :
    Satisfies (refreshPart p.1 a p.2 z) b ↔ Satisfies (z.2 j) b := by
  have ht : RootSatisfies p.1 a := ⟨j,h.2⟩
  have hz : rootSize p.1 ≠ 0 := by rw [h.1]; omega
  have hh : rootSize p.1 = 1 ∧ RootSatisfies p.1 a := ⟨h.1,ht⟩
  simp only [refreshPart, dite_eq_right hz, dite_eq_left hh, satisfies_cast]
  rw [trueRoot_eq _ _ _ h.1 h.2]

lemma forcedPrefix_testKills {u k M : ℕ} (a : Assignment k) (env : Fin M → RootData u k)
    (o : Fin M → Clause u k) (ys : Fin k → Fin M → Clause u (k-1)) (m : ℕ)
    (hforced : ∀ x ∈ pairPrefix Finset.univ
      (fun i => refreshData a (env i) (o i, fun j => ys j i)) m, x.1 = a)
    (j : Fin k) (hj : Available a env j) :
    ¬ ∃ b ∈ fibrePrefix a env o m,
      ∀ i : Fin M, i.val < m → TestAt a (env i) j → Satisfies (ys j i) b := by
  rintro ⟨b,hb,hparts⟩
  have hfb : (a,b) ∈ pairPrefix Finset.univ
      (fun i => refreshData a (env i) (o i, fun j => ys j i)) m := by
    have hh := congrArg (fun S => b ∈ S) (fibre_pairPrefix_refresh a env o ys m)
    simpa only [fibre, Finset.mem_filter, Finset.mem_univ, true_and] using hh.mpr hb
  have hflip : (flipRoot a j,b) ∈ pairPrefix Finset.univ
      (fun i => refreshData a (env i) (o i, fun j => ys j i)) m := by
    simp only [pairPrefix, Finset.mem_filter, Finset.mem_univ, true_and] at hfb ⊢
    intro i hi
    have hh := hfb i hi
    change RootSatisfies (env i).1 a ∨ Satisfies (refreshPart (env i).1 a (env i).2
      (o i, fun j => ys j i)) b at hh
    change RootSatisfies (env i).1 (flipRoot a j) ∨ Satisfies (refreshPart (env i).1 a (env i).2
      (o i, fun j => ys j i)) b
    rcases hh with hr | hp
    · by_cases ht : UniqueTrue (env i).1 a j
      · have hs : rootSize (env i).1 = 1 := by
          have hp : 0 < rootSize (env i).1 := by
            by_contra h
            exact rootSatisfies_zero _ (by omega) a hr
          have hlt : rootSize (env i).1 < 2 := Nat.lt_of_not_ge (fun h => hj i h ht)
          omega
        exact Or.inr ((refreshPart_test a (env i) j ⟨hs,ht.1⟩ _ b).mpr
          (hparts i hi ⟨hs,ht.1⟩))
      · exact Or.inl (rootSatisfies_flip _ a j hr ht)
    · exact Or.inr hp
  exact flipRoot_ne a j (hforced _ hflip)

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.forcedPrefix_testKills := @_root_.OAI.RandomKSAT.forcedPrefix_testKills
