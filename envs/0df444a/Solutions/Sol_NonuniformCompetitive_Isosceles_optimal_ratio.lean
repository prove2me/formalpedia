-- Prove2me | solution 1 for NonuniformCompetitive.Isosceles.optimal_ratio
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-07T02:16:42.832634+00:00
-- url     : https://prove2.me/submissions/4b119d91-80c1-4437-b219-46d0a0af9bee

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_randomized
import Definitions.Def_NonuniformCompetitive_Isosceles_isoscelesRatio

set_option autoImplicit false

/- Complete checked body: TriangleBasics -/
section

namespace NonuniformCompetitive.IsoscelesProof

open scoped BigOperators

abbrev Vtx := Fin 3

def triDist (d : ℕ) (x y : Vtx) : ℝ :=
  if x = y then 0 else if x = 2 ∨ y = 2 then d else 1

def val {M : Type*} (a b c : M) (x : Vtx) : M := ![a,b,c] x

def nearOther (x : Vtx) : Vtx := if x = 0 then 1 else 0

def pairConf (h : Vtx) : Fin 2 → Vtx :=
  if h = 0 then ![1,2] else if h = 1 then ![0,2] else ![0,1]

def triMove (d : ℕ) (C D : Fin 2 → Vtx) : ℝ :=
  ∑ i, triDist d (C i) (D i)

def swapConf (C : Fin 2 → Vtx) : Fin 2 → Vtx := ![C 1,C 0]

def pairMatch (d : ℕ) (h : Vtx) (C : Fin 2 → Vtx) : ℝ :=
  min (triMove d (pairConf h) C) (triMove d (swapConf (pairConf h)) C)

@[simp] theorem triDist_self (d : ℕ) (x : Vtx) : triDist d x x = 0 := by
  simp [triDist]

theorem triDist_symm (d : ℕ) (x y : Vtx) : triDist d x y = triDist d y x := by
  simp [triDist, eq_comm, or_comm]

theorem triDist_nonneg (d : ℕ) (x y : Vtx) : 0 ≤ triDist d x y := by
  unfold triDist
  split_ifs <;> positivity

theorem triDist_le (d : ℕ) (hd : 1 ≤ d) (x y : Vtx) : triDist d x y ≤ d := by
  unfold triDist
  split_ifs <;> first | exact le_rfl | exact Nat.cast_nonneg d | exact_mod_cast hd

theorem triDist_triangle (d : ℕ) (hd : 1 ≤ d) (x y z : Vtx) :
    triDist d x z ≤ triDist d x y + triDist d y z := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  fin_cases x <;> fin_cases y <;> fin_cases z <;> simp [triDist] <;> linarith

theorem nearOther_ne_far (x : Vtx) : nearOther x ≠ 2 := by
  unfold nearOther
  split_ifs <;> decide

theorem nearOther_other (x : Vtx) (hx : x ≠ 2) : nearOther (nearOther x) = x := by
  fin_cases x <;> norm_num [nearOther, Fin.ext_iff] at *

theorem pairConf_mem (h r : Vtx) : (∃ i, pairConf h i = r) ↔ r ≠ h := by
  fin_cases h <;> fin_cases r <;> simp [pairConf, Fin.exists_fin_two]

theorem triMove_nonneg (d : ℕ) (C D : Fin 2 → Vtx) : 0 ≤ triMove d C D :=
  Finset.sum_nonneg fun i _ => triDist_nonneg d (C i) (D i)

theorem triMove_triangle (d : ℕ) (hd : 1 ≤ d) (C D E : Fin 2 → Vtx) :
    triMove d C E ≤ triMove d C D + triMove d D E := by
  unfold triMove
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => triDist_triangle d hd (C i) (D i) (E i)

theorem pairMatch_nonneg (d : ℕ) (h : Vtx) (C : Fin 2 → Vtx) :
    0 ≤ pairMatch d h C :=
  le_min (triMove_nonneg _ _ _) (triMove_nonneg _ _ _)

theorem pairMatch_move (d : ℕ) (hd : 1 ≤ d) (h : Vtx) (C D : Fin 2 → Vtx) :
    pairMatch d h D ≤ pairMatch d h C + triMove d C D := by
  unfold pairMatch
  rcases le_total (triMove d (pairConf h) C) (triMove d (swapConf (pairConf h)) C) with hle | hle
  · rw [min_eq_left hle]
    exact (min_le_left _ _).trans (triMove_triangle d hd _ _ _)
  · rw [min_eq_right hle]
    exact (min_le_right _ _).trans (triMove_triangle d hd _ _ _)

theorem pairMatch_pair (d : ℕ) (hd : 1 ≤ d) (h g : Vtx) :
    pairMatch d h (pairConf g) = triDist d h g := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  fin_cases h <;> fin_cases g <;>
    simp [pairMatch, pairConf, swapConf, triMove, Fin.sum_univ_two, triDist]
  all_goals linarith

theorem val_dist {M : Type*} [MetricSpace M] (d : ℕ) (a b c : M)
    (hab : dist a b = 1) (hac : dist a c = d) (hbc : dist b c = d) (x y : Vtx) :
    dist (val a b c x) (val a b c y) = triDist d x y := by
  fin_cases x <;> fin_cases y <;> simp [val, triDist, hab, hac, hbc, dist_comm]

theorem val_injective {M : Type*} [MetricSpace M] (d : ℕ) (hd : 1 ≤ d)
    (a b c : M) (hab : dist a b = 1) (hac : dist a c = d) (hbc : dist b c = d) :
    Function.Injective (val a b c) := by
  intro x y hxy
  have hz : triDist d x y = 0 := by rw [← val_dist d a b c hab hac hbc, hxy, dist_self]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hd)
  fin_cases x <;> fin_cases y <;> simp [triDist] at *
  all_goals linarith

theorem val_surjective {M : Type*} (a b c : M) (hM : ∀ x : M, x = a ∨ x = b ∨ x = c) :
    Function.Surjective (val a b c) := by
  intro x
  rcases hM x with rfl | rfl | rfl
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩

theorem val_move {M : Type*} [MetricSpace M] (d : ℕ) (a b c : M)
    (hab : dist a b = 1) (hac : dist a c = d) (hbc : dist b c = d)
    (C D : Fin 2 → Vtx) :
    KServer.moveCost (val a b c ∘ C) (val a b c ∘ D) = triMove d C D := by
  apply Finset.sum_congr rfl
  intro i _
  exact val_dist d a b c hab hac hbc _ _

end NonuniformCompetitive.IsoscelesProof
end

/- Complete checked body: TrianglePolicies -/
section

set_option autoImplicit false

namespace NonuniformCompetitive.IsoscelesProof

structure TriPolicy where
  conf : List Vtx → (Fin 2 → Vtx)
  serves : ∀ h r, ∃ i, conf (h++[r]) i = r

noncomputable def triCost (d : ℕ) (A : TriPolicy) (h : List Vtx) : ℝ :=
  ∑ j ∈ Finset.range h.length, triMove d (A.conf (h.take j)) (A.conf (h.take (j+1)))

def TriIsLazy (A : TriPolicy) : Prop :=
  ∀ h r, ((∃ i, A.conf h i = r) → A.conf (h++[r]) = A.conf h) ∧
    ((¬∃ i, A.conf h i = r) → ∃ i, A.conf (h++[r]) = Function.update (A.conf h) i r)

lemma triCost_nonneg (d : ℕ) (A : TriPolicy) (h : List Vtx) : 0 ≤ triCost d A h :=
  Finset.sum_nonneg (fun _ _ => triMove_nonneg _ _ _)

@[simp] lemma triCost_nil (d : ℕ) (A : TriPolicy) : triCost d A [] = 0 := by simp [triCost]

lemma triCost_append_one (d : ℕ) (A : TriPolicy) (h : List Vtx) (r : Vtx) :
    triCost d A (h++[r]) = triCost d A h + triMove d (A.conf h) (A.conf (h++[r])) := by
  unfold triCost
  rw [List.length_append,List.length_singleton,Finset.sum_range_succ]
  have hs : (∑ j ∈ Finset.range h.length,
      triMove d (A.conf ((h++[r]).take j)) (A.conf ((h++[r]).take (j+1)))) =
      ∑ j ∈ Finset.range h.length,
      triMove d (A.conf (h.take j)) (A.conf (h.take (j+1))) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [List.take_append_of_le_length (by simpa using (Finset.mem_range.mp hj).le),
      List.take_append_of_le_length (by simpa using Nat.succ_le_of_lt (Finset.mem_range.mp hj))]
  rw [hs]
  have hlen : h.length+1 = (h++[r]).length := by simp
  rw [hlen,List.take_length]
  simp

def triShift (A : TriPolicy) (h : List Vtx) : TriPolicy where
  conf l := A.conf (h++l)
  serves l r := by simpa only [List.append_assoc] using A.serves (h++l) r

@[simp] lemma triShift_nil (A : TriPolicy) : triShift A [] = A := by
  cases A
  simp [triShift]

lemma triCost_append (d : ℕ) (A : TriPolicy) (h l : List Vtx) :
    triCost d A (h++l) = triCost d A h + triCost d (triShift A h) l := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l r ih =>
    rw [← List.append_assoc,triCost_append_one,ih,triCost_append_one]
    simp only [triShift,add_assoc,List.append_assoc]

lemma triShift_lazy (A : TriPolicy) (hA : TriIsLazy A) (h : List Vtx) : TriIsLazy (triShift A h) := by
  intro l r
  simpa only [triShift,List.append_assoc] using hA (h++l) r

namespace TriPolicy

variable {M : Type*} [MetricSpace M]

def toOriginal (e : Vtx ≃ M) (A : TriPolicy) : KServer.OnlineAlgorithm 2 M where
  conf h := e ∘ A.conf (h.map e.symm)
  serves h r := by
    obtain ⟨i,hi⟩ := A.serves (h.map e.symm) (e.symm r)
    refine ⟨i,?_⟩
    simp only [List.map_append,List.map_singleton,Function.comp_apply]
    rw [hi,e.apply_symm_apply]

def ofOriginal (e : Vtx ≃ M) (A : KServer.OnlineAlgorithm 2 M) : TriPolicy where
  conf h := e.symm ∘ A.conf (h.map e)
  serves h r := by
    obtain ⟨i,hi⟩ := A.serves (h.map e) (e r)
    refine ⟨i,?_⟩
    simp only [List.map_append,List.map_singleton,Function.comp_apply]
    rw [hi,e.symm_apply_apply]

lemma toOriginal_cost (d : ℕ) (e : Vtx ≃ M)
    (he : ∀ x y, dist (e x) (e y) = triDist d x y) (A : TriPolicy) (h : List M) :
    (A.toOriginal e).cost h = triCost d A (h.map e.symm) := by
  unfold KServer.OnlineAlgorithm.cost triCost
  simp only [List.length_map]
  apply Finset.sum_congr rfl
  intro j _hj
  unfold KServer.moveCost triMove
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [toOriginal,Function.comp_apply,List.map_take,he]

lemma ofOriginal_cost (d : ℕ) (e : Vtx ≃ M)
    (he : ∀ x y, dist (e x) (e y) = triDist d x y)
    (A : KServer.OnlineAlgorithm 2 M) (h : List Vtx) :
    triCost d (ofOriginal e A) h = A.cost (h.map e) := by
  unfold KServer.OnlineAlgorithm.cost triCost
  simp only [List.length_map]
  apply Finset.sum_congr rfl
  intro j _hj
  unfold KServer.moveCost triMove
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [ofOriginal,Function.comp_apply,List.map_take,← he,e.apply_symm_apply]

end TriPolicy

end NonuniformCompetitive.IsoscelesProof

end

/- Complete checked body: HoleLifting -/
section

namespace NonuniformCompetitive.IsoscelesProof

open scoped BigOperators

def FitsPair (C : Fin 2 → Vtx) (h : Vtx) : Prop :=
  C = pairConf h ∨ C = swapConf (pairConf h)

def pairChange (C : Fin 2 → Vtx) (h g : Vtx) : Fin 2 → Vtx :=
  if h = g then C else fun i => if C i = g then h else C i

theorem FitsPair.serves {C : Fin 2 → Vtx} {h r : Vtx} (hC : FitsPair C h) :
    (∃ i, C i = r) ↔ r ≠ h := by
  rcases hC with rfl | rfl
  · exact pairConf_mem h r
  · fin_cases h <;> fin_cases r <;> decide

theorem pairChange_fits (C : Fin 2 → Vtx) (h g : Vtx) (hC : FitsPair C h) :
    FitsPair (pairChange C h g) g := by
  rcases hC with rfl | rfl
  all_goals unfold FitsPair; fin_cases h <;> fin_cases g <;> decide

theorem pairChange_cost (d : ℕ) (C : Fin 2 → Vtx) (h g : Vtx) (hC : FitsPair C h) :
    triMove d C (pairChange C h g) = triDist d h g := by
  rcases hC with rfl | rfl
  all_goals fin_cases h <;> fin_cases g <;>
    simp [pairChange,pairConf,swapConf,triMove,Fin.sum_univ_two,triDist]

def liftHolePath (h : ℕ → Vtx) (C₀ : Fin 2 → Vtx) : ℕ → Fin 2 → Vtx
  | 0 => C₀
  | t+1 => pairChange (liftHolePath h C₀ t) (h t) (h (t+1))

theorem liftHolePath_fits (h : ℕ → Vtx) (C₀ : Fin 2 → Vtx) (hC : FitsPair C₀ (h 0)) (t : ℕ) :
    FitsPair (liftHolePath h C₀ t) (h t) := by
  induction t with
  | zero => exact hC
  | succ t ih => exact pairChange_fits _ _ _ ih

theorem liftHolePath_cost (d : ℕ) (h : ℕ → Vtx) (C₀ : Fin 2 → Vtx)
    (hC : FitsPair C₀ (h 0)) (t : ℕ) :
    triMove d (liftHolePath h C₀ t) (liftHolePath h C₀ (t+1)) = triDist d (h t) (h (t+1)) :=
  pairChange_cost d _ _ _ (liftHolePath_fits h C₀ hC t)

def holeTransition (g : List Vtx → Vtx) (s : List Vtx × (Fin 2 → Vtx)) (r : Vtx) :
    List Vtx × (Fin 2 → Vtx) :=
  (s.1++[r],pairChange s.2 (g s.1) (g (s.1++[r])))

def holeRun (g : List Vtx → Vtx) (C₀ : Fin 2 → Vtx) (h : List Vtx) :
    List Vtx × (Fin 2 → Vtx) := h.foldl (holeTransition g) ([],C₀)

@[simp] theorem holeRun_nil (g : List Vtx → Vtx) (C₀ : Fin 2 → Vtx) :
    holeRun g C₀ [] = ([],C₀) := rfl

theorem holeRun_append_one (g : List Vtx → Vtx) (C₀ : Fin 2 → Vtx) (h : List Vtx) (r : Vtx) :
    holeRun g C₀ (h++[r]) = holeTransition g (holeRun g C₀ h) r := by
  simp [holeRun,List.foldl_append]

@[simp] theorem holeRun_prefix (g : List Vtx → Vtx) (C₀ : Fin 2 → Vtx) (h : List Vtx) :
    (holeRun g C₀ h).1 = h := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h r ih => simp [holeRun_append_one,holeTransition,ih]

theorem holeRun_fits (g : List Vtx → Vtx) (C₀ : Fin 2 → Vtx) (hC : FitsPair C₀ (g []))
    (h : List Vtx) : FitsPair (holeRun g C₀ h).2 (g h) := by
  induction h using List.reverseRecOn with
  | nil => exact hC
  | append_singleton h r ih =>
    rw [holeRun_append_one]
    simp only [holeTransition,holeRun_prefix]
    exact pairChange_fits _ _ _ ih

def holePolicy (g : List Vtx → Vtx) (hg : ∀ h r, g (h++[r]) ≠ r)
    (C₀ : Fin 2 → Vtx) (hC : FitsPair C₀ (g [])) : TriPolicy where
  conf h := (holeRun g C₀ h).2
  serves h r := (holeRun_fits g C₀ hC (h++[r])).serves.mpr (Ne.symm (hg h r))

theorem holePolicy_cost (d : ℕ) (g : List Vtx → Vtx) (hg : ∀ h r, g (h++[r]) ≠ r)
    (C₀ : Fin 2 → Vtx) (hC : FitsPair C₀ (g [])) (h : List Vtx) :
    triCost d (holePolicy g hg C₀ hC) h =
      ∑ j ∈ Finset.range h.length, triDist d (g (h.take j)) (g (h.take (j+1))) := by
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j < h.length := Finset.mem_range.mp hj
  change triMove d (holeRun g C₀ (h.take j)).2 (holeRun g C₀ (h.take (j+1))).2 = _
  rw [List.take_succ_eq_append_getElem hj',holeRun_append_one]
  simp only [holeTransition,holeRun_prefix]
  exact pairChange_cost d _ _ _ (holeRun_fits g C₀ hC (h.take j))

end NonuniformCompetitive.IsoscelesProof
end

/- Complete checked body: TwoMatching -/
section

set_option autoImplicit false

namespace NonuniformCompetitive.IsoscelesProof

open KServer

variable {M : Type*} [MetricSpace M]

def flipTwo : Fin 2 → Fin 2 := ![1,0]

@[simp] lemma flipTwo_zero : flipTwo 0 = 1 := rfl
@[simp] lemma flipTwo_one : flipTwo 1 = 0 := rfl
@[simp] lemma flipTwo_twice (i : Fin 2) : flipTwo (flipTwo i) = i := by fin_cases i <;> rfl

noncomputable def matchingDist (C D : Config 2 M) : ℝ :=
  min (moveCost C D) (moveCost C (D ∘ flipTwo))

lemma move_nonneg (C D : Config 2 M) : 0 ≤ moveCost C D :=
  Finset.sum_nonneg (fun _ _ => dist_nonneg)

@[simp] lemma move_self (C : Config 2 M) : moveCost C C = 0 := by simp [moveCost]

lemma matching_nonneg (C D : Config 2 M) : 0 ≤ matchingDist C D :=
  le_min (move_nonneg _ _) (move_nonneg _ _)

@[simp] lemma matching_self (C : Config 2 M) : matchingDist C C = 0 := by
  simp only [matchingDist,move_self,min_eq_left (move_nonneg _ _)]

lemma move_triangle (C D E : Config 2 M) : moveCost C E ≤ moveCost C D + moveCost D E := by
  unfold moveCost
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => dist_triangle (C i) (D i) (E i))

lemma matching_triangle_right (C D E : Config 2 M) :
    matchingDist C E ≤ matchingDist C D + moveCost D E := by
  unfold matchingDist
  by_cases h : moveCost C D ≤ moveCost C (D ∘ flipTwo)
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans (move_triangle C D E)
  · rw [min_eq_right (le_of_not_ge h)]
    have ht := move_triangle C (D ∘ flipTwo) (E ∘ flipTwo)
    have he : moveCost (D ∘ flipTwo) (E ∘ flipTwo) = moveCost D E := by
      simp only [moveCost,Fin.sum_univ_two,Function.comp_apply,flipTwo_zero,flipTwo_one]
      exact add_comm _ _
    rw [he] at ht
    exact (min_le_right _ _).trans ht

lemma move_update (C : Config 2 M) (i : Fin 2) (r : M) :
    moveCost C (Function.update C i r) = dist (C i) r := by
  classical
  fin_cases i <;> simp [moveCost,Fin.sum_univ_two]

lemma exists_matched_update (C D : Config 2 M) (r : M) (hr : ∃ j, D j = r) :
    ∃ i : Fin 2, dist (C i) r + matchingDist (Function.update C i r) D ≤ matchingDist C D := by
  classical
  obtain ⟨j,hj⟩ := hr
  by_cases h : moveCost C D ≤ moveCost C (D ∘ flipTwo)
  · refine ⟨j,?_⟩
    have hm := min_le_left (moveCost (Function.update C j r) D)
      (moveCost (Function.update C j r) (D ∘ flipTwo))
    unfold matchingDist
    rw [min_eq_left h]
    change dist (C j) r + matchingDist (Function.update C j r) D ≤ _
    apply (add_le_add le_rfl hm).trans
    fin_cases j <;> simp_all [moveCost,Fin.sum_univ_two]
    all_goals linarith
  · refine ⟨flipTwo j,?_⟩
    have hm := min_le_right (moveCost (Function.update C (flipTwo j) r) D)
      (moveCost (Function.update C (flipTwo j) r) (D ∘ flipTwo))
    unfold matchingDist
    rw [min_eq_right (le_of_not_ge h)]
    change dist (C (flipTwo j)) r + matchingDist (Function.update C (flipTwo j) r) D ≤ _
    apply (add_le_add le_rfl hm).trans
    fin_cases j <;> simp_all [moveCost,Fin.sum_univ_two,flipTwo]
    all_goals linarith

noncomputable def lazyUpdate (C D : Config 2 M) (r : M) (hr : ∃ j, D j = r) : Config 2 M := by
  classical
  exact if ∃ i, C i = r then C
    else Function.update C (Classical.choose (exists_matched_update C D r hr)) r

lemma lazyUpdate_hit (C D : Config 2 M) (r : M) (hr : ∃ j, D j = r) (h : ∃ i, C i = r) :
    lazyUpdate C D r hr = C := by simp [lazyUpdate,h]

lemma lazyUpdate_miss (C D : Config 2 M) (r : M) (hr : ∃ j, D j = r) (h : ¬∃ i, C i = r) :
    ∃ i, lazyUpdate C D r hr = Function.update C i r := by
  exact ⟨Classical.choose (exists_matched_update C D r hr),by simp [lazyUpdate,h]⟩

lemma lazyUpdate_serves (C D : Config 2 M) (r : M) (hr : ∃ j, D j = r) :
    ∃ i, lazyUpdate C D r hr i = r := by
  classical
  by_cases h : ∃ i, C i = r
  · rw [lazyUpdate_hit C D r hr h]
    exact h
  · obtain ⟨i,hi⟩ := lazyUpdate_miss C D r hr h
    exact ⟨i,by rw [hi]; simp⟩

lemma lazyUpdate_bound (C D : Config 2 M) (r : M) (hr : ∃ j, D j = r) :
    moveCost C (lazyUpdate C D r hr) + matchingDist (lazyUpdate C D r hr) D ≤ matchingDist C D := by
  classical
  by_cases h : ∃ i, C i = r
  · rw [lazyUpdate_hit C D r hr h,move_self,zero_add]
  · simp only [lazyUpdate,if_neg h,move_update]
    exact Classical.choose_spec (exists_matched_update C D r hr)

end NonuniformCompetitive.IsoscelesProof

end

/- Complete checked body: KServerCosts -/
section

set_option autoImplicit false

namespace NonuniformCompetitive.IsoscelesProof

open KServer

variable {M : Type*} [MetricSpace M]

@[simp] lemma cost_nil (A : OnlineAlgorithm 2 M) : A.cost [] = 0 := by simp [OnlineAlgorithm.cost]

lemma cost_nonneg (A : OnlineAlgorithm 2 M) (l : List M) : 0 ≤ A.cost l :=
  Finset.sum_nonneg (fun _ _ => move_nonneg _ _)

lemma cost_append_one (A : OnlineAlgorithm 2 M) (h : List M) (r : M) :
    A.cost (h++[r]) = A.cost h + moveCost (A.conf h) (A.conf (h++[r])) := by
  unfold OnlineAlgorithm.cost
  rw [List.length_append,List.length_singleton,Finset.sum_range_succ]
  have hs : (∑ j ∈ Finset.range h.length,
      moveCost (A.conf ((h++[r]).take j)) (A.conf ((h++[r]).take (j+1)))) =
      ∑ j ∈ Finset.range h.length,
      moveCost (A.conf (h.take j)) (A.conf (h.take (j+1))) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [List.take_append_of_le_length (by simpa using (Finset.mem_range.mp hj).le),
      List.take_append_of_le_length (by simpa using Nat.succ_le_of_lt (Finset.mem_range.mp hj))]
  rw [hs]
  have hlen : h.length+1 = (h++[r]).length := by simp
  rw [hlen,List.take_length]
  simp

def shiftAlgorithm (A : OnlineAlgorithm 2 M) (h : List M) : OnlineAlgorithm 2 M where
  conf l := A.conf (h++l)
  serves l r := by simpa only [List.append_assoc] using A.serves (h++l) r

@[simp] lemma shift_nil (A : OnlineAlgorithm 2 M) : shiftAlgorithm A [] = A := by
  cases A
  simp [shiftAlgorithm]

lemma cost_append (A : OnlineAlgorithm 2 M) (h l : List M) :
    A.cost (h++l) = A.cost h + (shiftAlgorithm A h).cost l := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l r ih =>
    rw [← List.append_assoc,cost_append_one,ih,cost_append_one]
    simp only [shiftAlgorithm,add_assoc,List.append_assoc]

end NonuniformCompetitive.IsoscelesProof

end

/- Complete checked body: OfflinePath -/
section

set_option autoImplicit false

namespace NonuniformCompetitive.IsoscelesProof

open KServer

lemma offlineCost_le_serving_schedule {M : Type*} [MetricSpace M] (C₀ : Config 2 M)
    (σ : List M) (S : ℕ → Config 2 M) (hS : ServesFrom C₀ σ S) :
    offlineCost C₀ σ ≤ ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j+1)) := by
  apply csInf_le
  · refine ⟨0,?_⟩
    rintro c ⟨T,_hT,rfl⟩
    exact Finset.sum_nonneg (fun _ _ => move_nonneg _ _)
  · exact ⟨S,hS,rfl⟩

lemma offlineCost_le_schedule_mismatch {M : Type*} [MetricSpace M] (C₀ : Config 2 M)
    (σ : List M) (S : ℕ → Config 2 M)
    (hS : ∀ j : Fin σ.length, ∃ i, S (j+1) i = σ[j]) :
    offlineCost C₀ σ ≤ moveCost C₀ (S 0) + ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j+1)) := by
  let T : ℕ → Config 2 M := fun j => if j=0 then C₀ else S j
  have hT : ServesFrom C₀ σ T := by
    refine ⟨by simp [T],?_⟩
    intro j
    simpa [T] using hS j
  apply (offlineCost_le_serving_schedule C₀ σ T hT).trans
  cases hl : σ.length with
  | zero => simp [move_nonneg]
  | succ k =>
    rw [Finset.sum_range_succ',Finset.sum_range_succ']
    have htail : (∑ j ∈ Finset.range k, moveCost (T (j+1)) (T (j+1+1))) =
        ∑ j ∈ Finset.range k, moveCost (S (j+1)) (S (j+1+1)) := by simp [T]
    rw [htail]
    simp only [T,if_pos rfl,show ¬(1:ℕ)=0 by decide,ite_false]
    have hh := move_triangle C₀ (S 0) (S 1)
    linarith

lemma initial_pair_move_le {M : Type*} [MetricSpace M] (d : ℕ) (hd : 1≤d)
    (e : Vtx ≃ M) (he : ∀ x y, dist (e x) (e y) = triDist d x y) (C₀ : Config 2 M) (h : Vtx) :
    moveCost C₀ (e ∘ pairConf h) ≤ (2*d:ℝ) := by
  have hi (i : Fin 2) : dist (C₀ i) (e (pairConf h i)) ≤ d := by
    rw [← e.apply_symm_apply (C₀ i),he]
    exact triDist_le d hd _ _
  simp only [moveCost,Fin.sum_univ_two,Function.comp_apply]
  linarith [hi 0,hi 1]

lemma offlineCost_le_hole_path {M : Type*} [MetricSpace M] (d : ℕ) (hd : 1≤d)
    (e : Vtx ≃ M) (he : ∀ x y, dist (e x) (e y) = triDist d x y)
    (C₀ : Config 2 M) (σ : List Vtx) (h : ℕ → Vtx)
    (hs : ∀ j : Fin σ.length, σ[j] ≠ h (j+1)) :
    offlineCost C₀ (σ.map e) ≤ (2*d:ℝ) + ∑ j ∈ Finset.range σ.length, triDist d (h j) (h (j+1)) := by
  let T := liftHolePath h (pairConf (h 0))
  have hT (j : ℕ) : FitsPair (T j) (h j) := liftHolePath_fits h _ (Or.inl rfl) j
  let S : ℕ → Config 2 M := fun j => e ∘ T j
  have hS : ∀ j : Fin (σ.map e).length, ∃ i, S (j+1) i = (σ.map e)[j] := by
    intro j
    let k : Fin σ.length := ⟨j.val,by simpa using j.isLt⟩
    obtain ⟨i,hi⟩ := (hT (j+1)).serves.mpr (hs k)
    refine ⟨i,?_⟩
    simp only [S,Function.comp_apply,Fin.getElem_fin,List.getElem_map]
    exact congrArg e hi
  have hc := offlineCost_le_schedule_mismatch C₀ (σ.map e) S hS
  have hi : moveCost C₀ (S 0) ≤ (2*d:ℝ) := initial_pair_move_le d hd e he C₀ (h 0)
  have hcost : (∑ j ∈ Finset.range (σ.map e).length, moveCost (S j) (S (j+1))) =
      ∑ j ∈ Finset.range σ.length, triDist d (h j) (h (j+1)) := by
    simp only [List.length_map]
    apply Finset.sum_congr rfl
    intro j _hj
    have heq : moveCost (S j) (S (j+1)) = triMove d (T j) (T (j+1)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact he _ _
    rw [heq]
    exact liftHolePath_cost d h _ (Or.inl rfl) j
  rw [hcost] at hc
  linarith

end NonuniformCompetitive.IsoscelesProof

end

/- Complete checked body: HolePlans -/
section

set_option autoImplicit false

namespace NonuniformCompetitive.IsoscelesProof

inductive HolePlan where
  | nil
  | cons (request hole : Vtx) (tail : HolePlan)

namespace HolePlan

def requests : HolePlan → List Vtx
  | .nil => []
  | .cons r _ t => r::t.requests

def holes (h : Vtx) : HolePlan → ℕ → Vtx
  | _,0 => h
  | .nil,_+1 => h
  | .cons _ g t,k+1 => t.holes g k

def finish (h : Vtx) : HolePlan → Vtx
  | .nil => h
  | .cons _ g t => t.finish g

def Valid : HolePlan → Prop
  | .nil => True
  | .cons r g t => r≠g ∧ t.Valid

noncomputable def cost (d : ℕ) (h : Vtx) : HolePlan → ℝ
  | .nil => 0
  | .cons _ g t => triDist d h g+t.cost d g

def append : HolePlan → HolePlan → HolePlan
  | .nil,Q => Q
  | .cons r g P,Q => .cons r g (P.append Q)

lemma holes_zero (P : HolePlan) (h : Vtx) : P.holes h 0=h := by cases P <;> rfl

lemma requests_append (P Q : HolePlan) : (P.append Q).requests=P.requests++Q.requests := by
  induction P with
  | nil => rfl
  | cons r g P ih => simp only [append,requests,ih,List.cons_append]

lemma finish_append (P Q : HolePlan) (h : Vtx) : (P.append Q).finish h=Q.finish (P.finish h) := by
  induction P generalizing h with
  | nil => rfl
  | cons r g P ih => exact ih g

lemma cost_append (P Q : HolePlan) (d : ℕ) (h : Vtx) :
    (P.append Q).cost d h=P.cost d h+Q.cost d (P.finish h) := by
  induction P generalizing h with
  | nil => simp [append,cost,finish]
  | cons r g P ih => simp only [append,cost,finish,ih,add_assoc]

lemma valid_append (P Q : HolePlan) (hP : P.Valid) (hQ : Q.Valid) : (P.append Q).Valid := by
  induction P with
  | nil => exact hQ
  | cons r g P ih => exact ⟨hP.1,ih hP.2⟩

lemma serves (P : HolePlan) (hP : P.Valid) (h : Vtx) :
    ∀ j : Fin P.requests.length, P.requests[j] ≠ P.holes h (j+1) := by
  induction P generalizing h with
  | nil => intro j; exact Fin.elim0 j
  | cons r g P ih =>
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · change r ≠ P.holes g 0
      simpa only [holes_zero] using hP.1
    · exact ih hP.2 g k

lemma cost_eq_sum (P : HolePlan) (d : ℕ) (h : Vtx) :
    (∑ j ∈ Finset.range P.requests.length, triDist d (P.holes h j) (P.holes h (j+1))) = P.cost d h := by
  induction P generalizing h with
  | nil => simp [requests,cost]
  | cons r g P ih =>
    simp only [requests,List.length_cons]
    rw [Finset.sum_range_succ']
    simp only [holes,holes_zero]
    rw [ih]
    exact add_comm _ _

lemma offline_le {M : Type*} [MetricSpace M] (P : HolePlan) (hP : P.Valid)
    (d : ℕ) (hd : 1≤d) (e : Vtx ≃ M) (he : ∀ x y, dist (e x) (e y)=triDist d x y)
    (C₀ : KServer.Config 2 M) (h : Vtx) :
    KServer.offlineCost C₀ (P.requests.map e) ≤ (2*d:ℝ)+P.cost d h := by
  have hb := offlineCost_le_hole_path d hd e he C₀ P.requests (P.holes h) (P.serves hP h)
  rw [P.cost_eq_sum d h] at hb
  exact hb

end HolePlan

end NonuniformCompetitive.IsoscelesProof

end

/- Complete checked body: FiniteLaw -/
section

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace NonuniformCompetitive.IsoscelesProof

/-- A finite probability tree. Its branches are fixed before any algorithm coins are sampled. -/
inductive FiniteLaw (α : Type*) where
  | pure (a : α)
  | mix (q r : ℝ≥0) (sum_one : q + r = 1) (left right : FiniteLaw α)

namespace FiniteLaw

variable {α β : Type*}

def All (Q : FiniteLaw α) (P : α → Prop) : Prop :=
  match Q with
  | .pure a => P a
  | .mix _ _ _ L R => L.All P ∧ R.All P

noncomputable def mean (Q : FiniteLaw α) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  match Q with
  | .pure a => f a
  | .mix q r _ L R => q * L.mean f + r * R.mean f

noncomputable def realMean (Q : FiniteLaw α) (f : α → ℝ) : ℝ :=
  match Q with
  | .pure a => f a
  | .mix q r _ L R => q * L.realMean f + r * R.realMean f

def map (f : α → β) (Q : FiniteLaw α) : FiniteLaw β :=
  match Q with
  | .pure a => .pure (f a)
  | .mix q r h L R => .mix q r h (L.map f) (R.map f)

def bind (Q : FiniteLaw α) (F : α → FiniteLaw β) : FiniteLaw β :=
  match Q with
  | .pure a => F a
  | .mix q r h L R => .mix q r h (L.bind F) (R.bind F)

lemma all_of_forall (Q : FiniteLaw α) {P : α → Prop} (h : ∀ a, P a) : Q.All P := by
  induction Q with
  | pure a => exact h a
  | mix q r hs L R hL hR => exact ⟨hL,hR⟩

lemma all_mono (Q : FiniteLaw α) {P T : α → Prop} (h : Q.All P) (hm : ∀ a, P a → T a) :
    Q.All T := by
  induction Q with
  | pure a => exact hm a h
  | mix q r hs L R hL hR => exact ⟨hL h.1,hR h.2⟩

@[simp] lemma all_map (Q : FiniteLaw α) (f : α → β) (P : β → Prop) :
    (Q.map f).All P ↔ Q.All (fun a => P (f a)) := by
  induction Q with
  | pure a => rfl
  | mix q r hs L R hL hR => simp only [map,All,hL,hR]

@[simp] lemma all_bind (Q : FiniteLaw α) (F : α → FiniteLaw β) (P : β → Prop) :
    (Q.bind F).All P ↔ Q.All (fun a => (F a).All P) := by
  induction Q with
  | pure a => rfl
  | mix q r hs L R hL hR => simp only [bind,All,hL,hR]

@[simp] lemma mean_const (Q : FiniteLaw α) (c : ℝ≥0∞) : Q.mean (fun _ => c) = c := by
  induction Q with
  | pure a => rfl
  | mix q r hs L R hL hR =>
    simp only [mean,hL,hR,← add_mul,← ENNReal.coe_add,hs,ENNReal.coe_one,one_mul]

@[simp] lemma realMean_const (Q : FiniteLaw α) (c : ℝ) : Q.realMean (fun _ => c) = c := by
  induction Q with
  | pure a => rfl
  | mix q r hs L R hL hR =>
    simp only [realMean,hL,hR,← add_mul,← NNReal.coe_add,hs,NNReal.coe_one,one_mul]

lemma mean_add (Q : FiniteLaw α) (f g : α → ℝ≥0∞) :
    Q.mean (fun a => f a + g a) = Q.mean f + Q.mean g := by
  induction Q with
  | pure a => rfl
  | mix q r hs L R hL hR => simp only [mean,hL,hR]; ring

lemma realMean_add (Q : FiniteLaw α) (f g : α → ℝ) :
    Q.realMean (fun a => f a + g a) = Q.realMean f + Q.realMean g := by
  induction Q with
  | pure a => rfl
  | mix q r hs L R hL hR => simp only [realMean,hL,hR]; ring

lemma realMean_sub (Q : FiniteLaw α) (f g : α → ℝ) :
    Q.realMean (fun a => f a - g a) = Q.realMean f - Q.realMean g := by
  induction Q with
  | pure a => rfl
  | mix q r hs L R hL hR => simp only [realMean,hL,hR]; ring

lemma mean_mul_const (Q : FiniteLaw α) (f : α → ℝ≥0∞) (c : ℝ≥0∞) :
    Q.mean (fun a => f a * c) = Q.mean f * c := by
  induction Q with
  | pure a => rfl
  | mix q r hs L R hL hR => simp only [mean,hL,hR]; ring

lemma realMean_mul_const (Q : FiniteLaw α) (f : α → ℝ) (c : ℝ) :
    Q.realMean (fun a => f a * c) = Q.realMean f * c := by
  induction Q with
  | pure a => rfl
  | mix q r hs L R hL hR => simp only [realMean,hL,hR]; ring

lemma mean_mono (Q : FiniteLaw α) {f g : α → ℝ≥0∞} (h : Q.All (fun a => f a ≤ g a)) :
    Q.mean f ≤ Q.mean g := by
  induction Q with
  | pure a => exact h
  | mix q r hs L R hL hR =>
    dsimp only [mean]
    gcongr
    · exact hL h.1
    · exact hR h.2

lemma realMean_nonneg (Q : FiniteLaw α) {f : α → ℝ} (h : Q.All (fun a => 0 ≤ f a)) :
    0 ≤ Q.realMean f := by
  induction Q with
  | pure a => exact h
  | mix q r hs L R hL hR =>
    exact add_nonneg (mul_nonneg q.coe_nonneg (hL h.1)) (mul_nonneg r.coe_nonneg (hR h.2))

lemma mean_congr (Q : FiniteLaw α) {f g : α → ℝ≥0∞} (h : Q.All (fun a => f a = g a)) :
    Q.mean f = Q.mean g := by
  apply le_antisymm
  · exact Q.mean_mono (Q.all_mono h (fun _ h => h.le))
  · exact Q.mean_mono (Q.all_mono h (fun _ h => h.ge))

lemma realMean_congr (Q : FiniteLaw α) {f g : α → ℝ} (h : Q.All (fun a => f a = g a)) :
    Q.realMean f = Q.realMean g := by
  induction Q with
  | pure a => exact h
  | mix q r hs L R hL hR => simp only [realMean,hL h.1,hR h.2]

@[simp] lemma mean_map (Q : FiniteLaw α) (f : α → β) (g : β → ℝ≥0∞) :
    (Q.map f).mean g = Q.mean (fun a => g (f a)) := by
  induction Q with
  | pure a => rfl
  | mix q r hs L R hL hR => simp only [map,mean,hL,hR]

@[simp] lemma realMean_map (Q : FiniteLaw α) (f : α → β) (g : β → ℝ) :
    (Q.map f).realMean g = Q.realMean (fun a => g (f a)) := by
  induction Q with
  | pure a => rfl
  | mix q r hs L R hL hR => simp only [map,realMean,hL,hR]

@[simp] lemma mean_bind (Q : FiniteLaw α) (F : α → FiniteLaw β) (g : β → ℝ≥0∞) :
    (Q.bind F).mean g = Q.mean (fun a => (F a).mean g) := by
  induction Q with
  | pure a => rfl
  | mix q r hs L R hL hR => simp only [bind,mean,hL,hR]

@[simp] lemma realMean_bind (Q : FiniteLaw α) (F : α → FiniteLaw β) (g : β → ℝ) :
    (Q.bind F).realMean g = Q.realMean (fun a => (F a).realMean g) := by
  induction Q with
  | pure a => rfl
  | mix q r hs L R hL hR => simp only [bind,realMean,hL,hR]

lemma mean_ofReal (Q : FiniteLaw α) {f : α → ℝ} (h : Q.All (fun a => 0 ≤ f a)) :
    Q.mean (fun a => ENNReal.ofReal (f a)) = ENNReal.ofReal (Q.realMean f) := by
  induction Q with
  | pure a => rfl
  | mix q r hs L R hL hR =>
    simp only [mean,realMean,hL h.1,hR h.2]
    rw [ENNReal.ofReal_add (mul_nonneg q.coe_nonneg (L.realMean_nonneg h.1))
      (mul_nonneg r.coe_nonneg (R.realMean_nonneg h.2)),
      ENNReal.ofReal_mul q.coe_nonneg,ENNReal.ofReal_mul r.coe_nonneg,
      ENNReal.ofReal_coe_nnreal,ENNReal.ofReal_coe_nnreal]

lemma measurable_mean {Ω : Type*} [MeasurableSpace Ω] (Q : FiniteLaw α)
    (f : α → Ω → ℝ≥0∞) (hf : ∀ a, Measurable (f a)) :
    Measurable (fun ω => Q.mean (fun a => f a ω)) := by
  induction Q with
  | pure a => exact hf a
  | mix q r hs L R hL hR => exact (measurable_const.mul hL).add (measurable_const.mul hR)

lemma mean_lintegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Q : FiniteLaw α) (f : α → Ω → ℝ≥0∞) (hf : ∀ a, Measurable (f a)) :
    Q.mean (fun a => ∫⁻ ω, f a ω ∂μ) = ∫⁻ ω, Q.mean (fun a => f a ω) ∂μ := by
  induction Q with
  | pure a => rfl
  | mix q r hs L R hL hR =>
    simp only [mean,hL,hR]
    have hLm : Measurable (fun ω => (q : ℝ≥0∞) * L.mean (fun a => f a ω)) :=
      measurable_const.mul (L.measurable_mean f hf)
    symm
    calc
      _ = (∫⁻ ω, (q : ℝ≥0∞) * L.mean (fun a => f a ω) ∂μ) +
          ∫⁻ ω, (r : ℝ≥0∞) * R.mean (fun a => f a ω) ∂μ :=
        lintegral_add_left hLm _
      _ = _ := by rw [lintegral_const_mul _ (L.measurable_mean f hf),
        lintegral_const_mul _ (R.measurable_mean f hf)]

end FiniteLaw
end NonuniformCompetitive.IsoscelesProof

end

/- Complete checked body: GeometricLaw -/
section

set_option autoImplicit false

open scoped ENNReal NNReal

namespace NonuniformCompetitive.IsoscelesProof


noncomputable def hardStop (p : ℕ) : ℝ≥0 := ((p : ℝ≥0) + 1)⁻¹
noncomputable def hardGo (p : ℕ) : ℝ≥0 := (p : ℝ≥0) / ((p : ℝ≥0) + 1)

lemma hard_sum (p : ℕ) : hardStop p + hardGo p = 1 := by
  unfold hardStop hardGo
  have h : (p : ℝ≥0) + 1 ≠ 0 := by positivity
  field_simp
  ring

lemma hard_go_real (p : ℕ) : (hardGo p : ℝ) * ((p : ℝ) + 1) = p := by
  simp only [hardGo,NNReal.coe_div,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one]
  exact div_mul_cancel₀ _ (by positivity)

lemma hard_go_ennreal (p : ℕ) : (hardGo p : ℝ≥0∞) * ((p : ℝ≥0∞) + 1) = p := by
  have h : hardGo p * ((p : ℝ≥0) + 1) = p := by
    unfold hardGo
    exact div_mul_cancel₀ _ (by positivity)
  exact_mod_cast h

noncomputable def hardLaw (p : ℕ) : ℕ → FiniteLaw ℕ
  | 0 => .pure p
  | k + 1 => .mix (hardStop p) (hardGo p) (hard_sum p) (.pure 0) ((hardLaw p k).map Nat.succ)

lemma hard_writes_mean (p k : ℕ) : (hardLaw p k).realMean (fun w => (w : ℝ)) = p := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [hardLaw,FiniteLaw.realMean,FiniteLaw.realMean_map,Nat.cast_zero,mul_zero,zero_add,
      Nat.cast_succ]
    rw [FiniteLaw.realMean_add,FiniteLaw.realMean_const,ih]
    exact hard_go_real p

lemma hard_support (p k : ℕ) : (hardLaw p k).All (fun w => w < k ∨ w = p + k) := by
  induction k with
  | zero => exact Or.inr (by omega)
  | succ k ih =>
    refine ⟨Or.inl (by omega),?_⟩
    rw [FiniteLaw.all_map]
    exact FiniteLaw.all_mono _ ih (by intro w hw; omega)

lemma hard_tail_mean (p k : ℕ) :
    (hardLaw p k).realMean (fun w => if w = p + k then 1 else 0) = (hardGo p : ℝ) ^ k := by
  induction k with
  | zero => simp [hardLaw,FiniteLaw.realMean]
  | succ k ih =>
    simp only [hardLaw,FiniteLaw.realMean,FiniteLaw.realMean_map]
    have hzero : ¬ 0 = p + (k + 1) := by omega
    have heq : (fun w : ℕ => if w.succ = p + (k + 1) then (1 : ℝ) else 0) =
        fun w => if w = p + k then 1 else 0 := by
      funext w
      have hiff : w.succ = p + (k + 1) ↔ w = p + k := by omega
      simp only [hiff]
    rw [if_neg hzero, mul_zero, zero_add,heq,ih,pow_succ]
    ring

lemma hard_min_mean (p : ℕ) :
    (hardLaw p p).realMean (fun w => ((min w p : ℕ) : ℝ)) =
      (p : ℝ) * (1 - (hardGo p : ℝ) ^ p) := by
  have heq : (hardLaw p p).All (fun w => ((min w p : ℕ) : ℝ) =
      (w : ℝ) - (if w = p + p then 1 else 0) * (p : ℝ)) := by
    apply FiniteLaw.all_mono _ (hard_support p p)
    intro w hw
    rcases hw with hw | rfl
    · have hn : w ≠ p + p := by omega
      simp [min_eq_left hw.le,hn]
    · simp only [min_eq_right (by omega : p ≤ p + p),ite_true,one_mul,Nat.cast_add]
      ring
  rw [FiniteLaw.realMean_congr _ heq,FiniteLaw.realMean_sub,hard_writes_mean,
    FiniteLaw.realMean_mul_const,hard_tail_mean]
  ring

lemma hard_go_lt_one (p : ℕ) : (hardGo p : ℝ) < 1 := by
  simp only [hardGo,NNReal.coe_div,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one]
  exact (div_lt_one (by positivity)).mpr (by linarith)

lemma hard_threshold_mean (p k j : ℕ) (hj : j ≤ k) :
    (hardLaw p k).realMean (fun w => if w < j then (w : ℝ) else (p+j : ℕ)) = p := by
  induction k generalizing j with
  | zero =>
    have hj0 : j=0 := by omega
    subst j
    simp [hardLaw]
  | succ k ih =>
    cases j with
    | zero => simp only [Nat.not_lt_zero,ite_false,Nat.add_zero,FiniteLaw.realMean_const]
    | succ j =>
      simp only [hardLaw,FiniteLaw.realMean,FiniteLaw.realMean_map]
      have he : (fun w : ℕ => if w.succ < j+1 then (w.succ : ℝ) else ((p+(j+1) : ℕ) : ℝ)) =
          fun w => (if w < j then (w : ℝ) else ((p+j : ℕ) : ℝ))+1 := by
        funext w
        simp only [Nat.succ_lt_succ_iff,Nat.cast_succ,Nat.cast_add]
        split_ifs <;> ring
      rw [if_pos (by omega : 0 < j+1),Nat.cast_zero,mul_zero,zero_add,he,
        FiniteLaw.realMean_add,FiniteLaw.realMean_const,ih j (by omega),hard_go_real]

lemma hard_phase_profile_mean (p j : ℕ) (hj : j ≤ p) :
    (hardLaw p p).realMean (fun w =>
      (if w < j then (w : ℝ) else ((p+j : ℕ) : ℝ))+1+
      (if w=p+p then (1:ℝ) else 0)*(1/2)) = (p:ℝ)+1+(hardGo p : ℝ)^p/2 := by
  rw [FiniteLaw.realMean_add,FiniteLaw.realMean_add,hard_threshold_mean p p j hj,
    FiniteLaw.realMean_const,FiniteLaw.realMean_mul_const,hard_tail_mean]
  ring

end NonuniformCompetitive.IsoscelesProof

end

/- Complete checked body: PhaseLaw -/
section

set_option autoImplicit false

namespace NonuniformCompetitive.IsoscelesProof

def nearOfBool (b : Bool) : Vtx := if b then 1 else 0

@[simp] lemma nearOfBool_ne_far (b : Bool) : nearOfBool b ≠ 2 := by cases b <;> decide

def altWord (x : Vtx) : ℕ → List Vtx
  | 0 => []
  | k+1 => nearOther x :: altWord (nearOther x) k

def lastNear (x : Vtx) : ℕ → Vtx
  | 0 => x
  | k+1 => lastNear (nearOther x) k

lemma lastNear_ne_far (x : Vtx) (hx : x≠2) (k : ℕ) : lastNear x k ≠ 2 := by
  induction k generalizing x with
  | zero => exact hx
  | succ k ih => exact ih _ (nearOther_ne_far _)

lemma altWord_near (x : Vtx) (k : ℕ) : ∀ r ∈ altWord x k, r≠2 := by
  induction k generalizing x with
  | zero => simp [altWord]
  | succ k ih =>
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact nearOther_ne_far _
    · exact ih _ _ hr

structure PhaseSample where
  run : ℕ
  finish : Option Bool

namespace PhaseSample

def advance (s : PhaseSample) : PhaseSample := ⟨s.run+1,s.finish⟩

def word (x : Vtx) (s : PhaseSample) : List Vtx :=
  altWord x s.run ++ [2] ++ s.finish.toList.map nearOfBool

def endpoint (x : Vtx) (s : PhaseSample) : Vtx :=
  s.finish.elim (lastNear x s.run) nearOfBool

def benchmark (p : ℕ) (s : PhaseSample) : ℝ :=
  if s.finish.isSome then p+1 else s.run

def isLong (s : PhaseSample) : ℝ := if s.finish.isSome then 1 else 0

lemma benchmark_nonneg (p : ℕ) (s : PhaseSample) : 0 ≤ s.benchmark p := by
  unfold benchmark
  split_ifs <;> positivity

lemma advance_word (x : Vtx) (s : PhaseSample) :
    s.advance.word x = nearOther x :: s.word (nearOther x) := by
  simp only [word,advance,altWord,List.cons_append]

lemma advance_endpoint (x : Vtx) (s : PhaseSample) :
    s.advance.endpoint x = s.endpoint (nearOther x) := rfl

lemma endpoint_ne_far (x : Vtx) (hx : x≠2) (s : PhaseSample) : s.endpoint x ≠ 2 := by
  unfold endpoint
  cases s.finish with
  | none => exact lastNear_ne_far x hx _
  | some b => exact nearOfBool_ne_far b

lemma advance_benchmark (p : ℕ) (s : PhaseSample) :
    s.advance.benchmark p = s.benchmark p + (1-s.isLong) := by
  cases s with
  | mk run finish => cases finish <;> simp [advance,benchmark,isLong,Nat.cast_add]

end PhaseSample

def resetWord (x : Vtx) : ℕ → List Vtx
  | 0 => []
  | k+1 => resetWord x k ++ [2,x]

def fullPhaseWord (p : ℕ) (x : Vtx) (s : PhaseSample) : List Vtx := resetWord x (p+2) ++ s.word x

noncomputable def phaseLaw (p : ℕ) : ℕ → FiniteLaw PhaseSample
  | 0 => .mix (1/2) (1/2) (by norm_num) (.pure ⟨p+2,some false⟩) (.pure ⟨p+2,some true⟩)
  | k+1 => .mix (hardStop p) (hardGo p) (hard_sum p) (.pure ⟨1,none⟩)
      ((phaseLaw p k).map PhaseSample.advance)

lemma phaseLaw_support (p k : ℕ) : (phaseLaw p k).All (fun s : PhaseSample =>
    (s.finish = none ∧ 1 ≤ s.run ∧ s.run ≤ k) ∨ (s.finish ≠ none ∧ s.run = p+2+k)) := by
  induction k with
  | zero => exact ⟨Or.inr ⟨by simp,by simp⟩,Or.inr ⟨by simp,by simp⟩⟩
  | succ k ih =>
    refine ⟨Or.inl ⟨rfl,by decide,by change 1≤k+1; omega⟩,?_⟩
    rw [FiniteLaw.all_map]
    apply FiniteLaw.all_mono _ ih
    intro s hs
    rcases hs with ⟨hf,h1,h2⟩ | ⟨hf,he⟩
    · exact Or.inl ⟨hf,by dsimp [PhaseSample.advance]; omega,by dsimp [PhaseSample.advance]; omega⟩
    · exact Or.inr ⟨hf,by dsimp [PhaseSample.advance]; omega⟩

lemma phaseLaw_long_mean (p k : ℕ) :
    (phaseLaw p k).realMean PhaseSample.isLong = (hardGo p : ℝ)^k := by
  induction k with
  | zero => norm_num [phaseLaw,FiniteLaw.realMean,PhaseSample.isLong]
  | succ k ih =>
    simp only [phaseLaw,FiniteLaw.realMean,FiniteLaw.realMean_map]
    change (hardStop p : ℝ)*0+(hardGo p : ℝ)*(phaseLaw p k).realMean PhaseSample.isLong = _
    rw [mul_zero,zero_add,ih,pow_succ]
    ring

lemma phaseLaw_benchmark_mean (p k : ℕ) :
    (phaseLaw p k).realMean (PhaseSample.benchmark p) = (p:ℝ)+1-(k:ℝ)*(hardGo p : ℝ)^k := by
  induction k with
  | zero => norm_num [phaseLaw,FiniteLaw.realMean,PhaseSample.benchmark]; ring
  | succ k ih =>
    simp only [phaseLaw,FiniteLaw.realMean,FiniteLaw.realMean_map,PhaseSample.advance_benchmark]
    have hstop : PhaseSample.benchmark p ⟨1,none⟩ = 1 := by simp [PhaseSample.benchmark]
    rw [hstop]
    rw [FiniteLaw.realMean_add,FiniteLaw.realMean_sub,FiniteLaw.realMean_const,ih,phaseLaw_long_mean]
    have hs : (hardStop p : ℝ)+(hardGo p : ℝ)=1 := by exact_mod_cast hard_sum p
    have hg := hard_go_real p
    rw [pow_succ,Nat.cast_succ]
    nlinarith

end NonuniformCompetitive.IsoscelesProof

end

/- Complete checked body: PhasePlans -/
section

set_option autoImplicit false

namespace NonuniformCompetitive.IsoscelesProof

lemma plan_nearOther_ne_self (x : Vtx) (hx : x≠2) : nearOther x ≠ x := by
  fin_cases x <;> norm_num [nearOther,Fin.ext_iff] at *

lemma nearOther_dist (d : ℕ) (x : Vtx) (hx : x≠2) : triDist d (nearOther x) x=1 := by
  fin_cases x <;> norm_num [nearOther,triDist,Fin.ext_iff] at *

def fixedPlan (g : Vtx) : List Vtx → HolePlan
  | [] => .nil
  | r::l => .cons r g (fixedPlan g l)

lemma fixedPlan_requests (g : Vtx) (l : List Vtx) : (fixedPlan g l).requests=l := by
  induction l with
  | nil => rfl
  | cons r l ih => simp only [fixedPlan,HolePlan.requests,ih]

lemma fixedPlan_valid (g : Vtx) (l : List Vtx) (h : ∀r∈l,r≠g) : (fixedPlan g l).Valid := by
  induction l with
  | nil => trivial
  | cons r l ih => exact ⟨h r (by simp),ih (fun s hs => h s (by simp [hs]))⟩

lemma fixedPlan_same (d : ℕ) (g : Vtx) (l : List Vtx) :
    (fixedPlan g l).finish g=g ∧ (fixedPlan g l).cost d g=0 := by
  induction l with
  | nil => exact ⟨rfl,rfl⟩
  | cons r l ih => simpa only [fixedPlan,HolePlan.finish,HolePlan.cost,triDist_self,zero_add] using ih

lemma fixedPlan_cost_le (d : ℕ) (hd : 1≤d) (h g : Vtx) (l : List Vtx) :
    (fixedPlan g l).cost d h ≤ d := by
  cases l with
  | nil => simp [fixedPlan,HolePlan.cost]
  | cons r l =>
    simp only [fixedPlan,HolePlan.cost,(fixedPlan_same d g l).2,add_zero]
    exact triDist_le d hd h g

def rentalPlan (x : Vtx) : ℕ → HolePlan
  | 0 => .nil
  | k+1 => .cons (nearOther x) x (rentalPlan (nearOther x) k)

lemma rentalPlan_requests (x : Vtx) (k : ℕ) : (rentalPlan x k).requests=altWord x k := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simp only [rentalPlan,HolePlan.requests,altWord,ih]

lemma rentalPlan_facts (d : ℕ) (x : Vtx) (hx : x≠2) (k : ℕ) :
    (rentalPlan x k).requests=altWord x k ∧ (rentalPlan x k).Valid ∧
    (rentalPlan x k).finish (nearOther x)=nearOther (lastNear x k) ∧
    (rentalPlan x k).cost d (nearOther x)=k := by
  induction k generalizing x with
  | zero => simp [rentalPlan,altWord,lastNear,HolePlan.requests,HolePlan.Valid,HolePlan.finish,HolePlan.cost]
  | succ k ih =>
    obtain ⟨hreq,hvalid,hfin,hcost⟩ := ih (nearOther x) (nearOther_ne_far _)
    rw [nearOther_other x hx] at hfin hcost
    refine ⟨?_,⟨plan_nearOther_ne_self x hx,hvalid⟩,hfin,?_⟩
    · simp only [rentalPlan,HolePlan.requests,altWord,hreq]
    · simp only [rentalPlan,HolePlan.cost,nearOther_dist d x hx,hcost,Nat.cast_succ]
      ring

noncomputable def samplePlan (x : Vtx) (s : PhaseSample) : HolePlan :=
  match s.finish with
  | none => (rentalPlan x s.run).append (.cons 2 (nearOther (lastNear x s.run)) .nil)
  | some b => (fixedPlan 2 (altWord x s.run)).append
      (.cons 2 (nearOther (nearOfBool b)) (.cons (nearOfBool b) (nearOther (nearOfBool b)) .nil))

lemma samplePlan_requests (x : Vtx) (s : PhaseSample) : (samplePlan x s).requests=s.word x := by
  cases hs : s.finish with
  | none => simp [samplePlan,hs,HolePlan.requests_append,HolePlan.requests,PhaseSample.word,
      rentalPlan_requests]
  | some b => simp [samplePlan,hs,HolePlan.requests_append,HolePlan.requests,fixedPlan_requests,
      PhaseSample.word,List.append_assoc]

lemma samplePlan_facts (d p : ℕ) (hd : 1≤d) (hp : p+1=2*d) (x : Vtx) (hx : x≠2) (s : PhaseSample) :
    (samplePlan x s).Valid ∧ (samplePlan x s).finish (nearOther x)=nearOther (s.endpoint x) ∧
    (samplePlan x s).cost d (nearOther x) ≤ s.benchmark p := by
  cases hs : s.finish with
  | none =>
    obtain ⟨_hreq,hvalid,hfin,hcost⟩ := rentalPlan_facts d x hx s.run
    refine ⟨?_,?_,?_⟩
    · simp only [samplePlan,hs]
      exact HolePlan.valid_append _ _ hvalid ⟨Ne.symm (nearOther_ne_far _),trivial⟩
    · simp [samplePlan,hs,HolePlan.finish_append,HolePlan.finish,PhaseSample.endpoint]
    · simp [samplePlan,hs,HolePlan.cost_append,hfin,hcost,HolePlan.cost,PhaseSample.benchmark]
  | some b =>
    have hv := fixedPlan_valid 2 (altWord x s.run) (altWord_near _ _)
    refine ⟨?_,?_,?_⟩
    · simp only [samplePlan,hs]
      exact HolePlan.valid_append _ _ hv
        ⟨Ne.symm (nearOther_ne_far _),⟨Ne.symm (plan_nearOther_ne_self _ (nearOfBool_ne_far b)),trivial⟩⟩
    · simp [samplePlan,hs,HolePlan.finish_append,HolePlan.finish,PhaseSample.endpoint]
    · have h1 := fixedPlan_cost_le d hd (nearOther x) 2 (altWord x s.run)
      have h2 := triDist_le d hd ((fixedPlan 2 (altWord x s.run)).finish (nearOther x))
        (nearOther (nearOfBool b))
      have hpR : (p:ℝ)+1=2*d := by exact_mod_cast hp
      simp only [samplePlan,hs,HolePlan.cost_append,HolePlan.cost,triDist_self,add_zero,
        PhaseSample.benchmark,Option.isSome_some,ite_true]
      linarith

lemma resetWord_avoids_hole (x : Vtx) (hx : x≠2) (k : ℕ) : ∀r∈resetWord x k,r≠nearOther x := by
  induction k with
  | zero => simp [resetWord]
  | succ k ih =>
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact ih r hr
    · simp only [List.mem_cons,List.mem_nil_iff,or_false] at hr
      rcases hr with hr2 | hrx
      · subst r
        exact Ne.symm (nearOther_ne_far _)
      · rw [hrx]
        exact Ne.symm (plan_nearOther_ne_self x hx)

noncomputable def fullPhasePlan (p : ℕ) (x : Vtx) (s : PhaseSample) : HolePlan :=
  (fixedPlan (nearOther x) (resetWord x (p+2))).append (samplePlan x s)

lemma fullPhasePlan_facts (d p : ℕ) (hd : 1≤d) (hp : p+1=2*d) (x : Vtx) (hx : x≠2) (s : PhaseSample) :
    (fullPhasePlan p x s).requests=fullPhaseWord p x s ∧ (fullPhasePlan p x s).Valid ∧
    (fullPhasePlan p x s).finish (nearOther x)=nearOther (s.endpoint x) ∧
    (fullPhasePlan p x s).cost d (nearOther x) ≤ s.benchmark p := by
  obtain ⟨hv,hf,hc⟩ := samplePlan_facts d p hd hp x hx s
  have hr := fixedPlan_same d (nearOther x) (resetWord x (p+2))
  refine ⟨?_,HolePlan.valid_append _ _
    (fixedPlan_valid _ _ (resetWord_avoids_hole x hx _)) hv,?_,?_⟩
  · simp only [fullPhasePlan,HolePlan.requests_append,fixedPlan_requests,samplePlan_requests,fullPhaseWord]
  · simpa only [fullPhasePlan,HolePlan.finish_append,hr.1] using hf
  · simpa only [fullPhasePlan,HolePlan.cost_append,hr.1,hr.2,zero_add] using hc

end NonuniformCompetitive.IsoscelesProof

end

/- Complete checked body: LazyStates -/
section

set_option autoImplicit false

namespace NonuniformCompetitive.IsoscelesProof

def Covers (C : Fin 2 → Vtx) (r : Vtx) : Prop := ∃ i, C i = r

def Rental (C : Fin 2 → Vtx) (x : Vtx) : Prop := Covers C 2 ∧ Covers C x

def Bought (C : Fin 2 → Vtx) : Prop := Covers C 0 ∧ Covers C 1

lemma rental_misses_other (C : Fin 2 → Vtx) (x : Vtx) (hx : x≠2) (h : Rental C x) :
    ¬Covers C (nearOther x) := by
  generalize h0 : C 0 = x0
  generalize h1 : C 1 = x1
  fin_cases x <;> fin_cases x0 <;> fin_cases x1 <;>
    simp_all [Rental,Covers,Fin.exists_fin_two,nearOther]

lemma bought_covers_near (C : Fin 2 → Vtx) (h : Bought C) (r : Vtx) (hr : r≠2) : Covers C r := by
  fin_cases r <;> simp_all [Bought]

lemma bought_misses_far (C : Fin 2 → Vtx) (h : Bought C) : ¬Covers C 2 := by
  generalize h0 : C 0 = x0
  generalize h1 : C 1 = x1
  fin_cases x0 <;> fin_cases x1 <;>
    simp_all [Bought,Covers,Fin.exists_fin_two]

lemma triDist_miss_ge_one (d : ℕ) (hd : 1≤d) (x y : Vtx) (h : x≠y) : 1 ≤ triDist d x y := by
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd
  unfold triDist
  rw [if_neg h]
  split_ifs <;> linarith

lemma triMove_update (d : ℕ) (C : Fin 2 → Vtx) (i : Fin 2) (r : Vtx) :
    triMove d C (Function.update C i r) = triDist d (C i) r := by
  fin_cases i <;> simp [triMove,Fin.sum_univ_two]

lemma rental_step (d : ℕ) (A : TriPolicy) (hA : TriIsLazy A) (h : List Vtx) (x : Vtx)
    (hx : x≠2) (hC : Rental (A.conf h) x) :
    (Rental (A.conf (h++[nearOther x])) (nearOther x) ∧
      triMove d (A.conf h) (A.conf (h++[nearOther x])) = 1) ∨
    (Bought (A.conf (h++[nearOther x])) ∧
      triMove d (A.conf h) (A.conf (h++[nearOther x])) = d) := by
  have hm := rental_misses_other (A.conf h) x hx hC
  obtain ⟨i,hi⟩ := (hA h (nearOther x)).2 hm
  rw [hi,triMove_update]
  generalize h0 : A.conf h 0 = x0
  generalize h1 : A.conf h 1 = x1
  fin_cases x <;> fin_cases i <;> fin_cases x0 <;> fin_cases x1 <;>
    simp_all [Rental,Bought,Covers,Fin.exists_fin_two,nearOther,triDist]

lemma bought_return (d : ℕ) (A : TriPolicy) (hA : TriIsLazy A) (h : List Vtx)
    (hC : Bought (A.conf h)) :
    ∃ x : Vtx, x≠2 ∧ Rental (A.conf (h++[2])) x ∧ triMove d (A.conf h) (A.conf (h++[2])) = d := by
  obtain ⟨i,hi⟩ := (hA h 2).2 (bought_misses_far _ hC)
  rw [hi,triMove_update]
  refine ⟨A.conf h (if i=0 then 1 else 0),?_,?_,?_⟩
  all_goals
    generalize h0 : A.conf h 0 = x0
    generalize h1 : A.conf h 1 = x1
    fin_cases i <;> fin_cases x0 <;> fin_cases x1 <;>
      simp_all [Bought,Rental,Covers,Fin.exists_fin_two,triDist]

lemma miss_move_lower (d : ℕ) (hd : 1≤d) (C D : Fin 2 → Vtx) (r : Vtx)
    (hC : ¬Covers C r) (hD : Covers D r) : 1 ≤ triMove d C D := by
  obtain ⟨i,hi⟩ := hD
  have hne : C i ≠ r := by intro h; exact hC ⟨i,h⟩
  have hb := triDist_miss_ge_one d hd (C i) r hne
  rw [← hi] at hb
  exact hb.trans (Finset.single_le_sum (fun _ _ => triDist_nonneg _ _ _) (Finset.mem_univ i))

end NonuniformCompetitive.IsoscelesProof

end

/- Complete checked body: LazyRuns -/
section

set_option autoImplicit false

namespace NonuniformCompetitive.IsoscelesProof

@[simp] lemma triCost_singleton (d : ℕ) (A : TriPolicy) (r : Vtx) :
    triCost d A [r] = triMove d (A.conf []) (A.conf [r]) := by simp [triCost]

lemma triCost_cons (d : ℕ) (A : TriPolicy) (r : Vtx) (l : List Vtx) :
    triCost d A (r::l) = triMove d (A.conf []) (A.conf [r]) + triCost d (triShift A [r]) l := by
  simpa only [List.singleton_append,triCost_singleton] using triCost_append d A [r] l

lemma bought_near_word (d : ℕ) (A : TriPolicy) (hA : TriIsLazy A) (l : List Vtx)
    (hl : ∀ r ∈ l, r≠2) (hC : Bought (A.conf [])) :
    A.conf l = A.conf [] ∧ triCost d A l = 0 := by
  induction l generalizing A with
  | nil => simp
  | cons r l ih =>
    have hr : r≠2 := hl r (by simp)
    have hs : A.conf [r] = A.conf [] := by
      simpa only [List.nil_append] using (hA [] r).1 (bought_covers_near _ hC r hr)
    have hC' : Bought ((triShift A [r]).conf []) := by simpa [triShift,hs] using hC
    have hh := ih (triShift A [r]) (triShift_lazy A hA _) (fun s h => hl s (by simp [h])) hC'
    constructor
    · simpa only [triShift,List.singleton_append,List.append_nil,hs] using hh.1
    · rw [triCost_cons,hs,hh.2]
      simp [triMove]

lemma rental_alt_run (d : ℕ) (A : TriPolicy) (hA : TriIsLazy A) (x : Vtx) (hx : x≠2)
    (hC : Rental (A.conf []) x) (k : ℕ) :
    (Rental (A.conf (altWord x k)) (lastNear x k) ∧ triCost d A (altWord x k) = k) ∨
    (Bought (A.conf (altWord x k)) ∧ (d:ℝ) ≤ triCost d A (altWord x k)) := by
  induction k generalizing A x with
  | zero => exact Or.inl ⟨hC,by simp [altWord]⟩
  | succ k ih =>
    have hs := rental_step d A hA [] x hx hC
    simp only [List.nil_append] at hs
    rcases hs with ⟨hrent,hcost⟩ | ⟨hbuy,hcost⟩
    · have hh := ih (triShift A [nearOther x]) (triShift_lazy A hA _) (nearOther x)
        (nearOther_ne_far _) (by simpa [triShift] using hrent)
      rcases hh with ⟨hr,hc⟩ | ⟨hb,hc⟩
      · left
        refine ⟨?_,?_⟩
        · simpa only [triShift,List.singleton_append,altWord,lastNear] using hr
        · rw [altWord,triCost_cons,hcost,hc,Nat.cast_succ]
          ring
      · right
        refine ⟨?_,?_⟩
        · simpa only [triShift,List.singleton_append,altWord] using hb
        · rw [altWord,triCost_cons,hcost]
          linarith
    · have hh := bought_near_word d (triShift A [nearOther x]) (triShift_lazy A hA _)
        (altWord (nearOther x) k) (altWord_near _ _) (by simpa [triShift] using hbuy)
      right
      refine ⟨?_,?_⟩
      · have hEq : A.conf (altWord x (k+1)) = A.conf [nearOther x] := by
          simpa only [altWord,triShift,List.singleton_append,List.append_nil] using hh.1
        rw [hEq]
        exact hbuy
      · rw [altWord,triCost_cons,hcost,hh.2,add_zero]

lemma rental_fair_lower (d : ℕ) (hd : 1≤d) (A : TriPolicy) (x : Vtx) (hx : x≠2)
    (hC : Rental (A.conf []) x) :
    1 ≤ triCost d A [0] + triCost d A [1] := by
  have hm := rental_misses_other (A.conf []) x hx hC
  have hs : Covers (A.conf [nearOther x]) (nearOther x) := by
    simpa only [Covers,List.nil_append] using A.serves [] (nearOther x)
  have hl := miss_move_lower d hd (A.conf []) (A.conf [nearOther x]) (nearOther x) hm hs
  have h0 := triCost_nonneg d A [0]
  have h1 := triCost_nonneg d A [1]
  rw [triCost_singleton] at h0 h1
  rw [← triCost_singleton] at hl
  fin_cases x
  · norm_num [nearOther] at hl ⊢
    linarith
  · norm_num [nearOther] at hl ⊢
    linarith
  · exact (hx rfl).elim

lemma bought_return_fair_lower (d : ℕ) (hd : 1≤d) (A : TriPolicy) (hA : TriIsLazy A)
    (hC : Bought (A.conf [])) :
    (d:ℝ)+1/2 ≤ (triCost d A [2,0]+triCost d A [2,1])/2 := by
  obtain ⟨x,hx,hR,hcost⟩ := bought_return d A hA [] hC
  simp only [List.nil_append] at hR hcost
  have hf := rental_fair_lower d hd (triShift A [2]) x hx (by simpa [triShift] using hR)
  rw [triCost_cons d A 2 [0],triCost_cons d A 2 [1],hcost]
  linarith

lemma bought_long_lower (d : ℕ) (hd : 1≤d) (A : TriPolicy) (hA : TriIsLazy A)
    (x : Vtx) (k : ℕ) (hC : Bought (A.conf [])) :
    (d:ℝ)+1/2 ≤ (triCost d A (altWord x k++[2,0])+triCost d A (altWord x k++[2,1]))/2 := by
  obtain ⟨hs,hcost⟩ := bought_near_word d A hA (altWord x k) (altWord_near _ _) hC
  have hb : Bought ((triShift A (altWord x k)).conf []) := by simpa [triShift,hs] using hC
  have hh := bought_return_fair_lower d hd (triShift A (altWord x k)) (triShift_lazy A hA _) hb
  rw [triCost_append,triCost_append,hcost,zero_add,zero_add]
  exact hh

lemma rental_long_lower (d : ℕ) (hd : 1≤d) (A : TriPolicy) (hA : TriIsLazy A)
    (x : Vtx) (hx : x≠2) (hC : Rental (A.conf []) x) (k : ℕ) (hk : 2*d+1≤k) :
    (2*d:ℝ)+1/2 ≤ (triCost d A (altWord x k++[2,0])+triCost d A (altWord x k++[2,1]))/2 := by
  rcases rental_alt_run d A hA x hx hC k with ⟨_hr,hcost⟩ | ⟨hb,hcost⟩
  · have h0 := triCost_nonneg d (triShift A (altWord x k)) [2,0]
    have h1 := triCost_nonneg d (triShift A (altWord x k)) [2,1]
    have hkr : (2*d:ℝ)+1≤k := by exact_mod_cast hk
    rw [triCost_append,triCost_append,hcost]
    linarith
  · have hh := bought_return_fair_lower d hd (triShift A (altWord x k))
      (triShift_lazy A hA _) (by simpa [triShift] using hb)
    rw [triCost_append,triCost_append]
    linarith

end NonuniformCompetitive.IsoscelesProof

end

/- Complete checked body: ResetBlocks -/
section

set_option autoImplicit false

namespace NonuniformCompetitive.IsoscelesProof

lemma rental_block_stays (d : ℕ) (A : TriPolicy) (hA : TriIsLazy A) (x : Vtx)
    (hC : Rental (A.conf []) x) : A.conf [2,x] = A.conf [] ∧ triCost d A [2,x] = 0 := by
  have h2 : A.conf [2] = A.conf [] := by
    simpa only [List.nil_append] using (hA [] 2).1 hC.1
  have hx : A.conf [2,x] = A.conf [2] := by
    apply (hA [2] x).1
    rw [h2]
    exact hC.2
  constructor
  · exact hx.trans h2
  · rw [show [2,x] = [2]++[x] from rfl,triCost_append_one,triCost_singleton,List.singleton_append,hx,h2]
    simp [triMove]

lemma rental_reset_stays (d : ℕ) (A : TriPolicy) (hA : TriIsLazy A) (x : Vtx)
    (hC : Rental (A.conf []) x) (k : ℕ) :
    A.conf (resetWord x k) = A.conf [] ∧ triCost d A (resetWord x k) = 0 := by
  induction k with
  | zero => simp [resetWord]
  | succ k ih =>
    have hb := rental_block_stays d (triShift A (resetWord x k)) (triShift_lazy A hA _) x
      (by simpa [triShift,ih.1] using hC)
    constructor
    · simpa only [resetWord,triShift,List.append_nil,ih.1] using hb.1
    · rw [resetWord,triCost_append,ih.2,hb.2,add_zero]

lemma failed_block_cost (d : ℕ) (hd : 1≤d) (A : TriPolicy) (hA : TriIsLazy A) (x : Vtx)
    (hC : ¬Rental (A.conf [2,x]) x) : 1 ≤ triCost d A [2,x] := by
  have h2 : Covers (A.conf [2]) 2 := by simpa only [Covers,List.nil_append] using A.serves [] 2
  have hmiss : ¬Covers (A.conf [2]) x := by
    intro hx
    have he : A.conf [2,x] = A.conf [2] := (hA [2] x).1 hx
    apply hC
    rw [he]
    exact ⟨h2,hx⟩
  have hx : Covers (A.conf [2,x]) x := A.serves [2] x
  have hl := miss_move_lower d hd (A.conf [2]) (A.conf [2,x]) x hmiss hx
  have hn := triCost_nonneg d A [2]
  rw [show [2,x] = [2]++[x] from rfl,triCost_append_one,List.singleton_append]
  linarith

lemma failed_reset_cost (d : ℕ) (hd : 1≤d) (A : TriPolicy) (hA : TriIsLazy A) (x : Vtx) (k : ℕ)
    (hC : ¬Rental (A.conf (resetWord x k)) x) : (k:ℝ) ≤ triCost d A (resetWord x k) := by
  induction k with
  | zero => simp [resetWord]
  | succ k ih =>
    have hn : ¬Rental (A.conf (resetWord x k)) x := by
      intro hr
      have hs := rental_block_stays d (triShift A (resetWord x k)) (triShift_lazy A hA _) x
        (by simpa [triShift] using hr)
      have he : A.conf (resetWord x (k+1)) = A.conf (resetWord x k) := by
        simpa only [resetWord,triShift,List.append_nil] using hs.1
      apply hC
      rw [he]
      exact hr
    have hl := failed_block_cost d hd (triShift A (resetWord x k)) (triShift_lazy A hA _) x
      (by simpa only [triShift,resetWord] using hC)
    have ht := ih hn
    rw [resetWord,triCost_append,Nat.cast_succ]
    linarith

end NonuniformCompetitive.IsoscelesProof

end

/- Complete checked body: FiniteRealLaw -/
section

set_option autoImplicit false

namespace NonuniformCompetitive.IsoscelesProof.FiniteLaw

variable {α : Type*}

lemma realMean_mono (Q : FiniteLaw α) {f g : α → ℝ} (h : Q.All (fun a => f a ≤ g a)) :
    Q.realMean f ≤ Q.realMean g := by
  induction Q with
  | pure a => exact h
  | mix q r hs L R hL hR =>
    dsimp only [realMean]
    exact add_le_add (mul_le_mul_of_nonneg_left (hL h.1) q.coe_nonneg)
      (mul_le_mul_of_nonneg_left (hR h.2) r.coe_nonneg)

end NonuniformCompetitive.IsoscelesProof.FiniteLaw
end

/- Complete checked body: PhaseLower -/
section

set_option autoImplicit false

namespace NonuniformCompetitive.IsoscelesProof

lemma phaseLaw_cost_zero (d p : ℕ) (A : TriPolicy) (x : Vtx) :
    (phaseLaw p 0).realMean (fun s => triCost d A (s.word x)) =
      (triCost d A (altWord x (p+2)++[2,0])+triCost d A (altWord x (p+2)++[2,1]))/2 := by
  simp [phaseLaw,FiniteLaw.realMean,PhaseSample.word,nearOfBool,List.append_assoc]
  ring

lemma phaseLaw_cost_succ (d p k : ℕ) (A : TriPolicy) (x : Vtx) :
    (phaseLaw p (k+1)).realMean (fun s => triCost d A (s.word x)) =
      triMove d (A.conf []) (A.conf [nearOther x]) +
      (hardStop p : ℝ)*triCost d (triShift A [nearOther x]) [2] +
      (hardGo p : ℝ)*(phaseLaw p k).realMean
        (fun s => triCost d (triShift A [nearOther x]) (s.word (nearOther x))) := by
  simp only [phaseLaw,FiniteLaw.realMean,FiniteLaw.realMean_map,PhaseSample.advance_word]
  change (hardStop p : ℝ)*triCost d A [nearOther x,2]+
    (hardGo p : ℝ)*(phaseLaw p k).realMean (fun s => triCost d A (nearOther x::s.word (nearOther x))) = _
  simp_rw [triCost_cons d A (nearOther x)]
  rw [FiniteLaw.realMean_add,FiniteLaw.realMean_const]
  have hs : (hardStop p : ℝ)+(hardGo p : ℝ)=1 := by exact_mod_cast hard_sum p
  calc
    _ = ((hardStop p : ℝ)+(hardGo p : ℝ))*triMove d (A.conf []) (A.conf [nearOther x]) +
        (hardStop p : ℝ)*triCost d (triShift A [nearOther x]) [2]+
        (hardGo p : ℝ)*(phaseLaw p k).realMean
          (fun s => triCost d (triShift A [nearOther x]) (s.word (nearOther x))) := by ring
    _ = _ := by rw [hs,one_mul]

lemma bought_phase_lower (d : ℕ) (hd : 1≤d) (p k : ℕ) (A : TriPolicy) (hA : TriIsLazy A)
    (x : Vtx) (hC : Bought (A.conf [])) :
    (d:ℝ)+(hardGo p : ℝ)^k/2 ≤ (phaseLaw p k).realMean (fun s => triCost d A (s.word x)) := by
  induction k generalizing A x with
  | zero =>
    rw [phaseLaw_cost_zero]
    simpa using bought_long_lower d hd A hA x (p+2) hC
  | succ k ih =>
    have hs : A.conf [nearOther x] = A.conf [] := by
      simpa only [List.nil_append] using (hA [] (nearOther x)).1
        (bought_covers_near _ hC _ (nearOther_ne_far _))
    have hC' : Bought ((triShift A [nearOther x]).conf []) := by simpa [triShift,hs] using hC
    have ht := ih (triShift A [nearOther x]) (triShift_lazy A hA _) (nearOther x) hC'
    obtain ⟨_z,_hz,_hR,hmove⟩ := bought_return d (triShift A [nearOther x])
      (triShift_lazy A hA _) [] hC'
    have hstop : triCost d (triShift A [nearOther x]) [2] = d := by
      simpa only [List.nil_append,triCost_singleton] using hmove
    rw [phaseLaw_cost_succ,hs,hstop,pow_succ]
    simp only [triMove,triDist_self,Finset.sum_const_zero,zero_add]
    have hsum : (hardStop p : ℝ)+(hardGo p : ℝ)=1 := by exact_mod_cast hard_sum p
    have hid : (hardStop p : ℝ)*d+(hardGo p : ℝ)*d=d := by rw [← add_mul,hsum,one_mul]
    have hh := mul_le_mul_of_nonneg_left ht (hardGo p).coe_nonneg
    linarith

lemma rental_phase_lower (d : ℕ) (hd : 1≤d) (p : ℕ) (hp : p+1=2*d) (k : ℕ)
    (A : TriPolicy) (hA : TriIsLazy A) (x : Vtx) (hx : x≠2) (hC : Rental (A.conf []) x) :
    (2*d:ℝ)+(hardGo p : ℝ)^k/2 ≤ (phaseLaw p k).realMean (fun s => triCost d A (s.word x)) := by
  induction k generalizing A x with
  | zero =>
    rw [phaseLaw_cost_zero]
    simpa using rental_long_lower d hd A hA x hx hC (p+2) (by omega)
  | succ k ih =>
    have hs := rental_step d A hA [] x hx hC
    simp only [List.nil_append] at hs
    rw [phaseLaw_cost_succ,pow_succ]
    rcases hs with ⟨hrent,hmove⟩ | ⟨hbuy,hmove⟩
    · have ht := ih (triShift A [nearOther x]) (triShift_lazy A hA _) (nearOther x)
        (nearOther_ne_far _) (by simpa [triShift] using hrent)
      rw [hmove]
      have hstop := mul_nonneg (hardStop p).coe_nonneg
        (triCost_nonneg d (triShift A [nearOther x]) [2])
      have hmul := mul_le_mul_of_nonneg_left ht (hardGo p).coe_nonneg
      have hpR : (p:ℝ)+1=2*d := by exact_mod_cast hp
      have hid := hard_go_real p
      rw [hpR] at hid
      nlinarith
    · have hC' : Bought ((triShift A [nearOther x]).conf []) := by simpa [triShift] using hbuy
      have ht := bought_phase_lower d hd p k (triShift A [nearOther x]) (triShift_lazy A hA _)
        (nearOther x) hC'
      obtain ⟨_z,_hz,_hR,hs⟩ := bought_return d (triShift A [nearOther x])
        (triShift_lazy A hA _) [] hC'
      have hstop : triCost d (triShift A [nearOther x]) [2] = d := by
        simpa only [List.nil_append,triCost_singleton] using hs
      rw [hmove,hstop]
      have hsum : (hardStop p : ℝ)+(hardGo p : ℝ)=1 := by exact_mod_cast hard_sum p
      have hid : (hardStop p : ℝ)*d+(hardGo p : ℝ)*d=d := by rw [← add_mul,hsum,one_mul]
      have hmul := mul_le_mul_of_nonneg_left ht (hardGo p).coe_nonneg
      linarith

lemma full_phase_lower (d : ℕ) (hd : 1≤d) (p : ℕ) (hp : p+1=2*d)
    (A : TriPolicy) (hA : TriIsLazy A) (x : Vtx) (hx : x≠2) :
    (2*d:ℝ)+(hardGo p : ℝ)^p/2 ≤ (phaseLaw p p).realMean (fun s => triCost d A (fullPhaseWord p x s)) := by
  simp only [fullPhaseWord,triCost_append]
  rw [FiniteLaw.realMean_add,FiniteLaw.realMean_const]
  by_cases hR : Rental (A.conf (resetWord x (p+2))) x
  · have ht := rental_phase_lower d hd p hp p (triShift A (resetWord x (p+2)))
      (triShift_lazy A hA _) x hx (by simpa [triShift] using hR)
    have hn := triCost_nonneg d A (resetWord x (p+2))
    linarith
  · have ht := failed_reset_cost d hd A hA x (p+2) hR
    have hpR : (p:ℝ)+1=2*d := by exact_mod_cast hp
    have hm : 0 ≤ (phaseLaw p p).realMean
        (fun s => triCost d (triShift A (resetWord x (p+2))) (s.word x)) :=
      FiniteLaw.realMean_nonneg _ ((phaseLaw p p).all_of_forall (fun s => triCost_nonneg _ _ _))
    have hpow : (hardGo p : ℝ)^p ≤ 1 := pow_le_one₀ (hardGo p).coe_nonneg (hard_go_lt_one p).le
    push_cast at ht
    linarith

end NonuniformCompetitive.IsoscelesProof

end

/- Complete checked body: FiniteIID -/
section

set_option autoImplicit false

open scoped ENNReal

namespace NonuniformCompetitive.IsoscelesProof


namespace FiniteLaw

variable {α : Type*}

def iid (Q : FiniteLaw α) : ℕ → FiniteLaw (List α)
  | 0 => .pure []
  | k+1 => Q.bind (fun a => (iid Q k).map (List.cons a))

lemma iid_all (Q : FiniteLaw α) {P : α → Prop} (h : Q.All P) (k : ℕ) :
    (Q.iid k).All (fun l => ∀ a ∈ l, P a) := by
  induction k with
  | zero => simp [iid,All]
  | succ k ih =>
    rw [iid,all_bind]
    apply Q.all_mono h
    intro a ha
    rw [all_map]
    apply (Q.iid k).all_mono ih
    intro l hl b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ha
    · exact hl b hb

lemma iid_real_sum (Q : FiniteLaw α) (g : α → ℝ) (k : ℕ) :
    (Q.iid k).realMean (fun l => (l.map g).sum) = (k : ℝ) * Q.realMean g := by
  induction k with
  | zero => simp [iid,realMean]
  | succ k ih =>
    simp only [iid,realMean_bind,realMean_map,List.map_cons,List.sum_cons]
    have h : (fun a => (Q.iid k).realMean (fun l => g a + (l.map g).sum)) =
        fun a => g a + (k : ℝ) * Q.realMean g := by
      funext a
      rw [realMean_add,realMean_const,ih]
    rw [h,realMean_add,realMean_const]
    simp only [Nat.cast_succ]
    ring

end FiniteLaw

end NonuniformCompetitive.IsoscelesProof

end

/- Complete checked body: LazySimulation -/
section

set_option autoImplicit false

namespace NonuniformCompetitive.IsoscelesProof

open KServer

variable {M : Type*} [MetricSpace M]

noncomputable def lazyFrom (A : OnlineAlgorithm 2 M) (h : List M) (C : Config 2 M) :
    List M → Config 2 M
  | [] => C
  | r::l => lazyFrom A (h++[r]) (lazyUpdate C (A.conf (h++[r])) r (A.serves h r)) l

lemma lazyFrom_append (A : OnlineAlgorithm 2 M) (h : List M) (C : Config 2 M) (l t : List M) :
    lazyFrom A h C (l++t) = lazyFrom A (h++l) (lazyFrom A h C l) t := by
  induction l generalizing h C with
  | nil => simp [lazyFrom]
  | cons r l ih =>
    simp only [List.cons_append,lazyFrom,ih]
    simp only [List.append_assoc,List.singleton_append]

noncomputable def lazyConf (A : OnlineAlgorithm 2 M) (l : List M) : Config 2 M :=
  lazyFrom A [] (A.conf []) l

@[simp] lemma lazyConf_nil (A : OnlineAlgorithm 2 M) : lazyConf A [] = A.conf [] := rfl

lemma lazyConf_append_one (A : OnlineAlgorithm 2 M) (h : List M) (r : M) :
    lazyConf A (h++[r]) = lazyUpdate (lazyConf A h) (A.conf (h++[r])) r (A.serves h r) := by
  unfold lazyConf
  rw [lazyFrom_append]
  simp only [List.nil_append,lazyFrom]

noncomputable def lazyAlgorithm (A : OnlineAlgorithm 2 M) : OnlineAlgorithm 2 M where
  conf := lazyConf A
  serves h r := by rw [lazyConf_append_one]; exact lazyUpdate_serves _ _ _ _

def IsLazy (A : OnlineAlgorithm 2 M) : Prop :=
  ∀ h r, ((∃ i, A.conf h i = r) → A.conf (h++[r]) = A.conf h) ∧
    ((¬∃ i, A.conf h i = r) → ∃ i, A.conf (h++[r]) = Function.update (A.conf h) i r)

lemma lazyAlgorithm_lazy (A : OnlineAlgorithm 2 M) : IsLazy (lazyAlgorithm A) := by
  intro h r
  change ((∃ i, lazyConf A h i = r) → lazyConf A (h++[r]) = lazyConf A h) ∧
    ((¬∃ i, lazyConf A h i = r) → ∃ i, lazyConf A (h++[r]) = Function.update (lazyConf A h) i r)
  rw [lazyConf_append_one]
  exact ⟨lazyUpdate_hit _ _ _ _,lazyUpdate_miss _ _ _ _⟩

lemma lazyAlgorithm_cost_potential (A : OnlineAlgorithm 2 M) (l : List M) :
    (lazyAlgorithm A).cost l + matchingDist ((lazyAlgorithm A).conf l) (A.conf l) ≤ A.cost l := by
  induction l using List.reverseRecOn with
  | nil => simp [lazyAlgorithm]
  | append_singleton h r ih =>
    rw [cost_append_one,cost_append_one]
    have hs := lazyUpdate_bound (lazyConf A h) (A.conf (h++[r])) r (A.serves h r)
    have ht := matching_triangle_right (lazyConf A h) (A.conf h) (A.conf (h++[r]))
    change (lazyAlgorithm A).cost h + moveCost (lazyConf A h) (lazyConf A (h++[r])) +
      matchingDist (lazyConf A (h++[r])) (A.conf (h++[r])) ≤ _
    rw [lazyConf_append_one]
    change (lazyAlgorithm A).cost h + matchingDist (lazyConf A h) (A.conf h) ≤ _ at ih
    linarith

lemma lazyAlgorithm_cost_le (A : OnlineAlgorithm 2 M) (l : List M) :
    (lazyAlgorithm A).cost l ≤ A.cost l := by
  have h := lazyAlgorithm_cost_potential A l
  have hp := matching_nonneg ((lazyAlgorithm A).conf l) (A.conf l)
  linarith

lemma exists_lazy_dominated (A : OnlineAlgorithm 2 M) :
    ∃ B : OnlineAlgorithm 2 M, IsLazy B ∧ B.conf [] = A.conf [] ∧ ∀ l, B.cost l ≤ A.cost l := by
  exact ⟨lazyAlgorithm A,lazyAlgorithm_lazy A,rfl,lazyAlgorithm_cost_le A⟩

end NonuniformCompetitive.IsoscelesProof

end

/- Complete checked body: LazyTriangle -/
section

set_option autoImplicit false

namespace NonuniformCompetitive.IsoscelesProof

lemma TriPolicy.ofOriginal_lazy {M : Type*} [MetricSpace M] (e : Vtx ≃ M)
    (A : KServer.OnlineAlgorithm 2 M) (hA : IsLazy A) : TriIsLazy (TriPolicy.ofOriginal e A) := by
  classical
  intro h r
  constructor
  · intro hc
    have hh : ∃ i, A.conf (h.map e) i = e r := by
      obtain ⟨i,hi⟩ := hc
      refine ⟨i,?_⟩
      apply e.symm.injective
      simpa only [TriPolicy.ofOriginal,Function.comp_apply,Equiv.symm_apply_apply] using hi
    have heq := (hA (h.map e) (e r)).1 hh
    change e.symm ∘ A.conf ((h++[r]).map e) = e.symm ∘ A.conf (h.map e)
    rw [List.map_append,List.map_singleton,heq]
  · intro hc
    have hh : ¬∃ i, A.conf (h.map e) i = e r := by
      rintro ⟨i,hi⟩
      apply hc
      exact ⟨i,by simp [TriPolicy.ofOriginal,hi]⟩
    obtain ⟨i,hi⟩ := (hA (h.map e) (e r)).2 hh
    refine ⟨i,?_⟩
    change e.symm ∘ A.conf ((h++[r]).map e) = Function.update (e.symm ∘ A.conf (h.map e)) i r
    rw [List.map_append,List.map_singleton,hi]
    funext j
    by_cases hj : j=i
    · subst j; simp
    · simp [Function.comp_def,hj]

end NonuniformCompetitive.IsoscelesProof

end

/- Complete checked body: RepeatedAdversary -/
section

set_option autoImplicit false

namespace NonuniformCompetitive.IsoscelesProof

def adversaryWord (p : ℕ) (x : Vtx) : List PhaseSample → List Vtx
  | [] => []
  | s::l => fullPhaseWord p x s ++ adversaryWord p (s.endpoint x) l

noncomputable def adversaryPlan (p : ℕ) (x : Vtx) : List PhaseSample → HolePlan
  | [] => .nil
  | s::l => (fullPhasePlan p x s).append (adversaryPlan p (s.endpoint x) l)

lemma adversaryPlan_facts (d p : ℕ) (hd : 1≤d) (hp : p+1=2*d) (x : Vtx) (hx : x≠2)
    (l : List PhaseSample) :
    (adversaryPlan p x l).requests=adversaryWord p x l ∧ (adversaryPlan p x l).Valid ∧
      (adversaryPlan p x l).cost d (nearOther x) ≤ (l.map (PhaseSample.benchmark p)).sum := by
  induction l generalizing x with
  | nil => simp [adversaryPlan,adversaryWord,HolePlan.requests,HolePlan.Valid,HolePlan.cost]
  | cons s l ih =>
    obtain ⟨hr,hv,hc⟩ := ih (s.endpoint x) (s.endpoint_ne_far x hx)
    obtain ⟨hpr,hpv,hpf,hpc⟩ := fullPhasePlan_facts d p hd hp x hx s
    refine ⟨?_,HolePlan.valid_append _ _ hpv hv,?_⟩
    · simp only [adversaryPlan,HolePlan.requests_append,hpr,hr,adversaryWord]
    · simpa only [adversaryPlan,HolePlan.cost_append,hpf,List.map_cons,List.sum_cons] using add_le_add hpc hc

lemma offline_adversary_le {M : Type*} [MetricSpace M] (d p : ℕ) (hd : 1≤d) (hp : p+1=2*d)
    (e : Vtx ≃ M) (he : ∀ x y, dist (e x) (e y)=triDist d x y)
    (C₀ : KServer.Config 2 M) (x : Vtx) (hx : x≠2) (l : List PhaseSample) :
    KServer.offlineCost C₀ ((adversaryWord p x l).map e) ≤
      (2*d:ℝ)+(l.map (PhaseSample.benchmark p)).sum := by
  obtain ⟨hr,hv,hc⟩ := adversaryPlan_facts d p hd hp x hx l
  rw [← hr]
  exact (HolePlan.offline_le _ hv d hd e he C₀ (nearOther x)).trans (add_le_add le_rfl hc)

lemma repeated_lazy_lower (d p : ℕ) (hd : 1≤d) (hp : p+1=2*d)
    (A : TriPolicy) (hA : TriIsLazy A) (x : Vtx) (hx : x≠2) (N : ℕ) :
    (N:ℝ)*((2*d:ℝ)+(hardGo p : ℝ)^p/2) ≤
      ((phaseLaw p p).iid N).realMean (fun l => triCost d A (adversaryWord p x l)) := by
  induction N generalizing A x with
  | zero => simp [FiniteLaw.iid,FiniteLaw.realMean,adversaryWord]
  | succ N ih =>
    simp only [FiniteLaw.iid,FiniteLaw.realMean_bind,FiniteLaw.realMean_map,adversaryWord,triCost_append]
    have hs : (fun s => ((phaseLaw p p).iid N).realMean
        (fun l => triCost d A (fullPhaseWord p x s)+
          triCost d (triShift A (fullPhaseWord p x s)) (adversaryWord p (s.endpoint x) l))) =
      fun s => triCost d A (fullPhaseWord p x s)+((phaseLaw p p).iid N).realMean
        (fun l => triCost d (triShift A (fullPhaseWord p x s)) (adversaryWord p (s.endpoint x) l)) := by
      funext s
      rw [FiniteLaw.realMean_add,FiniteLaw.realMean_const]
    rw [hs,FiniteLaw.realMean_add]
    have ht := (phaseLaw p p).realMean_mono ((phaseLaw p p).all_of_forall
      (fun s => ih (triShift A (fullPhaseWord p x s)) (triShift_lazy A hA _)
        (s.endpoint x) (s.endpoint_ne_far x hx)))
    simp only [FiniteLaw.realMean_const] at ht
    have hh := full_phase_lower d hd p hp A hA x hx
    rw [Nat.cast_succ]
    nlinarith

lemma repeated_original_lower {M : Type*} [MetricSpace M] (d p : ℕ) (hd : 1≤d) (hp : p+1=2*d)
    (e : Vtx ≃ M) (he : ∀ x y, dist (e x) (e y)=triDist d x y)
    (A : KServer.OnlineAlgorithm 2 M) (x : Vtx) (hx : x≠2) (N : ℕ) :
    (N:ℝ)*((2*d:ℝ)+(hardGo p : ℝ)^p/2) ≤
      ((phaseLaw p p).iid N).realMean (fun l => A.cost ((adversaryWord p x l).map e)) := by
  obtain ⟨B,hB,_hinit,hcost⟩ := exists_lazy_dominated A
  have hl := repeated_lazy_lower d p hd hp (TriPolicy.ofOriginal e B)
    (TriPolicy.ofOriginal_lazy e B hB) x hx N
  simp_rw [TriPolicy.ofOriginal_cost d e he] at hl
  exact hl.trans (FiniteLaw.realMean_mono _
    (FiniteLaw.all_of_forall _ (fun l => hcost ((adversaryWord p x l).map e))))

end NonuniformCompetitive.IsoscelesProof

end

/- Complete checked body: RatioGeometry -/
section

set_option autoImplicit false

namespace NonuniformCompetitive.IsoscelesProof

open NonuniformCompetitive.Isosceles

lemma ratio_phase_identity (d : ℕ) (hd : 1≤d) :
    let p := 2*d-1
    0 < (2*d:ℝ)-(p:ℝ)*(hardGo p : ℝ)^p ∧
      isoscelesRatio d*((2*d:ℝ)-(p:ℝ)*(hardGo p : ℝ)^p) =
        (2*d:ℝ)+(hardGo p : ℝ)^p/2 := by
  dsimp only
  let p := 2*d-1
  have hp : 1≤p := by dsimp [p]; omega
  have hpR : (p:ℝ)=2*d-1 := by dsimp [p]; rw [Nat.cast_sub (by omega)]; push_cast; rfl
  have hdR : (1:ℝ)≤d := by exact_mod_cast hd
  have hb : (1:ℝ)<(2*d)/(2*d-1) := by
    apply (lt_div_iff₀ (by linarith)).mpr
    linarith
  have he : 1<eTwoDSubOne d := by
    unfold eTwoDSubOne
    exact one_lt_pow₀ hb (by omega)
  have hg : (hardGo p : ℝ) = ((2*d:ℝ)/(2*d-1))⁻¹ := by
    simp only [hardGo,NNReal.coe_div,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one,hpR]
    field_simp
    ring
  have hpow : (hardGo p : ℝ)^p=(eTwoDSubOne d)⁻¹ := by rw [hg,inv_pow]; rfl
  have hsmall : (hardGo p : ℝ)^p ≤ 1 := pow_le_one₀ (hardGo p).coe_nonneg (hard_go_lt_one p).le
  have hpnonneg : (0:ℝ)≤p := Nat.cast_nonneg p
  constructor
  · have hh := mul_le_mul_of_nonneg_left hsmall hpnonneg
    change 0 < (2*d:ℝ)-(p:ℝ)*(hardGo p : ℝ)^p
    linarith
  · change isoscelesRatio d*((2*d:ℝ)-(p:ℝ)*(hardGo p : ℝ)^p) =
        (2*d:ℝ)+(hardGo p : ℝ)^p/2
    rw [hpow,hpR]
    have hden : 0<eTwoDSubOne d-1+1/(2*(d:ℝ)) := by positivity
    have he0 : eTwoDSubOne d ≠ 0 := ne_of_gt (lt_trans zero_lt_one he)
    have hd0 : (d:ℝ) ≠ 0 := ne_of_gt (by linarith : (0:ℝ)<d)
    have hfactor : (2*d:ℝ)-(2*d-1)*(eTwoDSubOne d)⁻¹ =
        ((2*d:ℝ)/eTwoDSubOne d)*(eTwoDSubOne d-1+1/(2*d)) := by
      field_simp [he0,hd0]
      ring
    rw [hfactor]
    unfold isoscelesRatio
    rw [mul_comm ((2*d:ℝ)/eTwoDSubOne d) _,←mul_assoc,div_mul_cancel₀ _ (ne_of_gt hden)]
    field_simp [he0,hd0]
    ring

end NonuniformCompetitive.IsoscelesProof

end

/- Complete checked body: LowerBound -/
section

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace NonuniformCompetitive.IsoscelesProof

open KServer NonuniformCompetitive.Isosceles

lemma offline_nonneg {M : Type*} [MetricSpace M] (C₀ : Config 2 M) (σ : List M) :
    0  ≤  offlineCost C₀ σ := by
  apply Real.sInf_nonneg
  rintro c ⟨S,_hS,rfl⟩
  exact Finset.sum_nonneg (fun _ _ => move_nonneg _ _)

lemma randomized_repeated_lower {M : Type*} [MetricSpace M]
    (d p : ℕ) (hd : 1 ≤ d) (hp : p+1=2*d) (e : Vtx ≃ M)
    (he : ∀x y, dist (e x) (e y)=triDist d x y) (A : RandomizedAlgorithm 2 M) (N : ℕ) :
    ENNReal.ofReal ((N:ℝ)*((2*d:ℝ)+(hardGo p : ℝ)^p/2))  ≤ 
      ((phaseLaw p p).iid N).mean (fun l => A.expCost ((adversaryWord p 0 l).map e)) := by
  let := A.ms
  let := A.prob
  unfold RandomizedAlgorithm.expCost
  rw [FiniteLaw.mean_lintegral A.μ _
    (fun l ω => ENNReal.ofReal ((A.alg ω).cost ((adversaryWord p 0 l).map e)))
    (fun l => ENNReal.measurable_ofReal.comp (A.meas ((adversaryWord p 0 l).map e)))]
  calc
    _ = ∫⁻ _ω, ENNReal.ofReal ((N:ℝ)*((2*d:ℝ)+(hardGo p : ℝ)^p/2)) ∂A.μ := by simp
    _  ≤  _ := by
      apply lintegral_mono
      intro ω
      have hh := repeated_original_lower d p hd hp e he (A.alg ω) 0 (by decide) N
      dsimp only
      rw [FiniteLaw.mean_ofReal _
        (f := fun l => (A.alg ω).cost ((adversaryWord p 0 l).map e))
        (FiniteLaw.all_of_forall _ (fun l => cost_nonneg (A.alg ω) ((adversaryWord p 0 l).map e)))]
      exact ENNReal.ofReal_le_ofReal hh

lemma numeric_lower {M : Type*} [MetricSpace M] (d p : ℕ) (hd : 1 ≤ d) (hp : p+1=2*d)
    (e : Vtx ≃ M) (he : ∀x y,dist (e x) (e y)=triDist d x y) (C₀ : Config 2 M)
    (A : RandomizedAlgorithm 2 M) (ρ a : ℝ)
    (hA : ∀σ,A.expCost σ  ≤  ENNReal.ofReal (ρ*offlineCost C₀ σ+a)) (N : ℕ) :
    (N:ℝ)*((2*d:ℝ)+(hardGo p : ℝ)^p/2)  ≤ 
      max ρ 0*((2*d:ℝ)+(N:ℝ)*((2*d:ℝ)-(p:ℝ)*(hardGo p : ℝ)^p))+max a 0 := by
  let C := max ρ 0
  let D := max a 0
  have hC : 0 ≤ C := le_max_right _ _
  have hD : 0 ≤ D := le_max_right _ _
  let g : List PhaseSample → ℝ := fun l => C*((2*d:ℝ)+(l.map (PhaseSample.benchmark p)).sum)+D
  have hg : ∀l,0 ≤ g l := by
    intro l
    have hs : 0 ≤ (l.map (PhaseSample.benchmark p)).sum := List.sum_nonneg
      (by intro z hz; obtain ⟨s,_hs,rfl⟩ := List.mem_map.mp hz; exact s.benchmark_nonneg p)
    dsimp [g]
    positivity
  have hmean := ((phaseLaw p p).iid N).mean_mono
    (((phaseLaw p p).iid N).all_of_forall (fun l =>
      (hA _).trans (ENNReal.ofReal_le_ofReal (show ρ*offlineCost C₀ ((adversaryWord p 0 l).map e)+a  ≤  g l from by
        have ho := offline_adversary_le d p hd hp e he C₀ 0 (by decide) l
        have hn := offline_nonneg C₀ ((adversaryWord p 0 l).map e)
        have hc : ρ ≤ C := le_max_left _ _
        have ha : a ≤ D := le_max_left _ _
        dsimp [g]
        calc
          _  ≤  C*offlineCost C₀ ((adversaryWord p 0 l).map e)+D := by nlinarith
          _  ≤  _ := by gcongr))))
  have hpR : (p:ℝ)+1=2*d := by exact_mod_cast hp
  have hm : ((phaseLaw p p).iid N).realMean g =
      C*((2*d:ℝ)+(N:ℝ)*((2*d:ℝ)-(p:ℝ)*(hardGo p : ℝ)^p))+D := by
    dsimp only [g]
    simp_rw [mul_comm C]
    rw [FiniteLaw.realMean_add,FiniteLaw.realMean_const,FiniteLaw.realMean_mul_const,
      FiniteLaw.realMean_add,FiniteLaw.realMean_const,FiniteLaw.iid_real_sum,phaseLaw_benchmark_mean,hpR]
  rw [FiniteLaw.mean_ofReal _ (FiniteLaw.all_of_forall _ hg),hm] at hmean
  have hn : 0 ≤ C*((2*d:ℝ)+(N:ℝ)*((2*d:ℝ)-(p:ℝ)*(hardGo p : ℝ)^p))+D := by
    rw [←hm]
    exact FiniteLaw.realMean_nonneg _ (FiniteLaw.all_of_forall _ hg)
  exact (ENNReal.ofReal_le_ofReal_iff hn).mp ((randomized_repeated_lower d p hd hp e he A N).trans hmean)

lemma linear_coefficient_le {a b d : ℝ} (h : ∀k:ℕ,(k:ℝ)*a ≤ (k:ℝ)*b+d) : a ≤ b := by
  by_contra hn
  have hab : 0 < a-b := sub_pos.mpr (lt_of_not_ge hn)
  obtain ⟨k,hk⟩ := exists_nat_gt (d/(a-b))
  have hm : d < (k:ℝ)*(a-b) := (div_lt_iff₀ hab).mp hk
  have hh := h k
  nlinarith

theorem no_better_ratio_direct {M : Type} [MetricSpace M] (d : ℕ) (hd : 1 ≤ d) (a b c : M)
    (hM : ∀x:M,x=a ∨ x=b ∨ x=c)
    (hab : dist a b=1) (hac : dist a c=d) (hbc : dist b c=d)
    (C₀ : Config 2 M) (A : RandomizedAlgorithm 2 M) (ρ : ℝ) (hA : A.IsCompetitiveFrom C₀ ρ) :
    isoscelesRatio d  ≤  ρ := by
  let e : Vtx ≃ M := Equiv.ofBijective (val a b c)
    ⟨val_injective d hd a b c hab hac hbc,val_surjective a b c hM⟩
  have he : ∀x y,dist (e x) (e y)=triDist d x y := val_dist d a b c hab hac hbc
  let p := 2*d-1
  have hp : p+1=2*d := by dsimp [p]; omega
  obtain ⟨a₀,ha⟩ := hA.2
  have hcoef : (2*d:ℝ)+(hardGo p : ℝ)^p/2  ≤ 
      max ρ 0*((2*d:ℝ)-(p:ℝ)*(hardGo p : ℝ)^p) := by
    apply linear_coefficient_le (d := max ρ 0*(2*d:ℝ)+max a₀ 0)
    intro N
    have hh := numeric_lower d p hd hp e he C₀ A ρ a₀ ha N
    nlinarith
  obtain ⟨hD,hid⟩ := ratio_phase_identity d hd
  change 0 < (2*d:ℝ)-(p:ℝ)*(hardGo p : ℝ)^p at hD
  change isoscelesRatio d*((2*d:ℝ)-(p:ℝ)*(hardGo p : ℝ)^p)=
    (2*d:ℝ)+(hardGo p : ℝ)^p/2 at hid
  have hr : isoscelesRatio d ≤ max ρ 0 := by
    rw [←hid] at hcoef
    exact (mul_le_mul_iff_left₀ hD).mp hcoef
  have hH : 0 < (2*d:ℝ)+(hardGo p : ℝ)^p/2 := by
    have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd
    positivity
  have hα : 0 < isoscelesRatio d := (mul_pos_iff_of_pos_right hD).mp (by rw [hid];exact hH)
  by_cases hρ : 0 ≤ ρ
  · simpa only [max_eq_left hρ] using hr
  · rw [max_eq_right (le_of_not_ge hρ)] at hr
    linarith

end NonuniformCompetitive.IsoscelesProof

end

/- Complete checked body: AttributedIsosceles -/
section

set_option autoImplicit false

namespace IsoscelesLPAttained
-- Prove2me | solution 1 for NonuniformCompetitive.Isosceles.lp_attained
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T10:08:26.196438+00:00
-- url     : https://prove2.me/submissions/c769dd7c-dfd8-4e74-a63c-f7dd5b80f353

open NonuniformCompetitive.Isosceles
open scoped BigOperators

private theorem tight_sum (P a : ℝ) (hP : 1 < P) (k : ℕ) :
    ∑ i∈Finset.Icc 1 k, (1-(a-1)*((P/(P-1))^i-1)) =
      a*k-P*(a-1)*((P/(P-1))^k-1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k+1),ih,pow_succ]
    push_cast
    field_simp [ne_of_gt (sub_pos.mpr hP)]
    ring

private theorem prefix_bound (P a : ℝ) (hP : 1 < P) (π : ℕ → ℝ) (N : ℕ)
    (hcon : ∀ k, 1 ≤ k → k ≤ N → π k*P+∑ i∈Finset.Icc 1 k, (1-π i)≤a*k) :
    ∑ i∈Finset.Icc 1 N, π i ≤ (a-1)*(P*((P/(P-1))^N-1)-N) := by
  let S (k : ℕ) : ℝ := ∑ i∈Finset.Icc 1 k, π i
  have hb : ∀ k ≤ N, S k≤(a-1)*(P*((P/(P-1))^k-1)-k) := by
    intro k
    induction k with
    | zero => intro hk; simp [S]
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      have hc := hcon (k+1) (by omega) hk
      simp [Finset.sum_sub_distrib] at hc
      have hS : S (k+1)=S k+π (k+1) := Finset.sum_Icc_succ_top (by omega : 1 ≤ k+1) π
      change π (k+1)*P + ((k:ℝ)+1-S (k+1)) ≤ a*((k:ℝ)+1) at hc
      rw [hS] at hc
      have hid : (P-1)*((a-1)*((P/(P-1))^(k+1)-1)) =
          (a-1)*(1+P*((P/(P-1))^k-1)) := by
        rw [pow_succ]
        field_simp [ne_of_gt (sub_pos.mpr hP)]
        ring
      have hpi : π (k+1)≤(a-1)*((P/(P-1))^(k+1)-1) := by
        apply (mul_le_mul_iff_right₀ (sub_pos.mpr hP)).mp
        nlinarith [hid]
      have hid2 : (a-1)*(P*((P/(P-1))^(k+1)-1)-(k+1)) =
          (a-1)*(P*((P/(P-1))^k-1)-k)+(a-1)*((P/(P-1))^(k+1)-1) := by
        rw [pow_succ]
        field_simp [ne_of_gt (sub_pos.mpr hP)]
        ring
      rw [hS]
      push_cast
      rw [hid2]
      exact add_le_add ih' hpi
  exact hb N le_rfl

private theorem ratio_parameters (d : ℕ) (hd : 1 ≤ d) :
    1 < eTwoDSubOne d ∧ 0 < isoscelesRatio d-1 ∧
      (isoscelesRatio d-1)*(eTwoDSubOne d-1+1/(2*d))=1-1/(4*d) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hP : (1 : ℝ) < 2*d := by linarith
  have hr : (1 : ℝ) < (2*d)/(2*d-1) := by apply (lt_div_iff₀ (by linarith)).mpr; linarith
  have he : 1 < eTwoDSubOne d := by unfold eTwoDSubOne; exact one_lt_pow₀ hr (by omega)
  have hden : 0 < eTwoDSubOne d-1+1/(2*d) := by positivity
  have hsmall : 1/(4*(d:ℝ)) < 1 := by apply (div_lt_one (by positivity)).mpr; linarith
  have hid : (isoscelesRatio d-1)*(eTwoDSubOne d-1+1/(2*d))=1-1/(4*d) := by
    unfold isoscelesRatio
    rw [sub_mul,div_mul_cancel₀ _ (ne_of_gt hden)]
    field_simp [ne_of_gt (by linarith : (0:ℝ) < d)]
    ring
  refine ⟨he,?_,hid⟩
  have hh : 0 < (isoscelesRatio d-1)*(eTwoDSubOne d-1+1/(2*d)) := by rw [hid]; linarith
  exact (mul_pos_iff_of_pos_right hden).mp hh

theorem checked_isosceles_lp_attained (d : ℕ) (hd : 1 ≤ d) (π : ℕ → ℝ)
    (hπ : ∀ k : ℕ, 1 ≤ k → k ≤ 2 * d - 1 →
      π k = (isoscelesRatio d - 1) * (((2 * d : ℝ) / (2 * d - 1)) ^ k - 1))
    (hπ2d : π (2 * d) = 1) :
    0 ≤ π 1 ∧
    (∀ k : ℕ, 1 ≤ k → k < 2 * d → π k ≤ π (k + 1)) ∧
    (∀ k : ℕ, 1 ≤ k → k < 2 * d →
      π k * (2 * d : ℝ) + ∑ i ∈ Finset.Icc 1 k, (1 - π i) = isoscelesRatio d * (k : ℝ)) ∧
    (2 * d : ℝ) + ∑ i ∈ Finset.Icc 1 (2 * d - 1), (1 - π i) + 1 / 2
      = isoscelesRatio d * (2 * d : ℝ) := by
  obtain ⟨he,ha,hid⟩ := ratio_parameters d hd
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hP : (1:ℝ) < 2*d := by linarith
  have hr : (1:ℝ) < (2*d)/(2*d-1) := by apply (lt_div_iff₀ (by linarith)).mpr; linarith
  have hN : ((2*d-1:ℕ):ℝ)=2*(d:ℝ)-1 := by rw [Nat.cast_sub (by omega)]; push_cast; rfl
  have hs (k : ℕ) (hk : k ≤ 2*d-1) :
      ∑ i∈Finset.Icc 1 k, (1-π i) =
        isoscelesRatio d*k-(2*d)*(isoscelesRatio d-1)*(((2*d:ℝ)/(2*d-1))^k-1) := by
    calc
      _ = ∑ i∈Finset.Icc 1 k, (1-(isoscelesRatio d-1)*(((2*d:ℝ)/(2*d-1))^i-1)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hπ i (Finset.mem_Icc.mp hi).1 (le_trans (Finset.mem_Icc.mp hi).2 hk)]
      _ = _ := tight_sum _ _ hP k
  have hlast : (isoscelesRatio d-1)*((2*d)*(eTwoDSubOne d-1)+1)=2*d-1/2 := by
    have hh := congrArg (fun z : ℝ => z*(2*d)) hid
    field_simp [ne_of_gt (by linarith : (0:ℝ) < d)] at hh
    nlinarith
  refine ⟨?_,?_,?_,?_⟩
  · rw [hπ 1 (by omega) (by omega)]
    exact mul_nonneg ha.le (sub_nonneg.mpr (one_le_pow₀ hr.le))
  · intro k hk1 hk
    by_cases hkend : k+1=2*d
    · rw [hkend,hπ2d,hπ k hk1 (by omega)]
      have hkN : k=2*d-1 := by omega
      rw [hkN]
      change (isoscelesRatio d-1)*(eTwoDSubOne d-1) ≤ 1
      have hterm : 0 ≤ (isoscelesRatio d-1)/(2*d) := by positivity
      have hsmall : 0 ≤ 1/(4*(d:ℝ)) := by positivity
      nlinarith [hid]
    · rw [hπ k hk1 (by omega),hπ (k+1) (by omega) (by omega)]
      apply mul_le_mul_of_nonneg_left _ ha.le
      apply sub_le_sub_right
      exact pow_le_pow_right₀ hr.le (by omega)
  · intro k hk1 hk
    rw [hs k (by omega),hπ k hk1 (by omega)]
    ring
  · rw [hs _ le_rfl,hN]
    change 2*(d:ℝ)+ (isoscelesRatio d*(2*d-1)-(2*d)*(isoscelesRatio d-1)*(eTwoDSubOne d-1))+1/2 = isoscelesRatio d*(2*d)
    nlinarith [hlast]
end IsoscelesLPAttained

alias checked_isosceles_lp_attained := IsoscelesLPAttained.checked_isosceles_lp_attained

namespace IsoscelesLPLower
-- Prove2me | solution 1 for NonuniformCompetitive.Isosceles.lp_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T10:14:26.559984+00:00
-- url     : https://prove2.me/submissions/d0c9092f-1e4b-46f0-9c0f-46e5aee0e083

open NonuniformCompetitive.Isosceles
open scoped BigOperators

private theorem tight_sum (P a : ℝ) (hP : 1 < P) (k : ℕ) :
    ∑ i∈Finset.Icc 1 k, (1-(a-1)*((P/(P-1))^i-1)) =
      a*k-P*(a-1)*((P/(P-1))^k-1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k+1),ih,pow_succ]
    push_cast
    field_simp [ne_of_gt (sub_pos.mpr hP)]
    ring

private theorem prefix_bound (P a : ℝ) (hP : 1 < P) (π : ℕ → ℝ) (N : ℕ)
    (hcon : ∀ k, 1 ≤ k → k ≤ N → π k*P+∑ i∈Finset.Icc 1 k, (1-π i)≤a*k) :
    ∑ i∈Finset.Icc 1 N, π i ≤ (a-1)*(P*((P/(P-1))^N-1)-N) := by
  let S (k : ℕ) : ℝ := ∑ i∈Finset.Icc 1 k, π i
  have hb : ∀ k ≤ N, S k≤(a-1)*(P*((P/(P-1))^k-1)-k) := by
    intro k
    induction k with
    | zero => intro hk; simp [S]
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      have hc := hcon (k+1) (by omega) hk
      simp [Finset.sum_sub_distrib] at hc
      have hS : S (k+1)=S k+π (k+1) := Finset.sum_Icc_succ_top (by omega : 1 ≤ k+1) π
      change π (k+1)*P + ((k:ℝ)+1-S (k+1)) ≤ a*((k:ℝ)+1) at hc
      rw [hS] at hc
      have hid : (P-1)*((a-1)*((P/(P-1))^(k+1)-1)) =
          (a-1)*(1+P*((P/(P-1))^k-1)) := by
        rw [pow_succ]
        field_simp [ne_of_gt (sub_pos.mpr hP)]
        ring
      have hpi : π (k+1)≤(a-1)*((P/(P-1))^(k+1)-1) := by
        apply (mul_le_mul_iff_right₀ (sub_pos.mpr hP)).mp
        nlinarith [hid]
      have hid2 : (a-1)*(P*((P/(P-1))^(k+1)-1)-(k+1)) =
          (a-1)*(P*((P/(P-1))^k-1)-k)+(a-1)*((P/(P-1))^(k+1)-1) := by
        rw [pow_succ]
        field_simp [ne_of_gt (sub_pos.mpr hP)]
        ring
      rw [hS]
      push_cast
      rw [hid2]
      exact add_le_add ih' hpi
  exact hb N le_rfl

private theorem ratio_parameters (d : ℕ) (hd : 1 ≤ d) :
    1 < eTwoDSubOne d ∧ 0 < isoscelesRatio d-1 ∧
      (isoscelesRatio d-1)*(eTwoDSubOne d-1+1/(2*d))=1-1/(4*d) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hP : (1 : ℝ) < 2*d := by linarith
  have hr : (1 : ℝ) < (2*d)/(2*d-1) := by apply (lt_div_iff₀ (by linarith)).mpr; linarith
  have he : 1 < eTwoDSubOne d := by unfold eTwoDSubOne; exact one_lt_pow₀ hr (by omega)
  have hden : 0 < eTwoDSubOne d-1+1/(2*d) := by positivity
  have hsmall : 1/(4*(d:ℝ)) < 1 := by apply (div_lt_one (by positivity)).mpr; linarith
  have hid : (isoscelesRatio d-1)*(eTwoDSubOne d-1+1/(2*d))=1-1/(4*d) := by
    unfold isoscelesRatio
    rw [sub_mul,div_mul_cancel₀ _ (ne_of_gt hden)]
    field_simp [ne_of_gt (by linarith : (0:ℝ) < d)]
    ring
  refine ⟨he,?_,hid⟩
  have hh : 0 < (isoscelesRatio d-1)*(eTwoDSubOne d-1+1/(2*d)) := by rw [hid]; linarith
  exact (mul_pos_iff_of_pos_right hden).mp hh

theorem checked_isosceles_lp_lower_bound (d : ℕ) (hd : 1 ≤ d) (π : ℕ → ℝ) (α : ℝ)
    (hlt : ∀ k : ℕ, 1 ≤ k → k < 2 * d →
      π k * (2 * d : ℝ) + ∑ i ∈ Finset.Icc 1 k, (1 - π i) ≤ α * (k : ℝ))
    (hge : (2 * d : ℝ) + ∑ i ∈ Finset.Icc 1 (2 * d - 1), (1 - π i) + 1 / 2 ≤ α * (2 * d : ℝ)) :
    isoscelesRatio d ≤ α := by
  obtain ⟨he,ha,hid⟩ := ratio_parameters d hd
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hP : (1:ℝ) < 2*d := by linarith
  have hN : ((2*d-1:ℕ):ℝ)=2*(d:ℝ)-1 := by rw [Nat.cast_sub (by omega)]; push_cast; rfl
  have hb := prefix_bound (2*d) α hP π (2*d-1) (fun k hk1 hk => hlt k hk1 (by omega))
  rw [hN] at hb
  change (∑ i∈Finset.Icc 1 (2*d-1), π i) ≤ (α-1)*((2*d)*(eTwoDSubOne d-1)-(2*d-1)) at hb
  have hg := hge
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul,mul_one] at hg
  rw [hN] at hg
  have hden : 0 < eTwoDSubOne d-1+1/(2*d) := by positivity
  unfold isoscelesRatio
  apply (div_le_iff₀ hden).mpr
  apply (mul_le_mul_iff_right₀ (by linarith : (0:ℝ) < 2*d)).mp
  have hl : (eTwoDSubOne d+1/(4*d))*(2*d)=(2*d)*eTwoDSubOne d+1/2 := by
    field_simp [ne_of_gt (by linarith : (0:ℝ) < d)]
    ring
  have hr : (α*(eTwoDSubOne d-1+1/(2*d)))*(2*d)=α*((2*d)*(eTwoDSubOne d-1)+1) := by
    field_simp [ne_of_gt (by linarith : (0:ℝ) < d)]
  nlinarith [hl,hr]
end IsoscelesLPLower

alias checked_isosceles_lp_lower_bound := IsoscelesLPLower.checked_isosceles_lp_lower_bound

end

/- Complete checked body: ThresholdDistribution -/
section

namespace NonuniformCompetitive.IsoscelesProof

open scoped BigOperators
open NonuniformCompetitive.Isosceles

noncomputable def thresholdCDF (d k : ℕ) : ℝ :=
  if k = 0 then 0 else if k < 2*d then
    (isoscelesRatio d-1)*(((2*d:ℝ)/(2*d-1))^k-1) else 1

@[simp] theorem thresholdCDF_zero (d : ℕ) : thresholdCDF d 0 = 0 := by simp [thresholdCDF]

@[simp] theorem thresholdCDF_top (d : ℕ) (hd : 1 ≤ d) : thresholdCDF d (2*d) = 1 := by
  simp [thresholdCDF,show 2*d ≠ 0 by omega]

theorem threshold_lp (d : ℕ) (hd : 1 ≤ d) :
    0 ≤ thresholdCDF d 1 ∧
    (∀ k, 1 ≤ k → k < 2*d → thresholdCDF d k ≤ thresholdCDF d (k+1)) ∧
    (∀ k, 1 ≤ k → k < 2*d → thresholdCDF d k*(2*d:ℝ) +
      ∑ i ∈ Finset.Icc 1 k, (1-thresholdCDF d i) = isoscelesRatio d*k) ∧
    (2*d:ℝ) + (∑ i ∈ Finset.Icc 1 (2*d-1), (1-thresholdCDF d i)) + 1/2 =
      isoscelesRatio d*(2*d) := by
  apply checked_isosceles_lp_attained d hd (thresholdCDF d)
  · intro k hk hk'
    simp [thresholdCDF,show k ≠ 0 by omega,show k < 2*d by omega]
  · exact thresholdCDF_top d hd

theorem isoscelesRatio_ge_one (d : ℕ) (hd : 1 ≤ d) : 1 ≤ isoscelesRatio d := by
  have h := threshold_lp d hd
  have hc := h.2.2.1 1 (by omega) (by omega)
  simp only [Finset.Icc_self,Finset.sum_singleton,Nat.cast_one,mul_one] at hc
  have hp : 0 ≤ thresholdCDF d 1*((2*d:ℝ)-1) :=
    mul_nonneg h.1 (by
      have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd
      linarith)
  nlinarith

theorem thresholdCDF_step_mono (d : ℕ) (hd : 1 ≤ d) {k : ℕ} (hk : k < 2*d) :
    thresholdCDF d k ≤ thresholdCDF d (k+1) := by
  by_cases hz : k=0
  · subst k; simpa using (threshold_lp d hd).1
  · exact (threshold_lp d hd).2.1 k (by omega) hk

theorem thresholdCDF_mono (d : ℕ) (hd : 1 ≤ d) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ 2*d) :
    thresholdCDF d a ≤ thresholdCDF d b := by
  induction b,hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih => exact (ih (by omega)).trans (thresholdCDF_step_mono d hd (by omega))

theorem thresholdCDF_bounds (d : ℕ) (hd : 1 ≤ d) {k : ℕ} (hk : k ≤ 2*d) :
    0 ≤ thresholdCDF d k ∧ thresholdCDF d k ≤ 1 := by
  constructor
  · simpa only [thresholdCDF_zero] using thresholdCDF_mono d hd (Nat.zero_le k) hk
  · simpa only [thresholdCDF_top d hd] using thresholdCDF_mono d hd hk (le_refl (2*d))

noncomputable def thresholdWeight (d : ℕ) (j : Fin (2*d)) : ℝ :=
  thresholdCDF d (j.val+1)-thresholdCDF d j.val

theorem thresholdWeight_nonneg (d : ℕ) (hd : 1 ≤ d) (j : Fin (2*d)) :
    0 ≤ thresholdWeight d j := sub_nonneg.mpr (thresholdCDF_step_mono d hd j.isLt)

theorem thresholdCDF_telescope (d k : ℕ) :
    ∑ j ∈ Finset.range k, (thresholdCDF d (j+1)-thresholdCDF d j)=thresholdCDF d k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ,ih]; ring

theorem thresholdWeight_sum (d : ℕ) (hd : 1 ≤ d) : ∑ j : Fin (2*d), thresholdWeight d j=1 := by
  unfold thresholdWeight
  rw [Fin.sum_univ_eq_sum_range (fun j => thresholdCDF d (j+1)-thresholdCDF d j),
    thresholdCDF_telescope,thresholdCDF_top d hd]

theorem thresholdWeight_cdf (d : ℕ) {k : ℕ} (hk : k ≤ 2*d) :
    ∑ j : Fin (2*d), (if j.val+1 ≤ k then thresholdWeight d j else 0)=thresholdCDF d k := by
  classical
  unfold thresholdWeight
  rw [Fin.sum_univ_eq_sum_range (fun j => if j+1 ≤ k then
    thresholdCDF d (j+1)-thresholdCDF d j else 0)]
  have hset : (Finset.range (2*d)).filter (fun j => j+1 ≤ k) = Finset.range k := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  rw [← Finset.sum_filter,hset,thresholdCDF_telescope]

abbrev Seed (d : ℕ) := Fin (2*d) × Fin 2

noncomputable def seedWeight (d : ℕ) (s : Seed d) : ℝ := thresholdWeight d s.1 / 2

noncomputable def seedMean (d : ℕ) (f : Seed d → ℝ) : ℝ := ∑ s, seedWeight d s*f s

def seedCoin {d : ℕ} (s : Seed d) : Vtx := ⟨s.2.val,by omega⟩

theorem seedWeight_nonneg (d : ℕ) (hd : 1 ≤ d) (s : Seed d) : 0 ≤ seedWeight d s :=
  div_nonneg (thresholdWeight_nonneg d hd s.1) (by norm_num)

theorem seedWeight_sum (d : ℕ) (hd : 1 ≤ d) : ∑ s : Seed d, seedWeight d s = 1 := by
  simp only [seedWeight,Fintype.sum_prod_type,Fin.sum_univ_two]
  have h (j : Fin (2*d)) : thresholdWeight d j/2 + thresholdWeight d j/2 = thresholdWeight d j := by ring
  simp_rw [h]
  exact thresholdWeight_sum d hd

theorem seedMean_const (d : ℕ) (hd : 1 ≤ d) (c : ℝ) : seedMean d (fun _ => c) = c := by
  rw [seedMean,← Finset.sum_mul,seedWeight_sum d hd,one_mul]

theorem seedMean_add (d : ℕ) (f g : Seed d → ℝ) :
    seedMean d (fun s => f s+g s)=seedMean d f+seedMean d g := by
  simp [seedMean,mul_add,Finset.sum_add_distrib]

theorem seedMean_sub (d : ℕ) (f g : Seed d → ℝ) :
    seedMean d (fun s => f s-g s)=seedMean d f-seedMean d g := by
  simp [seedMean,mul_sub,Finset.sum_sub_distrib]

theorem seedMean_mul (d : ℕ) (c : ℝ) (f : Seed d → ℝ) :
    seedMean d (fun s => c*f s)=c*seedMean d f := by
  simp [seedMean,Finset.mul_sum,mul_left_comm]

theorem seedMean_indicator (d : ℕ) {k : ℕ} (hk : k ≤ 2*d) :
    seedMean d (fun s => if s.1.val+1 ≤ k then 1 else 0)=thresholdCDF d k := by
  simp only [seedMean,seedWeight,Fintype.sum_prod_type,Fin.sum_univ_two]
  have h (j : Fin (2*d)) : thresholdWeight d j/2*(if j.val+1 ≤ k then 1 else 0) +
      thresholdWeight d j/2*(if j.val+1 ≤ k then 1 else 0) =
      if j.val+1 ≤ k then thresholdWeight d j else 0 := by split_ifs <;> ring
  simp_rw [h]
  exact thresholdWeight_cdf d hk

theorem seedMean_coin (d : ℕ) (hd : 1 ≤ d) (x : Vtx) (hx : x ≠ 2) :
    seedMean d (fun s => if seedCoin s=x then 0 else 1)=1/2 := by
  fin_cases x <;> norm_num [Fin.ext_iff] at hx
  all_goals simp [seedMean,seedWeight,seedCoin,Fintype.sum_prod_type,Fin.sum_univ_two,
    ← Finset.sum_div,thresholdWeight_sum d hd]

end NonuniformCompetitive.IsoscelesProof
end

/- Complete checked body: WorkFunctions -/
section

namespace NonuniformCompetitive.IsoscelesProof

open scoped BigOperators

def WorkLip (d : ℕ) (w : Vtx → ℝ) : Prop :=
  ∀ h g, w h ≤ w g + triDist d h g

def workValue (d : ℕ) (w : Vtx → ℝ) (C : Fin 2 → Vtx) : ℝ :=
  min (w 0 + pairMatch d 0 C) (min (w 1 + pairMatch d 1 C) (w 2 + pairMatch d 2 C))

def workStep (d : ℕ) (w : Vtx → ℝ) (r h : Vtx) : ℝ :=
  if r = 0 then min (w 1 + triDist d 1 h) (w 2 + triDist d 2 h)
  else if r = 1 then min (w 0 + triDist d 0 h) (w 2 + triDist d 2 h)
  else min (w 0 + triDist d 0 h) (w 1 + triDist d 1 h)

theorem workValue_le (d : ℕ) (w : Vtx → ℝ) (C : Fin 2 → Vtx) (h : Vtx) :
    workValue d w C ≤ w h + pairMatch d h C := by
  fin_cases h
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

theorem workValue_attained (d : ℕ) (w : Vtx → ℝ) (C : Fin 2 → Vtx) :
    ∃ h, workValue d w C = w h + pairMatch d h C := by
  unfold workValue
  rcases le_total (w 0 + pairMatch d 0 C)
    (min (w 1 + pairMatch d 1 C) (w 2 + pairMatch d 2 C)) with h | h
  · exact ⟨0,min_eq_left h⟩
  · rw [min_eq_right h]
    rcases le_total (w 1 + pairMatch d 1 C) (w 2 + pairMatch d 2 C) with h | h
    · exact ⟨1,min_eq_left h⟩
    · exact ⟨2,min_eq_right h⟩

theorem workValue_move (d : ℕ) (hd : 1 ≤ d) (w : Vtx → ℝ)
    (C D : Fin 2 → Vtx) : workValue d w D ≤ workValue d w C + triMove d C D := by
  obtain ⟨h,hh⟩ := workValue_attained d w C
  have hm := pairMatch_move d hd h C D
  have hv := workValue_le d w D h
  rw [hh]
  linarith

theorem workValue_add (d : ℕ) (w : Vtx → ℝ) (a : ℝ) (C : Fin 2 → Vtx) :
    workValue d (fun h => a + w h) C = a + workValue d w C := by
  simp only [workValue, add_assoc, min_add_add_left]

theorem workValue_nonneg (d : ℕ) (w : Vtx → ℝ) (hw : ∀ h, 0 ≤ w h)
    (C : Fin 2 → Vtx) : 0 ≤ workValue d w C := by
  obtain ⟨h,hh⟩ := workValue_attained d w C
  rw [hh]
  exact add_nonneg (hw h) (pairMatch_nonneg d h C)

theorem workStep_le (d : ℕ) (w : Vtx → ℝ) (r h g : Vtx) (hg : g ≠ r) :
    workStep d w r h ≤ w g + triDist d g h := by
  fin_cases r <;> fin_cases g <;> simp [workStep] at *

theorem workStep_attained (d : ℕ) (w : Vtx → ℝ) (r h : Vtx) :
    ∃ g, g ≠ r ∧ workStep d w r h = w g + triDist d g h := by
  fin_cases r
  · by_cases hh : w 1 + triDist d 1 h ≤ w 2 + triDist d 2 h
    · exact ⟨1,by decide,by simp [workStep,min_eq_left hh]⟩
    · exact ⟨2,by decide,by simp [workStep,min_eq_right (le_of_not_ge hh)]⟩
  · by_cases hh : w 0 + triDist d 0 h ≤ w 2 + triDist d 2 h
    · exact ⟨0,by decide,by simp [workStep,min_eq_left hh]⟩
    · exact ⟨2,by decide,by simp [workStep,min_eq_right (le_of_not_ge hh)]⟩
  · by_cases hh : w 0 + triDist d 0 h ≤ w 1 + triDist d 1 h
    · exact ⟨0,by decide,by simp [workStep,min_eq_left hh]⟩
    · exact ⟨1,by decide,by simp [workStep,min_eq_right (le_of_not_ge hh)]⟩

theorem workStep_lip (d : ℕ) (hd : 1 ≤ d) (w : Vtx → ℝ) (r : Vtx) :
    WorkLip d (workStep d w r) := by
  intro h g
  obtain ⟨q,hq,heq⟩ := workStep_attained d w r g
  have hl := workStep_le d w r h q hq
  have ht := triDist_triangle d hd q g h
  rw [triDist_symm d g h] at ht
  rw [heq]
  linarith

/-- A serving configuration can be reached through a serving pair without additional movement. -/
theorem serving_pair_path (d : ℕ) (hd : 1 ≤ d) (h r : Vtx) (C : Fin 2 → Vtx)
    (hC : ∃ i, C i = r) :
    ∃ g, g ≠ r ∧ triDist d h g + pairMatch d g C ≤ pairMatch d h C := by
  have hCeq : C = ![C 0,C 1] := by ext i; fin_cases i <;> rfl
  rw [hCeq] at hC ⊢
  generalize C 0 = x at hC ⊢
  generalize C 1 = y at hC ⊢
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  fin_cases h <;> fin_cases r <;> fin_cases x <;> fin_cases y <;>
    simp [Fin.exists_fin_two] at hC
  all_goals first
    | (refine ⟨0, ?_, ?_⟩
       · decide
       · simp [triDist,pairMatch,triMove,pairConf,swapConf,Fin.sum_univ_two,Fin.ext_iff,min_def]
         all_goals split_ifs <;> linarith)
    | (refine ⟨1, ?_, ?_⟩
       · decide
       · simp [triDist,pairMatch,triMove,pairConf,swapConf,Fin.sum_univ_two,Fin.ext_iff,min_def]
         all_goals split_ifs <;> linarith)
    | (refine ⟨2, ?_, ?_⟩
       · decide
       · simp [triDist,pairMatch,triMove,pairConf,swapConf,Fin.sum_univ_two,Fin.ext_iff])

theorem workValue_step_serves (d : ℕ) (hd : 1 ≤ d) (w : Vtx → ℝ)
    (hw : WorkLip d w) (r : Vtx) (C : Fin 2 → Vtx) (hC : ∃ i, C i = r) :
    workValue d (workStep d w r) C ≤ workValue d w C := by
  obtain ⟨h,hh⟩ := workValue_attained d w C
  obtain ⟨g,hg,hpath⟩ := serving_pair_path d hd h r C hC
  have hval := workValue_le d (workStep d w r) C g
  have hs := workStep_le d w r g g hg
  simp only [triDist_self,add_zero] at hs
  have hl := hw g h
  rw [triDist_symm d g h] at hl
  rw [hh]
  linarith

end NonuniformCompetitive.IsoscelesProof
end

/- Complete checked body: WorkStages -/
section

namespace NonuniformCompetitive.IsoscelesProof

inductive Stage where
  | run (x : Vtx) (k : ℕ)
  | fork
  deriving DecidableEq

def Stage.Valid (d : ℕ) : Stage → Prop
  | .run x k => x ≠ 2 ∧ k ≤ 2*d
  | .fork => True

def stageWorkNat (d : ℕ) : Stage → Vtx → ℕ
  | .run x k, h => if h = 2 then d else if h = nearOther x then min k (2*d) else min (k+1) (2*d)
  | .fork, h => if h = 2 then d else 0

def stageWork (d : ℕ) (s : Stage) (h : Vtx) : ℝ := stageWorkNat d s h

def stageStep (d : ℕ) : Stage → Vtx → Stage
  | .run x k, r => if r = 2 then (if k < 2*d then .run x 0 else .fork)
      else if r = x then .run x k else .run r (min (k+1) (2*d))
  | .fork, r => if r = 2 then .fork else .run r 0

def stageGain (d : ℕ) : Stage → Vtx → ℕ
  | .run _ k, r => if r = 2 then min k (2*d) else 0
  | .fork, _ => 0

def initialStage : Stage := .run 0 0

theorem initialStage_valid (d : ℕ) : initialStage.Valid d := by
  norm_num [initialStage,Stage.Valid,Fin.ext_iff]

theorem stageStep_valid (d : ℕ) (s : Stage) (hs : s.Valid d) (r : Vtx) :
    (stageStep d s r).Valid d := by
  cases s with
  | fork => simp only [stageStep]; split_ifs <;> simp_all [Stage.Valid]
  | run x k =>
    obtain ⟨hx,hk⟩ := hs
    simp only [stageStep]
    split_ifs <;> simp_all [Stage.Valid]

theorem initialStage_work (d : ℕ) (hd : 1 ≤ d) (h : Vtx) :
    stageWork d initialStage h = triDist d 1 h := by
  have hm : min 1 (2*d)=1 := min_eq_left (by omega)
  fin_cases h <;> simp [stageWork,stageWorkNat,initialStage,nearOther,triDist,Fin.ext_iff,hm]

theorem initialStage_lip (d : ℕ) (hd : 1 ≤ d) : WorkLip d (stageWork d initialStage) := by
  intro h g
  rw [initialStage_work d hd,initialStage_work d hd]
  exact (triDist_triangle d hd 1 g h).trans_eq (by rw [triDist_symm d g h])

theorem stageWork_nonneg (d : ℕ) (s : Stage) (h : Vtx) : 0 ≤ stageWork d s h :=
  Nat.cast_nonneg _

def triNat (d : ℕ) (x y : Vtx) : ℕ :=
  if x=y then 0 else if x=2 ∨ y=2 then d else 1

def workNatStep (d : ℕ) (w : Vtx → ℕ) (r h : Vtx) : ℕ :=
  if r=0 then min (w 1+triNat d 1 h) (w 2+triNat d 2 h)
  else if r=1 then min (w 0+triNat d 0 h) (w 2+triNat d 2 h)
  else min (w 0+triNat d 0 h) (w 1+triNat d 1 h)

theorem workStep_cast (d : ℕ) (w : Vtx → ℕ) (r h : Vtx) :
    workStep d (fun a => (w a : ℝ)) r h = (workNatStep d w r h : ℝ) := by
  fin_cases r <;> fin_cases h <;>
    simp [workStep,workNatStep,triNat,triDist,Fin.ext_iff,min_add_add_right]

theorem stageWorkNat_step (d : ℕ) (hd : 1 ≤ d) (s : Stage) (hs : s.Valid d) (r h : Vtx) :
    workNatStep d (stageWorkNat d s) r h = stageGain d s r + stageWorkNat d (stageStep d s r) h := by
  cases s with
  | fork =>
    fin_cases r <;> fin_cases h <;>
      simp [workNatStep,stageWorkNat,stageStep,stageGain,triNat,nearOther,Fin.ext_iff]
    all_goals omega
  | run x k =>
    obtain ⟨hx,hk⟩ := hs
    fin_cases x <;> norm_num [Fin.ext_iff] at hx
    all_goals fin_cases r <;> fin_cases h <;> by_cases hl : k < 2*d
    all_goals simp [workNatStep,stageWorkNat,stageStep,stageGain,triNat,nearOther,Fin.ext_iff,hl]
    all_goals omega

/-- The exact extended-work-function update, including the long-return fork. -/
theorem stageWork_step (d : ℕ) (hd : 1 ≤ d) (s : Stage) (hs : s.Valid d) (r h : Vtx) :
    workStep d (stageWork d s) r h = (stageGain d s r : ℝ) + stageWork d (stageStep d s r) h := by
  change workStep d (fun a => (stageWorkNat d s a : ℝ)) r h = _
  rw [workStep_cast,stageWorkNat_step d hd s hs r h,Nat.cast_add]
  rfl

structure WorkState where
  bank : ℕ
  stage : Stage

def workTransition (d : ℕ) (s : WorkState) (r : Vtx) : WorkState :=
  ⟨s.bank + stageGain d s.stage r, stageStep d s.stage r⟩

def workRun (d : ℕ) (h : List Vtx) : WorkState :=
  h.foldl (workTransition d) ⟨0,initialStage⟩

@[simp] theorem workRun_nil (d : ℕ) : workRun d [] = ⟨0,initialStage⟩ := rfl

theorem workRun_append_one (d : ℕ) (h : List Vtx) (r : Vtx) :
    workRun d (h ++ [r]) = workTransition d (workRun d h) r := by
  simp [workRun,List.foldl_append]

theorem workRun_valid (d : ℕ) (h : List Vtx) : (workRun d h).stage.Valid d := by
  induction h using List.reverseRecOn with
  | nil => exact initialStage_valid d
  | append_singleton h r ih =>
    rw [workRun_append_one]
    exact stageStep_valid d _ ih r

theorem workRun_lip (d : ℕ) (hd : 1 ≤ d) (h : List Vtx) :
    WorkLip d (stageWork d (workRun d h).stage) := by
  induction h using List.reverseRecOn with
  | nil => exact initialStage_lip d hd
  | append_singleton h r _ih =>
    have hw := workStep_lip d hd (stageWork d (workRun d h).stage) r
    intro a b
    have hh := hw a b
    rw [stageWork_step d hd _ (workRun_valid d h), stageWork_step d hd _ (workRun_valid d h)] at hh
    rw [workRun_append_one]
    change stageWork d (stageStep d (workRun d h).stage r) a ≤
      stageWork d (stageStep d (workRun d h).stage r) b + triDist d a b
    linarith

end NonuniformCompetitive.IsoscelesProof
end

/- Complete checked body: ThresholdPolicy -/
section

namespace NonuniformCompetitive.IsoscelesProof

open scoped BigOperators

noncomputable def seedHole {d : ℕ} (z : Seed d) : Stage → Vtx
  | .run x k => if z.1.val+1 ≤ k then 2 else nearOther x
  | .fork => nearOther (seedCoin z)

@[simp] theorem seedHole_initial {d : ℕ} (z : Seed d) : seedHole z initialStage = 1 := by
  simp [seedHole,initialStage,nearOther]

theorem nearOther_ne_self (x : Vtx) (hx : x ≠ 2) : nearOther x ≠ x := by
  fin_cases x <;> norm_num [nearOther,Fin.ext_iff] at *

theorem seedHole_run_ne {d : ℕ} (z : Seed d) (x : Vtx) (k : ℕ) (hx : x ≠ 2) :
    seedHole z (.run x k) ≠ x := by
  by_cases hj : z.1.val+1 ≤ k
  · simpa [seedHole,hj] using Ne.symm hx
  · simpa [seedHole,hj] using nearOther_ne_self x hx

theorem seedHole_serves (d : ℕ) (_hd : 1 ≤ d) (s : Stage) (hs : s.Valid d) (r : Vtx) (z : Seed d) :
    seedHole z (stageStep d s r) ≠ r := by
  cases s with
  | fork =>
    by_cases hr : r=2
    · subst r
      simpa [stageStep,seedHole] using nearOther_ne_far (seedCoin z)
    · simpa [stageStep,hr] using seedHole_run_ne z r 0 hr
  | run x k =>
    have hx := hs.1
    by_cases hr : r=2
    · subst r
      by_cases hl : k < 2*d
      · simpa [stageStep,seedHole,hl] using nearOther_ne_far x
      · simpa [stageStep,seedHole,hl] using nearOther_ne_far (seedCoin z)
    · by_cases hrx : r=x
      · subst r
        simpa [stageStep,hx] using seedHole_run_ne z x k hx
      · simpa [stageStep,hr,hrx] using seedHole_run_ne z r (min (k+1) (2*d)) hr

noncomputable def thresholdHole {d : ℕ} (z : Seed d) (h : List Vtx) : Vtx :=
  seedHole z (workRun d h).stage

theorem thresholdHole_serves (d : ℕ) (hd : 1 ≤ d) (z : Seed d) (h : List Vtx) (r : Vtx) :
    thresholdHole z (h++[r]) ≠ r := by
  rw [thresholdHole,workRun_append_one]
  exact seedHole_serves d hd _ (workRun_valid d h) r z

noncomputable def thresholdPolicy (d : ℕ) (hd : 1 ≤ d) (z : Seed d) : TriPolicy :=
  holePolicy (thresholdHole z) (thresholdHole_serves d hd z) (pairConf 1)
    (by simp [thresholdHole,FitsPair])

@[simp] theorem thresholdPolicy_initial (d : ℕ) (hd : 1 ≤ d) (z : Seed d) :
    (thresholdPolicy d hd z).conf [] = pairConf 1 := rfl

noncomputable def seedStepCost (d : ℕ) (s : Stage) (r : Vtx) (z : Seed d) : ℝ :=
  match s with
  | .run x k => if r=2 then
      (if k < 2*d then (if z.1.val+1 ≤ k then d else 0) else d)
    else if r=x then 0 else
      (if z.1.val+1 ≤ k then 0 else if z.1.val+1 ≤ min (k+1) (2*d) then d else 1)
  | .fork => if r=2 then 0 else if seedCoin z=r then 0 else 1

theorem seedStepCost_eq (d : ℕ) (hd : 1 ≤ d) (s : Stage) (hs : s.Valid d) (r : Vtx) (z : Seed d) :
    triDist d (seedHole z s) (seedHole z (stageStep d s r)) = seedStepCost d s r z := by
  have hz := z.1.isLt
  have hc := z.2.isLt
  rcases z with ⟨j,b⟩
  cases s with
  | fork =>
    fin_cases b <;> fin_cases r <;>
      simp [seedHole,seedStepCost,stageStep,nearOther,seedCoin,triDist]
  | run x k =>
    obtain ⟨hx,hk⟩ := hs
    fin_cases x <;> norm_num [Fin.ext_iff] at hx
    all_goals fin_cases b <;> fin_cases r <;>
      simp [seedHole,seedStepCost,stageStep,nearOther,seedCoin,triDist]
    all_goals split_ifs <;> norm_num [Fin.ext_iff] at * <;> omega

theorem thresholdPolicy_step_cost (d : ℕ) (hd : 1 ≤ d) (z : Seed d) (h : List Vtx) (r : Vtx) :
    triMove d ((thresholdPolicy d hd z).conf h) ((thresholdPolicy d hd z).conf (h++[r])) =
      seedStepCost d (workRun d h).stage r z := by
  change triMove d (holeRun (thresholdHole z) (pairConf 1) h).2
      (holeRun (thresholdHole z) (pairConf 1) (h++[r])).2 = _
  rw [holeRun_append_one]
  simp only [holeTransition,holeRun_prefix]
  rw [pairChange_cost d _ _ _ (holeRun_fits (thresholdHole z) (pairConf 1)
    (by simp [thresholdHole,FitsPair]) h)]
  simp only [thresholdHole,workRun_append_one,workTransition]
  exact seedStepCost_eq d hd _ (workRun_valid d h) r z

end NonuniformCompetitive.IsoscelesProof
end

/- Complete checked body: ThresholdReserve -/
section

namespace NonuniformCompetitive.IsoscelesProof

open scoped BigOperators
open NonuniformCompetitive.Isosceles

noncomputable def rentSum (d k : ℕ) : ℝ := ∑ i ∈ Finset.Icc 1 k, (1-thresholdCDF d i)
noncomputable def runExpense (d k : ℕ) : ℝ := d*thresholdCDF d k + rentSum d k
noncomputable def stageReserve (d : ℕ) : Stage → ℝ
  | .run _ k => -runExpense d k
  | .fork => 1/2

@[simp] theorem rentSum_zero (d : ℕ) : rentSum d 0 = 0 := by simp [rentSum]
@[simp] theorem runExpense_zero (d : ℕ) : runExpense d 0 = 0 := by simp [runExpense]

theorem rentSum_succ (d k : ℕ) : rentSum d (k+1)=rentSum d k+1-thresholdCDF d (k+1) := by
  unfold rentSum
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k+1)]
  ring

theorem runExpense_succ (d k : ℕ) :
    runExpense d (k+1)-runExpense d k =
      d*(thresholdCDF d (k+1)-thresholdCDF d k)+1-thresholdCDF d (k+1) := by
  rw [runExpense,runExpense,rentSum_succ]
  ring

theorem runExpense_short (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk : k < 2*d) :
    runExpense d k + d*thresholdCDF d k = isoscelesRatio d*k := by
  by_cases hz : k=0
  · subst k; simp
  · have h := (threshold_lp d hd).2.2.1 k (by omega) hk
    change thresholdCDF d k*(2*d:ℝ)+rentSum d k=isoscelesRatio d*k at h
    unfold runExpense
    nlinarith

theorem runExpense_long (d : ℕ) (hd : 1 ≤ d) :
    runExpense d (2*d)+d+1/2 = isoscelesRatio d*(2*d) := by
  have hsum := rentSum_succ d (2*d-1)
  rw [show 2*d-1+1=2*d by omega,thresholdCDF_top d hd] at hsum
  have h := (threshold_lp d hd).2.2.2
  change (2*d:ℝ)+rentSum d (2*d-1)+1/2=isoscelesRatio d*(2*d) at h
  unfold runExpense
  rw [thresholdCDF_top d hd]
  nlinarith

theorem stageReserve_lower (d : ℕ) (hd : 1 ≤ d) (s : Stage) (hs : s.Valid d) :
    -(3*d:ℝ) ≤ stageReserve d s := by
  cases s with
  | fork =>
    have hd0 : (0:ℝ) ≤ d := Nat.cast_nonneg d
    simp only [stageReserve]
    linarith
  | run x k =>
    have hk := hs.2
    have hb := thresholdCDF_bounds d hd hk
    have hr : rentSum d k ≤ k := by
      calc rentSum d k ≤ ∑ _i ∈ Finset.Icc 1 k, (1:ℝ) := by
             apply Finset.sum_le_sum
             intro i hi
             have hh := (thresholdCDF_bounds d hd ((Finset.mem_Icc.mp hi).2.trans hk)).1
             linarith
           _ = k := by simp
    have hkR : (k:ℝ) ≤ 2*d := by exact_mod_cast hk
    have hm := mul_le_mul_of_nonneg_left hb.2 (Nat.cast_nonneg d)
    simp only [stageReserve,runExpense]
    nlinarith

noncomputable def meanStepCost (d : ℕ) (s : Stage) (r : Vtx) : ℝ :=
  match s with
  | .run x k => if r=2 then (if k < 2*d then d*thresholdCDF d k else d)
      else if r=x then 0 else runExpense d (min (k+1) (2*d))-runExpense d k
  | .fork => if r=2 then 0 else 1/2

theorem seedStepCost_mean (d : ℕ) (hd : 1 ≤ d) (s : Stage) (hs : s.Valid d) (r : Vtx) :
    seedMean d (fun z => seedStepCost d s r z)=meanStepCost d s r := by
  cases s with
  | fork =>
    by_cases hr : r=2
    · simp [seedStepCost,meanStepCost,hr,seedMean_const d hd]
    · simp only [seedStepCost,meanStepCost,if_neg hr]
      exact seedMean_coin d hd r hr
  | run x k =>
    have hk := hs.2
    by_cases hr : r=2
    · by_cases hl : k < 2*d
      · have he : (fun z : Seed d => seedStepCost d (.run x k) r z)=
            fun z => (d:ℝ)*(if z.1.val+1 ≤ k then 1 else 0) := by
          funext z
          simp only [seedStepCost,if_pos hr,if_pos hl]
          split_ifs <;> ring
        rw [he,seedMean_mul,seedMean_indicator d hk]
        simp [meanStepCost,hr,hl]
      · simp [seedStepCost,meanStepCost,hr,hl,seedMean_const d hd]
    · by_cases hrx : r=x
      · simp only [seedStepCost,if_neg hr,if_pos hrx,meanStepCost]
        exact seedMean_const d hd 0
      · by_cases hl : k < 2*d
        · have hn : min (k+1) (2*d)=k+1 := min_eq_left (by omega)
          have he : (fun z : Seed d => seedStepCost d (.run x k) r z)=
              fun z => (d:ℝ)*((if z.1.val+1 ≤ k+1 then 1 else 0)-(if z.1.val+1 ≤ k then 1 else 0))+
                (1-(if z.1.val+1 ≤ k+1 then 1 else 0)) := by
            funext z
            simp only [seedStepCost,if_neg hr,if_neg hrx,hn]
            split_ifs <;> first | omega | ring
          rw [he,seedMean_add,seedMean_mul,seedMean_sub,seedMean_sub,
            seedMean_indicator d (by omega),seedMean_indicator d hk,seedMean_const d hd]
          simp only [meanStepCost,if_neg hr,if_neg hrx,hn,runExpense_succ]
          ring
        · have hk' : k=2*d := by omega
          have he : (fun z : Seed d => seedStepCost d (.run x k) r z)=fun _ => 0 := by
            funext z
            simp [seedStepCost,hr,hrx,show z.1.val+1 ≤ k by have := z.1.isLt; omega]
          rw [he,seedMean_const d hd]
          simp [meanStepCost,hr,hrx,hk']

theorem meanStep_reserve (d : ℕ) (hd : 1 ≤ d) (s : Stage) (hs : s.Valid d) (r : Vtx) :
    meanStepCost d s r+stageReserve d (stageStep d s r)=
      isoscelesRatio d*(stageGain d s r)+stageReserve d s := by
  cases s with
  | fork => by_cases hr : r=2 <;> simp [meanStepCost,stageReserve,stageStep,stageGain,hr]
  | run x k =>
    have hk := hs.2
    by_cases hr : r=2
    · by_cases hl : k < 2*d
      · simp only [meanStepCost,stageReserve,stageStep,stageGain,if_pos hr,if_pos hl,
          Nat.min_eq_left hk,runExpense_zero,neg_zero,add_zero]
        have h := runExpense_short d hd k hl
        linarith
      · have hk' : k=2*d := by omega
        simp only [meanStepCost,stageStep,stageGain,if_pos hr,if_neg hl,stageReserve,Nat.min_eq_left hk]
        subst k
        have h := runExpense_long d hd
        push_cast
        linarith
    · simp only [meanStepCost,stageStep,stageGain,if_neg hr]
      by_cases hrx : r=x
      · simp only [if_pos hrx,stageReserve,Nat.cast_zero,mul_zero,zero_add]
      · simp only [if_neg hrx,stageReserve,Nat.cast_zero,mul_zero,zero_add]
        ring

end NonuniformCompetitive.IsoscelesProof
end

/- Complete checked body: WorkBenchmark -/
section

namespace NonuniformCompetitive.IsoscelesProof

open scoped BigOperators

theorem triMove_le_two (d : ℕ) (hd : 1 ≤ d) (C D : Fin 2 → Vtx) :
    triMove d C D ≤ 2*d := by
  have h0 := triDist_le d hd (C 0) (D 0)
  have h1 := triDist_le d hd (C 1) (D 1)
  simp only [triMove,Fin.sum_univ_two]
  linarith

theorem initialWorkValue_le (d : ℕ) (hd : 1 ≤ d) (C : Fin 2 → Vtx) :
    workValue d (stageWork d initialStage) C ≤ 2*d := by
  have hw := workValue_le d (stageWork d initialStage) C 1
  rw [initialStage_work d hd,triDist_self,zero_add] at hw
  exact hw.trans ((min_le_left _ _).trans (triMove_le_two d hd _ _))

theorem workValue_transition (d : ℕ) (hd : 1 ≤ d) (h : List Vtx) (r : Vtx)
    (C D : Fin 2 → Vtx) (hD : ∃ i, D i = r) :
    ((workRun d (h++[r])).bank : ℝ) + workValue d (stageWork d (workRun d (h++[r])).stage) D
      ≤ (workRun d h).bank + workValue d (stageWork d (workRun d h).stage) C + triMove d C D := by
  have hs := workValue_step_serves d hd (stageWork d (workRun d h).stage)
    (workRun_lip d hd h) r D hD
  have hm := workValue_move d hd (stageWork d (workRun d h).stage) C D
  have heq : workStep d (stageWork d (workRun d h).stage) r =
      fun a => (stageGain d (workRun d h).stage r : ℝ) + stageWork d (stageStep d (workRun d h).stage r) a :=
    funext fun a => stageWork_step d hd _ (workRun_valid d h) r a
  rw [heq,workValue_add] at hs
  rw [workRun_append_one]
  simp only [workTransition,Nat.cast_add]
  linarith

theorem bank_le_schedule (d : ℕ) (hd : 1 ≤ d) (h : List Vtx)
    (S : ℕ → Fin 2 → Vtx) (hs : ∀ j (hj : j < h.length), ∃ i, S (j+1) i = h[j]) :
    ((workRun d h).bank : ℝ) ≤ (∑ j ∈ Finset.range h.length, triMove d (S j) (S (j+1))) + 2*d := by
  have hind : ∀ t, t ≤ h.length →
      ((workRun d (h.take t)).bank : ℝ) +
          workValue d (stageWork d (workRun d (h.take t)).stage) (S t)
        ≤ (∑ j ∈ Finset.range t, triMove d (S j) (S (j+1))) + 2*d := by
    intro t
    induction t with
    | zero => intro _; simpa using initialWorkValue_le d hd (S 0)
    | succ t ih =>
      intro ht
      have ht' : t < h.length := by omega
      have hi := ih (by omega)
      have hn := workValue_transition d hd (h.take t) h[t] (S t) (S (t+1)) (hs t ht')
      rw [← List.take_succ_eq_append_getElem ht'] at hn
      rw [Finset.sum_range_succ]
      linarith
  have hi := hind h.length le_rfl
  simp only [List.take_length] at hi
  have hz := workValue_nonneg d (stageWork d (workRun d h).stage)
    (stageWork_nonneg d _) (S h.length)
  linarith

/-- The work bank is a lower bound for the original labelled-schedule optimum up to one fixed initial allowance. -/
theorem bank_le_offline {M : Type*} [MetricSpace M] (d : ℕ) (hd : 1 ≤ d)
    (e : Vtx ≃ M) (he : ∀ x y, dist (e x) (e y) = triDist d x y)
    (C₀ : KServer.Config 2 M) (h : List Vtx) :
    ((workRun d h).bank : ℝ) ≤ KServer.offlineCost C₀ (h.map e) + 2*d := by
  classical
  let σ := h.map e
  have hex : Set.Nonempty {c : ℝ | ∃ S : ℕ → KServer.Config 2 M,
      KServer.ServesFrom C₀ σ S ∧ c = ∑ j ∈ Finset.range σ.length, KServer.moveCost (S j) (S (j+1))} := by
    let S : ℕ → KServer.Config 2 M := fun t => if t=0 then C₀ else fun _ => σ[t-1]?.getD (C₀ 0)
    refine ⟨_,S,?_,rfl⟩
    constructor
    · simp [S]
    · intro j
      refine ⟨0,?_⟩
      simp [S]
  have hl : ((workRun d h).bank : ℝ) - 2*d ≤ KServer.offlineCost C₀ σ := by
    apply le_csInf hex
    rintro z ⟨S,hS,rfl⟩
    let T : ℕ → Fin 2 → Vtx := fun j i => e.symm (S j i)
    have ht : ∀ j (hj : j < h.length), ∃ i, T (j+1) i = h[j] := by
      intro j hj
      obtain ⟨i,hi⟩ := hS.2 ⟨j,by simpa [σ] using hj⟩
      refine ⟨i,?_⟩
      apply e.injective
      simpa [T,σ] using hi
    have hb := bank_le_schedule d hd h T ht
    have hc (j : ℕ) : triMove d (T j) (T (j+1)) = KServer.moveCost (S j) (S (j+1)) := by
      unfold triMove KServer.moveCost
      apply Finset.sum_congr rfl
      intro i _
      simpa [T] using (he (e.symm (S j i)) (e.symm (S (j+1) i))).symm
    simp only [hc] at hb
    simpa [σ] using (sub_le_iff_le_add.mpr hb)
  linarith

end NonuniformCompetitive.IsoscelesProof
end

/- Complete checked body: ThresholdMean -/
section

namespace NonuniformCompetitive.IsoscelesProof

open scoped BigOperators
open NonuniformCompetitive.Isosceles

theorem seedMean_mono (d : ℕ) (hd : 1 ≤ d) (f g : Seed d → ℝ) (h : ∀ z, f z ≤ g z) :
    seedMean d f ≤ seedMean d g :=
  Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (h z) (seedWeight_nonneg d hd z)

theorem threshold_mean_reserve (d : ℕ) (hd : 1 ≤ d) (h : List Vtx) :
    seedMean d (fun z => triCost d (thresholdPolicy d hd z) h)+stageReserve d (workRun d h).stage =
      isoscelesRatio d*(workRun d h).bank := by
  induction h using List.reverseRecOn with
  | nil => simp [triCost,seedMean,stageReserve,initialStage]
  | append_singleton h r ih =>
    have he : (fun z : Seed d => triCost d (thresholdPolicy d hd z) (h++[r]))=
        fun z => triCost d (thresholdPolicy d hd z) h+seedStepCost d (workRun d h).stage r z := by
      funext z
      rw [triCost_append_one,thresholdPolicy_step_cost]
    rw [he,seedMean_add,seedStepCost_mean d hd _ (workRun_valid d h)]
    have hr := meanStep_reserve d hd _ (workRun_valid d h) r
    rw [workRun_append_one]
    simp only [workTransition,Nat.cast_add]
    nlinarith

theorem threshold_mean_bound (d : ℕ) (hd : 1 ≤ d) (h : List Vtx) :
    seedMean d (fun z => triCost d (thresholdPolicy d hd z) h) ≤
      isoscelesRatio d*(workRun d h).bank+3*d := by
  have he := threshold_mean_reserve d hd h
  have hl := stageReserve_lower d hd _ (workRun_valid d h)
  linarith

def changeInitial (A : TriPolicy) (C₀ : Fin 2 → Vtx) : TriPolicy where
  conf h := if h=[] then C₀ else A.conf h
  serves h r := by simpa using A.serves h r

@[simp] theorem changeInitial_nil (A : TriPolicy) (C₀ : Fin 2 → Vtx) :
    (changeInitial A C₀).conf []=C₀ := by simp [changeInitial]

theorem changeInitial_cost (d : ℕ) (hd : 1 ≤ d) (A : TriPolicy) (C₀ : Fin 2 → Vtx) (h : List Vtx) :
    triCost d (changeInitial A C₀) h ≤ triCost d A h+2*d := by
  by_cases hh : h=[]
  · subst h; simp
  · have hlen : 0 < h.length := List.length_pos_iff.mpr hh
    have hs : ∀ j ∈ Finset.range h.length,
        triMove d ((changeInitial A C₀).conf (h.take j)) ((changeInitial A C₀).conf (h.take (j+1))) ≤
          triMove d (A.conf (h.take j)) (A.conf (h.take (j+1)))+(if j=0 then 2*d else 0) := by
      intro j _hj
      have ht : h.take (j+1) ≠ [] := by simp [List.take_eq_nil_iff,hh]
      by_cases hj : j=0
      · subst j
        simp only [changeInitial,List.take_zero,if_true,if_neg ht,Nat.zero_add,Nat.cast_mul,Nat.cast_ofNat]
        have hu := triMove_le_two d hd C₀ (A.conf (h.take 1))
        have hz := triMove_nonneg d (A.conf []) (A.conf (h.take 1))
        linarith
      · have ht0 : h.take j ≠ [] := by simp [List.take_eq_nil_iff,hh,hj]
        simp [changeInitial,hj,ht,ht0]
    have hsum := Finset.sum_le_sum hs
    simpa [triCost,Finset.sum_add_distrib,hlen] using hsum

theorem threshold_mean_from (d : ℕ) (hd : 1 ≤ d) (C₀ : Fin 2 → Vtx) (h : List Vtx) :
    seedMean d (fun z => triCost d (changeInitial (thresholdPolicy d hd z) C₀) h) ≤
      isoscelesRatio d*(workRun d h).bank+5*d := by
  have hm := seedMean_mono d hd _ _ (fun z => changeInitial_cost d hd (thresholdPolicy d hd z) C₀ h)
  rw [seedMean_add,seedMean_const d hd] at hm
  have hb := threshold_mean_bound d hd h
  linarith

end NonuniformCompetitive.IsoscelesProof
end

/- Complete checked body: RandomizedUpper -/
section

open MeasureTheory
open scoped ENNReal

namespace NonuniformCompetitive.IsoscelesProof

open NonuniformCompetitive.Isosceles

noncomputable def seedPMF (d : ℕ) (hd : 1 ≤ d) : PMF (Seed d) :=
  PMF.ofFintype (fun z => ENNReal.ofReal (seedWeight d z)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => seedWeight_nonneg d hd z),
      seedWeight_sum d hd,ENNReal.ofReal_one])

@[simp] theorem seedPMF_apply (d : ℕ) (hd : 1 ≤ d) (z : Seed d) :
    seedPMF d hd z=ENNReal.ofReal (seedWeight d z) := rfl

noncomputable def mixedThreshold {M : Type} [MetricSpace M] (d : ℕ) (hd : 1 ≤ d)
    (e : Vtx ≃ M) (C₀ : KServer.Config 2 M) : KServer.RandomizedAlgorithm 2 M := by
  classical
  letI : MeasurableSpace (Seed d) := ⊤
  exact { ι := Seed d
          μ := (seedPMF d hd).toMeasure
          prob := inferInstance
          alg := fun z => (changeInitial (thresholdPolicy d hd z) (e.symm ∘ C₀)).toOriginal e
          meas := fun _ => measurable_of_countable _ }

theorem mixedThreshold_expCost {M : Type} [MetricSpace M] (d : ℕ) (hd : 1 ≤ d)
    (e : Vtx ≃ M) (he : ∀ x y, dist (e x) (e y)=triDist d x y)
    (C₀ : KServer.Config 2 M) (h : List M) :
    (mixedThreshold d hd e C₀).expCost h =
      ENNReal.ofReal (seedMean d (fun z => triCost d
        (changeInitial (thresholdPolicy d hd z) (e.symm ∘ C₀)) (h.map e.symm))) := by
  classical
  let : MeasurableSpace (Seed d) := ⊤
  change (∫⁻ z : Seed d, ENNReal.ofReal (((changeInitial (thresholdPolicy d hd z)
      (e.symm ∘ C₀)).toOriginal e).cost h) ∂(seedPMF d hd).toMeasure)=_
  simp_rw [TriPolicy.toOriginal_cost d e he]
  rw [lintegral_fintype]
  unfold seedMean
  rw [ENNReal.ofReal_sum_of_nonneg (fun z _ =>
    mul_nonneg (seedWeight_nonneg d hd z) (triCost_nonneg _ _ _))]
  apply Finset.sum_congr rfl
  intro z _
  rw [(seedPMF d hd).toMeasure_apply_singleton z (measurableSet_singleton z),
    seedPMF_apply,ENNReal.ofReal_mul (seedWeight_nonneg d hd z)]
  exact mul_comm _ _

theorem mixedThreshold_competitive {M : Type} [MetricSpace M] (d : ℕ) (hd : 1 ≤ d)
    (e : Vtx ≃ M) (he : ∀ x y, dist (e x) (e y)=triDist d x y)
    (C₀ : KServer.Config 2 M) :
    (mixedThreshold d hd e C₀).IsCompetitiveFrom C₀ (isoscelesRatio d) := by
  constructor
  · intro z
    ext i
    simp [mixedThreshold,TriPolicy.toOriginal,changeInitial]
  · refine ⟨5*d+isoscelesRatio d*(2*d),?_⟩
    intro h
    rw [mixedThreshold_expCost d hd e he]
    apply ENNReal.ofReal_le_ofReal
    have hm := threshold_mean_from d hd (e.symm ∘ C₀) (h.map e.symm)
    have hb := bank_le_offline d hd e he C₀ (h.map e.symm)
    simp only [List.map_map,Equiv.apply_symm_apply,Function.comp_def,List.map_id'] at hb
    have ha : 0 ≤ isoscelesRatio d := (by norm_num : (0:ℝ) ≤ 1).trans (isoscelesRatio_ge_one d hd)
    have hh := mul_le_mul_of_nonneg_left hb ha
    nlinarith

theorem ratio_attained_direct {M : Type} [MetricSpace M] (d : ℕ) (hd : 1 ≤ d)
    (a b c : M) (hM : ∀ x : M, x=a ∨ x=b ∨ x=c)
    (hab : dist a b=1) (hac : dist a c=d) (hbc : dist b c=d) (C₀ : KServer.Config 2 M) :
    ∃ A : KServer.RandomizedAlgorithm 2 M, A.IsCompetitiveFrom C₀ (isoscelesRatio d) := by
  let e : Vtx ≃ M := Equiv.ofBijective (val a b c)
    ⟨val_injective d hd a b c hab hac hbc,val_surjective a b c hM⟩
  have he : ∀ x y, dist (e x) (e y)=triDist d x y := val_dist d a b c hab hac hbc
  exact ⟨mixedThreshold d hd e C₀,mixedThreshold_competitive d hd e he C₀⟩

end NonuniformCompetitive.IsoscelesProof

end

/- Complete checked body: IsoscelesRoot -/
section

namespace NonuniformCompetitive.Isosceles

/-- Theorem 12 (Karlin–Manasse–McGeoch–Owicki, Competitive Randomized Algorithms for Nonuniform
Problems, Algorithmica 11 (1994), p. 564). Consider the two-server problem on an isosceles
triangle with integer edge lengths `1, d, d` (`1 ≤ d`): a metric space consisting of exactly the
three points `a, b, c` with `dist a b = 1` and `dist a c = dist b c = d`. From every initial
configuration `C₀` of the two servers:
1. no randomized algorithm is competitive against an oblivious adversary within a factor less
   than `(e_{2d-1} + 1/(4d)) / ((e_{2d-1} - 1) + 1/(2d))`, and
2. some randomized algorithm achieves this competitive factor. -/
theorem optimal_ratio {M : Type} [MetricSpace M] (d : ℕ) (hd : 1 ≤ d) (a b c : M)
    (hM : ∀ x : M, x = a ∨ x = b ∨ x = c)
    (hab : dist a b = 1) (hac : dist a c = d) (hbc : dist b c = d)
    (C₀ : KServer.Config 2 M) :
    (∀ (A : KServer.RandomizedAlgorithm 2 M) (ρ : ℝ), A.IsCompetitiveFrom C₀ ρ →
        isoscelesRatio d ≤ ρ) ∧
      ∃ A : KServer.RandomizedAlgorithm 2 M, A.IsCompetitiveFrom C₀ (isoscelesRatio d) := by
  constructor
  · intro A ρ hA
    exact NonuniformCompetitive.IsoscelesProof.no_better_ratio_direct d hd a b c hM hab hac hbc C₀ A ρ hA
  · exact NonuniformCompetitive.IsoscelesProof.ratio_attained_direct d hd a b c hM hab hac hbc C₀

end NonuniformCompetitive.Isosceles

end

open NonuniformCompetitive.Isosceles


theorem solution {M : Type} [MetricSpace M] (d : ℕ) (hd : 1 ≤ d) (a b c : M)
    (hM : ∀ x : M, x = a ∨ x = b ∨ x = c)
    (hab : dist a b = 1) (hac : dist a c = d) (hbc : dist b c = d)
    (C₀ : KServer.Config 2 M) :
    (∀ (A : KServer.RandomizedAlgorithm 2 M) (ρ : ℝ), A.IsCompetitiveFrom C₀ ρ →
        isoscelesRatio d ≤ ρ) ∧
      ∃ A : KServer.RandomizedAlgorithm 2 M, A.IsCompetitiveFrom C₀ (isoscelesRatio d) := by
  exact NonuniformCompetitive.Isosceles.optimal_ratio d hd a b c hM hab hac hbc C₀

#print axioms NonuniformCompetitive.Isosceles.optimal_ratio
#print axioms solution
