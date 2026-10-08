-- Prove2me | solution 1 for NonuniformCompetitive.Triangle345.optimal_ratio
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-07T03:03:19.882333+00:00
-- url     : https://prove2.me/submissions/c1ec5766-6f63-41e2-bf7c-7496acc7cfbf

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_randomized

set_option autoImplicit false

/- Complete checked body: AttributedTriangle345 -/
section

set_option autoImplicit false

-- Prove2me | solution 1 for NonuniformCompetitive.Triangle345.lp_attained
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:30:33.257265+00:00
-- url     : https://prove2.me/submissions/9f84357d-1262-4c8b-8c8c-8c3fa6bd99ab


theorem checked_triangle345_lp_attained :
    let π₁ : ℝ := 2161 / 3207
    let π₂ : ℝ := 169 / 1069
    let π₃ : ℝ := 1481 / 3207
    let π₄ : ℝ := 2749 / 3207
    let π₅ : ℝ := 1016 / 3207
    let π₆ : ℝ := 371 / 1069
    let π₇ : ℝ := 2491 / 3207
    let π₈ : ℝ := 212 / 1069
    let π₉ : ℝ := 1961 / 3207
    let α : ℝ := 1652 / 1069
    (0 ≤ π₁ ∧ π₁ ≤ 1) ∧ (0 ≤ π₂ ∧ π₂ ≤ 1) ∧ (0 ≤ π₃ ∧ π₃ ≤ 1) ∧
    (0 ≤ π₄ ∧ π₄ ≤ 1) ∧ (0 ≤ π₅ ∧ π₅ ≤ 1) ∧ (0 ≤ π₆ ∧ π₆ ≤ 1) ∧
    (0 ≤ π₇ ∧ π₇ ≤ 1) ∧ (0 ≤ π₈ ∧ π₈ ≤ 1) ∧ (0 ≤ π₉ ∧ π₉ ≤ 1) ∧
    ∃ Φab Φac Φbc : ℝ,
      -- phase 1: {a,b}, requests ca, final {a,c}, opt 4
      8 - 4 * π₁ ≤ 4 * α + Φab - Φac ∧
      -- phase 2: {a,b}, requests cbaba, final {a,b}, opt 8
      16 + 2 * π₁ - 4 * π₂ - 2 * π₃ - 4 * π₄ ≤ 8 * α + Φab - Φab ∧
      -- phase 3: {a,b}, requests cbabca, final {a,c}, opt 12
      14 + 2 * π₁ - 4 * π₂ - 2 * π₃ + 6 * π₄ - 4 * π₅ ≤ 12 * α + Φab - Φac ∧
      -- phase 4: {a,b}, requests cbabcb, final {b,c}, opt 11
      11 + 2 * π₁ - 4 * π₂ - 2 * π₃ + 6 * π₄ + 2 * π₅ ≤ 11 * α + Φab - Φbc ∧
      -- phase 5: {a,b}, requests cbac, final {a,c}, opt 8
      8 + 2 * π₁ - 4 * π₂ + 6 * π₃ ≤ 8 * α + Φab - Φac ∧
      -- phase 6: {a,b}, requests cbc, final {b,c}, opt 5
      5 + 2 * π₁ + 6 * π₂ ≤ 5 * α + Φab - Φbc ∧
      -- phase 7: {a,c}, requests bab, final {a,b}, opt 4
      10 - 4 * π₆ - 2 * π₇ ≤ 4 * α + Φac - Φab ∧
      -- phase 8: {a,c}, requests bac, final {a,c}, opt 6
      6 - 4 * π₆ + 6 * π₇ ≤ 6 * α + Φac - Φac ∧
      -- phase 9: {a,c}, requests bc, final {b,c}, opt 3
      3 + 6 * π₆ ≤ 3 * α + Φac - Φbc ∧
      -- phase 10: {b,c}, requests aba, final {a,b}, opt 5
      11 - 2 * π₈ - 4 * π₉ ≤ 5 * α + Φbc - Φab ∧
      -- phase 11: {b,c}, requests abc, final {b,c}, opt 6
      6 - 2 * π₈ + 6 * π₉ ≤ 6 * α + Φbc - Φbc ∧
      -- phase 12: {b,c}, requests ac, final {a,c}, opt 3
      3 + 6 * π₈ ≤ 3 * α + Φbc - Φac := by
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, 0, (2812:ℝ)/3207, (1381:ℝ)/3207, ?_⟩
  norm_num

-- Prove2me | solution 1 for NonuniformCompetitive.Triangle345.lp_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:29:37.943012+00:00
-- url     : https://prove2.me/submissions/cd87de92-94b4-42fa-bb78-16f8323cbadd


theorem checked_triangle345_lp_lower_bound (π₁ π₂ π₃ π₄ π₅ π₆ π₇ π₈ π₉ Φab Φac Φbc α : ℝ)
    -- phase 1: {a,b}, requests ca, final {a,c}, opt 4
    (h1 : 8 - 4 * π₁ ≤ 4 * α + Φab - Φac)
    -- phase 2: {a,b}, requests cbaba, final {a,b}, opt 8
    (h2 : 16 + 2 * π₁ - 4 * π₂ - 2 * π₃ - 4 * π₄ ≤ 8 * α + Φab - Φab)
    -- phase 3: {a,b}, requests cbabca, final {a,c}, opt 12
    (h3 : 14 + 2 * π₁ - 4 * π₂ - 2 * π₃ + 6 * π₄ - 4 * π₅ ≤ 12 * α + Φab - Φac)
    -- phase 4: {a,b}, requests cbabcb, final {b,c}, opt 11
    (h4 : 11 + 2 * π₁ - 4 * π₂ - 2 * π₃ + 6 * π₄ + 2 * π₅ ≤ 11 * α + Φab - Φbc)
    -- phase 5: {a,b}, requests cbac, final {a,c}, opt 8
    (h5 : 8 + 2 * π₁ - 4 * π₂ + 6 * π₃ ≤ 8 * α + Φab - Φac)
    -- phase 6: {a,b}, requests cbc, final {b,c}, opt 5
    (h6 : 5 + 2 * π₁ + 6 * π₂ ≤ 5 * α + Φab - Φbc)
    -- phase 7: {a,c}, requests bab, final {a,b}, opt 4
    (h7 : 10 - 4 * π₆ - 2 * π₇ ≤ 4 * α + Φac - Φab)
    -- phase 8: {a,c}, requests bac, final {a,c}, opt 6
    (h8 : 6 - 4 * π₆ + 6 * π₇ ≤ 6 * α + Φac - Φac)
    -- phase 9: {a,c}, requests bc, final {b,c}, opt 3
    (h9 : 3 + 6 * π₆ ≤ 3 * α + Φac - Φbc)
    -- phase 10: {b,c}, requests aba, final {a,b}, opt 5
    (h10 : 11 - 2 * π₈ - 4 * π₉ ≤ 5 * α + Φbc - Φab)
    -- phase 11: {b,c}, requests abc, final {b,c}, opt 6
    (h11 : 6 - 2 * π₈ + 6 * π₉ ≤ 6 * α + Φbc - Φbc)
    -- phase 12: {b,c}, requests ac, final {a,c}, opt 3
    (h12 : 3 + 6 * π₈ ≤ 3 * α + Φbc - Φac) :
    (1652 / 1069 : ℝ) ≤ α := by
  linarith


end

/- Complete checked body: TriangleBasics -/
section

namespace NonuniformCompetitive.Triangle345Proof

open scoped BigOperators

abbrev Vtx := Fin 3

def triNat (x y : Vtx) : ℕ := ![![0,3,5],![3,0,4],![5,4,0]] x y

def triDist (x y : Vtx) : ℝ := triNat x y

def val {M : Type*} (a b c : M) (x : Vtx) : M := ![a,b,c] x

def pairConf (h : Vtx) : Fin 2 → Vtx :=
  if h=0 then ![1,2] else if h=1 then ![0,2] else ![0,1]

def triMove (C D : Fin 2 → Vtx) : ℝ := ∑ i, triDist (C i) (D i)

def swapConf (C : Fin 2 → Vtx) : Fin 2 → Vtx := ![C 1,C 0]

def pairMatch (h : Vtx) (C : Fin 2 → Vtx) : ℝ :=
  min (triMove (pairConf h) C) (triMove (swapConf (pairConf h)) C)

@[simp] theorem triDist_self (x : Vtx) : triDist x x=0 := by fin_cases x <;> norm_num [triDist,triNat]

theorem triDist_symm (x y : Vtx) : triDist x y=triDist y x := by
  fin_cases x <;> fin_cases y <;> rfl

theorem triDist_nonneg (x y : Vtx) : 0 ≤ triDist x y := Nat.cast_nonneg _

theorem triDist_le (x y : Vtx) : triDist x y ≤ 5 := by
  fin_cases x <;> fin_cases y <;> norm_num [triDist,triNat]

theorem triDist_pos (x y : Vtx) (hxy : x≠y) : 1 ≤ triDist x y := by
  fin_cases x <;> fin_cases y <;> norm_num [triDist,triNat,Fin.ext_iff] at *

theorem triDist_triangle (x y z : Vtx) : triDist x z ≤ triDist x y+triDist y z := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> norm_num [triDist,triNat]

theorem pairConf_mem (h r : Vtx) : (∃ i, pairConf h i=r) ↔ r≠h := by
  fin_cases h <;> fin_cases r <;> simp [pairConf,Fin.exists_fin_two]

theorem triMove_nonneg (C D : Fin 2 → Vtx) : 0 ≤ triMove C D :=
  Finset.sum_nonneg fun i _ => triDist_nonneg (C i) (D i)

theorem triMove_triangle (C D E : Fin 2 → Vtx) : triMove C E ≤ triMove C D+triMove D E := by
  unfold triMove
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => triDist_triangle (C i) (D i) (E i)

theorem triMove_le (C D : Fin 2 → Vtx) : triMove C D ≤ 10 := by
  have h0 := triDist_le (C 0) (D 0)
  have h1 := triDist_le (C 1) (D 1)
  simp only [triMove,Fin.sum_univ_two]
  linarith

theorem pairMatch_nonneg (h : Vtx) (C : Fin 2 → Vtx) : 0 ≤ pairMatch h C :=
  le_min (triMove_nonneg _ _) (triMove_nonneg _ _)

theorem pairMatch_move (h : Vtx) (C D : Fin 2 → Vtx) :
    pairMatch h D ≤ pairMatch h C+triMove C D := by
  unfold pairMatch
  rcases le_total (triMove (pairConf h) C) (triMove (swapConf (pairConf h)) C) with hl | hl
  · rw [min_eq_left hl]
    exact (min_le_left _ _).trans (triMove_triangle _ _ _)
  · rw [min_eq_right hl]
    exact (min_le_right _ _).trans (triMove_triangle _ _ _)

theorem pairMatch_pair (h g : Vtx) : pairMatch h (pairConf g)=triDist h g := by
  fin_cases h <;> fin_cases g <;>
    norm_num [pairMatch,pairConf,swapConf,triMove,Fin.sum_univ_two,triDist,triNat,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]

theorem val_dist {M : Type*} [MetricSpace M] (a b c : M)
    (hab : dist a b=3) (hac : dist a c=5) (hbc : dist b c=4) (x y : Vtx) :
    dist (val a b c x) (val a b c y)=triDist x y := by
  fin_cases x <;> fin_cases y <;> simp [val,triDist,triNat,hab,hac,hbc,dist_comm]

theorem val_injective {M : Type*} [MetricSpace M] (a b c : M)
    (hab : dist a b=3) (hac : dist a c=5) (hbc : dist b c=4) :
    Function.Injective (val a b c) := by
  intro x y hxy
  have hz : triDist x y=0 := by rw [← val_dist a b c hab hac hbc,hxy,dist_self]
  by_contra hn
  have hp := triDist_pos x y hn
  linarith

theorem val_surjective {M : Type*} (a b c : M) (hM : ∀ x:M,x=a ∨ x=b ∨ x=c) :
    Function.Surjective (val a b c) := by
  intro x
  rcases hM x with rfl | rfl | rfl
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩

theorem val_move {M : Type*} [MetricSpace M] (a b c : M)
    (hab : dist a b=3) (hac : dist a c=5) (hbc : dist b c=4) (C D : Fin 2 → Vtx) :
    KServer.moveCost (val a b c ∘ C) (val a b c ∘ D)=triMove C D := by
  apply Finset.sum_congr rfl
  intro i _
  exact val_dist a b c hab hac hbc _ _

end NonuniformCompetitive.Triangle345Proof
end

/- Complete checked body: TrianglePolicies -/
section

set_option autoImplicit false

namespace NonuniformCompetitive.Triangle345Proof

structure TriPolicy where
  conf : List Vtx → (Fin 2 → Vtx)
  serves : ∀ h r, ∃ i, conf (h++[r]) i = r

noncomputable def triCost (A : TriPolicy) (h : List Vtx) : ℝ :=
  ∑ j ∈ Finset.range h.length, triMove (A.conf (h.take j)) (A.conf (h.take (j+1)))

def TriIsLazy (A : TriPolicy) : Prop :=
  ∀ h r, ((∃ i, A.conf h i = r) → A.conf (h++[r]) = A.conf h) ∧
    ((¬∃ i, A.conf h i = r) → ∃ i, A.conf (h++[r]) = Function.update (A.conf h) i r)

lemma triCost_nonneg (A : TriPolicy) (h : List Vtx) : 0 ≤ triCost A h :=
  Finset.sum_nonneg (fun _ _ => triMove_nonneg _ _)

@[simp] lemma triCost_nil (A : TriPolicy) : triCost A [] = 0 := by simp [triCost]

lemma triCost_append_one (A : TriPolicy) (h : List Vtx) (r : Vtx) :
    triCost A (h++[r]) = triCost A h + triMove (A.conf h) (A.conf (h++[r])) := by
  unfold triCost
  rw [List.length_append,List.length_singleton,Finset.sum_range_succ]
  have hs : (∑ j ∈ Finset.range h.length,
      triMove (A.conf ((h++[r]).take j)) (A.conf ((h++[r]).take (j+1)))) =
      ∑ j ∈ Finset.range h.length,
      triMove (A.conf (h.take j)) (A.conf (h.take (j+1))) := by
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

lemma triCost_append (A : TriPolicy) (h l : List Vtx) :
    triCost A (h++l) = triCost A h + triCost (triShift A h) l := by
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

lemma toOriginal_cost (e : Vtx ≃ M)
    (he : ∀ x y, dist (e x) (e y) = triDist x y) (A : TriPolicy) (h : List M) :
    (A.toOriginal e).cost h = triCost A (h.map e.symm) := by
  unfold KServer.OnlineAlgorithm.cost triCost
  simp only [List.length_map]
  apply Finset.sum_congr rfl
  intro j _hj
  unfold KServer.moveCost triMove
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [toOriginal,Function.comp_apply,List.map_take,he]

lemma ofOriginal_cost (e : Vtx ≃ M)
    (he : ∀ x y, dist (e x) (e y) = triDist x y)
    (A : KServer.OnlineAlgorithm 2 M) (h : List Vtx) :
    triCost (ofOriginal e A) h = A.cost (h.map e) := by
  unfold KServer.OnlineAlgorithm.cost triCost
  simp only [List.length_map]
  apply Finset.sum_congr rfl
  intro j _hj
  unfold KServer.moveCost triMove
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [ofOriginal,Function.comp_apply,List.map_take,← he,e.apply_symm_apply]

end TriPolicy

end NonuniformCompetitive.Triangle345Proof

end

/- Complete checked body: HoleLifting -/
section

namespace NonuniformCompetitive.Triangle345Proof

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

theorem pairChange_cost (C : Fin 2 → Vtx) (h g : Vtx) (hC : FitsPair C h) :
    triMove C (pairChange C h g) = triDist h g := by
  rcases hC with rfl | rfl
  all_goals fin_cases h <;> fin_cases g <;>
    simp [pairChange,pairConf,swapConf,triMove,Fin.sum_univ_two,triDist,triNat]

def liftHolePath (h : ℕ → Vtx) (C₀ : Fin 2 → Vtx) : ℕ → Fin 2 → Vtx
  | 0 => C₀
  | t+1 => pairChange (liftHolePath h C₀ t) (h t) (h (t+1))

theorem liftHolePath_fits (h : ℕ → Vtx) (C₀ : Fin 2 → Vtx) (hC : FitsPair C₀ (h 0)) (t : ℕ) :
    FitsPair (liftHolePath h C₀ t) (h t) := by
  induction t with
  | zero => exact hC
  | succ t ih => exact pairChange_fits _ _ _ ih

theorem liftHolePath_cost (h : ℕ → Vtx) (C₀ : Fin 2 → Vtx)
    (hC : FitsPair C₀ (h 0)) (t : ℕ) :
    triMove (liftHolePath h C₀ t) (liftHolePath h C₀ (t+1)) = triDist (h t) (h (t+1)) :=
  pairChange_cost _ _ _ (liftHolePath_fits h C₀ hC t)

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

theorem holePolicy_cost (g : List Vtx → Vtx) (hg : ∀ h r, g (h++[r]) ≠ r)
    (C₀ : Fin 2 → Vtx) (hC : FitsPair C₀ (g [])) (h : List Vtx) :
    triCost (holePolicy g hg C₀ hC) h =
      ∑ j ∈ Finset.range h.length, triDist (g (h.take j)) (g (h.take (j+1))) := by
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j < h.length := Finset.mem_range.mp hj
  change triMove (holeRun g C₀ (h.take j)).2 (holeRun g C₀ (h.take (j+1))).2 = _
  rw [List.take_succ_eq_append_getElem hj',holeRun_append_one]
  simp only [holeTransition,holeRun_prefix]
  exact pairChange_cost _ _ _ (holeRun_fits g C₀ hC (h.take j))

end NonuniformCompetitive.Triangle345Proof
end

/- Complete checked body: PairStates -/
section

set_option autoImplicit false

namespace NonuniformCompetitive.Triangle345Proof

lemma triMove_symm (C D : Fin 2 → Vtx) : triMove C D = triMove D C := by
  apply Finset.sum_congr rfl
  intro i _
  exact triDist_symm _ _

lemma FitsPair.match_eq {C : Fin 2 → Vtx} {h : Vtx} (hC : FitsPair C h) (g : Vtx) :
    pairMatch g C = triDist g h := by
  rcases hC with rfl | rfl
  · exact pairMatch_pair _ _
  · fin_cases g <;> fin_cases h <;>
      norm_num [pairMatch,pairConf,swapConf,triMove,Fin.sum_univ_two,triDist,triNat,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]

lemma FitsPair.distinct {C : Fin 2 → Vtx} {h : Vtx} (hC : FitsPair C h) : C 0 ≠ C 1 := by
  rcases hC with rfl | rfl
  all_goals fin_cases h <;> decide

lemma distinct_fits (C : Fin 2 → Vtx) (hC : C 0 ≠ C 1) : ∃ h, FitsPair C h := by
  have he : C = ![C 0,C 1] := by funext i; fin_cases i <;> rfl
  have hf : ∀ x y : Vtx, x ≠ y → ∃ h, FitsPair ![x,y] h := by unfold FitsPair; decide
  rw [he]
  exact hf (C 0) (C 1) hC

lemma lazy_distinct (A : TriPolicy) (hA : TriIsLazy A) (l : List Vtx) (r : Vtx)
    (hC : A.conf l 0 ≠ A.conf l 1) : A.conf (l++[r]) 0 ≠ A.conf (l++[r]) 1 := by
  by_cases hc : ∃ i, A.conf l i=r
  · rw [(hA l r).1 hc]
    exact hC
  · obtain ⟨i,hi⟩ := (hA l r).2 hc
    rw [hi]
    fin_cases i
    · change r ≠ A.conf l 1
      intro he
      exact hc ⟨1,he.symm⟩
    · change A.conf l 0 ≠ r
      intro he
      exact hc ⟨0,he⟩

lemma lazy_next_pair (A : TriPolicy) (hA : TriIsLazy A) (l : List Vtx) (r h : Vtx)
    (hC : FitsPair (A.conf l) h) :
    ∃ g, g ≠ r ∧ FitsPair (A.conf (l++[r])) g ∧
      triDist h g ≤ triMove (A.conf l) (A.conf (l++[r])) := by
  obtain ⟨g,hg⟩ := distinct_fits (A.conf (l++[r])) (lazy_distinct A hA l r hC.distinct)
  refine ⟨g,Ne.symm (hg.serves.mp (A.serves l r)),hg,?_⟩
  have hb := pairMatch_move h (A.conf l) (A.conf (l++[r]))
  rw [hC.match_eq,hg.match_eq,triDist_self,zero_add] at hb
  exact hb

lemma pairMatch_le_ten (h : Vtx) (C : Fin 2 → Vtx) : pairMatch h C ≤ 10 :=
  (min_le_left _ _).trans (triMove_le _ _)

lemma triCost_singleton (A : TriPolicy) (r : Vtx) :
    triCost A [r] = triMove (A.conf []) (A.conf [r]) := by simp [triCost]

lemma triCost_cons (A : TriPolicy) (r : Vtx) (l : List Vtx) :
    triCost A (r::l) = triMove (A.conf []) (A.conf [r]) + triCost (triShift A [r]) l := by
  simpa only [triCost_singleton,List.singleton_append] using triCost_append A [r] l

lemma pairMatch_cost (A : TriPolicy) (h : Vtx) (l : List Vtx) :
    pairMatch h (A.conf []) ≤ triCost A l + pairMatch h (A.conf l) := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l r ih =>
    have hb := pairMatch_move h (A.conf (l++[r])) (A.conf l)
    rw [triMove_symm] at hb
    rw [triCost_append_one]
    linarith

end NonuniformCompetitive.Triangle345Proof

end

/- Complete checked body: ResetBlocks -/
section

set_option autoImplicit false

namespace NonuniformCompetitive.Triangle345Proof

def resetWord (h : Vtx) : ℕ → List Vtx
  | 0 => []
  | k+1 => resetWord h k ++ [pairConf h 0,pairConf h 1]

lemma fits_of_covers (C : Fin 2 → Vtx) (h : Vtx)
    (h0 : ∃ i, C i=pairConf h 0) (h1 : ∃ i, C i=pairConf h 1) : FitsPair C h := by
  have he : C = ![C 0,C 1] := by funext i; fin_cases i <;> rfl
  rw [he]
  generalize hC0 : C 0=x0
  generalize hC1 : C 1=x1
  fin_cases h <;> fin_cases x0 <;> fin_cases x1 <;>
    simp_all [FitsPair,pairConf,swapConf,Fin.exists_fin_two]

lemma reset_block_stays (A : TriPolicy) (hA : TriIsLazy A) (h : Vtx)
    (hC : FitsPair (A.conf []) h) :
    A.conf [pairConf h 0,pairConf h 1]=A.conf [] ∧
      triCost A [pairConf h 0,pairConf h 1]=0 := by
  have ha : ∃ i, A.conf [] i=pairConf h 0 := hC.serves.mpr ((pairConf_mem h _).mp ⟨0,rfl⟩)
  have hb : ∃ i, A.conf [] i=pairConf h 1 := hC.serves.mpr ((pairConf_mem h _).mp ⟨1,rfl⟩)
  have h0 : A.conf [pairConf h 0]=A.conf [] := by simpa using (hA [] _).1 ha
  have h1 : A.conf [pairConf h 0,pairConf h 1]=A.conf [pairConf h 0] :=
    (hA [pairConf h 0] _).1 (by simpa only [h0] using hb)
  constructor
  · exact h1.trans h0
  · rw [show [pairConf h 0,pairConf h 1]=[pairConf h 0]++[pairConf h 1] from rfl,
      triCost_append_one,triCost_singleton,List.singleton_append,h1,h0]
    simp [triMove]

lemma failed_block_cost (A : TriPolicy) (hA : TriIsLazy A) (h : Vtx)
    (hC : ¬FitsPair (A.conf [pairConf h 0,pairConf h 1]) h) :
    1 ≤ triCost A [pairConf h 0,pairConf h 1] := by
  have h0 : ∃ i, A.conf [pairConf h 0] i=pairConf h 0 := by simpa using A.serves [] (pairConf h 0)
  have hm : ¬∃ i, A.conf [pairConf h 0] i=pairConf h 1 := by
    intro hc
    have he := (hA [pairConf h 0] (pairConf h 1)).1 hc
    apply hC
    rw [show [pairConf h 0,pairConf h 1]=[pairConf h 0]++[pairConf h 1] from rfl,he]
    exact fits_of_covers _ _ h0 hc
  obtain ⟨i,hi⟩ := A.serves [pairConf h 0] (pairConf h 1)
  have hn : A.conf [pairConf h 0] i ≠ pairConf h 1 := by intro he; exact hm ⟨i,he⟩
  have hb := triDist_pos _ _ hn
  rw [← hi] at hb
  have hs := Finset.single_le_sum (fun j _ => triDist_nonneg (A.conf [pairConf h 0] j)
    (A.conf ([pairConf h 0]++[pairConf h 1]) j)) (Finset.mem_univ i)
  have hz := triCost_nonneg A [pairConf h 0]
  rw [show [pairConf h 0,pairConf h 1]=[pairConf h 0]++[pairConf h 1] from rfl,
    triCost_append_one]
  have hl : 1 ≤ triMove (A.conf [pairConf h 0]) (A.conf ([pairConf h 0]++[pairConf h 1])) := hb.trans hs
  linarith

lemma failed_reset_cost (A : TriPolicy) (hA : TriIsLazy A) (h : Vtx) (k : ℕ)
    (hC : ¬FitsPair (A.conf (resetWord h k)) h) : (k:ℝ) ≤ triCost A (resetWord h k) := by
  induction k with
  | zero => simp [resetWord]
  | succ k ih =>
    have hn : ¬FitsPair (A.conf (resetWord h k)) h := by
      intro hc
      have hs := reset_block_stays (triShift A (resetWord h k)) (triShift_lazy A hA _) h
        (by simpa [triShift] using hc)
      apply hC
      have he : A.conf (resetWord h (k+1))=A.conf (resetWord h k) := by
        simpa only [resetWord,triShift,List.append_nil] using hs.1
      rwa [he]
    have hl := failed_block_cost (triShift A (resetWord h k)) (triShift_lazy A hA _) h
      (by simpa only [triShift,resetWord] using hC)
    have ht := ih hn
    rw [resetWord,triCost_append,Nat.cast_succ]
    linarith

lemma reset_dominates_match (A : TriPolicy) (hA : TriIsLazy A) (h : Vtx) :
    pairMatch h (A.conf []) ≤ triCost A (resetWord h 10) := by
  by_cases hc : FitsPair (A.conf (resetWord h 10)) h
  · have hb := pairMatch_cost A h (resetWord h 10)
    rw [hc.match_eq,triDist_self,add_zero] at hb
    exact hb
  · exact (pairMatch_le_ten h _).trans (failed_reset_cost A hA h 10 hc)

end NonuniformCompetitive.Triangle345Proof

end

/- Complete checked body: FiniteLaw -/
section

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace NonuniformCompetitive.Triangle345Proof

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
end NonuniformCompetitive.Triangle345Proof

end

/- Complete checked body: FiniteRealLaw -/
section

set_option autoImplicit false

namespace NonuniformCompetitive.Triangle345Proof.FiniteLaw

variable {α : Type*}

lemma realMean_mono (Q : FiniteLaw α) {f g : α → ℝ} (h : Q.All (fun a => f a ≤ g a)) :
    Q.realMean f ≤ Q.realMean g := by
  induction Q with
  | pure a => exact h
  | mix q r hs L R hL hR =>
    dsimp only [realMean]
    exact add_le_add (mul_le_mul_of_nonneg_left (hL h.1) q.coe_nonneg)
      (mul_le_mul_of_nonneg_left (hR h.2) r.coe_nonneg)

lemma all_and (Q : FiniteLaw α) {P R : α → Prop} (hP : Q.All P) (hR : Q.All R) :
    Q.All (fun a => P a ∧ R a) := by
  induction Q with
  | pure a => exact ⟨hP,hR⟩
  | mix q r hs L R ihL ihR => exact ⟨ihL hP.1 hR.1,ihR hP.2 hR.2⟩

end NonuniformCompetitive.Triangle345Proof.FiniteLaw
end

/- Complete checked body: AdversaryTree -/
section

set_option autoImplicit false
open scoped NNReal

namespace NonuniformCompetitive.Triangle345Proof

/-- A finite oblivious request tree. Branches depend only on earlier requests. -/
inductive AdversaryTree where
  | leaf (endpoint : Vtx) (benchmark : ℝ)
  | ask (request : Vtx) (tail : AdversaryTree)
  | mix (q r : ℝ≥0) (sum_one : q+r=1) (left right : AdversaryTree)

abbrev Outcome := List Vtx × Vtx × ℝ

namespace AdversaryTree

def law : AdversaryTree → FiniteLaw Outcome
  | .leaf h b => .pure ([],h,b)
  | .ask r T => T.law.map (fun z => (r::z.1,z.2))
  | .mix q r hs L R => .mix q r hs L.law R.law

def minExcept (r : Vtx) (f : Vtx → ℝ) : ℝ :=
  if r=0 then min (f 1) (f 2) else if r=1 then min (f 0) (f 2) else min (f 0) (f 1)

lemma minExcept_le (r : Vtx) (f : Vtx → ℝ) (g : Vtx) (hg : g≠r) : minExcept r f ≤ f g := by
  fin_cases r <;> fin_cases g <;> simp_all [minExcept]

noncomputable def bellman : AdversaryTree → Vtx → ℝ
  | .leaf g _,h => triDist g h
  | .ask r T,h => minExcept r (fun g => triDist h g+T.bellman g)
  | .mix q r _ L R,h => q*L.bellman h+r*R.bellman h

lemma charged_lower (T : AdversaryTree) (A : TriPolicy) (hA : TriIsLazy A)
    (h : Vtx) (hc : FitsPair (A.conf []) h) :
    T.bellman h ≤ T.law.realMean (fun z => triCost A z.1+pairMatch z.2.1 (A.conf z.1)) := by
  induction T generalizing A h with
  | leaf g b => simpa [law,bellman,FiniteLaw.realMean] using (hc.match_eq g).ge
  | ask r T ih =>
    obtain ⟨g,hgr,hg,hmove⟩ := lazy_next_pair A hA [] r h hc
    have hgl : FitsPair ((triShift A [r]).conf []) g := by simpa [triShift] using hg
    have hb := ih (triShift A [r]) (triShift_lazy A hA _) g hgl
    have hm := minExcept_le r (fun g => triDist h g+T.bellman g) g hgr
    have he : (T.law.map (fun z => (r::z.1,z.2))).realMean
        (fun z => triCost A z.1+pairMatch z.2.1 (A.conf z.1)) =
        triMove (A.conf []) (A.conf [r])+
          T.law.realMean (fun z => triCost (triShift A [r]) z.1+
            pairMatch z.2.1 ((triShift A [r]).conf z.1)) := by
      rw [FiniteLaw.realMean_map]
      simp_rw [triCost_cons A r,add_assoc]
      rw [FiniteLaw.realMean_add,FiniteLaw.realMean_const]
      rfl
    change minExcept r _ ≤ _
    rw [law,he]
    simpa only [List.nil_append] using hm.trans (add_le_add hmove hb)
  | mix q r hs L R ihL ihR =>
    exact add_le_add (mul_le_mul_of_nonneg_left (ihL A hA h hc) q.coe_nonneg)
      (mul_le_mul_of_nonneg_left (ihR A hA h hc) r.coe_nonneg)

lemma reset_lower (T : AdversaryTree) (A : TriPolicy) (hA : TriIsLazy A)
    (h : Vtx) (hc : FitsPair (A.conf []) h) :
    T.bellman h ≤ T.law.realMean (fun z => triCost A (z.1++resetWord z.2.1 10)) := by
  apply (T.charged_lower A hA h hc).trans
  apply FiniteLaw.realMean_mono
  apply FiniteLaw.all_of_forall
  intro z
  rw [triCost_append]
  have hb := reset_dominates_match (triShift A z.1) (triShift_lazy A hA _) z.2.1
  simpa only [triShift,List.append_nil] using add_le_add le_rfl hb

end AdversaryTree
end NonuniformCompetitive.Triangle345Proof

end

/- Complete checked body: PhaseTree -/
section

set_option autoImplicit false
namespace NonuniformCompetitive.Triangle345Proof

noncomputable def tree0 : AdversaryTree :=
  (.ask 0 (.mix (330/440) (110/440) (by norm_num) (.ask 1 (.mix (198/330) (132/330) (by norm_num) (.ask 0 (.leaf 2 5)) (.ask 2 (.leaf 0 6)))) (.ask 2 (.leaf 1 3))))

noncomputable def tree1 : AdversaryTree :=
  (.ask 1 (.mix (228/380) (152/380) (by norm_num) (.ask 0 (.mix (171/228) (57/228) (by norm_num) (.ask 1 (.leaf 2 4)) (.ask 2 (.leaf 1 6)))) (.ask 2 (.leaf 0 3))))

noncomputable def tree2 : AdversaryTree :=
  (.ask 2 (.mix (150/450) (300/450) (by norm_num) (.ask 0 (.leaf 1 4)) (.ask 1 (.mix (180/300) (120/300) (by norm_num) (.ask 0 (.mix (135/180) (45/180) (by norm_num) (.ask 1 (.mix (81/135) (54/135) (by norm_num) (.ask 0 (.leaf 2 8)) (.ask 2 (.mix (18/54) (36/54) (by norm_num) (.ask 0 (.leaf 1 12)) (.ask 1 (.leaf 0 11)))))) (.ask 2 (.leaf 1 8)))) (.ask 2 (.leaf 0 5))))))

noncomputable def phaseTree (h : Vtx) : AdversaryTree := ![tree0,tree1,tree2] h

noncomputable def boundary (h : Vtx) : ℝ := ![1381/3207,2812/3207,0] h

noncomputable def phaseGain (h : Vtx) : ℝ := ![15/2,33/5,228/25] h

noncomputable def phaseLaw (h : Vtx) : FiniteLaw Outcome := (phaseTree h).law

def phaseWord (h : Vtx) (z : Outcome) : List Vtx :=
  resetWord h 10 ++ (z.1 ++ resetWord z.2.1 10)

lemma phaseTree_value (h : Vtx) : (phaseTree h).bellman h=phaseGain h := by
  fin_cases h <;> norm_num [phaseTree,tree0,tree1,tree2,AdversaryTree.bellman,
    AdversaryTree.minExcept,phaseGain,triDist,triNat,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Fin.ext_iff,NNReal.coe_div]

lemma phaseGain_le_ten (h : Vtx) : phaseGain h ≤ 10 := by fin_cases h <;> norm_num [phaseGain]

lemma boundary_bounds (h : Vtx) : 0 ≤ boundary h ∧ boundary h ≤ 1 := by
  fin_cases h <;> norm_num [boundary]

lemma phase_balance (h : Vtx) :
    phaseGain h = (1652/1069:ℝ)*(phaseLaw h).realMean (fun z => z.2.2)+boundary h-
      (phaseLaw h).realMean (fun z => boundary z.2.1) := by
  fin_cases h <;> norm_num [phaseLaw,phaseTree,tree0,tree1,tree2,AdversaryTree.law,
    FiniteLaw.realMean,FiniteLaw.realMean_map,phaseGain,boundary,NNReal.coe_div,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]

lemma phase_benchmark_ge_three (h : Vtx) : (phaseLaw h).All (fun z => 3 ≤ z.2.2) := by
  fin_cases h <;> norm_num [phaseLaw,phaseTree,tree0,tree1,tree2,AdversaryTree.law,
    FiniteLaw.All,FiniteLaw.all_map]

lemma phase_lower (A : TriPolicy) (hA : TriIsLazy A) (h : Vtx) :
    phaseGain h ≤ (phaseLaw h).realMean (fun z => triCost A (phaseWord h z)) := by
  by_cases hc : FitsPair (A.conf (resetWord h 10)) h
  · have hp : FitsPair ((triShift A (resetWord h 10)).conf []) h := by simpa [triShift] using hc
    have hb := (phaseTree h).reset_lower (triShift A (resetWord h 10)) (triShift_lazy A hA _) h hp
    rw [phaseTree_value] at hb
    have he : (phaseLaw h).realMean (fun z => triCost A (phaseWord h z)) =
        triCost A (resetWord h 10)+(phaseLaw h).realMean
          (fun z => triCost (triShift A (resetWord h 10)) (z.1++resetWord z.2.1 10)) := by
      simp only [phaseWord,triCost_append,FiniteLaw.realMean_add,FiniteLaw.realMean_const]
    rw [he]
    exact hb.trans (le_add_of_nonneg_left (triCost_nonneg _ _))
  · have hb := failed_reset_cost A hA h 10 hc
    apply (phaseGain_le_ten h).trans
    apply hb.trans
    calc
      triCost A (resetWord h 10) = (phaseLaw h).realMean (fun _ => triCost A (resetWord h 10)) :=
        (FiniteLaw.realMean_const _ _).symm
      _ ≤ _ := (phaseLaw h).realMean_mono ((phaseLaw h).all_of_forall (fun z => by
        rw [phaseWord,triCost_append]
        exact le_add_of_nonneg_right (triCost_nonneg _ _)))

end NonuniformCompetitive.Triangle345Proof

end

/- Complete checked body: RepeatedAdversary -/
section

set_option autoImplicit false

namespace NonuniformCompetitive.Triangle345Proof

/-- A fixed finite law of complete request words, final reference pairs and offline budgets. -/
noncomputable def repeatedLaw : ℕ → Vtx → FiniteLaw Outcome
  | 0,h => .pure ([],h,0)
  | N+1,h => (phaseLaw h).bind (fun z => (repeatedLaw N z.2.1).map
      (fun w => (phaseWord h z++w.1,w.2.1,z.2.2+w.2.2)))

lemma repeated_benchmark (N : ℕ) (h : Vtx) :
    (repeatedLaw N h).All (fun z => (3*N:ℝ) ≤ z.2.2) := by
  induction N generalizing h with
  | zero => simp [repeatedLaw,FiniteLaw.All]
  | succ N ih =>
    rw [repeatedLaw,FiniteLaw.all_bind]
    apply (phaseLaw h).all_mono (phase_benchmark_ge_three h)
    intro z hz
    rw [FiniteLaw.all_map]
    exact (repeatedLaw N z.2.1).all_mono (ih z.2.1) (fun w hw => by push_cast; linarith)

lemma repeated_lower (N : ℕ) (h : Vtx) (A : TriPolicy) (hA : TriIsLazy A) :
    (1652/1069:ℝ)*(repeatedLaw N h).realMean (fun z => z.2.2)+boundary h-
      (repeatedLaw N h).realMean (fun z => boundary z.2.1) ≤
      (repeatedLaw N h).realMean (fun z => triCost A z.1) := by
  induction N generalizing h A with
  | zero => simp [repeatedLaw,FiniteLaw.realMean]
  | succ N ih =>
    have ht := phase_lower A hA h
    rw [phase_balance] at ht
    have hb := (phaseLaw h).realMean_mono ((phaseLaw h).all_of_forall (fun z =>
      ih z.2.1 (triShift A (phaseWord h z)) (triShift_lazy A hA _)))
    have hl : (repeatedLaw (N+1) h).realMean (fun z => triCost A z.1) =
        (phaseLaw h).realMean (fun z => triCost A (phaseWord h z))+
        (phaseLaw h).realMean (fun z => (repeatedLaw N z.2.1).realMean
          (fun w => triCost (triShift A (phaseWord h z)) w.1)) := by
      simp only [repeatedLaw,FiniteLaw.realMean_bind,FiniteLaw.realMean_map,triCost_append,
        FiniteLaw.realMean_add,FiniteLaw.realMean_const]
    have hg : (repeatedLaw (N+1) h).realMean (fun z => z.2.2) =
        (phaseLaw h).realMean (fun z => z.2.2)+
        (phaseLaw h).realMean (fun z => (repeatedLaw N z.2.1).realMean (fun w => w.2.2)) := by
      simp only [repeatedLaw,FiniteLaw.realMean_bind,FiniteLaw.realMean_map,
        FiniteLaw.realMean_add,FiniteLaw.realMean_const]
    have he : (repeatedLaw (N+1) h).realMean (fun z => boundary z.2.1) =
        (phaseLaw h).realMean (fun z => (repeatedLaw N z.2.1).realMean
          (fun w => boundary w.2.1)) := by
      simp only [repeatedLaw,FiniteLaw.realMean_bind,FiniteLaw.realMean_map]
    rw [hl,hg,he]
    simp_rw [mul_comm (1652/1069:ℝ),FiniteLaw.realMean_sub,FiniteLaw.realMean_add,
      FiniteLaw.realMean_mul_const] at hb
    linarith

lemma repeated_lower_simple (N : ℕ) (h : Vtx) (A : TriPolicy) (hA : TriIsLazy A) :
    (1652/1069:ℝ)*(repeatedLaw N h).realMean (fun z => z.2.2)-1 ≤
      (repeatedLaw N h).realMean (fun z => triCost A z.1) := by
  have hl := repeated_lower N h A hA
  have he : (repeatedLaw N h).realMean (fun z => boundary z.2.1) ≤ 1 := by
    calc
      _ ≤ (repeatedLaw N h).realMean (fun _ => 1) :=
        (repeatedLaw N h).realMean_mono ((repeatedLaw N h).all_of_forall
          (fun z => (boundary_bounds z.2.1).2))
      _ = _ := FiniteLaw.realMean_const _ _
  have hh := (boundary_bounds h).1
  linarith

end NonuniformCompetitive.Triangle345Proof

end

/- Complete checked body: TwoMatching -/
section

set_option autoImplicit false

namespace NonuniformCompetitive.Triangle345Proof

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

end NonuniformCompetitive.Triangle345Proof

end

/- Complete checked body: KServerCosts -/
section

set_option autoImplicit false

namespace NonuniformCompetitive.Triangle345Proof

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

end NonuniformCompetitive.Triangle345Proof

end

/- Complete checked body: OfflinePath -/
section

set_option autoImplicit false

namespace NonuniformCompetitive.Triangle345Proof

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

lemma initial_pair_move_le {M : Type*} [MetricSpace M] (e : Vtx ≃ M) (he : ∀ x y, dist (e x) (e y) = triDist x y) (C₀ : Config 2 M) (h : Vtx) :
    moveCost C₀ (e ∘ pairConf h) ≤ (10:ℝ) := by
  have hi (i : Fin 2) : dist (C₀ i) (e (pairConf h i)) ≤ 5 := by
    rw [← e.apply_symm_apply (C₀ i),he]
    exact triDist_le _ _
  simp only [moveCost,Fin.sum_univ_two,Function.comp_apply]
  linarith [hi 0,hi 1]

lemma offlineCost_le_hole_path {M : Type*} [MetricSpace M] (e : Vtx ≃ M) (he : ∀ x y, dist (e x) (e y) = triDist x y)
    (C₀ : Config 2 M) (σ : List Vtx) (h : ℕ → Vtx)
    (hs : ∀ j : Fin σ.length, σ[j] ≠ h (j+1)) :
    offlineCost C₀ (σ.map e) ≤ (10:ℝ) + ∑ j ∈ Finset.range σ.length, triDist (h j) (h (j+1)) := by
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
  have hi : moveCost C₀ (S 0) ≤ (10:ℝ) := initial_pair_move_le e he C₀ (h 0)
  have hcost : (∑ j ∈ Finset.range (σ.map e).length, moveCost (S j) (S (j+1))) =
      ∑ j ∈ Finset.range σ.length, triDist (h j) (h (j+1)) := by
    simp only [List.length_map]
    apply Finset.sum_congr rfl
    intro j _hj
    have heq : moveCost (S j) (S (j+1)) = triMove (T j) (T (j+1)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact he _ _
    rw [heq]
    exact liftHolePath_cost h _ (Or.inl rfl) j
  rw [hcost] at hc
  linarith

end NonuniformCompetitive.Triangle345Proof

end

/- Complete checked body: HolePlans -/
section

set_option autoImplicit false

namespace NonuniformCompetitive.Triangle345Proof

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

noncomputable def cost (h : Vtx) : HolePlan → ℝ
  | .nil => 0
  | .cons _ g t => triDist h g+t.cost g

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

lemma cost_append (P Q : HolePlan) (h : Vtx) :
    (P.append Q).cost h=P.cost h+Q.cost (P.finish h) := by
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

lemma cost_eq_sum (P : HolePlan) (h : Vtx) :
    (∑ j ∈ Finset.range P.requests.length, triDist (P.holes h j) (P.holes h (j+1))) = P.cost h := by
  induction P generalizing h with
  | nil => simp [requests,cost]
  | cons r g P ih =>
    simp only [requests,List.length_cons]
    rw [Finset.sum_range_succ']
    simp only [holes,holes_zero]
    rw [ih]
    exact add_comm _ _

lemma offline_le {M : Type*} [MetricSpace M] (P : HolePlan) (hP : P.Valid)
    (e : Vtx ≃ M) (he : ∀ x y, dist (e x) (e y)=triDist x y)
    (C₀ : KServer.Config 2 M) (h : Vtx) :
    KServer.offlineCost C₀ (P.requests.map e) ≤ (10:ℝ)+P.cost h := by
  have hb := offlineCost_le_hole_path e he C₀ P.requests (P.holes h) (P.serves hP h)
  rw [P.cost_eq_sum h] at hb
  exact hb

end HolePlan

end NonuniformCompetitive.Triangle345Proof

end

/- Complete checked body: PhasePlans -/
section

set_option autoImplicit false
namespace NonuniformCompetitive.Triangle345Proof

def corePlan0 : HolePlan := (.cons 2 1 (.cons 0 1 .nil))
lemma corePlan0_facts : corePlan0.Valid ∧ corePlan0.requests=[2, 0] ∧ corePlan0.finish 2=1 ∧ corePlan0.cost 2=4 := by
  norm_num [corePlan0,HolePlan.Valid,HolePlan.requests,HolePlan.finish,HolePlan.cost,triDist,triNat,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Fin.ext_iff]

def corePlan1 : HolePlan := (.cons 2 1 (.cons 1 2 (.cons 0 2 (.cons 1 2 (.cons 0 2 .nil)))))
lemma corePlan1_facts : corePlan1.Valid ∧ corePlan1.requests=[2, 1, 0, 1, 0] ∧ corePlan1.finish 2=2 ∧ corePlan1.cost 2=8 := by
  norm_num [corePlan1,HolePlan.Valid,HolePlan.requests,HolePlan.finish,HolePlan.cost,triDist,triNat,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Fin.ext_iff]

def corePlan2 : HolePlan := (.cons 2 1 (.cons 1 2 (.cons 0 2 (.cons 1 2 (.cons 2 1 (.cons 0 1 .nil))))))
lemma corePlan2_facts : corePlan2.Valid ∧ corePlan2.requests=[2, 1, 0, 1, 2, 0] ∧ corePlan2.finish 2=1 ∧ corePlan2.cost 2=12 := by
  norm_num [corePlan2,HolePlan.Valid,HolePlan.requests,HolePlan.finish,HolePlan.cost,triDist,triNat,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Fin.ext_iff]

def corePlan3 : HolePlan := (.cons 2 0 (.cons 1 0 (.cons 0 1 (.cons 1 0 (.cons 2 0 (.cons 1 0 .nil))))))
lemma corePlan3_facts : corePlan3.Valid ∧ corePlan3.requests=[2, 1, 0, 1, 2, 1] ∧ corePlan3.finish 2=0 ∧ corePlan3.cost 2=11 := by
  norm_num [corePlan3,HolePlan.Valid,HolePlan.requests,HolePlan.finish,HolePlan.cost,triDist,triNat,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Fin.ext_iff]

def corePlan4 : HolePlan := (.cons 2 0 (.cons 1 0 (.cons 0 1 (.cons 2 1 .nil))))
lemma corePlan4_facts : corePlan4.Valid ∧ corePlan4.requests=[2, 1, 0, 2] ∧ corePlan4.finish 2=1 ∧ corePlan4.cost 2=8 := by
  norm_num [corePlan4,HolePlan.Valid,HolePlan.requests,HolePlan.finish,HolePlan.cost,triDist,triNat,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Fin.ext_iff]

def corePlan5 : HolePlan := (.cons 2 0 (.cons 1 0 (.cons 2 0 .nil)))
lemma corePlan5_facts : corePlan5.Valid ∧ corePlan5.requests=[2, 1, 2] ∧ corePlan5.finish 2=0 ∧ corePlan5.cost 2=5 := by
  norm_num [corePlan5,HolePlan.Valid,HolePlan.requests,HolePlan.finish,HolePlan.cost,triDist,triNat,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Fin.ext_iff]

def corePlan6 : HolePlan := (.cons 1 2 (.cons 0 2 (.cons 1 2 .nil)))
lemma corePlan6_facts : corePlan6.Valid ∧ corePlan6.requests=[1, 0, 1] ∧ corePlan6.finish 1=2 ∧ corePlan6.cost 1=4 := by
  norm_num [corePlan6,HolePlan.Valid,HolePlan.requests,HolePlan.finish,HolePlan.cost,triDist,triNat,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Fin.ext_iff]

def corePlan7 : HolePlan := (.cons 1 0 (.cons 0 1 (.cons 2 1 .nil)))
lemma corePlan7_facts : corePlan7.Valid ∧ corePlan7.requests=[1, 0, 2] ∧ corePlan7.finish 1=1 ∧ corePlan7.cost 1=6 := by
  norm_num [corePlan7,HolePlan.Valid,HolePlan.requests,HolePlan.finish,HolePlan.cost,triDist,triNat,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Fin.ext_iff]

def corePlan8 : HolePlan := (.cons 1 0 (.cons 2 0 .nil))
lemma corePlan8_facts : corePlan8.Valid ∧ corePlan8.requests=[1, 2] ∧ corePlan8.finish 1=0 ∧ corePlan8.cost 1=3 := by
  norm_num [corePlan8,HolePlan.Valid,HolePlan.requests,HolePlan.finish,HolePlan.cost,triDist,triNat,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Fin.ext_iff]

def corePlan9 : HolePlan := (.cons 0 2 (.cons 1 2 (.cons 0 2 .nil)))
lemma corePlan9_facts : corePlan9.Valid ∧ corePlan9.requests=[0, 1, 0] ∧ corePlan9.finish 0=2 ∧ corePlan9.cost 0=5 := by
  norm_num [corePlan9,HolePlan.Valid,HolePlan.requests,HolePlan.finish,HolePlan.cost,triDist,triNat,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Fin.ext_iff]

def corePlan10 : HolePlan := (.cons 0 1 (.cons 1 0 (.cons 2 0 .nil)))
lemma corePlan10_facts : corePlan10.Valid ∧ corePlan10.requests=[0, 1, 2] ∧ corePlan10.finish 0=0 ∧ corePlan10.cost 0=6 := by
  norm_num [corePlan10,HolePlan.Valid,HolePlan.requests,HolePlan.finish,HolePlan.cost,triDist,triNat,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Fin.ext_iff]

def corePlan11 : HolePlan := (.cons 0 1 (.cons 2 1 .nil))
lemma corePlan11_facts : corePlan11.Valid ∧ corePlan11.requests=[0, 2] ∧ corePlan11.finish 0=1 ∧ corePlan11.cost 0=3 := by
  norm_num [corePlan11,HolePlan.Valid,HolePlan.requests,HolePlan.finish,HolePlan.cost,triDist,triNat,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Fin.ext_iff]

lemma phase_core_plan (h : Vtx) : (phaseLaw h).All (fun z => ∃ P : HolePlan,
    P.Valid ∧ P.requests=z.1 ∧ P.finish h=z.2.1 ∧ P.cost h=z.2.2) := by
  fin_cases h
  · exact ⟨⟨⟨corePlan9,corePlan9_facts⟩,⟨corePlan10,corePlan10_facts⟩⟩,⟨corePlan11,corePlan11_facts⟩⟩
  · exact ⟨⟨⟨corePlan6,corePlan6_facts⟩,⟨corePlan7,corePlan7_facts⟩⟩,⟨corePlan8,corePlan8_facts⟩⟩
  · exact ⟨⟨corePlan0,corePlan0_facts⟩,⟨⟨⟨⟨corePlan1,corePlan1_facts⟩,⟨⟨corePlan2,corePlan2_facts⟩,⟨corePlan3,corePlan3_facts⟩⟩⟩,⟨corePlan4,corePlan4_facts⟩⟩,⟨corePlan5,corePlan5_facts⟩⟩⟩

def resetPlan (h : Vtx) : ℕ → HolePlan
  | 0 => .nil
  | k+1 => (resetPlan h k).append (.cons (pairConf h 0) h (.cons (pairConf h 1) h .nil))

lemma resetPlan_facts (h : Vtx) (k : ℕ) :
    (resetPlan h k).Valid ∧ (resetPlan h k).requests=resetWord h k ∧
    (resetPlan h k).finish h=h ∧ (resetPlan h k).cost h=0 := by
  have h0 : pairConf h 0 ≠ h := (pairConf_mem h _).mp ⟨0,rfl⟩
  have h1 : pairConf h 1 ≠ h := (pairConf_mem h _).mp ⟨1,rfl⟩
  induction k with
  | zero => simp [resetPlan,resetWord,HolePlan.Valid,HolePlan.requests,HolePlan.finish,HolePlan.cost]
  | succ k ih =>
    refine ⟨HolePlan.valid_append _ _ ih.1 ⟨h0,h1,trivial⟩,?_,?_,?_⟩
    · simp only [resetPlan,HolePlan.requests_append,ih.2.1,HolePlan.requests,resetWord]
    · simp only [resetPlan,HolePlan.finish_append,HolePlan.finish]
    · simp only [resetPlan,HolePlan.cost_append,ih.2.2.1,ih.2.2.2,HolePlan.cost,triDist_self,add_zero]

lemma phase_plan (h : Vtx) : (phaseLaw h).All (fun z => ∃ P : HolePlan,
    P.Valid ∧ P.requests=phaseWord h z ∧ P.finish h=z.2.1 ∧ P.cost h=z.2.2) := by
  apply (phaseLaw h).all_mono (phase_core_plan h)
  rintro z ⟨P,hP,hr,hf,hc⟩
  obtain ⟨hR,hRr,hRf,hRc⟩ := resetPlan_facts h 10
  obtain ⟨hS,hSr,hSf,hSc⟩ := resetPlan_facts z.2.1 10
  refine ⟨(resetPlan h 10).append (P.append (resetPlan z.2.1 10)),
    HolePlan.valid_append _ _ hR (HolePlan.valid_append _ _ hP hS),?_,?_,?_⟩
  · simp only [HolePlan.requests_append,hRr,hr,hSr,phaseWord]
  · simp only [HolePlan.finish_append,hRf,hf,hSf]
  · simp only [HolePlan.cost_append,hRc,hRf,hc,hf,hSc,add_zero,zero_add]

end NonuniformCompetitive.Triangle345Proof
end

/- Complete checked body: LazySimulation -/
section

set_option autoImplicit false

namespace NonuniformCompetitive.Triangle345Proof

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

end NonuniformCompetitive.Triangle345Proof

end

/- Complete checked body: LazyTriangle -/
section

set_option autoImplicit false

namespace NonuniformCompetitive.Triangle345Proof

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

end NonuniformCompetitive.Triangle345Proof

end

/- Complete checked body: OfflineAdversary -/
section

set_option autoImplicit false
namespace NonuniformCompetitive.Triangle345Proof

lemma repeated_plan (N : ℕ) (h : Vtx) : (repeatedLaw N h).All (fun z => ∃ P : HolePlan,
    P.Valid ∧ P.requests=z.1 ∧ P.finish h=z.2.1 ∧ P.cost h=z.2.2) := by
  induction N generalizing h with
  | zero => exact ⟨.nil,trivial,rfl,rfl,rfl⟩
  | succ N ih =>
    rw [repeatedLaw,FiniteLaw.all_bind]
    apply (phaseLaw h).all_mono (phase_plan h)
    rintro z ⟨P,hP,hr,hf,hc⟩
    rw [FiniteLaw.all_map]
    apply (repeatedLaw N z.2.1).all_mono (ih z.2.1)
    rintro w ⟨Q,hQ,hQr,hQf,hQc⟩
    refine ⟨P.append Q,P.valid_append Q hP hQ,?_,?_,?_⟩
    · simp only [HolePlan.requests_append,hr,hQr]
    · simp only [HolePlan.finish_append,hf,hQf]
    · simp only [HolePlan.cost_append,hc,hf,hQc]

lemma offline_repeated {M : Type*} [MetricSpace M] (e : Vtx ≃ M)
    (he : ∀ x y,dist (e x) (e y)=triDist x y) (C₀ : KServer.Config 2 M) (N : ℕ) (h : Vtx) :
    (repeatedLaw N h).All (fun z => KServer.offlineCost C₀ (z.1.map e) ≤ 10+z.2.2) := by
  apply (repeatedLaw N h).all_mono (repeated_plan N h)
  rintro z ⟨P,hP,hr,_hf,hc⟩
  have hb := P.offline_le hP e he C₀ h
  rwa [hr,hc] at hb

lemma repeated_original_lower {M : Type*} [MetricSpace M] (e : Vtx ≃ M)
    (he : ∀ x y,dist (e x) (e y)=triDist x y) (A : KServer.OnlineAlgorithm 2 M) (N : ℕ) (h : Vtx) :
    (1652/1069:ℝ)*(repeatedLaw N h).realMean (fun z => z.2.2)-1 ≤
      (repeatedLaw N h).realMean (fun z => A.cost (z.1.map e)) := by
  obtain ⟨B,hB,_hinit,hcost⟩ := exists_lazy_dominated A
  have hl := repeated_lower_simple N h (TriPolicy.ofOriginal e B) (TriPolicy.ofOriginal_lazy e B hB)
  simp_rw [TriPolicy.ofOriginal_cost e he] at hl
  exact hl.trans ((repeatedLaw N h).realMean_mono
    ((repeatedLaw N h).all_of_forall (fun z => hcost (z.1.map e))))

end NonuniformCompetitive.Triangle345Proof
end

/- Complete checked body: LowerBound -/
section

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

namespace NonuniformCompetitive.Triangle345Proof
open KServer

lemma offline_nonneg {M : Type*} [MetricSpace M] (C₀ : Config 2 M) (σ : List M) :
    0 ≤ offlineCost C₀ σ := by
  apply Real.sInf_nonneg
  rintro c ⟨S,_hS,rfl⟩
  exact Finset.sum_nonneg (fun _ _ => move_nonneg _ _)

lemma randomized_cost_law_lower {M : Type*} [MetricSpace M] (e : Vtx ≃ M)
    (Q : FiniteLaw Outcome) (c : ℝ)
    (hc : ∀ B : OnlineAlgorithm 2 M,c ≤ Q.realMean (fun z => B.cost (z.1.map e)))
    (A : RandomizedAlgorithm 2 M) :
    ENNReal.ofReal c ≤ Q.mean (fun z => A.expCost (z.1.map e)) := by
  let := A.ms
  let := A.prob
  unfold RandomizedAlgorithm.expCost
  rw [FiniteLaw.mean_lintegral A.μ Q (fun (z : Outcome) ω => ENNReal.ofReal ((A.alg ω).cost (z.1.map e)))
    (fun z => ENNReal.measurable_ofReal.comp (A.meas (z.1.map e)))]
  calc
    _ = ∫⁻ _ω, ENNReal.ofReal c ∂A.μ := by simp
    _ ≤ _ := by
      apply lintegral_mono
      intro ω
      dsimp only
      rw [FiniteLaw.mean_ofReal Q (f := fun z => (A.alg ω).cost (z.1.map e))
        (FiniteLaw.all_of_forall Q (fun z => cost_nonneg _ _))]
      exact ENNReal.ofReal_le_ofReal (hc (A.alg ω))

lemma randomized_repeated_lower {M : Type*} [MetricSpace M] (e : Vtx ≃ M)
    (he : ∀ x y,dist (e x) (e y)=triDist x y) (A : RandomizedAlgorithm 2 M) (N : ℕ) :
    ENNReal.ofReal ((1652/1069:ℝ)*(repeatedLaw N 2).realMean (fun z => z.2.2)-1) ≤
      (repeatedLaw N 2).mean (fun z => A.expCost (z.1.map e)) :=
  randomized_cost_law_lower e (repeatedLaw N 2) _ (fun B => repeated_original_lower e he B N 2) A

lemma numeric_lower {M : Type*} [MetricSpace M] (e : Vtx ≃ M)
    (he : ∀ x y,dist (e x) (e y)=triDist x y) (C₀ : Config 2 M)
    (A : RandomizedAlgorithm 2 M) (ρ a : ℝ)
    (hA : ∀ σ,A.expCost σ ≤ ENNReal.ofReal (ρ*offlineCost C₀ σ+a)) (N : ℕ) :
    (1652/1069:ℝ)*(repeatedLaw N 2).realMean (fun z => z.2.2)-1 ≤
      max ρ 0*(10+(repeatedLaw N 2).realMean (fun z => z.2.2))+max a 0 := by
  let C := max ρ 0
  let D := max a 0
  have hC : 0 ≤ C := le_max_right _ _
  have hD : 0 ≤ D := le_max_right _ _
  let g : Outcome → ℝ := fun z => C*(10+z.2.2)+D
  have hz := repeated_benchmark N 2
  have hg : (repeatedLaw N 2).All (fun z => 0 ≤ g z) := by
    apply (repeatedLaw N 2).all_mono hz
    intro z hz
    have hn : 0 ≤ z.2.2 := (by positivity : (0:ℝ) ≤ 3*N).trans hz
    dsimp [g]
    positivity
  have hmean := (repeatedLaw N 2).mean_mono
    ((repeatedLaw N 2).all_mono (offline_repeated e he C₀ N 2) (fun z ho =>
      (hA _).trans (ENNReal.ofReal_le_ofReal (show ρ*offlineCost C₀ (z.1.map e)+a ≤ g z from by
        have hn := offline_nonneg C₀ (z.1.map e)
        have hc : ρ ≤ C := le_max_left _ _
        have ha : a ≤ D := le_max_left _ _
        dsimp [g]
        calc
          _ ≤ C*offlineCost C₀ (z.1.map e)+D := by nlinarith
          _ ≤ _ := by gcongr))))
  have hm : (repeatedLaw N 2).realMean g = C*(10+(repeatedLaw N 2).realMean (fun z => z.2.2))+D := by
    dsimp only [g]
    simp_rw [mul_comm C]
    rw [FiniteLaw.realMean_add,FiniteLaw.realMean_const,FiniteLaw.realMean_mul_const,
      FiniteLaw.realMean_add,FiniteLaw.realMean_const]
  rw [FiniteLaw.mean_ofReal _ hg,hm] at hmean
  have hn : 0 ≤ C*(10+(repeatedLaw N 2).realMean (fun z => z.2.2))+D := by
    rw [←hm]
    exact FiniteLaw.realMean_nonneg _ hg
  exact (ENNReal.ofReal_le_ofReal_iff hn).mp ((randomized_repeated_lower e he A N).trans hmean)

theorem no_better_ratio_direct {M : Type} [MetricSpace M] (a b c : M)
    (hM : ∀ x:M,x=a ∨ x=b ∨ x=c)
    (hab : dist a b=3) (hac : dist a c=5) (hbc : dist b c=4)
    (C₀ : Config 2 M) (A : RandomizedAlgorithm 2 M) (ρ : ℝ) (hA : A.IsCompetitiveFrom C₀ ρ) :
    (1652/1069:ℝ) ≤ ρ := by
  let e : Vtx ≃ M := Equiv.ofBijective (val a b c)
    ⟨val_injective a b c hab hac hbc,val_surjective a b c hM⟩
  have he : ∀ x y,dist (e x) (e y)=triDist x y := val_dist a b c hab hac hbc
  obtain ⟨a₀,ha⟩ := hA.2
  have hr : (1652/1069:ℝ) ≤ max ρ 0 := by
    by_contra hn
    have hp : 0 < (1652/1069:ℝ)-max ρ 0 := sub_pos.mpr (lt_of_not_ge hn)
    obtain ⟨N,hN⟩ := exists_nat_gt ((10*max ρ 0+max a₀ 0+1)/(3*((1652/1069:ℝ)-max ρ 0)))
    have hlt : 10*max ρ 0+max a₀ 0+1 < (N:ℝ)*(3*((1652/1069:ℝ)-max ρ 0)) :=
      (div_lt_iff₀ (mul_pos (by norm_num) hp)).mp hN
    have hnum := numeric_lower e he C₀ A ρ a₀ ha N
    have hmean : (3*N:ℝ) ≤ (repeatedLaw N 2).realMean (fun z => z.2.2) := by
      calc
        _ = (repeatedLaw N 2).realMean (fun _ => (3*N:ℝ)) := (FiniteLaw.realMean_const _ _).symm
        _ ≤ _ := (repeatedLaw N 2).realMean_mono (repeated_benchmark N 2)
    nlinarith
  by_cases hρ : 0 ≤ ρ
  · simpa only [max_eq_left hρ] using hr
  · rw [max_eq_right (le_of_not_ge hρ)] at hr
    norm_num at hr

end NonuniformCompetitive.Triangle345Proof

end

/- Complete checked body: WorkFunctions -/
section

namespace NonuniformCompetitive.Triangle345Proof

open scoped BigOperators

def WorkLip (w : Vtx → ℝ) : Prop :=
  ∀ h g, w h ≤ w g + triDist h g

def workValue (w : Vtx → ℝ) (C : Fin 2 → Vtx) : ℝ :=
  min (w 0 + pairMatch 0 C) (min (w 1 + pairMatch 1 C) (w 2 + pairMatch 2 C))

def workStep (w : Vtx → ℝ) (r h : Vtx) : ℝ :=
  if r = 0 then min (w 1 + triDist 1 h) (w 2 + triDist 2 h)
  else if r = 1 then min (w 0 + triDist 0 h) (w 2 + triDist 2 h)
  else min (w 0 + triDist 0 h) (w 1 + triDist 1 h)

theorem workValue_le (w : Vtx → ℝ) (C : Fin 2 → Vtx) (h : Vtx) :
    workValue w C ≤ w h + pairMatch h C := by
  fin_cases h
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

theorem workValue_attained (w : Vtx → ℝ) (C : Fin 2 → Vtx) :
    ∃ h, workValue w C = w h + pairMatch h C := by
  unfold workValue
  rcases le_total (w 0 + pairMatch 0 C)
    (min (w 1 + pairMatch 1 C) (w 2 + pairMatch 2 C)) with h | h
  · exact ⟨0,min_eq_left h⟩
  · rw [min_eq_right h]
    rcases le_total (w 1 + pairMatch 1 C) (w 2 + pairMatch 2 C) with h | h
    · exact ⟨1,min_eq_left h⟩
    · exact ⟨2,min_eq_right h⟩

theorem workValue_move (w : Vtx → ℝ)
    (C D : Fin 2 → Vtx) : workValue w D ≤ workValue w C + triMove C D := by
  obtain ⟨h,hh⟩ := workValue_attained w C
  have hm := pairMatch_move h C D
  have hv := workValue_le w D h
  rw [hh]
  linarith

theorem workValue_add (w : Vtx → ℝ) (a : ℝ) (C : Fin 2 → Vtx) :
    workValue (fun h => a + w h) C = a + workValue w C := by
  simp only [workValue, add_assoc, min_add_add_left]

theorem workValue_nonneg (w : Vtx → ℝ) (hw : ∀ h, 0 ≤ w h)
    (C : Fin 2 → Vtx) : 0 ≤ workValue w C := by
  obtain ⟨h,hh⟩ := workValue_attained w C
  rw [hh]
  exact add_nonneg (hw h) (pairMatch_nonneg h C)

theorem workStep_le (w : Vtx → ℝ) (r h g : Vtx) (hg : g ≠ r) :
    workStep w r h ≤ w g + triDist g h := by
  fin_cases r <;> fin_cases g <;> simp [workStep] at *

theorem workStep_attained (w : Vtx → ℝ) (r h : Vtx) :
    ∃ g, g ≠ r ∧ workStep w r h = w g + triDist g h := by
  fin_cases r
  · by_cases hh : w 1 + triDist 1 h ≤ w 2 + triDist 2 h
    · exact ⟨1,by decide,by simp [workStep,min_eq_left hh]⟩
    · exact ⟨2,by decide,by simp [workStep,min_eq_right (le_of_not_ge hh)]⟩
  · by_cases hh : w 0 + triDist 0 h ≤ w 2 + triDist 2 h
    · exact ⟨0,by decide,by simp [workStep,min_eq_left hh]⟩
    · exact ⟨2,by decide,by simp [workStep,min_eq_right (le_of_not_ge hh)]⟩
  · by_cases hh : w 0 + triDist 0 h ≤ w 1 + triDist 1 h
    · exact ⟨0,by decide,by simp [workStep,min_eq_left hh]⟩
    · exact ⟨1,by decide,by simp [workStep,min_eq_right (le_of_not_ge hh)]⟩

theorem workStep_lip (w : Vtx → ℝ) (r : Vtx) :
    WorkLip (workStep w r) := by
  intro h g
  obtain ⟨q,hq,heq⟩ := workStep_attained w r g
  have hl := workStep_le w r h q hq
  have ht := triDist_triangle q g h
  rw [triDist_symm g h] at ht
  rw [heq]
  linarith

def pairMatchNat (h : Vtx) (C : Fin 2 → Vtx) : ℕ :=
  min (triNat (pairConf h 0) (C 0)+triNat (pairConf h 1) (C 1))
    (triNat (pairConf h 1) (C 0)+triNat (pairConf h 0) (C 1))

theorem pairMatchNat_cast (h : Vtx) (C : Fin 2 → Vtx) :
    (pairMatchNat h C:ℝ)=pairMatch h C := by
  simp [pairMatchNat,pairMatch,triMove,swapConf,Fin.sum_univ_two,triDist]

theorem serving_pair_nat : ∀ h r x y : Vtx, x=r ∨ y=r →
    ∃ g:Vtx,g≠r ∧ triNat h g+pairMatchNat g ![x,y] ≤ pairMatchNat h ![x,y] := by decide

/-- A serving configuration can be reached through a serving pair without additional movement. -/
theorem serving_pair_path (h r : Vtx) (C : Fin 2 → Vtx) (hC : ∃ i,C i=r) :
    ∃ g,g≠r ∧ triDist h g+pairMatch g C ≤ pairMatch h C := by
  have hc : C 0=r ∨ C 1=r := by simpa only [Fin.exists_fin_two] using hC
  have hCeq : C = ![C 0,C 1] := by ext i; fin_cases i <;> rfl
  obtain ⟨g,hg,he⟩ := serving_pair_nat h r (C 0) (C 1) hc
  refine ⟨g,hg,?_⟩
  rw [hCeq,←pairMatchNat_cast,←pairMatchNat_cast]
  change (triNat h g:ℝ)+(pairMatchNat g ![C 0,C 1]:ℝ) ≤ (pairMatchNat h ![C 0,C 1]:ℝ)
  exact_mod_cast he

theorem workValue_step_serves (w : Vtx → ℝ)
    (hw : WorkLip w) (r : Vtx) (C : Fin 2 → Vtx) (hC : ∃ i, C i = r) :
    workValue (workStep w r) C ≤ workValue w C := by
  obtain ⟨h,hh⟩ := workValue_attained w C
  obtain ⟨g,hg,hpath⟩ := serving_pair_path h r C hC
  have hval := workValue_le (workStep w r) C g
  have hs := workStep_le w r g g hg
  simp only [triDist_self,add_zero] at hs
  have hl := hw g h
  rw [triDist_symm g h] at hl
  rw [hh]
  linarith

end NonuniformCompetitive.Triangle345Proof
end

/- Complete checked body: FiniteData -/
section

namespace NonuniformCompetitive.Triangle345Proof

open scoped BigOperators

abbrev WorkId := Fin 12
abbrev Seed := Fin 10

noncomputable def ratio : ℝ := 1652/1069

def stateWorkNat (s : WorkId) (h : Vtx) : ℕ := ![![0,1,5],![0,3,1],![0,3,3],![0,3,5],![1,0,4],![1,4,0],![3,0,0],![3,0,2],![3,0,4],![3,4,0],![5,2,0],![5,4,0]] s h

def nextState (s : WorkId) (r : Vtx) : WorkId := ![![8,3,0],![10,1,3],![6,2,3],![7,3,3],![8,2,4],![11,5,3],![6,9,8],![7,5,8],![8,1,8],![11,9,0],![10,11,8],![11,11,4]] s r

def gain (s : WorkId) (r : Vtx) : ℕ := ![![1,0,0],![1,0,0],![3,0,0],![3,0,0],![0,1,0],![0,0,1],![0,0,0],![0,2,0],![0,3,0],![0,0,3],![0,0,2],![0,0,4]] s r

def seedNat (z : Seed) : ℕ := ![507,129,380,97,368,480,200,330,258,458] z

def stateHole (s : WorkId) (z : Seed) : Vtx := ![![1,1,1,0,0,0,0,0,0,0],![2,2,2,2,0,0,0,0,0,0],![2,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0],![1,1,1,1,1,1,1,0,0,0],![2,2,2,2,2,2,0,0,0,0],![2,2,2,2,2,1,1,1,1,1],![2,2,1,1,1,1,1,1,1,1],![1,1,1,1,1,1,1,1,1,1],![2,2,2,2,2,2,2,2,2,0],![2,2,2,2,2,2,2,2,1,1],![2,2,2,2,2,2,2,2,2,2]] s z

def potentialNat (s : WorkId) : ℕ := ![4429,6946,3916,1381,5950,6230,8736,5356,2812,2290,2864,0] s

def initialState : WorkId := 11

def stateWork (s : WorkId) (h : Vtx) : ℝ := stateWorkNat s h
noncomputable def seedWeight (z : Seed) : ℝ := (seedNat z:ℝ)/3207
noncomputable def potential (s : WorkId) : ℝ := (potentialNat s:ℝ)/3207
noncomputable def seedMean (f : Seed → ℝ) : ℝ := ∑ z, seedWeight z*f z

def workNatStep (w : Vtx → ℕ) (r h : Vtx) : ℕ :=
  if r=0 then min (w 1+triNat 1 h) (w 2+triNat 2 h)
  else if r=1 then min (w 0+triNat 0 h) (w 2+triNat 2 h)
  else min (w 0+triNat 0 h) (w 1+triNat 1 h)

theorem workStep_cast (w : Vtx → ℕ) (r h : Vtx) :
    workStep (fun a => (w a:ℝ)) r h=(workNatStep w r h:ℝ) := by
  fin_cases r <;> fin_cases h <;> simp [workStep,workNatStep,triNat,triDist,Fin.ext_iff]
  all_goals
    rw [← min_add_add_right]
    congr 1
    ring

theorem stateWorkNat_update : ∀ s r h,
    workNatStep (stateWorkNat s) r h=gain s r+stateWorkNat (nextState s r) h := by decide

theorem stateWork_update (s : WorkId) (r h : Vtx) :
    workStep (stateWork s) r h=(gain s r:ℝ)+stateWork (nextState s r) h := by
  change workStep (fun a => (stateWorkNat s a:ℝ)) r h=_
  rw [workStep_cast,stateWorkNat_update,Nat.cast_add]
  rfl

theorem stateWork_lip (s : WorkId) : WorkLip (stateWork s) := by
  have H : ∀ s h g, stateWorkNat s h ≤ stateWorkNat s g+triNat h g := by decide
  intro h g
  change (stateWorkNat s h:ℝ) ≤ (stateWorkNat s g:ℝ)+(triNat h g:ℝ)
  exact_mod_cast H s h g

theorem stateWork_nonneg (s : WorkId) (h : Vtx) : 0 ≤ stateWork s h := Nat.cast_nonneg _

theorem initial_work (h : Vtx) : stateWork initialState h=triDist 2 h := by fin_cases h <;> rfl

theorem stateHole_serves : ∀ s r z, stateHole (nextState s r) z ≠ r := by decide

theorem initial_hole : ∀ z, stateHole initialState z=2 := by decide

theorem seedNat_sum : ∑ z : Seed, seedNat z=3207 := by decide

theorem seedWeight_nonneg (z : Seed) : 0 ≤ seedWeight z := by unfold seedWeight; positivity

theorem seedWeight_sum : ∑ z : Seed, seedWeight z=1 := by
  unfold seedWeight
  rw [← Finset.sum_div,← Nat.cast_sum,seedNat_sum]
  norm_num

theorem potential_nonneg (s : WorkId) : 0 ≤ potential s := by unfold potential; positivity

@[simp] theorem potential_initial : potential initialState=0 := by
  have h : potentialNat initialState=0 := by decide
  unfold potential
  rw [h]
  norm_num

theorem weighted_step_certificate : ∀ s r,
    (∑ z : Seed, seedNat z*triNat (stateHole s z) (stateHole (nextState s r) z))+
      potentialNat (nextState s r)=4956*gain s r+potentialNat s := by decide

theorem seedMean_step (s : WorkId) (r : Vtx) :
    seedMean (fun z => triDist (stateHole s z) (stateHole (nextState s r) z))+potential (nextState s r)=
      ratio*(gain s r)+potential s := by
  have h := weighted_step_certificate s r
  have hr := congrArg (fun n : ℕ => (n:ℝ)) h
  push_cast at hr
  unfold seedMean seedWeight potential ratio triDist
  simp only [div_mul_eq_mul_div,← Finset.sum_div]
  linarith

end NonuniformCompetitive.Triangle345Proof

end

/- Complete checked body: WorkBank -/
section

namespace NonuniformCompetitive.Triangle345Proof

open scoped BigOperators

structure WorkState where
  bank : ℕ
  state : WorkId

def workTransition (s : WorkState) (r : Vtx) : WorkState :=
  ⟨s.bank+gain s.state r,nextState s.state r⟩

def workRun (h : List Vtx) : WorkState := h.foldl workTransition ⟨0,initialState⟩

@[simp] theorem workRun_nil : workRun []=⟨0,initialState⟩ := rfl

theorem workRun_append_one (h : List Vtx) (r : Vtx) :
    workRun (h++[r])=workTransition (workRun h) r := by simp [workRun,List.foldl_append]

theorem initialWorkValue_le (C : Fin 2 → Vtx) : workValue (stateWork initialState) C ≤ 10 := by
  have hw := workValue_le (stateWork initialState) C 2
  rw [initial_work,triDist_self,zero_add] at hw
  exact hw.trans ((min_le_left _ _).trans (triMove_le _ _))

theorem workValue_transition (h : List Vtx) (r : Vtx) (C D : Fin 2 → Vtx) (hD : ∃ i,D i=r) :
    ((workRun (h++[r])).bank:ℝ)+workValue (stateWork (workRun (h++[r])).state) D ≤
      (workRun h).bank+workValue (stateWork (workRun h).state) C+triMove C D := by
  have hs := workValue_step_serves (stateWork (workRun h).state) (stateWork_lip _) r D hD
  have hm := workValue_move (stateWork (workRun h).state) C D
  have he : workStep (stateWork (workRun h).state) r=
      fun a => (gain (workRun h).state r:ℝ)+stateWork (nextState (workRun h).state r) a :=
    funext fun a => stateWork_update _ r a
  rw [he,workValue_add] at hs
  rw [workRun_append_one]
  simp only [workTransition,Nat.cast_add]
  linarith

theorem bank_le_schedule (h : List Vtx) (S : ℕ → Fin 2 → Vtx)
    (hs : ∀ j (hj:j<h.length),∃i,S (j+1) i=h[j]) :
    ((workRun h).bank:ℝ) ≤ (∑ j ∈ Finset.range h.length,triMove (S j) (S (j+1)))+10 := by
  have hind : ∀ t,t≤h.length → ((workRun (h.take t)).bank:ℝ)+
      workValue (stateWork (workRun (h.take t)).state) (S t) ≤
        (∑ j ∈ Finset.range t,triMove (S j) (S (j+1)))+10 := by
    intro t
    induction t with
    | zero => intro _; simpa using initialWorkValue_le (S 0)
    | succ t ih =>
      intro ht
      have ht' : t<h.length := by omega
      have hi := ih (by omega)
      have hn := workValue_transition (h.take t) h[t] (S t) (S (t+1)) (hs t ht')
      rw [←List.take_succ_eq_append_getElem ht'] at hn
      rw [Finset.sum_range_succ]
      linarith
  have hi := hind h.length le_rfl
  simp only [List.take_length] at hi
  have hz := workValue_nonneg (stateWork (workRun h).state) (stateWork_nonneg _) (S h.length)
  linarith

theorem bank_le_offline {M : Type*} [MetricSpace M] (e : Vtx ≃ M)
    (he : ∀x y,dist (e x) (e y)=triDist x y) (C₀ : KServer.Config 2 M) (h : List Vtx) :
    ((workRun h).bank:ℝ) ≤ KServer.offlineCost C₀ (h.map e)+10 := by
  classical
  let σ := h.map e
  have hex : Set.Nonempty {c:ℝ | ∃ S:ℕ → KServer.Config 2 M,
      KServer.ServesFrom C₀ σ S ∧ c=∑j∈Finset.range σ.length,KServer.moveCost (S j) (S (j+1))} := by
    let S : ℕ → KServer.Config 2 M := fun t => if t=0 then C₀ else fun _ => σ[t-1]?.getD (C₀ 0)
    refine ⟨_,S,?_,rfl⟩
    constructor
    · simp [S]
    · intro j
      refine ⟨0,?_⟩
      simp [S]
  have hl : ((workRun h).bank:ℝ)-10 ≤ KServer.offlineCost C₀ σ := by
    apply le_csInf hex
    rintro z ⟨S,hS,rfl⟩
    let T : ℕ → Fin 2 → Vtx := fun j i => e.symm (S j i)
    have ht : ∀j (hj:j<h.length),∃i,T (j+1) i=h[j] := by
      intro j hj
      obtain ⟨i,hi⟩ := hS.2 ⟨j,by simpa [σ] using hj⟩
      refine ⟨i,?_⟩
      apply e.injective
      simpa [T,σ] using hi
    have hb := bank_le_schedule h T ht
    have hc (j:ℕ) : triMove (T j) (T (j+1))=KServer.moveCost (S j) (S (j+1)) := by
      unfold triMove KServer.moveCost
      apply Finset.sum_congr rfl
      intro i _
      simpa [T] using (he (e.symm (S j i)) (e.symm (S (j+1) i))).symm
    simp only [hc] at hb
    simpa [σ] using (sub_le_iff_le_add.mpr hb)
  linarith

end NonuniformCompetitive.Triangle345Proof

end

/- Complete checked body: UpperPolicy -/
section

namespace NonuniformCompetitive.Triangle345Proof

open scoped BigOperators

noncomputable def seedHistoryHole (z : Seed) (h : List Vtx) : Vtx := stateHole (workRun h).state z

theorem seedHistoryHole_serves (z : Seed) (h : List Vtx) (r : Vtx) :
    seedHistoryHole z (h++[r]) ≠ r := by
  rw [seedHistoryHole,workRun_append_one]
  exact stateHole_serves _ r z

noncomputable def upperPolicy (z : Seed) : TriPolicy :=
  holePolicy (seedHistoryHole z) (seedHistoryHole_serves z) (pairConf 2)
    (by simp [seedHistoryHole,initial_hole,FitsPair])

@[simp] theorem upperPolicy_initial (z : Seed) : (upperPolicy z).conf []=pairConf 2 := rfl

theorem upperPolicy_step_cost (z : Seed) (h : List Vtx) (r : Vtx) :
    triMove ((upperPolicy z).conf h) ((upperPolicy z).conf (h++[r]))=
      triDist (stateHole (workRun h).state z) (stateHole (nextState (workRun h).state r) z) := by
  change triMove (holeRun (seedHistoryHole z) (pairConf 2) h).2
    (holeRun (seedHistoryHole z) (pairConf 2) (h++[r])).2=_
  rw [holeRun_append_one]
  simp only [holeTransition,holeRun_prefix]
  rw [pairChange_cost _ _ _ (holeRun_fits (seedHistoryHole z) (pairConf 2)
    (by simp [seedHistoryHole,initial_hole,FitsPair]) h)]
  simp only [seedHistoryHole,workRun_append_one,workTransition]

theorem seedMean_const (c : ℝ) : seedMean (fun _ => c)=c := by
  rw [seedMean,←Finset.sum_mul,seedWeight_sum,one_mul]

theorem seedMean_add (f g : Seed → ℝ) : seedMean (fun z => f z+g z)=seedMean f+seedMean g := by
  simp [seedMean,mul_add,Finset.sum_add_distrib]

theorem seedMean_mono (f g : Seed → ℝ) (h : ∀z,f z≤g z) : seedMean f ≤ seedMean g :=
  Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (h z) (seedWeight_nonneg z)

theorem upper_mean_potential (h : List Vtx) :
    seedMean (fun z => triCost (upperPolicy z) h)+potential (workRun h).state=ratio*(workRun h).bank := by
  induction h using List.reverseRecOn with
  | nil => simp [seedMean,triCost]
  | append_singleton h r ih =>
    have he : (fun z:Seed => triCost (upperPolicy z) (h++[r]))=fun z =>
        triCost (upperPolicy z) h+triDist (stateHole (workRun h).state z)
          (stateHole (nextState (workRun h).state r) z) := by
      funext z
      rw [triCost_append_one,upperPolicy_step_cost]
    rw [he,seedMean_add]
    have hs := seedMean_step (workRun h).state r
    rw [workRun_append_one]
    simp only [workTransition,Nat.cast_add]
    nlinarith

theorem upper_mean_bound (h : List Vtx) :
    seedMean (fun z => triCost (upperPolicy z) h) ≤ ratio*(workRun h).bank := by
  have he := upper_mean_potential h
  have hz := potential_nonneg (workRun h).state
  linarith

def changeInitial (A : TriPolicy) (C₀ : Fin 2 → Vtx) : TriPolicy where
  conf h := if h=[] then C₀ else A.conf h
  serves h r := by simpa using A.serves h r

@[simp] theorem changeInitial_nil (A : TriPolicy) (C₀ : Fin 2 → Vtx) :
    (changeInitial A C₀).conf []=C₀ := by simp [changeInitial]

theorem changeInitial_cost (A : TriPolicy) (C₀ : Fin 2 → Vtx) (h : List Vtx) :
    triCost (changeInitial A C₀) h ≤ triCost A h+10 := by
  by_cases hh : h=[]
  · subst h; simp
  · have hlen : 0<h.length := List.length_pos_iff.mpr hh
    have hs : ∀j∈Finset.range h.length,
        triMove ((changeInitial A C₀).conf (h.take j)) ((changeInitial A C₀).conf (h.take (j+1))) ≤
          triMove (A.conf (h.take j)) (A.conf (h.take (j+1)))+(if j=0 then 10 else 0) := by
      intro j _hj
      have ht : h.take (j+1)≠[] := by simp [List.take_eq_nil_iff,hh]
      by_cases hj : j=0
      · subst j
        simp only [changeInitial,List.take_zero,if_true,if_neg ht,Nat.zero_add]
        have hu := triMove_le C₀ (A.conf (h.take 1))
        have hz := triMove_nonneg (A.conf []) (A.conf (h.take 1))
        linarith
      · have ht0 : h.take j≠[] := by simp [List.take_eq_nil_iff,hh,hj]
        simp [changeInitial,hj,ht,ht0]
    have hsum := Finset.sum_le_sum hs
    simpa [triCost,Finset.sum_add_distrib,hlen] using hsum

theorem upper_mean_from (C₀ : Fin 2 → Vtx) (h : List Vtx) :
    seedMean (fun z => triCost (changeInitial (upperPolicy z) C₀) h) ≤ ratio*(workRun h).bank+10 := by
  have hm := seedMean_mono _ _ (fun z => changeInitial_cost (upperPolicy z) C₀ h)
  rw [seedMean_add,seedMean_const] at hm
  have hb := upper_mean_bound h
  linarith

end NonuniformCompetitive.Triangle345Proof

end

/- Complete checked body: RandomizedUpper -/
section

open MeasureTheory
open scoped ENNReal

namespace NonuniformCompetitive.Triangle345Proof


noncomputable def seedPMF : PMF Seed :=
  PMF.ofFintype (fun z => ENNReal.ofReal (seedWeight z)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => seedWeight_nonneg z),
      seedWeight_sum,ENNReal.ofReal_one])

@[simp] theorem seedPMF_apply (z : Seed) :
    seedPMF z=ENNReal.ofReal (seedWeight z) := rfl

noncomputable def mixedUpper {M : Type} [MetricSpace M]
    (e : Vtx ≃ M) (C₀ : KServer.Config 2 M) : KServer.RandomizedAlgorithm 2 M := by
  classical
  let : MeasurableSpace Seed := ⊤
  exact { ι := Seed
          μ := (seedPMF).toMeasure
          prob := inferInstance
          alg := fun z => (changeInitial (upperPolicy z) (e.symm ∘ C₀)).toOriginal e
          meas := fun _ => measurable_of_countable _ }

theorem mixedUpper_expCost {M : Type} [MetricSpace M]
    (e : Vtx ≃ M) (he : ∀ x y, dist (e x) (e y)=triDist x y)
    (C₀ : KServer.Config 2 M) (h : List M) :
    (mixedUpper e C₀).expCost h =
      ENNReal.ofReal (seedMean (fun z => triCost
        (changeInitial (upperPolicy z) (e.symm ∘ C₀)) (h.map e.symm))) := by
  classical
  let : MeasurableSpace Seed := ⊤
  change (∫⁻ z : Seed, ENNReal.ofReal (((changeInitial (upperPolicy z)
      (e.symm ∘ C₀)).toOriginal e).cost h) ∂(seedPMF).toMeasure)=_
  simp_rw [TriPolicy.toOriginal_cost e he]
  rw [lintegral_fintype]
  unfold seedMean
  rw [ENNReal.ofReal_sum_of_nonneg (fun z _ =>
    mul_nonneg (seedWeight_nonneg z) (triCost_nonneg _ _))]
  apply Finset.sum_congr rfl
  intro z _
  rw [(seedPMF).toMeasure_apply_singleton z (measurableSet_singleton z),
    seedPMF_apply,ENNReal.ofReal_mul (seedWeight_nonneg z)]
  exact mul_comm _ _

theorem mixedUpper_competitive {M : Type} [MetricSpace M]
    (e : Vtx ≃ M) (he : ∀ x y, dist (e x) (e y)=triDist x y)
    (C₀ : KServer.Config 2 M) :
    (mixedUpper e C₀).IsCompetitiveFrom C₀ (ratio) := by
  constructor
  · intro z
    ext i
    simp [mixedUpper,TriPolicy.toOriginal,changeInitial]
  · refine ⟨10+ratio*10,?_⟩
    intro h
    rw [mixedUpper_expCost e he]
    apply ENNReal.ofReal_le_ofReal
    have hm := upper_mean_from (e.symm ∘ C₀) (h.map e.symm)
    have hb := bank_le_offline e he C₀ (h.map e.symm)
    simp only [List.map_map,Equiv.apply_symm_apply,Function.comp_def,List.map_id'] at hb
    have ha : 0 ≤ ratio := by norm_num [ratio]
    have hh := mul_le_mul_of_nonneg_left hb ha
    nlinarith

theorem ratio_attained_direct {M : Type} [MetricSpace M]
    (a b c : M) (hM : ∀ x : M, x=a ∨ x=b ∨ x=c)
    (hab : dist a b=3) (hac : dist a c=5) (hbc : dist b c=4) (C₀ : KServer.Config 2 M) :
    ∃ A : KServer.RandomizedAlgorithm 2 M, A.IsCompetitiveFrom C₀ (1652/1069:ℝ) := by
  let e : Vtx ≃ M := Equiv.ofBijective (val a b c)
    ⟨val_injective a b c hab hac hbc,val_surjective a b c hM⟩
  have he : ∀ x y, dist (e x) (e y)=triDist x y := val_dist a b c hab hac hbc
  exact ⟨mixedUpper e C₀,mixedUpper_competitive e he C₀⟩

end NonuniformCompetitive.Triangle345Proof

end

/- Complete checked body: TriangleRoot -/
section

namespace NonuniformCompetitive.Triangle345

/-- Karlin–Manasse–McGeoch–Owicki (Algorithmica 11, 1994), Theorem 13 (pp. 566–567): on the
triangle with edge lengths 3, 4, 5 (`d(a,b) = 3`, `d(a,c) = 5`, `d(b,c) = 4`), the optimal
randomized competitive factor of the two-server problem against an oblivious adversary is exactly
`1652/1069`: no randomized algorithm starting from `C₀` is competitive within a smaller factor,
and some randomized algorithm starting from `C₀` achieves it. Stated for every initial
configuration `C₀`. -/
theorem optimal_ratio
    {M : Type} [MetricSpace M] (a b c : M) (hM : ∀ x : M, x = a ∨ x = b ∨ x = c)
    (hab : dist a b = 3) (hac : dist a c = 5) (hbc : dist b c = 4)
    (C₀ : KServer.Config 2 M) :
    (∀ (A : KServer.RandomizedAlgorithm 2 M) (ρ : ℝ), A.IsCompetitiveFrom C₀ ρ → (1652 / 1069 : ℝ) ≤ ρ) ∧
    ∃ A : KServer.RandomizedAlgorithm 2 M, A.IsCompetitiveFrom C₀ (1652 / 1069) := by
  constructor
  · intro A ρ hA
    exact NonuniformCompetitive.Triangle345Proof.no_better_ratio_direct a b c hM hab hac hbc C₀ A ρ hA
  · exact NonuniformCompetitive.Triangle345Proof.ratio_attained_direct a b c hM hab hac hbc C₀

end NonuniformCompetitive.Triangle345

end

open NonuniformCompetitive.Triangle345


theorem solution
    {M : Type} [MetricSpace M] (a b c : M) (hM : ∀ x : M, x = a ∨ x = b ∨ x = c)
    (hab : dist a b = 3) (hac : dist a c = 5) (hbc : dist b c = 4)
    (C₀ : KServer.Config 2 M) :
    (∀ (A : KServer.RandomizedAlgorithm 2 M) (ρ : ℝ), A.IsCompetitiveFrom C₀ ρ → (1652 / 1069 : ℝ) ≤ ρ) ∧
    ∃ A : KServer.RandomizedAlgorithm 2 M, A.IsCompetitiveFrom C₀ (1652 / 1069) := by
  exact NonuniformCompetitive.Triangle345.optimal_ratio a b c hM hab hac hbc C₀

#print axioms NonuniformCompetitive.Triangle345.optimal_ratio
#print axioms solution
