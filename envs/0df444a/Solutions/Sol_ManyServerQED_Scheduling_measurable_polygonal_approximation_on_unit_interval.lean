-- Prove2me | solution 1 for ManyServerQED.Scheduling.measurable_polygonal_approximation_on_unit_interval
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T03:49:15.774538+00:00
-- url     : https://prove2.me/submissions/1f0a0ab4-f46b-4430-b3fa-fdf6227e1e13

import Mathlib

open Filter Topology Set MeasureTheory Finset
open scoped NNReal ENNReal

private abbrev UnitInterval := Icc (0:ℝ) 1

private noncomputable def polygonal {k : ℕ} (m : ℕ) (x : ℝ → Fin k → ℝ) :
    C(UnitInterval,Fin k → ℝ) where
  toFun s := x 0 + ∑ j ∈ range (m+1),
    (max 0 (min 1 (((m+1:ℕ):ℝ)*(s:ℝ)-(j:ℝ)))) •
      (x (((j+1:ℕ):ℝ)/(m+1:ℕ))-x ((j:ℝ)/(m+1:ℕ)))
  continuous_toFun := by
    apply continuous_const.add
    apply continuous_finset_sum
    intro j _
    exact ((continuous_const.max (continuous_const.min
      ((continuous_subtype_val.const_mul (((m+1:ℕ):ℝ))).sub continuous_const))).smul continuous_const)

private theorem polygonal_segment {k : ℕ} (m : ℕ) (x : ℝ → Fin k → ℝ)
    (s : UnitInterval) {j : ℕ} (hj : j < m+1)
    (hs : (((m+1:ℕ):ℝ)*(s:ℝ)) ∈ Icc (j:ℝ) ((j:ℝ)+1)) :
    let θ := (((m+1:ℕ):ℝ)*(s:ℝ))-(j:ℝ)
    polygonal m x s = (1-θ) • x ((j:ℝ)/(m+1:ℕ)) +
      θ • x (((j+1:ℕ):ℝ)/(m+1:ℕ)) := by
  let u : ℝ := (((m+1:ℕ):ℝ)*(s:ℝ))
  let a (j : ℕ) := x (((j+1:ℕ):ℝ)/(m+1:ℕ))-x ((j:ℝ)/(m+1:ℕ))
  let c (j : ℕ) := max 0 (min 1 (u-(j:ℝ)))
  have hC (l : ℕ) (hl : l < j) : c l = 1 := by
    have hl' : (l:ℝ)+1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt hl
    have hh : 1 ≤ u-(l:ℝ) := by linarith [hs.1]
    simp [c,min_eq_left hh]
  have hJ : c j = u-j := by
    have h0 : 0 ≤ u-(j:ℝ) := sub_nonneg.2 hs.1
    have h1 : u-(j:ℝ) ≤ 1 := by linarith [hs.2]
    dsimp only [c]
    rw [min_eq_right h1,max_eq_right h0]
  have hZ (l : ℕ) (hl : j+1 ≤ l) : c l = 0 := by
    have hl' : (j:ℝ)+1 ≤ l := by exact_mod_cast hl
    have hh : u-(l:ℝ) ≤ 0 := by linarith [hs.2]
    simp [c,min_eq_right (by linarith : u-(l:ℝ) ≤ 1),max_eq_left hh]
  have hSum (m' : ℕ) : (∑ l ∈ range m', a l) = x ((m':ℝ)/(m+1:ℕ))-x 0 := by
    induction m' with
    | zero => simp
    | succ j ih =>
        rw [sum_range_succ,ih]
        dsimp only [a]
        rw [show (j+1:ℕ) = j.succ by rfl]
        abel
  dsimp only
  change x 0 + (∑ l ∈ range (m+1), c l • a l) =
    (1-(u-(j:ℝ))) • x ((j:ℝ)/(m+1:ℕ)) + (u-(j:ℝ)) • x (((j+1:ℕ):ℝ)/(m+1:ℕ))
  rw [← sum_range_add_sum_Ico (fun l => c l • a l) (Nat.succ_le_of_lt hj)]
  have hz : (∑ l ∈ Finset.Ico (j+1) (m+1), c l • a l) = 0 :=
    Finset.sum_eq_zero (fun l hl => by rw [hZ l (mem_Ico.1 hl).1,zero_smul])
  rw [hz,add_zero,sum_range_succ,hJ]
  have he : (∑ l ∈ range j, c l • a l) = ∑ l ∈ range j, a l :=
    Finset.sum_congr rfl (fun l hl => by rw [hC l (mem_range.1 hl),one_smul])
  rw [he,hSum]
  dsimp only [a]
  module

private theorem find_polygonal_cell (m : ℕ) (s : UnitInterval) :
    ∃ j : ℕ, j < m+1 ∧ (((m+1:ℕ):ℝ)*(s:ℝ)) ∈ Icc (j:ℝ) ((j:ℝ)+1) := by
  let N : ℝ := (m+1:ℕ)
  let u := N*(s:ℝ)
  have hN : 0 < N := by dsimp [N]; positivity
  have hu : u ≤ N := mul_le_of_le_one_right hN.le s.2.2
  have h0 : 0 ≤ u := mul_nonneg hN.le s.2.1
  rcases hu.lt_or_eq with hu | hU
  · let j := ⌊u⌋₊
    have hj : (j:ℝ) < N := (Nat.floor_le h0).trans_lt hu
    change (j:ℝ) < (((m+1:ℕ):ℝ)) at hj
    exact ⟨j,by exact_mod_cast hj, Nat.floor_le h0,(Nat.lt_floor_add_one u).le⟩
  · refine ⟨m,by omega,?_⟩
    change u ∈ Icc (m:ℝ) ((m:ℝ)+1)
    rw [hU]
    simp [N]

private theorem close_grid_endpoints {m j : ℕ} (s : UnitInterval)
    (hj : j < m+1) (hS : (((m+1:ℕ):ℝ)*(s:ℝ)) ∈ Icc (j:ℝ) ((j:ℝ)+1)) :
    let a := (j:ℝ)/(m+1:ℕ)
    let b := (((j+1:ℕ):ℝ))/(m+1:ℕ)
    a ∈ Icc (0:ℝ) 1 ∧ b ∈ Icc (0:ℝ) 1 ∧
      |(s:ℝ)-a| ≤ 1/(m+1:ℕ) ∧ |(s:ℝ)-b| ≤ 1/(m+1:ℕ) := by
  intro a b
  have hN : 0 < (((m+1:ℕ):ℝ)) := by positivity
  have h1 : (s:ℝ) ≥ a := (div_le_iff₀ hN).2 (by simpa only [mul_comm] using hS.1)
  have h2 : (s:ℝ) ≤ b := (le_div_iff₀ hN).2 (by simpa only [Nat.cast_add,Nat.cast_one,mul_comm] using hS.2)
  have hb : b ≤ 1 := (div_le_one hN).2 (by exact_mod_cast (show j+1 ≤ m+1 by omega))
  have h0 : 0 ≤ a := div_nonneg (Nat.cast_nonneg _) hN.le
  have hd : b-a = 1/(m+1:ℕ) := by dsimp [a,b]; push_cast; ring
  refine ⟨⟨h0,h1.trans s.2.2⟩,⟨s.2.1.trans h2,hb⟩,?_,?_⟩
  · rw [abs_of_nonneg (sub_nonneg.2 h1),← hd]
    linarith
  · rw [abs_of_nonpos (sub_nonpos.2 h2),← hd]
    linarith

set_option maxHeartbeats 1600000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    [MeasurableSpace C(Icc (0:ℝ) 1, Fin k → ℝ)] [BorelSpace C(Icc (0:ℝ) 1, Fin k → ℝ)]
    (m : ℕ)
    (X : Ω → ℝ → Fin k → ℝ)
    (hXm : ∀ t ∈ Icc (0:ℝ) 1, Measurable (fun ω => X ω t)) :
    ∃ Y : Ω → C(Icc (0:ℝ) 1,Fin k → ℝ), Measurable Y ∧
      (∀ ω (A : ℝ), (∀ t ∈ Icc (0:ℝ) 1, ‖X ω t‖ ≤ A) → ∀ s, ‖Y ω s‖ ≤ A) ∧
      ∀ ω (e : ℝ), (∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, |s-t| ≤ 1/(m+1:ℕ) →
        ‖X ω s-X ω t‖ ≤ e) →
        ∀ s : Icc (0:ℝ) 1, ‖Y ω s-X ω s‖ ≤ e := by
  let Y (ω : Ω) := polygonal m (X ω)
  have hN : 0 < (((m+1:ℕ):ℝ)) := by positivity
  have hm (j : ℕ) (hj : j ≤ m+1) :
      (j:ℝ)/(m+1:ℕ) ∈ Icc (0:ℝ) 1 :=
    ⟨div_nonneg (Nat.cast_nonneg _) hN.le,(div_le_one hN).2 (by exact_mod_cast hj)⟩
  have hY : Measurable Y := by
    let θ (j : ℕ) : C(UnitInterval,ℝ) :=
      ⟨fun s => max 0 (min 1 (((m+1:ℕ):ℝ)*(s:ℝ)-(j:ℝ))),
        continuous_const.max (continuous_const.min
          ((continuous_subtype_val.const_mul (((m+1:ℕ):ℝ))).sub continuous_const))⟩
    have hconst : Continuous (ContinuousMap.const UnitInterval : (Fin k → ℝ) → C(UnitInterval,Fin k → ℝ)) :=
      (show LipschitzWith 1 (ContinuousMap.const UnitInterval) from
        LipschitzWith.of_dist_le_mul fun a b => by
          rw [NNReal.coe_one,one_mul]
          exact (ContinuousMap.dist_le (dist_nonneg (x := a) (y := b))).2 (fun _ => le_rfl)).continuous
    have hc : Measurable (fun ω => ContinuousMap.const UnitInterval (X ω 0)) :=
      hconst.measurable.comp (hXm 0 (by simp))
    have hTerm (j : ℕ) (hj : j ∈ range (m+1)) :
        Measurable (fun ω => θ j • ContinuousMap.const UnitInterval
          (X ω (((j+1:ℕ):ℝ)/(m+1:ℕ))-X ω ((j:ℝ)/(m+1:ℕ)))) := by
      have hJ : j+1 ≤ m+1 := Nat.succ_le_of_lt (mem_range.1 hj)
      let F (v : Fin k → ℝ) : C(UnitInterval,Fin k → ℝ) :=
        θ j • ContinuousMap.const UnitInterval v
      have hF : Continuous F :=
        (show LipschitzWith ⟨‖θ j‖,norm_nonneg _⟩ F from
          LipschitzWith.of_dist_le_mul fun a b => by
            apply (ContinuousMap.dist_le (mul_nonneg (norm_nonneg _) dist_nonneg)).2
            intro t
            change dist ((θ j t) • a) ((θ j t) • b) ≤ ‖θ j‖ * dist a b
            rw [dist_eq_norm,dist_eq_norm,← smul_sub,norm_smul]
            exact mul_le_mul_of_nonneg_right ((θ j).norm_coe_le_norm t) (norm_nonneg _)).continuous
      exact hF.measurable.comp
        ((hXm _ (hm _ hJ)).sub (hXm _ (hm _ (Nat.le_of_succ_le hJ))))
    have hh := hc.add (Finset.measurable_sum _ hTerm)
    convert hh using 1
    funext ω
    ext s i
    simp [Y,polygonal,θ]
  refine ⟨Y,hY,?_,?_⟩
  · intro ω A hA s
    obtain ⟨j,hJ,hS⟩ := find_polygonal_cell m s
    obtain ⟨ha,hb,_,_⟩ := close_grid_endpoints s hJ hS
    have hEq := polygonal_segment m (X ω) s hJ hS
    dsimp only at hEq
    rw [show Y ω s = polygonal m (X ω) s by rfl,hEq]
    let θ := (((m+1:ℕ):ℝ)*(s:ℝ))-(j:ℝ)
    have hθ : 0 ≤ θ := sub_nonneg.2 hS.1
    have hθ' : θ ≤ 1 := by dsimp [θ]; linarith [hS.2]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul,norm_smul,Real.norm_of_nonneg (sub_nonneg.2 hθ'),Real.norm_of_nonneg hθ]
    exact (add_le_add (mul_le_mul_of_nonneg_left (hA _ ha) (sub_nonneg.2 hθ'))
      (mul_le_mul_of_nonneg_left (hA _ hb) hθ)).trans_eq (by ring)
  · intro ω e hE s
    obtain ⟨j,hJ,hS⟩ := find_polygonal_cell m s
    obtain ⟨ha,hb,hsa,hsb⟩ := close_grid_endpoints s hJ hS
    have hEq := polygonal_segment m (X ω) s hJ hS
    dsimp only at hEq
    rw [show Y ω s = polygonal m (X ω) s by rfl,hEq]
    let θ := (((m+1:ℕ):ℝ)*(s:ℝ))-(j:ℝ)
    have hθ : 0 ≤ θ := sub_nonneg.2 hS.1
    have hθ' : θ ≤ 1 := by dsimp [θ]; linarith [hS.2]
    let a := (j:ℝ)/(m+1:ℕ)
    let b := (((j+1:ℕ):ℝ))/(m+1:ℕ)
    change ‖(1-θ) • X ω a + θ • X ω b-X ω s‖ ≤ e
    rw [show (1-θ) • X ω a + θ • X ω b-X ω s =
      (1-θ) • (X ω a-X ω s)+θ • (X ω b-X ω s) by module]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul,norm_smul,Real.norm_of_nonneg (sub_nonneg.2 hθ'),Real.norm_of_nonneg hθ]
    have hsa' : |a-(s:ℝ)| ≤ 1/(m+1:ℕ) := by rwa [abs_sub_comm]
    have hsb' : |b-(s:ℝ)| ≤ 1/(m+1:ℕ) := by rwa [abs_sub_comm]
    exact (add_le_add (mul_le_mul_of_nonneg_left (hE _ ha _ s.2 hsa') (sub_nonneg.2 hθ'))
      (mul_le_mul_of_nonneg_left (hE _ hb _ s.2 hsb') hθ)).trans_eq (by ring)
