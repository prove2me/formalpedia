-- Prove2me | solution 1 for MetricalTaskSystem.Randomized.uniform_minDetExpCost_ge
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T09:50:28.333826+00:00
-- url     : https://prove2.me/submissions/9896bb5e-6b32-490a-b600-1bbccdbee4fe

import Definitions.Def_MetricalTaskSystem_Randomized_Model
import Definitions.Def_MetricalTaskSystem_Randomized_TaskDistribution

open MetricalTaskSystem.Randomized
open MeasureTheory
open scoped ENNReal

private lemma integral_uniformStateSeq_fin {S : Type} [Fintype S] [Nonempty S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (j : ℕ) (g : (Fin j → S) → ℝ) :
    ∫ ω, g (fun i : Fin j => ω i) ∂(uniformStateSeq S) =
      ((Fintype.card S : ℝ)⁻¹ ^ j) * ∑ v : (Fin j → S), g v := by
  let μ₀ : Measure S := (PMF.uniformOfFintype S).toMeasure
  let I : Finset ℕ := Finset.range j
  let equivRange : (I → S) ≃ (Fin j → S) :=
    { toFun := fun y i => y ⟨i.val, Finset.mem_range.mpr i.isLt⟩
      invFun := fun v k => v ⟨k.val, Finset.mem_range.mp k.2⟩
      left_inv := fun y => by ext k; rfl
      right_inv := fun v => by ext i; rfl }
  have hcongr : (fun ω : ℕ → S => g (fun i : Fin j => ω i)) =
      (fun ω : ℕ → S => g (equivRange (I.restrict ω))) := rfl
  rw [hcongr]
  change (∫ ω : ℕ → S, (fun y : I → S => g (equivRange y)) (I.restrict ω) ∂Measure.infinitePi (fun _ : ℕ => μ₀)) = _
  have hmeas : AEStronglyMeasurable (fun y : I → S => g (equivRange y))
      (Measure.pi (fun _ : I => μ₀)) :=
    (Measurable.of_discrete (f := fun y : I → S => g (equivRange y))).aestronglyMeasurable
  rw [integral_restrict_infinitePi (fun _ : ℕ => μ₀) hmeas]
  rw [integral_fintype (Integrable.of_finite)]
  have hreal_singleton : ∀ y : I → S,
      (Measure.pi (fun _ : I => μ₀)).real {y} = ((Fintype.card S : ℝ)⁻¹) ^ j := by
    intro y
    unfold Measure.real
    have hsing : ({y} : Set (I → S)) = Set.univ.pi (fun i : I => {y i}) :=
      (Set.univ_pi_singleton y).symm
    rw [hsing, Measure.pi_pi]
    have hμ₀ : ∀ i : I, μ₀ {y i} = (Fintype.card S : ℝ≥0∞)⁻¹ := by
      intro i
      dsimp [μ₀]
      rw [PMF.toMeasure_apply_singleton _ (y i) (measurableSet_singleton (y i)),
          PMF.uniformOfFintype_apply]
    simp_rw [hμ₀]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe, Finset.card_range,
        ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  simp_rw [smul_eq_mul, hreal_singleton, ← Finset.mul_sum]
  congr 1
  exact Equiv.sum_comp equivRange g

private lemma list_ofFn_take_congr {α : Type*} {j : ℕ} (f₁ f₂ : Fin j → α) (n : ℕ)
    (h : ∀ k : Fin j, k.val < n → f₁ k = f₂ k) :
    (List.ofFn f₁).take n = (List.ofFn f₂).take n := by
  refine List.ext_getElem (by simp) fun m hm₁ hm₂ => ?_
  simp only [List.getElem_take, List.getElem_ofFn]
  have hm_lt_n : m < n := by
    simp only [List.length_take, List.length_ofFn, lt_min_iff] at hm₁
    exact hm₁.1
  have hm_lt_j : m < j := by
    simp only [List.length_take, List.length_ofFn, lt_min_iff] at hm₁
    exact hm₁.2
  exact h ⟨m, hm_lt_j⟩ hm_lt_n

theorem solution {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [MeasurableSpace S] [MeasurableSingletonClass S] (s₀ : S) (j : ℕ) :
    (j : ℝ) / Fintype.card S ≤
      minDetExpCost (uniformD (S := S)) s₀ (unitTask (S := S)) (uniformStateSeq S) j := by
  have hcard_pos : (0 : ℝ) < Fintype.card S := Nat.cast_pos.mpr Fintype.card_pos
  have hpow_pos : (0 : ℝ) < (Fintype.card S : ℝ) ^ j := pow_pos hcard_pos j
  unfold minDetExpCost
  refine le_ciInf fun A => ?_
  unfold expOnlineCost
  have hprefix : ∀ ω : ℕ → S,
      onlineCost (uniformD (S := S)) A s₀ (prefixTasks (unitTask (S := S)) ω j) =
        onlineCost (uniformD (S := S)) A s₀ (fun i : Fin j => unitTask (ω i)) :=
    fun _ => rfl
  simp_rw [hprefix]
  rw [integral_uniformStateSeq_fin j
      (fun v : Fin j → S => onlineCost (uniformD (S := S)) A s₀ (fun i => unitTask (v i)))]
  let stepCost (v : Fin j → S) (i : Fin j) : ℝ :=
    uniformD (onlineSchedule A s₀ (fun k => unitTask (v k)) i.castSucc)
      (onlineSchedule A s₀ (fun k => unitTask (v k)) i.succ) +
    unitTask (v i) (onlineSchedule A s₀ (fun k => unitTask (v k)) i.succ)
  let prevState (v : Fin j → S) (i : Fin j) : S :=
    onlineSchedule A s₀ (fun k => unitTask (v k)) i.castSucc
  have hprev_update : ∀ (v : Fin j → S) (i : Fin j) (s : S),
      prevState (Function.update v i s) i = prevState v i := by
    intro v i s
    dsimp [prevState, onlineSchedule]
    split_ifs with h0
    · rfl
    · congr 1
      refine list_ofFn_take_congr _ _ i.val fun k hk => ?_
      have hne : k ≠ i := fun h => Nat.ne_of_lt hk (congrArg Fin.val h)
      rw [Function.update_of_ne hne]
  have hstep_ge : ∀ (v : Fin j → S) (i : Fin j),
      (if v i = prevState v i then (1 : ℝ) else 0) ≤ stepCost v i := by
    intro v i
    change (if v i = prevState v i then (1 : ℝ) else 0) ≤
      uniformD (prevState v i) (onlineSchedule A s₀ (fun k => unitTask (v k)) i.succ) +
      unitTask (v i) (onlineSchedule A s₀ (fun k => unitTask (v k)) i.succ)
    set p := prevState v i
    set q := onlineSchedule A s₀ (fun k => unitTask (v k)) i.succ
    dsimp [uniformD, unitTask]
    by_cases hpq : p = q <;> by_cases hqv : q = v i <;> by_cases hvp : v i = p <;>
      simp_all
  have hsum_step : ∀ i : Fin j,
      (Fintype.card S : ℝ) ^ j ≤
        (Fintype.card S : ℝ) * ∑ v : (Fin j → S), stepCost v i := by
    intro i
    let swapAt : (Fin j → S) × S ≃ (Fin j → S) × S :=
      { toFun := fun p => (Function.update p.1 i p.2, p.1 i)
        invFun := fun p => (Function.update p.1 i p.2, p.1 i)
        left_inv := fun ⟨v, s⟩ => by simp
        right_inv := fun ⟨v, s⟩ => by simp }
    have hbij : (Fintype.card S : ℝ) * (∑ v : (Fin j → S), stepCost v i) =
        ∑ v : (Fin j → S), ∑ s : S, stepCost (Function.update v i s) i := by
      have h1 : (Fintype.card S : ℝ) * (∑ v : (Fin j → S), stepCost v i) =
          ∑ p : (Fin j → S) × S, stepCost p.1 i := by
        rw [Fintype.sum_prod_type]
        simp_rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
      rw [h1, ← Equiv.sum_comp swapAt (fun p => stepCost p.1 i), Fintype.sum_prod_type]
      rfl
    rw [hbij]
    have hcard_pow : ((Fintype.card S : ℝ) ^ j) = ∑ _v : (Fin j → S), (1 : ℝ) := by
      simp [Finset.sum_const, Finset.card_univ]
    rw [hcard_pow]
    refine Finset.sum_le_sum fun v _ => ?_
    have hinner : (1 : ℝ) = ∑ s : S, (if s = prevState v i then (1 : ℝ) else 0) := by
      simp
    rw [hinner]
    refine Finset.sum_le_sum fun s _ => ?_
    have hge := hstep_ge (Function.update v i s) i
    rwa [Function.update_self, hprev_update v i s] at hge
  have hsum_total : (j : ℝ) * (Fintype.card S : ℝ) ^ j ≤
      (Fintype.card S : ℝ) *
        ∑ v : (Fin j → S), onlineCost (uniformD (S := S)) A s₀ (fun i => unitTask (v i)) := by
    unfold onlineCost schedCost
    change (j : ℝ) * (Fintype.card S : ℝ) ^ j ≤
      (Fintype.card S : ℝ) * ∑ v : (Fin j → S), ∑ i : Fin j, stepCost v i
    rw [Finset.sum_comm, Finset.mul_sum]
    have hj_sum : (j : ℝ) * (Fintype.card S : ℝ) ^ j =
        ∑ _i : Fin j, (Fintype.card S : ℝ) ^ j := by
      simp [Finset.sum_const]
    rw [hj_sum]
    exact Finset.sum_le_sum fun i _ => hsum_step i
  rw [div_le_iff₀ hcard_pos]
  calc (j : ℝ)
      = ((Fintype.card S : ℝ)⁻¹ ^ j) * ((j : ℝ) * (Fintype.card S : ℝ) ^ j) := by
        rw [inv_pow, mul_comm (j : ℝ), ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpow_pos), one_mul]
    _ ≤ ((Fintype.card S : ℝ)⁻¹ ^ j) *
        ((Fintype.card S : ℝ) *
          ∑ v : (Fin j → S), onlineCost (uniformD (S := S)) A s₀ (fun i => unitTask (v i))) := by
        exact mul_le_mul_of_nonneg_left hsum_total (by positivity)
    _ = ((Fintype.card S : ℝ)⁻¹ ^ j *
          ∑ v : (Fin j → S), onlineCost (uniformD (S := S)) A s₀ (fun i => unitTask (v i))) *
        (Fintype.card S : ℝ) := by
        ring
