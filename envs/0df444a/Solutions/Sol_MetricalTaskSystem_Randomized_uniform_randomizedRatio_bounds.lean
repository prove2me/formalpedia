-- Prove2me | solution 1 for MetricalTaskSystem.Randomized.uniform_randomizedRatio_bounds
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T09:56:22.120623+00:00
-- url     : https://prove2.me/submissions/bb487840-18b2-46a0-aecc-c5710cffa46c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MetricalTaskSystem_Randomized_Model
import Definitions.Def_MetricalTaskSystem_Randomized_RandomizedAlgorithm
import Definitions.Def_MetricalTaskSystem_Randomized_TaskDistribution
import Theorems.Thm_MetricalTaskSystem_Randomized_uniform_expCompetitive_two_harmonic
import Theorems.Thm_MetricalTaskSystem_Randomized_randomizedRatio_ge_limsup
import Theorems.Thm_MetricalTaskSystem_Randomized_uniform_minDetExpCost_ge
import Theorems.Thm_MetricalTaskSystem_Randomized_uniform_expOfflineCost_limsup

open MetricalTaskSystem.Randomized
open MeasureTheory Filter
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
  change (∫ ω : ℕ → S, (fun y : I → S => g (equivRange y)) (I.restrict ω)
    ∂Measure.infinitePi (fun _ : ℕ => μ₀)) = _
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

private lemma const_of_step_eq {S : Type} {j : ℕ} (σ : Fin (j + 1) → S) (a k : ℕ)
    (hak : a + k ≤ j)
    (hstep : ∀ m (hm : m < k), σ ⟨a + m, by omega⟩ = σ ⟨a + m + 1, by omega⟩) :
    σ ⟨a + k, by omega⟩ = σ ⟨a, by omega⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h1 : σ ⟨a + k + 1, by omega⟩ = σ ⟨a + k, by omega⟩ :=
      (hstep k (by omega)).symm
    have h2 : σ ⟨a + k, by omega⟩ = σ ⟨a, by omega⟩ :=
      ih (by omega) (fun m hm => hstep m (by omega))
    exact h1.trans h2

private lemma idx_lt {j n : ℕ} (b : Fin (j / n)) (r : Fin n) : b.val * n + r.val < j := by
  have h1 : (b.val + 1) * n ≤ (j / n) * n := Nat.mul_le_mul_right n b.isLt
  have h2 : (j / n) * n ≤ j := Nat.div_mul_le_self j n
  have h3 : b.val * n + r.val < (b.val + 1) * n := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.add_lt_add_left r.isLt (b.val * n)
  omega

private lemma block_schedCost_ge_one {S : Type} [DecidableEq S] {j n : ℕ}
    (e : Fin n ≃ S) (σ : Fin (j + 1) → S) (v : Fin j → S) (b : Fin (j / n))
    (hve : ∀ r : Fin n, v ⟨b.val * n + r.val, idx_lt b r⟩ = e r) :
    (1 : ℝ) ≤ ∑ r : Fin n,
      (uniformD (σ (⟨b.val * n + r.val, idx_lt b r⟩ : Fin j).castSucc)
          (σ (⟨b.val * n + r.val, idx_lt b r⟩ : Fin j).succ) +
        unitTask (v ⟨b.val * n + r.val, idx_lt b r⟩)
          (σ (⟨b.val * n + r.val, idx_lt b r⟩ : Fin j).succ)) := by
  let idx (r : Fin n) : Fin j := ⟨b.val * n + r.val, idx_lt b r⟩
  let term (r : Fin n) : ℝ :=
    uniformD (σ (idx r).castSucc) (σ (idx r).succ) + unitTask (v (idx r)) (σ (idx r).succ)
  have hterm_nonneg : ∀ r : Fin n, 0 ≤ term r := by
    intro r
    dsimp [term, uniformD, unitTask]
    split_ifs <;> norm_num
  have hbn_le : b.val * n ≤ j := by
    have h1 := Nat.mul_le_mul_right n (le_of_lt b.isLt)
    have h2 := Nat.div_mul_le_self j n
    omega
  let s_start : S := σ ⟨b.val * n, by omega⟩
  by_cases hall : ∀ r : Fin n, σ (idx r).succ = s_start
  · let r₀ : Fin n := e.symm s_start
    have hr₀ : (1 : ℝ) ≤ term r₀ := by
      dsimp [term, uniformD, unitTask]
      have hsucc : σ (idx r₀).succ = s_start := hall r₀
      have hv : v (idx r₀) = s_start := by
        rw [hve r₀]
        exact e.apply_symm_apply s_start
      rw [hsucc, hv, if_pos rfl]
      split_ifs <;> norm_num
    exact le_trans hr₀ (Finset.single_le_sum (fun r _ => hterm_nonneg r) (Finset.mem_univ r₀))
  · have hex_step : ∃ r : Fin n, σ (idx r).castSucc ≠ σ (idx r).succ := by
      by_contra hno
      apply hall
      intro r
      have hstep : ∀ m (hm : m < r.val + 1),
          σ ⟨b.val * n + m, by have := idx_lt b r; omega⟩ =
            σ ⟨b.val * n + m + 1, by have := idx_lt b r; omega⟩ := by
        intro m hm
        have hlt_n : m < n := Nat.lt_of_lt_of_le hm r.isLt
        let rm : Fin n := ⟨m, hlt_n⟩
        have h_eq : σ (idx rm).castSucc = σ (idx rm).succ := by
          by_contra hne
          exact hno ⟨rm, hne⟩
        exact h_eq
      have hconst := const_of_step_eq σ (b.val * n) (r.val + 1)
        (by have := idx_lt b r; omega) hstep
      exact hconst
    obtain ⟨r₁, hr₁⟩ := hex_step
    have hr₁_ge : (1 : ℝ) ≤ term r₁ := by
      dsimp [term, uniformD, unitTask]
      rw [if_neg hr₁]
      split_ifs <;> norm_num
    exact le_trans hr₁_ge (Finset.single_le_sum (fun r _ => hterm_nonneg r) (Finset.mem_univ r₁))

private lemma expOfflineCost_tendsto_atTop {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [MeasurableSpace S] [MeasurableSingletonClass S] (s₀ : S) :
    Tendsto (fun j => expOfflineCost (uniformD (S := S)) s₀ (unitTask (S := S)) (uniformStateSeq S) j)
      atTop atTop := by
  let n : ℕ := Fintype.card S
  have hn_pos : 0 < n := Fintype.card_pos
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  have hpow_n_pos : (0 : ℝ) < (n : ℝ) ^ n := pow_pos hn_real_pos n
  let e : Fin n ≃ S := (Fintype.equivFin S).symm
  have hbound : ∀ j : ℕ,
      ((j / n : ℕ) : ℝ) / ((n : ℝ) ^ n) ≤
        expOfflineCost (uniformD (S := S)) s₀ (unitTask (S := S)) (uniformStateSeq S) j := by
    intro j
    have hpow_j_pos : (0 : ℝ) < (n : ℝ) ^ j := pow_pos hn_real_pos j
    unfold expOfflineCost
    have hprefix : ∀ ω : ℕ → S,
        offlineOpt (uniformD (S := S)) s₀ (prefixTasks (unitTask (S := S)) ω j) =
          offlineOpt (uniformD (S := S)) s₀ (fun i : Fin j => unitTask (ω i)) :=
      fun _ => rfl
    simp_rw [hprefix]
    rw [integral_uniformStateSeq_fin j
        (fun v : Fin j → S => offlineOpt (uniformD (S := S)) s₀ (fun i => unitTask (v i)))]
    let idx (b : Fin (j / n)) (r : Fin n) : Fin j := ⟨b.val * n + r.val, idx_lt b r⟩
    let indBlock (b : Fin (j / n)) (v : Fin j → S) : ℝ :=
      if ∀ r : Fin n, v (idx b r) = e r then 1 else 0
    have hoff_ge : ∀ v : Fin j → S,
        ∑ b : Fin (j / n), indBlock b v ≤
          offlineOpt (uniformD (S := S)) s₀ (fun i => unitTask (v i)) := by
      intro v
      unfold offlineOpt
      refine Finset.le_inf' _ _ fun σ _ => ?_
      unfold schedCost
      let step (i : Fin j) : ℝ :=
        uniformD (σ i.castSucc) (σ i.succ) + unitTask (v i) (σ i.succ)
      have hstep_nonneg : ∀ i : Fin j, 0 ≤ step i := by
        intro i
        dsimp [step, uniformD, unitTask]
        split_ifs <;> norm_num
      have hblock_le : ∀ b : Fin (j / n), indBlock b v ≤ ∑ r : Fin n, step (idx b r) := by
        intro b
        dsimp [indBlock]
        split_ifs with hve
        · exact block_schedCost_ge_one e σ v b hve
        · exact Finset.sum_nonneg fun r _ => hstep_nonneg (idx b r)
      have hsum_blocks : ∑ b : Fin (j / n), indBlock b v ≤
          ∑ p : Fin (j / n) × Fin n, step (idx p.1 p.2) := by
        rw [Fintype.sum_prod_type]
        exact Finset.sum_le_sum fun b _ => hblock_le b
      refine le_trans hsum_blocks ?_
      let emb : Fin (j / n) × Fin n ↪ Fin j :=
        { toFun := fun p => idx p.1 p.2
          inj' := by
            rintro ⟨b₁, r₁⟩ ⟨b₂, r₂⟩ h
            have hval : b₁.val * n + r₁.val = b₂.val * n + r₂.val := congrArg Fin.val h
            have hr1 : r₁.val < n := r₁.isLt
            have hr2 : r₂.val < n := r₂.isLt
            have hdiv1 : (b₁.val * n + r₁.val) / n = b₁.val := by
              rw [Nat.mul_comm, Nat.mul_add_div hn_pos, Nat.div_eq_of_lt hr1, Nat.add_zero]
            have hdiv2 : (b₂.val * n + r₂.val) / n = b₂.val := by
              rw [Nat.mul_comm, Nat.mul_add_div hn_pos, Nat.div_eq_of_lt hr2, Nat.add_zero]
            have hb_eq : b₁.val = b₂.val := by rw [← hdiv1, hval, hdiv2]
            have hr_eq : r₁.val = r₂.val := by
              rw [hb_eq] at hval
              exact Nat.add_left_cancel hval
            ext <;> assumption }
      have hsub := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ (Finset.univ.map emb)) (fun i _ _ => hstep_nonneg i)
      rw [Finset.sum_map] at hsub
      exact hsub
    have hsum_ind : ∀ b : Fin (j / n),
        (n : ℝ) ^ j = ((n : ℝ) ^ n) * ∑ v : (Fin j → S), indBlock b v := by
      intro b
      let updateBlock (v : Fin j → S) (π : Fin n → S) : Fin j → S :=
        fun i => if h : b.val * n ≤ i.val ∧ i.val < b.val * n + n then
          π ⟨i.val - b.val * n, by omega⟩
        else v i
      let extractBlock (v : Fin j → S) : Fin n → S := fun r => v (idx b r)
      have h_upd_ext : ∀ (v : Fin j → S) (π : Fin n → S),
          updateBlock (updateBlock v π) (extractBlock v) = v := by
        intro v π
        ext i
        dsimp [updateBlock, extractBlock, idx]
        split_ifs with h
        · congr 1
          ext
          dsimp
          omega
        · rfl
      have h_ext_upd : ∀ (v : Fin j → S) (π : Fin n → S),
          extractBlock (updateBlock v π) = π := by
        intro v π
        ext r
        dsimp [extractBlock, updateBlock, idx]
        have h : b.val * n ≤ b.val * n + r.val ∧ b.val * n + r.val < b.val * n + n := by
          exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left r.isLt _⟩
        rw [dif_pos h]
        congr 1
        ext
        dsimp
        omega
      let swapBlock : (Fin j → S) × (Fin n → S) ≃ (Fin j → S) × (Fin n → S) :=
        { toFun := fun p => (updateBlock p.1 p.2, extractBlock p.1)
          invFun := fun p => (updateBlock p.1 p.2, extractBlock p.1)
          left_inv := fun ⟨v, π⟩ => Prod.ext (h_upd_ext v π) (h_ext_upd v π)
          right_inv := fun ⟨v, π⟩ => Prod.ext (h_upd_ext v π) (h_ext_upd v π) }
      have hbij : ((n : ℝ) ^ n) * (∑ v : (Fin j → S), indBlock b v) =
          ∑ v : (Fin j → S), ∑ π : (Fin n → S), indBlock b (updateBlock v π) := by
        have hcard_pi : Fintype.card (Fin n → S) = n ^ n := by
          simp [n]
        have h1 : ((n : ℝ) ^ n) * (∑ v : (Fin j → S), indBlock b v) =
            ∑ p : (Fin j → S) × (Fin n → S), indBlock b p.1 := by
          rw [Fintype.sum_prod_type]
          simp_rw [Finset.sum_const, Finset.card_univ, hcard_pi, nsmul_eq_mul,
            Nat.cast_pow, ← Finset.mul_sum]
        rw [h1, ← Equiv.sum_comp swapBlock (fun p => indBlock b p.1), Fintype.sum_prod_type]
        rfl
      rw [hbij]
      have hcard_v : ((n : ℝ) ^ j) = ∑ _v : (Fin j → S), (1 : ℝ) := by
        simp [n, Finset.sum_const, Finset.card_univ]
      rw [hcard_v]
      refine Finset.sum_congr rfl fun v _ => ?_
      have hind_upd : ∀ π : Fin n → S,
          indBlock b (updateBlock v π) = if π = ⇑e then 1 else 0 := by
        intro π
        dsimp [indBlock]
        have hiff : (∀ r : Fin n, updateBlock v π (idx b r) = e r) ↔ π = ⇑e := by
          have hext := congrFun (h_ext_upd v π)
          dsimp [extractBlock] at hext
          simp_rw [hext]
          exact funext_iff.symm
        by_cases h : π = ⇑e
        · rw [if_pos (hiff.mpr h), if_pos h]
        · rw [if_neg (mt hiff.mp h), if_neg h]
      simp_rw [hind_upd]
      simp
    have hsum_all : ((j / n : ℕ) : ℝ) * ((n : ℝ) ^ j) ≤
        ((n : ℝ) ^ n) * ∑ v : (Fin j → S),
          offlineOpt (uniformD (S := S)) s₀ (fun i => unitTask (v i)) := by
      calc ((j / n : ℕ) : ℝ) * ((n : ℝ) ^ j)
          = ∑ b : Fin (j / n), ((n : ℝ) ^ j) := by
            simp [Finset.sum_const]
        _ = ∑ b : Fin (j / n), ((n : ℝ) ^ n) * ∑ v : (Fin j → S), indBlock b v := by
            refine Finset.sum_congr rfl fun b _ => hsum_ind b
        _ = ((n : ℝ) ^ n) * ∑ v : (Fin j → S), ∑ b : Fin (j / n), indBlock b v := by
            rw [← Finset.mul_sum, Finset.sum_comm]
        _ ≤ ((n : ℝ) ^ n) * ∑ v : (Fin j → S),
              offlineOpt (uniformD (S := S)) s₀ (fun i => unitTask (v i)) := by
            exact mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum fun v _ => hoff_ge v) (le_of_lt hpow_n_pos)
    rw [div_le_iff₀ hpow_n_pos]
    calc ((j / n : ℕ) : ℝ)
        = ((n : ℝ)⁻¹ ^ j) * (((j / n : ℕ) : ℝ) * ((n : ℝ) ^ j)) := by
          rw [inv_pow, mul_comm ((j / n : ℕ) : ℝ), ← mul_assoc,
              inv_mul_cancel₀ (ne_of_gt hpow_j_pos), one_mul]
      _ ≤ ((n : ℝ)⁻¹ ^ j) *
          (((n : ℝ) ^ n) * ∑ v : (Fin j → S),
            offlineOpt (uniformD (S := S)) s₀ (fun i => unitTask (v i))) := by
          exact mul_le_mul_of_nonneg_left hsum_all (by positivity)
      _ = (((n : ℝ)⁻¹ ^ j) * ∑ v : (Fin j → S),
            offlineOpt (uniformD (S := S)) s₀ (fun i => unitTask (v i))) *
          ((n : ℝ) ^ n) := by
          ring
  rw [tendsto_atTop_atTop]
  intro B
  obtain ⟨K, hK⟩ := exists_nat_ge (max B 0 * ((n : ℝ) ^ n) + 1)
  refine ⟨K * n, fun j hj => ?_⟩
  have hdiv : K ≤ j / n := by
    rw [Nat.le_div_iff_mul_le hn_pos]
    exact hj
  have hdiv_real : (K : ℝ) ≤ ((j / n : ℕ) : ℝ) := Nat.cast_le.mpr hdiv
  have hB_le : B ≤ ((j / n : ℕ) : ℝ) / ((n : ℝ) ^ n) := by
    rw [le_div_iff₀ hpow_n_pos]
    have hB_max : B * ((n : ℝ) ^ n) ≤ max B 0 * ((n : ℝ) ^ n) :=
      mul_le_mul_of_nonneg_right (le_max_left B 0) (le_of_lt hpow_n_pos)
    linarith
  exact le_trans hB_le (hbound j)

theorem solution {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] :
    (harmonic (Fintype.card S) : ℝ) ≤ randomizedRatio (uniformD (S := S)) ∧
      randomizedRatio (uniformD (S := S)) ≤ 2 * (harmonic (Fintype.card S) : ℝ) := by
  let H : ℝ := (harmonic (Fintype.card S) : ℝ)
  let n : ℝ := (Fintype.card S : ℝ)
  have hn_pos : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  obtain ⟨R₀, hR₀⟩ := uniform_expCompetitive_two_harmonic (S := S)
  have h2H_pos : 0 < 2 * H := hR₀.1
  have hH_pos : 0 < H := by linarith
  have hbddBelow : BddBelow {w : ℝ | ∃ R : RandomizedOnlineAlgorithm S,
      IsExpCompetitive (uniformD (S := S)) R w} := by
    refine ⟨0, ?_⟩
    rintro w ⟨_, hw, _⟩
    exact le_of_lt hw
  have hne : {w : ℝ | ∃ R : RandomizedOnlineAlgorithm S,
      IsExpCompetitive (uniformD (S := S)) R w}.Nonempty :=
    ⟨2 * H, R₀, hR₀⟩
  refine ⟨?_, csInf_le hbddBelow ⟨R₀, hR₀⟩⟩
  refine le_csInf hne ?_
  rintro w ⟨R, hR⟩
  let _ : MeasurableSpace S := ⊤
  have _ : MeasurableSingletonClass S := ⟨fun _ => trivial⟩
  obtain ⟨s₀⟩ := ‹Nonempty S›
  have hd : IsTaskSystem (uniformD (S := S)) :=
    { diag := fun i => by simp [uniformD]
      pos := fun i j hij => by simp [uniformD, hij]
      triangle := fun i j k => by
        dsimp [uniformD]
        by_cases hij : i = j <;> by_cases hjk : j = k <;> by_cases hik : i = k <;>
          simp_all }
  have hU : ∀ a s : S, 0 ≤ unitTask a s := by
    intro a s
    dsimp [unitTask]
    split_ifs <;> norm_num
  have _ : IsProbabilityMeasure (uniformStateSeq S) := by
    unfold uniformStateSeq
    infer_instance
  have hE : Tendsto
      (fun j => expOfflineCost (uniformD (S := S)) s₀ (unitTask (S := S)) (uniformStateSeq S) j)
      atTop atTop :=
    expOfflineCost_tendsto_atTop s₀
  have hlimsup := randomizedRatio_ge_limsup (uniformD (S := S)) hd (unitTask (S := S)) hU
    (uniformStateSeq S) s₀ hE R w hR
  obtain ⟨C, hC⟩ := uniform_expOfflineCost_limsup s₀
  by_contra hlt
  have hw_lt_H : w < H := not_le.mp hlt
  have hw_pos : 0 < w := hR.1
  let ε : ℝ := (H - w) / 2
  have hε_pos : 0 < ε := by dsimp [ε]; linarith
  have hHε_pos : 0 < H - ε := by dsimp [ε]; linarith
  have hnH_pos : 0 < n * H := mul_pos hn_pos hH_pos
  have hcoeff_pos : 0 < ε / (n * H) := div_pos hε_pos hnH_pos
  have hev_pos : ∀ᶠ j : ℕ in atTop,
      0 < expOfflineCost (uniformD (S := S)) s₀ (unitTask (S := S)) (uniformStateSeq S) j :=
    hE.eventually_gt_atTop 0
  rw [ eventually_atTop ] at hev_pos
  obtain ⟨J₁, hJ₁⟩ := hev_pos
  obtain ⟨J₂, hJ₂⟩ := exists_nat_ge (((H - ε) * max C 0) / (ε / (n * H)))
  have hev_le : ∀ᶠ j : ℕ in atTop,
      ((H - ε : ℝ) : EReal) ≤
        ((minDetExpCost (uniformD (S := S)) s₀ (unitTask (S := S)) (uniformStateSeq S) j /
          expOfflineCost (uniformD (S := S)) s₀ (unitTask (S := S)) (uniformStateSeq S) j : ℝ) :
          EReal) := by
    rw [eventually_atTop]
    refine ⟨max J₁ J₂, fun j hj => ?_⟩
    rw [EReal.coe_le_coe_iff]
    have hj₁ : J₁ ≤ j := le_trans (le_max_left J₁ J₂) hj
    have hj₂ : J₂ ≤ j := le_trans (le_max_right J₁ J₂) hj
    have hEj_pos := hJ₁ j hj₁
    have hEj_le := hC j
    have hmj_ge := uniform_minDetExpCost_ge s₀ j
    rw [le_div_iff₀ hEj_pos]
    have hj_real : ((H - ε) * max C 0) / (ε / (n * H)) ≤ (j : ℝ) :=
      le_trans hJ₂ (Nat.cast_le.mpr hj₂)
    have hmul_j : (H - ε) * max C 0 ≤ (j : ℝ) * (ε / (n * H)) :=
      (div_le_iff₀ hcoeff_pos).mp hj_real
    have hC_max : C ≤ max C 0 := le_max_left C 0
    have h_alg : (H - ε) * ((j : ℝ) / (n * H) + C) =
        (j : ℝ) / n - (ε / (n * H)) * (j : ℝ) + (H - ε) * C := by
      have hn_ne : n ≠ 0 := ne_of_gt hn_pos
      have hH_ne : H ≠ 0 := ne_of_gt hH_pos
      field_simp
    have hstep1 : (H - ε) *
        expOfflineCost (uniformD (S := S)) s₀ (unitTask (S := S)) (uniformStateSeq S) j ≤
        (H - ε) * ((j : ℝ) / (n * H) + C) :=
      mul_le_mul_of_nonneg_left hEj_le (le_of_lt hHε_pos)
    have hstep2 : (H - ε) * C ≤ (H - ε) * max C 0 :=
      mul_le_mul_of_nonneg_left hC_max (le_of_lt hHε_pos)
    change (H - ε) *
        expOfflineCost (uniformD (S := S)) s₀ (unitTask (S := S)) (uniformStateSeq S) j ≤
      minDetExpCost (uniformD (S := S)) s₀ (unitTask (S := S)) (uniformStateSeq S) j
    have hmj_ge' : (j : ℝ) / n ≤
        minDetExpCost (uniformD (S := S)) s₀ (unitTask (S := S)) (uniformStateSeq S) j := hmj_ge
    linarith
  have hle_limsup : ((H - ε : ℝ) : EReal) ≤
      limsup (fun j : ℕ =>
        ((minDetExpCost (uniformD (S := S)) s₀ (unitTask (S := S)) (uniformStateSeq S) j /
          expOfflineCost (uniformD (S := S)) s₀ (unitTask (S := S)) (uniformStateSeq S) j : ℝ) :
          EReal)) atTop :=
    le_limsup_of_frequently_le hev_le.frequently
  have hHε_le_w : H - ε ≤ w := EReal.coe_le_coe_iff.mp (le_trans hle_limsup hlimsup)
  dsimp [ε] at hHε_le_w
  linarith
