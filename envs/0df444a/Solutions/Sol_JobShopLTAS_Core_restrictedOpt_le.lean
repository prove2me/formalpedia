-- Prove2me | solution 1 for JobShopLTAS.Core.restrictedOpt_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T12:44:24.430002+00:00
-- url     : https://prove2.me/submissions/c6f9533a-ebaa-42ee-9396-575bdbe273ed

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_JobShopLTAS_Core_RestrictedProblem
import Theorems.Thm_JobShopLTAS_Core_card_bigJobs_le
import Theorems.Thm_JobShopLTAS_Core_Pmax_le_optMakespan

open JobShopLTAS.Core

private def beforeOp {m n : ℕ} {inst : Instance m n} (o₁ o₂ : inst.Op) : Prop :=
  o₁.1.val < o₂.1.val ∨ (o₁.1.val = o₂.1.val ∧ o₁.2.val < o₂.2.val)

private instance {m n : ℕ} {inst : Instance m n} : DecidableRel (beforeOp (inst := inst)) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

private noncomputable def sSer {m n : ℕ} (inst : Instance m n) (o : inst.Op) : ℝ :=
  ∑ o' ∈ Finset.univ.filter (fun o' : inst.Op => beforeOp o' o), inst.proc o'

private lemma sSer_step {m n : ℕ} (inst : Instance m n) {o₁ o₂ : inst.Op}
    (h : beforeOp o₁ o₂) :
    sSer inst o₁ + inst.proc o₁ ≤ sSer inst o₂ := by
  have hnot : o₁ ∉ Finset.univ.filter (fun o' : inst.Op => beforeOp o' o₁) := by
    simp [beforeOp]
  unfold sSer
  rw [add_comm, ← Finset.sum_insert hnot]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro o' ho'
    rw [Finset.mem_insert, Finset.mem_filter] at ho'
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases ho' with rfl | ⟨_, h'⟩
    · exact h
    · unfold beforeOp at h h' ⊢
      omega
  · intro o' _ _
    exact inst.p_nonneg o'.1 o'.2

private lemma sSer_feasible {m n : ℕ} (inst : Instance m n) :
    inst.IsFeasibleSchedule Finset.univ (sSer inst) where
  start_nonneg o _ := Finset.sum_nonneg (fun o' _ => inst.p_nonneg o'.1 o'.2)
  precedence j _ i i' hii' := by
    apply sSer_step inst (o₁ := ⟨j, i⟩) (o₂ := ⟨j, i'⟩)
    exact Or.inr ⟨rfl, by dsimp; omega⟩
  machine_disjoint o o' _ _ hne _ := by
    have htrich : beforeOp o o' ∨ beforeOp o' o := by
      unfold beforeOp
      by_cases h1 : o.1.val = o'.1.val
      · have h2 : o.2.val ≠ o'.2.val := by
          intro h2
          apply hne
          rcases o with ⟨j₁, i₁⟩
          rcases o' with ⟨j₂, i₂⟩
          have hj : j₁ = j₂ := Fin.ext h1
          subst hj
          congr
          exact Fin.ext h2
        omega
      · omega
    rcases htrich with h | h
    · exact Or.inl (sSer_step inst h)
    · exact Or.inr (sSer_step inst h)

private lemma sum_proc_le_m_mul_Pmax {m n : ℕ} (inst : Instance m n) :
    (∑ o : inst.Op, inst.proc o) ≤ (m : ℝ) * inst.Pmax := by
  have hfib : (∑ o : inst.Op, inst.proc o) = ∑ t : Fin m, inst.load t := by
    unfold Instance.load
    exact (Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) inst.proc).symm
  rw [hfib]
  have hle : ∑ t : Fin m, inst.load t ≤ ∑ _t : Fin m, inst.Pmax := by
    apply Finset.sum_le_sum
    intro t _
    exact le_ciSup (Set.finite_range _).bddAbove t
  simpa using hle

private lemma makespan_nonneg {m n : ℕ} (inst : Instance m n) (s : inst.Op → ℝ)
    (hs : inst.IsFeasibleSchedule Finset.univ s) :
    0 ≤ inst.makespan Finset.univ s := by
  unfold Instance.makespan
  by_cases h : Nonempty {o : inst.Op // o.1 ∈ (Finset.univ : Finset (Fin n))}
  · rcases h with ⟨⟨o₀, ho₀⟩⟩
    have h0 : 0 ≤ s o₀ + inst.proc o₀ :=
      add_nonneg (hs.start_nonneg o₀ ho₀) (inst.p_nonneg o₀.1 o₀.2)
    exact le_trans h0 (le_ciSup (f := fun o : {o : inst.Op // o.1 ∈ (Finset.univ : Finset (Fin n))} => s o.1 + inst.proc o.1) (Set.finite_range _).bddAbove ⟨o₀, ho₀⟩)
  · rw [not_nonempty_iff] at h
    simp

private lemma makespan_BT_nonneg {m n : ℕ} (inst : Instance m n) (J : Finset (Fin n)) (s : inst.Op → ℝ)
    (hs : inst.IsFeasibleSchedule J s) :
    0 ≤ inst.makespan J s := by
  unfold Instance.makespan
  by_cases h : Nonempty {o : inst.Op // o.1 ∈ J}
  · rcases h with ⟨⟨o₀, ho₀⟩⟩
    have h0 : 0 ≤ s o₀ + inst.proc o₀ :=
      add_nonneg (hs.start_nonneg o₀ ho₀) (inst.p_nonneg o₀.1 o₀.2)
    exact le_trans h0 (le_ciSup (f := fun o : {o : inst.Op // o.1 ∈ J} => s o.1 + inst.proc o.1)
      (Set.finite_range _).bddAbove ⟨o₀, ho₀⟩)
  · rw [not_nonempty_iff] at h
    simp

private lemma makespan_sSer_le {m n : ℕ} (inst : Instance m n) :
    inst.makespan Finset.univ (sSer inst) ≤ (m : ℝ) * inst.Pmax := by
  refine le_trans ?_ (sum_proc_le_m_mul_Pmax inst)
  unfold Instance.makespan
  by_cases h : Nonempty {o : inst.Op // o.1 ∈ (Finset.univ : Finset (Fin n))}
  · apply ciSup_le
    rintro ⟨o, _⟩
    dsimp
    unfold sSer
    have hnot : o ∉ Finset.univ.filter (fun o' : inst.Op => beforeOp o' o) := by
      simp [beforeOp]
    rw [add_comm, ← Finset.sum_insert hnot]
    exact Finset.sum_le_univ_sum_of_nonneg (fun o' => inst.p_nonneg o'.1 o'.2)
  · rw [not_nonempty_iff] at h
    simp
    exact Finset.sum_nonneg (fun o' _ => inst.p_nonneg o'.1 o'.2)

private lemma card_bigOps_le {m n : ℕ} (inst : Instance m n) (α : ℝ) :
    (Finset.univ.filter (fun o : inst.Op => o.1 ∈ inst.bigJobs α)).card ≤
      inst.maxOps * (inst.bigJobs α).card := by
  rw [Finset.card_filter]
  rw [Fintype.sum_sigma]
  have h1 : (∑ j : Fin n, ∑ _i : Fin (inst.μ j), (if j ∈ inst.bigJobs α then 1 else 0)) =
      ∑ j ∈ inst.bigJobs α, inst.μ j := by
    simp [Finset.sum_ite_mem]
  rw [h1]
  have h2 : ∑ j ∈ inst.bigJobs α, inst.μ j ≤ ∑ _j ∈ inst.bigJobs α, inst.maxOps := by
    apply Finset.sum_le_sum
    intro j _
    exact Finset.le_sup (f := inst.μ) (Finset.mem_univ j)
  simpa [Nat.mul_comm] using h2

private noncomputable def shiftFrom {m n : ℕ} {inst : Instance m n}
    (s : inst.Op → ℝ) (u₀ : inst.Op) (δ : ℝ) (o : inst.Op) : ℝ :=
  if s u₀ ≤ s o then s o + δ else s o

private lemma shiftFrom_feasible {m n : ℕ} (inst : Instance m n)
    (s : inst.Op → ℝ) (hs : inst.IsFeasibleSchedule Finset.univ s)
    (u₀ : inst.Op) (δ : ℝ) (hδ : 0 ≤ δ) :
    inst.IsFeasibleSchedule Finset.univ (shiftFrom s u₀ δ) where
  start_nonneg o ho := by
    unfold shiftFrom
    split_ifs <;> linarith [hs.start_nonneg o ho]
  precedence j hj i i' hii' := by
    have hprec := hs.precedence j hj i i' hii'
    have hp := inst.p_nonneg j i
    unfold shiftFrom
    split_ifs <;> linarith
  machine_disjoint o o' ho ho' hne hmach := by
    rcases hs.machine_disjoint o o' ho ho' hne hmach with h1 | h2
    · left
      have hp : 0 ≤ inst.proc o := inst.p_nonneg o.1 o.2
      unfold shiftFrom
      split_ifs <;> linarith
    · right
      have hp : 0 ≤ inst.proc o' := inst.p_nonneg o'.1 o'.2
      unfold shiftFrom
      split_ifs <;> linarith

private lemma round_bigOps {m n : ℕ} (inst : Instance m n) (B_ops : Finset inst.Op) (L : ℝ) (hL : 0 < L) :
    ∀ k : ℕ, ∀ U : Finset inst.Op, U ⊆ B_ops → U.card = k →
      ∀ s : inst.Op → ℝ, inst.IsFeasibleSchedule Finset.univ s →
      (∀ o ∈ B_ops \ U, ∃ r : ℕ, s o = r * L) →
      (∀ o ∈ B_ops \ U, ∀ u ∈ U, s o ≤ s u) →
      ∃ s' : inst.Op → ℝ, ∃ D : ℝ,
        inst.IsFeasibleSchedule Finset.univ s' ∧
        (∀ o ∈ B_ops, ∃ r : ℕ, s' o = r * L) ∧
        0 ≤ D ∧ D ≤ k * L ∧ (0 < k → D < k * L) ∧
        (∀ o : inst.Op, s o ≤ s' o ∧ s' o ≤ s o + D)
  | 0, U, _, hcard, s, hs, hmult, _ => by
    have hU : U = ∅ := Finset.card_eq_zero.mp hcard
    subst hU
    refine ⟨s, 0, hs, ?_, le_rfl, by positivity, by intro h; omega, fun o => ⟨le_rfl, by linarith⟩⟩
    intro o ho
    exact hmult o (by simp [ho])
  | k + 1, U, hU_sub, hcard, s, hs, hmult, hord => by
    have hne : U.Nonempty := Finset.card_pos.mp (by omega)
    rcases Finset.exists_min_image U s hne with ⟨u₀, hu₀, hmin⟩
    have hcard' : (U.erase u₀).card = k := by
      rw [Finset.card_erase_of_mem hu₀, hcard]
      rfl
    have hU'_sub : U.erase u₀ ⊆ B_ops :=
      Finset.Subset.trans (Finset.erase_subset u₀ U) hU_sub
    by_cases h_already : ∃ r : ℕ, s u₀ = r * L
    · have hmult' : ∀ o ∈ B_ops \ U.erase u₀, ∃ r : ℕ, s o = r * L := by
        intro o ho
        by_cases hou : o = u₀
        · subst hou; exact h_already
        · apply hmult o
          rw [Finset.mem_sdiff, Finset.mem_erase] at ho
          rw [Finset.mem_sdiff]
          exact ⟨ho.1, fun h => ho.2 ⟨hou, h⟩⟩
      have hord' : ∀ o ∈ B_ops \ U.erase u₀, ∀ u ∈ U.erase u₀, s o ≤ s u := by
        intro o ho u hu
        have hu_in : u ∈ U := Finset.mem_of_mem_erase hu
        by_cases hou : o = u₀
        · subst hou; exact hmin u hu_in
        · apply hord o _ u hu_in
          rw [Finset.mem_sdiff, Finset.mem_erase] at ho
          rw [Finset.mem_sdiff]
          exact ⟨ho.1, fun h => ho.2 ⟨hou, h⟩⟩
      rcases round_bigOps inst B_ops L hL k (U.erase u₀) hU'_sub hcard' s hs hmult' hord' with
        ⟨s', D', hs', hmult_s', hD'_nonneg, hD'_le, _, hbounds⟩
      refine ⟨s', D', hs', hmult_s', hD'_nonneg, ?_, ?_, hbounds⟩
      · push_cast; linarith
      · intro _; push_cast; linarith
    · set r₀ := ⌈s u₀ / L⌉₊
      set δ := (r₀ : ℝ) * L - s u₀
      have hs_u₀ : 0 ≤ s u₀ := hs.start_nonneg u₀ (Finset.mem_univ _)
      have hδ_nonneg : 0 ≤ δ := by
        have h1 : s u₀ / L ≤ r₀ := Nat.le_ceil _
        have h2 : s u₀ ≤ (r₀ : ℝ) * L := (div_le_iff₀ hL).mp h1
        linarith
      have hδ_lt : δ < L := by
        have h1 : (r₀ : ℝ) < s u₀ / L + 1 := Nat.ceil_lt_add_one (div_nonneg hs_u₀ hL.le)
        have h2 : (r₀ : ℝ) * L < (s u₀ / L + 1) * L := mul_lt_mul_of_pos_right h1 hL
        have h3 : (s u₀ / L + 1) * L = s u₀ + L := by
          rw [add_mul, div_mul_cancel₀ _ hL.ne', one_mul]
        linarith
      set s₁ := shiftFrom s u₀ δ
      have hs₁ : inst.IsFeasibleSchedule Finset.univ s₁ :=
        shiftFrom_feasible inst s hs u₀ δ hδ_nonneg
      have hmult' : ∀ o ∈ B_ops \ U.erase u₀, ∃ r : ℕ, s₁ o = r * L := by
        intro o ho
        by_cases hou : o = u₀
        · subst hou
          refine ⟨r₀, ?_⟩
          unfold s₁ shiftFrom
          simp [δ]
        · have ho_in : o ∈ B_ops \ U := by
            rw [Finset.mem_sdiff, Finset.mem_erase] at ho
            rw [Finset.mem_sdiff]
            exact ⟨ho.1, fun h => ho.2 ⟨hou, h⟩⟩
          have hle : s o ≤ s u₀ := hord o ho_in u₀ hu₀
          have hne_s : s o ≠ s u₀ := by
            intro heq
            apply h_already
            rcases hmult o ho_in with ⟨r, hr⟩
            exact ⟨r, by linarith⟩
          have hlt : s o < s u₀ := lt_of_le_of_ne hle hne_s
          have hs₁_eq : s₁ o = s o := by
            unfold s₁ shiftFrom
            rw [if_neg (not_le.mpr hlt)]
          rw [hs₁_eq]
          exact hmult o ho_in
      have hord' : ∀ o ∈ B_ops \ U.erase u₀, ∀ u ∈ U.erase u₀, s₁ o ≤ s₁ u := by
        intro o ho u hu
        have hu_in : u ∈ U := Finset.mem_of_mem_erase hu
        have h_u₀_le_u : s u₀ ≤ s u := hmin u hu_in
        have hs₁_u : s₁ u = s u + δ := by
          unfold s₁ shiftFrom
          rw [if_pos h_u₀_le_u]
        by_cases hou : o = u₀
        · subst hou
          have hs₁_u₀ : s₁ o = s o + δ := by
            unfold s₁ shiftFrom
            simp
          linarith
        · have ho_in : o ∈ B_ops \ U := by
            rw [Finset.mem_sdiff, Finset.mem_erase] at ho
            rw [Finset.mem_sdiff]
            exact ⟨ho.1, fun h => ho.2 ⟨hou, h⟩⟩
          have hle : s o ≤ s u := hord o ho_in u hu_in
          have hs₁_o : s₁ o ≤ s o + δ := by
            unfold s₁ shiftFrom
            split_ifs <;> linarith
          linarith
      rcases round_bigOps inst B_ops L hL k (U.erase u₀) hU'_sub hcard' s₁ hs₁ hmult' hord' with
        ⟨s', D', hs', hmult_s', hD'_nonneg, hD'_le, _, hbounds⟩
      refine ⟨s', δ + D', hs', hmult_s', add_nonneg hδ_nonneg hD'_nonneg, ?_, ?_, ?_⟩
      · push_cast; linarith
      · intro _; push_cast; linarith
      · intro o
        have hb := hbounds o
        have hs₁_lo : s o ≤ s₁ o := by
          unfold s₁ shiftFrom; split_ifs <;> linarith
        have hs₁_hi : s₁ o ≤ s o + δ := by
          unfold s₁ shiftFrom; split_ifs <;> linarith
        exact ⟨le_trans hs₁_lo hb.1, by linarith [hb.2]⟩

private lemma gridLength_pos {m n : ℕ} (inst : Instance m n) (ε α : ℝ)
    (hm : 2 ≤ m) (hε : 0 < ε) (hα : 0 < α) (hP : 0 < inst.Pmax) :
    0 < inst.gridLength ε α ∧ 0 < inst.numIntervals ε α := by
  have hm_pos : (0 : ℝ) < m := by positivity
  have hnum : 0 < inst.numIntervals ε α := by
    unfold Instance.numIntervals
    exact Nat.ceil_pos.mpr (by positivity)
  have hnum_r : (0 : ℝ) < inst.numIntervals ε α := Nat.cast_pos.mpr hnum
  have hhor : 0 < inst.horizon ε := by
    unfold Instance.horizon; positivity
  exact ⟨div_pos hhor hnum_r, hnum⟩

private lemma gridLength_le {m n : ℕ} (inst : Instance m n) (ε α : ℝ)
    (hm : 2 ≤ m) (hε : 0 < ε) (hα : 0 < α) (hP : 0 < inst.Pmax) :
    inst.gridLength ε α ≤ α * ε * inst.Pmax := by
  have ⟨_, hnum⟩ := gridLength_pos inst ε α hm hε hα hP
  have hnum_r : (0 : ℝ) < inst.numIntervals ε α := Nat.cast_pos.mpr hnum
  unfold Instance.gridLength
  rw [div_le_iff₀ hnum_r]
  have hceil : (m : ℝ) * (1 + (inst.maxOps : ℝ) * m * ε) / (α * ε) ≤ inst.numIntervals ε α :=
    Nat.le_ceil _
  have hαε : 0 < α * ε := mul_pos hα hε
  have hmul : (m : ℝ) * (1 + (inst.maxOps : ℝ) * m * ε) ≤ (inst.numIntervals ε α : ℝ) * (α * ε) :=
    (div_le_iff₀ hαε).mp hceil
  have hmul2 := mul_le_mul_of_nonneg_right hmul hP.le
  unfold Instance.horizon
  linarith

private lemma round_schedule_exists {m n : ℕ} (inst : Instance m n) (ε α : ℝ)
    (hm : 2 ≤ m) (hε : 0 < ε) (hα : 0 < α) (hP : 0 < inst.Pmax)
    (hcardB : ((inst.bigJobs α).card : ℝ) ≤ (m : ℝ) / α)
    (s : inst.Op → ℝ) (hs : inst.IsFeasibleSchedule Finset.univ s)
    (hM : inst.makespan Finset.univ s ≤ (m : ℝ) * inst.Pmax) :
    ∃ s' : inst.Op → ℝ,
      inst.IsFeasibleSchedule (inst.bigJobs α ∪ inst.tinyJobs ε α) s' ∧
      inst.IsRestricted ε α s' ∧
      inst.makespan (inst.bigJobs α ∪ inst.tinyJobs ε α) s' ≤
        inst.makespan Finset.univ s + (inst.maxOps : ℝ) * m * ε * inst.Pmax := by
  set B_ops := Finset.univ.filter (fun o : inst.Op => o.1 ∈ inst.bigJobs α)
  set L := inst.gridLength ε α
  have ⟨hL_pos, hnum_pos⟩ := gridLength_pos inst ε α hm hε hα hP
  have hBL_le : (B_ops.card : ℝ) * L ≤ (inst.maxOps : ℝ) * m * ε * inst.Pmax := by
    have h1 : (B_ops.card : ℝ) ≤ (inst.maxOps : ℝ) * (inst.bigJobs α).card := by
      exact_mod_cast card_bigOps_le inst α
    have h2 : (B_ops.card : ℝ) ≤ (inst.maxOps : ℝ) * ((m : ℝ) / α) :=
      le_trans h1 (mul_le_mul_of_nonneg_left hcardB (by positivity))
    have h3 : L ≤ α * ε * inst.Pmax := gridLength_le inst ε α hm hε hα hP
    have h4 : (B_ops.card : ℝ) * L ≤ ((inst.maxOps : ℝ) * ((m : ℝ) / α)) * (α * ε * inst.Pmax) :=
      mul_le_mul h2 h3 hL_pos.le (by positivity)
    have h5 : ((inst.maxOps : ℝ) * ((m : ℝ) / α)) * (α * ε * inst.Pmax) =
        (inst.maxOps : ℝ) * m * ε * inst.Pmax := by
      have hα_ne : α ≠ 0 := hα.ne'
      calc ((inst.maxOps : ℝ) * ((m : ℝ) / α)) * (α * ε * inst.Pmax)
          = (inst.maxOps : ℝ) * m * (α⁻¹ * α) * ε * inst.Pmax := by ring
        _ = (inst.maxOps : ℝ) * m * 1 * ε * inst.Pmax := by rw [inv_mul_cancel₀ hα_ne]
        _ = (inst.maxOps : ℝ) * m * ε * inst.Pmax := by ring
    linarith
  rcases round_bigOps inst B_ops L hL_pos B_ops.card B_ops Finset.Subset.rfl rfl s hs
    (by simp) (by simp) with ⟨s', D, hs', hmult, hD_nonneg, hD_le, hD_lt, hbounds⟩
  have hs'_BT : inst.IsFeasibleSchedule (inst.bigJobs α ∪ inst.tinyJobs ε α) s' :=
    { start_nonneg := fun o _ => hs'.start_nonneg o (Finset.mem_univ _)
      precedence := fun j _ i i' hii' => hs'.precedence j (Finset.mem_univ _) i i' hii'
      machine_disjoint := fun o o' _ _ hne hmach =>
        hs'.machine_disjoint o o' (Finset.mem_univ _) (Finset.mem_univ _) hne hmach }
  refine ⟨s', hs'_BT, ?_, ?_⟩
  · intro o ho
    have hoB : o ∈ B_ops := Finset.mem_filter.mpr ⟨Finset.mem_univ o, ho⟩
    have hcard_pos : 0 < B_ops.card := Finset.card_pos.mpr ⟨o, hoB⟩
    have hD_strict : D < (inst.maxOps : ℝ) * m * ε * inst.Pmax :=
      lt_of_lt_of_le (hD_lt hcard_pos) hBL_le
    rcases hmult o hoB with ⟨r, hr⟩
    refine ⟨r, ?_, hr⟩
    have hso_le : s o ≤ (m : ℝ) * inst.Pmax := by
      have hproc_nn : 0 ≤ inst.proc o := inst.p_nonneg o.1 o.2
      have hso_mk : s o + inst.proc o ≤ inst.makespan Finset.univ s :=
        le_ciSup (f := fun o' : {o' : inst.Op // o'.1 ∈ (Finset.univ : Finset (Fin n))} => s o'.1 + inst.proc o'.1)
          (Set.finite_range _).bddAbove ⟨o, Finset.mem_univ _⟩
      linarith
    have hs'o_lt : s' o < (m : ℝ) * inst.Pmax + (inst.maxOps : ℝ) * m * ε * inst.Pmax := by
      have hb := (hbounds o).2
      linarith
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
    have hterm_nn : 0 ≤ (inst.maxOps : ℝ) * m * ε * inst.Pmax := by positivity
    have hhor_ge : (m : ℝ) * inst.Pmax + (inst.maxOps : ℝ) * m * ε * inst.Pmax ≤ inst.horizon ε := by
      have hmul_m : (inst.maxOps : ℝ) * m * ε * inst.Pmax * 1 ≤
          (inst.maxOps : ℝ) * m * ε * inst.Pmax * (m : ℝ) :=
        mul_le_mul_of_nonneg_left hm1 hterm_nn
      unfold Instance.horizon
      linarith
    have hhor_eq : inst.horizon ε = (inst.numIntervals ε α : ℝ) * L := by
      have hnum_ne : (inst.numIntervals ε α : ℝ) ≠ 0 := (Nat.cast_pos.mpr hnum_pos).ne'
      unfold L Instance.gridLength
      exact (mul_div_cancel₀ _ hnum_ne).symm
    have hrL_lt : (r : ℝ) * L < (inst.numIntervals ε α : ℝ) * L := by
      linarith
    have hr_lt : (r : ℝ) < (inst.numIntervals ε α : ℝ) :=
      lt_of_mul_lt_mul_right hrL_lt hL_pos.le
    exact Nat.cast_lt.mp hr_lt
  · unfold Instance.makespan
    have hD_bound : D ≤ (inst.maxOps : ℝ) * m * ε * inst.Pmax := le_trans hD_le hBL_le
    by_cases hne : Nonempty {o : inst.Op // o.1 ∈ inst.bigJobs α ∪ inst.tinyJobs ε α}
    · apply ciSup_le
      rintro ⟨o, _⟩
      dsimp
      have hso_mk : s o + inst.proc o ≤ inst.makespan Finset.univ s :=
        le_ciSup (f := fun o' : {o' : inst.Op // o'.1 ∈ (Finset.univ : Finset (Fin n))} => s o'.1 + inst.proc o'.1)
          (Set.finite_range _).bddAbove ⟨o, Finset.mem_univ _⟩
      have hb := (hbounds o).2
      unfold Instance.makespan at hso_mk
      linarith
    · rw [not_nonempty_iff] at hne
      simp
      have hmk_nn : 0 ≤ inst.makespan Finset.univ s := makespan_nonneg inst s hs
      have hterm_nn : 0 ≤ (inst.maxOps : ℝ) * m * ε * inst.Pmax := by positivity
      unfold Instance.makespan at hmk_nn
      linarith

theorem solution {m n : ℕ} (inst : Instance m n) (ε α : ℝ)
    (hm : 2 ≤ m) (hμ : 1 ≤ inst.maxOps) (hε : 0 < ε) (hε1 : ε < 1)
    (hα_lo : ε ^ ⌈(m : ℝ) / ε⌉₊ ≤ α) (hα_hi : α ≤ ε) (hP : 0 < inst.Pmax) :
    (∃ s : inst.Op → ℝ,
        inst.IsFeasibleSchedule (inst.bigJobs α ∪ inst.tinyJobs ε α) s ∧
        inst.IsRestricted ε α s) ∧
      inst.restrictedOpt ε α ≤
        inst.optMakespan Finset.univ + (inst.maxOps : ℝ) * m * ε * inst.Pmax ∧
      inst.optMakespan Finset.univ + (inst.maxOps : ℝ) * m * ε * inst.Pmax ≤
        (1 + (inst.maxOps : ℝ) * m * ε) * inst.optMakespan Finset.univ := by
  have hα_pos : 0 < α := lt_of_lt_of_le (pow_pos hε _) hα_lo
  have hcardB : ((inst.bigJobs α).card : ℝ) ≤ (m : ℝ) / α :=
    (card_bigJobs_le inst ε α hm hμ hε hε1 hα_lo hα_hi hP).1
  rcases round_schedule_exists inst ε α hm hε hα_pos hP hcardB (sSer inst)
    (sSer_feasible inst) (makespan_sSer_le inst) with ⟨s'_ser, hs'_ser_feas, hs'_ser_rest, hs'_ser_mk⟩
  refine ⟨⟨s'_ser, hs'_ser_feas, hs'_ser_rest⟩, ?_, ?_⟩
  · set E := (inst.maxOps : ℝ) * m * ε * inst.Pmax
    set J_BT := inst.bigJobs α ∪ inst.tinyJobs ε α
    have hbdd_rest : BddBelow (inst.makespan J_BT '' {s | inst.IsFeasibleSchedule J_BT s ∧ inst.IsRestricted ε α s}) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨s, ⟨hs, _⟩, rfl⟩
      exact makespan_BT_nonneg inst J_BT s hs
    have hrest_le_ser : inst.restrictedOpt ε α ≤ inst.makespan Finset.univ (sSer inst) + E := by
      have h1 : inst.restrictedOpt ε α ≤ inst.makespan J_BT s'_ser :=
        csInf_le hbdd_rest ⟨s'_ser, ⟨hs'_ser_feas, hs'_ser_rest⟩, rfl⟩
      linarith
    have hser_le_mP : inst.makespan Finset.univ (sSer inst) ≤ (m : ℝ) * inst.Pmax :=
      makespan_sSer_le inst
    by_contra! hlt
    have hopt_lt : inst.optMakespan Finset.univ < inst.restrictedOpt ε α - E := by linarith
    have hne_univ : (inst.makespan Finset.univ '' {s | inst.IsFeasibleSchedule Finset.univ s}).Nonempty :=
      ⟨inst.makespan Finset.univ (sSer inst), sSer inst, sSer_feasible inst, rfl⟩
    rcases (csInf_lt_iff (by
      refine ⟨0, ?_⟩
      rintro _ ⟨s, hs, rfl⟩
      exact makespan_nonneg inst s hs) hne_univ).mp hopt_lt with ⟨_, ⟨s, hs, rfl⟩, hs_lt⟩
    have hs_le_mP : inst.makespan Finset.univ s ≤ (m : ℝ) * inst.Pmax := by linarith
    rcases round_schedule_exists inst ε α hm hε hα_pos hP hcardB s hs hs_le_mP with
      ⟨s', hs'_feas, hs'_rest, hs'_mk⟩
    have hrest_le_s' : inst.restrictedOpt ε α ≤ inst.makespan J_BT s' :=
      csInf_le hbdd_rest ⟨s', ⟨hs'_feas, hs'_rest⟩, rfl⟩
    linarith
  · have hP_le : inst.Pmax ≤ inst.optMakespan Finset.univ := Pmax_le_optMakespan inst
    have hcoeff_nn : 0 ≤ (inst.maxOps : ℝ) * m * ε := by positivity
    have hmul := mul_le_mul_of_nonneg_left hP_le hcoeff_nn
    linarith
