-- Prove2me | solution 1 for MinimaxSLP.RhsExtremal.disutility_Qval_eq_max_pairs
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T21:47:20.092079+00:00
-- url     : https://prove2.me/submissions/d4e240c1-b37b-4aa6-8126-86a69a1e823b

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_RhsExtremal_Model

open Matrix

namespace RhsExtLP

variable {m r : ℕ}

lemma mulVec_add_smul (A : Matrix (Fin m) (Fin r) ℝ) (π d : Fin r → ℝ) (t : ℝ) (j : Fin m) :
    (A *ᵥ (π + t • d)) j = (A *ᵥ π) j + t * (A *ᵥ d) j := by
  simp [Matrix.mulVec_add, Matrix.mulVec_smul]

/-- Moving along a direction with a positive component. -/
lemma step (A : Matrix (Fin m) (Fin r) ℝ) (q : Fin m → ℝ) (c : Fin r → ℝ)
    (π d : Fin r → ℝ) (hπ : A *ᵥ π ≤ q)
    (htight : ∀ j, (A *ᵥ π) j = q j → (A *ᵥ d) j = 0)
    (hcd : 0 ≤ c ⬝ᵥ d) (hpos : ∃ j, 0 < (A *ᵥ d) j) :
    ∃ π', A *ᵥ π' ≤ q ∧ c ⬝ᵥ π ≤ c ⬝ᵥ π' ∧
      (Finset.univ.filter fun j => (A *ᵥ π') j < q j) ⊂
        (Finset.univ.filter fun j => (A *ᵥ π) j < q j) := by
  classical
  set S := Finset.univ.filter fun j => 0 < (A *ᵥ d) j
  have hS : S.Nonempty := by
    obtain ⟨j, hj⟩ := hpos; exact ⟨j, by simp [S, hj]⟩
  set f : Fin m → ℝ := fun j => (q j - (A *ᵥ π) j) / (A *ᵥ d) j
  obtain ⟨j0, hj0S, hj0⟩ := S.exists_min_image f hS
  have hj0pos : 0 < (A *ᵥ d) j0 := by simpa [S] using hj0S
  have ht : 0 ≤ f j0 := div_nonneg (by linarith [hπ j0]) hj0pos.le
  refine ⟨π + f j0 • d, ?_, ?_, ?_⟩
  · intro j
    rw [mulVec_add_smul]
    by_cases hj : 0 < (A *ᵥ d) j
    · have h1 : f j0 ≤ f j := hj0 j (by simp [S, hj])
      have : f j * (A *ᵥ d) j = q j - (A *ᵥ π) j := by
        simp only [f]; field_simp
      nlinarith
    · nlinarith [hπ j]
  · rw [dotProduct_add, dotProduct_smul, smul_eq_mul]; nlinarith
  · rw [Finset.ssubset_iff_of_subset]
    · refine ⟨j0, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases lt_or_eq_of_le (hπ j0) with h | h
        · exact h
        · exact absurd (htight j0 h) hj0pos.ne'
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
        rw [mulVec_add_smul]
        have : f j0 * (A *ᵥ d) j0 = q j0 - (A *ᵥ π) j0 := by
          simp only [f]; field_simp
        linarith
    · intro j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro hj
      by_contra hns
      have heq : (A *ᵥ π) j = q j := le_antisymm (hπ j) (not_lt.mp hns)
      rw [mulVec_add_smul, htight j heq, mul_zero, add_zero] at hj
      linarith

lemma exists_extreme (A : Matrix (Fin m) (Fin r) ℝ) (q : Fin m → ℝ)
    (hinj : ∀ d, A *ᵥ d = 0 → d = 0) (c : Fin r → ℝ) (B : ℝ)
    (hB : ∀ π, A *ᵥ π ≤ q → c ⬝ᵥ π ≤ B) :
    ∀ π, A *ᵥ π ≤ q → ∃ e ∈ Set.extremePoints ℝ {π | A *ᵥ π ≤ q}, c ⬝ᵥ π ≤ c ⬝ᵥ e := by
  classical
  -- unboundedness contradiction
  have hunb : ∀ π d, A *ᵥ π ≤ q → A *ᵥ d ≤ 0 → 0 < c ⬝ᵥ d → False := by
    intro π d hπ hd hcd
    set t := (B - c ⬝ᵥ π) / (c ⬝ᵥ d) + 1
    have hπ' : A *ᵥ (π + t • d) ≤ q := by
      intro j
      have h0 : 0 ≤ t := by
        have := hB π hπ
        have : 0 ≤ (B - c ⬝ᵥ π) / (c ⬝ᵥ d) := div_nonneg (by linarith) hcd.le
        simp only [t]; linarith
      rw [mulVec_add_smul]; nlinarith [hπ j, mul_nonpos_of_nonneg_of_nonpos h0 (hd j)]
    have := hB _ hπ'
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at this
    have : t * (c ⬝ᵥ d) = B - c ⬝ᵥ π + c ⬝ᵥ d := by
      simp only [t]; field_simp
    linarith
  have key : ∀ π, A *ᵥ π ≤ q →
      (∀ π', A *ᵥ π' ≤ q →
        (Finset.univ.filter fun j => (A *ᵥ π') j < q j).card <
          (Finset.univ.filter fun j => (A *ᵥ π) j < q j).card →
        ∃ e ∈ Set.extremePoints ℝ {π | A *ᵥ π ≤ q}, c ⬝ᵥ π' ≤ c ⬝ᵥ e) →
      ∃ e ∈ Set.extremePoints ℝ {π | A *ᵥ π ≤ q}, c ⬝ᵥ π ≤ c ⬝ᵥ e := by
    intro π hπ IH
    by_cases hext : π ∈ Set.extremePoints ℝ {π | A *ᵥ π ≤ q}
    · exact ⟨π, hext, le_rfl⟩
    rw [mem_extremePoints] at hext
    push_neg at hext
    obtain ⟨x1, hx1, x2, hx2, hseg, hne⟩ := hext hπ
    obtain ⟨a, b, ha, hb, hab, hcomb⟩ := hseg
    set d := x1 - π
    have htight : ∀ j, (A *ᵥ π) j = q j → (A *ᵥ d) j = 0 := by
      intro j hj
      have e1 : (A *ᵥ π) j = a * (A *ᵥ x1) j + b * (A *ᵥ x2) j := by
        rw [← hcomb]; simp [Matrix.mulVec_add, Matrix.mulVec_smul]
      have h1 : (A *ᵥ x1) j ≤ q j := hx1 j
      have h2 : (A *ᵥ x2) j ≤ q j := hx2 j
      have hsum : a * (q j - (A *ᵥ x1) j) + b * (q j - (A *ᵥ x2) j) = 0 := by
        linear_combination (q j) * hab + e1 - hj
      have h3 : a * (q j - (A *ᵥ x1) j) = 0 := by
        linarith [mul_nonneg ha.le (sub_nonneg.mpr h1), mul_nonneg hb.le (sub_nonneg.mpr h2)]
      have : (A *ᵥ x1) j = q j := by
        rcases mul_eq_zero.mp h3 with h | h
        · exact absurd h ha.ne'
        · linarith
      simp [d, Matrix.mulVec_sub, this, hj]
    have hd0 : A *ᵥ d ≠ 0 := by
      intro h
      have hd : d = 0 := hinj d h
      have e1 : x1 = π := sub_eq_zero.mp hd
      apply hne e1
      have : b • x2 = b • π := by
        have : a • π + b • x2 = π := by rw [e1] at hcomb; exact hcomb
        calc b • x2 = π - a • π := eq_sub_of_add_eq' this
          _ = b • π := by rw [show b = 1 - a by linarith, sub_smul, one_smul]
      exact smul_right_injective _ hb.ne' this
    -- choose a good direction
    have hgood : ∃ d', (∀ j, (A *ᵥ π) j = q j → (A *ᵥ d') j = 0) ∧ 0 ≤ c ⬝ᵥ d' ∧
        ∃ j, 0 < (A *ᵥ d') j := by
      by_cases h1 : (∃ j, 0 < (A *ᵥ d) j) ∧ 0 ≤ c ⬝ᵥ d
      · exact ⟨d, htight, h1.2, h1.1⟩
      by_cases h2 : (∃ j, (A *ᵥ d) j < 0) ∧ c ⬝ᵥ d ≤ 0
      · refine ⟨-d, fun j hj => by simp [Matrix.mulVec_neg, htight j hj], by simp [h2.2], ?_⟩
        obtain ⟨j, hj⟩ := h2.1; exact ⟨j, by simp [Matrix.mulVec_neg]; linarith⟩
      exfalso
      rw [not_and_or] at h1 h2
      push_neg at h1 h2
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact hd0 (funext fun j => le_antisymm (h1 j) (h2 j))
      · exact hunb π d hπ h1 h2
      · exact hunb π (-d) hπ (fun j => by simp [Matrix.mulVec_neg, h2 j])
          (by simp; linarith)
      · linarith
    obtain ⟨d', ht', hc', hp'⟩ := hgood
    obtain ⟨π', hπ', hcπ, hss⟩ := step A q c π d' hπ ht' hc' hp'
    have hlt := Finset.card_lt_card hss
    obtain ⟨e, he, hce⟩ := IH π' hπ' hlt
    exact ⟨e, he, le_trans hcπ hce⟩
  suffices H : ∀ n, ∀ π, A *ᵥ π ≤ q →
      (Finset.univ.filter fun j => (A *ᵥ π) j < q j).card ≤ n →
      ∃ e ∈ Set.extremePoints ℝ {π | A *ᵥ π ≤ q}, c ⬝ᵥ π ≤ c ⬝ᵥ e from
    fun π hπ => H _ π hπ le_rfl
  intro n
  induction n with
  | zero => intro π hπ hcard; exact key π hπ (fun π' hπ' hlt => by omega)
  | succ n ih => intro π hπ hcard; exact key π hπ (fun π' hπ' hlt => ih π' hπ' (by omega))


lemma mulVec_dot_eq (W : Matrix (Fin m) (Fin r) ℝ) (w : Fin r → ℝ) (π : Fin m → ℝ) :
    (W *ᵥ w) ⬝ᵥ π = w ⬝ᵥ (Wᵀ *ᵥ π) := by
  rw [Matrix.mulVec_transpose, dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm]

end RhsExtLP

open MeasureTheory Matrix MinimaxSLP.RhsExtremal

theorem solution {r d n K N : ℕ} [NeZero K]
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (q : Fin d → ℝ)
    (α β : Fin K → ℝ) (ps : Fin N → Fin r → ℝ)
    (hα : ∀ k, 0 ≤ α k)
    (hA2 : ∀ z : Fin r → ℝ, ∃ w : Fin d → ℝ, 0 ≤ w ∧ W *ᵥ w = z)
    (hA3 : ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (hA5 : Set.range ps = Set.extremePoints ℝ {π : Fin r → ℝ | Wᵀ *ᵥ π ≤ q})
    (x : Fin n → ℝ) (h : Fin r → ℝ) :
    IsGreatest (Set.range fun i : Fin N => (h - T *ᵥ x) ⬝ᵥ ps i) (MinimaxSLP.RhsSDP.Qval W T q h x) ∧
    IsGreatest (Set.range fun ki : Fin K × Fin N => α ki.1 * ((h - T *ᵥ x) ⬝ᵥ ps ki.2) + β ki.1)
      (MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.RhsSDP.Qval W T q h x)) := by
  classical
  set c := h - T *ᵥ x with hc
  have hinj : ∀ v, Wᵀ *ᵥ v = 0 → v = 0 := by
    intro v hv
    obtain ⟨w, -, hw⟩ := hA2 v
    have : v ⬝ᵥ v = 0 := by
      have e : v ⬝ᵥ v = w ⬝ᵥ (Wᵀ *ᵥ v) := by
        rw [← RhsExtLP.mulVec_dot_eq, hw]
      rw [e, hv, dotProduct_zero]
    exact dotProduct_self_eq_zero.mp this
  obtain ⟨wc, hwc0, hwc⟩ := hA2 c
  have hB : ∀ π, Wᵀ *ᵥ π ≤ q → c ⬝ᵥ π ≤ wc ⬝ᵥ q := by
    intro π hπ
    rw [← hwc, RhsExtLP.mulVec_dot_eq]
    exact dotProduct_le_dotProduct_of_nonneg_left hπ hwc0
  have hext := RhsExtLP.exists_extreme Wᵀ q hinj c _ hB
  obtain ⟨π0, hπ0⟩ := hA3
  obtain ⟨e0, he0, -⟩ := hext π0 hπ0
  rw [← hA5] at he0
  obtain ⟨j0, -⟩ := he0
  haveI : Nonempty (Fin N) := ⟨j0⟩
  obtain ⟨i0, -, hi0⟩ := Finset.univ.exists_max_image (fun i => c ⬝ᵥ ps i) Finset.univ_nonempty
  have hps : ∀ i, Wᵀ *ᵥ ps i ≤ q := by
    intro i
    have : ps i ∈ Set.extremePoints ℝ {π : Fin r → ℝ | Wᵀ *ᵥ π ≤ q} := hA5 ▸ ⟨i, rfl⟩
    exact this.1
  have hG : IsGreatest ((fun π => c ⬝ᵥ π) '' {π : Fin r → ℝ | Wᵀ *ᵥ π ≤ q}) (c ⬝ᵥ ps i0) := by
    refine ⟨⟨ps i0, hps i0, rfl⟩, ?_⟩
    rintro _ ⟨π, hπ, rfl⟩
    obtain ⟨e, he, hce⟩ := hext π hπ
    rw [← hA5] at he
    obtain ⟨j, rfl⟩ := he
    exact le_trans hce (hi0 j (Finset.mem_univ _))
  have hQ : MinimaxSLP.RhsSDP.Qval W T q h x = c ⬝ᵥ ps i0 := hG.csSup_eq
  rw [hQ]
  refine ⟨⟨⟨i0, rfl⟩, ?_⟩, ?_⟩
  · rintro _ ⟨i, rfl⟩; exact hi0 i (Finset.mem_univ _)
  · unfold MinimaxSLP.ObjSDP.disutility
    obtain ⟨k0, -, hk0⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin K))
      (fun k => α k * (c ⬝ᵥ ps i0) + β k)
    refine ⟨⟨(k0, i0), ?_⟩, ?_⟩
    · simp only; rw [hk0]
    · rintro _ ⟨⟨k, i⟩, rfl⟩
      simp only
      calc α k * (c ⬝ᵥ ps i) + β k ≤ α k * (c ⬝ᵥ ps i0) + β k := by
            nlinarith [hi0 i (Finset.mem_univ _), hα k]
        _ ≤ _ := Finset.le_sup' (fun k => α k * (c ⬝ᵥ ps i0) + β k) (Finset.mem_univ k)
