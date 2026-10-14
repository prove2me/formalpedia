-- Prove2me | solution 1 for KangKurtz.Combine.lemma_3_8
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T12:33:42.778506+00:00
-- url     : https://prove2.me/submissions/31d8da2d-656a-4a59-9da3-09b58e8bac79

import Mathlib
import Definitions.Def_KangKurtz_Combine_Setting

namespace RRAux_KangKurtz_Combine_lemma_3_8

open KangKurtz.SCC

section
variable {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ) (α : Fin s → ℝ) (β : Fin r → ℝ)

theorem dot_sum {m : ℕ} (θs : Fin m → Fin s → ℝ) (k : Fin r) :
    dot ν ν' (∑ j, θs j) k = ∑ j, dot ν ν' (θs j) k := by
  unfold dot
  simp only [Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem exists_consume {φ : Fin s → ℝ} (hφ : ∀ i, 0 ≤ φ i) {k : Fin r}
    (h : dot ν ν' φ k < 0) : ∃ i, φ i ≠ 0 ∧ 0 < ν k i := by
  by_contra hc
  push Not at hc
  have : 0 ≤ dot ν ν' φ k := by
    unfold dot
    apply Finset.sum_nonneg
    intro i _
    by_cases h0 : φ i = 0
    · simp [h0]
    · have h1 := hc i h0
      have hz : 0 ≤ zeta ν ν' k i := by
        unfold zeta
        have : ν k i = 0 := by omega
        simp [this]
      exact mul_nonneg (hφ i) hz
  linarith

theorem exists_produce {φ : Fin s → ℝ} (hφ : ∀ i, 0 ≤ φ i) {k : Fin r}
    (h : 0 < dot ν ν' φ k) : ∃ i, φ i ≠ 0 ∧ 0 < ν' k i := by
  by_contra hc
  push Not at hc
  have : dot ν ν' φ k ≤ 0 := by
    unfold dot
    apply Finset.sum_nonpos
    intro i _
    by_cases h0 : φ i = 0
    · simp [h0]
    · have h1 := hc i h0
      have hz : zeta ν ν' k i ≤ 0 := by
        unfold zeta
        have : ν' k i = 0 := by omega
        simp [this]
      exact mul_nonpos_iff.mpr (Or.inl ⟨hφ i, hz⟩)
  linarith

theorem memG {φ : Fin s → ℝ} {k : Fin r} :
    k ∈ GammaPlus ν ν' φ ∪ GammaMinus ν ν' φ ↔ dot ν ν' φ k ≠ 0 := by
  simp only [GammaPlus, GammaMinus, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro (h | h)
    · exact ne_of_gt h
    · exact ne_of_lt h
  · intro h
    rcases lt_or_gt_of_ne h with h | h
    · exact Or.inr h
    · exact Or.inl h

theorem supp_nonempty {φ : Fin s → ℝ} (hφ : ∀ i, 0 ≤ φ i) {k : Fin r}
    (hk : k ∈ GammaPlus ν ν' φ ∪ GammaMinus ν ν' φ) :
    (Finset.univ.filter (fun i => 0 < φ i)).Nonempty := by
  rw [memG] at hk
  by_contra hc
  rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hc
  apply hk
  unfold dot
  apply Finset.sum_eq_zero
  intro i _
  have : φ i = 0 := le_antisymm (not_lt.mp (hc (Finset.mem_univ i))) (hφ i)
  simp [this]

theorem alpha_mono {φ ψ : Fin s → ℝ} (hle : ∀ i, 0 < φ i → 0 < ψ i)
    (h : (Finset.univ.filter (fun i => 0 < φ i)).Nonempty) :
    alphaTheta α φ ≤ alphaTheta α ψ := by
  have hsub : Finset.univ.filter (fun i => 0 < φ i) ⊆ Finset.univ.filter (fun i => 0 < ψ i) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hle i hi
  have h2 := h.mono hsub
  unfold alphaTheta
  simp only []
  rw [dif_pos h, dif_pos h2]
  exact Finset.sup'_mono α hsub h

theorem ts_bound {γ : ℝ} {φ : Fin s → ℝ} (h : TimeScale ν ν' α β γ φ) {k : Fin r}
    (hk : k ∈ GammaPlus ν ν' φ ∪ GammaMinus ν ν' φ) :
    γ ≤ alphaTheta α φ - rho ν α β k := by
  have hne : (GammaPlus ν ν' φ ∪ GammaMinus ν ν' φ).Nonempty := ⟨k, hk⟩
  unfold TimeScale gammaTheta at h
  simp only [] at h
  rw [dif_pos hne] at h
  have h1 := EReal.coe_le_coe_iff.mp h
  have h2 := Finset.le_sup' (rho ν α β) hk
  linarith

theorem ts_of_bound {γ : ℝ} {φ : Fin s → ℝ}
    (hb : ∀ k ∈ GammaPlus ν ν' φ ∪ GammaMinus ν ν' φ, γ ≤ alphaTheta α φ - rho ν α β k) :
    TimeScale ν ν' α β γ φ := by
  unfold TimeScale gammaTheta
  simp only []
  by_cases hne : (GammaPlus ν ν' φ ∪ GammaMinus ν ν' φ).Nonempty
  · rw [dif_pos hne]
    obtain ⟨k, hk, heq⟩ := Finset.exists_mem_eq_sup' hne (rho ν α β)
    apply EReal.coe_le_coe_iff.mpr
    rw [heq]
    exact hb k hk
  · rw [dif_neg hne]
    exact le_top

theorem le_maxRho {S : Finset (Fin r)} {k : Fin r} (hk : k ∈ S) :
    ((rho ν α β k : ℝ) : WithBot ℝ) ≤ maxRho ν α β S :=
  Finset.le_sup (f := fun k => ((rho ν α β k : ℝ) : WithBot ℝ)) hk

theorem maxRho_attain {S : Finset (Fin r)} (h : maxRho ν α β S ≠ ⊥) :
    ∃ k ∈ S, maxRho ν α β S = ((rho ν α β k : ℝ) : WithBot ℝ) := by
  have hne : S.Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty] at hc
    apply h
    rw [hc]
    rfl
  exact Finset.exists_mem_eq_sup S hne _


theorem core {m : ℕ} (θ : Fin s → ℝ) (θs : Fin m → Fin s → ℝ)
    (hsum : θ = ∑ j, θs j) (R : Fin m → Fin m → Prop)
    (wf1 : WellFounded R) (wf2 : WellFounded (flip R))
    (hR : ∀ a b k, a ≠ b → dot ν ν' (θs a) k < 0 → 0 < dot ν ν' (θs b) k → R a b)
    (H : ∀ j, maxRho ν α β (GammaPlus ν ν' (θs j) ∪ GammaMinus ν ν' (θs j)) =
      Finset.univ.sup (fun j' => maxRho ν α β (GammaPlus ν ν' (θs j') ∪ GammaMinus ν ν' (θs j')))
      → Balance ν ν' α β (θs j)) :
    Balance ν ν' α β θ := by
  classical
  set Mf : Fin m → WithBot ℝ :=
    fun j => maxRho ν α β (GammaPlus ν ν' (θs j) ∪ GammaMinus ν ν' (θs j)) with hMf
  set M := Finset.univ.sup Mf with hM
  have hdot : ∀ k, dot ν ν' θ k = ∑ j, dot ν ν' (θs j) k := by
    intro k; rw [hsum, dot_sum]
  have hpiece : ∀ k, k ∈ GammaPlus ν ν' θ ∪ GammaMinus ν ν' θ →
      ∃ j, k ∈ GammaPlus ν ν' (θs j) ∪ GammaMinus ν ν' (θs j) := by
    intro k hk
    rw [memG, hdot] at hk
    obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk
    exact ⟨j, (memG ν ν').mpr hj⟩
  have hupper : ∀ S ⊆ GammaPlus ν ν' θ ∪ GammaMinus ν ν' θ, maxRho ν α β S ≤ M := by
    intro S hS
    apply Finset.sup_le
    intro k hk
    obtain ⟨j, hj⟩ := hpiece k (hS hk)
    exact le_trans (le_maxRho ν α β hj) (Finset.le_sup (f := Mf) (Finset.mem_univ j))
  have hMfle : ∀ j, Mf j ≤ M := fun j => Finset.le_sup (f := Mf) (Finset.mem_univ j)
  have hlow : M ≤ maxRho ν α β (GammaPlus ν ν' θ) ∧ M ≤ maxRho ν α β (GammaMinus ν ν' θ) := by
    by_cases hMb : M = ⊥
    · rw [hMb]; exact ⟨bot_le, bot_le⟩
    have huniv : (Finset.univ : Finset (Fin m)).Nonempty := by
      by_contra hc
      rw [Finset.not_nonempty_iff_eq_empty] at hc
      apply hMb
      rw [hM, hc]
      rfl
    obtain ⟨j0, _, hj0⟩ := Finset.exists_mem_eq_sup _ huniv Mf
    have hJ : ({j | Mf j = M} : Set (Fin m)).Nonempty := ⟨j0, hj0.symm⟩
    have hsplit : ∀ j, Balance ν ν' α β (θs j) →
        Mf j = maxRho ν α β (GammaPlus ν ν' (θs j)) ∧
        Mf j = maxRho ν α β (GammaMinus ν ν' (θs j)) := by
      intro j hb
      unfold Balance at hb
      have : Mf j = maxRho ν α β (GammaPlus ν ν' (θs j)) ⊔ maxRho ν α β (GammaMinus ν ν' (θs j)) := by
        simp only [hMf, maxRho]
        exact Finset.sup_union
      rw [hb, sup_idem] at this
      exact ⟨this, this.trans hb.symm⟩
    constructor
    · obtain ⟨j, hjJ, hjmin⟩ := wf1.has_min _ hJ
      have hjM : Mf j = M := hjJ
      have hb := H j hjM
      have hj1 := (hsplit j hb).1
      rw [hjM] at hj1
      obtain ⟨k, hk, hkeq⟩ := maxRho_attain ν α β (fun h => hMb (hj1.trans h))
      have hkpos : 0 < dot ν ν' (θs j) k := by
        simpa [GammaPlus] using hk
      have hθk : 0 < dot ν ν' θ k := by
        rw [hdot]
        apply Finset.sum_pos'
        · intro j' _
          by_contra hneg
          push Not at hneg
          have hjj : j' ≠ j := by
            intro h; subst h; linarith
          have hRr := hR j' j k hjj hneg hkpos
          have hkG : k ∈ GammaPlus ν ν' (θs j') ∪ GammaMinus ν ν' (θs j') :=
            (memG ν ν').mpr (ne_of_lt hneg)
          have hge : M ≤ Mf j' := by
            rw [hj1, hkeq]; exact le_maxRho ν α β hkG
          exact hjmin j' (le_antisymm (hMfle j') hge) hRr
        · exact ⟨j, Finset.mem_univ _, hkpos⟩
      have hkθ : k ∈ GammaPlus ν ν' θ := by simpa [GammaPlus] using hθk
      rw [hj1, hkeq]
      exact le_maxRho ν α β hkθ
    · obtain ⟨j, hjJ, hjmax⟩ := wf2.has_min _ hJ
      have hjM : Mf j = M := hjJ
      have hb := H j hjM
      have hj1 := (hsplit j hb).2
      rw [hjM] at hj1
      obtain ⟨k, hk, hkeq⟩ := maxRho_attain ν α β (fun h => hMb (hj1.trans h))
      have hkneg : dot ν ν' (θs j) k < 0 := by
        simpa [GammaMinus] using hk
      have hθk : dot ν ν' θ k < 0 := by
        rw [hdot]
        apply Finset.sum_neg'
        · intro j' _
          by_contra hpos
          push Not at hpos
          have hjj : j ≠ j' := by
            intro h; subst h; linarith
          have hRr := hR j j' k hjj hkneg hpos
          have hkG : k ∈ GammaPlus ν ν' (θs j') ∪ GammaMinus ν ν' (θs j') :=
            (memG ν ν').mpr (ne_of_gt hpos)
          have hge : M ≤ Mf j' := by
            rw [hj1, hkeq]; exact le_maxRho ν α β hkG
          exact hjmax j' (le_antisymm (hMfle j') hge) hRr
        · exact ⟨j, Finset.mem_univ _, hkneg⟩
      have hkθ : k ∈ GammaMinus ν ν' θ := by simpa [GammaMinus] using hθk
      rw [hj1, hkeq]
      exact le_maxRho ν α β hkθ
  unfold Balance
  apply le_antisymm
  · exact le_trans (hupper _ Finset.subset_union_right) hlow.1
  · exact le_trans (hupper _ Finset.subset_union_left) hlow.2

theorem dot_smul (c : ℝ) (θ : Fin s → ℝ) (k : Fin r) :
    dot ν ν' (c • θ) k = c * dot ν ν' θ k := by
  unfold dot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem pos_iff_aux {c x : ℝ} (hc : 0 < c) : 0 < c * x ↔ 0 < x :=
  mul_pos_iff_of_pos_left hc

theorem neg_iff_aux {c x : ℝ} (hc : 0 < c) : c * x < 0 ↔ x < 0 := by
  constructor
  · intro h; by_contra h'; push Not at h'; nlinarith
  · intro h; nlinarith

theorem gp_smul {c : ℝ} (hc : 0 < c) (θ : Fin s → ℝ) :
    GammaPlus ν ν' (c • θ) = GammaPlus ν ν' θ := by
  ext k
  simp only [GammaPlus, Finset.mem_filter, Finset.mem_univ, true_and, dot_smul]
  exact pos_iff_aux hc

theorem gm_smul {c : ℝ} (hc : 0 < c) (θ : Fin s → ℝ) :
    GammaMinus ν ν' (c • θ) = GammaMinus ν ν' θ := by
  ext k
  simp only [GammaMinus, Finset.mem_filter, Finset.mem_univ, true_and, dot_smul]
  exact neg_iff_aux hc

theorem ts_iff {γ : ℝ} {φ : Fin s → ℝ} (hφ : ∀ i, 0 ≤ φ i) :
    KangKurtz.Combine.TimeScale ν ν' α β γ φ ↔ TimeScale ν ν' α β γ φ := by
  unfold KangKurtz.Combine.TimeScale TimeScale KangKurtz.Combine.gammaTheta gammaTheta
  simp only []
  by_cases hne : (GammaPlus ν ν' φ ∪ GammaMinus ν ν' φ).Nonempty
  · obtain ⟨k, hk⟩ := id hne
    have hs : (KangKurtz.Combine.supp φ).Nonempty := supp_nonempty ν ν' hφ hk
    have halpha : alphaTheta α φ = (KangKurtz.Combine.supp φ).sup' hs α := by
      unfold alphaTheta; exact dif_pos hs
    rw [dif_pos hne, dif_pos hne]
    try rw [dif_pos hs]
    rw [halpha]
  · rw [dif_neg hne, dif_neg hne]

end

end RRAux_KangKurtz_Combine_lemma_3_8

open KangKurtz.Combine in
theorem solution {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ) (α : Fin s → ℝ) (hα : ∀ i, 0 ≤ α i)
    (β : Fin r → ℝ)
    (γ : ℝ) (θ₁ θ₂ : Fin s → ℝ) (hθ₁ : ∀ i, 0 ≤ θ₁ i) (hθ₂ : ∀ i, 0 ≤ θ₂ i)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    (Cond32 ν ν' α β γ θ₁ → Cond32 ν ν' α β γ θ₂ →
      (Disjoint (KangKurtz.SCC.GammaPlus ν ν' θ₁) (KangKurtz.SCC.GammaMinus ν ν' θ₂) ∨
        Disjoint (KangKurtz.SCC.GammaMinus ν ν' θ₁) (KangKurtz.SCC.GammaPlus ν ν' θ₂)) →
      Cond32 ν ν' α β γ (c₁ • θ₁ + c₂ • θ₂)) ∧
    (KangKurtz.SCC.Balance ν ν' α β θ₁ → KangKurtz.SCC.Balance ν ν' α β θ₂ →
      (Disjoint (KangKurtz.SCC.GammaPlus ν ν' θ₁) (KangKurtz.SCC.GammaMinus ν ν' θ₂) ∨
        Disjoint (KangKurtz.SCC.GammaMinus ν ν' θ₁) (KangKurtz.SCC.GammaPlus ν ν' θ₂)) →
      KangKurtz.SCC.Balance ν ν' α β (c₁ • θ₁ + c₂ • θ₂)) := by
  classical
  set th : Fin 2 → Fin s → ℝ := ![θ₁, θ₂] with hthdef
  set cc : Fin 2 → ℝ := ![c₁, c₂] with hccdef
  set φ : Fin 2 → Fin s → ℝ := fun j => cc j • th j with hφdef
  set θ := c₁ • θ₁ + c₂ • θ₂ with hθdef
  have hcc : ∀ j, 0 < cc j := by
    intro j; fin_cases j
    · simpa [cc] using hc₁
    · simpa [cc] using hc₂
  have hth : ∀ j i, 0 ≤ th j i := by
    intro j i; fin_cases j
    · simpa [th] using hθ₁ i
    · simpa [th] using hθ₂ i
  have hsum : θ = ∑ j, φ j := by
    simp [θ, φ, Fin.sum_univ_two, cc, th]
  have hθnn : ∀ i, 0 ≤ θ i := by
    intro i
    simp only [θ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg hc₁.le (hθ₁ i)) (mul_nonneg hc₂.le (hθ₂ i))
  have hsupp : ∀ j i, 0 < th j i → 0 < θ i := by
    intro j i h
    fin_cases j
    · have h' : 0 < θ₁ i := by simpa [th] using h
      simp only [θ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_pos_of_pos_of_nonneg (mul_pos hc₁ h') (mul_nonneg hc₂.le (hθ₂ i))
    · have h' : 0 < θ₂ i := by simpa [th] using h
      simp only [θ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_pos_of_nonneg_of_pos (mul_nonneg hc₁.le (hθ₁ i)) (mul_pos hc₂ h')
  have hGP : ∀ j, KangKurtz.SCC.GammaPlus ν ν' (φ j) = KangKurtz.SCC.GammaPlus ν ν' (th j) :=
    fun j => RRAux_KangKurtz_Combine_lemma_3_8.gp_smul ν ν' (hcc j) (th j)
  have hGM : ∀ j, KangKurtz.SCC.GammaMinus ν ν' (φ j) = KangKurtz.SCC.GammaMinus ν ν' (th j) :=
    fun j => RRAux_KangKurtz_Combine_lemma_3_8.gm_smul ν ν' (hcc j) (th j)
  have hBal : ∀ j, KangKurtz.SCC.Balance ν ν' α β (th j) → KangKurtz.SCC.Balance ν ν' α β (φ j) := by
    intro j h
    unfold KangKurtz.SCC.Balance at h ⊢
    rw [hGP j, hGM j]
    exact h
  have hP1 : KangKurtz.SCC.GammaPlus ν ν' (th 0) = KangKurtz.SCC.GammaPlus ν ν' θ₁ := by simp [th]
  have hP2 : KangKurtz.SCC.GammaPlus ν ν' (th 1) = KangKurtz.SCC.GammaPlus ν ν' θ₂ := by simp [th]
  have hM1 : KangKurtz.SCC.GammaMinus ν ν' (th 0) = KangKurtz.SCC.GammaMinus ν ν' θ₁ := by simp [th]
  have hM2 : KangKurtz.SCC.GammaMinus ν ν' (th 1) = KangKurtz.SCC.GammaMinus ν ν' θ₂ := by simp [th]
  have hmemP : ∀ j k, 0 < KangKurtz.SCC.dot ν ν' (φ j) k → k ∈ KangKurtz.SCC.GammaPlus ν ν' (th j) := by
    intro j k h
    rw [← hGP j]
    simpa [KangKurtz.SCC.GammaPlus] using h
  have hmemM : ∀ j k, KangKurtz.SCC.dot ν ν' (φ j) k < 0 → k ∈ KangKurtz.SCC.GammaMinus ν ν' (th j) := by
    intro j k h
    rw [← hGM j]
    simpa [KangKurtz.SCC.GammaMinus] using h
  have hRex : (Disjoint (KangKurtz.SCC.GammaPlus ν ν' θ₁) (KangKurtz.SCC.GammaMinus ν ν' θ₂) ∨
        Disjoint (KangKurtz.SCC.GammaMinus ν ν' θ₁) (KangKurtz.SCC.GammaPlus ν ν' θ₂)) →
      ∃ R : Fin 2 → Fin 2 → Prop, WellFounded R ∧ WellFounded (flip R) ∧
        ∀ a b k, a ≠ b → KangKurtz.SCC.dot ν ν' (φ a) k < 0 →
          0 < KangKurtz.SCC.dot ν ν' (φ b) k → R a b := by
    rintro (hd | hd)
    · refine ⟨fun a b => a < b, wellFounded_lt, wellFounded_gt, ?_⟩
      intro a b k hab ha hb
      fin_cases a <;> fin_cases b
      · exact absurd rfl hab
      · decide
      · exfalso
        have h1 := hmemM 1 k ha
        have h2 := hmemP 0 k hb
        rw [hM2] at h1; rw [hP1] at h2
        exact Finset.disjoint_left.mp hd h2 h1
      · exact absurd rfl hab
    · refine ⟨fun a b => b < a, wellFounded_gt, wellFounded_lt, ?_⟩
      intro a b k hab ha hb
      fin_cases a <;> fin_cases b
      · exact absurd rfl hab
      · exfalso
        have h1 := hmemM 0 k ha
        have h2 := hmemP 1 k hb
        rw [hM1] at h1; rw [hP2] at h2
        exact Finset.disjoint_left.mp hd h1 h2
      · decide
      · exact absurd rfl hab
  refine ⟨?_, ?_⟩
  · intro h1 h2 hd
    obtain ⟨R, wf1, wf2, hR⟩ := hRex hd
    have hC : ∀ j, KangKurtz.SCC.Balance ν ν' α β (th j) ∨
        KangKurtz.SCC.TimeScale ν ν' α β γ (th j) := by
      intro j
      rw [← RRAux_KangKurtz_Combine_lemma_3_8.ts_iff ν ν' α β (hth j)]
      fin_cases j
      · simpa [th, Cond32] using h1
      · simpa [th, Cond32] using h2
    by_cases hT : TimeScale ν ν' α β γ θ
    · exact Or.inr hT
    left
    rw [RRAux_KangKurtz_Combine_lemma_3_8.ts_iff ν ν' α β hθnn] at hT
    apply RRAux_KangKurtz_Combine_lemma_3_8.core ν ν' α β θ φ hsum R wf1 wf2 hR
    intro j hj
    rcases hC j with hb | ht
    · exact hBal j hb
    exfalso
    have hex : ∃ k ∈ KangKurtz.SCC.GammaPlus ν ν' θ ∪ KangKurtz.SCC.GammaMinus ν ν' θ,
        KangKurtz.SCC.alphaTheta α θ - KangKurtz.SCC.rho ν α β k < γ := by
      by_contra hc
      push Not at hc
      exact hT (RRAux_KangKurtz_Combine_lemma_3_8.ts_of_bound ν ν' α β hc)
    obtain ⟨k, hk, hlt⟩ := hex
    have hk2 := hk
    rw [RRAux_KangKurtz_Combine_lemma_3_8.memG, hsum, RRAux_KangKurtz_Combine_lemma_3_8.dot_sum] at hk2
    obtain ⟨j1, _, hj1'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk2
    have hj1 := (RRAux_KangKurtz_Combine_lemma_3_8.memG ν ν').mpr hj1'
    have h1 := RRAux_KangKurtz_Combine_lemma_3_8.le_maxRho ν α β hj1
    have h2 : KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaPlus ν ν' (φ j1) ∪ KangKurtz.SCC.GammaMinus ν ν' (φ j1)) ≤
        Finset.univ.sup (fun j' => KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaPlus ν ν' (φ j') ∪ KangKurtz.SCC.GammaMinus ν ν' (φ j'))) :=
      Finset.le_sup (f := fun j' => KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaPlus ν ν' (φ j') ∪ KangKurtz.SCC.GammaMinus ν ν' (φ j')))
        (Finset.mem_univ j1)
    rw [← hj] at h2
    have h3 := le_trans h1 h2
    have hne : KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaPlus ν ν' (φ j) ∪ KangKurtz.SCC.GammaMinus ν ν' (φ j)) ≠ ⊥ :=
      ne_bot_of_le_ne_bot (WithBot.coe_ne_bot) h3
    obtain ⟨k', hk', hkeq⟩ := RRAux_KangKurtz_Combine_lemma_3_8.maxRho_attain ν α β hne
    rw [hkeq] at h3
    have h4 : KangKurtz.SCC.rho ν α β k ≤ KangKurtz.SCC.rho ν α β k' := WithBot.coe_le_coe.mp h3
    rw [hGP j, hGM j] at hk'
    have h5 := RRAux_KangKurtz_Combine_lemma_3_8.ts_bound ν ν' α β ht hk'
    have h6 := RRAux_KangKurtz_Combine_lemma_3_8.alpha_mono α (hsupp j)
      (RRAux_KangKurtz_Combine_lemma_3_8.supp_nonempty ν ν' (hth j) hk')
    linarith
  · intro h1 h2 hd
    obtain ⟨R, wf1, wf2, hR⟩ := hRex hd
    apply RRAux_KangKurtz_Combine_lemma_3_8.core ν ν' α β θ φ hsum R wf1 wf2 hR
    intro j _
    apply hBal
    fin_cases j
    · simpa [th] using h1
    · simpa [th] using h2

#print axioms solution
