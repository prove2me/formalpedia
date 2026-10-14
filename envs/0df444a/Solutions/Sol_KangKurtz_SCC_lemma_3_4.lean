-- Prove2me | solution 1 for KangKurtz.SCC.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T12:43:19.355779+00:00
-- url     : https://prove2.me/submissions/fabaab44-47c4-4cc2-a28d-377c32cb2ca2

import Mathlib
import Definitions.Def_KangKurtz_SCC_Setting

namespace RRAux_KangKurtz_SCC_lemma_3_4

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

theorem alpha_mono {φ ψ : Fin s → ℝ} (hle : ∀ i, φ i ≤ ψ i)
    (h : (Finset.univ.filter (fun i => 0 < φ i)).Nonempty) :
    alphaTheta α φ ≤ alphaTheta α ψ := by
  have hsub : Finset.univ.filter (fun i => 0 < φ i) ⊆ Finset.univ.filter (fun i => 0 < ψ i) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact lt_of_lt_of_le hi (hle i)
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

def Reach {m : ℕ} (θs : Fin m → Fin s → ℝ) (j j' : Fin m) : Prop :=
  j ≠ j' ∧ ∃ i i', θs j i ≠ 0 ∧ θs j' i' ≠ 0 ∧ Relation.ReflTransGen (Edge ν ν') i i'

theorem reach_trans {m : ℕ} (θs : Fin m → Fin s → ℝ)
    (hone : ∀ j i i', θs j i ≠ 0 → θs j i' ≠ 0 → SameComp ν ν' i i')
    (hdist : ∀ j j', j ≠ j' → ∀ i i',
      θs j i ≠ 0 → θs j' i' ≠ 0 → ¬ SameComp ν ν' i i')
    {a b c : Fin m} (h1 : Reach ν ν' θs a b) (h2 : Reach ν ν' θs b c) :
    Reach ν ν' θs a c := by
  obtain ⟨hab, i, i1, hi, hi1, hr1⟩ := h1
  obtain ⟨hbc, i2, i3, hi2, hi3, hr2⟩ := h2
  have h12 := (hone b i1 i2 hi1 hi2).1
  refine ⟨?_, i, i3, hi, hi3, hr1.trans (h12.trans hr2)⟩
  intro hac
  subst hac
  have h3i := (hone a i3 i hi3 hi).1
  exact hdist a b hab i i1 hi hi1 ⟨hr1, h12.trans (hr2.trans h3i)⟩

theorem edge_reach {m : ℕ} (θs : Fin m → Fin s → ℝ) (hθs : ∀ j i, 0 ≤ θs j i)
    {a b : Fin m} (hab : a ≠ b) {k : Fin r}
    (ha : dot ν ν' (θs a) k < 0) (hb : 0 < dot ν ν' (θs b) k) : Reach ν ν' θs a b := by
  obtain ⟨i, hi, hik⟩ := exists_consume ν ν' (hθs a) ha
  obtain ⟨i', hi', hik'⟩ := exists_produce ν ν' (hθs b) hb
  exact ⟨hab, i, i', hi, hi', Relation.ReflTransGen.single ⟨k, hik, hik'⟩⟩

theorem core {m : ℕ} (θ : Fin s → ℝ) (θs : Fin m → Fin s → ℝ)
    (hθs : ∀ j i, 0 ≤ θs j i)
    (hsum : θ = ∑ j, θs j)
    (hone : ∀ j i i', θs j i ≠ 0 → θs j i' ≠ 0 → SameComp ν ν' i i')
    (hdist : ∀ j j', j ≠ j' → ∀ i i',
      θs j i ≠ 0 → θs j' i' ≠ 0 → ¬ SameComp ν ν' i i')
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
  -- lower bounds
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
    have : IsTrans (Fin m) (Reach ν ν' θs) :=
      ⟨fun a b c h1 h2 => reach_trans ν ν' θs hone hdist h1 h2⟩
    have : Std.Irrefl (Reach ν ν' θs) := ⟨fun a h => h.1 rfl⟩
    have : IsTrans (Fin m) (flip (Reach ν ν' θs)) :=
      ⟨fun a b c h1 h2 => reach_trans ν ν' θs hone hdist h2 h1⟩
    have : Std.Irrefl (flip (Reach ν ν' θs)) := ⟨fun a h => h.1 rfl⟩
    have wf1 := Finite.wellFounded_of_trans_of_irrefl (Reach ν ν' θs)
    have wf2 := Finite.wellFounded_of_trans_of_irrefl (flip (Reach ν ν' θs))
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
          have hR := edge_reach ν ν' θs hθs hjj hneg hkpos
          have hkG : k ∈ GammaPlus ν ν' (θs j') ∪ GammaMinus ν ν' (θs j') :=
            (memG ν ν').mpr (ne_of_lt hneg)
          have hge : M ≤ Mf j' := by
            rw [hj1, hkeq]; exact le_maxRho ν α β hkG
          exact hjmin j' (le_antisymm (hMfle j') hge) hR
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
          have hR := edge_reach ν ν' θs hθs hjj hkneg hpos
          have hkG : k ∈ GammaPlus ν ν' (θs j') ∪ GammaMinus ν ν' (θs j') :=
            (memG ν ν').mpr (ne_of_gt hpos)
          have hge : M ≤ Mf j' := by
            rw [hj1, hkeq]; exact le_maxRho ν α β hkG
          exact hjmax j' (le_antisymm (hMfle j') hge) hR
        · exact ⟨j, Finset.mem_univ _, hkneg⟩
      have hkθ : k ∈ GammaMinus ν ν' θ := by simpa [GammaMinus] using hθk
      rw [hj1, hkeq]
      exact le_maxRho ν α β hkθ
  unfold Balance
  apply le_antisymm
  · exact le_trans (hupper _ Finset.subset_union_right) hlow.1
  · exact le_trans (hupper _ Finset.subset_union_left) hlow.2

end

end RRAux_KangKurtz_SCC_lemma_3_4

open KangKurtz.SCC in
theorem solution
    {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ)
    (hbinary : BinaryReactions ν)
    (α : Fin s → ℝ) (hα : ∀ i, 0 ≤ α i)
    (β : Fin r → ℝ) (γ : ℝ)
    (θ : Fin s → ℝ) (hθ : ∀ i, 0 ≤ θ i)
    {m : ℕ} (θs : Fin m → Fin s → ℝ)
    (hθs : ∀ j i, 0 ≤ θs j i)
    (hsum : θ = ∑ j, θs j)
    (hone : ∀ j i i', θs j i ≠ 0 → θs j i' ≠ 0 → SameComp ν ν' i i')
    (hdist : ∀ j j', j ≠ j' → ∀ i i',
      θs j i ≠ 0 → θs j' i' ≠ 0 → ¬ SameComp ν ν' i i') :
    ((∀ j, Cond32 ν ν' α β γ (θs j)) → Cond32 ν ν' α β γ θ) ∧
    ((∀ j, Balance ν ν' α β (θs j)) → Balance ν ν' α β θ) ∧
    ((∀ j, TimeScale ν ν' α β γ (θs j)) → TimeScale ν ν' α β γ θ) := by
  have hpiece : ∀ k, k ∈ GammaPlus ν ν' θ ∪ GammaMinus ν ν' θ →
      ∃ j, k ∈ GammaPlus ν ν' (θs j) ∪ GammaMinus ν ν' (θs j) := by
    intro k hk
    rw [RRAux_KangKurtz_SCC_lemma_3_4.memG, hsum, RRAux_KangKurtz_SCC_lemma_3_4.dot_sum] at hk
    obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk
    exact ⟨j, (RRAux_KangKurtz_SCC_lemma_3_4.memG ν ν').mpr hj⟩
  have hle : ∀ j i, θs j i ≤ θ i := by
    intro j i
    rw [hsum, Finset.sum_apply]
    exact Finset.single_le_sum (f := fun j => θs j i) (fun j' _ => hθs j' i) (Finset.mem_univ j)
  have halpha : ∀ j k, k ∈ GammaPlus ν ν' (θs j) ∪ GammaMinus ν ν' (θs j) →
      alphaTheta α (θs j) ≤ alphaTheta α θ := by
    intro j k hk
    exact RRAux_KangKurtz_SCC_lemma_3_4.alpha_mono α (hle j)
      (RRAux_KangKurtz_SCC_lemma_3_4.supp_nonempty ν ν' (hθs j) hk)
  refine ⟨?_, ?_, ?_⟩
  · intro h
    by_cases hT : TimeScale ν ν' α β γ θ
    · exact Or.inr hT
    left
    apply RRAux_KangKurtz_SCC_lemma_3_4.core ν ν' α β θ θs hθs hsum hone hdist
    intro j hj
    rcases h j with hb | ht
    · exact hb
    exfalso
    have hex : ∃ k ∈ GammaPlus ν ν' θ ∪ GammaMinus ν ν' θ,
        alphaTheta α θ - rho ν α β k < γ := by
      by_contra hc
      push Not at hc
      exact hT (RRAux_KangKurtz_SCC_lemma_3_4.ts_of_bound ν ν' α β hc)
    obtain ⟨k, hk, hlt⟩ := hex
    obtain ⟨j1, hj1⟩ := hpiece k hk
    have h1 := RRAux_KangKurtz_SCC_lemma_3_4.le_maxRho ν α β hj1
    have h2 : maxRho ν α β (GammaPlus ν ν' (θs j1) ∪ GammaMinus ν ν' (θs j1)) ≤
        Finset.univ.sup (fun j' => maxRho ν α β (GammaPlus ν ν' (θs j') ∪ GammaMinus ν ν' (θs j'))) :=
      Finset.le_sup (f := fun j' => maxRho ν α β (GammaPlus ν ν' (θs j') ∪ GammaMinus ν ν' (θs j')))
        (Finset.mem_univ j1)
    rw [← hj] at h2
    have h3 := le_trans h1 h2
    have hne : maxRho ν α β (GammaPlus ν ν' (θs j) ∪ GammaMinus ν ν' (θs j)) ≠ ⊥ :=
      ne_bot_of_le_ne_bot (WithBot.coe_ne_bot) h3
    obtain ⟨k', hk', hkeq⟩ := RRAux_KangKurtz_SCC_lemma_3_4.maxRho_attain ν α β hne
    rw [hkeq] at h3
    have h4 : rho ν α β k ≤ rho ν α β k' := WithBot.coe_le_coe.mp h3
    have h5 := RRAux_KangKurtz_SCC_lemma_3_4.ts_bound ν ν' α β ht hk'
    have h6 := halpha j k' hk'
    linarith
  · intro h
    apply RRAux_KangKurtz_SCC_lemma_3_4.core ν ν' α β θ θs hθs hsum hone hdist
    intro j _
    exact h j
  · intro h
    apply RRAux_KangKurtz_SCC_lemma_3_4.ts_of_bound
    intro k hk
    obtain ⟨j, hj⟩ := hpiece k hk
    have h5 := RRAux_KangKurtz_SCC_lemma_3_4.ts_bound ν ν' α β (h j) hj
    have h6 := halpha j k hj
    linarith

#print axioms solution
