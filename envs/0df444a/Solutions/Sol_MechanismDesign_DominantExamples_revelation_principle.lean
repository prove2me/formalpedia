-- Prove2me | solution 1 for MechanismDesign.DominantExamples.revelation_principle
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:31:16.294403+00:00
-- url     : https://prove2.me/submissions/82b1a50b-1fb2-40f4-b7a1-555fdd44b3a0

import Mathlib
import Definitions.Def_MechanismDesign_DominantExamples_Auction



namespace MechanismDesign.DominantExamples

theorem revelation_principle_core {ι : Type*} [Fintype ι] [DecidableEq ι] (E : AuctionSetting)
    {S : ι → Type*} (alloc pay : ι → ((j : ι) → S j) → ℝ)
    (h_alloc_nonneg : ∀ s i, 0 ≤ alloc i s) (h_alloc_le_one : ∀ s i, alloc i s ≤ 1)
    (h_alloc_sum : ∀ s, ∑ i, alloc i s ≤ 1)
    (σ : (i : ι) → ℝ → S i)
    (h_dominant : ∀ i, ∀ x ∈ Set.Icc E.lo E.hi, ∀ s : (j : ι) → S j, ∀ s' : S i,
      x * alloc i (Function.update s i s') - pay i (Function.update s i s') ≤
        x * alloc i (Function.update s i (σ i x)) - pay i (Function.update s i (σ i x))) :
    ∃ M : AuctionMechanism E ι, M.IsDSIC ∧
      ∀ θ ∈ E.typeSpace ι, ∀ i,
        M.q i θ = alloc i (fun j => σ j (θ j)) ∧ M.t i θ = pay i (fun j => σ j (θ j)) := by
  refine ⟨{ q := fun i θ => alloc i (fun j => σ j (θ j)),
            t := fun i θ => pay i (fun j => σ j (θ j)),
            q_nonneg := fun θ _ i => h_alloc_nonneg _ i,
            q_le_one := fun θ _ i => h_alloc_le_one _ i,
            sum_q_le_one := fun θ _ => h_alloc_sum _ }, ?_, fun θ _ i => ⟨rfl, rfl⟩⟩
  intro i θ hθ x _
  have hupd : (fun j => σ j (Function.update θ i x j)) =
      Function.update (fun j => σ j (θ j)) i (σ i x) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  have h := h_dominant i (θ i) (hθ i trivial) (fun j => σ j (θ j)) (σ i x)
  have h2 : Function.update (fun j => σ j (θ j)) i (σ i (θ i)) = (fun j => σ j (θ j)) :=
    Function.update_eq_self i _
  simp only [h2] at h
  show θ i * alloc i (fun j => σ j (Function.update θ i x j)) -
      pay i (fun j => σ j (Function.update θ i x j)) ≤
    θ i * alloc i (fun j => σ j (θ j)) - pay i (fun j => σ j (θ j))
  rw [hupd]; exact h

section Canon
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma cQ_nonneg (ψ : ι → ℝ → ℝ) (i : ι) (θ : ι → ℝ) : 0 ≤ canonicalAuctionQ ψ i θ := by
  unfold canonicalAuctionQ; split_ifs <;> positivity

lemma tieCount_pos (ψ : ι → ℝ → ℝ) (θ : ι → ℝ) (i : ι) : 0 < tieCount ψ θ i := by
  unfold tieCount
  apply Finset.card_pos.2
  exact ⟨i, by simp⟩

lemma cQ_le_one (ψ : ι → ℝ → ℝ) (i : ι) (θ : ι → ℝ) : canonicalAuctionQ ψ i θ ≤ 1 := by
  unfold canonicalAuctionQ
  split_ifs
  · have : (1 : ℝ) ≤ (tieCount ψ θ i : ℝ) := by exact_mod_cast tieCount_pos ψ θ i
    rw [div_le_one (by linarith)]; exact this
  · norm_num

lemma cT_eq (E : AuctionSetting) (ψ : ι → ℝ → ℝ) (i : ι) (θ : ι → ℝ) (x : ℝ) :
    canonicalAuctionT E ψ i (Function.update θ i x) =
      canonicalAuctionQ ψ i (Function.update θ i x) *
        sInf {x' | x' ∈ Set.Icc E.lo E.hi ∧
          0 < canonicalAuctionQ ψ i (Function.update θ i x')} := by
  unfold canonicalAuctionT
  split_ifs with h
  · simp only [Function.update_idem]
    congr 1
    unfold canonicalAuctionQ at h ⊢
    rw [if_pos]
    by_contra hc
    rw [if_neg hc] at h
    exact lt_irrefl _ h
  · have : canonicalAuctionQ ψ i (Function.update θ i x) = 0 :=
      le_antisymm (not_lt.1 h) (cQ_nonneg ψ i _)
    rw [this, zero_mul]

lemma ca_key (E : AuctionSetting) (ψ : ι → ℝ → ℝ)
    (hψ : ∀ i, StrictMonoOn (ψ i) (Set.Icc E.lo E.hi)) (θ : ι → ℝ) (i : ι)
    {a : ℝ} (ha : a ∈ Set.Icc E.lo E.hi) {x : ℝ} (hx : x ∈ Set.Icc E.lo E.hi) :
    let xs := sInf {x' | x' ∈ Set.Icc E.lo E.hi ∧
          0 < canonicalAuctionQ ψ i (Function.update θ i x')}
    canonicalAuctionQ ψ i (Function.update θ i x) * (a - xs) ≤
        canonicalAuctionQ ψ i (Function.update θ i a) * (a - xs) ∧
      0 ≤ canonicalAuctionQ ψ i (Function.update θ i a) * (a - xs) := by
  intro xs
  set X := {x' | x' ∈ Set.Icc E.lo E.hi ∧
          0 < canonicalAuctionQ ψ i (Function.update θ i x')} with hXdef
  have hbdd : BddBelow X := ⟨E.lo, fun y hy => hy.1.1⟩
  have hmem : ∀ y ∈ Set.Icc E.lo E.hi, 0 < canonicalAuctionQ ψ i (Function.update θ i y) →
      xs ≤ y := fun y hy h => csInf_le hbdd ⟨hy, h⟩
  have hnn : 0 ≤ canonicalAuctionQ ψ i (Function.update θ i a) * (a - xs) := by
    by_cases h : 0 < canonicalAuctionQ ψ i (Function.update θ i a)
    · exact mul_nonneg h.le (sub_nonneg.2 (hmem a ha h))
    · rw [le_antisymm (not_lt.1 h) (cQ_nonneg ψ i _), zero_mul]
  refine ⟨?_, hnn⟩
  by_cases hxq : 0 < canonicalAuctionQ ψ i (Function.update θ i x)
  · rcases le_or_gt a xs with hle | hlt
    · have : canonicalAuctionQ ψ i (Function.update θ i x) * (a - xs) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hxq.le (by linarith)
      linarith
    · obtain ⟨x', hx'X, hx'lt⟩ := exists_lt_of_csInf_lt (show X.Nonempty from ⟨x, hx, hxq⟩) hlt
      obtain ⟨hx'I, hx'q⟩ := hx'X
      have hcond : 0 ≤ ψ i x' ∧ ∀ j, j ≠ i → ψ j (θ j) ≤ ψ i x' := by
        unfold canonicalAuctionQ at hx'q
        split_ifs at hx'q with hc
        · obtain ⟨h1, h2⟩ := hc
          simp only [Function.update_self] at h1 h2
          refine ⟨h1, fun j hj => ?_⟩
          have := h2 j hj
          rwa [Function.update_of_ne hj] at this
        · exact absurd hx'q (lt_irrefl _)
      have hlt2 : ψ i x' < ψ i a := hψ i hx'I ha hx'lt
      have hq1 : canonicalAuctionQ ψ i (Function.update θ i a) = 1 := by
        unfold canonicalAuctionQ
        have hc : 0 ≤ ψ i (Function.update θ i a i) ∧ ∀ j, j ≠ i →
            ψ j (Function.update θ i a j) ≤ ψ i (Function.update θ i a i) := by
          simp only [Function.update_self]
          refine ⟨by linarith [hcond.1], fun j hj => ?_⟩
          rw [Function.update_of_ne hj]; linarith [hcond.2 j hj]
        rw [if_pos hc]
        have ht : tieCount ψ (Function.update θ i a) i = 1 := by
          unfold tieCount
          rw [Finset.card_eq_one]
          refine ⟨i, ?_⟩
          ext k
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · intro hk
            by_contra hki
            rw [Function.update_of_ne hki, Function.update_self] at hk
            have := hcond.2 k hki
            linarith
          · intro hk; subst hk; rfl
        rw [ht]; norm_num
      rw [hq1, one_mul]
      have := cQ_le_one ψ i (Function.update θ i x)
      nlinarith
  · rw [le_antisymm (not_lt.1 hxq) (cQ_nonneg ψ i _), zero_mul]
    exact hnn

end Canon

lemma upd_mem' {ι : Type*} [DecidableEq ι] {E : AuctionSetting} {θ : ι → ℝ}
    (hθ : θ ∈ E.typeSpace ι) (i : ι) {x : ℝ} (hx : x ∈ Set.Icc E.lo E.hi) :
    Function.update θ i x ∈ E.typeSpace ι := by
  intro j _
  by_cases hj : j = i
  · subst hj; simpa using hx
  · simp [Function.update_of_ne hj]; exact hθ j trivial

theorem canonical_auction_core {ι : Type*} [Fintype ι] [DecidableEq ι] {E : AuctionSetting}
    (M : AuctionMechanism E ι) (hM : M.IsCanonical) :
    M.IsDSIC ∧ M.IsEPIR ∧
      ∀ i, ∀ θ ∈ E.typeSpace ι, M.u i (Function.update θ i E.lo) = 0 := by
  obtain ⟨ψ, hψ, hMψ⟩ := hM
  have hψm : ∀ i, StrictMonoOn (ψ i) (Set.Icc E.lo E.hi) := fun i => (hψ i).1
  -- value of reporting x for type a
  have hval : ∀ θ ∈ E.typeSpace ι, ∀ i, ∀ x ∈ Set.Icc E.lo E.hi, ∀ a : ℝ,
      a * M.q i (Function.update θ i x) - M.t i (Function.update θ i x) =
        canonicalAuctionQ ψ i (Function.update θ i x) *
          (a - sInf {x' | x' ∈ Set.Icc E.lo E.hi ∧
            0 < canonicalAuctionQ ψ i (Function.update θ i x')}) := by
    intro θ hθ i x hx a
    obtain ⟨h1, h2⟩ := hMψ _ (upd_mem' hθ i hx) i
    rw [h1, h2, cT_eq]; ring
  have hθi : ∀ θ ∈ E.typeSpace ι, ∀ i, θ i ∈ Set.Icc E.lo E.hi := fun θ hθ i => hθ i trivial
  refine ⟨?_, ?_, ?_⟩
  · intro i θ hθ x hx
    have e1 := hval θ hθ i x hx (θ i)
    have e2 := hval θ hθ i (θ i) (hθi θ hθ i) (θ i)
    simp only [Function.update_eq_self] at e2
    rw [e1, e2]
    have k := (ca_key E ψ hψm θ i (hθi θ hθ i) hx).1
    simpa only [Function.update_eq_self] using k
  · intro i θ hθ
    have e2 := hval θ hθ i (θ i) (hθi θ hθ i) (θ i)
    simp only [Function.update_eq_self] at e2
    rw [e2]
    have k := (ca_key E ψ hψm θ i (hθi θ hθ i) (hθi θ hθ i)).2
    simpa only [Function.update_eq_self] using k
  · intro i θ hθ
    have hlo : E.lo ∈ Set.Icc E.lo E.hi := ⟨le_rfl, E.lo_lt_hi.le⟩
    unfold AuctionMechanism.u
    have e2 := hval θ hθ i E.lo hlo E.lo
    simp only [Function.update_self]
    rw [e2]
    set X := {x' | x' ∈ Set.Icc E.lo E.hi ∧
          0 < canonicalAuctionQ ψ i (Function.update θ i x')} with hXdef
    by_cases h : 0 < canonicalAuctionQ ψ i (Function.update θ i E.lo)
    · have hle : sInf X ≤ E.lo := csInf_le ⟨E.lo, fun y hy => hy.1.1⟩ ⟨hlo, h⟩
      have hge : E.lo ≤ sInf X := le_csInf ⟨E.lo, hlo, h⟩ (fun y hy => hy.1.1)
      rw [show E.lo - sInf X = 0 by linarith, mul_zero]
    · rw [le_antisymm (not_lt.1 h) (cQ_nonneg ψ i _), zero_mul]

end MechanismDesign.DominantExamples

open MechanismDesign.DominantExamples


theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (E : AuctionSetting)
    {S : ι → Type*} (alloc pay : ι → ((j : ι) → S j) → ℝ)
    (h_alloc_nonneg : ∀ s i, 0 ≤ alloc i s) (h_alloc_le_one : ∀ s i, alloc i s ≤ 1)
    (h_alloc_sum : ∀ s, ∑ i, alloc i s ≤ 1)
    (σ : (i : ι) → ℝ → S i)
    (h_dominant : ∀ i, ∀ x ∈ Set.Icc E.lo E.hi, ∀ s : (j : ι) → S j, ∀ s' : S i,
      x * alloc i (Function.update s i s') - pay i (Function.update s i s') ≤
        x * alloc i (Function.update s i (σ i x)) - pay i (Function.update s i (σ i x))) :
    ∃ M : AuctionMechanism E ι, M.IsDSIC ∧
      ∀ θ ∈ E.typeSpace ι, ∀ i,
        M.q i θ = alloc i (fun j => σ j (θ j)) ∧ M.t i θ = pay i (fun j => σ j (θ j)) := by
  exact revelation_principle_core E alloc pay h_alloc_nonneg h_alloc_le_one h_alloc_sum σ h_dominant
