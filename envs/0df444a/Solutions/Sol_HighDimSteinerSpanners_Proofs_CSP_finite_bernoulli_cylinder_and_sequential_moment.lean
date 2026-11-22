-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.CSP.finite_bernoulli_cylinder_and_sequential_moment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:50:19.076988+00:00
-- url     : https://prove2.me/submissions/2e274d4b-f8e4-4826-9999-79ba1613a55b

module
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_WitnessProjection
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Bernoulli
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_bernWeight_nonnegative
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_bernoulli_cylinder
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_snoc_injective
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_snoc_mem_pool
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_sequentialTailWeight_nonnegative

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section
namespace HighDimSteinerSpanners.Proofs.CSP
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (hp : ∀ i : ι, 0 ≤ p i ∧ p i ≤ 1) :
    (∀ ω : ι → Bool, 0 ≤ bernWeight p ω) ∧
    (∑ ω : ι → Bool, bernWeight p ω = 1) ∧
    (∀ S : Finset ι,
      ∑ ω : ι → Bool, (if ∀ i ∈ S, ω i = true then bernWeight p ω else 0) = ∏ i ∈ S, p i) ∧
    (∀ (β γ : Type) [DecidableEq β] [DecidableEq γ]
      (Pool : Finset β) (K : ℕ) (α_step : ℝ),
      0 ≤ α_step →
      ∀ (Base : (ι → Bool) → Prop) [DecidablePred Base]
        (A : (ι → Bool) → Finset β),
        (∀ ω : ι → Bool, A ω ⊆ Pool) →
        ∀ (S₀ : Finset ι)
          (U : (m : ℕ) → (Fin m → β) → Finset ι)
          (M_wit : (m : ℕ) → (Fin m → β) → β → Finset γ)
          (Q : (m : ℕ) → (Fin m → β) → β → γ → Finset ι),
          (∀ z₀ : Fin 0 → β, S₀ ⊆ U 0 z₀) →
          (∀ m < K, ∀ (z_prev : Fin m → β) (b : β),
            U m z_prev ⊆ U (m + 1) (Fin.snoc z_prev b)) →
          (∀ m < K, ∀ z_prev : Fin m → β,
            Function.Injective z_prev → (∀ t : Fin m, z_prev t ∈ Pool) →
            ∀ b ∈ Pool \ Finset.univ.image z_prev, ∀ w ∈ M_wit m z_prev b,
              Q m z_prev b w ⊆ U (m + 1) (Fin.snoc z_prev b) \ U m z_prev) →
          (∀ ω : ι → Bool, Base ω →
            (∀ i ∈ S₀, ω i = true) ∧
            (∀ z : Fin K → β, Function.Injective z → (∀ m : Fin K, z m ∈ A ω) →
              ∀ m : Fin K,
                ∃ w ∈ M_wit m.1 (fun t : Fin m.1 => z (t.castLE (Nat.le_of_lt m.isLt))) (z m),
                  ∀ i ∈ Q m.1 (fun t : Fin m.1 => z (t.castLE (Nat.le_of_lt m.isLt))) (z m) w,
                    ω i = true)) →
          (∀ m < K, ∀ z_prev : Fin m → β,
            Function.Injective z_prev → (∀ t : Fin m, z_prev t ∈ Pool) →
            ∑ b ∈ Pool \ Finset.univ.image z_prev,
              ∑ w ∈ M_wit m z_prev b, (∏ i ∈ Q m z_prev b w, p i) ≤ α_step) →
          ∑ ω : ι → Bool, (if Base ω ∧ K ≤ (A ω).card then bernWeight p ω else 0) ≤
            (∏ i ∈ S₀, p i) * α_step ^ K) :=
by
  have hW_nn := bernWeight_nonnegative p hp
  have hp_prod_nn : ∀ T : Finset ι, 0 ≤ ∏ i ∈ T, p i :=
    fun T => Finset.prod_nonneg (fun i _ => (hp i).1)
  have h_cyl := bernoulli_cylinder p
  have hW_sum : ∑ ω : ι → Bool, bernWeight p ω = 1 := by
    simpa using h_cyl ∅
  refine ⟨hW_nn, hW_sum, h_cyl, ?_⟩
  intro β γ _ _ Pool K α_step hα_nn Base _ A hA_sub S₀ U M_wit Q
    hU0 hU_mono hQ_sub hBase_wit hStep_sum
  have snoc_inj := snoc_injective Pool
  have snoc_mem_pool := snoc_mem_pool Pool
  let tailInd := sequentialTailWeight p Pool M_wit Q
  have tailInd_nonneg := sequentialTailWeight_nonnegative p Pool M_wit Q hW_nn
  have sum_tailInd_le : ∀ (r m : ℕ), m + r ≤ K →
      ∀ (z_prev : Fin m → β), Function.Injective z_prev → (∀ t : Fin m, z_prev t ∈ Pool) →
      ∀ (Acc : Finset ι), Acc ⊆ U m z_prev →
      ∑ ω : ι → Bool, tailInd r m z_prev Acc ω ≤ (∏ i ∈ Acc, p i) * α_step ^ r := by
    intro r
    induction r with
    | zero =>
      intro m _ z_prev _ _ Acc _
      dsimp [tailInd, sequentialTailWeight]
      rw [h_cyl Acc, pow_zero, mul_one]
    | succ r ih =>
      intro m hmr z_prev hinj hz_pool Acc hAcc
      have hm : m < K := by omega
      have hmr' : (m + 1) + r ≤ K := by omega
      let B_rem : Finset β := Pool \ Finset.univ.image z_prev
      have hswap : ∑ ω : ι → Bool, tailInd (r + 1) m z_prev Acc ω =
          ∑ b ∈ B_rem, ∑ w ∈ M_wit m z_prev b,
            ∑ ω : ι → Bool,
              tailInd r (m + 1) (Fin.snoc z_prev b) (Acc ∪ Q m z_prev b w) ω := by
        dsimp [tailInd, sequentialTailWeight]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun b _ => Finset.sum_comm)
      rw [hswap]
      have hterm : ∀ b ∈ B_rem, ∀ w ∈ M_wit m z_prev b,
          ∑ ω : ι → Bool,
            tailInd r (m + 1) (Fin.snoc z_prev b) (Acc ∪ Q m z_prev b w) ω ≤
          (∏ i ∈ Acc, p i) * (∏ i ∈ Q m z_prev b w, p i) * α_step ^ r := by
        intro b hb w hw
        have hinj' : Function.Injective (Fin.snoc z_prev b) := snoc_inj m z_prev hinj b hb
        have hz_pool' : ∀ u : Fin (m + 1), (Fin.snoc z_prev b : Fin (m + 1) → β) u ∈ Pool :=
          snoc_mem_pool m z_prev hz_pool b (Finset.mem_sdiff.mp hb).1
        have hQ_bw : Q m z_prev b w ⊆ U (m + 1) (Fin.snoc z_prev b) \ U m z_prev :=
          hQ_sub m hm z_prev hinj hz_pool b hb w hw
        have hAcc' : Acc ∪ Q m z_prev b w ⊆ U (m + 1) (Fin.snoc z_prev b) :=
          Finset.union_subset
            (Finset.Subset.trans hAcc (hU_mono m hm z_prev b))
            (Finset.Subset.trans hQ_bw Finset.sdiff_subset)
        have hDisj : Disjoint Acc (Q m z_prev b w) := by
          rw [Finset.disjoint_left]
          intro i hiAcc hiQ
          exact (Finset.mem_sdiff.mp (hQ_bw hiQ)).2 (hAcc hiAcc)
        have h_ih := ih (m + 1) hmr' (Fin.snoc z_prev b) hinj' hz_pool' (Acc ∪ Q m z_prev b w) hAcc'
        rwa [Finset.prod_union hDisj] at h_ih
      have hsum_le : ∑ b ∈ B_rem, ∑ w ∈ M_wit m z_prev b,
          ∑ ω : ι → Bool,
            tailInd r (m + 1) (Fin.snoc z_prev b) (Acc ∪ Q m z_prev b w) ω ≤
          ∑ b ∈ B_rem, ∑ w ∈ M_wit m z_prev b,
            ((∏ i ∈ Acc, p i) * (∏ i ∈ Q m z_prev b w, p i) * α_step ^ r) :=
        Finset.sum_le_sum (fun b hb => Finset.sum_le_sum (fun w hw => hterm b hb w hw))
      have hfactor : ∑ b ∈ B_rem, ∑ w ∈ M_wit m z_prev b,
          ((∏ i ∈ Acc, p i) * (∏ i ∈ Q m z_prev b w, p i) * α_step ^ r) =
          (∏ i ∈ Acc, p i) *
            (∑ b ∈ B_rem, ∑ w ∈ M_wit m z_prev b, (∏ i ∈ Q m z_prev b w, p i)) *
            α_step ^ r := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [Finset.mul_sum, Finset.sum_mul]
      have hstep := hStep_sum m hm z_prev hinj hz_pool
      have hmul1 : (∏ i ∈ Acc, p i) *
          (∑ b ∈ B_rem, ∑ w ∈ M_wit m z_prev b, (∏ i ∈ Q m z_prev b w, p i)) ≤
          (∏ i ∈ Acc, p i) * α_step :=
        mul_le_mul_of_nonneg_left hstep (hp_prod_nn Acc)
      have hmul2 : (∏ i ∈ Acc, p i) *
          (∑ b ∈ B_rem, ∑ w ∈ M_wit m z_prev b, (∏ i ∈ Q m z_prev b w, p i)) * α_step ^ r ≤
          (∏ i ∈ Acc, p i) * α_step * α_step ^ r :=
        mul_le_mul_of_nonneg_right hmul1 (pow_nonneg hα_nn r)
      calc
        ∑ b ∈ B_rem, ∑ w ∈ M_wit m z_prev b,
            ∑ ω : ι → Bool,
              tailInd r (m + 1) (Fin.snoc z_prev b) (Acc ∪ Q m z_prev b w) ω
          ≤ (∏ i ∈ Acc, p i) *
              (∑ b ∈ B_rem, ∑ w ∈ M_wit m z_prev b, (∏ i ∈ Q m z_prev b w, p i)) *
              α_step ^ r := by rwa [hfactor] at hsum_le
        _ ≤ (∏ i ∈ Acc, p i) * α_step * α_step ^ r := hmul2
        _ = (∏ i ∈ Acc, p i) * α_step ^ (r + 1) := by rw [mul_assoc, ← pow_succ']
  have bernWeight_le_tailInd : ∀ (ω : ι → Bool) (z : Fin K → β),
      Function.Injective z →
      (∀ s : Fin K, z s ∈ Pool) →
      (∀ s : Fin K,
        ∃ w ∈ M_wit s.1 (fun t : Fin s.1 => z (t.castLE (Nat.le_of_lt s.isLt))) (z s),
          ∀ i ∈ Q s.1 (fun t : Fin s.1 => z (t.castLE (Nat.le_of_lt s.isLt))) (z s) w,
            ω i = true) →
      ∀ (r m : ℕ) (hmr : m + r = K) (Acc : Finset ι),
        (∀ i ∈ Acc, ω i = true) →
        bernWeight p ω ≤
          tailInd r m (fun t : Fin m => z (t.castLE (Nat.le.intro hmr))) Acc ω := by
    intro ω z hz_inj hz_pool hwit r
    induction r with
    | zero =>
      intro m hmr Acc hω_Acc
      dsimp [tailInd, sequentialTailWeight]
      rw [if_pos hω_Acc]
    | succ r ih =>
      intro m hmr Acc hω_Acc
      have hm : m < K := by omega
      have hmr' : (m + 1) + r = K := by omega
      let s : Fin K := ⟨m, hm⟩
      let z_m : Fin m → β := fun t => z (t.castLE (Nat.le_of_lt hm))
      let b₀ : β := z s
      have hb₀ : b₀ ∈ Pool \ Finset.univ.image z_m := by
        rw [Finset.mem_sdiff]
        refine ⟨hz_pool s, ?_⟩
        intro himg
        rcases Finset.mem_image.mp himg with ⟨t, _, ht_eq⟩
        have hval := congr_arg Fin.val (hz_inj ht_eq)
        simp only [s, Fin.val_castLE] at hval
        exact absurd hval (Nat.ne_of_lt t.isLt)
      obtain ⟨w₀, hw₀_mem, hw₀_true⟩ := hwit s
      have hω_union : ∀ i ∈ Acc ∪ Q m z_m b₀ w₀, ω i = true := by
        intro i hi
        rcases Finset.mem_union.mp hi with hi | hi
        · exact hω_Acc i hi
        · exact hw₀_true i hi
      have hsnoc : Fin.snoc z_m b₀ =
          (fun t : Fin (m + 1) => z (t.castLE (Nat.le.intro hmr'))) := by
        funext u
        refine Fin.lastCases ?_ (fun t => ?_) u
        · simp only [Fin.snoc_last, b₀, s]
          congr 1
        · simp only [Fin.snoc_castSucc, z_m]
          congr 1
      have h1 : bernWeight p ω ≤
          tailInd r (m + 1) (Fin.snoc z_m b₀) (Acc ∪ Q m z_m b₀ w₀) ω := by
        have h_ih := ih (m + 1) hmr' (Acc ∪ Q m z_m b₀ w₀) hω_union
        rwa [← hsnoc] at h_ih
      have h2 : tailInd r (m + 1) (Fin.snoc z_m b₀) (Acc ∪ Q m z_m b₀ w₀) ω ≤
          ∑ w ∈ M_wit m z_m b₀,
            tailInd r (m + 1) (Fin.snoc z_m b₀) (Acc ∪ Q m z_m b₀ w) ω :=
        Finset.single_le_sum
          (fun w _ => tailInd_nonneg r (m + 1) (Fin.snoc z_m b₀) (Acc ∪ Q m z_m b₀ w) ω)
          hw₀_mem
      have h3 : ∑ w ∈ M_wit m z_m b₀,
          tailInd r (m + 1) (Fin.snoc z_m b₀) (Acc ∪ Q m z_m b₀ w) ω ≤
          tailInd (r + 1) m (fun t : Fin m => z (t.castLE (Nat.le.intro hmr))) Acc ω := by
        change ∑ w ∈ M_wit m z_m b₀,
            tailInd r (m + 1) (Fin.snoc z_m b₀) (Acc ∪ Q m z_m b₀ w) ω ≤
          ∑ b ∈ Pool \ Finset.univ.image z_m,
            ∑ w ∈ M_wit m z_m b,
              tailInd r (m + 1) (Fin.snoc z_m b) (Acc ∪ Q m z_m b w) ω
        exact Finset.single_le_sum
          (fun b _ => Finset.sum_nonneg (fun w _ =>
            tailInd_nonneg r (m + 1) (Fin.snoc z_m b) (Acc ∪ Q m z_m b w) ω))
          hb₀
      exact le_trans h1 (le_trans h2 h3)
  have hpt_ω : ∀ ω : ι → Bool,
      (if Base ω ∧ K ≤ (A ω).card then bernWeight p ω else 0) ≤
        tailInd K 0 Fin.elim0 S₀ ω := by
    intro ω
    by_cases h : Base ω ∧ K ≤ (A ω).card
    · rw [if_pos h]
      obtain ⟨T₀, hT₀_sub, hT₀_card⟩ := Finset.exists_subset_card_eq h.2
      let e : Fin K ≃ ↥T₀ := (finCongr hT₀_card.symm).trans T₀.equivFin.symm
      let z : Fin K → β := fun s => (e s).1
      have hz_inj : Function.Injective z := Subtype.val_injective.comp e.injective
      have hz_A : ∀ s : Fin K, z s ∈ A ω := fun s => hT₀_sub (e s).2
      have hz_pool : ∀ s : Fin K, z s ∈ Pool := fun s => hA_sub ω (hz_A s)
      obtain ⟨hω_S₀, hwit_all⟩ := hBase_wit ω h.1
      have hdom := bernWeight_le_tailInd ω z hz_inj hz_pool (hwit_all z hz_inj hz_A)
        K 0 (Nat.zero_add K) S₀ hω_S₀
      have hz0 : (fun t : Fin 0 => z (t.castLE (Nat.le.intro (Nat.zero_add K)))) = Fin.elim0 :=
        Subsingleton.elim _ _
      rwa [hz0] at hdom
    · rw [if_neg h]
      exact tailInd_nonneg K 0 Fin.elim0 S₀ ω
  calc
    ∑ ω : ι → Bool, (if Base ω ∧ K ≤ (A ω).card then bernWeight p ω else 0)
      ≤ ∑ ω : ι → Bool, tailInd K 0 Fin.elim0 S₀ ω :=
        Finset.sum_le_sum (fun ω _ => hpt_ω ω)
    _ ≤ (∏ i ∈ S₀, p i) * α_step ^ K :=
        sum_tailInd_le K 0 (Nat.zero_add K).le Fin.elim0
          (fun t => Fin.elim0 t) (fun t => Fin.elim0 t) S₀ (hU0 Fin.elim0)
end HighDimSteinerSpanners.Proofs.CSP
