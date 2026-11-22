-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.CSP.freshHomQueryCardinality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:51:57.83695+00:00
-- url     : https://prove2.me/submissions/4005e210-e2cf-4b56-9ca2-814d51d7e01a

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.GCongr
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_WitnessMoments
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_CherryMoments
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_ordered_pairs_card
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_twice_choose_two_int


set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section
namespace HighDimSteinerSpanners.Proofs.CSP
theorem _root_.solution : ∀ {N q : ℕ} (z : Fin N → Fin q) (S_old : Finset (Fin N → Fin q))
    (T : Finset (Fin N)), (∀ v ∈ T, ∀ y ∈ S_old, z v ≠ y v) →
    T.card * (N - 1) - T.card.choose 2 ≤ (homQueries z \ S_old.biUnion homQueries).card := by
  intro N q z S_old T hT
  let P_sub : Finset (Fin N) → Finset (Fin N × Fin N) := fun S =>
    Finset.univ.filter (fun uv : Fin N × Fin N => uv.1 < uv.2 ∧ uv.1 ∈ S ∧ uv.2 ∈ S)
  have hP_sub_card : ∀ S : Finset (Fin N), (P_sub S).card = S.card.choose 2 := by
    intro S
    have heq : P_sub S = (S ×ˢ S).filter (fun uv => uv.1 < uv.2) := by
      ext uv
      simp [P_sub, and_comm]
    rw [heq, ordered_pairs_card]
  let P_all : Finset (Fin N × Fin N) := Finset.univ.filter (fun uv : Fin N × Fin N => uv.1 < uv.2)
  let P_hit : Finset (Fin N × Fin N) := P_all.filter (fun uv => uv.1 ∈ T ∨ uv.2 ∈ T)
  have hP_all_card : P_all.card = N.choose 2 := by
    have heq : P_all = P_sub Finset.univ := by
      ext uv
      simp [P_all, P_sub]
    rw [heq, hP_sub_card, Finset.card_univ, Fintype.card_fin]
  have hP_miss_card : (P_all.filter (fun uv => ¬(uv.1 ∈ T ∨ uv.2 ∈ T))).card = (N -
      T.card).choose 2 := by
    have heq : P_all.filter (fun uv => ¬(uv.1 ∈ T ∨ uv.2 ∈ T)) = P_sub (Finset.univ \ T) := by
      ext uv
      simp only [P_all, P_sub, Finset.mem_filter, Finset.mem_univ, Finset.mem_sdiff, true_and,
          not_or]
    rw [heq, hP_sub_card, Finset.card_univ_sdiff, Fintype.card_fin]
  have hP_hit_card : P_hit.card = N.choose 2 - (N - T.card).choose 2 := by
    have hpart := Finset.card_filter_add_card_filter_not (s := P_all) (p := fun uv => uv.1 ∈ T ∨
        uv.2 ∈ T)
    change P_hit.card + (P_all.filter (fun uv => ¬(uv.1 ∈ T ∨ uv.2 ∈ T))).card = P_all.card at hpart
    rw [hP_miss_card, hP_all_card] at hpart
    omega
  have hT_le : T.card ≤ N := by
    simpa [Fintype.card_fin] using (Finset.card_le_univ T)
  have hbinom_eq : T.card * (N - 1) - T.card.choose 2 = N.choose 2 - (N - T.card).choose 2 := by
    rcases Nat.eq_zero_or_pos N with rfl | hN_pos
    · have h0 : T.card = 0 := by omega
      simp [h0]
    · have hc1 : (N - T.card).choose 2 ≤ N.choose 2 := Nat.choose_le_choose 2 (Nat.sub_le N T.card)
      have hc2 : T.card.choose 2 ≤ T.card * (N - 1) := by
        have h2c : 2 * T.card.choose 2 = T.card * (T.card - 1) := by
          rw [Nat.choose_two_right]
          exact Nat.mul_div_cancel' (Even.two_dvd (Nat.even_mul_pred_self T.card))
        have hsub : T.card - 1 ≤ N - 1 := Nat.sub_le_sub_right hT_le 1
        have hmul : T.card * (T.card - 1) ≤ T.card * (N - 1) := Nat.mul_le_mul_left T.card hsub
        omega
      have hz : 2 * (((T.card * (N - 1) - T.card.choose 2 : ℕ) : ℤ)) =
          2 * (((N.choose 2 - (N - T.card).choose 2 : ℕ) : ℤ)) := by
        rw [Nat.cast_sub hc2, Nat.cast_sub hc1, mul_sub, mul_sub,
          twice_choose_two_int T.card, twice_choose_two_int N, twice_choose_two_int (N - T.card)]
        push_cast
        rw [Nat.cast_sub (show 1 ≤ N by omega), Nat.cast_sub hT_le]
        push_cast
        ring
      omega
  rw [hbinom_eq, ← hP_hit_card]
  apply Finset.card_le_card_of_injOn (fun uv : Fin N × Fin N => (uv.1, uv.2, z uv.1, z uv.2))
  · rintro ⟨u₀, v₀⟩ huv
    simp only [P_hit, P_all, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at huv
    rw [Finset.mem_coe, Finset.mem_sdiff]
    refine ⟨?_, ?_⟩
    · simp only [homQueries, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(u₀, v₀), huv.1, rfl⟩
    · intro hmem
      rw [Finset.mem_biUnion] at hmem
      rcases hmem with ⟨y, hy, hqy⟩
      simp only [homQueries, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hqy
      rcases hqy with ⟨⟨u', v'⟩, _, heq⟩
      rcases Prod.mk.inj heq with ⟨rfl, heq2⟩
      rcases Prod.mk.inj heq2 with ⟨rfl, heq3⟩
      rcases Prod.mk.inj heq3 with ⟨hy1, hy2⟩
      rcases huv.2 with huT | hvT
      · exact hT u' huT y hy hy1.symm
      · exact hT v' hvT y hy hy2.symm
  · intro uv₁ _ uv₂ _ heq
    dsimp only at heq
    rcases Prod.mk.inj heq with ⟨h1, heq2⟩
    rcases Prod.mk.inj heq2 with ⟨h2, _⟩
    exact Prod.ext h1 h2
end HighDimSteinerSpanners.Proofs.CSP
