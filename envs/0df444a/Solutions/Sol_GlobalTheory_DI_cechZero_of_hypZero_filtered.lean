-- Prove2me | solution 1 for GlobalTheory.DI.cechZero_of_hypZero_filtered
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:26:33.395855+00:00
-- url     : https://prove2.me/submissions/6c073014-25cd-4d93-af30-69f5c01e9009

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechAndTotalDifferentialAdditiveSquareZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsTotalCochainOfDegreeSuccOfDifferentialsStatement
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_CechVanishingAlongFiltration
import Theorems.Thm_GlobalTheory_DI_FiltVanish_inTot_zero
import Theorems.Thm_GlobalTheory_DI_FiltVanish_inTot_add
import Theorems.Thm_GlobalTheory_DI_FiltVanish_inTot_sub
import Theorems.Thm_GlobalTheory_DI_Dtot_Dtot
import Theorems.Thm_GlobalTheory_DI_Dtot_sub
import Theorems.Thm_GlobalTheory_DI_delta_add
import Theorems.Thm_GlobalTheory_DI_delta_delta
import Theorems.Thm_GlobalTheory_DI_delta_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
namespace GlobalTheory.DI.FiltVanish
variable {ι : Type} {E : Type} [AddCommGroup E]
end GlobalTheory.DI.FiltVanish
private theorem delta_eq_zero_of_card_le_of_vanish_below {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E]
    (c : Finset ι → E) (p : ℕ) (hc : ∀ s : Finset ι, s.card < p → c s = 0)
    (t : Finset ι) (ht : t.card ≤ p) : delta c t = 0 := by
  unfold delta
  refine Finset.sum_eq_zero fun i hi => ?_
  have h1 : (t.erase i).card < p := by
    rw [Finset.card_erase_of_mem hi]
    have := Finset.card_pos.mpr ⟨i, hi⟩
    omega
  rw [hc _ h1, smul_zero]
private theorem inTot_succ_delta_of_inTot {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E]
    (N : ℕ → Finset ι → AddSubgroup E) (hN : ∀ q s t, s.Nonempty → s ⊆ t → N q s ≤ N q t)
    (m : ℕ) (c : Finset ι → E) (hc : InTot N m c) : InTot N (m + 1) (delta c) := by
  obtain ⟨h0, hmem, hbig⟩ := hc
  refine ⟨?_, fun q s hq => ?_, fun s hs => ?_⟩
  · simp [delta]
  · unfold delta
    refine sum_mem fun i hi => ?_
    refine zsmul_mem ?_ _
    have hcard : (s.erase i).card + 1 = s.card := Finset.card_erase_add_one hi
    by_cases he : (s.erase i).Nonempty
    · exact hN q _ _ he (Finset.erase_subset i s) (hmem q _ (by omega))
    · rw [Finset.not_nonempty_iff_eq_empty] at he
      rw [he, h0]
      exact zero_mem _
  · unfold delta
    refine Finset.sum_eq_zero fun i hi => ?_
    have hcard : (s.erase i).card + 1 = s.card := Finset.card_erase_add_one hi
    rw [hbig _ (by omega), smul_zero]
private theorem inTot_succ_Dtot_of_inTot {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E]
    (d : E →+ E) (T : ℕ → Finset ι → AddSubgroup E) (hT : ∀ q s t, s.Nonempty → s ⊆ t → T q s ≤ T q t)
    (hd : ∀ q s x, x ∈ T q s → d x ∈ T (q + 1) s)
    (m : ℕ) (c : Finset ι → E) (hc : InTot T m c) : InTot T (m + 1) (Dtot d c) := by
  have hδ := inTot_succ_delta_of_inTot T hT m c hc
  obtain ⟨h0, hmem, hbig⟩ := hc
  refine ⟨?_, fun q s hq => ?_, fun s hs => ?_⟩
  · simp [Dtot, hδ.1, h0]
  · simp only [Dtot]
    refine add_mem (hδ.2.1 q s hq) (zsmul_mem ?_ _)
    rcases q with _ | q
    · rw [hbig s (by omega), map_zero]
      exact zero_mem _
    · exact hd q s _ (hmem q s (by omega))
  · simp only [Dtot]
    rw [hδ.2.2 s hs, hbig s (by omega), map_zero, smul_zero, add_zero]
end

set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
open GlobalTheory.DI.FiltVanish
namespace GlobalTheory.DI
theorem _root_.solution : ∀ {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] (d : E →+ E) (N T : ℕ → Finset ι → AddSubgroup E) (Ψ : (Finset ι → E) →+ (Finset ι → E)) (γ : Finset ι → E → E), (∀ x, d (d x) = 0) → (∀ q s t, s.Nonempty → s ⊆ t → N q s ≤ N q t) → (∀ q s t, s.Nonempty → s ⊆ t → T q s ≤ T q t) → (∀ q s x, x ∈ T q s → d x ∈ T (q + 1) s) → (∀ m c, InTot N m c → Dtot d (Ψ c) = Ψ (delta c)) → (∀ m c, InTot N m c → InTot T m (Ψ c)) → (∀ s, s.Nonempty → CartierAt d (γ s) (fun a => N a s) (fun a => T a s)) → (∀ m c u, InTot N m c → u.Nonempty → (∀ s, s.card < u.card → c s = 0) → Ψ c u = γ u (c u)) → ∀ a b, HypZero d T (a + b) → CechZero (N a) b := by
  intro ι _ E _ d N T Ψ γ hdd hN hT hd hΨd hΨT hγ hlead a b hH
  have hγ0 : ∀ u : Finset ι, u.Nonempty → γ u 0 = 0 := by
    intro u hu
    have h := hlead 0 0 u (GlobalTheory.DI.FiltVanish.inTot_zero N 0) hu (fun _ _ => rfl)
    rw [map_zero] at h
    simpa using h.symm
  have key : ∀ (n k p : ℕ) (c y : Finset ι → E), p + k = n + 2 → InTot N (n + 1) c → delta c = 0 →
      (∀ s : Finset ι, s.card < p → c s = 0) → InTot T n y → (∀ s : Finset ι, s.card < p → y s = 0) →
      Dtot d y = Ψ c → ∃ y', InTot N n y' ∧ delta y' = c := by
    intro n k
    induction k with
    | zero =>
      intro p c y hpk hc hδc hclow hy hylow hDy
      refine ⟨0, GlobalTheory.DI.FiltVanish.inTot_zero N n, ?_⟩
      funext s
      have h0 : c s = 0 := by
        by_cases hs : s.card < p
        · exact hclow s hs
        · exact hc.2.2 s (by omega)
      rw [h0]
      simp [delta]
    | succ k ih =>
      intro p c y hpk hc hδc hclow hy hylow hDy
      rcases Nat.eq_zero_or_pos p with hp0 | hp0
      · subst hp0
        refine ih 1 c y (by omega) hc hδc ?_ hy ?_ hDy
        · intro s hs
          have he : s = ∅ := Finset.card_eq_zero.mp (by omega)
          rw [he]
          exact hc.1
        · intro s hs
          have he : s = ∅ := Finset.card_eq_zero.mp (by omega)
          rw [he]
          exact hy.1
      have hA : ∀ t : Finset ι, t.card = p → c t = 0 ∧ d (y t) = 0 := by
        intro t ht
        have hne : t.Nonempty := Finset.card_pos.mp (by omega)
        have hlt : ∀ s : Finset ι, s.card < t.card → c s = 0 := fun s hs => hclow s (by omega)
        have hl := hlead (n + 1) c t hc hne hlt
        rw [← hDy] at hl
        simp only [Dtot] at hl
        rw [delta_eq_zero_of_card_le_of_vanish_below y p hylow t (le_of_eq ht), zero_add, ht] at hl
        have hc0 : c t = 0 := by
          by_cases hpn : p = n + 1
          · have hyt : y t = 0 := hy.2.2 t (by omega)
            rw [hyt, map_zero, smul_zero] at hl
            have hmem : c t ∈ N 0 t := hc.2.1 0 t (by omega)
            exact (hγ t hne).inj_zero (c t) hmem hl.symm
          · have hmem : c t ∈ N (n - p + 1) t := hc.2.1 _ t (by omega)
            have hymem : y t ∈ T (n - p) t := hy.2.1 _ t (by omega)
            refine (hγ t hne).inj_succ (n - p) (c t) hmem (((-1 : ℤ) ^ p) • y t) (zsmul_mem hymem _) ?_
            rw [map_zsmul]
            exact hl.symm
        refine ⟨hc0, ?_⟩
        rw [hc0, hγ0 t hne] at hl
        rcases neg_one_pow_eq_or ℤ p with h | h
        · rw [h, one_smul] at hl
          exact hl
        · rw [h, neg_one_smul, neg_eq_zero] at hl
          exact hl
      by_cases hpn1 : p = n + 1
      · refine ⟨0, GlobalTheory.DI.FiltVanish.inTot_zero N n, ?_⟩
        funext s
        have h0 : c s = 0 := by
          rcases lt_trichotomy s.card p with h | h | h
          · exact hclow s h
          · exact (hA s h).1
          · exact hc.2.2 s (by omega)
        rw [h0]
        simp [delta]
      have hpn : p ≤ n := by omega
      have hB : ∀ t : Finset ι, ∃ xz : E × E, t.card = p → (xz.1 ∈ N (n - p) t ∧ xz.2 ∈ T (n - p - 1) t ∧ (n ≤ p → xz.2 = 0) ∧ y t = γ t xz.1 + d xz.2) := by
        intro t
        by_cases ht : t.card = p
        · have hne : t.Nonempty := Finset.card_pos.mp (by omega)
          have hymem : y t ∈ T (n - p) t := hy.2.1 _ t (by omega)
          have hdy := (hA t ht).2
          by_cases h0 : n - p = 0
          · have hymem' : y t ∈ T 0 t := by rw [← h0]; exact hymem
            obtain ⟨x, hx, hxy⟩ := (hγ t hne).surj_zero (y t) hymem' hdy
            refine ⟨(x, 0), fun _ => ⟨by rw [h0]; exact hx, zero_mem _, fun _ => rfl, ?_⟩⟩
            simp [hxy]
          · obtain ⟨q, hq⟩ : ∃ q, n - p = q + 1 := ⟨n - p - 1, by omega⟩
            have hymem' : y t ∈ T (q + 1) t := by rw [← hq]; exact hymem
            obtain ⟨x, hx, z, hz, hxy⟩ := (hγ t hne).surj_succ q (y t) hymem' hdy
            refine ⟨(x, z), fun _ => ⟨by rw [hq]; exact hx, by rw [show n - p - 1 = q by omega]; exact hz, fun _ => by omega, hxy⟩⟩
        · exact ⟨(0, 0), fun h => absurd h ht⟩
      choose xz hxz using hB
      obtain ⟨X, hXp, hXo⟩ : ∃ X : Finset ι → E, (∀ s : Finset ι, s.card = p → X s = (xz s).1) ∧ (∀ s : Finset ι, s.card ≠ p → X s = 0) :=
        ⟨fun s => if s.card = p then (xz s).1 else 0, fun s hs => if_pos hs, fun s hs => if_neg hs⟩
      obtain ⟨Z, hZp, hZo⟩ : ∃ Z : Finset ι → E, (∀ s : Finset ι, s.card = p → Z s = ((-1 : ℤ) ^ p) • (xz s).2) ∧ (∀ s : Finset ι, s.card ≠ p → Z s = 0) :=
        ⟨fun s => if s.card = p then ((-1 : ℤ) ^ p) • (xz s).2 else 0, fun s hs => if_pos hs, fun s hs => if_neg hs⟩
      have hXN : InTot N n X := by
        refine ⟨hXo ∅ (by rw [Finset.card_empty]; omega), fun q s hq => ?_, fun s hs => hXo s (by omega)⟩
        by_cases hs : s.card = p
        · rw [hXp s hs]
          have hqe : q = n - p := by omega
          subst hqe
          exact (hxz s hs).1
        · rw [hXo s hs]
          exact zero_mem _
      have hZT : InTot T (n - 1) Z := by
        refine ⟨hZo ∅ (by rw [Finset.card_empty]; omega), fun q s hq => ?_, fun s hs => ?_⟩
        · by_cases hs : s.card = p
          · rw [hZp s hs]
            have hqe : q = n - p - 1 := by omega
            subst hqe
            exact zsmul_mem (hxz s hs).2.1 _
          · rw [hZo s hs]
            exact zero_mem _
        · by_cases hs' : s.card = p
          · rw [hZp s hs', (hxz s hs').2.2.1 (by omega), smul_zero]
          · exact hZo s hs'
      have hn1 : n - 1 + 1 = n := by omega
      have hDZ : InTot T n (Dtot d Z) := hn1 ▸ inTot_succ_Dtot_of_inTot d T hT hd (n - 1) Z hZT
      have hΨX : InTot T n (Ψ X) := hΨT n X hXN
      have hδX : InTot N (n + 1) (delta X) := inTot_succ_delta_of_inTot N hN n X hXN
      have hΨXs : ∀ s : Finset ι, s.Nonempty → s.card ≤ p → Ψ X s = γ s (X s) :=
        fun s hs hsp => hlead n X s hXN hs (fun s' hs' => hXo s' (by omega))
      have hDZs : ∀ s : Finset ι, s.card ≤ p → Dtot d Z s = ((-1 : ℤ) ^ s.card) • d (Z s) := by
        intro s hs
        simp only [Dtot]
        rw [delta_eq_zero_of_card_le_of_vanish_below Z p (fun s' hs' => hZo s' (by omega)) s hs, zero_add]
      have hsq : ((-1 : ℤ) ^ p) * (-1 : ℤ) ^ p = 1 := by
        rw [← mul_pow]
        norm_num
      have hδc' : delta (c - delta X) = 0 := by
        rw [delta_sub, hδc, delta_delta, sub_zero]
      have hclow' : ∀ s : Finset ι, s.card < p + 1 → (c - delta X) s = 0 := by
        intro s hs
        rw [Pi.sub_apply, delta_eq_zero_of_card_le_of_vanish_below X p (fun s' hs' => hXo s' (by omega)) s (by omega), sub_zero]
        rcases Nat.lt_or_ge s.card p with h | h
        · exact hclow s h
        · exact (hA s (by omega)).1
      have hylow' : ∀ s : Finset ι, s.card < p + 1 → (y - Ψ X - Dtot d Z) s = 0 := by
        intro s hs
        simp only [Pi.sub_apply]
        rw [hDZs s (by omega)]
        rcases Nat.lt_or_ge s.card p with h | h
        · rw [hylow s h, hZo s (by omega), map_zero, smul_zero, sub_zero, zero_sub, neg_eq_zero]
          by_cases hne : s.Nonempty
          · rw [hΨXs s hne (by omega), hXo s (by omega), hγ0 s hne]
          · rw [Finset.not_nonempty_iff_eq_empty] at hne
            subst hne
            exact hΨX.1
        · have hsp : s.card = p := by omega
          have hne : s.Nonempty := Finset.card_pos.mp (by omega)
          rw [hΨXs s hne (by omega), hXp s hsp, hZp s hsp, hsp, map_zsmul, smul_smul, hsq, one_smul,
            (hxz s hsp).2.2.2]
          abel
      have hDy' : Dtot d (y - Ψ X - Dtot d Z) = Ψ (c - delta X) := by
        rw [Dtot_sub, Dtot_sub, Dtot_Dtot d hdd, hDy, hΨd n X hXN, map_sub, sub_zero]
      obtain ⟨y'', hy''N, hy''δ⟩ := ih (p + 1) (c - delta X) (y - Ψ X - Dtot d Z) (by omega)
        (GlobalTheory.DI.FiltVanish.inTot_sub hc hδX) hδc' hclow'
        (GlobalTheory.DI.FiltVanish.inTot_sub (GlobalTheory.DI.FiltVanish.inTot_sub hy hΨX) hDZ) hylow' hDy'
      exact ⟨y'' + X, GlobalTheory.DI.FiltVanish.inTot_add hy''N hXN, by rw [delta_add, hy''δ, sub_add_cancel]⟩
  intro c hc hδc
  have hcN : InTot N (a + b + 1) c := by
    refine ⟨hc.1, fun q s hq => ?_, fun s hs => hc.2.2 s (by omega)⟩
    by_cases hs : s.card = b + 1
    · have hqa : q = a := by omega
      subst hqa
      exact hc.2.1 s
    · rw [hc.2.2 s hs]
      exact zero_mem _
  have hΨc := hΨT _ c hcN
  have hDΨ : Dtot d (Ψ c) = 0 := by rw [hΨd _ c hcN, hδc, map_zero]
  obtain ⟨y, hy, hDy⟩ := hH (Ψ c) hΨc hDΨ
  obtain ⟨y', hy'N, hy'δ⟩ := key (a + b) (a + b + 2) 0 c y (by omega) hcN hδc
    (fun s hs => absurd hs (Nat.not_lt_zero _)) hy (fun s hs => absurd hs (Nat.not_lt_zero _)) hDy
  refine ⟨fun s => if s.card = b then y' s else 0, ⟨?_, fun s => ?_, fun s hs => if_neg hs⟩, ?_⟩
  · by_cases hb : b = 0
    · simp [hb, hy'N.1]
    · simp [hb, Ne.symm hb]
  · dsimp only
    split_ifs with hs
    · exact hy'N.2.1 a s (by omega)
    · exact zero_mem _
  · funext t
    by_cases ht : t.card = b + 1
    · rw [← hy'δ]
      simp only [delta]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hcard : (t.erase i).card = b := by
        rw [Finset.card_erase_of_mem hi]
        omega
      rw [if_pos hcard]
    · rw [hc.2.2 t ht]
      simp only [delta]
      refine Finset.sum_eq_zero fun i hi => ?_
      have hcard : (t.erase i).card ≠ b := by
        rw [Finset.card_erase_of_mem hi]
        have := Finset.card_pos.mpr ⟨i, hi⟩
        omega
      rw [if_neg hcard, smul_zero]
end GlobalTheory.DI
