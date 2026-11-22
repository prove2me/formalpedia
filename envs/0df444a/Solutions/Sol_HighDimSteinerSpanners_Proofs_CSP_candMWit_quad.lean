-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.CSP.candMWit_quad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:49:24.708893+00:00
-- url     : https://prove2.me/submissions/9707196e-f5f5-494e-94da-6d121516e287

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_CalibrationBounds
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_WitnessCardinality
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_candMFresh_subset_union

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section
namespace HighDimSteinerSpanners.Proofs.CSP
theorem _root_.solution {N q : ℕ} (C₁ r_star m : ℕ)
    (a b : Fin N → Fin q) (z_prev : Fin m → (Fin N → Fin q)) (x : Fin N → Fin q) :
    let M := candMFresh a b m z_prev x
    ∀ w ∈ candMWit C₁ r_star a b m z_prev x,
      (∀ uv ∈ candA2 C₁ a b x M w, uv.1 ≠ uv.2) ∧
      40 * ((M.card : ℤ) ^ 2 - 2 * ((candA2 C₁ a b x M w).card : ℤ)) ≤
        23 * (r_star : ℤ) * (M.card : ℤ) := by
  intro M
  let K_max := cspKMax C₁
  let W_ab := disagreeSet x a ∪ disagreeSet x b
  have hM_sub_W : M ⊆ W_ab := candMFresh_subset_union a b m z_prev x
  intro w hw
  have hw_filt := (Finset.mem_filter.mp hw).2
  let k := w.1
  let τ := w.2.1
  let B_fut := w.2.2.1
  let U_out := w.2.2.2
  rcases hw_filt with ⟨hτ_le, htail_le, hr_props⟩
  let M_piece := fun r : Fin K_max => M.filter (fun u => τ u = r.succ)
  let I_tilde := fun r : Fin K_max => M.filter (fun u => τ u = 0 ∨ r.1 + 1 < (τ u).1)
  let B_out := fun r : Fin K_max => W_ab.filter (fun v => (r, v) ∈ U_out)
  refine ⟨?_, ?_⟩
  · rintro ⟨u, v⟩ huv
    simp only [candA2, Finset.mem_filter, Finset.mem_product] at huv
    rcases huv with ⟨⟨huM, hvW⟩, r, hrk, hτu, hvB⟩
    obtain ⟨hBf_sub, _, hBo_disj, _⟩ := hr_props r hrk
    dsimp only
    intro heq
    subst heq
    rcases hvB with hvf | hvo
    · have huI := (Finset.mem_filter.mp (hBf_sub hvf)).2
      rw [hτu] at huI
      rcases huI with h0 | hlt
      · exact Fin.succ_ne_zero r h0
      · simp at hlt
    · have huBo : u ∈ B_out r := Finset.mem_filter.mpr ⟨hvW, hvo⟩
      have huMr : u ∈ M_piece r := Finset.mem_filter.mpr ⟨huM, hτu⟩
      exact Finset.disjoint_left.mp hBo_disj huBo (Finset.mem_union_left _ huMr)
  · -- Exact card of candA2
    let R_lt := (Finset.univ : Finset (Fin K_max)).filter (fun r => r.1 < k.1)
    have hA2_eq : candA2 C₁ a b x M w =
        R_lt.biUnion (fun r => M_piece r ×ˢ (B_fut r ∪ B_out r)) := by
      ext ⟨u, v⟩
      simp only [candA2, R_lt, M_piece, B_out, Finset.mem_filter, Finset.mem_product,
        Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨huM, hvW⟩, r, hrk, hτu, hvf | hvo⟩
        · exact ⟨r, hrk, ⟨huM, hτu⟩, Finset.mem_union_left _ hvf⟩
        · exact ⟨r, hrk, ⟨huM, hτu⟩, Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hvW, hvo⟩)⟩
      · rintro ⟨r, hrk, ⟨huM, hτu⟩, hv⟩
        rcases Finset.mem_union.mp hv with hvf | hvo
        · have hvfM : v ∈ M := (Finset.mem_filter.mp ((hr_props r hrk).1 hvf)).1
          exact ⟨⟨huM, hM_sub_W hvfM⟩, r, hrk, hτu, Or.inl hvf⟩
        · rcases Finset.mem_filter.mp hvo with ⟨hvW, hvoU⟩
          exact ⟨⟨huM, hvW⟩, r, hrk, hτu, Or.inr hvoU⟩
    have hA2_disj : (R_lt : Set (Fin K_max)).PairwiseDisjoint
        (fun r => M_piece r ×ˢ (B_fut r ∪ B_out r)) := by
      intro r₁ _ r₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      rintro ⟨u, v⟩ h₁ h₂
      simp only [M_piece, Finset.mem_product, Finset.mem_filter] at h₁ h₂
      exact hne (Fin.succ_injective _ (h₁.1.2.symm.trans h₂.1.2))
    have hA2_card : (candA2 C₁ a b x M w).card =
        ∑ r ∈ R_lt, (M_piece r).card * ((B_fut r).card + (B_out r).card) := by
      rw [hA2_eq, Finset.card_biUnion hA2_disj]
      refine Finset.sum_congr rfl (fun r hr => ?_)
      have hrk : r.1 < k.1 := (Finset.mem_filter.mp hr).2
      obtain ⟨hBf_sub, _, hBo_disj, _⟩ := hr_props r hrk
      have hdisj_f_o : Disjoint (B_fut r) (B_out r) := by
        rw [Finset.disjoint_left]
        intro z hzf hzo
        exact Finset.disjoint_left.mp hBo_disj hzo (Finset.mem_union_right _ (hBf_sub hzf))
      rw [Finset.card_product, Finset.card_union_of_disjoint hdisj_f_o]
    -- Backward induction on suffix j = k.1 - d
    let Suf := fun j : ℕ => M.filter (fun u => τ u = 0 ∨ j < (τ u).1)
    let A2_suf := fun j : ℕ =>
      ∑ r ∈ R_lt.filter (fun r => j ≤ r.1),
        (M_piece r).card * ((B_fut r).card + (B_out r).card)
    have h_ind : ∀ d : ℕ, d ≤ k.1 →
        40 * (((Suf (k.1 - d)).card : ℤ) ^ 2 - 2 * (A2_suf (k.1 - d) : ℤ)) ≤
          23 * (r_star : ℤ) * ((Suf (k.1 - d)).card : ℤ) := by
      intro d
      induction d with
      | zero =>
        intro _
        simp only [Nat.sub_zero]
        have hSuf_k : Suf k.1 = M.filter (fun u => τ u = 0) := by
          ext u
          simp only [Suf, Finset.mem_filter]
          constructor
          · rintro ⟨huM, h0 | hgt⟩
            · exact ⟨huM, h0⟩
            · exact absurd (hτ_le u huM) (not_le_of_gt hgt)
          · rintro ⟨huM, h0⟩
            exact ⟨huM, Or.inl h0⟩
        have hA2_k : A2_suf k.1 = 0 := by
          apply Finset.sum_eq_zero
          intro r hr
          simp only [R_lt, Finset.mem_filter, Finset.mem_univ, true_and] at hr
          omega
        rw [hSuf_k, hA2_k]
        have ht_int : 2 * (((M.filter (fun u => τ u = 0)).card : ℤ)) ≤ (r_star : ℤ) := by
          exact_mod_cast htail_le
        have ht_nn : (0 : ℤ) ≤ ((M.filter (fun u => τ u = 0)).card : ℤ) := Nat.cast_nonneg _
        nlinarith
      | succ d ih =>
        intro hd1
        let j := k.1 - (d + 1)
        have hjk : j < k.1 := by omega
        have hkd_eq : k.1 - d = j + 1 := by omega
        have hih := ih (by omega)
        rw [hkd_eq] at hih
        have hjK : j < K_max := lt_of_lt_of_le hjk (Nat.le_of_lt_succ k.2)
        let r0 : Fin K_max := ⟨j, hjK⟩
        have hr0_val : r0.1 = j := rfl
        have hr0_lt : r0.1 < k.1 := hjk
        obtain ⟨hBf_sub, hmiss_le, _, hBo_card⟩ := hr_props r0 hr0_lt
        have hSuf_split : Suf j = M_piece r0 ∪ Suf (j + 1) := by
          ext u
          simp only [Suf, M_piece, Finset.mem_union, Finset.mem_filter, Fin.ext_iff,
            Fin.val_succ, Fin.val_zero]
          rw [hr0_val]
          by_cases hu : u ∈ M
          · simp only [hu, true_and]
            omega
          · simp [hu]
        have hSuf_disj : Disjoint (M_piece r0) (Suf (j + 1)) := by
          rw [Finset.disjoint_left]
          intro u hu1 hu2
          simp only [M_piece, Suf, Finset.mem_filter, Fin.ext_iff,
            Fin.val_succ, Fin.val_zero] at hu1 hu2
          rw [hr0_val] at hu1
          omega
        have hSuf_card : (Suf j).card = (M_piece r0).card + (Suf (j + 1)).card := by
          rw [hSuf_split, Finset.card_union_of_disjoint hSuf_disj]
        have hA2_split : A2_suf j =
            (M_piece r0).card * ((B_fut r0).card + (B_out r0).card) + A2_suf (j + 1) := by
          have hset : R_lt.filter (fun r => j ≤ r.1) =
              insert r0 (R_lt.filter (fun r => j + 1 ≤ r.1)) := by
            ext r
            simp only [R_lt, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ,
              true_and, Fin.ext_iff]
            rw [hr0_val]
            omega
          have hnot : r0 ∉ R_lt.filter (fun r => j + 1 ≤ r.1) := by
            simp [r0]
          dsimp [A2_suf]
          rw [hset, Finset.sum_insert hnot]
        have hIt_eq : I_tilde r0 = Suf (j + 1) := rfl
        have hsdiff_card : (Suf (j + 1)).card =
            (I_tilde r0 \ B_fut r0).card + (B_fut r0).card := by
          rw [← hIt_eq, Finset.card_sdiff_add_card_eq_card hBf_sub]
        have hBo_card' : (B_out r0).card = (M_piece r0).card - (11 * r_star) / 40 := hBo_card
        have hBo_ineq : 40 * (M_piece r0).card ≤ 40 * (B_out r0).card + 11 * r_star := by
          rw [hBo_card']
          omega
        -- Finish step in ℤ
        set a_c : ℤ := ((M_piece r0).card : ℤ)
        set b_c : ℤ := ((Suf (j + 1)).card : ℤ)
        set f_c : ℤ := ((B_fut r0).card : ℤ)
        set m_c : ℤ := ((I_tilde r0 \ B_fut r0).card : ℤ)
        set o_c : ℤ := ((B_out r0).card : ℤ)
        have ha_nn : 0 ≤ a_c := Nat.cast_nonneg _
        have hbmf : b_c = m_c + f_c := by
          dsimp only [b_c, m_c, f_c]
          exact_mod_cast hsdiff_card
        have hmiss_le' : 80 * (I_tilde r0 \ B_fut r0).card ≤ r_star := hmiss_le
        have hm80 : 80 * m_c ≤ (r_star : ℤ) := by
          dsimp only [m_c]
          exact_mod_cast hmiss_le'
        have ho40 : 40 * a_c ≤ 40 * o_c + 11 * (r_star : ℤ) := by
          have hc : ((40 * (M_piece r0).card : ℕ) : ℤ) ≤
              ((40 * (B_out r0).card + 11 * r_star : ℕ) : ℤ) := by exact_mod_cast hBo_ineq
          push_cast at hc
          exact hc
        change 40 * (((Suf j).card : ℤ) ^ 2 - 2 * (A2_suf j : ℤ)) ≤
          23 * (r_star : ℤ) * ((Suf j).card : ℤ)
        rw [hSuf_card, hA2_split]
        push_cast
        change 40 * ((a_c + b_c) ^ 2 - 2 * (a_c * (f_c + o_c) + (A2_suf (j + 1) : ℤ))) ≤
          23 * (r_star : ℤ) * (a_c + b_c)
        have hterm_miss : 80 * a_c * (b_c - f_c) ≤ (r_star : ℤ) * a_c := by
          have hbf : b_c - f_c = m_c := by linarith only [hbmf]
          rw [hbf]
          nlinarith only [mul_le_mul_of_nonneg_right hm80 ha_nn]
        have hterm_out : 40 * (a_c ^ 2 - 2 * a_c * o_c) ≤ 22 * (r_star : ℤ) * a_c := by
          have hsq_nn : 0 ≤ 40 * a_c ^ 2 := by positivity
          nlinarith only [mul_le_mul_of_nonneg_right ho40 ha_nn, hsq_nn]
        change 40 * (b_c ^ 2 - 2 * (A2_suf (j + 1) : ℤ)) ≤ 23 * (r_star : ℤ) * b_c at hih
        nlinarith only [hih, hterm_miss, hterm_out]
    have h0 := h_ind k.1 (le_refl k.1)
    simp only [Nat.sub_self] at h0
    have hSuf0 : Suf 0 = M := by
      ext u
      simp only [Suf, Finset.mem_filter, Fin.ext_iff, Fin.val_zero]
      constructor
      · exact fun h => h.1
      · intro hu; exact ⟨hu, by omega⟩
    have hA2_0 : A2_suf 0 = (candA2 C₁ a b x M w).card := by
      rw [hA2_card]
      dsimp [A2_suf]
      congr 1
      ext r
      simp
    rwa [hSuf0, hA2_0] at h0
end HighDimSteinerSpanners.Proofs.CSP
