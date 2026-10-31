-- Prove2me | solution 1 for IncrKnapsack.PTAS.claim_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T03:11:47.941979+00:00
-- url     : https://prove2.me/submissions/fdac93ed-83f9-40a1-8812-fd8b5f842fd6

import Mathlib
import Definitions.Def_IncrKnapsack_PTAS_Model
import Theorems.Thm_IncrKnapsack_PTAS_representation_1

open Classical
open Finset BigOperators
open IncrKnapsack.PTAS

/-- weight of a subroutine answer, `0` for `none` -/
noncomputable def ikp2_wt {I : Instance} : Option (Sol I) → ℝ
  | some S => weight I S
  | none => 0

theorem ikp2_Ftil_zero (I : Instance) (K ξ : ℕ) (Φ : Finset ℝ) (A : Subroutine I) (m : ℕ)
    (ϕ : ℝ) : Ftil I K ξ Φ A m 0 ϕ = if ϕ = 0 then 0 else ⊤ := by
  cases m <;> simp [Ftil]

theorem ikp2_Ftil_m0 (I : Instance) (K ξ : ℕ) (Φ : Finset ℝ) (A : Subroutine I) (j : ℕ)
    (ϕ : ℝ) : Ftil I K ξ Φ A 0 j ϕ = if ϕ = 0 then 0 else ⊤ := by
  simp [Ftil]

theorem ikp2_ite_fin {x : ℝ} (h : (if x = 0 then (0 : WithTop ℝ) else ⊤) < ⊤) :
    (if x = 0 then (0 : WithTop ℝ) else ⊤) = 0 := by
  split_ifs at h ⊢ with hx
  · rfl
  · exact absurd h (lt_irrefl _)

theorem ikp2_weight_nonneg (I : Instance) (hI : I.Standing) (S : Sol I) : 0 ≤ weight I S := by
  unfold weight; exact Finset.sum_nonneg (fun i _ => (hI.w_pos i).le)

theorem ikp2_wt_nonneg (I : Instance) (hI : I.Standing) (o : Option (Sol I)) :
    0 ≤ ikp2_wt o := by
  cases o with
  | none => simp [ikp2_wt]
  | some S => exact ikp2_weight_nonneg I hI S

/-- Telescoping along the traceback. -/
theorem ikp2_telescope (I : Instance) (hI : I.Standing) (K ξ : ℕ)
    (Φ : Finset ℝ) (A : Subroutine I) (jt : ℕ → ℕ) (ϕt : ℕ → ℝ)
    (htr : IsTraceback I K ξ Φ A jt ϕt) :
    ∀ m, m ≤ Mcl I K ξ → Ftil I K ξ Φ A m (jt m) (ϕt m) =
      ((∑ m' ∈ Finset.Icc 1 m, ikp2_wt (outs I K ξ Φ A jt ϕt m') : ℝ) : WithTop ℝ) := by
  obtain ⟨hjM, _, hfinM, _, hstep⟩ := htr
  -- finiteness, downward
  have hfin : ∀ k, k ≤ Mcl I K ξ →
      Ftil I K ξ Φ A (Mcl I K ξ - k) (jt (Mcl I K ξ - k)) (ϕt (Mcl I K ξ - k)) < ⊤ := by
    intro k
    induction k with
    | zero => intro _; simpa [hjM] using hfinM
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      have e : Mcl I K ξ - k = (Mcl I K ξ - (k + 1)) + 1 := by omega
      rw [e] at ih'
      obtain ⟨h0, h1⟩ := hstep (Mcl I K ξ - (k + 1) + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at h0 h1
      by_cases hj : jt (Mcl I K ξ - (k + 1) + 1) = 0
      · obtain ⟨hj0, hp0⟩ := h0 hj
        rw [hj0, hp0, ikp2_Ftil_zero]; simp
      · obtain ⟨_, _, _, heq⟩ := h1 hj
        rw [heq] at ih'
        exact (WithTop.add_lt_top.1 ih').1
  have hfin' : ∀ m, m ≤ Mcl I K ξ → Ftil I K ξ Φ A m (jt m) (ϕt m) < ⊤ := by
    intro m hm
    have := hfin (Mcl I K ξ - m) (by omega)
    rwa [show Mcl I K ξ - (Mcl I K ξ - m) = m by omega] at this
  intro m
  induction m with
  | zero =>
    intro h0
    have := hfin' 0 h0
    rw [ikp2_Ftil_m0] at this ⊢
    rw [ikp2_ite_fin this]; simp
  | succ m ih =>
    intro hm
    rw [Finset.sum_Icc_succ_top (by omega), WithTop.coe_add, ← ih (by omega)]
    obtain ⟨h0, h1⟩ := hstep (m + 1) (by omega) hm
    simp only [Nat.add_sub_cancel] at h0 h1
    by_cases hj : jt (m + 1) = 0
    · obtain ⟨hj0, hp0⟩ := h0 hj
      have hf := hfin' (m + 1) hm
      rw [hj, ikp2_Ftil_zero] at hf ⊢
      rw [ikp2_ite_fin hf, hj0, hp0, ikp2_Ftil_zero]
      have : outs I K ξ Φ A jt ϕt (m + 1) = none := by simp [outs, hj]
      rw [this]; simp [ikp2_wt]
    · obtain ⟨_, _, _, heq⟩ := h1 hj
      have hf := hfin' (m + 1) hm
      rw [heq] at hf ⊢
      have ho : outs I K ξ Φ A jt ϕt (m + 1) =
          A (m + 1) (jt m) (jt (m + 1) - 1) (phiReq I K ξ (ϕt (m + 1)) (ϕt m))
            (omegaOf I K ξ Φ A m (jt m) (ϕt m)) := by simp [outs, hj]
      rw [← ho] at hf ⊢
      congr 1
      have hw := (WithTop.add_lt_top.1 hf).2
      cases hS : outs I K ξ Φ A jt ϕt (m + 1) with
      | none => rw [hS] at hw; simp [wOpt] at hw
      | some S => simp [wOpt, ikp2_wt]

theorem ikp2_item (I : Instance) (K ξ : ℕ)
    (Φ : Finset ℝ) (A : Subroutine I) (jt : ℕ → ℕ) (ϕt : ℕ → ℝ) (i : Fin I.n) (s : Fin I.T)
    (h : algOut I K ξ Φ A jt ϕt i = some s) :
    ∃ S, outs I K ξ Φ A jt ϕt (clus I K ξ s) = some S ∧ S i = some s ∧ IsGood I K ξ s ∧
      1 ≤ clus I K ξ s ∧ clus I K ξ s ≤ Mcl I K ξ := by
  unfold algOut at h
  obtain ⟨m, hm, hi⟩ := List.exists_of_findSome?_eq_some h
  rw [List.mem_range'] at hm
  unfold introAt at hi
  cases hS : outs I K ξ Φ A jt ϕt m with
  | none => rw [hS] at hi; simp at hi
  | some S =>
    rw [hS] at hi
    simp only [Option.filter_eq_some_iff, decide_eq_true_eq] at hi
    obtain ⟨hSi, hg, hc⟩ := hi
    refine ⟨S, by rw [hc]; exact hS, hSi, hg, ?_, ?_⟩
    · obtain ⟨k, hk, rfl⟩ := hm; omega
    · obtain ⟨k, hk, rfl⟩ := hm; omega

noncomputable def ikp2_psiO {I : Instance} (K : ℕ) : Option (Sol I) → Fin I.n → ℝ
  | some S, i => psiItem I (pr I K) S i
  | none, _ => 0

theorem solution (I : Instance) (hI : I.Standing) (K : ℕ) (hK : 4 < K) (ξ : ℕ) (hξ : ξ < K)
    (Φ : Finset ℝ) (A : Subroutine I) (jt : ℕ → ℕ) (ϕt : ℕ → ℝ)
    (hΦ : IsProfitGrid I K ξ Φ) (hA : IsSubroutine I K ξ A) (htr : IsTraceback I K ξ Φ A jt ϕt) :
    (1 - 2 * eps K) * ϕt (Mcl I K ξ) - (Mcl I K ξ : ℝ) * delta I K ξ ≤
      Psi I (pr I K) (algOut I K ξ Φ A jt ϕt) := by
  set So := algOut I K ξ Φ A jt ϕt with hSo
  set out := outs I K ξ Φ A jt ϕt with hout
  set M := Mcl I K ξ with hM
  set g : ℕ → ℝ := fun m => ∑ m' ∈ Finset.Icc 1 m, ikp2_wt (out m') with hg
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have he0 : 0 ≤ eps K := by unfold eps; positivity
  have he1 : eps K ≤ 1 := by
    unfold eps; rw [div_le_one hKpos]; exact_mod_cast (by omega : 1 ≤ K)
  have hpr : ∀ i, 0 ≤ pr I K i := fun i => by unfold pr; positivity
  have hlam : ∀ t, 0 ≤ lamPlus I t := by
    intro t; unfold lamPlus; exact Finset.sum_nonneg (fun τ _ => hI.lam_nonneg τ)
  have hitem : ∀ S : Sol I, ∀ i, 0 ≤ psiItem I (pr I K) S i := by
    intro S i; unfold psiItem
    split
    · exact mul_nonneg (hpr i) (hlam _)
    · exact le_refl _
  have hδ0 : 0 ≤ delta I K ξ := by
    unfold delta
    have : 0 ≤ lamLast I := hI.lam_last_pos.le
    have : 0 ≤ pmax I K := by
      unfold pmax; split_ifs with hne
      · obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' hne (pr I K); rw [hi]; exact hpr i
      · exact le_refl _
    positivity
  have htel := ikp2_telescope I hI K ξ Φ A jt ϕt htr
  have hg_nonneg : ∀ m, 0 ≤ g m := fun m =>
    Finset.sum_nonneg (fun m' _ => ikp2_wt_nonneg I hI (out m'))
  have homega : ∀ m, m ≤ M → omegaOf I K ξ Φ A m (jt m) (ϕt m) = g m := by
    intro m hm; unfold omegaOf; rw [htel m hm]; rfl
  have hfinite : ∀ m, m ≤ M → Ftil I K ξ Φ A m (jt m) (ϕt m) < ⊤ := by
    intro m hm; rw [htel m hm]; exact WithTop.coe_lt_top _
  obtain ⟨hjM, hϕM, _, _, hstep⟩ := htr
  -- ϕt at terminal states and at 0
  have hϕ0 : ϕt 0 = 0 := by
    have := hfinite 0 (Nat.zero_le _)
    rw [ikp2_Ftil_m0] at this
    by_contra h; rw [if_neg h] at this; exact lt_irrefl _ this
  have hϕzero : ∀ m, m ≤ M → jt m = 0 → ϕt m = 0 := by
    intro m hm hj
    have := hfinite m hm
    rw [hj, ikp2_Ftil_zero] at this
    by_contra h; rw [if_neg h] at this; exact lt_irrefl _ this
  -- monotonicity of ϕt and jt
  have hϕmono : ∀ m, 1 ≤ m → m ≤ M → ϕt (m - 1) ≤ ϕt m := by
    intro m h1 h2
    obtain ⟨h0, h1'⟩ := hstep m h1 h2
    by_cases hj : jt m = 0
    · rw [(h0 hj).2, hϕzero m h2 hj]
    · exact (h1' hj).2.2.1
  have hjmono : ∀ m, 1 ≤ m → m ≤ M → jt (m - 1) ≤ jt m := by
    intro m h1 h2
    obtain ⟨h0, h1'⟩ := hstep m h1 h2
    by_cases hj : jt m = 0
    · rw [(h0 hj).1, hj]
    · exact (h1' hj).1
  have hϕnn : ∀ m, m ≤ M → 0 ≤ ϕt m := by
    intro m hm
    rcases Nat.lt_or_ge m M with h | h
    · obtain ⟨h0, h1'⟩ := hstep (m + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at h0 h1'
      by_cases hj : jt (m + 1) = 0
      · rw [(h0 hj).2]
      · exact hΦ.2.1 _ (h1' hj).2.1
    · rw [show m = M by omega]; exact hΦ.2.1 _ hϕM
  have hjmono' : ∀ a b, a ≤ b → b ≤ M → jt a ≤ jt b := by
    intro a b hab hb
    induction b with
    | zero => rw [show a = 0 by omega]
    | succ b ih =>
      rcases Nat.eq_or_lt_of_le hab with h | h
      · rw [h]
      · have := hjmono (b + 1) (by omega) hb
        simp only [Nat.add_sub_cancel] at this
        exact le_trans (ih (by omega) (by omega)) this
  -- the outputs and their guarantee
  have hout_spec : ∀ m S, 1 ≤ m → m ≤ M → out m = some S →
      jt m ≠ 0 ∧ SingleAdm I K ξ m (jt (m - 1)) (jt m - 1) (g (m - 1)) S ∧
      (1 - eps K) * phiReq I K ξ (ϕt m) (ϕt (m - 1)) ≤ contrib I (pr I K) S := by
    intro m S h1 h2 hS
    have hj : jt m ≠ 0 := by intro hj; simp [hout, outs, hj] at hS
    have hSA : A m (jt (m - 1)) (jt m - 1) (phiReq I K ξ (ϕt m) (ϕt (m - 1))) (g (m - 1))
        = some S := by
      rw [← homega (m - 1) (by omega)]; simpa [hout, outs, hj] using hS
    have hphi : 0 ≤ phiReq I K ξ (ϕt m) (ϕt (m - 1)) := by unfold phiReq; exact le_max_right _ _
    obtain ⟨hadm, hprof, _⟩ := (hA m (jt (m - 1)) (jt m - 1) _ (g (m - 1)) hphi
      (hg_nonneg _)).1 S hSA
    exact ⟨hj, hadm, hprof⟩
  -- per-cluster profit bound
  have hc : ∀ m, 1 ≤ m → m ≤ M →
      (1 - eps K) * (ϕt m - (1 + eps K / (M : ℝ)) * ϕt (m - 1) - delta I K ξ) ≤
        ∑ i, ikp2_psiO K (out m) i := by
    intro m h1 h2
    by_cases hj : jt m = 0
    · have h0 := (hstep m h1 h2).1 hj
      rw [hϕzero m h2 hj, h0.2]
      have : out m = none := by simp [hout, outs, hj]
      rw [this]; simp only [ikp2_psiO, Finset.sum_const_zero]
      nlinarith
    · have hf := hfinite m h2
      rw [((hstep m h1 h2).2 hj).2.2.2] at hf
      have hw := (WithTop.add_lt_top.1 hf).2
      have ho : outs I K ξ Φ A jt ϕt m =
          A m (jt (m - 1)) (jt m - 1) (phiReq I K ξ (ϕt m) (ϕt (m - 1)))
            (omegaOf I K ξ Φ A (m - 1) (jt (m - 1)) (ϕt (m - 1))) := by simp [outs, hj]
      rw [← ho] at hw
      cases hS : out m with
      | none => rw [hout] at hS; rw [hS] at hw; simp [wOpt] at hw
      | some S =>
        obtain ⟨_, _, hprof⟩ := hout_spec m S h1 h2 hS
        have : ∑ i, ikp2_psiO K (some S) i = contrib I (pr I K) S := rfl
        rw [this]
        refine le_trans ?_ hprof
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        unfold phiReq; exact le_max_left _ _
  -- uniqueness of the cluster owning an item
  have huniq : ∀ m1 m2 S1 S2 i s1 s2, 1 ≤ m1 → m1 ≤ M → 1 ≤ m2 → m2 ≤ M →
      out m1 = some S1 → out m2 = some S2 → S1 i = some s1 → S2 i = some s2 → m1 = m2 := by
    have aux : ∀ m1 m2 S1 S2 i s1 s2, 1 ≤ m1 → m1 ≤ M → 1 ≤ m2 → m2 ≤ M →
        out m1 = some S1 → out m2 = some S2 → S1 i = some s1 → S2 i = some s2 → ¬ m1 < m2 := by
      intro m1 m2 S1 S2 i s1 s2 a1 a2 b1 b2 h1 h2 e1 e2 hlt
      obtain ⟨hj1, ⟨ad1, _⟩, _⟩ := hout_spec m1 S1 a1 a2 h1
      obtain ⟨_, ⟨ad2, _⟩, _⟩ := hout_spec m2 S2 b1 b2 h2
      have c1 := (ad1 i s1 e1).2.2.2
      have c2 := (ad2 i s2 e2).2.2.1
      have := hjmono' m1 (m2 - 1) (by omega) (by omega)
      omega
    intro m1 m2 S1 S2 i s1 s2 a1 a2 b1 b2 h1 h2 e1 e2
    rcases lt_trichotomy m1 m2 with h | h | h
    · exact absurd h (aux m1 m2 S1 S2 i s1 s2 a1 a2 b1 b2 h1 h2 e1 e2)
    · exact h
    · exact absurd h (aux m2 m1 S2 S1 i s2 s1 b1 b2 a1 a2 h2 h1 e2 e1)
  -- each item's contributions over clusters are dominated by its contribution in S̄
  have hitemS : ∀ i, ∑ m ∈ Finset.Icc 1 M, ikp2_psiO K (out m) i ≤ psiItem I (pr I K) So i := by
    intro i
    by_cases hex : ∃ m ∈ Finset.Icc 1 M, ∃ S s, out m = some S ∧ S i = some s
    · obtain ⟨m, hm, S, s, hS, hSi⟩ := hex
      rw [Finset.mem_Icc] at hm
      rw [Finset.sum_eq_single m]
      · -- S̄ i = some s
        have hintro : introAt I K ξ Φ A jt ϕt m i = some s := by
          obtain ⟨_, ⟨ad, _⟩, _⟩ := hout_spec m S hm.1 hm.2 hS
          obtain ⟨hgs, hcs, _⟩ := ad i s hSi
          unfold introAt; rw [← hout, hS]
          simp [hSi, hgs, hcs]
        have hSo : So i = some s := by
          have hmem : m ∈ List.range' 1 M := by rw [List.mem_range']; exact ⟨m - 1, by omega, by omega⟩
          have hsome : (So i).isSome := by
            rw [hSo, algOut, List.findSome?_isSome_iff]
            exact ⟨m, hmem, by rw [hintro]; rfl⟩
          obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hsome
          rw [hb]
          rw [hSo, algOut] at hb
          obtain ⟨m', hm', hb'⟩ := List.exists_of_findSome?_eq_some hb
          rw [List.mem_range'] at hm'
          obtain ⟨k, hk, rfl⟩ := hm'
          unfold introAt at hb'
          cases hS' : outs I K ξ Φ A jt ϕt (1 + 1 * k) with
          | none => rw [hS'] at hb'; simp at hb'
          | some S' =>
            rw [hS'] at hb'
            simp only [Option.filter_eq_some_iff] at hb'
            have := huniq m (1 + 1 * k) S S' i s b hm.1 hm.2 (by omega) (by omega) hS
              (by rw [hout]; exact hS') hSi hb'.1
            subst this
            rw [hout] at hS; rw [hS] at hS'; cases hS'
            rw [hSi] at hb'; rw [(Option.some_inj.1 hb'.1)]
        simp only [ikp2_psiO, hS]
        unfold psiItem; rw [hSi, hSo]
      · intro m' hm' hne
        rw [Finset.mem_Icc] at hm'
        cases hS' : out m' with
        | none => rfl
        | some S' =>
          simp only [ikp2_psiO]
          unfold psiItem
          cases hS'i : S' i with
          | none => rfl
          | some s' => exact absurd (huniq m' m S' S i s' s hm'.1 hm'.2 hm.1 hm.2 hS' hS hS'i hSi) hne
      · intro h; exact absurd (Finset.mem_Icc.2 hm) h
    · push_neg at hex
      rw [Finset.sum_eq_zero]
      · exact hitem So i
      · intro m hm
        cases hS : out m with
        | none => rfl
        | some S =>
          simp only [ikp2_psiO]
          unfold psiItem
          cases hSi : S i with
          | none => rfl
          | some s => exact absurd hSi (hex m hm S s hS)
  have hΨ : ∑ m ∈ Finset.Icc 1 M, ∑ i, ikp2_psiO K (out m) i ≤ Psi I (pr I K) So := by
    rw [representation_1, contrib, Finset.sum_comm]
    exact Finset.sum_le_sum (fun i _ => hitemS i)
  -- accumulate the per-cluster bounds
  set c := eps K / (M : ℝ) with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hacc : ∀ N, N ≤ M →
      (1 - eps K) * (ϕt N - c * N * ϕt N - N * delta I K ξ) ≤
        ∑ m ∈ Finset.Icc 1 N, ∑ i, ikp2_psiO K (out m) i := by
    intro N
    induction N with
    | zero => intro _; simp [hϕ0]
    | succ N ih =>
      intro hN
      rw [Finset.sum_Icc_succ_top (by omega)]
      have h1 := ih (by omega)
      have h2 := hc (N + 1) (by omega) hN
      simp only [Nat.add_sub_cancel] at h2
      have hmo := hϕmono (N + 1) (by omega) hN
      simp only [Nat.add_sub_cancel] at hmo
      have hnn := hϕnn N (by omega)
      push_cast
      have : (1 - eps K) * (c * (N + 1) * ϕt N) ≤ (1 - eps K) * (c * (N + 1) * ϕt (N + 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        apply mul_le_mul_of_nonneg_left hmo; positivity
      nlinarith
  have hfin := hacc M le_rfl
  have hcM : c * (M : ℝ) ≤ eps K := by
    rcases Nat.eq_zero_or_pos M with h | h
    · rw [h]; simp; exact he0
    · rw [hcdef, div_mul_cancel₀]; exact_mod_cast h.ne'
  have hϕMnn := hϕnn M le_rfl
  have hMδ : 0 ≤ (M : ℝ) * delta I K ξ := by positivity
  have : (1 - 2 * eps K) * ϕt M - (M : ℝ) * delta I K ξ ≤
      (1 - eps K) * (ϕt M - c * M * ϕt M - M * delta I K ξ) := by
    have h1 : c * M * ϕt M ≤ eps K * ϕt M := mul_le_mul_of_nonneg_right hcM hϕMnn
    nlinarith [mul_nonneg (sq_nonneg (eps K)) hϕMnn, mul_nonneg he0 hMδ]
  linarith
