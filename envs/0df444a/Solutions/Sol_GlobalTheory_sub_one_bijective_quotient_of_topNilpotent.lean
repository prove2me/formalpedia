-- Prove2me | solution 1 for GlobalTheory.sub_one_bijective_quotient_of_topNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:41:17.515879+00:00
-- url     : https://prove2.me/submissions/0f001666-fcae-4fc8-967f-b240ae4e02ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SubOneBijectiveQuotientOfTopNilpotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (N : Type) [AddCommGroup N] (p : ℕ) (Φ : N →+ N) (M D : AddSubgroup N) (F : ℕ → AddSubgroup N), D ≤ M → (∀ x ∈ M, Φ x ∈ M) → (∀ x ∈ D, Φ x ∈ D) → (∀ m, ∀ x ∈ F m, Φ x ∈ F (m + 1)) → (∀ m, F (m + 1) ≤ F m) → (∀ x, p • x ∈ M → x ∈ M) → (∀ x, p • x ∈ D → x ∈ D) → (∀ f : ℕ → N, (∀ i, f i ∈ M) → (∀ i, f i ∈ F i) → ∃ s ∈ M, ∀ m, s - ∑ i ∈ Finset.range m, f i ∈ F m) → (∀ x, (∀ m, ∃ d ∈ D, x - d ∈ F m) → ∃ d ∈ D, ∃ r, x - d = p • r) → (∀ y ∈ M, ∃ j : ℕ, ∃ d ∈ D, Φ^[j] y - d ∈ F 0) → (∀ x : ℕ → N, (∀ i, x i ∈ M) → ∃ s ∈ M, ∀ k, ∃ r, s - ∑ i ∈ Finset.range k, p ^ i • x i = p ^ k • r) → (∀ x, (∀ k : ℕ, ∃ d ∈ D, ∃ r, x - d = p ^ k • r) → x ∈ D) → (∀ y ∈ M, ∃ z ∈ M, y - (Φ z - z) ∈ D) ∧ (∀ z ∈ M, Φ z - z ∈ D → z ∈ D) := by
  intro N _ p Φ M D F hDM hΦM hΦD hΦF hFmono hpM hpD hFcomp hFclosed hnil hpcomp hpclosed
  have hiterM : ∀ (i : ℕ) (x : N), x ∈ M → Φ^[i] x ∈ M := by
    intro i
    induction i with
    | zero => intro x hx; simpa using hx
    | succ i ih => intro x hx; rw [Function.iterate_succ_apply']; exact hΦM _ (ih x hx)
  have htel : ∀ (x : N) (m : ℕ), Φ (∑ i ∈ Finset.range m, Φ^[i] x) - ∑ i ∈ Finset.range m, Φ^[i] x = Φ^[m] x - x := by
    intro x m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, map_add, Function.iterate_succ_apply']
      have hsplit : ∀ a b : N, Φ a + Φ b - (a + b) = (Φ a - a) + (Φ b - b) := fun a b => by abel
      rw [hsplit, ih]
      abel
  have step : ∀ z ∈ M, Φ z - z ∈ D → ∃ d ∈ D, ∃ r, z - d = p • r ∧ r ∈ M ∧ Φ r - r ∈ D := by
    intro z hzM hzD
    have hiter : ∀ j : ℕ, Φ^[j] z - z ∈ D := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [Function.iterate_succ_apply']
        have h : Φ (Φ^[j] z) - z = Φ (Φ^[j] z - z) + (Φ z - z) := by rw [map_sub]; abel
        rw [h]
        exact D.add_mem (hΦD _ ih) hzD
    have happrox : ∀ m, ∃ d ∈ D, z - d ∈ F m := by
      intro m
      induction m with
      | zero =>
        obtain ⟨j, d, hd, hj⟩ := hnil z hzM
        refine ⟨d - (Φ^[j] z - z), D.sub_mem hd (hiter j), ?_⟩
        have h : z - (d - (Φ^[j] z - z)) = Φ^[j] z - d := by abel
        rw [h]
        exact hj
      | succ m ih =>
        obtain ⟨d, hd, hm⟩ := ih
        refine ⟨Φ d - (Φ z - z), D.sub_mem (hΦD d hd) hzD, ?_⟩
        have h : z - (Φ d - (Φ z - z)) = Φ (z - d) := by rw [map_sub]; abel
        rw [h]
        exact hΦF m _ hm
    obtain ⟨d, hd, r, hr⟩ := hFclosed z happrox
    have hpr : p • r ∈ M := by rw [← hr]; exact M.sub_mem hzM (hDM hd)
    refine ⟨d, hd, r, hr, hpM r hpr, hpD _ ?_⟩
    have h : p • (Φ r - r) = (Φ z - z) - (Φ d - d) := by
      rw [smul_sub, ← map_nsmul, ← hr, map_sub]
      abel
    rw [h]
    exact D.sub_mem hzD (D.sub_mem (hΦD d hd) hd)
  have hinj : ∀ z ∈ M, Φ z - z ∈ D → z ∈ D := by
    intro z hzM hzD
    have key : ∀ k : ℕ, ∃ d ∈ D, ∃ r, z - d = p ^ k • r ∧ r ∈ M ∧ Φ r - r ∈ D := by
      intro k
      induction k with
      | zero => exact ⟨0, D.zero_mem, z, by simp, hzM, hzD⟩
      | succ k ih =>
        obtain ⟨d, hd, r, hr, hrM, hrD⟩ := ih
        obtain ⟨d', hd', r', hr', hr'M, hr'D⟩ := step r hrM hrD
        refine ⟨d + p ^ k • d', D.add_mem hd (nsmul_mem hd' _), r', ?_, hr'M, hr'D⟩
        calc z - (d + p ^ k • d') = p ^ k • (r - d') := by rw [smul_sub, ← hr]; abel
          _ = p ^ (k + 1) • r' := by rw [hr', pow_succ, mul_smul]
    apply hpclosed
    intro k
    obtain ⟨d, hd, r, hr, -, -⟩ := key k
    exact ⟨d, hd, r, hr⟩
  have step1 : ∀ y ∈ M, ∃ z ∈ M, ∃ d ∈ D, ∃ r, y - (Φ z - z) - d = p • r := by
    intro y hyM
    obtain ⟨j, d, hd, hj⟩ := hnil y hyM
    obtain ⟨e, he⟩ : ∃ e, e = Φ^[j] y - d := ⟨_, rfl⟩
    rw [← he] at hj
    have heM : e ∈ M := by rw [he]; exact M.sub_mem (hiterM j y hyM) (hDM hd)
    have hfF : ∀ i, Φ^[i] e ∈ F i := by
      intro i
      induction i with
      | zero => simpa using hj
      | succ i ih => rw [Function.iterate_succ_apply']; exact hΦF i _ ih
    obtain ⟨s, hsM, hs⟩ := hFcomp (fun i => Φ^[i] e) (fun i => hiterM i e heM) hfF
    have hx : ∀ m, Φ s - s + e ∈ F m := by
      intro m
      have hsm : s - ∑ i ∈ Finset.range m, Φ^[i] e ∈ F m := hs m
      have ht := htel e m
      generalize ∑ i ∈ Finset.range m, Φ^[i] e = S at hsm ht
      have h : Φ s - s + e = (Φ (s - S) - (s - S)) + Φ^[m] e := by
        rw [map_sub, ← sub_add_cancel (Φ^[m] e) e, ← ht]
        abel
      rw [h]
      exact add_mem (sub_mem (hFmono m (hΦF m _ hsm)) hsm) (hfF m)
    obtain ⟨d', hd', r, hr⟩ := hFclosed (Φ s - s + e) (fun m => ⟨0, D.zero_mem, by rw [sub_zero]; exact hx m⟩)
    refine ⟨-(∑ i ∈ Finset.range j, Φ^[i] y + s),
      M.neg_mem (M.add_mem (sum_mem fun i _ => hiterM i y hyM) hsM), d + d', D.add_mem hd hd', r, ?_⟩
    have hT := htel y j
    generalize ∑ i ∈ Finset.range j, Φ^[i] y = T at hT ⊢
    rw [← hr, map_neg, map_add, he, show Φ^[j] y = Φ T - T + y by rw [hT]; abel]
    abel
  choose! Z hZM Dd hDd R hR using step1
  have hRM : ∀ y ∈ M, R y ∈ M := by
    intro y hy
    apply hpM
    rw [← hR y hy]
    exact M.sub_mem (M.sub_mem hy (M.sub_mem (hΦM _ (hZM y hy)) (hZM y hy))) (hDM (hDd y hy))
  have hsurj : ∀ y ∈ M, ∃ z ∈ M, y - (Φ z - z) ∈ D := by
    intro y hyM
    have hys : ∀ k, R^[k] y ∈ M := by
      intro k
      induction k with
      | zero => simpa using hyM
      | succ k ih => rw [Function.iterate_succ_apply']; exact hRM _ ih
    have hexp : ∀ k, y - ∑ i ∈ Finset.range k, p ^ i • (Φ (Z (R^[i] y)) - Z (R^[i] y))
        - ∑ i ∈ Finset.range k, p ^ i • Dd (R^[i] y) = p ^ k • R^[k] y := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Function.iterate_succ_apply', pow_succ,
          mul_smul, ← hR _ (hys k), smul_sub (p ^ k) (R^[k] y - _), smul_sub (p ^ k) (R^[k] y), ← ih]
        abel
    obtain ⟨W, hWM, hW⟩ := hpcomp (fun i => Z (R^[i] y)) (fun i => hZM _ (hys i))
    refine ⟨W, hWM, hpclosed _ ?_⟩
    intro k
    obtain ⟨r, hr⟩ := hW k
    refine ⟨∑ i ∈ Finset.range k, p ^ i • Dd (R^[i] y),
      sum_mem fun i _ => nsmul_mem (hDd _ (hys i)) _, R^[k] y - (Φ r - r), ?_⟩
    have hsum : Φ (∑ i ∈ Finset.range k, p ^ i • Z (R^[i] y)) - ∑ i ∈ Finset.range k, p ^ i • Z (R^[i] y)
        = ∑ i ∈ Finset.range k, p ^ i • (Φ (Z (R^[i] y)) - Z (R^[i] y)) := by
      rw [map_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_nsmul, smul_sub]
    have hWe : W = ∑ i ∈ Finset.range k, p ^ i • Z (R^[i] y) + p ^ k • r := by rw [← hr]; abel
    rw [hWe, map_add, map_nsmul, smul_sub (p ^ k) (R^[k] y), smul_sub (p ^ k) (Φ r), ← hexp k, ← hsum]
    abel
  exact ⟨hsurj, hinj⟩
end GlobalTheory
