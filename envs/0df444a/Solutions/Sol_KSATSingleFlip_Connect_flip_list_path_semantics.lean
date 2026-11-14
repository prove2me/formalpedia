-- Prove2me | solution 1 for KSATSingleFlip.Connect.flip_list_path_semantics
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:25:21.536084+00:00
-- url     : https://prove2.me/submissions/fc2223ed-a0e4-4658-9925-eb5c2d555939

import Definitions.Def_KSATSingleFlip_Connect_SparseFlip

open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

theorem audit_scan_hamming_flip {n : ℕ} (z : Fin n → Bool) (u : Fin n) :
    hamming z (flip z u) = 1 := by
  have hs : disagree z (flip z u) = {u} := by
    ext v
    by_cases hv : v = u
    · subst v
      have : z u ≠ flip z u u := by
        simp only [flip, Function.update_self]
        cases h : z u <;> simp
      simpa [disagree] using this
    · simp only [disagree, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      rw [show flip z u v = z v from Function.update_of_ne hv _ _]
      simp [hv]
  simp [hamming, hs]

theorem audit_scan_flip_chain {n : ℕ} (order : List (Fin n)) (σ : Fin n → Bool) :
    (order.scanl (fun z u => flip z u) σ).IsChain (fun a b => hamming a b = 1) := by
  induction order generalizing σ with
  | nil => simp
  | cons v rest ih =>
    cases rest with
    | nil => simpa using audit_scan_hamming_flip σ v
    | cons w rest =>
      simp only [List.scanl_cons]
      apply List.isChain_cons_cons.mpr
      refine ⟨audit_scan_hamming_flip σ v, ?_⟩
      simpa only [List.scanl_cons] using ih (flip σ v)

/-- If all intermediate states satisfy the formula, the scan is a satisfying
single-flip path of exactly the number of listed flips. -/
theorem audit_scan_flip_path {n : ℕ} (Φ : GFormula (Fin n))
    (σ : Fin n → Bool) (order : List (Fin n))
    (hs : ∀ z ∈ order.scanl (fun z u => flip z u) σ, FSat z Φ) :
    IsSatPath Φ (order.scanl (fun z u => flip z u) σ) σ
      (order.foldl (fun z u => flip z u) σ) ∧
    pathLength (order.scanl (fun z u => flip z u) σ) = order.length := by
  constructor
  · unfold IsSatPath IsPathIn
    refine ⟨List.head?_scanl, List.getLast?_scanl, ?_, audit_scan_flip_chain order σ⟩
    intro z hz
    simpa [sols] using hs z hz
  · simp [pathLength]

/-- A no-duplicate scan flips precisely the listed coordinates. -/
theorem audit_fold_flips_at {n : ℕ} (order : List (Fin n)) (hn : order.Nodup)
    (σ : Fin n → Bool) (u : Fin n) :
    order.foldl (fun z v => flip z v) σ u = if u ∈ order then !σ u else σ u := by
  induction order generalizing σ with
  | nil => simp
  | cons v rest ih =>
    have hv : v ∉ rest := (List.nodup_cons.mp hn).1
    have hr : rest.Nodup := (List.nodup_cons.mp hn).2
    rw [List.foldl_cons, ih hr]
    by_cases huv : u = v
    · subst u
      simp [hv, flip]
    · have hf : flip σ v u = σ u := Function.update_of_ne huv _ _
      simp [huv, Ne.symm huv, hf]

theorem audit_fold_flips_disagree {n : ℕ} (order : List (Fin n)) (hn : order.Nodup)
    (σ : Fin n → Bool) :
    disagree σ (order.foldl (fun z v => flip z v) σ) = order.toFinset := by
  ext u
  simp only [disagree, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset]
  rw [audit_fold_flips_at order hn]
  by_cases hu : u ∈ order <;> cases h : σ u <;> simp [hu, h]

end KSATSingleFlip.Connect

open KSATSingleFlip.Connect

theorem solution {n : ℕ} (p : FlipListPath n) (Φ : GFormula (Fin n))
    (hs : p.Satisfies Φ) :
    IsSatPath Φ p.states p.initial p.terminal ∧
    pathLength p.states = p.flips.length ∧
    (p.flips.Nodup → disagree p.initial p.terminal = p.flips.toFinset) := by
  have h := audit_scan_flip_path Φ p.initial p.flips hs
  refine ⟨h.1, h.2, ?_⟩
  exact fun hn => audit_fold_flips_disagree p.flips hn p.initial

#print axioms solution
