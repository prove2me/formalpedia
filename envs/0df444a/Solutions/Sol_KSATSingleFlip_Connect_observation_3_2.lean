-- Prove2me | solution 1 for KSATSingleFlip.Connect.observation_3_2
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:57:20.357673+00:00
-- url     : https://prove2.me/submissions/8b0915e5-5818-49d4-8888-ea948cba0746

import Theorems.Thm_KSATSingleFlip_Connect_forcing_tree_bottom_up_satisfies

open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-- Every finite set of variables admits a bottom-up depth ordering. -/
theorem audit_depth_order {V : Type} [DecidableEq V]
    (s : Finset V) (depth : V → ℕ) :
    ∃ order : List V, order.Nodup ∧ order.toFinset = s ∧
      order.Pairwise (fun u v => depth v ≤ depth u) := by
  let rel : V → V → Bool := fun u v => decide (depth v ≤ depth u)
  let order := s.toList.mergeSort rel
  have hp : order.Perm s.toList := List.mergeSort_perm _ _
  refine ⟨order, hp.nodup_iff.mpr s.nodup_toList, ?_, ?_⟩
  · ext x
    simpa using hp.mem_iff (a := x)
  · have hs := List.pairwise_mergeSort (le := rel) (by
      intro a b c hab hbc
      dsimp [rel] at *
      simp only [decide_eq_true_eq] at *
      omega) (by
      intro a b
      dsimp [rel]
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact le_total _ _) s.toList
    simpa [order, rel] using hs



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

theorem solution {n : ℕ} (Φ : GFormula (Fin n)) (σ : Fin n → Bool)
    (T : ForcingTree Φ σ) (hσ : σ ∈ sols Φ) (hT : T.CompleteIn Finset.univ)
    (hacyclic : ((factorGraph Φ).induce {v | match v with
      | Sum.inl u => u ∈ T.vars
      | Sum.inr _ => True}).IsAcyclic) :
    (∃ order : List (Fin n), order.Nodup ∧ order.toFinset = T.vars ∧
      order.Pairwise (fun u v => T.depth v ≤ T.depth u)) ∧
    ∀ order : List (Fin n), order.Nodup → order.toFinset = T.vars →
      order.Pairwise (fun u v => T.depth v ≤ T.depth u) →
      ∃ τ : Fin n → Bool,
        IsSatPath Φ (order.scanl (fun z u => KSATSingleFlip.Connect.flip z u) σ) σ τ ∧
        pathLength (order.scanl (fun z u => KSATSingleFlip.Connect.flip z u) σ) = T.vars.card ∧
        disagree σ τ = T.vars := by
  constructor
  · exact audit_depth_order T.vars T.depth
  · intro order hn hv ho
    have hsat := forcing_tree_bottom_up_satisfies Φ σ T hσ hT hacyclic order hn hv ho
    have hpath := audit_scan_flip_path Φ σ order hsat
    refine ⟨order.foldl (fun z u => KSATSingleFlip.Connect.flip z u) σ, hpath.1, ?_, ?_⟩
    · rw [hpath.2, ← List.toFinset_card_of_nodup hn, hv]
    · rw [audit_fold_flips_disagree order hn, hv]

#print axioms solution
