-- Prove2me | solution 1 for KSATSingleFlip.Connect.forcing_tree_bottom_up_satisfies
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:01:18.731097+00:00
-- url     : https://prove2.me/submissions/21519f47-ac54-43b3-881d-670510749a80

import Theorems.Thm_KSATSingleFlip_Connect_forcing_tree_acyclic_true_unique

open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-- In a bottom-up order, a deeper listed vertex appears in every prefix
which contains its shallower ancestor. -/
theorem audit_depth_prefix {V : Type} [DecidableEq V] (depth : V → ℕ)
    (order : List V) (ho : order.Pairwise (fun u v => depth v ≤ depth u))
    (parent child : V) (hc : child ∈ order) (hdepth : depth parent < depth child)
    (i : ℕ) (hp : parent ∈ order.take i) : child ∈ order.take i := by
  by_contra hnot
  have hchild : child ∈ order.drop i := by
    have h : child ∈ order.take i ++ order.drop i := by simpa using hc
    exact (List.mem_append.mp h).resolve_left hnot
  have hpair : (order.take i ++ order.drop i).Pairwise (fun u v => depth v ≤ depth u) := by
    simpa using ho
  have hle := hpair.rel_of_mem_append hp hchild
  omega

/-- Every state in a flip scan is the fold over some prefix. -/
theorem audit_scan_state_prefix {n : ℕ} (order : List (Fin n)) (σ z : Fin n → Bool)
    (hz : z ∈ order.scanl (fun x u => flip x u) σ) :
    ∃ i ≤ order.length, z = (order.take i).foldl (fun x u => flip x u) σ := by
  obtain ⟨i, hi, hz⟩ := List.mem_iff_getElem.mp hz
  refine ⟨i, ?_, ?_⟩
  · simpa using hi
  · simpa [List.getElem_scanl hi] using hz.symm



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



/-- Clause preservation requires only that no clause have two originally true
literals in the tree. Acyclicity is one way to obtain that condition. -/
theorem audit_tree_flip_of_true_unique {n : ℕ} (Φ : GFormula (Fin n)) (σ : Fin n → Bool)
    (T : ForcingTree Φ σ) (hσ : σ ∈ sols Φ) (hT : T.CompleteIn Finset.univ)
    (hsep : ∀ c : Fin Φ.length, ∀ u ∈ T.vars, ∀ v ∈ T.vars,
      Φ.get c u = some (σ u) → Φ.get c v = some (σ v) → u = v)
    (order : List (Fin n)) (hn : order.Nodup) (hv : order.toFinset = T.vars)
    (ho : order.Pairwise (fun u v => T.depth v ≤ T.depth u)) :
    ∀ z ∈ order.scanl (fun z u => flip z u) σ, FSat z Φ := by
  intro z hz
  obtain ⟨i, hi, rfl⟩ := audit_scan_state_prefix order σ z hz
  let pre := order.take i
  have hpre : pre.Nodup := hn.take
  have heq (u : Fin n) : pre.foldl (fun z u => flip z u) σ u =
      if u ∈ pre then !σ u else σ u := audit_fold_flips_at pre hpre σ u
  have hin (u : Fin n) (hu : u ∈ pre) : u ∈ T.vars := by
    rw [← hv, List.mem_toFinset]
    exact List.mem_of_mem_take hu
  intro C hC
  obtain ⟨c, rfl⟩ := List.mem_iff_get.mp hC
  have hσsat : ClauseSat σ (Φ.get c) := (by simpa [sols] using hσ : FSat σ Φ) _ (Φ.get_mem c)
  by_cases hs : ∃ u, Φ.get c u = some (σ u) ∧ u ∉ pre
  · obtain ⟨u, hu, hnot⟩ := hs
    exact ⟨u, by rw [heq, if_neg hnot]; exact hu⟩
  · obtain ⟨v, hvtrue⟩ := hσsat
    have hvpre : v ∈ pre := by
      by_contra hnot
      exact hs ⟨v, hvtrue, hnot⟩
    have hvT : v ∈ T.vars := hin v hvpre
    have hforced : Forces σ (Φ.get c) v := by
      unfold Forces
      ext u
      simp only [satSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hut
        have hupre : u ∈ pre := by
          by_contra hnot
          exact hs ⟨u, hut, hnot⟩
        exact hsep c u (hin u hupre) v hvT hut hvtrue
      · rintro rfl
        exact hvtrue
    have hcT := (hT.2 v hvT c (Finset.mem_univ c) hforced)
    have hchild : T.child c ∈ T.vars := T.child_mem c hcT.1
    have hcpre : T.child c ∈ pre := by
      apply audit_depth_prefix T.depth order ho v (T.child c)
      · rw [← hv, List.mem_toFinset] at hchild
        exact hchild
      · have hh := T.depth_child c hcT.1
        rw [hcT.2] at hh
        omega
      · exact hvpre
    have hcne : T.child c ≠ v := by
      intro he
      have hh := T.depth_child c hcT.1
      rw [hcT.2, he] at hh
      omega
    have hcfalse : Φ.get c (T.child c) = some (!(σ (T.child c))) := by
      have hsome : (Φ.get c (T.child c)).isSome := by
        simpa [vbl] using T.child_vbl c hcT.1
      have hntrue : Φ.get c (T.child c) ≠ some (σ (T.child c)) := by
        intro he
        have hm : T.child c ∈ satSet σ (Φ.get c) := by
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩
        rw [hforced] at hm
        exact hcne (Finset.mem_singleton.mp hm)
      cases hsC : Φ.get c (T.child c) with
      | none => simp [hsC] at hsome
      | some b => cases hsc : σ (T.child c) <;> cases b <;> simp_all
    refine ⟨T.child c, ?_⟩
    rw [heq, if_pos hcpre]
    exact hcfalse


end KSATSingleFlip.Connect

open KSATSingleFlip.Connect

theorem solution {n : ℕ} (Φ : GFormula (Fin n)) (σ : Fin n → Bool)
    (T : ForcingTree Φ σ) (hσ : σ ∈ sols Φ) (hT : T.CompleteIn Finset.univ)
    (hacyclic : ((factorGraph Φ).induce {v | match v with
      | Sum.inl u => u ∈ T.vars
      | Sum.inr _ => True}).IsAcyclic)
    (order : List (Fin n)) (hn : order.Nodup) (hv : order.toFinset = T.vars)
    (ho : order.Pairwise (fun u v => T.depth v ≤ T.depth u)) :
    ∀ z ∈ order.scanl (fun z u => KSATSingleFlip.Connect.flip z u) σ, FSat z Φ := by
  exact audit_tree_flip_of_true_unique Φ σ T hσ hT
    (forcing_tree_acyclic_true_unique Φ σ T hacyclic) order hn hv ho

#print axioms solution
