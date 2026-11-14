-- Prove2me | solution 1 for KSATSingleFlip.Connect.wordRAM_geometry_sound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:02:51.349783+00:00
-- url     : https://prove2.me/submissions/2915752e-e90b-449a-b87f-76ca8b3585a0

import Definitions.Def_KSATSingleFlip_Connect_RAMLooseness


-- Component: AuditKSATSparseSemantics.lean

open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

theorem audit_sparse_clause_at {n k : ℕ} (C : SparseClause n k) (i : Fin k) :
    C.toClause (C.index i) = some (C.sign i) := by
  unfold SparseClause.toClause
  have h : ∃ j, C.index j = C.index i := ⟨i, rfl⟩
  rw [dif_pos h]
  have hchoice : Classical.choose h = i := C.index.injective (Classical.choose_spec h)
  rw [hchoice]

theorem audit_sparse_scope {n k : ℕ} (C : SparseClause n k) :
    vbl C.toClause = Finset.univ.image C.index := by
  ext v
  simp only [vbl, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro hv
    unfold SparseClause.toClause at hv
    split at hv
    · rename_i h
      exact ⟨Classical.choose h, Classical.choose_spec h⟩
    · simp at hv
  · rintro ⟨i, _, rfl⟩
    rw [audit_sparse_clause_at]
    rfl

theorem audit_sparse_scope_card {n k : ℕ} (C : SparseClause n k) :
    (vbl C.toClause).card = k := by
  rw [audit_sparse_scope, Finset.card_image_iff.mpr C.index.injective.injOn]
  simp

theorem audit_sparse_clause_sat {n k : ℕ} (C : SparseClause n k) (x : Fin n → Bool) :
    ClauseSat x C.toClause ↔ C.Sat x := by
  constructor
  · rintro ⟨v, hv⟩
    unfold SparseClause.toClause at hv
    split at hv
    · rename_i h
      refine ⟨Classical.choose h, ?_⟩
      have he := Option.some.inj hv
      simpa [Classical.choose_spec h] using he
    · simp at hv
  · rintro ⟨i, hi⟩
    exact ⟨C.index i, by rw [audit_sparse_clause_at, hi]⟩

theorem audit_sparse_input_linear (n k m c : ℕ) (hm : m ≤ c * n) :
    sparseFlipInputWords n k m ≤ 4 + (2 * k * c + 1) * n := by
  unfold sparseFlipInputWords
  nlinarith

theorem audit_flip_path_word_count {n : ℕ} (p : FlipListPath n) :
    p.wordCount = n + 1 + p.flips.length := rfl

end KSATSingleFlip.Connect

namespace KSATSingleFlip.Connect
open OAI.FixedClauseThreshold

/-- Every proper option-valued k-clause has a sparse representation. -/
theorem audit_sparse_represents_clause {n k : ℕ} (D : ProperClause n k) :
    ∃ C : SparseClause n k, C.toClause = D.val := by
  let S : Finset (Fin n) := vbl D.val
  have hcard : S.card = k := D.property
  let e : Fin k ≃ {v // v ∈ S} := (Finset.equivFinOfCardEq hcard).symm
  let C : SparseClause n k :=
    { index := e.toEmbedding.trans (Function.Embedding.subtype (· ∈ S))
      sign := fun i => (D.val (e i).1).getD false }
  refine ⟨C, ?_⟩
  funext v
  by_cases hv : v ∈ S
  · let i : Fin k := e.symm ⟨v, hv⟩
    have hi : C.index i = v := by simp [C, i]
    calc
      C.toClause v = C.toClause (C.index i) := by rw [hi]
      _ = some (C.sign i) := audit_sparse_clause_at C i
      _ = D.val v := by
        have hs : (D.val v).isSome := (Finset.mem_filter.mp hv).2
        have he : (e i).1 = v := by simpa [C] using hi
        dsimp [C]
        rw [he]
        cases hval : D.val v <;> simp_all
  · have hnone : D.val v = none := by
      have hs : ¬(D.val v).isSome := by
        simpa [S, vbl] using hv
      cases hval : D.val v <;> simp_all
    have hnindex : ¬∃ i, C.index i = v := by
      rintro ⟨i, hi⟩
      apply hv
      have he : (e i).1 = v := by simpa [C] using hi
      exact he ▸ (e i).property
    simp [SparseClause.toClause, hnindex, hnone]

end KSATSingleFlip.Connect

namespace KSATSingleFlip.Connect
open OAI.FixedClauseThreshold

/-- Every ordered formula has an order- and multiplicity-preserving sparse encoding. -/
theorem audit_sparse_represents_formula {n k m : ℕ} (F : Formula n k m) :
    ∃ G : SparseFormula n k m, sparseFormulaSemantics G = ofFormula F := by
  let G : SparseFormula n k m := fun j => Classical.choose (audit_sparse_represents_clause (F j))
  refine ⟨G, ?_⟩
  unfold sparseFormulaSemantics ofFormula
  apply congrArg List.ofFn
  funext j
  exact Classical.choose_spec (audit_sparse_represents_clause (F j))

end KSATSingleFlip.Connect


-- Component: AuditKSATFlipScanPath.lean

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


-- Component: AuditKSATWordRAM.lean

open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-- Serialization has exactly the sparse input word count. -/
theorem audit_sparse_input_length {n k m : ℕ} (F : SparseFormula n k m)
    (x : Fin n → Bool) (v : Fin n) :
    (sparseFlipInput F x v).length = sparseFlipInputWords n k m := by
  unfold sparseFlipInput sparseFlipInputWords
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_flatten,
    List.map_ofFn, Function.comp_def, List.length_ofFn, List.sum_ofFn]
  simp
  nlinarith

/-- Once halted, every subsequent transition leaves the state unchanged. -/
theorem audit_wordRAM_halted_step (p : WordRAMProgram) (w : ℕ) (s : WordRAMState)
    (h : s.halted = true) : wordRAMStep p w s = s := by
  simp [wordRAMStep, h]

theorem audit_wordRAM_halted_run (p : WordRAMProgram) (w T : ℕ) (s : WordRAMState)
    (h : s.halted = true) : wordRAMRun p w T s = s := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [wordRAMRun, audit_wordRAM_halted_step p w s h]
    exact ih

/-- A register write stores a word strictly below 2^w. -/
theorem audit_wordRAM_write_bounded (s : WordRAMState) (w r a : ℕ) :
    (s.writeNext w r a).registers r < 2^w := by
  simp [WordRAMState.writeNext, Nat.mod_lt, Nat.two_pow_pos]

/-- The chosen word width can represent instance dimensions, the entire
serialized input address range, and the supplied step bound. -/
theorem audit_wordRAM_width_capacity (n k m T : ℕ) :
    n < 2 ^ wordRAMWidth n k m T ∧
    k < 2 ^ wordRAMWidth n k m T ∧
    m < 2 ^ wordRAMWidth n k m T ∧
    sparseFlipInputWords n k m < 2 ^ wordRAMWidth n k m T ∧
    T < 2 ^ wordRAMWidth n k m T := by
  have h := Nat.lt_log2_self (n := n + k + m + sparseFlipInputWords n k m + T + 2)
  dsimp [wordRAMWidth]
  omega

/-- The routing input also uses a linear number of words. -/
theorem audit_sparse_route_input_length {n k m : ℕ} (F : SparseFormula n k m)
    (x y : Fin n → Bool) :
    (sparseRouteInput F x y).length = sparseRouteInputWords n k m := by
  unfold sparseRouteInput sparseRouteInputWords
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_flatten,
    List.map_ofFn, Function.comp_def, List.length_ofFn, List.sum_ofFn]
  simp
  nlinarith

theorem audit_wordRAM_route_width_capacity (n k m T : ℕ) :
    n < 2 ^ wordRAMRouteWidth n k m T ∧
    k < 2 ^ wordRAMRouteWidth n k m T ∧
    m < 2 ^ wordRAMRouteWidth n k m T ∧
    sparseRouteInputWords n k m < 2 ^ wordRAMRouteWidth n k m T ∧
    T < 2 ^ wordRAMRouteWidth n k m T := by
  have h := Nat.lt_log2_self (n := n + k + m + sparseRouteInputWords n k m + T + 2)
  dsimp [wordRAMRouteWidth]
  omega

/-- Every sparse flip-input word fits in the chosen machine word. -/
theorem audit_sparse_input_word_fits {n k m : ℕ} (F : SparseFormula n k m)
    (x : Fin n → Bool) (v : Fin n) (T : ℕ) (a : ℕ)
    (ha : a ∈ sparseFlipInput F x v) : a < 2 ^ wordRAMWidth n k m T := by
  have hc := audit_wordRAM_width_capacity n k m T
  simp only [sparseFlipInput, List.mem_append, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false, List.mem_flatten, List.mem_ofFn] at ha
  rcases ha with (((hhead | hclause) | hassign) | htarget)
  · rcases hhead with rfl | rfl | rfl
    · exact hc.1
    · exact hc.2.1
    · exact hc.2.2.1
  · obtain ⟨l, ⟨j, rfl⟩, hl⟩ := hclause
    simp only [List.mem_append, List.mem_ofFn] at hl
    rcases hl with ⟨i, hi⟩ | ⟨i, hi⟩
    · have hval := ((F j).index i).isLt
      omega
    · have hs := Bool.toNat_le ((F j).sign i)
      have hv := v.isLt
      omega
  · obtain ⟨i, hi⟩ := hassign
    have hs := Bool.toNat_le (x i)
    have hv := v.isLt
    omega
  · have hv := v.isLt
    omega

/-- Every local-routing input word fits in the chosen machine word. -/
theorem audit_sparse_route_input_word_fits {n k m : ℕ} (F : SparseFormula n k m)
    (x y : Fin n → Bool) (T : ℕ) (a : ℕ)
    (ha : a ∈ sparseRouteInput F x y) : a < 2 ^ wordRAMRouteWidth n k m T := by
  have hc := audit_wordRAM_route_width_capacity n k m T
  have hbase := Nat.lt_log2_self (n := n + k + m + sparseRouteInputWords n k m + T + 2)
  have hone : 1 < 2 ^ wordRAMRouteWidth n k m T := by
    dsimp [wordRAMRouteWidth]
    omega
  simp only [sparseRouteInput, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_flatten, List.mem_ofFn] at ha
  rcases ha with (((hhead | hclause) | hstart) | htarget)
  · rcases hhead with rfl | rfl | rfl
    · exact hc.1
    · exact hc.2.1
    · exact hc.2.2.1
  · obtain ⟨l, ⟨j, rfl⟩, hl⟩ := hclause
    simp only [List.mem_append, List.mem_ofFn] at hl
    rcases hl with ⟨i, hi⟩ | ⟨i, hi⟩
    · have hval := ((F j).index i).isLt
      omega
    · have hs := Bool.toNat_le ((F j).sign i)
      omega
  · obtain ⟨i, hi⟩ := hstart
    have hs := Bool.toNat_le (x i)
    omega
  · obtain ⟨i, hi⟩ := htarget
    have hs := Bool.toNat_le (y i)
    omega

/-- A successfully decoded flip output retains the supplied initial state. -/
theorem audit_wordRAM_flip_result_initial {n k m : ℕ} (program : WordRAMProgram) (T : ℕ)
    (F : SparseFormula n k m) (x : Fin n → Bool) (v : Fin n) (p : FlipListPath n)
    (h : wordRAMFlipResult program T F x v = some p) : p.initial = x := by
  unfold wordRAMFlipResult at h
  obtain ⟨flips, _, heq⟩ := Option.map_eq_some_iff.mp h
  cases heq
  rfl

/-- A successfully decoded route output retains the supplied initial state. -/
theorem audit_wordRAM_route_result_initial {n k m : ℕ} (program : WordRAMProgram) (T : ℕ)
    (F : SparseFormula n k m) (x y : Fin n → Bool) (p : FlipListPath n)
    (h : wordRAMRouteResult program T F x y = some p) : p.initial = x := by
  unfold wordRAMRouteResult at h
  obtain ⟨flips, _, heq⟩ := Option.map_eq_some_iff.mp h
  cases heq
  rfl

/-- A successfully decoded output can only come from a halted state. -/
theorem audit_wordRAM_decode_halted (n w : ℕ) (s : WordRAMState) (flips : List (Fin n))
    (h : wordRAMDecodeFlips n w s = some flips) : s.halted = true := by
  unfold wordRAMDecodeFlips at h
  split at h
  · rename_i hg
    exact hg.1
  · contradiction

end KSATSingleFlip.Connect


-- Component: AuditKSATRAMImpliesGeometry.lean

open scoped Classical BigOperators
open OAI.FixedClauseThreshold
namespace KSATSingleFlip.Connect

/-- Verified word-RAM outputs imply the paper's common-set geometric claims. -/
theorem audit_RAM_implies_geometry {n k m : ℕ} (F : Formula n k m)
    (A B : WordRAMProgram) (cA cB : ℕ) (radius pathConstant : ℝ)
    (h : HasRAMLooseLocalGeometry F A B cA cB radius pathConstant) :
    HasLooseLocalGeometry k (ofFormula F) radius pathConstant := by
  obtain ⟨G, hG⟩ := audit_sparse_represents_formula F
  obtain ⟨hsat, S, hsub, hmass, hgood⟩ := h
  refine ⟨hsat, S, hsub, hmass, ?_⟩
  intro x hx
  obtain ⟨hflip, hroute⟩ := hgood x hx
  constructor
  · intro v
    obtain ⟨p, hresult, hp, hchange, hlength⟩ := hflip v G hG
    have hinit := audit_wordRAM_flip_result_initial A (cA * n) G x v p hresult
    have hpath := audit_scan_flip_path (ofFormula F) p.initial p.flips hp
    refine ⟨p.terminal, p.states, ?_, hchange, ?_⟩
    · simpa [FlipListPath.states, FlipListPath.terminal, hinit] using hpath.1
    · simpa [FlipListPath.states, hpath.2] using hlength
  · intro y hy hdist
    obtain ⟨p, hresult, hp, hterm, hlength⟩ := hroute y hy hdist G hG
    have hinit := audit_wordRAM_route_result_initial B (cB * n * n) G x y p hresult
    have hpath := audit_scan_flip_path (ofFormula F) p.initial p.flips hp
    refine ⟨p.states, ?_, ?_⟩
    · have hpath' : IsSatPath (ofFormula F) p.states p.initial p.terminal := hpath.1
      rw [hinit, hterm] at hpath'
      exact hpath'
    · simpa [FlipListPath.states, hpath.2] using hlength

end KSATSingleFlip.Connect


open OAI.FixedClauseThreshold KSATSingleFlip.Connect

theorem solution {n k m : ℕ} (F : Formula n k m)
    (A B : WordRAMProgram) (cA cB : ℕ) (radius pathConstant : ℝ)
    (h : HasRAMLooseLocalGeometry F A B cA cB radius pathConstant) :
    HasLooseLocalGeometry k (ofFormula F) radius pathConstant := by
  exact audit_RAM_implies_geometry F A B cA cB radius pathConstant h

#print axioms solution
