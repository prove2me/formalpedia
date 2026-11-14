-- Prove2me | solution 1 for KSATSingleFlip.Connect.wordRAM_input_integrity
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:00:14.71998+00:00
-- url     : https://prove2.me/submissions/a84c25cd-4239-4be6-a518-2371ab846ab6

import Definitions.Def_KSATSingleFlip_Connect_WordRAM

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

open KSATSingleFlip.Connect

theorem solution (n k m T : ℕ) :
    (∀ (F : SparseFormula n k m) (x : Fin n → Bool) (v : Fin n),
      (sparseFlipInput F x v).length = sparseFlipInputWords n k m ∧
      ∀ a ∈ sparseFlipInput F x v, a < 2 ^ wordRAMWidth n k m T) ∧
    (∀ (F : SparseFormula n k m) (x y : Fin n → Bool),
      (sparseRouteInput F x y).length = sparseRouteInputWords n k m ∧
      ∀ a ∈ sparseRouteInput F x y, a < 2 ^ wordRAMRouteWidth n k m T) ∧
    (∀ (program : WordRAMProgram) (w : ℕ) (s : WordRAMState), s.halted = true →
      wordRAMRun program w T s = s) := by
  refine ⟨?_, ?_, ?_⟩
  · intro F x v
    exact ⟨audit_sparse_input_length F x v, audit_sparse_input_word_fits F x v T⟩
  · intro F x y
    exact ⟨audit_sparse_route_input_length F x y, audit_sparse_route_input_word_fits F x y T⟩
  · exact fun p w s h => audit_wordRAM_halted_run p w T s h

#print axioms solution
