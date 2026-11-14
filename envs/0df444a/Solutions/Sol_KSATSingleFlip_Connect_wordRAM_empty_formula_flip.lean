-- Prove2me | solution 1 for KSATSingleFlip.Connect.wordRAM_empty_formula_flip
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:12:51.659116+00:00
-- url     : https://prove2.me/submissions/186e1453-bb87-4c9d-99ef-93f2bbb99cae

import Definitions.Def_KSATSingleFlip_Connect_WordRAM


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


-- Component: AuditKSATEmptyFlipProgram.lean

open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-- A deterministic program that flips the requested variable when m=0. -/
def auditEmptyFlipProgram : WordRAMProgram :=
  [.constant 0 0, .load 1 0, .constant 2 3, .add 2 2 1, .load 3 2,
   .constant 4 1, .store 0 4, .constant 0 1, .store 0 4,
   .constant 0 2, .store 0 3, .halt]

/-- The last input word of an empty sparse formula is the requested variable. -/
theorem audit_empty_input_target {n k : ℕ} (F : SparseFormula n k 0)
    (x : Fin n → Bool) (v : Fin n) :
    (wordRAMStart (sparseFlipInput F x v)).memory (3 + n) = v.val := by
  rw [show 3 + n = n + 3 by omega]
  simp [wordRAMStart, sparseFlipInput, List.getElem?_append]

set_option maxHeartbeats 1000000 in
/-- The empty-formula program writes its one-index result and halts. -/
theorem audit_empty_flip_run (w n a : ℕ) (s : WordRAMState)
    (hpc : s.pc = 0) (hhalt : s.halted = false)
    (hn : n + 3 < 2^w) (ha : a < 2^w)
    (hfirst : s.memory 0 = n) (htarget : s.memory (3+n) = a) :
    let r := wordRAMRun auditEmptyFlipProgram w 12 s
    r.halted = true ∧ r.memory 0 = 1 ∧ r.memory 1 = 1 ∧ r.memory 2 = a := by
  have h0 : 0 < 2^w := by positivity
  have h1 : 1 < 2^w := by omega
  have h2 : 2 < 2^w := by omega
  have h3 : 3 < 2^w := by omega
  have hN : n < 2^w := by omega
  have hsum : 3+n < 2^w := by omega
  simp [wordRAMRun, wordRAMStep, auditEmptyFlipProgram, WordRAMState.read,
    WordRAMState.writeNext, Function.update_apply, hpc, hhalt, hfirst, htarget,
    Nat.mod_eq_of_lt, h0, h1, h2, h3, hN, hsum, ha]

/-- The decoder reads a well-formed one-flip output. -/
theorem audit_decode_single {n : ℕ} (w : ℕ) (s : WordRAMState) (v : Fin n)
    (hh : s.halted = true) (h0 : s.memory 0 = 1) (h1 : s.memory 1 = 1)
    (h2 : s.memory 2 = v.val) (hw : 1 + 2 ≤ 2^w) :
    wordRAMDecodeFlips n w s = some [v] := by
  unfold wordRAMDecodeFlips
  have hg : s.halted ∧ s.memory 0 = 1 ∧ s.memory 1 + 2 ≤ 2^w := by
    simp [hh, h0, h1, hw]
  rw [if_pos hg]
  simp [h1, h2, v.isLt]

set_option maxHeartbeats 800000 in
/-- The concrete empty-formula program returns exactly the requested flip. -/
theorem audit_empty_flip_result {n k : ℕ} (F : SparseFormula n k 0)
    (x : Fin n → Bool) (v : Fin n) :
    wordRAMFlipResult auditEmptyFlipProgram 12 F x v = some ⟨x, [v]⟩ := by
  let w := wordRAMWidth n k 0 12
  let s := wordRAMStart (sparseFlipInput F x v)
  have hc := audit_wordRAM_width_capacity n k 0 12
  have hn : n + 3 < 2^w := by
    dsimp [w]
    dsimp [sparseFlipInputWords] at hc
    omega
  have ha : v.val < 2^w := by
    have hv := v.isLt
    dsimp [w]
    omega
  have hfirst : s.memory 0 = n := by simp [s, wordRAMStart, sparseFlipInput]
  have htarget : s.memory (3+n) = v.val := audit_empty_input_target F x v
  have hrun := audit_empty_flip_run w n v.val s rfl rfl hn ha hfirst htarget
  have hguard : 1 + 2 ≤ 2^w := by omega
  have hdecode := audit_decode_single w (wordRAMRun auditEmptyFlipProgram w 12 s) v
    hrun.1 hrun.2.1 hrun.2.2.1 hrun.2.2.2 hguard
  have hmap := congrArg (Option.map (fun flips : List (Fin n) => FlipListPath.mk x flips)) hdecode
  simpa only [wordRAMFlipResult, Option.map_some] using hmap

/-- A concrete finite program solves every zero-clause variable-flip request,
returns a satisfying one-flip path, and halts within twelve RAM steps. -/
theorem audit_empty_formula_flip_program :
    ∃ program : WordRAMProgram, ∀ (n k : ℕ) (F : SparseFormula n k 0)
      (x : Fin n → Bool) (v : Fin n),
      wordRAMFlipResult program 12 F x v = some ⟨x, [v]⟩ ∧
      (FlipListPath.mk x [v]).Satisfies (sparseFormulaSemantics F) ∧
      (FlipListPath.mk x [v]).terminal v ≠ x v := by
  refine ⟨auditEmptyFlipProgram, ?_⟩
  intro n k F x v
  refine ⟨audit_empty_flip_result F x v, ?_, ?_⟩
  · simp [FlipListPath.Satisfies, FlipListPath.states, sparseFormulaSemantics, FSat]
  · simp only [FlipListPath.terminal, List.foldl_cons, List.foldl_nil, flip, Function.update_self]
    cases h : x v <;> simp

end KSATSingleFlip.Connect


open KSATSingleFlip.Connect

theorem solution :
    ∃ program : WordRAMProgram, ∀ (n k : ℕ) (F : SparseFormula n k 0)
      (x : Fin n → Bool) (v : Fin n),
      wordRAMFlipResult program 12 F x v = some ⟨x, [v]⟩ ∧
      (FlipListPath.mk x [v]).Satisfies (sparseFormulaSemantics F) ∧
      (FlipListPath.mk x [v]).terminal v ≠ x v := by
  exact audit_empty_formula_flip_program

#print axioms solution
