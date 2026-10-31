-- Prove2me | solution 1 for LeeSviridenkoVondrak.LocalSearch.theorem_3_1_monotone
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T04:37:14.439179+00:00
-- url     : https://prove2.me/submissions/b8e0bec7-a492-4588-9b2a-ab71572b624f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_LeeSviridenkoVondrak_LocalSearch_Model
import Definitions.Def_LeeSviridenkoVondrak_LocalSearch_OracleMachine
import Theorems.Thm_LeeSviridenkoVondrak_LocalSearch_lemma_3_2


namespace LSVAlgo
open LeeSviridenkoVondrak.LocalSearch

section Generic
variable {n k : ℕ}

open Classical in
noncomputable def execOp (f : Finset (Fin n) → ℝ) (M : Fin k → Matroid (Fin n))
    (op : Instruction) (s : MachineState n) : MachineState n :=
  let t := { s with pc := s.pc + 1, cost := s.cost + n + 1 }
  match op with
  | .natConst d v => { t with natReg := Function.update s.natReg d v }
  | .natCopy d a => { t with natReg := Function.update s.natReg d (s.natReg a) }
  | .natAdd d a b => { t with natReg := Function.update s.natReg d (s.natReg a + s.natReg b) }
  | .natSub d a b => { t with natReg := Function.update s.natReg d (s.natReg a - s.natReg b) }
  | .natBranch a b y z => { t with pc := if s.natReg a ≤ s.natReg b then y else z }
  | .realConst d v => { t with realReg := Function.update s.realReg d v }
  | .realCopy d a => { t with realReg := Function.update s.realReg d (s.realReg a) }
  | .realAdd d a b => { t with realReg := Function.update s.realReg d (s.realReg a + s.realReg b) }
  | .realSub d a b => { t with realReg := Function.update s.realReg d (s.realReg a - s.realReg b) }
  | .realMul d a b => { t with realReg := Function.update s.realReg d (s.realReg a * s.realReg b) }
  | .realDiv d a b => { t with realReg := Function.update s.realReg d (s.realReg a / s.realReg b) }
  | .realBranch a b y z => { t with pc := if s.realReg a ≤ s.realReg b then y else z }
  | .setEmpty d => { t with setReg := Function.update s.setReg d ∅ }
  | .setCopy d a => { t with setReg := Function.update s.setReg d (s.setReg a) }
  | .setInsert d a e =>
    { t with setReg := (Function.update s.setReg d (if h : s.natReg e < n then insert ⟨s.natReg e, h⟩ (s.setReg a) else s.setReg a)) }
  | .setErase d a e =>
    { t with setReg := (Function.update s.setReg d (if h : s.natReg e < n then (s.setReg a).erase ⟨s.natReg e, h⟩ else s.setReg a)) }
  | .setMember a e y z =>
    { t with pc := if h : s.natReg e < n then
        (if (⟨s.natReg e, h⟩ : Fin n) ∈ s.setReg a then y else z) else z }
  | .valueQuery d a => { t with realReg := Function.update s.realReg d (f (s.setReg a)) }
  | .indepQuery d j a =>
    { t with natReg := (Function.update s.natReg d (if h : s.natReg j < k then
        (if (M ⟨s.natReg j, h⟩).Indep (↑(s.setReg a) : Set (Fin n)) then 1 else 0)
       else 0)) }
  | .jump j => { t with pc := j }
  | .halt a => { t with halted := true, output := s.setReg a }

variable (code : List Instruction) (f : Finset (Fin n) → ℝ) (M : Fin k → Matroid (Fin n))

theorem step_exec {s : MachineState n} {op : Instruction} (h : s.halted = false)
    (hc : code[s.pc]? = some op) : machineStep code f M s = execOp f M op s := by
  unfold machineStep execOp
  simp only [h, hc]
  cases op <;> rfl

theorem cost_step (s : MachineState n) : (machineStep code f M s).cost ≤ s.cost + (n + 1) := by
  unfold machineStep
  by_cases h : s.halted
  · simp [h]
  · simp only [h]
    rcases hc : code[s.pc]? with _ | op
    · simp
    · cases op <;> simp

theorem cost_iter (t : ℕ) : ∀ s : MachineState n,
    ((machineStep code f M)^[t] s).cost ≤ s.cost + t * (n + 1) := by
  induction t with
  | zero => intro s; simp
  | succ t ih =>
    intro s
    rw [Function.iterate_succ_apply]
    have := ih (machineStep code f M s)
    have := cost_step code f M s
    rw [Nat.succ_mul]; omega

/-- `Reaches s B Q`: within at most `B` steps from `s` a state satisfying `Q` is reached. -/
def Reaches (s : MachineState n) (B : ℕ) (Q : MachineState n → Prop) : Prop :=
  ∃ t ≤ B, Q ((machineStep code f M)^[t] s)

variable {code f M}

theorem Reaches.now {s : MachineState n} {B : ℕ} {Q : MachineState n → Prop} (h : Q s) :
    Reaches code f M s B Q := ⟨0, Nat.zero_le _, h⟩

theorem Reaches.mono {s : MachineState n} {B B' : ℕ} {Q Q' : MachineState n → Prop}
    (h : Reaches code f M s B Q) (hB : B ≤ B') (hQ : ∀ s, Q s → Q' s) :
    Reaches code f M s B' Q' := by
  obtain ⟨t, ht, hq⟩ := h; exact ⟨t, ht.trans hB, hQ _ hq⟩

theorem Reaches.step {s : MachineState n} {B : ℕ} {Q : MachineState n → Prop}
    (h : Reaches code f M (machineStep code f M s) B Q) : Reaches code f M s (B + 1) Q := by
  obtain ⟨t, ht, hq⟩ := h
  exact ⟨t + 1, by omega, by rwa [Function.iterate_succ_apply]⟩

theorem Reaches.exec {s : MachineState n} {B : ℕ} {Q : MachineState n → Prop} {op : Instruction}
    (h0 : s.halted = false) (hc : code[s.pc]? = some op)
    (h : Reaches code f M (execOp f M op s) B Q) : Reaches code f M s (B + 1) Q := by
  apply Reaches.step; rwa [step_exec code f M h0 hc]

theorem Reaches.trans {s : MachineState n} {B1 B2 : ℕ} {Q R : MachineState n → Prop}
    (h1 : Reaches code f M s B1 Q) (h2 : ∀ s', Q s' → Reaches code f M s' B2 R) :
    Reaches code f M s (B1 + B2) R := by
  obtain ⟨t1, ht1, hq⟩ := h1
  obtain ⟨t2, ht2, hr⟩ := h2 _ hq
  refine ⟨t2 + t1, by omega, ?_⟩
  rwa [Function.iterate_add_apply]

open Classical in
noncomputable def indepVal (M : Fin k → Matroid (Fin n)) (x : ℕ) (X : Finset (Fin n)) : ℕ :=
  if h : x < k then (if (M ⟨x, h⟩).Indep (↑X : Set (Fin n)) then 1 else 0) else 0

def insV (X : Finset (Fin n)) (x : ℕ) : Finset (Fin n) :=
  if h : x < n then insert ⟨x, h⟩ X else X

def eraV (X : Finset (Fin n)) (x : ℕ) : Finset (Fin n) :=
  if h : x < n then X.erase ⟨x, h⟩ else X

section ops
variable (s : MachineState n)
@[simp] theorem eo_natConst (d v : ℕ) : execOp f M (.natConst d v) s =
    { s with pc := s.pc + 1, cost := s.cost + n + 1, natReg := Function.update s.natReg d v } := rfl
@[simp] theorem eo_natAdd (d a b : ℕ) : execOp f M (.natAdd d a b) s =
    { s with pc := s.pc + 1, cost := s.cost + n + 1, natReg := Function.update s.natReg d (s.natReg a + s.natReg b) } := rfl
@[simp] theorem eo_natBranch (a b y z : ℕ) : execOp f M (.natBranch a b y z) s =
    { s with pc := if s.natReg a ≤ s.natReg b then y else z, cost := s.cost + n + 1 } := rfl
@[simp] theorem eo_realConst (d : ℕ) (v : ℝ) : execOp f M (.realConst d v) s =
    { s with pc := s.pc + 1, cost := s.cost + n + 1, realReg := Function.update s.realReg d v } := rfl
@[simp] theorem eo_realCopy (d a : ℕ) : execOp f M (.realCopy d a) s =
    { s with pc := s.pc + 1, cost := s.cost + n + 1, realReg := Function.update s.realReg d (s.realReg a) } := rfl
@[simp] theorem eo_realAdd (d a b : ℕ) : execOp f M (.realAdd d a b) s =
    { s with pc := s.pc + 1, cost := s.cost + n + 1, realReg := Function.update s.realReg d (s.realReg a + s.realReg b) } := rfl
@[simp] theorem eo_realMul (d a b : ℕ) : execOp f M (.realMul d a b) s =
    { s with pc := s.pc + 1, cost := s.cost + n + 1, realReg := Function.update s.realReg d (s.realReg a * s.realReg b) } := rfl
@[simp] theorem eo_realDiv (d a b : ℕ) : execOp f M (.realDiv d a b) s =
    { s with pc := s.pc + 1, cost := s.cost + n + 1, realReg := Function.update s.realReg d (s.realReg a / s.realReg b) } := rfl
@[simp] theorem eo_realBranch (a b y z : ℕ) : execOp f M (.realBranch a b y z) s =
    { s with pc := if s.realReg a ≤ s.realReg b then y else z, cost := s.cost + n + 1 } := rfl
@[simp] theorem eo_setEmpty (d : ℕ) : execOp f M (.setEmpty d) s =
    { s with pc := s.pc + 1, cost := s.cost + n + 1, setReg := Function.update s.setReg d ∅ } := rfl
@[simp] theorem eo_setCopy (d a : ℕ) : execOp f M (.setCopy d a) s =
    { s with pc := s.pc + 1, cost := s.cost + n + 1, setReg := Function.update s.setReg d (s.setReg a) } := rfl
@[simp] theorem eo_setInsert (d a e : ℕ) : execOp f M (.setInsert d a e) s =
    { s with pc := s.pc + 1, cost := s.cost + n + 1, setReg := Function.update s.setReg d (insV (s.setReg a) (s.natReg e)) } := rfl
@[simp] theorem eo_setErase (d a e : ℕ) : execOp f M (.setErase d a e) s =
    { s with pc := s.pc + 1, cost := s.cost + n + 1, setReg := Function.update s.setReg d (eraV (s.setReg a) (s.natReg e)) } := rfl
@[simp] theorem eo_valueQuery (d a : ℕ) : execOp f M (.valueQuery d a) s =
    { s with pc := s.pc + 1, cost := s.cost + n + 1, realReg := Function.update s.realReg d (f (s.setReg a)) } := rfl
@[simp] theorem eo_indepQuery (d j a : ℕ) : execOp f M (.indepQuery d j a) s =
    { s with pc := s.pc + 1, cost := s.cost + n + 1, natReg := Function.update s.natReg d (indepVal M (s.natReg j) (s.setReg a)) } := rfl
@[simp] theorem eo_jump (j : ℕ) : execOp f M (.jump j) s =
    { s with pc := j, cost := s.cost + n + 1 } := rfl
@[simp] theorem eo_halt (a : ℕ) : execOp f M (.halt a) s =
    { s with pc := s.pc + 1, cost := s.cost + n + 1, halted := true, output := s.setReg a } := rfl
end ops

theorem indepVal_pos {M : Fin k → Matroid (Fin n)} {x : ℕ} {X : Finset (Fin n)} (hx : x < k)
    (h : (M ⟨x, hx⟩).Indep (↑X : Set (Fin n))) : indepVal M x X = 1 := by
  simp [indepVal, hx, h]

theorem indepVal_neg {M : Fin k → Matroid (Fin n)} {x : ℕ} {X : Finset (Fin n)} (hx : x < k)
    (h : ¬ (M ⟨x, hx⟩).Indep (↑X : Set (Fin n))) : indepVal M x X = 0 := by
  simp [indepVal, hx, h]

end Generic

end LSVAlgo


namespace LSVAlgo
open LeeSviridenkoVondrak.LocalSearch

section Generic
variable {n k : ℕ} {code : List Instruction} {f : Finset (Fin n) → ℝ} {M : Fin k → Matroid (Fin n)}

theorem Reaches.at {s : MachineState n} {B : ℕ} {Q : MachineState n → Prop} {op : Instruction}
    {p : ℕ} (h0 : s.halted = false) (hp : s.pc = p) (hc : code[p]? = some op)
    (h : Reaches code f M (execOp f M op s) (B - 1) Q) (hB : 1 ≤ B := by omega) :
    Reaches code f M s B Q :=
  (Reaches.exec h0 (hp ▸ hc) h).mono (by omega) (fun _ h => h)

theorem feas_loop (a fail : ℕ)
    (hc0 : code[a]? = some (.natBranch 6 5 (a+5) (a+1)))
    (hc1 : code[a+1]? = some (.indepQuery 3 5 1))
    (hc2 : code[a+2]? = some (.natBranch 3 1 fail (a+3)))
    (hc3 : code[a+3]? = some (.natAdd 5 5 2))
    (hc4 : code[a+4]? = some (.jump a)) :
    ∀ m j (s : MachineState n), k - j = m → s.pc = a → s.halted = false → s.natReg 6 = k →
      s.natReg 1 = 0 → s.natReg 2 = 1 → s.natReg 5 = j →
      (∀ j' : Fin k, j'.val < j → (M j').Indep ↑(s.setReg 1)) →
      Reaches code f M s (5 * m + 1) (fun s' => s'.halted = false ∧ s'.realReg = s.realReg ∧
        s'.setReg = s.setReg ∧ (∀ r, r ≠ 3 → r ≠ 5 → s'.natReg r = s.natReg r) ∧
        ((CommonIndependent M (s.setReg 1) ∧ s'.pc = a + 5) ∨
         (¬ CommonIndependent M (s.setReg 1) ∧ s'.pc = fail))) := by
  intro m
  induction m with
  | zero =>
    intro j s hm hpc h0 h6 h1 h2 h5 hind
    apply Reaches.at h0 hpc hc0
    apply Reaches.now
    refine ⟨h0, rfl, rfl, fun r _ _ => rfl, Or.inl ⟨fun j' => hind j' (by omega), ?_⟩⟩
    simp [h6, h5]; omega
  | succ m ih =>
    intro j s hm hpc h0 h6 h1 h2 h5 hind
    have hjk : j < k := by omega
    have hkj : ¬ k ≤ j := by omega
    apply Reaches.at h0 hpc hc0
    refine Reaches.at (p := a + 1) (by simp [h0]) (by simp only [eo_natAdd, eo_jump, eo_indepQuery, eo_natBranch]; rw [h6, h5, if_neg (by omega)]) hc1 ?_
    by_cases hI : (M ⟨j, hjk⟩).Indep ↑(s.setReg 1)
    · refine Reaches.at (p := a + 2) (by simp [h0, h1, h2, h5, h6, hkj, indepVal_pos hjk hI, Function.update_apply]) (by simp [h0, h1, h2, h5, h6, hkj, indepVal_pos hjk hI, Function.update_apply]) hc2 ?_
      refine Reaches.at (p := a + 3) (by simp [h0, h1, h2, h5, h6, hkj, indepVal_pos hjk hI, Function.update_apply])
        (by simp [h0, h1, h2, h5, h6, hkj, indepVal_pos hjk hI, Function.update_apply]) hc3 ?_
      refine Reaches.at (p := a + 4) (by simp [h0, h1, h2, h5, h6, hkj, indepVal_pos hjk hI, Function.update_apply]) (by simp [h0, h1, h2, h5, h6, hkj, indepVal_pos hjk hI, Function.update_apply]) hc4 ?_
      refine (ih (j + 1) _ (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_).mono (by omega) ?_
      · simp
      · simp [h0]
      · simp [Function.update_apply, h6]
      · simp [Function.update_apply, h1]
      · simp [Function.update_apply, h2]
      · simp [Function.update_apply, h5, h2]
      · intro j' hj'
        simp only [eo_natAdd, eo_jump, eo_indepQuery, eo_natBranch]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with h' | h'
        · exact hind j' h'
        · have : j' = ⟨j, hjk⟩ := Fin.ext h'
          subst this; exact hI
      rintro s' ⟨g0, g1, g2, g3, g4⟩
      refine ⟨g0, by rw [g1]; simp, by rw [g2]; simp, ?_, ?_⟩
      · intro r hr3 hr5; rw [g3 r hr3 hr5]; simp [Function.update_apply, hr3, hr5]
      · simpa [execOp] using g4
    · refine Reaches.at (p := a + 2) (by simp [h0]) (by simp [h6, h5, hkj]) hc2 ?_
      apply Reaches.now
      refine ⟨by simp [h0], by simp, by simp, ?_, Or.inr ⟨?_, ?_⟩⟩
      · intro r hr3 hr5; simp [Function.update_apply, hr3, hr5]
      · intro hC; exact hI (hC ⟨j, hjk⟩)
      · simp [h5, indepVal_neg hjk hI, h1]
end Generic
end LSVAlgo


namespace LSVAlgo
open LeeSviridenkoVondrak.LocalSearch

def fixedInstr (k : ℕ) (ε K1 : ℝ) : ℕ → Instruction
  | 0 => .natConst 2 1
  | 1 => .natConst 6 k
  | 2 => .realConst 4 1
  | 3 => .realConst 5 ε
  | 4 => .realConst 6 K1
  | 5 => .natBranch 0 4 9 6
  | 6 => .realAdd 3 3 4
  | 7 => .natAdd 4 4 2
  | 8 => .jump 5
  | 9 => .realMul 7 3 6
  | 10 => .realDiv 7 5 7
  | 11 => .realAdd 7 4 7
  | 12 => .natConst 4 0
  | 13 => .natBranch 0 4 28 14
  | 14 => .setEmpty 1
  | 15 => .setInsert 1 1 4
  | 16 => .natConst 5 0
  | 17 => .natBranch 6 5 22 18
  | 18 => .indepQuery 3 5 1
  | 19 => .natBranch 3 1 26 20
  | 20 => .natAdd 5 5 2
  | 21 => .jump 17
  | 22 => .valueQuery 2 1
  | 23 => .realBranch 2 0 26 24
  | 24 => .setCopy 0 1
  | 25 => .realCopy 0 2
  | 26 => .natAdd 4 4 2
  | 27 => .jump 13
  | 28 => .realBranch 0 8 29 30
  | 29 => .halt 0
  | _ => .realMul 1 7 0

/-- feasibility/value block, offset `r` from `fb = 32 + 2L`. -/
def fbInstr (L : ℕ) : ℕ → Instruction
  | 0 => .natConst 5 0
  | 1 => .natBranch 6 5 (32 + 2 * L + 6) (32 + 2 * L + 2)
  | 2 => .indepQuery 3 5 1
  | 3 => .natBranch 3 1 (43 + 2 * L) (32 + 2 * L + 4)
  | 4 => .natAdd 5 5 2
  | 5 => .jump (32 + 2 * L + 1)
  | 6 => .valueQuery 2 1
  | 7 => .realBranch 1 2 (32 + 2 * L + 8) (43 + 2 * L)
  | 8 => .setCopy 0 1
  | 9 => .realCopy 0 2
  | _ => .jump 30

/-- odometer block for digit `i`, offset `r`. -/
def incInstr (L i : ℕ) : ℕ → Instruction
  | 0 => .natBranch 0 (10 + i) (43 + 2 * L + 4 * i + 3) (43 + 2 * L + 4 * i + 1)
  | 1 => .natAdd (10 + i) (10 + i) 2
  | 2 => .jump (31 + L)
  | _ => .natConst (10 + i) 0

def instr (k L Lde : ℕ) (ε K1 : ℝ) (pc : ℕ) : Instruction :=
  if pc ≤ 30 then fixedInstr k ε K1 pc
  else if pc < 31 + L then .natConst (10 + (pc - 31)) 0
  else if pc = 31 + L then .setCopy 1 0
  else if pc < 32 + 2 * L then
    (if pc - (32 + L) < Lde then .setErase 1 1 (10 + (pc - (32 + L)))
      else .setInsert 1 1 (10 + (pc - (32 + L))))
  else if pc < 43 + 2 * L then fbInstr L (pc - (32 + 2 * L))
  else if pc < 43 + 6 * L then incInstr L ((pc - (43 + 2 * L)) / 4) ((pc - (43 + 2 * L)) % 4)
  else .halt 0

def prog (k L Lde : ℕ) (ε K1 : ℝ) : List Instruction :=
  List.ofFn (fun i : Fin (44 + 6 * L) => instr k L Lde ε K1 i)

section lookups
variable (k L Lde : ℕ) (ε K1 : ℝ)

theorem prog_get {pc : ℕ} (h : pc < 44 + 6 * L) :
    (prog k L Lde ε K1)[pc]? = some (instr k L Lde ε K1 pc) := by
  simp [prog, h]

theorem prog_fixed {pc : ℕ} (h : pc ≤ 30) :
    (prog k L Lde ε K1)[pc]? = some (fixedInstr k ε K1 pc) := by
  rw [prog_get _ _ _ _ _ (by omega)]; simp [instr, h]

theorem prog_reset {i : ℕ} (h : i < L) :
    (prog k L Lde ε K1)[31 + i]? = some (.natConst (10 + i) 0) := by
  rw [prog_get _ _ _ _ _ (by omega)]
  simp only [instr]
  rw [if_neg (by omega), if_pos (by omega)]
  simp

theorem prog_body : (prog k L Lde ε K1)[31 + L]? = some (.setCopy 1 0) := by
  rw [prog_get _ _ _ _ _ (by omega)]
  simp only [instr]
  rw [if_neg (by omega), if_neg (by omega)]; simp

theorem prog_build {i : ℕ} (h : i < L) :
    (prog k L Lde ε K1)[32 + L + i]? = some (if i < Lde then .setErase 1 1 (10 + i)
      else .setInsert 1 1 (10 + i)) := by
  rw [prog_get _ _ _ _ _ (by omega)]
  simp only [instr]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  have : 32 + L + i - (32 + L) = i := by omega
  rw [this]

theorem prog_fb {r : ℕ} (h : r ≤ 10) :
    (prog k L Lde ε K1)[32 + 2 * L + r]? = some (fbInstr L r) := by
  rw [prog_get _ _ _ _ _ (by omega)]
  simp only [instr]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  have : 32 + 2 * L + r - (32 + 2 * L) = r := by omega
  rw [this]

theorem prog_inc {i r : ℕ} (h : i < L) (hr : r < 4) :
    (prog k L Lde ε K1)[43 + 2 * L + 4 * i + r]? = some (incInstr L i r) := by
  rw [prog_get _ _ _ _ _ (by omega)]
  simp only [instr]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega)]
  have h1 : (43 + 2 * L + 4 * i + r - (43 + 2 * L)) / 4 = i := by omega
  have h2 : (43 + 2 * L + 4 * i + r - (43 + 2 * L)) % 4 = r := by omega
  rw [h1, h2]

theorem prog_final : (prog k L Lde ε K1)[43 + 6 * L]? = some (.halt 0) := by
  rw [prog_get _ _ _ _ _ (by omega)]
  simp only [instr]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

theorem pf0 : (prog k L Lde ε K1)[0]? = some (.natConst 2 1) := by
  rw [prog_fixed _ _ _ _ _ (by omega)]; rfl
theorem pf1 : (prog k L Lde ε K1)[1]? = some (.natConst 6 k) := by
  rw [prog_fixed _ _ _ _ _ (by omega)]; rfl
theorem pf2 : (prog k L Lde ε K1)[2]? = some (.realConst 4 1) := by
  rw [prog_fixed _ _ _ _ _ (by omega)]; rfl
theorem pf3 : (prog k L Lde ε K1)[3]? = some (.realConst 5 ε) := by
  rw [prog_fixed _ _ _ _ _ (by omega)]; rfl
theorem pf4 : (prog k L Lde ε K1)[4]? = some (.realConst 6 K1) := by
  rw [prog_fixed _ _ _ _ _ (by omega)]; rfl
theorem pf5 : (prog k L Lde ε K1)[5]? = some (.natBranch 0 4 9 6) := by
  rw [prog_fixed _ _ _ _ _ (by omega)]; rfl
theorem pf6 : (prog k L Lde ε K1)[6]? = some (.realAdd 3 3 4) := by
  rw [prog_fixed _ _ _ _ _ (by omega)]; rfl
theorem pf7 : (prog k L Lde ε K1)[7]? = some (.natAdd 4 4 2) := by
  rw [prog_fixed _ _ _ _ _ (by omega)]; rfl
theorem pf8 : (prog k L Lde ε K1)[8]? = some (.jump 5) := by
  rw [prog_fixed _ _ _ _ _ (by omega)]; rfl
theorem pf9 : (prog k L Lde ε K1)[9]? = some (.realMul 7 3 6) := by
  rw [prog_fixed _ _ _ _ _ (by omega)]; rfl
theorem pf10 : (prog k L Lde ε K1)[10]? = some (.realDiv 7 5 7) := by
  rw [prog_fixed _ _ _ _ _ (by omega)]; rfl
theorem pf11 : (prog k L Lde ε K1)[11]? = some (.realAdd 7 4 7) := by
  rw [prog_fixed _ _ _ _ _ (by omega)]; rfl
theorem pf12 : (prog k L Lde ε K1)[12]? = some (.natConst 4 0) := by
  rw [prog_fixed _ _ _ _ _ (by omega)]; rfl
theorem pf13 : (prog k L Lde ε K1)[13]? = some (.natBranch 0 4 28 14) := by
  rw [prog_fixed _ _ _ _ _ (by omega)]; rfl
theorem pf14 : (prog k L Lde ε K1)[14]? = some (.setEmpty 1) := by
  rw [prog_fixed _ _ _ _ _ (by omega)]; rfl
theorem pf15 : (prog k L Lde ε K1)[15]? = some (.setInsert 1 1 4) := by
  rw [prog_fixed _ _ _ _ _ (by omega)]; rfl
theorem pf16 : (prog k L Lde ε K1)[16]? = some (.natConst 5 0) := by
  rw [prog_fixed _ _ _ _ _ (by omega)]; rfl
theorem pf17 : (prog k L Lde ε K1)[17]? = some (.natBranch 6 5 22 18) := by
  rw [prog_fixed _ _ _ _ _ (by omega)]; rfl
theorem pf18 : (prog k L Lde ε K1)[18]? = some (.indepQuery 3 5 1) := by
  rw [prog_fixed _ _ _ _ _ (by omega)]; rfl
theorem pf19 : (prog k L Lde ε K1)[19]? = some (.natBranch 3 1 26 20) := by
  rw [prog_fixed _ _ _ _ _ (by omega)]; rfl
theorem pf20 : (prog k L Lde ε K1)[20]? = some (.natAdd 5 5 2) := by
  rw [prog_fixed _ _ _ _ _ (by omega)]; rfl
theorem pf21 : (prog k L Lde ε K1)[21]? = some (.jump 17) := by
  rw [prog_fixed _ _ _ _ _ (by omega)]; rfl
theorem pf22 : (prog k L Lde ε K1)[22]? = some (.valueQuery 2 1) := by
  rw [prog_fixed _ _ _ _ _ (by omega)]; rfl
theorem pf23 : (prog k L Lde ε K1)[23]? = some (.realBranch 2 0 26 24) := by
  rw [prog_fixed _ _ _ _ _ (by omega)]; rfl
theorem pf24 : (prog k L Lde ε K1)[24]? = some (.setCopy 0 1) := by
  rw [prog_fixed _ _ _ _ _ (by omega)]; rfl
theorem pf25 : (prog k L Lde ε K1)[25]? = some (.realCopy 0 2) := by
  rw [prog_fixed _ _ _ _ _ (by omega)]; rfl
theorem pf26 : (prog k L Lde ε K1)[26]? = some (.natAdd 4 4 2) := by
  rw [prog_fixed _ _ _ _ _ (by omega)]; rfl
theorem pf27 : (prog k L Lde ε K1)[27]? = some (.jump 13) := by
  rw [prog_fixed _ _ _ _ _ (by omega)]; rfl
theorem pf28 : (prog k L Lde ε K1)[28]? = some (.realBranch 0 8 29 30) := by
  rw [prog_fixed _ _ _ _ _ (by omega)]; rfl
theorem pf29 : (prog k L Lde ε K1)[29]? = some (.halt 0) := by
  rw [prog_fixed _ _ _ _ _ (by omega)]; rfl
theorem pf30 : (prog k L Lde ε K1)[30]? = some (.realMul 1 7 0) := by
  rw [prog_fixed _ _ _ _ _ (by omega)]; rfl

end lookups
end LSVAlgo


namespace LSVAlgo
open LeeSviridenkoVondrak.LocalSearch

section PhaseA
variable {n k : ℕ} (L Lde : ℕ) (ε K1 : ℝ) (f : Finset (Fin n) → ℝ) (M : Fin k → Matroid (Fin n))

theorem loopA : ∀ m x (s : MachineState n), n - x = m → x ≤ n → s.pc = 5 → s.halted = false →
    s.natReg 0 = n → s.natReg 2 = 1 → s.natReg 4 = x → s.realReg 4 = 1 → s.realReg 3 = x →
    Reaches (prog k L Lde ε K1) f M s (4 * m + 1) (fun s' => s'.pc = 9 ∧ s'.halted = false ∧
      s'.realReg 3 = n ∧ (∀ r, r ≠ 4 → s'.natReg r = s.natReg r) ∧
      (∀ r, r ≠ 3 → s'.realReg r = s.realReg r) ∧ s'.setReg = s.setReg) := by
  intro m
  induction m with
  | zero =>
    intro x s hm hx hpc h0 hn h2 h4 hr4 hr3
    have hxn : x = n := by omega
    subst hxn
    refine Reaches.at h0 hpc (pf5 k L Lde ε K1) ?_
    apply Reaches.now
    refine ⟨by simp [hn, h4], by simp [h0], by simp [hr3], fun r _ => rfl, fun r _ => rfl, rfl⟩
  | succ m ih =>
    intro x s hm hx hpc h0 hn h2 h4 hr4 hr3
    have hxn : ¬ n ≤ x := by omega
    refine Reaches.at h0 hpc (pf5 k L Lde ε K1) ?_
    refine Reaches.at (p := 6) (by simp [h0]) (by simp [hn, h4, hxn]) (pf6 k L Lde ε K1) ?_
    refine Reaches.at (p := 7) (by simp [h0]) (by simp [hn, h4, hxn]) (pf7 k L Lde ε K1) ?_
    refine Reaches.at (p := 8) (by simp [h0]) (by simp [hn, h4, hxn]) (pf8 k L Lde ε K1) ?_
    refine (ih (x + 1) _ (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_).mono (by omega) ?_
    · simp
    · simp [h0]
    · simp [Function.update_apply, hn]
    · simp [Function.update_apply, h2]
    · simp [Function.update_apply, h4, h2]
    · simp [Function.update_apply, hr4]
    · simp [Function.update_apply, hr4, hr3]
    · rintro s' ⟨g0, g1, g2, g3, g4, g5⟩
      refine ⟨g0, g1, g2, ?_, ?_, ?_⟩
      · intro r hr; rw [g3 r hr]; simp [Function.update_apply, hr]
      · intro r hr; rw [g4 r hr]; simp [Function.update_apply, hr]
      · rw [g5]; simp

theorem phaseA : Reaches (prog k L Lde ε K1) f M (initialState n) (4 * n + 14) (fun s =>
    s.pc = 13 ∧ s.halted = false ∧ s.natReg 0 = n ∧ s.natReg 1 = 0 ∧ s.natReg 2 = 1 ∧
    s.natReg 6 = k ∧ s.realReg 4 = 1 ∧ s.realReg 8 = 0 ∧ s.realReg 7 = 1 + ε / (n * K1) ∧
    s.natReg 4 = 0 ∧ s.setReg 0 = ∅ ∧ s.realReg 0 = 0) := by
  have e : 4 * n + 14 = 5 + ((4 * n + 1) + 8) := by ring
  rw [e]
  refine Reaches.at (p := 0) (by simp [initialState]) (by simp [initialState]) (pf0 k L Lde ε K1) ?_
  refine Reaches.at (p := 1) (by simp [initialState]) (by simp [initialState]) (pf1 k L Lde ε K1) ?_
  refine Reaches.at (p := 2) (by simp [initialState]) (by simp [initialState]) (pf2 k L Lde ε K1) ?_
  refine Reaches.at (p := 3) (by simp [initialState]) (by simp [initialState]) (pf3 k L Lde ε K1) ?_
  refine Reaches.at (p := 4) (by simp [initialState]) (by simp [initialState]) (pf4 k L Lde ε K1) ?_
  refine Reaches.mono (B := (4 * n + 1) + 4) (Reaches.trans (loopA L Lde ε K1 f M n 0 _ (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_) (by omega) (fun _ h => h)
  · simp [initialState]
  · simp [initialState]
  · simp [initialState, Function.update_apply]
  · simp [initialState, Function.update_apply]
  · simp [initialState, Function.update_apply]
  · simp [initialState, Function.update_apply]
  · simp [initialState, Function.update_apply]
  · rintro s ⟨g0, g1, g2, g3, g4, g5⟩
    have q0 := g3 0 (by decide); have q1 := g3 1 (by decide); have q2 := g3 2 (by decide)
    have q6 := g3 6 (by decide)
    have r4 := g4 4 (by decide); have r5 := g4 5 (by decide); have r6 := g4 6 (by decide)
    have r8 := g4 8 (by decide); have r0 := g4 0 (by decide)
    simp [initialState, Function.update_apply] at q0 q1 q2 q6 r4 r5 r6 r8 r0
    refine Reaches.at (p := 9) g1 g0 (pf9 k L Lde ε K1) ?_
    refine Reaches.at (p := 10) (by simp [g1]) (by simp [g0]) (pf10 k L Lde ε K1) ?_
    refine Reaches.at (p := 11) (by simp [g1]) (by simp [g0]) (pf11 k L Lde ε K1) ?_
    refine Reaches.at (p := 12) (by simp [g1]) (by simp [g0]) (pf12 k L Lde ε K1) ?_
    apply Reaches.now
    refine ⟨by simp [g0, fixedInstr], by simp [g1], by simp [Function.update_apply, q0],
      by simp [Function.update_apply, q1], by simp [Function.update_apply, q2],
      by simp [Function.update_apply, q6], by simp [Function.update_apply, r4],
      by simp [Function.update_apply, r8], ?_, by simp [Function.update_apply],
      by simp [g5, initialState], by simp [Function.update_apply, r0]⟩
    simp [Function.update_apply, r4, r5, r6, g2]

end PhaseA
end LSVAlgo


namespace LSVAlgo
open LeeSviridenkoVondrak.LocalSearch

section PhaseB
variable {n k : ℕ} (L Lde : ℕ) (ε K1 : ℝ) (f : Finset (Fin n) → ℝ) (M : Fin k → Matroid (Fin n))

def GoodC (ε K1 : ℝ) (s : MachineState n) : Prop :=
  s.halted = false ∧ s.natReg 0 = n ∧ s.natReg 1 = 0 ∧ s.natReg 2 = 1 ∧ s.natReg 6 = k ∧
    s.realReg 4 = 1 ∧ s.realReg 8 = 0 ∧ s.realReg 7 = 1 + ε / (n * K1)

def Best (x : ℕ) (S : Finset (Fin n)) (v : ℝ) : Prop :=
  (S = ∅ ∧ v = 0 ∨ ∃ y : Fin n, S = {y} ∧ CommonIndependent M {y} ∧ v = f {y} ∧ 0 < v) ∧
    ∀ y : Fin n, y.val < x → CommonIndependent M {y} → f {y} ≤ v

theorem iterB (x : ℕ) (hx : x < n) (s : MachineState n) (hpc : s.pc = 13)
    (hG : GoodC (k := k) ε K1 s) (h4 : s.natReg 4 = x)
    (hB : Best f M x (s.setReg 0) (s.realReg 0)) :
    Reaches (prog k L Lde ε K1) f M s (5 * k + 11) (fun s' => s'.pc = 13 ∧
      GoodC (k := k) ε K1 s' ∧ s'.natReg 4 = x + 1 ∧ Best f M (x + 1) (s'.setReg 0) (s'.realReg 0)) := by
  obtain ⟨h0, hn, h1, h2, h6, hr4, hr8, hr7⟩ := hG
  have hxn : ¬ n ≤ x := by omega
  refine Reaches.at h0 hpc (pf13 k L Lde ε K1) ?_
  refine Reaches.at (p := 14) (by simp [h0]) (by simp [hn, h4, hxn]) (pf14 k L Lde ε K1) ?_
  refine Reaches.at (p := 15) (by simp [h0]) (by simp [hn, h4, hxn]) (pf15 k L Lde ε K1) ?_
  refine Reaches.at (p := 16) (by simp [h0]) (by simp [hn, h4, hxn]) (pf16 k L Lde ε K1) ?_
  refine Reaches.mono (B := (5 * k + 1) + 6) (Reaches.trans (feas_loop 17 26 ?_ ?_ ?_ ?_ ?_ k 0 _ (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_) (by omega) (fun _ h => h)
  · rw [prog_fixed _ _ _ _ _ (by omega)]; rfl
  · rw [prog_fixed _ _ _ _ _ (by omega)]; rfl
  · rw [prog_fixed _ _ _ _ _ (by omega)]; rfl
  · rw [prog_fixed _ _ _ _ _ (by omega)]; rfl
  · rw [prog_fixed _ _ _ _ _ (by omega)]; rfl
  · simp [hn, h4, hxn]
  · simp [h0]
  · simp [Function.update_apply, h6]
  · simp [Function.update_apply, h1]
  · simp [Function.update_apply, h2]
  · simp [Function.update_apply]
  · intro j' hj'; exact absurd hj' (Nat.not_lt_zero _)
  rintro s' ⟨g0, gR, gS, gN, hcase⟩
  simp only [eo_natConst, eo_setInsert, eo_setEmpty, eo_natBranch] at gR gS gN hcase
  have hT : s'.setReg 1 = {(⟨x, hx⟩ : Fin n)} := by
    rw [gS]; simp [Function.update_apply, insV, h4, hx]
  rw [← gS, hT] at hcase
  have e0 : s'.setReg 0 = s.setReg 0 := by rw [gS]; simp [Function.update_apply]
  have e0r : s'.realReg = s.realReg := gR
  have n0 : s'.natReg 0 = n := by rw [gN 0 (by decide) (by decide)]; simp [Function.update_apply, hn]
  have n1 : s'.natReg 1 = 0 := by rw [gN 1 (by decide) (by decide)]; simp [Function.update_apply, h1]
  have n2 : s'.natReg 2 = 1 := by rw [gN 2 (by decide) (by decide)]; simp [Function.update_apply, h2]
  have n4 : s'.natReg 4 = x := by rw [gN 4 (by decide) (by decide)]; simp [Function.update_apply, h4]
  have n6 : s'.natReg 6 = k := by rw [gN 6 (by decide) (by decide)]; simp [Function.update_apply, h6]
  rcases hcase with ⟨hC, hpc'⟩ | ⟨hC, hpc'⟩
  · -- feasible singleton: pc 22
    refine Reaches.at (p := 22) g0 hpc' (pf22 k L Lde ε K1) ?_
    by_cases hv : f {(⟨x, hx⟩ : Fin n)} ≤ s.realReg 0
    · refine Reaches.at (p := 23) (by simp [g0]) (by simp [hpc']) (pf23 k L Lde ε K1) ?_
      refine Reaches.at (p := 26) (by simp [g0]) (by simp [Function.update_apply, hT, e0r, hv]) (pf26 k L Lde ε K1) ?_
      refine Reaches.at (p := 27) (by simp [g0]) (by simp [Function.update_apply, hT, e0r, hv]) (pf27 k L Lde ε K1) ?_
      apply Reaches.now
      refine ⟨by simp, ⟨by simp [g0], by simp [Function.update_apply, n0],
        by simp [Function.update_apply, n1], by simp [Function.update_apply, n2],
        by simp [Function.update_apply, n6], by simp [Function.update_apply, e0r, hr4],
        by simp [Function.update_apply, e0r, hr8], by simp [Function.update_apply, e0r, hr7]⟩,
        by simp [Function.update_apply, n4, n2], ?_⟩
      simp only [eo_natAdd, eo_jump, eo_realBranch, eo_valueQuery, Function.update_apply]
      simp only [show (2:ℕ) ≠ 0 by decide, if_false, e0, e0r]
      refine ⟨hB.1, fun y hy hyC => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hy with hy | hy
      · exact hB.2 y hy hyC
      · have : y = ⟨x, hx⟩ := Fin.ext hy
        subst this; exact hv
    · refine Reaches.at (p := 23) (by simp [g0]) (by simp [hpc']) (pf23 k L Lde ε K1) ?_
      refine Reaches.at (p := 24) (by simp [g0]) (by simp [Function.update_apply, hT, e0r, hv]) (pf24 k L Lde ε K1) ?_
      refine Reaches.at (p := 25) (by simp [g0]) (by simp [Function.update_apply, hT, e0r, hv]) (pf25 k L Lde ε K1) ?_
      refine Reaches.at (p := 26) (by simp [g0]) (by simp [Function.update_apply, hT, e0r, hv]) (pf26 k L Lde ε K1) ?_
      refine Reaches.at (p := 27) (by simp [g0]) (by simp [Function.update_apply, hT, e0r, hv]) (pf27 k L Lde ε K1) ?_
      apply Reaches.now
      refine ⟨by simp, ⟨by simp [g0], by simp [Function.update_apply, n0],
        by simp [Function.update_apply, n1], by simp [Function.update_apply, n2],
        by simp [Function.update_apply, n6], by simp [Function.update_apply, e0r, hr4],
        by simp [Function.update_apply, e0r, hr8], by simp [Function.update_apply, e0r, hr7]⟩,
        by simp [Function.update_apply, n4, n2], ?_⟩
      simp only [eo_natAdd, eo_jump, eo_realBranch, eo_valueQuery, eo_setCopy, eo_realCopy,
        Function.update_apply]
      simp only [show (2:ℕ) ≠ 0 by decide, if_false, if_true, hT, e0r]
      push_neg at hv
      have hpos : 0 < f {(⟨x, hx⟩ : Fin n)} := by
        rcases hB.1 with ⟨_, hv0⟩ | ⟨y, _, _, _, hy⟩
        · rw [← hv0]; exact hv
        · linarith
      refine ⟨Or.inr ⟨⟨x, hx⟩, rfl, hC, rfl, hpos⟩, fun y hy hyC => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hy with hy | hy
      · exact (hB.2 y hy hyC).trans hv.le
      · have : y = ⟨x, hx⟩ := Fin.ext hy
        subst this; exact le_rfl
  · -- infeasible: pc 26
    refine Reaches.at (p := 26) g0 hpc' (pf26 k L Lde ε K1) ?_
    refine Reaches.at (p := 27) (by simp [g0]) (by simp [hpc']) (pf27 k L Lde ε K1) ?_
    apply Reaches.now
    refine ⟨by simp, ⟨by simp [g0], by simp [Function.update_apply, n0],
      by simp [Function.update_apply, n1], by simp [Function.update_apply, n2],
      by simp [Function.update_apply, n6], by simp [Function.update_apply, e0r, hr4],
      by simp [Function.update_apply, e0r, hr8], by simp [Function.update_apply, e0r, hr7]⟩,
      by simp [Function.update_apply, n4, n2], ?_⟩
    simp only [eo_natAdd, eo_jump]
    rw [e0, e0r]
    refine ⟨hB.1, fun y hy hyC => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hy with hy | hy
    · exact hB.2 y hy hyC
    · have : y = ⟨x, hx⟩ := Fin.ext hy
      subst this; exact absurd hyC hC

end PhaseB
end LSVAlgo

namespace LSVAlgo
open LeeSviridenkoVondrak.LocalSearch
section PhaseB2
variable {n k : ℕ} (L Lde : ℕ) (ε K1 : ℝ) (f : Finset (Fin n) → ℝ) (M : Fin k → Matroid (Fin n))

theorem loopB : ∀ m x (s : MachineState n), n - x = m → x ≤ n → s.pc = 13 →
    GoodC (k := k) ε K1 s → s.natReg 4 = x → Best f M x (s.setReg 0) (s.realReg 0) →
    Reaches (prog k L Lde ε K1) f M s (m * (5 * k + 11) + 1) (fun s' => s'.pc = 28 ∧
      GoodC (k := k) ε K1 s' ∧ Best f M n (s'.setReg 0) (s'.realReg 0)) := by
  intro m
  induction m with
  | zero =>
    intro x s hm hx hpc hG h4 hB
    have hxn : x = n := by omega
    subst hxn
    obtain ⟨h0, hn, h1, h2, h6, hr4, hr8, hr7⟩ := hG
    refine Reaches.at h0 hpc (pf13 k L Lde ε K1) ?_
    apply Reaches.now
    exact ⟨by simp [hn, h4], ⟨h0, hn, h1, h2, h6, hr4, hr8, hr7⟩, hB⟩
  | succ m ih =>
    intro x s hm hx hpc hG h4 hB
    have hxn : x < n := by omega
    refine Reaches.mono (Reaches.trans (B2 := m * (5 * k + 11) + 1) (iterB L Lde ε K1 f M x hxn s hpc hG h4 hB) ?_) (by
      simp only [Nat.add_mul, one_mul]; omega) (fun _ h => h)
    rintro s' ⟨g1, g2, g3, g4⟩
    exact ih (x + 1) s' (by omega) (by omega) g1 g2 g3 g4

theorem endB (s : MachineState n) (hpc : s.pc = 28) (hG : GoodC (k := k) ε K1 s)
    (hB : Best f M n (s.setReg 0) (s.realReg 0)) :
    Reaches (prog k L Lde ε K1) f M s 2 (fun s' =>
      (s'.halted = true ∧ s'.output = ∅ ∧ ∀ y : Fin n, CommonIndependent M {y} → f {y} ≤ 0) ∨
      (s'.pc = 30 ∧ GoodC (k := k) ε K1 s' ∧ ∃ y : Fin n, s'.setReg 0 = {y} ∧ CommonIndependent M {y} ∧
        s'.realReg 0 = f {y} ∧ 0 < f {y} ∧ ∀ z : Fin n, CommonIndependent M {z} → f {z} ≤ f {y})) := by
  obtain ⟨h0, hn, h1, h2, h6, hr4, hr8, hr7⟩ := hG
  obtain ⟨hB1, hB2⟩ := hB
  refine Reaches.at h0 hpc (pf28 k L Lde ε K1) ?_
  by_cases hv : s.realReg 0 ≤ 0
  · refine Reaches.at (p := 29) (by simp [h0]) (by simp [hr8, hv]) (pf29 k L Lde ε K1) ?_
    apply Reaches.now
    left
    rcases hB1 with ⟨hS, hv0⟩ | ⟨y, _, _, _, hy⟩
    · refine ⟨by simp, by simp [hS], fun y hy => ?_⟩
      have := hB2 y y.2 hy; rw [hv0] at this; exact this
    · linarith
  · apply Reaches.now
    right
    rcases hB1 with ⟨hS, hv0⟩ | ⟨y, hS, hC, hvy, hy⟩
    · rw [hv0] at hv; exact absurd le_rfl hv
    · refine ⟨by simp [hr8, hv], ⟨by simp [h0], hn, h1, h2, h6, hr4, hr8, hr7⟩, y, hS, hC, hvy,
        hvy ▸ hy, fun z hz => hvy ▸ hB2 z z.2 hz⟩

end PhaseB2
end LSVAlgo


namespace LSVAlgo
open LeeSviridenkoVondrak.LocalSearch

def buildT {n : ℕ} (Lde : ℕ) (S : Finset (Fin n)) (D : ℕ → ℕ) : ℕ → Finset (Fin n)
  | 0 => S
  | i + 1 => if i < Lde then eraV (buildT Lde S D i) (D i) else insV (buildT Lde S D i) (D i)

theorem buildT_congr {n : ℕ} (Lde : ℕ) (S : Finset (Fin n)) (D E : ℕ → ℕ) :
    ∀ i, (∀ j, j < i → D j = E j) → buildT Lde S D i = buildT Lde S E i := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro h
    simp only [buildT]
    rw [ih (fun j hj => h j (by omega)), h i (by omega)]

section PhaseC
variable {n k : ℕ} (L Lde : ℕ) (ε K1 : ℝ) (f : Finset (Fin n) → ℝ) (M : Fin k → Matroid (Fin n))

def AtDigits (L : ℕ) (s : MachineState n) (D : ℕ → ℕ) : Prop := ∀ i, i < L → s.natReg (10 + i) = D i

theorem buildLoop (S : Finset (Fin n)) (D : ℕ → ℕ) : ∀ m i (s : MachineState n), L - i = m → i ≤ L →
    s.pc = 32 + L + i → s.halted = false → s.setReg 1 = buildT Lde S D i → AtDigits L s D →
    Reaches (prog k L Lde ε K1) f M s m (fun s' => s'.pc = 32 + 2 * L ∧ s'.halted = false ∧
      s'.natReg = s.natReg ∧ s'.realReg = s.realReg ∧ (∀ r, r ≠ 1 → s'.setReg r = s.setReg r) ∧
      s'.setReg 1 = buildT Lde S D L) := by
  intro m
  induction m with
  | zero =>
    intro i s hm hi hpc h0 hT hD
    have : i = L := by omega
    subst this
    exact Reaches.now ⟨by rw [hpc]; ring, h0, rfl, rfl, fun _ _ => rfl, hT⟩
  | succ m ih =>
    intro i s hm hi hpc h0 hT hD
    have hiL : i < L := by omega
    refine Reaches.at h0 hpc (prog_build k L Lde ε K1 hiL) ?_
    refine (ih (i + 1) _ (by omega) (by omega) ?_ ?_ ?_ ?_).mono (by omega) ?_
    · split_ifs <;> simp [hpc] <;> ring
    · split_ifs <;> simp [h0]
    · split_ifs with h <;> simp [buildT, h, hT, hD i hiL]
    · intro j hj; split_ifs <;> simp [hD j hj]
    · rintro s' ⟨g0, g1, g2, g3, g4, g5⟩
      refine ⟨g0, g1, ?_, ?_, ?_, g5⟩
      · rw [g2]; split_ifs <;> simp
      · rw [g3]; split_ifs <;> simp
      · intro r hr; rw [g4 r hr]; split_ifs <;> simp [Function.update_apply, hr]

theorem fbA : (prog k L Lde ε K1)[32 + 2 * L]? = some (.natConst 5 0) := by
  rw [show 32 + 2 * L = 32 + 2 * L + 0 by omega, prog_fb _ _ _ _ _ (by omega)]
  simp [fbInstr] <;> omega
theorem fl0 : (prog k L Lde ε K1)[33 + 2 * L]? = some (.natBranch 6 5 (33 + 2 * L + 5) (33 + 2 * L + 1)) := by
  rw [show 33 + 2 * L = 32 + 2 * L + 1 by omega, prog_fb _ _ _ _ _ (by omega)]
  simp [fbInstr] <;> omega
theorem fl1 : (prog k L Lde ε K1)[33 + 2 * L + 1]? = some (.indepQuery 3 5 1) := by
  rw [show 33 + 2 * L + 1 = 32 + 2 * L + 2 by omega, prog_fb _ _ _ _ _ (by omega)]
  simp [fbInstr] <;> omega
theorem fl2 : (prog k L Lde ε K1)[33 + 2 * L + 2]? = some (.natBranch 3 1 (43 + 2 * L) (33 + 2 * L + 3)) := by
  rw [show 33 + 2 * L + 2 = 32 + 2 * L + 3 by omega, prog_fb _ _ _ _ _ (by omega)]
  simp [fbInstr] <;> omega
theorem fl3 : (prog k L Lde ε K1)[33 + 2 * L + 3]? = some (.natAdd 5 5 2) := by
  rw [show 33 + 2 * L + 3 = 32 + 2 * L + 4 by omega, prog_fb _ _ _ _ _ (by omega)]
  simp [fbInstr] <;> omega
theorem fl4 : (prog k L Lde ε K1)[33 + 2 * L + 4]? = some (.jump (33 + 2 * L)) := by
  rw [show 33 + 2 * L + 4 = 32 + 2 * L + 5 by omega, prog_fb _ _ _ _ _ (by omega)]
  simp [fbInstr] <;> omega
theorem fv6 : (prog k L Lde ε K1)[33 + 2 * L + 5]? = some (.valueQuery 2 1) := by
  rw [show 33 + 2 * L + 5 = 32 + 2 * L + 6 by omega, prog_fb _ _ _ _ _ (by omega)]
  simp [fbInstr] <;> omega
theorem fv7 : (prog k L Lde ε K1)[39 + 2 * L]? = some (.realBranch 1 2 (40 + 2 * L) (43 + 2 * L)) := by
  rw [show 39 + 2 * L = 32 + 2 * L + 7 by omega, prog_fb _ _ _ _ _ (by omega)]
  simp [fbInstr] <;> omega
theorem fv8 : (prog k L Lde ε K1)[40 + 2 * L]? = some (.setCopy 0 1) := by
  rw [show 40 + 2 * L = 32 + 2 * L + 8 by omega, prog_fb _ _ _ _ _ (by omega)]
  simp [fbInstr] <;> omega
theorem fv9 : (prog k L Lde ε K1)[41 + 2 * L]? = some (.realCopy 0 2) := by
  rw [show 41 + 2 * L = 32 + 2 * L + 9 by omega, prog_fb _ _ _ _ _ (by omega)]
  simp [fbInstr] <;> omega
theorem fv10 : (prog k L Lde ε K1)[42 + 2 * L]? = some (.jump 30) := by
  rw [show 42 + 2 * L = 32 + 2 * L + 10 by omega, prog_fb _ _ _ _ _ (by omega)]
  simp [fbInstr] <;> omega


theorem bodyCheck (S : Finset (Fin n)) (fS thr : ℝ) (D : ℕ → ℕ) (s : MachineState n)
    (hpc : s.pc = 31 + L) (hG : GoodC (k := k) ε K1 s) (hS : s.setReg 0 = S) (hfS : s.realReg 0 = fS)
    (hthr : s.realReg 1 = thr) (hD : AtDigits L s D) :
    Reaches (prog k L Lde ε K1) f M s (L + 5 * k + 9) (fun s' =>
      (s'.pc = 30 ∧ GoodC (k := k) ε K1 s' ∧ s'.setReg 0 = buildT Lde S D L ∧
        s'.realReg 0 = f (buildT Lde S D L) ∧ CommonIndependent M (buildT Lde S D L) ∧
        thr ≤ f (buildT Lde S D L)) ∨
      (s'.pc = 43 + 2 * L ∧ GoodC (k := k) ε K1 s' ∧ s'.setReg 0 = S ∧ s'.realReg 0 = fS ∧
        s'.realReg 1 = thr ∧ AtDigits L s' D ∧
        ¬ (CommonIndependent M (buildT Lde S D L) ∧ thr ≤ f (buildT Lde S D L)))) := by
  obtain ⟨h0, hn, h1, h2, h6, hr4, hr8, hr7⟩ := hG
  refine Reaches.at h0 hpc (prog_body k L Lde ε K1) ?_
  refine Reaches.mono (B := L + ((5 * k + 1) + 7)) (Reaches.trans
    (buildLoop L Lde ε K1 f M S D L 0 _ (by omega) (by omega) ?_ ?_ ?_ ?_) ?_) (by omega) (fun _ h => h)
  · simp [hpc] <;> omega
  · simp [h0]
  · simp [buildT, hS]
  · intro j hj; simp [hD j hj]
  rintro s1 ⟨g0, g1, g2, g3, g4, g5⟩
  simp only [eo_setCopy] at g2 g3 g4
  refine Reaches.at (p := 32 + 2 * L) g1 g0 (fbA (k := k) L Lde ε K1) ?_
  refine Reaches.mono (B := (5 * k + 1) + 6) (Reaches.trans
    (feas_loop (33 + 2 * L) (43 + 2 * L) (fl0 (k := k) L Lde ε K1) (fl1 (k := k) L Lde ε K1) (fl2 (k := k) L Lde ε K1)
      (fl3 (k := k) L Lde ε K1) (fl4 (k := k) L Lde ε K1) k 0 _ (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_) (by omega)
      (fun _ h => h)
  · simp [g0]; ring
  · simp [g1]
  · simp [Function.update_apply, g2, h6]
  · simp [Function.update_apply, g2, h1]
  · simp [Function.update_apply, g2, h2]
  · simp [Function.update_apply]
  · intro j' hj'; exact absurd hj' (Nat.not_lt_zero _)
  rintro s2 ⟨k0, kR, kS, kN, hcase⟩
  simp only [eo_natConst] at kR kS kN hcase
  rw [g5] at hcase
  have e1 : s2.setReg 1 = buildT Lde S D L := by rw [kS, g5]
  have e0 : s2.setReg 0 = S := by
    rw [kS, g4 0 (by decide)]; simp [Function.update_apply, hS]
  have eR : s2.realReg = s.realReg := by rw [kR, g3]
  have eN : ∀ r, r ≠ 3 → r ≠ 5 → s2.natReg r = s.natReg r := by
    intro r hr3 hr5; rw [kN r hr3 hr5, g2]; simp [Function.update_apply, hr5]
  have hG2 : GoodC (k := k) ε K1 s2 := ⟨k0, by rw [eN 0 (by decide) (by decide), hn],
    by rw [eN 1 (by decide) (by decide), h1], by rw [eN 2 (by decide) (by decide), h2],
    by rw [eN 6 (by decide) (by decide), h6], by rw [eR, hr4], by rw [eR, hr8], by rw [eR, hr7]⟩
  have hD2 : AtDigits L s2 D := by
    intro i hi; rw [eN (10 + i) (by omega) (by omega), hD i hi]
  rcases hcase with ⟨hC, hpc2⟩ | ⟨hC, hpc2⟩
  · refine Reaches.at (p := 33 + 2 * L + 5) k0 hpc2 (fv6 (k := k) L Lde ε K1) ?_
    by_cases hv : thr ≤ f (buildT Lde S D L)
    · refine Reaches.at (p := 39 + 2 * L) (by simp [k0]) (by simp [hpc2]; ring) (fv7 (k := k) L Lde ε K1) ?_
      refine Reaches.at (p := 40 + 2 * L) (by simp [k0])
        (by simp [Function.update_apply, eR, hthr, e1, hv]) (fv8 (k := k) L Lde ε K1) ?_
      refine Reaches.at (p := 41 + 2 * L) (by simp [k0])
        (by simp [Function.update_apply, eR, hthr, e1, hv] <;> omega) (fv9 (k := k) L Lde ε K1) ?_
      refine Reaches.at (p := 42 + 2 * L) (by simp [k0])
        (by simp [Function.update_apply, eR, hthr, e1, hv] <;> omega) (fv10 (k := k) L Lde ε K1) ?_
      apply Reaches.now
      left
      obtain ⟨_, q0, q1, q2, q6, q4, q8, q7⟩ := hG2
      refine ⟨by simp, ⟨by simp [k0], by simp [q0], by simp [q1], by simp [q2], by simp [q6],
        by simp [Function.update_apply, q4], by simp [Function.update_apply, q8],
        by simp [Function.update_apply, q7]⟩, by simp [Function.update_apply, e1],
        by simp [Function.update_apply, e1], hC, hv⟩
    · refine Reaches.at (p := 39 + 2 * L) (by simp [k0]) (by simp [hpc2]; ring) (fv7 (k := k) L Lde ε K1) ?_
      apply Reaches.now
      right
      obtain ⟨_, q0, q1, q2, q6, q4, q8, q7⟩ := hG2
      refine ⟨by simp [Function.update_apply, eR, hthr, e1, hv], ⟨by simp [k0], by simp [q0], by simp [q1],
        by simp [q2], by simp [q6], by simp [Function.update_apply, q4], by simp [Function.update_apply, q8],
        by simp [Function.update_apply, q7]⟩, by simp [e0], by simp [Function.update_apply, eR, hfS],
        by simp [Function.update_apply, eR, hthr], fun i hi => by simp [hD2 i hi], fun h => hv h.2⟩
  · apply Reaches.now
    right
    exact ⟨hpc2, hG2, e0, by rw [eR, hfS], by rw [eR, hthr], hD2, fun h => hC h.1⟩

end PhaseC
end LSVAlgo


namespace LSVAlgo
open LeeSviridenkoVondrak.LocalSearch

section Odo
variable {n k : ℕ} (L Lde : ℕ) (ε K1 : ℝ) (f : Finset (Fin n) → ℝ) (M : Fin k → Matroid (Fin n))

theorem oc0 {i : ℕ} (h : i < L) : (prog k L Lde ε K1)[43 + 2 * L + 4 * i]? =
    some (.natBranch 0 (10 + i) (43 + 2 * L + 4 * i + 3) (43 + 2 * L + 4 * i + 1)) := by
  have := prog_inc k L Lde ε K1 h (r := 0) (by omega)
  simpa [incInstr] using this
theorem oc1 {i : ℕ} (h : i < L) : (prog k L Lde ε K1)[43 + 2 * L + 4 * i + 1]? =
    some (.natAdd (10 + i) (10 + i) 2) := by
  have := prog_inc k L Lde ε K1 h (r := 1) (by omega)
  simpa [incInstr] using this
theorem oc2 {i : ℕ} (h : i < L) : (prog k L Lde ε K1)[43 + 2 * L + 4 * i + 1 + 1]? =
    some (.jump (31 + L)) := by
  have := prog_inc k L Lde ε K1 h (r := 2) (by omega)
  simpa [incInstr] using this
theorem oc3 {i : ℕ} (h : i < L) : (prog k L Lde ε K1)[43 + 2 * L + 4 * i + 3]? =
    some (.natConst (10 + i) 0) := by
  have := prog_inc k L Lde ε K1 h (r := 3) (by omega)
  simpa [incInstr] using this

theorem GoodC_of {s s' : MachineState n} (h : GoodC (k := k) ε K1 s) (h0 : s'.halted = false)
    (hN : ∀ r, r < 10 → s'.natReg r = s.natReg r) (hR : s'.realReg = s.realReg) :
    GoodC (k := k) ε K1 s' := by
  obtain ⟨_, a0, a1, a2, a6, b4, b8, b7⟩ := h
  exact ⟨h0, by rw [hN 0 (by omega), a0], by rw [hN 1 (by omega), a1], by rw [hN 2 (by omega), a2],
    by rw [hN 6 (by omega), a6], by rw [hR, b4], by rw [hR, b8], by rw [hR, b7]⟩

def Improved (thr : ℝ) (s : MachineState n) : Prop :=
  s.pc = 30 ∧ GoodC (k := k) ε K1 s ∧ ∃ T, s.setReg 0 = T ∧ s.realReg 0 = f T ∧
    CommonIndependent M T ∧ thr ≤ f T

def W (n B0 : ℕ) : ℕ → ℕ
  | 0 => B0
  | i + 1 => (n + 1) * (W n B0 i + 3)

def PStmt (S : Finset (Fin n)) (fS thr : ℝ) (i : ℕ) : Prop :=
  ∀ (D : ℕ → ℕ) (s : MachineState n), s.pc = 31 + L → GoodC (k := k) ε K1 s → s.setReg 0 = S →
    s.realReg 0 = fS → s.realReg 1 = thr → AtDigits L s D → (∀ j, j < i → D j = 0) →
    (∀ j, j < L → D j ≤ n) →
    Reaches (prog k L Lde ε K1) f M s (W n (L + 5 * k + 9) i) (fun s' => Improved ε K1 f M thr s' ∨
      (s'.pc = 43 + 2 * L + 4 * i ∧ GoodC (k := k) ε K1 s' ∧ s'.setReg 0 = S ∧ s'.realReg 0 = fS ∧
        s'.realReg 1 = thr ∧ AtDigits L s' D ∧
        ∀ E : ℕ → ℕ, (∀ j, j < L → E j ≤ n) → (∀ j, i ≤ j → j < L → E j = D j) →
          ¬ (CommonIndependent M (buildT Lde S E L) ∧ thr ≤ f (buildT Lde S E L))))

theorem P0 (S : Finset (Fin n)) (fS thr : ℝ) : PStmt L Lde ε K1 f M S fS thr 0 := by
  intro D s hpc hG hS hfS hthr hD _ _
  refine (bodyCheck L Lde ε K1 f M S fS thr D s hpc hG hS hfS hthr hD).mono (by simp [W]) ?_
  rintro s' (⟨a1, a2, a3, a4, a5, a6⟩ | ⟨a1, a2, a3, a4, a5, a6, a7⟩)
  · exact Or.inl ⟨a1, a2, _, a3, a4, a5, a6⟩
  · refine Or.inr ⟨by rw [a1]; ring, a2, a3, a4, a5, a6, fun E _ hE => ?_⟩
    rw [buildT_congr Lde S E D L (fun j hj => hE j (Nat.zero_le _) hj)]
    exact a7


theorem Qc (S : Finset (Fin n)) (fS thr : ℝ) (i : ℕ) (hi : i < L)
    (hP : PStmt L Lde ε K1 f M S fS thr i) : ∀ c (D : ℕ → ℕ) (s : MachineState n), n - D i = c →
    D i ≤ n → s.pc = 31 + L → GoodC (k := k) ε K1 s → s.setReg 0 = S →
    s.realReg 0 = fS → s.realReg 1 = thr → AtDigits L s D → (∀ j, j < i → D j = 0) →
    (∀ j, j < L → D j ≤ n) →
    Reaches (prog k L Lde ε K1) f M s ((c + 1) * (W n (L + 5 * k + 9) i + 3))
      (fun s' => Improved ε K1 f M thr s' ∨
      (s'.pc = 43 + 2 * L + 4 * (i + 1) ∧ GoodC (k := k) ε K1 s' ∧ s'.setReg 0 = S ∧ s'.realReg 0 = fS ∧
        s'.realReg 1 = thr ∧ AtDigits L s' (Function.update D i 0) ∧
        ∀ E : ℕ → ℕ, (∀ j, j < L → E j ≤ n) → (∀ j, i < j → j < L → E j = D j) → D i ≤ E i →
          ¬ (CommonIndependent M (buildT Lde S E L) ∧ thr ≤ f (buildT Lde S E L)))) := by
  intro c
  induction c with
  | zero =>
    intro D s hc hDi hpc hG hS hfS hthr hD hz hb
    have hDn : D i = n := by omega
    refine Reaches.mono (Reaches.trans (B2 := 3) (hP D s hpc hG hS hfS hthr hD hz hb) ?_) (by ring_nf; omega)
      (fun _ h => h)
    rintro s1 (hI | ⟨a1, a2, a3, a4, a5, a6, a7⟩)
    · exact Reaches.now (Or.inl hI)
    have hG1 := a2
    obtain ⟨b0, b1, -, -, -, -, -, -⟩ := a2
    refine Reaches.at b0 a1 (oc0 (k := k) L Lde ε K1 hi) ?_
    refine Reaches.at (p := 43 + 2 * L + 4 * i + 3) (by simp [b0]) (by simp [b1, a6 i hi, hDn])
      (oc3 (k := k) L Lde ε K1 hi) ?_
    apply Reaches.now
    right
    refine ⟨by simp [b1, a6 i hi, hDn]; ring, GoodC_of ε K1 hG1 (by simp [b0]) (fun r hr => by
      simp [Function.update_apply]; intro h; omega) (by simp), by simp [a3], by simp [a4],
      by simp [a5], ?_, ?_⟩
    · intro j hj
      by_cases hji : j = i
      · subst hji; simp
      · simp [Function.update_apply, hji, a6 j hj]
    · intro E hE hEj hEi
      apply a7 E hE
      intro j hj hjL
      rcases Nat.lt_or_ge i j with h | h
      · exact hEj j h hjL
      · have : j = i := by omega
        subst this; have := hE j hjL; omega
  | succ c ih =>
    intro D s hc hDi hpc hG hS hfS hthr hD hz hb
    have hDn : D i < n := by omega
    refine Reaches.mono (Reaches.trans (B2 := 3 + (c + 1) * (W n (L + 5 * k + 9) i + 3))
      (hP D s hpc hG hS hfS hthr hD hz hb) ?_) (by ring_nf; omega) (fun _ h => h)
    rintro s1 (hI | ⟨a1, a2, a3, a4, a5, a6, a7⟩)
    · exact Reaches.now (Or.inl hI)
    have hG1 := a2
    obtain ⟨b0, b1, -, b2', -, -, -, -⟩ := a2
    refine Reaches.at b0 a1 (oc0 (k := k) L Lde ε K1 hi) ?_
    refine Reaches.at (p := 43 + 2 * L + 4 * i + 1) (by simp [b0])
      (by simp [b1, a6 i hi]; omega) (oc1 (k := k) L Lde ε K1 hi) ?_
    refine Reaches.at (p := 43 + 2 * L + 4 * i + 1 + 1) (by simp [b0])
      (by simp [b1, a6 i hi]; omega) (oc2 (k := k) L Lde ε K1 hi) ?_
    set D' := Function.update D i (D i + 1) with hD'
    refine Reaches.mono (ih D' _ (by simp [hD']; omega) (by simp [hD']; omega) (by simp)
      (GoodC_of ε K1 hG1 (by simp [b0]) (fun r hr => by
        simp [Function.update_apply]; intro h; omega) (by simp))
      (by simp [a3]) (by simp [a4]) (by simp [a5]) ?_ ?_ ?_) (by omega) ?_
    · intro j hj
      by_cases hji : j = i
      · subst hji; simp [hD', a6 j hj, b2']
      · have : 10 + j ≠ 10 + i := by omega
        simp [Function.update_apply, hD', hji, a6 j hj, this]
    · intro j hj; simp [hD', Function.update_apply, show j ≠ i by omega, hz j hj]
    · intro j hj
      by_cases hji : j = i
      · subst hji; simp [hD']; omega
      · simp [hD', Function.update_apply, hji, hb j hj]
    · rintro s' (hI | ⟨c1, c2, c3, c4, c5, c6, c7⟩)
      · exact Or.inl hI
      · refine Or.inr ⟨c1, c2, c3, c4, c5, ?_, ?_⟩
        · intro j hj; rw [c6 j hj]; simp [hD']
        · intro E hE hEj hEi
          rcases Nat.lt_or_ge (D i) (E i) with h | h
          · apply c7 E hE
            · intro j hj hjL; rw [hEj j hj hjL]; simp [hD', Function.update_apply, show j ≠ i by omega]
            · simp [hD']; omega
          · apply a7 E hE
            intro j hj hjL
            rcases Nat.lt_or_ge i j with h' | h'
            · exact hEj j h' hjL
            · have : j = i := by omega
              subst this; omega

theorem Pstep (S : Finset (Fin n)) (fS thr : ℝ) (i : ℕ) (hi : i < L)
    (hP : PStmt L Lde ε K1 f M S fS thr i) : PStmt L Lde ε K1 f M S fS thr (i + 1) := by
  intro D s hpc hG hS hfS hthr hD hz hb
  have hDi : D i = 0 := hz i (by omega)
  refine (Qc L Lde ε K1 f M S fS thr i hi hP (n - D i) D s rfl (by omega) hpc hG hS hfS hthr hD
    (fun j hj => hz j (by omega)) hb).mono (by simp [W, hDi]) ?_
  rintro s' (hI | ⟨c1, c2, c3, c4, c5, c6, c7⟩)
  · exact Or.inl hI
  · refine Or.inr ⟨c1, c2, c3, c4, c5, ?_, ?_⟩
    · intro j hj; rw [c6 j hj]
      by_cases hji : j = i
      · subst hji; simp [hDi]
      · simp [Function.update_apply, hji]
    · intro E hE hEj
      exact c7 E hE (fun j hj hjL => hEj j (by omega) hjL) (by omega)

theorem Pall (S : Finset (Fin n)) (fS thr : ℝ) : ∀ i, i ≤ L → PStmt L Lde ε K1 f M S fS thr i := by
  intro i
  induction i with
  | zero => intro _; exact P0 L Lde ε K1 f M S fS thr
  | succ i ih => intro h; exact Pstep L Lde ε K1 f M S fS thr i (by omega) (ih (by omega))

end Odo
end LSVAlgo


namespace LSVAlgo
open LeeSviridenkoVondrak.LocalSearch

section Round
variable {n k : ℕ} (L Lde : ℕ) (ε K1 : ℝ) (f : Finset (Fin n) → ℝ) (M : Fin k → Matroid (Fin n))

theorem resetLoop : ∀ m i (s : MachineState n), L - i = m → i ≤ L → s.pc = 31 + i →
    s.halted = false → (∀ j, j < i → s.natReg (10 + j) = 0) →
    Reaches (prog k L Lde ε K1) f M s m (fun s' => s'.pc = 31 + L ∧ s'.halted = false ∧
      (∀ r, r < 10 → s'.natReg r = s.natReg r) ∧ s'.realReg = s.realReg ∧ s'.setReg = s.setReg ∧
      ∀ j, j < L → s'.natReg (10 + j) = 0) := by
  intro m
  induction m with
  | zero =>
    intro i s hm hi hpc h0 hz
    have : i = L := by omega
    subst this
    exact Reaches.now ⟨hpc, h0, fun _ _ => rfl, rfl, rfl, hz⟩
  | succ m ih =>
    intro i s hm hi hpc h0 hz
    refine Reaches.at h0 hpc (prog_reset k L Lde ε K1 (i := i) (by omega)) ?_
    refine (ih (i + 1) _ (by omega) (by omega) (by simp [hpc]; ring) (by simp [h0]) ?_).mono
      (by omega) ?_
    · intro j hj
      by_cases hji : j = i
      · subst hji; simp
      · have : 10 + j ≠ 10 + i := by omega
        simp [Function.update_apply, this, hz j (by omega)]
    · rintro s' ⟨g0, g1, g2, g3, g4, g5⟩
      refine ⟨g0, g1, fun r hr => ?_, by rw [g3]; rfl, by rw [g4]; rfl, g5⟩
      rw [g2 r hr]; simp [Function.update_apply]; intro h; omega

theorem round (S : Finset (Fin n)) (s : MachineState n) (hpc : s.pc = 30)
    (hG : GoodC (k := k) ε K1 s) (hS : s.setReg 0 = S) (hfS : s.realReg 0 = f S) :
    Reaches (prog k L Lde ε K1) f M s (L + W n (L + 5 * k + 9) L + 2) (fun s' =>
      (s'.pc = 30 ∧ GoodC (k := k) ε K1 s' ∧ ∃ T, s'.setReg 0 = T ∧ s'.realReg 0 = f T ∧
        CommonIndependent M T ∧ (1 + ε / (n * K1)) * f S ≤ f T) ∨
      (s'.halted = true ∧ s'.output = S ∧ ∀ E : ℕ → ℕ, (∀ j, j < L → E j ≤ n) →
        ¬ (CommonIndependent M (buildT Lde S E L) ∧
          (1 + ε / (n * K1)) * f S ≤ f (buildT Lde S E L)))) := by
  have hG' := hG
  obtain ⟨h0, hn, h1, h2, h6, hr4, hr8, hr7⟩ := hG
  refine Reaches.at h0 hpc (pf30 k L Lde ε K1) ?_
  refine Reaches.mono (B := L + (W n (L + 5 * k + 9) L + 1)) (Reaches.trans
    (resetLoop L Lde ε K1 f M L 0 _ (by omega) (by omega) (by simp [hpc]) (by simp [h0])
      (fun j hj => absurd hj (Nat.not_lt_zero _))) ?_) (by omega) (fun _ h => h)
  rintro s1 ⟨g0, g1, g2, g3, g4, g5⟩
  simp only [eo_realMul] at g2 g3 g4
  have hG1 : GoodC (k := k) ε K1 s1 := by
    refine ⟨g1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [g2 0 (by omega)]; exact hn
    · rw [g2 1 (by omega)]; exact h1
    · rw [g2 2 (by omega)]; exact h2
    · rw [g2 6 (by omega)]; exact h6
    · rw [g3]; simp [Function.update_apply, hr4]
    · rw [g3]; simp [Function.update_apply, hr8]
    · rw [g3]; simp [Function.update_apply, hr7]
  have e0 : s1.setReg 0 = S := by rw [g4]; exact hS
  have ef : s1.realReg 0 = f S := by rw [g3]; simp [Function.update_apply, hfS]
  have et : s1.realReg 1 = (1 + ε / (n * K1)) * f S := by rw [g3]; simp [Function.update_apply, hfS, hr7]
  refine Reaches.mono (B := W n (L + 5 * k + 9) L + 1) (Reaches.trans
    (Pall L Lde ε K1 f M S (f S) ((1 + ε / (n * K1)) * f S) L le_rfl (fun _ => 0) s1 g0 hG1 e0 ef et
      (fun j hj => g5 j hj) (fun _ _ => rfl) (fun _ _ => Nat.zero_le _)) ?_) (by omega) (fun _ h => h)
  rintro s2 (⟨c1, c2, T, c3, c4, c5, c6⟩ | ⟨c1, c2, c3, c4, c5, c6, c7⟩)
  · exact Reaches.now (Or.inl ⟨c1, c2, T, c3, c4, c5, c6⟩)
  · refine Reaches.at c2.1 (c1.trans (by ring)) (prog_final k L Lde ε K1) ?_
    apply Reaches.now
    right
    exact ⟨by simp, by simp [c3], fun E hE => c7 E hE (fun j _ hj => absurd hj (by omega))⟩

end Round
end LSVAlgo


namespace LSVAlgo
open LeeSviridenkoVondrak.LocalSearch

section BuildRep
variable {n : ℕ}

open Classical in
noncomputable def ES (E : ℕ → ℕ) (a b : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun x => ∃ j, a ≤ j ∧ j < b ∧ E j = x.val)

theorem bt1 (Lde : ℕ) (S : Finset (Fin n)) (E : ℕ → ℕ) :
    ∀ i, i ≤ Lde → buildT Lde S E i = S \ ES E 0 i := by
  intro i
  induction i with
  | zero => intro _; ext x; simp [buildT, ES]
  | succ i ih =>
    intro hi
    simp only [buildT, if_pos (show i < Lde by omega), ih (by omega)]
    ext x
    simp only [eraV, ES]
    split_ifs with h
    · simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hx1, hx2, hx3⟩
        refine ⟨hx2, ?_⟩
        rintro ⟨j, -, hj, hjx⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
        · exact hx3 ⟨j, Nat.zero_le _, hj, hjx⟩
        · subst hj; exact hx1 (Fin.ext hjx.symm)
      · rintro ⟨hx2, hx3⟩
        refine ⟨fun hx => hx3 ⟨i, Nat.zero_le _, Nat.lt_succ_self _, by rw [hx]⟩, hx2,
          fun ⟨j, _, hj, hjx⟩ => hx3 ⟨j, Nat.zero_le _, by omega, hjx⟩⟩
    · simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hx2, hx3⟩
        refine ⟨hx2, ?_⟩
        rintro ⟨j, -, hj, hjx⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
        · exact hx3 ⟨j, Nat.zero_le _, hj, hjx⟩
        · subst hj; exact h (hjx ▸ x.2)
      · rintro ⟨hx2, hx3⟩
        exact ⟨hx2, fun ⟨j, _, hj, hjx⟩ => hx3 ⟨j, Nat.zero_le _, by omega, hjx⟩⟩

theorem bt2 (Lde : ℕ) (S : Finset (Fin n)) (E : ℕ → ℕ) :
    ∀ m, buildT Lde S E (Lde + m) = buildT Lde S E Lde ∪ ES E Lde (Lde + m) := by
  intro m
  induction m with
  | zero => ext x; simp [ES]; intro j h1 h2; omega
  | succ m ih =>
    rw [show Lde + (m + 1) = (Lde + m) + 1 by ring]
    simp only [buildT, if_neg (show ¬ (Lde + m < Lde) by omega), ih]
    ext x
    simp only [insV, ES]
    split_ifs with h
    · simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro (hx | hx | ⟨j, h1, h2, h3⟩)
        · exact Or.inr ⟨Lde + m, by omega, by omega, by rw [hx]⟩
        · exact Or.inl hx
        · exact Or.inr ⟨j, h1, by omega, h3⟩
      · rintro (hx | ⟨j, h1, h2, h3⟩)
        · exact Or.inr (Or.inl hx)
        · rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h2 | h2
          · exact Or.inr (Or.inr ⟨j, h1, h2, h3⟩)
          · subst h2; exact Or.inl (Fin.ext h3.symm)
    · simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro (hx | ⟨j, h1, h2, h3⟩)
        · exact Or.inl hx
        · exact Or.inr ⟨j, h1, by omega, h3⟩
      · rintro (hx | ⟨j, h1, h2, h3⟩)
        · exact Or.inl hx
        · rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h2 | h2
          · exact Or.inr ⟨j, h1, h2, h3⟩
          · subst h2; exact absurd (h3 ▸ x.2) h

/-- Encode a finset of size at most `m` as digits in positions `[a, a+m)`, padded with `n`. -/
noncomputable def encodeList (B : Finset (Fin n)) : List ℕ := B.toList.map Fin.val

theorem encode_mem (B : Finset (Fin n)) (x : Fin n) :
    x ∈ B ↔ ∃ j, j < (encodeList B).length ∧ (encodeList B).getD j n = x.val := by
  constructor
  · intro hx
    have : x ∈ B.toList := Finset.mem_toList.mpr hx
    obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem this
    refine ⟨j, by simpa [encodeList] using hj, ?_⟩
    simp [encodeList, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, hjx]
  · rintro ⟨j, hj, hjx⟩
    have hj' : j < B.toList.length := by simpa [encodeList] using hj
    have : (encodeList B).getD j n = (B.toList[j]'hj').val := by
      simp [encodeList, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']
    rw [this] at hjx
    have : x = B.toList[j]'hj' := Fin.ext hjx.symm
    rw [this]; exact Finset.mem_toList.mp (List.getElem_mem _)

theorem encode_ge (B : Finset (Fin n)) (j : ℕ) (hj : (encodeList B).length ≤ j) :
    (encodeList B).getD j n = n := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hj]

theorem encode_le (B : Finset (Fin n)) (j : ℕ) : (encodeList B).getD j n ≤ n := by
  by_cases hj : j < (encodeList B).length
  · have hj' : j < B.toList.length := by simpa [encodeList] using hj
    have : (encodeList B).getD j n = (B.toList[j]'hj').val := by
      simp [encodeList, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']
    rw [this]; exact (B.toList[j]'hj').2.le
  · rw [encode_ge B j (by omega)]

theorem encode_len (B : Finset (Fin n)) : (encodeList B).length = B.card := by
  simp [encodeList]

theorem buildT_rep (Lde La : ℕ) (S T : Finset (Fin n)) (hA : (T \ S).card ≤ La)
    (hB : (S \ T).card ≤ Lde) :
    ∃ E : ℕ → ℕ, (∀ j, j < Lde + La → E j ≤ n) ∧ buildT Lde S E (Lde + La) = T := by
  let E : ℕ → ℕ := fun j => if j < Lde then (encodeList (S \ T)).getD j n
    else (encodeList (T \ S)).getD (j - Lde) n
  refine ⟨E, fun j _ => ?_, ?_⟩
  · simp only [E]; split_ifs <;> exact encode_le _ _
  rw [bt2, bt1 Lde S E Lde le_rfl]
  have h1 : (ES E 0 Lde : Finset (Fin n)) = S \ T := by
    ext x
    simp only [ES, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [encode_mem (S \ T) x]
    constructor
    · rintro ⟨j, -, hj, hjx⟩
      simp only [E, if_pos hj] at hjx
      by_cases hjl : j < (encodeList (S \ T)).length
      · exact ⟨j, hjl, hjx⟩
      · rw [encode_ge _ j (by omega)] at hjx; exact absurd x.2 (by omega)
    · rintro ⟨j, hjl, hjx⟩
      have : j < Lde := by rw [encode_len] at hjl; omega
      exact ⟨j, Nat.zero_le _, this, by simp only [E, if_pos this]; exact hjx⟩
  have h2 : (ES E Lde (Lde + La) : Finset (Fin n)) = T \ S := by
    ext x
    simp only [ES, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [encode_mem (T \ S) x]
    constructor
    · rintro ⟨j, hj1, hj, hjx⟩
      simp only [E, if_neg (show ¬ j < Lde by omega)] at hjx
      by_cases hjl : j - Lde < (encodeList (T \ S)).length
      · exact ⟨j - Lde, hjl, hjx⟩
      · rw [encode_ge _ _ (by omega)] at hjx; exact absurd x.2 (by omega)
    · rintro ⟨j, hjl, hjx⟩
      have : j < La := by rw [encode_len] at hjl; omega
      refine ⟨Lde + j, by omega, by omega, ?_⟩
      simp only [E, if_neg (show ¬ Lde + j < Lde by omega), show Lde + j - Lde = j by omega]
      exact hjx
  rw [h1, h2]
  ext x
  simp only [Finset.mem_union, Finset.mem_sdiff]
  tauto

end BuildRep
end LSVAlgo


namespace LSVAlgo
open LeeSviridenkoVondrak.LocalSearch

section MathAux
variable {n k : ℕ}

theorem sub_sum (f : Finset (Fin n) → ℝ) (hsub : NonmonotoneSubmod.Shared.Submodular f) :
    ∀ T : Finset (Fin n), f T ≤ f ∅ + ∑ x ∈ T, (f {x} - f ∅) := by
  intro T
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    have h := hsub T {a}
    have e1 : T ∪ {a} = insert a T := by ext; simp [or_comm]
    have e2 : T ∩ {a} = ∅ := by ext x; simp; intro hx hxa; subst hxa; exact ha hx
    rw [e1, e2] at h
    rw [Finset.sum_insert ha]
    linarith

theorem ci_single (M : Fin k → Matroid (Fin n)) {C : Finset (Fin n)} (hC : CommonIndependent M C)
    {x : Fin n} (hx : x ∈ C) : CommonIndependent M {x} := by
  intro j
  exact (hC j).subset (by simpa using hx)

theorem ci_empty (M : Fin k → Matroid (Fin n)) : CommonIndependent M ∅ := by
  intro j; simpa using (M j).empty_indep

theorem upper_bound (f : Finset (Fin n) → ℝ) (M : Fin k → Matroid (Fin n))
    (hsub : NonmonotoneSubmod.Shared.Submodular f) (hnn : Nonnegative f) (hmono : Nondecreasing f)
    (v0 : ℝ) (y0 : Fin n) (hv0 : f {y0} = v0)
    (hmax : ∀ z : Fin n, CommonIndependent M {z} → f {z} ≤ v0) :
    ∀ T, CommonIndependent M T → f T ≤ n * v0 := by
  intro T hT
  have h1 := sub_sum f hsub T
  have hle : ∑ x ∈ T, (f {x} - f ∅) ≤ ∑ x ∈ T, (v0 - f ∅) :=
    Finset.sum_le_sum (fun x hx => by linarith [hmax x (ci_single M hT hx)])
  rw [Finset.sum_const, nsmul_eq_mul] at hle
  have he : f ∅ ≤ v0 := hv0 ▸ hmono ∅ {y0} (Finset.empty_subset _)
  have h0 := hnn ∅
  have hcard : (T.card : ℝ) ≤ n := by
    have := Finset.card_le_univ T; simp at this; exact_mod_cast this
  have hn1 : (1 : ℝ) ≤ n := by
    have : 0 < n := Fin.pos y0
    exact_mod_cast this
  have hv0' : 0 ≤ v0 := le_trans h0 he
  have key : f T ≤ f ∅ + T.card * (v0 - f ∅) := by linarith
  rcases Nat.eq_zero_or_pos T.card with hc | hc
  · rw [hc] at key; simp at key
    nlinarith
  · have hc' : (1 : ℝ) ≤ T.card := by exact_mod_cast hc
    nlinarith [mul_le_mul_of_nonneg_right hcard hv0', mul_nonneg (sub_nonneg.mpr hc') h0]

theorem degenerate_bound (f : Finset (Fin n) → ℝ) (M : Fin k → Matroid (Fin n))
    (hsub : NonmonotoneSubmod.Shared.Submodular f) (hnn : Nonnegative f) (hmono : Nondecreasing f)
    (hz : ∀ y : Fin n, CommonIndependent M {y} → f {y} ≤ 0) :
    ∀ C, CommonIndependent M C → f C ≤ f ∅ := by
  intro C hC
  rcases C.eq_empty_or_nonempty with h | ⟨x, hx⟩
  · rw [h]
  · have hx1 := hz x (ci_single M hC hx)
    have hx2 := hmono ∅ {x} (Finset.empty_subset _)
    have h0 := hnn ∅
    have hf0 : f ∅ = 0 := by linarith
    have h1 := sub_sum f hsub C
    have hle : ∑ y ∈ C, (f {y} - f ∅) ≤ 0 :=
      Finset.sum_nonpos (fun y hy => by linarith [hz y (ci_single M hC hy)])
    linarith

theorem opt_le (f : Finset (Fin n) → ℝ) (M : Fin k → Matroid (Fin n)) (X : ℝ)
    (h : ∀ C, CommonIndependent M C → f C ≤ X) : optimum f M ≤ X := by
  apply csSup_le
  · exact ⟨f ∅, ∅, ci_empty M, rfl⟩
  · rintro v ⟨C, hC, rfl⟩; exact h C hC

end MathAux
end LSVAlgo


namespace LSVAlgo
open LeeSviridenkoVondrak.LocalSearch

theorem pot_step (m c v0 fS fT : ℝ) (hm : 0 ≤ m) (hc : 0 < c) (hv0 : 0 < v0)
    (hv : (1 + m * c) * v0 ≤ fS) (hT : (1 + c) * fS ≤ fT) : (1 + (m + 1) * c) * v0 ≤ fT := by
  have h1 : (1 + c) * ((1 + m * c) * v0) ≤ (1 + c) * fS := mul_le_mul_of_nonneg_left hv (by linarith)
  have h2 : 0 ≤ m * c * c * v0 := by positivity
  nlinarith

section Outer
variable {n k : ℕ} (L Lde : ℕ) (ε K1 : ℝ) (f : Finset (Fin n) → ℝ) (M : Fin k → Matroid (Fin n))

theorem outer (v0 : ℝ) (hv0 : 0 < v0) (hU : ∀ T, CommonIndependent M T → f T ≤ n * v0) (N : ℕ)
    (hN : ∀ m : ℕ, (1 + m * (ε / (n * K1))) * v0 ≤ n * v0 → m ≤ N) (hc : 0 < ε / (n * K1)) :
    ∀ r m (s : MachineState n) (S : Finset (Fin n)), N - m = r → m ≤ N → s.pc = 30 →
      GoodC (k := k) ε K1 s → s.setReg 0 = S → s.realReg 0 = f S → CommonIndependent M S →
      (1 + m * (ε / (n * K1))) * v0 ≤ f S →
      Reaches (prog k L Lde ε K1) f M s ((r + 1) * (L + W n (L + 5 * k + 9) L + 2)) (fun s' =>
        s'.halted = true ∧ CommonIndependent M s'.output ∧ 0 < f s'.output ∧
        ∀ E : ℕ → ℕ, (∀ j, j < L → E j ≤ n) →
          ¬ (CommonIndependent M (buildT Lde s'.output E L) ∧
            (1 + ε / (n * K1)) * f s'.output ≤ f (buildT Lde s'.output E L))) := by
  intro r
  induction r with
  | zero =>
    intro m s S hr hm hpc hG hS hfS hC hv
    refine Reaches.mono (Reaches.trans (B2 := 0)
      (round L Lde ε K1 f M S s hpc hG hS hfS) ?_) (by ring_nf; omega) (fun _ h => h)
    rintro s' (⟨-, -, T, -, -, hT, hTv⟩ | ⟨h1, h2, h3⟩)
    · exfalso
      have hm1 : m + 1 ≤ N := by
        apply hN
        refine le_trans ?_ (hU T hT)
        push_cast
        exact pot_step _ _ _ _ _ (by positivity) hc hv0 hv hTv
      omega
    · apply Reaches.now
      have hpos : 0 < f S := by
        have hmc : (0:ℝ) ≤ m * (ε / (n * K1)) := by positivity
        nlinarith
      exact ⟨h1, h2 ▸ hC, h2 ▸ hpos, h2 ▸ h3⟩
  | succ r ih =>
    intro m s S hr hm hpc hG hS hfS hC hv
    refine Reaches.mono (Reaches.trans (B2 := (r + 1) * (L + W n (L + 5 * k + 9) L + 2))
      (round L Lde ε K1 f M S s hpc hG hS hfS) ?_) (by ring_nf; omega) (fun _ h => h)
    rintro s' (⟨h1, h2, T, h3, h4, hT, hTv⟩ | ⟨h1, h2, h3⟩)
    · have hmc : (0:ℝ) ≤ m * (ε / (n * K1)) := by positivity
      have hv' : (1 + ((m + 1 : ℕ) : ℝ) * (ε / (n * K1))) * v0 ≤ f T := by
        push_cast
        exact pot_step _ _ _ _ _ (by positivity) hc hv0 hv hTv
      have hm1 : m + 1 ≤ N := hN (m + 1) (le_trans hv' (hU T hT))
      exact ih (m + 1) s' T (by omega) hm1 h1 h2 h3 h4 hT hv'
    · apply Reaches.now
      have hpos : 0 < f S := by
        have hmc : (0:ℝ) ≤ m * (ε / (n * K1)) := by positivity
        nlinarith
      exact ⟨h1, h2 ▸ hC, h2 ▸ hpos, h2 ▸ h3⟩

end Outer
end LSVAlgo


namespace LSVAlgo

theorem W_le (n B0 : ℕ) : ∀ i, W n B0 i ≤ (n + 1) ^ i * (B0 + 3 * i) := by
  intro i
  induction i with
  | zero => simp [W]
  | succ i ih =>
    simp only [W]
    have h1 : 1 ≤ (n + 1) ^ i := Nat.one_le_pow _ _ (by omega)
    calc (n + 1) * (W n B0 i + 3) ≤ (n + 1) * ((n + 1) ^ i * (B0 + 3 * i) + 3 * (n + 1) ^ i) :=
          Nat.mul_le_mul_left _ (by nlinarith)
      _ = (n + 1) ^ (i + 1) * (B0 + 3 * (i + 1)) := by ring

theorem total_le (n k L Kc : ℕ) :
    (4 * n + 14) + (n * (5 * k + 11) + 1) + 2 +
      (n * n * Kc + 1) * (L + W n (L + 5 * k + 9) L + 2) ≤
    (40 + 5 * k + (Kc + 1) * (4 * L + 2 + (L + 5 * k + 9))) * (n + 1) ^ (L + 2) := by
  set P := n + 1 with hP
  set X := P ^ L with hX
  have hX1 : 1 ≤ X := Nat.one_le_pow _ _ (by omega)
  have hW := W_le n (L + 5 * k + 9) L
  rw [← hX] at hW
  have hPL : P ^ (L + 2) = X * (P * P) := by rw [hX, pow_add]; ring
  rw [hPL]
  have hR : L + W n (L + 5 * k + 9) L + 2 ≤ X * (4 * L + 2 + (L + 5 * k + 9)) := by nlinarith
  have hN : n * n * Kc + 1 ≤ (Kc + 1) * (P * P) := by
    have : n * n ≤ P * P := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have hPP : 1 ≤ P * P := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h1 : (n * n * Kc + 1) * (L + W n (L + 5 * k + 9) L + 2) ≤
      ((Kc + 1) * (P * P)) * (X * (4 * L + 2 + (L + 5 * k + 9))) := Nat.mul_le_mul hN hR
  have h2 : (4 * n + 14) + (n * (5 * k + 11) + 1) + 2 ≤ (40 + 5 * k) * (X * (P * P)) := by
    have hnP : n ≤ X * (P * P) := by nlinarith
    have : 1 ≤ X * (P * P) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    nlinarith
  nlinarith

end LSVAlgo


namespace LSVAlgo
open LeeSviridenkoVondrak.LocalSearch

theorem param_ineq (k : ℕ) (δ : ℝ) (hδ : 0 < δ) (p : ℕ) (hp : 2 / δ ≤ p) :
    (1 + δ / (2 * ((k : ℝ) + 1))) * ((k : ℝ) + 1 / (p : ℝ)) ≤ (k : ℝ) + δ := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le (by positivity) hp
  have h1 : 1 / (p : ℝ) ≤ δ / 2 := by
    rw [div_le_iff₀ hp0]
    have := (div_le_iff₀ hδ).mp hp
    linarith
  have hp1 : 1 / (p : ℝ) ≤ 1 := by
    rw [div_le_one hp0]
    have : (1 : ℝ) ≤ p := by
      have : (0 : ℕ) < p := by exact_mod_cast hp0
      exact_mod_cast this
    exact this
  have hk0 : (0 : ℝ) ≤ k := by positivity
  set e := δ / (2 * ((k : ℝ) + 1)) with he
  have he0 : 0 ≤ e := by positivity
  have he1 : e * ((k : ℝ) + 1) = δ / 2 := by rw [he]; field_simp
  have hq0 : 0 ≤ 1 / (p : ℝ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hp1 he0]

end LSVAlgo

open LeeSviridenkoVondrak.LocalSearch LSVAlgo in
theorem solution (k : ℕ) (hk : 2 ≤ k) (δ : ℝ) (hδ : 0 < δ) :
    ∃ code : List Instruction, ∃ A d : ℕ, 0 < A ∧
      ∀ (n : ℕ) (f : Finset (Fin n) → ℝ) (M : Fin k → Matroid (Fin n)),
        (∀ j, (M j).E = Set.univ) → Nonnegative f → Nondecreasing f →
        NonmonotoneSubmod.Shared.Submodular f →
        ∃ steps : ℕ,
          (runMachine code f M steps).halted = true ∧
          (runMachine code f M steps).cost ≤ A * (n + 1) ^ d ∧
          CommonIndependent M (runMachine code f M steps).output ∧
          optimum f M / ((k : ℝ) + δ) ≤ f (runMachine code f M steps).output := by
  set p : ℕ := ⌈2 / δ⌉₊ with hpdef
  have hp2 : 2 / δ ≤ (p : ℝ) := Nat.le_ceil _
  have hp1 : 1 ≤ p := by
    have : (0 : ℝ) < p := lt_of_lt_of_le (by positivity) hp2
    exact_mod_cast this
  set ε : ℝ := δ / (2 * ((k : ℝ) + 1)) with hεdef
  have hε : 0 < ε := by positivity
  set K1 : ℝ := (k : ℝ) + 1 with hK1
  have hK1p : 0 < K1 := by positivity
  set Lde : ℕ := 2 * k * p
  set L : ℕ := Lde + 2 * p
  set Kc : ℕ := ⌈K1 / ε⌉₊
  refine ⟨prog k L Lde ε K1, 40 + 5 * k + (Kc + 1) * (4 * L + 2 + (L + 5 * k + 9)), L + 3,
    by positivity, ?_⟩
  intro n f M hE hnn hmono hsub
  have hkδ : (0 : ℝ) < k + δ := by positivity
  -- the run
  have run : Reaches (prog k L Lde ε K1) f M (initialState n)
      ((4 * n + 14) + (n * (5 * k + 11) + 1) + 2 +
        (n * n * Kc + 1) * (L + W n (L + 5 * k + 9) L + 2))
      (fun s => s.halted = true ∧ CommonIndependent M s.output ∧
        optimum f M / ((k : ℝ) + δ) ≤ f s.output) := by
    refine Reaches.mono (Reaches.trans (B2 := (n * (5 * k + 11) + 1) +
      (2 + (n * n * Kc + 1) * (L + W n (L + 5 * k + 9) L + 2))) (phaseA L Lde ε K1 f M) ?_)
      (by omega) (fun _ h => h)
    rintro s ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩
    have hG : GoodC (k := k) ε K1 s := ⟨a2, a3, a4, a5, a6, a7, a8, a9⟩
    have hB0 : Best f M 0 (s.setReg 0) (s.realReg 0) :=
      ⟨Or.inl ⟨a11, a12⟩, fun y hy => absurd hy (Nat.not_lt_zero _)⟩
    have e1 := loopB L Lde ε K1 f M n 0 s (by omega) (by omega) a1 hG a10 hB0
    refine Reaches.trans e1 ?_
    rintro s1 ⟨b1, b2, b3⟩
    refine Reaches.trans (B2 := (n * n * Kc + 1) * (L + W n (L + 5 * k + 9) L + 2))
      (endB L Lde ε K1 f M s1 b1 b2 b3) ?_
    rintro s2 (⟨c1, c2, c3⟩ | ⟨c1, c2, y0, c3, c4, c5, c6, c7⟩)
    · apply Reaches.now
      refine ⟨c1, by rw [c2]; exact ci_empty M, ?_⟩
      rw [c2]
      have hopt : optimum f M ≤ f ∅ := opt_le f M _ (degenerate_bound f M hsub hnn hmono c3)
      have h0 := hnn ∅
      rw [div_le_iff₀ hkδ]
      have : (1 : ℝ) ≤ k + δ := by
        have : (2 : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      nlinarith
    · -- local search phase
      have hn1 : 0 < n := Fin.pos y0
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have hc : 0 < ε / (n * K1) := by positivity
      have hU := upper_bound f M hsub hnn hmono (f {y0}) y0 rfl c7
      have hN : ∀ m : ℕ, (1 + m * (ε / (n * K1))) * f {y0} ≤ n * f {y0} → m ≤ n * n * Kc := by
        intro m hm
        have h1 : 1 + m * (ε / (n * K1)) ≤ n := le_of_mul_le_mul_right hm c6
        have h2 : (m : ℝ) * ε ≤ n * n * K1 := by
          have : (m : ℝ) * (ε / (n * K1)) ≤ n := by linarith
          rw [mul_div_assoc', div_le_iff₀ (by positivity)] at this
          nlinarith
        have h3 : (m : ℝ) ≤ n * n * (K1 / ε) := by
          rw [mul_div_assoc', le_div_iff₀ hε]; linarith
        have h4 : (K1 / ε) ≤ (Kc : ℝ) := Nat.le_ceil _
        have h5 : (m : ℝ) ≤ n * n * Kc := le_trans h3 (by gcongr)
        exact_mod_cast h5
      have e2 := outer L Lde ε K1 f M (f {y0}) c6 hU (n * n * Kc) hN hc (n * n * Kc) 0 s2 {y0}
        (by omega) (by omega) c1 c2 c3 c5 c4 (by simp)
      refine Reaches.mono e2 le_rfl ?_
      rintro s3 ⟨d1, d2, d3, d4⟩
      refine ⟨d1, d2, ?_⟩
      set S := s3.output
      have hALO : ApproxLocalOptimum f M p ε S := by
        refine ⟨d2, fun T hT => ?_⟩
        obtain ⟨hTC, hTa, hTb⟩ := hT
        obtain ⟨E, hEb, hET⟩ := buildT_rep Lde (2 * p) S T hTa hTb
        have := d4 E hEb
        rw [hET] at this
        push_neg at this
        exact this hTC
      have hopt : optimum f M ≤ (1 + ε) * ((k : ℝ) + 1 / (p : ℝ)) * f S := by
        apply opt_le
        intro C hC
        have h32 := lemma_3_2 hk hp1 f hsub hnn M hE S C hC ε hε hALO
        have hmC : f C ≤ f (S ∪ C) := hmono _ _ Finset.subset_union_right
        have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 + 1 / (p : ℝ) := by
          have : (2 : ℝ) ≤ k := by exact_mod_cast hk
          have : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
          linarith
        have := mul_nonneg hk1 (hnn (S ∩ C))
        linarith
      have hpar := param_ineq k δ hδ p hp2
      rw [div_le_iff₀ hkδ]
      have hfS := d3.le
      calc optimum f M ≤ (1 + ε) * ((k : ℝ) + 1 / (p : ℝ)) * f S := hopt
        _ ≤ (k + δ) * f S := by nlinarith
        _ = f S * (k + δ) := by ring
  obtain ⟨t, ht, h1, h2, h3⟩ := run
  refine ⟨t, h1, ?_, h2, h3⟩
  have hc := cost_iter (prog k L Lde ε K1) f M t (initialState n)
  simp only [initialState, zero_add] at hc
  calc (runMachine (prog k L Lde ε K1) f M t).cost ≤ t * (n + 1) := hc
    _ ≤ (40 + 5 * k + (Kc + 1) * (4 * L + 2 + (L + 5 * k + 9))) * (n + 1) ^ (L + 2) * (n + 1) :=
        Nat.mul_le_mul_right _ (le_trans ht (total_le n k L Kc))
    _ = (40 + 5 * k + (Kc + 1) * (4 * L + 2 + (L + 5 * k + 9))) * (n + 1) ^ (L + 3) := by ring
