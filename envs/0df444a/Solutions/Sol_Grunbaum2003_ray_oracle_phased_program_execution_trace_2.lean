-- Prove2me | solution 2 for Grunbaum2003.ray_oracle_phased_program_execution_trace
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T00:50:43.937387+00:00
-- url     : https://prove2.me/submissions/3524f6a2-9cb2-4b2f-b55c-977810e42d1b

import Mathlib
import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsPolytopeRayOracle
import Definitions.Def_Grunbaum2003_RayInstruction
import Definitions.Def_Grunbaum2003_RayConfiguration
import Definitions.Def_Grunbaum2003_rayMachineStep
import Definitions.Def_Grunbaum2003_rayMachineRun
import Definitions.Def_Grunbaum2003_PolytopeFace

set_option autoImplicit false
open scoped BigOperators Matrix Classical

namespace G81
open Grunbaum2003

/-! ## Chunk 1: machine basics -/

section Machine
variable {d : ℕ}

/-- the vector a query at configuration `c` would send to the oracle -/
noncomputable def qv (d : ℕ) (c : RayConfiguration) : Fin d → ℝ :=
  fun i => c.tape (c.head + (i.val : ℤ))

theorem run_zero (prog : List RayInstruction) (O : (Fin d → ℝ) → Fin d → ℝ)
    (c : RayConfiguration) : rayMachineRun prog O 0 c = some c := rfl

theorem run_succ (prog : List RayInstruction) (O : (Fin d → ℝ) → Fin d → ℝ) (t : ℕ)
    (c : RayConfiguration) :
    rayMachineRun prog O (t + 1) c = (rayMachineStep prog O c).bind (rayMachineRun prog O t) :=
  rfl

theorem run_add' (prog : List RayInstruction) (O : (Fin d → ℝ) → Fin d → ℝ) :
    ∀ (a b : ℕ) (c : RayConfiguration), rayMachineRun prog O (a + b) c =
      (rayMachineRun prog O a c).bind (rayMachineRun prog O b) := by
  intro a
  induction a with
  | zero => intro b c; simp [run_zero]
  | succ a ih =>
    intro b c
    rw [show a + 1 + b = (a + b) + 1 by omega, run_succ, run_succ]
    cases h : rayMachineStep prog O c with
    | none => rfl
    | some c' => simp [ih]

theorem step_halt (prog : List RayInstruction) (O : (Fin d → ℝ) → Fin d → ℝ)
    (c : RayConfiguration) (h : prog[c.pc]? = some .halt) :
    rayMachineStep prog O c = some c := by
  unfold rayMachineStep
  simp [h]

theorem run_halt (prog : List RayInstruction) (O : (Fin d → ℝ) → Fin d → ℝ)
    (c : RayConfiguration) (h : prog[c.pc]? = some .halt) :
    ∀ t, rayMachineRun prog O t c = some c := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => rw [run_succ, step_halt prog O c h]; simpa using ih

theorem halted_unique (prog : List RayInstruction) (O : (Fin d → ℝ) → Fin d → ℝ)
    (c0 c c' : RayConfiguration) (t t' : ℕ)
    (h : rayMachineRun prog O t c0 = some c) (hh : prog[c.pc]? = some .halt)
    (h' : rayMachineRun prog O t' c0 = some c') (hh' : prog[c'.pc]? = some .halt) :
    c = c' := by
  rcases le_total t t' with htt | htt
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le htt
    rw [run_add', h] at h'
    simp only [Option.bind_some] at h'
    rw [run_halt prog O c hh k] at h'
    exact Option.some.inj h'
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le htt
    rw [run_add', h'] at h
    simp only [Option.bind_some] at h
    rw [run_halt prog O c' hh' k] at h
    exact (Option.some.inj h).symm

/-- the instruction at `c` is a query -/
def IsQ (prog : List RayInstruction) (c : RayConfiguration) : Prop :=
  ∃ n, prog[c.pc]? = some (.query n)

theorem step_congr (prog : List RayInstruction) (O1 O2 : (Fin d → ℝ) → Fin d → ℝ)
    (c : RayConfiguration) (h : IsQ prog c → O1 (qv d c) = O2 (qv d c)) :
    rayMachineStep prog O1 c = rayMachineStep prog O2 c := by
  unfold rayMachineStep
  rcases hc : prog[c.pc]? with _ | i
  · simp
  · cases i with
    | query n =>
      have this : O1 (fun i : Fin d => c.tape (c.head + (i.val : ℤ))) =
          O2 (fun i : Fin d => c.tape (c.head + (i.val : ℤ))) := h ⟨n, hc⟩
      simp [this]
    | _ => simp

theorem run_congr (prog : List RayInstruction) (O1 O2 : (Fin d → ℝ) → Fin d → ℝ) :
    ∀ (t : ℕ) (c0 : RayConfiguration),
      (∀ s < t, ∀ c', rayMachineRun prog O1 s c0 = some c' → IsQ prog c' →
        O1 (qv d c') = O2 (qv d c')) →
      rayMachineRun prog O1 t c0 = rayMachineRun prog O2 t c0 := by
  intro t
  induction t with
  | zero => intro c0 _; rfl
  | succ t ih =>
    intro c0 h
    rw [run_succ, run_succ]
    have hs := step_congr prog O1 O2 c0 (fun hq => h 0 (by omega) c0 rfl hq)
    rw [← hs]
    cases hst : rayMachineStep prog O1 c0 with
    | none => rfl
    | some c1 =>
      simp only [Option.bind_some]
      apply ih c1
      intro s hs' c' hc' hq
      apply h (s + 1) (by omega) c'
      · rw [run_succ, hst]; simpa using hc'
      · exact hq

/-- query count bookkeeping: each step adds 1 to `queries` iff it is a query step -/
theorem step_queries (prog : List RayInstruction) (O : (Fin d → ℝ) → Fin d → ℝ)
    (c c' : RayConfiguration) (h : rayMachineStep prog O c = some c') :
    c'.queries = c.queries + (if IsQ prog c then 1 else 0) := by
  unfold rayMachineStep at h
  rcases hc : prog[c.pc]? with _ | i
  · simp [hc] at h
  · cases i with
    | query n =>
      have hq : IsQ prog c := ⟨n, hc⟩
      simp only [hc] at h
      split_ifs at h
      cases h
      simp [hq]
    | halt =>
      have hq : ¬ IsQ prog c := by rintro ⟨n, hn⟩; rw [hc] at hn; cases hn
      simp only [hc] at h
      cases h; simp [hq]
    | constant dst v nx =>
      have hq : ¬ IsQ prog c := by rintro ⟨n, hn⟩; rw [hc] at hn; cases hn
      simp only [hc] at h
      cases h; simp [hq]
    | add dst a b nx =>
      have hq : ¬ IsQ prog c := by rintro ⟨n, hn⟩; rw [hc] at hn; cases hn
      simp only [hc] at h
      cases h; simp [hq]
    | sub dst a b nx =>
      have hq : ¬ IsQ prog c := by rintro ⟨n, hn⟩; rw [hc] at hn; cases hn
      simp only [hc] at h
      cases h; simp [hq]
    | mul dst a b nx =>
      have hq : ¬ IsQ prog c := by rintro ⟨n, hn⟩; rw [hc] at hn; cases hn
      simp only [hc] at h
      cases h; simp [hq]
    | div dst a b nx =>
      have hq : ¬ IsQ prog c := by rintro ⟨n, hn⟩; rw [hc] at hn; cases hn
      simp only [hc] at h
      split_ifs at h
      cases h; simp [hq]
    | branch a x y z =>
      have hq : ¬ IsQ prog c := by rintro ⟨n, hn⟩; rw [hc] at hn; cases hn
      simp only [hc] at h
      cases h; simp [hq]
    | shift o nx =>
      have hq : ¬ IsQ prog c := by rintro ⟨n, hn⟩; rw [hc] at hn; cases hn
      simp only [hc] at h
      cases h; simp [hq]

/-- a query step that succeeds was sent a nonzero vector and answers with the oracle -/
theorem step_query_nonzero (prog : List RayInstruction) (O : (Fin d → ℝ) → Fin d → ℝ)
    (c c' : RayConfiguration) (h : rayMachineStep prog O c = some c') (hq : IsQ prog c) :
    qv d c ≠ 0 := by
  obtain ⟨n, hn⟩ := hq
  unfold rayMachineStep at h
  simp only [hn] at h
  intro h0
  have h0' : (fun i : Fin d => c.tape (c.head + (i.val : ℤ))) = 0 := h0
  rw [if_pos h0'] at h
  cases h

end Machine

/-! ## Chunk 6a: extreme points of a partial square are corners -/

section SquareExt

/-- every extreme point of `{x | ∀ i ∈ S, L i x ≤ 1}` has both coordinates `±1` when each `L i`
is `σ • x_k` with `σ ∈ {1, -1, 0}` -/
theorem ext_partial_square {f : ℕ} (L : Fin f → (Fin 2 → ℝ) →L[ℝ] ℝ)
    (hL : ∀ i, ∃ (k : Fin 2) (σ : ℝ), (σ = 1 ∨ σ = -1 ∨ σ = 0) ∧ ∀ x, L i x = σ * x k)
    (S : Finset (Fin f)) (v : Fin 2 → ℝ)
    (hv : v ∈ ({x : Fin 2 → ℝ | ∀ i ∈ S, L i x ≤ 1}).extremePoints ℝ) :
    ∀ k : Fin 2, v k = 1 ∨ v k = -1 := by
  intro k
  by_contra hne
  push Not at hne
  obtain ⟨hne1, hne2⟩ := hne
  rw [mem_extremePoints] at hv
  obtain ⟨hvQ, hvx⟩ := hv
  set δ : ℝ := min |1 - v k| |1 + v k| with hδ
  have hδpos : 0 < δ := by
    apply lt_min
    · exact abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hne1))
    · apply abs_pos.mpr
      intro h; apply hne2; linarith
  set w : Fin 2 → ℝ := Pi.single k δ with hw
  have hmem : ∀ s : ℝ, (s = 1 ∨ s = -1) → v + s • w ∈ {x : Fin 2 → ℝ | ∀ i ∈ S, L i x ≤ 1} := by
    intro s hs i hi
    obtain ⟨k', σ, hσ, hLx⟩ := hL i
    have hvi := hvQ i hi
    rw [hLx] at hvi ⊢
    by_cases hkk : k' = k
    · subst hkk
      simp only [hw, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
      have h1 : δ ≤ |1 - v k'| := min_le_left _ _
      have h2 : δ ≤ |1 + v k'| := min_le_right _ _
      rcases hσ with rfl | rfl | rfl
      · have hlt : v k' < 1 := lt_of_le_of_ne (by linarith) hne1
        rw [abs_of_pos (by linarith)] at h1
        rcases hs with rfl | rfl <;> nlinarith
      · have hlt : -1 < v k' := by
          rcases lt_or_eq_of_le (show -1 ≤ v k' by linarith) with h | h
          · exact h
          · exact absurd h.symm hne2
        rw [abs_of_pos (by linarith)] at h2
        rcases hs with rfl | rfl <;> nlinarith
      · simp
    · simp only [hw, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Pi.single_eq_of_ne hkk]
      simpa using hvi
  have h1 := hmem 1 (Or.inl rfl)
  have h2 := hmem (-1) (Or.inr rfl)
  have hseg : v ∈ openSegment ℝ (v + (1:ℝ) • w) (v + (-1:ℝ) • w) := by
    refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have := (hvx _ h1 _ h2 hseg).1
  have hw0 : w = 0 := by
    have : (1:ℝ) • w = 0 := by
      have h' := congrArg (fun x => x - v) this
      simpa using h'
    simpa using this
  have : w k = 0 := by rw [hw0]; rfl
  simp [hw] at this
  linarith

end SquareExt

/-! ## Chunk 6: trace bound for the square -/

section TraceBound

/-- the closed square `[-1,1]^2` -/
def sqSet : Set (Fin 2 → ℝ) := {x | ∀ k, |x k| ≤ 1}

theorem sqSet_closed : IsClosed sqSet := by
  have : sqSet = ⋂ k : Fin 2, {x : Fin 2 → ℝ | |x k| ≤ 1} := by
    ext x; simp [sqSet]
  rw [this]
  exact isClosed_iInter fun k =>
    isClosed_le ((continuous_apply k).abs) continuous_const

theorem sq_open_sub_interior : {x : Fin 2 → ℝ | ∀ k, |x k| < 1} ⊆ interior sqSet := by
  apply interior_maximal
  · intro x hx k; exact (hx k).le
  · have : {x : Fin 2 → ℝ | ∀ k, |x k| < 1} = ⋂ k : Fin 2, {x : Fin 2 → ℝ | |x k| < 1} := by
      ext x; simp
    rw [this]
    exact isOpen_iInter_of_finite fun k =>
      isOpen_lt ((continuous_apply k).abs) continuous_const

/-- a ray oracle of the square fixes every corner -/
theorem corner_fixed (oracle : (Fin 2 → ℝ) → Fin 2 → ℝ)
    (ho : IsPolytopeRayOracle sqSet oracle) (v : Fin 2 → ℝ)
    (hv : ∀ k, v k = 1 ∨ v k = -1) : oracle v = v := by
  have hv0 : v ≠ 0 := by
    intro h
    rcases hv 0 with h1 | h1 <;> rw [h] at h1 <;> norm_num at h1
  obtain ⟨hfr, t, ht, hov⟩ := ho v hv0
  have habs : ∀ k, |v k| = 1 := by
    intro k; rcases hv k with h | h <;> rw [h] <;> norm_num
  rcases lt_trichotomy t 1 with h | h | h
  · exfalso
    have hin : t • v ∈ interior sqSet := by
      apply sq_open_sub_interior
      intro k
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul, habs k, abs_of_pos ht]
      linarith
    rw [← hov] at hin
    exact hfr.2 hin
  · rw [hov, h, one_smul]
  · exfalso
    have hcl : oracle v ∈ sqSet := by
      have := hfr.1
      rwa [sqSet_closed.closure_eq] at this
    have h0 := hcl 0
    rw [hov] at h0
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, habs 0, abs_of_pos ht] at h0
    linarith

/-- the four corners -/
noncomputable def cornerFS : Finset (Fin 2 → ℝ) :=
  Finset.univ.image (fun b : Fin 2 → Bool => fun k => if b k then (1 : ℝ) else -1)

theorem cornerFS_card : cornerFS.card ≤ 4 := by
  unfold cornerFS
  refine (Finset.card_image_le).trans ?_
  simp

theorem mem_cornerFS (v : Fin 2 → ℝ) (hv : ∀ k, v k = 1 ∨ v k = -1) : v ∈ cornerFS := by
  unfold cornerFS
  rw [Finset.mem_image]
  refine ⟨fun k => decide (v k = 1), Finset.mem_univ _, ?_⟩
  funext k
  rcases hv k with h | h
  · simp [h]
  · simp [h]; norm_num

/-- Chunk 6: any phased trace on the square has `q_N ≤ 7`. -/
theorem trace_bound {f : ℕ} (L : Fin f → (Fin 2 → ℝ) →L[ℝ] ℝ)
    (hL : ∀ i, ∃ (k : Fin 2) (σ : ℝ), (σ = 1 ∨ σ = -1 ∨ σ = 0) ∧ ∀ x, L i x = σ * x k)
    (P : Set (Fin 2 → ℝ)) (oracle : (Fin 2 → ℝ) → Fin 2 → ℝ)
    (hfix : ∀ v : Fin 2 → ℝ, (∀ k, v k = 1 ∨ v k = -1) → oracle v = v)
    (N : ℕ) (S_seq : ℕ → Finset (Fin f)) (C_seq : ℕ → Finset (Fin 2 → ℝ)) (q_seq : ℕ → ℕ)
    (hC0 : C_seq 0 = ∅) (hq0 : q_seq 0 ≤ 2 + 1)
    (hstep : ∀ s < N,
      (S_seq (s + 1) = S_seq s ∧
        ∃ v ∈ ({x : Fin 2 → ℝ | ∀ i ∈ S_seq s, L i x ≤ 1}).extremePoints ℝ,
          v ∈ P ∧ v ∉ C_seq s ∧ C_seq (s + 1) = insert v (C_seq s) ∧
          q_seq (s + 1) ≤ q_seq s + 1) ∨
      (C_seq (s + 1) = C_seq s ∧
        ∃ v ∈ ({x : Fin 2 → ℝ | ∀ i ∈ S_seq s, L i x ≤ 1}).extremePoints ℝ,
          oracle v ≠ v ∧
          ∃ i_new : Fin f,
            L i_new (oracle v) = 1 ∧
            S_seq (s + 1) = insert i_new (S_seq s) ∧
            q_seq (s + 1) ≤ q_seq s + (1 + (2 - 1) * (2 * (f - (S_seq s).card) + 3)))) :
    q_seq N ≤ 7 := by
  have inv : ∀ s ≤ N, C_seq s ⊆ cornerFS ∧ q_seq s ≤ 3 + (C_seq s).card := by
    intro s
    induction s with
    | zero => intro _; rw [hC0]; simp; omega
    | succ s ih =>
      intro hs
      obtain ⟨ihC, ihq⟩ := ih (by omega)
      rcases hstep s (by omega) with ⟨_, v, hvE, _, hvC, hCs, hqs⟩ | ⟨_, v, hvE, hne, _⟩
      · have hc := ext_partial_square L hL _ v hvE
        refine ⟨?_, ?_⟩
        · rw [hCs]; exact Finset.insert_subset (mem_cornerFS v hc) ihC
        · rw [hCs, Finset.card_insert_of_notMem hvC]; omega
      · exact absurd (hfix v (ext_partial_square L hL _ v hvE)) hne
  obtain ⟨hC, hq⟩ := inv N le_rfl
  have := (Finset.card_le_card hC).trans cornerFS_card
  omega

end TraceBound

/-! ## Chunk 2a: straight-line framework -/

section StraightLine

inductive Op where
  | const (dst : ℤ) (v : ℚ)
  | add (dst a b : ℤ)
  | sub (dst a b : ℤ)
  | mul (dst a b : ℤ)
  | div (dst a b : ℤ)
  | shift (o : ℤ)
  | query

def Op.toInstr : Op → ℕ → RayInstruction
  | .const dst v, n => .constant dst v n
  | .add dst a b, n => .add dst a b n
  | .sub dst a b, n => .sub dst a b n
  | .mul dst a b, n => .mul dst a b n
  | .div dst a b, n => .div dst a b n
  | .shift o, n => .shift o n
  | .query, n => .query n

/-- semantics of one straight-line op; it advances `pc` by one -/
noncomputable def opSem (d : ℕ) (O : (Fin d → ℝ) → Fin d → ℝ) :
    Op → RayConfiguration → Option RayConfiguration
  | .const dst v, c => some ⟨c.pc + 1, c.head,
      Function.update c.tape (c.head + dst) (v : ℝ), c.queries⟩
  | .add dst a b, c => some ⟨c.pc + 1, c.head,
      Function.update c.tape (c.head + dst) (c.tape (c.head + a) + c.tape (c.head + b)), c.queries⟩
  | .sub dst a b, c => some ⟨c.pc + 1, c.head,
      Function.update c.tape (c.head + dst) (c.tape (c.head + a) - c.tape (c.head + b)), c.queries⟩
  | .mul dst a b, c => some ⟨c.pc + 1, c.head,
      Function.update c.tape (c.head + dst) (c.tape (c.head + a) * c.tape (c.head + b)), c.queries⟩
  | .div dst a b, c => if c.tape (c.head + b) = 0 then none else some ⟨c.pc + 1, c.head,
      Function.update c.tape (c.head + dst) (c.tape (c.head + a) / c.tape (c.head + b)), c.queries⟩
  | .shift o, c => some ⟨c.pc + 1, c.head + o, c.tape, c.queries⟩
  | .query, c => if qv d c = 0 then none else some ⟨c.pc + 1, c.head,
      (fun j => if h : 0 ≤ j - c.head ∧ j - c.head < (d : ℤ) then
        O (qv d c) ⟨(j - c.head).toNat, by omega⟩ else c.tape j), c.queries + 1⟩

theorem step_op {d : ℕ} (prog : List RayInstruction) (O : (Fin d → ℝ) → Fin d → ℝ)
    (c : RayConfiguration) (o : Op) (h : prog[c.pc]? = some (o.toInstr (c.pc + 1))) :
    rayMachineStep prog O c = opSem d O o c := by
  cases o <;> simp [rayMachineStep, h, Op.toInstr, opSem] <;> (unfold qv; split_ifs <;> rfl)

theorem opSem_pc {d : ℕ} (O : (Fin d → ℝ) → Fin d → ℝ) (o : Op) (c c' : RayConfiguration)
    (h : opSem d O o c = some c') : c'.pc = c.pc + 1 := by
  cases o <;> simp only [opSem] at h <;> (try split_ifs at h) <;>
    (cases h) <;> rfl

noncomputable def foldOps (d : ℕ) (O : (Fin d → ℝ) → Fin d → ℝ) :
    List Op → RayConfiguration → Option RayConfiguration
  | [], c => some c
  | o :: os, c => (opSem d O o c).bind (foldOps d O os)

theorem run_ops {d : ℕ} (prog : List RayInstruction) (O : (Fin d → ℝ) → Fin d → ℝ) :
    ∀ (ops : List Op) (c : RayConfiguration),
      (∀ i (hi : i < ops.length), prog[c.pc + i]? = some (ops[i].toInstr (c.pc + i + 1))) →
      rayMachineRun prog O ops.length c = foldOps d O ops c := by
  intro ops
  induction ops with
  | nil => intro c _; rfl
  | cons o os ih =>
    intro c h
    rw [List.length_cons, run_succ, step_op prog O c o (by have h0 := h 0 (by simp); rwa [List.getElem_cons_zero, Nat.add_zero] at h0)]
    simp only [foldOps]
    cases hs : opSem d O o c with
    | none => rfl
    | some c1 =>
      simp only [Option.bind_some]
      apply ih
      intro i hi
      have h1 := h (i + 1) (by simp; omega)
      rw [opSem_pc O o c c1 hs, show c.pc + 1 + i = c.pc + (i + 1) by omega]
      simpa using h1

def mkProg (ops : List Op) : List RayInstruction :=
  ops.mapIdx (fun i o => o.toInstr (i + 1)) ++ [RayInstruction.halt]

theorem mkProg_halt (ops : List Op) : (mkProg ops)[ops.length]? = some .halt := by
  simp [mkProg]

theorem run_mkProg {d : ℕ} (O : (Fin d → ℝ) → Fin d → ℝ) (ops : List Op)
    (c : RayConfiguration) (hc : c.pc = 0) :
    rayMachineRun (mkProg ops) O ops.length c = foldOps d O ops c := by
  apply run_ops
  intro i hi
  rw [hc]
  simp [mkProg, List.getElem?_append_left, hi]

end StraightLine

/-! ## Chunk 2b: the inner sample program for d = 2 -/

section InnerSample

def innerOps : List Op :=
  [.shift 2, .const 0 1, .const 1 0, .query, .shift 2, .const 0 0, .const 1 1, .query,
   .shift 2, .const 0 (-1), .const 1 (-1), .query, .shift (-6), .shift 0]

def innerSampleW (_d : ℕ) : List RayInstruction := mkProg innerOps

noncomputable def queryVectorW (d : ℕ) (i : ℕ) : Fin d → ℝ :=
  fun j => if i < d then (if j.val = i then 1 else 0) else -1

theorem qvW_ne0 : queryVectorW 2 0 ≠ 0 := by
  intro h; have := congrFun h 0; simp [queryVectorW] at this
theorem qvW_ne1 : queryVectorW 2 1 ≠ 0 := by
  intro h; have := congrFun h 1; simp [queryVectorW] at this
theorem qvW_ne2 : queryVectorW 2 2 ≠ 0 := by
  intro h; have := congrFun h 0; simp [queryVectorW] at this

theorem inner_e0 (X : ℤ → ℝ) (p q' : ℕ) :
    qv 2 ⟨p, 2, Function.update (Function.update X 2 1) 3 0, q'⟩ = queryVectorW 2 0 := by
  funext k; fin_cases k <;> simp [qv, queryVectorW, Function.update_apply]
theorem inner_e1 (X : ℤ → ℝ) (p q' : ℕ) :
    qv 2 ⟨p, 4, Function.update (Function.update X 4 0) 5 1, q'⟩ = queryVectorW 2 1 := by
  funext k; fin_cases k <;> simp [qv, queryVectorW, Function.update_apply]
theorem inner_e2 (X : ℤ → ℝ) (p q' : ℕ) :
    qv 2 ⟨p, 6, Function.update (Function.update X 6 (-1)) 7 (-1), q'⟩ = queryVectorW 2 2 := by
  funext k; fin_cases k <;> simp [qv, queryVectorW, Function.update_apply]

theorem innerW_spec (oracle : (Fin 2 → ℝ) → Fin 2 → ℝ) (tape : ℤ → ℝ) (q : ℕ) :
      ∃ c : RayConfiguration,
        rayMachineRun (innerSampleW 2) oracle ((2 + 1) * (2 + 2) + 2)
          {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
        c.pc = (2 + 1) * (2 + 2) + 2 ∧
        (innerSampleW 2)[c.pc]? = some .halt ∧
        c.head = 0 ∧
        c.queries = q + (2 + 1) ∧
        (∀ i : Fin (2 + 1), ∀ j : Fin 2,
          c.tape ((((i.val + 1) * 2 + j.val : ℕ) : ℤ)) = oracle (queryVectorW 2 i.val) j) ∧
        (∀ z : ℤ, (z < (2 : ℤ) ∨ (((2 + 2) * 2 : ℕ) : ℤ) ≤ z) → c.tape z = tape z) := by
  have hlen : (2 + 1) * (2 + 2) + 2 = innerOps.length := rfl
  rw [hlen, innerSampleW, run_mkProg oracle innerOps _ rfl]
  simp [foldOps, innerOps, opSem, inner_e0, inner_e1, inner_e2, qvW_ne0, qvW_ne1, qvW_ne2,
    Function.update_apply]
  refine ⟨mkProg_halt innerOps, ?_, ?_⟩
  · intro i
    fin_cases i <;> refine ⟨?_, ?_⟩ <;> (try simp) <;> (try rfl)
  · intro z hz
    have h2 : z ≠ 2 := by omega
    have h3 : z ≠ 3 := by omega
    have h4 : z ≠ 4 := by omega
    have h5 : z ≠ 5 := by omega
    have h6 : z ≠ 6 := by omega
    have h7 : z ≠ 7 := by omega
    have a1 : ¬ (2 ≤ z ∧ z ≤ 3) := by omega
    have a2 : ¬ (4 ≤ z ∧ z ≤ 5) := by omega
    have a3 : ¬ (6 ≤ z ∧ z ≤ 7) := by omega
    simp [h2, h3, h4, h5, h6, h7, a1, a2, a3]

end InnerSample


section OpLemmas
variable {d : ℕ} (O : (Fin d → ℝ) → Fin d → ℝ) (c : RayConfiguration)

theorem opSem_const (dst : ℤ) (v : ℚ) : opSem d O (.const dst v) c = some ⟨c.pc + 1, c.head,
    Function.update c.tape (c.head + dst) (v : ℝ), c.queries⟩ := rfl
theorem opSem_add (dst a b : ℤ) : opSem d O (.add dst a b) c = some ⟨c.pc + 1, c.head,
    Function.update c.tape (c.head + dst) (c.tape (c.head + a) + c.tape (c.head + b)), c.queries⟩ := rfl
theorem opSem_sub (dst a b : ℤ) : opSem d O (.sub dst a b) c = some ⟨c.pc + 1, c.head,
    Function.update c.tape (c.head + dst) (c.tape (c.head + a) - c.tape (c.head + b)), c.queries⟩ := rfl
theorem opSem_mul (dst a b : ℤ) : opSem d O (.mul dst a b) c = some ⟨c.pc + 1, c.head,
    Function.update c.tape (c.head + dst) (c.tape (c.head + a) * c.tape (c.head + b)), c.queries⟩ := rfl
theorem opSem_shift (o : ℤ) : opSem d O (.shift o) c = some ⟨c.pc + 1, c.head + o, c.tape, c.queries⟩ := rfl
theorem opSem_div_of (dst a b : ℤ) (h : c.tape (c.head + b) ≠ 0) : opSem d O (.div dst a b) c =
    some ⟨c.pc + 1, c.head,
      Function.update c.tape (c.head + dst) (c.tape (c.head + a) / c.tape (c.head + b)), c.queries⟩ := by
  simp [opSem, h]

end OpLemmas

theorem qv2_eq (c : RayConfiguration) (w : Fin 2 → ℝ) (h0 : c.tape c.head = w 0)
    (h1 : c.tape (c.head + 1) = w 1) : qv 2 c = w := by
  funext k; fin_cases k
  · simpa [qv] using h0
  · simpa [qv] using h1

theorem opSem_query_of (O : (Fin 2 → ℝ) → Fin 2 → ℝ) (c : RayConfiguration) (w : Fin 2 → ℝ)
    (h0 : c.tape c.head = w 0) (h1 : c.tape (c.head + 1) = w 1) (hne : w ≠ 0) :
    opSem 2 O .query c = some ⟨c.pc + 1, c.head,
      (fun j => if h : 0 ≤ j - c.head ∧ j - c.head < ((2 : ℕ) : ℤ) then
        O w ⟨(j - c.head).toNat, by omega⟩ else c.tape j), c.queries + 1⟩ := by
  have hq := qv2_eq c w h0 h1
  simp only [opSem, hq, if_neg hne]

/-! ## Chunk 2c: midpoint (d = 2) -/

section Midpoint

def midOps (pBase qBase B : ℤ) : List Op :=
  [.const (B + 2) 2, .add B pBase qBase, .div B B (B + 2),
   .add (B + 1) (pBase + 1) (qBase + 1), .div (B + 1) (B + 1) (B + 2)]

def midDest (pBase qBase minBase : ℤ) : ℤ := max minBase (max pBase qBase + 2)

def midProg (pBase qBase minBase : ℤ) : List RayInstruction :=
  mkProg (midOps pBase qBase (midDest pBase qBase minBase))

theorem mid_core (oracle : (Fin 2 → ℝ) → Fin 2 → ℝ) (source : ℤ → ℝ)
    (pBase qBase B : ℤ) (q : ℕ) (hp : pBase + 2 ≤ B) (hq : qBase + 2 ≤ B) :
    ∃ c' : RayConfiguration,
      rayMachineRun (mkProg (midOps pBase qBase B)) oracle 5 ⟨0, 0, source, q⟩ = some c' ∧
      c'.pc = 5 ∧ (mkProg (midOps pBase qBase B))[c'.pc]? = some .halt ∧
      c'.head = 0 ∧ c'.queries = q ∧
      (∀ i : Fin 2, c'.tape (B + (i.val : ℤ)) =
          (source (pBase + (i.val : ℤ)) + source (qBase + (i.val : ℤ))) / 2) ∧
      (∀ z : ℤ, z < B → c'.tape z = source z) := by
  have hlen : 5 = (midOps pBase qBase B).length := rfl
  rw [hlen, run_mkProg oracle _ _ rfl]
  have h1 : pBase ≠ B + 2 := by omega
  have h2 : qBase ≠ B + 2 := by omega
  have h3 : pBase + 1 ≠ B + 2 := by omega
  have h4 : qBase + 1 ≠ B + 2 := by omega
  have h5 : pBase + 1 ≠ B := by omega
  have h6 : qBase + 1 ≠ B := by omega
  have h7 : B ≠ B + 2 := by omega
  have h8 : B + 1 ≠ B + 2 := by omega
  have h9 : B + 1 ≠ B := by omega
  simp [foldOps, midOps, opSem, Function.update_apply, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  refine ⟨mkProg_halt _, ?_⟩
  intro z hz
  have a1 : z ≠ B := by omega
  have a2 : z ≠ B + 1 := by omega
  have a3 : z ≠ B + 2 := by omega
  simp [a1, a2, a3]

theorem midW_spec (oracle : (Fin 2 → ℝ) → Fin 2 → ℝ) (source : ℤ → ℝ)
    (pBase qBase minBase : ℤ) (q : ℕ) :
    let prog := midProg pBase qBase minBase
    let outBase := midDest pBase qBase minBase
    let steps := 5
    minBase ≤ outBase ∧
    ∃ c' : RayConfiguration,
      rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
      c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
      c'.head = 0 ∧ c'.queries = q ∧
      (∀ i : Fin 2,
        c'.tape (outBase + (i.val : ℤ)) =
          (source (pBase + (i.val : ℤ)) + source (qBase + (i.val : ℤ))) / 2) ∧
      (∀ z : ℤ, z < outBase → c'.tape z = source z) := by
  intro prog outBase steps
  have hB1 : minBase ≤ outBase := le_max_left _ _
  have hB2 : max pBase qBase + 2 ≤ outBase := le_max_right _ _
  have hp : pBase ≤ max pBase qBase := le_max_left _ _
  have hq : qBase ≤ max pBase qBase := le_max_right _ _
  exact ⟨hB1, mid_core oracle source pBase qBase outBase q (by omega) (by omega)⟩

end Midpoint

/-! ## Chunk 2d: perturbed ray query (d = 2) -/

section Perturbed

def pertOps (pBase uBase epsCell B : ℤ) : List Op :=
  [.mul B epsCell uBase, .add B pBase B, .mul (B + 1) epsCell (uBase + 1),
   .add (B + 1) (pBase + 1) (B + 1), .shift B, .query, .shift (-B)]

def pertDest (pBase uBase epsCell minBase : ℤ) : ℤ :=
  max minBase (max (max pBase uBase) epsCell + 2)

def pertProg (pBase uBase epsCell minBase : ℤ) : List RayInstruction :=
  mkProg (pertOps pBase uBase epsCell (pertDest pBase uBase epsCell minBase))

theorem pert_core (oracle : (Fin 2 → ℝ) → Fin 2 → ℝ) (source : ℤ → ℝ)
    (pBase uBase epsCell B : ℤ) (q : ℕ) (hp : pBase + 2 ≤ B) (hu : uBase + 2 ≤ B)
    (he : epsCell + 2 ≤ B)
    (hne : (fun i : Fin 2 =>
        source (pBase + (i.val : ℤ)) + source epsCell * source (uBase + (i.val : ℤ))) ≠ 0) :
    ∃ c' : RayConfiguration,
      rayMachineRun (mkProg (pertOps pBase uBase epsCell B)) oracle 7 ⟨0, 0, source, q⟩ = some c' ∧
      c'.pc = 7 ∧ (mkProg (pertOps pBase uBase epsCell B))[c'.pc]? = some .halt ∧
      c'.head = 0 ∧ c'.queries = q + 1 ∧
      (∀ i : Fin 2,
        c'.tape (B + (i.val : ℤ)) =
          oracle (fun j : Fin 2 =>
            source (pBase + (j.val : ℤ)) + source epsCell * source (uBase + (j.val : ℤ))) i) ∧
      (∀ z : ℤ, z < B → c'.tape z = source z) := by
  have hlen : 7 = (pertOps pBase uBase epsCell B).length := rfl
  rw [hlen, run_mkProg oracle _ _ rfl]
  have a1 : uBase ≠ B := by omega
  have a2 : pBase + 1 ≠ B := by omega
  have a3 : uBase + 1 ≠ B := by omega
  have a4 : epsCell ≠ B := by omega
  have a5 : B + 1 ≠ B := by omega
  have a6 : pBase ≠ B := by omega
  have a7 : epsCell ≠ B + 1 := by omega
  have a8 : uBase + 1 ≠ B + 1 := by omega
  have a9 : pBase + 1 ≠ B + 1 := by omega
  simp only [foldOps, pertOps, opSem_mul, opSem_add, opSem_shift, Option.bind_some]
  rw [opSem_query_of oracle _ _ (by simp [Function.update_apply, a1, a4, a5, a6])
    (by simp [Function.update_apply, a2, a3, a4, a5, a7, a8, a9]) hne]
  simp only [Option.bind_some, foldOps, opSem_shift]
  refine ⟨_, rfl, rfl, mkProg_halt _, by simp, rfl, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp
  · intro z hz
    have b1 : ¬ (0 ≤ z - (0 + B)) := by omega
    have b2 : z ≠ B := by omega
    have b3 : z ≠ B + 1 := by omega
    simp only [b1, false_and, dite_false]
    simp [Function.update_apply, b2, b3]

theorem pertW_spec (oracle : (Fin 2 → ℝ) → Fin 2 → ℝ) (source : ℤ → ℝ)
    (pBase uBase epsCell minBase : ℤ) (q : ℕ) :
    (fun i : Fin 2 =>
      source (pBase + (i.val : ℤ)) + source epsCell * source (uBase + (i.val : ℤ))) ≠ 0 →
    let prog := pertProg pBase uBase epsCell minBase
    let outBase := pertDest pBase uBase epsCell minBase
    let steps := 7
    minBase ≤ outBase ∧
    ∃ c' : RayConfiguration,
      rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
      c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
      c'.head = 0 ∧ c'.queries = q + 1 ∧
      (∀ i : Fin 2,
        c'.tape (outBase + (i.val : ℤ)) =
          oracle (fun j : Fin 2 =>
            source (pBase + (j.val : ℤ)) + source epsCell * source (uBase + (j.val : ℤ))) i) ∧
      (∀ z : ℤ, z < outBase → c'.tape z = source z) := by
  intro hne prog outBase steps
  have hB1 : minBase ≤ outBase := le_max_left _ _
  have hB2 : max (max pBase uBase) epsCell + 2 ≤ outBase := le_max_right _ _
  have h1 : max pBase uBase ≤ max (max pBase uBase) epsCell := le_max_left _ _
  have h2 : epsCell ≤ max (max pBase uBase) epsCell := le_max_right _ _
  have h3 : pBase ≤ max pBase uBase := le_max_left _ _
  have h4 : uBase ≤ max pBase uBase := le_max_right _ _
  exact ⟨hB1, pert_core oracle source pBase uBase epsCell outBase q (by omega) (by omega)
    (by omega) hne⟩

end Perturbed

/-! ## Chunk 2e: Cramer row (d = 2) -/

section Cramer

def cramOps (vBase B : ℤ) : List Op :=
  [.mul B vBase (vBase + 3), .mul (B + 1) (vBase + 1) (vBase + 2), .sub (B + 2) B (B + 1),
   .sub B (vBase + 3) (vBase + 1), .div B B (B + 2),
   .sub (B + 1) vBase (vBase + 2), .div (B + 1) (B + 1) (B + 2)]

def cramDest (vBase minBase : ℤ) : ℤ := max minBase (vBase + 4)

def cramProg (vBase minBase : ℤ) : List RayInstruction := mkProg (cramOps vBase (cramDest vBase minBase))

theorem cram_core (oracle : (Fin 2 → ℝ) → Fin 2 → ℝ) (source : ℤ → ℝ)
    (vBase B : ℤ) (q : ℕ) (hB : vBase + 4 ≤ B)
    (hdet : source vBase * source (vBase + 3) - source (vBase + 1) * source (vBase + 2) ≠ 0) :
    ∃ c' : RayConfiguration,
      rayMachineRun (mkProg (cramOps vBase B)) oracle 7 ⟨0, 0, source, q⟩ = some c' ∧
      c'.pc = 7 ∧ (mkProg (cramOps vBase B))[c'.pc]? = some .halt ∧
      c'.head = 0 ∧ c'.queries = q ∧
      c'.tape B = (source (vBase + 3) - source (vBase + 1)) /
        (source vBase * source (vBase + 3) - source (vBase + 1) * source (vBase + 2)) ∧
      c'.tape (B + 1) = (source vBase - source (vBase + 2)) /
        (source vBase * source (vBase + 3) - source (vBase + 1) * source (vBase + 2)) ∧
      (∀ z : ℤ, z < B → c'.tape z = source z) := by
  have hlen : 7 = (cramOps vBase B).length := rfl
  rw [hlen, run_mkProg oracle _ _ rfl]
  have a0 : vBase ≠ B := by omega
  have a1 : vBase + 1 ≠ B := by omega
  have a2 : vBase + 2 ≠ B := by omega
  have a3 : vBase + 3 ≠ B := by omega
  have b0 : vBase ≠ B + 1 := by omega
  have b1 : vBase + 1 ≠ B + 1 := by omega
  have b2 : vBase + 2 ≠ B + 1 := by omega
  have b3 : vBase + 3 ≠ B + 1 := by omega
  have c0 : vBase ≠ B + 2 := by omega
  have c1 : vBase + 1 ≠ B + 2 := by omega
  have c2 : vBase + 2 ≠ B + 2 := by omega
  have c3 : vBase + 3 ≠ B + 2 := by omega
  have e1 : B ≠ B + 1 := by omega
  have e2 : B ≠ B + 2 := by omega
  have e3 : B + 1 ≠ B + 2 := by omega
  simp [foldOps, cramOps, opSem, Function.update_apply, a0, a1, a2, a3, b0, b1, b2, b3,
    c0, c1, c2, c3, e1, e2, e3, Ne.symm e1, Ne.symm e2, Ne.symm e3, hdet]
  refine ⟨mkProg_halt _, ?_⟩
  intro z hz
  have z1 : z ≠ B := by omega
  have z2 : z ≠ B + 1 := by omega
  have z3 : z ≠ B + 2 := by omega
  simp [z1, z2, z3]

theorem cramW_spec (oracle : (Fin 2 → ℝ) → Fin 2 → ℝ) (source : ℤ → ℝ)
    (vBase minBase : ℤ) (q : ℕ) :
    let v : Matrix (Fin 2) (Fin 2) ℝ :=
      fun i j => source (vBase + (i.val : ℤ) * ((2 : ℕ) : ℤ) + (j.val : ℤ))
    v.det ≠ 0 →
    let prog := cramProg vBase minBase
    let outBase := cramDest vBase minBase
    let steps := 7
    minBase ≤ outBase ∧
    ∃ c' : RayConfiguration,
      rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
      c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
      c'.head = 0 ∧ c'.queries = q ∧
      (∀ k : Fin 2,
        c'.tape (outBase + (k.val : ℤ)) =
          (v.updateCol k (fun _ => 1)).det / v.det) ∧
      (∀ z : ℤ, z < outBase → c'.tape z = source z) := by
  intro v hdet prog outBase steps
  have hdv : v.det = source vBase * source (vBase + 3) - source (vBase + 1) * source (vBase + 2) := by
    rw [Matrix.det_fin_two]
    simp only [v]
    norm_num <;> (try ring_nf) <;> simp
  have hB1 : minBase ≤ outBase := le_max_left _ _
  have hB2 : vBase + 4 ≤ outBase := le_max_right _ _
  obtain ⟨c', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    cram_core oracle source vBase outBase q hB2 (hdv ▸ hdet)
  refine ⟨hB1, c', h1, h2, h3, h4, h5, ?_, h8⟩
  intro k
  rw [hdv]
  fin_cases k
  · simp only [Fin.zero_eta, Fin.val_zero, Nat.cast_zero, add_zero, h6]
    congr 1
    rw [Matrix.det_fin_two]
    simp [Matrix.updateCol, v]
    (try ring_nf)
  · simp only [Fin.mk_one, Fin.val_one, Nat.cast_one, h7]
    congr 1
    rw [Matrix.det_fin_two]
    simp [Matrix.updateCol, v]
    (try ring_nf)

end Cramer


/-! ## Chunk 2f: stepEps (d = 2, general k) -/

section StepEps

noncomputable def rvE (source : ℤ → ℝ) (rowBase xBase : ℤ) (j : ℕ) : ℝ :=
  source (rowBase + (j : ℤ) * 2) * source xBase + source (rowBase + (j : ℤ) * 2 + 1) * source (xBase + 1)

def rowAOps (r0 pBase B : ℤ) : List Op :=
  [.mul (B + 5) r0 pBase, .mul (B + 6) (r0 + 1) (pBase + 1), .add (B + 5) (B + 5) (B + 6),
   .sub (B + 5) (B + 3) (B + 5), .add (B + 6) (B + 3) (B + 5), .div (B + 5) (B + 5) (B + 6),
   .mul (B + 1) (B + 1) (B + 5)]

def rowBOps (r0 uBase B : ℤ) : List Op :=
  [.mul (B + 7) r0 uBase, .mul (B + 8) (r0 + 1) (uBase + 1), .add (B + 7) (B + 7) (B + 8),
   .mul (B + 7) (B + 7) (B + 7), .add (B + 2) (B + 2) (B + 7)]

def rowOps (r0 pBase uBase B : ℤ) : List Op := rowAOps r0 pBase B ++ rowBOps r0 uBase B

def initOps (B : ℤ) : List Op := [.const (B + 1) 1, .const (B + 2) 1, .const (B + 3) 1, .const (B + 4) 2]

def finOps (aCell B : ℤ) : List Op :=
  [.mul (B + 5) aCell (B + 2), .add (B + 5) (B + 3) (B + 5), .add (B + 5) (B + 5) (B + 1),
   .mul (B + 5) (B + 4) (B + 5), .mul (B + 6) aCell (B + 1), .div B (B + 6) (B + 5)]

def rowsOps (rowBase pBase uBase B : ℤ) : ℕ → List Op
  | 0 => []
  | n + 1 => rowsOps rowBase pBase uBase B n ++ rowOps (rowBase + (n : ℤ) * 2) pBase uBase B

theorem rowsOps_length (rowBase pBase uBase B : ℤ) (n : ℕ) :
    (rowsOps rowBase pBase uBase B n).length = 12 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rowsOps, ih, rowOps, rowAOps, rowBOps]; ring

theorem foldOps_append {d : ℕ} (O : (Fin d → ℝ) → Fin d → ℝ) :
    ∀ (l1 l2 : List Op) (c : RayConfiguration),
      foldOps d O (l1 ++ l2) c = (foldOps d O l1 c).bind (foldOps d O l2) := by
  intro l1
  induction l1 with
  | nil => intro l2 c; rfl
  | cons o os ih =>
    intro l2 c
    simp only [List.cons_append, foldOps]
    cases opSem d O o c with
    | none => rfl
    | some c1 => simp [ih]

def Good (source : ℤ → ℝ) (rowBase pBase uBase B : ℤ) (q n : ℕ) (c : RayConfiguration) : Prop :=
  c.pc = 4 + 12 * n ∧ c.head = 0 ∧ c.queries = q ∧
  c.tape (B + 1) = ∏ j ∈ Finset.range n,
      (1 - rvE source rowBase pBase j) / (1 + (1 - rvE source rowBase pBase j)) ∧
  c.tape (B + 2) = 1 + ∑ j ∈ Finset.range n, (rvE source rowBase uBase j) ^ 2 ∧
  c.tape (B + 3) = 1 ∧ c.tape (B + 4) = 2 ∧ ∀ z < B, c.tape z = source z

theorem init_good (O : (Fin 2 → ℝ) → Fin 2 → ℝ) (source : ℤ → ℝ) (rowBase pBase uBase B : ℤ)
    (q : ℕ) : ∃ c, foldOps 2 O (initOps B) ⟨0, 0, source, q⟩ = some c ∧
      Good source rowBase pBase uBase B q 0 c := by
  simp only [foldOps, initOps, opSem, Option.bind_some]
  refine ⟨_, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Function.update_apply]
  · simp [Function.update_apply]
  · simp [Function.update_apply]
  · simp [Function.update_apply]
  · intro z hz
    have a1 : z ≠ B + 1 := by omega
    have a2 : z ≠ B + 2 := by omega
    have a3 : z ≠ B + 3 := by omega
    have a4 : z ≠ B + 4 := by omega
    simp [Function.update_apply, a1, a2, a3, a4]

theorem rowA_spec (O : (Fin 2 → ℝ) → Fin 2 → ℝ) (c : RayConfiguration) (r0 pBase B : ℤ)
    (hh : c.head = 0) (hr : r0 + 2 ≤ B) (hp : pBase + 2 ≤ B) (h3 : c.tape (B + 3) = 1)
    (hden : (1 : ℝ) + (1 - (c.tape r0 * c.tape pBase + c.tape (r0 + 1) * c.tape (pBase + 1))) ≠ 0) :
    ∃ c1, foldOps 2 O (rowAOps r0 pBase B) c = some c1 ∧ c1.pc = c.pc + 7 ∧ c1.head = 0 ∧
      c1.queries = c.queries ∧
      c1.tape (B + 1) = c.tape (B + 1) *
        ((1 - (c.tape r0 * c.tape pBase + c.tape (r0 + 1) * c.tape (pBase + 1))) /
          (1 + (1 - (c.tape r0 * c.tape pBase + c.tape (r0 + 1) * c.tape (pBase + 1))))) ∧
      ∀ z, z ≠ B + 1 → z ≠ B + 5 → z ≠ B + 6 → c1.tape z = c.tape z := by
  obtain ⟨pc, head, T, qq⟩ := c
  simp only at hh h3 hden ⊢
  subst hh
  have f0_1 : r0 ≠ B + 1 := by omega
  have f0_5 : r0 ≠ B + 5 := by omega
  have f0_6 : r0 ≠ B + 6 := by omega
  have f1_1 : r0 + 1 ≠ B + 1 := by omega
  have f1_5 : r0 + 1 ≠ B + 5 := by omega
  have f1_6 : r0 + 1 ≠ B + 6 := by omega
  have f2_1 : pBase ≠ B + 1 := by omega
  have f2_5 : pBase ≠ B + 5 := by omega
  have f2_6 : pBase ≠ B + 6 := by omega
  have f3_1 : pBase + 1 ≠ B + 1 := by omega
  have f3_5 : pBase + 1 ≠ B + 5 := by omega
  have f3_6 : pBase + 1 ≠ B + 6 := by omega
  simp [foldOps, rowAOps, opSem, Function.update_apply, h3, hden, f0_1, f0_5, f0_6, f1_1, f1_5, f1_6, f2_1, f2_5, f2_6, f3_1, f3_5, f3_6]
  intro z a1 a5 a6
  simp [a1, a5, a6]

theorem rowB_spec (O : (Fin 2 → ℝ) → Fin 2 → ℝ) (c : RayConfiguration) (r0 uBase B : ℤ)
    (hh : c.head = 0) (hr : r0 + 2 ≤ B) (hu : uBase + 2 ≤ B) :
    ∃ c1, foldOps 2 O (rowBOps r0 uBase B) c = some c1 ∧ c1.pc = c.pc + 5 ∧ c1.head = 0 ∧
      c1.queries = c.queries ∧
      c1.tape (B + 2) = c.tape (B + 2) +
        (c.tape r0 * c.tape uBase + c.tape (r0 + 1) * c.tape (uBase + 1)) *
        (c.tape r0 * c.tape uBase + c.tape (r0 + 1) * c.tape (uBase + 1)) ∧
      ∀ z, z ≠ B + 2 → z ≠ B + 7 → z ≠ B + 8 → c1.tape z = c.tape z := by
  obtain ⟨pc, head, T, qq⟩ := c
  simp only at hh ⊢
  subst hh
  have g0_2 : r0 ≠ B + 2 := by omega
  have g0_7 : r0 ≠ B + 7 := by omega
  have g0_8 : r0 ≠ B + 8 := by omega
  have g1_2 : r0 + 1 ≠ B + 2 := by omega
  have g1_7 : r0 + 1 ≠ B + 7 := by omega
  have g1_8 : r0 + 1 ≠ B + 8 := by omega
  have g2_2 : uBase ≠ B + 2 := by omega
  have g2_7 : uBase ≠ B + 7 := by omega
  have g2_8 : uBase ≠ B + 8 := by omega
  have g3_2 : uBase + 1 ≠ B + 2 := by omega
  have g3_7 : uBase + 1 ≠ B + 7 := by omega
  have g3_8 : uBase + 1 ≠ B + 8 := by omega
  simp [foldOps, rowBOps, opSem, Function.update_apply, g0_2, g0_7, g0_8, g1_2, g1_7, g1_8, g2_2, g2_7, g2_8, g3_2, g3_7, g3_8]
  intro z a1 a5 a6
  simp [a1, a5, a6]

theorem row_step (O : (Fin 2 → ℝ) → Fin 2 → ℝ) (source : ℤ → ℝ) (rowBase pBase uBase B : ℤ)
    (q n : ℕ) (c : RayConfiguration)
    (hr : rowBase + (n : ℤ) * 2 + 2 ≤ B) (hp : pBase + 2 ≤ B) (hu : uBase + 2 ≤ B)
    (hrow : rvE source rowBase pBase n < 1) (hG : Good source rowBase pBase uBase B q n c) :
    ∃ c', foldOps 2 O (rowOps (rowBase + (n : ℤ) * 2) pBase uBase B) c = some c' ∧
      Good source rowBase pBase uBase B q (n + 1) c' := by
  obtain ⟨hpc, hh, hq, h1, h2, h3, h4, hT⟩ := hG
  have t0 := hT (rowBase + (n : ℤ) * 2) (by omega)
  have t1 := hT (rowBase + (n : ℤ) * 2 + 1) (by omega)
  have t2 := hT pBase (by omega)
  have t3 := hT (pBase + 1) (by omega)
  have t4 := hT uBase (by omega)
  have t5 := hT (uBase + 1) (by omega)
  have hrv : rvE source rowBase pBase n = source (rowBase + (n : ℤ) * 2) * source pBase +
      source (rowBase + (n : ℤ) * 2 + 1) * source (pBase + 1) := rfl
  have hrv' : rvE source rowBase uBase n = source (rowBase + (n : ℤ) * 2) * source uBase +
      source (rowBase + (n : ℤ) * 2 + 1) * source (uBase + 1) := rfl
  have hden : (1 : ℝ) + (1 - (c.tape (rowBase + (n : ℤ) * 2) * c.tape pBase +
      c.tape (rowBase + (n : ℤ) * 2 + 1) * c.tape (pBase + 1))) ≠ 0 := by
    rw [t0, t1, t2, t3, ← hrv]; intro h; linarith
  obtain ⟨c1, e1, p1, hh1, q1, v1, fr1⟩ :=
    rowA_spec O c (rowBase + (n : ℤ) * 2) pBase B hh (by omega) hp h3 hden
  obtain ⟨c2, e2, p2, hh2, q2, v2, fr2⟩ :=
    rowB_spec O c1 (rowBase + (n : ℤ) * 2) uBase B hh1 (by omega) hu
  refine ⟨c2, ?_, ?_, hh2, by rw [q2, q1, hq], ?_, ?_, ?_, ?_, ?_⟩
  · rw [rowOps, foldOps_append, e1]
    simpa using e2
  · rw [p2, p1, hpc]; ring
  · rw [fr2 _ (by omega) (by omega) (by omega), v1, t0, t1, t2, t3, h1, ← hrv,
      Finset.prod_range_succ]
  · rw [v2, fr1 _ (by omega) (by omega) (by omega), fr1 _ (by omega) (by omega) (by omega),
      fr1 _ (by omega) (by omega) (by omega), fr1 _ (by omega) (by omega) (by omega),
      fr1 _ (by omega) (by omega) (by omega), t0, t1, t4, t5, h2, ← hrv', Finset.sum_range_succ]
    ring
  · rw [fr2 _ (by omega) (by omega) (by omega), fr1 _ (by omega) (by omega) (by omega), h3]
  · rw [fr2 _ (by omega) (by omega) (by omega), fr1 _ (by omega) (by omega) (by omega), h4]
  · intro z hz
    rw [fr2 _ (by omega) (by omega) (by omega), fr1 _ (by omega) (by omega) (by omega), hT z hz]

theorem rows_good (O : (Fin 2 → ℝ) → Fin 2 → ℝ) (source : ℤ → ℝ) (rowBase pBase uBase B : ℤ)
    (q k : ℕ) (c0 : RayConfiguration) (h0 : Good source rowBase pBase uBase B q 0 c0)
    (hr : rowBase + (k : ℤ) * 2 ≤ B) (hp : pBase + 2 ≤ B) (hu : uBase + 2 ≤ B)
    (hrow : ∀ j < k, rvE source rowBase pBase j < 1) :
    ∀ n ≤ k, ∃ c, foldOps 2 O (rowsOps rowBase pBase uBase B n) c0 = some c ∧
      Good source rowBase pBase uBase B q n c := by
  intro n
  induction n with
  | zero => intro _; exact ⟨c0, rfl, h0⟩
  | succ n ih =>
    intro hn
    obtain ⟨c, hc, hG⟩ := ih (by omega)
    obtain ⟨c', hc', hG'⟩ := row_step O source rowBase pBase uBase B q n c
      (by have : (n : ℤ) + 1 ≤ k := by exact_mod_cast hn
          linarith) hp hu (hrow n (by omega)) hG
    refine ⟨c', ?_, hG'⟩
    rw [rowsOps, foldOps_append, hc]
    simpa using hc'

theorem fin_step (O : (Fin 2 → ℝ) → Fin 2 → ℝ) (source : ℤ → ℝ) (aCell B : ℤ) (c : RayConfiguration)
    (δv Mv : ℝ) (ha : 0 < source aCell) (hδ : 0 < δv) (hM : 1 ≤ Mv) (hB : aCell + 1 ≤ B)
    (hh : c.head = 0) (h1 : c.tape (B + 1) = δv) (h2 : c.tape (B + 2) = Mv)
    (h3 : c.tape (B + 3) = 1) (h4 : c.tape (B + 4) = 2) (hT : ∀ z < B, c.tape z = source z) :
    ∃ c', foldOps 2 O (finOps aCell B) c = some c' ∧ c'.pc = c.pc + 6 ∧ c'.head = 0 ∧
      c'.queries = c.queries ∧
      c'.tape B = source aCell * δv / (2 * (1 + source aCell * Mv + δv)) ∧
      ∀ z < B, c'.tape z = source z := by
  obtain ⟨pc, head, T, qq⟩ := c
  simp only at hh h1 h2 h3 h4 hT
  subst hh
  have t0 : T aCell = source aCell := hT _ (by omega)
  have g5 : aCell ≠ B + 5 := by omega
  have g6 : aCell ≠ B + 6 := by omega
  have g1 : aCell ≠ B + 1 := by omega
  have g2 : aCell ≠ B + 2 := by omega
  have hpos : 0 < 2 * (1 + source aCell * Mv + δv) := by nlinarith
  simp only [foldOps, finOps, opSem, Option.bind_some]
  rw [if_neg]
  · simp only [Option.bind_some]
    refine ⟨_, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · simp [Function.update_apply, t0, h1, h2, h3, h4, g1, g2, g5, g6]
    · intro z hz
      have a0 : z ≠ B := by omega
      have a5 : z ≠ B + 5 := by omega
      have a6 : z ≠ B + 6 := by omega
      simp [Function.update_apply, a0, a5, a6, hT z hz]
  · simp [Function.update_apply, t0, h1, h2, h3, h4, g1, g2, g5, g6]
    intro h
    have : 2 * (1 + source aCell * Mv + δv) = 0 := by linarith
    linarith

def stepDest (k : ℕ) (rowBase pBase uBase aCell minBase : ℤ) : ℤ :=
  max minBase (max (max (rowBase + (k : ℤ) * 2) (max pBase uBase + 2)) (aCell + 1))

def stepProg (k : ℕ) (rowBase pBase uBase aCell minBase : ℤ) : List RayInstruction :=
  let B := stepDest k rowBase pBase uBase aCell minBase
  mkProg (initOps B ++ rowsOps rowBase pBase uBase B k ++ finOps aCell B)

theorem rowVal_eq (source : ℤ → ℝ) (rowBase x : ℤ) (j : ℕ) :
    (∑ i : Fin 2, source (rowBase + (j : ℤ) * ((2 : ℕ) : ℤ) + (i.val : ℤ)) * source (x + (i.val : ℤ)))
      = rvE source rowBase x j := by
  simp [Fin.sum_univ_two, rvE]

theorem stepW_spec {k : ℕ} (oracle : (Fin 2 → ℝ) → Fin 2 → ℝ) (source : ℤ → ℝ)
    (rowBase pBase uBase aCell minBase : ℤ) (q : ℕ) :
    0 < source aCell →
    (∀ j : Fin k,
      ∑ i : Fin 2, source (rowBase + (j.val : ℤ) * ((2 : ℕ) : ℤ) + (i.val : ℤ)) *
        source (pBase + (i.val : ℤ)) < 1) →
    let prog := stepProg k rowBase pBase uBase aCell minBase
    let dst := stepDest k rowBase pBase uBase aCell minBase
    let steps := 12 * k + 10
    let rowVal (j : Fin k) (xBase : ℤ) : ℝ :=
      ∑ i : Fin 2, source (rowBase + (j.val : ℤ) * ((2 : ℕ) : ℤ) + (i.val : ℤ)) *
        source (xBase + (i.val : ℤ))
    let δ : ℝ := ∏ j : Fin k, (1 - rowVal j pBase) / (1 + (1 - rowVal j pBase))
    let M : ℝ := 1 + ∑ j : Fin k, (rowVal j uBase) ^ 2
    minBase ≤ dst ∧
    ∃ c' : RayConfiguration,
      rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
      c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
      c'.head = 0 ∧ c'.queries = q ∧
      c'.tape dst = source aCell * δ / (2 * (1 + source aCell * M + δ)) ∧
      ∀ z : ℤ, z < dst → c'.tape z = source z := by
  intro ha hrows prog dst steps rowVal δ M
  set B := stepDest k rowBase pBase uBase aCell minBase with hBdef
  have hB1 : minBase ≤ B := le_max_left _ _
  have hB2 : max (max (rowBase + (k : ℤ) * 2) (max pBase uBase + 2)) (aCell + 1) ≤ B := le_max_right _ _
  have m1 := le_max_left (max (rowBase + (k : ℤ) * 2) (max pBase uBase + 2)) (aCell + 1)
  have m2 := le_max_right (max (rowBase + (k : ℤ) * 2) (max pBase uBase + 2)) (aCell + 1)
  have m3 := le_max_left (rowBase + (k : ℤ) * 2) (max pBase uBase + 2)
  have m4 := le_max_right (rowBase + (k : ℤ) * 2) (max pBase uBase + 2)
  have m5 := le_max_left pBase uBase
  have m6 := le_max_right pBase uBase
  have hrow : ∀ j < k, rvE source rowBase pBase j < 1 := by
    intro j hj
    have := hrows ⟨j, hj⟩
    rwa [rowVal_eq] at this
  have hδeq : δ = ∏ j ∈ Finset.range k,
      (1 - rvE source rowBase pBase j) / (1 + (1 - rvE source rowBase pBase j)) := by
    simp only [δ, rowVal, rowVal_eq]
    exact Fin.prod_univ_eq_prod_range (fun j => (1 - rvE source rowBase pBase j) /
      (1 + (1 - rvE source rowBase pBase j))) k
  have hMeq : M = 1 + ∑ j ∈ Finset.range k, (rvE source rowBase uBase j) ^ 2 := by
    simp only [M, rowVal, rowVal_eq]
    rw [Fin.sum_univ_eq_sum_range (fun j => (rvE source rowBase uBase j) ^ 2) k]
  have hδpos : 0 < δ := by
    rw [hδeq]
    apply Finset.prod_pos
    intro j hj
    have := hrow j (Finset.mem_range.mp hj)
    apply div_pos <;> linarith
  have hM1 : 1 ≤ M := by
    rw [hMeq]
    have : 0 ≤ ∑ j ∈ Finset.range k, (rvE source rowBase uBase j) ^ 2 :=
      Finset.sum_nonneg (fun j _ => sq_nonneg _)
    linarith
  refine ⟨hB1, ?_⟩
  obtain ⟨c0, hc0, hG0⟩ := init_good oracle source rowBase pBase uBase B q
  obtain ⟨c1, hc1, hG1⟩ := rows_good oracle source rowBase pBase uBase B q k c0 hG0
    (by omega) (by omega) (by omega) hrow k le_rfl
  obtain ⟨hpc1, hh1, hq1, h11, h12, h13, h14, hT1⟩ := hG1
  obtain ⟨c2, hc2, hpc2, hh2, hq2, hval, hT2⟩ := fin_step oracle source aCell B c1 δ M ha hδpos hM1
    (by omega) hh1 (by rw [h11, hδeq]) (by rw [h12, hMeq]) h13 h14 hT1
  have hlen : steps = (initOps B ++ rowsOps rowBase pBase uBase B k ++ finOps aCell B).length := by
    simp [steps, rowsOps_length, initOps, finOps] <;> omega
  have hrun : rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c2 := by
    rw [hlen]
    show rayMachineRun (mkProg _) oracle _ _ = _
    rw [run_mkProg oracle _ _ rfl, foldOps_append, foldOps_append, hc0]
    simp only [Option.bind_some]
    rw [hc1]
    simpa using hc2
  have hpcs : c2.pc = steps := by rw [hpc2, hpc1]; simp only [steps]; ring
  refine ⟨c2, hrun, hpcs, ?_, hh2, by rw [hq2, hq1], hval, hT2⟩
  rw [hpcs, hlen]
  exact mkProg_halt _

end StepEps


/-! ## Chunk 2i: relocation and local slack -/

section Relocate

def relocI (n : ℕ) : RayInstruction → RayInstruction
  | .constant dst v nx => .constant dst v (n + nx)
  | .add dst a b nx => .add dst a b (n + nx)
  | .sub dst a b nx => .sub dst a b (n + nx)
  | .mul dst a b nx => .mul dst a b (n + nx)
  | .div dst a b nx => .div dst a b (n + nx)
  | .branch a x y z => .branch a (n + x) (n + y) (n + z)
  | .shift o nx => .shift o (n + nx)
  | .query nx => .query (n + nx)
  | .halt => .halt

def relocC (n : ℕ) (c : RayConfiguration) : RayConfiguration :=
  ⟨n + c.pc, c.head, c.tape, c.queries⟩

theorem reloc_get (pre prog : List RayInstruction) (pc : ℕ) :
    (pre ++ prog.map (relocI pre.length))[pre.length + pc]? = (prog[pc]?).map (relocI pre.length) := by
  rw [List.getElem?_append_right (by omega)]
  simp

theorem reloc_step {d : ℕ} (pre prog : List RayInstruction) (O : (Fin d → ℝ) → Fin d → ℝ)
    (c : RayConfiguration) :
    rayMachineStep (pre ++ prog.map (relocI pre.length)) O (relocC pre.length c) =
      (rayMachineStep prog O c).map (relocC pre.length) := by
  obtain ⟨pc, head, T, qq⟩ := c
  unfold rayMachineStep
  simp only [relocC]
  rw [reloc_get]
  rcases h : prog[pc]? with _ | i
  · simp
  · cases i with
    | branch a x y z =>
      by_cases h1 : T (head + a) < 0
      · simp [relocI, relocC, h1]
      · by_cases h2 : T (head + a) = 0 <;> simp [relocI, relocC, h1, h2]
    | query nx =>
      by_cases h1 : (fun i : Fin d => T (head + ((i : ℕ) : ℤ))) = 0
      · simp [relocI, h1]
      · first
          | (simp only [relocI]; rw [if_neg h1, if_neg h1]; rfl)
          | (simp only [relocI, h1, if_false]; rfl)
          | (simp [relocI, relocC, h1])
    | _ => simp [relocI, relocC] <;> (try split_ifs) <;> (try simp_all) <;> (try rfl) <;> done

theorem reloc_run {d : ℕ} (pre prog : List RayInstruction) (O : (Fin d → ℝ) → Fin d → ℝ) :
    ∀ (t : ℕ) (c : RayConfiguration),
      rayMachineRun (pre ++ prog.map (relocI pre.length)) O t (relocC pre.length c) =
        (rayMachineRun prog O t c).map (relocC pre.length) := by
  intro t
  induction t with
  | zero => intro c; rfl
  | succ t ih =>
    intro c
    rw [run_succ, run_succ, reloc_step]
    cases rayMachineStep prog O c with
    | none => rfl
    | some c1 => simp [ih]

theorem relocW (pre program : List RayInstruction) (oracle : (Fin 2 → ℝ) → (Fin 2 → ℝ)) (t : ℕ)
    (c : RayConfiguration) :
      (relocC pre.length c).pc = pre.length + c.pc ∧
      (relocC pre.length c).head = c.head ∧
      (relocC pre.length c).tape = c.tape ∧
      (relocC pre.length c).queries = c.queries ∧
      rayMachineRun (pre ++ program.map (relocI pre.length)) oracle t
          (relocC pre.length c) =
        (rayMachineRun program oracle t c).map (relocC pre.length) ∧
      (program[c.pc]? = some .halt →
        (pre ++ program.map (relocI pre.length))[
          (relocC pre.length c).pc]? = some .halt) := by
  refine ⟨rfl, rfl, rfl, rfl, reloc_run pre program oracle t c, ?_⟩
  intro h
  show (pre ++ program.map (relocI pre.length))[pre.length + c.pc]? = _
  rw [reloc_get, h]
  rfl

end Relocate

theorem localSlackW : ∀ {k : ℕ} (L : Fin k → (Fin 2 → ℝ) →ₗ[ℝ] ℝ) (p u : Fin 2 → ℝ),
      (∀ j, L j p < 1) →
      let δ := ∏ j, (1 - L j p) / (1 + (1 - L j p))
      let M := 1 + ∑ j, (L j u) ^ 2
      0 < δ ∧ 0 ≤ M ∧ (∀ j, L j p ≤ 1 - δ) ∧ (∀ j, |L j u| ≤ M) := by
  intro k L p u hL δ M
  set f : Fin k → ℝ := fun j => (1 - L j p) / (1 + (1 - L j p)) with hf
  have hfj : ∀ j, 0 < f j ∧ f j ≤ 1 - L j p ∧ f j ≤ 1 := by
    intro j
    have h1 := hL j
    have hd : 0 < 1 + (1 - L j p) := by linarith
    refine ⟨div_pos (by linarith) hd, ?_, ?_⟩
    · rw [hf, div_le_iff₀ hd]; nlinarith
    · rw [hf, div_le_iff₀ hd]; linarith
  have hδ : δ = ∏ j, f j := rfl
  have hsum : 0 ≤ ∑ j, (L j u) ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  refine ⟨?_, by simp only [M]; linarith, ?_, ?_⟩
  · rw [hδ]; exact Finset.prod_pos (fun j _ => (hfj j).1)
  · intro j
    have hle : δ ≤ f j := by
      rw [hδ, ← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ j)]
      apply mul_le_of_le_one_right (hfj j).1.le
      exact Finset.prod_le_one (fun i _ => (hfj i).1.le) (fun i _ => (hfj i).2.2)
    linarith [(hfj j).2.1]
  · intro j
    have h1 : (L j u) ^ 2 ≤ ∑ i, (L i u) ^ 2 :=
      Finset.single_le_sum (f := fun i => (L i u) ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    have h2 : |L j u| ≤ 1 + (L j u) ^ 2 := by
      nlinarith [abs_nonneg (L j u), sq_abs (L j u), sq_nonneg (|L j u| - 1)]
    simp only [M]; linarith




/-! ## Chunk 2g/2h helpers -/

theorem run_add3 {d : ℕ} (prog : List RayInstruction) (O : (Fin d → ℝ) → Fin d → ℝ) :
    ∀ (a b : ℕ) (c : RayConfiguration), rayMachineRun prog O (a + b) c =
      (rayMachineRun prog O a c).bind (rayMachineRun prog O b) := by
  intro a
  induction a with
  | zero => intro b c; rw [Nat.zero_add]; rfl
  | succ a ih =>
    intro b c
    rw [show a + 1 + b = (a + b) + 1 by omega, run_succ, run_succ]
    cases rayMachineStep prog O c with
    | none => rfl
    | some c1 => exact ih b c1

theorem run_one {d : ℕ} (prog : List RayInstruction) (O : (Fin d → ℝ) → Fin d → ℝ)
    (c : RayConfiguration) : rayMachineRun prog O 1 c = rayMachineStep prog O c := by
  show (rayMachineStep prog O c).bind (rayMachineRun prog O 0) = _
  cases rayMachineStep prog O c <;> rfl

theorem foldOps_pc {d : ℕ} (O : (Fin d → ℝ) → Fin d → ℝ) :
    ∀ (l : List Op) (c c' : RayConfiguration), foldOps d O l c = some c' →
      c'.pc = c.pc + l.length := by
  intro l
  induction l with
  | nil => intro c c' h; simp [foldOps] at h; subst h; simp
  | cons o os ih =>
    intro c c' h
    simp only [foldOps] at h
    cases hs : opSem d O o c with
    | none => rw [hs] at h; simp at h
    | some c1 =>
      rw [hs, Option.bind_some] at h
      rw [ih c1 c' h, opSem_pc O o c c1 hs, List.length_cons]; omega

theorem step_branch {d : ℕ} (prog : List RayInstruction) (O : (Fin d → ℝ) → Fin d → ℝ)
    (c : RayConfiguration) (a : ℤ) (n e po : ℕ) (h : prog[c.pc]? = some (.branch a n e po)) :
    rayMachineStep prog O c = some ⟨if c.tape (c.head + a) < 0 then n else
      if c.tape (c.head + a) = 0 then e else po, c.head, c.tape, c.queries⟩ := by
  simp [rayMachineStep, h]

theorem step_const {d : ℕ} (prog : List RayInstruction) (O : (Fin d → ℝ) → Fin d → ℝ)
    (c : RayConfiguration) (dst : ℤ) (v : ℚ) (nx : ℕ) (h : prog[c.pc]? = some (.constant dst v nx)) :
    rayMachineStep prog O c = some ⟨nx, c.head, Function.update c.tape (c.head + dst) (v : ℝ), c.queries⟩ := by
  simp [rayMachineStep, h]

theorem prod_incl {V : ℕ} (a b : ℕ → ℝ) (P Q : Fin V → Prop)
    (ha : ∀ k : Fin V, a k = if P k then 1 else 0) (hb : ∀ k : Fin V, b k = if Q k then 1 else 0) :
    ∏ k ∈ Finset.range V, (a k * b k - a k + 1) = if (∀ k : Fin V, P k → Q k) then (1 : ℝ) else 0 := by
  rw [Finset.prod_range (fun k => a k * b k - a k + 1)]
  split_ifs with h
  · apply Finset.prod_eq_one
    intro k _
    rw [ha k, hb k]
    by_cases hp : P k
    · simp [hp, h k hp]
    · simp [hp]
  · push_neg at h
    obtain ⟨k, hp, hq⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    rw [ha k, hb k]; simp [hp, hq]

theorem idx_lt {a b A B : ℕ} (ha : a < A) (hb : b < B) : a * B + b < A * B := by
  calc a * B + b < a * B + B := by omega
    _ = (a + 1) * B := by ring
    _ ≤ A * B := Nat.mul_le_mul (Nat.succ_le_of_lt ha) le_rfl

theorem idx_div {a b B : ℕ} (hb : b < B) : (a * B + b) / B = a := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < B), Nat.div_eq_of_lt hb, Nat.zero_add]

theorem idx_mod {a b B : ℕ} (hb : b < B) : (a * B + b) % B = b := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

/-! ## Chunk 2h: header + inclusion table (straight line) -/
section Table

def tA (fv : ℤ) (V i k : ℕ) : ℤ := fv + (i : ℤ) * (V : ℤ) + (k : ℤ)

def tFac (fv : ℤ) (V : ℕ) (S out : ℤ) (i j k : ℕ) : List Op :=
  [.mul S (tA fv V i k) (tA fv V j k), .sub S S (tA fv V i k), .add S S (S + 1), .mul out out S]

def tFacs (fv : ℤ) (V : ℕ) (S out : ℤ) (i j : ℕ) : ℕ → List Op
  | 0 => []
  | K + 1 => tFacs fv V S out i j K ++ tFac fv V S out i j K

def tPairs (fv : ℤ) (n V : ℕ) (Ob S : ℤ) : ℕ → List Op
  | 0 => []
  | P + 1 => tPairs fv n V Ob S P ++ (.const (Ob + (n : ℤ) + 1 + (P : ℤ)) 1 ::
      tFacs fv V S (Ob + (n : ℤ) + 1 + (P : ℤ)) (P / n) (P % n) V)

def tHdr (Ob : ℤ) : ℕ → List Op
  | 0 => []
  | i + 1 => tHdr Ob i ++ [.const (Ob + (i : ℤ)) 1]

def tabDest (n V : ℕ) (fv minBase : ℤ) : ℤ := max minBase (fv + (n : ℤ) * (V : ℤ))
def tabS (n : ℕ) (Ob : ℤ) : ℤ := Ob + (n : ℤ) + 1 + ((n * n : ℕ) : ℤ)

def tabOps (n V : ℕ) (fv Ob : ℤ) : List Op :=
  tHdr Ob n ++ [.const (Ob + (n : ℤ)) 0, .const (tabS n Ob + 1) 1] ++
    tPairs fv n V Ob (tabS n Ob) (n * n) ++ [.shift Ob]

def tabProg (n V : ℕ) (fv minBase : ℤ) : List RayInstruction :=
  mkProg (tabOps n V fv (tabDest n V fv minBase))
def tabSteps (n V : ℕ) (_fv : ℤ) : ℕ := n + 2 + n * n * (1 + 4 * V) + 1

theorem tFacs_length (fv : ℤ) (V : ℕ) (S out : ℤ) (i j : ℕ) :
    ∀ K, (tFacs fv V S out i j K).length = 4 * K := by
  intro K; induction K with
  | zero => rfl
  | succ K ih => simp [tFacs, ih, tFac] <;> ring

theorem tPairs_length (fv : ℤ) (n V : ℕ) (Ob S : ℤ) :
    ∀ P, (tPairs fv n V Ob S P).length = P * (1 + 4 * V) := by
  intro P; induction P with
  | zero => simp [tPairs]
  | succ P ih => simp [tPairs, ih, tFacs_length] <;> ring

theorem tHdr_length (Ob : ℤ) : ∀ N, (tHdr Ob N).length = N := by
  intro N; induction N with
  | zero => rfl
  | succ N ih => simp [tHdr, ih]

theorem tabOps_length (n V : ℕ) (fv Ob : ℤ) : (tabOps n V fv Ob).length = tabSteps n V fv := by
  simp [tabOps, tabSteps, tHdr_length, tPairs_length] <;> ring

theorem tFac_spec (Oc : (Fin 2 → ℝ) → Fin 2 → ℝ) (c : RayConfiguration) (fv : ℤ) (V : ℕ)
    (S out : ℤ) (i j k : ℕ) (hh : c.head = 0) (hS : out ≠ S) (hiS : tA fv V i k ≠ S) :
    ∃ pc' t', foldOps 2 Oc (tFac fv V S out i j k) c = some ⟨pc', 0, t', c.queries⟩ ∧
      t' out = c.tape out * (c.tape (tA fv V i k) * c.tape (tA fv V j k) - c.tape (tA fv V i k)
        + c.tape (S + 1)) ∧
      ∀ z, z ≠ S → z ≠ out → t' z = c.tape z := by
  obtain ⟨pc, hd, tp, qq⟩ := c
  simp only at hh
  subst hh
  have h1 : S + 1 ≠ S := by omega
  refine ⟨_, _, rfl, ?_, ?_⟩
  · simp [Function.update_apply, hS, hiS, h1]
  · intro z hz1 hz2; simp [Function.update_apply, hz1, hz2]

theorem tFacs_spec (Oc : (Fin 2 → ℝ) → Fin 2 → ℝ) (fv : ℤ) (V : ℕ) (S out : ℤ) (i j : ℕ)
    (hS : out < S) (hrd : ∀ k < V, tA fv V i k < out ∧ tA fv V j k < out) :
    ∀ K, K ≤ V → ∀ c : RayConfiguration, c.head = 0 → c.tape (S + 1) = 1 →
    ∃ pc' t', foldOps 2 Oc (tFacs fv V S out i j K) c = some ⟨pc', 0, t', c.queries⟩ ∧
      t' out = c.tape out * ∏ k ∈ Finset.range K,
        (c.tape (tA fv V i k) * c.tape (tA fv V j k) - c.tape (tA fv V i k) + 1) ∧
      ∀ z, z ≠ S → z ≠ out → t' z = c.tape z := by
  intro K
  induction K with
  | zero =>
    intro _ c hh _
    obtain ⟨pc, hd, tp, qq⟩ := c
    simp only at hh
    subst hh
    exact ⟨pc, tp, rfl, by simp, fun _ _ _ => rfl⟩
  | succ K ih =>
    intro hK c hh h1
    obtain ⟨pc1, t1, hf1, hout1, hfr1⟩ := ih (by omega) c hh h1
    obtain ⟨hA, hB⟩ := hrd K (by omega)
    obtain ⟨pc2, t2, hf2, hout2, hfr2⟩ := tFac_spec Oc ⟨pc1, 0, t1, c.queries⟩ fv V S out i j K rfl
      (by omega) (by omega)
    dsimp only at hout2 hfr2
    refine ⟨pc2, t2, ?_, ?_, ?_⟩
    · show foldOps 2 Oc (tFacs fv V S out i j K ++ tFac fv V S out i j K) c = _
      rw [foldOps_append, hf1, Option.bind_some]; exact hf2
    · rw [hout2, Finset.prod_range_succ, hout1, hfr1 (tA fv V i K) (by omega) (by omega),
        hfr1 (tA fv V j K) (by omega) (by omega), hfr1 (S + 1) (by omega) (by omega), h1]
      ring
    · intro z hz1 hz2; rw [hfr2 z hz1 hz2, hfr1 z hz1 hz2]

theorem tHdr_spec (Oc : (Fin 2 → ℝ) → Fin 2 → ℝ) (Ob : ℤ) :
    ∀ (N : ℕ) (c : RayConfiguration), c.head = 0 →
    ∃ pc' t', foldOps 2 Oc (tHdr Ob N) c = some ⟨pc', 0, t', c.queries⟩ ∧
      (∀ i < N, t' (Ob + (i : ℤ)) = 1) ∧ ∀ z, (z < Ob ∨ Ob + (N : ℤ) ≤ z) → t' z = c.tape z := by
  intro N
  induction N with
  | zero =>
    intro c hh
    obtain ⟨pc, hd, tp, qq⟩ := c
    simp only at hh
    subst hh
    exact ⟨pc, tp, rfl, fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ => rfl⟩
  | succ N ih =>
    intro c hh
    obtain ⟨pc1, t1, hf1, hv1, hfr1⟩ := ih c hh
    refine ⟨pc1 + 1, Function.update t1 (Ob + (N : ℤ)) 1, ?_, ?_, ?_⟩
    · show foldOps 2 Oc (tHdr Ob N ++ [.const (Ob + (N : ℤ)) 1]) c = _
      rw [foldOps_append, hf1, Option.bind_some]
      simp [foldOps, opSem]
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
      · rw [Function.update_of_ne (show Ob + (i : ℤ) ≠ Ob + (N : ℤ) by omega), hv1 i hi]
      · rw [hi, Function.update_apply, if_pos rfl]
    · intro z hz
      rw [Function.update_of_ne (show z ≠ Ob + (N : ℤ) by omega), hfr1 z (by omega)]

set_option maxHeartbeats 1000000 in
theorem tPairs_spec (Oc : (Fin 2 → ℝ) → Fin 2 → ℝ) (fv : ℤ) (n V N : ℕ) (Ob S : ℤ)
    (hN : N = n * n) (hS : Ob + (n : ℤ) + 1 + (N : ℤ) ≤ S)
    (hrd : ∀ i < n, ∀ k < V, tA fv V i k < Ob) :
    ∀ P, P ≤ N → ∀ c : RayConfiguration, c.head = 0 → c.tape (S + 1) = 1 →
    ∃ pc' t', foldOps 2 Oc (tPairs fv n V Ob S P) c = some ⟨pc', 0, t', c.queries⟩ ∧
      (∀ p < P, t' (Ob + (n : ℤ) + 1 + (p : ℤ)) = ∏ k ∈ Finset.range V,
        (c.tape (tA fv V (p / n) k) * c.tape (tA fv V (p % n) k) - c.tape (tA fv V (p / n) k) + 1)) ∧
      ∀ z, z ≠ S → (z < Ob + (n : ℤ) + 1 ∨ Ob + (n : ℤ) + 1 + (P : ℤ) ≤ z) → t' z = c.tape z := by
  intro P
  induction P with
  | zero =>
    intro _ c hh _
    obtain ⟨pc, hd, tp, qq⟩ := c
    simp only at hh
    subst hh
    exact ⟨pc, tp, rfl, fun p hp => absurd hp (Nat.not_lt_zero _), fun _ _ _ => rfl⟩
  | succ P ih =>
    intro hP c hh h1
    obtain ⟨pc1, t1, hf1, hv1, hfr1⟩ := ih (by omega) c hh h1
    have hPn : P < n * n := by rw [← hN]; omega
    have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hPn)
    have hi : P / n < n := Nat.div_lt_of_lt_mul hPn
    have hj : P % n < n := Nat.mod_lt _ hn
    have hS' : Ob + (n : ℤ) + 1 + (P : ℤ) < S := by omega
    have hc2 : Function.update t1 (Ob + (n : ℤ) + 1 + (P : ℤ)) 1 (S + 1) = 1 := by
      rw [Function.update_of_ne (show S + 1 ≠ Ob + (n : ℤ) + 1 + (P : ℤ) by omega),
        hfr1 (S + 1) (by omega) (Or.inr (by omega)), h1]
    obtain ⟨pc3, t3, hf3, hv3, hfr3⟩ := tFacs_spec Oc fv V S (Ob + (n : ℤ) + 1 + (P : ℤ)) (P / n)
      (P % n) hS' (fun k hk => ⟨by have := hrd _ hi k hk; omega, by have := hrd _ hj k hk; omega⟩)
      V le_rfl ⟨pc1 + 1, 0, Function.update t1 (Ob + (n : ℤ) + 1 + (P : ℤ)) 1, c.queries⟩ rfl hc2
    dsimp only at hf3 hv3 hfr3
    refine ⟨pc3, t3, ?_, ?_, ?_⟩
    · show foldOps 2 Oc (tPairs fv n V Ob S P ++ (.const (Ob + (n : ℤ) + 1 + (P : ℤ)) 1 ::
        tFacs fv V S (Ob + (n : ℤ) + 1 + (P : ℤ)) (P / n) (P % n) V)) c = _
      rw [foldOps_append, hf1, Option.bind_some]
      have e : foldOps 2 Oc (.const (Ob + (n : ℤ) + 1 + (P : ℤ)) 1 ::
          tFacs fv V S (Ob + (n : ℤ) + 1 + (P : ℤ)) (P / n) (P % n) V) ⟨pc1, 0, t1, c.queries⟩ =
          foldOps 2 Oc (tFacs fv V S (Ob + (n : ℤ) + 1 + (P : ℤ)) (P / n) (P % n) V)
            ⟨pc1 + 1, 0, Function.update t1 (Ob + (n : ℤ) + 1 + (P : ℤ)) 1, c.queries⟩ := by
        simp [foldOps, opSem]
      rw [e, hf3]
    · intro p hp
      rcases Nat.lt_succ_iff_lt_or_eq.mp hp with hp | hp
      · rw [hfr3 (Ob + (n : ℤ) + 1 + (p : ℤ)) (by omega) (by omega),
          Function.update_of_ne (show Ob + (n : ℤ) + 1 + (p : ℤ) ≠ Ob + (n : ℤ) + 1 + (P : ℤ) by omega),
          hv1 p hp]
      · rw [hp, hv3, Function.update_apply, if_pos rfl, one_mul]
        apply Finset.prod_congr rfl
        intro k hk
        have hk' := Finset.mem_range.mp hk
        have ha := hrd _ hi k hk'
        have hb := hrd _ hj k hk'
        rw [Function.update_of_ne (show tA fv V (P / n) k ≠ Ob + (n : ℤ) + 1 + (P : ℤ) by omega),
          Function.update_of_ne (show tA fv V (P % n) k ≠ Ob + (n : ℤ) + 1 + (P : ℤ) by omega),
          hfr1 (tA fv V (P / n) k) (by omega) (Or.inl (by omega)),
          hfr1 (tA fv V (P % n) k) (by omega) (Or.inl (by omega))]
    · intro z hzS hz
      rw [hfr3 z hzS (by omega),
        Function.update_of_ne (show z ≠ Ob + (n : ℤ) + 1 + (P : ℤ) by omega), hfr1 z hzS (by omega)]

set_option maxHeartbeats 1000000 in
theorem tab_core (Oc : (Fin 2 → ℝ) → Fin 2 → ℝ) (source : ℤ → ℝ) (fv : ℤ) (n V : ℕ) (Ob : ℤ)
    (q : ℕ) (hrd : ∀ i < n, ∀ k < V, tA fv V i k < Ob) :
    ∃ c' : RayConfiguration, foldOps 2 Oc (tabOps n V fv Ob) ⟨0, 0, source, q⟩ = some c' ∧
      c'.head = Ob ∧ c'.queries = q ∧
      (∀ i < n, c'.tape (Ob + (i : ℤ)) = 1) ∧ c'.tape (Ob + (n : ℤ)) = 0 ∧
      (∀ p < n * n, c'.tape (Ob + (n : ℤ) + 1 + (p : ℤ)) = ∏ k ∈ Finset.range V,
        (source (tA fv V (p / n) k) * source (tA fv V (p % n) k) - source (tA fv V (p / n) k) + 1)) ∧
      ∀ z, z < Ob → c'.tape z = source z := by
  have hNN0 : (0 : ℤ) ≤ ((n * n : ℕ) : ℤ) := by positivity
  have hS : Ob + (n : ℤ) + 1 + ((n * n : ℕ) : ℤ) ≤ tabS n Ob := le_refl _
  obtain ⟨pc1, t1, hf1, hv1, hfr1⟩ := tHdr_spec Oc Ob n ⟨0, 0, source, q⟩ rfl
  dsimp only at hf1 hfr1
  have hc2r : ∀ z, z < Ob →
      Function.update (Function.update t1 (Ob + (n : ℤ)) 0) (tabS n Ob + 1) 1 z = source z := by
    intro z hz
    rw [Function.update_of_ne (show z ≠ tabS n Ob + 1 by omega),
      Function.update_of_ne (show z ≠ Ob + (n : ℤ) by omega)]
    exact hfr1 z (Or.inl hz)
  obtain ⟨pc3, t3, hf3, hv3, hfr3⟩ := tPairs_spec Oc fv n V (n * n) Ob (tabS n Ob) rfl hS hrd
    (n * n) le_rfl
    ⟨pc1 + 1 + 1, 0, Function.update (Function.update t1 (Ob + (n : ℤ)) 0) (tabS n Ob + 1) 1, q⟩ rfl
    (by simp)
  dsimp only at hf3 hv3 hfr3
  refine ⟨⟨pc3 + 1, Ob, t3, q⟩, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · have h2 : foldOps 2 Oc [.const (Ob + (n : ℤ)) 0, .const (tabS n Ob + 1) 1] ⟨pc1, 0, t1, q⟩ =
        some ⟨pc1 + 1 + 1, 0,
          Function.update (Function.update t1 (Ob + (n : ℤ)) 0) (tabS n Ob + 1) 1, q⟩ := by
      simp [foldOps, opSem]
    have h3 : foldOps 2 Oc [.shift Ob] ⟨pc3, 0, t3, q⟩ = some ⟨pc3 + 1, Ob, t3, q⟩ := by
      simp [foldOps, opSem]
    simp only [tabOps, foldOps_append, hf1, Option.bind_some, h2, hf3, h3]
  · intro i hi
    dsimp only
    rw [hfr3 (Ob + (i : ℤ)) (by omega) (Or.inl (by omega)),
      Function.update_of_ne (show Ob + (i : ℤ) ≠ tabS n Ob + 1 by omega),
      Function.update_of_ne (show Ob + (i : ℤ) ≠ Ob + (n : ℤ) by omega), hv1 i hi]
  · dsimp only
    rw [hfr3 (Ob + (n : ℤ)) (by omega) (Or.inl (by omega)),
      Function.update_of_ne (show Ob + (n : ℤ) ≠ tabS n Ob + 1 by omega), Function.update_apply,
      if_pos rfl]
  · intro p hp
    have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hp)
    have hi := Nat.div_lt_of_lt_mul hp
    have hj := Nat.mod_lt p hn
    dsimp only
    rw [hv3 p hp]
    apply Finset.prod_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rw [hc2r _ (hrd _ hi k hk'), hc2r _ (hrd _ hj k hk')]
  · intro z hz
    dsimp only
    rw [hfr3 z (by omega) (Or.inl (by omega)), hc2r z hz]

theorem tabW_spec {n V : ℕ} (oracle : (Fin 2 → ℝ) → Fin 2 → ℝ) (source : ℤ → ℝ)
    (fvBase minBase : ℤ) (q : ℕ) (inc : Fin n → Fin V → Prop) :
    (∀ (a : Fin n) (k : Fin V),
      source (fvBase + (a.val : ℤ) * (V : ℤ) + (k.val : ℤ)) = if inc a k then (1 : ℝ) else 0) →
    let prog := tabProg n V fvBase minBase
    let outBase := tabDest n V fvBase minBase
    let steps := tabSteps n V fvBase
    minBase ≤ outBase ∧
    ∃ c' : RayConfiguration,
      rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
      c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
      c'.head = outBase ∧ c'.queries = q ∧
      (∀ i : Fin n, c'.tape (c'.head + (i.val : ℤ)) = 1) ∧
      c'.tape (c'.head + (n : ℤ)) = 0 ∧
      (∀ i j : Fin n,
        c'.tape (c'.head + ((n + 1 + i.val * n + j.val : ℕ) : ℤ)) =
          if (∀ k : Fin V, inc i k → inc j k) then (1 : ℝ) else 0) ∧
      (∀ z : ℤ, z < c'.head → c'.tape z = source z) := by
  intro hsrc
  dsimp only
  have hrd : ∀ i < n, ∀ k < V, tA fvBase V i k < tabDest n V fvBase minBase := by
    intro i hi k hk
    have h1 : ((i : ℤ) + 1) * (V : ℤ) ≤ (n : ℤ) * V :=
      mul_le_mul_of_nonneg_right (by omega) (by positivity)
    have h2 : fvBase + (n : ℤ) * V ≤ tabDest n V fvBase minBase := le_max_right _ _
    have h3 : (k : ℤ) < V := by exact_mod_cast hk
    simp only [tA]; nlinarith
  obtain ⟨c', hf, hh, hq, hhd, hz, htab, hfr⟩ :=
    tab_core oracle source fvBase n V (tabDest n V fvBase minBase) q hrd
  have hpc : c'.pc = tabSteps n V fvBase := by
    rw [foldOps_pc oracle _ _ _ hf, tabOps_length]; simp
  refine ⟨le_max_left _ _, c', ?_, hpc, ?_, hh, hq, ?_, ?_, ?_, ?_⟩
  · show rayMachineRun (mkProg (tabOps n V fvBase (tabDest n V fvBase minBase))) oracle
      (tabSteps n V fvBase) _ = _
    rw [← tabOps_length n V fvBase (tabDest n V fvBase minBase), run_mkProg oracle _ _ rfl]
    exact hf
  · rw [hpc, ← tabOps_length n V fvBase (tabDest n V fvBase minBase)]; exact mkProg_halt _
  · intro i; rw [hh]; exact hhd i i.isLt
  · rw [hh]; exact hz
  · intro i j
    have hp := idx_lt i.isLt j.isLt
    have hv := htab _ hp
    rw [idx_div j.isLt, idx_mod j.isLt] at hv
    rw [hh, show tabDest n V fvBase minBase + ((n + 1 + i.val * n + j.val : ℕ) : ℤ) =
      tabDest n V fvBase minBase + (n : ℤ) + 1 + ((i.val * n + j.val : ℕ) : ℤ) by push_cast; ring, hv]
    exact prod_incl (fun k => source (tA fvBase V i.val k)) (fun k => source (tA fvBase V j.val k))
      (inc i) (inc j) (fun k => hsrc i k) (fun k => hsrc j k)
  · rw [hh]; exact hfr

end Table

/-! ## Chunk 2g: facet-vertex incidence matrix (branching blocks) -/
section Incidence

def iL (lB : ℤ) (j i : ℕ) : ℤ := lB + (j : ℤ) * ((2 : ℕ) : ℤ) + (i : ℤ)
def iX (xB : ℤ) (k i : ℕ) : ℤ := xB + (k : ℤ) * ((2 : ℕ) : ℤ) + (i : ℤ)

def iBlk (V : ℕ) (lB xB O S : ℤ) (p : ℕ) : ℕ → RayInstruction
  | 0 => .mul S (iL lB (p / V) 0) (iX xB (p % V) 0) (1 + 7 * p + 0 + 1)
  | 1 => .mul (S + 1) (iL lB (p / V) 1) (iX xB (p % V) 1) (1 + 7 * p + 1 + 1)
  | 2 => .add S S (S + 1) (1 + 7 * p + 2 + 1)
  | 3 => .sub S S (S + 2) (1 + 7 * p + 3 + 1)
  | 4 => .branch S (1 + 7 * p + 5) (1 + 7 * p + 6) (1 + 7 * p + 5)
  | 5 => .constant (O + (p : ℤ)) 0 (1 + 7 * (p + 1))
  | _ => .constant (O + (p : ℤ)) 1 (1 + 7 * (p + 1))

def blkOps (V : ℕ) (lB xB S : ℤ) (p : ℕ) : List Op :=
  [.mul S (iL lB (p / V) 0) (iX xB (p % V) 0), .mul (S + 1) (iL lB (p / V) 1) (iX xB (p % V) 1),
   .add S S (S + 1), .sub S S (S + 2)]

def iInstr (N V : ℕ) (lB xB O S : ℤ) (t : ℕ) : RayInstruction :=
  if t = 0 then .constant (S + 2) 1 1
  else if t < 1 + 7 * N then iBlk V lB xB O S ((t - 1) / 7) ((t - 1) % 7)
  else .halt

def incDest (m V : ℕ) (lB xB minBase : ℤ) : ℤ :=
  max minBase (max (lB + 2 * (m : ℤ)) (xB + 2 * (V : ℤ)))
def incProg (m V : ℕ) (lB xB minBase : ℤ) : List RayInstruction :=
  (List.range (2 + 7 * (m * V))).map (iInstr (m * V) V lB xB (incDest m V lB xB minBase)
    (incDest m V lB xB minBase + ((m * V : ℕ) : ℤ)))

theorem iget (N V : ℕ) (lB xB O S : ℤ) (t : ℕ) (ht : t < 2 + 7 * N) :
    ((List.range (2 + 7 * N)).map (iInstr N V lB xB O S))[t]? = some (iInstr N V lB xB O S t) := by
  simp [ht]

theorem iget_blk (N V : ℕ) (lB xB O S : ℤ) (p r : ℕ) (hp : p < N) (hr : r < 7) :
    ((List.range (2 + 7 * N)).map (iInstr N V lB xB O S))[1 + 7 * p + r]? =
      some (iBlk V lB xB O S p r) := by
  rw [iget N V lB xB O S (1 + 7 * p + r) (by omega), iInstr,
    if_neg (show ¬ (1 + 7 * p + r = 0) by omega), if_pos (show 1 + 7 * p + r < 1 + 7 * N by omega),
    show (1 + 7 * p + r - 1) / 7 = p by omega, show (1 + 7 * p + r - 1) % 7 = r by omega]

set_option maxHeartbeats 1000000 in
theorem inc_blk (Oc : (Fin 2 → ℝ) → Fin 2 → ℝ) (prog : List RayInstruction) (V : ℕ)
    (lB xB O S : ℤ) (p : ℕ)
    (hget : ∀ r < 7, prog[1 + 7 * p + r]? = some (iBlk V lB xB O S p r))
    (c : RayConfiguration) (hpc : c.pc = 1 + 7 * p) (hh : c.head = 0) (h2 : c.tape (S + 2) = 1)
    (hr : ∀ i < 2, iL lB (p / V) i < O ∧ iX xB (p % V) i < O) (hOS : O + (p : ℤ) < S) :
    ∃ t', rayMachineRun prog Oc 6 c = some ⟨1 + 7 * (p + 1), 0, t', c.queries⟩ ∧
      t' (O + (p : ℤ)) = (if c.tape (iL lB (p / V) 0) * c.tape (iX xB (p % V) 0) +
          c.tape (iL lB (p / V) 1) * c.tape (iX xB (p % V) 1) = 1 then 1 else 0) ∧
      ∀ z, z ≠ S → z ≠ S + 1 → z ≠ O + (p : ℤ) → t' z = c.tape z := by
  obtain ⟨pc, hd, tp, qq⟩ := c
  dsimp only at hpc hh h2 ⊢
  subst hpc hh
  obtain ⟨hA0, hB0⟩ := hr 0 (by norm_num)
  obtain ⟨hA1, hB1⟩ := hr 1 (by norm_num)
  have hops : rayMachineRun prog Oc 4 ⟨1 + 7 * p, 0, tp, qq⟩ =
      foldOps 2 Oc (blkOps V lB xB S p) ⟨1 + 7 * p, 0, tp, qq⟩ := by
    refine run_ops prog Oc (blkOps V lB xB S p) _ ?_
    intro i hi
    have hi4 : i < 4 := by simpa [blkOps] using hi
    rw [hget i (by omega)]
    interval_cases i <;> rfl
  have hf : ∃ t4, foldOps 2 Oc (blkOps V lB xB S p) ⟨1 + 7 * p, 0, tp, qq⟩ =
      some ⟨1 + 7 * p + 4, 0, t4, qq⟩ ∧
      t4 S = tp (iL lB (p / V) 0) * tp (iX xB (p % V) 0) +
        tp (iL lB (p / V) 1) * tp (iX xB (p % V) 1) - 1 ∧
      ∀ z, z ≠ S → z ≠ S + 1 → t4 z = tp z := by
    have e1 : iL lB (p / V) 1 ≠ S := by omega
    have e2 : iX xB (p % V) 1 ≠ S := by omega
    have e3 : S + 1 ≠ S := by omega
    have e4 : S + 2 ≠ S := by omega
    have e5 : S + 2 ≠ S + 1 := by omega
    refine ⟨_, rfl, ?_, ?_⟩
    · simp [Function.update_apply, e1, e2, e3, e4, e5, h2]
    · intro z hz1 hz2
      simp [Function.update_apply, hz1, hz2]
  obtain ⟨t4, hf4, h4S, hfr4⟩ := hf
  have hbr : prog[1 + 7 * p + 4]? = some (.branch S (1 + 7 * p + 5) (1 + 7 * p + 6) (1 + 7 * p + 5)) :=
    hget 4 (by norm_num)
  have h5 : prog[1 + 7 * p + 5]? = some (.constant (O + (p : ℤ)) 0 (1 + 7 * (p + 1))) :=
    hget 5 (by norm_num)
  have h6 : prog[1 + 7 * p + 6]? = some (.constant (O + (p : ℤ)) 1 (1 + 7 * (p + 1))) :=
    hget 6 (by norm_num)
  rw [show (6 : ℕ) = 4 + (1 + 1) from rfl, run_add3, hops, hf4, Option.bind_some, run_add3, run_one]
  by_cases hd1 : tp (iL lB (p / V) 0) * tp (iX xB (p % V) 0) +
      tp (iL lB (p / V) 1) * tp (iX xB (p % V) 1) = 1
  · have hs4 : rayMachineStep prog Oc ⟨1 + 7 * p + 4, 0, t4, qq⟩ = some ⟨1 + 7 * p + 6, 0, t4, qq⟩ := by
      rw [step_branch prog Oc ⟨1 + 7 * p + 4, 0, t4, qq⟩ S _ _ _ hbr]
      simp [h4S, hd1]
    have hs6 : rayMachineStep prog Oc ⟨1 + 7 * p + 6, 0, t4, qq⟩ =
        some ⟨1 + 7 * (p + 1), 0, Function.update t4 (O + (p : ℤ)) 1, qq⟩ := by
      rw [step_const prog Oc ⟨1 + 7 * p + 6, 0, t4, qq⟩ _ _ _ h6]; simp
    rw [hs4, Option.bind_some, run_one, hs6]
    refine ⟨_, rfl, by simp [hd1], ?_⟩
    intro z hz1 hz2 hz3
    rw [Function.update_of_ne hz3, hfr4 z hz1 hz2]
  · have hs4 : rayMachineStep prog Oc ⟨1 + 7 * p + 4, 0, t4, qq⟩ = some ⟨1 + 7 * p + 5, 0, t4, qq⟩ := by
      rw [step_branch prog Oc ⟨1 + 7 * p + 4, 0, t4, qq⟩ S _ _ _ hbr]
      simp [h4S, hd1, sub_eq_zero]
    have hs5 : rayMachineStep prog Oc ⟨1 + 7 * p + 5, 0, t4, qq⟩ =
        some ⟨1 + 7 * (p + 1), 0, Function.update t4 (O + (p : ℤ)) 0, qq⟩ := by
      rw [step_const prog Oc ⟨1 + 7 * p + 5, 0, t4, qq⟩ _ _ _ h5]; simp
    rw [hs4, Option.bind_some, run_one, hs5]
    refine ⟨_, rfl, by simp [hd1], ?_⟩
    intro z hz1 hz2 hz3
    rw [Function.update_of_ne hz3, hfr4 z hz1 hz2]

theorem inc_run (Oc : (Fin 2 → ℝ) → Fin 2 → ℝ) (source : ℤ → ℝ) (N V : ℕ) (lB xB O S : ℤ) (q : ℕ)
    (hrd : ∀ p < N, ∀ i < 2, iL lB (p / V) i < O ∧ iX xB (p % V) i < O) (hOS : O + (N : ℤ) ≤ S) :
    ∀ P, P ≤ N → ∃ t', rayMachineRun ((List.range (2 + 7 * N)).map (iInstr N V lB xB O S)) Oc
        (1 + 6 * P) ⟨0, 0, source, q⟩ = some ⟨1 + 7 * P, 0, t', q⟩ ∧
      t' (S + 2) = 1 ∧
      (∀ p < P, t' (O + (p : ℤ)) = if source (iL lB (p / V) 0) * source (iX xB (p % V) 0) +
          source (iL lB (p / V) 1) * source (iX xB (p % V) 1) = 1 then 1 else 0) ∧
      ∀ z, z < O → t' z = source z := by
  intro P
  induction P with
  | zero =>
    intro _
    refine ⟨Function.update source (S + 2) 1, ?_, by simp, fun p hp => absurd hp (Nat.not_lt_zero _), ?_⟩
    · simp only [Nat.mul_zero, Nat.add_zero]
      rw [run_one, step_const _ Oc ⟨0, 0, source, q⟩ (S + 2) 1 1 (iget N V lB xB O S 0 (by omega))]
      simp
    · intro z hz; rw [Function.update_of_ne (show z ≠ S + 2 by omega)]
  | succ P ih =>
    intro hP
    obtain ⟨t1, hr1, h12, hv1, hfr1⟩ := ih (by omega)
    obtain ⟨t2, hr2, hv2, hfr2⟩ := inc_blk Oc ((List.range (2 + 7 * N)).map (iInstr N V lB xB O S))
      V lB xB O S P (fun r hr => iget_blk N V lB xB O S P r (by omega) hr) ⟨1 + 7 * P, 0, t1, q⟩
      rfl rfl h12 (hrd P (by omega)) (by omega)
    dsimp only at hv2 hfr2
    refine ⟨t2, ?_, ?_, ?_, ?_⟩
    · rw [show 1 + 6 * (P + 1) = (1 + 6 * P) + 6 by ring, run_add3, hr1, Option.bind_some, hr2]
    · rw [hfr2 (S + 2) (by omega) (by omega) (by omega), h12]
    · intro p hp
      rcases Nat.lt_succ_iff_lt_or_eq.mp hp with hp | hp
      · rw [hfr2 (O + (p : ℤ)) (by omega) (by omega) (by omega), hv1 p hp]
      · rw [hp, hv2]
        simp only [hfr1 _ (hrd P (by omega) 0 (by norm_num)).1,
          hfr1 _ (hrd P (by omega) 0 (by norm_num)).2, hfr1 _ (hrd P (by omega) 1 (by norm_num)).1,
          hfr1 _ (hrd P (by omega) 1 (by norm_num)).2]
    · intro z hz; rw [hfr2 z (by omega) (by omega) (by omega), hfr1 z hz]

theorem incW_spec {m V : ℕ} (oracle : (Fin 2 → ℝ) → Fin 2 → ℝ) (source : ℤ → ℝ)
    (lBase xBase minBase : ℤ) (q : ℕ) :
    let prog := incProg m V lBase xBase minBase
    let outBase := incDest m V lBase xBase minBase
    let steps := 1 + 6 * (m * V)
    let haltPC := 1 + 7 * (m * V)
    minBase ≤ outBase ∧
    ∃ c' : RayConfiguration,
      rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
      c'.pc = haltPC ∧ prog[c'.pc]? = some .halt ∧
      c'.head = 0 ∧ c'.queries = q ∧
      (∀ (j : Fin m) (k : Fin V),
        c'.tape (outBase + (j.val : ℤ) * (V : ℤ) + (k.val : ℤ)) =
          if (∑ i : Fin 2,
              source (lBase + (j.val : ℤ) * ((2 : ℕ) : ℤ) + (i.val : ℤ)) *
                source (xBase + (k.val : ℤ) * ((2 : ℕ) : ℤ) + (i.val : ℤ))) = 1
          then (1 : ℝ) else 0) ∧
      (∀ z : ℤ, z < outBase → c'.tape z = source z) := by
  dsimp only
  have hrd : ∀ p < m * V, ∀ i < 2, iL lBase (p / V) i < incDest m V lBase xBase minBase ∧
      iX xBase (p % V) i < incDest m V lBase xBase minBase := by
    intro p hp i hi
    have hV : 0 < V := Nat.pos_of_ne_zero (by rintro rfl; simp at hp)
    have h1 : p / V < m := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hp)
    have h2 : p % V < V := Nat.mod_lt _ hV
    have h3 : lBase + 2 * (m : ℤ) ≤ incDest m V lBase xBase minBase :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    have h4 : xBase + 2 * (V : ℤ) ≤ incDest m V lBase xBase minBase :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    generalize p / V = j at h1 ⊢
    generalize p % V = k at h2 ⊢
    simp only [iL, iX]
    constructor <;> omega
  obtain ⟨t', hrun, -, hv, hfr⟩ := inc_run oracle source (m * V) V lBase xBase _ _ q hrd (le_refl _)
    (m * V) (le_refl _)
  refine ⟨le_max_left _ _, ⟨1 + 7 * (m * V), 0, t', q⟩, hrun, rfl, ?_, rfl, rfl, ?_, hfr⟩
  · show (incProg m V lBase xBase minBase)[1 + 7 * (m * V)]? = some RayInstruction.halt
    unfold incProg
    rw [iget (m * V) V lBase xBase _ _ (1 + 7 * (m * V)) (by omega), iInstr,
      if_neg (show ¬ (1 + 7 * (m * V) = 0) by omega),
      if_neg (show ¬ (1 + 7 * (m * V) < 1 + 7 * (m * V)) by omega)]
  · intro j k
    have hp := idx_lt j.isLt k.isLt
    have hv' := hv (j.val * V + k.val) hp
    rw [idx_div k.isLt, idx_mod k.isLt] at hv'
    dsimp only
    rw [show incDest m V lBase xBase minBase + (j.val : ℤ) * (V : ℤ) + (k.val : ℤ) =
      incDest m V lBase xBase minBase + ((j.val * V + k.val : ℕ) : ℤ) by push_cast; ring, hv']
    simp [Fin.sum_univ_two, iL, iX]

end Incidence


section HPoly


/-- At an extreme point of an H-polyhedron `{y | A i y ≤ 1}`, the tight rows determine
every direction: a direction killed by all tight rows is zero. -/
theorem hpoly_extreme_rigid {d m : ℕ} (A : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) {x : Fin d → ℝ}
    (hx : x ∈ ({y | ∀ i, A i y ≤ 1} : Set (Fin d → ℝ)).extremePoints ℝ)
    (w : Fin d → ℝ) (hw : ∀ i, A i x = 1 → A i w = 0) : w = 0 := by
  rw [mem_extremePoints] at hx
  obtain ⟨hxQ, hext⟩ := hx
  have hev : ∀ᶠ ε in nhds (0:ℝ), ∀ i, A i (x + ε • w) ≤ 1 ∧ A i (x - ε • w) ≤ 1 := by
    rw [Filter.eventually_all]
    intro i
    by_cases ht : A i x = 1
    · refine Filter.Eventually.of_forall (fun ε => ?_)
      simp [map_add, map_sub, map_smul, ht, hw i ht]
    · have hlt : A i x < 1 := lt_of_le_of_ne (hxQ i) ht
      have hc1 : Continuous fun ε : ℝ => A i (x + ε • w) := by fun_prop
      have hc2 : Continuous fun ε : ℝ => A i (x - ε • w) := by fun_prop
      have h1 : ∀ᶠ ε in nhds (0:ℝ), A i (x + ε • w) < 1 :=
        hc1.continuousAt.eventually_lt continuousAt_const (by simpa using hlt)
      have h2 : ∀ᶠ ε in nhds (0:ℝ), A i (x - ε • w) < 1 :=
        hc2.continuousAt.eventually_lt continuousAt_const (by simpa using hlt)
      filter_upwards [h1, h2] with ε e1 e2
      exact ⟨e1.le, e2.le⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hε : dist (δ / 2) (0:ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith
  have hp := hball hε
  have hseg : x ∈ openSegment ℝ (x + (δ / 2) • w) (x - (δ / 2) • w) :=
    ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, by ext j; simp; ring⟩
  have heq := (hext _ (fun i => (hp i).1) _ (fun i => (hp i).2) hseg).1
  have hz : (δ / 2) • w = 0 := by simpa using heq
  rcases smul_eq_zero.1 hz with h | h
  · linarith
  · exact h

/-- An H-polyhedron `{y | A i y ≤ 1}` with finitely many rows has finitely many extreme points. -/
theorem hpoly_extreme_finite {d m : ℕ} (A : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) :
    (({y | ∀ i, A i y ≤ 1} : Set (Fin d → ℝ)).extremePoints ℝ).Finite := by
  apply Set.Finite.of_finite_image (f := fun x => {i | A i x = 1}) (Set.toFinite _)
  intro x hx y hy hxy
  have hxy' : ∀ i, A i x = 1 ↔ A i y = 1 := fun i => by
    have := congrArg (fun s : Set (Fin m) => i ∈ s) hxy
    simpa using this
  have h0 := hpoly_extreme_rigid A hx (x - y) (fun i hi => by
    rw [map_sub, hi, (hxy' i).1 hi]; ring)
  exact sub_eq_zero.1 h0


/-- Converse of `hpoly_extreme_rigid`: a feasible point whose tight rows kill no nonzero
direction is an extreme point. -/
theorem isExposed_level {d : ℕ} (P : Set (Fin d → ℝ)) (l : (Fin d → ℝ) →L[ℝ] ℝ)
    (hle : ∀ x ∈ P, l x ≤ 1) : IsExposed ℝ P {x ∈ P | l x = 1} := by
  rintro ⟨x0, hx0P, hx0⟩
  refine ⟨l, ?_⟩
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hxP, hx⟩
    exact ⟨hxP, fun y hy => by rw [hx]; exact hle y hy⟩
  · rintro ⟨hxP, hx⟩
    exact ⟨hxP, le_antisymm (hle x hxP) (by rw [← hx0]; exact hx x0 hx0P)⟩


theorem compact_eq_hull_of_finite_ext {d : ℕ} {Q : Set (Fin d → ℝ)} (hc : IsCompact Q)
    (hcv : Convex ℝ Q) (hf : (Q.extremePoints ℝ).Finite) :
    convexHull ℝ (Q.extremePoints ℝ) = Q := by
  have h := closure_convexHull_extremePoints hc hcv
  rwa [(Set.Finite.isCompact_convexHull (𝕜 := ℝ) hf).isClosed.closure_eq] at h


abbrev HP {d m : ℕ} (A : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) : Set (Fin d → ℝ) := {x | ∀ i, A i x ≤ 1}

theorem hp_eq_iInter {d m : ℕ} (A : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) :
    HP A = ⋂ i, {x | A i x ≤ 1} := by ext; simp [HP]

theorem hp_closed {d m : ℕ} (A : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) : IsClosed (HP A) := by
  rw [hp_eq_iInter]; exact isClosed_iInter fun i => isClosed_le (A i).continuous continuous_const

theorem hp_convex {d m : ℕ} (A : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) : Convex ℝ (HP A) := by
  rw [hp_eq_iInter]
  exact convex_iInter fun i => convex_halfSpace_le (A i : (Fin d → ℝ) →ₗ[ℝ] ℝ).isLinear 1

theorem hp_compact {d m : ℕ} (A : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) {R : ℝ}
    (hR : ∀ x ∈ HP A, ∀ k, |x k| ≤ R) : IsCompact (HP A) := by
  apply Metric.isCompact_of_isClosed_isBounded (hp_closed A)
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨max R 0, fun x hx => ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (le_max_right _ _)]
  intro k; rw [Real.norm_eq_abs]; exact (hR x hx k).trans (le_max_left _ _)

theorem hp_zero_mem {d m : ℕ} (A : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) : (0 : Fin d → ℝ) ∈ HP A := by
  intro i; simp

theorem hp_zero_interior {d m : ℕ} (A : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) :
    (0 : Fin d → ℝ) ∈ interior (HP A) := by
  have hopen : IsOpen {x : Fin d → ℝ | ∀ i, A i x < 1} := by
    have : {x : Fin d → ℝ | ∀ i, A i x < 1} = ⋂ i, {x | A i x < 1} := by ext; simp
    rw [this]; exact isOpen_iInter_of_finite fun i => isOpen_lt (A i).continuous continuous_const
  have h0 : (0 : Fin d → ℝ) ∈ {x : Fin d → ℝ | ∀ i, A i x < 1} := by simp
  exact interior_maximal (fun x hx i => (hx i).le) hopen h0

theorem hp_tight_frontier {d m : ℕ} (A : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) {b : Fin d → ℝ}
    (hb : b ∈ HP A) {i : Fin m} (hi : A i b = 1) : b ∈ frontier (HP A) := by
  rw [(hp_closed A).frontier_eq]
  refine ⟨hb, fun hint => ?_⟩
  have hc : Continuous fun t : ℝ => (1 + t) • b := by fun_prop
  have ht : Filter.Tendsto (fun t : ℝ => (1 + t) • b) (nhds 0) (nhds b) := by
    simpa using hc.tendsto 0
  have hev := ht.eventually (mem_interior_iff_mem_nhds.mp hint)
  have hev2 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), (1 + t) • b ∈ HP A :=
    nhdsWithin_le_nhds hev
  obtain ⟨t, htP, ht0⟩ := (hev2.and eventually_mem_nhdsWithin).exists
  have h1 := htP i
  rw [map_smul, hi, smul_eq_mul, mul_one] at h1
  linarith [Set.mem_Ioi.mp ht0]

theorem hp_pos_dir {d m : ℕ} (A : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) {R : ℝ}
    (hR : ∀ x ∈ HP A, ∀ k, |x k| ≤ R) (u : Fin d → ℝ) (hu : u ≠ 0) : ∃ i, 0 < A i u := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨k, hk⟩ : ∃ k, u k ≠ 0 := by
    by_contra h; push_neg at h; exact hu (funext h)
  have hpos : 0 < |u k| := abs_pos.mpr hk
  set t : ℝ := (|R| + 1) / |u k| with ht
  have htpos : 0 < t := div_pos (by positivity) hpos
  have hmem : t • u ∈ HP A := by
    intro i; rw [map_smul, smul_eq_mul]
    nlinarith [hcon i]
  have h := hR _ hmem k
  rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos htpos, ht, div_mul_cancel₀ _ hpos.ne'] at h
  linarith [le_abs_self R]

theorem hp_oracle {d m : ℕ} (A : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) {R : ℝ}
    (hR : ∀ x ∈ HP A, ∀ k, |x k| ≤ R) : ∃ oracle, IsPolytopeRayOracle (HP A) oracle := by
  have key : ∀ u : Fin d → ℝ, u ≠ 0 → ∃ t : ℝ, 0 < t ∧ t • u ∈ frontier (HP A) := by
    intro u hu
    obtain ⟨i0, hi0⟩ := hp_pos_dir A hR u hu
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => A i u)
      ⟨i0, Finset.mem_univ _⟩
    have hjpos : 0 < A j u := lt_of_lt_of_le hi0 (hj i0 (Finset.mem_univ _))
    refine ⟨(A j u)⁻¹, inv_pos.mpr hjpos, hp_tight_frontier A (i := j) ?_ ?_⟩
    · intro i
      rw [map_smul, smul_eq_mul, inv_mul_le_iff₀ hjpos, mul_one]
      exact hj i (Finset.mem_univ _)
    · rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hjpos.ne']
  refine ⟨fun u => if hu : u = 0 then 0 else (Classical.choose (key u hu)) • u, fun v hv => ?_⟩
  simp only [dif_neg hv]
  exact ⟨(Classical.choose_spec (key v hv)).2, _, (Classical.choose_spec (key v hv)).1, rfl⟩

/-- Patch a ray oracle: answer with `O1` wherever its answer lies on the frontier. -/
theorem oracle_patch {d : ℕ} {P : Set (Fin d → ℝ)} (O1 O2 : (Fin d → ℝ) → Fin d → ℝ)
    (h1 : ∀ v, v ≠ 0 → ∃ t : ℝ, 0 < t ∧ O1 v = t • v) (h2 : IsPolytopeRayOracle P O2) :
    IsPolytopeRayOracle P (fun v => if O1 v ∈ frontier P then O1 v else O2 v) := by
  intro v hv
  by_cases h : O1 v ∈ frontier P
  · simp only [if_pos h]; exact ⟨h, h1 v hv⟩
  · simp only [if_neg h]; exact h2 v hv

theorem hp_isDPolytope {d m : ℕ} (A : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) {R : ℝ}
    (hR : ∀ x ∈ HP A, ∀ k, |x k| ≤ R) : IsDPolytope (HP A) := by
  have hc := hp_compact A hR
  have hf : ((HP A).extremePoints ℝ).Finite := hpoly_extreme_finite A
  have hhull := compact_eq_hull_of_finite_ext hc (hp_convex A) hf
  refine ⟨⟨_, hf, ?_, hhull.symm⟩, ?_⟩
  · by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have h0 := hp_zero_mem A
    rw [← hhull, hne, convexHull_empty] at h0
    exact h0
  · exact (hp_convex A).interior_nonempty_iff_affineSpan_eq_top.mp ⟨0, hp_zero_interior A⟩

theorem face_eq_hull {d : ℕ} {P : Set (Fin d → ℝ)} (hc : IsCompact P) (hcv : Convex ℝ P)
    (hf : (P.extremePoints ℝ).Finite) {F : Set (Fin d → ℝ)} (hF : IsExposed ℝ P F) :
    F = convexHull ℝ (F ∩ P.extremePoints ℝ) := by
  have hFc : IsCompact F := hF.isCompact hc
  have hFcv : Convex ℝ F := hF.convex hcv
  have he : F.extremePoints ℝ = F ∩ P.extremePoints ℝ := hF.isExtreme.extremePoints_eq
  rw [← he]
  exact (compact_eq_hull_of_finite_ext hFc hFcv
    (by rw [he]; exact hf.subset Set.inter_subset_right)).symm

theorem faces_finite {d : ℕ} {P : Set (Fin d → ℝ)} (hc : IsCompact P) (hcv : Convex ℝ P)
    (hf : (P.extremePoints ℝ).Finite) : Finite (PolytopeFace P) := by
  haveI := hf.finite_subsets.to_subtype
  refine Finite.of_injective (β := ↥{t | t ⊆ P.extremePoints ℝ})
    (fun F => ⟨F.val ∩ P.extremePoints ℝ, Set.inter_subset_right⟩) ?_
  intro F G h
  have h' : F.val ∩ P.extremePoints ℝ = G.val ∩ P.extremePoints ℝ := congrArg Subtype.val h
  apply Subtype.ext
  calc F.val = convexHull ℝ (F.val ∩ P.extremePoints ℝ) := face_eq_hull hc hcv hf F.2
    _ = convexHull ℝ (G.val ∩ P.extremePoints ℝ) := by rw [h']
    _ = G.val := (face_eq_hull hc hcv hf G.2).symm

theorem hp_faces_finite {d m : ℕ} (A : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) {R : ℝ}
    (hR : ∀ x ∈ HP A, ∀ k, |x k| ≤ R) : ∃ n : ℕ, Nonempty (Fin n ≃ PolytopeFace (HP A)) := by
  haveI := faces_finite (hp_compact A hR) (hp_convex A) (hpoly_extreme_finite A)
  exact ⟨Nat.card (PolytopeFace (HP A)), ⟨(Finite.equivFin _).symm⟩⟩

theorem facet_two_pts {m : ℕ} (A : Fin m → (Fin 2 → ℝ) →L[ℝ] ℝ) (i : Fin m) {p q : Fin 2 → ℝ}
    (hp : p ∈ HP A) (hq : q ∈ HP A) (hpi : A i p = 1) (hqi : A i q = 1) (hpq : p ≠ q) :
    {x ∈ HP A | A i x = 1}.Nonempty ∧ IsExposed ℝ (HP A) {x ∈ HP A | A i x = 1} ∧
      Module.finrank ℝ (affineSpan ℝ {x ∈ HP A | A i x = 1}).direction = 2 - 1 := by
  refine ⟨⟨p, hp, hpi⟩, isExposed_level _ (A i) (fun x hx => hx i), ?_⟩
  set F := {x ∈ HP A | A i x = 1} with hF
  have hle : (affineSpan ℝ F).direction ≤ LinearMap.ker (A i : (Fin 2 → ℝ) →ₗ[ℝ] ℝ) := by
    rw [direction_affineSpan, vectorSpan_def, Submodule.span_le]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    simp [LinearMap.mem_ker, vsub_eq_sub, map_sub, hx.2, hy.2]
  have hker : Module.finrank ℝ (LinearMap.ker (A i : (Fin 2 → ℝ) →ₗ[ℝ] ℝ)) ≤ 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker (A i : (Fin 2 → ℝ) →ₗ[ℝ] ℝ)
    rw [Module.finrank_fin_fun] at h
    have hr : 0 < Module.finrank ℝ (LinearMap.range (A i : (Fin 2 → ℝ) →ₗ[ℝ] ℝ)) := by
      apply Nat.pos_of_ne_zero
      intro h0
      rw [Submodule.finrank_eq_zero] at h0
      have h1 : (1 : ℝ) ∈ LinearMap.range (A i : (Fin 2 → ℝ) →ₗ[ℝ] ℝ) := ⟨p, by simp [hpi]⟩
      rw [h0, Submodule.mem_bot] at h1
      exact one_ne_zero h1
    omega
  have hne : p -ᵥ q ∈ (affineSpan ℝ F).direction :=
    AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ F ⟨hp, hpi⟩)
      (subset_affineSpan ℝ F ⟨hq, hqi⟩)
  have hpos : 0 < Module.finrank ℝ (affineSpan ℝ F).direction := by
    apply Nat.pos_of_ne_zero
    intro h0
    rw [Submodule.finrank_eq_zero] at h0
    rw [h0, Submodule.mem_bot, vsub_eq_sub, sub_eq_zero] at hne
    exact hpq hne
  have := Submodule.finrank_mono hle
  omega

theorem faces_lower {d : ℕ} {P : Set (Fin d → ℝ)} [Finite (PolytopeFace P)] {k r : ℕ}
    (G : Fin k → Set (Fin d → ℝ)) (hG : ∀ j, IsExposed ℝ P (G j)) (v : Fin r → Fin d → ℝ)
    (sig : Fin k → Finset (Fin r)) (hsig : ∀ j i, v i ∈ G j ↔ i ∈ sig j)
    (hinj : Function.Injective sig) : k ≤ Nat.card (PolytopeFace P) := by
  have hGinj : Function.Injective G := by
    intro j j' h; apply hinj; ext i; rw [← hsig, ← hsig, h]
  have := Nat.card_le_card_of_injective (fun j : Fin k => (⟨G j, hG j⟩ : PolytopeFace P))
    (fun j j' h => hGinj (congrArg Subtype.val h))
  simpa using this

theorem facets_lower {d : ℕ} {P : Set (Fin d → ℝ)} [Finite (PolytopeFace P)] {k r e : ℕ}
    (G : Fin k → Set (Fin d → ℝ))
    (hG : ∀ j, (G j).Nonempty ∧ IsExposed ℝ P (G j) ∧
      Module.finrank ℝ (affineSpan ℝ (G j)).direction = e)
    (v : Fin r → Fin d → ℝ) (sig : Fin k → Finset (Fin r)) (hsig : ∀ j i, v i ∈ G j ↔ i ∈ sig j)
    (hinj : Function.Injective sig) : k ≤ faceCount P e := by
  have hGinj : Function.Injective G := by
    intro j j' h; apply hinj; ext i; rw [← hsig, ← hsig, h]
  set S := {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
    Module.finrank ℝ (affineSpan ℝ F).direction = e} with hSdef
  have hS : S.Finite := by
    have : S ⊆ Set.range (fun F : PolytopeFace P => F.val) := fun F hF => ⟨⟨F, hF.2.1⟩, rfl⟩
    exact (Set.finite_range _).subset this
  have hsub : Set.range G ⊆ S := by rintro _ ⟨j, rfl⟩; exact hG j
  unfold faceCount
  calc k = (Set.range G).ncard := by rw [Set.ncard_range_of_injective hGinj]; simp
    _ ≤ S.ncard := Set.ncard_le_ncard hsub hS

theorem vertex_face {d m : ℕ} (A : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) (i j : Fin m) :
    IsExposed ℝ (HP A) {x ∈ HP A | ((2:ℝ)⁻¹ • (A i + A j)) x = 1} ∧
    ∀ x, x ∈ {x ∈ HP A | ((2:ℝ)⁻¹ • (A i + A j)) x = 1} ↔
      (x ∈ HP A ∧ A i x = 1 ∧ A j x = 1) := by
  refine ⟨isExposed_level _ _ (fun x hx => ?_), fun x => ?_⟩
  · have := hx i; have := hx j
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, smul_eq_mul]
    linarith
  · simp only [Set.mem_sep_iff, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      smul_eq_mul]
    constructor
    · rintro ⟨hx, h⟩; have := hx i; have := hx j; exact ⟨hx, by linarith, by linarith⟩
    · rintro ⟨hx, h1, h2⟩; exact ⟨hx, by rw [h1, h2]; norm_num⟩

/-- In a centrally symmetric set, an exposed face holding an antipodal pair is everything. -/
theorem sym_face_full {d : ℕ} {P F : Set (Fin d → ℝ)} (hsym : ∀ y ∈ P, -y ∈ P)
    (hF : IsExposed ℝ P F) {x : Fin d → ℝ} (hx : x ∈ F) (hnx : -x ∈ F) : P ⊆ F := by
  obtain ⟨l, rfl⟩ := hF ⟨x, hx⟩
  intro y hy
  have h1 := hx.2 (-x) hnx.1
  have h2 := hnx.2 x hx.1
  simp only [map_neg] at h1 h2
  refine ⟨hy, fun z hz => ?_⟩
  have h3 := hx.2 z hz
  have h4 := hx.2 (-y) (hsym y hy)
  rw [map_neg] at h4
  linarith

end HPoly


section Square

def sqK : Fin 4 → Fin 2 := ![0, 1, 0, 1]
def sqS : Fin 4 → ℝ := ![1, 1, -1, -1]
def sqV : Fin 4 → Fin 2 → ℝ := ![![1, 1], ![-1, 1], ![-1, -1], ![1, -1]]
def sqSig : Fin 4 → Finset (Fin 4) := ![{0, 3}, {0, 1}, {1, 2}, {2, 3}]

noncomputable def sqA : Fin 4 → (Fin 2 → ℝ) →L[ℝ] ℝ :=
  fun i => sqS i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (sqK i)

theorem sqA_apply (i : Fin 4) (x : Fin 2 → ℝ) : sqA i x = sqS i * x (sqK i) := by
  simp [sqA]

theorem sqA_form : ∀ i, ∃ (k : Fin 2) (σ : ℝ), (σ = 1 ∨ σ = -1 ∨ σ = 0) ∧
    ∀ x, sqA i x = σ * x k := by
  intro i
  refine ⟨sqK i, sqS i, ?_, fun x => sqA_apply i x⟩
  fin_cases i <;> simp [sqS]

theorem mem_HP_sq (x : Fin 2 → ℝ) : x ∈ HP sqA ↔ ∀ k, |x k| ≤ 1 := by
  constructor
  · intro h
    have h0 : x 0 ≤ 1 := by simpa [sqA_apply, sqK, sqS] using h 0
    have h1 : x 1 ≤ 1 := by simpa [sqA_apply, sqK, sqS] using h 1
    have h2 : -1 * x 0 ≤ 1 := by
      have := h 2; rw [sqA_apply] at this; simpa [sqK, sqS] using this
    have h3 : -1 * x 1 ≤ 1 := by
      have := h 3; rw [sqA_apply] at this; simpa [sqK, sqS] using this
    rw [Fin.forall_fin_two]
    exact ⟨abs_le.2 ⟨by linarith, h0⟩, abs_le.2 ⟨by linarith, h1⟩⟩
  · intro h i
    have h0 := abs_le.1 (h 0)
    have h1 := abs_le.1 (h 1)
    rw [sqA_apply]
    fin_cases i <;> simp [sqK, sqS] <;> linarith

theorem sq_bound : ∀ x ∈ HP sqA, ∀ k, |x k| ≤ 1 := fun x hx => (mem_HP_sq x).1 hx

theorem sq_symm : ∀ y ∈ HP sqA, -y ∈ HP sqA := by
  intro y hy
  rw [mem_HP_sq] at hy ⊢
  intro k
  simpa [abs_neg] using hy k

theorem sqV_mem (i : Fin 4) : sqV i ∈ HP sqA := by
  rw [mem_HP_sq]
  intro k
  fin_cases i <;> fin_cases k <;> simp [sqV]

theorem sqV_neg (i : Fin 4) : sqV (i + 2) = -sqV i := by
  fin_cases i <;> funext k <;> fin_cases k <;> simp [sqV]

theorem sq_ext_pm (v : Fin 2 → ℝ) (hv : v ∈ (HP sqA).extremePoints ℝ) :
    ∀ k, v k = 1 ∨ v k = -1 := by
  intro k
  by_contra hne
  push Not at hne
  obtain ⟨hn1, hn2⟩ := hne
  have hw := hpoly_extreme_rigid sqA hv (Pi.single k 1) (fun i hi => ?_)
  · have := congrFun hw k
    simp at this
  · rw [sqA_apply] at hi ⊢
    by_cases hk : sqK i = k
    · exfalso
      rw [hk] at hi
      have hs : sqS i = 1 ∨ sqS i = -1 := by fin_cases i <;> simp [sqS]
      rcases hs with hs | hs <;> rw [hs] at hi
      · exact hn1 (by linarith)
      · exact hn2 (by linarith)
    · rw [Pi.single_eq_of_ne hk]
      ring

theorem sq_ext (v : Fin 2 → ℝ) (hv : v ∈ (HP sqA).extremePoints ℝ) : ∃ i, v = sqV i := by
  have h0 := sq_ext_pm v hv 0
  have h1 := sq_ext_pm v hv 1
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · exact ⟨0, by funext k; fin_cases k <;> simp [sqV, h0, h1]⟩
  · exact ⟨3, by funext k; fin_cases k <;> simp [sqV, h0, h1]⟩
  · exact ⟨1, by funext k; fin_cases k <;> simp [sqV, h0, h1]⟩
  · exact ⟨2, by funext k; fin_cases k <;> simp [sqV, h0, h1]⟩

theorem sq_finite_faces : Finite (PolytopeFace (HP sqA)) :=
  faces_finite (hp_compact sqA sq_bound) (hp_convex sqA) (hpoly_extreme_finite sqA)

theorem sqSig_inj : Function.Injective sqSig := by decide

theorem sq_hsig : ∀ j i, sqV i ∈ {x ∈ HP sqA | sqA j x = 1} ↔ i ∈ sqSig j := by
  intro j i
  rw [Set.mem_sep_iff, and_iff_right (sqV_mem i), sqA_apply]
  fin_cases j <;> fin_cases i <;> norm_num [sqV, sqK, sqS, sqSig] <;> decide

theorem sq_facets : 4 ≤ faceCount (HP sqA) 1 := by
  haveI := sq_finite_faces
  have hG : ∀ j : Fin 4, ({x ∈ HP sqA | sqA j x = 1}).Nonempty ∧
      IsExposed ℝ (HP sqA) {x ∈ HP sqA | sqA j x = 1} ∧
      Module.finrank ℝ (affineSpan ℝ {x ∈ HP sqA | sqA j x = 1}).direction = 2 - 1 := by
    intro j
    have key : ∃ a b : Fin 4, sqA j (sqV a) = 1 ∧ sqA j (sqV b) = 1 ∧ sqV a ≠ sqV b := by
      have hne : ∀ a b : Fin 4, a ≠ b → sqV a ≠ sqV b := by
        intro a b hab h
        exact hab (by
          fin_cases a <;> fin_cases b <;> first
            | rfl
            | (exfalso; have e0 := congrFun h 0; have e1 := congrFun h 1;
               revert e0 e1; norm_num [sqV]))
      have hm : ∀ a, a ∈ sqSig j → sqA j (sqV a) = 1 := by
        intro a ha
        have := (sq_hsig j a).2 ha
        exact this.2
      fin_cases j
      · exact ⟨0, 3, hm 0 (by decide), hm 3 (by decide), hne 0 3 (by decide)⟩
      · exact ⟨0, 1, hm 0 (by decide), hm 1 (by decide), hne 0 1 (by decide)⟩
      · exact ⟨1, 2, hm 1 (by decide), hm 2 (by decide), hne 1 2 (by decide)⟩
      · exact ⟨2, 3, hm 2 (by decide), hm 3 (by decide), hne 2 3 (by decide)⟩
    obtain ⟨a, b, ha, hb, hab⟩ := key
    exact facet_two_pts sqA j (sqV_mem a) (sqV_mem b) ha hb hab
  exact facets_lower (fun j => {x ∈ HP sqA | sqA j x = 1}) hG sqV sqSig sq_hsig sqSig_inj

def sqT : Finset (Finset (Fin 4)) :=
  Finset.univ.filter (fun S => S = Finset.univ ∨ ∀ i ∈ S, i + 2 ∉ S)

theorem sqT_card : sqT.card = 10 := by decide

noncomputable def sigF (F : PolytopeFace (HP sqA)) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => sqV i ∈ F.val)

theorem sigF_mem (F : PolytopeFace (HP sqA)) : sigF F ∈ sqT := by
  simp only [sqT, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h : ∃ i, sqV i ∈ F.val ∧ sqV (i + 2) ∈ F.val
  · left
    obtain ⟨i, h1, h2⟩ := h
    rw [sqV_neg] at h2
    have hsub := sym_face_full sq_symm F.2 h1 h2
    ext j
    simp [sigF, hsub (sqV_mem j)]
  · right
    intro i hi hi2
    simp only [sigF, Finset.mem_filter, Finset.mem_univ, true_and] at hi hi2
    exact h ⟨i, hi, hi2⟩

theorem sq_faces_le : Nat.card (PolytopeFace (HP sqA)) ≤ 10 := by
  have hc := hp_compact sqA sq_bound
  have hcv := hp_convex sqA
  have hf := hpoly_extreme_finite sqA
  have hinj : Function.Injective (fun F : PolytopeFace (HP sqA) => (⟨sigF F, sigF_mem F⟩ : sqT)) := by
    intro F G hFG
    have hs : sigF F = sigF G := congrArg Subtype.val hFG
    have key : ∀ (F G : PolytopeFace (HP sqA)), sigF F = sigF G →
        F.val ∩ (HP sqA).extremePoints ℝ ⊆ G.val ∩ (HP sqA).extremePoints ℝ := by
      intro F G hs x hx
      obtain ⟨i, rfl⟩ := sq_ext x hx.2
      have hi : i ∈ sigF F := by
        simp only [sigF, Finset.mem_filter, Finset.mem_univ, true_and]; exact hx.1
      rw [hs] at hi
      simp only [sigF, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact ⟨hi, hx.2⟩
    have heq : F.val ∩ (HP sqA).extremePoints ℝ = G.val ∩ (HP sqA).extremePoints ℝ :=
      Set.Subset.antisymm (key F G hs) (key G F hs.symm)
    apply Subtype.ext
    calc F.val = convexHull ℝ (F.val ∩ (HP sqA).extremePoints ℝ) := face_eq_hull hc hcv hf F.2
      _ = convexHull ℝ (G.val ∩ (HP sqA).extremePoints ℝ) := by rw [heq]
      _ = G.val := (face_eq_hull hc hcv hf G.2).symm
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_finsetCard, sqT_card] at this
  exact this

theorem sq_faces_equiv_le (n : ℕ) (e : Fin n ≃ PolytopeFace (HP sqA)) : n ≤ 10 := by
  have := Nat.card_congr e
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  rw [this]; exact sq_faces_le

noncomputable def padL {d r : ℕ} (A : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (n : ℕ) :
    Fin n → (Fin d → ℝ) →L[ℝ] ℝ :=
  fun i => if h : i.val < r then A ⟨i.val, h⟩ else 0

theorem hp_padL {d r n : ℕ} (A : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (hn : r ≤ n) :
    HP (padL A n) = HP A := by
  ext x
  simp only [HP, Set.mem_setOf_eq]
  constructor
  · intro h i
    have := h ⟨i.val, by omega⟩
    simpa [padL, i.2] using this
  · intro h i
    by_cases hi : i.val < r
    · simpa [padL, hi] using h ⟨i.val, hi⟩
    · simp [padL, hi]

theorem padL_form {r n : ℕ} (A : Fin r → (Fin 2 → ℝ) →L[ℝ] ℝ)
    (hA : ∀ i, ∃ (k : Fin 2) (σ : ℝ), (σ = 1 ∨ σ = -1 ∨ σ = 0) ∧ ∀ x, A i x = σ * x k) :
    ∀ i, ∃ (k : Fin 2) (σ : ℝ), (σ = 1 ∨ σ = -1 ∨ σ = 0) ∧ ∀ x, padL A n i x = σ * x k := by
  intro i
  by_cases hi : i.val < r
  · obtain ⟨k, σ, hσ, hx⟩ := hA ⟨i.val, hi⟩
    exact ⟨k, σ, hσ, fun x => by simp only [padL, dif_pos hi]; exact hx x⟩
  · exact ⟨0, 0, Or.inr (Or.inr rfl), fun x => by simp [padL, hi]⟩

end Square


section Pent

theorem faces_lower_ft {d : ℕ} {P : Set (Fin d → ℝ)} [Finite (PolytopeFace P)] {ι : Type}
    [Fintype ι] {r : ℕ} (G : ι → Set (Fin d → ℝ)) (hG : ∀ j, IsExposed ℝ P (G j))
    (v : Fin r → Fin d → ℝ) (sig : ι → Finset (Fin r)) (hsig : ∀ j i, v i ∈ G j ↔ i ∈ sig j)
    (hinj : Function.Injective sig) : Fintype.card ι ≤ Nat.card (PolytopeFace P) := by
  have hGinj : Function.Injective G := by
    intro j j' h; apply hinj; ext i; rw [← hsig, ← hsig, h]
  have := Nat.card_le_card_of_injective (fun j : ι => (⟨G j, hG j⟩ : PolytopeFace P))
    (fun j j' h => hGinj (congrArg Subtype.val h))
  simpa using this

noncomputable def pentG (A : Fin 5 → (Fin 2 → ℝ) →L[ℝ] ℝ) :
    Fin 5 ⊕ Fin 5 ⊕ Unit → Set (Fin 2 → ℝ)
  | .inl i => {x ∈ HP A | A i x = 1}
  | .inr (.inl i) => {x ∈ HP A | ((2:ℝ)⁻¹ • (A i + A (i + 1))) x = 1}
  | .inr (.inr _) => HP A

def pentSig : Fin 5 ⊕ Fin 5 ⊕ Unit → Finset (Fin 5)
  | .inl i => {i, i - 1}
  | .inr (.inl i) => {i}
  | .inr (.inr _) => Finset.univ

theorem pentSig_inj : Function.Injective pentSig := by decide

theorem pent_comb1 : ∀ i k : Fin 5, (k = i ∨ k + 1 = i) ↔ k ∈ ({i, i - 1} : Finset (Fin 5)) := by
  decide

theorem pent_comb2 : ∀ i k : Fin 5, ((k = i ∨ k + 1 = i) ∧ (k = i + 1 ∨ k + 1 = i + 1)) ↔
    k ∈ ({i} : Finset (Fin 5)) := by
  decide

theorem pent_faces (A : Fin 5 → (Fin 2 → ℝ) →L[ℝ] ℝ) [Finite (PolytopeFace (HP A))]
    (w : Fin 5 → Fin 2 → ℝ) (hw : ∀ k, w k ∈ HP A)
    (hT : ∀ i k, A i (w k) = 1 ↔ (k = i ∨ k + 1 = i)) :
    11 ≤ Nat.card (PolytopeFace (HP A)) := by
  have hG : ∀ j, IsExposed ℝ (HP A) (pentG A j) := by
    rintro (i | i | u)
    · exact isExposed_level _ (A i) (fun x hx => hx i)
    · exact (vertex_face A i (i + 1)).1
    · exact IsExposed.refl (𝕜 := ℝ) (HP A)
  have hsig : ∀ j k, w k ∈ pentG A j ↔ k ∈ pentSig j := by
    rintro (i | i | u) k
    · simp only [pentG, pentSig]
      rw [Set.mem_sep_iff, and_iff_right (hw k), hT, pent_comb1]
    · simp only [pentG, pentSig]
      rw [(vertex_face A i (i + 1)).2, and_iff_right (hw k), hT, hT, pent_comb2]
    · simp only [pentG, pentSig]
      simp [hw k]
  have := faces_lower_ft (pentG A) hG w pentSig hsig pentSig_inj
  simpa using this

theorem pent_comb3 : ∀ a b : Fin 5,
    (∀ i : Fin 5, (a = i ∨ a + 1 = i) ↔ (b = i ∨ b + 1 = i)) → a = b := by
  decide

theorem pent_facets (A : Fin 5 → (Fin 2 → ℝ) →L[ℝ] ℝ) [Finite (PolytopeFace (HP A))]
    (w : Fin 5 → Fin 2 → ℝ) (hw : ∀ k, w k ∈ HP A)
    (hT : ∀ i k, A i (w k) = 1 ↔ (k = i ∨ k + 1 = i)) :
    5 ≤ faceCount (HP A) 1 := by
  have hne : ∀ a b, a ≠ b → w a ≠ w b := by
    intro a b hab h
    apply hab
    apply pent_comb3
    intro i
    rw [← hT, ← hT, h]
  have hG : ∀ j : Fin 5, ({x ∈ HP A | A j x = 1}).Nonempty ∧
      IsExposed ℝ (HP A) {x ∈ HP A | A j x = 1} ∧
      Module.finrank ℝ (affineSpan ℝ {x ∈ HP A | A j x = 1}).direction = 2 - 1 := by
    intro j
    have h1 : A j (w j) = 1 := (hT j j).2 (Or.inl rfl)
    have h2 : A j (w (j - 1)) = 1 := (hT j (j - 1)).2 (Or.inr (by simp))
    have h3 : j ≠ j - 1 := by
      have : ∀ j : Fin 5, j ≠ j - 1 := by decide
      exact this j
    exact facet_two_pts A j (hw j) (hw (j - 1)) h1 h2 (hne _ _ h3)
  have hsig : ∀ j k, w k ∈ {x ∈ HP A | A j x = 1} ↔ k ∈ ({j, j - 1} : Finset (Fin 5)) := by
    intro j k
    rw [Set.mem_sep_iff, and_iff_right (hw k), hT, pent_comb1]
  have hinj : Function.Injective (fun j : Fin 5 => ({j, j - 1} : Finset (Fin 5))) := by decide
  exact facets_lower (fun j => {x ∈ HP A | A j x = 1}) hG w _ hsig hinj

theorem pent_faces_equiv (A : Fin 5 → (Fin 2 → ℝ) →L[ℝ] ℝ) [Finite (PolytopeFace (HP A))]
    (w : Fin 5 → Fin 2 → ℝ) (hw : ∀ k, w k ∈ HP A)
    (hT : ∀ i k, A i (w k) = 1 ↔ (k = i ∨ k + 1 = i))
    (n : ℕ) (e : Fin n ≃ PolytopeFace (HP A)) : 11 ≤ n := by
  have := Nat.card_congr e
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  rw [this]; exact pent_faces A w hw hT

end Pent


section PentConcrete

noncomputable def penA (C0 C1 : Fin 5 → ℝ) : Fin 5 → (Fin 2 → ℝ) →L[ℝ] ℝ :=
  fun i => C0 i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 +
    C1 i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1

theorem penA_apply (C0 C1 : Fin 5 → ℝ) (i : Fin 5) (x : Fin 2 → ℝ) :
    penA C0 C1 i x = C0 i * x 0 + C1 i * x 1 := by
  simp [penA]

/-! Cut at the corner `(a, b)`: rows `a x0`, `t (a x0 + b x1)`, `b x1`, `-a x0`, `-b x1`
with `t (1 + u) = 1`. -/
def cutC0 (a t : ℝ) : Fin 5 → ℝ := ![a, t * a, 0, -a, 0]
def cutC1 (b t : ℝ) : Fin 5 → ℝ := ![0, t * b, b, 0, -b]
def cutW (a b u : ℝ) : Fin 5 → Fin 2 → ℝ :=
  ![![a, b * u], ![a * u, b], ![-a, b], ![-a, -b], ![a, -b]]

theorem cut_hT (a b u t : ℝ) (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) (hu0 : 0 < u)
    (hu1 : u < 1) (ht0 : 0 < t) (ht : t * (1 + u) = 1) :
    ∀ i k, penA (cutC0 a t) (cutC1 b t) i (cutW a b u k) = 1 ↔ (k = i ∨ k + 1 = i) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> intro i k <;> rw [penA_apply] <;>
    fin_cases i <;> fin_cases k <;> simp [cutC0, cutC1, cutW] <;>
    first
      | linarith
      | linear_combination ht
      | (intro h; linarith)
      | (intro h; nlinarith [ht, ht0, hu0, hu1])

theorem cut_mem (a b u t : ℝ) (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) (hu0 : 0 < u)
    (hu1 : u < 1) (ht0 : 0 < t) (ht : t * (1 + u) = 1) :
    ∀ k, cutW a b u k ∈ HP (penA (cutC0 a t) (cutC1 b t)) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> intro k i <;> rw [penA_apply] <;>
    fin_cases i <;> fin_cases k <;> simp [cutC0, cutC1, cutW] <;>
    first
      | linarith
      | nlinarith [ht, ht0, hu0, hu1]

theorem cut_bound (a b t : ℝ) (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    ∀ x ∈ HP (penA (cutC0 a t) (cutC1 b t)), ∀ k, |x k| ≤ 1 := by
  intro x hx
  have h0 := hx 0; have h2 := hx 2; have h3 := hx 3; have h4 := hx 4
  rw [penA_apply] at h0 h2 h3 h4
  simp [cutC0, cutC1] at h0 h2 h3 h4
  rw [Fin.forall_fin_two]
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    exact ⟨abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by linarith, by linarith⟩⟩

/-! Bump over the edge `x0 = a`: apex `(2a, 0)`. -/
noncomputable def bumpC0 (a : ℝ) : Fin 5 → ℝ := ![a / 2, 0, -a, 0, a / 2]
noncomputable def bumpC1 : Fin 5 → ℝ := ![1 / 2, 1, 0, -1, -1 / 2]
def bumpW (a : ℝ) : Fin 5 → Fin 2 → ℝ := ![![a, 1], ![-a, 1], ![-a, -1], ![a, -1], ![2 * a, 0]]

theorem bump_hT (a : ℝ) (ha : a = 1 ∨ a = -1) :
    ∀ i k, penA (bumpC0 a) bumpC1 i (bumpW a k) = 1 ↔ (k = i ∨ k + 1 = i) := by
  rcases ha with rfl | rfl <;> intro i k <;> rw [penA_apply] <;>
    fin_cases i <;> fin_cases k <;> norm_num [bumpC0, bumpC1, bumpW] <;> decide

theorem bump_mem (a : ℝ) (ha : a = 1 ∨ a = -1) : ∀ k, bumpW a k ∈ HP (penA (bumpC0 a) bumpC1) := by
  rcases ha with rfl | rfl <;> intro k i <;> rw [penA_apply] <;>
    fin_cases i <;> fin_cases k <;> norm_num [bumpC0, bumpC1, bumpW]

theorem bump_bound (a : ℝ) (ha : a = 1 ∨ a = -1) :
    ∀ x ∈ HP (penA (bumpC0 a) bumpC1), ∀ k, |x k| ≤ 3 := by
  intro x hx
  have h0 := hx 0; have h1 := hx 1; have h2 := hx 2; have h3 := hx 3
  rw [penA_apply] at h0 h1 h2 h3
  simp [bumpC0, bumpC1] at h0 h1 h2 h3
  rw [Fin.forall_fin_two]
  rcases ha with rfl | rfl <;>
    exact ⟨abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by linarith, by linarith⟩⟩

/-! Bump over the edge `x1 = b`: apex `(0, 2b)`. -/
noncomputable def bumpSC0 : Fin 5 → ℝ := ![1 / 2, 1, 0, -1, -1 / 2]
noncomputable def bumpSC1 (b : ℝ) : Fin 5 → ℝ := ![b / 2, 0, -b, 0, b / 2]
def bumpSW (b : ℝ) : Fin 5 → Fin 2 → ℝ := ![![1, b], ![1, -b], ![-1, -b], ![-1, b], ![0, 2 * b]]

theorem bumpS_hT (b : ℝ) (hb : b = 1 ∨ b = -1) :
    ∀ i k, penA bumpSC0 (bumpSC1 b) i (bumpSW b k) = 1 ↔ (k = i ∨ k + 1 = i) := by
  rcases hb with rfl | rfl <;> intro i k <;> rw [penA_apply] <;>
    fin_cases i <;> fin_cases k <;> norm_num [bumpSC0, bumpSC1, bumpSW] <;> decide

theorem bumpS_mem (b : ℝ) (hb : b = 1 ∨ b = -1) :
    ∀ k, bumpSW b k ∈ HP (penA bumpSC0 (bumpSC1 b)) := by
  rcases hb with rfl | rfl <;> intro k i <;> rw [penA_apply] <;>
    fin_cases i <;> fin_cases k <;> norm_num [bumpSC0, bumpSC1, bumpSW]

theorem bumpS_bound (b : ℝ) (hb : b = 1 ∨ b = -1) :
    ∀ x ∈ HP (penA bumpSC0 (bumpSC1 b)), ∀ k, |x k| ≤ 3 := by
  intro x hx
  have h0 := hx 0; have h1 := hx 1; have h2 := hx 2; have h3 := hx 3
  rw [penA_apply] at h0 h1 h2 h3
  simp [bumpSC0, bumpSC1] at h0 h1 h2 h3
  rw [Fin.forall_fin_two]
  rcases hb with rfl | rfl <;>
    exact ⟨abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by linarith, by linarith⟩⟩

end PentConcrete

/-! ## Chunk 8: assembly -/

section Assembly

def HPROG (program : List RayInstruction) : Prop :=

      ∀ P : Set (Fin 2 → ℝ), IsDPolytope P → (0 : Fin 2 → ℝ) ∈ interior P →
        ∀ oracle : (Fin 2 → ℝ) → (Fin 2 → ℝ), IsPolytopeRayOracle P oracle →
          2 + 1 ≤ faceCount P (2 - 1) →
          ∀ (L : Fin (faceCount P (2 - 1)) → (Fin 2 → ℝ) →L[ℝ] ℝ),
            P = {x | ∀ i, L i x ≤ 1} →
            (∀ i, L i = 0 ∨
              ({x ∈ P | L i x = 1}.Nonempty ∧ IsExposed ℝ P {x ∈ P | L i x = 1} ∧
                Module.finrank ℝ (affineSpan ℝ {x ∈ P | L i x = 1}).direction = 2 - 1)) →
            (∃ n : ℕ, Nonempty (Fin n ≃ PolytopeFace P)) →
            ∃ (t : ℕ) (c : RayConfiguration) (n : ℕ) (e : Fin n ≃ PolytopeFace P)
              (N : ℕ)
              (S_seq : ℕ → Finset (Fin (faceCount P (2 - 1))))
              (C_seq : ℕ → Finset (Fin 2 → ℝ))
              (q_seq : ℕ → ℕ),
              rayMachineRun program oracle t
                { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
              program[c.pc]? = some .halt ∧
              C_seq 0 = ∅ ∧
              q_seq 0 ≤ 2 + 1 ∧
              (∀ s < N,
                (S_seq (s + 1) = S_seq s ∧
                  ∃ v ∈ ({x : Fin 2 → ℝ | ∀ i ∈ S_seq s, L i x ≤ 1}).extremePoints ℝ,
                    v ∈ P ∧ v ∉ C_seq s ∧ C_seq (s + 1) = insert v (C_seq s) ∧
                    q_seq (s + 1) ≤ q_seq s + 1) ∨
                (C_seq (s + 1) = C_seq s ∧
                  ∃ v ∈ ({x : Fin 2 → ℝ | ∀ i ∈ S_seq s, L i x ≤ 1}).extremePoints ℝ,
                    oracle v ≠ v ∧
                    ∃ i_new : Fin (faceCount P (2 - 1)),
                      L i_new (oracle v) = 1 ∧
                      S_seq (s + 1) = insert i_new (S_seq s) ∧
                      q_seq (s + 1) ≤ q_seq s +
                        (1 + (2 - 1) * (2 * (faceCount P (2 - 1) - (S_seq s).card) + 3)))) ∧
              c.queries ≤ q_seq N ∧
              (∀ i : Fin n, c.tape (c.head + (i.val : ℤ)) = 1) ∧
              c.tape (c.head + (n : ℤ)) = 0 ∧
              ∀ i j : Fin n,
                c.tape (c.head + ((n + 1 + i.val * n + j.val : ℕ) : ℤ)) =
                  if (∀ x : Fin 2 → ℝ, IsExposed ℝ P {x} → x ∈ (e i).val → x ∈ (e j).val)
                  then 1 else 0

theorem run_query_set (prog : List RayInstruction) (O : (Fin 2 → ℝ) → Fin 2 → ℝ) :
    ∀ (t : ℕ) (c0 c : RayConfiguration), rayMachineRun prog O t c0 = some c →
      ∃ Qs : Finset (Fin 2 → ℝ), Qs.card + c0.queries ≤ c.queries ∧ (∀ u ∈ Qs, u ≠ 0) ∧
        ∀ s < t, ∀ c', rayMachineRun prog O s c0 = some c' → IsQ prog c' → qv 2 c' ∈ Qs := by
  intro t
  induction t with
  | zero =>
    intro c0 c h
    rw [run_zero] at h
    have e : c0 = c := Option.some.inj h
    subst e
    exact ⟨∅, by simp, by simp, fun s hs => absurd hs (Nat.not_lt_zero _)⟩
  | succ t ih =>
    intro c0 c h
    rw [run_succ] at h
    cases hst : rayMachineStep prog O c0 with
    | none => rw [hst] at h; simp at h
    | some c1 =>
      rw [hst, Option.bind_some] at h
      obtain ⟨Q1, hc1, hne1, hmem1⟩ := ih c1 c h
      have hq := step_queries prog O c0 c1 hst
      by_cases hQ : IsQ prog c0
      · refine ⟨insert (qv 2 c0) Q1, ?_, ?_, ?_⟩
        · have := Finset.card_insert_le (qv 2 c0) Q1
          rw [if_pos hQ] at hq; omega
        · intro u hu
          rcases Finset.mem_insert.1 hu with rfl | hu
          · exact step_query_nonzero prog O c0 c1 hst hQ
          · exact hne1 u hu
        · intro s hs c' hc' hq'
          cases s with
          | zero =>
            rw [run_zero] at hc'
            have e : c0 = c' := Option.some.inj hc'
            subst e; exact Finset.mem_insert_self _ _
          | succ s =>
            rw [run_succ, hst, Option.bind_some] at hc'
            exact Finset.mem_insert_of_mem (hmem1 s (by omega) c' hc' hq')
      · refine ⟨Q1, ?_, hne1, ?_⟩
        · rw [if_neg hQ] at hq; omega
        · intro s hs c' hc' hq'
          cases s with
          | zero =>
            rw [run_zero] at hc'
            have e : c0 = c' := Option.some.inj hc'
            subst e; exact absurd hq' hQ
          | succ s =>
            rw [run_succ, hst, Option.bind_some] at hc'
            exact hmem1 s (by omega) c' hc' hq'

theorem frontier_of_sub {P Q : Set (Fin 2 → ℝ)} (hQ : IsClosed Q) (hsub : Q ⊆ P)
    {p : Fin 2 → ℝ} (hp : p ∈ Q) (hpf : p ∈ frontier P) : p ∈ frontier Q := by
  rw [hQ.frontier_eq]
  exact ⟨hp, fun hi => hpf.2 (interior_mono hsub hi)⟩

theorem hp_sq_eq : HP sqA = sqSet := by
  ext x; exact mem_HP_sq x

theorem sq_frontier {p : Fin 2 → ℝ} (hp : p ∈ frontier (HP sqA)) :
    (∀ k, |p k| ≤ 1) ∧ (|p 0| = 1 ∨ |p 1| = 1) := by
  rw [hp_sq_eq, sqSet_closed.frontier_eq] at hp
  have h1 : ∀ k, |p k| ≤ 1 := hp.1
  refine ⟨h1, ?_⟩
  by_contra hne
  push_neg at hne
  have hne' : ∀ k, |p k| ≠ 1 := by
    intro k; fin_cases k
    · exact hne.1
    · exact hne.2
  exact hp.2 (sq_open_sub_interior (fun k => lt_of_le_of_ne (h1 k) (hne' k)))

theorem fin_max_lt {α : Type} (s : Finset α) (g : α → ℝ) (h : ∀ p ∈ s, g p < 1) :
    ∃ u : ℝ, 0 < u ∧ u < 1 ∧ ∀ p ∈ s, g p ≤ u := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1 / 2, by norm_num, by norm_num, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨u, hu0, hu1, hu⟩ := ih (fun p hp => h p (Finset.mem_insert_of_mem hp))
    refine ⟨max u (g a), lt_max_of_lt_left hu0, max_lt hu1 (h a (Finset.mem_insert_self _ _)), ?_⟩
    intro p hp
    rcases Finset.mem_insert.1 hp with rfl | hp
    · exact le_max_right _ _
    · exact (hu p hp).trans (le_max_left _ _)

theorem padL_facets {r n : ℕ} (A : Fin r → (Fin 2 → ℝ) →L[ℝ] ℝ) {P : Set (Fin 2 → ℝ)}
    (hA : ∀ j, ({x ∈ P | A j x = 1}).Nonempty ∧ IsExposed ℝ P {x ∈ P | A j x = 1} ∧
      Module.finrank ℝ (affineSpan ℝ {x ∈ P | A j x = 1}).direction = 2 - 1) :
    ∀ i, padL A n i = 0 ∨ ({x ∈ P | padL A n i x = 1}.Nonempty ∧
      IsExposed ℝ P {x ∈ P | padL A n i x = 1} ∧
      Module.finrank ℝ (affineSpan ℝ {x ∈ P | padL A n i x = 1}).direction = 2 - 1) := by
  intro i
  by_cases hi : i.val < r
  · right
    have e : padL A n i = A ⟨i.val, hi⟩ := by simp [padL, hi]
    rw [e]; exact hA _
  · left; simp [padL, hi]

theorem sq_rows : ∀ j : Fin 4, ({x ∈ HP sqA | sqA j x = 1}).Nonempty ∧
      IsExposed ℝ (HP sqA) {x ∈ HP sqA | sqA j x = 1} ∧
      Module.finrank ℝ (affineSpan ℝ {x ∈ HP sqA | sqA j x = 1}).direction = 2 - 1 := by
  intro j
  have key : ∃ a b : Fin 4, sqA j (sqV a) = 1 ∧ sqA j (sqV b) = 1 ∧ sqV a ≠ sqV b := by
    have hne : ∀ a b : Fin 4, a ≠ b → sqV a ≠ sqV b := by
      intro a b hab h
      exact hab (by
        fin_cases a <;> fin_cases b <;> first
          | rfl
          | (exfalso; have e0 := congrFun h 0; have e1 := congrFun h 1;
             revert e0 e1; norm_num [sqV]))
    have hm : ∀ a, a ∈ sqSig j → sqA j (sqV a) = 1 := by
      intro a ha
      have := (sq_hsig j a).2 ha
      exact this.2
    fin_cases j
    · exact ⟨0, 3, hm 0 (by decide), hm 3 (by decide), hne 0 3 (by decide)⟩
    · exact ⟨0, 1, hm 0 (by decide), hm 1 (by decide), hne 0 1 (by decide)⟩
    · exact ⟨1, 2, hm 1 (by decide), hm 2 (by decide), hne 1 2 (by decide)⟩
    · exact ⟨2, 3, hm 2 (by decide), hm 3 (by decide), hne 2 3 (by decide)⟩
  obtain ⟨a, b, ha, hb, hab⟩ := key
  exact facet_two_pts sqA j (sqV_mem a) (sqV_mem b) ha hb hab

theorem pent_rows (A : Fin 5 → (Fin 2 → ℝ) →L[ℝ] ℝ)
    (w : Fin 5 → Fin 2 → ℝ) (hw : ∀ k, w k ∈ HP A)
    (hT : ∀ i k, A i (w k) = 1 ↔ (k = i ∨ k + 1 = i)) :
    ∀ j : Fin 5, ({x ∈ HP A | A j x = 1}).Nonempty ∧
      IsExposed ℝ (HP A) {x ∈ HP A | A j x = 1} ∧
      Module.finrank ℝ (affineSpan ℝ {x ∈ HP A | A j x = 1}).direction = 2 - 1 := by
  have hne : ∀ a b, a ≠ b → w a ≠ w b := by
    intro a b hab h
    apply hab
    apply pent_comb3
    intro i
    rw [← hT, ← hT, h]
  intro j
  have h1 : A j (w j) = 1 := (hT j j).2 (Or.inl rfl)
  have h2 : A j (w (j - 1)) = 1 := (hT j (j - 1)).2 (Or.inr (by simp))
  have h3 : j ≠ j - 1 := by
    have : ∀ j : Fin 5, j ≠ j - 1 := by decide
    exact this j
  exact facet_two_pts A j (hw j) (hw (j - 1)) h1 h2 (hne _ _ h3)

theorem pent_contra (program : List RayInstruction) (hprog : HPROG program)
    (A : Fin 5 → (Fin 2 → ℝ) →L[ℝ] ℝ) (w : Fin 5 → Fin 2 → ℝ) (hw : ∀ k, w k ∈ HP A)
    (hT : ∀ i k, A i (w k) = 1 ↔ (k = i ∨ k + 1 = i)) {R : ℝ} (hR : ∀ x ∈ HP A, ∀ k, |x k| ≤ R)
    (O1 : (Fin 2 → ℝ) → Fin 2 → ℝ) (h1 : ∀ v, v ≠ 0 → ∃ t : ℝ, 0 < t ∧ O1 v = t • v)
    (t : ℕ) (c : RayConfiguration) (n : ℕ) (hn : n ≤ 10)
    (hrun : rayMachineRun program O1 t
      { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c)
    (hhalt : program[c.pc]? = some .halt)
    (htape0 : c.tape (c.head + (n : ℤ)) = 0)
    (hagree : ∀ s < t, ∀ c', rayMachineRun program O1 s
      { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c' → IsQ program c' →
        O1 (qv 2 c') ∈ frontier (HP A)) : False := by
  unfold HPROG at hprog
  obtain ⟨nf, hnf⟩ := hp_faces_finite A hR
  haveI : Finite (PolytopeFace (HP A)) := Finite.of_equiv _ hnf.some
  obtain ⟨O2, hO2⟩ := hp_oracle A hR
  have hO' := oracle_patch O1 O2 h1 hO2
  have hfc := pent_facets A w hw hT
  have hrun' : rayMachineRun program (fun v => if O1 v ∈ frontier (HP A) then O1 v else O2 v) t
      { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c := by
    rw [← hrun]; symm
    apply run_congr program O1 _
    intro s hs c' hc' hq
    rw [if_pos (hagree s hs c' hc' hq)]
  obtain ⟨t', c', n', e', N', S', C', q', hrun2, hhalt2, -, -, -, -, ht1', -, -⟩ :=
    hprog (HP A) (hp_isDPolytope A hR) (hp_zero_interior A) _ hO'
      (le_trans (by norm_num) hfc) (padL A (faceCount (HP A) (2 - 1)))
      (hp_padL A hfc).symm (padL_facets A (pent_rows A w hw hT)) ⟨nf, hnf⟩
  obtain rfl := halted_unique program _ _ c c' t t' hrun' hhalt hrun2 hhalt2
  have hn11 : 11 ≤ n' := pent_faces_equiv A w hw hT n' e'
  have h := ht1' ⟨n, by omega⟩
  simp only [Fin.val_mk] at h
  linarith

theorem eight_lt (Ans : Finset (Fin 2 → ℝ)) (hAc : Ans.card ≤ 7)
    (hc : ∀ a b : ℝ, (a = 1 ∨ a = -1) → (b = 1 ∨ b = -1) → ![a, b] ∈ Ans)
    (p1 p2 p3 p4 : Fin 2 → ℝ) (h1 : p1 ∈ Ans ∧ p1 0 = 1 ∧ |p1 1| < 1)
    (h2 : p2 ∈ Ans ∧ p2 0 = -1 ∧ |p2 1| < 1)
    (h3 : p3 ∈ Ans ∧ p3 1 = 1 ∧ |p3 0| < 1) (h4 : p4 ∈ Ans ∧ p4 1 = -1 ∧ |p4 0| < 1) :
    False := by
  have nb : ∀ x : ℝ, |x| < 1 → x ≠ 1 ∧ x ≠ -1 := by
    intro x hx
    constructor <;> intro h <;> rw [h] at hx <;> norm_num at hx
  obtain ⟨a1, a1'⟩ := nb _ h1.2.2
  obtain ⟨a2, a2'⟩ := nb _ h2.2.2
  obtain ⟨a3, a3'⟩ := nb _ h3.2.2
  obtain ⟨a4, a4'⟩ := nb _ h4.2.2
  let f : Fin 8 → Fin 2 → ℝ := ![![1, 1], ![-1, 1], ![-1, -1], ![1, -1], p1, p2, p3, p4]
  let g : (Fin 2 → ℝ) → Fin 8 := fun p =>
    if p 0 = 1 then (if p 1 = 1 then 0 else if p 1 = -1 then 3 else 4)
    else if p 0 = -1 then (if p 1 = 1 then 1 else if p 1 = -1 then 2 else 5)
    else (if p 1 = 1 then 6 else 7)
  have hgf : ∀ i, g (f i) = i := by
    intro i
    fin_cases i <;> norm_num [f, g, h1.2.1, h2.2.1, h3.2.1, h4.2.1, a1, a1', a2, a2', a3, a3',
      a4, a4'] <;> rfl
  have hinj : Function.Injective f := Function.LeftInverse.injective hgf
  have hsub : Finset.univ.image f ⊆ Ans := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    fin_cases i
    · exact hc 1 1 (Or.inl rfl) (Or.inl rfl)
    · exact hc (-1) 1 (Or.inr rfl) (Or.inl rfl)
    · exact hc (-1) (-1) (Or.inr rfl) (Or.inr rfl)
    · exact hc 1 (-1) (Or.inl rfl) (Or.inr rfl)
    · exact h1.1
    · exact h2.1
    · exact h3.1
    · exact h4.1
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj] at this
  simp at this
  omega

theorem key_contra (program : List RayInstruction) (hprog : HPROG program) : False := by
  have hprog0 := hprog
  unfold HPROG at hprog0
  obtain ⟨O1, hO1⟩ := hp_oracle sqA sq_bound
  obtain ⟨nf, hnf⟩ := hp_faces_finite sqA sq_bound
  haveI : Finite (PolytopeFace (HP sqA)) := Finite.of_equiv _ hnf.some
  obtain ⟨t, c, n, e, N, S, C, q, hrun, hhalt, hC0, hq0, hstep, hcq, -, ht0, -⟩ :=
    hprog0 (HP sqA) (hp_isDPolytope sqA sq_bound) (hp_zero_interior sqA) O1 hO1
      (le_trans (by norm_num) sq_facets) (padL sqA (faceCount (HP sqA) (2 - 1)))
      (hp_padL sqA sq_facets).symm (padL_facets sqA sq_rows) ⟨nf, hnf⟩
  have hfix : ∀ v : Fin 2 → ℝ, (∀ k, v k = 1 ∨ v k = -1) → O1 v = v :=
    corner_fixed O1 (by rw [← hp_sq_eq]; exact hO1)
  have hqN := trace_bound (padL sqA _) (padL_form sqA sqA_form) (HP sqA) O1 hfix N S C q
    hC0 hq0 hstep
  have hn10 : n ≤ 10 := sq_faces_equiv_le n e
  obtain ⟨Qs, hQc, hQne, hQmem⟩ := run_query_set program O1 t _ c hrun
  have hQc' : Qs.card ≤ 7 := by simp at hQc; omega
  set Ans := Qs.image O1 with hAns
  have hAc : Ans.card ≤ 7 := Finset.card_image_le.trans hQc'
  have hAf : ∀ p ∈ Ans, p ∈ frontier (HP sqA) := by
    intro p hp
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hp
    exact (hO1 u (hQne u hu)).1
  have hgoal : ∀ (A : Fin 5 → (Fin 2 → ℝ) →L[ℝ] ℝ) (w : Fin 5 → Fin 2 → ℝ),
      (∀ k, w k ∈ HP A) → (∀ i k, A i (w k) = 1 ↔ (k = i ∨ k + 1 = i)) →
      ∀ R : ℝ, (∀ x ∈ HP A, ∀ k, |x k| ≤ R) → (∀ p ∈ Ans, p ∈ frontier (HP A)) → False := by
    intro A w hw hT R hR hA
    exact pent_contra program hprog A w hw hT hR O1 (fun v hv => (hO1 v hv).2) t c n hn10
      hrun hhalt ht0
      (fun s hs c' hc' hq => hA _ (Finset.mem_image_of_mem O1 (hQmem s hs c' hc' hq)))
  by_cases hA : ∃ a b : ℝ, (a = 1 ∨ a = -1) ∧ (b = 1 ∨ b = -1) ∧ ![a, b] ∉ Ans
  · -- cut the free corner
    obtain ⟨a, b, ha, hb, hv⟩ := hA
    have hlt : ∀ p ∈ Ans, a * p 0 + b * p 1 - 1 < 1 := by
      intro p hp
      by_contra hge
      push_neg at hge
      have hb0 := abs_le.1 ((sq_frontier (hAf p hp)).1 0)
      have hb1 := abs_le.1 ((sq_frontier (hAf p hp)).1 1)
      apply hv
      have hp' : p = ![a, b] := by
        funext k
        fin_cases k <;> simp <;> rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
          linarith
      rw [← hp']; exact hp
    obtain ⟨u, hu0, hu1, hu⟩ := fin_max_lt Ans (fun p => a * p 0 + b * p 1 - 1) hlt
    obtain ⟨t, ht0, ht⟩ : ∃ t : ℝ, 0 < t ∧ t * (1 + u) = 1 :=
      ⟨1 / (1 + u), by positivity, by field_simp⟩
    have hmem : ∀ p ∈ Ans, p ∈ HP (penA (cutC0 a t) (cutC1 b t)) := by
      intro p hp
      show ∀ i, _
      intro i
      have hb0 := abs_le.1 ((sq_frontier (hAf p hp)).1 0)
      have hb1 := abs_le.1 ((sq_frontier (hAf p hp)).1 1)
      have hu' : a * p 0 + b * p 1 - 1 ≤ u := hu p hp
      have key := mul_le_mul_of_nonneg_left (show a * p 0 + b * p 1 ≤ 1 + u by linarith) ht0.le
      rw [penA_apply]
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> fin_cases i <;>
        simp [cutC0, cutC1] <;> nlinarith
    apply hgoal _ (cutW a b u) (cut_mem a b u _ ha hb hu0 hu1 ht0 ht)
      (cut_hT a b u _ ha hb hu0 hu1 ht0 ht) 1 (cut_bound a b _ ha hb)
    intro p hp
    exact frontier_of_sub (hp_closed _)
      (fun x hx => (mem_HP_sq x).2 (cut_bound a b _ ha hb x hx)) (hmem p hp) (hAf p hp)
  push_neg at hA
  by_cases hE : ∃ a : ℝ, (a = 1 ∨ a = -1) ∧ ∀ p ∈ Ans, ¬ (p 0 = a ∧ |p 1| < 1)
  · obtain ⟨a, ha, hE⟩ := hE
    apply hgoal _ (bumpW a) (bump_mem a ha) (bump_hT a ha) 3 (bump_bound a ha)
    intro p hp
    obtain ⟨hbd, hor⟩ := sq_frontier (hAf p hp)
    have hb0 := abs_le.1 (hbd 0)
    have hb1 := abs_le.1 (hbd 1)
    have hpm : p ∈ HP (penA (bumpC0 a) bumpC1) := by
      show ∀ i, _
      intro i
      rw [penA_apply]
      rcases ha with rfl | rfl <;> fin_cases i <;> simp [bumpC0, bumpC1] <;> linarith
    have htight : ∃ i, penA (bumpC0 a) bumpC1 i p = 1 := by
      by_cases h1 : |p 1| = 1
      · rcases (abs_eq zero_le_one).1 h1 with h | h
        · exact ⟨⟨1, by norm_num⟩, by rw [penA_apply]; simp [bumpC0, bumpC1, h] <;> norm_num⟩
        · exact ⟨⟨3, by norm_num⟩, by rw [penA_apply]; simp [bumpC0, bumpC1, h] <;> norm_num⟩
      · have h0 : |p 0| = 1 := hor.resolve_right h1
        have hlt : |p 1| < 1 := lt_of_le_of_ne (hbd 1) h1
        have hne : p 0 ≠ a := fun h => hE p hp ⟨h, hlt⟩
        rcases (abs_eq zero_le_one).1 h0 with h | h <;> rcases ha with rfl | rfl <;>
          first
            | exact absurd h hne
            | exact ⟨⟨2, by norm_num⟩, by rw [penA_apply]; simp [bumpC0, bumpC1, h] <;> norm_num⟩
    obtain ⟨i, hi⟩ := htight
    exact hp_tight_frontier _ hpm hi
  push_neg at hE
  by_cases hES : ∃ b : ℝ, (b = 1 ∨ b = -1) ∧ ∀ p ∈ Ans, ¬ (p 1 = b ∧ |p 0| < 1)
  · obtain ⟨b, hb, hES⟩ := hES
    apply hgoal _ (bumpSW b) (bumpS_mem b hb) (bumpS_hT b hb) 3 (bumpS_bound b hb)
    intro p hp
    obtain ⟨hbd, hor⟩ := sq_frontier (hAf p hp)
    have hb0 := abs_le.1 (hbd 0)
    have hb1 := abs_le.1 (hbd 1)
    have hpm : p ∈ HP (penA bumpSC0 (bumpSC1 b)) := by
      show ∀ i, _
      intro i
      rw [penA_apply]
      rcases hb with rfl | rfl <;> fin_cases i <;> simp [bumpSC0, bumpSC1] <;> linarith
    have htight : ∃ i, penA bumpSC0 (bumpSC1 b) i p = 1 := by
      by_cases h0 : |p 0| = 1
      · rcases (abs_eq zero_le_one).1 h0 with h | h
        · exact ⟨⟨1, by norm_num⟩, by rw [penA_apply]; simp [bumpSC0, bumpSC1, h] <;> norm_num⟩
        · exact ⟨⟨3, by norm_num⟩, by rw [penA_apply]; simp [bumpSC0, bumpSC1, h] <;> norm_num⟩
      · have h1 : |p 1| = 1 := hor.resolve_left h0
        have hlt : |p 0| < 1 := lt_of_le_of_ne (hbd 0) h0
        have hne : p 1 ≠ b := fun h => hES p hp ⟨h, hlt⟩
        rcases (abs_eq zero_le_one).1 h1 with h | h <;> rcases hb with rfl | rfl <;>
          first
            | exact absurd h hne
            | exact ⟨⟨2, by norm_num⟩, by rw [penA_apply]; simp [bumpSC0, bumpSC1, h] <;> norm_num⟩
    obtain ⟨i, hi⟩ := htight
    exact hp_tight_frontier _ hpm hi
  push_neg at hES
  obtain ⟨p1, hp1, e1, l1⟩ := hE 1 (Or.inl rfl)
  obtain ⟨p2, hp2, e2, l2⟩ := hE (-1) (Or.inr rfl)
  obtain ⟨p3, hp3, e3, l3⟩ := hES 1 (Or.inl rfl)
  obtain ⟨p4, hp4, e4, l4⟩ := hES (-1) (Or.inr rfl)
  exact eight_lt Ans hAc hA p1 p2 p3 p4 ⟨hp1, e1, l1⟩ ⟨hp2, e2, l2⟩ ⟨hp3, e3, l3⟩ ⟨hp4, e4, l4⟩

end Assembly

end G81

open Grunbaum2003 in
theorem solution : ¬ (∀ (d : ℕ) (hd : 2 ≤ d)
    (run_add : ∀ (program : List RayInstruction)
      (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
      rayMachineRun program oracle (a + b) c =
        (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
    (relocateInst : ℕ → RayInstruction → RayInstruction)
    (relocateCfg : ℕ → RayConfiguration → RayConfiguration)
    (hRelocate : ∀ (pre program : List RayInstruction)
      (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t : ℕ) (c : RayConfiguration),
      (relocateCfg pre.length c).pc = pre.length + c.pc ∧
      (relocateCfg pre.length c).head = c.head ∧
      (relocateCfg pre.length c).tape = c.tape ∧
      (relocateCfg pre.length c).queries = c.queries ∧
      rayMachineRun (pre ++ program.map (relocateInst pre.length)) oracle t
          (relocateCfg pre.length c) =
        (rayMachineRun program oracle t c).map (relocateCfg pre.length) ∧
      (program[c.pc]? = some .halt →
        (pre ++ program.map (relocateInst pre.length))[
          (relocateCfg pre.length c).pc]? = some .halt))
    (innerSampleProgram : ℕ → List RayInstruction)
    (queryVector : ∀ d : ℕ, ℕ → Fin d → ℝ)
    (hInnerProg : ∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (tape : ℤ → ℝ) (q : ℕ),
      ∃ c : RayConfiguration,
        rayMachineRun (innerSampleProgram d) oracle ((d + 1) * (d + 2) + 2)
          {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
        c.pc = (d + 1) * (d + 2) + 2 ∧
        (innerSampleProgram d)[c.pc]? = some .halt ∧
        c.head = 0 ∧
        c.queries = q + (d + 1) ∧
        (∀ i : Fin (d + 1), ∀ j : Fin d,
          c.tape ((((i.val + 1) * d + j.val : ℕ) : ℤ)) = oracle (queryVector d i.val) j) ∧
        (∀ z : ℤ, (z < (d : ℤ) ∨ (((d + 2) * d : ℕ) : ℤ) ≤ z) → c.tape z = tape z))
    (frameCramerCoefficients : Matrix (Fin d) (Fin d) ℝ → Fin d → ℝ)
    (frameNormal : Matrix (Fin d) (Fin d) ℝ → (Fin d → ℝ) →L[ℝ] ℝ)
    (hFrameNormal : ∀ (v : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ),
      frameNormal v x = ∑ k, frameCramerCoefficients v k * x k)
    (hLocalSlack : ∀ {k : ℕ} (L : Fin k → (Fin d → ℝ) →ₗ[ℝ] ℝ) (p u : Fin d → ℝ),
      (∀ j, L j p < 1) →
      let δ := ∏ j, (1 - L j p) / (1 + (1 - L j p))
      let M := 1 + ∑ j, (L j u) ^ 2
      0 < δ ∧ 0 ≤ M ∧ (∀ j, L j p ≤ 1 - δ) ∧ (∀ j, |L j u| ≤ M))
    (stepEpsProgram : ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℤ → List RayInstruction)
    (stepEpsDest : ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ)
    (stepEpsSteps : ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℕ)
    (hStepEpsProg : ∀ {k : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (rowBase pBase uBase aCell minBase : ℤ) (q : ℕ),
      0 < source aCell →
      (∀ j : Fin k,
        ∑ i : Fin d, source (rowBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
          source (pBase + (i.val : ℤ)) < 1) →
      let prog := stepEpsProgram d k rowBase pBase uBase aCell minBase
      let dst := stepEpsDest d k rowBase pBase uBase aCell minBase
      let steps := stepEpsSteps d k rowBase pBase uBase aCell
      let rowVal (j : Fin k) (xBase : ℤ) : ℝ :=
        ∑ i : Fin d, source (rowBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
          source (xBase + (i.val : ℤ))
      let δ : ℝ := ∏ j : Fin k, (1 - rowVal j pBase) / (1 + (1 - rowVal j pBase))
      let M : ℝ := 1 + ∑ j : Fin k, (rowVal j uBase) ^ 2
      minBase ≤ dst ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
        c'.head = 0 ∧ c'.queries = q ∧
        c'.tape dst = source aCell * δ / (2 * (1 + source aCell * M + δ)) ∧
        ∀ z : ℤ, z < dst → c'.tape z = source z)
    (perturbedRayQueryProgram : ℕ → ℤ → ℤ → ℤ → ℤ → List RayInstruction)
    (perturbedRayQueryDest : ℕ → ℤ → ℤ → ℤ → ℤ → ℤ)
    (perturbedRayQuerySteps : ℕ → ℤ → ℤ → ℤ → ℕ)
    (hPerturbedQueryProg : ∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (pBase uBase epsCell minBase : ℤ) (q : ℕ),
      (fun i : Fin d =>
        source (pBase + (i.val : ℤ)) + source epsCell * source (uBase + (i.val : ℤ))) ≠ 0 →
      let prog := perturbedRayQueryProgram d pBase uBase epsCell minBase
      let outBase := perturbedRayQueryDest d pBase uBase epsCell minBase
      let steps := perturbedRayQuerySteps d pBase uBase epsCell
      minBase ≤ outBase ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
        c'.head = 0 ∧ c'.queries = q + 1 ∧
        (∀ i : Fin d,
          c'.tape (outBase + (i.val : ℤ)) =
            oracle (fun j : Fin d =>
              source (pBase + (j.val : ℤ)) + source epsCell * source (uBase + (j.val : ℤ))) i) ∧
        (∀ z : ℤ, z < outBase → c'.tape z = source z))
    (cramerRowProgram : ℕ → ℤ → ℤ → List RayInstruction)
    (cramerRowDest : ℕ → ℤ → ℤ → ℤ)
    (cramerRowSteps : ℕ → ℤ → ℕ)
    (hCramerProg : ∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (vBase minBase : ℤ) (q : ℕ),
      let v : Matrix (Fin d) (Fin d) ℝ :=
        fun i j => source (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))
      v.det ≠ 0 →
      let prog := cramerRowProgram d vBase minBase
      let outBase := cramerRowDest d vBase minBase
      let steps := cramerRowSteps d vBase
      minBase ≤ outBase ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
        c'.head = 0 ∧ c'.queries = q ∧
        (∀ k : Fin d,
          c'.tape (outBase + (k.val : ℤ)) =
            (v.updateCol k (fun _ => 1)).det / v.det) ∧
        (∀ z : ℤ, z < outBase → c'.tape z = source z))
    (midpointVecProgram : ℕ → ℤ → ℤ → ℤ → List RayInstruction)
    (midpointVecDest : ℕ → ℤ → ℤ → ℤ → ℤ)
    (midpointVecSteps : ℕ → ℤ → ℤ → ℕ)
    (hMidpointProg : ∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (pBase qBase minBase : ℤ) (q : ℕ),
      let prog := midpointVecProgram d pBase qBase minBase
      let outBase := midpointVecDest d pBase qBase minBase
      let steps := midpointVecSteps d pBase qBase
      minBase ≤ outBase ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
        c'.head = 0 ∧ c'.queries = q ∧
        (∀ i : Fin d,
          c'.tape (outBase + (i.val : ℤ)) =
            (source (pBase + (i.val : ℤ)) + source (qBase + (i.val : ℤ))) / 2) ∧
        (∀ z : ℤ, z < outBase → c'.tape z = source z))
    (facetVertexIncidenceMatrixProgram : ℕ → ℕ → ℕ → ℤ → ℤ → ℤ → List RayInstruction)
    (facetVertexIncidenceMatrixDest : ℕ → ℕ → ℕ → ℤ → ℤ → ℤ → ℤ)
    (facetVertexIncidenceMatrixSteps : ℕ → ℕ → ℕ → ℤ → ℤ → ℕ)
    (facetVertexIncidenceMatrixPC : ℕ → ℕ → ℕ → ℤ → ℤ → ℕ)
    (hIncMatrixProg : ∀ {m V : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (lBase xBase minBase : ℤ) (q : ℕ),
      let prog := facetVertexIncidenceMatrixProgram d m V lBase xBase minBase
      let outBase := facetVertexIncidenceMatrixDest d m V lBase xBase minBase
      let steps := facetVertexIncidenceMatrixSteps d m V lBase xBase
      let haltPC := facetVertexIncidenceMatrixPC d m V lBase xBase
      minBase ≤ outBase ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = haltPC ∧ prog[c'.pc]? = some .halt ∧
        c'.head = 0 ∧ c'.queries = q ∧
        (∀ (j : Fin m) (k : Fin V),
          c'.tape (outBase + (j.val : ℤ) * (V : ℤ) + (k.val : ℤ)) =
            if (∑ i : Fin d,
                source (lBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
                  source (xBase + (k.val : ℤ) * (d : ℤ) + (i.val : ℤ))) = 1
            then (1 : ℝ) else 0) ∧
        (∀ z : ℤ, z < outBase → c'.tape z = source z))
    (headerAndInclusionTableProgram : ℕ → ℕ → ℤ → ℤ → List RayInstruction)
    (headerAndInclusionTableDest : ℕ → ℕ → ℤ → ℤ → ℤ)
    (headerAndInclusionTableSteps : ℕ → ℕ → ℤ → ℕ)
    (hTableProg : ∀ {n V : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (fvBase minBase : ℤ) (q : ℕ) (inc : Fin n → Fin V → Prop),
      (∀ (a : Fin n) (k : Fin V),
        source (fvBase + (a.val : ℤ) * (V : ℤ) + (k.val : ℤ)) =
          if inc a k then (1 : ℝ) else 0) →
      let prog := headerAndInclusionTableProgram n V fvBase minBase
      let outBase := headerAndInclusionTableDest n V fvBase minBase
      let steps := headerAndInclusionTableSteps n V fvBase
      minBase ≤ outBase ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
        c'.head = outBase ∧ c'.queries = q ∧
        (∀ i : Fin n, c'.tape (c'.head + (i.val : ℤ)) = 1) ∧
        c'.tape (c'.head + (n : ℤ)) = 0 ∧
        (∀ i j : Fin n,
          c'.tape (c'.head + ((n + 1 + i.val * n + j.val : ℕ) : ℤ)) =
            if (∀ k : Fin V, inc i k → inc j k) then (1 : ℝ) else 0) ∧
        (∀ z : ℤ, z < c'.head → c'.tape z = source z))
    (secondQueryProgram firstMidpointProgram referenceWalkProgram : List RayInstruction),
    ∃ program : List RayInstruction,
      ∀ P : Set (Fin d → ℝ), IsDPolytope P → (0 : Fin d → ℝ) ∈ interior P →
        ∀ oracle : (Fin d → ℝ) → (Fin d → ℝ), IsPolytopeRayOracle P oracle →
          d + 1 ≤ faceCount P (d - 1) →
          ∀ (L : Fin (faceCount P (d - 1)) → (Fin d → ℝ) →L[ℝ] ℝ),
            P = {x | ∀ i, L i x ≤ 1} →
            (∀ i, L i = 0 ∨
              ({x ∈ P | L i x = 1}.Nonempty ∧ IsExposed ℝ P {x ∈ P | L i x = 1} ∧
                Module.finrank ℝ (affineSpan ℝ {x ∈ P | L i x = 1}).direction = d - 1)) →
            (∃ n : ℕ, Nonempty (Fin n ≃ PolytopeFace P)) →
            ∃ (t : ℕ) (c : RayConfiguration) (n : ℕ) (e : Fin n ≃ PolytopeFace P)
              (N : ℕ)
              (S_seq : ℕ → Finset (Fin (faceCount P (d - 1))))
              (C_seq : ℕ → Finset (Fin d → ℝ))
              (q_seq : ℕ → ℕ),
              rayMachineRun program oracle t
                { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
              program[c.pc]? = some .halt ∧
              C_seq 0 = ∅ ∧
              q_seq 0 ≤ d + 1 ∧
              (∀ s < N,
                (S_seq (s + 1) = S_seq s ∧
                  ∃ v ∈ ({x : Fin d → ℝ | ∀ i ∈ S_seq s, L i x ≤ 1}).extremePoints ℝ,
                    v ∈ P ∧ v ∉ C_seq s ∧ C_seq (s + 1) = insert v (C_seq s) ∧
                    q_seq (s + 1) ≤ q_seq s + 1) ∨
                (C_seq (s + 1) = C_seq s ∧
                  ∃ v ∈ ({x : Fin d → ℝ | ∀ i ∈ S_seq s, L i x ≤ 1}).extremePoints ℝ,
                    oracle v ≠ v ∧
                    ∃ i_new : Fin (faceCount P (d - 1)),
                      L i_new (oracle v) = 1 ∧
                      S_seq (s + 1) = insert i_new (S_seq s) ∧
                      q_seq (s + 1) ≤ q_seq s +
                        (1 + (d - 1) * (2 * (faceCount P (d - 1) - (S_seq s).card) + 3)))) ∧
              c.queries ≤ q_seq N ∧
              (∀ i : Fin n, c.tape (c.head + (i.val : ℤ)) = 1) ∧
              c.tape (c.head + (n : ℤ)) = 0 ∧
              ∀ i j : Fin n,
                c.tape (c.head + ((n + 1 + i.val * n + j.val : ℕ) : ℤ)) =
                  if (∀ x : Fin d → ℝ, IsExposed ℝ P {x} → x ∈ (e i).val → x ∈ (e j).val)
                  then 1 else 0) := by
  intro H
  obtain ⟨program, hprog⟩ := H 2 le_rfl (G81.run_add' (d := 2)) G81.relocI G81.relocC G81.relocW
    G81.innerSampleW G81.queryVectorW G81.innerW_spec (fun _ _ => 0) (fun _ => 0)
    (by intro v x; simp) G81.localSlackW
    (fun _ k => G81.stepProg k) (fun _ k => G81.stepDest k) (fun _ k _ _ _ _ => 12 * k + 10)
    G81.stepW_spec
    (fun _ => G81.pertProg) (fun _ => G81.pertDest) (fun _ _ _ _ => 7) G81.pertW_spec
    (fun _ => G81.cramProg) (fun _ => G81.cramDest) (fun _ _ => 7) G81.cramW_spec
    (fun _ => G81.midProg) (fun _ => G81.midDest) (fun _ _ _ => 5) G81.midW_spec
    (fun _ m V => G81.incProg m V) (fun _ m V => G81.incDest m V)
    (fun _ m V _ _ => 1 + 6 * (m * V)) (fun _ m V _ _ => 1 + 7 * (m * V)) G81.incW_spec
    G81.tabProg G81.tabDest G81.tabSteps G81.tabW_spec [] [] []
  exact G81.key_contra program hprog
