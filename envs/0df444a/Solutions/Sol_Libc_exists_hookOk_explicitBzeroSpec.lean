-- Prove2me | solution 1 for Libc.exists_hookOk_explicitBzeroSpec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-24T17:27:33.252085+00:00
-- url     : https://prove2.me/submissions/ce1e879b-92ed-4124-994b-9d4ebfd2ff8d

import Definitions.Def_Libc_ExplicitBzero

/-! Non-vacuity of `Libc.explicitBzeroSpec`: a hook that writes `x1` zero bytes at `x0` and
returns to `x30` meets the contract. Self-contained against the published bundles (the upstream
version in `exists_hookOk_explicitBzeroSpec.upstream.lean` uses DeepMind's ProofLib). -/

open Arm64

namespace Libc.BzeroHook

/-! ## Single-byte writes -/

theorem read8_write8 (m : Memory) (a x : BitVec 64) (v : BitVec 8) :
    (m.write8 a v).read8 x = if x = a then v else m.read8 x := by
  unfold Memory.read8 Memory.write8
  by_cases h : x = a <;> simp [h]

theorem perm_write8 (m : Memory) (a x : BitVec 64) (v : BitVec 8) :
    (m.write8 a v).perm x = m.perm x := by
  unfold Memory.perm Memory.write8 Memory.rawPerm
  by_cases h : x = a
  · subst h
    cases hc : m.cells x with
    | none => simp
    | some c =>
      obtain ⟨p, b⟩ := c
      cases p <;> simp [Perm.rwx]
  · simp [h]

theorem isLazyFree_write8 (m : Memory) (a x : BitVec 64) (v : BitVec 8) :
    (m.write8 a v).isLazyFree x = if x = a then false else m.isLazyFree x := by
  unfold Memory.isLazyFree Memory.write8 Memory.rawPerm
  by_cases h : x = a
  · subst h
    cases hc : m.cells x with
    | none => simp
    | some c =>
      obtain ⟨p, b⟩ := c
      cases p <;> simp
  · simp [h]

theorem isAnon_write8 (m : Memory) (a x : BitVec 64) (v : BitVec 8) :
    (m.write8 a v).isAnon x = m.isAnon x := by
  unfold Memory.isAnon Memory.write8 Memory.rawPerm
  by_cases h : x = a
  · subst h
    cases hc : m.cells x with
    | none => simp
    | some c =>
      obtain ⟨p, b⟩ := c
      cases p <;> simp
  · simp [h]

/-! ## Writing `n` zero bytes -/

theorem inRegion_succ (a x : BitVec 64) (n : Nat) :
    InRegion a (n + 1) x ↔ x = a ∨ InRegion (a + 1#64) n x := by
  unfold InRegion
  bv_omega

theorem zeros_read8 (n : Nat) : ∀ (m : Memory) (a x : BitVec 64),
    (m.writeBytes a (List.replicate n 0#8)).read8 x = if InRegion a n x then 0#8 else m.read8 x := by
  induction n with
  | zero => intro m a x; simp [Memory.writeBytes, InRegion]
  | succ n ih =>
    intro m a x
    rw [List.replicate_succ, Memory.writeBytes, ih, read8_write8]
    by_cases h1 : InRegion (a + 1#64) n x
    · simp [h1, (inRegion_succ a x n).2 (Or.inr h1)]
    · by_cases h2 : x = a
      · simp [h2, (inRegion_succ a a n).2 (Or.inl rfl)]
      · have h3 : ¬ InRegion a (n + 1) x := fun h => by
          rcases (inRegion_succ a x n).1 h with h | h
          · exact h2 h
          · exact h1 h
        simp [h1, h2, h3]

theorem zeros_perm (n : Nat) : ∀ (m : Memory) (a x : BitVec 64),
    (m.writeBytes a (List.replicate n 0#8)).perm x = m.perm x := by
  induction n with
  | zero => intro m a x; rfl
  | succ n ih =>
    intro m a x
    rw [List.replicate_succ, Memory.writeBytes, ih, perm_write8]

theorem zeros_isAnon (n : Nat) : ∀ (m : Memory) (a x : BitVec 64),
    (m.writeBytes a (List.replicate n 0#8)).isAnon x = m.isAnon x := by
  induction n with
  | zero => intro m a x; rfl
  | succ n ih =>
    intro m a x
    rw [List.replicate_succ, Memory.writeBytes, ih, isAnon_write8]

theorem zeros_isLazyFree (n : Nat) : ∀ (m : Memory) (a x : BitVec 64),
    (m.writeBytes a (List.replicate n 0#8)).isLazyFree x =
      if InRegion a n x then false else m.isLazyFree x := by
  induction n with
  | zero => intro m a x; simp [Memory.writeBytes, InRegion]
  | succ n ih =>
    intro m a x
    rw [List.replicate_succ, Memory.writeBytes, ih, isLazyFree_write8]
    by_cases h1 : InRegion (a + 1#64) n x
    · simp [h1, (inRegion_succ a x n).2 (Or.inr h1)]
    · by_cases h2 : x = a
      · simp [h2, (inRegion_succ a a n).2 (Or.inl rfl)]
      · have h3 : ¬ InRegion a (n + 1) x := fun h => by
          rcases (inRegion_succ a x n).1 h with h | h
          · exact h2 h
          · exact h1 h
        simp [h1, h2, h3]

/-! ## Heaps -/

/-- The heap owning `[a, a + n)` read-write with every byte zero. -/
def zHeap (a : BitVec 64) (n : Nat) : Heap :=
  { phys := fun x => if InRegion a n x then some (.rw 0#8) else none }

theorem empty_union (h : Heap) : Heap.empty.union h = h := rfl

theorem zHeap_holds (n : Nat) : ∀ (a : BitVec 64), n ≤ 2 ^ 64 →
    (pointsToBytes a (List.replicate n 0#8)).holds (zHeap a n) := by
  induction n with
  | zero =>
    intro a _
    show zHeap a 0 = Heap.empty
    unfold zHeap Heap.empty
    congr
  | succ n ih =>
    intro a hn
    refine ⟨Heap.singleton a 0#8, zHeap (a + 1#64) n, ?_, ?_, rfl, ih (a + 1#64) (by omega)⟩
    · have ha : ¬ InRegion (a + 1#64) n a := by
        unfold InRegion
        bv_omega
      refine ⟨fun x => ?_, fun _ _ => Or.inl rfl, fun _ _ => Or.inl rfl, ?_, fun _ => Or.inl rfl⟩
      · by_cases hx : x = a
        · subst hx
          exact Or.inr (Or.inl (by simp [zHeap, ha]))
        · exact Or.inl (by simp [Heap.singleton, hx])
      · intro γ k oa v h
        rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> cases h
    · unfold zHeap Heap.singleton Heap.union
      congr
      funext x
      by_cases hx : x = a
      · subst hx
        simp [(inRegion_succ x x n).2 (Or.inl rfl)]
      · by_cases h1 : InRegion (a + 1#64) n x
        · simp [hx, h1, (inRegion_succ a x n).2 (Or.inr h1)]
        · have h3 : ¬ InRegion a (n + 1) x := fun h => by
            rcases (inRegion_succ a x n).1 h with h | h
            · exact hx h
            · exact h1 h
          simp [hx, h1, h3]

/-- `h'` is `h` with the values of some read-write cells changed. -/
def Rew (h h' : Heap) : Prop :=
  (∀ a, h'.phys a = h.phys a ∨
    ∃ b b', h.phys a = some (.rw b) ∧ h'.phys a = some (.rw b')) ∧
  h'.auth = h.auth ∧ h'.frag = h.frag ∧ h'.mapped = h.mapped

theorem Rew.disjoint {h h' g : Heap} (r : Rew h h') (d : h.Disjoint g) : h'.Disjoint g := by
  obtain ⟨r1, ra, rf, rm⟩ := r
  obtain ⟨d1, d2, d3, d4, d5⟩ := d
  refine ⟨fun a => ?_, ?_, ?_, ?_, ?_⟩
  · rcases r1 a with e | ⟨b, b', e1, e2⟩
    · rw [e]; exact d1 a
    · rcases d1 a with h0 | h0 | ⟨c, c1, _⟩
      · rw [e1] at h0; cases h0
      · exact Or.inr (Or.inl h0)
      · rw [e1] at c1; cases c1
  · rw [ra]; exact d2
  · rw [rf]; exact d3
  · rw [ra, rf]; exact d4
  · rw [rm]; exact d5

theorem Rew.union_left {h h' : Heap} (g : Heap) (r : Rew h h') : Rew (h.union g) (h'.union g) := by
  obtain ⟨r1, ra, rf, rm⟩ := r
  refine ⟨fun a => ?_, ?_, ?_, ?_⟩
  · rcases r1 a with e | ⟨b, b', e1, e2⟩
    · left; simp only [Heap.union, e]
    · right; exact ⟨b, b', by simp [Heap.union, e1], by simp [Heap.union, e2]⟩
  · simp only [Heap.union, ra]
  · simp only [Heap.union, rf]
  · simp only [Heap.union, rm]

theorem matches_zeros {H H' : Heap} {m : Memory} {p : BitVec 64} {n : Nat}
    (hM : H.Matches m) (r : Rew H H')
    (hin : ∀ a, InRegion p n a → H'.phys a = some (.rw 0#8) ∧ ∃ b, H.phys a = some (.rw b))
    (hout : ∀ a, ¬ InRegion p n a → H'.phys a = H.phys a) :
    H'.Matches (m.writeBytes p (List.replicate n 0#8)) := by
  obtain ⟨_, ra, rf, rm⟩ := r
  obtain ⟨hM1, ⟨B, hB⟩, hM3⟩ := hM
  refine ⟨fun a c hc => ?_, ⟨B, fun γ hγ k => by rw [ra, rf]; exact hB γ hγ k⟩, fun a ha => ?_⟩
  · by_cases h : InRegion p n a
    · obtain ⟨h1, b, h2⟩ := hin a h
      rw [h1] at hc
      cases hc
      have := hM1 a _ h2
      simp only at this
      simp [zeros_read8, zeros_perm, zeros_isLazyFree, h, this.2.1]
    · rw [hout a h] at hc
      have := hM1 a c hc
      cases c <;> simpa [zeros_read8, zeros_perm, zeros_isLazyFree, h] using this
  · rw [rm] at ha
    rw [zeros_perm, zeros_isAnon]
    exact hM3 a ha

/-! ## The hook -/

/-- Writes `x1` zero bytes at `x0` and returns to `x30`. -/
def hookBzero (s : State) : State :=
  (s.setMem (s.mem.writeBytes (s.readReg64 .x0)
    (List.replicate (s.readReg64 .x1).toNat 0#8))).setPC (s.readReg64 .lr)

theorem hookBzero_ok : HookOk hookBzero explicitBzeroSpec := by
  rintro ⟨p, n⟩ R s0 hrun ⟨H, hH, hM⟩ _
  obtain ⟨H1, hR, d1, rfl, ⟨hP, H2, -, rfl, ⟨rfl, hx0, hx1⟩,
    ⟨hReg, hS, d2, rfl, ⟨mm, rfl⟩, ⟨mS, hSh⟩⟩⟩, hRh⟩ := hH
  rw [empty_union] at d1 hM
  have hS_eq : hS = regionHeap (s0.sp - BitVec.ofNat 64 VerifiedLibraries.Musl.externStack)
      VerifiedLibraries.Musl.externStack mS := hSh
  -- the region is shorter than the address space: it is disjoint from the 4096-byte stack area
  have hn : n < 2 ^ 64 := by
    refine Nat.lt_of_not_le fun hle => ?_
    have hin : InRegion p n (s0.sp - BitVec.ofNat 64 VerifiedLibraries.Musl.externStack) := by
      unfold InRegion
      exact Nat.lt_of_lt_of_le (BitVec.isLt _) hle
    rcases d2.1 (s0.sp - BitVec.ofNat 64 VerifiedLibraries.Musl.externStack) with h | h | ⟨c, h, _⟩
    · simp [regionHeap, hin] at h
    · simp [hS_eq, regionHeap, InRegion, VerifiedLibraries.Musl.externStack] at h
    · simp [regionHeap, hin] at h
  have r0 : Rew (regionHeap p n mm) (zHeap p n) := by
    refine ⟨fun a => ?_, rfl, rfl, rfl⟩
    by_cases h : InRegion p n a
    · exact Or.inr ⟨mm.read8 a, 0#8, by simp [regionHeap, h], by simp [zHeap, h]⟩
    · left; simp [regionHeap, zHeap, h]
  have r1 := Rew.union_left hS r0
  have r2 := Rew.union_left hR r1
  have hmem : (hookBzero s0).mem = s0.mem.writeBytes p (List.replicate n 0#8) := by
    simp only [hookBzero, hx0, hx1]; rfl
  refine ⟨?_, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl⟩, ?_⟩⟩
  · intro a hfr
    rw [hmem]
    have hout : ¬ InRegion p n a := by
      intro h
      have := hM.1 a (.rw (mm.read8 a)) (by simp [Heap.union, regionHeap, h])
      simp only at this
      simp [Memory.Frozen, this.2.1, Perm.rw, Perm.frozen] at hfr
    simp [zeros_read8, zeros_perm, zeros_isLazyFree, zeros_isAnon, hout]
  · rw [hmem]
    refine ⟨((zHeap p n).union hS).union hR,
      ⟨(zHeap p n).union hS, hR, r1.disjoint d1, rfl,
        ⟨zHeap p n, hS, r0.disjoint d2, rfl, zHeap_holds n p (Nat.le_of_lt hn), ⟨mS, hSh⟩⟩, hRh⟩,
      matches_zeros hM r2 (fun a h => ⟨by simp [Heap.union, zHeap, h],
        mm.read8 a, by simp [Heap.union, regionHeap, h]⟩) (fun a h => by
          simp [Heap.union, zHeap, regionHeap, h])⟩

end Libc.BzeroHook

open Libc.BzeroHook in
theorem solution :
    ∃ f : State → State, HookOk f Libc.explicitBzeroSpec :=
  ⟨hookBzero, hookBzero_ok⟩
