-- Prove2me | solution 1 for MemoryConsistency.first_next_write_pointers_certify_last_writes
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T19:12:27.415931+00:00
-- url     : https://prove2.me/submissions/1f5c5afa-dbd9-44b3-be32-f06396f52f78

import Mathlib

set_option autoImplicit false

namespace PvsNP.LocalMemoryLinks

variable {Addr : Type}

/-- Active records are stores. Every record, including a store, reads
the previous value at its own address. -/
def WritesAt (address : ℕ → Addr) (active : ℕ → Bool) (cell : Addr) (i : ℕ) : Prop :=
  active i = true ∧ address i = cell

def Immediate (address : ℕ → Addr) (active : ℕ → Bool) (t : ℕ) : Option ℕ → Prop
  | none => ∀ r < t, ¬ WritesAt address active (address t) r
  | some s => s < t ∧ WritesAt address active (address t) s ∧
    ∀ r, s < r → r < t → ¬ WritesAt address active (address t) r

theorem Immediate.unique {address : ℕ → Addr} {active : ℕ → Bool} {t : ℕ}
    {a b : Option ℕ} (ha : Immediate address active t a)
    (hb : Immediate address active t b) : a = b := by
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some s => exact (ha s hb.1 hb.2.1).elim
  | some s =>
    cases b with
    | none => exact (hb s ha.1 ha.2.1).elim
    | some r =>
      rcases lt_trichotomy s r with before | equal | after
      · exact (ha.2.2 r before hb.1 hb.2.1).elim
      · rw [equal]
      · exact (hb.2.2 s after ha.1 ha.2.1).elim

def NotBefore (t : ℕ) : Option ℕ → Prop
  | none => True
  | some i => t ≤ i

/-- Check every row against the two pointers of its write interval.
At an active row, the root or the preceding store must also point to
the current row. The upper bound includes the time of the current
row, since reads within a store see the pre-store value. -/
def Local (address : ℕ → Addr) (active : ℕ → Bool)
    (previous next : ℕ → Option ℕ) (root : Addr → Option ℕ) (horizon : ℕ) : Prop :=
  ∀ t < horizon, match previous t with
  | none => NotBefore t (root (address t)) ∧ (active t = true → root (address t) = some t)
  | some s => s < t ∧ WritesAt address active (address t) s ∧
      NotBefore t (next s) ∧ (active t = true → next s = some t)

/-- At any query row, the address root lies before the row exactly when
some store does. This comparison remains valid for unconstrained roots
of addresses with no writes. -/
theorem root_notBefore_iff_no_prior {address : ℕ → Addr} {active : ℕ → Bool}
    {previous next : ℕ → Option ℕ} {root : Addr → Option ℕ} {horizon : ℕ}
    (links : Local address active previous next root horizon) (t : ℕ)
    (inside : t < horizon) :
    NotBefore t (root (address t)) ↔ ∀ r < t, ¬ WritesAt address active (address t) r := by
  classical
  constructor
  · intro rootLater u before writes
    have earlier : ∃ r < t, WritesAt address active (address t) r := ⟨u,before,writes⟩
    let first := Nat.find earlier
    have hf : first < t ∧ WritesAt address active (address t) first := Nat.find_spec earlier
    have atFirst := links first (hf.1.trans inside)
    cases firstPrev : previous first with
    | none =>
      rw [firstPrev] at atFirst
      have forced : root (address t) = some first := by
        have forced := atFirst.2 hf.2.1
        rwa [hf.2.2] at forced
      rw [forced] at rootLater
      exact Nat.not_le_of_lt hf.1 rootLater
    | some s =>
      rw [firstPrev] at atFirst
      have noEarlier : first ≤ s := Nat.find_min' earlier
        ⟨atFirst.1.trans hf.1,atFirst.2.1.1,atFirst.2.1.2.trans hf.2.2⟩
      omega
  · intro no
    have now := links t inside
    cases current : previous t with
    | none => rw [current] at now; exact now.1
    | some s => rw [current] at now; exact (no s now.1 now.2.1).elim

/-- Every read receives its genuine previous writer. Each local
obligation uses only the current row, a claimed predecessor and a
root or forward lookup. -/
theorem immediate_of_local {address : ℕ → Addr} {active : ℕ → Bool}
    {previous next : ℕ → Option ℕ} {root : Addr → Option ℕ} {horizon : ℕ}
    (links : Local address active previous next root horizon) :
    ∀ t < horizon, Immediate address active t (previous t) := by
  classical
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro inside
    have now := links t inside
    cases atTime : previous t with
    | none =>
      rw [atTime] at now
      exact (root_notBefore_iff_no_prior links t inside).mp now.1
    | some s =>
      rw [atTime] at now
      refine ⟨now.1,now.2.1,fun u lower upper writes => ?_⟩
      have gap : ∃ r, s < r ∧ r < t ∧ WritesAt address active (address t) r :=
        ⟨u,lower,upper,writes⟩
      let nearest := Nat.find gap
      have info : s < nearest ∧ nearest < t ∧ WritesAt address active (address t) nearest :=
        Nat.find_spec gap
      have asPrev : Immediate address active nearest (some s) := by
        refine ⟨info.1,⟨now.2.1.1,now.2.1.2.trans info.2.2.2.symm⟩,fun r low high store => ?_⟩
        have nearLe : nearest ≤ r := Nat.find_min' gap
          ⟨low,high.trans info.2.1,store.1,store.2.trans info.2.2.2⟩
        omega
      have determined := (ih nearest info.2.1 (info.2.1.trans inside)).unique asPrev
      have atNearest := links nearest (info.2.1.trans inside)
      rw [determined] at atNearest
      have impossible := now.2.2.1
      rw [atNearest.2.2.2 info.2.2.1] at impossible
      exact Nat.not_le_of_lt info.2.1 impossible

open Classical in
private noncomputable def firstHit (p : ℕ → Prop) : Option ℕ :=
  if h : ∃ i, p i then some (Nat.find h) else none

private theorem firstHit_notBefore (p : ℕ → Prop) (t : ℕ) (h : ∀ r < t, ¬ p r) :
    NotBefore t (firstHit p) := by
  classical
  unfold firstHit
  split_ifs with has
  · change t ≤ Nat.find has
    by_contra! earlier
    exact h _ earlier (Nat.find_spec has)
  · trivial

private theorem firstHit_eq (p : ℕ → Prop) (t : ℕ) (h : ∀ r < t, ¬ p r)
    (yes : p t) : firstHit p = some t := by
  classical
  have has : ∃ r, p r := ⟨t,yes⟩
  have lower := firstHit_notBefore p t h
  unfold firstHit at lower ⊢
  rw [dif_pos has] at lower ⊢
  exact congrArg some (Nat.le_antisymm (Nat.find_min' has yes) lower)

/-- The exact first and next store positions supply a complete choice of
the additional pointers whenever the previous-writer table is correct. -/
theorem local_completion {address : ℕ → Addr} {active : ℕ → Bool}
    {previous : ℕ → Option ℕ} {horizon : ℕ}
    (back : ∀ t < horizon, Immediate address active t (previous t)) :
    ∃ next : ℕ → Option ℕ, ∃ root : Addr → Option ℕ,
      Local address active previous next root horizon := by
  let root (a : Addr) := firstHit (fun r => r < horizon ∧ WritesAt address active a r)
  let next (s : ℕ) := firstHit (fun r => s < r ∧ r < horizon ∧ WritesAt address active (address s) r)
  refine ⟨next,root,fun t inside => ?_⟩
  have h := back t inside
  cases atTime : previous t with
  | none =>
    rw [atTime] at h
    have no : ∀ r < t, ¬ (r < horizon ∧ WritesAt address active (address t) r) :=
      fun r early hit => h r early hit.2
    exact ⟨firstHit_notBefore _ _ no,fun written => firstHit_eq _ _ no ⟨inside,written,rfl⟩⟩
  | some s =>
    rw [atTime] at h
    have no : ∀ r < t, ¬ (s < r ∧ r < horizon ∧ WritesAt address active (address s) r) :=
      fun r early hit => h.2.2 r hit.1 early ⟨hit.2.2.1,hit.2.2.2.trans h.2.1.2⟩
    exact ⟨h.1,h.2.1,firstHit_notBefore _ _ no,fun written =>
      firstHit_eq _ _ no ⟨h.1,inside,written,h.2.1.2.symm⟩⟩

theorem local_iff_immediate {address : ℕ → Addr} {active : ℕ → Bool}
    {previous : ℕ → Option ℕ} {horizon : ℕ} :
    (∃ next : ℕ → Option ℕ, ∃ root : Addr → Option ℕ,
      Local address active previous next root horizon) ↔
      ∀ t < horizon, Immediate address active t (previous t) :=
  ⟨fun ⟨_,_,links⟩ => immediate_of_local links,local_completion⟩

end PvsNP.LocalMemoryLinks


theorem solution
    {A : Type} (address : ℕ → A) (stores : ℕ → Bool) (previous : ℕ → Option ℕ) (H : ℕ) :
    let writesAt (a : A) (i : ℕ) := stores i = true ∧ address i = a
    let notBefore (t : ℕ) (p : Option ℕ) : Prop :=
      match p with
      | none => True
      | some r => t ≤ r
    (∃ next : ℕ → Option ℕ, ∃ first : A → Option ℕ, ∀ t < H,
      match previous t with
      | none => notBefore t (first (address t)) ∧
          (stores t = true → first (address t) = some t)
      | some s => s < t ∧ writesAt (address t) s ∧ notBefore t (next s) ∧
          (stores t = true → next s = some t)) ↔
    ∀ t < H, match previous t with
    | none => ∀ r < t, ¬ writesAt (address t) r
    | some s => s < t ∧ writesAt (address t) s ∧
        ∀ r, s < r → r < t → ¬ writesAt (address t) r := by
  exact PvsNP.LocalMemoryLinks.local_iff_immediate

#print axioms solution
