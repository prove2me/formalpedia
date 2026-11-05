-- Prove2me | solution 1 for OAI.ThreeMachine.main_theorem
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T07:01:53.213477+00:00
-- url     : https://prove2.me/submissions/f7325864-e6a0-41a0-a3df-5584be298cc1

import Mathlib
import Definitions.Def_ThreeMachine
import Definitions.Def_OAIThreeMachineSched02
import Theorems.Thm_OAI_ThreeMachine_StackCompiler_requestRawBound_length

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.all false
set_option Elab.async false


section
-- module SeparatorWalk
namespace OAI

section

namespace ThreeMachine
namespace Structure

theorem ofFn_lt_of_first_difference {n : ℕ} (f g : Fin n → ℕ)
    (i : Fin n) (hbefore : ∀ j, j < i → f j = g j) (hi : f i < g i) :
    List.ofFn f < List.ofFn g := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    by_cases h0 : i.val = 0
    · have e : i = 0 := Fin.ext h0
      exact List.Lex.rel (by simpa [e] using hi)
    · let j : Fin n := ⟨i.val - 1, by omega⟩
      have ei : j.succ = i := Fin.ext (by dsimp [j]; omega)
      have he : f 0 = g 0 := hbefore 0 (by change 0 < i.val; omega)
      rw [he]
      apply List.Lex.cons
      apply ih (fun k => f k.succ) (fun k => g k.succ) j
      · intro k hk
        apply hbefore k.succ
        rw [← ei]
        exact Fin.succ_lt_succ_iff.mpr hk
      · simpa [ei] using hi

theorem exchange_time_other {J : Type} [Fintype J] [DecidableEq J]
    (p : Layout J) (x y z : J) (hx : z ≠ x) (hy : z ≠ y) :
    (p.exchange x y).time z = p.time z := by
  simp [Layout.time, Layout.exchange, Equiv.swap_apply_of_ne_of_ne hx hy]

theorem respects_exchange {J : Type} [Fintype J] [DecidableEq J]
    {p : Layout J} {r : J → J → Prop} (hp : p.Respects r)
    (x y : J) (hxy : p.time y < p.time x)
    (hpred : ∀ u, r u x → p.time u < p.time y)
    (hsucc : ∀ v, r y v → p.time x < p.time v) :
    (p.exchange x y).Respects r := by
  intro u v huv
  have htime := hp u v huv
  by_cases hux : u = x
  · subst u
    by_cases hvx : v = x
    · subst v
      omega
    by_cases hvy : v = y
    · subst v
      simp only [exchange_time_left, exchange_time_right]
      exact hxy
    rw [exchange_time_left, exchange_time_other p x y v hvx hvy]
    exact hxy.trans htime
  by_cases huy : u = y
  · subst u
    have hav := hsucc v huv
    by_cases hvx : v = x
    · subst v
      omega
    by_cases hvy : v = y
    · subst v
      omega
    rw [exchange_time_right, exchange_time_other p x y v hvx hvy]
    exact hav
  rw [exchange_time_other p x y u hux huy]
  by_cases hvx : v = x
  · subst v
    rw [exchange_time_left]
    exact hpred u huv
  by_cases hvy : v = y
  · subst v
    rw [exchange_time_right]
    exact htime.trans hxy
  rw [exchange_time_other p x y v hvx hvy]
  exact htime

end Structure
end ThreeMachine

namespace ThreeMachine.Structure

section Walk
variable {J : Type}

theorem exists_exception {W : Finset J} {r : J → J → Prop} {time : J → ℕ}
    {S : Set J} {s : ℕ} (h : ¬LaterLow W r time S s) :
    ∃ x, Exception W r time S s x := by
  classical
  let candidates := W.filter (fun x => s < time x ∧ x ∈ S ∧ x ∉ DescAt r time s)
  have hne : candidates.Nonempty := by
    simp only [LaterLow, not_forall] at h
    obtain ⟨x, hw, ht, hS, hD⟩ := h
    exact ⟨x, by simp [candidates, hw, ht, hS, hD]⟩
  obtain ⟨x, hx, hmin⟩ := candidates.exists_min_image time hne
  have hx' : x ∈ W ∧ s < time x ∧ x ∈ S ∧ x ∉ DescAt r time s := by
    simpa [candidates] using hx
  refine ⟨x, hx'.1, hx'.2.2.1, hx'.2.1, hx'.2.2.2, ?_⟩
  intro y hy hlow hsy hyx
  by_contra hnd
  have hmem : y ∈ candidates := by simp [candidates, hy, hsy, hlow, hnd]
  have := hmin y hmem
  omega

theorem exception_ready {W : Finset J} {r : J → J → Prop} {time : J → ℕ}
    {S : Set J} {s : ℕ} {x : J}
    (htrans : ∀ ⦃a b c⦄, r a b → r b c → r a c) (hrespect : ∀ u v, r u v → time u < time v)
    (hideal : IdealOn W r S) (hx : Exception W r time S s x) :
    ∀ u ∈ W, r u x → time u < s := by
  intro u hu hux
  have huxTime := hrespect u x hux
  have huLow := hideal u hu x hx.mem hux hx.low
  by_contra hn
  have hsu : s ≤ time u := by omega
  rcases hsu.eq_or_lt with heq | hlt
  · exact hx.not_desc ⟨u, heq.symm, hux⟩
  · obtain ⟨y, hy, hyu⟩ := hx.earliest u hu huLow hlt huxTime
    exact hx.not_desc ⟨y, hy, htrans hyu hux⟩

theorem trace_to_slot {W : Finset J} {r : J → J → Prop} {time : J → ℕ}
    {S : Set J} {s t : ℕ}
    (htrans : ∀ ⦃a b c⦄, r a b → r b c → r a c) (hrespect : ∀ u v, r u v → time u < time v)
    (hideal : IdealOn W r S)
    (hforce : ∀ y ∈ W, y ∉ S → s ≤ time y → time y < t →
      ∃ z ∈ W, r y z ∧ time z ≤ t)
    (y : J) (hy : y ∈ W) (hyHigh : y ∉ S) (hsy : s ≤ time y)
    (hyt : time y ≤ t) :
    ∃ z ∈ W, time z = t ∧ (y = z ∨ r y z) ∧ z ∉ S := by
  classical
  let candidates := W.filter (fun z => (y = z ∨ r y z) ∧ time z ≤ t)
  have hne : candidates.Nonempty := ⟨y, by simp [candidates, hy, hyt]⟩
  obtain ⟨z, hz, hmax⟩ := candidates.exists_max_image time hne
  have hz' : z ∈ W ∧ (y = z ∨ r y z) ∧ time z ≤ t := by
    simpa [candidates] using hz
  have hzHigh : z ∉ S := by
    intro hlow
    rcases hz'.2.1 with e | hrel
    · exact hyHigh (e ▸ hlow)
    · exact hyHigh (hideal y hy z hz'.1 hrel hlow)
  have hsz : s ≤ time z := by
    rcases hz'.2.1 with e | hrel
    · simpa [← e] using hsy
    · exact hsy.trans (hrespect y z hrel).le
  have hzt : time z = t := by
    by_contra hn
    have hlt : time z < t := by omega
    obtain ⟨v, hv, hzv, hvt⟩ := hforce z hz'.1 hzHigh hsz hlt
    have hyv : r y v := by
      rcases hz'.2.1 with e | hrel
      · simpa [e] using hzv
      · exact htrans hrel hzv
    have hv' : v ∈ candidates := by simp [candidates, hv, hyv, hvt]
    have := hmax v hv'
    have := hrespect z v hzv
    omega
  exact ⟨z, hz'.1, hzt, hz'.2.1, hzHigh⟩

theorem advance_earlier_high {W : Finset J} {r : J → J → Prop}
    {time priority : J → ℕ} {S : Set J} {s : ℕ} {x : J}
    (htrans : ∀ ⦃a b c⦄, r a b → r b c → r a c) (hrespect : ∀ u v, r u v → time u < time v)
    (hclosed : SlotClosed W time) (hpos : AdmissiblePosition W time s)
    (hideal : IdealOn W r S) (hprefix : PrefixOn W priority S)
    (hnorm : LocalObstruction W r time priority)
    (hbefore : EarlierHigh W r time S s) (hx : Exception W r time S s x) :
    EarlierHigh W r time S (time x) := by
  have hready := exception_ready htrans hrespect hideal hx
  have hforce : ∀ y ∈ W, y ∉ S → s ≤ time y → time y < time x →
      ∃ z ∈ W, r y z ∧ time z ≤ time x := by
    intro y hy hyHigh hsy hyt
    exact hnorm x hx.mem y hy hyt (hprefix x hx.mem hx.low y hy hyHigh)
      (fun u hu hur => (hready u hu hur).trans_le hsy)
  intro z hz hzt hzHigh
  by_cases hzs : time z < s
  · obtain ⟨y, hys, hzy⟩ := hbefore z hz hzs hzHigh
    have hy : y ∈ W := by
      rcases hpos with ⟨a, ha, has⟩ | hleft
      · exact hclosed a ha y (hys.trans has.symm)
      · have := hleft z hz
        omega
    have hyHigh : y ∉ S := by
      intro hylow
      exact hzHigh (hideal z hz y hy hzy hylow)
    obtain ⟨v, _hv, hvt, hyv, _hvHigh⟩ := trace_to_slot htrans hrespect hideal
      hforce y hy hyHigh (by omega) (by have := hx.later; omega)
    refine ⟨v, hvt, ?_⟩
    rcases hyv with e | hrel
    · simpa [e] using hzy
    · exact htrans hzy hrel
  · have hsz : s ≤ time z := by omega
    obtain ⟨v, _hv, hvt, hzv, _hvHigh⟩ := trace_to_slot htrans hrespect hideal
      hforce z hz hzHigh hsz hzt.le
    refine ⟨v, hvt, ?_⟩
    rcases hzv with e | hrel
    · subst v
      omega
    · exact hrel

theorem advance_shared_earlier {W : Finset J} {r : J → J → Prop}
    {time priority : J → ℕ} {S Splus : Set J} {s : ℕ} {x a : J}
    (htrans : ∀ ⦃a b c⦄, r a b → r b c → r a c) (hrespect : ∀ u v, r u v → time u < time v)
    (hclosed : SlotClosed W time) (hpos : AdmissiblePosition W time s)
    (hideal : IdealOn W r S) (hidealPlus : IdealOn W r Splus)
    (hprefix : PrefixOn W priority S) (hprefixPlus : PrefixOn W priority Splus)
    (hpromotion : ∀ z ∈ W, z ∈ Splus ↔ z ∈ S ∨ z = a)
    (hnorm : LocalObstruction W r time priority)
    (hbefore : EarlierHigh W r time S s)
    (hx : Exception W r time Splus s x) :
    EarlierHigh W r time S (time x) := by
  by_cases hxOld : x ∈ S
  · apply advance_earlier_high htrans hrespect hclosed hpos hideal hprefix hnorm hbefore
    exact ⟨hx.mem, hxOld, hx.later, hx.not_desc, fun y hy hlow hsy hyx =>
      hx.earliest y hy ((hpromotion y hy).mpr (Or.inl hlow)) hsy hyx⟩
  · have hxa : x = a := ((hpromotion x hx.mem).mp hx.low).resolve_left hxOld
    have hbeforePlus : EarlierHigh W r time Splus s := by
      intro z hz hzs hzHigh
      exact hbefore z hz hzs (fun h => hzHigh ((hpromotion z hz).mpr (Or.inl h)))
    have hnew := advance_earlier_high htrans hrespect hclosed hpos hidealPlus
      hprefixPlus hnorm hbeforePlus hx
    intro z hz hzx hzHigh
    apply hnew z hz hzx
    intro hlow
    rcases (hpromotion z hz).mp hlow with h | e
    · exact hzHigh h
    · have : z = x := e.trans hxa.symm
      have heq : time z = time x := congrArg time this
      omega

end Walk
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section SharedWalk
variable {J : Type}

theorem AdvancePath.le {W : Finset J} {r : J → J → Prop} {time : J → ℕ}
    {S : Set J} {s t : ℕ} (h : AdvancePath W r time S s t) : s ≤ t := by
  induction h with
  | refl => exact le_rfl
  | step _ hx ih => exact ih.trans hx.later.le

theorem AdvancePath.endpoint {W : Finset J} {r : J → J → Prop} {time : J → ℕ}
    {S : Set J} {s t : ℕ} (h : AdvancePath W r time S s t) :
    t = s ∨ ∃ x ∈ W, time x = t := by
  cases h with
  | refl => exact Or.inl rfl
  | step _ hx => exact Or.inr ⟨_, hx.mem, rfl⟩

theorem AdvancePath.admissible {W : Finset J} {r : J → J → Prop} {time : J → ℕ}
    {S : Set J} {s t : ℕ} (h : AdvancePath W r time S s t)
    (hpos : AdmissiblePosition W time s) : AdmissiblePosition W time t := by
  rcases h.endpoint with e | hmem
  · simpa [e] using hpos
  · exact Or.inl hmem

theorem AdvancePath.shared_earlier {W : Finset J} {r : J → J → Prop}
    {time priority : J → ℕ} {S Splus : Set J} {s t : ℕ} {a : J}
    (htrans : ∀ ⦃a b c⦄, r a b → r b c → r a c)
    (hrespect : ∀ u v, r u v → time u < time v)
    (hclosed : SlotClosed W time) (hpos : AdmissiblePosition W time s)
    (hideal : IdealOn W r S) (hidealPlus : IdealOn W r Splus)
    (hprefix : PrefixOn W priority S) (hprefixPlus : PrefixOn W priority Splus)
    (hpromotion : ∀ z ∈ W, z ∈ Splus ↔ z ∈ S ∨ z = a)
    (hnorm : LocalObstruction W r time priority)
    (hbefore : EarlierHigh W r time S s)
    (h : AdvancePath W r time Splus s t) : EarlierHigh W r time S t := by
  induction h with
  | refl => exact hbefore
  | step h hx ih =>
      exact advance_shared_earlier htrans hrespect hclosed (h.admissible hpos)
        hideal hidealPlus hprefix hprefixPlus hpromotion hnorm ih hx

theorem shared_cutoff {W : Finset J} {r : J → J → Prop}
    {time priority : J → ℕ} {S Splus : Set J} {s : ℕ} {a : J}
    (htrans : ∀ ⦃a b c⦄, r a b → r b c → r a c)
    (hrespect : ∀ u v, r u v → time u < time v)
    (hclosed : SlotClosed W time) (hpos : AdmissiblePosition W time s)
    (hideal : IdealOn W r S) (hidealPlus : IdealOn W r Splus)
    (hprefix : PrefixOn W priority S) (hprefixPlus : PrefixOn W priority Splus)
    (hpromotion : ∀ z ∈ W, z ∈ Splus ↔ z ∈ S ∨ z = a)
    (hnorm : LocalObstruction W r time priority)
    (hsep : Separator W r time S s) :
    ∃ t, s ≤ t ∧ AdvancePath W r time Splus s t ∧
      Separator W r time S t ∧ Separator W r time Splus t := by
  classical
  let candidates := (insert s (W.image time)).filter (AdvancePath W r time Splus s)
  have hne : candidates.Nonempty := ⟨s, by simp [candidates, AdvancePath.refl]⟩
  obtain ⟨t, ht, hmax⟩ := candidates.exists_max_image id hne
  have hpath : AdvancePath W r time Splus s t := (Finset.mem_filter.mp ht).2
  have hafter : LaterLow W r time Splus t := by
    by_contra hn
    obtain ⟨x, hx⟩ := exists_exception hn
    have hnext : AdvancePath W r time Splus s (time x) := .step hpath hx
    have hmem : time x ∈ candidates := by
      simp only [candidates, Finset.mem_filter, Finset.mem_insert, Finset.mem_image]
      exact ⟨Or.inr ⟨x, hx.mem, rfl⟩, hnext⟩
    have := hmax (time x) hmem
    have := hx.later
    simp only [id_eq] at *
    omega
  have hbefore := hpath.shared_earlier htrans hrespect hclosed hpos hideal hidealPlus
    hprefix hprefixPlus hpromotion hnorm hsep.1
  refine ⟨t, hpath.le, hpath, ⟨hbefore, ?_⟩, ⟨?_, hafter⟩⟩
  · intro x hx htx hlow
    exact hafter x hx htx ((hpromotion x hx).mpr (Or.inl hlow))
  · intro x hx hxt hhigh
    exact hbefore x hx hxt (fun h => hhigh ((hpromotion x hx).mpr (Or.inl h)))

theorem separator_congr {W : Finset J} {r : J → J → Prop} {time : J → ℕ}
    {S Splus : Set J} {s : ℕ} (heq : ∀ z ∈ W, z ∈ S ↔ z ∈ Splus) :
    Separator W r time S s ↔ Separator W r time Splus s := by
  constructor
  · rintro ⟨hbefore, hafter⟩
    constructor
    · intro x hx hxt hhigh
      exact hbefore x hx hxt (fun h => hhigh ((heq x hx).mp h))
    · intro x hx htx hlow
      exact hafter x hx htx ((heq x hx).mpr hlow)
  · rintro ⟨hbefore, hafter⟩
    constructor
    · intro x hx hxt hhigh
      exact hbefore x hx hxt (fun h => hhigh ((heq x hx).mpr h))
    · intro x hx htx hlow
      exact hafter x hx htx ((heq x hx).mp hlow)

end SharedWalk
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section IdealSeparator
variable {J : Type}

theorem AdvancePath.earlier {W : Finset J} {r : J → J → Prop}
    {time priority : J → ℕ} {S : Set J} {s t : ℕ}
    (htrans : ∀ ⦃a b c⦄, r a b → r b c → r a c)
    (hrespect : ∀ u v, r u v → time u < time v)
    (hclosed : SlotClosed W time) (hpos : AdmissiblePosition W time s)
    (hideal : IdealOn W r S) (hprefix : PrefixOn W priority S)
    (hnorm : LocalObstruction W r time priority)
    (hbefore : EarlierHigh W r time S s)
    (h : AdvancePath W r time S s t) : EarlierHigh W r time S t := by
  induction h with
  | refl => exact hbefore
  | step h hx ih =>
      exact advance_earlier_high htrans hrespect hclosed
        (h.admissible hpos) hideal hprefix hnorm ih hx

theorem walk_to_separator {W : Finset J} {r : J → J → Prop}
    {time priority : J → ℕ} {S : Set J} {s : ℕ}
    (htrans : ∀ ⦃a b c⦄, r a b → r b c → r a c)
    (hrespect : ∀ u v, r u v → time u < time v)
    (hclosed : SlotClosed W time) (hpos : AdmissiblePosition W time s)
    (hideal : IdealOn W r S) (hprefix : PrefixOn W priority S)
    (hnorm : LocalObstruction W r time priority)
    (hbefore : EarlierHigh W r time S s) :
    ∃ t, s ≤ t ∧ AdvancePath W r time S s t ∧ Separator W r time S t := by
  classical
  let candidates := (insert s (W.image time)).filter (AdvancePath W r time S s)
  have hne : candidates.Nonempty := ⟨s, by simp [candidates, AdvancePath.refl]⟩
  obtain ⟨t, ht, hmax⟩ := candidates.exists_max_image id hne
  have hpath : AdvancePath W r time S s t := (Finset.mem_filter.mp ht).2
  refine ⟨t, hpath.le, hpath, hpath.earlier htrans hrespect hclosed hpos hideal
    hprefix hnorm hbefore, ?_⟩
  by_contra hn
  obtain ⟨x, hx⟩ := exists_exception hn
  have hnext : AdvancePath W r time S s (time x) := .step hpath hx
  have hmem : time x ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_insert, Finset.mem_image]
    exact ⟨Or.inr ⟨x, hx.mem, rfl⟩, hnext⟩
  have := hmax (time x) hmem
  have := hx.later
  simp only [id_eq] at *
  omega

end IdealSeparator
end ThreeMachine.Structure

end

end OAI
end

section
-- module GlobalBoundaries
namespace OAI

section

namespace ThreeMachine.Structure

theorem GlobalUpset.union {J : Type} {r : J → J → Prop} {A B : Set J}
    (hA : GlobalUpset r A) (hB : GlobalUpset r B) : GlobalUpset r (A ∪ B) := by
  intro x y hxy hx
  exact hx.elim (fun h => Or.inl (hA hxy h)) (fun h => Or.inr (hB hxy h))

namespace GlobalList
variable {J : Type}

theorem lastIndex_mem {K : GlobalList J} {x : J} (hx : x ∈ K.Qual) :
    K.lastIndex x ∈ K.indices ∧ x ∈ K.entry (K.lastIndex x) := by
  obtain ⟨i, hi, hxi⟩ := hx
  have hne : (K.memberships x).Nonempty := ⟨i, (mem_memberships K x i).mpr ⟨hi, hxi⟩⟩
  have := Finset.sup_mem_of_nonempty (f := id) hne
  obtain ⟨j, hj, e⟩ := this
  change j = K.lastIndex x at e
  apply (mem_memberships K x (K.lastIndex x)).mp
  rw [← e]
  exact hj

theorem qual_upset {K : GlobalList J} {r : J → J → Prop}
    (hK : K.Upsets r) : GlobalUpset r K.Qual := by
  rintro x y hxy ⟨i, hi, hx⟩
  exact ⟨i, hi, hK i hi hxy hx⟩

theorem key_extends {K : GlobalList J} {r : J → J → Prop} {rank : J → ℕ}
    (hK : K.Upsets r) (hrank : ∀ x y, r x y → rank x < rank y)
    {x y : J} (hx : x ∈ K.Qual) (hxy : r x y) : K.KeyLT rank x y := by
  obtain ⟨hi, hxlast⟩ := lastIndex_mem hx
  have hle : K.lastIndex x ≤ K.lastIndex y := le_lastIndex hi (hK _ hi hxy hxlast)
  rcases hle.lt_or_eq with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, hrank x y hxy⟩

theorem carry_membership (K : GlobalList J) (rank : J → ℕ) (d r i : ℕ) (x : J) :
    i ∈ (K.carry rank d r).memberships x ↔
      i ∈ K.indices ∧ d ≤ i ∧ x ∈ K.entry i ∧ (i = d → r ≤ rank x) := by
  classical
  rw [mem_memberships]
  change (i ∈ K.indices.filter (d ≤ ·) ∧
    x ∈ (if i = d then K.entry i ∩ {x | r ≤ rank x} else K.entry i)) ↔ _
  rw [Finset.mem_filter]
  by_cases hi : i = d <;> simp [hi, and_assoc]

theorem carry_selection (K : GlobalList J) (rank : J → ℕ) (d r : ℕ) (x : J) :
    x ∈ (K.carry rank d r).Qual ↔ x ∈ K.Qual ∧
      (d < K.lastIndex x ∨ K.lastIndex x = d ∧ r ≤ rank x) := by
  constructor
  · rintro ⟨i, hi, hx⟩
    have hc := (carry_membership K rank d r i x).mp
      ((mem_memberships _ _ _).mpr ⟨hi, hx⟩)
    refine ⟨⟨i, hc.1, hc.2.2.1⟩, ?_⟩
    have hle := le_lastIndex hc.1 hc.2.2.1
    by_cases h : d < K.lastIndex x
    · exact Or.inl h
    · have hid : i = d := by omega
      exact Or.inr ⟨by omega, hc.2.2.2 hid⟩
  · rintro ⟨hq, hmax⟩
    obtain ⟨hi, hx⟩ := lastIndex_mem hq
    refine ⟨K.lastIndex x, ?_⟩
    apply (mem_memberships _ _ _).mp
    apply (carry_membership K rank d r _ x).mpr
    refine ⟨hi, ?_, hx, ?_⟩
    · rcases hmax with h | ⟨h, _⟩ <;> omega
    · intro e
      rcases hmax with h | ⟨_, hr⟩
      · omega
      · exact hr

theorem carry_lastIndex {K : GlobalList J} {rank : J → ℕ} {d r : ℕ} {x : J}
    (hx : x ∈ (K.carry rank d r).Qual) :
    (K.carry rank d r).lastIndex x = K.lastIndex x := by
  have hsel := (carry_selection K rank d r x).mp hx
  apply le_antisymm
  · apply Finset.sup_le
    intro i hi
    have hm := (carry_membership K rank d r i x).mp hi
    exact le_lastIndex hm.1 hm.2.2.1
  · obtain ⟨hi, hxi⟩ := lastIndex_mem hsel.1
    apply Finset.le_sup (f := id) (b := K.lastIndex x)
    apply (carry_membership K rank d r (K.lastIndex x) x).mpr
    refine ⟨hi, ?_, hxi, ?_⟩
    · rcases hsel.2 with h | ⟨h, _⟩ <;> omega
    · intro e
      rcases hsel.2 with h | ⟨_, hr⟩
      · omega
      · exact hr

theorem carry_key {K : GlobalList J} {rank : J → ℕ} {d r : ℕ} {x y : J}
    (hx : x ∈ (K.carry rank d r).Qual) (hy : y ∈ (K.carry rank d r).Qual) :
    (K.carry rank d r).KeyLT rank x y ↔ K.KeyLT rank x y := by
  simp only [KeyLT, carry_lastIndex hx, carry_lastIndex hy]

theorem carry_upsets {K : GlobalList J} {rank : J → ℕ} {d t : ℕ}
    {r : J → J → Prop} (hK : K.Upsets r)
    (hrank : ∀ x y, r x y → rank x < rank y) : (K.carry rank d t).Upsets r := by
  classical
  intro i hi x y hxy hx
  have hi' : i ∈ K.indices ∧ d ≤ i := by simpa [carry] using hi
  by_cases hid : i = d
  · have hx' : x ∈ K.entry i ∧ t ≤ rank x := by simpa [carry, hid] using hx
    have hrankxy := hrank x y hxy
    have hy : y ∈ K.entry i := hK i hi'.1 hxy hx'.1
    simpa [carry, hid] using And.intro hy (show t ≤ rank y by omega)
  · have hx' : x ∈ K.entry i := by simpa [carry, hid] using hx
    simpa [carry, hid] using hK i hi'.1 hxy hx'

end GlobalList
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section IntervalNormalization
variable {J : Type} [Fintype J]

theorem Layout.FixedOutside.refl (p : Layout J) (W : Set J) : p.FixedOutside p W :=
  fun _ _ => rfl

theorem Layout.FixedOutside.mono {p q : Layout J} {W U : Set J}
    (h : p.FixedOutside q W) (hWU : W ⊆ U) : p.FixedOutside q U :=
  fun x hx => h x (fun hW => hx (hWU hW))

theorem exists_normalizedOn (p : Layout J) (W : Set J) (r : J → J → Prop)
    (priority : J → ℕ) (hp : p.Respects r) :
    ∃ q : Layout J, p.FixedOutside q W ∧ q.NormalizedOn W r priority := by
  classical
  let candidates : Finset (Layout J) := Finset.univ.filter
    (fun q => q.Respects r ∧ p.FixedOutside q W)
  have hne : candidates.Nonempty := ⟨p, by simp [candidates, hp, Layout.FixedOutside.refl]⟩
  obtain ⟨q, hq, hmin⟩ := candidates.exists_min_image (fun q => q.signature priority) hne
  have hq' : q.Respects r ∧ p.FixedOutside q W := by simpa [candidates] using hq
  refine ⟨q, hq'.2, hq'.1, ?_⟩
  intro u hu hqu
  exact hmin u (by simp [candidates, hu, hq'.2.trans hqu])

theorem normalizedOn_no_improvement {p q : Layout J} {W : Set J}
    {r : J → J → Prop} {priority : J → ℕ} (hp : p.NormalizedOn W r priority)
    (hq : q.Respects r) (hfix : p.FixedOutside q W)
    (i : Fin (Fintype.card J))
    (hbefore : ∀ j, j < i → priority (q.symm j) = priority (p.symm j))
    (hi : priority (q.symm i) < priority (p.symm i)) : False := by
  have hlt : q.signature priority < p.signature priority :=
    ofFn_lt_of_first_difference _ _ i hbefore hi
  exact (not_lt_of_ge (hp.2 q hq hfix)) hlt

theorem exchange_fixedOutside [DecidableEq J] {p : Layout J} {W : Set J}
    {x y : J} (hx : x ∈ W) (hy : y ∈ W) : p.FixedOutside (p.exchange x y) W := by
  intro z hz
  have hzx : z ≠ x := fun e => hz (e ▸ hx)
  have hzy : z ≠ y := fun e => hz (e ▸ hy)
  simp [Layout.exchange, Equiv.swap_apply_of_ne_of_ne hzx hzy]

theorem normalizedOn_prefix_no_exchange [DecidableEq J]
    {p q : Layout J} {W : Set J} {r : J → J → Prop} {priority : J → ℕ}
    (hp : p.NormalizedOn W r priority) (hfix : p.FixedOutside q W)
    {x y : J} (hx : x ∈ W) (hy : y ∈ W)
    (hprefix : ∀ j, j ≤ p y → q.symm j = p.symm j)
    (ht : q.time y < q.time x) (hbetter : priority x < priority y)
    (hswap : (q.exchange x y).Respects r) : False := by
  have hqy : q y = p y := by
    have he := hprefix (p y) le_rfl
    simp only [p.symm_apply_apply] at he
    exact (congrArg q he).symm.trans (q.apply_symm_apply _)
  have hpos : p y < q x := by
    change (p y).val < (q x).val
    dsimp [Layout.time] at ht
    rw [hqy] at ht
    omega
  apply normalizedOn_no_improvement hp hswap
    (hfix.trans (exchange_fixedOutside hx hy)) (p y)
  · intro j hj
    have hpy := hprefix j hj.le
    have hny : q.symm j ≠ y := by
      intro e
      have he : j = p y := by simpa [hqy] using congrArg q e
      exact (ne_of_lt hj) he
    have hnx : q.symm j ≠ x := by
      intro e
      have he : j = q x := by simpa using congrArg q e
      rw [he] at hj
      exact (not_lt_of_ge hpos.le) hj
    change priority ((Equiv.swap x y) (q.symm j)) = priority (p.symm j)
    rw [Equiv.swap_apply_of_ne_of_ne hnx hny, hpy]
  · have hpy := hprefix (p y) le_rfl
    simp only [p.symm_apply_apply] at hpy
    simpa [Layout.exchange, hpy] using hbetter

theorem normalizedOn_local_obstruction {p : Layout J} {W : Finset J}
    {a b : ℕ} {r : J → J → Prop} {priority : J → ℕ}
    (hp : p.NormalizedOn (W : Set J) r priority)
    (hW : ∀ z, z ∈ W ↔ a < p.time z ∧ p.time z < b) :
    LocalObstruction W r p.time priority := by
  classical
  intro x hx y hy htyx hbetter hpred
  by_contra hn
  have hsucc : ∀ v, r y v → p.time x < p.time v := by
    intro v hyv
    have hyvTime := hp.1 y v hyv
    by_cases hv : v ∈ W
    · by_contra h
      exact hn ⟨v, hv, hyv, by omega⟩
    · have hnt : ¬(a < p.time v ∧ p.time v < b) := fun h => hv ((hW v).mpr h)
      have hxt := (hW x).mp hx
      have hyt := (hW y).mp hy
      omega
  have hready : ∀ u, r u x → p.time u < p.time y := by
    intro u hux
    by_cases hu : u ∈ W
    · exact hpred u hu hux
    · have huxTime := hp.1 u x hux
      have hnt : ¬(a < p.time u ∧ p.time u < b) := fun h => hu ((hW u).mpr h)
      have hxt := (hW x).mp hx
      have hyt := (hW y).mp hy
      omega
  exact normalizedOn_prefix_no_exchange hp (Layout.FixedOutside.refl p _)
    hx hy (fun _ _ => rfl) htyx hbetter (respects_exchange hp.1 x y htyx hready hsucc)

end IntervalNormalization
end ThreeMachine.Structure

namespace ThreeMachine.Structure

namespace Boundary
variable {J : Type}

theorem weakPred_downset {r : J → J → Prop}
    (htrans : ∀ ⦃a b c⦄, r a b → r b c → r a c) (B : Boundary J) :
    GlobalDownset r (B.weakPred r) := by
  intro x y hxy hy
  cases B with
  | left => exact hy.elim
  | right => trivial
  | actual Z =>
      rcases hy with h | h
      · exact Or.inl (pred_downset htrans (.actual Z) hxy h)
      · exact Or.inl ⟨y, h, hxy⟩

theorem actual_pred_eq {r : J → J → Prop} {time : J → ℕ} {T s : ℕ} {Z : Triple J}
    (hZ : (Boundary.actual Z).At time T s) :
    (Boundary.actual Z).pred r = PredAt r time s := by
  ext x
  simp only [pred, PredAt, Set.mem_ofPred_eq, hZ.2.2]

theorem actual_desc_eq {r : J → J → Prop} {time : J → ℕ} {T s : ℕ} {Z : Triple J}
    (hZ : (Boundary.actual Z).At time T s) :
    (Boundary.actual Z).desc r = DescAt r time s := by
  ext x
  simp only [desc, DescAt, Set.mem_ofPred_eq, hZ.2.2]

end Boundary

namespace Formula
variable {A J : Type}

theorem leaves_pos (p : Formula A) : 0 < p.leaves := by
  induction p with
  | leaf => exact Nat.zero_lt_one
  | conj p q hp hq | disj p q hp hq => dsimp [leaves]; omega

end Formula

namespace Described
variable {A J : Type} {atoms : A → Set J} {W U : Set J} {k l : ℕ}

theorem atom (a : A) : Described atoms (atoms a) 1 := ⟨.leaf a false, rfl, le_rfl⟩

end Described
end ThreeMachine.Structure

end

end OAI
end

section
-- module CutoffSimplification
namespace OAI

section

namespace ThreeMachine.Structure
namespace GlobalList
variable {J : Type}

theorem lt_nextIndex {K : GlobalList J} {i : ℕ} (hi : i ∈ K.indices) :
    i < K.nextIndex := by
  have h := Finset.le_sup (f := id) hi
  change i ≤ K.indices.sup id at h
  dsimp [nextIndex]
  omega

theorem nextIndex_not_mem (K : GlobalList J) : K.nextIndex ∉ K.indices := by
  intro hi
  exact (lt_irrefl _ (lt_nextIndex hi)).elim

theorem append_membership (K : GlobalList J) (A : Set J) (i : ℕ) (x : J) :
    i ∈ (K.append A).memberships x ↔
      (i = K.nextIndex ∧ x ∈ A) ∨ (i ∈ K.indices ∧ x ∈ K.entry i) := by
  classical
  rw [mem_memberships]
  change (i ∈ insert K.nextIndex K.indices ∧
    x ∈ (if i = K.nextIndex then A else K.entry i)) ↔ _
  by_cases hi : i = K.nextIndex
  · subst i
    simp [nextIndex_not_mem]
  · simp [hi]

theorem append_qual (K : GlobalList J) (A : Set J) :
    (K.append A).Qual = K.Qual ∪ A := by
  ext x
  constructor
  · rintro ⟨i, hi, hx⟩
    rcases (append_membership K A i x).mp ((mem_memberships _ _ _).mpr ⟨hi, hx⟩)
      with ⟨_, hx⟩ | ⟨hi, hx⟩
    · exact Or.inr hx
    · exact Or.inl ⟨i, hi, hx⟩
  · rintro (⟨i, hi, hx⟩ | hx)
    · exact ⟨i, (mem_memberships _ _ _).mp
        ((append_membership K A i x).mpr (Or.inr ⟨hi, hx⟩))⟩
    · exact ⟨K.nextIndex, (mem_memberships _ _ _).mp
        ((append_membership K A _ x).mpr (Or.inl ⟨rfl, hx⟩))⟩

theorem append_upsets {K : GlobalList J} {A : Set J} {r : J → J → Prop}
    (hK : K.Upsets r) (hA : GlobalUpset r A) : (K.append A).Upsets r := by
  classical
  intro i hi
  change i ∈ insert K.nextIndex K.indices at hi
  rcases Finset.mem_insert.mp hi with hi | hi
  · subst i
    simpa [append, nextIndex] using hA
  · have hn : i ≠ K.nextIndex := (lt_nextIndex hi).ne
    change GlobalUpset r (if i = K.nextIndex then A else K.entry i)
    simpa [hn] using hK i hi

theorem append_lastIndex_of_mem {K : GlobalList J} {A : Set J} {x : J}
    (hx : x ∈ A) : (K.append A).lastIndex x = K.nextIndex := by
  apply le_antisymm
  · apply Finset.sup_le
    intro i hi
    rcases (append_membership K A i x).mp hi with ⟨hi, _⟩ | ⟨hi, _⟩
    · exact hi.le
    · exact (lt_nextIndex hi).le
  · apply Finset.le_sup (f := id) (b := K.nextIndex)
    exact (append_membership K A _ x).mpr (Or.inl ⟨rfl, hx⟩)

theorem append_lastIndex_of_not_mem {K : GlobalList J} {A : Set J} {x : J}
    (hx : x ∉ A) : (K.append A).lastIndex x = K.lastIndex x := by
  apply congrArg (fun s : Finset ℕ => s.sup id)
  ext i
  rw [append_membership, mem_memberships]
  simp [hx]

theorem append_key_of_not_mem {K : GlobalList J} {A : Set J} {rank : J → ℕ}
    {x y : J} (hx : x ∉ A) (hy : y ∉ A) :
    (K.append A).KeyLT rank x y ↔ K.KeyLT rank x y := by
  simp only [KeyLT, append_lastIndex_of_not_mem hx, append_lastIndex_of_not_mem hy]

end GlobalList
end ThreeMachine.Structure

namespace ThreeMachine.Structure
variable {J : Type}

namespace Boundary

theorem pred_subset_weakPred (r : J → J → Prop) (B : Boundary J) :
    B.pred r ⊆ B.weakPred r := by
  cases B with
  | left => exact Set.Subset.rfl
  | right => exact Set.Subset.rfl
  | actual Z => exact Set.subset_union_left

theorem separates_congr {r : J → J → Prop} {time : J → ℕ}
    {B : Boundary J} {W S S' : Set J} {s : ℕ}
    (h : ∀ x ∈ W, x ∈ S ↔ x ∈ S') :
    B.Separates r time W S s ↔ B.Separates r time W S' s := by
  unfold Separates
  constructor <;> rintro ⟨hp, hd⟩
  · exact ⟨fun x hx ht hn => hp x hx ht (fun hs => hn ((h x hx).mp hs)),
      fun x hx ht hs => hd x hx ht ((h x hx).mpr hs)⟩
  · exact ⟨fun x hx ht hn => hp x hx ht (fun hs => hn ((h x hx).mpr hs)),
      fun x hx ht hs => hd x hx ht ((h x hx).mp hs)⟩

theorem left_separates {r : J → J → Prop} {time : J → ℕ} {W S : Set J} :
    (Boundary.left : Boundary J).Separates r time W S 0 := by
  exact ⟨fun _ _ h _ => (Nat.not_lt_zero _ h).elim, fun _ _ _ _ => trivial⟩

theorem actual_separates {r : J → J → Prop} {time : J → ℕ} {T s : ℕ}
    {Z : Triple J} {W : Finset J} {S : Set J}
    (hZ : (Boundary.actual Z).At time T s) :
    (Boundary.actual Z).Separates r time W S s ↔ Separator W r time S s := by
  unfold Separates Separator EarlierHigh LaterLow
  rw [actual_pred_eq hZ, actual_desc_eq hZ]
  rfl

end Boundary

end ThreeMachine.Structure

namespace ThreeMachine.Structure
variable {J : Type}

end ThreeMachine.Structure

end

end OAI
end

section
-- module FrameInvariants
namespace OAI

section

namespace ThreeMachine.Structure
namespace Layout
variable {J : Type} [Fintype J]

theorem triple_at (p : Layout J) (hfull : 3 ∣ Fintype.card J)
    (s : ℕ) (hs : 1 ≤ s) (hsT : s ≤ Fintype.card J / 3) :
    (Boundary.actual (p.triple hfull s hs hsT)).At p.time (Fintype.card J / 3) s := by
  exact ⟨hs, hsT, fun x => p.mem_slot s x⟩

theorem reverse_respects {p : Layout J} {r : J → J → Prop}
    (hfull : 3 ∣ Fintype.card J) (hp : p.Respects r) :
    p.reverse.Respects (fun x y => r y x) := by
  intro x y hyx
  rw [p.reverse_time hfull, p.reverse_time hfull]
  have hxy := hp y x hyx
  have hx := p.time_bounds hfull x
  have hy := p.time_bounds hfull y
  omega

theorem reverse_full {p : Layout J} {r : J → J → Prop} (hp : p.Full r) :
    p.reverse.Full (fun x y => r y x) := ⟨hp.1, reverse_respects hp.1 hp.2⟩

end Layout

namespace Boundary
variable {J : Type} [Fintype J]

theorem at_reverse {p : Layout J} (hfull : 3 ∣ Fintype.card J)
    {B : Boundary J} {s : ℕ} (h : B.At p.time (Fintype.card J / 3) s) :
    B.reverse.At p.reverse.time (Fintype.card J / 3) (Fintype.card J / 3 + 1 - s) := by
  cases B with
  | left => dsimp [At] at h; subst s; rfl
  | right => dsimp [At] at h; subst s; simp [reverse, At]
  | actual Z =>
      dsimp only [At] at h
      refine ⟨by omega, by omega, ?_⟩
      intro x
      rw [h.2.2, p.reverse_time hfull]
      have hx := p.time_bounds hfull x
      omega

end Boundary

end ThreeMachine.Structure

namespace ThreeMachine.Structure
section IntervalHelpers
variable {J : Type} [Fintype J]

end IntervalHelpers
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section BoundaryWalk
variable {J : Type} [Fintype J]

theorem exception_global_ready {r : J → J → Prop} {p : Layout J}
    {E : Finset J} {a v : ℕ} {S : Set J} {x : J}
    (htrans : ∀ ⦃u z w⦄, r u z → r z w → r u w) (hp : p.Respects r)
    (hE : ∀ z, z ∈ E ↔ a < p.time z ∧ p.time z < v)
    (hideal : IdealOn E r S) (hx : Exception E r p.time S a x) :
    ∀ u, r u x → p.time u < a := by
  intro u hux
  have htx := hp u x hux
  have hxt := (hE x).mp hx.mem
  by_contra hn
  have hau : a ≤ p.time u := by omega
  rcases hau.eq_or_lt with he | hl
  · exact hx.not_desc ⟨u, he.symm, hux⟩
  · have hu : u ∈ E := (hE u).mpr ⟨hl, htx.trans hxt.2⟩
    have := exception_ready htrans hp hideal hx u hu hux
    omega

omit [Fintype J] in

theorem advance_carry_descendant {r : J → J → Prop} {time priority : J → ℕ}
    {E : Finset J} {H S : Set J} {a v s : ℕ} {x y : J}
    (htrans : ∀ ⦃u z w⦄, r u z → r z w → r u w)
    (hrespect : ∀ u z, r u z → time u < time z)
    (hE : ∀ z, z ∈ E ↔ a < time z ∧ time z < v)
    (hH : GlobalUpset r H) (hhigh : ∀ z ∈ E, z ∈ H → z ∉ S)
    (hideal : IdealOn E r S) (hprefix : PrefixOn E priority S)
    (hnorm : LocalObstruction E r time priority)
    (has : a ≤ s) (hx : Exception E r time S s x)
    (hfirst : s = a → ∀ z ∈ H, time z = a → ∃ u ∈ E, r z u ∧ time u ≤ time x)
    (hyH : y ∈ H) (hys : time y = s) :
    ∃ z ∈ E, time z = time x ∧ r y z ∧ z ∈ H := by
  have hready := exception_ready htrans hrespect hideal hx
  have hforce : ∀ z ∈ E, z ∉ S → s ≤ time z → time z < time x →
      ∃ u ∈ E, r z u ∧ time u ≤ time x := by
    intro z hz hnS hsz hzx
    exact hnorm x hx.mem z hz hzx (hprefix x hx.mem hx.low z hz hnS)
      (fun u hu hux => (hready u hu hux).trans_le hsz)
  have hsucc : ∃ u ∈ E, r y u ∧ time u ≤ time x := by
    by_cases hsa : s = a
    · exact hfirst hsa y hyH (hys.trans hsa)
    · have hyE : y ∈ E := (hE y).mpr
        ⟨by omega, by have := (hE x).mp hx.mem; have := hx.later; omega⟩
      exact hforce y hyE (hhigh y hyE hyH) (by omega) (by have := hx.later; omega)
  obtain ⟨u, hu, hyu, hut⟩ := hsucc
  have huH := hH hyu hyH
  have hsu : s ≤ time u := by have := hrespect y u hyu; omega
  obtain ⟨z, hz, hzt, huz, _hnS⟩ := trace_to_slot htrans hrespect hideal hforce
    u hu (hhigh u hu huH) hsu hut
  have hyz : r y z := by
    rcases huz with e | hur
    · simpa [e] using hyu
    · exact htrans hyu hur
  exact ⟨z, hz, hzt, hyz, hH hyz hyH⟩

theorem first_boundary_force [DecidableEq J]
    {r : J → J → Prop} {p : Layout J} {E : Finset J} {a v : ℕ}
    {S H : Set J} {x : J}
    (htrans : ∀ ⦃u z w⦄, r u z → r z w → r u w) (hp : p.Respects r)
    (hE : ∀ z, z ∈ E ↔ a < p.time z ∧ p.time z < v)
    (hideal : IdealOn E r S) (hx : Exception E r p.time S a x)
    (hno : ∀ y ∈ H, p.time y = a → ¬(p.exchange x y).Respects r) :
    ∀ y ∈ H, p.time y = a → ∃ u ∈ E, r y u ∧ p.time u ≤ p.time x := by
  have hready : ∀ u, r u x → p.time u < a :=
    exception_global_ready htrans hp hE hideal hx
  intro y hy hya
  by_contra hn
  have hsucc : ∀ u, r y u → p.time x < p.time u := by
    intro u hyu
    by_contra hntu
    have hxv := ((hE x).mp hx.mem).2
    have hyut := hp y u hyu
    have huE : u ∈ E := (hE u).mpr ⟨by omega, by omega⟩
    exact hn ⟨u, huE, hyu, by omega⟩
  have hyx : p.time y < p.time x := by have := hx.later; omega
  exact hno y hy hya (respects_exchange hp x y hyx (fun u hur => by
    have := hready u hur; omega) hsucc)

end BoundaryWalk
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section VaryingWalk
variable {J : Type}

theorem CutoffWalk.le {E : Finset J} {r : J → J → Prop} {time priority : J → ℕ}
    {S : Set J} {a t : ℕ} (h : CutoffWalk E r time priority S a t) : a ≤ t := by
  induction h with
  | refl => exact le_rfl
  | step _ _ _ _ hx ih => exact ih.trans hx.later.le

theorem CutoffWalk.mono {E : Finset J} {r : J → J → Prop} {time priority : J → ℕ}
    {S S' : Set J} {a t : ℕ} (h : CutoffWalk E r time priority S a t)
    (hsub : ∀ z ∈ E, z ∈ S → z ∈ S') : CutoffWalk E r time priority S' a t := by
  induction h with
  | refl => exact .refl
  | step _ hi hp hb hx ih => exact .step ih hi hp (fun z hz hu => hsub z hz (hb z hz hu)) hx

theorem CutoffWalk.trans_advance {E : Finset J} {r : J → J → Prop}
    {time priority : J → ℕ} {S U : Set J} {a s t : ℕ}
    (h : CutoffWalk E r time priority S a s) (hp : AdvancePath E r time U s t)
    (hi : IdealOn E r U) (hprefix : PrefixOn E priority U)
    (hbelow : ∀ z ∈ E, z ∈ U → z ∈ S) :
    CutoffWalk E r time priority S a t := by
  induction hp with
  | refl => exact h
  | step _ hx ih => exact .step ih hi hprefix hbelow hx

theorem CutoffWalk.carry {E : Finset J} {r : J → J → Prop} {time priority : J → ℕ}
    {S H : Set J} {a v t : ℕ}
    (htrans : ∀ ⦃u z w⦄, r u z → r z w → r u w)
    (hrespect : ∀ u z, r u z → time u < time z)
    (hE : ∀ z, z ∈ E ↔ a < time z ∧ time z < v)
    (hH : GlobalUpset r H) (hhigh : ∀ z ∈ E, z ∈ H → z ∉ S)
    (hnorm : LocalObstruction E r time priority)
    (hfirst : ∀ U, IdealOn E r U → PrefixOn E priority U →
      (∀ z ∈ E, z ∈ U → z ∈ S) → ∀ x, Exception E r time U a x →
      ∀ y ∈ H, time y = a → ∃ u ∈ E, r y u ∧ time u ≤ time x)
    (hwalk : CutoffWalk E r time priority S a t) :
    ∀ y ∈ H, time y = a → ∃ z, time z = t ∧ (z = y ∨ r y z) ∧ z ∈ H := by
  induction hwalk with
  | refl => exact fun y hy ht => ⟨y, ht, Or.inl rfl, hy⟩
  | @step s x U prev hi hp hb hx ih =>
    intro y hy hyt
    obtain ⟨z, hzt, hyz, hzH⟩ := ih y hy hyt
    obtain ⟨w, _hw, hwt, hzw, hwH⟩ := advance_carry_descendant htrans hrespect hE hH
      (fun z hz hzH hzU => hhigh z hz hzH (hb z hz hzU)) hi hp hnorm prev.le hx
      (fun hsa => hfirst U hi hp hb x (by simpa only [hsa] using hx)) hzH hzt
    refine ⟨w, hwt, Or.inr ?_, hwH⟩
    rcases hyz with rfl | hyz
    · exact hzw
    · exact htrans hyz hzw

end VaryingWalk

section PastUpdate
variable {J : Type} [Fintype J]

omit [Fintype J] in

theorem Boundary.weakPred_witness {r : J → J → Prop} {time : J → ℕ}
    {T a : ℕ} {A : Boundary J} {x : J}
    (hA : A.At time T a) (ha : a ≤ T) (hx : x ∈ A.weakPred r) :
    ∃ y, time y = a ∧ (x = y ∨ r x y) := by
  cases A with
  | left => exact False.elim hx
  | right => simp only [Boundary.At] at hA; omega
  | actual Z =>
    rcases hx with ⟨y, hy, hxy⟩ | hx
    · exact ⟨y, (hA.2.2 y).mp hy, Or.inr hxy⟩
    · exact ⟨x, (hA.2.2 x).mp hx, Or.inl rfl⟩

theorem past_update {r : J → J → Prop} {p : Layout J} {priority : J → ℕ}
    {E : Finset J} {a v ap : ℕ} {A A' : Boundary J} {K K' : GlobalList J}
    {S H : Set J}
    (hp : p.Full r) (htrans : ∀ ⦃u z w⦄, r u z → r z w → r u w)
    (hA : A.At p.time (Fintype.card J / 3) a)
    (hA' : A'.At p.time (Fintype.card J / 3) ap)
    (ha : a ≤ Fintype.card J / 3) (hap : ap < v)
    (hE : ∀ z, z ∈ E ↔ a < p.time z ∧ p.time z < v)
    (hparent : PastInvariant r p.time K A a)
    (hH : GlobalUpset r H) (hHO : H ⊆ K.Qual)
    (hearly : ∀ z ∈ K'.Qual, p.time z ≤ a → z ∈ H)
    (hhigh : ∀ z ∈ E, z ∈ K'.Qual → z ∉ S)
    (hHhigh : ∀ z ∈ E, z ∈ H → z ∉ S)
    (hsep : A'.Separates r p.time E S ap)
    (hnorm : LocalObstruction E r p.time priority)
    (hfirst : ∀ U, IdealOn E r U → PrefixOn E priority U →
      (∀ z ∈ E, z ∈ U → z ∈ S) → ∀ x, Exception E r p.time U a x →
      ∀ y ∈ H, p.time y = a → ∃ u ∈ E, r y u ∧ p.time u ≤ p.time x)
    (hwalk : CutoffWalk E r p.time priority S a ap) :
    PastInvariant r p.time K' A' ap := by
  intro z hz hzt
  by_cases hae : p.time z ≤ a
  · have hzH := hearly z hz hae
    obtain ⟨y, hya, hzy⟩ := Boundary.weakPred_witness hA ha (hparent z (hHO hzH) hae)
    have hyH : y ∈ H := by
      rcases hzy with rfl | hzy
      · exact hzH
      · exact hH hzy hzH
    obtain ⟨w, hwt, hyw, _hwH⟩ := hwalk.carry htrans hp.2 hE hH hHhigh hnorm hfirst y hyH hya
    have hwmem : w ∈ A'.weakPred r :=
      (Boundary.mem_weak_at_time (p.time_bounds hp.1) hA' hwt).1
    rcases hzy with rfl | hzy
    · rcases hyw with rfl | hyw
      · exact hwmem
      · exact Boundary.weakPred_downset htrans A' hyw hwmem
    · have hzw : r z w := by
        rcases hyw with rfl | hyw
        · exact hzy
        · exact htrans hzy hyw
      exact Boundary.weakPred_downset htrans A' hzw hwmem
  · have hzE := (hE z).mpr ⟨by omega, by omega⟩
    rcases hzt.eq_or_lt with he | hl
    · exact (Boundary.mem_weak_at_time (p.time_bounds hp.1) hA' he).1
    · exact A'.pred_subset_weakPred r (hsep.1 z hzE hl (hhigh z hzE hz))

end PastUpdate
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section ChildSwaps
variable {J : Type} [Fintype J] [DecidableEq J]

omit [DecidableEq J] in
theorem Layout.FixedOutside.earlier_positions {p q : Layout J} {W : Set J} {a b : ℕ}
    (hfix : p.FixedOutside q W) (hW : ∀ x, x ∈ W ↔ x ∈ Window p.time a b)
    {y : J} (hy : p.time y ≤ a) : ∀ j, j ≤ p y → q.symm j = p.symm j := by
  intro j hj
  have hn : p.symm j ∉ W := by
    intro hmem
    have ht := ((hW _).mp hmem).1
    dsimp [Layout.time] at ht hy
    have hjv : j.val ≤ (p y).val := hj
    simp only [p.apply_symm_apply] at ht
    omega
  apply q.injective
  rw [q.apply_symm_apply, hfix _ hn, p.apply_symm_apply]

theorem swap_from_normalized {r : J → J → Prop} {p : Layout J}
    {E W : Set J} {a b ap bp : ℕ} {A' : Boundary J}
    {K : GlobalList J} {rank priority : J → ℕ}
    (hE : ∀ x, x ∈ E ↔ x ∈ Window p.time a b)
    (hW : ∀ x, x ∈ W ↔ x ∈ Window p.time ap bp)
    (ha : a < ap) (hb : bp ≤ b) (hab : ap < bp)
    (hnorm : p.NormalizedOn E r priority)
    (hqual : ∀ x ∈ W, x ∉ A'.desc r → x ∈ K.Qual)
    (hkeys : ∀ x ∈ W, x ∈ K.Qual → ∀ y, p.time y = ap → y ∈ K.Qual →
      K.KeyLT rank x y → priority x < priority y) :
    SwapInvariant r p W K rank A' ap := by
  intro q hfix _hq x hx hnx y hy hyq hkey hswap
  have hWx := (hfix.window hW x).mp hx
  have hnWy : y ∉ W := by
    intro hw
    have ht := ((hfix.window hW) y).mp hw
    exact (lt_irrefl ap) (hy ▸ ht.1)
  have hpya : p.time y = ap := (hfix.time hnWy).symm.trans hy
  have hWE : W ⊆ E := by
    intro z hz
    have ht := (hW z).mp hz
    exact (hE z).mpr ⟨ha.trans ht.1, ht.2.trans_le hb⟩
  have hyE : y ∈ E := (hE y).mpr ⟨by omega, by omega⟩
  exact normalizedOn_prefix_no_exchange hnorm (hfix.mono hWE) (hWE hx) hyE
    (hfix.earlier_positions hW hpya.le) (by have := hWx.1; omega)
    (hkeys x hx (hqual x hx hnx) y hpya hyq hkey) hswap

end ChildSwaps
end ThreeMachine.Structure

end

end OAI
end

section
-- module RunCertificates
namespace OAI

section

namespace ThreeMachine.Structure
section RunCertificates
variable {J A : Type}

theorem rankTail_upset {r : J → J → Prop} {rank : J → ℕ}
    (hrank : ∀ x y, r x y → rank x < rank y) (k : ℕ) :
    GlobalUpset r (RankTail rank k) := by
  intro x y hxy hx
  exact hx.trans (hrank x y hxy).le

namespace RunData
variable {K : GlobalList J} {rank : J → ℕ} {atoms : A → Set J} {W W' : Set J}

theorem flat_union_agrees (D : RunData K rank atoms W) :
    ∀ x ∈ W, (∃ i ∈ K.indices, x ∈ D.flatEntry i) ↔ x ∈ K.Qual := by
  classical
  intro x hx
  constructor
  · rintro ⟨i, hi, hxi⟩
    by_cases he : i = 0
    · subst i
      change x ∈ if 0 = 0 then _ else _ at hxi
      rcases hxi with hD | htail
      · obtain ⟨h1, hx1⟩ := D.pair hi x hx hD
        exact ⟨1, h1, hx1⟩
      · by_cases hD : x ∈ D.second
        · obtain ⟨h1, hx1⟩ := D.pair hi x hx hD
          exact ⟨1, h1, hx1⟩
        · refine ⟨0, hi, ?_⟩
          rw [D.entry_eq 0 hi]
          exact ⟨D.cover x hx hD, htail⟩
    · exact ⟨i, hi, by simpa only [flatEntry, he, ite_false] using hxi⟩
  · rintro ⟨i, hi, hxi⟩
    refine ⟨i, hi, ?_⟩
    by_cases he : i = 0
    · subst i
      dsimp only [flatEntry]
      exact Or.inr ((D.entry_eq 0 hi) ▸ hxi).2
    · simpa only [flatEntry, he, ite_false] using hxi

theorem short_upset_extension (D : RunData K rank atoms W) {r : J → J → Prop}
    (hK : K.Upsets r) (hD : GlobalUpset r D.second)
    (hstrict : ∀ x y, r x y → rank x < rank y)
    (hrank : ∀ k, Described atoms (RankTail rank k) 1)
    (hfalse : Described atoms ∅ 1) (hcard : K.indices.card ≤ 5) :
    ∃ H : Set J, GlobalUpset r H ∧ Described atoms H 20 ∧
      ∀ x ∈ W, x ∈ H ↔ x ∈ K.Qual := by
  classical
  let H : Set J := {x | ∃ i ∈ K.indices, x ∈ D.flatEntry i}
  refine ⟨H, ?_, ?_, D.flat_union_agrees⟩
  · intro x y hxy hx
    obtain ⟨i, hi, hxi⟩ := hx
    refine ⟨i, hi, ?_⟩
    by_cases he : i = 0
    · subst i
      exact (hD.union (rankTail_upset hstrict _)) hxy hxi
    · simp only [flatEntry, he, ite_false] at hxi ⊢
      exact hK i hi hxy hxi
  · by_cases hne : K.indices.Nonempty
    · have hsmall : ∀ i ∈ K.indices, Described atoms (D.flatEntry i) 4 := by
        intro i hi
        by_cases he : i = 0
        · subst i
          exact (D.second_small.union (hrank _)).mono (by omega)
        · simp only [flatEntry, he, ite_false]
          rw [D.entry_eq i hi]
          exact ((D.simple i hi he).inter (hrank _)).mono (by omega)
      have hh := Described.finite_union K.indices D.flatEntry (fun _ => 4) hne hsmall
      apply hh.mono
      simp only [Finset.sum_const, smul_eq_mul]
      omega
    · have he : K.indices = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hH : H = ∅ := by ext x; simp [H, he]
      rw [hH]
      exact hfalse.mono (by omega)

end RunData
end RunCertificates
end ThreeMachine.Structure

namespace ThreeMachine.Structure
namespace GlobalList
variable {J : Type}

theorem pair_upsets {r : J → J → Prop} {A B : Set J}
    (hA : GlobalUpset r A) (hB : GlobalUpset r B) : (pair A B).Upsets r := by
  intro i _
  dsimp [pair]
  split <;> assumption

theorem InjectionDisjoint.carry {K : GlobalList J} {W : Set J} {rank : J → ℕ}
    (h : K.InjectionDisjoint W) (d k : ℕ) : (K.carry rank d k).InjectionDisjoint W := by
  intro i hi h2i j hj h2j hn x hx hxi hxj
  have hmi := (carry_membership K rank d k i x).mp
    ((mem_memberships _ x i).mpr ⟨hi, hxi⟩)
  have hmj := (carry_membership K rank d k j x).mp
    ((mem_memberships _ x j).mpr ⟨hj, hxj⟩)
  exact h i hmi.1 h2i j hmj.1 h2j hn x hx hmi.2.2.1 hmj.2.2.1

theorem InjectionDisjoint.append {K : GlobalList J} {W I : Set J}
    (h : K.InjectionDisjoint W) (hdisj : ∀ x ∈ W, x ∈ I → x ∉ K.Qual) :
    (K.append I).InjectionDisjoint W := by
  classical
  intro i hi h2i j hj h2j hn x hx hxi hxj
  have hmi := (append_membership K I i x).mp ((mem_memberships _ x i).mpr ⟨hi, hxi⟩)
  have hmj := (append_membership K I j x).mp ((mem_memberships _ x j).mpr ⟨hj, hxj⟩)
  rcases hmi with ⟨hi, hxi⟩ | ⟨hi, hxi⟩ <;>
    rcases hmj with ⟨hj, hxj⟩ | ⟨hj, hxj⟩
  · exact hn (hi.trans hj.symm)
  · exact hdisj x hx hxi ⟨j, hj, hxj⟩
  · exact hdisj x hx hxj ⟨i, hi, hxi⟩
  · exact h i hi h2i j hj h2j hn x hx hxi hxj

end GlobalList

namespace RunData
variable {J A : Type} {rank : J → ℕ} {atoms : A → Set J} {W : Set J}

end RunData
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section NumericWalk
variable {J : Type}

theorem priorityCut_prefix (W : Finset J) (priority : J → ℕ) (k : ℕ) :
    PrefixOn W priority (PriorityCut priority k) := by
  intro x _ hx y _ hy
  change priority x < k at hx
  change ¬priority y < k at hy
  omega

theorem priorityCut_ideal {W : Finset J} {r : J → J → Prop} {priority : J → ℕ}
    (hstrict : ∀ x ∈ W, ∀ y ∈ W, r x y → priority x < priority y) (k : ℕ) :
    IdealOn W r (PriorityCut priority k) := by
  intro x hx y hy hxy hlow
  exact (hstrict x hx y hy hxy).trans hlow

theorem numeric_shared_cutoff {W : Finset J} {r : J → J → Prop}
    {time priority : J → ℕ} {s k : ℕ}
    (htrans : ∀ ⦃a b c⦄, r a b → r b c → r a c)
    (hrespect : ∀ u v, r u v → time u < time v)
    (hclosed : SlotClosed W time) (hpos : AdmissiblePosition W time s)
    (hinj : Set.InjOn priority W)
    (hstrict : ∀ x ∈ W, ∀ y ∈ W, r x y → priority x < priority y)
    (hnorm : LocalObstruction W r time priority)
    (hsep : Separator W r time (PriorityCut priority k) s) :
    ∃ t, s ≤ t ∧ AdvancePath W r time (PriorityCut priority (k+1)) s t ∧
      Separator W r time (PriorityCut priority k) t ∧
      Separator W r time (PriorityCut priority (k+1)) t := by
  classical
  by_cases hex : ∃ x ∈ W, priority x = k
  · obtain ⟨x, hx, hxk⟩ := hex
    apply shared_cutoff (a := x) htrans hrespect hclosed hpos
      (priorityCut_ideal hstrict k) (priorityCut_ideal hstrict (k+1))
      (priorityCut_prefix W priority k) (priorityCut_prefix W priority (k+1)) ?_ hnorm hsep
    intro z hz
    change priority z < k+1 ↔ priority z < k ∨ z = x
    constructor
    · intro h
      by_cases hzk : priority z < k
      · exact Or.inl hzk
      · exact Or.inr (hinj hz hx (by omega))
    · rintro (h | rfl) <;> omega
  · have heq : ∀ z ∈ W, z ∈ PriorityCut priority k ↔ z ∈ PriorityCut priority (k+1) := by
      intro z hz
      have hne : priority z ≠ k := fun h => hex ⟨z, hz, h⟩
      change priority z < k ↔ priority z < k+1
      omega
    exact ⟨s, le_rfl, .refl s, hsep, (separator_congr heq).mp hsep⟩

theorem exists_numeric_walk {E : Finset J} {r : J → J → Prop}
    {time priority : J → ℕ} {a lo : ℕ}
    (htrans : ∀ ⦃u v w⦄, r u v → r v w → r u w)
    (hrespect : ∀ u v, r u v → time u < time v)
    (hclosed : SlotClosed E time) (hpos : AdmissiblePosition E time a)
    (hinj : Set.InjOn priority E)
    (hstrict : ∀ x ∈ E, ∀ y ∈ E, r x y → priority x < priority y)
    (hnorm : LocalObstruction E r time priority)
    (hstart : Separator E r time (PriorityCut priority lo) a) (count : ℕ) :
    Nonempty (NumericWalkData E r time priority a lo count) := by
  classical
  induction count with
  | zero =>
    refine ⟨⟨fun _ => a, rfl, fun _ => Or.inl rfl, ?_, ?_, fun i => Fin.elim0 i⟩⟩
    · intro i
      have he : i.val = 0 := by omega
      simpa only [he, Nat.add_zero] using hstart
    · intro _
      exact .refl
  | succ n ih =>
    obtain ⟨ih⟩ := ih
    let last : Fin (n+1) := Fin.last n
    have hlastpos : AdmissiblePosition E time (ih.position last) := by
      rcases ih.endpoint last with he | hm
      · simpa only [he] using hpos
      · exact Or.inl hm
    obtain ⟨t, _ht, hpath, hsep, hnext⟩ := numeric_shared_cutoff htrans hrespect hclosed
      hlastpos hinj hstrict hnorm (ih.separator last)
    let pos : Fin (n+2) → ℕ := Fin.lastCases t ih.position
    have hcast (i : Fin (n+1)) : pos i.castSucc = ih.position i := by simp [pos]
    have hend : pos (Fin.last (n+1)) = t := by simp [pos]
    refine ⟨{ position := pos, first := ?_, endpoint := ?_, separator := ?_, history := ?_, steps := ?_ }⟩
    · change pos (0 : Fin (n+1)).castSucc = a
      rw [hcast, ih.first]
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [hend]
        rcases hpath.endpoint with he | hm
        · rw [he]
          exact ih.endpoint last
        · exact Or.inr hm
      · rw [hcast]
        exact ih.endpoint j
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [hend]
        simpa only [last, Fin.val_last, Nat.add_assoc] using hnext
      · rw [hcast]
        exact ih.separator j
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [hend]
        apply CutoffWalk.trans_advance
          ((ih.history last).mono (fun z _ hz => show priority z < lo + (n+1) from by
            have : priority z < lo + n := hz; omega)) hpath
          (priorityCut_ideal hstrict _) (priorityCut_prefix E priority _) (fun _ _ hz => hz)
      · rw [hcast]
        exact ih.history j
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · change AdvancePath E r time (PriorityCut priority (lo+n+1))
          (pos (Fin.last n).castSucc) (pos (Fin.last (n+1))) ∧ _
        rw [hcast, hend]
        constructor
        · exact hpath
        · simpa only [Fin.succ_last, hend] using hsep
      · have hleft : pos j.castSucc.castSucc = ih.position j.castSucc := hcast _
        have hright : pos j.castSucc.succ = ih.position j.succ := by
          rw [Fin.succ_castSucc, hcast]
        simpa only [Fin.val_castSucc, hleft, hright] using ih.steps j

end NumericWalk
end ThreeMachine.Structure

end

end OAI
end

section
-- module PriorityUpdates
namespace OAI

section

namespace ThreeMachine.Structure
section PriorityEncoding
variable {J : Type}

theorem pairCode_lt {B i j rx ry : ℕ} (hx : rx < B) (hy : ry < B) :
    i * B + rx < j * B + ry ↔ i < j ∨ i = j ∧ rx < ry := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · have hm := Nat.mul_le_mul_right B (Nat.succ_le_of_lt hij)
    rw [Nat.succ_mul] at hm
    constructor
    · exact fun _ => Or.inl hij
    · omega
  · simp only [lt_self_iff_false, true_and, false_or, Nat.add_lt_add_iff_left]
  · have hm := Nat.mul_le_mul_right B (Nat.succ_le_of_lt hji)
    rw [Nat.succ_mul] at hm
    constructor
    · omega
    · rintro (h | ⟨h, _⟩) <;> omega

namespace GlobalList

theorem keyValue_lt_iff {K : GlobalList J} {rank : J → ℕ} {B : ℕ} {x y : J}
    (hx : rank x < B) (hy : rank y < B) :
    K.keyValue rank B x < K.keyValue rank B y ↔ K.KeyLT rank x y :=
  pairCode_lt hx hy

theorem keyValue_injective {K : GlobalList J} {rank : J → ℕ} {B : ℕ}
    (hrank : ∀ x, rank x < B) (hinj : Function.Injective rank) :
    Function.Injective (K.keyValue rank B) := by
  intro x y he
  apply hinj
  have hn1 : ¬K.KeyLT rank x y := by
    rw [← keyValue_lt_iff (hrank x) (hrank y), he]
    exact lt_irrefl _
  have hn2 : ¬K.KeyLT rank y x := by
    rw [← keyValue_lt_iff (hrank y) (hrank x), he]
    exact lt_irrefl _
  unfold KeyLT at hn1 hn2
  omega

theorem lastIndex_le_sup (K : GlobalList J) (x : J) :
    K.lastIndex x ≤ K.indices.sup id := by
  apply Finset.sup_le
  intro i hi
  exact Finset.le_sup (f := id) ((mem_memberships K x i).mp hi).1

theorem keyValue_bound {K : GlobalList J} {rank : J → ℕ} {B : ℕ}
    (hrank : ∀ x, rank x < B) (x : J) :
    K.keyValue rank B x < (K.indices.sup id + 1) * B := by
  have hm := Nat.mul_le_mul_right B (K.lastIndex_le_sup x)
  have hx := hrank x
  unfold keyValue
  rw [Nat.add_mul]
  simp only [one_mul]
  omega

theorem carryNumeric_selection {K : GlobalList J} {rank : J → ℕ} {B t : ℕ}
    (hB : 0 < B) (hrank : ∀ x, rank x < B) (x : J) :
    x ∈ (K.carry rank (t/B) (t%B)).Qual ↔
      x ∈ K.Qual ∧ t ≤ K.keyValue rank B x := by
  rw [carry_selection]
  have htmod : t % B < B := Nat.mod_lt _ hB
  have hdiv : t / B * B + t % B = t := by simpa only [Nat.mul_comm] using Nat.div_add_mod t B
  have hlt := pairCode_lt (hrank x) htmod (i := K.lastIndex x) (j := t/B)
  unfold keyValue
  rw [hdiv] at hlt
  constructor
  · rintro ⟨hx, hgt | ⟨he, hr⟩⟩
    · refine ⟨hx, ?_⟩
      by_contra hn
      rcases hlt.mp (by omega) with h | ⟨h, _⟩ <;> omega
    · exact ⟨hx, by omega⟩
  · rintro ⟨hx, ht⟩
    refine ⟨hx, ?_⟩
    by_cases he : K.lastIndex x = t/B
    · right
      refine ⟨he, ?_⟩
      rw [he] at ht
      omega
    · left
      by_contra hn
      have hless : K.lastIndex x < t/B := by omega
      have hcode := hlt.mpr (Or.inl hless)
      omega

theorem samePriority_injective {K : GlobalList J} {rank : J → ℕ} {B : ℕ} {P : Set J}
    (hrank : ∀ x, rank x < B) (hinj : Function.Injective rank) :
    Function.Injective (K.samePriority rank B P) := by
  classical
  intro x y he
  have hx := hrank x
  have hy := hrank y
  have hkx := K.keyValue_bound hrank x
  have hky := K.keyValue_bound hrank y
  by_cases hqx : x ∈ K.Qual
  · by_cases hqy : y ∈ K.Qual
    · simp only [samePriority, ite_eq_left hqx, ite_eq_left hqy] at he
      exact keyValue_injective hrank hinj (Nat.add_left_cancel he)
    · by_cases hpy : y ∈ P
      · simp only [samePriority, ite_eq_left hqx, ite_eq_right hqy, ite_eq_left hpy] at he
        omega
      · simp only [samePriority, ite_eq_left hqx, ite_eq_right hqy, ite_eq_right hpy] at he
        omega
  · by_cases hqy : y ∈ K.Qual
    · by_cases hpx : x ∈ P
      · simp only [samePriority, ite_eq_right hqx, ite_eq_left hqy, ite_eq_left hpx] at he
        omega
      · simp only [samePriority, ite_eq_right hqx, ite_eq_left hqy, ite_eq_right hpx] at he
        omega
    · by_cases hpx : x ∈ P <;> by_cases hpy : y ∈ P
      · simp only [samePriority, ite_eq_right hqx, ite_eq_right hqy, ite_eq_left hpx, ite_eq_left hpy] at he
        exact hinj he
      · simp only [samePriority, ite_eq_right hqx, ite_eq_right hqy, ite_eq_left hpx, ite_eq_right hpy] at he
        omega
      · simp only [samePriority, ite_eq_right hqx, ite_eq_right hqy, ite_eq_right hpx, ite_eq_left hpy] at he
        omega
      · simp only [samePriority, ite_eq_right hqx, ite_eq_right hqy, ite_eq_right hpx, ite_eq_right hpy] at he
        exact hinj (Nat.add_left_cancel he)

theorem samePriority_extends {K : GlobalList J} {rank : J → ℕ} {B : ℕ}
    {P W : Set J} {r : J → J → Prop}
    (hrank : ∀ x, rank x < B) (hstrict : ∀ x y, r x y → rank x < rank y)
    (hup : K.Upsets r) (hP : ∀ x y, r x y → y ∈ P → x ∈ P)
    (hqual : ∀ x ∈ W, x ∈ K.Qual → x ∈ P) :
    ∀ x ∈ W, ∀ y ∈ W, r x y → K.samePriority rank B P x < K.samePriority rank B P y := by
  classical
  intro x hx y hy hxy
  have hr := hstrict x y hxy
  have hrx := hrank x
  have hry := hrank y
  have hkx := K.keyValue_bound hrank x
  have hky := K.keyValue_bound hrank y
  by_cases hqx : x ∈ K.Qual
  · have hqy := K.qual_upset hup hxy hqx
    simp only [samePriority, ite_eq_left hqx, ite_eq_left hqy, Nat.add_lt_add_iff_left]
    exact (keyValue_lt_iff hrx hry).mpr (K.key_extends hup hstrict hqx hxy)
  · by_cases hqy : y ∈ K.Qual
    · have hpx := hP x y hxy (hqual y hy hqy)
      simp only [samePriority, ite_eq_right hqx, ite_eq_left hqy, ite_eq_left hpx]
      omega
    · by_cases hpy : y ∈ P
      · have hpx := hP x y hxy hpy
        simp only [samePriority, ite_eq_right hqx, ite_eq_right hqy, ite_eq_left hpx, ite_eq_left hpy]
        exact hr
      · by_cases hpx : x ∈ P
        · simp only [samePriority, ite_eq_right hqx, ite_eq_right hqy, ite_eq_right hpy, ite_eq_left hpx]
          omega
        · simp only [samePriority, ite_eq_right hqx, ite_eq_right hqy, ite_eq_right hpy, ite_eq_right hpx]
          omega

theorem samePriority_key {K : GlobalList J} {rank : J → ℕ} {B : ℕ} {P : Set J}
    (hrank : ∀ x, rank x < B) {x y : J} (hx : x ∈ K.Qual) (hy : y ∈ K.Qual) :
    K.samePriority rank B P x < K.samePriority rank B P y ↔ K.KeyLT rank x y := by
  classical
  simp only [samePriority, ite_eq_left hx, ite_eq_left hy, Nat.add_lt_add_iff_left]
  exact keyValue_lt_iff (hrank x) (hrank y)

theorem samePriority_cut {K : GlobalList J} {rank : J → ℕ} {B t : ℕ} {P W : Set J}
    (hB : 0 < B) (hrank : ∀ x, rank x < B)
    (hqual : ∀ x ∈ W, x ∈ K.Qual → x ∈ P)
    (ht : t ≤ (K.indices.sup id + 1) * B) :
    ∀ x ∈ W, x ∈ PriorityCut (K.samePriority rank B P) (B+t) ↔
      x ∈ P \ (K.carry rank (t/B) (t%B)).Qual := by
  classical
  intro x hx
  rw [Set.mem_sdiff, carryNumeric_selection hB hrank]
  change K.samePriority rank B P x < B+t ↔ x ∈ P ∧ ¬(x ∈ K.Qual ∧ _)
  by_cases hqx : x ∈ K.Qual
  · have hpx := hqual x hx hqx
    simp only [samePriority, hpx, hqx, ite_true, true_and]
    omega
  · by_cases hpx : x ∈ P
    · simp only [samePriority, hpx, hqx, ite_false, ite_true, false_and, not_false_eq_true,
        and_self, iff_true]
      have := hrank x
      omega
    · simp only [samePriority, hpx, hqx, ite_false, false_and, iff_false]
      omega

end GlobalList
end PriorityEncoding
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section SwitchedPriorities
variable {J : Type}

theorem switchPriority_injective {rank : J → ℕ} {B : ℕ} {D : Set J}
    (hrank : ∀ x, rank x < B) (hinj : Function.Injective rank) :
    Function.Injective (switchPriority rank B D) := by
  classical
  intro x y he
  have hx := hrank x
  have hy := hrank y
  by_cases hxD : x ∈ D <;> by_cases hyD : y ∈ D <;>
    simp only [switchPriority, hxD, hyD, ite_true, ite_false] at he
  · exact hinj (Nat.add_left_cancel he)
  · omega
  · omega
  · exact hinj he

theorem switchPriority_extends {r : J → J → Prop} {rank : J → ℕ} {B : ℕ} {D : Set J}
    (hrank : ∀ x, rank x < B) (hstrict : ∀ x y, r x y → rank x < rank y)
    (hup : GlobalUpset r D) :
    ∀ x y, r x y → switchPriority rank B D x < switchPriority rank B D y := by
  classical
  intro x y hxy
  have hlt := hstrict x y hxy
  by_cases hxD : x ∈ D
  · have hyD := hup hxy hxD
    simp only [switchPriority, ite_eq_left hxD, ite_eq_left hyD, Nat.add_lt_add_iff_left]
    exact hlt
  · by_cases hyD : y ∈ D
    · simp only [switchPriority, ite_eq_right hxD, ite_eq_left hyD]
      have := hrank x
      omega
    · simp only [switchPriority, ite_eq_right hxD, ite_eq_right hyD]
      exact hlt

theorem switchPriority_cut {rank : J → ℕ} {B t : ℕ} {D : Set J}
    (ht : t ≤ B) :
    PriorityCut (switchPriority rank B D) t = Dᶜ \ RankTail rank t := by
  classical
  ext x
  change (if x ∈ D then B + rank x else rank x) < t ↔ x ∉ D ∧ ¬t ≤ rank x
  by_cases hx : x ∈ D
  · simp only [hx, ite_true, not_true_eq_false, false_and, iff_false]
    omega
  · simp only [hx, ite_false, not_false_eq_true, true_and, not_le]

namespace GlobalList

theorem pair_lastIndex_right {A D : Set J} {x : J} (hx : x ∈ D) :
    (pair A D).lastIndex x = 1 := by
  have hx1 : x ∈ (pair A D).entry 1 := by simpa [pair] using hx
  apply le_antisymm
  · apply Finset.sup_le
    intro i hi
    have := ((mem_memberships (pair A D) x i).mp hi).1
    simp only [pair, Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with rfl | rfl <;> simp
  · exact le_lastIndex (by simp [pair]) hx1

theorem pair_lastIndex_left {A D : Set J} {x : J} (hx : x ∉ D) :
    (pair A D).lastIndex x = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply Finset.sup_le
  intro i hi
  obtain ⟨hi, hxi⟩ := (mem_memberships (pair A D) x i).mp hi
  simp only [pair, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · exact le_rfl
  · exact (hx (by simpa [pair] using hxi)).elim

theorem switchPair_agreement {rank : J → ℕ} {B t : ℕ} {W G D : Set J}
    (ht : t ≤ B) (hcover : ∀ x ∈ W, x ∉ D → x ∈ G) :
    ∀ x ∈ W, x ∈ (pair (G ∩ RankTail rank t) D).Qual ↔
      x ∉ PriorityCut (switchPriority rank B D) t := by
  rw [switchPriority_cut ht, qual_pair]
  intro x hx
  change (x ∈ G ∧ t ≤ rank x) ∨ x ∈ D ↔ ¬(x ∉ D ∧ ¬t ≤ rank x)
  by_cases hD : x ∈ D
  · simp [hD]
  · have hG := hcover x hx hD
    simp [hD, hG]

theorem switchPair_key {rank : J → ℕ} {B t : ℕ} {G D : Set J}
    (hrank : ∀ x, rank x < B) (x y : J) :
    (pair (G ∩ RankTail rank t) D).KeyLT rank x y ↔
      switchPriority rank B D x < switchPriority rank B D y := by
  classical
  have hx := hrank x
  have hy := hrank y
  unfold KeyLT
  by_cases hxD : x ∈ D <;> by_cases hyD : y ∈ D
  · rw [pair_lastIndex_right hxD, pair_lastIndex_right hyD]
    simp only [lt_self_iff_false, true_and, false_or, switchPriority, ite_eq_left hxD,
      ite_eq_left hyD, Nat.add_lt_add_iff_left]
  · rw [pair_lastIndex_right hxD, pair_lastIndex_left hyD]
    simp only [Nat.not_lt_zero, Nat.one_ne_zero, false_and, false_or, switchPriority,
      ite_eq_left hxD, ite_eq_right hyD, false_iff]
    omega
  · rw [pair_lastIndex_left hxD, pair_lastIndex_right hyD]
    simp only [Nat.zero_lt_one, true_or, switchPriority, ite_eq_right hxD, ite_eq_left hyD, true_iff]
    omega
  · rw [pair_lastIndex_left hxD, pair_lastIndex_left hyD]
    simp only [lt_self_iff_false, true_and, false_or, switchPriority, ite_eq_right hxD, ite_eq_right hyD]

end GlobalList
end SwitchedPriorities
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section ReverseSeeds
variable {J A : Type}

variable {r : J → J → Prop} {time : J → ℕ} {atoms : A → Set J}

variable [Fintype J]

end ReverseSeeds
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section DescriptionInterface
variable {J A : Type} {r : J → J → Prop} {rank : J → ℕ} {atoms : A → Set J}

namespace RunData
variable {K : GlobalList J} {W : Set J}

theorem carry_cutoff_small (D : RunData K rank atoms W) (hA : AtomSupport atoms r rank)
    (hcard : K.indices.card ≤ 5) (B : Boundary J) (d k : ℕ) :
    Described atoms (B.pred r \ (K.carry rank d k).Qual) 205 := by
  have hc : (K.carry rank d k).indices.card ≤ 5 := by
    exact (Finset.card_filter_le _ _).trans hcard
  exact ((hA.pred B).diff ((D.carry d k).qual_small hA hc)).mono (by omega)

theorem carry_low_extension (D : RunData K rank atoms W)
    (hA : AtomSupport atoms r rank) (hcard : K.indices.card ≤ 5)
    (hK : K.Upsets r) (hsecond : GlobalUpset r D.second)
    (hstrict : ∀ x y, r x y → rank x < rank y)
    (htrans : ∀ ⦃x y z⦄, r x y → r y z → r x z)
    (B : Boundary J) (d k : ℕ) :
    ∃ H : Set J, GlobalUpset (fun x y => r y x) H ∧ Described atoms H 21 ∧
      ∀ x ∈ W, x ∈ H ↔ x ∈ B.pred r \ (K.carry rank d k).Qual := by
  have hc : (K.carry rank d k).indices.card ≤ 5 :=
    (Finset.card_filter_le _ _).trans hcard
  obtain ⟨U, hUup, hUsmall, hUagree⟩ := (D.carry d k).short_upset_extension
    (GlobalList.carry_upsets hK hstrict) hsecond hstrict hA.rankTail hA.falsity hc
  refine ⟨B.pred r \ U, ?_, (hA.pred B).diff hUsmall, ?_⟩
  · intro x y hyx hx
    exact ⟨Boundary.pred_downset htrans B hyx hx.1, fun hyU => hx.2 (hUup hyx hyU)⟩
  · intro x hx
    simp only [Set.mem_sdiff, hUagree x hx]

end RunData

end DescriptionInterface
end ThreeMachine.Structure

namespace ThreeMachine.Structure
namespace GlobalList
section SameUpdate
variable {J : Type} {K : GlobalList J} {rank : J → ℕ}

theorem carry_qual_subset (K : GlobalList J) (rank : J → ℕ) (d k : ℕ) :
    (K.carry rank d k).Qual ⊆ K.Qual := by
  intro x hx
  exact ((carry_selection K rank d k x).mp hx).1

theorem sameUpdate_agreement {B t : ℕ} {W D P : Set J}
    (hB : 0 < B) (hrank : ∀ x, rank x < B)
    (hqual : ∀ x ∈ W, x ∈ K.Qual → x ∈ P)
    (hcover : ∀ x ∈ W, x ∈ D ∨ x ∈ P)
    (ht : t ≤ (K.indices.sup id + 1) * B) :
    ∀ x ∈ W, x ∈ (K.sameUpdate rank B t D P).Qual ↔
      x ∉ PriorityCut (K.samePriority rank B P) (B+t) := by
  intro x hx
  rw [samePriority_cut hB hrank hqual ht x hx]
  change x ∈ ((K.carry rank (t/B) (t%B)).append (D \ P)).Qual ↔ _
  rw [append_qual]
  have hc : x ∈ (K.carry rank (t/B) (t%B)).Qual → x ∈ P :=
    fun h => hqual x hx (carry_qual_subset K rank _ _ h)
  have hd := hcover x hx
  simp only [Set.mem_union, Set.mem_sdiff]
  tauto

theorem sameUpdate_disjoint {B t : ℕ} {W D P : Set J}
    (hdisj : K.InjectionDisjoint W)
    (hqual : ∀ x ∈ W, x ∈ K.Qual → x ∈ P) :
    (K.sameUpdate rank B t D P).InjectionDisjoint W := by
  apply (hdisj.carry _ _).append
  intro x hx hI hC
  exact hI.2 (hqual x hx (carry_qual_subset K rank _ _ hC))

theorem sameUpdate_upsets {B t : ℕ} {D P : Set J} {r : J → J → Prop}
    (hK : K.Upsets r) (hD : GlobalUpset r D)
    (hP : GlobalUpset (fun x y => r y x) P)
    (hstrict : ∀ x y, r x y → rank x < rank y) :
    (K.sameUpdate rank B t D P).Upsets r := by
  apply append_upsets (carry_upsets hK hstrict)
  intro x y hxy hx
  exact ⟨hD hxy hx.1, fun hyP => hx.2 (hP hxy hyP)⟩

theorem sameUpdate_key {B t : ℕ} {W D P : Set J}
    (hrank : ∀ x, rank x < B)
    (hqual : ∀ x ∈ W, x ∈ K.Qual → x ∈ P)
    {x y : J} (hxW : x ∈ W) (hyW : y ∈ W)
    (hx : x ∈ (K.sameUpdate rank B t D P).Qual)
    (hy : y ∈ (K.sameUpdate rank B t D P).Qual) :
    (K.sameUpdate rank B t D P).KeyLT rank x y ↔
      K.samePriority rank B P x < K.samePriority rank B P y := by
  classical
  let C := K.carry rank (t/B) (t%B)
  let I := D \ P
  change x ∈ (C.append I).Qual at hx
  change y ∈ (C.append I).Qual at hy
  change (C.append I).KeyLT rank x y ↔ _
  have hCx : x ∈ C.Qual → x ∈ K.Qual := fun hx => carry_qual_subset K rank _ _ hx
  have hCy : y ∈ C.Qual → y ∈ K.Qual := fun hy => carry_qual_subset K rank _ _ hy
  have hvx := K.keyValue_bound hrank x
  have hvy := K.keyValue_bound hrank y
  by_cases hxI : x ∈ I <;> by_cases hyI : y ∈ I
  · have hxP : x ∉ P := hxI.2
    have hyP : y ∉ P := hyI.2
    have hxK : x ∉ K.Qual := fun h => hxP (hqual x hxW h)
    have hyK : y ∉ K.Qual := fun h => hyP (hqual y hyW h)
    simp only [KeyLT, append_lastIndex_of_mem hxI, append_lastIndex_of_mem hyI,
      lt_self_iff_false, true_and, false_or, samePriority, ite_eq_right hxK, ite_eq_right hyK,
      ite_eq_right hxP, ite_eq_right hyP, Nat.add_lt_add_iff_left]
  · have hyC : y ∈ C.Qual := by rw [append_qual] at hy; exact hy.resolve_right hyI
    have hxP : x ∉ P := hxI.2
    have hxK : x ∉ K.Qual := fun h => hxP (hqual x hxW h)
    have hbefore := lt_nextIndex (lastIndex_mem hyC).1
    simp only [KeyLT, append_lastIndex_of_mem hxI, append_lastIndex_of_not_mem hyI,
      samePriority, ite_eq_right hxK, ite_eq_right hxP, ite_eq_left (hCy hyC)]
    constructor <;> intro h <;> omega
  · have hxC : x ∈ C.Qual := by rw [append_qual] at hx; exact hx.resolve_right hxI
    have hyP : y ∉ P := hyI.2
    have hyK : y ∉ K.Qual := fun h => hyP (hqual y hyW h)
    have hbefore := lt_nextIndex (lastIndex_mem hxC).1
    simp only [KeyLT, append_lastIndex_of_not_mem hxI, append_lastIndex_of_mem hyI,
      samePriority, ite_eq_left (hCx hxC), ite_eq_right hyK, ite_eq_right hyP]
    constructor
    · intro _
      omega
    · intro _
      exact Or.inl hbefore
  · have hxC : x ∈ C.Qual := by rw [append_qual] at hx; exact hx.resolve_right hxI
    have hyC : y ∈ C.Qual := by rw [append_qual] at hy; exact hy.resolve_right hyI
    rw [append_key_of_not_mem hxI hyI, carry_key hxC hyC]
    exact (samePriority_key hrank (hCx hxC) (hCy hyC)).symm

end SameUpdate
end GlobalList
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section SameBoundaryUpdate
variable {J : Type} [Fintype J] [DecidableEq J]

omit [Fintype J] [DecidableEq J] in
theorem Boundary.desc_eq_of_interior {r : J → J → Prop} {time : J → ℕ}
    {T a : ℕ} {A : Boundary J} (hA : A.At time T a) (ha : 1 ≤ a ∧ a ≤ T) :
    A.desc r = DescAt r time a := by
  cases A with
  | left => simp only [Boundary.At] at hA; omega
  | right => simp only [Boundary.At] at hA; omega
  | actual Z => exact Boundary.actual_desc_eq hA

theorem sameUpdate_past {r : J → J → Prop} {p : Layout J} {rank : J → ℕ}
    {a b v ap B t : ℕ} {A Z A' : Boundary J} {W : Set J} {E : Finset J}
    {K : GlobalList J}
    (hp : p.Full r) (htrans : ∀ ⦃x y z⦄, r x y → r y z → r x z)
    (hA : A.At p.time (Fintype.card J / 3) a)
    (hA' : A'.At p.time (Fintype.card J / 3) ap)
    (hW : ∀ x, x ∈ W ↔ x ∈ Window p.time a b)
    (hE : ∀ x, x ∈ E ↔ a < p.time x ∧ p.time x < v)
    (hv : v < b) (ha : a ≤ Fintype.card J / 3) (hap : ap < v)
    (hB : 0 < B) (hrank : ∀ x, rank x < B)
    (hstrict : ∀ x y, r x y → rank x < rank y)
    (hK : K.Upsets r)
    (hhigh : ∀ x ∈ W, x ∈ K.Qual → x ∈ Z.pred r)
    (hlow : ∀ x ∈ W, x ∉ K.Qual → x ∈ A.desc r)
    (hpast : PastInvariant r p.time K A a)
    (hswap : SwapInvariant r p W K rank A a)
    (ht : t ≤ (K.indices.sup id + 1) * B)
    (hnorm : LocalObstruction E r p.time (K.samePriority rank B (Z.pred r)))
    (hsep : A'.Separates r p.time E
      (PriorityCut (K.samePriority rank B (Z.pred r)) (B+t)) ap)
    (hwalk : CutoffWalk E r p.time (K.samePriority rank B (Z.pred r))
      (PriorityCut (K.samePriority rank B (Z.pred r)) (B+t)) a ap) :
    PastInvariant r p.time (K.sameUpdate rank B t (A.desc r) (Z.pred r)) A' ap := by
  let H := (K.carry rank (t/B) (t%B)).Qual
  have hEW : (E : Set J) ⊆ W := by
    intro x hx
    have hxE := (hE x).mp hx
    exact (hW x).mpr ⟨hxE.1, hxE.2.trans hv⟩
  have hcover : ∀ x ∈ W, x ∈ A.desc r ∨ x ∈ Z.pred r := by
    intro x hx
    by_cases hq : x ∈ K.Qual
    · exact Or.inr (hhigh x hx hq)
    · exact Or.inl (hlow x hx hq)
  have hagree := GlobalList.sameUpdate_agreement hB hrank hhigh hcover ht
  have hHhigh : ∀ x ∈ E, x ∈ H → x ∉ PriorityCut
      (K.samePriority rank B (Z.pred r)) (B+t) := by
    intro x hx hH hS
    have := (GlobalList.samePriority_cut hB hrank hhigh ht x (hEW hx)).mp hS
    exact this.2 hH
  apply past_update hp htrans hA hA' ha hap hE hpast
    (GlobalList.qual_upset (GlobalList.carry_upsets hK hstrict))
    (GlobalList.carry_qual_subset K rank (t/B) (t%B))
  · intro x hx hxa
    rw [GlobalList.sameUpdate, GlobalList.append_qual] at hx
    rcases hx with hx | hx
    · exact hx
    · have := Boundary.desc_time hp.2 (p.time_bounds hp.1) hA hx.1
      omega
  · intro x hx hq
    exact (hagree x (hEW hx)).mp hq
  · exact hHhigh
  · exact hsep
  · exact hnorm
  · intro U hUideal _hUpre hUsub x hx
    apply first_boundary_force htrans hp.2 hE hUideal hx
    intro y hy hya
    have habound : 1 ≤ a ∧ a ≤ Fintype.card J / 3 := hya ▸ p.time_bounds hp.1 y
    have hxD : x ∉ A.desc r := by
      rw [Boundary.desc_eq_of_interior hA habound]
      exact hx.not_desc
    have hxW : x ∈ W := hEW hx.mem
    have hxK : x ∈ K.Qual := by by_contra hn; exact hxD (hlow x hxW hn)
    have hyK : y ∈ K.Qual := GlobalList.carry_qual_subset K rank _ _ hy
    have hxS := hUsub x hx.mem hx.low
    have hyval : t ≤ K.keyValue rank B y :=
      ((GlobalList.carryNumeric_selection hB hrank y).mp hy).2
    have hpriority : K.samePriority rank B (Z.pred r) x <
        K.samePriority rank B (Z.pred r) y := by
      change K.samePriority rank B (Z.pred r) x < B+t at hxS
      have hypri : K.samePriority rank B (Z.pred r) y = B + K.keyValue rank B y := by
        simp only [GlobalList.samePriority, ite_eq_left hyK]
      rw [hypri]
      omega
    exact hswap p (Layout.FixedOutside.refl p W) hp.2 x hxW hxD y hya hyK
      ((GlobalList.samePriority_key hrank hxK hyK).mp hpriority)
  · exact hwalk

theorem sameUpdate_swap_inherited {r : J → J → Prop} {p : Layout J}
    {rank : J → ℕ} {K : GlobalList J} {W W' : Set J}
    {A Z : Boundary J} {a b B t : ℕ}
    (hp : p.Full r) (hA : A.At p.time (Fintype.card J / 3) a)
    (hW : ∀ x, x ∈ W ↔ x ∈ Window p.time a b) (hsub : W' ⊆ W)
    (hparent : SwapInvariant r p W K rank A a)
    (hqual : ∀ x ∈ W', x ∉ A.desc r →
      x ∈ (K.sameUpdate rank B t (A.desc r) (Z.pred r)).Qual) :
    SwapInvariant r p W' (K.sameUpdate rank B t (A.desc r) (Z.pred r)) rank A a := by
  intro q hfix hq x hx hnx y hy hyq hkey
  have hAq := (hfix.mono hsub).boundary hW (Or.inl le_rfl) hA
  have hyD : y ∉ A.desc r := by
    intro hD
    have := Boundary.desc_time hq (q.time_bounds hp.1) hAq hD
    omega
  have hxI : x ∉ A.desc r \ Z.pred r := fun h => hnx h.1
  have hyI : y ∉ A.desc r \ Z.pred r := fun h => hyD h.1
  have hxC : x ∈ (K.carry rank (t/B) (t%B)).Qual := by
    have h := hqual x hx hnx
    rw [GlobalList.sameUpdate, GlobalList.append_qual] at h
    exact h.resolve_right hxI
  have hyC : y ∈ (K.carry rank (t/B) (t%B)).Qual := by
    rw [GlobalList.sameUpdate, GlobalList.append_qual] at hyq
    exact hyq.resolve_right hyI
  have hkeyOld : K.KeyLT rank x y := by
    change ((K.carry rank (t/B) (t%B)).append (A.desc r \ Z.pred r)).KeyLT rank x y at hkey
    exact (GlobalList.carry_key hxC hyC).mp
      ((GlobalList.append_key_of_not_mem hxI hyI).mp hkey)
  exact hparent q (hfix.mono hsub) hq x (hsub hx) hnx y hy
    (GlobalList.carry_qual_subset K rank _ _ hyC) hkeyOld

end SameBoundaryUpdate
end ThreeMachine.Structure

end

end OAI
end

section
-- module NodeCertificates
namespace OAI

section

namespace ThreeMachine.Structure
section NodeCertificates
variable {J A : Type} [Fintype J] [DecidableEq J]

namespace NodeData
variable {r : J → J → Prop} {rank : J → ℕ} {atoms : A → Set J}
    {p q : Layout J} {W : Set J}

theorem cover (D : NodeData r rank atoms p W) :
    ∀ x ∈ W, x ∈ D.left.desc r ∨ x ∈ D.right.pred r := by
  intro x hx
  by_cases hq : x ∈ D.list.Qual
  · exact Or.inr (D.high x hx hq)
  · exact Or.inl (D.low x hx hq)

end NodeData

namespace EdgeData
variable {r : J → J → Prop} {rank : J → ℕ} {atoms : A → Set J}
    {p : Layout J} {W : Set J} {a b v ap bp : ℕ} {B V A' B' : Boundary J}

end EdgeData
end NodeCertificates
end ThreeMachine.Structure

namespace ThreeMachine.Structure
namespace Boundary
variable {J : Type} {time : J → ℕ} {T s : ℕ}

theorem at_le {B : Boundary J} (hB : B.At time T s) : s ≤ T+1 := by
  cases B with
  | left => simp only [At] at hB; omega
  | right => exact hB.le
  | actual Z => exact hB.2.1.trans (by omega)

theorem at_unique {B C : Boundary J} (hB : B.At time T s) (hC : C.At time T s) :
    B = C := by
  cases B <;> cases C <;> try rfl
  all_goals simp only [At] at hB hC
  all_goals try omega
  congr 1
  apply Subtype.ext
  ext x
  exact (hB.2.2 x).trans (hC.2.2 x).symm

end Boundary

section SameEdges
variable {J A : Type} [Fintype J] [DecidableEq J]
    {r : J → J → Prop} {rank : J → ℕ} {atoms : A → Set J}
    {p : Layout J} {W : Set J}

theorem exists_same_edge (D : NodeData r rank atoms p W)
    (htrans : ∀ ⦃x y z⦄, r x y → r y z → r x z)
    (hA : AtomSupport atoms r rank)
    {B t v ap bp : ℕ} {V A' B' : Boundary J}
    (hB : 0 < B) (hrank : ∀ x, rank x < B)
    (hstrict : ∀ x y, r x y → rank x < rank y)
    (hv : D.a < v ∧ v < D.b)
    (hV : V.At p.time (Fintype.card J / 3) v)
    (hcenter : V.Separates r p.time W (D.right.pred r) v)
    (hap : D.a ≤ ap) (hab : ap < bp) (hbp : bp ≤ v)
    (hA' : A'.At p.time (Fintype.card J / 3) ap)
    (hB' : B'.At p.time (Fintype.card J / 3) bp)
    (hactual : ∃ Z, B' = Boundary.actual Z)
    (ht : t ≤ (D.list.indices.sup id + 1) * B)
    (hnorm : p.NormalizedOn (Window p.time D.a v) r
      (D.list.samePriority rank B (D.right.pred r)))
    (hstart : A'.Separates r p.time (Window p.time D.a v)
      (PriorityCut (D.list.samePriority rank B (D.right.pred r)) (B+t)) ap)
    (hend : B'.Separates r p.time (Window p.time D.a v)
      (PriorityCut (D.list.samePriority rank B (D.right.pred r)) (B+t)) bp)
    (E : Finset J) (hEwin : ∀ x, x ∈ E ↔ x ∈ Window p.time D.a v)
    (hwalk : CutoffWalk E r p.time
      (D.list.samePriority rank B (D.right.pred r))
      (PriorityCut (D.list.samePriority rank B (D.right.pred r)) (B+t)) D.a ap) :
    Nonempty (EdgeData r rank atoms p W D.a D.b v ap bp D.right V A' B') := by
  classical
  let S := PriorityCut (D.list.samePriority rank B (D.right.pred r)) (B+t)
  let K' := D.list.sameUpdate rank B t (D.left.desc r) (D.right.pred r)
  let H := D.right.pred r \ (D.list.carry rank (t/B) (t%B)).Qual
  have hagree : ∀ x ∈ W, x ∈ S ↔ x ∈ H :=
    GlobalList.samePriority_cut hB hrank D.high ht
  have hlabels : ∀ x ∈ W, x ∈ K'.Qual ↔ x ∉ S :=
    GlobalList.sameUpdate_agreement hB hrank D.high D.cover ht
  have hsub : Window p.time ap bp ⊆ W := by
    intro x hx
    exact (D.window x).mpr ⟨hap.trans_lt hx.1, (hx.2.trans_le hbp).trans hv.2⟩
  have hE : Window p.time ap bp ⊆ Window p.time D.a v := by
    intro x hx
    exact ⟨hap.trans_lt hx.1, hx.2.trans_le hbp⟩
  have hqual : ∀ x ∈ Window p.time ap bp, x ∉ A'.desc r → x ∈ K'.Qual := by
    intro x hx hn
    apply (hlabels x (hsub hx)).mpr
    intro hS
    exact hn (hstart.2 x (hE hx) hx.1 hS)
  have hswap : SwapInvariant r p (Window p.time ap bp) K' rank A' ap := by
    rcases hap.eq_or_lt with he | hl
    · have hAA : A' = D.left := Boundary.at_unique hA' (he ▸ D.leftAt)
      subst ap
      subst A'
      exact sameUpdate_swap_inherited D.full D.leftAt D.window hsub D.swap hqual
    · apply swap_from_normalized (fun _ => Iff.rfl) (fun _ => Iff.rfl) hl hbp hab hnorm hqual
      intro x hx hxK y hya hyK hkey
      have hyW : y ∈ W := (D.window y).mpr ⟨by omega,
        by have := hv.2; omega⟩
      exact (GlobalList.sameUpdate_key hrank D.high (hsub hx) hyW hxK hyK).mp hkey
  have hapos : D.a ≤ Fintype.card J / 3 := by
    have := Boundary.at_le D.rightAt
    omega
  have hEeq : (↑E : Set J) = Window p.time D.a v := Set.ext hEwin
  have hpast : PastInvariant r p.time K' A' ap := by
    apply sameUpdate_past D.full htrans D.leftAt hA' D.window
      (E := E) hEwin
      hv.2 hapos (hab.trans_le hbp) hB hrank hstrict D.upsets D.high D.low
      D.past D.swap ht
    · apply normalizedOn_local_obstruction
      · simpa only [hEeq] using hnorm
      · exact hEwin
    · simpa only [hEeq] using hstart
    · exact hwalk
  obtain ⟨Hext, hHup, hHsmall, hHagree⟩ := D.run.carry_low_extension hA D.length
    D.upsets D.second_upset hstrict htrans D.right (t/B) (t%B)
  refine ⟨{
    full := D.full, parent := Set.ext D.window, endAt := D.rightAt
    centerAt := hV, startAt := hA', targetAt := hB', targetActual := hactual
    start_le := hap, strict := hab, target_le := hbp, center_lt := hv.2
    cutoff := S, finalCutoff := D.right.pred r, finalSmall := hA.pred D.right, centerSep := hcenter
    startSep := hstart, targetSep := hend
    covers := fun x hx hs => ((hagree x hx).mp hs).1
    below := fun x hx hs => ((hagree x hx).mp hs).1
    list := K', run := (D.run.carry (t/B) (t%B)).append
        (D.left.desc r \ D.right.pred r) ((hA.desc D.left).diff (hA.pred D.right))
    upsets := GlobalList.sameUpdate_upsets D.upsets
        (Boundary.desc_upset htrans D.left) (fun _ _ hxy hx => Boundary.pred_downset htrans D.right hxy hx) hstrict
    second_upset := D.second_upset
    disjoint := GlobalList.sameUpdate_disjoint D.disjoint D.high
    labels := hlabels, past := hpast, swap := hswap
    globalCutoff := H, cutoffSmall := D.run.carry_cutoff_small hA D.length D.right (t/B) (t%B)
    cutoffAgrees := fun x hx => (hagree x hx).symm
    lowExtension := Hext, downset := hHup, lowSmall := hHsmall
    lowAgrees := fun x hx => (hHagree x hx).trans (hagree x hx).symm }⟩

end SameEdges
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section SwitchedEdges
variable {J A : Type} [Fintype J] [DecidableEq J]

variable {r : J → J → Prop} {rank : J → ℕ} {atoms : A → Set J}
    {p : Layout J} {W : Set J}

theorem exists_switch_edge {a b v ap bp B t : ℕ} {L R V A' B' : Boundary J}
    (hp : p.Full r) (htrans : ∀ ⦃x y z⦄, r x y → r y z → r x z)
    (hA : AtomSupport atoms r rank) (hrank : ∀ x, rank x < B)
    (hstrict : ∀ x y, r x y → rank x < rank y)
    (hW : ∀ x, x ∈ W ↔ x ∈ Window p.time a b)
    (hL : L.At p.time (Fintype.card J / 3) a)
    (hR : R.At p.time (Fintype.card J / 3) b)
    (hcover : ∀ x ∈ W, x ∈ L.desc r ∨ x ∈ R.pred r)
    (G : SwitchSeed r p.time atoms W L a)
    (hv : a < v ∧ v < b) (hV : V.At p.time (Fintype.card J / 3) v)
    (hcenter : V.Separates r p.time W (L.desc r)ᶜ v)
    (hap : a ≤ ap) (hab : ap < bp) (hbp : bp ≤ v)
    (hA' : A'.At p.time (Fintype.card J / 3) ap)
    (hB' : B'.At p.time (Fintype.card J / 3) bp)
    (hactual : ∃ Z, B' = Boundary.actual Z) (ht : t ≤ B)
    (hnorm : p.NormalizedOn (Window p.time a v) r (switchPriority rank B (L.desc r)))
    (hstart : A'.Separates r p.time (Window p.time a v)
      (PriorityCut (switchPriority rank B (L.desc r)) t) ap)
    (hend : B'.Separates r p.time (Window p.time a v)
      (PriorityCut (switchPriority rank B (L.desc r)) t) bp) :
    Nonempty (EdgeData r rank atoms p W a b v ap bp R V A' B') := by
  classical
  let S := PriorityCut (switchPriority rank B (L.desc r)) t
  let K' := GlobalList.pair (G.predicate ∩ RankTail rank t) (L.desc r)
  have hlabels : ∀ x ∈ W, x ∈ K'.Qual ↔ x ∉ S :=
    GlobalList.switchPair_agreement ht G.cover
  have hcut : S = (L.desc r)ᶜ \ RankTail rank t := switchPriority_cut ht
  have hsup : GlobalUpset r (L.desc r) := Boundary.desc_upset htrans L
  have hK : K'.Upsets r := GlobalList.pair_upsets
    (fun _ _ hxy hx => ⟨G.upset hxy hx.1, rankTail_upset hstrict t hxy hx.2⟩) hsup
  have hnonearly : ∀ x ∈ K'.Qual, a < p.time x := by
    intro x hx
    rw [GlobalList.qual_pair] at hx
    rcases hx with hx | hx
    · exact G.later x hx.1
    · exact Boundary.desc_time hp.2 (p.time_bounds hp.1) hL hx
  have hsub : Window p.time ap bp ⊆ W := by
    intro x hx
    exact (hW x).mpr ⟨hap.trans_lt hx.1, (hx.2.trans_le hbp).trans hv.2⟩
  have hE : Window p.time ap bp ⊆ Window p.time a v := by
    intro x hx
    exact ⟨hap.trans_lt hx.1, hx.2.trans_le hbp⟩
  have hqual : ∀ x ∈ Window p.time ap bp, x ∉ A'.desc r → x ∈ K'.Qual := by
    intro x hx hn
    apply (hlabels x (hsub hx)).mpr
    intro hS
    exact hn (hstart.2 x (hE hx) hx.1 hS)
  have hpast : PastInvariant r p.time K' A' ap := by
    intro x hx ht'
    have hax := hnonearly x hx
    have hxE : x ∈ Window p.time a v := ⟨hax, ht'.trans_lt (hab.trans_le hbp)⟩
    rcases ht'.eq_or_lt with he | hl
    · exact (Boundary.mem_weak_at_time (p.time_bounds hp.1) hA' he).1
    · have hxW : x ∈ W := (hW x).mpr ⟨hax, hxE.2.trans hv.2⟩
      exact A'.pred_subset_weakPred r (hstart.1 x hxE hl ((hlabels x hxW).mp hx))
  have hswap : SwapInvariant r p (Window p.time ap bp) K' rank A' ap := by
    rcases hap.eq_or_lt with he | hl
    · intro q hfix _ x _ _ y hy hyK
      have hnW : y ∉ Window p.time ap bp := by
        intro hyW
        have h := (hfix.window (fun _ => Iff.rfl) y).mp hyW
        have := h.1
        omega
      have hya : p.time y = a := by rw [← hfix.time hnW, hy]; omega
      have := hnonearly y hyK
      omega
    · apply swap_from_normalized (fun _ => Iff.rfl) (fun _ => Iff.rfl) hl hbp hab hnorm hqual
      intro x _ _ y _ _ hkey
      exact (GlobalList.switchPair_key hrank x y).mp hkey
  have hSsmall : Described atoms S 2 := by
    rw [hcut]
    exact (hA.desc L).compl.diff (hA.rankTail t)
  have hSdown : GlobalUpset (fun x y => r y x) S := by
    rw [hcut]
    intro x y hyx hx
    exact ⟨fun hyD => hx.1 (hsup hyx hyD), fun hyr =>
      hx.2 (rankTail_upset hstrict t hyx hyr)⟩
  refine ⟨{
    full := hp, parent := Set.ext hW, endAt := hR, centerAt := hV
    startAt := hA', targetAt := hB', targetActual := hactual
    start_le := hap, strict := hab, target_le := hbp, center_lt := hv.2
    cutoff := S, finalCutoff := (L.desc r)ᶜ, finalSmall := (hA.desc L).compl, centerSep := hcenter
    startSep := hstart, targetSep := hend, covers := ?_, below := ?_
    list := K', run := RunData.switched G.small (hA.desc L) G.cover t
    upsets := hK, second_upset := hsup, disjoint := ?_, labels := hlabels
    past := hpast, swap := hswap, globalCutoff := S
    cutoffSmall := hSsmall.mono (by omega), cutoffAgrees := fun _ _ => Iff.rfl
    lowExtension := S, downset := hSdown, lowSmall := hSsmall.mono (by omega)
    lowAgrees := fun _ _ => Iff.rfl }⟩
  · intro x hx hS
    rw [hcut] at hS
    exact (hcover x hx).resolve_left hS.1
  · intro x _ hS
    rw [hcut] at hS
    exact hS.1
  · intro i hi h2i
    simp only [K', GlobalList.pair, Finset.mem_insert, Finset.mem_singleton] at hi
    omega

end SwitchedEdges
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section Centers
variable {J A : Type} [Fintype J] [DecidableEq J]
    {r : J → J → Prop} {rank : J → ℕ} {atoms : A → Set J}
    {p q : Layout J} {W : Set J}

omit [DecidableEq J] in

theorem window_first_slot {a b : ℕ} (hp : p.Full r)
    (hne : (Window p.time a b).Nonempty) :
    ∃ x ∈ Window p.time a b, p.time x = a+1 := by
  obtain ⟨y, hy⟩ := hne
  change a < p.time y ∧ p.time y < b at hy
  have hybound := p.time_bounds hp.1 y
  have hb : a+1 ≤ Fintype.card J / 3 := by omega
  have hc := p.card_slot hp.1 (a+1) (by omega) hb
  have hn : (p.slot (a+1)).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hx⟩ := hn
  have hx' := (p.mem_slot (a+1) x).mp hx
  exact ⟨x, ⟨by omega, by omega⟩, hx'⟩

theorem exists_node_center (D : NodeData r rank atoms p W)
    (htrans : ∀ ⦃x y z⦄, r x y → r y z → r x z) (hne : W.Nonempty) :
    ∃ q : Layout J, ∃ _hfix : p.FixedOutside q W, q.Respects r ∧
      ∃ (v : ℕ) (V : Boundary J), D.a < v ∧ v < D.b ∧
        V.At q.time (Fintype.card J / 3) v ∧
        V.Separates r q.time W (D.right.pred r) v := by
  classical
  let priority := fun x : J => if x ∈ D.right.pred r then (p x).val
    else Fintype.card J + (p x).val
  obtain ⟨q, hfix, hnorm⟩ := exists_normalizedOn p W r priority D.full.2
  let Dq := D.reorder hfix hnorm.1
  have hwindow : ∀ x, x ∈ W ↔ x ∈ Window q.time D.a D.b := Dq.window
  let E := W.toFinset
  have hE : ∀ x, x ∈ E ↔ x ∈ W := by intro x; simp [E]
  have hEeq : (↑E : Set J) = W := Set.ext hE
  have hclosed : SlotClosed E q.time := by
    intro x hx y hxy
    apply (hE y).mpr
    have h := (hwindow x).mp ((hE x).mp hx)
    exact (hwindow y).mpr (by simpa only [Window, Set.mem_ofPred, ← hxy] using h)
  have hideal : IdealOn E r (D.right.pred r) := by
    intro x _ y _ hxy hy
    exact Boundary.pred_downset htrans D.right hxy hy
  have hprefix : PrefixOn E priority (D.right.pred r) := by
    intro x _ hx y _ hy
    simp only [priority, ite_eq_left hx, ite_eq_right hy]
    have := (p x).isLt
    omega
  have hne' : (Window q.time D.a D.b).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, (hwindow x).mp hx⟩
  obtain ⟨x, hx, hxa⟩ := window_first_slot Dq.full hne'
  have hnormE : LocalObstruction E r q.time priority := by
    apply normalizedOn_local_obstruction
    · simpa only [hEeq] using hnorm
    · intro x
      exact (hE x).trans (hwindow x)
  have hfirst : EarlierHigh E r q.time (D.right.pred r) (D.a+1) := by
    intro x hx htime _
    have := ((hwindow x).mp ((hE x).mp hx)).1
    omega
  obtain ⟨v, _, hpath, hsep⟩ := walk_to_separator htrans hnorm.1 hclosed
    (Or.inl ⟨x, (hE x).mpr ((hwindow x).mpr hx), hxa⟩) hideal hprefix hnormE hfirst
  have hv : ∃ z ∈ W, q.time z = v := by
    rcases hpath.endpoint with he | ⟨z, hz, he⟩
    · exact ⟨x, (hwindow x).mpr hx, hxa.trans he.symm⟩
    · exact ⟨z, (hE z).mp hz, he⟩
  obtain ⟨z, hz, hzv⟩ := hv
  have hvwin := (hwindow z).mp hz
  have hvlo := hvwin.1
  have hvhi := hvwin.2
  have hvbound := q.time_bounds D.full.1 z
  have hva : D.a < v := by omega
  have hvb : v < D.b := by omega
  have hvpos : 1 ≤ v := by omega
  have hvle : v ≤ Fintype.card J / 3 := by omega
  let V := Boundary.actual (q.triple D.full.1 v hvpos hvle)
  have hV : V.At q.time (Fintype.card J / 3) v := q.triple_at D.full.1 v hvpos hvle
  refine ⟨q, hfix, hnorm.1, v, V, hva, hvb, hV, ?_⟩
  simpa only [hEeq] using (Boundary.actual_separates hV).mpr hsep

omit [DecidableEq J] in

theorem Layout.FixedOutside.before_iff {U : Set J} {a b s : ℕ}
    (hfix : p.FixedOutside q U) (hU : ∀ x, x ∈ U ↔ x ∈ Window p.time a b)
    (hs : s ≤ a ∨ b ≤ s) (x : J) : p.time x < s ↔ q.time x < s := by
  by_cases hx : x ∈ U
  · have hp := (hU x).mp hx
    have hq := (hfix.window hU x).mp hx
    rcases hs with hs | hs <;> dsimp [Window] at hp hq <;> omega
  · rw [hfix.time hx]

omit [DecidableEq J] in
theorem Layout.FixedOutside.after_iff {U : Set J} {a b s : ℕ}
    (hfix : p.FixedOutside q U) (hU : ∀ x, x ∈ U ↔ x ∈ Window p.time a b)
    (hs : s ≤ a ∨ b ≤ s) (x : J) : s < p.time x ↔ s < q.time x := by
  by_cases hx : x ∈ U
  · have hp := (hU x).mp hx
    have hq := (hfix.window hU x).mp hx
    rcases hs with hs | hs <;> dsimp [Window] at hp hq <;> omega
  · rw [hfix.time hx]

omit [DecidableEq J] in
theorem Boundary.Separates.reorder {U S : Set J} {a b s : ℕ} {V : Boundary J}
    (hsep : V.Separates r p.time W S s) (hfix : p.FixedOutside q U)
    (hU : ∀ x, x ∈ U ↔ x ∈ Window p.time a b) (hs : s ≤ a ∨ b ≤ s) :
    V.Separates r q.time W S s := by
  constructor
  · intro x hx htime hn
    exact hsep.1 x hx ((hfix.before_iff hU hs x).mpr htime) hn
  · intro x hx htime hS
    exact hsep.2 x hx ((hfix.after_iff hU hs x).mpr htime) hS

end Centers
end ThreeMachine.Structure

end

end OAI
end

section
-- module SplitPaths
namespace OAI

section

namespace ThreeMachine.Structure
section SplitGraph
variable {J A : Type}

namespace SplitVertex
variable {r : J → J → Prop} {atoms : A → Set J} {W : Set J}

theorem AtTime.unique {u v : SplitVertex r atoms W} {time : J → ℕ} {s : ℕ}
    (hu : u.AtTime time s) (hv : v.AtTime time s) : u = v := by
  apply ext
  · exact Set.ext (fun x => (hu.1 x).trans (hv.1 x).symm)
  · apply Subtype.ext
    exact Finset.ext (fun x => (hu.2.1 x).trans (hv.2.1 x).symm)
  · exact Set.ext (fun x => (hu.2.2 x).trans (hv.2.2 x).symm)

theorem middle_subset (v : SplitVertex r atoms W) : (v.middle.val : Set J) ⊆ W :=
  fun x hx => (v.partition x).mpr (Or.inr (Or.inl hx))

theorem gap_reverse {u v : SplitVertex r atoms W}
    (_huv : u.left ∪ u.middle.val ⊆ v.left) :
    u.right \ (v.middle.val ∪ v.right) = v.left \ (u.left ∪ u.middle.val) := by
  rw [u.right_eq, v.right_eq]
  have hvm := Set.disjoint_left.mp v.left_middle
  ext x
  constructor
  · rintro ⟨⟨hxW, hnu⟩, hnv⟩
    have hxv : x ∈ v.left := by
      by_contra hn
      exact hnv (Or.inr ⟨hxW, fun h => h.elim hn (fun hm => hnv (Or.inl hm))⟩)
    exact ⟨hxv, hnu⟩
  · rintro ⟨hxv, hnu⟩
    refine ⟨⟨v.left_subset hxv, hnu⟩, ?_⟩
    rintro (hm | ⟨_, hn⟩)
    · exact hvm hxv hm
    · exact hn (Or.inl hxv)

theorem step_reverse {P Q : Set J → Prop} {u v : SplitVertex r atoms W}
    (hPQ : ∀ X, P X → Q X) (h : Step P u v) : Step Q v.reverse u.reverse := by
  refine ⟨?_, ?_⟩
  · intro x hx
    change x ∈ u.right
    rw [u.right_eq]
    have hxW : x ∈ W := hx.elim (fun hx => v.right_subset hx) (fun hx => v.middle_subset hx)
    refine ⟨hxW, ?_⟩
    intro hu
    have hvl := h.1 hu
    exact hx.elim (fun hv => Set.disjoint_left.mp v.left_right hvl hv)
      (fun hv => Set.disjoint_left.mp v.left_middle hvl hv)
  · change Q (u.right \ (v.right ∪ v.middle.val))
    rw [Set.union_comm v.right, gap_reverse h.1]
    exact hPQ _ h.2

theorem path_reverse {P Q : Set J → Prop} (hPQ : ∀ X, P X → Q X)
    {u v : SplitVertex r atoms W} (h : Relation.ReflTransGen (Step P) u v) :
    Relation.ReflTransGen (Step Q) v.reverse u.reverse := by
  induction h with
  | refl => exact .refl
  | tail h hs ih => exact (Relation.ReflTransGen.single (step_reverse hPQ hs)).trans ih

end SplitVertex

namespace AcceptedAt
variable {r : J → J → Prop} {atoms : A → Set J}

theorem reverse {n : ℕ} {W : Set J} (h : AcceptedAt r atoms n W) :
    AcceptedAt (fun x y => r y x) atoms n W := by
  induction n generalizing W with
  | zero => exact h
  | succ n ih =>
    refine ⟨h.1, ?_⟩
    rcases h.2 with he | ⟨u, v, hu, hp, hv⟩
    · exact Or.inl he
    · exact Or.inr ⟨v.reverse, u.reverse, ih hv,
        SplitVertex.path_reverse (fun _ => ih) hp, ih hu⟩

end AcceptedAt
end SplitGraph
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section TemporalSplits
variable {J A : Type} [Fintype J] {r : J → J → Prop} {rank : J → ℕ}
    {atoms : A → Set J} {p q : Layout J} {W : Set J}

theorem SplitVertex.ofTime_at {a b s k : ℕ} {Z : Triple J} {F : Set J}
    (hp : p.Full r) (hW : ∀ x, x ∈ W ↔ x ∈ Window p.time a b)
    (hs : a < s ∧ s < b) (hZ : (Boundary.actual Z).At p.time (Fintype.card J / 3) s)
    (hF : Described atoms F k) (hk : k+1 ≤ 10000)
    (hZA : Described atoms (Z.val : Set J) 1)
    (hbefore : ∀ x ∈ W, x ∈ F ↔ p.time x < s) :
    (ofTime hp hW hs hZ hF hk hZA hbefore).AtTime p.time s := by
  refine ⟨fun _ => Iff.rfl, ?_, fun _ => Iff.rfl⟩
  intro x
  change x ∈ Z.val ↔ x ∈ W ∧ p.time x = s
  rw [hZ.2.2 x]
  exact ⟨fun hx => ⟨(hW x).mpr ⟨by omega, by omega⟩, hx⟩, And.right⟩

theorem EdgeData.targetVertex_at [DecidableEq J]
    {a b v ap bp : ℕ} {B V A' B' : Boundary J}
    (D : EdgeData r rank atoms p W a b v ap bp B V A' B')
    (hA : AtomSupport atoms r rank) (hFinal : Described atoms D.finalCutoff 1) :
    (D.targetVertex hA hFinal).AtTime p.time bp := by
  unfold targetVertex
  exact SplitVertex.ofTime_at _ _ _ _ _ _ _ _

end TemporalSplits
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section PrefixPaths
variable {J A : Type} [Fintype J] {r : J → J → Prop} {rank : J → ℕ}
    {atoms : A → Set J} {p q : Layout J} {W : Set J} {P : Set J → Prop}

omit [Fintype J] in
theorem SplitVertex.AtTime.congr {u : SplitVertex r atoms W} {f g : J → ℕ} {s : ℕ}
    (h : u.AtTime f s) (hbefore : ∀ x, f x < s ↔ g x < s)
    (hafter : ∀ x, s < f x ↔ s < g x) : u.AtTime g s := by
  refine ⟨fun x => (h.1 x).trans (and_congr_right fun _ => hbefore x), ?_,
    fun x => (h.2.2 x).trans (and_congr_right fun _ => hafter x)⟩
  intro x
  rw [h.2.1 x]
  have hb := hbefore x
  have ha := hafter x
  apply and_congr_right
  intro _
  omega

theorem EdgeData.reached [DecidableEq J]
    {a b v ap bp : ℕ} {B V A' B' : Boundary J}
    (D : EdgeData r rank atoms p W a b v ap bp B V A' B')
    (hA : AtomSupport atoms r rank) (hFinal : Described atoms D.finalCutoff 1)
    (hprev : Reached P r atoms W p.time a ap)
    (hgap : P (Window p.time ap bp)) : Reached P r atoms W p.time a bp := by
  let w := D.targetVertex hA hFinal
  have hw : w.AtTime p.time bp := D.targetVertex_at hA hFinal
  have hW : ∀ x, x ∈ W ↔ x ∈ Window p.time a b := by intro x; rw [D.parent]
  right
  rcases hprev with he | ⟨u, z, hu, hp, hz⟩
  · have hleft : w.left = Window p.time ap bp := by
      ext x
      rw [hw.1 x, hW x]
      change ((a < p.time x ∧ p.time x < b) ∧ p.time x < bp) ↔
        ap < p.time x ∧ p.time x < bp
      have := D.target_le
      have := D.center_lt
      omega
    exact ⟨w, w, hleft.symm ▸ hgap, .refl, hw⟩
  · have hzW : z.left ∪ z.middle.val ⊆ w.left := by
      intro x hx
      rw [hw.1 x]
      rcases hx with hl | hm
      · have := (hz.1 x).mp hl
        exact ⟨this.1, this.2.trans D.strict⟩
      · have := (hz.2.1 x).mp hm
        exact ⟨this.1, this.2 ▸ D.strict⟩
    have hgapEq : w.left \ (z.left ∪ z.middle.val) = Window p.time ap bp := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_union, Finset.mem_coe, hw.1 x, hz.1 x, hz.2.1 x]
      rw [hW x]
      change (((a < p.time x ∧ p.time x < b) ∧ p.time x < bp) ∧
        ¬(((a < p.time x ∧ p.time x < b) ∧ p.time x < ap) ∨
          ((a < p.time x ∧ p.time x < b) ∧ p.time x = ap))) ↔
          ap < p.time x ∧ p.time x < bp
      have := D.start_le
      have := D.target_le
      have := D.center_lt
      omega
    exact ⟨u, w, hu, hp.tail ⟨hzW, hgapEq.symm ▸ hgap⟩, hw⟩

omit [Fintype J] in
theorem Reached.congr_time {f g : J → ℕ} {a s : ℕ}
    (h : Reached P r atoms W f a s) (hbefore : ∀ x, f x < s ↔ g x < s)
    (hafter : ∀ x, s < f x ↔ s < g x) : Reached P r atoms W g a s := by
  rcases h with he | ⟨u, v, hu, hp, hv⟩
  · exact Or.inl he
  · exact Or.inr ⟨u, v, hu, hp, hv.congr hbefore hafter⟩

end PrefixPaths
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section WalkPaths
variable {J A : Type} [Fintype J] {r : J → J → Prop} {rank : J → ℕ}
    {atoms : A → Set J} {p : Layout J} {W : Set J} {P : Set J → Prop}

omit [Fintype J] in
theorem NumericWalkData.reached {E : Finset J} {time priority : J → ℕ} {a lo count v : ℕ}
    (D : NumericWalkData E r time priority a lo count)
    (hpos : ∀ i, D.position i < v)
    (happly : ∀ (i : Fin (count+1)) (bp : ℕ), D.position i < bp → bp ≤ v →
      Separator E r time (PriorityCut priority (lo+i.val)) bp →
      Reached P r atoms W time a (D.position i) → Reached P r atoms W time a bp)
    (hfinal : Separator E r time (PriorityCut priority (lo+count)) v) :
    Reached P r atoms W time a v := by
  have hreach : ∀ i, Reached P r atoms W time a (D.position i) := by
    intro i
    induction i using Fin.induction with
    | zero => rw [D.first]; exact Or.inl rfl
    | succ i ih =>
      have hle := (D.steps i).1.le
      rcases hle.eq_or_lt with he | hl
      · exact he ▸ ih
      · exact happly i.castSucc (D.position i.succ) hl (hpos i.succ).le (D.steps i).2 ih
  exact happly (Fin.last count) v (hpos _) le_rfl hfinal (hreach _)

theorem separator_at {E : Finset J} {S : Set J} {s a v : ℕ}
    (hp : p.Full r) (hE : ∀ x, x ∈ E ↔ x ∈ Window p.time a v)
    (hs : 1 ≤ s ∧ s ≤ Fintype.card J / 3)
    (hsep : Separator E r p.time S s) :
    (Boundary.actual (p.triple hp.1 s hs.1 hs.2)).Separates r p.time
      (Window p.time a v) S s := by
  have heq : (↑E : Set J) = Window p.time a v := Set.ext hE
  rw [← heq]
  exact (Boundary.actual_separates (p.triple_at hp.1 s hs.1 hs.2)).mpr hsep

omit [Fintype J] in
theorem Boundary.Separates.mono_domain {time : J → ℕ} {U S : Set J} {B : Boundary J} {s : ℕ}
    (h : B.Separates r time W S s) (hUW : U ⊆ W) : B.Separates r time U S s :=
  ⟨fun x hx ht hn => h.1 x (hUW hx) ht hn, fun x hx ht hs => h.2 x (hUW hx) ht hs⟩

theorem Boundary.at_bounds {B : Boundary J} {s : ℕ}
    (h : B.At p.time (Fintype.card J / 3) s) : s ≤ Fintype.card J / 3 + 1 := by
  cases B with
  | left => dsimp [At] at h; omega
  | right => exact h.le
  | actual Z => exact h.2.1.trans (Nat.le_succ _)

theorem Boundary.actual_of_interior {B : Boundary J} {s : ℕ}
    (h : B.At p.time (Fintype.card J / 3) s)
    (hs : 1 ≤ s ∧ s ≤ Fintype.card J / 3) : ∃ Z, B = Boundary.actual Z := by
  cases B with
  | left => dsimp [At] at h; omega
  | right => dsimp [At] at h; omega
  | actual Z => exact ⟨Z, rfl⟩

end WalkPaths
end ThreeMachine.Structure

end

end OAI
end

section
-- module HierarchyCompleteness
namespace OAI

section

namespace ThreeMachine.Structure
section SamePaths
variable {J A : Type} [Fintype J] [DecidableEq J]
    {r : J → J → Prop} {rank : J → ℕ} {atoms : A → Set J}
    {p : Layout J} {W : Set J} {P : Set J → Prop}

theorem EdgeData.child_ssubset {a b v ap bp : ℕ} {B V A' B' : Boundary J}
    (D : EdgeData r rank atoms p W a b v ap bp B V A' B') :
    Window p.time ap bp ⊂ W := by
  have hsub : Window p.time ap bp ⊆ W := by
    intro x hx
    rw [D.parent]
    exact ⟨D.start_le.trans_lt hx.1, (hx.2.trans_le D.target_le).trans D.center_lt⟩
  have hv : 1 ≤ v ∧ v ≤ Fintype.card J / 3 := by
    have := Boundary.at_bounds D.endAt
    have := D.start_le
    have := D.strict
    have := D.target_le
    have := D.center_lt
    omega
  have hc := p.card_slot D.full.1 v hv.1 hv.2
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < (p.slot v).card by omega)
  have ht := (p.mem_slot v x).mp hx
  have hxW : x ∈ W := by
    rw [D.parent]
    exact ⟨by have := D.start_le; have := D.strict; have := D.target_le; omega,
      ht ▸ D.center_lt⟩
  refine Set.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
  intro he
  have hh : ap < p.time x ∧ p.time x < bp :=
    show x ∈ Window p.time ap bp from he.symm ▸ hxW
  have := D.target_le
  omega

omit [Fintype J] [DecidableEq J] in
theorem GlobalList.samePriority_final {K : GlobalList J} {B : ℕ} {Q : Set J}
    (hrank : ∀ x, rank x < B) (hhigh : ∀ x ∈ W, x ∈ K.Qual → x ∈ Q) :
    ∀ x ∈ W, x ∈ PriorityCut (K.samePriority rank B Q)
      (B + (K.indices.sup id + 1)*B) ↔ x ∈ Q := by
  classical
  intro x hx
  have hr := hrank x
  have hk := K.keyValue_bound hrank x
  change K.samePriority rank B Q x < B + (K.indices.sup id + 1)*B ↔ x ∈ Q
  by_cases hq : x ∈ K.Qual
  · have hQ := hhigh x hx hq
    simp only [samePriority, ite_eq_left hq, hQ, iff_true]
    omega
  · by_cases hQ : x ∈ Q <;>
      simp only [samePriority, ite_eq_right hq, hQ, ite_true, ite_false, iff_true, iff_false] <;> omega

theorem same_path_normalized (D : NodeData r rank atoms p W)
    (htrans : ∀ ⦃x y z⦄, r x y → r y z → r x z)
    (hA : AtomSupport atoms r rank) {B v : ℕ} {V : Boundary J}
    (hB : 0 < B) (hrank : ∀ x, rank x < B) (hinj : Function.Injective rank)
    (hstrict : ∀ x y, r x y → rank x < rank y)
    (hv : D.a < v ∧ v < D.b)
    (hV : V.At p.time (Fintype.card J / 3) v)
    (hcenter : V.Separates r p.time W (D.right.pred r) v)
    (hnorm : p.NormalizedOn (Window p.time D.a v) r
      (D.list.samePriority rank B (D.right.pred r)))
    (hchild : ∀ U, U ⊂ W → Nonempty (NodeData r rank atoms p U) → P U) :
    Reached P r atoms W p.time D.a v := by
  classical
  let E := (Window p.time D.a v).toFinset
  have hE : ∀ x, x ∈ E ↔ x ∈ Window p.time D.a v := by intro x; simp [E]
  have hEeq : (↑E : Set J) = Window p.time D.a v := Set.ext hE
  have hsub : Window p.time D.a v ⊆ W := by
    intro x hx
    exact (D.window x).mpr ⟨hx.1, hx.2.trans hv.2⟩
  let priority := D.list.samePriority rank B (D.right.pred r)
  let count := (D.list.indices.sup id + 1) * B
  have hfinalAgree : ∀ x ∈ Window p.time D.a v,
      x ∈ PriorityCut priority (B+count) ↔ x ∈ D.right.pred r := by
    intro x hx
    exact GlobalList.samePriority_final hrank D.high x (hsub hx)
  have hfinalSep : V.Separates r p.time (Window p.time D.a v)
      (PriorityCut priority (B+count)) v :=
    (Boundary.separates_congr (fun x hx => (hfinalAgree x hx).symm)).mp
      (hcenter.mono_domain hsub)
  have hvbounds : 1 ≤ v ∧ v ≤ Fintype.card J / 3 := by
    have := Boundary.at_bounds D.rightAt
    omega
  have hVactual := Boundary.actual_of_interior hV hvbounds
  have hedge {ap bp t : ℕ} {A' B' : Boundary J}
      (hap : D.a ≤ ap) (hab : ap < bp) (hbp : bp ≤ v)
      (hAA : A'.At p.time (Fintype.card J / 3) ap)
      (hBB : B'.At p.time (Fintype.card J / 3) bp)
      (hact : ∃ Z, B' = Boundary.actual Z) (ht : t ≤ count)
      (hstart : A'.Separates r p.time (Window p.time D.a v)
        (PriorityCut priority (B+t)) ap)
      (hend : B'.Separates r p.time (Window p.time D.a v)
        (PriorityCut priority (B+t)) bp)
      (hwalk : CutoffWalk E r p.time priority (PriorityCut priority (B+t)) D.a ap)
      (hprev : Reached P r atoms W p.time D.a ap) :
      Reached P r atoms W p.time D.a bp := by
    obtain ⟨F⟩ := exists_same_edge D htrans hA hB hrank hstrict hv hV hcenter
      hap hab hbp hAA hBB hact ht hnorm hstart hend E hE hwalk
    exact F.reached hA F.finalSmall hprev
      (hchild _ F.child_ssubset ⟨F.toNode htrans hA⟩)
  by_cases ha : D.a = 0
  · have hL : D.left = Boundary.left := Boundary.at_unique D.leftAt ha
    apply hedge le_rfl hv.1 le_rfl D.leftAt hV hVactual le_rfl _ hfinalSep .refl (Or.inl rfl)
    rw [hL, ha]
    exact Boundary.left_separates
  · have habounds : 1 ≤ D.a ∧ D.a ≤ Fintype.card J / 3 := by omega
    obtain ⟨Z, hZ⟩ := Boundary.actual_of_interior D.leftAt habounds
    have hstartBoundary : D.left.Separates r p.time (Window p.time D.a v)
        (PriorityCut priority B) D.a := by
      constructor
      · intro x hx ht _
        have := hx.1
        omega
      · intro x hx _ hs
        apply D.low x (hsub hx)
        intro hq
        have hs' : priority x < B := hs
        dsimp only [priority, GlobalList.samePriority] at hs'
        rw [ite_eq_left hq] at hs'
        omega
    have hstart : Separator E r p.time (PriorityCut priority B) D.a := by
      apply (Boundary.actual_separates (hZ ▸ D.leftAt)).mp
      simpa only [hEeq, ← hZ] using hstartBoundary
    have hclosed : SlotClosed E p.time := by
      intro x hx y hy
      apply (hE y).mpr
      have hh := (hE x).mp hx
      simpa only [Window, Set.mem_ofPred, hy] using hh
    have hpriority := GlobalList.samePriority_extends hrank hstrict D.upsets
      (fun _ _ hxy hy => Boundary.pred_downset htrans D.right hxy hy) D.high
    have hnormE : LocalObstruction E r p.time priority :=
      normalizedOn_local_obstruction (hEeq.symm ▸ hnorm) hE
    obtain ⟨walk⟩ := exists_numeric_walk htrans D.full.2 hclosed
      (Or.inr fun x hx => ((hE x).mp hx).1)
      (GlobalList.samePriority_injective hrank hinj).injOn
      (fun x hx y hy hxy => hpriority x (hsub ((hE x).mp hx)) y (hsub ((hE y).mp hy)) hxy)
      hnormE hstart count
    have hpos : ∀ i, walk.position i < v := by
      intro i
      rcases walk.endpoint i with he | ⟨x, hx, ht⟩
      · simpa only [he] using hv.1
      · exact ht ▸ ((hE x).mp hx).2
    apply walk.reached hpos
    · intro i bp hab hbp hsep hprev
      have hap := (walk.history i).le
      have haps : 1 ≤ walk.position i ∧ walk.position i ≤ Fintype.card J / 3 := by
        have := hpos i
        omega
      have hbps : 1 ≤ bp ∧ bp ≤ Fintype.card J / 3 := by omega
      exact hedge hap hab hbp (p.triple_at D.full.1 _ haps.1 haps.2)
        (p.triple_at D.full.1 _ hbps.1 hbps.2) ⟨_, rfl⟩ (by have := i.isLt; omega)
        (separator_at D.full hE haps (walk.separator i))
        (separator_at D.full hE hbps hsep) (walk.history i) hprev
    · obtain ⟨Q, hQ⟩ := hVactual
      apply (Boundary.actual_separates (hQ ▸ hV)).mp
      simpa only [hEeq, ← hQ] using hfinalSep

end SamePaths
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section SwitchPaths
variable {J A : Type} [Fintype J] [DecidableEq J]
    {r : J → J → Prop} {rank : J → ℕ} {atoms : A → Set J}
    {p q : Layout J} {W : Set J} {P : Set J → Prop}

omit [Fintype J] [DecidableEq J] in
theorem switchPriority_final {B : ℕ} {D : Set J} (hrank : ∀ x, rank x < B) :
    PriorityCut (switchPriority rank B D) B = Dᶜ := by
  classical
  ext x
  have := hrank x
  change (if x ∈ D then B+rank x else rank x) < B ↔ x ∉ D
  split_ifs <;> simp_all

theorem switch_path_normalized {a b v B : ℕ} {L R V : Boundary J}
    (hp : p.Full r) (htrans : ∀ ⦃x y z⦄, r x y → r y z → r x z)
    (hA : AtomSupport atoms r rank) (hrank : ∀ x, rank x < B)
    (hinj : Function.Injective rank) (hstrict : ∀ x y, r x y → rank x < rank y)
    (hW : ∀ x, x ∈ W ↔ x ∈ Window p.time a b)
    (hL : L.At p.time (Fintype.card J / 3) a)
    (hR : R.At p.time (Fintype.card J / 3) b)
    (hcover : ∀ x ∈ W, x ∈ L.desc r ∨ x ∈ R.pred r)
    (G : SwitchSeed r p.time atoms W L a)
    (hv : a < v ∧ v < b) (hV : V.At p.time (Fintype.card J / 3) v)
    (hcenter : V.Separates r p.time W (L.desc r)ᶜ v)
    (hnorm : p.NormalizedOn (Window p.time a v) r (switchPriority rank B (L.desc r)))
    (hchild : ∀ U, U ⊂ W → Nonempty (NodeData r rank atoms p U) → P U) :
    Reached P r atoms W p.time a v := by
  classical
  let E := (Window p.time a v).toFinset
  have hE : ∀ x, x ∈ E ↔ x ∈ Window p.time a v := by intro x; simp [E]
  have hEeq : (↑E : Set J) = Window p.time a v := Set.ext hE
  have hsub : Window p.time a v ⊆ W := by
    intro x hx
    exact (hW x).mpr ⟨hx.1, hx.2.trans hv.2⟩
  let priority := switchPriority rank B (L.desc r)
  have hfinalSep : V.Separates r p.time (Window p.time a v)
      (PriorityCut priority B) v := by
    rw [show PriorityCut priority B = (L.desc r)ᶜ from switchPriority_final hrank]
    exact hcenter.mono_domain hsub
  have hvbounds : 1 ≤ v ∧ v ≤ Fintype.card J / 3 := by
    have := Boundary.at_bounds hR
    omega
  have hVactual := Boundary.actual_of_interior hV hvbounds
  have hedge {ap bp t : ℕ} {A' B' : Boundary J}
      (hap : a ≤ ap) (hab : ap < bp) (hbp : bp ≤ v)
      (hAA : A'.At p.time (Fintype.card J / 3) ap)
      (hBB : B'.At p.time (Fintype.card J / 3) bp)
      (hact : ∃ Z, B' = Boundary.actual Z) (ht : t ≤ B)
      (hstart : A'.Separates r p.time (Window p.time a v) (PriorityCut priority t) ap)
      (hend : B'.Separates r p.time (Window p.time a v) (PriorityCut priority t) bp)
      (hprev : Reached P r atoms W p.time a ap) :
      Reached P r atoms W p.time a bp := by
    obtain ⟨F⟩ := exists_switch_edge hp htrans hA hrank hstrict hW hL hR hcover G
      hv hV hcenter hap hab hbp hAA hBB hact ht hnorm hstart hend
    exact F.reached hA F.finalSmall hprev
      (hchild _ F.child_ssubset ⟨F.toNode htrans hA⟩)
  by_cases ha : a = 0
  · have hLL : L = Boundary.left := Boundary.at_unique hL ha
    apply hedge le_rfl hv.1 le_rfl hL hV hVactual le_rfl _ hfinalSep (Or.inl rfl)
    rw [hLL, ha]
    exact Boundary.left_separates
  · have habounds : 1 ≤ a ∧ a ≤ Fintype.card J / 3 := by omega
    have hstart : Separator E r p.time (PriorityCut priority 0) a := by
      constructor
      · intro x hx ht _
        have := ((hE x).mp hx).1
        omega
      · intro x _ _ hs
        exact (Nat.not_lt_zero _ hs).elim
    have hclosed : SlotClosed E p.time := by
      intro x hx y hy
      apply (hE y).mpr
      have hh := (hE x).mp hx
      simpa only [Window, Set.mem_ofPred, hy] using hh
    have hpriority := switchPriority_extends hrank hstrict (Boundary.desc_upset htrans L)
    have hnormE : LocalObstruction E r p.time priority :=
      normalizedOn_local_obstruction (hEeq.symm ▸ hnorm) hE
    obtain ⟨walk⟩ := exists_numeric_walk htrans hp.2 hclosed
      (Or.inr fun x hx => ((hE x).mp hx).1)
      (switchPriority_injective hrank hinj).injOn
      (fun x _ y _ hxy => hpriority x y hxy) hnormE hstart B
    have hpos : ∀ i, walk.position i < v := by
      intro i
      rcases walk.endpoint i with he | ⟨x, hx, ht⟩
      · simpa only [he] using hv.1
      · exact ht ▸ ((hE x).mp hx).2
    apply walk.reached hpos
    · intro i bp hab hbp hsep hprev
      have hap := (walk.history i).le
      have haps : 1 ≤ walk.position i ∧ walk.position i ≤ Fintype.card J / 3 := by
        have := hpos i
        omega
      have hbps : 1 ≤ bp ∧ bp ≤ Fintype.card J / 3 := by omega
      exact hedge (t := i.val) hap hab hbp (p.triple_at hp.1 _ haps.1 haps.2)
        (p.triple_at hp.1 _ hbps.1 hbps.2) ⟨_, rfl⟩ (by have := i.isLt; omega)
        (separator_at hp hE haps (by simpa only [Nat.zero_add] using walk.separator i))
        (separator_at hp hE hbps (by simpa only [Nat.zero_add] using hsep)) hprev
    · obtain ⟨Q, hQ⟩ := hVactual
      apply (Boundary.actual_separates (hQ ▸ hV)).mp
      simpa only [Nat.zero_add, hEeq, ← hQ] using hfinalSep

end SwitchPaths
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section SideNormalization
variable {J A : Type} [Fintype J] [DecidableEq J]
    {r : J → J → Prop} {rank : J → ℕ} {atoms : A → Set J}
    {p : Layout J} {W : Set J} {P : Set J → Prop}

theorem same_path (D : NodeData r rank atoms p W)
    (htrans : ∀ ⦃x y z⦄, r x y → r y z → r x z)
    (hA : AtomSupport atoms r rank) {B v : ℕ} {V : Boundary J}
    (hB : 0 < B) (hrank : ∀ x, rank x < B) (hinj : Function.Injective rank)
    (hstrict : ∀ x y, r x y → rank x < rank y)
    (hv : D.a < v ∧ v < D.b)
    (hV : V.At p.time (Fintype.card J / 3) v)
    (hcenter : V.Separates r p.time W (D.right.pred r) v)
    (hchild : ∀ q U, U ⊂ W → Nonempty (NodeData r rank atoms q U) → P U) :
    Reached P r atoms W p.time D.a v := by
  let E := Window p.time D.a v
  have hsub : E ⊆ W := fun x hx => (D.window x).mpr ⟨hx.1, hx.2.trans hv.2⟩
  obtain ⟨q, hfix, hnorm⟩ := exists_normalizedOn p E r
    (D.list.samePriority rank B (D.right.pred r)) D.full.2
  let Dq := D.reorder (hfix.mono hsub) hnorm.1
  have hE : E = Window q.time D.a v := Set.ext (hfix.window (fun _ => Iff.rfl))
  have hVq := hfix.boundary (fun _ => Iff.rfl) (Or.inr le_rfl) hV
  have hcenterq := hcenter.reorder hfix (fun _ => Iff.rfl) (Or.inr le_rfl)
  have hnormq : q.NormalizedOn (Window q.time Dq.a v) r
      (Dq.list.samePriority rank B (Dq.right.pred r)) := by
    change q.NormalizedOn (Window q.time D.a v) r
      (D.list.samePriority rank B (D.right.pred r))
    exact hE ▸ hnorm
  have hreach := same_path_normalized Dq htrans hA hB hrank hinj hstrict hv hVq
    hcenterq hnormq (hchild q)
  exact hreach.congr_time
    (fun x => (hfix.before_iff (fun _ => Iff.rfl) (Or.inr le_rfl) x).symm)
    (fun x => (hfix.after_iff (fun _ => Iff.rfl) (Or.inr le_rfl) x).symm)

theorem switch_path {a b v B : ℕ} {L R V : Boundary J}
    (hp : p.Full r) (htrans : ∀ ⦃x y z⦄, r x y → r y z → r x z)
    (hA : AtomSupport atoms r rank) (hrank : ∀ x, rank x < B)
    (hinj : Function.Injective rank) (hstrict : ∀ x y, r x y → rank x < rank y)
    (hW : ∀ x, x ∈ W ↔ x ∈ Window p.time a b)
    (hL : L.At p.time (Fintype.card J / 3) a)
    (hR : R.At p.time (Fintype.card J / 3) b)
    (hcover : ∀ x ∈ W, x ∈ L.desc r ∨ x ∈ R.pred r)
    (G : SwitchSeed r p.time atoms W L a)
    (hv : a < v ∧ v < b) (hV : V.At p.time (Fintype.card J / 3) v)
    (hcenter : V.Separates r p.time W (L.desc r)ᶜ v)
    (hchild : ∀ q U, U ⊂ W → Nonempty (NodeData r rank atoms q U) → P U) :
    Reached P r atoms W p.time a v := by
  let E := Window p.time a v
  have hsub : E ⊆ W := fun x hx => (hW x).mpr ⟨hx.1, hx.2.trans hv.2⟩
  obtain ⟨q, hfix, hnorm⟩ := exists_normalizedOn p E r
    (switchPriority rank B (L.desc r)) hp.2
  have hE : E = Window q.time a v := Set.ext (hfix.window (fun _ => Iff.rfl))
  have hfixW := hfix.mono hsub
  have hWq := hfixW.window hW
  have hLq := hfixW.boundary hW (Or.inl le_rfl) hL
  have hRq := hfixW.boundary hW (Or.inr le_rfl) hR
  have hVq := hfix.boundary (fun _ => Iff.rfl) (Or.inr le_rfl) hV
  have hcenterq := hcenter.reorder hfix (fun _ => Iff.rfl) (Or.inr le_rfl)
  have hnormq : q.NormalizedOn (Window q.time a v) r
      (switchPriority rank B (L.desc r)) := by simpa only [hE] using hnorm
  have hreach := switch_path_normalized ⟨hp.1, hnorm.1⟩ htrans hA hrank hinj hstrict
    hWq hLq hRq hcover (G.reorder hW hfixW) hv hVq hcenterq hnormq (hchild q)
  exact hreach.congr_time
    (fun x => (hfix.before_iff (fun _ => Iff.rfl) (Or.inr le_rfl) x).symm)
    (fun x => (hfix.after_iff (fun _ => Iff.rfl) (Or.inr le_rfl) x).symm)

end SideNormalization
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section ReversePaths
variable {J A : Type} [Fintype J] {r : J → J → Prop}
    {atoms : A → Set J} {p : Layout J} {W S : Set J}

theorem Boundary.Separates.reverse {B : Boundary J} {s : ℕ}
    (hfull : 3 ∣ Fintype.card J) (hs : s ≤ Fintype.card J / 3 + 1)
    (h : B.Separates r p.time W S s) :
    B.reverse.Separates (fun x y => r y x) p.reverse.time W Sᶜ
      (Fintype.card J / 3 + 1 - s) := by
  constructor
  · intro x hx ht hn
    have hxbound := p.time_bounds hfull x
    rw [p.reverse_time hfull] at ht
    have hl : s < p.time x := by omega
    have hxS : x ∈ S := by simpa only [Set.mem_compl_iff, not_not] using hn
    simpa only [Boundary.pred_reverse] using h.2 x hx hl hxS
  · intro x hx ht hn
    have hxbound := p.time_bounds hfull x
    rw [p.reverse_time hfull] at ht
    have hl : p.time x < s := by omega
    simpa only [Boundary.desc_reverse] using h.1 x hx hl hn

theorem SplitVertex.AtTime.reverse {u : SplitVertex r atoms W} {s : ℕ}
    (hfull : 3 ∣ Fintype.card J) (hs : s ≤ Fintype.card J / 3 + 1)
    (h : u.AtTime p.time s) :
    u.reverse.AtTime p.reverse.time (Fintype.card J / 3 + 1 - s) := by
  constructor
  · intro x
    change x ∈ u.right ↔ _
    rw [h.2.2 x, p.reverse_time hfull]
    have := p.time_bounds hfull x
    apply and_congr_right
    intro _
    omega
  · constructor
    · intro x
      change x ∈ u.middle.val ↔ _
      rw [h.2.1 x, p.reverse_time hfull]
      have := p.time_bounds hfull x
      apply and_congr_right
      intro _
      omega
    · intro x
      change x ∈ u.left ↔ _
      rw [h.1 x, p.reverse_time hfull]
      have := p.time_bounds hfull x
      apply and_congr_right
      intro _
      omega

theorem window_reverse {a b : ℕ} (hfull : 3 ∣ Fintype.card J)
    (ha : a ≤ Fintype.card J / 3 + 1) (hb : b ≤ Fintype.card J / 3 + 1) :
    Window p.reverse.time (Fintype.card J / 3 + 1 - b) (Fintype.card J / 3 + 1 - a) =
      Window p.time a b := by
  ext x
  change (_ < p.reverse.time x ∧ p.reverse.time x < _) ↔ _ < p.time x ∧ p.time x < _
  rw [p.reverse_time hfull]
  have := p.time_bounds hfull x
  omega

end ReversePaths
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section Completeness
variable {J A : Type} [Fintype J] [DecidableEq J] {atoms : A → Set J}

theorem node_complete (n : ℕ) :
    ∀ (r : J → J → Prop) (rank reverseRank : J → ℕ) (p : Layout J) (W : Set J) (B : ℕ),
    (∀ ⦃x y z⦄, r x y → r y z → r x z) →
    AtomSupport atoms r rank → AtomSupport atoms (fun x y => r y x) reverseRank →
    0 < B → (∀ x, rank x < B) → (∀ x, reverseRank x < B) →
    Function.Injective rank → Function.Injective reverseRank →
    (∀ x y, r x y → rank x < rank y) →
    (∀ x y, r y x → reverseRank x < reverseRank y) →
    NodeData r rank atoms p W → W.ncard ≤ n → AcceptedAt r atoms n W := by
  induction n with
  | zero =>
    intro r rank reverseRank p W B _ _ _ _ _ _ _ _ _ _ D hcard
    have hW : W = ∅ := (Set.ncard_eq_zero (Set.toFinite W)).mp (Nat.eq_zero_of_le_zero hcard)
    exact ⟨D.small.mono (by omega), hW⟩
  | succ n ih =>
    intro r rank reverseRank p W B htrans hA hAR hB hrank hrankR hinj hinjR hstrict hstrictR D hcard
    have hsmall : Described atoms W 10000 := D.small.mono (by omega)
    by_cases hWempty : W = ∅
    · exact ⟨hsmall, Or.inl hWempty⟩
    have hne : W.Nonempty := Set.nonempty_iff_ne_empty.mpr hWempty
    obtain ⟨q, hfix, hq, v, V, hav, hvb, hV, hcenter⟩ := exists_node_center D htrans hne
    let Dq := D.reorder hfix hq
    have hchild : ∀ q U, U ⊂ W → Nonempty (NodeData r rank atoms q U) →
        AcceptedAt r atoms n U := by
      intro q U hU hDU
      obtain ⟨DU⟩ := hDU
      have hlt := Set.ncard_lt_ncard hU
      exact ih r rank reverseRank q U B htrans hA hAR hB hrank hrankR
        hinj hinjR hstrict hstrictR DU (by omega)
    have hchildR : ∀ q U, U ⊂ W →
        Nonempty (NodeData (fun x y => r y x) reverseRank atoms q U) →
        AcceptedAt (fun x y => r y x) atoms n U := by
      intro q U hU hDU
      obtain ⟨DU⟩ := hDU
      have hlt := Set.ncard_lt_ncard hU
      exact ih (fun x y => r y x) reverseRank rank q U B
        (fun {_ _ _} hxy hyz => htrans hyz hxy) hAR hA hB hrankR hrank
        hinjR hinj hstrictR hstrict DU (by omega)
    have hleft := same_path Dq htrans hA hB hrank hinj hstrict ⟨hav, hvb⟩ hV hcenter hchild
    let T := Fintype.card J / 3
    have ha : D.a ≤ T+1 := Boundary.at_bounds D.leftAt
    have hb : D.b ≤ T+1 := Boundary.at_bounds D.rightAt
    have hv : v ≤ T+1 := by omega
    have hfrom : T+1-D.b < T+1-v := by omega
    have hto : T+1-v < T+1-D.a := by omega
    have hWr : ∀ x, x ∈ W ↔ x ∈ Window q.reverse.time (T+1-D.b) (T+1-D.a) := by
      rw [window_reverse D.full.1 ha hb]
      exact Dq.window
    have hcoverr : ∀ x ∈ W, x ∈ Dq.right.reverse.desc (fun x y => r y x) ∨
        x ∈ Dq.left.reverse.pred (fun x y => r y x) := by
      intro x hx
      simpa only [Boundary.desc_reverse, Boundary.pred_reverse, or_comm] using Dq.cover x hx
    have hcenterr : V.reverse.Separates (fun x y => r y x) q.reverse.time W
        (Dq.right.reverse.desc (fun x y => r y x))ᶜ (T+1-v) := by
      rw [Boundary.desc_reverse]
      exact hcenter.reverse D.full.1 hv
    have hright := switch_path (Layout.reverse_full Dq.full) (fun {_ _ _} hxy hyz => htrans hyz hxy)
      hAR hrankR hinjR hstrictR hWr (Boundary.at_reverse D.full.1 Dq.rightAt)
      (Boundary.at_reverse D.full.1 Dq.leftAt) hcoverr
      (Dq.reverseSeed.toSwitch D.full.1 hb) ⟨hfrom, hto⟩
      (Boundary.at_reverse D.full.1 hV) hcenterr hchildR
    rcases hleft with he | ⟨ul, vl, hul, hpl, hvl⟩
    · change v = D.a at he
      omega
    rcases hright with he | ⟨ur, vr, hur, hpr, hvr⟩
    · change T+1-v = T+1-D.b at he
      omega
    have hvback : T+1-(T+1-v) = v := by omega
    have hvr' : vr.reverse.AtTime q.time v := by
      have hh := hvr.reverse D.full.1 (Nat.sub_le (T+1) v)
      change vr.reverse.AtTime q.reverse.reverse.time (T+1-(T+1-v)) at hh
      rw [hvback] at hh
      simpa only [Layout.reverse_reverse] using hh
    have hsame : vl = vr.reverse := hvl.unique hvr'
    have hpr' := SplitVertex.path_reverse (fun _ h => AcceptedAt.reverse h) hpr
    refine ⟨hsmall, Or.inr ⟨ul, ur.reverse, hul, ?_, AcceptedAt.reverse hur⟩⟩
    exact hpl.trans (hsame.symm ▸ hpr')

end Completeness
end ThreeMachine.Structure

end

end OAI
end

section
-- module HierarchySoundness
namespace OAI

section

namespace ThreeMachine.Structure
section Soundness
variable {J A : Type} [Fintype J] {r : J → J → Prop} {atoms : A → Set J}

namespace FullBlock
variable {U V W : Set J}

end FullBlock

namespace SplitVertex
variable {W : Set J} {u v : SplitVertex r atoms W}

theorem path_sound {P : Set J → Prop} (hP : ∀ U, P U → Nonempty (FullBlock r U))
    (h : Relation.ReflTransGen (Step P) u v) (hs : Nonempty (FullBlock r u.left)) :
    Nonempty (FullBlock r v.left) := by
  induction h with
  | refl => exact hs
  | tail _ ht ih =>
    obtain ⟨s⟩ := ih
    obtain ⟨t⟩ := hP _ ht.2
    exact ⟨advance s ht.1 t⟩

end SplitVertex

theorem AcceptedAt.sound {n : ℕ} {W : Set J} (h : AcceptedAt r atoms n W) :
    Nonempty (FullBlock r W) := by
  induction n generalizing W with
  | zero => exact h.2 ▸ ⟨FullBlock.empty⟩
  | succ n ih =>
    rcases h.2 with he | ⟨u, v, hu, hp, hv⟩
    · exact he ▸ ⟨FullBlock.empty⟩
    · obtain ⟨s⟩ := SplitVertex.path_sound (fun _ h => ih h) hp (ih hu)
      obtain ⟨t⟩ := ih hv
      exact ⟨v.finish s t⟩

end Soundness
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section AtomicFamily
variable {J : Type} [Fintype J]

namespace Atomic

theorem eval_reversed (r : J → J → Prop) (rank reverseRank : J → ℕ)
    (a : Atomic J) :
    ∃ b : Atomic J, eval (fun x y => r y x) reverseRank rank a = eval r rank reverseRank b := by
  cases a with
  | constant b => exact ⟨.constant b, rfl⟩
  | threshold frame upper k =>
    refine ⟨.threshold (!frame) upper k, ?_⟩
    cases frame <;> rfl
  | cone frame kind Z =>
    refine ⟨.cone (!frame) kind Z, ?_⟩
    cases frame <;> rfl

theorem support (r : J → J → Prop) (rank reverseRank : J → ℕ)
    (hrank : ∀ x, rank x ≤ Fintype.card J) :
    AtomSupport (eval r rank reverseRank) r rank := by
  have htrue : Described (eval r rank reverseRank) Set.univ 1 :=
    Described.atom (atoms := eval r rank reverseRank) (.constant true)
  have hfalse : Described (eval r rank reverseRank) ∅ 1 :=
    Described.atom (atoms := eval r rank reverseRank) (.constant false)
  refine ⟨htrue, hfalse, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    by_cases hk : k < Fintype.card J + 2
    · exact Described.atom (atoms := eval r rank reverseRank) (.threshold false false ⟨k, hk⟩)
    · have he : RankTail rank k = ∅ := by
        ext x
        have := hrank x
        simp only [RankTail, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        omega
      exact he ▸ hfalse
  · intro B
    cases B with
    | left => exact hfalse
    | right => exact htrue
    | actual Z => exact Described.atom (atoms := eval r rank reverseRank) (.cone false 1 Z)
  · intro B
    cases B with
    | left => exact htrue
    | right => exact hfalse
    | actual Z => exact Described.atom (atoms := eval r rank reverseRank) (.cone false 2 Z)
  · intro B
    cases B with
    | left => exact hfalse
    | right => exact htrue
    | actual Z => exact Described.atom (atoms := eval r rank reverseRank) (.cone false 3 Z)
  · intro B
    cases B with
    | left => exact htrue
    | right => exact hfalse
    | actual Z => exact Described.atom (atoms := eval r rank reverseRank) (.cone false 4 Z)
  · intro Z
    exact Described.atom (atoms := eval r rank reverseRank) (.cone false 0 Z)

theorem support_reverse (r : J → J → Prop) (rank reverseRank : J → ℕ)
    (hrank : ∀ x, reverseRank x ≤ Fintype.card J) :
    AtomSupport (eval r rank reverseRank) (fun x y => r y x) reverseRank := by
  have transfer (S : Set J) (h : Described (eval (fun x y => r y x) reverseRank rank) S 1) :
      Described (eval r rank reverseRank) S 1 := by
    obtain ⟨f, hf, hk⟩ := h
    cases f with
    | leaf a b =>
      obtain ⟨a', ha'⟩ := eval_reversed r rank reverseRank a
      refine ⟨.leaf a' b, ?_, le_rfl⟩
      cases b <;> simpa only [Formula.eval, ha'] using hf
    | conj p q | disj p q =>
      have := p.leaves_pos
      have := q.leaves_pos
      simp only [Formula.leaves] at hk
      omega
  have h := support (fun x y => r y x) reverseRank rank hrank
  exact ⟨transfer _ h.truth, transfer _ h.falsity, fun k => transfer _ (h.rankTail k),
    fun B => transfer _ (h.pred B), fun B => transfer _ (h.desc B),
    fun B => transfer _ (h.weakPred B), fun B => transfer _ (h.weakDesc B),
    fun Z => transfer _ (h.triple Z)⟩

end Atomic
end AtomicFamily
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section Ranks
variable {J K : Type} [Fintype J] [LinearOrder K]

theorem rankOfKey_strict {key : J → K} {x y : J} (h : key x < key y) :
    rankOfKey key x < rankOfKey key y := by
  have hsub : Finset.univ.filter (fun z => key z < key x) ⊂
      Finset.univ.filter (fun z => key z < key y) := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro z hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2.trans h⟩
    · intro he
      have hm : x ∈ Finset.univ.filter (fun z => key z < key y) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      rw [← he] at hm
      exact lt_irrefl _ (Finset.mem_filter.mp hm).2
  have := Finset.card_lt_card hsub
  dsimp [rankOfKey]
  omega

theorem rankOfKey_bounds (key : J → K) (x : J) :
    1 ≤ rankOfKey key x ∧ rankOfKey key x ≤ Fintype.card J := by
  have hsub : Finset.univ.filter (fun y => key y < key x) ⊂ (Finset.univ : Finset J) := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
    intro he
    have hm : x ∈ Finset.univ.filter (fun y => key y < key x) := by rw [he]; exact Finset.mem_univ _
    exact lt_irrefl _ (Finset.mem_filter.mp hm).2
  have := Finset.card_lt_card hsub
  simp only [Finset.card_univ] at this
  dsimp [rankOfKey]
  omega

theorem rankOfKey_injective {key : J → K} (hinj : Function.Injective key) :
    Function.Injective (rankOfKey key) := by
  intro x y he
  rcases lt_trichotomy (key x) (key y) with h | h | h
  · have := rankOfKey_strict h
    omega
  · exact hinj h
  · have := rankOfKey_strict h
    omega

end Ranks

section IndexedRanks
variable {n : ℕ} (r : Fin n → Fin n → Prop) [DecidableRel r]

theorem jobKey_injective : Function.Injective (jobKey r) := by
  intro x y h
  exact congrArg (fun z : Lex (ℕ × Fin n) => (ofLex z).2) h

theorem jobRank_injective : Function.Injective (jobRank r) := rankOfKey_injective (jobKey_injective r)

theorem jobRank_bounds (x : Fin n) : 1 ≤ jobRank r x ∧ jobRank r x ≤ n := by
  simpa [jobRank] using rankOfKey_bounds (jobKey r) x

theorem jobRank_strict
    (hirr : ∀ x, ¬r x x) (htrans : ∀ ⦃x y z⦄, r x y → r y z → r x z)
    {x y : Fin n} (hxy : r x y) : jobRank r x < jobRank r y := by
  have hsub : Finset.univ.filter (fun z => r z x) ⊂ Finset.univ.filter (fun z => r z y) := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro z hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, htrans (Finset.mem_filter.mp hz).2 hxy⟩
    · intro he
      have hm : x ∈ Finset.univ.filter (fun z => r z y) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩
      rw [← he] at hm
      exact hirr x (Finset.mem_filter.mp hm).2
  apply rankOfKey_strict
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (Finset.card_lt_card hsub))

theorem reverseJobRank_bounds (x : Fin n) : 1 ≤ reverseJobRank r x ∧ reverseJobRank r x ≤ n := by
  have := jobRank_bounds r x
  dsimp [reverseJobRank]
  omega

theorem reverseJobRank_injective : Function.Injective (reverseJobRank r) := by
  intro x y h
  apply jobRank_injective r
  have := jobRank_bounds r x
  have := jobRank_bounds r y
  dsimp [reverseJobRank] at h
  omega

theorem reverseJobRank_strict
    (hirr : ∀ x, ¬r x x) (htrans : ∀ ⦃x y z⦄, r x y → r y z → r x z)
    {x y : Fin n} (hxy : r y x) : reverseJobRank r x < reverseJobRank r y := by
  have := jobRank_strict r hirr htrans hxy
  have := jobRank_bounds r x
  dsimp [reverseJobRank]
  omega

end IndexedRanks
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section ScheduleLayouts
variable {J : Type} [Fintype J]

theorem exists_slot_embedding {T : ℕ} (time : J → ℕ)
    (hbound : ∀ x, 1 ≤ time x ∧ time x ≤ T)
    (hcap : ∀ t, {x | time x = t}.ncard ≤ 3) :
    ∃ f : J → Fin (3*T), Function.Injective f ∧
      ∀ x, (f x).val / 3 + 1 = time x := by
  classical
  let slot : J → Fin T := fun x => ⟨time x - 1, by have := hbound x; omega⟩
  have hc (i : Fin T) : Fintype.card {x // slot x = i} ≤ 3 := by
    have he : {x | slot x = i} = {x | time x = i.val + 1} := by
      ext x
      simp only [Set.mem_ofPred_eq, Fin.ext_iff]
      change time x - 1 = i.val ↔ time x = i.val + 1
      have := hbound x
      omega
    rw [← Nat.card_eq_fintype_card]
    change {x | slot x = i}.ncard ≤ 3
    rw [he]
    exact hcap _
  let embed (i : Fin T) : {x // slot x = i} ↪ Fin 3 :=
    (Fintype.equivFin {x // slot x = i}).toEmbedding.trans
      (Fin.castLEEmb (by simpa using hc i))
  let code : (Σ i : Fin T, {x // slot x = i}) → Fin T × Fin 3 :=
    fun z => (z.1, embed z.1 z.2)
  have hcode : Function.Injective code := by
    rintro ⟨i, x⟩ ⟨j, y⟩ he
    obtain ⟨hij, hxy⟩ := Prod.mk.inj he
    cases hij
    have hxy' := (embed i).injective hxy
    change x = y at hxy'
    subst y
    rfl
  let f₀ : J → Fin T × Fin 3 := code ∘ (Equiv.sigmaFiberEquiv slot).symm
  have hf : Function.Injective f₀ := hcode.comp (Equiv.sigmaFiberEquiv slot).symm.injective
  let conv : Fin T × Fin 3 ≃ Fin (3*T) :=
    finProdFinEquiv.trans (finCongr (Nat.mul_comm T 3))
  let f : J → Fin (3*T) := conv ∘ f₀
  refine ⟨f, conv.injective.comp hf, ?_⟩
  intro x
  have hidx : (embed (slot x) ⟨x, rfl⟩).val < 3 := (embed (slot x) ⟨x, rfl⟩).isLt
  change ((embed (slot x) ⟨x, rfl⟩).val + 3 * (slot x).val) / 3 + 1 = time x
  change ((embed (slot x) ⟨x, rfl⟩).val + 3 * (time x - 1)) / 3 + 1 = time x
  have := hbound x
  omega

theorem exists_layout_time {T : ℕ} (time : J → ℕ)
    (hbound : ∀ x, 1 ≤ time x ∧ time x ≤ T)
    (hcap : ∀ t, {x | time x = t}.ncard ≤ 3)
    (hsize : Fintype.card J = 3 * T) :
    ∃ p : Layout J, ∀ x, p.time x = time x := by
  obtain ⟨f, hf, ht⟩ := exists_slot_embedding time hbound hcap
  let e : J ≃ Fin (3*T) := Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, by simpa using hsize⟩)
  let p : Layout J := e.trans (finCongr hsize.symm)
  exact ⟨p, ht⟩

theorem FullBlock.layout {r : J → J → Prop} (s : FullBlock r Set.univ) :
    ∃ p : Layout J, p.Full r := by
  have hsize : Fintype.card J = 3*s.length := by
    simpa only [Set.ncard_univ, Nat.card_eq_fintype_card] using s.size
  obtain ⟨p, hp⟩ := exists_layout_time s.time (fun x => s.bounds x (Set.mem_univ x))
    (fun t => by simpa only [Set.mem_univ, true_and] using s.capacity t) hsize
  refine ⟨p, ⟨s.length, hsize⟩, ?_⟩
  intro x y hxy
  simpa only [hp] using s.respects x (Set.mem_univ x) y (Set.mem_univ y) hxy

theorem accepted_iff_full_layout [DecidableEq J]
    (r : J → J → Prop) (rank reverseRank : J → ℕ)
    (htrans : ∀ ⦃x y z⦄, r x y → r y z → r x z)
    (hrank : ∀ x, rank x ≤ Fintype.card J)
    (hrankR : ∀ x, reverseRank x ≤ Fintype.card J)
    (hinj : Function.Injective rank) (hinjR : Function.Injective reverseRank)
    (hstrict : ∀ x y, r x y → rank x < rank y)
    (hstrictR : ∀ x y, r y x → reverseRank x < reverseRank y) :
    AcceptedAt r (Atomic.eval r rank reverseRank) (Fintype.card J) Set.univ ↔
      ∃ p : Layout J, p.Full r := by
  constructor
  · intro h
    obtain ⟨s⟩ := h.sound
    exact s.layout
  · rintro ⟨p, hp⟩
    have hA := Atomic.support r rank reverseRank hrank
    exact node_complete (Fintype.card J) r rank reverseRank p Set.univ
      (Fintype.card J+1) htrans hA (Atomic.support_reverse r rank reverseRank hrankR)
      (by omega) (fun x => by have := hrank x; omega)
      (fun x => by have := hrankR x; omega) hinj hinjR hstrict hstrictR
      (NodeData.root p hp hA) (by simp)

end ScheduleLayouts
end ThreeMachine.Structure

end

end OAI
end

section
-- module Padding
namespace OAI

section

namespace ThreeMachine

theorem Feasible.order {n T : ℕ} {G : Instance n} {time : Fin n → ℕ}
    (h : Feasible G T time) {x y : Fin n} (hxy : G.order x y) : time x < time y := by
  induction hxy with
  | single hxy => exact h.2.2 _ _ hxy
  | tail _ hxy ih => exact ih.trans (h.2.2 _ _ hxy)

theorem paddedOrder_trans {n m : ℕ} {r : Fin n → Fin n → Prop}
    (htrans : ∀ ⦃x y z⦄, r x y → r y z → r x z) :
    ∀ ⦃x y z⦄, paddedOrder r m x y → paddedOrder r m y z → paddedOrder r m x z := by
  rintro _ _ _ ⟨a, b, ha, hb, hab⟩ ⟨c, d, hc, hd, hcd⟩
  have he : b = c := Fin.ext (hb.symm.trans hc)
  subst c
  exact ⟨a, d, ha, hd, htrans hab hcd⟩

theorem paddedOrder_irrefl {n m : ℕ} {r : Fin n → Fin n → Prop}
    (hirr : ∀ x, ¬r x x) : ∀ x, ¬paddedOrder r m x x := by
  rintro _ ⟨a, b, ha, hb, hab⟩
  have he : a = b := Fin.ext (ha.symm.trans hb)
  exact hirr a (he ▸ hab)

theorem paddedOrder_castLE {n m : ℕ} {r : Fin n → Fin n → Prop} (hnm : n ≤ m)
    (x y : Fin n) : paddedOrder r m (Fin.castLE hnm x) (Fin.castLE hnm y) ↔ r x y := by
  constructor
  · rintro ⟨a, b, ha, hb, hab⟩
    have ea : x = a := Fin.ext ha
    have eb : y = b := Fin.ext hb
    simpa only [ea, eb] using hab
  · intro h
    exact ⟨x, y, rfl, rfl, h⟩

namespace Structure

theorem Layout.capacity {J : Type} [Fintype J] (p : Layout J)
    (hfull : 3 ∣ Fintype.card J) (t : ℕ) : (p.slot t).card ≤ 3 := by
  by_cases ht : 1 ≤ t ∧ t ≤ Fintype.card J / 3
  · exact (p.card_slot hfull t ht.1 ht.2).le
  · have he : p.slot t = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hx' := (p.mem_slot t x).mp hx
      have := p.time_bounds hfull x
      omega
    simp [he]

end Structure

theorem feasible_iff_padded_layout {n T : ℕ} (G : Instance n) (hn : n ≤ 3*T) :
    (∃ time, Feasible G T time) ↔
      ∃ p : Structure.Layout (Fin (3*T)), p.Full (paddedOrder G.order (3*T)) := by
  classical
  constructor
  · rintro ⟨time, htime⟩
    have hcap (t : ℕ) : {x | time x = t}.ncard ≤ 3 := by
      have he : {x | time x = t} = (Finset.univ.filter (fun x => time x = t) : Set (Fin n)) := by
        ext x
        simp
      rw [he, Set.ncard_coe_finset]
      exact htime.2.1 t
    obtain ⟨f, hf, ht⟩ := Structure.exists_slot_embedding time htime.1 hcap
    obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair (Fin.castLE hn) f
      (Fin.castLE_injective hn) hf
    let p : Structure.Layout (Fin (3*T)) := σ.trans (finCongr (Fintype.card_fin _).symm)
    have hp (x : Fin n) : p.time (Fin.castLE hn x) = time x := by
      change (σ (Fin.castLE hn x)).val / 3 + 1 = time x
      rw [hσ]
      exact ht x
    refine ⟨p, by simp, ?_⟩
    rintro x y ⟨a, b, ha, hb, hab⟩
    have ea : x = Fin.castLE hn a := Fin.ext ha
    have eb : y = Fin.castLE hn b := Fin.ext hb
    rw [ea, eb, hp, hp]
    exact htime.order hab
  · rintro ⟨p, hp⟩
    let time : Fin n → ℕ := fun x => p.time (Fin.castLE hn x)
    refine ⟨time, ?_, ?_, ?_⟩
    · intro x
      have h := p.time_bounds hp.1 (Fin.castLE hn x)
      simpa only [Fintype.card_fin, Nat.mul_div_right _ (by omega : 0 < 3)] using h
    · intro t
      have hcard : (Finset.univ.filter (fun x : Fin n => time x = t)).card ≤ (p.slot t).card := by
        apply Finset.card_le_card_of_injOn (Fin.castLE hn)
        · intro x hx
          exact (p.mem_slot _ _).mpr (Finset.mem_filter.mp hx).2
        · exact (Fin.castLE_injective hn).injOn
      exact hcard.trans (p.capacity hp.1 t)
    · intro x y hxy
      exact hp.2 _ _ ((paddedOrder_castLE hn x y).mpr (.single hxy))

theorem Feasible.size_bound {n T : ℕ} {G : Instance n} {time : Fin n → ℕ}
    (h : Feasible G T time) : n ≤ 3*T := by
  classical
  have hcap (t : ℕ) : {x | time x = t}.ncard ≤ 3 := by
    have he : {x | time x = t} = (Finset.univ.filter (fun x => time x = t) : Set (Fin n)) := by
      ext x
      simp
    rw [he, Set.ncard_coe_finset]
    exact h.2.1 t
  obtain ⟨f, hf, _⟩ := Structure.exists_slot_embedding time h.1 hcap
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf

end ThreeMachine

end

end OAI
end

section
-- module EffectiveFamily
namespace OAI

section

namespace ThreeMachine.Structure
namespace Formula
variable {A B C : Type}

theorem occurrence_representation (p : Formula A) :
    ∃ (s : Formula (Fin p.leaves)) (f : Fin p.leaves → A),
      s.leaves = p.leaves ∧ s.map f = p := by
  induction p with
  | leaf a sign =>
    exact ⟨.leaf ⟨0, by simp [leaves]⟩ sign, fun _ => a, rfl, rfl⟩
  | conj p q hp hq =>
    obtain ⟨p', fp, hlp, hep⟩ := hp
    obtain ⟨q', fq, hlq, heq⟩ := hq
    refine ⟨.conj (p'.map (Fin.castAdd q.leaves)) (q'.map (Fin.natAdd p.leaves)),
      Fin.addCases fp fq, ?_, ?_⟩
    · simp only [leaves, leaves_map, hlp, hlq]
    · change ((p'.map (Fin.castAdd q.leaves)).map (Fin.addCases fp fq)).conj
        ((q'.map (Fin.natAdd p.leaves)).map (Fin.addCases fp fq)) = p.conj q
      rw [map_comp, map_comp]
      have hfp : (Fin.addCases fp fq) ∘ (Fin.castAdd q.leaves) = fp := by funext i; simp
      have hfq : (Fin.addCases fp fq) ∘ (Fin.natAdd p.leaves) = fq := by funext i; simp
      rw [hfp, hfq, hep, heq]
  | disj p q hp hq =>
    obtain ⟨p', fp, hlp, hep⟩ := hp
    obtain ⟨q', fq, hlq, heq⟩ := hq
    refine ⟨.disj (p'.map (Fin.castAdd q.leaves)) (q'.map (Fin.natAdd p.leaves)),
      Fin.addCases fp fq, ?_, ?_⟩
    · simp only [leaves, leaves_map, hlp, hlq]
    · change ((p'.map (Fin.castAdd q.leaves)).map (Fin.addCases fp fq)).disj
        ((q'.map (Fin.natAdd p.leaves)).map (Fin.addCases fp fq)) = p.disj q
      rw [map_comp, map_comp]
      have hfp : (Fin.addCases fp fq) ∘ (Fin.castAdd q.leaves) = fp := by funext i; simp
      have hfq : (Fin.addCases fp fq) ∘ (Fin.natAdd p.leaves) = fq := by funext i; simp
      rw [hfp, hfq, hep, heq]

theorem mem_depthEnum (alphabet : List A) (hA : ∀ a, a ∈ alphabet)
    (n : ℕ) (p : Formula A) (hp : p.leaves ≤ n) : p ∈ depthEnum alphabet n := by
  induction n generalizing p with
  | zero => have := p.leaves_pos; omega
  | succ n ih =>
    cases p with
    | leaf a sign =>
      apply List.mem_append_left
      apply List.mem_flatMap.mpr
      exact ⟨a, hA a, by cases sign <;> simp⟩
    | conj p q =>
      have hposp := p.leaves_pos
      have hposq := q.leaves_pos
      simp only [leaves] at hp
      apply List.mem_append_right
      apply List.mem_flatMap.mpr
      refine ⟨p, ih p (by omega), List.mem_flatMap.mpr ⟨q, ih q (by omega), ?_⟩⟩
      simp
    | disj p q =>
      have hposp := p.leaves_pos
      have hposq := q.leaves_pos
      simp only [leaves] at hp
      apply List.mem_append_right
      apply List.mem_flatMap.mpr
      refine ⟨p, ih p (by omega), List.mem_flatMap.mpr ⟨q, ih q (by omega), ?_⟩⟩
      simp

theorem mem_templates {K : ℕ} (s : Formula (Fin K)) (hs : s.leaves ≤ K) :
    s ∈ templates K := by
  exact List.mem_filter.mpr ⟨mem_depthEnum _ (fun _ => List.mem_finRange _) K s hs,
    by simpa using hs⟩

theorem template_representation {K : ℕ} (p : Formula A) (hp : p.leaves ≤ K) :
    ∃ (s : Formula (Fin K)) (f : Fin K → A), s ∈ templates K ∧ s.map f = p := by
  obtain ⟨s, f, hs, hf⟩ := occurrence_representation p
  let default : A := f ⟨0, p.leaves_pos⟩
  let g : Fin K → A := fun i => if hi : i.val < p.leaves then f ⟨i.val, hi⟩ else default
  let s' := s.map (Fin.castLE hp)
  have hcomp : g ∘ (Fin.castLE hp) = f := by
    funext i
    simp only [Function.comp_apply, g, Fin.val_castLE, dite_eq_left i.isLt]
  refine ⟨s', g, ?_, ?_⟩
  · exact mem_templates s' (by simpa only [s', leaves_map, hs] using hp)
  · change (s.map (Fin.castLE hp)).map g = p
    rw [map_comp, hcomp, hf]

end Formula

theorem mem_assignments {A : Type} (alphabet : List A) (hA : ∀ a, a ∈ alphabet)
    (k : ℕ) (f : Fin k → A) : f ∈ assignments alphabet k := by
  induction k with
  | zero =>
    have he : f = Fin.elim0 := by funext i; exact Fin.elim0 i
    simp [assignments, he]
  | succ k ih =>
    apply List.mem_flatMap.mpr
    refine ⟨f 0, hA _, List.mem_map.mpr ⟨fun i => f i.succ, ih _, ?_⟩⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

end ThreeMachine.Structure

namespace ThreeMachine.Structure
section EffectiveAlphabet
variable {J : Type} [Fintype J] [DecidableEq J]

omit [Fintype J] in
theorem mem_tripleList (jobs : List J) (hjobs : ∀ x, x ∈ jobs) (Z : Triple J) :
    Z ∈ tripleList jobs := by
  obtain ⟨a,b,c,_,_,_,he⟩ := Finset.card_eq_three.mp Z.property
  apply List.mem_filterMap.mpr
  refine ⟨Z.val, List.mem_flatMap.mpr ⟨a, hjobs a,
    List.mem_flatMap.mpr ⟨b, hjobs b, List.mem_map.mpr ⟨c, hjobs c, he.symm⟩⟩⟩, ?_⟩
  simp only [dite_eq_left Z.property]

theorem Atomic.mem_alphabet (jobs : List J) (hjobs : ∀ x, x ∈ jobs) (a : Atomic J) :
    a ∈ alphabet jobs := by
  cases a with
  | constant b => cases b <;> simp [alphabet]
  | threshold frame upper k =>
    apply List.mem_append_left
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨frame, by cases frame <;> simp, List.mem_flatMap.mpr
      ⟨upper, by cases upper <;> simp, List.mem_map.mpr ⟨k, List.mem_finRange _, rfl⟩⟩⟩
  | cone frame kind Z =>
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨frame, by cases frame <;> simp, List.mem_flatMap.mpr
      ⟨kind, List.mem_finRange _, List.mem_map.mpr ⟨Z, mem_tripleList jobs hjobs Z, rfl⟩⟩⟩

end EffectiveAlphabet
end ThreeMachine.Structure

end

end OAI
end

section
-- module DynamicProgram
namespace OAI

section

namespace ThreeMachine.Algorithm
open Structure

namespace Block
variable {J : Type} [Fintype J] [DecidableEq J] {r : J → J → Prop}

omit [Fintype J] [DecidableEq J] in
theorem valid_empty : (empty : Block J).Valid r ∅ := by
  let b : FullBlock r (↑(∅ : Finset J) : Set J) :=
    { length := 0
      time := fun _ => 0
      bounds := by simp
      capacity := by simp
      respects := by simp
      size := by simp }
  exact ⟨b, rfl, rfl⟩

omit [DecidableEq J] in
theorem valid_triple {Z : Finset J} (hc : Z.card = 3)
    (ha : ∀ x ∈ Z, ∀ y ∈ Z, ¬r x y) : (triple : Block J).Valid r Z :=
  ⟨FullBlock.triple ⟨Z,hc⟩ ha, rfl, rfl⟩

theorem valid_append {U V : Finset J} {s t : Block J}
    (hs : s.Valid r U) (ht : t.Valid r V) (hd : Disjoint U V)
    (hb : ∀ x ∈ V, ∀ y ∈ U, ¬r x y) : (append U s t).Valid r (U ∪ V) := by
  obtain ⟨s', hsl, hst⟩ := hs
  obtain ⟨t', htl, htt⟩ := ht
  have hd' : Disjoint (U : Set J) (V : Set J) := Finset.disjoint_coe.mpr hd
  let b := s'.append t' hd' hb
  let c : FullBlock r (↑(U ∪ V) : Set J) :=
    { length := b.length, time := b.time
      bounds := fun x hx => b.bounds x (by simpa using hx)
      capacity := fun k => by simpa using b.capacity k
      respects := fun x hx y hy hxy => b.respects x (by simpa using hx) y (by simpa using hy) hxy
      size := by simpa using b.size }
  refine ⟨c, ?_, ?_⟩
  · change s'.length + t'.length = s.length + t.length
    rw [hsl, htl]
  · funext x
    by_cases hx : x ∈ U <;> simp [c, b, FullBlock.append, append, hx, hsl, hst, htt]

omit [Fintype J] [DecidableEq J] in
theorem Valid.of_eq {U V : Finset J} {s : Block J} (h : s.Valid r U) (he : U = V) :
    s.Valid r V := he ▸ h

end Block

namespace State
variable {J : Type} [Fintype J] [DecidableEq J] {r : J → J → Prop}

omit [Fintype J] in
theorem Compatible.left_subset {W : Finset J} {u : State J} (h : u.Compatible r W) :
    u.left ⊆ W := by
  rw [← h.1]
  exact fun _ hx => Finset.mem_union_left _ (Finset.mem_union_left _ hx)

theorem valid_advance {W : Finset J} {u v : State J} {s t : Block J}
    (hu : u.Compatible r W) (hv : v.Compatible r W) (hs : s.Valid r u.left)
    (hsub : u.upto ⊆ v.left) (ht : t.Valid r (v.left \ u.upto)) :
    (u.advance s t).Valid r v.left := by
  have hs' := Block.valid_append hs
    (Block.valid_triple hu.2.2.2.2.1 hu.2.2.2.2.2.1) hu.2.1 hu.2.2.2.2.2.2.1
  have hd : Disjoint u.upto (v.left \ u.upto) :=
    Finset.disjoint_left.mpr (fun _ hx hy => (Finset.mem_sdiff.mp hy).2 hx)
  have hb : ∀ x ∈ v.left \ u.upto, ∀ y ∈ u.upto, ¬r x y := by
    intro x hx y hy
    have hxr : x ∈ u.right := by
      have hxW := hv.left_subset (Finset.mem_sdiff.mp hx).1
      rw [← hu.1] at hxW
      rcases Finset.mem_union.mp hxW with hp | hr
      · exact ((Finset.mem_sdiff.mp hx).2 hp).elim
      · exact hr
    rcases Finset.mem_union.mp hy with hy | hy
    · exact hu.2.2.2.2.2.2.2.1 x hxr y hy
    · exact hu.2.2.2.2.2.2.2.2 x hxr y hy
  have he : u.upto ∪ (v.left \ u.upto) = v.left := Finset.union_sdiff_of_subset hsub
  exact (Block.valid_append hs' ht hd hb).of_eq he

theorem valid_finish {W : Finset J} {u : State J} {s t : Block J}
    (hu : u.Compatible r W) (hs : s.Valid r u.left) (ht : t.Valid r u.right) :
    (u.finish s t).Valid r W := by
  have hs' := Block.valid_append hs
    (Block.valid_triple hu.2.2.2.2.1 hu.2.2.2.2.2.1) hu.2.1 hu.2.2.2.2.2.2.1
  have hd : Disjoint u.upto u.right := Finset.disjoint_union_left.mpr ⟨hu.2.2.1,hu.2.2.2.1⟩
  have hb : ∀ x ∈ u.right, ∀ y ∈ u.upto, ¬r x y := by
    intro x hx y hy
    exact (Finset.mem_union.mp hy).elim
      (hu.2.2.2.2.2.2.2.1 x hx y) (hu.2.2.2.2.2.2.2.2 x hx y)
  exact (Block.valid_append hs' ht hd hb).of_eq hu.1

omit [Fintype J] in
theorem left_card_strict {W : Finset J} {u v : State J}
    (hu : u.Compatible r W) (hsub : u.upto ⊆ v.left) : u.left.card < v.left.card := by
  have he : u.upto.card = u.left.card + 3 := by
    rw [upto, Finset.card_union_of_disjoint hu.2.1, hu.2.2.2.2.1]
  have := Finset.card_le_card hsub
  omega

end State
end ThreeMachine.Algorithm

namespace ThreeMachine.Algorithm

theorem lookup_mem {K V : Type} [DecidableEq K] {tab : List (K × V)} {k : K} {v : V}
    (h : lookup tab k = some v) : (k,v) ∈ tab := by
  induction tab with
  | nil => simp [lookup] at h
  | cons a xs ih =>
    simp only [lookup] at h
    split_ifs at h with he
    · subst k
      have he' : a.2 = v := Option.some.inj h
      rw [← he']
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem has_iff_mem {K V : Type} [DecidableEq K] (tab : List (K × V)) (k : K) :
    Has tab k ↔ ∃ v, (k,v) ∈ tab := by
  constructor
  · rintro ⟨v,hv⟩
    exact ⟨v, lookup_mem hv⟩
  · induction tab with
    | nil => simp
    | cons a xs ih =>
      rintro ⟨v,hv⟩
      by_cases he : a.1 = k
      · exact ⟨a.2, by simp [lookup, he]⟩
      · rw [List.mem_cons] at hv
        rcases hv with hv | hv
        · exact (he (congrArg Prod.fst hv).symm).elim
        · obtain ⟨v',hv'⟩ := ih ⟨v,hv⟩
          exact ⟨v', by simp only [lookup, ite_eq_right he, hv']⟩

theorem firstResult_some {K V : Type} {f : K → Option V} {ks : List K} {v : V}
    (h : firstResult f ks = some v) : ∃ k ∈ ks, f k = some v := by
  induction ks with
  | nil => simp [firstResult] at h
  | cons k ks ih =>
    cases hf : f k with
    | none =>
      obtain ⟨k',hk',he⟩ := ih (by simpa only [firstResult, hf] using h)
      exact ⟨k', List.mem_cons_of_mem _ hk',he⟩
    | some u =>
      have he : u = v := Option.some.inj (by simpa only [firstResult, hf] using h)
      exact ⟨k,List.mem_cons_self,he ▸ hf⟩

theorem firstResult_has {K V : Type} (f : K → Option V) (ks : List K) :
    (∃ v, firstResult f ks = some v) ↔ ∃ k ∈ ks, ∃ v, f k = some v := by
  constructor
  · rintro ⟨v,hv⟩
    obtain ⟨k,hk,hv⟩ := firstResult_some hv
    exact ⟨k,hk,v,hv⟩
  · induction ks with
    | nil => simp
    | cons k ks ih =>
      rintro ⟨k',hk',v,hv⟩
      cases hf : f k with
      | some u => exact ⟨u, by simp [firstResult,hf]⟩
      | none =>
        have hk : k' ∈ ks := by
          rcases List.mem_cons.mp hk' with he | he
          · subst k'
            rw [hf] at hv
            contradiction
          · exact he
        obtain ⟨u,hu⟩ := ih ⟨k',hk,v,hv⟩
        exact ⟨u, by simpa only [firstResult,hf] using hu⟩

theorem mem_tableOf {K V : Type} (ks : List K) (f : K → Option V) (k : K) (v : V) :
    (k,v) ∈ tableOf ks f ↔ k ∈ ks ∧ f k = some v := by
  rw [tableOf,List.mem_filterMap]
  constructor
  · rintro ⟨a,ha,he⟩
    cases hf : f a with
    | none => simp [hf] at he
    | some b =>
      have hab : (a,b) = (k,v) := Option.some.inj (by simpa [hf] using he)
      cases hab
      exact ⟨ha,hf⟩
  · rintro ⟨hk,hv⟩
    exact ⟨k,hk, by simp [hv]⟩

theorem has_tableOf {K V : Type} [DecidableEq K] (ks : List K) (f : K → Option V) (k : K) :
    Has (tableOf ks f) k ↔ k ∈ ks ∧ ∃ v, f k = some v := by
  rw [has_iff_mem]
  simp only [mem_tableOf, exists_and_left]

namespace Walk
variable {K : Type} {r : K → K → Prop}

theorem of_path {a b : K} (h : Relation.ReflTransGen r a b) : ∃ n, Walk r n a b := by
  induction h with
  | refl => exact ⟨0,.refl _⟩
  | tail _ hs ih => obtain ⟨n,hn⟩ := ih; exact ⟨n+1,.tail hn hs⟩

theorem rank_bound {ρ : K → ℕ} (hr : ∀ a b, r a b → ρ a < ρ b)
    {n a b} (h : Walk r n a b) : n + ρ a ≤ ρ b := by
  induction h with
  | refl => omega
  | tail _ hs ih => have := hr _ _ hs; omega

end Walk
end ThreeMachine.Algorithm

namespace ThreeMachine.Algorithm
open Structure
section DynamicProgram
variable {J : Type} [Fintype J] [DecidableEq J] (r : J → J → Prop) [DecidableRel r]

theorem states_compatible {family triples : List (Finset J)} {W : Finset J} {u : State J}
    (h : u ∈ states r family triples W) : u.Compatible r W := by
  exact of_decide_eq_true (List.mem_filter.mp h).2

omit [DecidableRel r] in
theorem markings_good {tab : List (Finset J × Block J)} {sts : List (State J)} {W : Finset J}
    (htab : TableGood r tab) (hsts : ∀ u ∈ sts, u.Compatible r W) (k : ℕ) :
    MarksGood r W (markings tab sts k) := by
  induction k with
  | zero =>
    intro u s h
    obtain ⟨hu, hs⟩ := (mem_tableOf sts _ u s).mp h
    exact ⟨hsts u hu, htab _ _ (lookup_mem hs)⟩
  | succ k ih =>
    intro v s h
    obtain ⟨hv, hs⟩ := (mem_tableOf sts _ v s).mp h
    refine ⟨hsts v hv, ?_⟩
    cases he : lookup (markings tab sts k) v with
    | some b =>
      have hb : b = s := Option.some.inj (by simpa only [he] using hs)
      exact hb ▸ (ih v b (lookup_mem he)).2
    | none =>
      obtain ⟨⟨u,b⟩, hu, hh⟩ := firstResult_some (by simpa only [he] using hs)
      simp only [tryAdvance] at hh
      split_ifs at hh with hsub
      · cases hg : lookup tab (v.left \ u.upto) with
        | none => simp [hg] at hh
        | some t =>
          have hes : u.advance b t = s := Option.some.inj (by simpa [hg] using hh)
          exact hes ▸ State.valid_advance (ih u b hu).1 (hsts v hv)
            (ih u b hu).2 hsub (htab _ _ (lookup_mem hg))

theorem solve_good {tab : List (Finset J × Block J)} (htab : TableGood r tab)
    (family triples : List (Finset J)) {W : Finset J} {s : Block J}
    (h : solve r tab family triples W = some s) : s.Valid r W := by
  simp only [solve] at h
  split_ifs at h with he
  · subst W
    have hs : Block.empty = s := Option.some.inj h
    exact hs ▸ Block.valid_empty
  · obtain ⟨⟨u,b⟩,hu,hs⟩ := firstResult_some h
    have hg := markings_good r htab (fun v hv => states_compatible r hv) (Fintype.card J) u b hu
    cases ht : lookup tab u.right with
    | none => simp [ht] at hs
    | some t =>
      have hes : u.finish b t = s := Option.some.inj (by simpa [ht] using hs)
      exact hes ▸ State.valid_finish hg.1 hg.2 (htab _ _ (lookup_mem ht))

theorem layers_good (family triples : List (Finset J)) (k : ℕ) :
    TableGood r (layers r family triples k) := by
  induction k with
  | zero =>
    intro W s h
    have he : (W,s) = (∅,Block.empty) := by simpa only [layers, List.mem_singleton] using h
    cases he
    exact Block.valid_empty
  | succ k ih =>
    intro W s h
    exact solve_good r ih family triples ((mem_tableOf family _ W s).mp h).2

omit [Fintype J] [DecidableRel r] in
theorem markings_stay {tab : List (Finset J × Block J)} {sts : List (State J)}
    {v : State J} (hv : v ∈ sts) {k : ℕ} (h : Has (markings tab sts k) v) :
    Has (markings tab sts (k+1)) v := by
  obtain ⟨s,hs⟩ := h
  apply (has_tableOf sts _ v).mpr
  exact ⟨hv,s,by simp only [hs]⟩

omit [Fintype J] [DecidableRel r] in
theorem markings_mono {tab : List (Finset J × Block J)} {sts : List (State J)}
    {v : State J} (hv : v ∈ sts) {k l : ℕ} (h : Has (markings tab sts k) v) (hkl : k ≤ l) :
    Has (markings tab sts l) v := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hkl
  clear hkl
  induction d with
  | zero => exact h
  | succ d ih => exact markings_stay hv ih

omit [Fintype J] [DecidableRel r] in
theorem markings_step {tab : List (Finset J × Block J)} {sts : List (State J)}
    {u v : State J} (hv : v ∈ sts) (hsub : u.upto ⊆ v.left)
    (hgap : Has tab (v.left \ u.upto)) {k : ℕ} (hu : Has (markings tab sts k) u) :
    Has (markings tab sts (k+1)) v := by
  apply (has_tableOf sts _ v).mpr
  refine ⟨hv, ?_⟩
  cases he : lookup (markings tab sts k) v with
  | some b => exact ⟨b,rfl⟩
  | none =>
    apply (firstResult_has _ _).mpr
    obtain ⟨s,hs⟩ := hu
    obtain ⟨t,ht⟩ := hgap
    exact ⟨(u,s),lookup_mem hs,u.advance s t,by simp [tryAdvance,hsub,ht]⟩

omit [Fintype J] [DecidableRel r] in
theorem markings_walk {tab : List (Finset J × Block J)} {sts : List (State J)}
    {u v : State J} {k : ℕ} (hu : u ∈ sts) (hinit : Has tab u.left)
    (h : Walk (Arc tab sts) k u v) : Has (markings tab sts k) v := by
  induction h with
  | refl => exact (has_tableOf sts _ _).mpr ⟨hu,hinit⟩
  | tail _ hs ih => exact markings_step hs.2.1 hs.2.2.1 hs.2.2.2 (ih hu hinit)

theorem solve_complete_path {tab : List (Finset J × Block J)} {family triples : List (Finset J)}
    {W : Finset J} {u v : State J} (hu : u ∈ states r family triples W)
    (hv : v ∈ states r family triples W) (hinit : Has tab u.left) (hfinal : Has tab v.right)
    (hpath : Relation.ReflTransGen (Arc tab (states r family triples W)) u v) :
    ∃ s, solve r tab family triples W = some s := by
  by_cases he : W = ∅
  · exact ⟨Block.empty, by simp [solve,he]⟩
  obtain ⟨k,hk⟩ := Walk.of_path hpath
  have hbound : k ≤ Fintype.card J := by
    have hb := hk.rank_bound (ρ := fun s => s.left.card) (fun a b hh =>
      State.left_card_strict (states_compatible r hh.1) hh.2.2.1)
    have hc := Finset.card_le_univ v.left
    omega
  have hm := markings_mono hv (markings_walk hu hinit hk) hbound
  obtain ⟨s,hs⟩ := hm
  obtain ⟨t,ht⟩ := hfinal
  simp only [solve,ite_eq_right he]
  apply (firstResult_has _ _).mpr
  exact ⟨(v,s),lookup_mem hs,v.finish s t,by simp [ht]⟩

end DynamicProgram
end ThreeMachine.Algorithm

namespace ThreeMachine.Algorithm
open Structure
open scoped Classical
section EraseSplits
variable {J A : Type} [Fintype J] [DecidableEq J] {r : J → J → Prop}
    {atoms : A → Set J} {W : Set J}

theorem State.erase_compatible (v : SplitVertex r atoms W) :
    (erase v).Compatible r W.toFinset := by
  classical
  refine ⟨?_, ?_, ?_, ?_, v.middle.property, ?_, ?_, ?_, ?_⟩
  · ext x
    simpa only [erase, Finset.mem_union, Set.mem_toFinset, or_assoc] using (v.partition x).symm
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp v.left_middle (Set.mem_toFinset.mp hx) hy
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp v.left_right (Set.mem_toFinset.mp hx) (Set.mem_toFinset.mp hy)
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp v.middle_right hx (Set.mem_toFinset.mp hy)
  · exact v.antichain
  · intro x hx y hy
    exact v.no_middle_left x hx y (Set.mem_toFinset.mp hy)
  · intro x hx y hy
    exact v.no_right_left x (Set.mem_toFinset.mp hx) y (Set.mem_toFinset.mp hy)
  · intro x hx y hy
    exact v.no_right_middle x (Set.mem_toFinset.mp hx) y hy

theorem State.erase_candidate (v : SplitVertex r atoms W) {F : Set J} (hF : v.left = W ∩ F) :
    candidate W.toFinset F.toFinset v.middle.val = erase v := by
  classical
  apply State.ext
  · ext x
    change x ∈ W.toFinset ∩ F.toFinset ↔ x ∈ v.left.toFinset
    simp only [Finset.mem_inter, Set.mem_toFinset,hF,Set.mem_inter_iff]
  · rfl
  · ext x
    change x ∈ W.toFinset \ ((W.toFinset ∩ F.toFinset) ∪ v.middle.val) ↔ x ∈ v.right.toFinset
    simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union, Set.mem_toFinset]
    rw [v.right_eq]
    simp only [Set.mem_sdiff, Set.mem_union, Finset.mem_coe, hF, Set.mem_inter_iff]

theorem State.erase_mem_states [DecidableRel r] (family triples : List (Finset J))
    (hfamily : ∀ F, Described atoms F 10000 → F.toFinset ∈ family)
    (htriples : ∀ Z : Triple J, Z.val ∈ triples) (v : SplitVertex r atoms W) :
    erase v ∈ states r family triples W.toFinset := by
  classical
  obtain ⟨F,hF,he⟩ := v.small_left
  apply List.mem_filter.mpr
  refine ⟨List.mem_flatMap.mpr ⟨F.toFinset,hfamily F hF,
    List.mem_map.mpr ⟨v.middle.val,htriples v.middle, erase_candidate v he⟩⟩, ?_⟩
  exact decide_eq_true (erase_compatible v)

theorem State.erase_inclusion {u v : SplitVertex r atoms W}
    (h : u.left ∪ u.middle.val ⊆ v.left) : (erase u).upto ⊆ (erase v).left := by
  classical
  intro x hx
  apply Set.mem_toFinset.mpr
  apply h
  rcases Finset.mem_union.mp hx with hx | hx
  · exact Or.inl (Set.mem_toFinset.mp hx)
  · exact Or.inr hx

theorem State.erase_gap (u v : SplitVertex r atoms W) :
    (v.left \ (u.left ∪ u.middle.val)).toFinset = (erase v).left \ (erase u).upto := by
  classical
  ext x
  simp only [Set.mem_toFinset, Set.mem_sdiff, Set.mem_union, Finset.mem_coe,
    erase, upto, Finset.mem_sdiff, Finset.mem_union]

end EraseSplits

section Completeness
variable {J A : Type} [Fintype J] [DecidableEq J] (r : J → J → Prop) [DecidableRel r]
    (atoms : A → Set J) (family triples : List (Finset J))
    (hfamily : ∀ F, Described atoms F 10000 → F.toFinset ∈ family)
    (htriples : ∀ Z : Triple J, Z.val ∈ triples)

include hfamily htriples in
theorem layers_complete (k : ℕ) {W : Set J} (h : AcceptedAt r atoms k W) :
    Has (layers r family triples k) W.toFinset := by
  classical
  induction k generalizing W with
  | zero =>
    have he : W = ∅ := h.2
    subst W
    refine ⟨Block.empty, ?_⟩
    simp [layers, lookup]
  | succ k ih =>
    apply (has_tableOf family _ W.toFinset).mpr
    refine ⟨hfamily W h.1, ?_⟩
    rcases h.2 with he | ⟨u,v,hu,hp,hv⟩
    · subst W
      exact ⟨Block.empty,by simp [solve]⟩
    · have hstate (s : SplitVertex r atoms W) := State.erase_mem_states family triples hfamily htriples s
      apply solve_complete_path r (hstate u) (hstate v) (ih hu) (ih hv)
      clear hv
      induction hp with
      | refl => exact .refl
      | @tail v w _ hs ihp =>
        refine ihp.tail ⟨hstate v,hstate w,State.erase_inclusion hs.1,?_⟩
        rw [← State.erase_gap]
        simpa only [← Set.toFinite_toFinset] using ih hs.2

end Completeness
end ThreeMachine.Algorithm

end

end OAI
end

section
-- module SchedulingAlgorithm
namespace OAI

section

namespace ThreeMachine.Algorithm
section Closure
variable {n : ℕ}

theorem closureStep_mono (E R : Finset (Fin n × Fin n)) : R ⊆ closureStep E R :=
  Finset.subset_union_left

theorem closureTable_mono (G : Instance n) {k l : ℕ} (h : k ≤ l) :
    closureTable G k ⊆ closureTable G l := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction d with
  | zero => exact Finset.Subset.refl _
  | succ d ih =>
    change closureTable G k ⊆ closureTable G ((k+d)+1)
    rw [closureTable_succ]
    exact ih.trans (closureStep_mono G.edges.toFinset (closureTable G (k+d)))

theorem closureTable_sound (G : Instance n) (k : ℕ) {x y : Fin n}
    (h : (x,y) ∈ closureTable G k) : G.order x y := by
  induction k generalizing x y with
  | zero => exact .single (by simpa [Instance.edge] using h)
  | succ k ih =>
    rw [closureTable_succ, closureStep, Finset.mem_union] at h
    rcases h with h | h
    · exact ih h
    · obtain ⟨v,hv,he⟩ := (Finset.mem_filter.mp h).2
      exact (ih hv).tail (by simpa [Instance.edge] using he)

theorem walk_closure (G : Instance n) {k : ℕ} {x y : Fin n}
    (h : Walk G.edge (k+1) x y) : (x,y) ∈ closureTable G k := by
  generalize he : k+1 = l at h
  induction h generalizing k with
  | refl => omega
  | @tail m x y z hp hz ih =>
    cases k with
    | zero =>
      have hm : m = 0 := by omega
      subst m
      cases hp
      simpa [Instance.edge] using hz
    | succ k =>
      have hm : k+1 = m := by omega
      have hh := ih hm
      rw [closureTable_succ, closureStep]
      apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,y,hh,by simpa [Instance.edge] using hz⟩

theorem transGen_walk (G : Instance n) {x y : Fin n} (h : G.order x y) :
    ∃ k, Walk G.edge (k+1) x y := by
  induction h with
  | single he => exact ⟨0,.tail (.refl _) he⟩
  | tail _ he ih => obtain ⟨k,hk⟩ := ih; exact ⟨k+1,.tail hk he⟩

theorem reachable_iff (G : Instance n) (hG : G.acyclic) (x y : Fin n) :
    reachable G x y ↔ G.order x y := by
  classical
  constructor
  · exact closureTable_sound G n
  · intro h
    obtain ⟨k,hk⟩ := transGen_walk G h
    have hr : ∀ a b, G.edge a b → Structure.jobRank G.order a < Structure.jobRank G.order b :=
      fun _ _ he => Structure.jobRank_strict G.order hG
        (fun {_ _ _} h₁ h₂ => h₁.trans h₂) (.single he)
    have hb := hk.rank_bound hr
    have hy := Structure.jobRank_bounds G.order y
    apply closureTable_mono G (show k ≤ n by omega)
    exact walk_closure G hk

end Closure
end ThreeMachine.Algorithm

namespace ThreeMachine.Structure
section EffectiveFamily
variable {J : Type} [Fintype J] [DecidableEq J]

theorem Formula.coe_evalFinset {A : Type} (atoms : A → Finset J) (p : Formula A) :
    (p.evalFinset atoms : Set J) = p.eval (fun a => (atoms a : Set J)) := by
  induction p with
  | leaf a b => cases b <;> simp [evalFinset, eval]
  | conj p q ihp ihq | disj p q ihp ihq => simp [evalFinset, eval, ihp, ihq]

open scoped Classical in
theorem effectiveFamily_complete (r : J → J → Prop) [DecidableRel r]
    (rank reverseRank : J → ℕ) (jobs : List J) (hjobs : ∀ x, x ∈ jobs)
    (K : ℕ) (W : Set J) (hW : Described (Atomic.eval r rank reverseRank) W K) :
    W.toFinset ∈ effectiveFamily r rank reverseRank jobs K := by
  classical
  obtain ⟨p,hp,hpk⟩ := hW
  obtain ⟨s,f,hs,he⟩ := Formula.template_representation p hpk
  apply List.mem_flatMap.mpr
  refine ⟨f,mem_assignments _ (Atomic.mem_alphabet jobs hjobs) K f,
    List.mem_map.mpr ⟨s,hs,?_⟩⟩
  apply Finset.coe_injective
  rw [Formula.coe_evalFinset,he]
  have ha : (fun a => (↑(Finset.univ.filter (Atomic.eval r rank reverseRank a)) : Set J)) =
      Atomic.eval r rank reverseRank := by
    funext a; ext x
    exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ x))
  rw [ha,hp]
  simp

end EffectiveFamily
end ThreeMachine.Structure

namespace ThreeMachine

end ThreeMachine

namespace ThreeMachine.Algorithm
open Structure

theorem fullSolve_sound {m : ℕ} (r : Fin m → Fin m → Prop) [DecidableRel r]
    {s : Block (Fin m)} (hs : fullSolve r = some s) : s.Valid r Finset.univ :=
  layers_good r _ _ m _ _ (lookup_mem hs)

theorem fullSolve_complete {m : ℕ} (r : Fin m → Fin m → Prop) [DecidableRel r]
    (hirr : ∀ x, ¬r x x) (htrans : ∀ ⦃x y z⦄, r x y → r y z → r x z)
    (h : ∃ p : Layout (Fin m), p.Full r) : ∃ s, fullSolve r = some s := by
  classical
  have ha := (accepted_iff_full_layout r (jobRank r) (reverseJobRank r) htrans
    (fun x => by simpa using (jobRank_bounds r x).2)
    (fun x => by simpa using (reverseJobRank_bounds r x).2)
    (jobRank_injective r) (reverseJobRank_injective r)
    (fun _ _ hxy => jobRank_strict r hirr htrans hxy)
    (fun _ _ hxy => reverseJobRank_strict r hirr htrans hxy)).mpr h
  have hh := layers_complete r (Atomic.eval r (jobRank r) (reverseJobRank r))
    (effectiveFamily r (jobRank r) (reverseJobRank r) (List.finRange m) 10000)
    ((tripleList (List.finRange m)).map Subtype.val)
    (fun F hF => effectiveFamily_complete r _ _ _ (fun _ => List.mem_finRange _) 10000 F hF)
    (fun Z => List.mem_map.mpr ⟨Z,mem_tripleList _ (fun _ => List.mem_finRange _) Z,rfl⟩) m
    (by simpa only [Fintype.card_fin] using ha)
  simpa only [Set.toFinset_univ,fullSolve,Has] using hh

theorem reachable_trans {n : ℕ} (G : Instance n) (hG : G.acyclic) :
    ∀ ⦃x y z⦄, reachable G x y → reachable G y z → reachable G x z := by
  intro x y z hxy hyz
  exact (reachable_iff G hG x z).mpr
    (((reachable_iff G hG x y).mp hxy).trans ((reachable_iff G hG y z).mp hyz))

theorem reachable_irrefl {n : ℕ} (G : Instance n) (hG : G.acyclic) :
    ∀ x, ¬reachable G x x := fun x hx => hG x ((reachable_iff G hG x x).mp hx)

theorem Block.restrict_feasible {n T : ℕ} (G : Instance n) (hG : G.acyclic) (hn : n ≤ 3*T)
    {s : Block (Fin (3*T))} (hs : s.Valid (paddedOrder (reachable G) (3*T)) Finset.univ) :
    Feasible G T (fun x => s.time (Fin.castLE hn x)) := by
  obtain ⟨b,hbl,hbt⟩ := hs
  have hbT : b.length = T := by
    have hc := b.size
    simp only [Finset.coe_univ,Set.ncard_univ,Nat.card_eq_fintype_card,Fintype.card_fin] at hc
    omega
  have hbcap (t : ℕ) : (Finset.univ.filter (fun x => b.time x = t)).card ≤ 3 := by
    have hc := b.capacity t
    have he : {x | x ∈ (↑(Finset.univ : Finset (Fin (3*T))) : Set (Fin (3*T))) ∧ b.time x = t} =
        (Finset.univ.filter (fun x => b.time x = t) : Set (Fin (3*T))) := by ext x; simp
    rw [he,Set.ncard_coe_finset] at hc
    exact hc
  rw [← hbt]
  refine ⟨?_,?_,?_⟩
  · intro x
    simpa only [hbT] using b.bounds (Fin.castLE hn x) (by simp)
  · intro t
    apply le_trans _ (hbcap t)
    apply Finset.card_le_card_of_injOn (Fin.castLE hn)
    · intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hx).2⟩
    · intro x _ y _ hxy
      exact Fin.castLE_injective hn hxy
  · intro x y he
    apply b.respects _ (by simp) _ (by simp)
    apply (paddedOrder_castLE hn x y).mpr
    exact (reachable_iff G hG x y).mpr (.single he)

theorem scheduleAt_sound {n T : ℕ} (G : Instance n) (hG : G.acyclic)
    {time : Fin n → ℕ} (h : scheduleAt G T = some time) : Feasible G T time := by
  unfold scheduleAt at h
  split_ifs at h with hn
  · obtain ⟨s,hs,hstime⟩ := Option.map_eq_some_iff.mp h
    subst time
    exact Block.restrict_feasible G hG hn (fullSolve_sound _ hs)

theorem scheduleAt_complete {n T : ℕ} (G : Instance n) (hG : G.acyclic)
    (hf : ∃ time, Feasible G T time) : ∃ time, scheduleAt G T = some time := by
  obtain ⟨time,htime⟩ := hf
  have hn := htime.size_bound
  have hp := (feasible_iff_padded_layout G hn).mp ⟨time,htime⟩
  have hrel : paddedOrder (reachable G) (3*T) = paddedOrder G.order (3*T) := by
    have hr : reachable G = G.order := by funext x y; exact propext (reachable_iff G hG x y)
    rw [hr]
  obtain ⟨s,hs⟩ := fullSolve_complete (paddedOrder (reachable G) (3*T))
    (paddedOrder_irrefl (reachable_irrefl G hG)) (paddedOrder_trans (reachable_trans G hG))
    (by simpa only [hrel] using hp)
  exact ⟨fun x => s.time (Fin.castLE hn x),by simp [scheduleAt,hn,hs]⟩

theorem scheduleAt_none_iff {n T : ℕ} (G : Instance n) (hG : G.acyclic) :
    scheduleAt G T = none ↔ ¬∃ time, Feasible G T time := by
  constructor
  · intro hn he
    obtain ⟨time,htime⟩ := scheduleAt_complete G hG he
    rw [hn] at htime
    contradiction
  · intro he
    cases h : scheduleAt G T with
    | none => rfl
    | some time => exact (he ⟨time,scheduleAt_sound G hG h⟩).elim

end ThreeMachine.Algorithm

namespace ThreeMachine.Algorithm
open Structure

theorem best_spec {n : ℕ} (G : Instance n) (hG : G.acyclic) (k : ℕ) :
    BestSpec G k (best G k) := by
  induction k with
  | zero => intro T hT hTk; omega
  | succ k ih =>
    dsimp only [best]
    cases hb : best G k with
    | some a =>
      rw [hb] at ih
      rcases a with ⟨T,time⟩
      obtain ⟨hT,hTk,hfeas,hmin⟩ := ih
      refine ⟨hT,by omega,hfeas,?_⟩
      intro T' time' hT' hT'k hf'
      by_cases hh : T' ≤ k
      · exact hmin T' time' hT' hh hf'
      · omega
    | none =>
      rw [hb] at ih
      change ∀ T, 1 ≤ T → T ≤ k → ¬∃ time, Feasible G T time at ih
      cases hs : scheduleAt G (k+1) with
      | none =>
        intro T hT hTk
        by_cases he : T = k+1
        · subst T
          exact (scheduleAt_none_iff G hG).mp hs
        · exact ih T hT (by omega)
      | some time =>
        refine ⟨by omega,le_rfl,scheduleAt_sound G hG hs,?_⟩
        intro T' time' hT' hT'k hf'
        by_contra hlt
        exact ih T' hT' (by omega) ⟨time',hf'⟩

theorem serial_feasible {n : ℕ} (G : Instance n) (hG : G.acyclic) :
    Feasible G n (jobRank (reachable G)) := by
  refine ⟨jobRank_bounds _,?_,?_⟩
  · intro t
    apply le_trans (show _ ≤ 1 from ?_) (by omega : 1 ≤ 3)
    apply Finset.card_le_one.mpr
    intro x hx y hy
    apply jobRank_injective (reachable G)
    exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
  · intro x y he
    exact jobRank_strict (reachable G) (reachable_irrefl G hG) (reachable_trans G hG)
      ((reachable_iff G hG x y).mpr (.single he))

theorem best_optimum {n : ℕ} (G : Instance n) (hn : 1 ≤ n) (hG : G.acyclic) :
    ∃ T time, best G n = some (T,time) ∧ Feasible G T time ∧
      ∀ T' time', Feasible G T' time' → T ≤ T' := by
  have hs := best_spec G hG n
  cases hb : best G n with
  | none =>
    rw [hb] at hs
    exact (hs n hn le_rfl ⟨_,serial_feasible G hG⟩).elim
  | some a =>
    rw [hb] at hs
    rcases a with ⟨T,time⟩
    obtain ⟨_,hTn,hf,hmin⟩ := hs
    refine ⟨T,time,rfl,hf,?_⟩
    intro T' time' hf'
    have hT' : 1 ≤ T' := by
      have := hf'.1 ⟨0,by omega⟩
      omega
    by_cases hle : T' ≤ n
    · exact hmin T' time' hT' hle hf'
    · omega

theorem output_correct {n : ℕ} (G : Instance n) (hn : 1 ≤ n) (hG : G.acyclic)
    (deadline : Option ℕ) : CorrectOutput G deadline (output G deadline) := by
  cases deadline with
  | none =>
    obtain ⟨T,time,hbest,hf,hmin⟩ := best_optimum G hn hG
    exact ⟨T,time,hf,hmin,by simp [output,hbest]⟩
  | some T =>
    cases hs : scheduleAt G T with
    | none => exact Or.inl ⟨by simp [output,hs],(scheduleAt_none_iff G hG).mp hs⟩
    | some time => exact Or.inr ⟨time,scheduleAt_sound G hG hs,by simp [output,hs]⟩

end ThreeMachine.Algorithm

end

end OAI
end

section
-- module StackMachine
namespace OAI

section

namespace ThreeMachine.StackCompiler

theorem head_stackTape (xs : List Bool) : unsymbol (stackTape xs).head = xs.head? := by
  cases xs with
  | nil => rfl
  | cons b xs => exact unsymbol_symbol b

theorem tape_two_phases (a : Action) (xs : List Bool) :
    applyTape (phaseTwo a (middleTape a xs).head) (middleTape a xs) = stackTape (a.apply xs) := by
  cases a with
  | stay => simp [applyTape, phaseTwo, middleTape, phaseOne, Action.apply]
  | pop =>
    change (((stackTape xs).write 0).move .right).write
      (((stackTape xs).write 0).move .right).head = stackTape xs.tail
    rw [Turing.Tape.write_self]
    simp only [stackTape, Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.write_mk',
      Turing.Tape.move_right_mk', Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
      blank_cons]
    cases xs <;> rfl
  | push b =>
    change (((stackTape xs).write (stackTape xs).head).move .left).write (symbol b) =
      stackTape (b :: xs)
    rw [Turing.Tape.write_self]
    simp only [stackTape, Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.move_left_mk',
      Turing.Tape.write_mk', Turing.ListBlank.tail_mk,
      List.tail_nil, List.tail_cons, List.map_cons, Turing.ListBlank.cons_mk]

section Compilation
variable {k : ℕ} {Q : Type} [Fintype Q] (P : Program k Q)

theorem step_ready {c : TapeCfg (k := k) (Q := Q)} {s : State k Q}
    (h : Relates P c s) :
    (compile P).step c =
      (P.transition s.control (fun j => (s.store j).head?)).map (fun qa => middleCfg qa s.store) := by
  have ht : (fun j => unsymbol (c.tapes j).head) = fun j => (s.store j).head? := by
    funext j
    rw [h.2 j, head_stackTape]
  unfold Machine.step compile
  simp only [h.1, ht]
  cases he : P.transition s.control (fun j => (s.store j).head?) with
  | none => rfl
  | some qa =>
    apply congrArg some
    congr 1
    funext j
    dsimp only
    rw [h.2 j]
    rfl

theorem step_middle (qa : Q × Actions k) (s : Store k) :
    (compile P).step (middleCfg qa s) =
      some (readyCfg ⟨qa.1,fun j => (qa.2 j).apply (s j)⟩) := by
  unfold Machine.step compile middleCfg
  simp only [read_numberControl]
  apply congrArg some
  congr 1
  funext j
  exact tape_two_phases (qa.2 j) (s j)

theorem halted_iff {c : TapeCfg (k := k) (Q := Q)} {s : State k Q}
    (h : Relates P c s) : (compile P).step c = none ↔ P.step s = none := by
  rw [step_ready P h]
  unfold Program.step
  cases P.transition s.control (fun j => (s.store j).head?) <;> simp

theorem two_steps {c : TapeCfg (k := k) (Q := Q)} {s : State k Q}
    (h : Relates P c s) :
    Relates P ((fun d => ((compile P).step d).getD d)^[2] c) ((P.step s).getD s) := by
  rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [step_ready P h]
  cases he : P.transition s.control (fun j => (s.store j).head?) with
  | none =>
    simp only [Option.map_none, Option.getD_none]
    rw [step_ready P h, he]
    simpa [Program.step, he] using h
  | some qa =>
    simp only [Option.map_some, Option.getD_some, step_middle]
    simp [Program.step, he]

theorem simulate {c : TapeCfg (k := k) (Q := Q)} {s : State k Q}
    (h : Relates P c s) (n : ℕ) :
    Relates P ((fun d => ((compile P).step d).getD d)^[2*n] c)
      ((fun d => (P.step d).getD d)^[n] s) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [Nat.mul_succ, Nat.add_comm (2*n) 2, Function.iterate_add_apply]
    simpa only [Function.iterate_succ_apply'] using two_steps P ih

theorem relates_initial (input : List Bool) :
    Relates P ((compile P).initial input) ⟨P.initial, initialStore input⟩ := by
  refine ⟨read_zero P, ?_⟩
  intro i
  change Turing.Tape.mk₁ (if i = 0 then input.map bitSymbol else []) =
    Turing.Tape.mk₁ ((if i = 0 then input else []).map symbol)
  split_ifs <;> rfl

theorem simulate_initial (input : List Bool) (n : ℕ) :
    Relates P ((compile P).run input (2*n)) (P.run (initialStore input) n) :=
  simulate P (relates_initial P input) n

theorem compile_produces (input out : List Bool) (bound : ℕ)
    (h : ∃ n ≤ bound, P.step (P.run (initialStore input) n) = none ∧
      (P.run (initialStore input) n).store 0 = out) :
    (compile P).Produces input out (2*bound) := by
  obtain ⟨n,hn,hh,ho⟩ := h
  have hs := simulate_initial P input n
  refine ⟨2*n, by omega, (halted_iff P hs).mpr hh, ?_⟩
  rw [hs.2 0, ho]
  exact Turing.Tape.mk'_right₀ _ _

end Compilation
namespace Program
variable {k : ℕ} {Q R S : Type}

theorem Exec.iterate {P : Program k Q} {s t : State k Q} {n : ℕ}
    (h : Exec P s n t) : (fun c => (P.step c).getD c)^[n] s = t := by
  induction h with
  | halt => rfl
  | next he _ ih => simpa only [Function.iterate_succ_apply, he, Option.getD_some] using ih

theorem Exec.halted {P : Program k Q} {s t : State k Q} {n : ℕ}
    (h : Exec P s n t) : P.step t = none := by
  induction h with
  | halt h => exact h
  | next _ _ ih => exact ih

theorem Exec.continue {P : Program k Q} {P' : Program k R} (f : Q → R)
    (hs : ∀ s t, P.step s = some t →
      P'.step (State.mapControl f s) = some (State.mapControl f t))
    {s t : State k Q} {u : State k R} {n m : ℕ} (h : Exec P s n t)
    (ht : Exec P' (State.mapControl f t) m u) :
    Exec P' (State.mapControl f s) (n+m) u := by
  induction h with
  | halt => simpa only [Nat.zero_add] using ht
  | next he _ ih => simpa only [Nat.add_right_comm] using Exec.next (hs _ _ he) (ih ht)

theorem lift_step (P : Program k Q) (P' : Program k R) (f : Q → R)
    (h : ∀ q heads q' a, P.transition q heads = some (q',a) →
      P'.transition (f q) heads = some (f q',a))
    (s t : State k Q) (he : P.step s = some t) :
    P'.step (State.mapControl f s) = some (State.mapControl f t) := by
  unfold step at he
  cases hh : P.transition s.control (fun i => (s.store i).head?) with
  | none => simp [hh] at he
  | some qa =>
    have het : t = ⟨qa.1,fun i => (qa.2 i).apply (s.store i)⟩ := by
      simpa [hh] using he.symm
    subst t
    simp [step, State.mapControl, h _ _ _ _ hh]

theorem seq_left_step (P : Program k Q) (P' : Program k R)
    (s t : State k Q) (h : P.step s = some t) :
    (seq P P').step (State.mapControl Sum.inl s) = some (State.mapControl Sum.inl t) := by
  apply lift_step P (seq P P') Sum.inl _ s t h
  intro q heads q' a ha
  simp [seq,ha]

theorem seq_right_exec (P : Program k Q) {P' : Program k R}
    {s t : State k R} {n : ℕ} (h : Exec P' s n t) :
    Exec (seq P P') (State.mapControl Sum.inr s) n (State.mapControl Sum.inr t) := by
  induction h with
  | halt he =>
    apply Exec.halt
    unfold step at he ⊢
    cases hh : P'.transition s.control (fun i => (s.store i).head?) <;> simp_all [seq,State.mapControl]
  | next he _ ih =>
    apply Exec.next _ ih
    apply lift_step P' (seq P P') Sum.inr _ _ _ he
    intro q heads q' a ha
    simp [seq, ha]

theorem seq_exec {P : Program k Q} {P' : Program k R} {s t : Store k}
    {q : Q} {r : R} {n m : ℕ} (h : Exec P ⟨P.initial,s⟩ n ⟨q,t⟩)
    {u : Store k} (h' : Exec P' ⟨P'.initial,t⟩ m ⟨r,u⟩) :
    Exec (seq P P') ⟨(seq P P').initial,s⟩ (n+m+1) ⟨Sum.inr r,u⟩ := by
  have hh := h.halted
  have hs : (seq P P').step ⟨Sum.inl q,t⟩ = some ⟨Sum.inr P'.initial,t⟩ := by
    unfold step at hh ⊢
    cases ht : P.transition q (fun i => (t i).head?) <;> simp_all [seq, stayActions,Action.apply]
  have hx := h.continue Sum.inl (seq_left_step P P') (Exec.next hs (seq_right_exec P h'))
  simpa only [State.mapControl, seq, Nat.add_assoc] using hx

theorem instruction_exec (a : Heads k → Actions k) (s : Store k) :
    Exec (instruction a) ⟨false,s⟩ 1
      ⟨true,fun i => (a (fun j => (s j).head?) i).apply (s i)⟩ := by
  apply Exec.next (by rfl)
  exact Exec.halt rfl

theorem loop_body_step (test : Heads k → Bool) (P : Program k Q)
    (s t : State k Q) (h : P.step s = some t) :
    (loop test P).step (State.mapControl some s) = some (State.mapControl some t) := by
  apply lift_step P (loop test P) some _ s t h
  intro q heads q' a ha
  simp [loop,ha]

theorem loop_stop (test : Heads k → Bool) (P : Program k Q) (s : Store k)
    (h : test (fun i => (s i).head?) = false) :
    Exec (loop test P) ⟨none,s⟩ 0 ⟨none,s⟩ := by
  exact Exec.halt (by simp [step,loop,h])

theorem loop_iterate (test : Heads k → Bool) {P : Program k Q} {s t u : Store k}
    {q : Q} {n m : ℕ} (hs : test (fun i => (s i).head?) = true)
    (h : Exec P ⟨P.initial,s⟩ n ⟨q,t⟩)
    (hrest : Exec (loop test P) ⟨none,t⟩ m ⟨none,u⟩) :
    Exec (loop test P) ⟨none,s⟩ (n+m+2) ⟨none,u⟩ := by
  have hstart : (loop test P).step ⟨none,s⟩ = some ⟨some P.initial,s⟩ := by
    simp [step,loop,hs,stayActions,Action.apply]
  have hhalt := h.halted
  have hend : (loop test P).step ⟨some q,t⟩ = some ⟨none,t⟩ := by
    unfold step at hhalt ⊢
    cases ht : P.transition q (fun i => (t i).head?) <;>
      simp_all [loop,stayActions,Action.apply]
  have hb := h.continue some (loop_body_step test P) (Exec.next hend hrest)
  convert Exec.next hstart hb using 1
  omega

end Program
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
namespace Program
variable {k : ℕ}

theorem transfer_instruction {src dst : Fin (k+1)} (hne : src ≠ dst)
    (b : Bool) (xs : List Bool) (s : Store k) (hs : s src = b :: xs) :
    Exec (instruction (transferActions src dst)) ⟨false,s⟩ 1
      ⟨true,transferOnce src dst b xs s⟩ := by
  have h := instruction_exec (transferActions src dst) s
  convert h using 1
  congr 1
  funext i
  by_cases hi : i = src
  · subst i
    simp [transferOnce, transferActions, hne, hs, Action.apply]
  · by_cases hd : i = dst
    · subst i
      simp [transferOnce, transferActions, hne.symm, hs, Action.apply]
    · simp [transferOnce, transferActions,hi,hd,Action.apply]

theorem transfer_result_once {src dst : Fin (k+1)} (hne : src ≠ dst)
    (b : Bool) (xs : List Bool) (s : Store k) (hs : s src = b::xs) :
    transferResult src dst (transferOnce src dst b xs s) = transferResult src dst s := by
  funext i
  by_cases hi : i = dst
  · subst i
    simp [transferResult,transferOnce,hne,hs,List.reverse_cons,List.append_assoc]
  · by_cases hsrc : i = src
    · subst i
      simp [transferResult,transferOnce,hne]
    · simp [transferResult,transferOnce,hi,hsrc]

theorem transfer_exec {src dst : Fin (k+1)} (hne : src ≠ dst) (s : Store k) :
    Exec (transfer src dst) ⟨none,s⟩ (3*(s src).length) ⟨none,transferResult src dst s⟩ := by
  generalize he : s src = xs
  induction xs generalizing s with
  | nil =>
    have hr : transferResult src dst s = s := by
      funext i
      by_cases hd : i = dst
      · subst i; simp [transferResult,he]
      · by_cases hs : i = src
        · subst i; simp [transferResult,he,hne]
        · simp [transferResult,hd,hs]
    rw [hr]
    exact loop_stop _ _ s (by simp [he])
  | cons b xs ih =>
    let s' := transferOnce src dst b xs s
    have hs' : s' src = xs := by simp [s',transferOnce,hne]
    have hrest := ih s' hs'
    rw [transfer_result_once hne b xs s he] at hrest
    have hbody := transfer_instruction hne b xs s he
    have hx := loop_iterate (fun h => (h src).isSome) (by simp [he]) hbody hrest
    convert hx using 1 <;> first | rfl | simp only [List.length_cons]; omega

end Program
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler.Program
variable {k : ℕ}

theorem pop_instruction (src : Fin (k+1)) (s : Store k) :
    Exec (instruction (fun _ => popActions src)) ⟨false,s⟩ 1
      ⟨true,Function.update s src (s src).tail⟩ := by
  convert instruction_exec (fun _ => popActions src) s using 1
  congr 1
  funext i
  by_cases h : i = src <;> simp [popActions,Action.apply,h]

theorem clear_exec (src : Fin (k+1)) (s : Store k) :
    Exec (clear src) ⟨none,s⟩ (3*(s src).length) ⟨none,Function.update s src []⟩ := by
  generalize he : s src = xs
  induction xs generalizing s with
  | nil =>
    have hr : Function.update s src [] = s := by rw [← he]; exact Function.update_eq_self _ _
    rw [hr]
    exact loop_stop _ _ s (by simp [he])
  | cons b xs ih =>
    let s' := Function.update s src xs
    have hrest := ih s' (by simp [s'])
    have hu : Function.update s' src [] = Function.update s src [] := by simp [s']
    rw [hu] at hrest
    have hbody : Exec (instruction (fun _ => popActions src)) ⟨false,s⟩ 1 ⟨true,s'⟩ := by
      simpa only [he,List.tail_cons] using pop_instruction src s
    have hx := loop_iterate (fun h => (h src).isSome) (by simp [he]) hbody hrest
    convert hx using 1 <;> first | rfl | simp only [List.length_cons]; omega

theorem spread_instruction {src dst₁ dst₂ : Fin (k+1)}
    (h₁ : src ≠ dst₁) (h₂ : src ≠ dst₂) (h₃ : dst₁ ≠ dst₂)
    (b : Bool) (xs : List Bool) (s : Store k) (hs : s src = b :: xs) :
    Exec (instruction (spreadActions src dst₁ dst₂)) ⟨false,s⟩ 1
      ⟨true,spreadOnce src dst₁ dst₂ b xs s⟩ := by
  convert instruction_exec (spreadActions src dst₁ dst₂) s using 1
  congr 1
  funext i
  by_cases hi : i = src
  · subst i; simp [spreadOnce,spreadActions,h₁,h₂,hs,Action.apply]
  · by_cases hdi : i = dst₁
    · subst i; simp [spreadOnce,spreadActions,h₁.symm,h₃,hs,Action.apply]
    · by_cases hdj : i = dst₂
      · subst i; simp [spreadOnce,spreadActions,h₂.symm,hs,Action.apply]
      · simp [spreadOnce,spreadActions,hi,hdi,hdj,Action.apply]

theorem spread_result_once {src dst₁ dst₂ : Fin (k+1)}
    (h₁ : src ≠ dst₁) (h₂ : src ≠ dst₂) (h₃ : dst₁ ≠ dst₂)
    (b : Bool) (xs : List Bool) (s : Store k) (hs : s src = b::xs) :
    spreadResult src dst₁ dst₂ (spreadOnce src dst₁ dst₂ b xs s) = spreadResult src dst₁ dst₂ s := by
  funext i
  by_cases hi : i = dst₂
  · subst i
    simp [spreadResult,spreadOnce,h₁,h₂,hs,List.reverse_cons,List.append_assoc]
  · by_cases hd : i = dst₁
    · subst i
      simp [spreadResult,spreadOnce,h₁,h₂,h₃,hs,List.reverse_cons,List.append_assoc]
    · by_cases hsrc : i = src
      · subst i; simp [spreadResult,spreadOnce,h₁,h₂]
      · simp [spreadResult,spreadOnce,hi,hd,hsrc]

theorem spread_exec {src dst₁ dst₂ : Fin (k+1)}
    (h₁ : src ≠ dst₁) (h₂ : src ≠ dst₂) (h₃ : dst₁ ≠ dst₂) (s : Store k) :
    Exec (spread src dst₁ dst₂) ⟨none,s⟩ (3*(s src).length) ⟨none,spreadResult src dst₁ dst₂ s⟩ := by
  generalize he : s src = xs
  induction xs generalizing s with
  | nil =>
    have hr : spreadResult src dst₁ dst₂ s = s := by
      funext i
      by_cases hd₂ : i = dst₂
      · subst i; simp [spreadResult,he]
      · by_cases hd₁ : i = dst₁
        · subst i; simp [spreadResult,he,h₃]
        · by_cases hs : i = src
          · subst i; simp [spreadResult,he,h₁,h₂]
          · simp [spreadResult,hd₁,hd₂,hs]
    rw [hr]
    exact loop_stop _ _ s (by simp [he])
  | cons b xs ih =>
    let s' := spreadOnce src dst₁ dst₂ b xs s
    have hs' : s' src = xs := by simp [s',spreadOnce,h₁,h₂]
    have hrest := ih s' hs'
    rw [spread_result_once h₁ h₂ h₃ b xs s he] at hrest
    have hbody := spread_instruction h₁ h₂ h₃ b xs s he
    have hx := loop_iterate (fun h => (h src).isSome) (by simp [he]) hbody hrest
    convert hx using 1 <;> first | rfl | simp only [List.length_cons]; omega

theorem prepend_exec {src dst tmp : Fin (k+1)}
    (h₁ : src ≠ dst) (h₂ : src ≠ tmp) (h₃ : dst ≠ tmp)
    (s : Store k) (htmp : s tmp = []) :
    Exec (prepend src dst tmp) ⟨(prepend src dst tmp).initial,s⟩
      (6*(s src).length+1) ⟨Sum.inr none,Function.update s dst (s src ++ s dst)⟩ := by
  have hx := seq_exec (transfer_exec h₂ s)
    (spread_exec h₂.symm h₃.symm h₁ (transferResult src tmp s))
  have hl : (transferResult src tmp s tmp).length = (s src).length := by simp [transferResult,htmp]
  have he : spreadResult tmp src dst (transferResult src tmp s) =
      Function.update s dst (s src ++ s dst) := by
    funext i
    by_cases hd : i = dst
    · subst i; simp [spreadResult,transferResult,htmp,h₃,h₁.symm]
    · by_cases hsrc : i = src
      · subst i; simp [spreadResult,transferResult,htmp,h₂,h₁]
      · by_cases ht : i = tmp
        · subst i; simp [spreadResult,transferResult,htmp,h₂.symm,h₃.symm]
        · simp [spreadResult,transferResult,hd,hsrc,ht]
  rw [he,hl] at hx
  convert hx using 1 <;> first | rfl | omega

end ThreeMachine.StackCompiler.Program

namespace ThreeMachine.StackCompiler.Program
variable {k : ℕ}

theorem copy_exec {src dst tmp : Fin (k+1)}
    (h₁ : src ≠ dst) (h₂ : src ≠ tmp) (h₃ : dst ≠ tmp)
    (s : Store k) (htmp : s tmp = []) :
    Exec (copy src dst tmp) ⟨(copy src dst tmp).initial,s⟩
      (3*(s dst).length+6*(s src).length+2)
      ⟨Sum.inr (Sum.inr none),Function.update s dst (s src)⟩ := by
  have hx := seq_exec (clear_exec dst s)
    (prepend_exec h₁ h₂ h₃ (Function.update s dst []) (by simp [h₃.symm,htmp]))
  simpa [copy,h₁,Nat.add_assoc] using hx

end ThreeMachine.StackCompiler.Program

end

end OAI
end

section
-- module TreeData
namespace OAI

section

namespace ThreeMachine.StackCompiler

namespace Data

end Data

namespace Program
variable {k : ℕ}

theorem scan_instruction {src dst ct : Fin (k+1)}
    (h₁ : src ≠ dst) (h₂ : src ≠ ct) (h₃ : dst ≠ ct)
    (s : Store k) (b : Bool) (rest : List Bool) (hs : s src = b :: rest) :
    Exec (instruction (scanActions src dst ct)) ⟨false,s⟩ 1 ⟨true,scanOnce src dst ct s b rest⟩ := by
  convert instruction_exec (scanActions src dst ct) s using 1
  congr 1
  funext i
  by_cases hi : i = ct
  · subst i; cases b <;> simp [scanActions,scanOnce,hs,h₂.symm,h₃.symm,Action.apply]
  · by_cases hd : i = dst
    · subst i; simp [scanActions,scanOnce,hs,hi,h₁.symm,Action.apply]
    · by_cases hsrc : i = src
      · subst i; simp [scanActions,scanOnce,hs,h₁,h₂,Action.apply]
      · simp [scanActions,scanOnce,hi,hd,hsrc,Action.apply]

theorem scanned_scanned {src dst ct : Fin (k+1)}
    (h₃ : dst ≠ ct) (s : Store k) (rest mid w₁ w₂ : List Bool) (c d : ℕ) :
    scanned src dst ct (scanned src dst ct s mid w₁ d) rest w₂ c =
      scanned src dst ct s rest (w₁ ++ w₂) c := by
  funext i
  by_cases hc : i = ct
  · subst i; simp [scanned]
  · by_cases hd : i = dst
    · subst i; simp [scanned,h₃,List.reverse_append,List.append_assoc]
    · by_cases hs : i = src
      · subst i; simp [scanned,hc,hd]
      · simp [scanned,hc,hd,hs]

theorem scan_tree_continue {src dst ct : Fin (k+1)}
    (h₁ : src ≠ dst) (h₂ : src ≠ ct) (h₃ : dst ≠ ct) (d : Data) :
    ∀ (s t : Store k) (rest : List Bool) (c m : ℕ),
      s src = d.encode ++ rest → s ct = List.replicate (c+1) true →
      Exec (scan src dst ct) ⟨none,scanned src dst ct s rest d.encode c⟩ m ⟨none,t⟩ →
      Exec (scan src dst ct) ⟨none,s⟩ (3*d.size+m) ⟨none,t⟩ := by
  induction d with
  | nil =>
    intro s t rest c m hs hc hrest
    have hsrc : s src = false :: rest := by simpa using hs
    have he : scanOnce src dst ct s false rest = scanned src dst ct s rest [false] c := by
      simp [scanOnce,scanned,hc,List.replicate_succ]
    have hbody := scan_instruction h₁ h₂ h₃ s false rest hsrc
    rw [he] at hbody
    have hx := loop_iterate (fun h => (h ct).isSome) (by simp [hc,List.replicate_succ]) hbody hrest
    convert hx using 1 <;> first | rfl | simp only [Data.size_nil]; omega
  | pair a b iha ihb =>
    intro s t rest c m hs hc hrest
    let s₁ := scanOnce src dst ct s true (a.encode ++ b.encode ++ rest)
    have hs₁ : s₁ src = a.encode ++ (b.encode ++ rest) := by
      simp [s₁,scanOnce,h₁,h₂,List.append_assoc]
    have hc₁ : s₁ ct = List.replicate (c+2) true := by
      simp [s₁,scanOnce,hc,List.replicate_succ]
    let s₂ := scanned src dst ct s₁ (b.encode ++ rest) a.encode (c+1)
    have hs₂ : s₂ src = b.encode ++ rest := by simp [s₂,scanned,h₁,h₂]
    have hc₂ : s₂ ct = List.replicate (c+1) true := by simp [s₂,scanned]
    have hend : scanned src dst ct s₂ rest b.encode c =
        scanned src dst ct s rest (Data.pair a b).encode c := by
      rw [show s₂ = scanned src dst ct s₁ (b.encode ++ rest) a.encode (c+1) by rfl,
        scanned_scanned h₃]
      funext i
      by_cases hi : i = ct
      · subst i; simp [scanned]
      · by_cases hd : i = dst
        · subst i; simp [scanned,s₁,scanOnce,h₃,List.reverse_cons,List.reverse_append,
            Data.encode,List.append_assoc]
        · by_cases hsrc : i = src
          · subst i; simp [scanned,hi,hd]
          · simp [scanned,s₁,scanOnce,hi,hd,hsrc]
    have hafterB := ihb s₂ t rest c m hs₂ hc₂ (by rwa [hend])
    have hafterA := iha s₁ t (b.encode ++ rest) (c+1) (3*b.size+m) hs₁ hc₁ hafterB
    have hsrc : s src = true :: (a.encode ++ b.encode ++ rest) := by
      simpa [Data.encode,List.append_assoc] using hs
    have hbody := scan_instruction h₁ h₂ h₃ s true _ hsrc
    have hx := loop_iterate (fun h => (h ct).isSome) (by simp [hc,List.replicate_succ]) hbody hafterA
    convert hx using 1 <;> first | rfl | rw [Data.size_pair]; omega

theorem scan_tree {src dst ct : Fin (k+1)}
    (h₁ : src ≠ dst) (h₂ : src ≠ ct) (h₃ : dst ≠ ct)
    (d : Data) (s : Store k) (rest : List Bool)
    (hs : s src = d.encode ++ rest) (hc : s ct = [true]) :
    Exec (scan src dst ct) ⟨none,s⟩ (3*d.size)
      ⟨none,scanned src dst ct s rest d.encode 0⟩ := by
  have hstop : Exec (scan src dst ct) ⟨none,scanned src dst ct s rest d.encode 0⟩ 0
      ⟨none,scanned src dst ct s rest d.encode 0⟩ :=
    loop_stop _ _ _ (by simp [scanned])
  simpa using scan_tree_continue h₁ h₂ h₃ d s _ rest 0 0 hs (by simpa using hc) hstop

end Program
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler.Program
variable {k : ℕ} {Q R : Type}

theorem Exec.runs {P : Program k Q} {s t : Store k} {n : ℕ} {q : Q}
    (h : Exec P ⟨P.initial,s⟩ n ⟨q,t⟩) : P.Runs s t n := ⟨n,le_rfl,q,h⟩

theorem Runs.mono {P : Program k Q} {s t : Store k} {n m : ℕ}
    (h : P.Runs s t n) (hnm : n ≤ m) : P.Runs s t m := by
  obtain ⟨t',ht',q,hq⟩ := h
  exact ⟨t',ht'.trans hnm,q,hq⟩

theorem Runs.computes {P : Program k Q} {s t : Store k} {n : ℕ}
    (h : P.Runs s t n) : P.Computes s t n := by
  obtain ⟨m,hm,q,hq⟩ := h
  refine ⟨m,hm,?_,?_⟩
  · exact congrArg State.store hq.iterate
  · unfold run
    rw [hq.iterate]
    exact hq.halted

theorem Runs.seq {P : Program k Q} {P' : Program k R} {s t u : Store k} {n m : ℕ}
    (h : P.Runs s t n) (h' : P'.Runs t u m) : (seq P P').Runs s u (n+m+1) := by
  obtain ⟨n',hn',q,hq⟩ := h
  obtain ⟨m',hm',r,hr⟩ := h'
  exact (seq_exec hq hr).runs.mono (by omega)

theorem branch_left_exec (test : Heads k → Bool) {P : Program k Q} (P' : Program k R)
    {s t : State k Q} {n : ℕ} (h : Exec P s n t) :
    Exec (branch test P P') (State.mapControl (some ∘ Sum.inl) s) n
      (State.mapControl (some ∘ Sum.inl) t) := by
  induction h with
  | halt he =>
    apply Exec.halt
    unfold step at he ⊢
    cases hh : P.transition s.control (fun i => (s.store i).head?) <;>
      simp_all [branch,State.mapControl]
  | next he _ ih =>
    apply Exec.next _ ih
    apply lift_step P (branch test P P') (some ∘ Sum.inl) _ _ _ he
    intro q heads q' a ha
    simp [branch,ha]

theorem branch_right_exec (test : Heads k → Bool) (P : Program k Q) {P' : Program k R}
    {s t : State k R} {n : ℕ} (h : Exec P' s n t) :
    Exec (branch test P P') (State.mapControl (some ∘ Sum.inr) s) n
      (State.mapControl (some ∘ Sum.inr) t) := by
  induction h with
  | halt he =>
    apply Exec.halt
    unfold step at he ⊢
    cases hh : P'.transition s.control (fun i => (s.store i).head?) <;>
      simp_all [branch,State.mapControl]
  | next he _ ih =>
    apply Exec.next _ ih
    apply lift_step P' (branch test P P') (some ∘ Sum.inr) _ _ _ he
    intro q heads q' a ha
    simp [branch,ha]

theorem Runs.branch_left (test : Heads k → Bool) {P : Program k Q} (P' : Program k R)
    {s t : Store k} {n : ℕ} (h : P.Runs s t n) (ht : test (fun i => (s i).head?) = true) :
    (branch test P P').Runs s t (n+1) := by
  obtain ⟨m,hm,q,hq⟩ := h
  have hs : (branch test P P').step ⟨none,s⟩ = some ⟨some (.inl P.initial),s⟩ := by
    simp [step,branch,ht,stayActions,Action.apply]
  exact ⟨m+1,by omega,some (.inl q),Exec.next hs (branch_left_exec test P' hq)⟩

theorem Runs.branch_right (test : Heads k → Bool) (P : Program k Q) {P' : Program k R}
    {s t : Store k} {n : ℕ} (h : P'.Runs s t n) (ht : test (fun i => (s i).head?) = false) :
    (branch test P P').Runs s t (n+1) := by
  obtain ⟨m,hm,q,hq⟩ := h
  have hs : (branch test P P').step ⟨none,s⟩ = some ⟨some (.inr P'.initial),s⟩ := by
    simp [step,branch,ht,stayActions,Action.apply]
  exact ⟨m+1,by omega,some (.inr q),Exec.next hs (branch_right_exec test P hq)⟩

theorem move_exec {src dst tmp : Fin (k+1)}
    (h₁ : src ≠ dst) (h₂ : src ≠ tmp) (h₃ : dst ≠ tmp)
    (s : Store k) (htmp : s tmp = []) :
    Exec (move src dst tmp) ⟨(move src dst tmp).initial,s⟩
      (3*(s dst).length+6*(s src).length+2)
      ⟨Sum.inr (Sum.inr none),Function.update (Function.update s src []) dst (s src)⟩ := by
  let s₁ := Function.update s dst []
  let s₂ := transferResult src tmp s₁
  have hx := seq_exec (clear_exec dst s)
    (seq_exec (transfer_exec h₂ s₁) (transfer_exec h₃.symm s₂))
  have hl₁ : s₁ src = s src := by simp [s₁,h₁]
  have hl₂ : (s₂ tmp).length = (s src).length := by simp [s₂,s₁,transferResult,h₁,h₃.symm,htmp]
  have he : transferResult tmp dst s₂ = Function.update (Function.update s src []) dst (s src) := by
    funext i
    by_cases hd : i = dst
    · subst i; simp [transferResult,s₂,s₁,h₃,h₃.symm,htmp,h₁,h₁.symm]
    · by_cases ht : i = tmp
      · subst i; simp [transferResult,s₂,s₁,h₃.symm,htmp,h₁,h₂.symm]
      · by_cases hsrc : i = src
        · subst i; simp [transferResult,s₂,s₁,h₁,h₂]
        · simp [transferResult,s₂,s₁,hd,ht,hsrc]
  rw [he,hl₁,hl₂] at hx
  convert hx using 1 <;> first | rfl | omega

end ThreeMachine.StackCompiler.Program

namespace ThreeMachine.StackCompiler.Program
variable {k : ℕ}

theorem push_exec (dst : Fin (k+1)) (b : Bool) (s : Store k) :
    Exec (push dst b) ⟨false,s⟩ 1 ⟨true,Function.update s dst (b :: s dst)⟩ := by
  have he : (fun i => (if i = dst then Action.push b else Action.stay).apply (s i)) =
      Function.update s dst (b :: s dst) := by
    funext i
    by_cases hi : i = dst <;> simp [hi,Action.apply]
  simpa only [push,he] using instruction_exec (fun _ i => if i = dst then .push b else .stay) s

theorem setNil_runs (dst : Fin (k+1)) (s : Store k) :
    (setNil dst).Runs s (Function.update s dst Data.nil.encode) (3*(s dst).length+2) := by
  have h := (clear_exec dst s).runs.seq (push_exec dst false (Function.update s dst [])).runs
  simpa [setNil] using h

theorem setPair_runs {dst a b tmp buf : Fin (k+1)}
    (hd : dst ≠ tmp) (hd' : dst ≠ buf) (ha : a ≠ tmp) (ha' : a ≠ buf)
    (hb : b ≠ tmp) (hb' : b ≠ buf) (htb : tmp ≠ buf)
    (s : Store k) (ht : s tmp = []) (hu : s buf = []) :
    (setPair dst a b tmp buf).Runs s
      (Function.update s dst (true :: (s a ++ s b)))
      (12*(s a).length+12*(s b).length+3*(s dst).length+14) := by
  let s₁ := Function.update s tmp (s b)
  let s₂ := Function.update s tmp (s a ++ s b)
  let s₃ := Function.update s tmp (true :: (s a ++ s b))
  have h₁ : (prepend b tmp buf).Runs s s₁ (6*(s b).length+1) := by
    simpa [s₁,ht] using (prepend_exec hb hb' htb s hu).runs
  have h₂ : (prepend a tmp buf).Runs s₁ s₂ (6*(s a).length+1) := by
    have hh := (prepend_exec ha ha' htb s₁ (by simp [s₁,htb.symm,hu])).runs
    simpa [s₁,s₂,ha] using hh
  have h₃ : (push tmp true).Runs s₂ s₃ 1 := by
    simpa [s₂,s₃] using (push_exec tmp true s₂).runs
  have h₄ : (move tmp dst buf).Runs s₃ (Function.update s dst (true :: (s a ++ s b)))
      (3*(s dst).length+6*((s a).length+(s b).length+1)+2) := by
    have hh := (move_exec hd.symm htb hd' s₃ (by simp [s₃,htb.symm,hu])).runs
    have he : Function.update s₃ tmp [] = s := by
      ext i
      by_cases hi : i = tmp <;> simp [s₃,hi,ht]
    rw [he] at hh
    simpa [s₃,hd] using hh
  exact (h₁.seq (h₂.seq (h₃.seq h₄))).mono (by omega)

end ThreeMachine.StackCompiler.Program

end

end OAI
end

section
-- module RegisterMachine
namespace OAI

section

namespace ThreeMachine.StackCompiler

attribute [instance] Packed.finiteControl

namespace Packed
variable {k : ℕ}

theorem Runs.seq {P P' : Packed k} {s t u : Store k} {n m : ℕ}
    (h : P.Runs s t n) (h' : P'.Runs t u m) : (P.seq P').Runs s u (n+m+1) :=
  Program.Runs.seq h h'

theorem Runs.mono {P : Packed k} {s t : Store k} {n m : ℕ}
    (h : P.Runs s t n) (hnm : n ≤ m) : P.Runs s t m := Program.Runs.mono h hnm

end Packed

namespace Tree
variable {r : ℕ}

theorem memory_update (s : Registers r) (dst : Fin r) (d : Data) :
    memory (Function.update s dst d) = Function.update (memory s) (reg dst) d.encode := by
  funext i
  refine Fin.addCases (m := r) (n := 4) (fun i => ?_) (fun i => ?_) i
  · change memory _ (reg i) = Function.update (memory s) (reg dst) d.encode (reg i)
    by_cases hi : i = dst <;> simp [hi]
  · change memory _ (temp i) = Function.update (memory s) (reg dst) d.encode (temp i)
    simp

theorem nil_runs (dst : Fin r) (s : Registers r) :
    (nil dst).Runs (memory s) (memory (Function.update s dst .nil)) (3*(s dst).size+2) := by
  rw [memory_update]
  simpa only [nil,Packed.Runs,Packed.ofProgram,memory_reg,Data.size] using Program.setNil_runs (reg dst) (memory s)

theorem pair_runs (dst a b : Fin r) (s : Registers r) :
    (pair dst a b).Runs (memory s) (memory (Function.update s dst (.pair (s a) (s b))))
      (12*(s a).size+12*(s b).size+3*(s dst).size+14) := by
  rw [memory_update]
  simpa only [pair,Packed.Runs,Packed.ofProgram,memory_reg,Data.size,Data.encode_pair,List.cons_append] using
    Program.setPair_runs (dst := reg dst) (a := reg a) (b := reg b) (tmp := temp 0) (buf := temp 1)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (memory s) (by simp) (by simp)

end Tree
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler.Tree
variable {r : ℕ}

theorem work_update_temp (s : Registers r) (t : Fin 4 → List Bool) (i : Fin 4) (word : List Bool) :
    Function.update (work s t) (temp i) word = work s (Function.update t i word) := by
  funext j
  refine Fin.addCases (m := r) (n := 4) (fun j => ?_) (fun j => ?_) j
  · change Function.update (work s t) (temp i) word (reg j) = work _ _ (reg j)
    simp
  · change Function.update (work s t) (temp i) word (temp j) = work _ _ (temp j)
    by_cases hj : j = i <;> simp [hj]

theorem selectFinish_runs (head : Bool) (s : Registers r) (a b : Data) :
    (selectFinish head).Runs (work s ![b.encode,[],a.encode.reverse,[]])
      (work s ![(if head then a else b).encode,[],[],[]]) (3*a.size+3*b.size+2) := by
  cases head with
  | false =>
    have h₁ := (Program.clear_exec (temp 2) (work s ![b.encode,[],a.encode.reverse,[]])).runs
    rw [work_update_temp] at h₁
    have he : Function.update ![b.encode,[],a.encode.reverse,[]] (2 : Fin 4) [] = ![b.encode,[],[],[]] := by
      funext i; fin_cases i <;> simp
    rw [he] at h₁
    have h₂ := (Program.clear_exec (temp 2) (work s ![b.encode,[],[],[]])).runs
    rw [work_update_temp] at h₂
    have he₂ : Function.update ![b.encode,[],[],[]] (2 : Fin 4) [] = ![b.encode,[],[],[]] := by
      funext i; fin_cases i <;> simp
    rw [he₂] at h₂
    have hx := h₁.seq h₂
    exact hx.mono (by simp [Data.size]; omega)
  | true =>
    have h₁ := (Program.clear_exec (temp 0) (work s ![b.encode,[],a.encode.reverse,[]])).runs
    rw [work_update_temp] at h₁
    have he : Function.update ![b.encode,[],a.encode.reverse,[]] (0 : Fin 4) [] = ![[],[],a.encode.reverse,[]] := by
      funext i; fin_cases i <;> simp
    rw [he] at h₁
    have h₂ := (Program.transfer_exec (show (temp 2 : Fin (r+4)) ≠ temp 0 by simp)
      (work s ![[],[],a.encode.reverse,[]])).runs
    have he₂ : Program.transferResult (temp 2) (temp 0) (work s ![[],[],a.encode.reverse,[]]) =
        work s ![a.encode,[],[],[]] := by
      simp only [Program.transferResult,work_temp,Matrix.cons_val_two,Matrix.cons_val_zero,
        List.append_nil,work_update_temp]
      congr 1
      funext i; fin_cases i <;> simp
    rw [he₂] at h₂
    exact (h₁.seq h₂).mono (by simp [Data.size]; omega)

end ThreeMachine.StackCompiler.Tree

namespace ThreeMachine.StackCompiler.Tree
variable {r : ℕ}

theorem selectPair_runs (head : Bool) (dst : Fin r) (s : Registers r) (a b : Data) :
    (selectPair head dst).Runs (work s ![(Data.pair a b).encode,[],[],[]])
      (memory (Function.update s dst (if head then a else b)))
      (30*(a.size+b.size+(s dst).size+1)) := by
  let s₀ := work s ![(Data.pair a b).encode,[],[],[]]
  let s₁ := work s ![a.encode++b.encode,[],[],[]]
  let s₂ := work s ![a.encode++b.encode,[],[],[true]]
  let s₃ := work s ![b.encode,[],a.encode.reverse,[]]
  let s₄ := work s ![(if head then a else b).encode,[],[],[]]
  have h₁ : (Packed.ofProgram (Program.instruction (fun _ => Program.popActions (temp 0)))).Runs s₀ s₁ 1 := by
    have hh := (Program.pop_instruction (temp 0) s₀).runs
    have he : Function.update s₀ (temp 0) (s₀ (temp 0)).tail = s₁ := by
      simp only [s₀,s₁,work_temp,Matrix.cons_val_zero,Data.encode_pair,work_update_temp]
      congr 1
      funext i; fin_cases i <;> simp
    rwa [he] at hh
  have h₂ : (Packed.ofProgram (Program.push (temp 3) true)).Runs s₁ s₂ 1 := by
    have hh := (Program.push_exec (temp 3) true s₁).runs
    have he : Function.update s₁ (temp 3) (true :: s₁ (temp 3)) = s₂ := by
      simp only [s₁,s₂,work_temp,Matrix.cons_val_three,work_update_temp]
      congr 1
      funext i; fin_cases i <;> simp
    rwa [he] at hh
  have h₃ : (Packed.ofProgram (Program.scan (temp 0) (temp 2) (temp 3))).Runs s₂ s₃ (3*a.size) := by
    have hh := (Program.scan_tree (src := temp 0) (dst := temp 2) (ct := temp 3)
      (by simp) (by simp) (by simp) a s₂ b.encode (by simp [s₂]) (by simp [s₂])).runs
    have he : Program.scanned (temp 0) (temp 2) (temp 3) s₂ b.encode a.encode 0 = s₃ := by
      simp only [Program.scanned,s₂,s₃,work_temp,Matrix.cons_val_two,
        List.replicate_zero,work_update_temp]
      congr 1
      funext i; fin_cases i <;> simp
    rwa [he] at hh
  have h₄ : (selectFinish head).Runs s₃ s₄ (3*a.size+3*b.size+2) :=
    selectFinish_runs head s a b
  have h₅ : (Packed.ofProgram (Program.move (temp 0) (reg dst) (temp 1))).Runs s₄
      (memory (Function.update s dst (if head then a else b)))
      (3*(s dst).size+6*(if head then a else b).size+2) := by
    have hh := (Program.move_exec (src := temp 0) (dst := reg dst) (tmp := temp 1)
      (by simp) (by simp) (by simp) s₄ (by simp [s₄])).runs
    have he : Function.update s₄ (temp 0) [] = memory s := by
      simp only [s₄,work_update_temp]
      have hw : Function.update ![(if head then a else b).encode,[],[],[]] (0 : Fin 4) [] = ![[],[],[],[]] := by
        funext i; fin_cases i <;> simp
      rw [hw,work_empty]
    rw [he] at hh
    simpa only [Packed.Runs,Packed.ofProgram,s₄,work_reg,work_temp,Matrix.cons_val_zero,← memory_update,Data.size] using hh
  apply (h₁.seq (h₂.seq (h₃.seq (h₄.seq h₅)))).mono
  cases head <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega

theorem selectAux_runs (head : Bool) (dst : Fin r) (s : Registers r) (d : Data) :
    (selectAux head dst).Runs (work s ![d.encode,[],[],[]])
      (memory (Function.update s dst (if head then d.head else d.tail)))
      (40*(d.size+(s dst).size+1)) := by
  cases d with
  | nil =>
    have hh := (Program.move_exec (src := temp 0) (dst := reg dst) (tmp := temp 1)
      (by simp) (by simp) (by simp) (work s ![Data.nil.encode,[],[],[]]) (by simp)).runs
    have he : Function.update (work s ![Data.nil.encode,[],[],[]]) (temp 0) [] = memory s := by
      rw [work_update_temp]
      have hw : Function.update ![Data.nil.encode,[],[],[]] (0 : Fin 4) [] = ![[],[],[],[]] := by
        funext i; fin_cases i <;> simp
      rw [hw,work_empty]
    rw [he] at hh
    have hx := hh.branch_right (fun h => (h (temp 0)).getD false) (selectPair head dst).program (by simp)
    have hout : (if head then Data.nil.head else Data.nil.tail) = Data.nil := by cases head <;> rfl
    rw [hout,memory_update]
    simpa only [selectAux,Packed.Runs,Packed.branch,Packed.ofProgram,work_temp,Matrix.cons_val_zero] using
      hx.mono (m := 40*(Data.nil.size+(s dst).size+1)) (by simp [Data.size]; omega)
  | pair a b =>
    have hh := selectPair_runs head dst s a b
    have hx := Program.Runs.branch_left (fun h => (h (temp 0)).getD false)
      (Program.move (temp 0) (reg dst) (temp 1)) hh (by simp [Data.encode_pair])
    exact hx.mono (by simp [Data.size_pair]; omega)

theorem select_runs (head : Bool) (dst src : Fin r) (s : Registers r) :
    (select head dst src).Runs (memory s)
      (memory (Function.update s dst (if head then (s src).head else (s src).tail)))
      (50*((s src).size+(s dst).size+1)) := by
  have h₁ := (Program.copy_exec (src := reg src) (dst := temp 0) (tmp := temp 1)
    (by simp) (by simp) (by simp) (memory s) (by simp)).runs
  have he : Function.update (memory s) (temp 0) (memory s (reg src)) = work s ![(s src).encode,[],[],[]] := by
    rw [memory_reg,← work_empty,work_update_temp]
    congr 1
    funext i; fin_cases i <;> simp
  rw [he] at h₁
  have h₂ := selectAux_runs head dst s (s src)
  exact (h₁.seq h₂).mono (by simp [Data.size]; omega)

end ThreeMachine.StackCompiler.Tree

namespace ThreeMachine.StackCompiler.Program
variable {k : ℕ} {Q : Type}

theorem Runs.loop_stop (test : Heads k → Bool) (P : Program k Q) (s : Store k)
    (hs : test (fun i => (s i).head?) = false) : (loop test P).Runs s s 0 :=
  (Program.loop_stop test P s hs).runs

theorem Runs.loop_iterate (test : Heads k → Bool) {P : Program k Q}
    {s t u : Store k} {n m : ℕ} (h : P.Runs s t n) (h' : (loop test P).Runs t u m)
    (hs : test (fun i => (s i).head?) = true) : (loop test P).Runs s u (n+m+2) := by
  obtain ⟨n',hn,q,hq⟩ := h
  obtain ⟨m',hm,r,hr⟩ := h'
  have hnone : r = none := by
    have hh := hr.halted
    cases r with
    | none => rfl
    | some q =>
      unfold step at hh
      cases he : P.transition q (fun i => (u i).head?) <;> simp_all [loop]
  subst r
  exact (Program.loop_iterate test hs hq hr).runs.mono (by omega)

end ThreeMachine.StackCompiler.Program

namespace ThreeMachine.StackCompiler.Tree
variable {r : ℕ}

theorem skip_runs (s : Registers r) : skip.Runs (memory s) (memory s) 1 := by
  have hh := (Program.instruction_exec (k := r+3) (fun _ => Program.stayActions) (memory s)).runs
  simpa only [skip,Packed.Runs,Packed.ofProgram,Program.stayActions,Action.apply] using hh

theorem copy_runs (dst src : Fin r) (s : Registers r) :
    (copy dst src).Runs (memory s) (memory (Function.update s dst (s src)))
      (3*(s dst).size+6*(s src).size+2) := by
  by_cases he : dst = src
  · subst src
    simpa [copy] using (skip_runs s).mono (by omega : 1 ≤ 3*(s dst).size+6*(s dst).size+2)
  · rw [memory_update]
    unfold copy
    rw [ite_eq_right he]
    have hh := (Program.copy_exec (src := reg src) (dst := reg dst) (tmp := temp 0)
      (by simpa using Ne.symm he) (by simp) (by simp) (memory s) (by simp)).runs
    simpa only [memory_reg,Data.size,Packed.Runs,Packed.ofProgram] using hh

namespace Code

end Code

theorem Eval.compile {p : Code (Fin r)} {s t : Registers r} {n : ℕ} (h : Eval p s t n) :
    p.compile.Runs (memory s) (memory t) (150*n) := by
  induction h with
  | skip s => exact (skip_runs s).mono (by omega)
  | nil dst s =>
    apply (nil_runs dst s).mono
    omega
  | pair dst a b s =>
    apply (pair_runs dst a b s).mono
    omega
  | select head dst src s =>
    apply (select_runs head dst src s).mono
    omega
  | copy dst src s =>
    apply (copy_runs dst src s).mono
    omega
  | seq _ _ ih ih' => exact (ih.seq ih').mono (by omega)
  | @branch_true src p q s t n hs _ ih =>
    exact (Program.Runs.branch_left _ q.compile.program ih (by simpa using hs)).mono (by omega)
  | @branch_false src p q s t n hs _ ih =>
    exact (Program.Runs.branch_right _ p.compile.program ih (by simpa using hs)).mono (by omega)
  | @loop_stop src p s hs =>
    exact (Program.Runs.loop_stop _ p.compile.program (memory s) (by simpa using hs)).mono (by omega)
  | @loop_step src p s t u n m hs _ _ ih ih' =>
    exact (Program.Runs.loop_iterate _ ih ih' (by simpa using hs)).mono (by omega)

end ThreeMachine.StackCompiler.Tree

end

end OAI
end

section
-- module RoutineCompiler
namespace OAI

section

namespace ThreeMachine.StackCompiler.Tree
variable {V W : Type} [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] [DecidableEq W] in
theorem overlay_of_agree (f : V → W) (s : V → Data) (base : W → Data)
    (h : ∀ i, base (f i) = s i) : overlay f s base = base := by
  funext j
  by_cases hj : ∃ a, f a = j
  · unfold overlay Function.extend
    simp only [dite_eq_left hj]
    rw [← h]
    congr 1
    exact Classical.choose_spec hj
  · exact overlay_out s base hj

end ThreeMachine.StackCompiler.Tree

namespace ThreeMachine.StackCompiler.Tree
variable {V W : Type} [DecidableEq V] [DecidableEq W]

end ThreeMachine.StackCompiler.Tree

namespace ThreeMachine.StackCompiler
open ThreeMachine.StackCompiler.Tree

attribute [instance] Routine.finiteVars Routine.decVars

namespace Routine
variable {f g : Data → Data} {charge charge' : Data → ℕ}

end Routine
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
open ThreeMachine.StackCompiler.Tree
variable {V W : Type} [DecidableEq V] [DecidableEq W]

namespace Routine
variable {f g : Data → Data} {c d : Data → ℕ}

end Routine
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
open ThreeMachine.StackCompiler.Tree

variable {V : Type} [DecidableEq V]

namespace Routine
variable {f g : Data → Data} {c d : Data → ℕ}

end Routine
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler.Tree
variable {V : Type} [DecidableEq V]

end ThreeMachine.StackCompiler.Tree

end

end OAI
end

section
-- module MachineBridge
namespace OAI

section

namespace ThreeMachine.StackCompiler.Packed
variable {k : ℕ}

theorem halt_runs (s : Store k) : halt.Runs s s 0 :=
  ⟨0,le_rfl,(),Program.Exec.halt rfl⟩

theorem pushWord_runs (dst : Fin (k+1)) (bs : List Bool) (s : Store k) :
    (pushWord dst bs).Runs s (Function.update s dst (bs ++ s dst)) (2*bs.length) := by
  induction bs with
  | nil => simpa only [pushWord,List.nil_append,Function.update_eq_self,List.length_nil,Nat.mul_zero] using halt_runs s
  | cons b bs ih =>
    have hp : (ofProgram (Program.push dst b)).Runs (Function.update s dst (bs ++ s dst))
        (Function.update (Function.update s dst (bs ++ s dst)) dst (b :: (bs ++ s dst))) 1 := by
      change (Program.push dst b).Runs _ _ _
      simpa only [Function.update_self] using (Program.push_exec dst b (Function.update s dst (bs ++ s dst))).runs
    have h := ih.seq hp
    simpa only [pushWord,List.length_cons,Function.update_self,Function.update_idem,
      List.cons_append,Nat.mul_add,Nat.mul_one,Nat.add_assoc] using h

theorem pop_runs (src : Fin (k+1)) (s : Store k) :
    (pop src).Runs s (Function.update s src (s src).tail) 1 :=
  (Program.pop_instruction src s).runs

theorem popN_runs (src : Fin (k+1)) (n : ℕ) (s : Store k) :
    (popN src n).Runs s (Function.update s src ((s src).drop n)) (2*n) := by
  induction n generalizing s with
  | zero => simpa only [popN,List.drop_zero,Function.update_eq_self,Nat.mul_zero] using halt_runs s
  | succ n ih =>
    have h := (pop_runs src s).seq (ih (Function.update s src (s src).tail))
    have h' := h.mono (show 1+2*n+1 ≤ 2*(n+1) by omega)
    simpa only [popN,Function.update_self,Function.update_idem,List.drop_tail] using h'

end ThreeMachine.StackCompiler.Packed

namespace ThreeMachine.StackCompiler.Raw
open Packed
variable {k : ℕ}

theorem encoded_cons (b : Bool) (xs : List Bool) :
    (enc (b :: xs)).encode = boolChunk b ++ (enc xs).encode := rfl

theorem encodeBody_runs {src dst : Fin (k+1)} (hne : src ≠ dst)
    (b : Bool) (bs : List Bool) (s : Store k) (hs : s src = b :: bs) :
    (encodeBody src dst).Runs s
      (Function.update (Function.update s src bs) dst (boolChunk b ++ s dst)) 12 := by
  have h := (Packed.pop_runs src s).seq
    (Packed.pushWord_runs dst (boolChunk b) (Function.update s src (s src).tail))
  simp only [hs,List.tail_cons,Function.update_of_ne hne.symm] at h
  cases b with
  | false =>
    exact (Program.Runs.branch_right _ _ h (by simp [hs])).mono (by decide)
  | true =>
    exact (Program.Runs.branch_left _ _ h (by simp [hs])).mono (by decide)

theorem encodeLoop_runs {src dst : Fin (k+1)} (hne : src ≠ dst)
    (bs ys : List Bool) (s : Store k) (hs : s src = bs) (hd : s dst = (enc ys).encode) :
    (encodeLoop src dst).Runs s
      (Function.update (Function.update s src []) dst (enc (bs.reverse ++ ys)).encode)
      (14*bs.length) := by
  induction bs generalizing ys s with
  | nil =>
    have he : Function.update (Function.update s src []) dst (enc ([] ++ ys)).encode = s := by
      rw [List.nil_append,← hd]; ext i
      by_cases hi : i = dst <;> by_cases hj : i = src <;> simp_all
    rw [List.reverse_nil,he]
    exact Program.Runs.loop_stop _ _ s (by simp [hs])
  | cons b bs ih =>
    let t := Function.update (Function.update s src bs) dst (boolChunk b ++ s dst)
    have hb : (encodeBody src dst).Runs s t 12 := encodeBody_runs hne b bs s hs
    have ht : t src = bs := by simp [t,hne]
    have hd' : t dst = (enc (b :: ys)).encode := by simp only [t,Function.update_self,hd,encoded_cons]
    have hr := ih (b :: ys) t ht hd'
    have he : Function.update (Function.update t src []) dst (enc (bs.reverse ++ b :: ys)).encode =
        Function.update (Function.update s src []) dst (enc ((b :: bs).reverse ++ ys)).encode := by
      simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
      ext i
      by_cases hi : i = dst <;> by_cases hj : i = src <;> simp_all [t]
    rw [he] at hr
    exact (Program.Runs.loop_iterate _ hb hr (by simp [hs])).mono (by simp only [List.length_cons]; omega)

end ThreeMachine.StackCompiler.Raw

namespace ThreeMachine.StackCompiler.Raw
open Packed
variable {k : ℕ}

theorem decodeAfterTag_runs {src dst : Fin (k+1)} (hne : src ≠ dst)
    (b : Bool) (rest : List Bool) (s : Store k) (hs : s src = (enc b).encode ++ rest) :
    (decodeAfterTag src dst).Runs s
      (Function.update (Function.update s src rest) dst (b :: s dst)) 10 := by
  cases b with
  | false =>
    have h := Program.Runs.seq (Packed.popN_runs src 1 s)
      (Program.push_exec dst false (Function.update s src ((s src).drop 1))).runs
    have he : (enc false).encode = [false] := rfl
    simp only [hs,he,List.singleton_append,List.drop_succ_cons,List.drop_zero,
      Function.update_of_ne hne.symm] at h
    exact (Program.Runs.branch_right _ _ h (by simp [hs])).mono (by omega)
  | true =>
    have h := Program.Runs.seq (Packed.popN_runs src 3 s)
      (Program.push_exec dst true (Function.update s src ((s src).drop 3))).runs
    have he : (enc true).encode = [true,false,false] := rfl
    simp only [hs,he,List.cons_append,List.nil_append,List.drop_succ_cons,List.drop_zero,
      Function.update_of_ne hne.symm] at h
    exact (Program.Runs.branch_left _ _ h (by simp [hs])).mono (by omega)

theorem decodeBody_runs {src dst : Fin (k+1)} (hne : src ≠ dst)
    (b : Bool) (bs : List Bool) (s : Store k) (hs : s src = (enc (b :: bs)).encode) :
    (decodeBody src dst).Runs s
      (Function.update (Function.update s src (enc bs).encode) dst (b :: s dst)) 12 := by
  have ht : (Function.update s src (s src).tail) src = (enc b).encode ++ (enc bs).encode := by
    simp only [Function.update_self,hs,encoded_cons,boolChunk,List.cons_append,List.tail_cons]
  have h := (Packed.pop_runs src s).seq (decodeAfterTag_runs hne b (enc bs).encode _ ht)
  simpa only [decodeBody,Function.update_idem,Function.update_of_ne hne.symm,Nat.reduceAdd] using h

theorem decodeLoop_runs {src dst : Fin (k+1)} (hne : src ≠ dst)
    (bs : List Bool) (s : Store k) (hs : s src = (enc bs).encode) :
    (decodeLoop src dst).Runs s
      (Function.update (Function.update s src [false]) dst (bs.reverse ++ s dst))
      (14*bs.length) := by
  induction bs generalizing s with
  | nil =>
    have he : Function.update (Function.update s src [false]) dst ([] ++ s dst) = s := by
      rw [List.nil_append]; ext i
      by_cases hi : i = dst <;> by_cases hj : i = src <;> simp_all
    rw [List.reverse_nil,he]
    exact Program.Runs.loop_stop _ _ s (by change (s src).head?.getD false = _; rw [hs]; rfl)
  | cons b bs ih =>
    let t := Function.update (Function.update s src (enc bs).encode) dst (b :: s dst)
    have hb : (decodeBody src dst).Runs s t 12 := decodeBody_runs hne b bs s hs
    have hr := ih t (by simp [t,hne])
    have he : Function.update (Function.update t src [false]) dst (bs.reverse ++ t dst) =
        Function.update (Function.update s src [false]) dst ((b :: bs).reverse ++ s dst) := by
      simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
      ext i
      by_cases hi : i = dst <;> by_cases hj : i = src <;> simp_all [t]
    rw [he] at hr
    exact (Program.Runs.loop_iterate _ hb hr (by change (s src).head?.getD false = _; rw [hs]; rfl)).mono
      (by simp only [List.length_cons]; omega)

end ThreeMachine.StackCompiler.Raw

namespace ThreeMachine.StackCompiler.Tree
variable {V W : Type} [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] [DecidableEq W] in
theorem overlay_zero (f : V → W) : overlay f (zeroStore V) (zeroStore W) = zeroStore W :=
  overlay_of_agree f _ _ (fun _ => rfl)

theorem overlay_start {f : V → W} (hf : Function.Injective f) (input : V) (x : Data) :
    overlay f (start input x) (zeroStore W) = start (f input) x := by
  rw [start,overlay_update hf,overlay_zero]
  rfl

theorem overlay_finish {f : V → W} (hf : Function.Injective f) (a b : V) (x y : Data) :
    overlay f (finish a b x y) (zeroStore W) = finish (f a) (f b) x y := by
  rw [finish,overlay_update hf,overlay_start hf]
  rfl

end ThreeMachine.StackCompiler.Tree

namespace ThreeMachine.StackCompiler.Routine
open ThreeMachine.StackCompiler.Tree
variable {f : Data → Data} {charge : Data → ℕ}
variable (R : Routine f charge)

theorem number_injective : Function.Injective R.number :=
  (Fin.succ_injective _).comp (Fintype.equivFin R.Vars).injective

theorem numberedCode_runs (x : Data) :
    R.numberedCode.compile.Runs (memory (start (R.number R.input) x))
      (memory (finish (R.number R.input) (R.number R.output) x (f x))) (150*charge x) := by
  obtain ⟨n,hn,he⟩ := R.correct x
  have hh := (he.rename R.number_injective (zeroStore (Fin (Fintype.card R.Vars+1)))).compile
  rw [overlay_start R.number_injective,overlay_finish R.number_injective] at hh
  exact hh.mono (Nat.mul_le_mul_left 150 hn)

theorem initRegs_runs (s : Store (Fintype.card R.Vars+4)) :
    R.initRegs.Runs s (fun j => if j.val < Fintype.card R.Vars+1 then false :: s j else s j) 1 := by
  have he : (fun j => (if j.val < Fintype.card R.Vars+1 then Action.push false else Action.stay).apply (s j)) =
      (fun j => if j.val < Fintype.card R.Vars+1 then false :: s j else s j) := by
    funext j
    split_ifs <;> rfl
  simpa only [initRegs,Packed.Runs,Packed.ofProgram,he] using
    (Program.instruction_exec (fun _ j =>
      if j.val < Fintype.card R.Vars+1 then Action.push false else .stay) s).runs

theorem inputProgram_runs (bs : List Bool) :
    R.inputProgram.Runs (initialStore bs)
      (memory (start (R.number R.input) (enc bs))) (17*bs.length+3) := by
  let s : Store (Fintype.card R.Vars+4) := Function.update (fun _ => []) (temp 0) bs.reverse
  have ht : (Packed.ofProgram (Program.transfer 0 (temp 0))).Runs
      (initialStore bs) s (3*bs.length) := by
    have h := (Program.transfer_exec (Ne.symm R.temp_ne_zero) (initialStore bs)).runs
    have he : Program.transferResult 0 (temp 0) (initialStore bs) = s := by
      funext i
      by_cases hi : i = temp 0 <;> by_cases hz : i = 0 <;>
        simp_all [Program.transferResult,initialStore,s,R.temp_ne_zero,Ne.symm R.temp_ne_zero]
    simpa only [Packed.Runs,Packed.ofProgram,initialStore,ite_true,he] using h
  let t : Store (Fintype.card R.Vars+4) :=
    fun j => if j.val < Fintype.card R.Vars+1 then false :: s j else s j
  have hi : R.initRegs.Runs s t 1 := R.initRegs_runs s
  have hts : t (temp 0) = bs.reverse := by simp [t,s,temp]
  have htd : t (reg (R.number R.input)) = (enc ([] : List Bool)).encode := by
    have hv : (reg (R.number R.input)).val < Fintype.card R.Vars+1 := (R.number R.input).isLt
    simp only [t,ite_eq_left hv,s,Function.update_of_ne (reg_ne_temp _ _)]
    rfl
  have he := Raw.encodeLoop_runs (temp_ne_reg _ _) bs.reverse [] t hts htd
  have hfinal : Function.update (Function.update t (temp 0) [])
      (reg (R.number R.input)) (enc (bs.reverse.reverse ++ [])).encode =
      memory (start (R.number R.input) (enc bs)) := by
    simp only [List.reverse_reverse,List.append_nil]
    funext j
    refine Fin.addCases (m := Fintype.card R.Vars+1) (n := 4) (fun i => ?_) (fun i => ?_) j
    · change Function.update (Function.update t (temp 0) []) (reg (R.number R.input))
        (enc bs).encode (reg i) = memory (start (R.number R.input) (enc bs)) (reg i)
      by_cases hh : i = R.number R.input
      · subst i; simp
      · have hv : (reg i).val < Fintype.card R.Vars+1 := i.isLt
        simp only [Function.update_of_ne (show reg i ≠ reg (R.number R.input) by simpa using hh),
          memory_reg,start_other _ hh,t,ite_eq_left hv,s,
          Function.update_of_ne (reg_ne_temp _ _)]
        rfl
    · change Function.update (Function.update t (temp 0) []) (reg (R.number R.input))
        (enc bs).encode (temp i) = memory (start (R.number R.input) (enc bs)) (temp i)
      by_cases hh : i = 0
      · subst i; simp
      · have hv : ¬(temp (r := Fintype.card R.Vars+1) i).val < Fintype.card R.Vars+1 := by
          simp only [temp,Fin.val_natAdd]; omega
        simp only [Function.update_of_ne (temp_ne_reg _ _),memory_temp,
          Function.update_of_ne (show (temp i : Fin (Fintype.card R.Vars+1+4)) ≠ temp 0 by simpa using hh),
          t,ite_eq_right hv,s]
  rw [hfinal] at he
  exact (ht.seq (hi.seq he)).mono (by simp only [List.length_reverse]; omega)

theorem outputProgram_runs (bs out : List Bool) :
    ∃ t, R.outputProgram.Runs
      (memory (finish (R.number R.input) (R.number R.output) (enc bs) (enc out))) t
      (17*out.length+3) ∧ t 0 = out := by
  let s := memory (finish (R.number R.input) (R.number R.output) (enc bs) (enc out))
  have hzero : s 0 = [false] := by
    change memory _ (reg (0 : Fin (Fintype.card R.Vars+1))) = _
    simp only [memory_reg,finish,Function.update_of_ne (Ne.symm (R.number_ne_zero R.output)),
      start_other _ (Ne.symm (R.number_ne_zero R.input))]
    rfl
  have hd := Raw.decodeLoop_runs (reg_ne_temp _ 0) out s
    (show s (reg (R.number R.output)) = (enc out).encode by simp [s])
  let u := Function.update (Function.update s (reg (R.number R.output)) [false])
    (temp 0) (out.reverse ++ s (temp 0))
  have hu : u 0 = [false] := by
    simp only [u,Function.update_of_ne (Ne.symm R.temp_ne_zero),
      Function.update_of_ne (Ne.symm (R.reg_number_ne_zero R.output)),hzero]
  have hv : u (temp 0) = out.reverse := by simp [u,s]
  let v := Function.update u 0 []
  have hp : (Packed.pop 0).Runs u v 1 := by
    simpa only [hu,List.tail_cons,List.tail_nil] using Packed.pop_runs 0 u
  have ht := (Program.transfer_exec R.temp_ne_zero v).runs
  have hvt : v (temp 0) = out.reverse := by simp [v,R.temp_ne_zero,hv]
  have hvz : v 0 = [] := by simp [v]
  rw [hvt,List.length_reverse] at ht
  have ht' : (Packed.ofProgram (Program.transfer (temp 0) 0)).Runs v
      (Program.transferResult (temp 0) 0 v) (3*out.length) := ht
  refine ⟨Program.transferResult (temp 0) 0 v,?_,?_⟩
  · exact (hd.seq (hp.seq ht')).mono (by omega)
  · simp [Program.transferResult,hvt,hvz]

theorem rawProgram_runs (bs out : List Bool) (h : f (enc bs) = enc out) :
    ∃ t, R.rawProgram.Runs (initialStore bs) t
      (1000*(charge (enc bs)+bs.length+out.length+1)) ∧ t 0 = out := by
  have hi := R.inputProgram_runs bs
  have hc := R.numberedCode_runs (enc bs)
  rw [h] at hc
  obtain ⟨t,ho,ht⟩ := R.outputProgram_runs bs out
  exact ⟨t,(hi.seq (hc.seq ho)).mono (by omega),ht⟩

include R in
theorem exists_rawMachine : ∃ k q g, ∃ M : Machine k q g,
    ∀ bs out, f (enc bs) = enc out →
      M.Produces bs out (2000*(charge (enc bs)+bs.length+out.length+1)) := by
  refine ⟨_,_,_,compile R.rawProgram.program,?_⟩
  intro bs out h
  obtain ⟨t,ht,ho⟩ := R.rawProgram_runs bs out h
  have hh := ht.computes
  obtain ⟨n,hn,hs,hh⟩ := hh
  have he := compile_produces R.rawProgram.program bs out
    (1000*(charge (enc bs)+bs.length+out.length+1)) ⟨n,hn,hh,by rw [hs,ho]⟩
  simpa only [← Nat.mul_assoc] using he

end ThreeMachine.StackCompiler.Routine
end

end OAI
end

section
-- module Main
namespace OAI

section
namespace ThreeMachine.StackCompiler

theorem enc_request {n : ℕ} (x : Request n) :
    enc x = enc (ThreeMachine.encodeInput x.graph x.deadline) := rfl

theorem Uniform.exists_requestMachine
    (R : Uniform (fun n (x : Request n) => Algorithm.output x.graph x.deadline)) :
    ∃ k q g, ∃ M : Machine k q g, ∀ n (x : Request n),
      M.Produces (ThreeMachine.encodeInput x.graph x.deadline)
        (Algorithm.output x.graph x.deadline)
        (2000*(R.time n x+(ThreeMachine.encodeInput x.graph x.deadline).length+
          (Algorithm.output x.graph x.deadline).length+1)) := by
  obtain ⟨k,q,g,M,hM⟩ := R.routine.exists_rawMachine
  refine ⟨k,q,g,M,?_⟩
  intro n x
  have hc := R.correct n x
  rw [enc_request] at hc
  have hr := hM (ThreeMachine.encodeInput x.graph x.deadline)
    (Algorithm.output x.graph x.deadline) hc
  simpa only [Uniform.time,enc_request] using hr

end ThreeMachine.StackCompiler

end

end OAI

namespace OAI
section
namespace ThreeMachine
open StackCompiler

theorem main_theorem : ReleaseTheorem := by
  obtain ⟨k,q,g,M,hM⟩ := Uniform.exists_requestMachine Uniform.requestAnswer
  obtain ⟨C,hC⟩ := requestRawBound_length
  refine ⟨k,q,g,M,C+1,by omega,?_⟩
  intro n G hn hG deadline hd
  let x : Request n := ⟨G,deadline⟩
  have hsmall : deadline.getD 0 ≤ n := by
    cases deadline with
    | none => simp only [Option.getD_none]; omega
    | some T => exact (hd T (by simp)).2
  let y : SmallDeadline := ⟨⟨n,x⟩,hsmall⟩
  refine ⟨Algorithm.output G deadline,Algorithm.output_correct G hn hG deadline,?_⟩
  have hr := hM n x
  have hb : 2000*(Uniform.requestAnswer.time n x+
      (encodeInput G deadline).length+(Algorithm.output G deadline).length+1) ≤
        (C+1)*((encodeInput G deadline).length+2)^150020 := by
    calc
      _ = requestRawBound y.1 := rfl
      _ ≤ C*((encodeInput G deadline).length+2)^150020 := by
        have hy := hC y
        dsimp only [RequestData.bits,y,x] at hy
        exact hy
      _ ≤ (C+1)*((encodeInput G deadline).length+2)^150020 :=
        Nat.mul_le_mul_right _ (Nat.le_succ C)
  obtain ⟨t,ht,halt,out⟩ := hr
  exact ⟨t,ht.trans hb,halt,out⟩

end ThreeMachine
end
end OAI
end

theorem solution : OAI.ThreeMachine.ReleaseTheorem := OAI.ThreeMachine.main_theorem
